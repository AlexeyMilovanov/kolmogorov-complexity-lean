#!/usr/bin/env python3
"""Regression tests for the migration-fidelity parser and ledger assertions."""

from __future__ import annotations

from collections import Counter
import importlib.util
from pathlib import Path
import sys
import tempfile


CHECKER_PATH = Path(__file__).with_name("check_migration_fidelity.py")


def load_checker():
    spec = importlib.util.spec_from_file_location("migration_fidelity", CHECKER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {CHECKER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main() -> int:
    checker = load_checker()
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        sample = root / "Sample.lean"
        sample.write_text(
            """
namespace Outer

/- theorem commentGhost : True := by trivial -/
-- lemma lineGhost : True := by trivial

@[simp]
theorem attributed : True := by trivial

namespace Inner

@[aesop safe, simp]
protected lemma repeated : True := by trivial

end Inner

section LocalSection

def repeated : Nat := 0

end LocalSection
end Outer

namespace Second
def repeated : Nat := 1
end Second
""".lstrip(),
            encoding="utf-8",
        )
        declarations = checker.declarations_for("Sample.lean", sample)
        identities = Counter(declaration.identity for declaration in declarations)
        assert identities == Counter(
            {
                "Outer.attributed": 1,
                "Outer.Inner.repeated": 1,
                "Outer.repeated": 1,
                "Second.repeated": 1,
            }
        )
        attributes = {
            declaration.qualified_name: declaration.attributes
            for declaration in declarations
        }
        assert attributes["Outer.attributed"] == ("simp",)
        assert attributes["Outer.Inner.repeated"] == ("aesop", "simp")
        assert all("Ghost" not in declaration.qualified_name for declaration in declarations)

        smoke = root / "Smoke.lean"
        smoke.write_text(
            """
-- assert_compat "commented" => Missing.name
/- assert_compat "blocked" => Also.missing -/
assert_compat "source.one" => Target.one
assert_compat "source.two" =>
  Target.two
""".lstrip(),
            encoding="utf-8",
        )
        assert checker.compatibility_assertions(smoke) == Counter(
            {
                ("source.one", "Target.one"): 1,
                ("source.two", "Target.two"): 1,
            }
        )

        coverage = "| Other | same |\n| Primrec toolkit | old API |\n"
        changed = "| Other | same |\n| Primrec toolkit | new API |\n"
        assert checker.normalize_coverage(coverage) == checker.normalize_coverage(changed)
        try:
            checker.normalize_coverage("| Other | same |\n")
        except checker.FidelityError:
            pass
        else:
            raise AssertionError("missing Primrec coverage row was accepted")

    print("FIDELITY REGRESSION TESTS OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
