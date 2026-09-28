#!/usr/bin/env python3
"""Self-test for `scripts/check_headers.py --by-name`.

Builds throw-away git repositories whose "before" and "after" trees exercise
the cases the freeze check has to get right -- declarations that move between
modules, `namespace`/`section`/`end` nesting across a split, a binder renamed
to an underscore, an exact-duplicate deletion, and the changes that must be
reported as problems -- and asserts on the checker's output.

Usage:  python3 scripts/tests/check_headers_selftest.py
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# `CHECK_HEADERS` points the self-test at another copy of the checker, which
# is how the previous, broken version was scored against these same cases.
CHECKER = Path(os.environ.get(
    'CHECK_HEADERS',
    Path(__file__).resolve().parent.parent / 'check_headers.py'))


def run(cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)


def scenario(before: dict[str, str], after: dict[str, str],
             tables: dict[str, str] | None = None,
             extra_args: tuple[str, ...] = ()) -> str:
    """Commit `before`, write `after`, return the checker's output.

    `tables` holds auxiliary non-Lean files (a rename table, a
    definition-merge table) written into the working tree before the check,
    and `extra_args` the options that point the checker at them.
    """
    tmp = Path(tempfile.mkdtemp())
    (tmp / 'scripts').mkdir()
    shutil.copy(CHECKER, tmp / 'scripts' / 'check_headers.py')
    run(['git', 'init', '-q'], tmp)
    run(['git', 'config', 'user.email', 'a@b.c'], tmp)
    run(['git', 'config', 'user.name', 'test'], tmp)
    for name, text in before.items():
        p = tmp / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    run(['git', 'add', '-A'], tmp)
    run(['git', 'commit', '-qm', 'before'], tmp)
    for name in before:
        (tmp / name).unlink()
    for name, text in {**after, **(tables or {})}.items():
        p = tmp / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    run(['git', 'add', '-A'], tmp)
    r = run([sys.executable, 'scripts/check_headers.py', '--by-name',
             '--rev', 'HEAD', '--allow-underscore', *extra_args], tmp)
    shutil.rmtree(tmp)
    return r.stdout


FAILURES: list[str] = []


def expect(label: str, out: str, *, problems: int, contains=(),
           absent=(), moved: int | None = None, dups: int | None = None,
           underscores: int | None = None,
           merged: int | None = None) -> None:
    fields = {'moved': r'(\d+) moved modules',
              'underscores': r'(\d+) underscore renames',
              'dups': r'(\d+) duplicate copies removed',
              'merged': r'(\d+) definitions merged',
              'problems': r'(\d+) problems'}
    got = {}
    for key, pat in fields.items():
        m = re.search(pat, out)
        if m is None:
            print(f'FAIL {label}: no summary line in\n{out}')
            FAILURES.append(label)
            return
        got[key] = int(m.group(1))
    ok = True
    msgs = []
    for key, want in (('problems', problems), ('moved', moved),
                      ('dups', dups), ('underscores', underscores),
                      ('merged', merged)):
        if want is not None and got[key] != want:
            ok = False
            msgs.append(f'{key}: expected {want}, got {got[key]}')
    for s in contains:
        if s not in out:
            ok = False
            msgs.append(f'missing from output: {s!r}')
    for s in absent:
        if s in out:
            ok = False
            msgs.append(f'unexpectedly present in output: {s!r}')
    if ok:
        print(f'ok   {label}')
    else:
        print(f'FAIL {label}')
        for msg in msgs:
            print(f'       {msg}')
        for line in out.strip().split('\n'):
            print(f'     | {line}')
        FAILURES.append(label)


BIG = '''\
import Mathlib

namespace Kolmogorov

namespace SUV

section Basics

variable {n : ℕ}

/-- doc -/
theorem alpha (h : n = 0) : n + 1 = 1 := by simp [h]

end Basics

noncomputable section

def beta : ℕ → ℕ := fun k => k + 1

end

namespace Ch01

@[simp]
theorem gamma (m : ℕ) : m + 0 = m := by simp

end Ch01

end SUV

def delta : ℕ := 3

end Kolmogorov
'''

# The same declarations, split over two modules, namespaces re-opened.
SPLIT_A = '''\
import Mathlib

namespace Kolmogorov
namespace SUV
section Basics

variable {n : ℕ}

/-- doc -/
theorem alpha (h : n = 0) : n + 1 = 1 := by simp [h]

end Basics
end SUV
end Kolmogorov
'''

SPLIT_B = '''\
import Mathlib

namespace Kolmogorov
namespace SUV

noncomputable section

def beta : ℕ → ℕ := fun k => k + 1

end

namespace Ch01

@[simp]
theorem gamma (m : ℕ) : m + 0 = m := by simp

end Ch01

end SUV

def delta : ℕ := 3

end Kolmogorov
'''


# Two theorems with token-identical headers in different `variable` contexts.
CTX_ONE = '''\
import Mathlib

namespace Kolmogorov

section Implicit

variable {n : ℕ}

/-- doc -/
theorem zeta : n + 0 = n := by simp

end Implicit

end Kolmogorov
'''

CTX_TWO = CTX_ONE.replace('''end Implicit
''', '''end Implicit

section Explicit

variable (n : ℕ)

/-- doc -/
theorem eta : n + 0 = n := by simp

end Explicit
''')

# A self-contained lemma, alone and inside a section whose binders it re-binds.
INST_PLAIN = '''\\
import Mathlib

namespace Kolmogorov

/-- doc -/
theorem iota {\u03b1 : Type*} [Primcodable \u03b1] (l : List \u03b1) : l.length = l.length :=
  rfl

end Kolmogorov
'''

INST_SECTION = '''\\
import Mathlib

namespace Kolmogorov

section Ctx

variable {\u03b1 : Type*} [Primcodable \u03b1]

/-- doc -/
theorem iota {\u03b1 : Type*} [Primcodable \u03b1] (l : List \u03b1) : l.length = l.length :=
  rfl

end Ctx

end Kolmogorov
'''

# The same theorem with and without an `omit ... in` prefix.
OMIT_ONE = '''\
import Mathlib

namespace Kolmogorov

section Ctx

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- doc -/
theorem iota (s : Finset A) : s.card = s.card := rfl

end Ctx

end Kolmogorov
'''

OMIT_TWO = OMIT_ONE.replace('''end Ctx
''', '''omit [DecidableEq A] in
/-- doc -/
theorem theta (s : Finset A) : s.card = s.card := rfl

end Ctx
''')


# Two theorems whose statements bind a `let`: they agree up to the binding
# and differ after it.
LET_ONE = '''\
import Mathlib

namespace Kolmogorov

/-- doc -/
theorem kappa (n : ℕ) : let m := n + 1
    0 < m := by simp

end Kolmogorov
'''

LET_TWO = LET_ONE.replace('''end Kolmogorov
''', '''/-- doc -/
theorem lam (n : ℕ) : let m := n + 1
    m ≠ 0 := by simp

end Kolmogorov
''')


# Two theorems whose statements continue on a line that opens an absolute
# value: the leading `|` must not be read as a pattern-matching equation.
ABS_ONE = '''\
import Mathlib

namespace Kolmogorov

/-- doc -/
theorem mu (n : ℤ) :
    |n| ≤ |n| := le_refl _

end Kolmogorov
'''

ABS_TWO = ABS_ONE.replace('''end Kolmogorov
''', '''/-- doc -/
theorem nu (n : ℤ) :
    |n + 1| ≤ |n + 1| := le_refl _

end Kolmogorov
''')


# A definition duplicated in two namespaces, with the arguments of the copy
# that goes away written in the other order, and a theorem about each copy.
MERGE_BEFORE = """\
import Mathlib

namespace Kolmogorov

namespace Short

/-- the survivor -/
def padBits (s : List Bool) (n : ℕ) : List Bool := s ++ List.replicate n false

/-- doc -/
theorem padBits_length (s : List Bool) (n : ℕ) :
    (padBits s n).length = s.length + n := by simp [padBits]

end Short

namespace Omega

/-- the copy that goes away -/
def padBits (n : ℕ) (s : List Bool) : List Bool := s ++ List.replicate n false

/-- doc -/
theorem padBits_nil (n : ℕ) :
    padBits n [] = List.replicate n false := by simp [padBits]

end Omega

end Kolmogorov
"""

# After the merge: one definition, the `Omega` theorem restated in terms of it.
MERGE_AFTER = """\
import Mathlib

namespace Kolmogorov

namespace Short

/-- the survivor -/
def padBits (s : List Bool) (n : ℕ) : List Bool := s ++ List.replicate n false

/-- doc -/
theorem padBits_length (s : List Bool) (n : ℕ) :
    (padBits s n).length = s.length + n := by simp [padBits]

end Short

namespace Omega

open Short

/-- doc -/
theorem padBits_nil (n : ℕ) :
    padBits [] n = List.replicate n false := by simp [padBits]

end Omega

end Kolmogorov
"""

MERGE_TABLE = ('deleted_def\tsurvivor_def\tequality_lemma\targument_map\n'
               'Kolmogorov.Omega.padBits\tKolmogorov.Short.padBits\t'
               'Kolmogorov.Omega.padBits_eq_padBits\t1,0\n')


# A statement whose reference had to be disambiguated with `_root_.`, and a
# rename between copies whose binder names are Greek.
ROOT_BEFORE = """\
import Mathlib

namespace Kolmogorov

/-- doc -/
theorem rho (hα : (0 : ℕ) = 0) : Nat.succ 0 = 1 := rfl

end Kolmogorov
"""

ROOT_AFTER = """\
import Mathlib

namespace Kolmogorov

/-- doc -/
theorem rho (hα : (0 : ℕ) = 0) : _root_.Nat.succ 0 = 1 := rfl

end Kolmogorov
"""

EQUATIONS_BEFORE = """\
import Mathlib

namespace Kolmogorov

/-- doc -/
theorem nodup_eraseDups_bitString : ∀ (l : List (List Bool)), l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    exact absurd rfl (by simp)
  termination_by l => l.length

/-- doc -/
theorem abs_bar (x : ℤ) : 0 ≤ x
    |x| := by
  exact abs_nonneg x

end Kolmogorov
"""

EQUATIONS_AFTER = """\
import Mathlib

namespace Kolmogorov

/-- doc -/
theorem nodup_eraseDups_bitString : ∀ (l : List (List Bool)), l.eraseDups.Nodup :=
  nodup_eraseDups_list

/-- doc -/
theorem abs_bar (x : ℤ) : 0 ≤ x
    |x| := by
  positivity

end Kolmogorov
"""

EQUATIONS_CHANGED = EQUATIONS_AFTER.replace(
    'theorem abs_bar (x : ℤ) : 0 ≤ x', 'theorem abs_bar (x : ℤ) : 0 < x')


GREEK_BEFORE = """\
import Mathlib

namespace Kolmogorov

/-- doc -/
theorem sigma_add {α β : ℕ} (hα : α = 0) (hβ : β = 0) : α + β = 0 := by
  simp [hα, hβ]

end Kolmogorov
"""

GREEK_AFTER = """\
import Mathlib

namespace Kolmogorov

namespace ComputableReals

/-- doc -/
theorem sigma_add {a b : ℕ} (ha : a = 0) (hb : b = 0) : a + b = 0 := by
  simp [ha, hb]

end ComputableReals

end Kolmogorov
"""

GREEK_TABLE = ('Kolmogorov.sigma_add\tKolmogorov.ComputableReals.sigma_add\t'
               'A.lean\tpublic\n')



# A public theorem and a private helper, for the recorded re-cut table.
RECUT_BEFORE = """\
import Mathlib

namespace Kolmogorov

/-- doc -/
theorem omicron (n : ℕ) (h : n = 0) : n + 1 = 1 := by simp [h]

/-- doc -/
private theorem piHelper (n : ℕ) : n + 0 = n := by simp

end Kolmogorov
"""

# `omicron` restated: one binder more.
RECUT_RESTATED = RECUT_BEFORE.replace('theorem omicron (n : ℕ) (h : n = 0)',
                                      'theorem omicron (n : ℕ) (k : ℕ) (h : n = 0)')

# `piHelper` inlined away.
RECUT_DELETED = RECUT_BEFORE.replace("""/-- doc -/
private theorem piHelper (n : ℕ) : n + 0 = n := by simp

""", '')

RECUT_HEAD = 'fqn\tkind\treason\tvisibility\n'

def main() -> int:
    # 1. a pure split: every declaration keeps its fully qualified name
    out = scenario({'Big.lean': BIG},
                   {'A.lean': SPLIT_A, 'B.lean': SPLIT_B})
    expect('split preserves fully qualified names', out, problems=0, moved=4,
           dups=0, underscores=0)

    # 2. an underscore rename inside a split
    out = scenario({'Big.lean': BIG},
                   {'A.lean': SPLIT_A.replace('(h : n = 0)', '(_h : n = 0)'),
                    'B.lean': SPLIT_B})
    expect('underscore rename reported, not a problem', out, problems=0,
           underscores=1, contains=['UNDERSCORED Kolmogorov.SUV.alpha'])

    # 3. a genuine header change is a problem
    out = scenario({'Big.lean': BIG},
                   {'A.lean': SPLIT_A.replace('(h : n = 0)',
                                              '(h : n = 0) (k : ℕ)'),
                    'B.lean': SPLIT_B})
    expect('added binder is a problem', out, problems=1,
           contains=['HEADER CHANGED Kolmogorov.SUV.alpha'])

    # 4. a deleted declaration is a problem, and is not paired with an
    #    unrelated survivor
    out = scenario({'Big.lean': BIG},
                   {'A.lean': SPLIT_A,
                    'B.lean': SPLIT_B.replace('''@[simp]
theorem gamma (m : ℕ) : m + 0 = m := by simp

''', '')})
    expect('deleted declaration is a problem', out, problems=1, dups=0,
           contains=['MISSING DECL Kolmogorov.SUV.Ch01.gamma'],
           absent=['DUPLICATE REMOVED'])

    # 5. an exact-duplicate theorem: same statement, different proof and
    #    different name -> a duplicate deletion, not a problem
    dup_before = BIG.replace('def delta : ℕ := 3',
                             'theorem deltaCopy (m : ℕ) : m + 0 = m := by\n'
                             '  omega\n\ndef delta : ℕ := 3')
    out = scenario({'Big.lean': dup_before},
                   {'A.lean': SPLIT_A, 'B.lean': SPLIT_B})
    expect('duplicate theorem deletion is listed, not a problem', out,
           problems=0, dups=1,
           contains=['DUPLICATE REMOVED Kolmogorov.deltaCopy'
                     ' (Big.lean) -> Kolmogorov.SUV.Ch01.gamma (B.lean)'])

    # 6. two definitions of the same type but different values are not
    #    duplicates of each other
    def_before = BIG.replace('def delta : ℕ := 3',
                             'def delta : ℕ := 3\n\ndef epsilon : ℕ := 4')
    out = scenario({'Big.lean': def_before},
                   {'A.lean': SPLIT_A, 'B.lean': SPLIT_B})
    expect('same-type definitions are not duplicates', out, problems=1,
           dups=0, contains=['MISSING DECL Kolmogorov.epsilon'],
           absent=['DUPLICATE REMOVED'])

    # 7. a definition copied verbatim under another name may be deduplicated
    def_before = BIG.replace('def delta : ℕ := 3',
                             'def delta : ℕ := 3\n\ndef deltaCopy : ℕ := 3')
    out = scenario({'Big.lean': def_before},
                   {'A.lean': SPLIT_A, 'B.lean': SPLIT_B})
    expect('verbatim duplicate definition is listed, not a problem', out,
           problems=0, dups=1,
           contains=['DUPLICATE REMOVED Kolmogorov.deltaCopy'
                     ' (Big.lean) -> Kolmogorov.delta (B.lean)'])

    # 8. an unchanged tree compares clean
    out = scenario({'Big.lean': BIG}, {'Big.lean': BIG})
    expect('identical trees compare clean', out, problems=0, moved=0)

    # 9. `end` of a named section must not close the enclosing namespace: a
    #    declaration after it keeps its fully qualified name
    out = scenario({'Big.lean': BIG},
                   {'Big.lean': BIG.replace('end Basics', 'end Basics\n\n'
                                            'theorem zeta : True := trivial')})
    expect('a section end does not pop the namespace', out, problems=0,
           absent=['MISSING DECL'])

    # 10. the same split, but between file names that exist in both trees:
    #     the namespace stack has to be tracked per file, not carried over
    out = scenario({'A.lean': BIG, 'B.lean': 'import Mathlib\n'},
                   {'A.lean': SPLIT_A, 'B.lean': SPLIT_B})
    expect('split between pre-existing file names', out, problems=0, moved=3,
           dups=0)

    # 11. two theorems whose written headers are token-identical but whose
    #     `variable` contexts differ are not duplicates of each other
    out = scenario({'C.lean': CTX_TWO}, {'C.lean': CTX_ONE})
    expect('different variable contexts are not duplicates', out, problems=1,
           dups=0, contains=['MISSING DECL Kolmogorov.eta'],
           absent=['DUPLICATE REMOVED'])

    # 12. the same two theorems in the *same* context are duplicates
    out = scenario({'C.lean': CTX_TWO.replace('variable (n : ℕ)',
                                              'variable {n : ℕ}')},
                   {'C.lean': CTX_ONE})
    expect('equal variable contexts make a duplicate', out, problems=0,
           dups=1, contains=['DUPLICATE REMOVED Kolmogorov.eta'])

    # 13. an `omit ... in` prefix is part of the statement
    out = scenario({'D.lean': OMIT_TWO}, {'D.lean': OMIT_ONE})
    expect('an omit prefix is part of the statement', out, problems=1,
           dups=0, contains=['MISSING DECL Kolmogorov.theta'],
           absent=['DUPLICATE REMOVED'])

    # 14. a statement that binds a `let` is compared past the binding
    out = scenario({'E.lean': LET_TWO}, {'E.lean': LET_ONE})
    expect('a let-binding does not truncate the statement', out, problems=1,
           dups=0, contains=['MISSING DECL Kolmogorov.lam'],
           absent=['DUPLICATE REMOVED'])

    # 15. a leading `|` in a theorem statement is an absolute value
    out = scenario({'F.lean': ABS_TWO}, {'F.lean': ABS_ONE})
    expect('an absolute value does not truncate the statement', out,
           problems=1, dups=0, contains=['MISSING DECL Kolmogorov.nu'],
           absent=['DUPLICATE REMOVED'])

    # 16. `lemma` and `theorem` declare the same thing
    out = scenario({'Big.lean': BIG},
                   {'Big.lean': BIG.replace('theorem gamma', 'lemma gamma')})
    expect('lemma and theorem are the same declaration', out, problems=0,
           dups=0, absent=['HEADER CHANGED'])

    # 17. `Nat` and `ℕ` name the same type, `Nat.bits` is untouched
    nat_before = BIG.replace('theorem gamma (m : ℕ) : m + 0 = m := by simp',
                             'theorem gamma (m : Nat) : m + 0 = m := by simp')
    out = scenario({'Big.lean': nat_before}, {'Big.lean': BIG})
    expect('Nat and ℕ are the same type', out, problems=0, dups=0,
           absent=['HEADER CHANGED'])

    # 18. a changed *qualified* name is still a problem
    out = scenario({'Big.lean': BIG},
                   {'Big.lean': BIG.replace('m + 0 = m', 'Nat.succ m ≠ 0')})
    expect('a changed statement is still a problem', out, problems=1,
           contains=['HEADER CHANGED Kolmogorov.SUV.Ch01.gamma'])

    # 19. a section instance binder that mentions only re-bound variables is
    #     not in force in the declaration, so moving a self-contained lemma
    #     into such a section does not change its statement
    out = scenario({'G.lean': INST_PLAIN}, {'G.lean': INST_SECTION})
    expect('a shadowed instance binder is not part of the statement', out,
           problems=0, absent=['HEADER CHANGED'])


    # 20. a definition merge: the deleted copy is reported as merged, and the
    #     theorem that was restated in terms of the survivor -- with the
    #     recorded argument map applied -- is not a changed statement
    out = scenario({'M.lean': MERGE_BEFORE}, {'M.lean': MERGE_AFTER},
                   tables={'merges.tsv': MERGE_TABLE},
                   extra_args=('--definition-merges', 'merges.tsv'))
    expect('a definition merge rewrites references and their arguments', out,
           problems=0, merged=1,
           contains=['DEFINITION MERGED Kolmogorov.Omega.padBits '
                     '-> Kolmogorov.Short.padBits'],
           absent=['HEADER CHANGED'])

    # 21. without the table the same tree is a changed statement
    out = scenario({'M.lean': MERGE_BEFORE}, {'M.lean': MERGE_AFTER})
    expect('a definition merge without the table is a problem', out,
           problems=2, merged=0,
           contains=['HEADER CHANGED Kolmogorov.Omega.padBits_nil',
                     'MISSING DECL Kolmogorov.Omega.padBits'])

    # 22. a real change to a statement about a merged definition is still a
    #     problem, table or no table
    broken = MERGE_AFTER.replace('padBits [] n = List.replicate n false',
                                 'padBits [] n = List.replicate n true')
    out = scenario({'M.lean': MERGE_BEFORE}, {'M.lean': broken},
                   tables={'merges.tsv': MERGE_TABLE},
                   extra_args=('--definition-merges', 'merges.tsv'))
    expect('a genuine change under a definition merge is a problem', out,
           problems=1, merged=1,
           contains=['HEADER CHANGED Kolmogorov.Omega.padBits_nil'])


    # 23. `_root_.` only says which constant a name resolves to
    out = scenario({'R.lean': ROOT_BEFORE}, {'R.lean': ROOT_AFTER})
    expect('a _root_ prefix is not a changed statement', out, problems=0,
           absent=['HEADER CHANGED'])

    # 24. a rename whose copies differ only in Greek binder names
    out = scenario({'A.lean': GREEK_BEFORE}, {'A.lean': GREEK_AFTER},
                   tables={'renames.tsv': GREEK_TABLE},
                   extra_args=('--renames', 'renames.tsv'))
    expect('Greek binder names are alpha-equivalent under a rename', out,
           problems=0,
           contains=['RENAMED Kolmogorov.sigma_add'])


    # 25. the equations of a pattern-matching *proof* are the proof, not the
    #     statement: re-deriving such a theorem from a general lemma is not a
    #     changed statement, while a line of the statement that merely starts
    #     with `|` (an absolute value) still belongs to the header
    out = scenario({'E.lean': EQUATIONS_BEFORE}, {'E.lean': EQUATIONS_AFTER})
    expect('equation alternatives of a theorem are its proof', out,
           problems=0, absent=['HEADER CHANGED'])

    # 26. and a real change to a statement whose header spans a `|…|` line is
    #     still reported
    out = scenario({'E.lean': EQUATIONS_BEFORE}, {'E.lean': EQUATIONS_CHANGED})
    expect('a changed statement on an absolute-value line is a problem', out,
           problems=1, contains=['HEADER CHANGED Kolmogorov.abs_bar'])

    # 27. a header change with no row in the re-cut table is a problem, even
    #     when the table names some other declaration
    out = scenario({'N.lean': RECUT_BEFORE}, {'N.lean': RECUT_RESTATED},
                   tables={'recut.tsv': RECUT_HEAD +
                           'Kolmogorov.piHelper\tdeleted\twas inlined\tprivate\n'},
                   extra_args=('--recut', 'recut.tsv'))
    expect('a restatement with no recut row is a problem', out, problems=1,
           contains=['HEADER CHANGED Kolmogorov.omicron'],
           absent=['RECORDED RESTATEMENT'])

    # 28. a `deleted` row does not license a restatement
    out = scenario({'N.lean': RECUT_BEFORE}, {'N.lean': RECUT_RESTATED},
                   tables={'recut.tsv': RECUT_HEAD +
                           'Kolmogorov.omicron\tdeleted\tinlined into its caller\tpublic\n'},
                   extra_args=('--recut', 'recut.tsv'))
    expect('a deleted row does not license a restatement', out, problems=1,
           contains=['HEADER CHANGED Kolmogorov.omicron'],
           absent=['RECORDED RESTATEMENT'])

    # 29. and a `restated` row does not license a deletion
    out = scenario({'N.lean': RECUT_BEFORE}, {'N.lean': RECUT_DELETED},
                   tables={'recut.tsv': RECUT_HEAD +
                           'Kolmogorov.piHelper\trestated\tone binder dropped\tprivate\n'},
                   extra_args=('--recut', 'recut.tsv'))
    expect('a restated row does not license a deletion', out, problems=1,
           contains=['MISSING DECL Kolmogorov.piHelper'],
           absent=['RECORDED DELETION'])

    # 30. a recorded restatement is not a problem, and the header diff is
    #     still printed under it so a reviewer sees what changed
    out = scenario({'N.lean': RECUT_BEFORE}, {'N.lean': RECUT_RESTATED},
                   tables={'recut.tsv': RECUT_HEAD +
                           'Kolmogorov.omicron\trestated\tthe k binder is new\tpublic\n'},
                   extra_args=('--recut', 'recut.tsv'))
    expect('a recorded restatement prints its diff and is not a problem', out,
           problems=0,
           contains=['RECORDED RESTATEMENT Kolmogorov.omicron',
                     "'h' -> 'k'", 'token count'],
           absent=['HEADER CHANGED'])

    # 31. a row whose visibility disagrees with the base revision is a
    #     problem and licenses nothing
    out = scenario({'N.lean': RECUT_BEFORE}, {'N.lean': RECUT_RESTATED},
                   tables={'recut.tsv': RECUT_HEAD +
                           'Kolmogorov.omicron\trestated\tthe k binder is new\tprivate\n'},
                   extra_args=('--recut', 'recut.tsv'))
    expect('a wrong visibility is a problem', out, problems=2,
           contains=['RECUT VISIBILITY Kolmogorov.omicron',
                     'HEADER CHANGED Kolmogorov.omicron'],
           absent=['RECORDED RESTATEMENT'])

    # 32. and so is a row without the visibility column at all
    out = scenario({'N.lean': RECUT_BEFORE}, {'N.lean': RECUT_RESTATED},
                   tables={'recut.tsv': RECUT_HEAD +
                           'Kolmogorov.omicron\trestated\tthe k binder is new\n'},
                   extra_args=('--recut', 'recut.tsv'))
    expect('a recut row without a visibility column is a problem', out,
           problems=2,
           contains=['RECUT ROW Kolmogorov.omicron',
                     'HEADER CHANGED Kolmogorov.omicron'],
           absent=['RECORDED RESTATEMENT'])

    if FAILURES:
        print(f'\n{len(FAILURES)} failing case(s)')
        return 1
    print('\nall cases pass')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
