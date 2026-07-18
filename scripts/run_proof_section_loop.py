#!/usr/bin/env python3
"""Prepare/run sectionwise Lean proof implementation loops (algstat edition).

KolmogorovMathlib restricted-type (VS40 section 6) loop:

    Gemini -> Codex -> Opus -> Codex -> Aristotle

Every Nth iteration (default: 5) is strategic and plans the next N-1 proof
iterations. Aristotle receives a strategic packet on those iterations too.

The same runner supports proof implementation and post-proof polishing. In
polishing mode the theorem statements are frozen: agents reduce elaboration
cost, remove local heartbeat overrides and warnings, and improve Mathlib style
without introducing `sorry`s or weakening the formal API.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import datetime as dt
import filecmp
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import textwrap
import time
import traceback
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PROOF_LOOP_DIR = ROOT / "proof_loop"
SECTIONS_PATH = PROOF_LOOP_DIR / "sections.json"
DEFAULT_RUNS_DIR = ROOT / "proof_loop_runs"
DEFAULT_STOP_FILE = PROOF_LOOP_DIR / "PAUSE"
CODEX_MODEL = os.environ.get("KOLMOGOROV_CODEX_MODEL", "gpt-5.6-sol")
CODEX_EFFORT = os.environ.get("KOLMOGOROV_CODEX_EFFORT", "xhigh")
DEFAULT_STABILITY_LAB_ROOT = Path(
    os.environ.get(
        "HARPER_STABILITY_LAB_ROOT",
        str(ROOT.parent / "harper-stability-lab")
        if (ROOT.parent / "harper-stability-lab").exists()
        else "/home/lesha/harper-stability-lab",
    )
)


def utc_stamp() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def read_text(path: Path, max_chars: int | None = None) -> str:
    if not path.exists():
        return f"[missing: {path}]\n"
    text = path.read_text(encoding="utf-8", errors="replace")
    if max_chars is not None and len(text) > max_chars:
        return text[:max_chars] + f"\n\n[TRUNCATED at {max_chars} chars from {path}]\n"
    return text


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def section_stop_file(stop_file: Path, section: dict[str, Any]) -> Path:
    """Return the soft-pause file for one section.

    With the default global stop file `proof_loop/PAUSE`, section `P4...` is
    paused by `proof_loop/PAUSE.P4...`.  If the caller overrides
    `--stop-file`, the same suffix convention is used next to that file.
    """
    return stop_file.with_name(f"{stop_file.name}.{section['id']}")


def pause_status(args: argparse.Namespace, section: dict[str, Any]) -> dict[str, str] | None:
    """Return pause metadata if the global or section pause file exists."""
    if args.stop_file.exists():
        return {"scope": "global", "file": str(args.stop_file)}
    local_stop = section_stop_file(args.stop_file, section)
    if local_stop.exists():
        return {"scope": "section", "file": str(local_stop)}
    return None


def mark_paused(manifest: dict[str, Any], status: dict[str, str], **extra: Any) -> None:
    manifest["status"] = "paused"
    manifest["paused_at"] = utc_now()
    manifest["pause_scope"] = status["scope"]
    manifest["pause_file"] = status["file"]
    manifest.update(extra)


def load_json(path: Path, default: Any) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return default


def load_sections() -> list[dict[str, Any]]:
    return json.loads(SECTIONS_PATH.read_text(encoding="utf-8"))


def count_sorries_at(root: Path) -> int:
    text = scan_sorries_at(root)
    if text.startswith("("):
        return 0
    return sum(1 for line in text.splitlines() if line.strip())


def count_section_sorries_at(root: Path, section: dict[str, Any]) -> int:
    total = 0
    for path in iter_candidate_files(root, section):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        total += text.count("sorry")
        total += text.count("sorryAx")
    return total


def rel_file_block(root: Path, paths: list[str], max_each: int = 50000) -> str:
    chunks: list[str] = []
    for rel in paths:
        path = root / rel
        suffix = "lean" if path.suffix == ".lean" else "text"
        chunks.append(f"\n\n## FILE: {rel}\n\n```{suffix}\n")
        chunks.append(read_text(path, max_each).strip())
        chunks.append("\n```\n")
    return "".join(chunks)


def latest_file(pattern_root: Path, glob: str) -> Path | None:
    files = sorted(pattern_root.glob(glob), key=lambda p: p.stat().st_mtime if p.exists() else 0)
    return files[-1] if files else None


def collect_context(section: dict[str, Any], root: Path) -> str:
    coverage = read_text(root / "COVERAGE.md", 20000)
    readme = read_text(root / "README.md", 8000)
    if section.get("workflow") == "polish":
        target_files = "\n".join(f"- `{path}`" for path in section.get("files", []))
        return f"""
# Repository Context

Current worktree root: `{root}`

The project is complete and sorry-free at the baseline. Use `COVERAGE.md` to
identify public declarations, but inspect exact proof bodies directly in the
worktree instead of relying on copied source excerpts.

## Primary polishing files

{target_files}

## COVERAGE.md

```markdown
{coverage.strip()}
```

## README.md

```markdown
{readme.strip()}
```
"""

    plan = read_text(root / "PLAN_RESTRICTED_TYPE.md", 45000)
    source6 = read_text(PROOF_LOOP_DIR / "SOURCE_SECTION6.md", 70000)
    prior_aristotle = read_text(PROOF_LOOP_DIR / "PRIOR_ARISTOTLE_ARTIFACTS.md", 12000)
    return f"""
# Repository Context

Current worktree root: `{root}`

Read `COVERAGE.md` FIRST: build on the theorems named there, never re-derive
them. Conventions: paper-facing statements against `StandardMachine`
(`KolmogorovMathlib/Interface/StandardMachine.lean`); lists/tuples via
`listCode` (`KolmogorovMathlib/Encoding/Tuples.lean`); new general `Primrec`
lemmas go in `KolmogorovMathlib/Foundation/PrimrecExtras.lean`; slack via
`logSlack` + `SlackArith` combinators at one visible budget; slack constants
are quantified BEFORE the string (`exists c, forall x n ...`).

## COVERAGE.md

```markdown
{coverage.strip()}
```

## README.md

```markdown
{readme.strip()}
```

## Prior Aristotle artifacts

```markdown
{prior_aristotle.strip()}
```

## Formalization plan (PLAN_RESTRICTED_TYPE.md)

```markdown
{plan.strip()}
```

## Source: VS40 survey, section 6 (verbatim excerpt)

```tex
{source6.strip()}
```

# Section Files
{rel_file_block(root, section["files"])}
"""


def scan_sorries() -> str:
    return scan_sorries_at(ROOT)


def scan_section_sorries_at(root: Path, section: dict[str, Any]) -> str:
    lines: list[str] = []
    for path in iter_candidate_files(root, section):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        rel = path.relative_to(root)
        for idx, line in enumerate(text.splitlines(), 1):
            if re.search(r"\bsorry\b|sorryAx", line):
                lines.append(f"{rel}:{idx}:{line}")
    return "\n".join(lines) if lines else "(no section sorries found)"


def scan_sorries_at(root: Path) -> str:
    cmd = [
        "bash",
        "-lc",
        "if command -v rg >/dev/null 2>&1; then "
        "rg -n '\\bsorry\\b|sorryAx' KolmogorovMathlib || true; "
        "else grep -RInE '\\bsorry\\b|sorryAx' KolmogorovMathlib || true; fi",
    ]
    try:
        cp = subprocess.run(cmd, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
        return cp.stdout.strip() or "(no sorries found)"
    except Exception as exc:
        return f"(sorry scan failed: {type(exc).__name__}: {exc})"


def is_polishing(section: dict[str, Any]) -> bool:
    return section.get("workflow") == "polish"


def scan_polish_debt_at(root: Path) -> str:
    """Return static proof-engineering debt that agents can attack locally."""
    needles = (
        "set_option maxHeartbeats",
        "set_option maxRecDepth",
        "set_option linter.",
    )
    lines: list[str] = []
    source_root = root / "KolmogorovMathlib"
    for path in sorted(source_root.rglob("*.lean")):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        rel = path.relative_to(root)
        for idx, line in enumerate(text.splitlines(), 1):
            stripped = line.strip()
            if any(needle in line for needle in needles) or stripped == "import Mathlib":
                lines.append(f"{rel}:{idx}:{line}")
    return "\n".join(lines) if lines else "(no static polishing debt found)"


def import_pipeline_module():
    os.environ.setdefault("HARPER_LAB_ROOT", str(ROOT))
    scripts_dir = DEFAULT_STABILITY_LAB_ROOT / "scripts"
    if str(scripts_dir) not in sys.path:
        sys.path.insert(0, str(scripts_dir))
    import harper_pipeline  # type: ignore

    return harper_pipeline


def import_pipeline():
    return import_pipeline_module().call_agent_safe


def previous_outputs(iter_dir: Path) -> str:
    chunks: list[str] = []
    for path in sorted(iter_dir.glob("*.md")):
        if path.name.endswith(".prompt.md") or path.name == "aristotle_prompt.md":
            continue
        chunks.append(f"\n\n# PREVIOUS OUTPUT: {path.name}\n\n")
        chunks.append(read_text(path, 50000).strip())
        chunks.append("\n")
    return "".join(chunks).strip() or "(none yet)"


def latest_strategy_outputs(section_dir: Path, before_iteration: int) -> str:
    strategy_dirs: list[Path] = []
    for path in section_dir.glob("iter_*_strategy"):
        try:
            iteration = int(path.name.split("_", 2)[1])
        except Exception:
            continue
        if iteration < before_iteration:
            strategy_dirs.append(path)
    if not strategy_dirs:
        return "(no previous strategy iteration for this section)"
    latest = sorted(strategy_dirs, key=lambda p: p.name)[-1]
    chunks = [f"# LATEST STRATEGY: {latest.name}\n"]
    for name in ["04_codex.md", "03_opus.md", "02_codex.md", "01_gemini.md"]:
        path = latest / name
        if path.exists():
            chunks.append(f"\n\n## {name}\n\n")
            chunks.append(read_text(path, 50000).strip())
    aristotle_log = latest / "aristotle_submit.log"
    if aristotle_log.exists():
        tail = "\n".join(read_text(aristotle_log, 50000).splitlines()[-80:])
        chunks.append("\n\n## Aristotle strategy log tail\n\n```text\n")
        chunks.append(tail)
        chunks.append("\n```\n")
    return "".join(chunks).strip()


def section_header(section: dict[str, Any]) -> str:
    return f"""
# Section

- id: `{section['id']}`
- title: {section['title']}
- module: `{section['module']}`
- targets: {', '.join(f'`{t}`' for t in section.get('targets', []))}
- notes: {section.get('notes', '')}
"""


def polishing_ordinary_prompt(
    stage: str,
    section: dict[str, Any],
    iteration: int,
    context: str,
    previous: str,
    work_root: Path,
) -> str:
    role = {
        "01_gemini": "Gemini, first proof-polishing implementer",
        "02_codex": "Codex, first verifier and repairer",
        "03_opus": "Opus, independent proof-style and performance reviewer",
        "04_codex": "Codex, final verifier and Aristotle-packet curator",
    }[stage]
    stage_task = {
        "01_gemini": (
            "Choose a small coherent batch of current debt and improve it in the "
            "worktree. Start with low-risk local heartbeat overrides or the three "
            "current Lean info suggestions. Refactor the proof rather than merely "
            "raising or relocating a limit. Run targeted builds for every touched module."
        ),
        "02_codex": (
            "Adversarially review Gemini's actual diff. Revert regressions, repair "
            "broken or slower proofs, and continue the same small batch where safe. "
            "Confirm that theorem statements and assumptions are byte-for-byte unchanged."
        ),
        "03_opus": (
            "Independently inspect the resulting proofs for elaboration cost and "
            "Mathlib style. Simplify brittle tactic scripts, remove unnecessary local "
            "options/imports/comments, and test the touched modules. Preserve only "
            "measurable improvements that compile."
        ),
        "04_codex": (
            "Perform the final strict review. Check the complete iteration diff, fix "
            "remaining local issues, run targeted builds and then the full audit when "
            "the batch is stable. Curate exact remaining expensive declarations for "
            "Aristotle, including useful failed approaches from earlier stages."
        ),
    }[stage]
    return f"""
You are {role} in a Lean 4 post-proof polishing iteration.

Iteration: {iteration}. This is an ordinary editing iteration.
Worktree: `{work_root}`

The restricted-family formalization is already complete and kernel-checked.
This iteration must improve implementation quality without changing its
mathematical content. Do not add new milestones or draft new theorems.

{section_header(section)}

# Current static polishing debt

```text
{scan_polish_debt_at(work_root)}
```

# Current `sorry` scan (must remain empty)

```text
{scan_section_sorries_at(work_root, section)}
```

# Previous outputs in this iteration

```markdown
{previous}
```

# Latest strategic polishing plan

```markdown
{latest_strategy_outputs(work_root.parent, iteration)}
```

# Task

{stage_task}

Priorities, in order:
1. Remove local `set_option maxHeartbeats` by making the enclosed proof cheaper.
2. Remove Lean warnings/info suggestions and unnecessary linter suppressions.
3. Narrow broad imports, remove dead helpers and stale implementation commentary.
4. Prefer shorter, robust Mathlib-style proofs when compile time does not regress.

Use targeted `lake env lean <file>` or module builds while editing. Do not launch
repeated blind full builds; the final Codex should run `bash scripts/audit.sh`
once the batch is stable.

Required output:

STATUS: IMPROVED / NO_SAFE_IMPROVEMENT / BUILD_BROKEN / INTERFACE_PROBLEM

## Changes Made
List exact files/declarations and the debt removed.

## Verification
Report targeted builds, full audit if run, and remaining heartbeat count.

## Aristotle Optimization Packet
Give 1-3 exact expensive declarations or style leaves for Aristotle. Include
the existing proof and any tested partial replacement; never create a `sorry`.

## Risks
Report compile-time regressions, statement drift, or reverted attempts.

Hard constraints:
- Zero `sorry`/`sorryAx` before and after every stage.
- No `axiom`, `admit`, `unsafe`, `implemented_by`, or `native_decide`.
- Do not change theorem statements, assumptions, definitions' semantics, or public names.
- Never replace a heartbeat override by a larger/global override or by disabling limits.
- If an attempted cleanup does not compile, revert that attempt before finishing.
- Do not commit, push, or edit files outside the allowed section prefixes.

{context}
"""


def ordinary_prompt(
    stage: str,
    section: dict[str, Any],
    iteration: int,
    context: str,
    previous: str,
    work_root: Path,
) -> str:
    if is_polishing(section):
        return polishing_ordinary_prompt(stage, section, iteration, context, previous, work_root)
    role = {
        "01_gemini": "Gemini, first implementation agent",
        "02_codex": "Codex, first verifier and repairer",
        "03_opus": "Opus, independent proof improver and critic",
        "04_codex": "Codex, final verifier, repairer, and Aristotle-packet preparer",
    }[stage]
    stage_task = {
        "01_gemini": (
            "Try to close or strictly reconstruct one or more `sorry`s in this "
            "section. Edit Lean files in the worktree. If a target is too hard, "
            "replace it only by genuinely smaller named lemmas with precise "
            "`sorry`s. If there are no open sorries, advance to the next "
            "milestone of the global plan (draft its files and sorries)."
        ),
        "02_codex": (
            "Review Gemini's changes. Keep correct progress, reject or revert "
            "unsound edits, repair build/type errors, and then try to close or "
            "strictly reconstruct more `sorry`s yourself. Leave a verified, clearly "
            "diagnosed worktree for Opus, including exact remaining proof gaps and "
            "any mathematical or interface risks that need independent review."
        ),
        "03_opus": (
            "Independently review the complete Gemini and first-Codex result. Keep "
            "only sound progress, repair proof architecture or Lean errors, and "
            "attack the hardest remaining obligations yourself. Prefer compiling "
            "proofs or genuinely smaller exact leaf lemmas over prose suggestions. "
            "Leave the worktree in a state that a final Codex pass can certify."
        ),
        "04_codex": (
            "Perform the final adversarial review of all preceding edits. Inspect "
            "the actual diff, reject or repair unsound shortcuts, close additional "
            "leaves where possible, and run targeted builds plus the full audit as "
            "far as practical. Then curate a clean Aristotle packet containing only "
            "the remaining exact frozen Lean obligations and the useful partial work."
        ),
    }[stage]
    return f"""
You are {role} for a Lean 4 proof implementation iteration.

Iteration: {iteration}

This is an ordinary proof iteration, not the strategic planning iteration.
You may edit files in the isolated worktree below.

GLOBAL GOAL: formalize ALL of VS40 section 6 (descriptions of restricted
type) following `PLAN_RESTRICTED_TYPE.md`. Closing the current `sorry`s is
only the local step. If the sorry scan below is empty, or the current
milestone is essentially closed, ADVANCE TO THE NEXT MILESTONE from the plan
(recommended order: M0 -> M2 -> M4 -> M5; M3 examples in parallel; M6/M7 as
stretch; skip milestones whose theorems already exist): create the next
file(s) under `KolmogorovMathlib/Restricted/` with carefully drafted DRAFT
statements and honest `sorry` leaves, wire them as imports into
`KolmogorovMathlib.lean`, and update `COVERAGE.md`. Statement quality gates:
slack constants quantified before the string; stress-test new predicates on
`fullFamily` and on trivial families; never weaken already-proved statements;
never invent work outside the plan.

Worktree: `{work_root}`

The frozen interface files must not be weakened or casually edited. If you find
a genuine interface contradiction, stop and report `INTERFACE_PROBLEM`; otherwise
work inside the section worker files and local helper lemmas.

{section_header(section)}

# Current `sorry` scan in this worktree

```text
{scan_section_sorries_at(work_root, section)}
```

# Previous outputs in this iteration

```markdown
{previous}
```

# Latest strategic plan for this section

```markdown
{latest_strategy_outputs(work_root.parent, iteration)}
```

# Task

{stage_task}

Required output:

STATUS: IMPLEMENTED / PARTIAL_IMPLEMENTATION / BUILD_BROKEN / BLOCKED_BY_MATH / INTERFACE_PROBLEM

## Changes Made
List exact files and declarations changed.

## Verification
Say whether you ran `lake build`, `bash scripts/audit.sh`, or targeted
`lake env lean ...`; include the relevant result.

## Remaining Sorries
List exact declarations still open in this section and why they are now smaller
or better isolated.

## Aristotle Leaf Packet
State 1-3 remaining leaf obligations that are small enough for Aristotle.
Include theorem statements in Lean-like syntax when possible.

## Risks
List any questionable edits, false shortcuts avoided, or places needing review.

Hard constraints:
- No `axiom`, `admit`, `unsafe`, or `implemented_by`.
- Do not move or rename `sorry` as progress.
- Do not weaken theorem statements.
- Do not edit curated interface statements unless reporting `INTERFACE_PROBLEM`.
- Preserve module boundaries: this section may use interface statements from
  other sections only as hypotheses unless the dependency graph already permits
  the import.

{context}
"""


def polishing_strategy_prompt(
    stage: str,
    section: dict[str, Any],
    iteration: int,
    previous: str,
    span: int,
    work_root: Path,
) -> str:
    role = {
        "01_gemini": "Gemini polishing strategist",
        "02_codex": "Codex first polishing-plan critic",
        "03_opus": "Opus independent performance and style reviewer",
        "04_codex": "Codex final polishing-plan synthesizer",
    }[stage]
    stage_task = {
        "01_gemini": "Group the remaining debt into small dependency-aware batches and estimate build risk.",
        "02_codex": "Check Gemini's plan against the actual declarations, imports, and build hotspots.",
        "03_opus": "Stress-test the plan for theorem drift, elaboration regressions, and non-Mathlib style.",
        "04_codex": "Freeze an executable four-iteration plan with exact files, declarations, and acceptance tests.",
    }[stage]
    return f"""
You are {role} for strategic Lean proof polishing.

Iteration: {iteration}. Plan the next {span} ordinary iterations. Do not edit
the worktree during this strategy iteration.

{section_header(section)}

# Current static polishing debt

```text
{scan_polish_debt_at(work_root)}
```

# Current `sorry` scan (must remain empty)

```text
{scan_section_sorries_at(work_root, section)}
```

# Previous strategy-agent outputs

```markdown
{previous}
```

# Stage-specific task

{stage_task}

Required output:

STATUS: STRATEGY_READY / NO_SAFE_IMPROVEMENT / NEEDS_HUMAN_DECISION

## Best Plan For The Next Four Ordinary Iterations
For each iteration give exact files/declarations, the proposed cheaper proof,
targeted verification, expected heartbeat reduction, and rollback criterion.

## Aristotle Optimization Priority
Rank 3-8 exact declarations where independent proof search could remove a local
heartbeat override or replace a brittle proof without changing the theorem.

## Risks
Flag any proposal that could alter the API, assumptions, semantics, or compile time.

Hard constraints: no edits, no new `sorry`, no theorem weakening, and no plan
whose only effect is moving or increasing a resource override.
"""


def strategy_prompt(
    stage: str,
    section: dict[str, Any],
    iteration: int,
    context: str,
    previous: str,
    span: int,
    work_root: Path,
) -> str:
    if is_polishing(section):
        return polishing_strategy_prompt(stage, section, iteration, previous, span, work_root)
    role = {
        "01_gemini": "Gemini strategy planner",
        "02_codex": "Codex first strategy critic",
        "03_opus": "Opus independent strategy reviewer",
        "04_codex": "Codex final strategy synthesizer",
    }[stage]
    stage_task = {
        "01_gemini": (
            "Propose the next proof plan from the actual declarations and dependency "
            "graph. Identify concrete Lean-sized leaves rather than broad aspirations."
        ),
        "02_codex": (
            "Critique Gemini's plan against the current Lean code. Correct false "
            "assumptions, missing dependencies, and obligations that are too large."
        ),
        "03_opus": (
            "Independently stress-test the proposed strategy mathematically and as "
            "Lean proof engineering. Identify hidden gaps and propose sharper leaves."
        ),
        "04_codex": (
            "Synthesize the final executable plan from all preceding reviews. Freeze "
            "the next ordinary targets and exact Aristotle-sized leaf statements."
        ),
    }[stage]
    return f"""
You are {role} for a strategic Lean proof-planning iteration.

Iteration: {iteration}. This is a strategy iteration. Do not try to solve a
single proof. Plan the next {span} ordinary proof iterations for this section.

{section_header(section)}

# Current `sorry` scan in this section worktree

```text
{scan_section_sorries_at(work_root, section)}
```

# Previous outputs in this iteration

```markdown
{previous}
```

# Stage-specific task

{stage_task}

Required output:

STATUS: STRATEGY_READY / NEEDS_HUMAN_DECISION / INTERFACE_PROBLEM

GLOBAL GOAL: formalize ALL of VS40 section 6 (descriptions of restricted
type) following `PLAN_RESTRICTED_TYPE.md`. Closing the current `sorry`s is
only the local step. If the sorry scan below is empty, or the current
milestone is essentially closed, ADVANCE TO THE NEXT MILESTONE from the plan
(recommended order: M0 -> M2 -> M4 -> M5; M3 examples in parallel; M6/M7 as
stretch; skip milestones whose theorems already exist): create the next
file(s) under `KolmogorovMathlib/Restricted/` with carefully drafted DRAFT
statements and honest `sorry` leaves, wire them as imports into
`KolmogorovMathlib.lean`, and update `COVERAGE.md`. Statement quality gates:
slack constants quantified before the string; stress-test new predicates on
`fullFamily` and on trivial families; never weaken already-proved statements;
never invent work outside the plan.

## Section Diagnosis
What is the real dependency shape of this section (relative to the global plan)?

## Next {span} Iterations
For each of the next {span} ordinary iterations, give:
- target declaration;
- proof idea;
- expected leaf lemmas for Aristotle;
- success criterion.

## Parallelization Notes
Which subtargets can be worked independently?

## Stop Conditions
When should the loop pause for human review?

Hard constraints:
- No interface weakening.
- No hidden dependency on unproved worker proofs except through explicit
  statement hypotheses.
- Prefer small leaf lemmas with stable Lean statements.

{context}
"""


def write_aristotle_packet(
    section: dict[str, Any],
    iteration: int,
    iter_dir: Path,
    mode: str,
    work_root: Path,
) -> Path:
    project_label = f"KCLean_{section['id']}_iter{iteration:03d}_{mode}"
    if is_polishing(section) and mode == "strategy":
        prompt = f"""
You are Aristotle reviewing a strategic Lean 4 proof-polishing iteration.

Project label: `{project_label}`
Project directory: `{work_root}`
Section: `{section['id']}` / {section['title']}

Do not edit proofs in this strategic round. Review the four agents' plans and
produce the safest next-four-iteration optimization plan. The existing theorem
statements and semantics are frozen.

# Current static polishing debt

```text
{scan_polish_debt_at(work_root)}
```

# Strategy agent outputs

```markdown
{previous_outputs(iter_dir)}
```

Rank exact declarations where a cheaper equivalent proof is plausible, and
state targeted build checks and rollback criteria. Never propose adding,
moving, or increasing a heartbeat override.
"""
    elif is_polishing(section):
        prompt = f"""
You are Aristotle optimizing an already-complete Lean 4 formalization.

Project label: `{project_label}`
Project directory: `{work_root}`
Section: `{section['id']}` / {section['title']}

The project currently builds with zero `sorry`. Improve one or more exact
proofs selected by the previous agents: remove a local heartbeat override,
reduce elaboration cost, resolve an info/warning, or replace a brittle tactic
script with a robust Mathlib-style proof. Edit the submitted project and return
all useful partial work even if every optimization does not succeed.

Hard constraints:
- Keep every theorem statement, assumption, public name, and definition's semantics unchanged.
- Keep the project free of `sorry`, `sorryAx`, `axiom`, `admit`, `unsafe`,
  `implemented_by`, and `native_decide`.
- Never raise, globalize, disable, or merely relocate a resource limit.
- Revert any attempted edit that does not compile.

# Current static polishing debt

```text
{scan_polish_debt_at(work_root)}
```

# Agent outputs and exact optimization packet

```markdown
{previous_outputs(iter_dir)}
```
"""
    elif mode == "strategy":
        prompt = f"""
You are Aristotle working on strategic proof planning for a Lean 4 project.

Project label: `{project_label}`
Project directory: `{work_root}`
Section: `{section['id']}` / {section['title']}
Module: `{section['module']}`

This is strategy iteration {iteration}. Do not try to solve a large proof in
one shot. Instead, review the preceding strategy agents and produce the
best next-four-iteration plan for this section, with leaf obligations suitable
for future Aristotle submissions.

Required output:

STATUS: STRATEGY_READY / NEEDS_HUMAN_DECISION / INTERFACE_PROBLEM

## Best Plan For The Next Four Ordinary Iterations
For each iteration give:
- target declaration(s);
- exact Lean file(s);
- mathematical proof idea;
- leaf lemmas that look appropriate for Aristotle;
- expected success criterion.

## Aristotle Leaf Priority
Rank the 3-8 leaf obligations that Aristotle should attack first.

## Risks
Name any statement that looks too large, too vague, or badly shaped for
Aristotle.

# Current `sorry` scan

```text
{scan_section_sorries_at(work_root, section)}
```

# Strategy agent outputs

```markdown
{previous_outputs(iter_dir)}
```
"""
    else:
        prompt = f"""
You are Aristotle working on a Lean 4 project.

Project label: `{project_label}`
Project directory: `{work_root}`
Section: `{section['id']}` / {section['title']}
Module: `{section['module']}`

The previous agents selected leaf proof targets. Use the context below and try
to prove one or more small Lean obligations without changing the frozen theorem
statements.

Hard constraints:
- No `axiom`, `admit`, `unsafe`, or `implemented_by`.
- Do not weaken existing statements.
- Prefer proving leaf lemmas exactly as stated or curated by the final Codex in
  `04_codex.md`.

# Current `sorry` scan

```text
{scan_section_sorries_at(work_root, section)}
```

# Agent outputs

```markdown
{previous_outputs(iter_dir)}
```
"""
    prompt_path = iter_dir / "aristotle_prompt.md"
    write_text(prompt_path, textwrap.dedent(prompt).strip() + "\n")
    submit = f"""#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess

source_dir = Path({str(work_root)!r})
project_label = {project_label!r}
project_dir = Path({str(iter_dir / project_label)!r})
prompt = Path({str(prompt_path)!r}).read_text(encoding="utf-8")
destination = Path({str(iter_dir / "aristotle_result.tar.gz")!r})

def ignore(_dir, names):
    ignored = {{
        ".git",
        ".lake",
        "proof_loop_runs",
        "proof_loop_readiness",
        "interface_part_reviews",
        "reviews",
        "__pycache__",
    }}
    return {{
        name for name in names
        if name in ignored or name.endswith(".olean") or name.endswith(".ilean") or name.endswith(".pyc")
    }}

if project_dir.exists():
    shutil.rmtree(project_dir)
shutil.copytree(source_dir, project_dir, ignore=ignore)
(project_dir / "ARISTOTLE_PROJECT_LABEL.md").write_text(
    f"# {{project_label}}\\n\\nThis is an Aristotle submission copy for section `{section['id']}`, "
    f"iteration `{iteration}`, mode `{mode}`.\\n",
    encoding="utf-8",
)

cmd = [
    "/home/lesha/.local/bin/aristotle",
    "submit",
    prompt,
    "--project-dir",
    str(project_dir),
    "--wait",
    "--destination",
    str(destination),
]
print("project_label:", project_label, flush=True)
print("command:", " ".join(cmd[:2] + ["<prompt>", "--project-dir", str(project_dir), "--wait", "--destination", str(destination)]), flush=True)
raise SystemExit(subprocess.run(cmd).returncode)
"""
    submit_path = iter_dir / "submit_aristotle.py"
    write_text(submit_path, submit)
    return prompt_path


def submit_aristotle(iter_dir: Path, timeout_seconds: int) -> dict[str, Any]:
    script = iter_dir / "submit_aristotle.py"
    if not script.exists():
        return {"submitted": False, "reason": "missing submit_aristotle.py"}
    cp = subprocess.run(
        ["python3", str(script)],
        cwd=iter_dir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout_seconds + 1800,
    )
    write_text(iter_dir / "aristotle_submit.log", cp.stdout)
    archive = iter_dir / "aristotle_result.tar.gz"
    interrupted = "Connection to server was interrupted" in cp.stdout
    project_id, task_id = parse_aristotle_ids(cp.stdout)
    if (interrupted or not archive.exists()) and project_id and task_id:
        followup = wait_for_aristotle_and_download(iter_dir, project_id, task_id, archive, timeout_seconds=timeout_seconds)
        return {
            "submitted": True,
            "returncode": followup["returncode"],
            "initial_returncode": cp.returncode,
            "interrupted": interrupted,
            "project_id": project_id,
            "task_id": task_id,
            "followup": followup,
        }
    if interrupted or not archive.exists():
        return {
            "submitted": True,
            "returncode": 1,
            "initial_returncode": cp.returncode,
            "interrupted": interrupted,
            "reason": "aristotle_wait_interrupted_or_missing_archive",
            "project_id": project_id,
            "task_id": task_id,
            "archive_exists": archive.exists(),
        }
    return {"submitted": True, "returncode": cp.returncode, "project_id": project_id, "task_id": task_id}


def parse_aristotle_ids(output: str) -> tuple[str | None, str | None]:
    project_id = None
    task_id = None
    for line in output.splitlines():
        line = line.strip()
        if line.startswith("Project created:"):
            project_id = line.split(":", 1)[1].strip()
        elif line.startswith("Project:"):
            project_id = line.split(":", 1)[1].strip()
        elif line.startswith("Task:"):
            task_id = line.split(":", 1)[1].strip()
    return project_id, task_id


def aristotle_task_status(project_id: str, task_id: str) -> tuple[str, str]:
    rc, out = command_output(
        ["/home/lesha/.local/bin/aristotle", "tasks", project_id, "--limit", "5"],
        ROOT,
        timeout=60,
    )
    if rc != 0:
        return "UNKNOWN", out
    for line in out.splitlines():
        if task_id in line:
            parts = line.split()
            if parts:
                return parts[-1], out
    return "UNKNOWN", out


def wait_for_aristotle_and_download(
    iter_dir: Path,
    project_id: str,
    task_id: str,
    archive: Path,
    *,
    timeout_seconds: int = 7200,
    poll_seconds: int = 300,
) -> dict[str, Any]:
    log_path = iter_dir / "aristotle_followup.log"
    started = time.monotonic()
    last_status = "UNKNOWN"
    while time.monotonic() - started < timeout_seconds:
        status, out = aristotle_task_status(project_id, task_id)
        last_status = status
        with log_path.open("a", encoding="utf-8") as handle:
            handle.write(f"\n[{utc_now()}] status={status}\n")
            handle.write(out)
            if not out.endswith("\n"):
                handle.write("\n")
        if status not in {"IN_PROGRESS", "QUEUED", "UNKNOWN"}:
            break
        time.sleep(poll_seconds)
    if last_status in {"IN_PROGRESS", "QUEUED", "UNKNOWN"}:
        return {"returncode": 1, "status": last_status, "reason": "timeout_waiting_for_aristotle"}

    cp = subprocess.run(
        ["/home/lesha/.local/bin/aristotle", "download", project_id, "--destination", str(archive)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=1200,
    )
    with log_path.open("a", encoding="utf-8") as handle:
        handle.write(f"\n[{utc_now()}] download returncode={cp.returncode}\n")
        handle.write(cp.stdout)
        if not cp.stdout.endswith("\n"):
            handle.write("\n")
    return {"returncode": cp.returncode, "status": last_status, "archive": str(archive)}


def run_process_capture(
    *,
    name: str,
    cmd: list[str],
    cwd: Path,
    prompt: str | None,
    out_dir: Path,
    timeout: int,
) -> tuple[bool, str]:
    out_dir.mkdir(parents=True, exist_ok=True)
    hp = import_pipeline_module()
    env = hp.model_env()
    prompt_path = out_dir / f"{name}.prompt.md"
    raw_path = out_dir / f"{name}.raw.json"
    started_at = utc_now()
    started = time.monotonic()
    try:
        completed = subprocess.run(
            cmd,
            input=prompt,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=str(cwd),
            env=env,
            timeout=timeout,
        )
        payload = {
            "name": name,
            "cmd": cmd,
            "cwd": str(cwd),
            "returncode": completed.returncode,
            "started_at": started_at,
            "finished_at": utc_now(),
            "duration_seconds": round(time.monotonic() - started, 3),
            "stdout": completed.stdout,
            "stderr": completed.stderr,
            "prompt_path": str(prompt_path),
        }
        write_json(raw_path, payload)
        if completed.returncode != 0:
            raise RuntimeError(f"{name} failed with exit code {completed.returncode}; see {raw_path}")
        text = str(payload.get("stdout", "")).strip()
        if not text:
            text = f"STATUS: EMPTY_OUTPUT\n\nCommand completed but produced empty stdout.\n"
        write_text(out_dir / f"{name}.md", text + "\n")
        return True, text
    except Exception as exc:
        text = (
            f"STATUS: FAILED\n\nagent_id: `{name}`\n\n"
            f"error: `{type(exc).__name__}: {exc}`\n\n"
            "Traceback:\n\n```text\n"
            f"{traceback.format_exc()}```\n"
        )
        write_text(out_dir / f"{name}.FAILED.md", text)
        return False, text


def command_output(argv: list[str], cwd: Path, timeout: int = 1800) -> tuple[int, str]:
    cp = subprocess.run(
        argv,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )
    return cp.returncode, cp.stdout


def run_edit_agent(
    kind: str,
    agent_id: str,
    prompt: str,
    out_dir: Path,
    timeout: int,
    dry_run: bool,
    work_root: Path,
) -> tuple[bool, str]:
    checkpoint_path = out_dir / f"{agent_id}.checkpoint.md"
    checkpoint_msg = f"""

Checkpoint protocol:
- Immediately create or update `{checkpoint_path}` if your tool surface can
  write files.
- If you work for more than about 10 minutes, append useful partial progress to
  that checkpoint every ~10 minutes: candidate proof terms, exact theorem names,
  failed tactics, local lemmas, obstacles, or any useful partial Lean code.
- If you cannot write files, include a `Checkpoint summary` section in stdout.
"""
    prompt = prompt.rstrip() + checkpoint_msg
    prompt_path = out_dir / f"{agent_id}.prompt.md"
    write_text(prompt_path, prompt)
    if dry_run:
        text = f"STATUS: DRY_RUN\n\nPrompt written to `{prompt_path}`.\n"
        write_text(out_dir / f"{agent_id}.md", text)
        return True, text
    hp = import_pipeline_module()
    if kind == "gemini":
        launcher_prompt = (
            "Read the full task prompt from this file and follow it exactly:\n"
            f"{prompt_path}\n\n"
            "You have write access to the worktree. Edit files there if useful, "
            "then report what changed. Preserve partial progress using the "
            f"checkpoint file `{checkpoint_path}`."
        )
        cmd = [
            hp.AGY_BIN,
            "--dangerously-skip-permissions",
            "--mode",
            "accept-edits",
            "--model",
            hp.GEMINI_MODEL,
            "--print-timeout",
            f"{max(60, timeout - 30)}s",
            "--add-dir",
            str(work_root),
            "--add-dir",
            str(out_dir),
            "--print",
            launcher_prompt,
        ]
        return run_process_capture(name=agent_id, cmd=cmd, cwd=work_root, prompt="", out_dir=out_dir, timeout=timeout)
    if kind == "codex":
        cmd = [
            hp.CODEX_BIN,
            "exec",
            "--ephemeral",
            "--skip-git-repo-check",
            "--sandbox",
            "workspace-write",
            "-C",
            str(work_root),
            "--color",
            "never",
            "-m",
            CODEX_MODEL,
            "-c",
            f'model_reasoning_effort="{CODEX_EFFORT}"',
            "-",
        ]
        return run_process_capture(name=agent_id, cmd=cmd, cwd=work_root, prompt=prompt, out_dir=out_dir, timeout=timeout)
    if kind == "claude":
        cmd = [
            hp.CLAUDE_BIN,
            "-p",
            "--model",
            hp.CLAUDE_MODEL,
            "--effort",
            hp.CLAUDE_EFFORT,
            "--dangerously-skip-permissions",
            "--no-session-persistence",
            "--add-dir",
            str(work_root),
            "--add-dir",
            str(out_dir),
        ]
        return run_process_capture(name=agent_id, cmd=cmd, cwd=work_root, prompt=prompt, out_dir=out_dir, timeout=timeout)
    raise ValueError(f"unsupported edit agent kind: {kind}")


def run_strategy_agent(
    kind: str,
    agent_id: str,
    prompt: str,
    out_dir: Path,
    timeout: int,
    dry_run: bool,
    work_root: Path,
) -> tuple[bool, str]:
    prompt_path = out_dir / f"{agent_id}.prompt.md"
    write_text(prompt_path, prompt)
    if dry_run:
        text = f"STATUS: DRY_RUN\n\nPrompt written to `{prompt_path}`.\n"
        write_text(out_dir / f"{agent_id}.md", text)
        return True, text
    hp = import_pipeline_module()
    if kind == "gemini":
        launcher_prompt = (
            "Read the full strategy prompt from this file and follow it exactly:\n"
            f"{prompt_path}\n\n"
            f"The current repository is the worktree `{work_root}`, not the parent/root checkout. "
            "Do not edit Lean files during this strategy iteration."
        )
        cmd = [
            hp.AGY_BIN,
            "--dangerously-skip-permissions",
            "--mode",
            "accept-edits",
            "--model",
            hp.GEMINI_MODEL,
            "--print-timeout",
            f"{max(60, timeout - 30)}s",
            "--add-dir",
            str(work_root),
            "--add-dir",
            str(out_dir),
            "--print",
            launcher_prompt,
        ]
        return run_process_capture(
            name=agent_id,
            cmd=cmd,
            cwd=work_root,
            prompt="",
            out_dir=out_dir,
            timeout=timeout,
        )
    if kind == "codex":
        cmd = [
            hp.CODEX_BIN,
            "exec",
            "--ephemeral",
            "--skip-git-repo-check",
            "--sandbox",
            "read-only",
            "-C",
            str(work_root),
            "--color",
            "never",
            "-m",
            CODEX_MODEL,
            "-c",
            f'model_reasoning_effort="{CODEX_EFFORT}"',
            "-",
        ]
        return run_process_capture(
            name=agent_id,
            cmd=cmd,
            cwd=work_root,
            prompt=prompt,
            out_dir=out_dir,
            timeout=timeout,
        )
    if kind == "claude":
        cmd = [
            hp.CLAUDE_BIN,
            "-p",
            "--model",
            hp.CLAUDE_MODEL,
            "--effort",
            hp.CLAUDE_EFFORT,
            "--dangerously-skip-permissions",
            "--no-session-persistence",
            "--add-dir",
            str(work_root),
            "--add-dir",
            str(out_dir),
        ]
        return run_process_capture(
            name=agent_id,
            cmd=cmd,
            cwd=work_root,
            prompt=prompt,
            out_dir=out_dir,
            timeout=timeout,
        )
    raise ValueError(f"unsupported strategy agent kind: {kind}")


def prepare_worktree(section_dir: Path) -> Path:
    work_root = section_dir / "_worktree"
    if work_root.exists():
        return work_root

    def ignore(_: str, names: list[str]) -> set[str]:
        ignored = {
            ".git",
            ".lake",
            "proof_loop_runs",
            "proof_loop_readiness",
            "interface_part_reviews",
            "reviews",
        }
        return {name for name in names if name in ignored or name.endswith(".olean") or name.endswith(".ilean")}

    shutil.copytree(ROOT, work_root, ignore=ignore)
    command_output(["git", "init", "-q"], work_root, timeout=60)
    command_output(["git", "add", "."], work_root, timeout=120)
    command_output(
        ["git", "-c", "user.name=proof-loop", "-c", "user.email=proof-loop@example.invalid", "commit", "-q", "-m", "baseline"],
        work_root,
        timeout=120,
    )
    lake = work_root / ".lake"
    lake.mkdir(exist_ok=True)
    for name in ["packages", "config"]:
        src = ROOT / ".lake" / name
        dst = lake / name
        if src.exists() and not dst.exists():
            dst.symlink_to(src, target_is_directory=src.is_dir())
    # Seed the project build artifacts from ROOT so the first worktree
    # build is incremental (only files the agents touch get rebuilt).
    build_src = ROOT / ".lake" / "build"
    build_dst = lake / "build"
    if build_src.exists() and not build_dst.exists():
        shutil.copytree(build_src, build_dst)
    return work_root


def allowed_prefixes(section: dict[str, Any]) -> list[str]:
    return [str(p) for p in section.get("allowed_prefixes", [])]


def is_allowed_candidate(rel: str, section: dict[str, Any]) -> bool:
    if rel.startswith("KolmogorovMathlib/Interface/"):
        return False
    return any(rel == prefix.rstrip("/") or rel.startswith(prefix) for prefix in allowed_prefixes(section))


def iter_candidate_files(root: Path, section: dict[str, Any]) -> list[Path]:
    files: list[Path] = []
    for prefix in allowed_prefixes(section):
        path = root / prefix
        if path.is_file() and path.suffix == ".lean":
            files.append(path)
        elif path.is_dir():
            files.extend(path.rglob("*.lean"))
    return sorted(set(files))


def iter_mergeable_files(root: Path, section: dict[str, Any]) -> list[Path]:
    files = list(iter_candidate_files(root, section))
    for prefix in allowed_prefixes(section):
        path = root / prefix
        if path.is_file() and path.suffix == ".md":
            files.append(path)
        elif path.is_dir():
            files.extend(path.rglob("*.md"))
    return sorted(set(files))


def changed_candidate_files(work_root: Path, section: dict[str, Any]) -> list[tuple[str, Path]]:
    changed: list[tuple[str, Path]] = []
    for path in iter_mergeable_files(work_root, section):
        rel = path.relative_to(work_root).as_posix()
        if not is_allowed_candidate(rel, section):
            continue
        root_path = ROOT / rel
        if not root_path.exists() or not filecmp.cmp(path, root_path, shallow=False):
            changed.append((rel, path))
    return changed


def safe_extract_project_tar(archive: Path, dest: Path) -> Path | None:
    if not archive.exists():
        return None
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    dest_resolved = dest.resolve()
    with tarfile.open(archive, "r:gz") as tf:
        members = []
        for member in tf.getmembers():
            parts = Path(member.name).parts
            if ".lake" in parts:
                continue
            target = (dest / member.name).resolve()
            if not str(target).startswith(str(dest_resolved) + os.sep):
                raise RuntimeError(f"unsafe tar member: {member.name}")
            members.append(member)
        tf.extractall(dest, members=members)
    candidates = sorted(
        list(dest.rglob("lakefile.lean")) + list(dest.rglob("lakefile.toml")),
        key=lambda p: len(p.parts))
    return candidates[0].parent if candidates else None


def integrate_aristotle_result(iter_dir: Path, work_root: Path, section: dict[str, Any]) -> dict[str, Any]:
    archive = iter_dir / "aristotle_result.tar.gz"
    if not archive.exists():
        return {"integrated": False, "reason": "missing_result_archive"}
    dest = iter_dir / "aristotle_unpacked"
    project = safe_extract_project_tar(archive, dest)
    if project is None:
        return {"integrated": False, "reason": "no_lakefile_in_archive"}
    copied: list[str] = []
    for rel, src in changed_candidate_files(project, section):
        dst = work_root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        copied.append(rel)
    return {"integrated": True, "project": str(project), "copied": copied}


def restore_backup(backup: dict[str, Path | None]) -> None:
    for rel, saved in backup.items():
        target = ROOT / rel
        if saved is None:
            if target.exists():
                target.unlink()
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(saved, target)


def merge_gate(section: dict[str, Any], work_root: Path, iter_dir: Path, args: argparse.Namespace) -> dict[str, Any]:
    import fcntl

    gate_dir = iter_dir / "merge_gate"
    gate_dir.mkdir(parents=True, exist_ok=True)
    lock_path = ROOT / "proof_loop" / "MERGE_GATE.lock"
    before_count = count_sorries_at(ROOT)
    changed = changed_candidate_files(work_root, section)
    if not changed:
        result = {"status": "NO_CHANGES", "before_sorries": before_count, "changed": []}
        write_json(gate_dir / "result.json", result)
        return result

    with lock_path.open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        before_count = count_sorries_at(ROOT)
        backup_dir = gate_dir / "backup"
        if backup_dir.exists():
            shutil.rmtree(backup_dir)
        backup_dir.mkdir()
        backup: dict[str, Path | None] = {}
        copied: list[str] = []
        try:
            for rel, src in changed:
                target = ROOT / rel
                if target.exists():
                    saved = backup_dir / rel
                    saved.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(target, saved)
                    backup[rel] = saved
                else:
                    backup[rel] = None
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, target)
                copied.append(rel)

            after_count = count_sorries_at(ROOT)
            allowed_after = before_count + args.max_sorry_increase_per_merge
            if after_count > allowed_after:
                restore_backup(backup)
                result = {
                    "status": "REJECTED",
                    "reason": "too_many_new_sorries",
                    "before_sorries": before_count,
                    "after_sorries": after_count,
                    "max_sorry_increase_per_merge": args.max_sorry_increase_per_merge,
                    "changed": copied,
                }
                write_json(gate_dir / "result.json", result)
                return result

            audit_rc, audit_out = command_output(["bash", "scripts/audit.sh"], ROOT, timeout=args.audit_timeout_seconds)
            write_text(gate_dir / "audit.log", audit_out)
            if audit_rc != 0:
                restore_backup(backup)
                result = {
                    "status": "REJECTED",
                    "reason": "audit_failed",
                    "audit_rc": audit_rc,
                    "before_sorries": before_count,
                    "after_sorries": after_count,
                    "changed": copied,
                }
                write_json(gate_dir / "result.json", result)
                return result

            result = {
                "status": "ACCEPTED",
                "before_sorries": before_count,
                "after_sorries": after_count,
                "changed": copied,
            }
            write_json(gate_dir / "result.json", result)
            return result
        except Exception as exc:
            restore_backup(backup)
            result = {
                "status": "REJECTED",
                "reason": f"exception: {type(exc).__name__}: {exc}",
                "traceback": traceback.format_exc(),
                "changed": copied,
            }
            write_json(gate_dir / "result.json", result)
            return result


def run_iteration(
    section: dict[str, Any],
    section_dir: Path,
    iteration: int,
    args: argparse.Namespace,
    context: str,
    work_root: Path,
) -> dict[str, Any]:
    mode = "strategy" if args.strategy_every > 0 and iteration % args.strategy_every == 0 else "proof"
    iter_dir = section_dir / f"iter_{iteration:03d}_{mode}"
    iter_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = iter_dir / "manifest.json"
    existing_manifest = load_json(manifest_path, {})
    if (
        existing_manifest.get("section") == section["id"]
        and existing_manifest.get("iteration") == iteration
        and existing_manifest.get("mode") == mode
        and isinstance(existing_manifest.get("stages"), list)
        and existing_manifest.get("status") != "complete"
    ):
        manifest = existing_manifest
        manifest["resumed_at"] = utc_now()
    else:
        manifest: dict[str, Any] = {
            "section": section["id"],
            "iteration": iteration,
            "mode": mode,
            "started_at": utc_now(),
            "stages": [],
        }
    write_json(iter_dir / "manifest.json", manifest)
    completed_stages = {
        str(stage.get("stage"))
        for stage in manifest.get("stages", [])
        if isinstance(stage, dict) and stage.get("ok") is True
    }

    stages = [
        ("gemini", "01_gemini"),
        ("codex", "02_codex"),
        ("claude", "03_opus"),
        ("codex", "04_codex"),
    ]
    for kind, stage in stages:
        if stage in completed_stages and (iter_dir / f"{stage}.md").exists():
            continue
        if status := pause_status(args, section):
            mark_paused(manifest, status)
            write_json(iter_dir / "manifest.json", manifest)
            return manifest
        previous = previous_outputs(iter_dir)
        if mode == "strategy":
            prompt = strategy_prompt(stage, section, iteration, context, previous, args.strategy_every - 1, work_root)
            ok, text = run_strategy_agent(
                kind,
                stage,
                prompt,
                iter_dir,
                args.timeout_seconds,
                args.dry_run,
                work_root,
            )
        else:
            prompt = ordinary_prompt(stage, section, iteration, context, previous, work_root)
            ok, text = run_edit_agent(kind, stage, prompt, iter_dir, args.timeout_seconds, args.dry_run, work_root)
        manifest["stages"].append({"stage": stage, "kind": kind, "ok": ok, "chars": len(text)})
        write_json(iter_dir / "manifest.json", manifest)
        if status := pause_status(args, section):
            mark_paused(manifest, status, paused_after_stage=stage)
            write_json(iter_dir / "manifest.json", manifest)
            return manifest

    if status := pause_status(args, section):
        mark_paused(manifest, status, paused_before_aristotle=True)
        write_json(iter_dir / "manifest.json", manifest)
        return manifest

    open_leaves = count_section_sorries_at(work_root, section)
    manifest["open_leaves_after_stages"] = open_leaves
    aristotle_prompt = write_aristotle_packet(section, iteration, iter_dir, mode, work_root)
    manifest["aristotle_prompt"] = str(aristotle_prompt)
    should_submit_aristotle = open_leaves > 0 or is_polishing(section)
    if args.submit_aristotle and not args.dry_run and should_submit_aristotle:
        manifest["aristotle"] = submit_aristotle(iter_dir, args.aristotle_timeout_seconds)
        followup = manifest["aristotle"].get("followup", {}) if isinstance(manifest.get("aristotle"), dict) else {}
        if followup.get("reason") == "timeout_waiting_for_aristotle":
            manifest["status"] = "waiting_aristotle"
            manifest["waiting_since"] = utc_now()
            write_json(iter_dir / "manifest.json", manifest)
            return manifest
        # Aristotle can return a useful archive even when its task status is
        # OUT_OF_BUDGET or another nonzero terminal status. The merge gate is
        # the authority: integrate any downloaded archive, then build/audit it.
        if mode != "strategy" and (iter_dir / "aristotle_result.tar.gz").exists():
            manifest["aristotle_integration"] = integrate_aristotle_result(iter_dir, work_root, section)
    else:
        manifest["aristotle"] = {
            "submitted": False,
            "reason": "no_actionable_packet" if not should_submit_aristotle else "default_prepare_only",
        }
    if mode != "strategy" and not args.dry_run:
        integration = manifest.get("aristotle_integration", {}) if isinstance(manifest.get("aristotle_integration"), dict) else {}
        if args.submit_aristotle and should_submit_aristotle and not integration.get("integrated"):
            manifest["status"] = "blocked_missing_aristotle_result"
            manifest["blocked_reason"] = "Aristotle result was not downloaded/integrated; refusing LLM-only merge."
            write_json(iter_dir / "manifest.json", manifest)
            return manifest
        manifest["merge_gate"] = merge_gate(section, work_root, iter_dir, args)
    manifest["status"] = "complete"
    manifest["finished_at"] = utc_now()
    write_json(iter_dir / "manifest.json", manifest)
    return manifest


def run_section(section: dict[str, Any], run_dir: Path, args: argparse.Namespace) -> dict[str, Any]:
    section_dir = run_dir / section["id"]
    section_dir.mkdir(parents=True, exist_ok=True)
    work_root = prepare_worktree(section_dir)
    context = collect_context(section, work_root)
    write_text(section_dir / "section_context.md", context)
    results = []
    iteration = args.start_iteration
    completed = 0
    while args.until_zero_sorries or completed < args.iterations:
        if not args.until_zero_sorries and completed >= args.iterations:
            break
        if args.until_zero_sorries and count_sorries_at(ROOT) == 0:
            break
        if args.until_zero_sorries and count_section_sorries_at(ROOT, section) == 0:
            break
        if pause_status(args, section):
            break
        result = run_iteration(section, section_dir, iteration, args, context, work_root)
        results.append(result)
        if result.get("status") in {"waiting_aristotle", "blocked_missing_aristotle_result"}:
            break
        iteration += 1
        completed += 1
    summary = {
        "section": section["id"],
        "title": section["title"],
        "iterations_requested": args.iterations,
        "iterations_completed": len(results),
        "results": results,
    }
    write_json(section_dir / "section_summary.json", summary)
    return summary


def selected_sections(args: argparse.Namespace, sections: list[dict[str, Any]]) -> list[dict[str, Any]]:
    requested = args.section or ["all"]
    if "all" in requested:
        return sections
    by_id = {section["id"]: section for section in sections}
    missing = [item for item in requested if item not in by_id]
    if missing:
        raise SystemExit(f"unknown section(s): {', '.join(missing)}")
    return [by_id[item] for item in requested]


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--section", action="append", help="Section id, or all. May be repeated.")
    parser.add_argument("--list-sections", action="store_true")
    parser.add_argument("--iterations", type=int, default=1)
    parser.add_argument("--start-iteration", type=int, default=1)
    parser.add_argument("--strategy-every", type=int, default=5)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--timeout-seconds", type=int, default=3600)
    parser.add_argument("--aristotle-timeout-seconds", type=int, default=86400)
    parser.add_argument("--run-dir", type=Path, default=None)
    parser.add_argument("--runs-root", type=Path, default=DEFAULT_RUNS_DIR)
    parser.add_argument("--stop-file", type=Path, default=DEFAULT_STOP_FILE)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--submit-aristotle", action="store_true")
    parser.add_argument("--until-zero-sorries", action="store_true")
    parser.add_argument("--max-sorry-increase-per-merge", type=int, default=10**9)
    parser.add_argument("--audit-timeout-seconds", type=int, default=1800)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    sections = load_sections()
    if args.list_sections:
        for section in sections:
            print(f"{section['id']}: {section['title']}")
        return 0

    run_dir = (args.run_dir or (args.runs_root / f"{utc_stamp()}-proof-section-loop")).resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    write_json(
        run_dir / "manifest.json",
        {
            "started_at": utc_now(),
            "root": str(ROOT),
            "run_dir": str(run_dir),
            "dry_run": args.dry_run,
            "submit_aristotle": args.submit_aristotle,
            "aristotle_timeout_seconds": args.aristotle_timeout_seconds,
            "strategy_every": args.strategy_every,
            "iterations": args.iterations,
            "sections": args.section or ["all"],
        },
    )
    chosen = selected_sections(args, sections)

    summaries: list[dict[str, Any]] = []
    errors: list[dict[str, str]] = []
    if args.jobs <= 1 or len(chosen) <= 1:
        for section in chosen:
            try:
                summaries.append(run_section(section, run_dir, args))
            except Exception as exc:
                errors.append({"section": section["id"], "error": f"{type(exc).__name__}: {exc}", "traceback": traceback.format_exc()})
    else:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = {pool.submit(run_section, section, run_dir, args): section for section in chosen}
            for future in as_completed(futures):
                section = futures[future]
                try:
                    summaries.append(future.result())
                except Exception as exc:
                    errors.append({"section": section["id"], "error": f"{type(exc).__name__}: {exc}", "traceback": traceback.format_exc()})

    write_json(run_dir / "SUMMARY.json", {"summaries": summaries, "errors": errors})
    lines = ["# Proof Section Loop Summary", "", f"- run_dir: `{run_dir}`", f"- dry_run: `{args.dry_run}`", ""]
    for summary in sorted(summaries, key=lambda x: x["section"]):
        lines.append(f"- {summary['section']}: {summary['iterations_completed']} iteration(s)")
    if errors:
        lines.append("")
        lines.append("## Errors")
        for error in errors:
            lines.append(f"- {error['section']}: {error['error']}")
    write_text(run_dir / "SUMMARY.md", "\n".join(lines) + "\n")
    if errors:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
