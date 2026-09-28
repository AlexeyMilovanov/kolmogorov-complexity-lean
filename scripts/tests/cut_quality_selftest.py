#!/usr/bin/env python3
"""Self-test for `scripts/cut_quality.py`.

Each case writes a throw-away tree of Lean-shaped text under a temporary root,
runs the checker over it with the allow-list disabled, and asserts which codes
it reports.  Every code has at least one positive case (the pattern the audits
call mechanical) and one negative case (the same shape, made honest), so a
checker that fires on everything fails just as loudly as one that fires on
nothing.  The files never have to compile: the gate is pure text analysis.

Usage:  python3 scripts/tests/cut_quality_selftest.py
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path

CHECKER = Path(os.environ.get(
    'CUT_QUALITY',
    Path(__file__).resolve().parent.parent / 'cut_quality.py'))

HEADER = 'namespace Kolmogorov\n\n'
FOOTER = '\nend Kolmogorov\n'


def run_files(files: dict[str, str]) -> list[tuple[str, str]]:
    """Return the (code, fully qualified name) pairs reported for a tree."""
    tmp = Path(tempfile.mkdtemp())
    for rel, body in files.items():
        module = tmp / 'KolmogorovMathlib' / rel
        module.parent.mkdir(parents=True, exist_ok=True)
        module.write_text(HEADER + body + FOOTER)
    out = subprocess.run(
        [sys.executable, '-B', str(CHECKER), '--root', str(tmp), '--no-allow'],
        capture_output=True, text=True)
    found = []
    for line in out.stdout.split('\n'):
        cols = line.split('\t')
        if len(cols) >= 2 and cols[0] != 'SUMMARY':
            found.append((cols[0], cols[1]))
    return found


CASES: list[tuple[str, str, str, bool, dict[str, str]]] = []


def case(name: str, code: str, body: str, expected: bool,
         extra: dict[str, str] | None = None) -> None:
    """Register a case; `extra` adds further modules beside `Case.lean`."""
    CASES.append((name, code, body, expected, extra or {}))


# -- RFL-BINDER --------------------------------------------------------------

case('rfl-binder: two equations closed by `rfl` and `by omega`', 'RFL-BINDER', '''
/-- A cut whose two equation binders the caller closes with nothing. -/
private lemma step_bound (a b c d : Nat) (hc : c = a + b) (hd : d = a + b + 1)
    (hab : a ≤ b) :
    c ≤ d := by
  omega

/-- The parent. -/
theorem parent (a b : Nat) (hab : a ≤ b) : a + b ≤ a + b + 1 := by
  have h : a + b ≤ a + b + 1 := step_bound a b (a + b) (a + b + 1) rfl (by omega) hab
  exact h
''', True)

case('rfl-binder: the equations carry real content', 'RFL-BINDER', '''
/-- The binders are supplied by facts the caller proved. -/
private lemma step_bound (a b c d : Nat) (hc : c = a + b) (hd : d = a + b + 1)
    (hab : a ≤ b) :
    c ≤ d := by
  omega

/-- The parent. -/
theorem parent (a b c d : Nat) (hab : a ≤ b) (hc : c = a + b)
    (hd : d = a + b + 1) : c ≤ d := by
  have h : c ≤ d := step_bound a b c d hc hd hab
  exact h
''', False)

# -- SINGLE-USE-TAIL ---------------------------------------------------------

case('single-use tail: the conclusion is the caller\'s next `have`',
     'SINGLE-USE-TAIL', '''
/-- A cut with the parent's parameters hoisted into binders. -/
private lemma tail_step (a b c d e f g h : Nat) (hab : a ≤ b) (hcd : c ≤ d) :
    a + c + e + f + g + h ≤ b + d + e + f + g + h := by
  omega

/-- The parent. -/
theorem parent (a b c d e f g h : Nat) (hab : a ≤ b) (hcd : c ≤ d) :
    True := by
  have hstep : a + c + e + f + g + h ≤ b + d + e + f + g + h :=
    tail_step a b c d e f g h hab hcd
  trivial
''', True)

case('single-use tail: two consumers, so the statement is used as a fact',
     'SINGLE-USE-TAIL', '''
/-- A bound two proofs use. -/
lemma tail_step (a b c d e f g h : Nat) (hab : a ≤ b) (hcd : c ≤ d) :
    a + c + e + f + g + h ≤ b + d + e + f + g + h := by
  omega

/-- The first consumer. -/
theorem parent (a b c d e f g h : Nat) (hab : a ≤ b) (hcd : c ≤ d) : True := by
  have hstep : a + c + e + f + g + h ≤ b + d + e + f + g + h :=
    tail_step a b c d e f g h hab hcd
  trivial

/-- The second consumer. -/
theorem other (a b c d e f g h : Nat) (hab : a ≤ b) (hcd : c ≤ d) : True := by
  have hstep : a + c + e + f + g + h ≤ b + d + e + f + g + h :=
    tail_step a b c d e f g h hab hcd
  trivial
''', False)

# -- WRAPPER -----------------------------------------------------------------

case('wrapper: one application of a lemma with the same statement', 'WRAPPER', '''
/-- The lemma with the content. -/
theorem base_bound (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 := by
  omega

/-- A second name for `base_bound`. -/
private lemma copied_bound (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 :=
  base_bound a b hab

/-- The parent. -/
theorem parent (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 :=
  copied_bound a b hab
''', True)

case('wrapper: the body is an argument, not a restatement', 'WRAPPER', '''
/-- The lemma with the content. -/
theorem base_bound (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 := by
  omega

/-- A different statement, proved from it. -/
private lemma shifted_bound (a b : Nat) (hab : a ≤ b) : a ≤ b + 2 := by
  have h := base_bound a b hab
  omega

/-- The parent. -/
theorem parent (a b : Nat) (hab : a ≤ b) : a ≤ b + 3 := by
  have h := shifted_bound a b hab
  omega
''', False)

case('wrapper: the special case of a primed sibling', 'WRAPPER', '''
/-- The general lemma. -/
theorem base_bound' (a b : Nat) (hab : a < b) : a <= b + 1 := by
  omega

/-- The Mathlib-convention special case. -/
theorem base_bound (a b : Nat) (hab : a < b) : a <= b + 1 :=
  base_bound' a b hab

/-- The parent. -/
theorem parent (a b : Nat) (hab : a < b) : a <= b + 2 := by
  have h := base_bound a b hab
  omega
''', False)

case('wrapper: the special case of an `_of_` sibling', 'WRAPPER', '''
/-- The general lemma. -/
theorem base_bound_of_lt (a b : Nat) (hab : a < b) : a <= b + 1 := by
  omega

/-- The Mathlib-convention special case. -/
theorem base_bound (a b : Nat) (hab : a < b) : a <= b + 1 :=
  base_bound_of_lt a b hab

/-- The parent. -/
theorem parent (a b : Nat) (hab : a < b) : a <= b + 2 := by
  have h := base_bound a b hab
  omega
''', False)

# -- LONG-STATEMENT ----------------------------------------------------------

LONG_BINDERS = '\n'.join(
    f'    (h{i} : a{i} ≤ b{i})' for i in range(14))
LONG_NAMES = ' '.join(f'a{i} b{i}' for i in range(14))
LONG_CONCL = ' +\n      '.join(f'a{i}' for i in range(14))
LONG_RHS = ' +\n      '.join(f'b{i}' for i in range(14))
LONG_ARGS = ' '.join(f'h{i}' for i in range(14))

case('long statement: many lines and hypotheses copied from the parent',
     'LONG-STATEMENT', f'''
/-- A cut that copies its parent's signature. -/
private lemma wide_step ({LONG_NAMES} : Nat)
{LONG_BINDERS} :
    {LONG_CONCL} ≤
      {LONG_RHS} := by
  omega

/-- The parent. -/
theorem parent ({LONG_NAMES} : Nat)
{LONG_BINDERS} :
    True := by
  have hstep := wide_step {LONG_NAMES} {LONG_ARGS}
  trivial
''', True)

case('long statement: the same hypotheses, written compactly', 'LONG-STATEMENT',
     f'''
/-- A compact statement. -/
private lemma narrow_step ({LONG_NAMES} : Nat) (h0 : a0 ≤ b0) :
    a0 ≤ b0 := h0

/-- The parent. -/
theorem parent ({LONG_NAMES} : Nat)
{LONG_BINDERS} :
    True := by
  have hstep := narrow_step {LONG_NAMES} h0
  trivial
''', False)

# -- THEOREM-HYP -------------------------------------------------------------

case('theorem hypothesis: three quantified implications in the signature',
     'THEOREM-HYP', '''
/-- A cut whose hypotheses are three whole theorems. -/
private lemma assembled (a b : Nat)
    (hone : ∀ n : Nat, n ≤ a → n ≤ b)
    (htwo : ∀ n : Nat, n ≤ b → n ≤ a + b)
    (hthree : ∀ n : Nat, n ≤ a + b → n ≤ a + b + 1) :
    a ≤ a + b + 1 := by
  omega

/-- The parent. -/
theorem parent (a b : Nat) : a ≤ a + b + 1 :=
  assembled a b (fun _ h => h.trans (Nat.le_add_left a b))
    (fun _ h => h.trans (Nat.le_add_left b a)) (fun _ h => h.trans (Nat.le_succ _))
''', True)

case('theorem hypothesis: two documented interface hypotheses',
     'THEOREM-HYP', '''
/-- A cut with two interface hypotheses. -/
private lemma assembled (a b : Nat)
    (hone : ∀ n : Nat, n ≤ a → n ≤ b)
    (htwo : ∀ n : Nat, n ≤ b → n ≤ a + b) :
    a ≤ a + b := by
  omega

/-- The parent. -/
theorem parent (a b : Nat) (hone : ∀ n : Nat, n ≤ a → n ≤ b)
    (htwo : ∀ n : Nat, n ≤ b → n ≤ a + b) : a ≤ a + b :=
  assembled a b hone htwo
''', False)

# -- SIBLING-PAIR ------------------------------------------------------------

case('sibling pair: two cuts of one parent differing in one constant',
     'SIBLING-PAIR', '''
/-- The first half. -/
private lemma half_left (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 := by omega

/-- The second half. -/
private lemma half_right (a b : Nat) (hab : a ≤ b) : a ≤ b + 2 := by omega

/-- The parent. -/
theorem parent (a b : Nat) (hab : a ≤ b) : True := by
  have h1 := half_left a b hab
  have h2 := half_right a b hab
  trivial
''', True)

case('sibling pair: the two lemmas are about two different objects',
     'SIBLING-PAIR', '''
/-- The first object. -/
def leftValue (a : Nat) : Nat := a + 1

/-- The second object. -/
def rightValue (a : Nat) : Nat := a + 2

/-- A fact about the first. -/
private lemma left_pos (a : Nat) (ha : 0 < a) : 0 < leftValue a := by
  simp [leftValue]

/-- A fact about the second. -/
private lemma right_pos (a : Nat) (ha : 0 < a) : 0 < rightValue a := by
  simp [rightValue]

/-- The parent. -/
theorem parent (a : Nat) (ha : 0 < a) : True := by
  have h1 := left_pos a ha
  have h2 := right_pos a ha
  trivial
''', False)

# -- PADDED-BOUND ------------------------------------------------------------

case('padded bound: four summands repeated on both sides', 'PADDED-BOUND', '''
/-- A cut that pads its content with the caller's constants. -/
private lemma padded (p q r s x y : Nat) (hxy : x ≤ y) :
    p + q + r + s + x ≤ y + (p + q + r + s) := by
  omega

/-- The parent. -/
theorem parent (p q r s x y : Nat) (hxy : x ≤ y) : True := by
  have h := padded p q r s x y hxy
  trivial
''', True)

case('padded bound: a monotonicity statement with one shared summand',
     'PADDED-BOUND', '''
/-- Adding a constant preserves the bound. -/
private lemma shifted (p x y : Nat) (hxy : x ≤ y) : x + p ≤ y + p := by
  omega

/-- The parent. -/
theorem parent (p x y : Nat) (hxy : x ≤ y) : True := by
  have h := shifted p x y hxy
  trivial
''', False)

# -- BINDER-RESTATE ----------------------------------------------------------

case('binder restatement: the body opens by renaming a hypothesis',
     'BINDER-RESTATE', '''
/-- A cut whose first step restates its own hypothesis. -/
private lemma restating (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 := by
  have hcopy : a ≤ b := hab
  omega

/-- The parent. -/
theorem parent (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 :=
  restating a b hab
''', True)

case('binder restatement: the first step is a consequence, not a copy',
     'BINDER-RESTATE', '''
/-- A cut whose first step derives something. -/
private lemma deriving_step (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 := by
  have hstep : a ≤ b + 1 := Nat.le_succ_of_le hab
  exact hstep

/-- The parent. -/
theorem parent (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 :=
  deriving_step a b hab
''', False)


# -- the refinements of 2026-09-11 ------------------------------------------

case('rfl-binder: the equations relate two arguments the caller proves',
     'RFL-BINDER', '''
/-- A transfer whose equations relate two states. -/
private lemma transfer_step (a b : Nat) (s t : Nat × Nat)
    (hfst : t.1 = s.1) (hsnd : t.2 = s.2) (hab : a ≤ b) : t.1 ≤ s.1 + b := by
  omega

/-- The parent. -/
theorem parent (a b : Nat) (s t : Nat × Nat) (hab : a ≤ b) (hst : t = s) :
    t.1 ≤ s.1 + b := by
  have h : t.1 ≤ s.1 + b :=
    transfer_step a b s t (by rw [hst]) (by rw [hst]) hab
  exact h
''', False)

case('single-use tail: the caller proves every hypothesis on the spot',
     'SINGLE-USE-TAIL', '''
/-- A bound the parent has to earn. -/
private lemma tail_step (a b c d e f g h : Nat) (hab : a ≤ b) (hcd : c ≤ d) :
    a + c + e + f + g + h ≤ b + d + e + f + g + h := by
  omega

/-- The parent. -/
theorem parent (a b c d e f g h : Nat) : True := by
  have hstep : a + c + e + f + g + h ≤ b + d + e + f + g + h :=
    tail_step a b c d e f g h (by omega) (by omega)
  trivial
''', False)

case('wrapper: the statement applies its own `_aux` sibling', 'WRAPPER', '''
/-- The induction. -/
private lemma base_bound_aux (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 := by
  omega

/-- The statement. -/
theorem base_bound (a b : Nat) (hab : a ≤ b) : a ≤ b + 1 :=
  base_bound_aux a b hab

/-- The parent. -/
theorem parent (a b : Nat) (hab : a ≤ b) : a ≤ b + 3 := by
  have h := base_bound a b hab
  omega
''', False)

case('sibling pair: two projections of the same argument', 'SIBLING-PAIR', '''
/-- The first projection is a natural number. -/
theorem proj_one (r : Nat × Nat) : 0 ≤ r.1 := Nat.zero_le _

/-- The second projection is a natural number. -/
theorem proj_two (r : Nat × Nat) : 0 ≤ r.2 := Nat.zero_le _

/-- The parent. -/
theorem parent (r : Nat × Nat) : True := by
  have h1 := proj_one r
  have h2 := proj_two r
  trivial
''', False)

case('sibling pair: a `let` inside the statement does not end it',
     'SIBLING-PAIR', '''
/-- The first fact. -/
theorem with_let_one (a : Nat) : let x := a + 1; x ≤ a + 1 := by
  intro x
  omega

/-- The second fact. -/
theorem with_let_two (a : Nat) : let y := a + 2; y ≤ a + 2 := by
  intro y
  omega

/-- The parent. -/
theorem parent (a : Nat) : True := by
  have h1 := with_let_one a
  have h2 := with_let_two a
  trivial
''', False)


# -- the rules restored on 2026-09-11 ---------------------------------------
#
# The gate was loosened until it caught 6 of the 10 reference cases of audit
# #4 while its own self-test stayed green.  Each case below is one of the
# tightenings that lost a reference case, or the parsing bug that lost one.

case('rfl-binder: `≤` bounds on constants the conclusion does mention',
     'RFL-BINDER', '''
/-- A cut whose two `≤` binders the only caller closes with `le_rfl`. -/
private lemma budget_step (b c gap p : Nat) (hc : c ≤ b) (hgap : gap ≤ b * p) :
    c * p + gap ≤ b * p + b * p := by
  exact Nat.add_le_add (Nat.mul_le_mul_right p hc) hgap

/-- The parent. -/
theorem parent (b p : Nat) : b * p + b * p ≤ b * p + b * p := by
  have h : b * p + b * p ≤ b * p + b * p := budget_step b b (b * p) p le_rfl le_rfl
  exact h
''', True)

case('rfl-binder: a `set … with h` equation spanning three lines',
     'RFL-BINDER', '''
/-- A cut whose one empty binder is the caller's own multi-line `set`. -/
private lemma packed_bound (a b c d e f g C : Nat)
    (hC : C = a + b + c + d + e + f + g) :
    a + b + c + d + e + f + g ≤ C := by
  omega

/-- The parent. -/
theorem parent (a b c d e f g : Nat) : True := by
  set C := a + b +
    c + d +
      e + f + g with hC
  have h : a + b + c + d + e + f + g ≤ C :=
    packed_bound a b c d e f g C hC
  trivial
''', True)

case('rfl-binder: one empty binder in a short signature', 'RFL-BINDER', '''
/-- A step whose single equation the caller closes by `rfl`. -/
private lemma small_step (a b : Nat) (hb : b = a + 1) : a ≤ b := by
  omega

/-- The parent. -/
theorem parent (a : Nat) : a ≤ a + 1 := by
  have h : a ≤ a + 1 := small_step a (a + 1) rfl
  exact h
''', False)

case('single-use tail: a specialisation with no hypotheses at all',
     'SINGLE-USE-TAIL', '''
/-- An eight-fold specialisation of an associative bound. -/
private lemma sum_eight_le (a b c d e f g n : Nat) :
    a + b + c + d + e + f + g + n ≤ a + b + c + d + e + f + g + n + 1 := by
  omega

/-- The parent. -/
theorem parent (p q r s t u v w : Nat) : True := by
  have hsum : p + q + r + s + t + u + v + w ≤ p + q + r + s + t + u + v + w + 1 :=
    sum_eight_le p q r s t u v w
  trivial
''', True)

case('single-use tail: no hypotheses, and a conclusion of its own',
     'SINGLE-USE-TAIL', '''
/-- A bound on a sum of eight terms. -/
private lemma sum_eight_le (a b c d e f g n : Nat) :
    a + b + c + d + e + f + g + n ≤ a + b + c + d + e + f + g + n + 1 := by
  omega

/-- The parent, which goes on from it. -/
theorem parent (p q r s t u v w : Nat) : True := by
  have hsum : p + q + r + s + t + u + v + w < p + q + r + s + t + u + v + w + 2 :=
    Nat.lt_succ_of_le (sum_eight_le p q r s t u v w)
  trivial
''', False)

case('single-use tail: the caller hands its own `have`s back under other names',
     'SINGLE-USE-TAIL', '''
/-- A cut with the parent's parameters hoisted into binders. -/
private lemma tail_step (a b c d e f g h : Nat) (hab : a ≤ b) (hcd : c ≤ d) :
    a + c + e + f + g + h ≤ b + d + e + f + g + h := by
  omega

/-- The parent. -/
theorem parent (a b c d e f g h : Nat) : True := by
  have hone : a ≤ b := by omega
  have htwo : c ≤ d := by omega
  have hstep : a + c + e + f + g + h ≤ b + d + e + f + g + h :=
    tail_step a b c d e f g h hone htwo
  trivial
''', True)

case('single-use tail: the sole caller lives in another module',
     'SINGLE-USE-TAIL', '''
/-- A cut with the parent's parameters hoisted into binders. -/
private lemma tail_step (a b c d e f g h : Nat) (hab : a ≤ b) (hcd : c ≤ d) :
    a + c + e + f + g + h ≤ b + d + e + f + g + h := by
  omega
''', True, {'Other.lean': '''
/-- The parent, in a module of its own. -/
theorem parent (a b c d e f g h : Nat) (hone : a ≤ b) (htwo : c ≤ d) :
    True := by
  have hstep : a + c + e + f + g + h ≤ b + d + e + f + g + h :=
    tail_step a b c d e f g h hone htwo
  trivial
'''})


def main() -> int:
    failures = 0
    for name, code, body, expected, extra in CASES:
        found = run_files({'Case.lean': body, **extra})
        codes = {c for c, _ in found}
        ok = (code in codes) if expected else (code not in codes)
        status = 'ok' if ok else 'FAIL'
        if not ok:
            failures += 1
            print(f'{status}  {name}')
            print(f'      expected {code} '
                  f'{"present" if expected else "absent"}; '
                  f'reported {sorted(codes) or "nothing"}')
        else:
            print(f'{status}  {name}')
    print(f'{len(CASES)} cases, {failures} failures')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
