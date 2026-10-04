/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.UniversalAlphaTest
import KolmogorovMathlib.AlgorithmicRandomness.StageComputable
import KolmogorovMathlib.MonotoneComplexity.FloorSelectorObstruction
import KolmogorovMathlib.MonotoneComplexity.TwoSidedMeasureRepresentation
import KolmogorovMathlib.Foundation.BigOperators

/-!
# The postponing trimming engine of SUV Theorem 118(a) (§5.8, p. 173)

> "Assume that `α` is lower semicomputable.  This means that we can generate
> better and better approximations from below to `α`, but we do not know their
> precision.  If we use these approximations (instead of true `α`) in the
> requirements for the cover … we get stronger requirements.  Consider the
> algorithm from the previous theorem … and let it use rational lower
> approximations of `α` instead of `α` itself, with the following modification.
> Do not reject permanently the intervals that violate these requirements, but
> postpone them and check again when a new approximation to `α` arrives.  If a
> cover satisfies the requirement for the true `α`, all its intervals will be
> eventually let through."  (SUV §5.8, p. 173, A. Khodyrev)

The universal test for a lower semicomputable `α` is built exactly like the one
for a rational `α` (`Dimension/UniversalAlphaTest.lean`): the same rows
(`uaRow`) at the same budgets (`uaLevel`), with the *one-pass* `α`-trimming
replaced by the postponing variant, which is the single leaf of this module.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- The exponent charged to the `j`-th interval at stage `t`: the current lower approximation of
`α` times the length of the interval, in units of `2 ^ -t`. -/
def wexp (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (m t j : ℕ) : ℕ :=
  a t * ((E m j).elim 0 List.length) / 2 ^ t


/-- Unfolding of the charged exponent. -/
lemma wexp_def (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (m t j : ℕ) :
    wexp a E m t j = a t * ((E m j).elim 0 List.length) / 2 ^ t := rfl

/-- The stage-`t` weight of the `j`-th interval, `2^{-⌊α_t l⌋}`. -/
noncomputable def wmass (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (m t j : ℕ) : ℝ≥0∞ :=
  (E m j).elim 0 (fun _ => (2 : ℝ≥0∞)⁻¹ ^ wexp a E m t j)

/-- The common scale at which the first `p + 1` charges of stage `t` are compared with the budget.
-/
def wscale (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m t p : ℕ) : ℕ :=
  N m + ((List.range (p + 1)).map (fun j => wexp a E m t j)).sum

/-- Unfolding of the common scale. -/
lemma wscale_def (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m t p : ℕ) :
    wscale a E N m t p
      = N m + ((List.range (p + 1)).map (fun j => wexp a E m t j)).sum := rfl

/-- The charged exponent is computable. -/
lemma computable_wexp {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) :
    Computable fun p : (ℕ × ℕ) × ℕ => wexp a E p.1.1 p.1.2 p.2 := by
  have hlen : Computable fun p : (ℕ × ℕ) × ℕ => ((E p.1.1 p.2).elim 0 List.length) := by
    have hopt : Computable fun p : (ℕ × ℕ) × ℕ => E p.1.1 p.2 :=
      hE.comp (Computable.fst.comp Computable.fst) Computable.snd
    have hmap : Computable fun p : (ℕ × ℕ) × ℕ => (E p.1.1 p.2).map List.length :=
      Computable.option_map hopt (Computable.list_length.comp Computable.snd)
    refine (Computable.option_getD hmap (Computable.const 0)).of_eq fun p => ?_
    cases E p.1.1 p.2 <;> rfl
  have hpow : Computable fun n : ℕ => 2 ^ n := primrec_two_pow_aux.to_comp
  have hmul : Computable fun p : (ℕ × ℕ) × ℕ =>
      a p.1.2 * ((E p.1.1 p.2).elim 0 List.length) :=
    Primrec.nat_mul.to_comp.comp (ha.comp (Computable.snd.comp Computable.fst)) hlen
  refine (Primrec.nat_div.to_comp.comp hmul
    (hpow.comp (Computable.snd.comp Computable.fst))).of_eq fun p => ?_
  rfl

attribute [irreducible] wexp

/-- The charged exponent is computable as a function of the summation index. -/
lemma computable_wexp_body {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) :
    Computable₂ fun (p : (ℕ × ℕ) × ℕ) (j : ℕ) => wexp a E p.1.1 p.1.2 j := by
  have harg : Computable fun r : ((ℕ × ℕ) × ℕ) × ℕ => (r.1.1, r.2) :=
    Computable.pair (Computable.fst.comp Computable.fst) Computable.snd
  exact ((computable_wexp ha hE).comp harg).of_eq fun r => rfl

/-- The sum of the charged exponents up to the pointer is computable. -/
lemma computable_wscale_sum {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) :
    Computable fun p : (ℕ × ℕ) × ℕ =>
      ((List.range (p.2 + 1)).map (fun j => wexp a E p.1.1 p.1.2 j)).sum := by
  have hlist : Computable fun p : (ℕ × ℕ) × ℕ => List.range (p.2 + 1) :=
    Primrec.list_range.to_comp.comp
      (Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1))
  exact computable_list_sum_map hlist (computable_wexp_body ha hE)

/-- The common scale is computable. -/
lemma computable_wscale {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun p : (ℕ × ℕ) × ℕ => wscale a E N p.1.1 p.1.2 p.2 := by
  refine (Primrec.nat_add.to_comp.comp (hN.comp (Computable.fst.comp Computable.fst))
    (computable_wscale_sum ha hE)).of_eq fun p => ?_
  rfl


/-- The postponing admission test: the first `p + 1` intervals, charged at the current
approximation of `α`, still fit into the budget of row `m`. -/
def wtest (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m t p : ℕ) : Bool :=
  decide (((List.range (p + 1)).map (fun j =>
      (E m j).elim 0 (fun _ => 2 ^ (wscale a E N m t p - wexp a E m t j)))).sum
    ≤ 2 ^ (wscale a E N m t p - N m))

/-- Unfolding of the admission test in integer form. -/
lemma wtest_def (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m t p : ℕ) :
    wtest a E N m t p
      = decide (((List.range (p + 1)).map (fun j =>
          (E m j).elim 0 (fun _ => 2 ^ (wscale a E N m t p - wexp a E m t j)))).sum
        ≤ 2 ^ (wscale a E N m t p - N m)) := rfl

/-- The pointer of the postponing engine: how many intervals of row `m` have been let through by
stage `t`. -/
def wptr (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      if wtest a E N m (t + 1) (wptr a E N m t) then wptr a E N m t + 1 else wptr a E N m t

/-- The trimmed enumeration: the interval let through at the stage recorded in the index, and
nothing at the other indices. -/
def wemit (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m j : ℕ) :
    Option BitString :=
  if wptr a E N m (Nat.unpair j).2 = (Nat.unpair j).1 + 1 ∧ 1 ≤ (Nat.unpair j).2 ∧
      wptr a E N m ((Nat.unpair j).2 - 1) = (Nat.unpair j).1
    then E m (Nat.unpair j).1 else none

attribute [irreducible] wscale

/-- The scaled weight of one interval inside the admission test is computable. -/
lemma computable_wtest_exp {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun r : ((ℕ × ℕ) × ℕ) × ℕ =>
      2 ^ (wscale a E N r.1.1.1 r.1.1.2 r.1.2 - wexp a E r.1.1.1 r.1.1.2 r.2) := by
  have hpow : Computable fun n : ℕ => 2 ^ n := primrec_two_pow_aux.to_comp
  have h1 : Computable fun r : ((ℕ × ℕ) × ℕ) × ℕ => wscale a E N r.1.1.1 r.1.1.2 r.1.2 :=
    (computable_wscale ha hE hN).comp Computable.fst
  have h2 : Computable fun r : ((ℕ × ℕ) × ℕ) × ℕ => wexp a E r.1.1.1 r.1.1.2 r.2 :=
    (computable_wexp_body ha hE).comp Computable.fst Computable.snd
  exact hpow.comp (Primrec.nat_sub.to_comp.comp h1 h2)

/-- The summand of the admission test is computable in the summation index. -/
lemma computable_wtest_body {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable₂ fun (p : (ℕ × ℕ) × ℕ) (j : ℕ) =>
      (E p.1.1 j).elim 0
        (fun _ => 2 ^ (wscale a E N p.1.1 p.1.2 p.2 - wexp a E p.1.1 p.1.2 j)) := by
  have hopt : Computable fun r : ((ℕ × ℕ) × ℕ) × ℕ => E r.1.1.1 r.2 :=
    hE.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd
  have hexp := computable_wtest_exp ha hE hN
  refine (Computable.option_casesOn hopt (Computable.const 0) (hexp.comp Computable.fst).to₂).of_eq
    fun r => ?_
  cases hEr : E r.1.1.1 r.2 <;> simp [hEr]

/-- The sum inside the admission test is computable. -/
lemma computable_wtest_sum {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun p : (ℕ × ℕ) × ℕ =>
      ((List.range (p.2 + 1)).map (fun j =>
        (E p.1.1 j).elim 0 (fun _ =>
          2 ^ (wscale a E N p.1.1 p.1.2 p.2 - wexp a E p.1.1 p.1.2 j)))).sum := by
  have hlist : Computable fun p : (ℕ × ℕ) × ℕ => List.range (p.2 + 1) :=
    Primrec.list_range.to_comp.comp
      (Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1))
  exact computable_list_sum_map hlist (computable_wtest_body ha hE hN)

/-- The admission test is computable. -/
lemma computable_wtest {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun p : (ℕ × ℕ) × ℕ => wtest a E N p.1.1 p.1.2 p.2 := by
  have hpow : Computable fun n : ℕ => 2 ^ n := primrec_two_pow_aux.to_comp
  have hrhs : Computable fun p : (ℕ × ℕ) × ℕ =>
      2 ^ (wscale a E N p.1.1 p.1.2 p.2 - N p.1.1) :=
    hpow.comp (Primrec.nat_sub.to_comp.comp (computable_wscale ha hE hN)
      (hN.comp (Computable.fst.comp Computable.fst)))
  refine (((PrimrecPred.decide Primrec.nat_le).to_comp).comp
    (Computable.pair (computable_wtest_sum ha hE hN) hrhs)).of_eq fun p => ?_
  rfl

attribute [irreducible] wtest

/-- The pointer, written as a plain recursion on the stage. -/
lemma wptr_eq_natRec (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m t : ℕ) :
    wptr a E N m t
      = Nat.rec 0 (fun t' ih => if wtest a E N m (t' + 1) ih then ih + 1 else ih) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [wptr, ih]

/-- The argument shuffle used in the recursion for the pointer is computable. -/
lemma computable_wptr_arg :
    Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) => (((r.1.1, r.2.1 + 1) : ℕ × ℕ), r.2.2) :=
  Computable.pair (Computable.pair (Computable.fst.comp Computable.fst)
    (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 1)))
    (Computable.snd.comp Computable.snd)

/-- The test used at each step of the pointer recursion is computable. -/
lemma computable_wptr_cond {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) => wtest a E N r.1.1 (r.2.1 + 1) r.2.2 := by
  refine ((computable_wtest ha hE hN).comp computable_wptr_arg).of_eq fun r => ?_
  rfl

/-- One step of the pointer recursion is computable. -/
lemma computable_wptr_step {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable₂ fun (p : ℕ × ℕ) (q : ℕ × ℕ) =>
      if wtest a E N p.1 (q.1 + 1) q.2 then q.2 + 1 else q.2 := by
  refine (Computable.cond (computable_wptr_cond ha hE hN)
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd) (Computable.const 1))
    (Computable.snd.comp Computable.snd)).of_eq fun r => ?_
  cases hb : wtest a E N r.1.1 (r.2.1 + 1) r.2.2 <;> simp [hb]

/-- The pointer is computable in the row and the stage. -/
lemma computable_wptr {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun p : ℕ × ℕ => wptr a E N p.1 p.2 := by
  refine (Computable.nat_rec Computable.snd (Computable.const 0)
    (computable_wptr_step ha hE hN)).of_eq fun p => ?_
  rw [wptr_eq_natRec]

/-- The pointer at the stage coded in an index is computable. -/
lemma computable_wptr_at {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun p : ℕ × ℕ => wptr a E N p.1 (Nat.unpair p.2).2 := by
  have ht : Computable fun p : ℕ × ℕ => (Nat.unpair p.2).2 :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  refine ((computable_wptr ha hE hN).comp (Computable.pair Computable.fst ht)).of_eq fun p => ?_
  rfl

/-- The pointer at the stage before the one coded in an index is computable. -/
lemma computable_wptr_prev {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun p : ℕ × ℕ => wptr a E N p.1 ((Nat.unpair p.2).2 - 1) := by
  have ht : Computable fun p : ℕ × ℕ => (Nat.unpair p.2).2 - 1 :=
    Primrec.nat_sub.to_comp.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp (Computable.const 1)
  refine ((computable_wptr ha hE hN).comp (Computable.pair Computable.fst ht)).of_eq fun p => ?_
  rfl

/-- The first clause of the emission condition is computable. -/
lemma computable_wemit_c1 {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun p : ℕ × ℕ =>
      decide (wptr a E N p.1 (Nat.unpair p.2).2 = (Nat.unpair p.2).1 + 1) := by
  have hk : Computable fun p : ℕ × ℕ => (Nat.unpair p.2).1 + 1 :=
    Primrec.nat_add.to_comp.comp
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp (Computable.const 1)
  refine (((PrimrecPred.decide (Primrec.eq (α := ℕ))).to_comp).comp
    (Computable.pair (computable_wptr_at ha hE hN) hk)).of_eq fun p => ?_
  rfl

/-- The second clause of the emission condition is computable. -/
lemma computable_wemit_c2 :
    Computable fun p : ℕ × ℕ => decide (1 ≤ (Nat.unpair p.2).2) := by
  have ht : Computable fun p : ℕ × ℕ => (Nat.unpair p.2).2 :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  refine (((PrimrecPred.decide Primrec.nat_le).to_comp).comp
    (Computable.pair (Computable.const 1) ht)).of_eq fun p => ?_
  rfl

/-- The third clause of the emission condition is computable. -/
lemma computable_wemit_c3 {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun p : ℕ × ℕ =>
      decide (wptr a E N p.1 ((Nat.unpair p.2).2 - 1) = (Nat.unpair p.2).1) := by
  have hk : Computable fun p : ℕ × ℕ => (Nat.unpair p.2).1 :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  refine (((PrimrecPred.decide (Primrec.eq (α := ℕ))).to_comp).comp
    (Computable.pair (computable_wptr_prev ha hE hN) hk)).of_eq fun p => ?_
  rfl

/-- The emission condition is computable. -/
lemma computable_wemit_cond {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable fun p : ℕ × ℕ =>
      (decide (wptr a E N p.1 (Nat.unpair p.2).2 = (Nat.unpair p.2).1 + 1) &&
        decide (1 ≤ (Nat.unpair p.2).2) &&
        decide (wptr a E N p.1 ((Nat.unpair p.2).2 - 1) = (Nat.unpair p.2).1)) := by
  have h12 : Computable fun p : ℕ × ℕ =>
      (decide (wptr a E N p.1 (Nat.unpair p.2).2 = (Nat.unpair p.2).1 + 1) &&
        decide (1 ≤ (Nat.unpair p.2).2)) := by
    refine ((Primrec₂.to_comp Primrec.and).comp
      (computable_wemit_c1 ha hE hN) computable_wemit_c2).of_eq fun p => ?_
    rfl
  refine ((Primrec₂.to_comp Primrec.and).comp h12
    (computable_wemit_c3 ha hE hN)).of_eq fun p => ?_
  rfl

/-- The trimmed enumeration is computable in the row and the index. -/
lemma computable_wemit {a : ℕ → ℕ} (ha : Computable a) {E : ℕ → ℕ → Option BitString}
    (hE : Computable₂ E) {N : ℕ → ℕ} (hN : Computable N) :
    Computable₂ fun m j => wemit a E N m j := by
  have hk : Computable fun p : ℕ × ℕ => (Nat.unpair p.2).1 :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hE' : Computable fun p : ℕ × ℕ => E p.1 (Nat.unpair p.2).1 := hE.comp Computable.fst hk
  refine (Computable.cond (computable_wemit_cond ha hE hN) hE' (Computable.const none)).of_eq
    fun p => ?_
  simp only [wemit]
  by_cases h1 : wptr a E N p.1 (Nat.unpair p.2).2 = (Nat.unpair p.2).1 + 1 <;>
    by_cases h2 : 1 ≤ (Nat.unpair p.2).2 <;>
    by_cases h3 : wptr a E N p.1 ((Nat.unpair p.2).2 - 1) = (Nat.unpair p.2).1 <;>
    simp [h1, h2, h3]


/-- The dyadic value of a finite sum of numerators is the sum of the dyadic values. -/
lemma dyadicValue_sum_range' (n : ℕ) (g : ℕ → ℕ) (t : ℕ) :
    dyadicValue (∑ j ∈ Finset.range n, g j) t = ∑ j ∈ Finset.range n, dyadicValue (g j) t := by
  induction n with
  | zero => simp [dyadicValue]
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, dyadicValue_add, ih]

/-- Each charged exponent up to the pointer is at most the common scale. -/
lemma wexp_le_wscale (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ)
    {m t p j : ℕ} (hj : j ≤ p) : wexp a E m t j ≤ wscale a E N m t p := by
  rw [wscale_def, sum_list_range_eq_finset_sum']
  have : wexp a E m t j ≤ ∑ i ∈ Finset.range (p + 1), wexp a E m t i :=
    Finset.single_le_sum (f := fun i => wexp a E m t i) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
  omega

/-- The admission test fires exactly when the `α`-mass of the first `p + 1` intervals is within
the budget `2 ^ -N m`. -/
lemma wtest_iff (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m t p : ℕ) :
    wtest a E N m t p = true ↔
      (∑ j ∈ Finset.range (p + 1), wmass a E m t j) ≤ (2 : ℝ≥0∞)⁻¹ ^ N m := by
  set M := wscale a E N m t p with hM
  have hNM : N m ≤ M := by
    rw [hM, wscale_def]
    omega
  have hkey : ∀ j ∈ Finset.range (p + 1),
      wmass a E m t j
        = dyadicValue ((E m j).elim 0 (fun _ => 2 ^ (M - wexp a E m t j))) M := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hle : wexp a E m t j ≤ M := wexp_le_wscale a E N (by omega : j ≤ p)
    cases hEj : E m j with
    | none => simp [wmass, hEj, dyadicValue]
    | some x =>
        simp only [wmass, hEj, Option.elim_some]
        exact (dyadicValue_two_pow_sub hle).symm
  rw [Finset.sum_congr rfl hkey, ← dyadicValue_sum_range']
  have hbudget : ((2 : ℝ≥0∞)⁻¹) ^ N m = dyadicValue (2 ^ (M - N m)) M :=
    (dyadicValue_two_pow_sub hNM).symm
  rw [hbudget, wtest_def, decide_eq_true_iff, sum_list_range_eq_finset_sum']
  constructor
  · intro h
    exact dyadicValue_le _ _ _ h
  · intro h
    by_contra hcon
    push Not at hcon
    exact absurd h (not_le.2 (dyadicValue_lt_of_lt _ hcon))

/-- The pointer never goes back. -/
lemma wptr_mono (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m : ℕ) :
    Monotone (wptr a E N m) := by
  refine monotone_nat_of_le_succ fun t => ?_
  rw [wptr]
  split_ifs <;> omega


/-- Reading a dyadic comparison back as an inequality of numerators. -/
lemma mul_le_of_dyadicValue_le' {n m u v : ℕ} (h : dyadicValue n u ≤ dyadicValue m v) :
    n * 2 ^ v ≤ m * 2 ^ u := by
  by_contra hcon
  push Not at hcon
  have h1 : dyadicValue (m * 2 ^ u) (v + u) < dyadicValue (n * 2 ^ v) (v + u) :=
    dyadicValue_lt_of_lt _ hcon
  rw [← dyadicValue_scale m v u, Nat.add_comm v u, ← dyadicValue_scale n u v] at h1
  exact absurd h (not_le.2 h1)

/-- The stage exponents grow with the stage. -/
lemma wexp_mono {a : ℕ → ℕ}
    (ha_mono : ∀ t, dyadicValue (a t) t ≤ dyadicValue (a (t + 1)) (t + 1))
    (E : ℕ → ℕ → Option BitString) (m j : ℕ) : Monotone (fun t => wexp a E m t j) := by
  refine monotone_nat_of_le_succ fun t => ?_
  have hcross : a t * 2 ^ (t + 1) ≤ a (t + 1) * 2 ^ t := mul_le_of_dyadicValue_le' (ha_mono t)
  set L := (E m j).elim 0 List.length with hL
  rw [wexp_def, wexp_def, ← hL]
  have hpos : 0 < 2 ^ t := pow_pos (by norm_num) t
  have hd : a t * L / 2 ^ t * 2 ^ t ≤ a t * L := Nat.div_mul_le_self _ _
  refine (Nat.le_div_iff_mul_le (by positivity)).2 ?_
  have h1 : (a t * L / 2 ^ t) * 2 ^ (t + 1) * 2 ^ t
      = ((a t * L / 2 ^ t) * 2 ^ t) * 2 ^ (t + 1) := by ring
  have h2 : (a t * L) * 2 ^ (t + 1) = (a t * 2 ^ (t + 1)) * L := by ring
  have h3 : (a (t + 1) * 2 ^ t) * L = (a (t + 1) * L) * 2 ^ t := by ring
  have hchain : (a t * L / 2 ^ t) * 2 ^ (t + 1) * 2 ^ t ≤ (a (t + 1) * L) * 2 ^ t := by
    calc (a t * L / 2 ^ t) * 2 ^ (t + 1) * 2 ^ t
        = ((a t * L / 2 ^ t) * 2 ^ t) * 2 ^ (t + 1) := h1
      _ ≤ (a t * L) * 2 ^ (t + 1) := Nat.mul_le_mul_right _ hd
      _ = (a t * 2 ^ (t + 1)) * L := h2
      _ ≤ (a (t + 1) * 2 ^ t) * L := Nat.mul_le_mul_right _ hcross
      _ = (a (t + 1) * L) * 2 ^ t := h3
  exact Nat.le_of_mul_le_mul_right hchain hpos

/-- Refining the approximation of `α` only decreases the mass charged to an interval. -/
lemma wmass_antitone {a : ℕ → ℕ}
    (ha_mono : ∀ t, dyadicValue (a t) t ≤ dyadicValue (a (t + 1)) (t + 1))
    (E : ℕ → ℕ → Option BitString) (m j : ℕ) {t t' : ℕ} (h : t ≤ t') :
    wmass a E m t' j ≤ wmass a E m t j := by
  cases hEj : E m j with
  | none => simp [wmass, hEj]
  | some x =>
      simp only [wmass, hEj, Option.elim_some]
      exact inv_two_pow_antitone (wexp_mono ha_mono E m j h)

/-- The true `α`-weight never exceeds a stage weight. -/
lemma alphaMass_le_wmass {α : ℝ} (hα : 0 ≤ α) {a : ℕ → ℕ}
    (ha_le : ∀ t, dyadicValue (a t) t ≤ ENNReal.ofReal α)
    (E : ℕ → ℕ → Option BitString) (m t j : ℕ) :
    (E m j).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α) ≤ wmass a E m t j := by
  cases hEj : E m j with
  | none => simp [wmass, hEj]
  | some x =>
      simp only [wmass, hEj, Option.elim_some]
      have hexp : ((wexp a E m t j : ℕ) : ℝ) ≤ (x.length : ℝ) * α := by
        have hdiv : ((a t * x.length / 2 ^ t : ℕ) : ℝ)
            ≤ ((a t * x.length : ℕ) : ℝ) / ((2 ^ t : ℕ) : ℝ) := Nat.cast_div_le
        have hq : ((a t : ℕ) : ℝ) / ((2 ^ t : ℕ) : ℝ) ≤ α := by
          have h1 := ha_le t
          rw [dyadicValue] at h1
          have h2 : ((a t : ℝ≥0∞) / (2 : ℝ≥0∞) ^ t).toReal ≤ (ENNReal.ofReal α).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
          rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
            ENNReal.toReal_natCast, ENNReal.toReal_ofReal hα] at h2
          simpa using h2
        have hEj' : wexp a E m t j = a t * x.length / 2 ^ t := by simp [wexp_def, hEj]
        rw [hEj']
        refine le_trans hdiv ?_
        have hrw : ((a t * x.length : ℕ) : ℝ) / ((2 ^ t : ℕ) : ℝ)
            = (((a t : ℕ) : ℝ) / ((2 ^ t : ℕ) : ℝ)) * (x.length : ℝ) := by
          push_cast
          ring
        rw [hrw, mul_comm ((x.length : ℝ)) α]
        exact mul_le_mul_of_nonneg_right hq (by positivity)
      rw [uniformMeasure_cantorCylinder, ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) x.length,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) (wexp a E m t j)]
      exact ENNReal.rpow_le_rpow_of_exponent_ge inv_two_le_one hexp

/-- The invariant: after every stage the emitted prefix is within budget. -/
lemma wptr_invariant {a : ℕ → ℕ}
    (ha_mono : ∀ t, dyadicValue (a t) t ≤ dyadicValue (a (t + 1)) (t + 1))
    (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m t : ℕ) :
    (∑ j ∈ Finset.range (wptr a E N m t), wmass a E m t j) ≤ (2 : ℝ≥0∞)⁻¹ ^ N m := by
  induction t with
  | zero => simp [wptr]
  | succ t ih =>
      by_cases htest : wtest a E N m (t + 1) (wptr a E N m t) = true
      · have hp : wptr a E N m (t + 1) = wptr a E N m t + 1 := by
          rw [wptr, ite_eq_left htest]
        rw [hp]
        exact (wtest_iff a E N m (t + 1) (wptr a E N m t)).1 htest
      · have hp : wptr a E N m (t + 1) = wptr a E N m t := by
          rw [wptr, ite_eq_right htest]
        rw [hp]
        refine le_trans (Finset.sum_le_sum fun j _ => ?_) ih
        exact wmass_antitone ha_mono E m j (Nat.le_succ t)

/-- Hence the emitted prefix has `α`-weight within budget. -/
lemma alphaSum_wptr_le {α : ℝ} (hα : 0 ≤ α) {a : ℕ → ℕ}
    (ha_le : ∀ t, dyadicValue (a t) t ≤ ENNReal.ofReal α)
    (ha_mono : ∀ t, dyadicValue (a t) t ≤ dyadicValue (a (t + 1)) (t + 1))
    (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m t : ℕ) :
    (∑ j ∈ Finset.range (wptr a E N m t),
        (E m j).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ N m :=
  le_trans (Finset.sum_le_sum fun j _ => alphaMass_le_wmass hα ha_le E m t j)
    (wptr_invariant ha_mono E N m t)



/-! ### The emitted enumeration stays within budget -/

/-- An emitted index carries the interval of its row, at the stage where the pointer passed it. -/
lemma wemit_ne_none {a : ℕ → ℕ} {E : ℕ → ℕ → Option BitString} {N : ℕ → ℕ} {m j : ℕ}
    (h : wemit a E N m j ≠ none) :
    wemit a E N m j = E m (Nat.unpair j).1 ∧
      wptr a E N m (Nat.unpair j).2 = (Nat.unpair j).1 + 1 ∧ 1 ≤ (Nat.unpair j).2 ∧
      wptr a E N m ((Nat.unpair j).2 - 1) = (Nat.unpair j).1 := by
  classical
  by_cases hc : wptr a E N m (Nat.unpair j).2 = (Nat.unpair j).1 + 1 ∧ 1 ≤ (Nat.unpair j).2 ∧
      wptr a E N m ((Nat.unpair j).2 - 1) = (Nat.unpair j).1
  · exact ⟨by simp only [wemit, ite_eq_left hc], hc.1, hc.2.1, hc.2.2⟩
  · exact absurd (by simp only [wemit, ite_eq_right hc]) h

/-- An interval of a row is emitted at most once. -/
lemma wemit_injOn {a : ℕ → ℕ} {E : ℕ → ℕ → Option BitString} {N : ℕ → ℕ} {m j j' : ℕ}
    (hj : wemit a E N m j ≠ none) (hj' : wemit a E N m j' ≠ none)
    (hk : (Nat.unpair j).1 = (Nat.unpair j').1) : j = j' := by
  obtain ⟨-, h1, h2, h3⟩ := wemit_ne_none hj
  obtain ⟨-, h1', h2', h3'⟩ := wemit_ne_none hj'
  have ht : (Nat.unpair j).2 = (Nat.unpair j').2 := by
    by_contra hne
    rcases Nat.lt_or_ge (Nat.unpair j).2 (Nat.unpair j').2 with hlt | hge
    · have hle : (Nat.unpair j).2 ≤ (Nat.unpair j').2 - 1 := by omega
      have := wptr_mono a E N m hle
      rw [h1, h3'] at this
      omega
    · have hlt' : (Nat.unpair j').2 < (Nat.unpair j).2 := by omega
      have hle : (Nat.unpair j').2 ≤ (Nat.unpair j).2 - 1 := by omega
      have := wptr_mono a E N m hle
      rw [h1', h3] at this
      omega
  have e1 := Nat.pair_unpair j
  have e2 := Nat.pair_unpair j'
  rw [← e1, ← e2, hk, ht]

/-- The trimmed enumeration of row `m` has total `α`-mass at most `2 ^ -N m`, whatever the
enumeration it trims. -/
lemma tsum_wemit_le {α : ℝ} (hα : 0 ≤ α) {a : ℕ → ℕ}
    (ha_le : ∀ t, dyadicValue (a t) t ≤ ENNReal.ofReal α)
    (ha_mono : ∀ t, dyadicValue (a t) t ≤ dyadicValue (a (t + 1)) (t + 1))
    (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m : ℕ) :
    (∑' j, (wemit a E N m j).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ N m := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  set f : BitString → ℝ≥0∞ := fun x => uniformMeasure (cantorCylinder x) ^ α with hf
  set T := S.sup (fun j => (Nat.unpair j).2) with hT
  set S' := S.filter (fun j => wemit a E N m j ≠ none) with hS'
  have hsum_eq : ∑ j ∈ S, (wemit a E N m j).elim 0 f = ∑ j ∈ S', (wemit a E N m j).elim 0 f := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro j hj hj'
    have hnone : wemit a E N m j = none := by
      by_contra hc
      exact hj' (Finset.mem_filter.2 ⟨hj, hc⟩)
    simp [hnone]
  have hmemS' : ∀ j ∈ S', wemit a E N m j ≠ none := fun j hj => (Finset.mem_filter.1 hj).2
  have hval : ∀ j ∈ S', (wemit a E N m j).elim 0 f = (E m (Nat.unpair j).1).elim 0 f := by
    intro j hj
    rw [(wemit_ne_none (hmemS' j hj)).1]
  have hlt : ∀ j ∈ S', (Nat.unpair j).1 < wptr a E N m T := by
    intro j hj
    obtain ⟨-, h1, -, -⟩ := wemit_ne_none (hmemS' j hj)
    have hle : (Nat.unpair j).2 ≤ T := Finset.le_sup (f := fun j => (Nat.unpair j).2)
      (Finset.mem_filter.1 hj).1
    have := wptr_mono a E N m hle
    omega
  have hinj : ∀ j ∈ S', ∀ j' ∈ S', (Nat.unpair j).1 = (Nat.unpair j').1 → j = j' :=
    fun j hj j' hj' h => wemit_injOn (hmemS' j hj) (hmemS' j' hj') h
  calc ∑ j ∈ S, (wemit a E N m j).elim 0 f
      = ∑ j ∈ S', (wemit a E N m j).elim 0 f := hsum_eq
    _ = ∑ j ∈ S', (E m (Nat.unpair j).1).elim 0 f := Finset.sum_congr rfl hval
    _ = ∑ k ∈ S'.image (fun j => (Nat.unpair j).1), (E m k).elim 0 f := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ k ∈ Finset.range (wptr a E N m T), (E m k).elim 0 f := by
        refine Finset.sum_le_sum_of_subset ?_
        intro k hk
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
        exact Finset.mem_range.2 (hlt j hj)
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ N m := alphaSum_wptr_le hα ha_le ha_mono E N m T


/-! ### The stage weights converge to the true weight -/

/-- The pointer advances by at most one per stage. -/
lemma wptr_succ_le (a : ℕ → ℕ) (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m t : ℕ) :
    wptr a E N m (t + 1) ≤ wptr a E N m t + 1 := by
  rw [wptr]
  split_ifs <;> omega

/-- For a single interval the stage weight is eventually within a factor `4` of
the true `α`-weight: from some stage on `(α - α_t)·l ≤ 1`, and `⌊α_t l⌋ > α_t l - 1`. -/
lemma exists_wmass_le {α : ℝ} (hα : 0 < α) {a : ℕ → ℕ}
    (ha_mono : ∀ t, dyadicValue (a t) t ≤ dyadicValue (a (t + 1)) (t + 1))
    (ha_sup : ⨆ t, dyadicValue (a t) t = ENNReal.ofReal α)
    (E : ℕ → ℕ → Option BitString) (m j : ℕ) :
    ∃ T, ∀ t, T ≤ t →
      wmass a E m t j
        ≤ 4 * ((E m j).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α)) := by
  cases hEj : E m j with
  | none => exact ⟨0, fun t _ => by simp [wmass, hEj]⟩
  | some x =>
      have hlpos : (0 : ℝ) < (x.length : ℝ) + 1 := by positivity
      have hlt : ENNReal.ofReal (α - 1 / ((x.length : ℝ) + 1)) < ⨆ t, dyadicValue (a t) t := by
        rw [ha_sup]
        refine (ENNReal.ofReal_lt_ofReal_iff hα).2 ?_
        have : (0 : ℝ) < 1 / ((x.length : ℝ) + 1) := by positivity
        linarith
      obtain ⟨T, hT⟩ := lt_iSup_iff.1 hlt
      refine ⟨T, fun t htT => ?_⟩
      refine le_trans (wmass_antitone ha_mono E m j htT) ?_
      -- the approximation at stage `T` is close enough
      have hntop : dyadicValue (a T) T ≠ ⊤ :=
        ENNReal.div_ne_top (by simp) (by positivity)
      have htoReal : (dyadicValue (a T) T).toReal = (a T : ℝ) / 2 ^ T := by
        rw [dyadicValue, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
          ENNReal.toReal_natCast]
      have hq : α - 1 / ((x.length : ℝ) + 1) ≤ (a T : ℝ) / 2 ^ T := by
        have h3 := ENNReal.toReal_mono hntop hT.le
        rw [htoReal] at h3
        by_cases hpos : 0 ≤ α - 1 / ((x.length : ℝ) + 1)
        · rwa [ENNReal.toReal_ofReal hpos] at h3
        · push Not at hpos
          exact le_trans hpos.le (by positivity)
      have hmul : (x.length : ℝ) * α - 1 ≤ (a T : ℝ) * (x.length : ℝ) / 2 ^ T := by
        have h1 : (α - 1 / ((x.length : ℝ) + 1)) * (x.length : ℝ)
            ≤ ((a T : ℝ) / 2 ^ T) * (x.length : ℝ) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
        have h2 : (x.length : ℝ) / ((x.length : ℝ) + 1) ≤ 1 := by
          rw [div_le_one hlpos]
          linarith
        have h3 : (α - 1 / ((x.length : ℝ) + 1)) * (x.length : ℝ)
            = (x.length : ℝ) * α - (x.length : ℝ) / ((x.length : ℝ) + 1) := by
          field_simp
        rw [h3] at h1
        have h4 : ((a T : ℝ) / 2 ^ T) * (x.length : ℝ) = (a T : ℝ) * (x.length : ℝ) / 2 ^ T := by
          ring
        rw [h4] at h1
        linarith
      have hexp : (x.length : ℝ) * α - 2 ≤ ((wexp a E m T j : ℕ) : ℝ) := by
        have hEj' : wexp a E m T j = a T * x.length / 2 ^ T := by simp [wexp_def, hEj]
        have hposd : 0 < 2 ^ T := pow_pos (by norm_num) T
        have hfl : a T * x.length < (a T * x.length / 2 ^ T + 1) * 2 ^ T :=
          (Nat.div_lt_iff_lt_mul hposd).1 (Nat.lt_succ_self _)
        have hflR : ((a T * x.length : ℕ) : ℝ)
            < (((a T * x.length / 2 ^ T : ℕ) : ℝ) + 1) * ((2 ^ T : ℕ) : ℝ) := by
          exact_mod_cast hfl
        have hposR : (0 : ℝ) < ((2 ^ T : ℕ) : ℝ) := by positivity
        have hdiv : (a T : ℝ) * (x.length : ℝ) / 2 ^ T
            < ((a T * x.length / 2 ^ T : ℕ) : ℝ) + 1 := by
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ T)]
          push_cast at hflR ⊢
          linarith
        rw [hEj']
        linarith
      -- conclude
      have hmass : wmass a E m T j = ((2 : ℝ≥0∞)⁻¹) ^ (wexp a E m T j) := by
        simp [wmass, hEj]
      rw [hmass]
      simp only [Option.elim_some, uniformMeasure_cantorCylinder]
      have hrpow1 : ((2 : ℝ≥0∞)⁻¹) ^ (wexp a E m T j)
          = ((2 : ℝ≥0∞)⁻¹) ^ ((wexp a E m T j : ℕ) : ℝ) :=
        (ENNReal.rpow_natCast _ _).symm
      have hrpow2 : (((2 : ℝ≥0∞)⁻¹) ^ x.length) ^ α
          = ((2 : ℝ≥0∞)⁻¹) ^ ((x.length : ℝ) * α) := by
        rw [← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) x.length, ← ENNReal.rpow_mul]
      have hsplit : ((2 : ℝ≥0∞)⁻¹) ^ ((x.length : ℝ) * α - 2)
          = 4 * ((2 : ℝ≥0∞)⁻¹) ^ ((x.length : ℝ) * α) := by
        rw [ENNReal.rpow_sub _ _ (by simp) (by simp)]
        have h2 : ((2 : ℝ≥0∞)⁻¹) ^ (2 : ℝ) = (4 : ℝ≥0∞)⁻¹ := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
          rw [← ENNReal.inv_pow]
          norm_num
        rw [h2, ENNReal.div_eq_inv_mul, inv_inv]
      rw [hrpow1, hrpow2, ← hsplit]
      exact ENNReal.rpow_le_rpow_of_exponent_ge inv_two_le_one hexp


/-! ### Every interval of a small row is eventually let through -/

/-- If the row's own `α`-mass is strictly inside its budget, the admission test eventually holds
at every stage for a fixed pointer. -/
lemma exists_wtest_true {α : ℝ} (hα : 0 < α) {a : ℕ → ℕ}
    (ha_mono : ∀ t, dyadicValue (a t) t ≤ dyadicValue (a (t + 1)) (t + 1))
    (ha_sup : ⨆ t, dyadicValue (a t) t = ENNReal.ofReal α)
    (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m : ℕ)
    (hsmall : (∑' k, (E m k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
      < (2 : ℝ≥0∞)⁻¹ ^ (N m + 3)) (p : ℕ) :
    ∃ T, ∀ t, T ≤ t → wtest a E N m t p = true := by
  classical
  choose Tj hTj using fun j => exists_wmass_le hα ha_mono ha_sup E m j
  refine ⟨(Finset.range (p + 1)).sup Tj, fun t ht => ?_⟩
  rw [wtest_iff]
  have hfinal : (4 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ (N m + 3)) ≤ (2 : ℝ≥0∞)⁻¹ ^ N m := by
    have hsplit : ((2 : ℝ≥0∞)⁻¹) ^ (N m + 3) = ((2 : ℝ≥0∞)⁻¹) ^ (N m + 1) * ((2 : ℝ≥0∞)⁻¹) ^ 2 := by
      rw [← pow_add]
    have hfour : (4 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 2 = 1 := by
      rw [← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ 2 = 4 by norm_num,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    calc (4 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ (N m + 3))
        = ((4 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 2) * ((2 : ℝ≥0∞)⁻¹) ^ (N m + 1) := by
          rw [hsplit]; ring
      _ = ((2 : ℝ≥0∞)⁻¹) ^ (N m + 1) := by rw [hfour, one_mul]
      _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ N m := inv_two_pow_antitone (by omega)
  calc (∑ j ∈ Finset.range (p + 1), wmass a E m t j)
      ≤ ∑ j ∈ Finset.range (p + 1),
          4 * ((E m j).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α)) := by
        refine Finset.sum_le_sum fun j hj => hTj j t (le_trans (Finset.le_sup hj) ht)
    _ = 4 * ∑ j ∈ Finset.range (p + 1),
          ((E m j).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α)) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * ∑' k, ((E m k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α)) := by
        gcongr
        exact ENNReal.sum_le_tsum _
    _ ≤ 4 * ((2 : ℝ≥0∞)⁻¹ ^ (N m + 3)) := by
        gcongr
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ N m := hfinal

/-- If the row's own `α`-mass is strictly inside its budget, the pointer passes every index, so
nothing is postponed for ever. -/
lemma exists_le_wptr {α : ℝ} (hα : 0 < α) {a : ℕ → ℕ}
    (ha_mono : ∀ t, dyadicValue (a t) t ≤ dyadicValue (a (t + 1)) (t + 1))
    (ha_sup : ⨆ t, dyadicValue (a t) t = ENNReal.ofReal α)
    (E : ℕ → ℕ → Option BitString) (N : ℕ → ℕ) (m : ℕ)
    (hsmall : (∑' k, (E m k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
      < (2 : ℝ≥0∞)⁻¹ ^ (N m + 3)) (k : ℕ) :
    ∃ t, k ≤ wptr a E N m t := by
  induction k with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
      obtain ⟨t₀, ht₀⟩ := ih
      obtain ⟨Tk, hTk⟩ := exists_wtest_true hα ha_mono ha_sup E N m hsmall k
      by_cases hgt : k + 1 ≤ wptr a E N m (max t₀ Tk)
      · exact ⟨max t₀ Tk, hgt⟩
      · have h1 : k ≤ wptr a E N m (max t₀ Tk) :=
          le_trans ht₀ (wptr_mono a E N m (le_max_left _ _))
        have heq : wptr a E N m (max t₀ Tk) = k := by omega
        refine ⟨max t₀ Tk + 1, ?_⟩
        rw [wptr, heq, ite_eq_left (hTk (max t₀ Tk + 1) (by omega))]

/-- An index the pointer has passed is emitted by the trimmed enumeration. -/
lemma exists_wemit_eq {a : ℕ → ℕ} {E : ℕ → ℕ → Option BitString} {N : ℕ → ℕ} {m k : ℕ}
    (h : ∃ t, k + 1 ≤ wptr a E N m t) : ∃ j, wemit a E N m j = E m k := by
  classical
  have hspec : k + 1 ≤ wptr a E N m (Nat.find h) := Nat.find_spec h
  have ht0pos : 1 ≤ Nat.find h := by
    by_contra hc
    push Not at hc
    have h0 : Nat.find h = 0 := by omega
    rw [h0] at hspec
    simp [wptr] at hspec
  have hprev : ¬ (k + 1 ≤ wptr a E N m (Nat.find h - 1)) := Nat.find_min h (by omega)
  have hstep : wptr a E N m (Nat.find h) ≤ wptr a E N m (Nat.find h - 1) + 1 := by
    have hsucc : Nat.find h - 1 + 1 = Nat.find h := by omega
    have hle := wptr_succ_le a E N m (Nat.find h - 1)
    rwa [hsucc] at hle
  have h1 : wptr a E N m (Nat.find h) = k + 1 := by omega
  have h2 : wptr a E N m (Nat.find h - 1) = k := by omega
  refine ⟨Nat.pair k (Nat.find h), ?_⟩
  simp only [wemit, Nat.unpair_pair]
  rw [ite_eq_left ⟨h1, ht0pos, h2⟩]

/-- The postponing trimming engine of SUV
Theorem 118(a) (§5.8, p. 173): for a *lower semicomputable* exponent `α` the
one-pass trimming of Theorem 117 is replaced by "do not reject permanently the
intervals that violate the requirements, but postpone them and check again when
a new approximation to `α` arrives".

Emit the interval `E m k` at the *first* stage `t` at which the running `w_t`-sum
of the intervals emitted so far, together with `E m k`, stays below `2^{-N m}`
(the "first stage" device of `Dimension/LowComplexityCover.lean`'s `firstStage`
keeps the multiplicity at one, which is what makes the emitted weight finite).
Everything in that test is decidable at each stage, so the emission is
computable.  For the weight bound: at every stage the `w_t`-weight of the emitted
finite set is `≤ 2^{-N m}` and the true `α`-weight is below it, and the emitted
set grows with `t`, so the total `α`-weight is at most `2^{-N m}`.  For the
covering: if the whole row has `α`-weight `< 2^{-(N m + 3)}`, then every finite
prefix of it has `w_t`-weight tending to at most `2·2^{-(N m + 3)} < 2^{-N m}`,
so each interval is eventually let through, and no interval is lost. -/
theorem exists_computable₂_postponeTrim_alphaCover (α : ℝ) (hα : 0 < α)
    (hlsc : IsLowerSemicomputableENNReal (ENNReal.ofReal α))
    (E : ℕ → ℕ → Option BitString) (hE : Computable₂ E) (N : ℕ → ℕ) (hN : Computable N) :
    ∃ T : ℕ → ℕ → Option BitString, Computable₂ T ∧
      (∀ m, (∑' k, (T m k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
        ≤ (2 : ℝ≥0∞)⁻¹ ^ N m) ∧
      (∀ m, (∑' k, (E m k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
          < (2 : ℝ≥0∞)⁻¹ ^ (N m + 3) →
        (⋃ k, (E m k).elim ∅ cantorCylinder) ⊆ ⋃ k, (T m k).elim ∅ cantorCylinder) := by
  obtain ⟨aa, ha_mono, ha_sup, ha_comp⟩ := hlsc
  have ha_le : ∀ t, dyadicValue (aa t) t ≤ ENNReal.ofReal α := by
    intro t
    rw [← ha_sup]
    exact le_iSup (fun s => dyadicValue (aa s) s) t
  refine ⟨wemit aa E N, computable_wemit ha_comp hE hN, fun m => ?_, fun m hsmall => ?_⟩
  · exact tsum_wemit_le hα.le ha_le ha_mono E N m
  · intro w hw
    obtain ⟨k, hwk⟩ := Set.mem_iUnion.1 hw
    obtain ⟨t, ht⟩ := exists_le_wptr hα ha_mono ha_sup E N m hsmall (k + 1)
    obtain ⟨j, hj⟩ := exists_wemit_eq ⟨t, ht⟩
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    rw [hj]
    exact hwk

/-- **SUV Theorem 118, the enumeration step (§5.8, p. 173)**, in the unfolded
form: the universal effective `α`-test for a lower semicomputable `α`.

The proof is the proof of `exists_universal_alphaTest_raw` verbatim, with the
one-pass `α`-trimming replaced by the postponing engine: the rows and the budgets
are the same, the budgets still sum to `2^{-den ε} ≤ ε`, and a row whose
`α`-weight obeys its budget is still let through in full. -/
theorem exists_universal_alphaTest_real_raw (α : ℝ) (hα : 0 < α)
    (hlsc : IsLowerSemicomputableENNReal (ENNReal.ofReal α)) :
    ∃ I : ℚ → ℕ → Option BitString, Computable₂ I ∧
      (∀ ε : ℚ, 0 < ε →
        (∑' k, (I ε k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
          ≤ ENNReal.ofReal (ε : ℝ)) ∧
      (∀ B : Set CantorSeq,
        (∃ J : ℚ → ℕ → Option BitString, Computable₂ J ∧ ∀ δ : ℚ, 0 < δ →
          B ⊆ (⋃ k, (J δ k).elim ∅ cantorCylinder) ∧
            (∑' k, (J δ k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
              < ENNReal.ofReal (δ : ℝ)) →
        ∀ ε : ℚ, 0 < ε → B ⊆ ⋃ k, (I ε k).elim ∅ cantorCylinder) := by
  obtain ⟨T, hTcomp, hTweight, hTcover⟩ :=
    exists_computable₂_postponeTrim_alphaCover α hα hlsc uaRow computable₂_uaRow uaLevel
      computable_uaLevel
  refine ⟨fun ε j => T (Nat.pair (ratCode ε) (Nat.unpair j).1) (Nat.unpair j).2, ?_, ?_, ?_⟩
  · have hm : Computable fun p : ℚ × ℕ => Nat.pair (ratCode p.1) (Nat.unpair p.2).1 :=
      Computable₂.comp Primrec₂.natPair.to_comp (computable_ratCode.comp Computable.fst)
        ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
    exact (hTcomp.comp hm ((Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp)).of_eq
      fun _ => rfl
  · -- the total `α`-weight of the test at accuracy `ε`
    intro ε hε
    have hre : (∑' j, (T (Nat.pair (ratCode ε) (Nat.unpair j).1)
          (Nat.unpair j).2).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
        = ∑' p : ℕ × ℕ, (T (Nat.pair (ratCode ε) p.1) p.2).elim 0
            (fun x => uniformMeasure (cantorCylinder x) ^ α) := by
      rw [← Equiv.tsum_eq Nat.pairEquiv (fun j : ℕ =>
        (T (Nat.pair (ratCode ε) (Nat.unpair j).1) (Nat.unpair j).2).elim 0
          (fun x => uniformMeasure (cantorCylinder x) ^ α))]
      exact tsum_congr fun p => by
        have h : Nat.unpair (Nat.pairEquiv p) = p := Equiv.symm_apply_apply Nat.pairEquiv p
        change (T (Nat.pair (ratCode ε) (Nat.unpair (Nat.pairEquiv p)).1)
            (Nat.unpair (Nat.pairEquiv p)).2).elim 0
              (fun x => uniformMeasure (cantorCylinder x) ^ α) = _
        rw [h]
    rw [hre, ENNReal.tsum_prod (f := fun c k => (T (Nat.pair (ratCode ε) c) k).elim 0
      (fun x => uniformMeasure (cantorCylinder x) ^ α))]
    calc (∑' (c : ℕ) (k : ℕ), (T (Nat.pair (ratCode ε) c) k).elim 0
            (fun x => uniformMeasure (cantorCylinder x) ^ α))
        ≤ ∑' c : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (ε.den + c + 1) := by
          refine ENNReal.tsum_le_tsum fun c => ?_
          have h1 := hTweight (Nat.pair (ratCode ε) c)
          rwa [uaLevel_pair] at h1
      _ = (2 : ℝ≥0∞)⁻¹ ^ ε.den := tsum_inv_two_pow_shift ε.den
      _ ≤ ENNReal.ofReal (ε : ℝ) := by
          rw [← dyadicValue_one_eq_inv_two_pow']
          exact dyadicValue_den_le_rat hε
  · -- every effective `α`-null set is covered
    rintro B ⟨J, hJcomp, hJ⟩ ε hε
    set hB : ℕ → ℕ → Option BitString := fun m k => J ((2 : ℚ)⁻¹ ^ m) k with hBdef
    have hBcomp : Computable₂ hB :=
      hJcomp.comp (computable_pow_half.comp Computable.fst) Computable.snd
    obtain ⟨c, hfaith, hcomplete⟩ := exists_code_candEnum_faithful hBcomp
    set L : ℕ := ε.den + c + 5 with hLdef
    set N : ℕ := ε.den + c + 1 with hNdef
    have hlev : ε.den + c + 4 + 1 = L := by rw [hLdef]
    have hδpos : (0 : ℚ) < (2 : ℚ)⁻¹ ^ L := by positivity
    have hδR : ENNReal.ofReal (((2 : ℚ)⁻¹ ^ L : ℚ) : ℝ) = (2 : ℝ≥0∞)⁻¹ ^ L := by
      rw [ofReal_pow_half_eq_dyadicValue, dyadicValue_one_eq_inv_two_pow']
    -- the row's `α`-weight is below its budget, so the engine lets it through
    have hrowsmall : (∑' s, (uaRow (Nat.pair (ratCode ε) c) s).elim 0
          (fun x => uniformMeasure (cantorCylinder x) ^ α))
        < (2 : ℝ≥0∞)⁻¹ ^ (uaLevel (Nat.pair (ratCode ε) c) + 3) := by
      rw [uaLevel_pair, uaRow_pair, ← hNdef]
      have hbound := tsum_firstCand_le α (h := hB) (c := c) (n := ε.den + c + 4)
        (fun s u hs => hfaith (ε.den + c + 4) s u hs)
      rw [hlev] at hbound
      refine lt_of_le_of_lt hbound ?_
      have hlt := (hJ ((2 : ℚ)⁻¹ ^ L) hδpos).2
      rw [hδR] at hlt
      refine lt_of_lt_of_le hlt ?_
      refine inv_two_pow_antitone ?_
      omega
    have hcovrow : (⋃ s, (uaRow (Nat.pair (ratCode ε) c) s).elim ∅ cantorCylinder)
        ⊆ ⋃ k, (T (Nat.pair (ratCode ε) c) k).elim ∅ cantorCylinder :=
      hTcover (Nat.pair (ratCode ε) c) hrowsmall
    have hBsub : B ⊆ ⋃ i, (hB L i).elim ∅ cantorCylinder := by
      have := (hJ ((2 : ℚ)⁻¹ ^ L) hδpos).1
      simpa [hBdef] using this
    have hcov : B ⊆ ⋃ s, (uaRow (Nat.pair (ratCode ε) c) s).elim ∅ cantorCylinder := by
      refine hBsub.trans ?_
      have hsub := iUnion_subset_iUnion_firstCand (h := hB) (c := c) (n := ε.den + c + 4)
        (fun i u hu => hcomplete (ε.den + c + 4) i u (by rwa [hlev]))
      rw [hlev] at hsub
      rw [uaRow_pair]
      exact hsub
    intro w hw
    obtain ⟨k, hwk⟩ := Set.mem_iUnion.1 (hcovrow (hcov hw))
    exact Set.mem_iUnion.2 ⟨Nat.pair c k, by simpa using hwk⟩

end Kolmogorov
