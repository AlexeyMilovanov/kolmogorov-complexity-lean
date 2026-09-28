import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.AlgorithmicRandomness.LSCConstruction
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.DyadicEnumeration
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.MonotoneLimits

/-!
# The four descriptions of a lower-semicomputable function

`lowerSemicomputableFun_characterizations` is the endpoint of this group: for a function
`f : CantorSeq → ℝ≥0∞`, lower semicomputability is equivalent to each of the three standard
presentations of SUV Theorem 40 — a supremum of computable basic functions, a monotone limit
of such functions, and a sum of computable nonnegative basic functions.

The implication proved here is the one from a sum to a monotone limit
(`isMonotoneLimit_of_isSum`), through the partial sums `monotoneApprox` kept in dyadic
numerator form: `monotoneApprox_take` bounds how much of the argument a stage reads,
`approx_mono` and `approx_val_eq_sum` identify its value, and `monotoneApprox_comp` gives
computability.  The other implications come from `DyadicEnumeration` and `MonotoneLimits`.
-/

namespace Kolmogorov
open MeasureTheory Topology
open scoped ENNReal NNReal

/-- The stage-`s` partial sum of a family of dyadic terms, kept in numerator form: the value at
stage `s` is `2^{-s}` times `monotoneApprox term s x`. -/
def monotoneApprox (term : ℕ → BitString → ℕ) : ℕ → BitString → ℕ
| 0, x => term 0 (x.take 0)
| s + 1, x => 2 * monotoneApprox term s x + term (s + 1) (x.take (s + 1))

/-- The stage-`s` partial sum only reads the first `s` bits of its argument. -/
lemma monotoneApprox_take (term : ℕ → BitString → ℕ) (s : ℕ) :
    ∀ (x : BitString) (m : ℕ), s ≤ m →
      monotoneApprox term s (x.take m) = monotoneApprox term s x := by
  induction s with
  | zero =>
    intro x m h
    change term 0 (List.take 0 (x.take m)) = term 0 (x.take 0)
    rw [List.take_take, Nat.min_eq_left (by omega)]
  | succ s ih =>
    intro x m h
    change 2 * monotoneApprox term s (x.take m) + term (s + 1) (List.take (s + 1) (x.take m)) = 2 *
        monotoneApprox term s x + term (s + 1) (x.take (s + 1))
    rw [ih x m (by omega), List.take_take, Nat.min_eq_left h]

/-- The dyadic values of the partial sums increase with the stage, the terms being
nonnegative. -/
lemma approx_mono (term : ℕ → BitString → ℕ) (w : CantorSeq) (s : ℕ) :
    dyadicValue (monotoneApprox term s (cantorPrefix w s)) s ≤ dyadicValue
        (monotoneApprox term (s + 1) (cantorPrefix w (s + 1))) (s + 1) := by
  have h1 : monotoneApprox term (s + 1) (cantorPrefix w (s + 1)) =
      2 * monotoneApprox term s (cantorPrefix w (s + 1)) +
        term (s + 1) (cantorPrefix w (s + 1)) := by
    change 2 * monotoneApprox term s (cantorPrefix w (s + 1)) + term (s + 1)
        (List.take (s + 1) (cantorPrefix w (s + 1))) = _
    have hl : (cantorPrefix w (s + 1)).length = s + 1 := cantorPrefix_length w (s + 1)
    rw [List.take_of_length_le (by omega)]
  have h2 : monotoneApprox term s (cantorPrefix w (s + 1)) =
      monotoneApprox term s (cantorPrefix w s) := by
    have ht : cantorPrefix w s = (cantorPrefix w (s + 1)).take s := by
      exact (cantorPrefix_take w s (s + 1) (by omega)).symm
    rw [ht, monotoneApprox_take term s (cantorPrefix w (s + 1)) s (by omega)]
  rw [h1, h2]
  have hd : dyadicValue (monotoneApprox term s (cantorPrefix w s) * 2) (s + 1) = dyadicValue
      (monotoneApprox term s (cantorPrefix w s)) s := by
    have h_pow : monotoneApprox term s (cantorPrefix w s) * 2 ^ (s + 1 - s) = monotoneApprox term s
        (cantorPrefix w s) * 2 := by
      have : s + 1 - s = 1 := by omega
      rw [this, pow_one]
    rw [← h_pow]
    exact dyadicValue_mul_two_pow_sub
      (monotoneApprox term s (cantorPrefix w s)) (s + 1) s (by omega)
  have hadd : dyadicValue
      (2 * monotoneApprox term s (cantorPrefix w s) +
        term (s + 1) (cantorPrefix w (s + 1))) (s + 1) =
    dyadicValue (2 * monotoneApprox term s (cantorPrefix w s)) (s + 1) + dyadicValue
        (term (s + 1) (cantorPrefix w (s + 1))) (s + 1) := by
    unfold dyadicValue
    push_cast
    exact ENNReal.add_div
  rw [mul_comm] at hd
  rw [hadd, hd]
  exact self_le_add_right _ _

/-- The stage-`s` partial sum evaluates to the sum of the first `s + 1` dyadic terms along the
sequence. -/
lemma approx_val_eq_sum (term : ℕ → BitString → ℕ) (w : CantorSeq) (s : ℕ) :
    dyadicValue (monotoneApprox term s (cantorPrefix w s)) s = ∑ i ∈ Finset.range (s + 1),
        dyadicValue (term i (cantorPrefix w i)) i := by
  induction s with
  | zero =>
    dsimp [monotoneApprox]
    simp [cantorPrefix]
  | succ s ih =>
    have h1 : monotoneApprox term (s + 1) (cantorPrefix w (s + 1)) =
        2 * monotoneApprox term s (cantorPrefix w (s + 1)) +
          term (s + 1) (cantorPrefix w (s + 1)) := by
      change 2 * monotoneApprox term s (cantorPrefix w (s + 1)) + term (s + 1)
          (List.take (s + 1) (cantorPrefix w (s + 1))) = _
      have hl : (cantorPrefix w (s + 1)).length = s + 1 := cantorPrefix_length w (s + 1)
      rw [List.take_of_length_le (by omega)]
    have h2 : monotoneApprox term s (cantorPrefix w (s + 1)) =
        monotoneApprox term s (cantorPrefix w s) := by
      have ht : cantorPrefix w s = (cantorPrefix w (s + 1)).take s := by
        exact (cantorPrefix_take w s (s + 1) (by omega)).symm
      rw [ht, monotoneApprox_take term s (cantorPrefix w (s + 1)) s (by omega)]
    rw [h1, h2, Finset.sum_range_succ, ← ih]
    have hd : dyadicValue (monotoneApprox term s (cantorPrefix w s) * 2) (s + 1) = dyadicValue
        (monotoneApprox term s (cantorPrefix w s)) s := by
      have h_pow : monotoneApprox term s (cantorPrefix w s) * 2 ^ (s + 1 - s) =
          monotoneApprox term s (cantorPrefix w s) * 2 := by
        have : s + 1 - s = 1 := by omega
        rw [this, pow_one]
      rw [← h_pow]
      exact dyadicValue_mul_two_pow_sub
        (monotoneApprox term s (cantorPrefix w s)) (s + 1) s (by omega)
    unfold dyadicValue at hd ⊢
    push_cast at hd ⊢
    rw [ENNReal.add_div, mul_comm]
    congr 1

/-- The partial sums of a computable family of dyadic terms are computable in the stage and the
string. -/
lemma monotoneApprox_comp {term : ℕ → BitString → ℕ}
    (hcomp_c : Computable fun p : ℕ × BitString => term p.1 p.2) :
    Computable (fun p : ℕ × BitString => monotoneApprox term p.1 p.2) := by
  have h_eq : (fun p : ℕ × BitString => monotoneApprox term p.1 p.2) =
      fun p : ℕ × BitString => Nat.rec (term 0 (p.2.take 0))
          (fun y ih => 2 * ih + term (y + 1) (p.2.take (y + 1))) p.1 := by
    funext p
    rcases p with ⟨s, x⟩
    induction s with
    | zero => rfl
    | succ s ih => dsimp [monotoneApprox]; rw [ih]; rfl
  rw [h_eq]
  refine Computable.nat_rec (g := fun p : ℕ × BitString => term 0 (p.2.take 0))
    (h := fun (p : ℕ × BitString) (p2 : ℕ × ℕ) => 2 * p2.2 + term (p2.1 + 1) (p.2.take (p2.1 + 1)))
    Computable.fst ?_ ?_
  · exact hcomp_c.comp (Computable.pair (Computable.const 0) (Computable₂.comp
      Primrec.list_take.to_comp Computable.snd (Computable.const 0)))
  · exact Computable₂.comp Primrec.nat_add.to_comp
      (Computable₂.comp Primrec.nat_mul.to_comp (Computable.const 2) (Computable.snd.comp
          Computable.snd))
      (hcomp_c.comp (Computable.pair
        (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
        (Computable₂.comp Primrec.list_take.to_comp
          (Computable.snd.comp Computable.fst)
          (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)))))

/-- A sum of computable nonnegative basic functions is a monotone limit of computable basic
functions. -/
lemma isMonotoneLimit_of_isSum {f : CantorSeq → ℝ≥0∞}
    (hf : IsSumOfComputableNonnegativeBasicFunctions f) :
        IsMonotoneLimitOfComputableBasicFunctions f := by
  rcases hf with ⟨term, hcomp, hsum⟩
  refine ⟨monotoneApprox term, monotoneApprox_comp hcomp,
    fun s w => approx_mono term w s, fun w => ?_⟩
  rw [hsum w]
  have heq : ∀ s, dyadicValue (monotoneApprox term s (cantorPrefix w s)) s = ∑ i ∈ Finset.range
      (s + 1), dyadicValue (term i (cantorPrefix w i)) i := approx_val_eq_sum term w
  simp_rw [heq]
  have ht : (⨆ s, ∑ i ∈ Finset.range (s + 1), dyadicValue (term i (cantorPrefix w i)) i) = ∑' i,
      dyadicValue (term i (cantorPrefix w i)) i := by
    rw [ENNReal.tsum_eq_iSup_nat]
    apply le_antisymm
    · exact iSup_le fun s => le_iSup_of_le (s + 1) le_rfl
    · refine iSup_le fun s => ?_
      cases s with
      | zero => simp
      | succ s => exact le_iSup_of_le s le_rfl
  exact ht.symm
/-- Lower semicomputability of a function on Cantor space is equivalent to each of the three
standard descriptions: a supremum, a monotone limit, and a sum of computable basic functions. -/
theorem lowerSemicomputableFun_characterizations (f : CantorSeq → ℝ≥0∞) :
    (IsLowerSemicomputableFun f ↔ IsSupremumOfComputableBasicFunctions f) ∧
    (IsLowerSemicomputableFun f ↔ IsMonotoneLimitOfComputableBasicFunctions f) ∧
    (IsLowerSemicomputableFun f ↔ IsSumOfComputableNonnegativeBasicFunctions f) := by
  have h1 : IsLowerSemicomputableFun f ↔ IsSupremumOfComputableBasicFunctions f :=
    ⟨isSupremum_of_isLowerSemicomputableFun, isLowerSemicomputableFun_of_isSupremum⟩
  have h2 : IsSupremumOfComputableBasicFunctions f ↔ IsMonotoneLimitOfComputableBasicFunctions f :=
    ⟨isMonotoneLimit_of_isSupremum, isSupremum_of_isMonotoneLimit⟩
  have h3 : IsMonotoneLimitOfComputableBasicFunctions f ↔
      IsSumOfComputableNonnegativeBasicFunctions f :=
    ⟨isSum_of_isMonotoneLimit_proof, isMonotoneLimit_of_isSum⟩
  exact ⟨h1, h1.trans h2, (h1.trans h2).trans h3⟩

end Kolmogorov
