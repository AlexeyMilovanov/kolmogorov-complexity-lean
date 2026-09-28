/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.AlgorithmicRandomness.Trim
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.MonotoneComplexity.Dimension.PostponeTrim
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayTestComputable
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionDyadic

/-!
# Computability tools for SUV Section 5.7.5–5.7.6

Four elementary, **proved** computability facts that Sections 5.7.5–5.7.6 use silently:

* `computable_ratLe` — the order of `ℚ` is decidable *computably*
  (`RatComputable.lean` only supplies the special case `q ≤ 1`);
* `computable_inv_two_pow_rat` — `k ↦ 2^{-k}` is a computable rational sequence;
  together these two give the rounding `⌈−log₂ rᵢ⌉` of SUV p. 165 by bounded search;
* `computable_symm_of_bijective` — the inverse of a computable bijection of `ℕ` is
  computable (SUV p. 167, "consider some computable permutation `π`": the source uses
  `π⁻¹` as freely as `π`);
* `IsLSC.comp_left` and `isLowerSemicomputableSemimeasureNat_comp` — a lower
  semicomputable semimeasure on `ℕ` stays one after a computable rearrangement of the
  index set.  This is the whole content of "a computable permutation changes the a priori
  probability only by a constant factor" (SUV p. 167) once maximality is applied.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Computable rational comparisons -/

/-- The dyadic rational sequence `k ↦ 2^{-k}` is computable. -/
theorem computable_inv_two_pow_rat : Computable (fun k : ℕ => ((2 : ℚ)⁻¹) ^ k) := by
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun k : ℕ => 2 ^ k)
    (Computable.const 1) Computable.pow2 (fun k => pow_pos (by norm_num : (0 : ℕ) < 2) k)
    (fun k => ?_)
  push_cast
  rw [inv_pow, one_div]

/-- The rational sequence `k ↦ 2^k` is computable. -/
theorem computable_two_pow_rat : Computable (fun k : ℕ => ((2 : ℚ) ^ k)) := by
  refine computable_of_num_den (N := fun k : ℕ => ((2 ^ k : ℕ) : ℤ)) (D := fun _ : ℕ => 1)
    (ComputableReals.primrec_natCastInt.to_comp.comp Computable.pow2) (Computable.const 1)
    (fun _ => Nat.one_pos) (fun k => ?_)
  push_cast
  ring

/-- A `foldr`-encoded bounded disjunction is true exactly when some member of the list
satisfies the test.  This is the shape in which a bounded existential over a merely
*computable* (not primitive recursive) enumerator is available. -/
theorem foldr_or_eq_true_iff {α : Type*} (f : α → Bool) (l : List α) :
    (l.foldr (fun a b => f a || b) false = true) ↔ ∃ a ∈ l, f a = true := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-! ### The inverse of a computable permutation of `ℕ` -/

/-- **SUV p. 167.** The inverse of a computable bijection of `ℕ` is computable: the
unique preimage is found by unbounded search (`Computable.inverse`). -/
theorem computable_symm_of_bijective {π : ℕ → ℕ} (hπ : Function.Bijective π)
    (hπc : Computable π) : Computable (Equiv.ofBijective π hπ).symm := by
  have hsurj : ∀ y, ∃ x, π x = y := hπ.surjective
  refine (Computable.inverse π hπc hsurj).of_eq (fun y => ?_)
  refine hπ.injective ?_
  rw [Nat.find_spec (hsurj y)]
  exact ((Equiv.ofBijective π hπ).apply_symm_apply y).symm

/-! ### Lower semicomputability under a computable rearrangement of the index set -/

/-- Lower semicomputability is preserved by precomposition with a computable map of the
output coordinate: an approximation for `f` at `σ x` is an approximation for
`f ∘ σ` at `x`. -/
theorem IsLSC.comp_left {f : BitString → BitString → ℝ≥0∞} (hf : IsLSC f)
    {σ : BitString → BitString} (hσ : Computable σ) :
    IsLSC (fun x ctx => f (σ x) ctx) := by
  obtain ⟨A, hmono, hsup, hA⟩ := hf
  refine ⟨fun s x ctx => A s (σ x) ctx, fun s x ctx => hmono s (σ x) ctx,
    fun x ctx => hsup (σ x) ctx, ?_⟩
  exact hA.comp (Computable.fst.pair
    ((hσ.comp (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd)))

/-- **SUV p. 167.** A lower semicomputable semimeasure on `ℕ` stays one after a
computable *bijective* rearrangement of the index set: the total mass is unchanged
(`Equiv.tsum_eq`) and lower semicomputability is `IsLSC.comp_left`. -/
theorem isLowerSemicomputableSemimeasureNat_comp {m : ℕ → ℝ≥0∞}
    (hm : IsLowerSemicomputableSemimeasureNat m) {σ : ℕ → ℕ}
    (hσb : Function.Bijective σ) (hσ : Computable σ) :
    IsLowerSemicomputableSemimeasureNat (fun n => m (σ n)) := by
  constructor
  · change (∑' x : BitString, m (σ (bitStringToNat x))) ≤ 1
    calc (∑' x : BitString, m (σ (bitStringToNat x)))
        = ∑' n : ℕ, m (σ n) := tsum_comp_bitStringToNat (fun n => m (σ n))
      _ = ∑' n : ℕ, m n := (Equiv.ofBijective σ hσb).tsum_eq m
      _ ≤ 1 := hm.tsum_le_one
  · have hcomp : Computable (fun x : BitString => natToBitString (σ (bitStringToNat x))) :=
      computable_natToBitString.comp (hσ.comp computable_bitStringToNat)
    simpa using hm.2.comp_left hcomp

/-- The sum of a list of naturals is primitive
recursive (`List.sum` is a `foldr`, and `Primrec.list_foldr` covers it). -/
theorem primrec_listSum : Primrec (fun l : List ℕ => l.sum) := by
  refine (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq (fun l => ?_)
  induction l with
  | nil => rfl
  | cons a t ih => simpa using ih

/-- The dyadic value of a finite sum splits. -/
theorem dyadicValue_sum_range (s : ℕ) (f : ℕ → ℕ) :
    dyadicValue (∑ j ∈ Finset.range s, f j) s
      = ∑ j ∈ Finset.range s, dyadicValue (f j) s := by
  simp only [dyadicValue, Nat.cast_sum, ENNReal.div_eq_inv_mul, Finset.mul_sum]

/-- A *computable* sequence of rationals is in
particular a lower semicomputable `ℕ`-indexed nonnegative function: the dyadic floors
`⌊rᵢ·2ˢ⌋/2ˢ` of `RatComputable.lean` are a computable non-decreasing approximation
converging to `ENNReal.ofReal rᵢ`.  This is the "note that `rᵢ = O(m(i))`" step of
SUV p. 165. -/
theorem isLSC_ofReal_of_computable {r : ℕ → ℚ} (hr : Computable r) :
    IsLSC (fun (x _ : BitString) => ENNReal.ofReal ((r (bitStringToNat x) : ℚ) : ℝ)) := by
  refine ⟨fun s x _ => ratDyadicFloor (r (bitStringToNat x)) s, ?_, ?_, ?_⟩
  · exact fun s out _ => dyadicValue_ratDyadicFloor_mono_of_le (le_refl _) s
  · intro out _
    simpa using
      iSup_dyadicValue_ratDyadicFloor (f := fun _ : ℕ => r (bitStringToNat out)) monotone_const
  · exact computable_ratDyadicFloor.comp
      (hr.comp (computable_bitStringToNat.comp (Computable.fst.comp Computable.snd)))
      Computable.fst

/-- **SUV p. 157, machine-free.**  The discrete a priori probability is strictly positive at
every index: it dominates the computable semimeasure `k ↦ 2^{-(k+1)}`, whose total mass is
exactly `1`.  Unlike `apriori_pos` this needs no optimal machine, so it is available in the
statements of §5.7.6 that quantify over `m` alone. -/
theorem apriori_pos_of_universal {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) (n : ℕ) :
    0 < m n := by
  have hcomp : Computable (fun k : ℕ => ((2 : ℚ)⁻¹) ^ (k + 1)) :=
    computable_inv_two_pow_rat.comp
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1)).to_comp
  have hsm : IsLowerSemicomputableSemimeasureNat
      (fun k : ℕ => ENNReal.ofReal (((((2 : ℚ)⁻¹) ^ (k + 1) : ℚ)) : ℝ)) := by
    refine ⟨?_, isLSC_ofReal_of_computable hcomp⟩
    change (∑' x : BitString,
      ENNReal.ofReal (((((2 : ℚ)⁻¹) ^ (bitStringToNat x + 1) : ℚ)) : ℝ)) ≤ 1
    rw [tsum_comp_bitStringToNat
      (fun k : ℕ => ENNReal.ofReal (((((2 : ℚ)⁻¹) ^ (k + 1) : ℚ)) : ℝ)),
      tsum_congr (fun k : ℕ => ofReal_rat_inv_two_pow (k + 1))]
    simpa using (tsum_inv_two_pow_shift 0).le
  obtain ⟨c, hc, hdom⟩ := hm.dominates hsm
  refine lt_of_lt_of_le ?_ (hdom n)
  refine ENNReal.mul_pos hc.ne' ?_
  rw [ofReal_rat_inv_two_pow]
  exact pow_ne_zero _ (by simp)

end Kolmogorov
