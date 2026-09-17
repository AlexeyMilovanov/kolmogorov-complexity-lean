/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.MonotoneComplexityBounds
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity

/-!
# A priori complexity is bounded by monotone complexity (SUV Theorem 85(e))

Feeding a computable stream map `D` with fair coin flips turns it into a probabilistic
generator (`streamMapGenerator`).  A monotone program `p` for `x` forces the whole
cylinder above `p` into the event "the output extends `x`", so the generated continuous
semimeasure at `x` is at least `2^(-l(p))`.  Maximality of the universal continuous
semimeasure then gives

`KA x ≤ KM_D(x) + O(1)`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- A computable stream map, run on a fair-coin input sequence, is a probabilistic
generator whose lower graph is the lower graph of the map. -/
def streamMapGenerator (D : BitStream → BitStream) (hD : IsComputableStreamMap D) :
    ProbabilisticGenerator where
  output w := D (.infinite w)
  lowerGraph := streamLowerGraph D
  lowerGraph_re := hD.2
  lowerGraph_sound := by
    intro p y hy w hw
    exact le_trans hy (hD.1.1 (show BitStream.finite p ≤ BitStream.infinite w from hw))
  lowerGraph_complete := by
    intro w y hy
    obtain ⟨n, hn⟩ := (continuousStreamMap_finite_le_infinite_iff D hD.1 w y).1 hy
    refine ⟨cantorPrefix w n, ?_, hn⟩
    exact (isCantorPrefix_iff_cantorPrefix_eq _ w).2 (by simp)

/-- A monotone program of length `n` for `x` forces at least mass `2^(-n)` onto `x`. -/
lemma inv_two_pow_le_generatedTreeSemimeasure_streamMapGenerator
    {D : BitStream → BitStream} (hD : IsComputableStreamMap D) {p x : BitString}
    (h : monotoneProduces D p x) :
    (2 : ℝ≥0∞)⁻¹ ^ p.length ≤ generatedTreeSemimeasure (streamMapGenerator D hD) x := by
  rw [generatedTreeSemimeasure, ← uniformMeasure_cantorCylinder p]
  exact measure_mono (fun w hw => (streamMapGenerator D hD).lowerGraph_sound h hw)

/-- **SUV Theorem 85(e)**: a priori complexity is bounded by monotone complexity up to an
additive constant. -/
theorem exists_const_KA_le_KMOf {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℝ, ∀ x : BitString, KA x ≤ ((KMOf D x).toNat : ℝ) + c := by
  obtain ⟨c, hc_top, hc⟩ := universalContinuousSemimeasure_isMaximal
    (generatedTreeSemimeasure (streamMapGenerator D hD.1))
    (generatedTreeSemimeasure_isLowerSemicomputableContinuousSemimeasure _)
  refine ⟨Real.logb 2 c.toReal, fun x => ?_⟩
  have hne : KMOf D x ≠ ⊤ := KMOf_ne_top_of_isOptimal hD x
  have hlt : KMOf D x < (((KMOf D x).toNat + 1 : ℕ) : ℕ∞) := by
    conv_lhs => rw [← ENat.natCast_toNat hne]
    exact_mod_cast Nat.lt_succ_self _
  obtain ⟨p, hp, hplen⟩ := (KMOf_lt_iff D x _).1 hlt
  have hple : p.length ≤ (KMOf D x).toNat := by
    have : p.length < (KMOf D x).toNat + 1 := by exact_mod_cast hplen
    omega
  refine KA_le_nat_add_log_of_inv_two_pow_le x _ c hc_top ?_
  calc (2 : ℝ≥0∞)⁻¹ ^ (KMOf D x).toNat
      ≤ (2 : ℝ≥0∞)⁻¹ ^ p.length := pow_le_pow_right_of_le_one' (by norm_num) hple
    _ ≤ generatedTreeSemimeasure (streamMapGenerator D hD.1) x :=
        inv_two_pow_le_generatedTreeSemimeasure_streamMapGenerator hD.1 hp
    _ ≤ c * universalContinuousSemimeasure x := hc x


/-- **SUV Theorem 85(f)**: an infinite sequence is computable if and only if the monotone
complexity of its prefixes is bounded. -/
noncomputable def constStreamMap (w : CantorSeq) : BitStream → BitStream := fun _ => .infinite w

/-- The map sending every input to the fixed sequence `w` is a continuous stream map. -/
lemma constStreamMap_isContinuous (w : CantorSeq) : IsContinuousStreamMap (constStreamMap w) := by
  constructor
  · intro x y h
    exact le_refl _
  · intro v y h
    exact h 0

/-- For a computable sequence the constant stream map is computable. -/
lemma constStreamMap_isComputable (w : CantorSeq) (hw : Computable w) :
    IsComputableStreamMap (constStreamMap w) := by
  constructor
  · exact constStreamMap_isContinuous w
  · have H : Computable (fun p : BitString × BitString => cantorPrefix w p.2.length) :=
      (computable_cantorPrefix w hw).comp (Primrec.to_comp (Primrec.list_length.comp Primrec.snd))
    have H2 : Computable (fun p : BitString × BitString =>
        decide (cantorPrefix w p.2.length = p.2)) :=
      (Primrec.to_comp (PrimrecPred.decide Primrec.eq)).comp (Computable.pair H Computable.snd)
    refine isRE_of_computable_bool _ _ (fun p => ?_) H2
    dsimp [streamLowerGraph, constStreamMap]
    rw [decide_eq_true_iff]
    have H_le : BitStream.finite p.2 ≤ BitStream.infinite w ↔ IsCantorPrefix p.2 w := Iff.rfl
    rw [H_le]
    exact (isCantorPrefix_iff_cantorPrefix_eq p.2 w).symm

/-- Relative to the decompressor that always outputs `w`, every prefix of `w` has monotone
complexity
zero. -/
lemma KMOf_constStreamMap_zero (w : CantorSeq) (n : ℕ) :
    KMOf (constStreamMap w) (cantorPrefix w n) = 0 := by
  apply le_antisymm
  · apply sInf_le
    use []
    constructor
    · dsimp [monotoneProduces, constStreamMap]
      have H_le : BitStream.finite (cantorPrefix w n) ≤ BitStream.infinite w ↔
          IsCantorPrefix (cantorPrefix w n) w := Iff.rfl
      rw [H_le]
      rw [isCantorPrefix_iff_cantorPrefix_eq]
      simp
    · rfl
  · exact bot_le

/-- **SUV Theorem 85(f)**: an infinite sequence is computable if and only if the monotone
complexity of its prefixes is bounded. -/
theorem computable_iff_KMOf_prefixes_bounded {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) (w : CantorSeq) :
    Computable w ↔ ∃ c : ℕ, ∀ n, KMOf D (cantorPrefix w n) ≤ c := by
  constructor
  · intro hw
    obtain ⟨c, hc⟩ := hD.2 _ (constStreamMap_isComputable w hw)
    use c
    intro n
    have := hc (cantorPrefix w n)
    rw [KMOf_constStreamMap_zero] at this
    exact le_trans this (le_of_eq (zero_add _))
  · rintro ⟨c, hc⟩
    rw [computable_iff_KA_prefixes_bounded]
    obtain ⟨c_a, hc_a⟩ := exists_const_KA_le_KMOf hD
    use (c : ℝ) + c_a
    intro n
    have h1 := hc_a (cantorPrefix w n)
    have h2 := hc n
    calc KA (cantorPrefix w n)
      _ ≤ ((KMOf D (cantorPrefix w n)).toNat : ℝ) + c_a := h1
      _ ≤ (c : ℝ) + c_a := by
        have h3 : (KMOf D (cantorPrefix w n)).toNat ≤ c := by
          have h_le := h2
          rw [← ENat.natCast_toNat (KMOf_ne_top_of_isOptimal hD (cantorPrefix w n))] at h_le
          exact ENat.natCast_le_natCast.mp h_le
        have h4 : ((KMOf D (cantorPrefix w n)).toNat : ℝ) ≤ (c : ℝ) := Nat.cast_le.mpr h3
        linarith
end Kolmogorov
