import KolmogorovMathlib.Entropy.Complexity.Basic
import KolmogorovMathlib.Entropy.Coding
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import KolmogorovMathlib.MonotoneComplexity.MonotoneComplexityBounds
import KolmogorovMathlib.MonotoneComplexity.ArithmeticCoding
import KolmogorovMathlib.AlgorithmicRandomness.BlockMap
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.DyadicEnumeration

/-!
# The expected monotone complexity of an i.i.d. word

SUV Problem 236, p. 228.

The expected monotone complexity of an i.i.d. binary word `ξ^N`, with no condition `N`, is at
most `N H(ξ) + O(1)` for every rational distribution on two letters
(`exists_expect_KMOf_le_mul_entropyDist`).  The Bernoulli measure with rational parameter is
computable, and the monotone complexity of a word is at most the negative logarithm of its
probability up to a constant.
-/

namespace Kolmogorov

open Finset

open scoped ENNReal

/-! ### Monotone complexity -/

/-- Exponentiation of a rational base by a natural exponent is computable in both arguments. -/
private lemma computable_ratPow : Computable (fun z : ℚ × ℕ => z.1 ^ z.2) := by
  let step : ℚ × ℕ → ℕ × ℚ → ℚ := fun z q => q.2 * z.1
  have hstep : Computable (fun z : (ℚ × ℕ) × (ℕ × ℚ) => step z.1 z.2) :=
    computable₂_ratMul.comp (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.fst)
  have hrec := Computable.nat_rec (h := step) Computable.snd
    (Computable.const 1) hstep.to₂
  exact hrec.of_eq fun z => by
    induction z.2 with
    | zero => simp
    | succ n ih => simp only [step, ih, pow_succ, mul_comm]

/-- The number of `false` bits in a bit string is computable. -/
private lemma count_false_computable :
    Computable (fun x : BitString => x.count false) := by
  have hsub : Computable (fun x : BitString => x.length - x.count true) :=
    Primrec.nat_sub.to_comp.comp Primrec.list_length.to_comp primrec_count_true.to_comp
  exact hsub.of_eq fun x => by
    rw [← count_true_add_count_false x]
    exact Nat.add_sub_cancel_left _ _

/-- The exact rational cylinder mass of a Bernoulli measure with rational parameter `pq`:
`pq^(#true) · (1 - pq)^(#false)`. -/
private def bernRatMass (pq : ℚ) (x : BitString) : ℚ :=
  pq ^ x.count true * (1 - pq) ^ x.count false

/-- The rational cylinder mass is computable in the string, for a fixed parameter. -/
private lemma bernRatMass_computable (pq : ℚ) :
    Computable (fun x : BitString => bernRatMass pq x) := by
  have h1 := computable_ratPow.comp ((Computable.const pq).pair primrec_count_true.to_comp)
  have h2 := computable_ratPow.comp ((Computable.const (1 - pq)).pair count_false_computable)
  exact (computable₂_ratMul.comp h1 h2).of_eq fun x => rfl

/-- The dyadic-floor approximation of the rational cylinder mass. -/
private def bernMassApprox (pq : ℚ) (x : BitString) (s : ℕ) : ℕ :=
  ratDyadicFloor (bernRatMass pq x) s

/-- The dyadic-floor approximation is computable in the string and the precision. -/
private lemma bernMassApprox_computable (pq : ℚ) : Computable₂ (bernMassApprox pq) := by
  have hmass : Computable (fun z : BitString × ℕ => bernRatMass pq z.1) :=
    (bernRatMass_computable pq).comp Computable.fst
  exact (computable_ratDyadicFloor.comp hmass Computable.snd).of_eq fun z => rfl

/-- The Bernoulli cylinder mass equals `ENNReal.ofReal` of its exact rational value. -/
private lemma cantorMass_bern_eq_ofReal (p : NNReal) (hp : p ≤ 1) (pq : ℚ)
    (hpqr : (p : ℝ) = pq) (x : BitString) :
    cantorMass (bernoulliMeasure p hp) x = ENNReal.ofReal (bernRatMass pq x : ℝ) := by
  have hne : cantorMass (bernoulliMeasure p hp) x ≠ ⊤ := by
    unfold cantorMass; exact MeasureTheory.measure_ne_top _ _
  have hpENN : (p : ℝ≥0∞) ≤ 1 := by exact_mod_cast hp
  have htoReal : (cantorMass (bernoulliMeasure p hp) x).toReal =
      (p : ℝ) ^ x.count true * (1 - (p : ℝ)) ^ x.count false := by
    rw [cantorMass_bernoulliMeasure_prod, prod_map_ite_bool,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hpENN (by simp)]
    simp
  have hbern : (bernRatMass pq x : ℝ) =
      (p : ℝ) ^ x.count true * (1 - (p : ℝ)) ^ x.count false := by
    rw [bernRatMass]; push_cast; rw [hpqr]
  rw [← ENNReal.ofReal_toReal hne, htoReal, hbern]

/-- The Bernoulli measure with rational parameter is computable, through the exact rational mass
and its dyadic floors. -/
private lemma isComputableMeasure_bernRat (p : NNReal) (hp : p ≤ 1) (pq : ℚ)
    (hpq0 : 0 ≤ pq) (hpq1 : pq ≤ 1) (hpqr : (p : ℝ) = pq) :
    IsComputableMeasure (bernoulliMeasure p hp) := by
  apply isComputableMeasure_of_dyadicFloorApprox (a := bernMassApprox pq)
    (bernMassApprox_computable pq)
  intro x s
  have hmass := cantorMass_bern_eq_ofReal p hp pq hpqr x
  have hbern0 : (0 : ℚ) ≤ bernRatMass pq x :=
    mul_nonneg (pow_nonneg hpq0 _) (pow_nonneg (by linarith) _)
  have hdpos : (0 : ℝ) < ((2 ^ s : ℕ) : ℝ) := by positivity
  have hfloor : ((bernMassApprox pq x s : ℕ) : ℝ) ≤
      (bernRatMass pq x : ℝ) * ((2 ^ s : ℕ) : ℝ) := by
    rw [bernMassApprox, ratDyadicFloor_eq_floor]
    exact_mod_cast Nat.floor_le (mul_nonneg hbern0 (by positivity))
  have hceil : (bernRatMass pq x : ℝ) * ((2 ^ s : ℕ) : ℝ) ≤
      ((bernMassApprox pq x s : ℕ) : ℝ) + 1 := by
    rw [bernMassApprox, ratDyadicFloor_eq_floor]
    exact_mod_cast (Nat.lt_floor_add_one (bernRatMass pq x * (2 ^ s : ℕ))).le
  refine ⟨?_, ?_⟩
  · rw [dyadicValue_eq_ofReal, hmass]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ hdpos]
    exact hfloor
  · rw [hmass, dyadicValue_eq_ofReal, dyadicValue_eq_ofReal,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← add_div, le_div_iff₀ hdpos]
    push_cast
    push_cast at hceil
    linarith [hceil]

/-- The pointwise coding bound in logarithmic form: an optimal monotone decompressor codes `x`
in at most `-log₂ m + c` bits, when the weight bound `2^{-c} · m ≤ 2^{-KM(x)}` holds and `m` is a
finite nonzero mass. -/
private lemma KMOf_toNat_le_neg_logb_of_weight {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) (c : ℕ) (x : BitString) {m : ℝ≥0∞}
    (hm0 : m ≠ 0) (hmtop : m ≠ ⊤)
    (hw : (2 : ℝ≥0∞)⁻¹ ^ c * m ≤ complexityWeight (KMOf D x)) :
    ((KMOf D x).toNat : ℝ) ≤ -Real.logb 2 m.toReal + c := by
  have hk : KMOf D x ≠ ⊤ := KMOf_ne_top_of_isOptimal hD x
  have hcw : complexityWeight (KMOf D x) = (2 : ℝ≥0∞)⁻¹ ^ (KMOf D x).toNat := by
    conv_lhs => rw [← ENat.natCast_toNat hk]
    rw [complexityWeight_coe]
  rw [hcw] at hw
  have hmR : 0 < m.toReal := ENNReal.toReal_pos hm0 hmtop
  have e1 : ((2 : ℝ≥0∞)⁻¹ ^ c * m).toReal = (2 : ℝ)⁻¹ ^ c * m.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  have e2 : ((2 : ℝ≥0∞)⁻¹ ^ (KMOf D x).toNat).toReal = (2 : ℝ)⁻¹ ^ (KMOf D x).toNat := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  have hwR : (2 : ℝ)⁻¹ ^ c * m.toReal ≤ (2 : ℝ)⁻¹ ^ (KMOf D x).toNat := by
    rw [← e1, ← e2]
    exact ENNReal.toReal_mono (by finiteness) hw
  have hlog := (Real.logb_le_logb (b := 2) (by norm_num)
    (mul_pos (by positivity) hmR) (by positivity)).mpr hwR
  have hL : Real.logb 2 ((2 : ℝ)⁻¹ ^ c * m.toReal) = -(c : ℝ) + Real.logb 2 m.toReal := by
    rw [Real.logb_mul (pow_ne_zero c (by norm_num)) hmR.ne', Real.logb_pow, Real.logb_inv,
      Real.logb_self_eq_one (by norm_num)]
    ring
  have hR : Real.logb 2 ((2 : ℝ)⁻¹ ^ (KMOf D x).toNat) = -((KMOf D x).toNat : ℝ) := by
    rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    ring
  rw [hL, hR] at hlog
  linarith

/-- **The expected monotone complexity of an i.i.d. word is at most `N H(ξ) + O(1)`**, with no
condition `N`.  The word `w : Fin N → Bool` is read as the bit string `List.ofFn w`.

**Weaker than the printed statement**: the book states this for a `k`-letter alphabet, and this is
the two-letter case, because the library's monotone complexity `KMOf` is defined for binary
sequences; the `k`-letter case would need monotone complexity for `k`-ary sequences and a
transport of it through the block encoding.  Within the binary case the statement is the printed
one for arbitrary rational `p`, zero values included.  SUV Problem 236, p. 228. -/
theorem exists_expect_KMOf_le_mul_entropyDist (μ : FiniteProbSpace Bool)
    (hrat : ∀ a, ∃ r : ℚ, μ.prob a = (r : ℝ)) (D : BitStream → BitStream)
    (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℕ, ∀ N : ℕ,
      ((μ.power N).expect fun w => ((KMOf D (List.ofFn w)).toNat : ℝ)) ≤
        (N : ℝ) * entropyDist μ.prob + c := by
  classical
  obtain ⟨pq, hpq⟩ := hrat true
  set p : NNReal := ⟨μ.prob true, μ.prob_nonneg true⟩ with hp_def
  have hptrue : (p : ℝ) = μ.prob true := by rw [hp_def]; exact NNReal.coe_mk _ _
  have hpqr : (p : ℝ) = pq := by rw [hptrue]; exact hpq
  have hprobtrue_le : μ.prob true ≤ 1 := by
    have h := Finset.single_le_sum (f := μ.prob) (fun i _ => μ.prob_nonneg i)
      (Finset.mem_univ true)
    rwa [μ.sum_prob] at h
  have hp1R : (p : ℝ) ≤ 1 := by rw [hptrue]; exact hprobtrue_le
  have hp : p ≤ 1 := by exact_mod_cast hp1R
  have hpq0 : 0 ≤ pq := by
    have : (0 : ℝ) ≤ (pq : ℝ) := by rw [← hpqr]; positivity
    exact_mod_cast this
  have hpq1 : pq ≤ 1 := by
    have : (pq : ℝ) ≤ 1 := by rw [← hpqr]; exact hp1R
    exact_mod_cast this
  have hsum : μ.prob false = 1 - μ.prob true := by
    have h := μ.sum_prob
    rw [Fintype.sum_bool] at h
    linarith
  have hptrue2 : μ.prob true = (p : ℝ) := hptrue.symm
  have hpfalse : μ.prob false = 1 - (p : ℝ) := by rw [hsum, hptrue2]
  -- the product distribution equals the Bernoulli cylinder mass of the block encoding
  have hqeq : ∀ (N : ℕ) (w : Fin N → Bool),
      (μ.power N).prob w = (cantorMass (bernoulliMeasure p hp) (List.ofFn w)).toReal := by
    intro N w
    rw [cantorMass_bernoulliMeasure_prod, List.map_ofFn, List.prod_ofFn, ENNReal.toReal_prod]
    change (∏ i, μ.prob (w i)) = _
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [Function.comp_apply]
    cases hwi : w i with
    | true => rw [ite_eq_left rfl, ENNReal.coe_toReal, hptrue2]
    | false =>
        rw [ite_eq_right (by decide),
          ENNReal.toReal_sub_of_le (by exact_mod_cast hp) (by simp), ENNReal.toReal_one,
          ENNReal.coe_toReal, hpfalse]
  -- Theorem 89 for monotone complexity applied to the computable Bernoulli measure
  obtain ⟨c, hc⟩ := exists_const_cantorMass_mul_le_complexityWeight_KMOf
    (bernoulliMeasure p hp) (isComputableMeasure_bernRat p hp pq hpq0 hpq1 hpqr) hD
  refine ⟨c, fun N => ?_⟩
  have hpoint : ∀ w : Fin N → Bool,
      (μ.power N).prob w * ((KMOf D (List.ofFn w)).toNat : ℝ) ≤
        negMulLog2 ((μ.power N).prob w) + (c : ℝ) * (μ.power N).prob w := by
    intro w
    have hq0 : 0 ≤ (μ.power N).prob w := (μ.power N).prob_nonneg w
    have hqcm := hqeq N w
    rcases eq_or_lt_of_le hq0 with hq_zero | hq_pos
    · rw [← hq_zero]; simp
    · have hcm0 : cantorMass (bernoulliMeasure p hp) (List.ofFn w) ≠ 0 := by
        intro h
        rw [h, ENNReal.toReal_zero] at hqcm
        linarith
      have hcmtop : cantorMass (bernoulliMeasure p hp) (List.ofFn w) ≠ ⊤ := by
        unfold cantorMass; exact MeasureTheory.measure_ne_top _ _
      have hkbound := KMOf_toNat_le_neg_logb_of_weight hD c (List.ofFn w) hcm0 hcmtop
        (hc (List.ofFn w))
      rw [← hqcm] at hkbound
      have hnml : negMulLog2 ((μ.power N).prob w) =
          (μ.power N).prob w * (-Real.logb 2 ((μ.power N).prob w)) := by
        unfold negMulLog2 Real.negMulLog Real.logb; ring
      rw [hnml]
      calc (μ.power N).prob w * ((KMOf D (List.ofFn w)).toNat : ℝ)
          ≤ (μ.power N).prob w * (-Real.logb 2 ((μ.power N).prob w) + c) :=
            mul_le_mul_of_nonneg_left hkbound (le_of_lt hq_pos)
        _ = (μ.power N).prob w * (-Real.logb 2 ((μ.power N).prob w)) +
              (c : ℝ) * (μ.power N).prob w := by ring
  calc (μ.power N).expect (fun w => ((KMOf D (List.ofFn w)).toNat : ℝ))
      = ∑ w, (μ.power N).prob w * ((KMOf D (List.ofFn w)).toNat : ℝ) := rfl
    _ ≤ ∑ w, (negMulLog2 ((μ.power N).prob w) + (c : ℝ) * (μ.power N).prob w) :=
        Finset.sum_le_sum (fun w _ => hpoint w)
    _ = (∑ w, negMulLog2 ((μ.power N).prob w)) + (c : ℝ) * ∑ w, (μ.power N).prob w := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (N : ℝ) * entropyDist μ.prob + c := by
        have hED : entropyDist (μ.power N).prob = (N : ℝ) * entropyDist μ.prob :=
          entropyDist_prod_eq μ.prob_nonneg μ.sum_prob N
        rw [show (∑ w : Fin N → Bool, negMulLog2 ((μ.power N).prob w))
              = entropyDist (μ.power N).prob from rfl,
          hED, (μ.power N).sum_prob, mul_one]

end Kolmogorov
