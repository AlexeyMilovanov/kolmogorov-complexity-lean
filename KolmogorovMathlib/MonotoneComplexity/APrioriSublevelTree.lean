import KolmogorovMathlib.MonotoneComplexity.AntichainSum
import KolmogorovMathlib.MonotoneComplexity.MonotoneAPriori
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.Foundation.UnboundedSearch

/-!
# The sublevel sets of a priori complexity as a tree

`kaSublevel k` collects the strings whose universal a priori mass exceeds `2 ^ (-k)`, that is
those of a priori complexity below `k`. Three structural facts are proved about it:
`kaSublevel_prefixClosed`, so the sublevel is a subtree; `kaSublevel_card_le_pow`, bounding any
antichain inside it by `2 ^ k` members; and `kaSublevel_isRE`, recursive enumerability uniformly
in `k`. `mem_kaSublevel_of_KA_lt` and `KA_le_of_mem_kaSublevel` relate membership to the value of
`KA`.
-/

noncomputable section

namespace Kolmogorov

/-- The strings of a priori mass above `2 ^ (-k)`, that is, of a priori complexity below `k`. -/
def kaSublevel (k : ℕ) : Set BitString :=
  {x | (2 : ENNReal)⁻¹ ^ k < universalContinuousSemimeasure x}

/-- The a priori sublevels are closed under taking prefixes. -/
lemma kaSublevel_prefixClosed {k : ℕ} {x y : BitString}
    (hxy : x <+: y) (hy : y ∈ kaSublevel k) : x ∈ kaSublevel k := by
  dsimp [kaSublevel] at *
  have h_anti := IsContinuousTreeSemimeasure.antitone_of_prefix
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1 hxy
  exact lt_of_lt_of_le hy h_anti

/-- An antichain inside the `k`-th a priori sublevel has at most `2 ^ k` members. -/
lemma kaSublevel_card_le_pow {k : ℕ} (S : Finset BitString)
    (hS : ∀ x ∈ S, x ∈ kaSublevel k)
    (hanti : ∀ x ∈ S, ∀ y ∈ S, x <+: y → x = y) :
    S.card ≤ 2 ^ k := by
  have h_meas := IsContinuousTreeSemimeasure.sum_antichain_le
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1 S hanti
  have h_sum : (S.card : ENNReal) * (2 : ENNReal)⁻¹ ^ k
      ≤ ∑ y ∈ S, universalContinuousSemimeasure y := by
    calc
      (S.card : ENNReal) * (2 : ENNReal)⁻¹ ^ k = ∑ y ∈ S, (2 : ENNReal)⁻¹ ^ k := by simp
      _ ≤ ∑ y ∈ S, universalContinuousSemimeasure y :=
        Finset.sum_le_sum (fun i hi => le_of_lt (hS i hi))
  have h_bound : (S.card : ENNReal) * (2 : ENNReal)⁻¹ ^ k ≤ 1 := le_trans h_sum h_meas
  have h_bound2 : (S.card : ENNReal) ≤ 2 ^ k := by
    have h_mul : (S.card : ENNReal) * (2 : ENNReal)⁻¹ ^ k * (2 : ENNReal) ^ k
        ≤ 1 * (2 : ENNReal) ^ k := by
      gcongr
    rw [← ENNReal.inv_pow, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one,
      one_mul] at h_mul
    exact h_mul
  exact_mod_cast h_bound2


open scoped ENNReal

private lemma dyadic_lt_iff (k m s : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ k < (m : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s ↔ 2 ^ s < m * 2 ^ k := by
  have H1 : ((2 : ℝ≥0∞)⁻¹ ^ k).toReal = (2 : ℝ)⁻¹ ^ k := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  have H2 : ((m : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s).toReal = (m : ℝ) / (2 : ℝ) ^ s := by
    rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  have H3 : (2 : ℝ≥0∞)⁻¹ ^ k ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have H4 : (m : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by positivity)
  rw [← ENNReal.toReal_lt_toReal H3 H4, H1, H2]
  have H5 : (2 : ℝ)⁻¹ ^ k = 1 / (2 : ℝ) ^ k := by rw [inv_pow, one_div]
  rw [H5]
  have H_pos_k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have H_pos_s : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  rw [div_lt_div_iff₀ H_pos_k H_pos_s, one_mul]
  have H6 : (m : ℝ) * (2 : ℝ) ^ k = ((m * 2 ^ k : ℕ) : ℝ) := by push_cast; rfl
  have H7 : (2 : ℝ) ^ s = ((2 ^ s : ℕ) : ℝ) := by push_cast; rfl
  rw [H6, H7]
  exact Nat.cast_lt

private lemma Computable.natMul {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a * g a) :=
  (Primrec₂.to_comp Primrec.nat_mul).comp hf hg

private lemma Computable.natLt_comp {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) :
    Computable (fun a => decide (f a < g a)) :=
  Computable.natLt.comp (Computable.pair hf hg)

private lemma Computable.pow2_comp {α : Type*} [Primcodable α] {f : α → ℕ}
    (hf : Computable f) :
    Computable (fun a => 2 ^ f a) :=
  Computable.pow2.comp hf


/-- Membership in the a priori sublevels is recursively enumerable uniformly in the level. -/
lemma kaSublevel_isRE : IsRE fun p : BitString × ℕ => p.1 ∈ kaSublevel p.2 := by
  have H := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2
  dsimp [IsLSC] at H
  rcases H with ⟨approx, hmono, hsup, hcomp⟩
  have h_eq : (fun p : BitString × ℕ => p.1 ∈ kaSublevel p.2) =
      fun p => ∃ s : ℕ, (2 : ENNReal)⁻¹ ^ p.2 < dyadicValue (approx s p.1 []) s := by
    funext p
    dsimp [kaSublevel]
    rw [←hsup p.1 []]
    exact propext lt_iSup_iff
  rw [h_eq]
  refine IsRE.exists_encodable ?_
  have h_eq2 : (fun p : (BitString × ℕ) × ℕ =>
        (2 : ENNReal)⁻¹ ^ p.1.2 < dyadicValue (approx p.2 p.1.1 []) p.2) =
      fun p => (2 ^ p.2 < approx p.2 p.1.1 [] * 2 ^ p.1.2) := by
    funext p
    exact propext (dyadic_lt_iff p.1.2 (approx p.2 p.1.1 []) p.2)
  rw [h_eq2]
  let check : (BitString × ℕ) × ℕ → Bool := fun p =>
    decide (2 ^ p.2 < approx p.2 p.1.1 [] * 2 ^ p.1.2)
  have H_comp : Computable check := by
    have h1 : Computable fun p : (BitString × ℕ) × ℕ => 2 ^ p.2 :=
      Computable.pow2_comp Computable.snd
    have h2_inner : Computable fun p : (BitString × ℕ) × ℕ =>
        (p.2, p.1.1, ([] : BitString)) :=
      Computable.pair Computable.snd
        (Computable.pair (Computable.fst.comp Computable.fst) (Computable.const []))
    have h2 : Computable fun p : (BitString × ℕ) × ℕ => approx p.2 p.1.1 [] :=
      hcomp.comp h2_inner
    have h3 : Computable fun p : (BitString × ℕ) × ℕ => 2 ^ p.1.2 :=
      Computable.pow2_comp (Computable.snd.comp Computable.fst)
    have h4 : Computable fun p : (BitString × ℕ) × ℕ => approx p.2 p.1.1 [] * 2 ^ p.1.2 :=
      Computable.natMul h2 h3
    exact Computable.natLt_comp h1 h4
  exact IsRE.of_iff (IsRE_of_computable H_comp) (by intro a; simp [check])

/-- A string of a priori complexity below `k` lies in the `k`-th sublevel. -/
lemma mem_kaSublevel_of_KA_lt {x : BitString} {k : ℕ} (h : KA x < k) :
    x ∈ kaSublevel k := by
  dsimp [kaSublevel, KA] at *
  have h_pos := universalContinuousSemimeasure_pos x
  have h_ne_top :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have h_real_pos : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos h_pos.ne' h_ne_top
  have h1 : - k < Real.logb 2 (universalContinuousSemimeasure x).toReal := by linarith
  have h2 : (2 : ℝ) ^ (- (k : ℝ))
      < (2 : ℝ) ^ (Real.logb 2 (universalContinuousSemimeasure x).toReal) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
  rw [Real.rpow_logb (by norm_num) (by norm_num) h_real_pos] at h2
  have h3 : (2 : ℝ) ^ (- (k : ℝ)) = ((2 : ℝ)⁻¹) ^ k := by
    rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, inv_pow]
  rw [h3] at h2
  have h4 : ENNReal.ofReal (((2 : ℝ)⁻¹) ^ k)
      < ENNReal.ofReal (universalContinuousSemimeasure x).toReal := by
    rwa [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  rw [ENNReal.ofReal_toReal h_ne_top] at h4
  have h5 : ENNReal.ofReal (((2 : ℝ)⁻¹) ^ k) = (2 : ENNReal)⁻¹ ^ k := by
    have H : ENNReal.ofReal ((2:ℝ)⁻¹) = (2:ENNReal)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_cast
    rw [ENNReal.ofReal_pow (by positivity), H]
  rwa [h5] at h4

/-- A string in the `k`-th sublevel has a priori complexity at most `k`. -/
lemma KA_le_of_mem_kaSublevel {x : BitString} {k : ℕ} (h : x ∈ kaSublevel k) :
    KA x ≤ k := by
  dsimp [kaSublevel, KA] at *
  have h_pos := universalContinuousSemimeasure_pos x
  have h_ne_top :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have h_real_pos : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos h_pos.ne' h_ne_top
  have h5 : ENNReal.ofReal (((2 : ℝ)⁻¹) ^ k) = (2 : ENNReal)⁻¹ ^ k := by
    have H : ENNReal.ofReal ((2:ℝ)⁻¹) = (2:ENNReal)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_cast
    rw [ENNReal.ofReal_pow (by positivity), H]
  rw [←h5] at h
  have h6 : ((2 : ℝ)⁻¹) ^ k < (universalContinuousSemimeasure x).toReal := by
    have ht : ENNReal.ofReal (universalContinuousSemimeasure x).toReal
        = universalContinuousSemimeasure x :=
      ENNReal.ofReal_toReal h_ne_top
    rw [←ht] at h
    rwa [ENNReal.ofReal_lt_ofReal_iff h_real_pos] at h
  have h7 : (2 : ℝ) ^ (- (k : ℝ)) < (universalContinuousSemimeasure x).toReal := by
    have h3 : (2 : ℝ) ^ (- (k : ℝ)) = ((2 : ℝ)⁻¹) ^ k := by
      rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, inv_pow]
    rwa [h3]
  have h8 : Real.logb 2 ((2 : ℝ) ^ (- (k : ℝ)))
      < Real.logb 2 (universalContinuousSemimeasure x).toReal := by
    refine Real.logb_lt_logb (by norm_num) ?_ h7
    positivity
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at h8
  linarith

end Kolmogorov
