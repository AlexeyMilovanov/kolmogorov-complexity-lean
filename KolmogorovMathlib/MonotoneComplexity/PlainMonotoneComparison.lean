/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.MonotoneAPriori
import KolmogorovMathlib.MonotoneComplexity.MonotoneFromPrefix
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Complexity.Properties

/-!
# Plain complexity versus monotone complexity

Plain complexity `C = plainK V` and monotone complexity `KM = KMOf D` differ by at
most a logarithmic term in the length of the string:

* `exists_const_plainK_le_KMOf_add_log` : `C(x) ≤ KM(x) + 2 log₂ (l(x) + 1) + O(1)`,
  assembled from `plainK ≤ K + O(1)`, `K ≤ KA + 2 log l(x) + O(1)` (SUV 79(e)) and
  `KA ≤ KM + O(1)` (SUV 85(e));
* `exists_const_KMOf_le_plainK_add_log` : `KM(x) ≤ C(x) + 2 log₂ (l(x) + 1) + O(1)`,
  assembled from `KM ≤ K + O(1)` (SUV 85(d)), `K(x) ≤ C(x) + K(C(x)) + O(1)`
  (SUV Theorem 65) and `K(y) ≤ 2 l(y) + O(1)`;
* `exists_const_abs_plainK_sub_KMOf_le_log` : the two-sided form
  `|C(x) − KM(x)| ≤ 2 log₂ (l(x) + 1) + O(1)`.

All constants are uniform in `x`.
-/

namespace Kolmogorov

/-- Splitting a logarithm of a shifted argument: `log₂ (n + c) ≤ log₂ (n + 1) + log₂ (c + 1)`. -/
lemma logb_two_nat_add_le (n c : ℕ) :
    Real.logb 2 ((n : ℝ) + c) ≤ Real.logb 2 ((n : ℝ) + 1) + Real.logb 2 ((c : ℝ) + 1) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc1 : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have hsplit : Real.logb 2 (((n : ℝ) + 1) * ((c : ℝ) + 1)) =
      Real.logb 2 ((n : ℝ) + 1) + Real.logb 2 ((c : ℝ) + 1) :=
    Real.logb_mul (ne_of_gt hn1) (ne_of_gt hc1)
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ (n : ℝ) + c) with h0 | hpos
  · have hnonneg : 0 ≤ Real.logb 2 ((n : ℝ) + 1) + Real.logb 2 ((c : ℝ) + 1) := by
      have h1 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
        Real.logb_nonneg (by norm_num) (by linarith)
      have h2 : 0 ≤ Real.logb 2 ((c : ℝ) + 1) :=
        Real.logb_nonneg (by norm_num) (by linarith)
      linarith
    rw [← h0]
    simpa using hnonneg
  · have hle : (n : ℝ) + c ≤ ((n : ℝ) + 1) * ((c : ℝ) + 1) := by nlinarith [hn1, hc1]
    calc Real.logb 2 ((n : ℝ) + c)
        ≤ Real.logb 2 (((n : ℝ) + 1) * ((c : ℝ) + 1)) :=
          (Real.logb_le_logb (by norm_num) hpos (by positivity)).mpr hle
      _ = _ := hsplit

private lemma toNat_le_add_of_le {a b : ℕ∞} {c : ℕ} (h : a ≤ b + (c : ℕ∞)) (hb : b ≠ ⊤) :
    a.toNat ≤ b.toNat + c := by
  have hrhs : b + (c : ℕ∞) ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hb, ENat.natCast_ne_top c⟩
  have h' := ENat.toNat_le_toNat h hrhs
  rwa [ENat.toNat_add hb (ENat.natCast_ne_top c), ENat.toNat_natCast] at h'

/-- Relative to an optimal prefix machine every string has finite prefix complexity. -/
lemma KPPlain_ne_top_of_isOptimalPrefixConditional {U : Map} (hU : IsOptimalPrefixConditional U)
    (x : BitString) : KPPlain U x ≠ ⊤ := by
  obtain ⟨c, hc⟩ := KPPlain_le_two_mul_length U hU
  have h : KPPlain U x ≤ ((2 * x.length + c : ℕ) : ℕ∞) := by
    have := hc x
    push_cast
    exact_mod_cast this
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) h

/-- Relative to an optimal conditional machine every string has finite plain complexity. -/
lemma plainK_ne_top_of_isOptimalConditional {V : Map} (hV : isOptimalConditional V)
    (x : BitString) : plainK V x ≠ ⊤ := by
  obtain ⟨c, hc⟩ := plainK_le_length V hV
  exact ne_top_of_le_natCast_add (hc x)

/-- Plain complexity exceeds monotone complexity by at most a logarithmic term:
`C(x) ≤ KM(x) + 2 log₂ (l(x) + 1) + O(1)`. -/
theorem exists_const_plainK_le_KMOf_add_log (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℝ, ∀ x : BitString,
      ((plainK V x).toNat : ℝ) ≤ ((KMOf D x).toNat : ℝ) +
        2 * Real.logb 2 ((x.length : ℝ) + 1) + c := by
  obtain ⟨c₀, h₀⟩ := plain_le_prefix V U hV hU.isPrefixDecompressor
  obtain ⟨c₁, h₁⟩ := KPPlain_le_KA_add_two_mul_log_length U hU
  obtain ⟨c₂, h₂⟩ := exists_const_KA_le_KMOf hD
  refine ⟨c₀ + c₁ + c₂, fun x => ?_⟩
  have hstep0 : (plainK V x).toNat ≤ (KPPlain U x).toNat + c₀ :=
    toNat_le_add_of_le (h₀ x) (KPPlain_ne_top_of_isOptimalPrefixConditional hU x)
  have hstep0' : ((plainK V x).toNat : ℝ) ≤ ((KPPlain U x).toNat : ℝ) + c₀ := by
    exact_mod_cast hstep0
  have hlogmono : Real.logb 2 (x.length : ℝ) ≤ Real.logb 2 ((x.length : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos x.length with h | h
    · rw [h]
      simp only [Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg (by norm_num) (by norm_num)
    · exact (Real.logb_le_logb (by norm_num) (by exact_mod_cast h) (by positivity)).mpr
        (by linarith)
  have h1 := h₁ x
  have h2 := h₂ x
  linarith

/-- Monotone complexity exceeds plain complexity by at most a logarithmic term:
`KM(x) ≤ C(x) + 2 log₂ (l(x) + 1) + O(1)`. -/
theorem exists_const_KMOf_le_plainK_add_log (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℝ, ∀ x : BitString,
      ((KMOf D x).toNat : ℝ) ≤ ((plainK V x).toNat : ℝ) +
        2 * Real.logb 2 ((x.length : ℝ) + 1) + c := by
  obtain ⟨c₃, h₃⟩ := exists_const_KMOf_le_KP hD hU.isPrefixMachine hU.isDecompressor
  obtain ⟨c₄, h₄⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨c₅, h₅⟩ := plainK_le_length V hV
  obtain ⟨c₆, h₆⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨(c₃ + c₄ + c₆ : ℕ) + 2 * Real.logb 2 ((c₅ : ℝ) + 1) + 2, fun x => ?_⟩
  set kC : ℕ := (plainK V x).toNat with hkC
  have hfin : plainK V x = (kC : ℕ∞) :=
    (ENat.natCast_toNat (plainK_ne_top_of_isOptimalConditional hV x)).symm
  set L : ℕ := (Nat.bits kC).length with hL
  -- `KM_D x ≤ K(x) + c₃ ≤ kC + K(bits kC) + c₄ + c₃ ≤ kC + 2 L + c₆ + c₄ + c₃`
  have hchain : KMOf D x ≤ ((kC + 2 * L + (c₃ + c₄ + c₆) : ℕ) : ℕ∞) := by
    have hA : KMOf D x ≤ KPPlain U x + (c₃ : ℕ∞) := h₃ x
    have hB : KPPlain U x ≤ (kC : ℕ∞) + KPPlain U (Nat.bits kC) + (c₄ : ℕ∞) := h₄ x kC hfin
    have hC : KPPlain U (Nat.bits kC) ≤ 2 * (L : ℕ∞) + (c₆ : ℕ∞) := by
      simpa [hL] using h₆ (Nat.bits kC)
    calc KMOf D x ≤ KPPlain U x + (c₃ : ℕ∞) := hA
      _ ≤ ((kC : ℕ∞) + KPPlain U (Nat.bits kC) + (c₄ : ℕ∞)) + (c₃ : ℕ∞) := by gcongr
      _ ≤ ((kC : ℕ∞) + (2 * (L : ℕ∞) + (c₆ : ℕ∞)) + (c₄ : ℕ∞)) + (c₃ : ℕ∞) := by gcongr
      _ = ((kC + 2 * L + (c₃ + c₄ + c₆) : ℕ) : ℕ∞) := by push_cast; ring
  have hnat : (KMOf D x).toNat ≤ kC + 2 * L + (c₃ + c₄ + c₆) := by
    have := ENat.toNat_le_toNat hchain (ENat.natCast_ne_top _)
    exact this
  have hreal : ((KMOf D x).toNat : ℝ) ≤ (kC : ℝ) + 2 * (L : ℝ) + ((c₃ + c₄ + c₆ : ℕ) : ℝ) := by
    exact_mod_cast hnat
  -- `L ≤ log₂ kC + 1` and `kC ≤ l(x) + c₅`
  have hLlog : (L : ℝ) ≤ Real.logb 2 (kC : ℝ) + 1 := natBits_length_le_logb_add_one kC
  have hkCle : kC ≤ x.length + c₅ := by
    have := h₅ x
    have h' : plainK V x ≤ ((x.length + c₅ : ℕ) : ℕ∞) := by push_cast; exact_mod_cast this
    have := ENat.toNat_le_toNat h' (ENat.natCast_ne_top _)
    exact (by rwa [hkC] : kC ≤ x.length + c₅)
  have hkCreal : (kC : ℝ) ≤ (x.length : ℝ) + (c₅ : ℝ) := by exact_mod_cast hkCle
  have hlogkC : Real.logb 2 (kC : ℝ) ≤ Real.logb 2 ((x.length : ℝ) + (c₅ : ℝ)) := by
    rcases Nat.eq_zero_or_pos kC with h | h
    · rw [h]
      simp only [Nat.cast_zero, Real.logb_zero]
      rcases Nat.eq_zero_or_pos (x.length + c₅) with h0 | hpos
      · have hx : (x.length : ℝ) + (c₅ : ℝ) = 0 := by
          have hx0 : x.length = 0 := by omega
          have hc0 : c₅ = 0 := by omega
          simp [hx0, hc0]
        rw [hx]
        simp
      · exact Real.logb_nonneg (by norm_num) (by
          have h1 : (1 : ℝ) ≤ ((x.length + c₅ : ℕ) : ℝ) := by exact_mod_cast hpos
          push_cast at h1
          linarith)
    · exact (Real.logb_le_logb (by norm_num) (by exact_mod_cast h)
        (by
          have : (0 : ℝ) < (kC : ℝ) := by exact_mod_cast h
          linarith)).mpr hkCreal
  have hsplit := logb_two_nat_add_le x.length c₅
  have hplain : ((plainK V x).toNat : ℝ) = (kC : ℝ) := by rw [hkC]
  rw [hplain]
  push_cast at hreal ⊢
  linarith

/-- Two-sided comparison: `|C(x) − KM(x)| ≤ 2 log₂ (l(x) + 1) + O(1)`. -/
theorem exists_const_abs_plainK_sub_KMOf_le_log (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℝ, ∀ x : BitString,
      |((plainK V x).toNat : ℝ) - ((KMOf D x).toNat : ℝ)| ≤
        2 * Real.logb 2 ((x.length : ℝ) + 1) + c := by
  obtain ⟨cA, hA⟩ := exists_const_plainK_le_KMOf_add_log V U hV hU hD
  obtain ⟨cB, hB⟩ := exists_const_KMOf_le_plainK_add_log V U hV hU hD
  refine ⟨max cA cB, fun x => ?_⟩
  have h1 := hA x
  have h2 := hB x
  have hmA : cA ≤ max cA cB := le_max_left _ _
  have hmB : cB ≤ max cA cB := le_max_right _ _
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Kolmogorov
