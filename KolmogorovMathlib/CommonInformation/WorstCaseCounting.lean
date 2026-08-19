import Mathlib.Algebra.Order.BigOperators.Group.Finset
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.CommonInformation.Definitions
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.CommonInformation.ConditionalCounting

namespace Kolmogorov

def muchnikThreshold (n : Nat) : Nat := (11 * n + 9) / 10

theorem muchnik_lt_threshold_iff (k n : Nat) :
  k < muchnikThreshold n ↔ 10 * k < 11 * n := by
  unfold muchnikThreshold
  omega

def IsMuchnikSurvivor
    (V : Map) (n : Nat) (x y : BitString) : Prop :=
  x.length = 2 * n + 2 ∧
  y.length = 2 * n + 2 ∧
  (2 * n : ENat) ≤ plainK V x ∧
  (2 * n : ENat) ≤ plainK V y ∧
  (3 * n : ENat) ≤ pairPlainK V x y ∧
  (muchnikThreshold n, muchnikThreshold n, muchnikThreshold n) ∉
    CommonInformationRegion V x y

theorem enat_lt_coe_iff_le_pred
    {q : ENat} {t : Nat} (ht : 0 < t) :
  q < (t : ENat) ↔ q ≤ ((t - 1 : Nat) : ENat) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [Nat.succ_sub_one, Nat.cast_succ]
  exact ENat.lt_add_one_iff (ENat.coe_ne_top s)

theorem exists_mem_avoiding_four
    {α : Type*}
    {U B₁ B₂ B₃ B₄ : Finset α}
    (h : B₁.card + B₂.card + B₃.card + B₄.card < U.card) :
  ∃ x ∈ U, x ∉ B₁ ∧ x ∉ B₂ ∧ x ∉ B₃ ∧ x ∉ B₄ := by
  classical
  let B := B₁ ∪ B₂ ∪ B₃ ∪ B₄
  have hcard : B.card < U.card := by
    dsimp [B]
    calc
      (B₁ ∪ B₂ ∪ B₃ ∪ B₄).card
          ≤ (B₁ ∪ B₂ ∪ B₃).card + B₄.card :=
        Finset.card_union_le _ _
      _ ≤ ((B₁ ∪ B₂).card + B₃.card) + B₄.card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ ((B₁.card + B₂.card) + B₃.card) + B₄.card := by
        gcongr
        exact Finset.card_union_le _ _
      _ = B₁.card + B₂.card + B₃.card + B₄.card := by omega
      _ < U.card := h
  obtain ⟨x, hxU, hxB⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨x, hxU, ?_⟩
  simpa [B] using hxB

theorem muchnik_bad_card_sum_lt
    {n : Nat} (hn : 0 < n) :
  2^(4*n+2) + 2^(4*n+2) + 2^(3*n) +
      2^(3 * muchnikThreshold n) < 2^(4*n+4) := by
  by_cases hnSmall : n < 3
  · interval_cases n <;> norm_num [muchnikThreshold] at hn ⊢
  · have hnLarge : 3 ≤ n := by omega
    have hThreshold : 3 * muchnikThreshold n ≤ 4 * n := by
      unfold muchnikThreshold
      omega
    have hThree : 3 * n ≤ 4 * n := by omega
    have hPowThreshold : 2 ^ (3 * muchnikThreshold n) ≤ 2 ^ (4 * n) :=
      Nat.pow_le_pow_right (by norm_num) hThreshold
    have hPowThree : 2 ^ (3 * n) ≤ 2 ^ (4 * n) :=
      Nat.pow_le_pow_right (by norm_num) hThree
    calc
      2^(4*n+2) + 2^(4*n+2) + 2^(3*n) +
            2^(3 * muchnikThreshold n)
          ≤ 2^(4*n+2) + 2^(4*n+2) + 2^(4*n) + 2^(4*n) := by
            omega
      _ = 10 * 2 ^ (4 * n) := by
        rw [show 4 * n + 2 = 4 * n + 2 by rfl, pow_add]
        norm_num
        ring
      _ < 16 * 2 ^ (4 * n) :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.pow_pos (by norm_num))
      _ = 2 ^ (4 * n + 4) := by
        rw [pow_add]
        norm_num
        ring

theorem exists_muchnikSurvivor
    (V : Map) {n : Nat} (hn : 0 < n) :
  ∃ x y, IsMuchnikSurvivor V n x y := by
  classical
  let L := 2 * n + 2
  let marginalBound := 2 * n - 1
  let pairBound := 3 * n - 1
  let commonBound := muchnikThreshold n - 1
  let U := (stringsOfLength L).product (stringsOfLength L)
  let B₁ := U.filter fun p => plainK V p.1 ≤ (marginalBound : ENat)
  let B₂ := U.filter fun p => plainK V p.2 ≤ (marginalBound : ENat)
  let B₃ := U.filter fun p => pairPlainK V p.1 p.2 ≤ (pairBound : ENat)
  let B₄ := commonWitnessPairsLe V commonBound commonBound commonBound
  have hCommonPos : 0 < muchnikThreshold n :=
    (muchnik_lt_threshold_iff 0 n).mpr (by omega)
  have hB₁ : B₁.card < 2 ^ (4 * n + 2) := by
    dsimp [B₁, U, L, marginalBound]
    have hExponent : 2 * n + 2 + (2 * n - 1) + 1 = 4 * n + 2 := by omega
    rw [← hExponent]
    exact card_fixedLengthPairs_lowLeft_lt V (2 * n + 2) (2 * n - 1)
  have hB₂ : B₂.card < 2 ^ (4 * n + 2) := by
    dsimp [B₂, U, L, marginalBound]
    have hExponent : 2 * n + 2 + (2 * n - 1) + 1 = 4 * n + 2 := by omega
    rw [← hExponent]
    exact card_fixedLengthPairs_lowRight_lt V (2 * n + 2) (2 * n - 1)
  have hB₃ : B₃.card < 2 ^ (3 * n) := by
    dsimp [B₃, U, L, pairBound]
    have hExponent : 3 * n - 1 + 1 = 3 * n := by omega
    rw [← hExponent]
    exact card_fixedLengthPairs_lowPair_lt V (2 * n + 2) (3 * n - 1)
  have hB₄ : B₄.card < 2 ^ (3 * muchnikThreshold n) := by
    dsimp [B₄, commonBound]
    have hExponent :
        (muchnikThreshold n - 1 + 1) +
          (muchnikThreshold n - 1 + 1) +
          (muchnikThreshold n - 1 + 1) =
            3 * muchnikThreshold n := by omega
    simpa only [hExponent] using
      card_commonWitnessPairsLe_lt V
        (muchnikThreshold n - 1)
        (muchnikThreshold n - 1)
        (muchnikThreshold n - 1)
  have hU : U.card = 2 ^ (4 * n + 4) := by
    dsimp [U, L]
    rw [Finset.card_product]
    simp only [cardStringsOfLength]
    rw [← pow_add]
    congr 1
    omega
  have hBad : B₁.card + B₂.card + B₃.card + B₄.card < U.card := by
    rw [hU]
    have hTotal := muchnik_bad_card_sum_lt hn
    omega
  obtain ⟨p, hpU, hp₁, hp₂, hp₃, hp₄⟩ :=
    exists_mem_avoiding_four (U := U) (B₁ := B₁) (B₂ := B₂)
      (B₃ := B₃) (B₄ := B₄) hBad
  rcases p with ⟨x, y⟩
  have hLengths : x.length = 2 * n + 2 ∧ y.length = 2 * n + 2 := by
    dsimp [U, L] at hpU
    change (x, y) ∈
      stringsOfLength (2 * n + 2) ×ˢ stringsOfLength (2 * n + 2) at hpU
    rw [Finset.mem_product, memStringsOfLength, memStringsOfLength] at hpU
    exact hpU
  have hxNotLow : ¬plainK V x ≤ ((2 * n - 1 : Nat) : ENat) := by
    intro hx
    apply hp₁
    dsimp [B₁, marginalBound]
    exact Finset.mem_filter.mpr ⟨hpU, hx⟩
  have hyNotLow : ¬plainK V y ≤ ((2 * n - 1 : Nat) : ENat) := by
    intro hy
    apply hp₂
    dsimp [B₂, marginalBound]
    exact Finset.mem_filter.mpr ⟨hpU, hy⟩
  have hxyNotLow : ¬pairPlainK V x y ≤ ((3 * n - 1 : Nat) : ENat) := by
    intro hxy
    apply hp₃
    dsimp [B₃, pairBound]
    exact Finset.mem_filter.mpr ⟨hpU, hxy⟩
  have hxComplex : (2 * n : ENat) ≤ plainK V x := by
    apply le_of_not_gt
    intro hx
    exact hxNotLow ((enat_lt_coe_iff_le_pred (q := plainK V x) (by omega)).mp hx)
  have hyComplex : (2 * n : ENat) ≤ plainK V y := by
    apply le_of_not_gt
    intro hy
    exact hyNotLow ((enat_lt_coe_iff_le_pred (q := plainK V y) (by omega)).mp hy)
  have hxyComplex : (3 * n : ENat) ≤ pairPlainK V x y := by
    apply le_of_not_gt
    intro hxy
    exact hxyNotLow
      ((enat_lt_coe_iff_le_pred (q := pairPlainK V x y) (by omega)).mp hxy)
  have hNoCommon :
      (muchnikThreshold n, muchnikThreshold n, muchnikThreshold n) ∉
        CommonInformationRegion V x y := by
    intro hRegion
    apply hp₄
    dsimp [B₄, commonBound]
    apply (mem_commonWitnessPairsLe_iff V
      (muchnikThreshold n - 1)
      (muchnikThreshold n - 1)
      (muchnikThreshold n - 1) x y).mpr
    change ∃ z,
      plainK V z < (muchnikThreshold n : ENat) ∧
      condK V x z < (muchnikThreshold n : ENat) ∧
      condK V y z < (muchnikThreshold n : ENat) at hRegion
    obtain ⟨z, hz, hx, hy⟩ := hRegion
    exact ⟨z,
      (enat_lt_coe_iff_le_pred hCommonPos).mp hz,
      (enat_lt_coe_iff_le_pred hCommonPos).mp hx,
      (enat_lt_coe_iff_le_pred hCommonPos).mp hy⟩
  exact ⟨x, y, hLengths.1, hLengths.2, hxComplex, hyComplex, hxyComplex, hNoCommon⟩

end Kolmogorov
