import Mathlib.Algebra.Order.BigOperators.Group.Finset
import KolmogorovMathlib.CommonInformation.Definitions
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.CommonInformation.WorstCaseCounting
import KolmogorovMathlib.CommonInformation.WorstCaseRegionBounds

namespace Kolmogorov

noncomputable def muchnikRegionBadPairs (V : Map) (n : Nat) : Finset (BitString × BitString) :=
  (muchnikAdmissibleTriples n).toFinset.biUnion (fun t => commonWitnessPairsLe V t.1 t.2.1 t.2.2)

theorem mem_muchnikRegionBadPairs_iff
    (V : Map) (n : Nat) (x y : BitString) :
  (x, y) ∈ muchnikRegionBadPairs V n ↔
    ∃ t ∈ muchnikAdmissibleTriples n, ∃ z,
      plainK V z ≤ (t.1 : ENat) ∧
      condK V x z ≤ (t.2.1 : ENat) ∧
      condK V y z ≤ (t.2.2 : ENat) := by
  classical
  simp [muchnikRegionBadPairs, mem_commonWitnessPairsLe_iff]

/-- Once the logarithmic margin permits any admissible triple, the cubic
parameter scan is smaller than a single `n`-bit block. -/
theorem muchnikRegion_cubic_le_pow {n : Nat} (hn : 22 ≤ n) :
    (3 * n) ^ 3 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (3 * (n + 1)) ^ 3 ≤ 2 * (3 * n) ^ 3 := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ n by omega)
          norm_num [pow_succ]
          nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2)]
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

theorem muchnikRegion_bad_card_sum_lt
    {n : Nat} (hn : 0 < n) :
  2^(4*n+2) + 2^(4*n+2) + 2^(3*n) +
      2 ^ muchnikRegionMargin n * (muchnikAdmissibleTriples n).length < 2^(4*n+4) := by
  have hMarginTerm :
      2 ^ muchnikRegionMargin n * (muchnikAdmissibleTriples n).length <
        2 ^ (4 * n) := by
    by_cases hEmpty : muchnikAdmissibleTriples n = []
    · simp [hEmpty]
    · obtain ⟨t, ts, hList⟩ := List.exists_cons_of_ne_nil hEmpty
      have ht : t ∈ muchnikAdmissibleTriples n := by
        rw [hList]
        exact List.Mem.head ts
      have hMargin : muchnikRegionMargin n < 3 * n := by
        rw [mem_muchnikAdmissibleTriples_iff] at ht
        omega
      have hBits : 0 < (Nat.bits n).length := by
        rw [Nat.size_eq_bits_len]
        exact Nat.size_pos.mpr hn
      have hnLarge : 22 ≤ n := by
        have hMarginLower : 64 ≤ muchnikRegionMargin n := by
          simp only [muchnikRegionMargin, logSlack]
          omega
        omega
      have hLength :
          (muchnikAdmissibleTriples n).length ≤ 2 ^ n :=
        (length_muchnikAdmissibleTriples_le n).trans
          (muchnikRegion_cubic_le_pow hnLarge)
      have hMarginPow :
          2 ^ muchnikRegionMargin n < 2 ^ (3 * n) :=
        Nat.pow_lt_pow_right (by norm_num) hMargin
      calc
        2 ^ muchnikRegionMargin n * (muchnikAdmissibleTriples n).length
            ≤ 2 ^ muchnikRegionMargin n * 2 ^ n :=
          Nat.mul_le_mul_left _ hLength
        _ < 2 ^ (3 * n) * 2 ^ n :=
          Nat.mul_lt_mul_of_pos_right hMarginPow (Nat.pow_pos (by norm_num))
        _ = 2 ^ (4 * n) := by
          rw [← pow_add]
          congr 1
          omega
  have hThreePow : 2 ^ (3 * n) ≤ 2 ^ (4 * n) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  calc
    2^(4*n+2) + 2^(4*n+2) + 2^(3*n) +
          2 ^ muchnikRegionMargin n * (muchnikAdmissibleTriples n).length
        < 2^(4*n+2) + 2^(4*n+2) + 2^(4*n) + 2^(4*n) := by omega
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

theorem card_muchnikRegionBadPairs_lt
    (V : Map) {n : Nat} (_hn : 0 < n) :
  (muchnikRegionBadPairs V n).card < 2 ^ (4 * n + 2) := by
  classical
  by_cases hEmpty : muchnikAdmissibleTriples n = []
  · simp [muchnikRegionBadPairs, hEmpty]
  · obtain ⟨t₀, ts, hList⟩ := List.exists_cons_of_ne_nil hEmpty
    have ht₀ : t₀ ∈ muchnikAdmissibleTriples n := by
      rw [hList]
      exact List.Mem.head ts
    have hMarginLe : muchnikRegionMargin n ≤ 4 * n + 2 := by
      have htAdm := (mem_muchnikAdmissibleTriples_iff n t₀).mp ht₀
      omega
    let r := 4 * n + 2 - muchnikRegionMargin n
    have hEach :
        ∀ t ∈ (muchnikAdmissibleTriples n).toFinset,
          (commonWitnessPairsLe V t.1 t.2.1 t.2.2).card ≤ 2 ^ r := by
      intro t ht
      have htList : t ∈ muchnikAdmissibleTriples n := by simpa using ht
      have htAdm := (mem_muchnikAdmissibleTriples_iff n t).mp htList
      have hExponent :
          (t.1 + 1) + (t.2.1 + 1) + (t.2.2 + 1) ≤ r := by
        dsimp [r]
        omega
      exact (card_commonWitnessPairsLe_lt V t.1 t.2.1 t.2.2).le.trans
        (Nat.pow_le_pow_right (by norm_num) hExponent)
    have hLengthPow :
        (muchnikAdmissibleTriples n).length < 2 ^ muchnikRegionMargin n := by
      have hDouble :
          2 * (muchnikAdmissibleTriples n).length <
            2 ^ muchnikRegionMargin n :=
        lt_of_le_of_lt
          (Nat.mul_le_mul_left 2 (length_muchnikAdmissibleTriples_le n))
          (two_mul_muchnikRegion_cubic_lt n)
      omega
    calc
      (muchnikRegionBadPairs V n).card
          ≤ ∑ t ∈ (muchnikAdmissibleTriples n).toFinset,
              (commonWitnessPairsLe V t.1 t.2.1 t.2.2).card := by
            unfold muchnikRegionBadPairs
            exact Finset.card_biUnion_le
      _ ≤ (muchnikAdmissibleTriples n).toFinset.card * 2 ^ r :=
        Finset.sum_le_card_nsmul _ _ _ hEach
      _ = (muchnikAdmissibleTriples n).length * 2 ^ r := by
        rw [List.toFinset_card_of_nodup (muchnikAdmissibleTriples_nodup n)]
      _ < 2 ^ muchnikRegionMargin n * 2 ^ r :=
        Nat.mul_lt_mul_of_pos_right hLengthPow (Nat.pow_pos (by norm_num))
      _ = 2 ^ (4 * n + 2) := by
        rw [← pow_add]
        congr 1
        dsimp [r]
        omega

theorem not_mem_muchnikRegionBadPairs_iff
    (V : Map) (n : Nat) (x y : BitString) :
  (x, y) ∉ muchnikRegionBadPairs V n ↔
    ∀ z,
      (3 * n : ENat) ≤ plainK V z + condK V x z + muchnikRegionMargin n ∨
      (3 * n : ENat) ≤ plainK V z + condK V y z + muchnikRegionMargin n ∨
      (4 * n : ENat) ≤ plainK V z + condK V x z + condK V y z + muchnikRegionMargin n := by
  constructor
  · intro hNot z
    by_contra hBounds
    push Not at hBounds
    have hPlainFinite : plainK V z ≠ ⊤ := by
      intro hTop
      rw [hTop] at hBounds
      simp at hBounds
    have hXFinite : condK V x z ≠ ⊤ := by
      intro hTop
      rw [hTop] at hBounds
      simp at hBounds
    have hYFinite : condK V y z ≠ ⊤ := by
      intro hTop
      rw [hTop] at hBounds
      simp at hBounds
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hPlainFinite
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hXFinite
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hYFinite
    have hNat :
        a + b + muchnikRegionMargin n < 3 * n ∧
        a + c + muchnikRegionMargin n < 3 * n ∧
        a + b + c + muchnikRegionMargin n < 4 * n := by
      rw [← ha, ← hb, ← hc] at hBounds
      exact_mod_cast hBounds
    apply hNot
    rw [mem_muchnikRegionBadPairs_iff]
    refine ⟨(a, b, c), ?_, z, ?_, ?_, ?_⟩
    · rw [mem_muchnikAdmissibleTriples_iff]
      exact hNat
    · rw [ha]
    · rw [hb]
    · rw [hc]
  · intro hBounds hMem
    rw [mem_muchnikRegionBadPairs_iff] at hMem
    obtain ⟨t, ht, z, hz, hx, hy⟩ := hMem
    have htAdm := (mem_muchnikAdmissibleTriples_iff n t).mp ht
    have hX :
        plainK V z + condK V x z + muchnikRegionMargin n < (3 * n : ENat) := by
      calc
        plainK V z + condK V x z + muchnikRegionMargin n
            ≤ (t.1 : ENat) + (t.2.1 : ENat) + muchnikRegionMargin n := by
              gcongr
        _ < (3 * n : ENat) := by exact_mod_cast htAdm.1
    have hY :
        plainK V z + condK V y z + muchnikRegionMargin n < (3 * n : ENat) := by
      calc
        plainK V z + condK V y z + muchnikRegionMargin n
            ≤ (t.1 : ENat) + (t.2.2 : ENat) + muchnikRegionMargin n := by
              gcongr
        _ < (3 * n : ENat) := by exact_mod_cast htAdm.2.1
    have hXY :
        plainK V z + condK V x z + condK V y z + muchnikRegionMargin n <
          (4 * n : ENat) := by
      calc
        plainK V z + condK V x z + condK V y z + muchnikRegionMargin n
            ≤ (t.1 : ENat) + (t.2.1 : ENat) + (t.2.2 : ENat) +
                muchnikRegionMargin n := by
              gcongr
        _ < (4 * n : ENat) := by exact_mod_cast htAdm.2.2
    rcases hBounds z with h | h | h
    · exact (not_le_of_gt hX) h
    · exact (not_le_of_gt hY) h
    · exact (not_le_of_gt hXY) h

theorem exists_muchnikRegionSurvivor
    (V : Map) {n : Nat} (hn : 0 < n) :
  ∃ x y, IsMuchnikRegionSurvivor V n x y := by
  classical
  let L := 2 * n + 2
  let marginalBound := 2 * n - 1
  let pairBound := 3 * n - 1
  let U := (stringsOfLength L).product (stringsOfLength L)
  let B₁ := U.filter fun p => plainK V p.1 ≤ (marginalBound : ENat)
  let B₂ := U.filter fun p => plainK V p.2 ≤ (marginalBound : ENat)
  let B₃ := U.filter fun p => pairPlainK V p.1 p.2 ≤ (pairBound : ENat)
  let B₄ := muchnikRegionBadPairs V n
  have hB₁ : B₁.card < 2 ^ (4 * n + 2) := by
    have hExponent : 2 * n + 2 + (2 * n - 1) + 1 = 4 * n + 2 := by omega
    have H := card_fixedLengthPairs_lowLeft_lt V (2 * n + 2) (2 * n - 1)
    rw [hExponent] at H
    convert H using 1
  have hB₂ : B₂.card < 2 ^ (4 * n + 2) := by
    have hExponent : 2 * n + 2 + (2 * n - 1) + 1 = 4 * n + 2 := by omega
    have H := card_fixedLengthPairs_lowRight_lt V (2 * n + 2) (2 * n - 1)
    rw [hExponent] at H
    convert H using 1
  have hB₃ : B₃.card < 2 ^ (3 * n) := by
    have hExponent : 3 * n - 1 + 1 = 3 * n := by omega
    have H := card_fixedLengthPairs_lowPair_lt V (2 * n + 2) (3 * n - 1)
    rw [hExponent] at H
    convert H using 1
  have hB₄ : B₄.card < 2 ^ (4 * n + 2) := by
    dsimp [B₄]
    exact card_muchnikRegionBadPairs_lt V hn
  have hU : U.card = 2 ^ (4 * n + 4) := by
    dsimp [U, L]
    rw [Finset.card_product]
    simp only [cardStringsOfLength]
    rw [← pow_add]
    congr 1
    omega
  have hBad : B₁.card + B₂.card + B₃.card + B₄.card < U.card := by
    rw [hU]
    have hThreePow : 2 ^ (3 * n) ≤ 2 ^ (4 * n) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    calc
      B₁.card + B₂.card + B₃.card + B₄.card
          < 2 ^ (4 * n + 2) + 2 ^ (4 * n + 2) +
              2 ^ (4 * n) + 2 ^ (4 * n + 2) := by omega
      _ = 13 * 2 ^ (4 * n) := by
        rw [show 4 * n + 2 = 4 * n + 2 by rfl, pow_add]
        norm_num
        ring
      _ < 16 * 2 ^ (4 * n) :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.pow_pos (by norm_num))
      _ = 2 ^ (4 * n + 4) := by
        rw [pow_add]
        norm_num
        ring
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
    rw [Finset.mem_filter]
    exact ⟨hpU, hx⟩
  have hyNotLow : ¬plainK V y ≤ ((2 * n - 1 : Nat) : ENat) := by
    intro hy
    apply hp₂
    dsimp [B₂, marginalBound]
    rw [Finset.mem_filter]
    exact ⟨hpU, hy⟩
  have hxyNotLow : ¬pairPlainK V x y ≤ ((3 * n - 1 : Nat) : ENat) := by
    intro hxy
    apply hp₃
    dsimp [B₃, pairBound]
    rw [Finset.mem_filter]
    exact ⟨hpU, hxy⟩
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
  have hObstruction :
      ∀ z,
        (3 * n : ENat) ≤ plainK V z + condK V x z + muchnikRegionMargin n ∨
        (3 * n : ENat) ≤ plainK V z + condK V y z + muchnikRegionMargin n ∨
        (4 * n : ENat) ≤ plainK V z + condK V x z + condK V y z +
          muchnikRegionMargin n := by
    apply (not_mem_muchnikRegionBadPairs_iff V n x y).mp
    exact hp₄
  exact ⟨x, y, hLengths.1, hLengths.2, hxComplex, hyComplex, hxyComplex, hObstruction⟩

end Kolmogorov
