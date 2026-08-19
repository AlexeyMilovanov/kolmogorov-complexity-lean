import KolmogorovMathlib.CommonInformation.Definitions
import KolmogorovMathlib.CommonInformation.WorstCaseRegionBounds
import KolmogorovMathlib.CommonInformation.WorstCaseRegionCounting
import KolmogorovMathlib.CommonInformation.CompactAdvice
import KolmogorovMathlib.CommonInformation.WorstCaseSelector
import KolmogorovMathlib.CommonInformation.Counting

open ENat

namespace Kolmogorov

noncomputable def muchnikRegionConditionalAdvice
    (V : Map) (n : Nat) : Nat :=
  ((muchnikConditionalBounds n).map fun b =>
    (conditionalDescriptionPairsLe V b.1 b.2).card).sum

noncomputable def muchnikRegionAdviceCount
    (V : Map) (n : Nat) : Nat :=
  (compressibleWords V [] (2 * n - 1)).card +
  (compressibleWords V [] (3 * n - 1)).card +
  muchnikRegionConditionalAdvice V n

theorem muchnikRegion_conditional_pow_lt {n α δ : Nat}
    (h : α + δ + muchnikRegionMargin n < 3 * n) :
  (3 * n) ^ 2 * 2 ^ (α + δ + 2) < 2 ^ (3 * n) := by
  have hMarginLower : 32 ≤ muchnikRegionMargin n := by
    simp only [muchnikRegionMargin, logSlack]
    omega
  have hThreeN : 2 ≤ 3 * n := by omega
  have hPolynomial :
      4 * (3 * n) ^ 2 < 2 ^ muchnikRegionMargin n := by
    calc
      4 * (3 * n) ^ 2 = 2 * (2 * (3 * n) ^ 2) := by ring
      _ ≤ 2 * ((3 * n) * (3 * n) ^ 2) := by
        exact Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_right ((3 * n) ^ 2) hThreeN)
      _ = 2 * (3 * n) ^ 3 := by ring
      _ < 2 ^ muchnikRegionMargin n :=
        two_mul_muchnikRegion_cubic_lt n
  calc
    (3 * n) ^ 2 * 2 ^ (α + δ + 2)
        = (4 * (3 * n) ^ 2) * 2 ^ (α + δ) := by
          rw [show α + δ + 2 = (α + δ) + 2 by omega, pow_add]
          norm_num
          ring
    _ < 2 ^ muchnikRegionMargin n * 2 ^ (α + δ) :=
      Nat.mul_lt_mul_of_pos_right hPolynomial (Nat.pow_pos (by norm_num))
    _ = 2 ^ (muchnikRegionMargin n + (α + δ)) := by rw [← pow_add]
    _ < 2 ^ (3 * n) := by
      apply Nat.pow_lt_pow_right (by norm_num)
      omega

theorem muchnikRegionConditionalAdvice_sum_lt
    (V : Map) {n : Nat} (hn : 0 < n) :
  muchnikRegionConditionalAdvice V n < 2 ^ (3 * n) := by
  classical
  by_cases hEmpty : muchnikConditionalBounds n = []
  · simp [muchnikRegionConditionalAdvice, hEmpty]
  · obtain ⟨b₀, bs, hList⟩ := List.exists_cons_of_ne_nil hEmpty
    have hb₀ : b₀ ∈ muchnikConditionalBounds n := by
      rw [hList]
      exact List.Mem.head bs
    have hMarginLe : muchnikRegionMargin n ≤ 3 * n := by
      have hAdm := (mem_muchnikConditionalBounds_iff n b₀).mp hb₀
      omega
    have hMarginLower : 32 ≤ muchnikRegionMargin n := by
      simp only [muchnikRegionMargin, logSlack]
      omega
    let s := muchnikRegionMargin n - 1
    let r := 3 * n - s
    have hEach :
        ∀ b ∈ muchnikConditionalBounds n,
          (conditionalDescriptionPairsLe V b.1 b.2).card ≤ 2 ^ r := by
      intro b hb
      have hAdm := (mem_muchnikConditionalBounds_iff n b).mp hb
      have hExponent : (b.1 + 1) + (b.2 + 1) ≤ r := by
        dsimp [r, s]
        omega
      exact (card_conditionalDescriptionPairsLe_lt V b.1 b.2).le.trans
        (Nat.pow_le_pow_right (by norm_num) hExponent)
    have sum_le_length_mul :
        ∀ l : List (Nat × Nat),
          (∀ b ∈ l,
            (conditionalDescriptionPairsLe V b.1 b.2).card ≤ 2 ^ r) →
          (l.map fun b =>
            (conditionalDescriptionPairsLe V b.1 b.2).card).sum
              ≤ l.length * 2 ^ r := by
      intro l hl
      induction l with
      | nil => simp
      | cons b l ih =>
          have hb :
              (conditionalDescriptionPairsLe V b.1 b.2).card ≤ 2 ^ r :=
            hl b (List.Mem.head l)
          have hTail :
              ∀ b' ∈ l,
                (conditionalDescriptionPairsLe V b'.1 b'.2).card ≤ 2 ^ r := by
            intro b' hb'
            exact hl b' (List.Mem.tail b hb')
          have ih' := ih hTail
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          nlinarith
    have hSum :
        ((muchnikConditionalBounds n).map fun b =>
            (conditionalDescriptionPairsLe V b.1 b.2).card).sum
          ≤ (muchnikConditionalBounds n).length * 2 ^ r := by
      exact sum_le_length_mul (muchnikConditionalBounds n) hEach
    have hLength :
        (muchnikConditionalBounds n).length ≤ (3 * n) ^ 2 :=
      length_muchnikConditionalBounds_le n
    have hSquare :
        (3 * n) ^ 2 < 2 ^ s := by
      have hThreeN : 1 ≤ 3 * n := by
        have hAdm := (mem_muchnikConditionalBounds_iff n b₀).mp hb₀
        omega
      have hDoubleSquare :
          2 * (3 * n) ^ 2 < 2 ^ muchnikRegionMargin n := by
        have hPow : (3 * n) ^ 2 ≤ (3 * n) ^ 3 := by
          rw [show (3 : Nat) = 2 + 1 by omega, pow_succ]
          exact Nat.le_mul_of_pos_right _ hThreeN
        calc
          2 * (3 * n) ^ 2 ≤ 2 * (3 * n) ^ 3 :=
            Nat.mul_le_mul_left 2 hPow
          _ < 2 ^ muchnikRegionMargin n :=
            two_mul_muchnikRegion_cubic_lt n
      have hMarginSucc :
          muchnikRegionMargin n = s + 1 := by
        dsimp [s]
        omega
      have hPowSucc : 2 ^ (s + 1) = 2 ^ s * 2 := by rw [pow_succ]
      rw [hMarginSucc, hPowSucc] at hDoubleSquare
      omega
    unfold muchnikRegionConditionalAdvice
    calc
      ((muchnikConditionalBounds n).map fun b =>
          (conditionalDescriptionPairsLe V b.1 b.2).card).sum
          ≤ (muchnikConditionalBounds n).length * 2 ^ r := hSum
      _ ≤ (3 * n) ^ 2 * 2 ^ r := Nat.mul_le_mul_right _ hLength
      _ < 2 ^ s * 2 ^ r :=
        Nat.mul_lt_mul_of_pos_right hSquare (Nat.pow_pos (by norm_num))
      _ = 2 ^ (3 * n) := by
        rw [← pow_add]
        congr 1
        dsimp [r, s]
        omega

theorem muchnikRegion_advice_three_sum_lt {n : Nat} (hn : 0 < n) :
  2 ^ (2 * n) + 2 ^ (3 * n) + 2 ^ (3 * n) < 2 ^ (3 * n + 2) := by
  have hPow : 2 ^ (2 * n) < 2 ^ (3 * n) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  calc
    2 ^ (2 * n) + 2 ^ (3 * n) + 2 ^ (3 * n)
        < 3 * 2 ^ (3 * n) := by omega
    _ < 4 * 2 ^ (3 * n) :=
      Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.pow_pos (by norm_num))
    _ = 2 ^ (3 * n + 2) := by
      rw [pow_add]
      norm_num
      ring

theorem muchnikRegionAdviceCount_lt
    (V : Map) {n : Nat} (hn : 0 < n) :
  muchnikRegionAdviceCount V n < 2 ^ (3 * n + 2) := by
  have hMarginal :
      (compressibleWords V [] (2 * n - 1)).card < 2 ^ (2 * n) := by
    have h := cardCompressibleWordsLt V [] (2 * n - 1)
    have hExponent : 2 * n - 1 + 1 = 2 * n := by omega
    simpa only [hExponent] using h
  have hPair :
      (compressibleWords V [] (3 * n - 1)).card < 2 ^ (3 * n) := by
    have h := cardCompressibleWordsLt V [] (3 * n - 1)
    have hExponent : 3 * n - 1 + 1 = 3 * n := by omega
    simpa only [hExponent] using h
  have hConditional :
      muchnikRegionConditionalAdvice V n < 2 ^ (3 * n) :=
    muchnikRegionConditionalAdvice_sum_lt V hn
  unfold muchnikRegionAdviceCount
  exact lt_of_lt_of_le
    (show
      (compressibleWords V [] (2 * n - 1)).card +
          (compressibleWords V [] (3 * n - 1)).card +
          muchnikRegionConditionalAdvice V n
        < 2 ^ (2 * n) + 2 ^ (3 * n) + 2 ^ (3 * n) by omega)
    (muchnikRegion_advice_three_sum_lt hn).le

end Kolmogorov
