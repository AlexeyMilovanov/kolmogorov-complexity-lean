import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.CommonInformation.Definitions
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.CommonInformation.CompactAdvice
import KolmogorovMathlib.CommonInformation.WorstCaseCounting

namespace Kolmogorov

def muchnikRegionMargin (n : Nat) : Nat := logSlack 32 n

def muchnikAdmissibleTriples (n : Nat) : List CommonInformationTriple :=
  (((List.range (3 * n)).product (List.range (3 * n))).product (List.range (3 * n))).filterMap
    fun ⟨⟨a, b⟩, c⟩ =>
      if a + b + muchnikRegionMargin n < 3 * n ∧
         a + c + muchnikRegionMargin n < 3 * n ∧
         a + b + c + muchnikRegionMargin n < 4 * n
      then some (a, b, c) else none

def muchnikConditionalBounds (n : Nat) : List (Nat × Nat) :=
  ((List.range (3 * n)).product (List.range (3 * n))).filterMap
    fun ⟨a, d⟩ =>
      if a + d + muchnikRegionMargin n < 3 * n
      then some (a, d) else none

def IsMuchnikRegionSurvivor (V : Map) (n : Nat) (x y : BitString) : Prop :=
  x.length = 2 * n + 2 ∧
  y.length = 2 * n + 2 ∧
  (2 * n : ENat) ≤ plainK V x ∧
  (2 * n : ENat) ≤ plainK V y ∧
  (3 * n : ENat) ≤ pairPlainK V x y ∧
  ∀ z,
    (3 * n : ENat) ≤ plainK V z + condK V x z + muchnikRegionMargin n ∨
    (3 * n : ENat) ≤ plainK V z + condK V y z + muchnikRegionMargin n ∨
    (4 * n : ENat) ≤ plainK V z + condK V x z + condK V y z + muchnikRegionMargin n

theorem mem_muchnikAdmissibleTriples_iff (n : Nat) (t : CommonInformationTriple) :
  t ∈ muchnikAdmissibleTriples n ↔
    t.1 + t.2.1 + muchnikRegionMargin n < 3 * n ∧
    t.1 + t.2.2 + muchnikRegionMargin n < 3 * n ∧
    t.1 + t.2.1 + t.2.2 + muchnikRegionMargin n < 4 * n := by
  rcases t with ⟨a, b, c⟩
  simp [muchnikAdmissibleTriples]
  omega

theorem mem_muchnikConditionalBounds_iff (n : Nat) (b : Nat × Nat) :
  b ∈ muchnikConditionalBounds n ↔
    b.1 + b.2 + muchnikRegionMargin n < 3 * n := by
  rcases b with ⟨a, d⟩
  simp [muchnikConditionalBounds]
  omega

theorem muchnikAdmissibleTriple_projections {n : Nat} {t : CommonInformationTriple}
    (ht : t ∈ muchnikAdmissibleTriples n) :
  (t.1, t.2.1) ∈ muchnikConditionalBounds n ∧
  (t.1, t.2.2) ∈ muchnikConditionalBounds n := by
  rw [mem_muchnikAdmissibleTriples_iff] at ht
  constructor <;> rw [mem_muchnikConditionalBounds_iff]
  · exact ht.1
  · exact ht.2.1

theorem muchnikAdmissibleTriples_nodup (n : Nat) :
  (muchnikAdmissibleTriples n).Nodup := by
  unfold muchnikAdmissibleTriples
  apply List.Nodup.filterMap
  · rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ t ht ht'
    change t ∈ (if a + b + muchnikRegionMargin n < 3 * n ∧
        a + c + muchnikRegionMargin n < 3 * n ∧
        a + b + c + muchnikRegionMargin n < 4 * n
      then some (a, b, c) else none) at ht
    change t ∈ (if a' + b' + muchnikRegionMargin n < 3 * n ∧
        a' + c' + muchnikRegionMargin n < 3 * n ∧
        a' + b' + c' + muchnikRegionMargin n < 4 * n
      then some (a', b', c') else none) at ht'
    by_cases h : a + b + muchnikRegionMargin n < 3 * n ∧
        a + c + muchnikRegionMargin n < 3 * n ∧
        a + b + c + muchnikRegionMargin n < 4 * n
    · rw [if_pos h] at ht
      injection ht with ht
      by_cases h' : a' + b' + muchnikRegionMargin n < 3 * n ∧
          a' + c' + muchnikRegionMargin n < 3 * n ∧
          a' + b' + c' + muchnikRegionMargin n < 4 * n
      · rw [if_pos h'] at ht'
        injection ht' with ht'
        cases ht
        cases ht'
        rfl
      · simp [h'] at ht'
    · simp [h] at ht
  · exact ((List.nodup_range.product List.nodup_range).product List.nodup_range)

theorem muchnikConditionalBounds_nodup (n : Nat) :
  (muchnikConditionalBounds n).Nodup := by
  unfold muchnikConditionalBounds
  apply List.Nodup.filterMap
  · rintro ⟨a, d⟩ ⟨a', d'⟩ b hb hb'
    change b ∈ (if a + d + muchnikRegionMargin n < 3 * n
      then some (a, d) else none) at hb
    change b ∈ (if a' + d' + muchnikRegionMargin n < 3 * n
      then some (a', d') else none) at hb'
    by_cases h : a + d + muchnikRegionMargin n < 3 * n
    · rw [if_pos h] at hb
      injection hb with hb
      by_cases h' : a' + d' + muchnikRegionMargin n < 3 * n
      · rw [if_pos h'] at hb'
        injection hb' with hb'
        cases hb
        cases hb'
        rfl
      · simp [h'] at hb'
    · simp [h] at hb
  · exact List.nodup_range.product List.nodup_range

theorem length_muchnikAdmissibleTriples_le (n : Nat) :
  (muchnikAdmissibleTriples n).length ≤ (3 * n) ^ 3 := by
  unfold muchnikAdmissibleTriples
  calc
    _ ≤ ((((List.range (3 * n)).product (List.range (3 * n))).product
        (List.range (3 * n))).length) := List.length_filterMap_le _ _
    _ = (3 * n) ^ 3 := by simp [List.product, pow_succ]

theorem length_muchnikConditionalBounds_le (n : Nat) :
  (muchnikConditionalBounds n).length ≤ (3 * n) ^ 2 := by
  unfold muchnikConditionalBounds
  calc
    _ ≤ (((List.range (3 * n)).product (List.range (3 * n))).length) :=
      List.length_filterMap_le _ _
    _ = (3 * n) ^ 2 := by simp [List.product, pow_two]

/-- The fixed margin uniformly absorbs even twice the cubic parameter scan.
This is stronger than the polynomial factor needed in the later semantic-union
and compact-advice cardinality estimates. -/
theorem two_mul_muchnikRegion_cubic_lt (n : Nat) :
    2 * (3 * n) ^ 3 < 2 ^ muchnikRegionMargin n := by
  let b := (Nat.bits n).length
  have hn : n ≤ 2 ^ b := (lt_two_pow_length_natBits n).le
  have hthree : 3 * n ≤ 2 ^ (b + 2) := by
    calc
      3 * n ≤ 3 * 2 ^ b := Nat.mul_le_mul_left 3 hn
      _ ≤ 4 * 2 ^ b := by omega
      _ = 2 ^ (b + 2) := by rw [pow_add]; norm_num; omega
  calc
    2 * (3 * n) ^ 3 ≤ 2 * (2 ^ (b + 2)) ^ 3 :=
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hthree 3)
    _ = 2 * 2 ^ ((b + 2) * 3) := by rw [pow_mul]
    _ = 2 ^ ((b + 2) * 3 + 1) := by rw [pow_succ]; omega
    _ < 2 ^ muchnikRegionMargin n := by
      apply Nat.pow_lt_pow_right (by norm_num)
      simp only [muchnikRegionMargin, logSlack, b]
      omega

theorem muchnikRegionMargin_primrec :
    Primrec muchnikRegionMargin := by
  unfold muchnikRegionMargin logSlack
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 32)
      (Primrec.list_length.comp primrecNatBits))
    (Primrec.const 32)

theorem muchnikAdmissibleTriples_primrec :
  Primrec muchnikAdmissibleTriples := by
  have hThreeN : Primrec (fun n : Nat => 3 * n) :=
    Primrec.nat_mul.comp (Primrec.const 3) Primrec.id
  have hFourN : Primrec (fun n : Nat => 4 * n) :=
    Primrec.nat_mul.comp (Primrec.const 4) Primrec.id
  have hRange : Primrec (fun n : Nat => List.range (3 * n)) :=
    Primrec.list_range.comp hThreeN
  have hPairBody : Primrec₂ (fun (n a : Nat) =>
      (List.range (3 * n)).map fun b => (a, b)) :=
    (Primrec.list_map
      (hRange.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂
  have hPairs : Primrec (fun n : Nat =>
      (List.range (3 * n)).product (List.range (3 * n))) := by
    exact Primrec.list_flatMap hRange hPairBody
  have hTripleBody : Primrec₂ (fun (n : Nat) (ab : Nat × Nat) =>
      (List.range (3 * n)).map fun c => (ab, c)) :=
    (Primrec.list_map
      (hRange.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂
  have hTriples : Primrec (fun n : Nat =>
      ((List.range (3 * n)).product (List.range (3 * n))).product
        (List.range (3 * n))) := by
    exact Primrec.list_flatMap hPairs hTripleBody
  have hN : Primrec (fun q : Nat × ((Nat × Nat) × Nat) => q.1) :=
    Primrec.fst
  have hA : Primrec (fun q : Nat × ((Nat × Nat) × Nat) => q.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hB : Primrec (fun q : Nat × ((Nat × Nat) × Nat) => q.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hC : Primrec (fun q : Nat × ((Nat × Nat) × Nat) => q.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hMarginN : Primrec (fun q : Nat × ((Nat × Nat) × Nat) =>
      muchnikRegionMargin q.1) := muchnikRegionMargin_primrec.comp hN
  have hThreeN' : Primrec (fun q : Nat × ((Nat × Nat) × Nat) => 3 * q.1) :=
    hThreeN.comp hN
  have hFourN' : Primrec (fun q : Nat × ((Nat × Nat) × Nat) => 4 * q.1) :=
    hFourN.comp hN
  have hAB : Primrec (fun q : Nat × ((Nat × Nat) × Nat) =>
      q.2.1.1 + q.2.1.2 + muchnikRegionMargin q.1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hA hB) hMarginN
  have hAC : Primrec (fun q : Nat × ((Nat × Nat) × Nat) =>
      q.2.1.1 + q.2.2 + muchnikRegionMargin q.1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hA hC) hMarginN
  have hABC : Primrec (fun q : Nat × ((Nat × Nat) × Nat) =>
      q.2.1.1 + q.2.1.2 + q.2.2 + muchnikRegionMargin q.1) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp hA hB) hC) hMarginN
  have hPred : PrimrecPred (fun q : Nat × ((Nat × Nat) × Nat) =>
      q.2.1.1 + q.2.1.2 + muchnikRegionMargin q.1 < 3 * q.1 ∧
      q.2.1.1 + q.2.2 + muchnikRegionMargin q.1 < 3 * q.1 ∧
      q.2.1.1 + q.2.1.2 + q.2.2 + muchnikRegionMargin q.1 < 4 * q.1) :=
    (Primrec.nat_lt.comp hAB hThreeN').and
      ((Primrec.nat_lt.comp hAC hThreeN').and
        (Primrec.nat_lt.comp hABC hFourN'))
  have hOut : Primrec (fun q : Nat × ((Nat × Nat) × Nat) =>
      if q.2.1.1 + q.2.1.2 + muchnikRegionMargin q.1 < 3 * q.1 ∧
         q.2.1.1 + q.2.2 + muchnikRegionMargin q.1 < 3 * q.1 ∧
         q.2.1.1 + q.2.1.2 + q.2.2 + muchnikRegionMargin q.1 < 4 * q.1
      then some (q.2.1.1, q.2.1.2, q.2.2) else none) :=
    Primrec.ite hPred
      (Primrec.option_some.comp (hA.pair (hB.pair hC)))
      (Primrec.const none)
  unfold muchnikAdmissibleTriples
  exact Primrec.listFilterMap hTriples hOut.to₂

theorem muchnikConditionalBounds_primrec :
  Primrec muchnikConditionalBounds := by
  have hThreeN : Primrec (fun n : Nat => 3 * n) :=
    Primrec.nat_mul.comp (Primrec.const 3) Primrec.id
  have hRange : Primrec (fun n : Nat => List.range (3 * n)) :=
    Primrec.list_range.comp hThreeN
  have hPairBody : Primrec₂ (fun (n a : Nat) =>
      (List.range (3 * n)).map fun d => (a, d)) :=
    (Primrec.list_map
      (hRange.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂
  have hPairs : Primrec (fun n : Nat =>
      (List.range (3 * n)).product (List.range (3 * n))) := by
    exact Primrec.list_flatMap hRange hPairBody
  have hN : Primrec (fun q : Nat × (Nat × Nat) => q.1) := Primrec.fst
  have hA : Primrec (fun q : Nat × (Nat × Nat) => q.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hD : Primrec (fun q : Nat × (Nat × Nat) => q.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hPred : PrimrecPred (fun q : Nat × (Nat × Nat) =>
      q.2.1 + q.2.2 + muchnikRegionMargin q.1 < 3 * q.1) :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp hA hD)
        (muchnikRegionMargin_primrec.comp hN))
      (hThreeN.comp hN)
  have hOut : Primrec (fun q : Nat × (Nat × Nat) =>
      if q.2.1 + q.2.2 + muchnikRegionMargin q.1 < 3 * q.1
      then some (q.2.1, q.2.2) else none) :=
    Primrec.ite hPred
      (Primrec.option_some.comp (hA.pair hD))
      (Primrec.const none)
  unfold muchnikConditionalBounds
  exact Primrec.listFilterMap hPairs hOut.to₂

end Kolmogorov
