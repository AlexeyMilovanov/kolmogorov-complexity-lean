import KolmogorovMathlib.CommonInformation.WorstCaseRegionStages

namespace Kolmogorov

open Nat.Partrec (Code)

private def sharedWitnessLists
    (r : (List BitString × List BitString) ×
      (BitString × BitString)) : Bool :=
  r.1.1.any fun p =>
    decide (pairCode (decodeFirst p) r.2.1 ∈ r.1.1) &&
    decide (pairCode (decodeFirst p) r.2.2 ∈ r.1.2)

private theorem sharedWitnessLists_primrec :
    Primrec sharedWitnessLists := by
  have hLeft : Primrec
      (fun r : (List BitString × List BitString) ×
        (BitString × BitString) => r.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hPred : Primrec₂
      (fun (r : (List BitString × List BitString) ×
          (BitString × BitString)) (p : BitString) =>
        decide (pairCode (decodeFirst p) r.2.1 ∈ r.1.1) &&
        decide (pairCode (decodeFirst p) r.2.2 ∈ r.1.2)) := by
    have hFirst : Primrec
        (fun s : ((List BitString × List BitString) ×
            (BitString × BitString)) × BitString =>
          decide (pairCode (decodeFirst s.2) s.1.2.1 ∈ s.1.1.1)) :=
      bitString_mem_primrec.comp
        (pairCode_primrec.comp
          (decodeFirst_primrec'.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hSecond : Primrec
        (fun s : ((List BitString × List BitString) ×
            (BitString × BitString)) × BitString =>
          decide (pairCode (decodeFirst s.2) s.1.2.2 ∈ s.1.1.2)) :=
      bitString_mem_primrec.comp
        (pairCode_primrec.comp
          (decodeFirst_primrec'.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    exact (Primrec.and.comp hFirst hSecond).to₂
  exact (list_any_primrec hLeft hPred).of_eq fun _ => rfl

private def sharedWitnessLeftStage (c : Code)
    (r : (Nat × CommonInformationTriple) ×
      (BitString × BitString)) : List BitString :=
  conditionalDescriptionPairsStage c
    r.1.2.1 r.1.2.2.1 r.1.1

private theorem sharedWitnessLeftStage_primrec (c : Code) :
    Primrec (sharedWitnessLeftStage c) := by
  have ht : Primrec
      (fun r : (Nat × CommonInformationTriple) ×
          (BitString × BitString) => r.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec
      (fun r : (Nat × CommonInformationTriple) ×
          (BitString × BitString) => r.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hb : Primrec
      (fun r : (Nat × CommonInformationTriple) ×
          (BitString × BitString) => r.1.2.2.1) :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact ((conditionalDescriptionPairsStage_primrec c).comp
    (Primrec.pair (Primrec.pair ha hb) ht)).of_eq fun _ => rfl

private def sharedWitnessRightStage (c : Code)
    (r : (Nat × CommonInformationTriple) ×
      (BitString × BitString)) : List BitString :=
  conditionalDescriptionPairsStage c
    r.1.2.1 r.1.2.2.2 r.1.1

private theorem sharedWitnessRightStage_primrec (c : Code) :
    Primrec (sharedWitnessRightStage c) := by
  have ht : Primrec
      (fun r : (Nat × CommonInformationTriple) ×
          (BitString × BitString) => r.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec
      (fun r : (Nat × CommonInformationTriple) ×
          (BitString × BitString) => r.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hd : Primrec
      (fun r : (Nat × CommonInformationTriple) ×
          (BitString × BitString) => r.1.2.2.2) :=
    Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact ((conditionalDescriptionPairsStage_primrec c).comp
    (Primrec.pair (Primrec.pair ha hd) ht)).of_eq fun _ => rfl

private def sharedWitnessStageArgs (c : Code)
    (r : (Nat × CommonInformationTriple) ×
      (BitString × BitString)) :
    (List BitString × List BitString) ×
      (BitString × BitString) :=
  ((sharedWitnessLeftStage c r, sharedWitnessRightStage c r),
    (r.2.1, r.2.2))

private theorem sharedWitnessStageArgs_primrec (c : Code) :
    Primrec (sharedWitnessStageArgs c) := by
  exact (((sharedWitnessLeftStage_primrec c).pair
      (sharedWitnessRightStage_primrec c)).pair
    ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

def muchnikRegionSharedWitnessAtStage
    (c : Code) (t : Nat) (q : CommonInformationTriple)
    (x y : BitString) : Bool :=
  sharedWitnessLists
    ((conditionalDescriptionPairsStage c q.1 q.2.1 t,
      conditionalDescriptionPairsStage c q.1 q.2.2 t), (x, y))

theorem muchnikRegionSharedWitnessAtStage_eq_true_iff
    {c : Code} {t : Nat} {q : CommonInformationTriple} {x y : BitString} :
  muchnikRegionSharedWitnessAtStage c t q x y = true ↔
    ∃ z,
      pairCode z x ∈
        conditionalDescriptionPairsStage c q.1 q.2.1 t ∧
      pairCode z y ∈
        conditionalDescriptionPairsStage c q.1 q.2.2 t := by
  let left :=
    conditionalDescriptionPairsStage c q.1 q.2.1 t
  let right :=
    conditionalDescriptionPairsStage c q.1 q.2.2 t
  change
    left.any (fun p =>
      decide (pairCode (decodeFirst p) x ∈ left) &&
      decide (pairCode (decodeFirst p) y ∈ right)) = true ↔
      ∃ z, pairCode z x ∈ left ∧ pairCode z y ∈ right
  constructor
  · simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨p, _hp, hpx, hpy⟩
    exact ⟨decodeFirst p, hpx, hpy⟩
  · rintro ⟨z, hzx, hzy⟩
    rw [List.any_eq_true]
    refine ⟨pairCode z x, hzx, ?_⟩
    simp only [decodeFirst_pairCode, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hzx, hzy⟩

theorem muchnikRegionSharedWitnessAtStage_primrec (c : Code) :
  Primrec
    (fun r : (Nat × CommonInformationTriple) ×
        (BitString × BitString) =>
      muchnikRegionSharedWitnessAtStage
        c r.1.1 r.1.2 r.2.1 r.2.2) := by
  exact (sharedWitnessLists_primrec.comp
    (sharedWitnessStageArgs_primrec c)).of_eq fun _ => rfl

private theorem pairCode_mem_conditionalDescriptionPairsStage_iff_of_complete
    {V : Map} {c : Code} {α β t : Nat} {z v : BitString}
    (hcomplete :
      (conditionalDescriptionPairsStage c α β t).toFinset =
        conditionalDescriptionPairsLe V α β) :
    pairCode z v ∈ conditionalDescriptionPairsStage c α β t ↔
      plainK V z ≤ (α : ENat) ∧
      condK V v z ≤ (β : ENat) := by
  rw [← List.mem_toFinset, hcomplete,
    mem_conditionalDescriptionPairsLe_iff]
  constructor
  · rintro ⟨z', v', hcode, hz, hv⟩
    have hpair : (z, v) = (z', v') :=
      pairCode_injective hcode
    cases hpair
    exact ⟨hz, hv⟩
  · rintro ⟨hz, hv⟩
    exact ⟨z, v, rfl, hz, hv⟩

theorem muchnikRegionSharedWitnessAtStage_complete_iff
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n t : Nat} {q : CommonInformationTriple} {x y : BitString}
    (hcount :
      muchnikRegionMergedStageCount c n t =
        muchnikRegionAdviceCount V n)
    (hq : q ∈ muchnikAdmissibleTriples n) :
  muchnikRegionSharedWitnessAtStage c t q x y = true ↔
    ∃ z,
      plainK V z ≤ (q.1 : ENat) ∧
      condK V x z ≤ (q.2.1 : ENat) ∧
      condK V y z ≤ (q.2.2 : ENat) := by
  obtain ⟨_, _, hConditional⟩ :=
    muchnikRegionMergedStage_exact_of_total hc hcount
  obtain ⟨hLeftProjection, hRightProjection⟩ :=
    muchnikAdmissibleTriple_projections hq
  have hLeftComplete :
      (conditionalDescriptionPairsStage c
        q.1 q.2.1 t).toFinset =
      conditionalDescriptionPairsLe V q.1 q.2.1 := by
    simpa only [Prod.fst, Prod.snd] using
      hConditional (q.1, q.2.1) hLeftProjection
  have hRightComplete :
      (conditionalDescriptionPairsStage c
        q.1 q.2.2 t).toFinset =
      conditionalDescriptionPairsLe V q.1 q.2.2 := by
    simpa only [Prod.fst, Prod.snd] using
      hConditional (q.1, q.2.2) hRightProjection
  rw [muchnikRegionSharedWitnessAtStage_eq_true_iff]
  constructor
  · rintro ⟨z, hzx, hzy⟩
    have hxSem :=
      (pairCode_mem_conditionalDescriptionPairsStage_iff_of_complete
        hLeftComplete).mp hzx
    have hySem :=
      (pairCode_mem_conditionalDescriptionPairsStage_iff_of_complete
        hRightComplete).mp hzy
    exact ⟨z, hxSem.1, hxSem.2, hySem.2⟩
  · rintro ⟨z, hz, hx, hy⟩
    refine ⟨z, ?_, ?_⟩
    · exact
        (pairCode_mem_conditionalDescriptionPairsStage_iff_of_complete
          hLeftComplete).mpr ⟨hz, hx⟩
    · exact
        (pairCode_mem_conditionalDescriptionPairsStage_iff_of_complete
          hRightComplete).mpr ⟨hz, hy⟩

def muchnikRegionBadAtStage
    (c : Code) (n t : Nat) (w : BitString) : Bool :=
  let marginal := boundedOutputStage c (2 * n - 1) t
  let pairs := boundedOutputStage c (3 * n - 1) t
  let x := decodeFirst w
  let y := decodeSecond w
  decide (x ∈ marginal) ||
    decide (y ∈ marginal) ||
    decide (pairCode x y ∈ pairs) ||
    (muchnikAdmissibleTriples n).any fun q =>
      muchnikRegionSharedWitnessAtStage c t q x y

theorem muchnikRegionBadAtStage_primrec (c : Code) :
  Primrec
    (fun r : (Nat × Nat) × BitString =>
      muchnikRegionBadAtStage c r.1.1 r.1.2 r.2) := by
  have hn : Primrec
      (fun r : (Nat × Nat) × BitString => r.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ht : Primrec
      (fun r : (Nat × Nat) × BitString => r.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec
      (fun r : (Nat × Nat) × BitString => r.2) :=
    Primrec.snd
  have hx : Primrec
      (fun r : (Nat × Nat) × BitString =>
        decodeFirst r.2) :=
    decodeFirst_primrec'.comp hw
  have hy : Primrec
      (fun r : (Nat × Nat) × BitString =>
        decodeSecond r.2) :=
    decodeSecond_primrec'.comp hw
  have hMarginalBound : Primrec
      (fun r : (Nat × Nat) × BitString =>
        2 * r.1.1 - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 2) hn)
      (Primrec.const 1)
  have hPairBound : Primrec
      (fun r : (Nat × Nat) × BitString =>
        3 * r.1.1 - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 3) hn)
      (Primrec.const 1)
  have hMarginal : Primrec
      (fun r : (Nat × Nat) × BitString =>
        boundedOutputStage c (2 * r.1.1 - 1) r.1.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair hMarginalBound ht)
  have hPairs : Primrec
      (fun r : (Nat × Nat) × BitString =>
        boundedOutputStage c (3 * r.1.1 - 1) r.1.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair hPairBound ht)
  have hLeft : Primrec
      (fun r : (Nat × Nat) × BitString =>
        decide (decodeFirst r.2 ∈
          boundedOutputStage c (2 * r.1.1 - 1) r.1.2)) :=
    bitString_mem_primrec.comp hx hMarginal
  have hRight : Primrec
      (fun r : (Nat × Nat) × BitString =>
        decide (decodeSecond r.2 ∈
          boundedOutputStage c (2 * r.1.1 - 1) r.1.2)) :=
    bitString_mem_primrec.comp hy hMarginal
  have hPair : Primrec
      (fun r : (Nat × Nat) × BitString =>
        decide (pairCode (decodeFirst r.2) (decodeSecond r.2) ∈
          boundedOutputStage c (3 * r.1.1 - 1) r.1.2)) :=
    bitString_mem_primrec.comp
      (pairCode_primrec.comp hx hy) hPairs
  have hTriples : Primrec
      (fun r : (Nat × Nat) × BitString =>
        muchnikAdmissibleTriples r.1.1) :=
    muchnikAdmissibleTriples_primrec.comp hn
  have hSharedPred : Primrec₂
      (fun (r : (Nat × Nat) × BitString)
          (q : CommonInformationTriple) =>
        muchnikRegionSharedWitnessAtStage c r.1.2 q
          (decodeFirst r.2) (decodeSecond r.2)) := by
    have hArgs : Primrec
        (fun s : ((Nat × Nat) × BitString) ×
            CommonInformationTriple =>
          ((s.1.1.2, s.2),
            (decodeFirst s.1.2, decodeSecond s.1.2))) :=
      ((ht.comp Primrec.fst).pair Primrec.snd).pair
        ((hx.comp Primrec.fst).pair (hy.comp Primrec.fst))
    exact ((muchnikRegionSharedWitnessAtStage_primrec c).comp
      hArgs).to₂
  have hCommon : Primrec
      (fun r : (Nat × Nat) × BitString =>
        (muchnikAdmissibleTriples r.1.1).any fun q =>
          muchnikRegionSharedWitnessAtStage c r.1.2 q
            (decodeFirst r.2) (decodeSecond r.2)) :=
    list_any_primrec hTriples hSharedPred
  unfold muchnikRegionBadAtStage
  exact Primrec.or.comp
    (Primrec.or.comp (Primrec.or.comp hLeft hRight) hPair)
    hCommon

theorem muchnikRegionBadAtStage_false_iff
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n t : Nat} {w : BitString} (hn : 0 < n)
    (hcount :
      muchnikRegionMergedStageCount c n t =
        muchnikRegionAdviceCount V n) :
  muchnikRegionBadAtStage c n t w = false ↔
    (2 * n : ENat) ≤ plainK V (decodeFirst w) ∧
    (2 * n : ENat) ≤ plainK V (decodeSecond w) ∧
    (3 * n : ENat) ≤
      pairPlainK V (decodeFirst w) (decodeSecond w) ∧
    (decodeFirst w, decodeSecond w) ∉
      muchnikRegionBadPairs V n := by
  obtain ⟨hMarginal, hPairs, _hConditional⟩ :=
    muchnikRegionMergedStage_exact_of_total hc hcount
  let marginal := boundedOutputStage c (2 * n - 1) t
  let pairs := boundedOutputStage c (3 * n - 1) t
  let x := decodeFirst w
  let y := decodeSecond w
  have hTwoN : 0 < 2 * n := Nat.mul_pos (by norm_num) hn
  have hThreeN : 0 < 3 * n := Nat.mul_pos (by norm_num) hn
  have hMarginalMem (u : BitString) :
      u ∉ marginal ↔ (2 * n : ENat) ≤ plainK V u := by
    have hfinset :
        marginal.toFinset =
          compressibleWords V [] (2 * n - 1) := by
      simpa only [marginal] using hMarginal
    rw [← List.mem_toFinset, hfinset,
      mem_compressibleWords_iff]
    constructor
    · intro hnot
      apply le_of_not_gt
      intro hlt
      apply hnot
      exact
        (enat_lt_coe_iff_le_pred
          (q := plainK V u) hTwoN).mp hlt
    · intro hlo hle
      exact (not_lt_of_ge hlo)
        ((enat_lt_coe_iff_le_pred
          (q := plainK V u) hTwoN).mpr hle)
  have hPairMem :
      pairCode x y ∉ pairs ↔
        (3 * n : ENat) ≤ pairPlainK V x y := by
    have hfinset :
        pairs.toFinset =
          compressibleWords V [] (3 * n - 1) := by
      simpa only [pairs] using hPairs
    rw [← List.mem_toFinset, hfinset,
      mem_compressibleWords_iff]
    change
      (¬plainK V (pairCode x y) ≤
        ((3 * n - 1 : Nat) : ENat)) ↔
      (3 * n : ENat) ≤ pairPlainK V x y
    constructor
    · intro hnot
      apply le_of_not_gt
      intro hlt
      apply hnot
      exact
        (enat_lt_coe_iff_le_pred
          (q := pairPlainK V x y) hThreeN).mp hlt
    · intro hlo hle
      exact (not_lt_of_ge hlo)
        ((enat_lt_coe_iff_le_pred
          (q := pairPlainK V x y) hThreeN).mpr hle)
  have hCommonBool :
      (muchnikAdmissibleTriples n).any
          (fun q =>
            muchnikRegionSharedWitnessAtStage c t q x y) =
          false ↔
        (x, y) ∉ muchnikRegionBadPairs V n := by
    rw [List.any_eq_false]
    constructor
    · intro hnone hbad
      rw [mem_muchnikRegionBadPairs_iff] at hbad
      obtain ⟨q, hq, z, hz, hxz, hyz⟩ := hbad
      exact hnone q hq
        ((muchnikRegionSharedWitnessAtStage_complete_iff
          hc hcount hq).mpr ⟨z, hz, hxz, hyz⟩)
    · intro hnot q hq hshared
      apply hnot
      rw [mem_muchnikRegionBadPairs_iff]
      obtain ⟨z, hz, hxz, hyz⟩ :=
        (muchnikRegionSharedWitnessAtStage_complete_iff
          hc hcount hq).mp hshared
      exact ⟨q, hq, z, hz, hxz, hyz⟩
  change
    (decide (x ∈ marginal) || decide (y ∈ marginal) ||
      decide (pairCode x y ∈ pairs) ||
      (muchnikAdmissibleTriples n).any
        (fun q =>
          muchnikRegionSharedWitnessAtStage c t q x y)) =
        false ↔ _
  simp only [Bool.or_eq_false_eq_eq_false_and_eq_false,
    decide_eq_false_iff_not]
  rw [hMarginalMem x, hMarginalMem y, hPairMem,
    hCommonBool]
  simp only [x, y, and_assoc]

theorem exists_fixedLengthPairCode_not_regionBad
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n t : Nat} (hn : 0 < n)
    (hcount :
      muchnikRegionMergedStageCount c n t =
        muchnikRegionAdviceCount V n) :
  ∃ w ∈ fixedLengthPairCodes (2 * n + 2),
    muchnikRegionBadAtStage c n t w = false := by
  obtain ⟨x, y, hsurvivor⟩ :=
    exists_muchnikRegionSurvivor V hn
  refine ⟨pairCode x y, ?_, ?_⟩
  · apply
      (mem_fixedLengthPairCodes_iff
        (2 * n + 2) (pairCode x y)).mpr
    exact
      ⟨x, y, hsurvivor.1, hsurvivor.2.1, rfl⟩
  · apply
      (muchnikRegionBadAtStage_false_iff
        hc hn hcount).mpr
    have hnotBad :
        (x, y) ∉ muchnikRegionBadPairs V n :=
      (not_mem_muchnikRegionBadPairs_iff V n x y).mpr
        hsurvivor.2.2.2.2.2
    simpa only [decodeFirst_pairCode,
      decodeSecond_pairCode] using
      And.intro hsurvivor.2.2.1
        (And.intro hsurvivor.2.2.2.1
          (And.intro hsurvivor.2.2.2.2.1 hnotBad))

theorem muchnikRegionFindAtStage_spec
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n t : Nat} (hn : 0 < n)
    (hcount :
      muchnikRegionMergedStageCount c n t =
        muchnikRegionAdviceCount V n) :
    ∃ w,
      (fixedLengthPairCodes (2 * n + 2)).find?
        (fun u => !muchnikRegionBadAtStage c n t u) = some w ∧
      IsMuchnikRegionSurvivor V n
        (decodeFirst w) (decodeSecond w) := by
  obtain ⟨w₀, hw₀Candidates, hw₀Good⟩ :=
    exists_fixedLengthPairCode_not_regionBad hc hn hcount
  have hw₀Predicate :
      (!muchnikRegionBadAtStage c n t w₀) = true := by
    rw [hw₀Good]
    rfl
  have hFindSome :
      ∃ w,
        (fixedLengthPairCodes (2 * n + 2)).find?
          (fun u => !muchnikRegionBadAtStage c n t u) =
            some w := by
    apply Option.isSome_iff_exists.mp
    rw [List.find?_isSome]
    exact ⟨w₀, hw₀Candidates, hw₀Predicate⟩
  obtain ⟨w, hwFind⟩ := hFindSome
  have hwCandidates :
      w ∈ fixedLengthPairCodes (2 * n + 2) :=
    List.mem_of_find?_eq_some hwFind
  have hwPredicate :
      (!muchnikRegionBadAtStage c n t w) = true :=
    List.find?_some
      (p := fun u => !muchnikRegionBadAtStage c n t u)
      (a := w) (l := fixedLengthPairCodes (2 * n + 2))
      hwFind
  have hwGood :
      muchnikRegionBadAtStage c n t w = false := by
    cases hbad : muchnikRegionBadAtStage c n t w with
    | false => rfl
    | true =>
        have hfalse : false = true := by
          simpa only [hbad, Bool.not_true] using hwPredicate
        exact Bool.noConfusion hfalse
  have hwSemantics :=
    (muchnikRegionBadAtStage_false_iff
      hc hn hcount).mp hwGood
  obtain ⟨x, y, hxLength, hyLength, hwPair⟩ :=
    (mem_fixedLengthPairCodes_iff
      (2 * n + 2) w).mp hwCandidates
  refine ⟨w, hwFind, ?_⟩
  subst w
  simp only [decodeFirst_pairCode,
    decodeSecond_pairCode] at hwSemantics ⊢
  exact
    ⟨hxLength, hyLength, hwSemantics.1,
      hwSemantics.2.1, hwSemantics.2.2.1,
      (not_mem_muchnikRegionBadPairs_iff V n x y).mp
        hwSemantics.2.2.2⟩

end Kolmogorov
