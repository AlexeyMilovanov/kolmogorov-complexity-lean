import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.CommonInformation.IncidenceCoding
import KolmogorovMathlib.CommonInformation.IncidenceProfile
import KolmogorovMathlib.CommonInformation.IncidenceWitnessRectangles
import KolmogorovMathlib.CommonInformation.Interfaces
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Nodup

namespace Kolmogorov

open Nat.Partrec (Code)

noncomputable def incidentCommonWitnessPairCodesLe
    (V : Map) (n α β γ : Nat) : Finset BitString :=
  (incidentCommonWitnessPairsLe V n α β γ).image fun p => pairCode p.1 p.2

def incidentCommonWitnessPairsStage
    (c : Code) (n α β γ : Nat) (stage : Nat) : List BitString :=
  (commonWitnessPairsStage c α β γ stage).filter
    (· ∈ concreteIncidentPairCodes n)

lemma incidentCommonWitnessPairsStage_nodup (c : Code) (n α β γ stage : Nat) :
    (incidentCommonWitnessPairsStage c n α β γ stage).Nodup := by
  apply List.Nodup.filter
  exact commonWitnessPairsStage_nodup c α β γ stage

lemma incidentCommonWitnessPairsStage_prefix (c : Code) (n α β γ stage : Nat) :
    incidentCommonWitnessPairsStage c n α β γ stage <+:
      incidentCommonWitnessPairsStage c n α β γ (stage + 1) := by
  apply List.IsPrefix.filter
  exact commonWitnessPairsStage_prefix c α β γ stage

private lemma incidentBitStringMemDecide_primrec :
    Primrec₂ (fun (w : BitString) (l : List BitString) => decide (w ∈ l)) := by
  have key : ∀ (w : BitString) (l : List BitString),
      decide (w ∈ l) =
        l.foldr (fun x acc => if x = w then true else acc) false := by
    intro w l
    induction l with
    | nil => simp
    | cons x t ih =>
        simp only [List.mem_cons, List.foldr_cons, ← ih]
        by_cases h : x = w
        · simp only [h, true_or, decide_true, ↓reduceIte]
        · simp only [Bool.decide_or, h, ↓reduceIte, eq_comm,
            Bool.eq_or_self, true_eq_decide_iff]
          exact fun heq => absurd heq.symm h
  have hcond : PrimrecPred
      (fun a : (BitString × List BitString) × (BitString × Bool) =>
        a.2.1 = a.1.1) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have hstep : Primrec₂
      (fun (p : BitString × List BitString) (q : BitString × Bool) =>
        if q.1 = p.1 then true else q.2) :=
    Primrec.ite hcond (Primrec.const true) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.snd (Primrec.const false) hstep).of_eq
    (fun p => (key p.1 p.2).symm)

private lemma incidentListFilter_computable :
    Computable₂
      (fun (l allowed : List BitString) => l.filter (· ∈ allowed)) := by
  have hmem : PrimrecRel
      (fun (w : BitString) (l : List BitString) => w ∈ l) := by
    refine ⟨inferInstance, ?_⟩
    exact incidentBitStringMemDecide_primrec
  exact (PrimrecRel.listFilter hmem).to_comp

private def incidentCommonWitnessStageInput
    (q : (Nat × Nat × Nat × Nat) × Nat) :
    (Nat × Nat × Nat) × Nat :=
  ((q.1.2.1, q.1.2.2.1, q.1.2.2.2), q.2)

private lemma incidentCommonWitnessStageInput_computable :
    Computable incidentCommonWitnessStageInput := by
  have hα : Primrec
      (fun q : (Nat × Nat × Nat × Nat) × Nat => q.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hβ : Primrec
      (fun q : (Nat × Nat × Nat × Nat) × Nat => q.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hγ : Primrec
      (fun q : (Nat × Nat × Nat × Nat) × Nat => q.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact ((Primrec.pair (Primrec.pair hα (Primrec.pair hβ hγ))
    Primrec.snd).of_eq (fun _ => rfl)).to_comp

lemma incidentCommonWitnessPairsStage_computable (c : Code) :
    Computable (fun q : (Nat × Nat × Nat × Nat) × Nat =>
      incidentCommonWitnessPairsStage c q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) := by
  have hCommon :=
    (commonWitnessPairsStage_computable c).comp
      incidentCommonWitnessStageInput_computable
  have hAllowed : Computable
      (fun q : (Nat × Nat × Nat × Nat) × Nat =>
        concreteIncidentPairCodes q.1.1) :=
    concreteIncidentPairCodes_primrec.to_comp.comp
      (Computable.fst.comp Computable.fst)
  exact (incidentListFilter_computable.comp hCommon hAllowed).of_eq
    (fun _ => rfl)

lemma mem_incidentCommonWitnessPairsStage_eventually_iff
    {V : Map} {c : Code} (hc : IsCodeFor c V) (n α β γ : Nat) (w : BitString) :
    (∃ stage, w ∈ incidentCommonWitnessPairsStage c n α β γ stage) ↔
      w ∈ incidentCommonWitnessPairCodesLe V n α β γ := by
  constructor
  · rintro ⟨stage, hw⟩
    have hwCommon : w ∈ commonWitnessPairsStage c α β γ stage :=
      (List.mem_filter.mp hw).1
    have hwInc : w ∈ concreteIncidentPairCodes n :=
      of_decide_eq_true (List.mem_filter.mp hw).2
    obtain ⟨x, y, z, rfl, hz, hx, hy⟩ :=
      mem_commonWitnessPairsStage_sound hc hwCommon
    rw [incidentCommonWitnessPairCodesLe, Finset.mem_image]
    refine ⟨(x, y), ?_, rfl⟩
    rw [incidentCommonWitnessPairsLe, Finset.mem_filter]
    exact ⟨(mem_commonWitnessPairsLe_iff V α β γ x y).mpr
      ⟨z, hz, hx, hy⟩, hwInc⟩
  · rw [incidentCommonWitnessPairCodesLe, Finset.mem_image]
    rintro ⟨⟨x, y⟩, hp, rfl⟩
    rw [incidentCommonWitnessPairsLe, Finset.mem_filter] at hp
    obtain ⟨z, hz, hx, hy⟩ :=
      (mem_commonWitnessPairsLe_iff V α β γ x y).mp hp.1
    obtain ⟨stage, hstage⟩ :=
      (mem_commonWitnessPairsStage_eventually_iff hc α β γ x y).mpr
        ⟨z, hz, hx, hy⟩
    exact ⟨stage, List.mem_filter.mpr
      ⟨hstage, decide_eq_true hp.2⟩⟩

lemma incidentCommonWitnessPairsStage_length_le
    {V : Map} {c : Code} (hc : IsCodeFor c V) (n α β γ stage : Nat) :
    (incidentCommonWitnessPairsStage c n α β γ stage).length ≤
      (incidentCommonWitnessPairsLe V n α β γ).card := by
  let l := incidentCommonWitnessPairsStage c n α β γ stage
  have hsub : l.toFinset ⊆
      incidentCommonWitnessPairCodesLe V n α β γ := by
    intro w hw
    apply (mem_incidentCommonWitnessPairsStage_eventually_iff
      hc n α β γ w).mp
    exact ⟨stage, by simpa [l] using hw⟩
  calc
    l.length = l.toFinset.card :=
      (List.toFinset_card_of_nodup
        (incidentCommonWitnessPairsStage_nodup
          c n α β γ stage)).symm
    _ ≤ (incidentCommonWitnessPairCodesLe V n α β γ).card :=
      Finset.card_le_card hsub
    _ ≤ (incidentCommonWitnessPairsLe V n α β γ).card :=
      Finset.card_image_le

def incidentCommonWitnessRankInput (n α β γ : Nat) (rank : BitString) : BitString :=
  pairCode (listCode [Nat.bits n, Nat.bits α, Nat.bits β, Nat.bits γ]) rank

lemma incidentCommonWitnessRankInput_length (n α β γ : Nat) (rank : BitString) :
    (incidentCommonWitnessRankInput n α β γ rank).length =
      rank.length + 4 * ((Nat.bits n).length + (Nat.bits α).length +
                         (Nat.bits β).length + (Nat.bits γ).length) + 9 := by
  simp [incidentCommonWitnessRankInput, length_pairCode]
  omega

private def incidentCommonWitnessRankParameters
    (input : BitString) : Nat × Nat × Nat × Nat :=
  let pList := decodeListCode (decodeFirst input)
  (bitsToNat (pList.getD 0 []),
    bitsToNat (pList.getD 1 []),
    bitsToNat (pList.getD 2 []),
    bitsToNat (pList.getD 3 []))

private lemma incidentCommonWitnessRankParameters_primrec :
    Primrec incidentCommonWitnessRankParameters := by
  have hpList : Primrec (fun input : BitString =>
      decodeListCode (decodeFirst input)) :=
    decodeListCode_primrec.comp decodeFirst_primrec'
  have hget (i : Nat) : Primrec (fun input : BitString =>
      (decodeListCode (decodeFirst input)).getD i []) :=
    (Primrec.list_getD ([] : BitString)).comp hpList (Primrec.const i)
  have hn (i : Nat) : Primrec (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD i [])) :=
    bitsToNat_primrec.comp (hget i)
  exact (Primrec.pair (hn 0)
    (Primrec.pair (hn 1) (Primrec.pair (hn 2) (hn 3)))).of_eq
      (fun _ => rfl)

private def incidentCommonWitnessRankValue (input : BitString) : Nat :=
  decodeFixedWidthNatCode (decodeSecond input)

private lemma incidentCommonWitnessRankValue_primrec :
    Primrec incidentCommonWitnessRankValue :=
  (decodeFixedWidthNatCode_primrec.comp decodeSecond_primrec').of_eq
    (fun _ => rfl)

private def incidentCommonWitnessSelectorStageInput
    (q : BitString × Nat) : (Nat × Nat × Nat × Nat) × Nat :=
  (incidentCommonWitnessRankParameters q.1, q.2)

private lemma incidentCommonWitnessSelectorStageInput_computable :
    Computable incidentCommonWitnessSelectorStageInput :=
  ((incidentCommonWitnessRankParameters_primrec.comp Primrec.fst).pair
    Primrec.snd).to_comp

private def incidentCommonWitnessSelectorStage
    (c : Code) (q : BitString × Nat) : List BitString :=
  let params := incidentCommonWitnessRankParameters q.1
  incidentCommonWitnessPairsStage c
    params.1 params.2.1 params.2.2.1 params.2.2.2 q.2

private lemma incidentCommonWitnessSelectorStage_computable (c : Code) :
    Computable (incidentCommonWitnessSelectorStage c) :=
  ((incidentCommonWitnessPairsStage_computable c).comp
    incidentCommonWitnessSelectorStageInput_computable).of_eq
      (fun _ => rfl)

private def incidentCommonWitnessSelectorCheck
    (c : Code) (input : BitString) (t : Nat) : Bool :=
  decide (incidentCommonWitnessRankValue input <
    (incidentCommonWitnessSelectorStage c (input, t)).length)

private lemma incidentCommonWitnessSelectorStageLength_computable (c : Code) :
    Computable (fun q : BitString × Nat =>
      (incidentCommonWitnessSelectorStage c q).length) :=
  Computable.list_length.comp
    (incidentCommonWitnessSelectorStage_computable c)

private lemma incidentCommonWitnessRankValueOnPair_computable :
    Computable (fun q : BitString × Nat =>
      incidentCommonWitnessRankValue q.1) :=
  incidentCommonWitnessRankValue_primrec.to_comp.comp Computable.fst

private lemma incidentNatLtDecide_computable :
    Computable₂ (fun a b : Nat => decide (a < b)) :=
  (PrimrecPred.decide Primrec.nat_lt).to_comp

private lemma incidentCommonWitnessSelectorCheck_computable (c : Code) :
    Computable₂ (incidentCommonWitnessSelectorCheck c) := by
  exact ((incidentNatLtDecide_computable.comp
    incidentCommonWitnessRankValueOnPair_computable
    (incidentCommonWitnessSelectorStageLength_computable c)).of_eq
      (fun _ => rfl)).to₂

private def incidentCommonWitnessSelectorPost
    (c : Code) (input : BitString) (stage : Nat) : BitString :=
  (incidentCommonWitnessSelectorStage c (input, stage)).getD
    (incidentCommonWitnessRankValue input) []

private lemma incidentCommonWitnessSelectorPost_computable (c : Code) :
    Computable₂ (incidentCommonWitnessSelectorPost c) := by
  exact (((Primrec.list_getD ([] : BitString)).to_comp.comp
    (incidentCommonWitnessSelectorStage_computable c)
    incidentCommonWitnessRankValueOnPair_computable).of_eq
      (fun _ => rfl)).to₂

def incidentCommonWitnessRankSelector (c : Code) : BitString →. BitString := fun input =>
  Nat.rfind (fun t =>
    Part.some (incidentCommonWitnessSelectorCheck c input t)) >>= fun stage =>
  Part.some (incidentCommonWitnessSelectorPost c input stage)

lemma incidentCommonWitnessRankSelector_partrec (c : Code) :
    Partrec (incidentCommonWitnessRankSelector c) := by
  exact (Partrec.bind
    (Partrec.rfind
      (incidentCommonWitnessSelectorCheck_computable c).partrec₂)
    (incidentCommonWitnessSelectorPost_computable c).partrec₂).of_eq
      (fun _ => rfl)

private lemma incidentCommonWitnessPairsStage_prefix_of_le
    (c : Code) (n α β γ : Nat) {t₁ t₂ : Nat} (h : t₁ ≤ t₂) :
    incidentCommonWitnessPairsStage c n α β γ t₁ <+:
      incidentCommonWitnessPairsStage c n α β γ t₂ := by
  induction h with
  | refl => exact List.prefix_refl _
  | step ht ih =>
      exact List.IsPrefix.trans ih
        (incidentCommonWitnessPairsStage_prefix c n α β γ _)

lemma incidentCommonWitnessRankSelector_recovers
    (c : Code) (n α β γ s rank : Nat) (stage : Nat) :
    rank < (incidentCommonWitnessPairsStage c n α β γ stage).length →
    rank < 2 ^ s →
    (incidentCommonWitnessPairsStage c n α β γ stage).getD rank [] ∈
      incidentCommonWitnessRankSelector c
        (incidentCommonWitnessRankInput n α β γ (fixedWidthNatCode rank s)) := by
  intro hrank _hrankWidth
  simp only [incidentCommonWitnessRankSelector,
    incidentCommonWitnessRankInput, incidentCommonWitnessSelectorCheck,
    incidentCommonWitnessSelectorPost, incidentCommonWitnessSelectorStage,
    incidentCommonWitnessRankParameters, incidentCommonWitnessRankValue,
    decodeFirst_pairCode, decodeListCode_listCode, List.getD_cons_zero,
    List.getD_cons_succ, bitsToNat_bits, decodeSecond_pairCode,
    decodeFixedWidthNatCode_encode, Part.bind_eq_bind]
  rw [Part.mem_bind_iff]
  let hex : ∃ t,
      rank < (incidentCommonWitnessPairsStage c n α β γ t).length :=
    ⟨stage, hrank⟩
  let t₀ := Nat.find hex
  refine ⟨t₀, ?_, ?_⟩
  · refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · simpa using Nat.find_spec hex
    · intro m hm
      have hnot := Nat.find_min hex hm
      simp [hnot]
  · have ht₀ : rank <
        (incidentCommonWitnessPairsStage c n α β γ t₀).length :=
      Nat.find_spec hex
    have ht₀le : t₀ ≤ stage :=
      Nat.find_le (p := fun t =>
        rank < (incidentCommonWitnessPairsStage c n α β γ t).length)
        hrank
    have hprefix : incidentCommonWitnessPairsStage c n α β γ t₀ <+:
        incidentCommonWitnessPairsStage c n α β γ stage :=
      incidentCommonWitnessPairsStage_prefix_of_le c n α β γ ht₀le
    have hget := StagedEnumeration.getD_eq_of_prefix
      (incidentCommonWitnessPairsStage c n α β γ t₀)
      (incidentCommonWitnessPairsStage c n α β γ stage)
      hprefix rank [] ht₀
    exact Part.mem_some_iff.mpr hget

lemma mem_incidentCommonWitnessPairsLe_of_mem_region
    {V : Map} {n α β γ : Nat} {x y : BitString} :
    0 < α → 0 < β → 0 < γ →
    concreteIncidentCodeRel n x y →
    (α, β, γ) ∈ CommonInformationRegion V x y →
    (x, y) ∈ incidentCommonWitnessPairsLe V n (α - 1) (β - 1) (γ - 1) := by
  rintro hα hβ hγ hinc ⟨z, hz, hx, hy⟩
  rw [incidentCommonWitnessPairsLe, Finset.mem_filter]
  refine ⟨(mem_commonWitnessPairsLe_iff V _ _ _ x y).mpr
    ⟨z, ?_, ?_, ?_⟩, hinc⟩
  · exact (enat_lt_coe_iff_le_pred hα).mp hz
  · exact (enat_lt_coe_iff_le_pred hβ).mp hx
  · exact (enat_lt_coe_iff_le_pred hγ).mp hy

lemma logSlack_sum_lt_eighth_eventually (c₁ c₂ : Nat) :
    ∃ N, ∀ n, N ≤ n → logSlack c₁ n + logSlack c₂ n < n / 8 := by
  obtain ⟨M, hM⟩ :=
    exists_bits_linear_domination 16 (c₁ + c₂) (c₁ + c₂)
  refine ⟨max M 8, ?_⟩
  intro n hn
  have hMn : M ≤ n := le_trans (Nat.le_max_left _ _) hn
  have h8n : 8 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hdom := hM n hMn
  unfold logSlack
  have hsum :
      c₁ * (Nat.bits n).length + c₁ +
          (c₂ * (Nat.bits n).length + c₂) =
        (c₁ + c₂) * (Nat.bits n).length + (c₁ + c₂) := by
    ring
  rw [hsum]
  omega

lemma pairPlainK_incidentCommonWitness_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C, ∀ n α β γ s x y,
      (x, y) ∈ incidentCommonWitnessPairsLe V n α β γ →
      (incidentCommonWitnessPairsLe V n α β γ).card < 2 ^ s →
      pairPlainK V x y ≤
        ((s + 4 * ((Nat.bits n).length + (Nat.bits α).length +
                   (Nat.bits β).length + (Nat.bits γ).length) + 9 + C : Nat) : ENat) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cSelector, hSelector⟩ :=
    plainK_partrec_map_le V hV (incidentCommonWitnessRankSelector code)
      (incidentCommonWitnessRankSelector_partrec code)
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
  refine ⟨cLength + cSelector, ?_⟩
  intro n α β γ s x y hmem hcard
  have hpairCode : pairCode x y ∈
      incidentCommonWitnessPairCodesLe V n α β γ := by
    rw [incidentCommonWitnessPairCodesLe, Finset.mem_image]
    exact ⟨(x, y), hmem, rfl⟩
  obtain ⟨stage, hstage⟩ :=
    (mem_incidentCommonWitnessPairsStage_eventually_iff
      hcode n α β γ (pairCode x y)).mpr hpairCode
  let l := incidentCommonWitnessPairsStage code n α β γ stage
  let rank := l.idxOf (pairCode x y)
  have hrank : rank < l.length :=
    List.idxOf_lt_length_of_mem hstage
  have hstageLength : l.length ≤
      (incidentCommonWitnessPairsLe V n α β γ).card := by
    simpa [l] using
      incidentCommonWitnessPairsStage_length_le hcode n α β γ stage
  have hrankPow : rank < 2 ^ s := by omega
  have hget : l.getD rank [] = pairCode x y := by
    rw [List.getD_eq_getElem l [] hrank]
    exact List.idxOf_get hrank
  have hselected : pairCode x y ∈
      incidentCommonWitnessRankSelector code
        (incidentCommonWitnessRankInput n α β γ
          (fixedWidthNatCode rank s)) := by
    rw [← hget]
    exact incidentCommonWitnessRankSelector_recovers
      code n α β γ s rank stage hrank hrankPow
  let input := incidentCommonWitnessRankInput n α β γ
    (fixedWidthNatCode rank s)
  have hInputLength : input.length =
      s + 4 * ((Nat.bits n).length + (Nat.bits α).length +
        (Nat.bits β).length + (Nat.bits γ).length) + 9 := by
    dsimp only [input]
    rw [incidentCommonWitnessRankInput_length,
      fixedWidthNatCode_length hrankPow]
  calc
    pairPlainK V x y = plainK V (pairCode x y) := rfl
    _ ≤ plainK V input + (cSelector : ENat) :=
      hSelector input (pairCode x y) hselected
    _ ≤ (input.length : ENat) + (cLength : ENat) +
        (cSelector : ENat) := by
      gcongr
      exact hLength input
    _ = ((s + 4 * ((Nat.bits n).length + (Nat.bits α).length +
          (Nat.bits β).length + (Nat.bits γ).length) + 9 +
          (cLength + cSelector) : Nat) : ENat) := by
      rw [hInputLength]
      push_cast
      ac_rfl

lemma pairPlainK_incidentCommonWitness_source_bounds
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C, ∀ n α β γ x y,
      (x, y) ∈ incidentCommonWitnessPairsLe V n α β γ →
      pairPlainK V x y ≤
          ((α + γ / 2 + max (γ / 2) β +
            4 * ((Nat.bits n).length + (Nat.bits α).length +
                 (Nat.bits β).length + (Nat.bits γ).length) + C : Nat) : ENat) ∧
      pairPlainK V x y ≤
          ((α + β / 2 + max (β / 2) γ +
            4 * ((Nat.bits n).length + (Nat.bits α).length +
                 (Nat.bits β).length + (Nat.bits γ).length) + C : Nat) : ENat) := by
  obtain ⟨C, hC⟩ := pairPlainK_incidentCommonWitness_le V hV
  refine ⟨15 + C, ?_⟩
  intro n α β γ x y hmem
  constructor
  · have h := hC n α β γ
      (α + γ / 2 + max (γ / 2) β + 6) x y hmem
      card_incidentCommonWitnessPairsLe_lt_source_bound1
    convert h using 1
    norm_cast
    omega
  · have h := hC n α β γ
      (α + β / 2 + max (β / 2) γ + 6) x y hmem
      card_incidentCommonWitnessPairsLe_lt_source_bound2
    convert h using 1
    norm_cast
    omega

lemma exercise_310_every_highComplexity_incident_edge
    (V : Map) (hV : isOptimalConditional V) (d : Nat) :
    ∃ C N, ∀ n, N ≤ n →
      ∀ (e : ConcreteIncidentEdge n) (kxy : Nat),
        HasPlainComplexityValue V
          (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2)) kxy →
        3 * n ≤ kxy + logSlack d n →
        ∃ kx ky,
          HasPlainComplexityValue V (concretePointCode n e.1.1) kx ∧
          HasPlainComplexityValue V (concreteLineCode n e.1.2) ky ∧
          NatCloseWithin kx (2 * n) (logSlack C n) ∧
          NatCloseWithin ky (2 * n) (logSlack C n) ∧
          NatCloseWithin kxy (3 * n) (logSlack C n) ∧
          MutualInformationWithin V
            (concretePointCode n e.1.1) (concreteLineCode n e.1.2) n (logSlack C n) ∧
          (muchnikThreshold n, muchnikThreshold n, muchnikThreshold n) ∉
            CommonInformationRegion V
              (concretePointCode n e.1.1) (concreteLineCode n e.1.2) := by
  obtain ⟨Cprofile, hprofile⟩ :=
    exercise_309_incident_edge_profile V hV d
  obtain ⟨Ccoding, hcoding⟩ :=
    pairPlainK_incidentCommonWitness_le V hV
  let CoverC := 30 + Ccoding
  obtain ⟨Ndom, hdom⟩ :=
    logSlack_sum_lt_eighth_eventually CoverC d
  refine ⟨Cprofile, max Ndom 64, ?_⟩
  intro n hn e kxy hkxy hhigh
  obtain ⟨kx, ky, hkx, hky, hkxClose, hkyClose,
      hkxyClose, hmi⟩ := hprofile n e kxy hkxy hhigh
  refine ⟨kx, ky, hkx, hky, hkxClose, hkyClose,
    hkxyClose, hmi, ?_⟩
  intro hregion
  let x := concretePointCode n e.1.1
  let y := concreteLineCode n e.1.2
  let t := muchnikThreshold n - 1
  let s := 3 * n - n / 8
  let overhead := 4 * ((Nat.bits n).length + (Nat.bits t).length +
    (Nat.bits t).length + (Nat.bits t).length) + 9 + Ccoding
  have h64 : 64 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hNdom : Ndom ≤ n := le_trans (Nat.le_max_left _ _) hn
  have htPos : 0 < muchnikThreshold n :=
    (muchnik_lt_threshold_iff 0 n).mpr (by omega)
  have hinc : concreteIncidentCodeRel n x y :=
    concreteIncidentCodeRel_iff_exists_edge.mpr ⟨e, rfl, rfl⟩
  have hmem : (x, y) ∈ incidentCommonWitnessPairsLe V n t t t := by
    exact mem_incidentCommonWitnessPairsLe_of_mem_region
      htPos htPos htPos hinc hregion
  have hcard :
      (incidentCommonWitnessPairsLe V n t t t).card < 2 ^ s := by
    exact muchnikThreshold_incidentCommonWitness_card_lt_gap
      (V := V) h64
  have hPairUpper := hcoding n t t t s x y hmem hcard
  have hPairUpper' :
      pairPlainK V x y ≤ ((s + overhead : Nat) : ENat) := by
    calc
      pairPlainK V x y ≤
          ((s + 4 * ((Nat.bits n).length + (Nat.bits t).length +
            (Nat.bits t).length + (Nat.bits t).length) + 9 +
            Ccoding : Nat) : ENat) := hPairUpper
      _ = ((s + overhead : Nat) : ENat) := by
        dsimp only [overhead]
        push_cast
        ac_rfl
  have hkxyExact : HasPlainComplexityValue V (pairCode x y) kxy := by
    simpa only [x, y] using hkxy
  have hPairUpperNat : kxy ≤ s + overhead := by
    change plainK V (pairCode x y) ≤
      ((s + overhead : Nat) : ENat) at hPairUpper'
    rw [hkxyExact] at hPairUpper'
    exact_mod_cast hPairUpper'
  have htLe : t ≤ 2 * n := by
    dsimp only [t]
    unfold muchnikThreshold
    omega
  have hbitsT :
      (Nat.bits t).length ≤ 2 * (Nat.bits n).length + 1 := by
    calc
      (Nat.bits t).length ≤ (Nat.bits (2 * n)).length :=
        length_natBits_mono htLe
      _ ≤ 2 * (Nat.bits n).length + 1 := by
        simpa [two_mul] using length_natBits_add_le n n
  have hBits : 0 < (Nat.bits n).length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_pos.mpr (by omega)
  have hOver : overhead ≤ logSlack CoverC n := by
    dsimp only [overhead, CoverC]
    unfold logSlack
    nlinarith
  have hBudget : overhead + logSlack d n < n / 8 :=
    (Nat.add_le_add_right hOver _).trans_lt (hdom n hNdom)
  dsimp only [s] at hPairUpperNat
  omega

/-- The incidence construction supplies explicit Muchnik counterexamples with
the Exercise 309 profile.  This is the incidence alternative to Theorem 223,
not a second declaration of that theorem. -/
lemma exists_incidence_muchnik_counterexample
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C N, ∀ n, N ≤ n →
      ∃ (e : ConcreteIncidentEdge n) (kx ky kxy : Nat),
        let x := concretePointCode n e.1.1
        let y := concreteLineCode n e.1.2
        x.length = 2 * (n + 1) ∧
        y.length = 2 * (n + 1) ∧
        HasPlainComplexityValue V (pairCode x y) kxy ∧
        HasPlainComplexityValue V x kx ∧
        HasPlainComplexityValue V y ky ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        MutualInformationWithin V x y n (logSlack C n) ∧
        (muchnikThreshold n, muchnikThreshold n, muchnikThreshold n) ∉
          CommonInformationRegion V x y := by
  obtain ⟨C, N, hExercise⟩ :=
    exercise_310_every_highComplexity_incident_edge V hV 0
  refine ⟨C, max N 1, ?_⟩
  intro n hn
  have hN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnPos : 0 < n := by
    have : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
    omega
  obtain ⟨e, kxy, hkxy, hhigh⟩ :=
    exists_highComplexity_concreteIncidentEdge V hV hnPos
  have hhighZero : 3 * n ≤ kxy + logSlack 0 n := by
    simpa [logSlack] using hhigh
  obtain ⟨kx, ky, hkx, hky, hkxClose, hkyClose,
      hkxyClose, hmi, hregion⟩ :=
    hExercise n hN e kxy hkxy hhighZero
  refine ⟨e, kx, ky, kxy, ?_, ?_, hkxy, hkx, hky,
    hkxyClose, hkxClose, hkyClose, hmi, hregion⟩
  · exact concretePointCode_length n e.1.1
  · exact concreteLineCode_length n e.1.2

end Kolmogorov
