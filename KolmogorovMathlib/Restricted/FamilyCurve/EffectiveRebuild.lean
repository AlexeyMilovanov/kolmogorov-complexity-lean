import KolmogorovMathlib.Restricted.FamilyCurve.Selector

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- One step of effective rebuilding: if the requested cardinality `c` is at most
the predecessor `A`'s cardinality, apply the maximum-intersection selector.
Otherwise, deterministically retain the predecessor `A`. -/
def restrictedEffectiveRebuildStep (𝒜 : DescriptionFamily) :
    BitString →. BitString := fun input =>
  let Acode := restrictedSelectorField input 0
  let A_card := (decodeCoverCodeList Acode).dedup.length
  let c := bitsToNat (restrictedSelectorField input 2)
  if c ≤ A_card then
    restrictedMaxIntersectionCoverSelector 𝒜 input
  else
    Part.some Acode

lemma restrictedEffectiveRebuildStep_partrec (𝒜 : DescriptionFamily) :
    Partrec (restrictedEffectiveRebuildStep 𝒜) := by
  have hfield (i : ℕ) : Computable (fun input : BitString =>
      restrictedSelectorField input i) :=
    restrictedSelectorField_computable.comp Computable.id (Computable.const i)
  have hc : Computable (fun input : BitString =>
      bitsToNat (restrictedSelectorField input 2)) :=
    bitsToNat_computable.comp (hfield 2)
  have hcard : Computable (fun input : BitString =>
      (decodeCoverCodeList (restrictedSelectorField input 0)).dedup.length) :=
    Computable.list_length.comp
      (dedup_primrec.to_comp.comp
        (decodeCoverCodeList_primrec.to_comp.comp (hfield 0)))
  have hguard : Computable (fun input : BitString =>
      decide (bitsToNat (restrictedSelectorField input 2) ≤
        (decodeCoverCodeList (restrictedSelectorField input 0)).dedup.length)) := by
    have hle : Computable₂ (fun a b : ℕ => decide (a ≤ b)) :=
      (PrimrecPred.decide Primrec.nat_le).to_comp
    exact hle.comp hc hcard
  refine (Partrec.cond hguard
    (restrictedMaxIntersectionCoverSelector_partrec 𝒜)
    (hfield 0).partrec).of_eq ?_
  intro input
  unfold restrictedEffectiveRebuildStep
  by_cases h : bitsToNat (restrictedSelectorField input 2) ≤
      (decodeCoverCodeList (restrictedSelectorField input 0)).dedup.length
  · simp [h]
  · simp [h]

lemma restrictedEffectiveRebuildStep_spec (𝒜 : DescriptionFamily)
    (Acode Ccode : BitString) (n c q0 A_bound : ℕ)
    (A C : Finset BitString)
    (hAcode : decodeCoverCodeList Acode = canonicalFinsetList A)
    (hCcode : decodeCoverCodeList Ccode = canonicalFinsetList C)
    (hq0 : q0 = 𝒜.overhead n)
    (hA : 𝒜.mem A) (hC : C ⊆ A) (hC_n : ∀ x ∈ C, x.length = n)
    (hc_pos : 0 < c) (hc_bound : c ≤ A_bound)
    (hAcard : A.card ≤ A_bound) :
    ∃ Bcode B,
      restrictedEffectiveRebuildStep 𝒜
          (restrictedCoverSelectorInput Acode Ccode c q0) = Part.some Bcode ∧
      decodeCoverCodeList Bcode = canonicalFinsetList B ∧
      𝒜.mem B ∧
      B.card ≤ c ∧
      c * C.card ≤ (𝒜.overhead n * A_bound) * (B ∩ C).card := by
  have hAcard_code :
      (decodeCoverCodeList Acode).dedup.length = A.card := by
    rw [hAcode, List.dedup_eq_self.mpr (canonicalFinsetList_nodup A),
      length_canonicalFinsetList]
  by_cases hcA : c ≤ A.card
  · obtain ⟨Bcode, B, hselect, hBcode, hBmem, hBcard, hdensity⟩ :=
      restrictedMaxIntersectionCoverSelector_spec 𝒜 Acode Ccode n c q0
        A C hAcode hCcode hq0 hA hC hC_n hc_pos hcA
    refine ⟨Bcode, B, ?_, hBcode, hBmem, hBcard, ?_⟩
    · unfold restrictedEffectiveRebuildStep
      simp only [restrictedSelectorField_input_zero,
        restrictedSelectorField_input_two, hAcard_code, if_pos hcA]
      exact hselect
    · exact hdensity.trans (Nat.mul_le_mul_right (B ∩ C).card
        (Nat.mul_le_mul_left (𝒜.overhead n) hAcard))
  · refine ⟨Acode, A, ?_, hAcode, hA, Nat.le_of_lt (Nat.lt_of_not_ge hcA), ?_⟩
    · unfold restrictedEffectiveRebuildStep
      simp only [restrictedSelectorField_input_zero,
        restrictedSelectorField_input_two, hAcard_code, if_neg hcA]
    · rw [Finset.inter_eq_right.mpr hC]
      have hover : 1 ≤ 𝒜.overhead n := 𝒜.overhead_pos n
      calc
        c * C.card ≤ A_bound * C.card := Nat.mul_le_mul_right C.card hc_bound
        _ = (1 * A_bound) * C.card := by simp
        _ ≤ (𝒜.overhead n * A_bound) * C.card :=
          Nat.mul_le_mul_right C.card (Nat.mul_le_mul_right A_bound hover)

/-- Canonical code of the live intersection represented by two model codes.
The first decoded list supplies the canonical order; `dedup` makes the operation
well behaved even on malformed inputs. -/
noncomputable def restrictedLiveIntersectionCode
    (Ccode Bcode : BitString) : BitString :=
  canonicalUniformCodeOfList
    ((decodeCoverCodeList Ccode).filter
      (fun x => decide (x ∈ decodeCoverCodeList Bcode))).dedup

theorem restrictedLiveIntersectionCode_primrec :
    Primrec (fun p : BitString × BitString =>
      restrictedLiveIntersectionCode p.1 p.2) := by
  unfold restrictedLiveIntersectionCode
  apply canonicalUniformCodeOfList_primrec.comp
  apply dedup_primrec.comp
  apply list_filter_primrec
  · exact decodeCoverCodeList_primrec.comp Primrec.fst
  · exact bitString_mem_primrec.comp Primrec.snd
      (decodeCoverCodeList_primrec.comp (Primrec.snd.comp Primrec.fst))

lemma decodeCoverCodeList_canonicalUniformCodeOfList (L : List BitString) :
    decodeCoverCodeList (canonicalUniformCodeOfList L) = L := by
  unfold decodeCoverCodeList canonicalUniformCodeOfList
  rw [decodeDistributionData_code]
  rw [List.map_map]
  exact List.map_id'' (fun _ => rfl) L

lemma decode_restrictedLiveIntersectionCode
    (Ccode Bcode : BitString) (C B : Finset BitString)
    (hCcode : decodeCoverCodeList Ccode = canonicalFinsetList C)
    (hBcode : decodeCoverCodeList Bcode = canonicalFinsetList B) :
    decodeCoverCodeList (restrictedLiveIntersectionCode Ccode Bcode) =
      canonicalFinsetList (C ∩ B) := by
  rw [restrictedLiveIntersectionCode,
    decodeCoverCodeList_canonicalUniformCodeOfList, hCcode, hBcode]
  let L := (canonicalFinsetList C).filter
    (fun x => decide (x ∈ canonicalFinsetList B))
  have hnd : L.Nodup := (canonicalFinsetList_nodup C).filter _
  have hpair : L.Pairwise bitStringLE :=
    List.Pairwise.filter _ (Finset.pairwise_sort C bitStringLE)
  have hfin : L.toFinset = C ∩ B := by
    ext x
    simp [L, mem_canonicalFinsetList]
  have hcanon : canonicalFinsetList L.toFinset = L :=
    canonicalFinsetList_of_sorted L hnd hpair
  rw [List.dedup_eq_self.mpr hnd, ← hfin, hcanon]

theorem restrictedSelectorField_primrec :
    Primrec₂ restrictedSelectorField := by
  exact (Primrec.list_getD []).comp
    (decodeListCode_primrec.comp Primrec.fst) Primrec.snd

theorem restrictedCoverSelectorInput_primrec :
    Primrec (fun a : BitString × BitString × ℕ × ℕ =>
      restrictedCoverSelectorInput a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  unfold restrictedCoverSelectorInput
  apply listCode_primrec.comp
  exact Primrec.list_cons.comp Primrec.fst
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp
        (primrecNatBits.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.list_cons.comp
          (primrecNatBits.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.const []))))

/-- Input encoding for a suffix rebuild.  The fields are the predecessor model
code, the current live-pool code, a `listCode` of the requested cardinalities,
and the numerical overhead. -/
def restrictedEffectiveRebuildSuffixInput
    (Acode Ccode : BitString) (sizes : List ℕ) (q0 : ℕ) : BitString :=
  listCode [Acode, Ccode, listCode (sizes.map Nat.bits), Nat.bits q0]

@[simp] lemma restrictedSelectorField_suffixInput_zero
    (Acode Ccode : BitString) (sizes : List ℕ) (q0 : ℕ) :
    restrictedSelectorField
      (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0) 0 = Acode := by
  unfold restrictedSelectorField restrictedEffectiveRebuildSuffixInput
  rw [decodeListCode_listCode]
  rfl

@[simp] lemma restrictedSelectorField_suffixInput_one
    (Acode Ccode : BitString) (sizes : List ℕ) (q0 : ℕ) :
    restrictedSelectorField
      (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0) 1 = Ccode := by
  unfold restrictedSelectorField restrictedEffectiveRebuildSuffixInput
  rw [decodeListCode_listCode]
  rfl

@[simp] lemma restrictedSelectorField_suffixInput_two
    (Acode Ccode : BitString) (sizes : List ℕ) (q0 : ℕ) :
    restrictedSelectorField
      (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0) 2 =
        listCode (sizes.map Nat.bits) := by
  unfold restrictedSelectorField restrictedEffectiveRebuildSuffixInput
  rw [decodeListCode_listCode]
  rfl

@[simp] lemma restrictedSelectorField_suffixInput_three
    (Acode Ccode : BitString) (sizes : List ℕ) (q0 : ℕ) :
    bitsToNat (restrictedSelectorField
      (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0) 3) = q0 := by
  unfold restrictedSelectorField restrictedEffectiveRebuildSuffixInput
  rw [decodeListCode_listCode]
  exact bitsToNat_bits q0

/-- Requested cardinalities decoded from a suffix-rebuild input. -/
def restrictedEffectiveRebuildSizes (input : BitString) : List ℕ :=
  (decodeListCode (restrictedSelectorField input 2)).map bitsToNat

theorem restrictedEffectiveRebuildSizes_primrec :
    Primrec restrictedEffectiveRebuildSizes := by
  unfold restrictedEffectiveRebuildSizes
  exact Primrec.list_map
    (decodeListCode_primrec.comp
      (restrictedSelectorField_primrec.comp Primrec.id (Primrec.const 2)))
    (bitsToNat_primrec.comp Primrec.snd).to₂

@[simp] lemma restrictedEffectiveRebuildSizes_input
    (Acode Ccode : BitString) (sizes : List ℕ) (q0 : ℕ) :
    restrictedEffectiveRebuildSizes
      (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0) = sizes := by
  unfold restrictedEffectiveRebuildSizes restrictedEffectiveRebuildSuffixInput
    restrictedSelectorField
  rw [decodeListCode_listCode]
  simp only [List.getD_cons_succ, List.getD_cons_zero, decodeListCode_listCode,
    List.map_map]
  exact List.map_id'' (fun c => bitsToNat_bits c) sizes

private abbrev RestrictedEffectiveRebuildState :=
  BitString × BitString × List BitString

/-- One indexed transition used by the suffix iterator.  The state stores the
current model code, current live-pool code, and all model codes produced so far. -/
noncomputable def restrictedEffectiveRebuildSuffixNext (𝒜 : DescriptionFamily)
    (input : BitString) (indexed : ℕ × RestrictedEffectiveRebuildState) :
    Part RestrictedEffectiveRebuildState :=
  let idx := indexed.1
  let state := indexed.2
  let c := (restrictedEffectiveRebuildSizes input).getD idx 0
  let q0 := bitsToNat (restrictedSelectorField input 3)
  (restrictedEffectiveRebuildStep 𝒜
      (restrictedCoverSelectorInput state.1 state.2.1 c q0)).map
    (fun Bcode =>
      (Bcode, restrictedLiveIntersectionCode state.2.1 Bcode,
        state.2.2 ++ [Bcode]))

lemma restrictedEffectiveRebuildSuffixNext_partrec (𝒜 : DescriptionFamily) :
    Partrec (fun a : BitString × (ℕ × RestrictedEffectiveRebuildState) =>
      restrictedEffectiveRebuildSuffixNext 𝒜 a.1 a.2) := by
  have hAcode : Computable (fun a : BitString ×
      (ℕ × RestrictedEffectiveRebuildState) => a.2.2.1) := by
    exact Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hCcode : Computable (fun a : BitString ×
      (ℕ × RestrictedEffectiveRebuildState) => a.2.2.2.1) := by
    exact Computable.fst.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hcodes : Computable (fun a : BitString ×
      (ℕ × RestrictedEffectiveRebuildState) => a.2.2.2.2) := by
    exact Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hidx : Computable (fun a : BitString ×
      (ℕ × RestrictedEffectiveRebuildState) => a.2.1) := by
    exact Computable.fst.comp Computable.snd
  have hc : Computable (fun a : BitString ×
      (ℕ × RestrictedEffectiveRebuildState) =>
        (restrictedEffectiveRebuildSizes a.1).getD a.2.1 0) := by
    have hget : Computable₂ (fun l : List ℕ => fun i => l.getD i 0) :=
      (Primrec.list_getD 0).to_comp
    exact (hget.comp
      (restrictedEffectiveRebuildSizes_primrec.to_comp.comp Computable.fst) hidx).of_eq
      fun _ => rfl
  have hq0 : Computable (fun a : BitString ×
      (ℕ × RestrictedEffectiveRebuildState) =>
        bitsToNat (restrictedSelectorField a.1 3)) :=
    (bitsToNat_computable.comp
      (restrictedSelectorField_computable.comp Computable.fst
        ((Computable.const 3) : Computable (fun a : BitString × (ℕ × RestrictedEffectiveRebuildState) => 3)))).of_eq
      fun _ => rfl
  have hselectorInput : Computable (fun a : BitString ×
      (ℕ × RestrictedEffectiveRebuildState) =>
        restrictedCoverSelectorInput a.2.2.1 a.2.2.2.1
          ((restrictedEffectiveRebuildSizes a.1).getD a.2.1 0)
          (bitsToNat (restrictedSelectorField a.1 3))) :=
    (restrictedCoverSelectorInput_primrec.to_comp.comp
      (hAcode.pair (hCcode.pair (hc.pair hq0)))).of_eq fun _ => rfl
  have hcall : Partrec (fun a : BitString ×
      (ℕ × RestrictedEffectiveRebuildState) =>
        restrictedEffectiveRebuildStep 𝒜
          (restrictedCoverSelectorInput a.2.2.1 a.2.2.2.1
            ((restrictedEffectiveRebuildSizes a.1).getD a.2.1 0)
            (bitsToNat (restrictedSelectorField a.1 3)))) :=
    ((restrictedEffectiveRebuildStep_partrec 𝒜).comp hselectorInput).of_eq fun _ => rfl
  have hpost : Computable₂ (fun
      (a : BitString × (ℕ × RestrictedEffectiveRebuildState))
      (Bcode : BitString) =>
        (Bcode, restrictedLiveIntersectionCode a.2.2.2.1 Bcode,
          a.2.2.2.2 ++ [Bcode])) := by
    have hmodelCode : Computable (fun p :
        (BitString × (ℕ × RestrictedEffectiveRebuildState)) × BitString =>
          p.1.2.2.2.1) :=
      Computable.fst.comp
        (Computable.snd.comp (Computable.snd.comp
          (Computable.snd.comp Computable.fst)))
    have hBcode : Computable (fun p :
        (BitString × (ℕ × RestrictedEffectiveRebuildState)) × BitString =>
          p.2) :=
      Computable.snd
    have hcodes : Computable (fun p :
        (BitString × (ℕ × RestrictedEffectiveRebuildState)) × BitString =>
          p.1.2.2.2.2) :=
      Computable.snd.comp
        (Computable.snd.comp (Computable.snd.comp
          (Computable.snd.comp Computable.fst)))
    have hliveCode : Computable (fun p :
        (BitString × (ℕ × RestrictedEffectiveRebuildState)) × BitString =>
        restrictedLiveIntersectionCode p.1.2.2.2.1 p.2) :=
      (restrictedLiveIntersectionCode_primrec.to_comp.comp
        (hmodelCode.pair hBcode)).of_eq fun _ => rfl
    have houtputCodes : Computable (fun p :
        (BitString × (ℕ × RestrictedEffectiveRebuildState)) × BitString =>
        p.1.2.2.2.2 ++ [p.2]) := by
      have happend : Computable₂ (fun l1 l2 : List BitString => l1 ++ l2) :=
        Primrec.list_append.to_comp
      have hcons : Computable₂ (fun (c : BitString) (l : List BitString) =>
          c :: l) := Primrec.list_cons.to_comp
      have hnil : Computable (fun _p :
          (BitString × (ℕ × RestrictedEffectiveRebuildState)) × BitString =>
            ([] : List BitString)) := Computable.const []
      exact (happend.comp hcodes (hcons.comp hBcode hnil)).of_eq fun _ => rfl
    exact Computable₂.mk
      ((Computable.pair hBcode
        (Computable.pair hliveCode houtputCodes)).of_eq fun _ => rfl)
  exact (Partrec.map hcall hpost).of_eq fun _ => rfl

/-- Iterate the effective rebuild step over all cardinalities encoded in the
input and return a `listCode` containing the predecessor followed by every
selected suffix model code. -/
noncomputable def restrictedEffectiveRebuildSuffix (𝒜 : DescriptionFamily) :
    BitString →. BitString := fun input =>
  let sizes := restrictedEffectiveRebuildSizes input
  let Acode := restrictedSelectorField input 0
  let Ccode := restrictedSelectorField input 1
  let initial : Part RestrictedEffectiveRebuildState :=
    Part.some (Acode, Ccode, [Acode])
  let final : Part RestrictedEffectiveRebuildState :=
    Nat.rec (motive := fun _ => Part RestrictedEffectiveRebuildState)
      initial (fun idx state =>
        state.bind (fun value =>
          restrictedEffectiveRebuildSuffixNext 𝒜 input (idx, value)))
      sizes.length
  final.map (fun state => listCode state.2.2)

lemma restrictedEffectiveRebuildSuffix_partrec (𝒜 : DescriptionFamily) :
    Partrec (restrictedEffectiveRebuildSuffix 𝒜) := by
  have hfield (i : ℕ) : Computable (fun input : BitString =>
      restrictedSelectorField input i) :=
    restrictedSelectorField_computable.comp Computable.id (Computable.const i)
  have hcount : Computable (fun input : BitString =>
      (restrictedEffectiveRebuildSizes input).length) :=
    Computable.list_length.comp restrictedEffectiveRebuildSizes_primrec.to_comp
  have hinitial : Partrec (fun input : BitString =>
      Part.some (restrictedSelectorField input 0,
        restrictedSelectorField input 1,
        [restrictedSelectorField input 0])) := by
    have hcomp : Computable (fun input : BitString =>
        (restrictedSelectorField input 0,
          restrictedSelectorField input 1,
          [restrictedSelectorField input 0])) := by
      apply Primrec.to_comp
      exact Primrec.pair
        (restrictedSelectorField_primrec.comp Primrec.id (Primrec.const 0))
        (Primrec.pair
          (restrictedSelectorField_primrec.comp Primrec.id (Primrec.const 1))
          (Primrec.list_cons.comp
            (restrictedSelectorField_primrec.comp Primrec.id (Primrec.const 0))
            (Primrec.const ([] : List BitString))))
    exact hcomp.partrec
  have hnext : Partrec₂ (fun input : BitString =>
      fun indexed : ℕ × RestrictedEffectiveRebuildState =>
        restrictedEffectiveRebuildSuffixNext 𝒜 input indexed) :=
    (restrictedEffectiveRebuildSuffixNext_partrec 𝒜).to₂
  have hfinal : Partrec (fun input : BitString =>
      Nat.rec (motive := fun _ => Part RestrictedEffectiveRebuildState)
        (Part.some (restrictedSelectorField input 0,
          restrictedSelectorField input 1,
          [restrictedSelectorField input 0]))
        (fun idx state => state.bind (fun value =>
          restrictedEffectiveRebuildSuffixNext 𝒜 input (idx, value)))
        (restrictedEffectiveRebuildSizes input).length) :=
    Partrec.nat_rec hcount hinitial hnext
  have hout : Computable₂ (fun (_input : BitString)
      (state : RestrictedEffectiveRebuildState) => listCode state.2.2) := by
    exact (listCode_primrec.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to_comp.to₂
  refine (Partrec.map hfinal hout).of_eq ?_
  intro input
  rfl

/-- Exact chronological code-level trace produced by the suffix iterator. -/
inductive RestrictedEffectiveRebuildCodeTrace (𝒜 : DescriptionFamily)
    (q0 : ℕ) (sizes : List ℕ) (Acode₀ Ccode₀ : BitString) :
    ℕ → BitString → BitString → List BitString → Prop
  | nil : RestrictedEffectiveRebuildCodeTrace 𝒜 q0 sizes Acode₀ Ccode₀
      0 Acode₀ Ccode₀ [Acode₀]
  | cons {idx : ℕ} {Acode Ccode Bcode : BitString}
      {codes : List BitString}
      (hprev : RestrictedEffectiveRebuildCodeTrace 𝒜 q0 sizes Acode₀ Ccode₀
        idx Acode Ccode codes)
      (hstep : restrictedEffectiveRebuildStep 𝒜
        (restrictedCoverSelectorInput Acode Ccode (sizes.getD idx 0) q0) =
          Part.some Bcode) :
      RestrictedEffectiveRebuildCodeTrace 𝒜 q0 sizes Acode₀ Ccode₀
        (idx + 1) Bcode (restrictedLiveIntersectionCode Ccode Bcode)
        (codes ++ [Bcode])

/-- Live-pool codes before each remaining model code is selected. -/
noncomputable def restrictedEffectiveRebuildLiveCodesFrom
    (Ccode : BitString) : List BitString → List BitString
  | [] => [Ccode]
  | Bcode :: codes =>
      Ccode :: restrictedEffectiveRebuildLiveCodesFrom
        (restrictedLiveIntersectionCode Ccode Bcode) codes

/-- Live-pool codes aligned with a model-code trace.  The first model code is
the retained predecessor, so intersections start with the tail. -/
noncomputable def restrictedEffectiveRebuildLiveCodes
    (Ccode : BitString) : List BitString → List BitString
  | [] => []
  | _Acode :: codes => restrictedEffectiveRebuildLiveCodesFrom Ccode codes

lemma restrictedEffectiveRebuildLiveCodesFrom_length
    (Ccode : BitString) (codes : List BitString) :
    (restrictedEffectiveRebuildLiveCodesFrom Ccode codes).length =
      codes.length + 1 := by
  induction codes generalizing Ccode with
  | nil => rfl
  | cons Bcode codes ih =>
      simp [restrictedEffectiveRebuildLiveCodesFrom, ih]

lemma restrictedEffectiveRebuildLiveCodes_length
    (Ccode : BitString) (codes : List BitString) :
    (restrictedEffectiveRebuildLiveCodes Ccode codes).length = codes.length := by
  cases codes with
  | nil => rfl
  | cons Acode codes =>
      simp [restrictedEffectiveRebuildLiveCodes,
        restrictedEffectiveRebuildLiveCodesFrom_length]

lemma restrictedEffectiveRebuildLiveCodesFrom_prefix_append
    (Ccode : BitString) (codes extra : List BitString) :
    restrictedEffectiveRebuildLiveCodesFrom Ccode codes <+:
      restrictedEffectiveRebuildLiveCodesFrom Ccode (codes ++ extra) := by
  induction codes generalizing Ccode with
  | nil =>
      cases extra <;> simp [restrictedEffectiveRebuildLiveCodesFrom]
  | cons Bcode codes ih =>
      simp only [restrictedEffectiveRebuildLiveCodesFrom, List.cons_append]
      obtain ⟨extra', hextra'⟩ := ih
        (restrictedLiveIntersectionCode Ccode Bcode)
      exact ⟨extra', congrArg (List.cons Ccode) hextra'⟩

lemma restrictedEffectiveRebuildLiveCodes_prefix_append
    (Ccode : BitString) (codes extra : List BitString) (hcodes : codes ≠ []) :
    restrictedEffectiveRebuildLiveCodes Ccode codes <+:
      restrictedEffectiveRebuildLiveCodes Ccode (codes ++ extra) := by
  cases codes with
  | nil => exact False.elim (hcodes rfl)
  | cons Acode codes =>
      exact restrictedEffectiveRebuildLiveCodesFrom_prefix_append Ccode codes extra

lemma restrictedEffectiveRebuildLiveCodesFrom_append_getD
    (Ccode Bcode : BitString) (codes : List BitString) :
    (restrictedEffectiveRebuildLiveCodesFrom Ccode (codes ++ [Bcode])).getD
        (codes.length + 1) [] =
      restrictedLiveIntersectionCode
        ((restrictedEffectiveRebuildLiveCodesFrom Ccode codes).getD
          codes.length []) Bcode := by
  induction codes generalizing Ccode with
  | nil => simp [restrictedEffectiveRebuildLiveCodesFrom]
  | cons code codes ih =>
      simpa [restrictedEffectiveRebuildLiveCodesFrom, Nat.add_assoc] using
        ih (restrictedLiveIntersectionCode Ccode code)

lemma restrictedEffectiveRebuildLiveCodes_append_getD
    (Ccode Bcode : BitString) (codes : List BitString) (hcodes : codes ≠ []) :
    (restrictedEffectiveRebuildLiveCodes Ccode (codes ++ [Bcode])).getD
        codes.length [] =
      restrictedLiveIntersectionCode
        ((restrictedEffectiveRebuildLiveCodes Ccode codes).getD
          (codes.length - 1) []) Bcode := by
  cases codes with
  | nil => exact False.elim (hcodes rfl)
  | cons Acode codes =>
      simpa [restrictedEffectiveRebuildLiveCodes] using
        restrictedEffectiveRebuildLiveCodesFrom_append_getD Ccode Bcode codes

/-- A terminating suffix computation returns exactly a code-level trace. -/
lemma restrictedEffectiveRebuildSuffix_eval (𝒜 : DescriptionFamily)
    (Acode Ccode : BitString) (sizes : List ℕ) (q0 : ℕ)
    (output : BitString)
    (houtput : restrictedEffectiveRebuildSuffix 𝒜
      (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0) =
        Part.some output) :
    ∃ Afinal Cfinal : BitString, ∃ codes : List BitString,
      output = listCode codes ∧
      RestrictedEffectiveRebuildCodeTrace 𝒜 q0 sizes Acode Ccode
        sizes.length Afinal Cfinal codes := by
  have run_spec : ∀ m : ℕ, ∀ finalState : RestrictedEffectiveRebuildState,
      Nat.rec (motive := fun _ => Part RestrictedEffectiveRebuildState)
          (Part.some (Acode, Ccode, [Acode]))
          (fun idx state => state.bind (fun value =>
            restrictedEffectiveRebuildSuffixNext 𝒜
              (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0)
              (idx, value))) m = Part.some finalState →
      RestrictedEffectiveRebuildCodeTrace 𝒜 q0 sizes Acode Ccode m
        finalState.1 finalState.2.1 finalState.2.2 := by
    intro m
    induction m with
    | zero =>
        intro finalState hfinal
        have heq : finalState = (Acode, Ccode, [Acode]) := by
          simpa using Part.some_injective hfinal.symm
        subst finalState
        exact RestrictedEffectiveRebuildCodeTrace.nil
    | succ m ih =>
        intro finalState hfinal
        have hmem : finalState ∈
            (Nat.rec (motive := fun _ => Part RestrictedEffectiveRebuildState)
              (Part.some (Acode, Ccode, [Acode]))
              (fun idx state => state.bind (fun value =>
                restrictedEffectiveRebuildSuffixNext 𝒜
                  (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0)
                  (idx, value))) m).bind
              (fun value => restrictedEffectiveRebuildSuffixNext 𝒜
                (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0)
                (m, value)) := by
          exact Part.eq_some_iff.mp hfinal
        obtain ⟨previous, hprevious, hnext⟩ := Part.mem_bind_iff.mp hmem
        have htrace := ih previous (Part.eq_some_iff.mpr hprevious)
        obtain ⟨Bcode, hBcode, hstate⟩ := (Part.mem_map_iff _).mp hnext
        have hstep : restrictedEffectiveRebuildStep 𝒜
            (restrictedCoverSelectorInput previous.1 previous.2.1
              (sizes.getD m 0) q0) = Part.some Bcode := by
          apply Part.eq_some_iff.mpr
          simpa [restrictedEffectiveRebuildSuffixNext] using hBcode
        have hstate_eq : finalState =
            (Bcode, restrictedLiveIntersectionCode previous.2.1 Bcode,
              previous.2.2 ++ [Bcode]) := by
          simpa [restrictedEffectiveRebuildSuffixNext] using hstate.symm
        subst finalState
        exact RestrictedEffectiveRebuildCodeTrace.cons htrace hstep
  unfold restrictedEffectiveRebuildSuffix at houtput
  simp only [restrictedEffectiveRebuildSizes_input,
    restrictedSelectorField_suffixInput_zero,
    restrictedSelectorField_suffixInput_one] at houtput
  have houtmem := Part.eq_some_iff.mp houtput
  obtain ⟨finalState, hfinalState, hvalue⟩ := (Part.mem_map_iff _).mp houtmem
  refine ⟨finalState.1, finalState.2.1, finalState.2.2, ?_, ?_⟩
  · exact hvalue.symm
  · exact run_spec sizes.length finalState (Part.eq_some_iff.mpr hfinalState)

/-- The cardinality bound available before suffix step `idx`. -/
def restrictedEffectiveRebuildBound
    (sizes : List ℕ) (A_bound idx : ℕ) : ℕ :=
  if idx = 0 then A_bound else sizes.getD (idx - 1) 0

/-- Decoded mathematical contract of one indexed suffix step. -/
def RestrictedEffectiveRebuildDecodedStep (𝒜 : DescriptionFamily)
    (n A_bound : ℕ) (sizes : List ℕ) (Ccode : BitString)
    (codes : List BitString) (idx : ℕ) : Prop :=
  ∃ Bprev Cprev Bnext : Finset BitString,
    decodeCoverCodeList (codes.getD idx []) = canonicalFinsetList Bprev ∧
    decodeCoverCodeList
        ((restrictedEffectiveRebuildLiveCodes Ccode codes).getD idx []) =
      canonicalFinsetList Cprev ∧
    decodeCoverCodeList (codes.getD (idx + 1) []) =
      canonicalFinsetList Bnext ∧
    𝒜.mem Bprev ∧
    Bprev.card ≤ restrictedEffectiveRebuildBound sizes A_bound idx ∧
    Cprev ⊆ Bprev ∧
    (∀ x ∈ Cprev, x.length = n) ∧
    𝒜.mem Bnext ∧
    Bnext.card ≤ sizes.getD idx 0 ∧
    sizes.getD idx 0 * Cprev.card ≤
      (𝒜.overhead n *
        restrictedEffectiveRebuildBound sizes A_bound idx) *
        (Bnext ∩ Cprev).card

/-- Mathematical invariant of every valid prefix of a code-level trace. -/
lemma restrictedEffectiveRebuildCodeTrace_prefix_spec (𝒜 : DescriptionFamily)
    (Acode Ccode : BitString) (sizes : List ℕ) (q0 n A_bound : ℕ)
    (A C : Finset BitString)
    (hAcode : decodeCoverCodeList Acode = canonicalFinsetList A)
    (hCcode : decodeCoverCodeList Ccode = canonicalFinsetList C)
    (hq0 : q0 = 𝒜.overhead n)
    (hA : 𝒜.mem A) (hC : C ⊆ A)
    (hC_n : ∀ x ∈ C, x.length = n)
    (hAcard : A.card ≤ A_bound)
    (hsizes_pos : ∀ i < sizes.length, 0 < sizes.getD i 0)
    (hsizes_head : sizes.getD 0 0 ≤ A_bound)
    (hsizes_mono : ∀ i, i + 1 < sizes.length →
      sizes.getD (i + 1) 0 ≤ sizes.getD i 0)
    {count : ℕ} {Afinal Cfinal : BitString} {codes : List BitString}
    (hcount : count ≤ sizes.length)
    (htrace : RestrictedEffectiveRebuildCodeTrace 𝒜 q0 sizes Acode Ccode
      count Afinal Cfinal codes) :
    codes.length = count + 1 ∧
    codes.getD count [] = Afinal ∧
    (restrictedEffectiveRebuildLiveCodes Ccode codes).getD count [] = Cfinal ∧
    (∀ i < count,
      RestrictedEffectiveRebuildDecodedStep 𝒜 n A_bound sizes Ccode codes i) ∧
    ∃ Acur Ccur : Finset BitString,
      decodeCoverCodeList Afinal = canonicalFinsetList Acur ∧
      decodeCoverCodeList Cfinal = canonicalFinsetList Ccur ∧
      𝒜.mem Acur ∧
      Acur.card ≤ restrictedEffectiveRebuildBound sizes A_bound count ∧
      Ccur ⊆ Acur ∧
      (∀ x ∈ Ccur, x.length = n) := by
  induction htrace with
  | nil =>
      refine ⟨rfl, rfl, rfl,
        ?_, A, C, hAcode, hCcode, hA, ?_, hC, hC_n⟩
      · intro i hi
        omega
      · simpa [restrictedEffectiveRebuildBound] using hAcard
  | @cons idx AcurCode CcurCode Bcode codes hprev hstep ih =>
      have hidx_lt : idx < sizes.length := by omega
      have hprev_spec := ih (Nat.le_of_lt hidx_lt)
      rcases hprev_spec with
        ⟨hcodes_len, hAcur_at, hCcur_at, hsteps,
          Acur, Ccur, hAcurcode, hCcurcode, hAcur, hAcurcard,
          hCcur, hCcur_n⟩
      have hc_pos : 0 < sizes.getD idx 0 := hsizes_pos idx hidx_lt
      have hc_bound : sizes.getD idx 0 ≤
          restrictedEffectiveRebuildBound sizes A_bound idx := by
        cases idx with
        | zero => simpa [restrictedEffectiveRebuildBound] using hsizes_head
        | succ idx =>
            simpa [restrictedEffectiveRebuildBound] using
              hsizes_mono idx (by omega)
      obtain ⟨Bcode', Bnext, hselect, hBnextcode, hBnext,
        hBnextcard, hdensity⟩ :=
        restrictedEffectiveRebuildStep_spec 𝒜 AcurCode CcurCode n
          (sizes.getD idx 0) q0
          (restrictedEffectiveRebuildBound sizes A_bound idx)
          Acur Ccur hAcurcode hCcurcode hq0 hAcur hCcur hCcur_n
          hc_pos hc_bound hAcurcard
      have hBcode : Bcode' = Bcode := by
        rw [hstep] at hselect
        exact Part.some_injective hselect.symm
      subst Bcode'
      have hcodes_ne : codes ≠ [] := by
        intro hnil
        rw [hnil] at hcodes_len
        simp at hcodes_len
      have hAcur_append : (codes ++ [Bcode]).getD idx [] = AcurCode := by
        rw [List.getD_append codes [Bcode] [] idx (by omega)]
        exact hAcur_at
      have hBnext_append :
          (codes ++ [Bcode]).getD (idx + 1) [] = Bcode := by
        rw [List.getD_append_right codes [Bcode] [] (idx + 1) (by omega)]
        simp [hcodes_len]
      have hlive_prefix := restrictedEffectiveRebuildLiveCodes_prefix_append
        Ccode codes [Bcode] hcodes_ne
      have hCcur_append :
          (restrictedEffectiveRebuildLiveCodes Ccode (codes ++ [Bcode])).getD
              idx [] = CcurCode := by
        obtain ⟨extra, hextra⟩ := hlive_prefix
        rw [← hextra, List.getD_append _ _ _ _ (by
          rw [restrictedEffectiveRebuildLiveCodes_length, hcodes_len]
          omega)]
        exact hCcur_at
      have hCnext_append :
          (restrictedEffectiveRebuildLiveCodes Ccode (codes ++ [Bcode])).getD
              (idx + 1) [] =
            restrictedLiveIntersectionCode CcurCode Bcode := by
        have hlast := restrictedEffectiveRebuildLiveCodes_append_getD
          Ccode Bcode codes hcodes_ne
        have hprevious :
            (restrictedEffectiveRebuildLiveCodes Ccode codes).getD
                (codes.length - 1) [] = CcurCode := by
          simpa [hcodes_len] using hCcur_at
        rw [hprevious] at hlast
        simpa [hcodes_len] using hlast
      refine ⟨?_, hBnext_append, hCnext_append, ?_, ?_⟩
      · simp [hcodes_len]
      · intro i hi
        by_cases hi_old : i < idx
        · have hcode_i : (codes ++ [Bcode]).getD i [] = codes.getD i [] :=
            List.getD_append codes [Bcode] [] i (by omega)
          have hcode_succ : (codes ++ [Bcode]).getD (i + 1) [] =
              codes.getD (i + 1) [] :=
            List.getD_append codes [Bcode] [] (i + 1) (by omega)
          have hlive_i :
              (restrictedEffectiveRebuildLiveCodes Ccode
                (codes ++ [Bcode])).getD i [] =
              (restrictedEffectiveRebuildLiveCodes Ccode codes).getD i [] := by
            obtain ⟨extra, hextra⟩ := hlive_prefix
            rw [← hextra, List.getD_append _ _ _ _ (by
              rw [restrictedEffectiveRebuildLiveCodes_length, hcodes_len]
              omega)]
          obtain ⟨Bprev, Cprev, Bnext, hprevCode, hprevLive,
            hnextCode, hprevMem, hprevCard, hprevSubset, hprevLength,
            hnextMem, hnextCard, hnextDensity⟩ := hsteps i hi_old
          unfold RestrictedEffectiveRebuildDecodedStep
          refine ⟨Bprev, Cprev, Bnext, ?_, ?_, ?_, hprevMem, hprevCard,
            hprevSubset, hprevLength, hnextMem, hnextCard, hnextDensity⟩
          · rw [hcode_i]
            exact hprevCode
          · rw [hlive_i]
            exact hprevLive
          · rw [hcode_succ]
            exact hnextCode
        · have hi_eq : i = idx := by omega
          subst i
          unfold RestrictedEffectiveRebuildDecodedStep
          refine ⟨Acur, Ccur, Bnext, ?_, ?_, ?_, hAcur, hAcurcard,
            hCcur, hCcur_n, hBnext, hBnextcard, ?_⟩
          · rw [hAcur_append]
            exact hAcurcode
          · rw [hCcur_append]
            exact hCcurcode
          · rw [hBnext_append]
            exact hBnextcode
          · exact hdensity
      · refine ⟨Bnext, Ccur ∩ Bnext, hBnextcode, ?_, hBnext, ?_,
          Finset.inter_subset_right, ?_⟩
        · exact decode_restrictedLiveIntersectionCode CcurCode Bcode
            Ccur Bnext hCcurcode hBnextcode
        · simpa [restrictedEffectiveRebuildBound] using hBnextcard
        · intro x hx
          exact hCcur_n x (Finset.inter_subset_left hx)

/-- Valid decreasing requested sizes make the executable suffix iterator
terminate with a code-level trace. -/
lemma restrictedEffectiveRebuildSuffix_terminates (𝒜 : DescriptionFamily)
    (Acode Ccode : BitString) (sizes : List ℕ) (q0 n A_bound : ℕ)
    (A C : Finset BitString)
    (hAcode : decodeCoverCodeList Acode = canonicalFinsetList A)
    (hCcode : decodeCoverCodeList Ccode = canonicalFinsetList C)
    (hq0 : q0 = 𝒜.overhead n)
    (hA : 𝒜.mem A) (hC : C ⊆ A)
    (hC_n : ∀ x ∈ C, x.length = n)
    (hAcard : A.card ≤ A_bound)
    (hsizes_pos : ∀ i < sizes.length, 0 < sizes.getD i 0)
    (hsizes_head : sizes.getD 0 0 ≤ A_bound)
    (hsizes_mono : ∀ i, i + 1 < sizes.length →
      sizes.getD (i + 1) 0 ≤ sizes.getD i 0) :
    ∃ output Afinal Cfinal codes,
      restrictedEffectiveRebuildSuffix 𝒜
          (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0) =
        Part.some output ∧
      output = listCode codes ∧
      RestrictedEffectiveRebuildCodeTrace 𝒜 q0 sizes Acode Ccode
        sizes.length Afinal Cfinal codes := by
  let input := restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0
  have run_exists : ∀ count : ℕ, count ≤ sizes.length →
      ∃ state : RestrictedEffectiveRebuildState,
        Nat.rec (motive := fun _ => Part RestrictedEffectiveRebuildState)
            (Part.some (Acode, Ccode, [Acode]))
            (fun idx current => current.bind (fun value =>
              restrictedEffectiveRebuildSuffixNext 𝒜 input (idx, value)))
            count = Part.some state ∧
        RestrictedEffectiveRebuildCodeTrace 𝒜 q0 sizes Acode Ccode
          count state.1 state.2.1 state.2.2 := by
    intro count hcount
    induction count with
    | zero =>
        exact ⟨(Acode, Ccode, [Acode]), rfl,
          RestrictedEffectiveRebuildCodeTrace.nil⟩
    | succ count ih =>
        have hcount_le : count ≤ sizes.length := by omega
        obtain ⟨state, hrun, htrace⟩ := ih hcount_le
        have hprefix := restrictedEffectiveRebuildCodeTrace_prefix_spec 𝒜
          Acode Ccode sizes q0 n A_bound A C hAcode hCcode hq0 hA hC
          hC_n hAcard hsizes_pos hsizes_head hsizes_mono hcount_le htrace
        obtain ⟨Acur, Ccur, hAcurcode, hCcurcode, hAcur,
          hAcurcard, hCcur, hCcur_n⟩ := hprefix.2.2.2.2
        have hc_pos : 0 < sizes.getD count 0 :=
          hsizes_pos count (by omega)
        have hc_bound : sizes.getD count 0 ≤
            restrictedEffectiveRebuildBound sizes A_bound count := by
          cases count with
          | zero => simpa [restrictedEffectiveRebuildBound] using hsizes_head
          | succ count =>
              simpa [restrictedEffectiveRebuildBound] using
                hsizes_mono count (by omega)
        obtain ⟨Bcode, B, hstep, _hBcode, _hBmem, _hBcard, _hdensity⟩ :=
          restrictedEffectiveRebuildStep_spec 𝒜 state.1 state.2.1 n
            (sizes.getD count 0) q0
            (restrictedEffectiveRebuildBound sizes A_bound count)
            Acur Ccur hAcurcode hCcurcode hq0 hAcur hCcur hCcur_n
            hc_pos hc_bound hAcurcard
        let nextState : RestrictedEffectiveRebuildState :=
          (Bcode, restrictedLiveIntersectionCode state.2.1 Bcode,
            state.2.2 ++ [Bcode])
        refine ⟨nextState, ?_, ?_⟩
        · simp only [hrun, Part.bind_some]
          unfold restrictedEffectiveRebuildSuffixNext
          simp only [input, restrictedEffectiveRebuildSizes_input,
            restrictedSelectorField_suffixInput_three, hstep, Part.map_some]
          rfl
        · exact RestrictedEffectiveRebuildCodeTrace.cons htrace hstep
  obtain ⟨state, hrun, htrace⟩ := run_exists sizes.length le_rfl
  refine ⟨listCode state.2.2, state.1, state.2.1, state.2.2, ?_, rfl, htrace⟩
  unfold restrictedEffectiveRebuildSuffix
  simp only [restrictedEffectiveRebuildSizes_input,
    restrictedSelectorField_suffixInput_zero,
    restrictedSelectorField_suffixInput_one]
  change (Nat.rec (motive := fun _ => Part RestrictedEffectiveRebuildState)
      (Part.some (Acode, Ccode, [Acode]))
      (fun idx current => current.bind (fun value =>
        restrictedEffectiveRebuildSuffixNext 𝒜 input (idx, value)))
      sizes.length).map (fun current => listCode current.2.2) = _
  rw [hrun]
  rfl

/-- Valid decreasing requested sizes make the effective suffix computation
terminate, and every decoded step has the family-membership, size, and density
properties needed by the extensional sampled-run rebuild. -/
lemma restrictedEffectiveRebuildSuffix_decodes_density (𝒜 : DescriptionFamily)
    (Acode Ccode : BitString) (sizes : List ℕ) (q0 n A_bound : ℕ)
    (A C : Finset BitString)
    (hAcode : decodeCoverCodeList Acode = canonicalFinsetList A)
    (hCcode : decodeCoverCodeList Ccode = canonicalFinsetList C)
    (hq0 : q0 = 𝒜.overhead n)
    (hA : 𝒜.mem A) (hC : C ⊆ A)
    (hC_n : ∀ x ∈ C, x.length = n)
    (hAcard : A.card ≤ A_bound)
    (hsizes_pos : ∀ i < sizes.length, 0 < sizes.getD i 0)
    (hsizes_head : sizes.getD 0 0 ≤ A_bound)
    (hsizes_mono : ∀ i, i + 1 < sizes.length →
      sizes.getD (i + 1) 0 ≤ sizes.getD i 0) :
    ∃ output Afinal Cfinal codes,
      restrictedEffectiveRebuildSuffix 𝒜
          (restrictedEffectiveRebuildSuffixInput Acode Ccode sizes q0) =
        Part.some output ∧
      output = listCode codes ∧
      RestrictedEffectiveRebuildCodeTrace 𝒜 q0 sizes Acode Ccode
        sizes.length Afinal Cfinal codes ∧
      codes.length = sizes.length + 1 ∧
      ∀ i < sizes.length, ∃ Bprev Cprev Bnext : Finset BitString,
        decodeCoverCodeList (codes.getD i []) = canonicalFinsetList Bprev ∧
        decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes Ccode codes).getD i []) =
          canonicalFinsetList Cprev ∧
        decodeCoverCodeList (codes.getD (i + 1) []) =
          canonicalFinsetList Bnext ∧
        𝒜.mem Bprev ∧
        Bprev.card ≤ (if i = 0 then A_bound else sizes.getD (i - 1) 0) ∧
        Cprev ⊆ Bprev ∧
        (∀ x ∈ Cprev, x.length = n) ∧
        𝒜.mem Bnext ∧
        Bnext.card ≤ sizes.getD i 0 ∧
        sizes.getD i 0 * Cprev.card ≤
          (𝒜.overhead n *
            (if i = 0 then A_bound else sizes.getD (i - 1) 0)) *
            (Bnext ∩ Cprev).card := by
  obtain ⟨output, Afinal, Cfinal, codes, hrun, houtput, htrace⟩ :=
    restrictedEffectiveRebuildSuffix_terminates 𝒜 Acode Ccode sizes
      q0 n A_bound A C hAcode hCcode hq0 hA hC hC_n hAcard
      hsizes_pos hsizes_head hsizes_mono
  have hspec := restrictedEffectiveRebuildCodeTrace_prefix_spec 𝒜
    Acode Ccode sizes q0 n A_bound A C hAcode hCcode hq0 hA hC hC_n
    hAcard hsizes_pos hsizes_head hsizes_mono
    (count := sizes.length) (Afinal := Afinal) (Cfinal := Cfinal)
    (codes := codes) le_rfl htrace
  refine ⟨output, Afinal, Cfinal, codes, hrun, houtput, htrace, hspec.1, ?_⟩
  intro i hi
  have hstep := hspec.2.2.2.1 i hi
  simpa [RestrictedEffectiveRebuildDecodedStep,
    restrictedEffectiveRebuildBound] using hstep

end Kolmogorov
