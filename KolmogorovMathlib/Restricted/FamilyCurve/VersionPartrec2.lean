import KolmogorovMathlib.Restricted.FamilyCurve.VersionPartrec

/-!
# M7: version decoder computability, part 2

The remaining `Computable`/`Partrec` layers of the version decoder: the
chronological bad-code stream, the effective one-step update, event-prefix
execution, the decoder trace, change counting, and the decoder itself.

Two ingredients keep elaboration polynomial throughout: `Primcodable`
instances and every composed definition are held `[local irreducible]`
inside the section, so definitional checks match by name; and each
irreducible definition first gets a value-shape equation (proved by `rfl`
while still reducible) that the combinator proofs invoke via `of_eq`.
Parameters travel packed — numeric tuples in one `Nat.pair` tower, string
tuples in one `listCode` bundle — so no large `Primcodable` product
instances arise.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open CodedFiniteDistribution

/-! Value-shape equations (definitions still reducible). -/

private lemma DFB_shape (q0 : ℕ) (sizes : List ℕ) (state bad : BitString)
    (s : ℕ) :
    restrictedEffectiveDensityFailsBool q0 ((sizes, state, bad), s) =
      decide ((2 * q0 * sizes.getD s 0) *
        restrictedDecodedCoverCard
          ((restrictedEffectiveLiveCodesAfterDelete state bad).getD
            (s + 1) []) <
      sizes.getD (s + 1) 0 *
        restrictedDecodedCoverCard
          ((restrictedEffectiveLiveCodesAfterDelete state bad).getD
            s [])) := rfl

private lemma FFS_shape (q0 : ℕ) (sizes : List ℕ) (state bad : BitString) :
    restrictedEffectiveFirstFailedScale q0 sizes state bad =
      (List.range (sizes.length - 1)).findIdx (fun s =>
        restrictedEffectiveDensityFailsBool q0 ((sizes, state, bad), s)) :=
  rfl

private lemma StepInput_shape (q0 : ℕ) (sizes : List ℕ)
    (state bad : BitString) :
    restrictedEffectiveSampledRunStepInput q0 (sizes, state, bad) =
      restrictedEffectiveRebuildSuffixInput
        ((decodeListCode (restrictedSelectorField state 1)).getD
          (restrictedEffectiveFirstFailedScale q0 sizes state bad) [])
        ((restrictedEffectiveLiveCodesAfterDelete state bad).getD
          (restrictedEffectiveFirstFailedScale q0 sizes state bad) [])
        (sizes.drop
          (restrictedEffectiveFirstFailedScale q0 sizes state bad + 1))
        q0 := rfl

private lemma StepPost_shape (q0 : ℕ) (sizes : List ℕ)
    (state bad raw : BitString) :
    restrictedEffectiveSampledRunStepPost q0 ((sizes, state, bad), raw) =
      restrictedEffectiveSampledStateCode
        (restrictedEffectiveDeleteCode
          (restrictedSelectorField state 0) bad)
        ((decodeListCode (restrictedSelectorField state 1)).take
          (restrictedEffectiveFirstFailedScale q0 sizes state bad) ++
        decodeListCode raw) := rfl

private lemma Step_shape (𝒜 : DescriptionFamily) (q0 : ℕ) (sizes : List ℕ)
    (state bad : BitString) :
    restrictedEffectiveSampledRunStep 𝒜 q0 sizes state bad =
      (restrictedEffectiveRebuildSuffix 𝒜
        (restrictedEffectiveSampledRunStepInput q0
          (sizes, state, bad))).map (fun raw =>
        restrictedEffectiveSampledRunStepPost q0
          ((sizes, state, bad), raw)) := rfl

/-- The packed bundle carrying `sizes`, `state`, `bad`, `raw` in one
`listCode` blob: field `0` is the state code, `1` the bad code, `2` the raw
suffix output, `3` the size list. -/
private def stepBundle (sizes : List ℕ) (state bad raw : BitString) :
    BitString :=
  listCode [state, bad, raw, listCode (sizes.map Nat.bits)]

private lemma stepBundle_state (sizes : List ℕ) (state bad raw : BitString) :
    restrictedSelectorField (stepBundle sizes state bad raw) 0 = state := by
  unfold restrictedSelectorField stepBundle
  rw [decodeListCode_listCode]
  rfl

private lemma stepBundle_bad (sizes : List ℕ) (state bad raw : BitString) :
    restrictedSelectorField (stepBundle sizes state bad raw) 1 = bad := by
  unfold restrictedSelectorField stepBundle
  rw [decodeListCode_listCode]
  rfl

private lemma stepBundle_sizes (sizes : List ℕ) (state bad raw : BitString) :
    (decodeListCode
      (restrictedSelectorField (stepBundle sizes state bad raw) 3)).map
        bitsToNat = sizes := by
  unfold restrictedSelectorField stepBundle
  rw [decodeListCode_listCode,
    show [state, bad, raw, listCode (sizes.map Nat.bits)].getD 3 [] =
      listCode (sizes.map Nat.bits) from rfl,
    decodeListCode_listCode, List.map_map]
  simp [Function.comp_def, bitsToNat_bits]

section PackedOpaque

/- See the module docstring: opaque instances and definitions make every
composition match by name. -/
attribute [local irreducible] Primcodable.prod Primcodable.list
attribute [local irreducible] restrictedEffectiveLiveCodesAfterDelete
  restrictedEffectiveDeleteCode restrictedSelectorField
  restrictedEffectiveDensityFailsBool restrictedEffectiveFirstFailedScale
  restrictedDecodedCoverCard restrictedEffectiveSampledRunStepPost
  restrictedEffectiveSampledStateCode restrictedEffectiveSampledRunStepInput
  restrictedEffectiveRebuildSuffixInput restrictedEffectiveSampledRunStep
  restrictedAnchoredInitialFromCode
  restrictedAnchoredSizesFromCode restrictedSampledBadCodeStream
  restrictedSampledBadCodesUpToTime restrictedSampledBadCodesRaw
  anchoredDecodedSteps anchoredDecodedSlack anchoredDecodedAmbientLength
  anchoredDecodedLength anchoredModelListAt

/-- Raw enumeration as an encoded blob: the grid parameters ride in one
`Nat.pair` tower, the growing code list travels as `listCode`. -/
lemma restrictedSampledBadCodesRaw_codes_packed (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun p : BitString × ℕ =>
      listCode (restrictedSampledBadCodesRaw c p.1 𝒜 (Nat.unpair p.2).1
        (Nat.unpair (Nat.unpair p.2).2).1
        (Nat.unpair (Nat.unpair p.2).2).2)) := by
  have hgs : Computable (fun p : BitString × ℕ => (Nat.unpair p.2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hbase : Computable (fun _p : BitString × ℕ =>
      listCode ([] : List BitString)) := Computable.const (listCode [])
  have hΔ : Computable (fun r : (BitString × ℕ) × (ℕ × BitString) =>
      (Nat.unpair (Nat.unpair r.1.2).2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.fst))))).to_comp
  have ht : Computable (fun r : (BitString × ℕ) × (ℕ × BitString) =>
      (Nat.unpair (Nat.unpair r.1.2).2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.fst))))).to_comp
  have hsample : Computable
      (fun r : (BitString × ℕ) × (ℕ × BitString) =>
      decode_restrictedCurveGridCode_sample r.1.1 r.2.1) :=
    (decode_restrictedCurveGridCode_sample_computable.comp
      (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))).of_eq fun _ => rfl
  have hnextSample : Computable
      (fun r : (BitString × ℕ) × (ℕ × BitString) =>
      decode_restrictedCurveGridCode_sample r.1.1 (r.2.1 + 1)) :=
    (decode_restrictedCurveGridCode_sample_computable.comp
      (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))).of_eq fun _ => rfl
  have hstage : Computable
      (fun r : (BitString × ℕ) × (ℕ × BitString) =>
      familyStageModelCodesList c
        (decode_restrictedCurveGridCode_sample r.1.1 (r.2.1 + 1)).1 𝒜
        ((decode_restrictedCurveGridCode_sample r.1.1 r.2.1).2 -
          ((Nat.unpair (Nat.unpair r.1.2).2).1 + 1))
        (Nat.unpair (Nat.unpair r.1.2).2).2) :=
    ((familyStageModelCodesList_computable_uniform c 𝒜).comp
      (Computable.pair (Computable.fst.comp hnextSample)
        (Computable.pair
          (Primrec.nat_sub.to_comp.comp (Computable.snd.comp hsample)
            (Computable.succ.comp hΔ)) ht))).of_eq fun _ => rfl
  have hstep : Computable₂
      (fun (p : BitString × ℕ) (r : ℕ × BitString) =>
      listCode (decodeListCode r.2 ++ familyStageModelCodesList c
        (decode_restrictedCurveGridCode_sample p.1 (r.1 + 1)).1 𝒜
        ((decode_restrictedCurveGridCode_sample p.1 r.1).2 -
          ((Nat.unpair (Nat.unpair p.2).2).1 + 1))
        (Nat.unpair (Nat.unpair p.2).2).2)) :=
    (listCode_primrec.to_comp.comp
      (Computable.list_append.comp
        (decodeListCode_primrec.to_comp.comp
          (Computable.snd.comp Computable.snd))
        hstage)).to₂.of_eq fun _ => rfl
  refine (Computable.nat_rec hgs hbase hstep).of_eq ?_
  rintro ⟨gridCode, nd⟩
  simp only []
  generalize (Nat.unpair nd).1 = gs
  generalize (Nat.unpair (Nat.unpair nd).2).1 = Δ
  generalize (Nat.unpair (Nat.unpair nd).2).2 = t
  induction gs with
  | zero => simp [restrictedSampledBadCodesRaw]
  | succ gs ih =>
      simp only [listCode_nil, restrictedSampledBadCodesRaw, List.range_succ,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at ih ⊢
      rw [ih, decodeListCode_listCode]

/-- Blob raw enumeration with the time split into an explicit component. -/
private lemma restrictedSampledBadCodesRaw_codes_at (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun r : (BitString × ℕ) × ℕ =>
      listCode (restrictedSampledBadCodesRaw c r.1.1 𝒜
        (Nat.unpair r.1.2).1
        (Nat.unpair (Nat.unpair r.1.2).2).1 r.2)) := by
  have hrepack : Computable (fun r : (BitString × ℕ) × ℕ =>
      ((r.1.1, Nat.pair (Nat.unpair r.1.2).1
        (Nat.pair (Nat.unpair (Nat.unpair r.1.2).2).1 r.2)) :
        BitString × ℕ)) :=
    Computable.pair (Computable.fst.comp Computable.fst)
      (Primrec₂.natPair.to_comp.comp
        ((Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.snd.comp Primrec.fst))).to_comp)
        (Primrec₂.natPair.to_comp.comp
          ((Primrec.fst.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp
              (Primrec.snd.comp Primrec.fst))))).to_comp)
          Computable.snd))
  exact ((restrictedSampledBadCodesRaw_codes_packed c 𝒜).comp hrepack).of_eq (fun r => by simp)

/-- Blob stage enumeration (`eraseDups` of the raw list) at explicit time. -/
private lemma restrictedSampledBadCodesUpToTime_codes_at (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun r : (BitString × ℕ) × ℕ =>
      listCode (restrictedSampledBadCodesUpToTime c r.1.1 𝒜
        (Nat.unpair r.1.2).1
        (Nat.unpair (Nat.unpair r.1.2).2).1 r.2)) := by
  have := listCode_primrec.to_comp.comp
    (eraseDups_bitstring_primrec.to_comp.comp
      (decodeListCode_primrec.to_comp.comp (restrictedSampledBadCodesRaw_codes_at c 𝒜)))
  exact this.of_eq (fun r => by
    simp [restrictedSampledBadCodesUpToTime, decodeListCode_listCode])

/-- Blob stream at time zero. -/
private lemma restrictedSampledBadCodeStream_codes_base (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun p : BitString × ℕ =>
      listCode (restrictedSampledBadCodesUpToTime c p.1 𝒜
        (Nat.unpair p.2).1
        (Nat.unpair (Nat.unpair p.2).2).1 0)) := by
  have hrepack0 : Computable (fun p : BitString × ℕ =>
      ((p.1, Nat.pair (Nat.unpair p.2).1
        (Nat.pair (Nat.unpair (Nat.unpair p.2).2).1 0)) : BitString × ℕ)) :=
    Computable.pair Computable.fst
      (Primrec₂.natPair.to_comp.comp
        ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
        (Primrec₂.natPair.to_comp.comp
          ((Primrec.fst.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))).to_comp)
          (Computable.const 0)))
  have hblob := (restrictedSampledBadCodesRaw_codes_packed c 𝒜).comp hrepack0
  have := listCode_primrec.to_comp.comp
    (eraseDups_bitstring_primrec.to_comp.comp
      (decodeListCode_primrec.to_comp.comp hblob))
  exact this.of_eq (fun p => by
    simp [restrictedSampledBadCodesUpToTime, decodeListCode_listCode])

/-- One blob step of the chronological stream recursion. -/
private lemma restrictedSampledBadCodeStream_codes_step (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable₂ (fun (p : BitString × ℕ) (r : ℕ × BitString) =>
      listCode ((decodeListCode r.2 ++
        restrictedSampledBadCodesUpToTime c p.1 𝒜 (Nat.unpair p.2).1
          (Nat.unpair (Nat.unpair p.2).2).1 (r.1 + 1)).eraseDups)) := by
  have h : Computable (fun x : (BitString × ℕ) × (ℕ × BitString) =>
      listCode ((decodeListCode x.2.2 ++
        restrictedSampledBadCodesUpToTime c x.1.1 𝒜 (Nat.unpair x.1.2).1
          (Nat.unpair (Nat.unpair x.1.2).2).1 (x.2.1 + 1)).eraseDups)) := by
    have := listCode_primrec.to_comp.comp
      (eraseDups_bitstring_primrec.to_comp.comp
        (Computable.list_append.comp
          (decodeListCode_primrec.to_comp.comp
            (Computable.snd.comp Computable.snd))
          (decodeListCode_primrec.to_comp.comp
            ((restrictedSampledBadCodesUpToTime_codes_at c 𝒜).comp (Computable.pair Computable.fst
              (Computable.succ.comp
                (Computable.fst.comp Computable.snd)))))))
    exact this.of_eq (fun x => by simp [decodeListCode_listCode])
  exact h.to₂

/-- The chronological bad-code stream as an encoded blob over packed
parameters. -/
lemma restrictedSampledBadCodeStream_codes_packed (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun p : BitString × ℕ =>
      listCode (restrictedSampledBadCodeStream c p.1 𝒜 (Nat.unpair p.2).1
        (Nat.unpair (Nat.unpair p.2).2).1
        (Nat.unpair (Nat.unpair p.2).2).2)) := by
  have ht : Computable (fun p : BitString × ℕ =>
      (Nat.unpair (Nat.unpair p.2).2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))).to_comp
  refine (Computable.nat_rec ht (restrictedSampledBadCodeStream_codes_base c 𝒜)
    (restrictedSampledBadCodeStream_codes_step c 𝒜)).of_eq ?_
  rintro ⟨gridCode, nd⟩
  simp only []
  generalize (Nat.unpair nd).1 = gs
  generalize (Nat.unpair (Nat.unpair nd).2).1 = Δ
  generalize (Nat.unpair (Nat.unpair nd).2).2 = t
  induction t with
  | zero => simp [restrictedSampledBadCodeStream]
  | succ t ih =>
      simp only [restrictedSampledBadCodeStream] at ih ⊢
      rw [ih, decodeListCode_listCode]

/-- The chronological bad-code stream is computable jointly in its grid
code, number of intervals, slack, and time. -/
lemma restrictedSampledBadCodeStream_computable_all (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun p : ((BitString × ℕ) × ℕ) × ℕ =>
      restrictedSampledBadCodeStream c p.1.1.1 𝒜 p.1.1.2 p.1.2 p.2) := by
  have hpack : Computable (fun p : ((BitString × ℕ) × ℕ) × ℕ =>
      ((p.1.1.1, Nat.pair p.1.1.2 (Nat.pair p.1.2 p.2)) : BitString × ℕ)) :=
    Computable.pair
      (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Primrec₂.natPair.to_comp.comp
        (Computable.snd.comp (Computable.fst.comp Computable.fst))
        (Primrec₂.natPair.to_comp.comp
          (Computable.snd.comp Computable.fst)
          Computable.snd))
  have hblob := (restrictedSampledBadCodeStream_codes_packed c 𝒜).comp hpack
  exact (decodeListCode_primrec.to_comp.comp hblob).of_eq (fun p => by
    simp [decodeListCode_listCode])

/-- Packed least failed scale (over the blob-and-overhead carrier). -/
private lemma FFS_packed :
    Primrec (fun w : BitString × ℕ =>
      restrictedEffectiveFirstFailedScale w.2
        ((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat)
        (restrictedSelectorField w.1 0)
        (restrictedSelectorField w.1 1)) := by
  have hsizesR : Primrec (fun r : (BitString × ℕ) × ℕ =>
      (decodeListCode (restrictedSelectorField r.1.1 3)).map bitsToNat) :=
    Primrec.list_map
      (decodeListCode_primrec.comp
        (restrictedSelectorField_primrec.comp
          (Primrec.fst.comp Primrec.fst) (Primrec.const 3)))
      (bitsToNat_primrec.comp Primrec.snd).to₂
  have hlive : Primrec (fun r : (BitString × ℕ) × ℕ =>
      restrictedEffectiveLiveCodesAfterDelete
        (restrictedSelectorField r.1.1 0)
        (restrictedSelectorField r.1.1 1)) :=
    restrictedEffectiveLiveCodesAfterDelete_primrec.comp
      (Primrec.pair
        (restrictedSelectorField_primrec.comp
          (Primrec.fst.comp Primrec.fst) (Primrec.const 0))
        (restrictedSelectorField_primrec.comp
          (Primrec.fst.comp Primrec.fst) (Primrec.const 1)))
  have hDFB : Primrec₂ (fun (w : BitString × ℕ) (s : ℕ) =>
      restrictedEffectiveDensityFailsBool w.2
        ((((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat,
          restrictedSelectorField w.1 0, restrictedSelectorField w.1 1)),
          s)) := by
    have hleft : Primrec (fun r : (BitString × ℕ) × ℕ =>
        (2 * r.1.2 *
          (((decodeListCode (restrictedSelectorField r.1.1 3)).map
            bitsToNat).getD r.2 0)) *
          restrictedDecodedCoverCard
            ((restrictedEffectiveLiveCodesAfterDelete
              (restrictedSelectorField r.1.1 0)
              (restrictedSelectorField r.1.1 1)).getD (r.2 + 1) [])) :=
      Primrec.nat_mul.comp
        (Primrec.nat_mul.comp
          (Primrec.nat_mul.comp (Primrec.const 2)
            (Primrec.snd.comp Primrec.fst))
          ((Primrec.list_getD 0).comp hsizesR Primrec.snd))
        (restrictedDecodedCoverCard_primrec.comp
          ((Primrec.list_getD []).comp hlive
            (Primrec.succ.comp Primrec.snd)))
    have hright : Primrec (fun r : (BitString × ℕ) × ℕ =>
        (((decodeListCode (restrictedSelectorField r.1.1 3)).map
          bitsToNat).getD (r.2 + 1) 0) *
          restrictedDecodedCoverCard
            ((restrictedEffectiveLiveCodesAfterDelete
              (restrictedSelectorField r.1.1 0)
              (restrictedSelectorField r.1.1 1)).getD r.2 [])) :=
      Primrec.nat_mul.comp
        ((Primrec.list_getD 0).comp hsizesR
          (Primrec.succ.comp Primrec.snd))
        (restrictedDecodedCoverCard_primrec.comp
          ((Primrec.list_getD []).comp hlive Primrec.snd))
    exact ((PrimrecPred.decide
      (Primrec.nat_lt.comp hleft hright)).of_eq (fun r =>
        (DFB_shape r.1.2
          ((decodeListCode (restrictedSelectorField r.1.1 3)).map bitsToNat)
          (restrictedSelectorField r.1.1 0)
          (restrictedSelectorField r.1.1 1) r.2).symm)).to₂
  have hrange : Primrec (fun w : BitString × ℕ =>
      List.range
        (((decodeListCode (restrictedSelectorField w.1 3)).map
          bitsToNat).length - 1)) :=
    Primrec.list_range.comp
      (Primrec.nat_sub.comp
        (Primrec.list_length.comp
          (Primrec.list_map
            (decodeListCode_primrec.comp
              (restrictedSelectorField_primrec.comp Primrec.fst
                (Primrec.const 3)))
            (bitsToNat_primrec.comp Primrec.snd).to₂))
        (Primrec.const 1))
  exact (Primrec.list_findIdx hrange hDFB).of_eq (fun w =>
    (FFS_shape w.2
      ((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat)
      (restrictedSelectorField w.1 0)
      (restrictedSelectorField w.1 1)).symm)

/-- Packed rebuild-suffix input. -/
private lemma StepInput_packed :
    Primrec (fun w : BitString × ℕ =>
      restrictedEffectiveSampledRunStepInput w.2
        (((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat,
          restrictedSelectorField w.1 0, restrictedSelectorField w.1 1))) := by
  have hstate : Primrec (fun w : BitString × ℕ =>
      restrictedSelectorField w.1 0) :=
    restrictedSelectorField_primrec.comp Primrec.fst (Primrec.const 0)
  have hbad : Primrec (fun w : BitString × ℕ =>
      restrictedSelectorField w.1 1) :=
    restrictedSelectorField_primrec.comp Primrec.fst (Primrec.const 1)
  have hsizes : Primrec (fun w : BitString × ℕ =>
      (decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat) :=
    Primrec.list_map
      (decodeListCode_primrec.comp
        (restrictedSelectorField_primrec.comp Primrec.fst
          (Primrec.const 3)))
      (bitsToNat_primrec.comp Primrec.snd).to₂
  have hmodels : Primrec (fun w : BitString × ℕ =>
      (decodeListCode
        (restrictedSelectorField (restrictedSelectorField w.1 0) 1)).getD
          (restrictedEffectiveFirstFailedScale w.2
            ((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat)
            (restrictedSelectorField w.1 0)
            (restrictedSelectorField w.1 1)) []) :=
    (Primrec.list_getD []).comp
      (decodeListCode_primrec.comp
        (restrictedSelectorField_primrec.comp hstate (Primrec.const 1)))
      FFS_packed
  have hlives : Primrec (fun w : BitString × ℕ =>
      (restrictedEffectiveLiveCodesAfterDelete
        (restrictedSelectorField w.1 0)
        (restrictedSelectorField w.1 1)).getD
          (restrictedEffectiveFirstFailedScale w.2
            ((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat)
            (restrictedSelectorField w.1 0)
            (restrictedSelectorField w.1 1)) []) :=
    (Primrec.list_getD []).comp
      (restrictedEffectiveLiveCodesAfterDelete_primrec.comp
        (Primrec.pair hstate hbad))
      FFS_packed
  have hdrop : Primrec (fun w : BitString × ℕ =>
      ((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat).drop
        (restrictedEffectiveFirstFailedScale w.2
          ((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat)
          (restrictedSelectorField w.1 0)
          (restrictedSelectorField w.1 1) + 1)) :=
    Primrec.list_drop.comp hsizes (Primrec.succ.comp FFS_packed)
  exact (restrictedEffectiveRebuildSuffixInput_primrec_all.comp
    (Primrec.pair (Primrec.pair hmodels hlives)
      (Primrec.pair hdrop Primrec.snd))).of_eq (fun w =>
    (StepInput_shape w.2
      ((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat)
      (restrictedSelectorField w.1 0)
      (restrictedSelectorField w.1 1)).symm)

/-- Packed reassembly with the raw suffix output as a second argument. -/
private lemma StepPost_packed2 :
    Computable₂ (fun (w : BitString × ℕ) (raw : BitString) =>
      restrictedEffectiveSampledRunStepPost w.2
        ((((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat,
          restrictedSelectorField w.1 0, restrictedSelectorField w.1 1)),
          raw)) := by
  have hstate : Primrec (fun r : (BitString × ℕ) × BitString =>
      restrictedSelectorField r.1.1 0) :=
    restrictedSelectorField_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.const 0)
  have hdeleted : Primrec (fun r : (BitString × ℕ) × BitString =>
      restrictedEffectiveDeleteCode
        (restrictedSelectorField (restrictedSelectorField r.1.1 0) 0)
        (restrictedSelectorField r.1.1 1)) :=
    restrictedEffectiveDeleteCode_primrec.comp
      (Primrec.pair
        (restrictedSelectorField_primrec.comp hstate (Primrec.const 0))
        (restrictedSelectorField_primrec.comp
          (Primrec.fst.comp Primrec.fst) (Primrec.const 1)))
  have hcodes : Primrec (fun r : (BitString × ℕ) × BitString =>
      (decodeListCode
        (restrictedSelectorField (restrictedSelectorField r.1.1 0) 1)).take
          (restrictedEffectiveFirstFailedScale r.1.2
            ((decodeListCode
              (restrictedSelectorField r.1.1 3)).map bitsToNat)
            (restrictedSelectorField r.1.1 0)
            (restrictedSelectorField r.1.1 1)) ++
        decodeListCode r.2) :=
    Primrec.list_append.comp
      (Primrec.list_take.comp
        (decodeListCode_primrec.comp
          (restrictedSelectorField_primrec.comp hstate (Primrec.const 1)))
        (FFS_packed.comp Primrec.fst))
      (decodeListCode_primrec.comp Primrec.snd)
  exact ((restrictedEffectiveSampledStateCode_primrec.comp
    (Primrec.pair hdeleted hcodes)).of_eq (fun r =>
      (StepPost_shape r.1.2
        ((decodeListCode (restrictedSelectorField r.1.1 3)).map bitsToNat)
        (restrictedSelectorField r.1.1 0)
        (restrictedSelectorField r.1.1 1) r.2).symm)).to_comp.to₂

/-- Packed one-step update. -/
private lemma Step_packed (𝒜 : DescriptionFamily) :
    Partrec (fun w : BitString × ℕ =>
      restrictedEffectiveSampledRunStep 𝒜 w.2
        ((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat)
        (restrictedSelectorField w.1 0)
        (restrictedSelectorField w.1 1)) :=
  (Partrec.map
    ((restrictedEffectiveRebuildSuffix_partrec 𝒜).comp
      StepInput_packed.to_comp)
    StepPost_packed2).of_eq (fun w =>
      (Step_shape 𝒜 w.2
        ((decodeListCode (restrictedSelectorField w.1 3)).map bitsToNat)
        (restrictedSelectorField w.1 0)
        (restrictedSelectorField w.1 1)).symm)

/-- One effective bad-event update, partial-recursive uniformly in `q0`. -/
lemma restrictedEffectiveSampledRunStep_partrec_all
    (𝒜 : DescriptionFamily) :
    Partrec (fun p : ℕ × (List ℕ × BitString × BitString) =>
      restrictedEffectiveSampledRunStep 𝒜 p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have henc : Computable (fun p : ℕ × (List ℕ × BitString × BitString) =>
      ((stepBundle p.2.1 p.2.2.1 p.2.2.2 [], p.1) : BitString × ℕ)) := by
    have hfields : Primrec (fun p : ℕ × (List ℕ × BitString × BitString) =>
        ([p.2.2.1, p.2.2.2, [], listCode (p.2.1.map Nat.bits)] :
          List BitString)) :=
      Primrec.list_cons.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.list_cons.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.list_cons.comp (Primrec.const [])
            (Primrec.list_cons.comp
              (listCode_primrec.comp
                (Primrec.list_map (Primrec.fst.comp Primrec.snd)
                  (primrecNatBits.comp Primrec.snd).to₂))
              (Primrec.const []))))
    exact (Primrec.pair (listCode_primrec.comp hfields)
      Primrec.fst).to_comp
  exact ((Step_packed 𝒜).comp henc).of_eq (fun p => by
    rw [stepBundle_sizes, stepBundle_state, stepBundle_bad])

/-- Event-prefix execution is partial-recursive jointly in the overhead,
sizes, initial state, event list, and prefix length. -/
lemma restrictedEventPrefixRun_partrec_all (𝒜 : DescriptionFamily) :
    Partrec (fun p : (((ℕ × List ℕ) × BitString) × List BitString) × ℕ =>
      restrictedEventPrefixRun 𝒜 p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2) := by
  let P := (((ℕ × List ℕ) × BitString) × List BitString) × ℕ
  have hcount : Computable (fun p : P => p.2) := Computable.snd
  have hbase : Partrec (fun p : P => Part.some p.1.1.2) :=
    (Computable.snd.comp (Computable.fst.comp Computable.fst)).partrec
  have hq0 : Computable (fun r : P × (ℕ × BitString) => r.1.1.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp
      (Computable.fst.comp (Computable.fst.comp Computable.fst)))
  have hsizes : Computable (fun r : P × (ℕ × BitString) => r.1.1.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp
      (Computable.fst.comp (Computable.fst.comp Computable.fst)))
  have hstate : Computable (fun r : P × (ℕ × BitString) => r.2.2) :=
    Computable.snd.comp Computable.snd
  have hevents : Computable (fun r : P × (ℕ × BitString) => r.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hindex : Computable (fun r : P × (ℕ × BitString) => r.2.1) :=
    Computable.fst.comp Computable.snd
  have hbad : Computable (fun r : P × (ℕ × BitString) =>
      r.1.1.2.getD r.2.1 []) :=
    (Primrec.list_getD []).to_comp.comp hevents hindex
  have hinput : Computable (fun r : P × (ℕ × BitString) =>
      (r.1.1.1.1.1, (r.1.1.1.1.2, r.2.2, r.1.1.2.getD r.2.1 []))) :=
    Computable.pair hq0 (Computable.pair hsizes
      (Computable.pair hstate hbad))
  have hnext : Partrec₂ (fun (_p : P) (r : ℕ × BitString) =>
      restrictedEffectiveSampledRunStep 𝒜 _p.1.1.1.1 _p.1.1.1.2
        r.2 (_p.1.2.getD r.1 [])) :=
    (restrictedEffectiveSampledRunStep_partrec_all 𝒜).comp hinput |>.to₂
  exact (Partrec.nat_rec hcount hbase hnext).of_eq (fun _ => rfl)

/-- The event-indexed decoder trace is a single partial-recursive procedure in
the grid code, explicit overhead, and event count. -/
lemma anchoredDecoderTrace_partrec (𝒜 : DescriptionFamily) (c : Code) :
    Partrec (fun p : (BitString × ℕ) × ℕ =>
      anchoredDecoderTrace 𝒜 c p.1.1 p.1.2 p.2) := by
  let P := (BitString × ℕ) × ℕ
  have hgrid : Computable (fun p : P => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hq0 : Computable (fun p : P => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hm : Computable (fun p : P => p.2) := Computable.snd
  have hsteps : Computable (fun p : P => anchoredDecodedSteps p.1.1) :=
    anchoredDecodedSteps_primrec.to_comp.comp hgrid
  have hΔ : Computable (fun p : P => anchoredDecodedSlack p.1.1) :=
    anchoredDecodedSlack_primrec.to_comp.comp hgrid
  have hamb : Computable (fun p : P =>
      anchoredDecodedAmbientLength p.1.1) :=
    anchoredDecodedAmbientLength_primrec.to_comp.comp hgrid
  have hgridR : Computable (fun r : P × ℕ => r.1.1.1) :=
    hgrid.comp Computable.fst
  have hstepsR : Computable (fun r : P × ℕ =>
      anchoredDecodedSteps r.1.1.1) := hsteps.comp Computable.fst
  have hΔR : Computable (fun r : P × ℕ =>
      anchoredDecodedSlack r.1.1.1) := hΔ.comp Computable.fst
  have hstream : Computable (fun r : P × ℕ =>
      restrictedSampledBadCodeStream c r.1.1.1 𝒜.toPre
        (anchoredDecodedSteps r.1.1.1)
        (anchoredDecodedSlack r.1.1.1) r.2) :=
    (restrictedSampledBadCodeStream_computable_all c 𝒜.toPre).comp
      (Computable.pair
        (Computable.pair (Computable.pair hgridR hstepsR) hΔR)
        Computable.snd)
  have hmR : Computable (fun r : P × ℕ => r.1.2) :=
    hm.comp Computable.fst
  have hcheck : Computable₂ (fun (p : P) (τ : ℕ) => decide (p.2 ≤
      (restrictedSampledBadCodeStream c p.1.1 𝒜.toPre
        (anchoredDecodedSteps p.1.1)
        (anchoredDecodedSlack p.1.1) τ).length)) :=
    ((PrimrecPred.decide Primrec.nat_le).to_comp.to₂.comp hmR
      (Computable.list_length.comp hstream)).to₂
  have hfind : Partrec (fun p : P => Nat.rfind (fun τ => Part.some
      (decide (p.2 ≤ (restrictedSampledBadCodeStream c p.1.1 𝒜.toPre
        (anchoredDecodedSteps p.1.1)
        (anchoredDecodedSlack p.1.1) τ).length)))) :=
    Partrec.rfind hcheck.partrec₂
  have hinitInput : Computable (fun p : P =>
      ((((p.1.2, p.1.1), anchoredDecodedSteps p.1.1),
        anchoredDecodedSlack p.1.1), anchoredDecodedAmbientLength p.1.1)) :=
    Computable.pair
      (Computable.pair (Computable.pair (Computable.pair hq0 hgrid) hsteps) hΔ)
      hamb
  have hinit : Partrec (fun p : P =>
      restrictedAnchoredInitialFromCode 𝒜 p.1.2 p.1.1
        (anchoredDecodedSteps p.1.1) (anchoredDecodedSlack p.1.1)
        (anchoredDecodedAmbientLength p.1.1)) :=
    (restrictedAnchoredInitialFromCode_partrec_all 𝒜).comp hinitInput
  have hsizesR : Computable (fun r : P × ℕ =>
      restrictedAnchoredSizesFromCode r.1.1.1
        (anchoredDecodedSteps r.1.1.1) (anchoredDecodedSlack r.1.1.1)
        (anchoredDecodedAmbientLength r.1.1.1)) :=
    restrictedAnchoredSizesFromCode_computable_all.comp
      (Computable.pair
        (Computable.pair (Computable.pair hgridR hstepsR) hΔR)
        (hamb.comp Computable.fst))
  have hinitR : Partrec (fun r : P × ℕ =>
      restrictedAnchoredInitialFromCode 𝒜 r.1.1.2 r.1.1.1
        (anchoredDecodedSteps r.1.1.1) (anchoredDecodedSlack r.1.1.1)
        (anchoredDecodedAmbientLength r.1.1.1)) :=
    hinit.comp Computable.fst
  have hprefixInput : Computable (fun r : (P × ℕ) × BitString =>
      ((((r.1.1.1.2,
          restrictedAnchoredSizesFromCode r.1.1.1.1
            (anchoredDecodedSteps r.1.1.1.1)
            (anchoredDecodedSlack r.1.1.1.1)
            (anchoredDecodedAmbientLength r.1.1.1.1)), r.2),
        restrictedSampledBadCodeStream c r.1.1.1.1 𝒜.toPre
          (anchoredDecodedSteps r.1.1.1.1)
          (anchoredDecodedSlack r.1.1.1.1) r.1.2), r.1.1.2)) :=
    Computable.pair
      (Computable.pair
        (Computable.pair
          (Computable.pair
            (hq0.comp (Computable.fst.comp Computable.fst))
            (hsizesR.comp Computable.fst))
          Computable.snd)
        (hstream.comp Computable.fst))
      (hm.comp (Computable.fst.comp Computable.fst))
  have hprefix : Partrec₂ (fun (r : P × ℕ) (st0 : BitString) =>
      restrictedEventPrefixRun 𝒜 r.1.1.2
        (restrictedAnchoredSizesFromCode r.1.1.1
          (anchoredDecodedSteps r.1.1.1) (anchoredDecodedSlack r.1.1.1)
          (anchoredDecodedAmbientLength r.1.1.1)) st0
        (restrictedSampledBadCodeStream c r.1.1.1 𝒜.toPre
          (anchoredDecodedSteps r.1.1.1)
          (anchoredDecodedSlack r.1.1.1) r.2) r.1.2) :=
    ((restrictedEventPrefixRun_partrec_all 𝒜).comp hprefixInput).to₂
  have hbody : Partrec₂ (fun (p : P) (τ : ℕ) =>
      (restrictedAnchoredInitialFromCode 𝒜 p.1.2 p.1.1
        (anchoredDecodedSteps p.1.1) (anchoredDecodedSlack p.1.1)
        (anchoredDecodedAmbientLength p.1.1)).bind
      (fun st0 => restrictedEventPrefixRun 𝒜 p.1.2
        (restrictedAnchoredSizesFromCode p.1.1
          (anchoredDecodedSteps p.1.1) (anchoredDecodedSlack p.1.1)
          (anchoredDecodedAmbientLength p.1.1)) st0
        (restrictedSampledBadCodeStream c p.1.1 𝒜.toPre
          (anchoredDecodedSteps p.1.1)
          (anchoredDecodedSlack p.1.1) τ) p.2)) :=
    (Partrec.bind hinitR hprefix).to₂
  exact (Partrec.bind hfind hbody).of_eq (fun _ => rfl)

/-- Change counting is partial-recursive jointly in the grid, overhead, scale,
and event count. -/
lemma anchoredChangeTrace_partrec (𝒜 : DescriptionFamily) (c : Code) :
    Partrec (fun p : ((BitString × ℕ) × ℕ) × ℕ =>
      anchoredChangeTrace 𝒜 c p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  let P := ((BitString × ℕ) × ℕ) × ℕ
  have hgrid : Computable (fun p : P => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hq0 : Computable (fun p : P => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hs : Computable (fun p : P => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hcount : Computable (fun p : P => p.2) := Computable.snd
  have htraceBase : Partrec (fun p : P =>
      anchoredDecoderTrace 𝒜 c p.1.1.1 p.1.1.2 0) :=
    (anchoredDecoderTrace_partrec 𝒜 c).comp
      (Computable.pair (Computable.pair hgrid hq0) (Computable.const 0))
  have hbase : Partrec (fun p : P =>
      (anchoredDecoderTrace 𝒜 c p.1.1.1 p.1.1.2 0).map
        (fun code => (0, anchoredModelListAt p.1.2 code))) :=
    Partrec.map htraceBase
      ((Primrec.pair (Primrec.const 0)
        (anchoredModelListAt_primrec.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)).to_comp.to₂)
  have htraceStep : Partrec
      (fun r : P × (ℕ × (ℕ × List BitString)) =>
      anchoredDecoderTrace 𝒜 c r.1.1.1.1 r.1.1.1.2 (r.2.1 + 1)) :=
    (anchoredDecoderTrace_partrec 𝒜 c).comp
      (Computable.pair
        (Computable.pair
          (hgrid.comp Computable.fst) (hq0.comp Computable.fst))
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))
  have hstepPost : Computable₂
      (fun (r : P × (ℕ × (ℕ × List BitString))) (code : BitString) =>
      if anchoredModelListAt r.1.1.2 code = r.2.2.2 then
        (r.2.2.1, r.2.2.2)
      else (r.2.2.1 + 1, anchoredModelListAt r.1.1.2 code)) := by
    have hscale : Primrec (fun x :
        (P × (ℕ × (ℕ × List BitString))) × BitString => x.1.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hmodel : Primrec (fun x :
        (P × (ℕ × (ℕ × List BitString))) × BitString =>
        anchoredModelListAt x.1.1.1.2 x.2) :=
      anchoredModelListAt_primrec.comp hscale Primrec.snd
    have hprevCount : Primrec (fun x :
        (P × (ℕ × (ℕ × List BitString))) × BitString => x.1.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have hprevList : Primrec (fun x :
        (P × (ℕ × (ℕ × List BitString))) × BitString => x.1.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact ((Primrec.ite (Primrec.eq.comp hmodel hprevList)
      (Primrec.pair hprevCount hprevList)
      (Primrec.pair (Primrec.nat_add.comp hprevCount (Primrec.const 1))
        hmodel)).to_comp).to₂
  have hstep : Partrec₂ (fun (p : P) (r : ℕ × (ℕ × List BitString)) =>
      (anchoredDecoderTrace 𝒜 c p.1.1.1 p.1.1.2 (r.1 + 1)).map
        (fun code => if anchoredModelListAt p.1.2 code = r.2.2 then
          (r.2.1, r.2.2)
        else (r.2.1 + 1, anchoredModelListAt p.1.2 code))) :=
    (Partrec.map htraceStep hstepPost).to₂
  refine (Partrec.nat_rec hcount hbase hstep).of_eq ?_
  rintro ⟨⟨⟨grid, q0⟩, sc⟩, m⟩
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only []
      rw [show anchoredChangeTrace 𝒜 c grid q0 sc (m + 1) =
          (anchoredChangeTrace 𝒜 c grid q0 sc m).bind (fun p =>
            (anchoredDecoderTrace 𝒜 c grid q0 (m + 1)).map (fun code =>
              if anchoredModelListAt sc code = p.2 then (p.1, p.2)
              else (p.1 + 1, anchoredModelListAt sc code))) from rfl,
        ← ih]

/-- The fixed-code version decoder is partial-recursive.  In particular, its
invariance constant may depend on the decompressor code `c`, which is why the
paper-facing complexity leaf below fixes `c` before choosing its slack
constant. -/
lemma anchoredVersionDecoder_partrec (𝒜 : DescriptionFamily) (c : Code) :
    Partrec (anchoredVersionDecoder 𝒜 c) := by
  have hparts : Computable (fun bundle : BitString => decodeListCode bundle) :=
    decodeListCode_primrec.to_comp
  have hpart (i : ℕ) : Computable (fun bundle : BitString =>
      (decodeListCode bundle).getD i []) :=
    (Primrec.list_getD []).to_comp.comp hparts (Computable.const i)
  have hgrid : Computable (fun bundle : BitString =>
      (decodeListCode bundle).getD 0 []) := hpart 0
  have hq0 : Computable (fun bundle : BitString =>
      bitsToNat ((decodeListCode bundle).getD 1 [])) :=
    bitsToNat_primrec.to_comp.comp (hpart 1)
  have hs : Computable (fun bundle : BitString =>
      bitsToNat ((decodeListCode bundle).getD 2 [])) :=
    bitsToNat_primrec.to_comp.comp (hpart 2)
  have hv : Computable (fun bundle : BitString =>
      bitsToNat ((decodeListCode bundle).getD 3 [])) :=
    bitsToNat_primrec.to_comp.comp (hpart 3)
  have hchangeInput : Computable (fun r : BitString × ℕ =>
      (((((decodeListCode r.1).getD 0 [],
          bitsToNat ((decodeListCode r.1).getD 1 [])),
        bitsToNat ((decodeListCode r.1).getD 2 [])), r.2))) :=
    Computable.pair
      (Computable.pair
        (Computable.pair (hgrid.comp Computable.fst)
          (hq0.comp Computable.fst))
        (hs.comp Computable.fst))
      Computable.snd
  have hchange : Partrec (fun r : BitString × ℕ =>
      anchoredChangeTrace 𝒜 c
        ((decodeListCode r.1).getD 0 [])
        (bitsToNat ((decodeListCode r.1).getD 1 []))
        (bitsToNat ((decodeListCode r.1).getD 2 [])) r.2) :=
    (anchoredChangeTrace_partrec 𝒜 c).comp hchangeInput
  have hcheckPost : Computable₂ (fun (r : BitString × ℕ)
      (p : ℕ × List BitString) => decide
        (bitsToNat ((decodeListCode r.1).getD 3 []) ≤ p.1)) :=
    ((PrimrecPred.decide Primrec.nat_le).to_comp.to₂.comp
      (hv.comp (Computable.fst.comp Computable.fst))
      (Computable.fst.comp Computable.snd)).to₂
  have hcheck : Partrec₂ (fun (bundle : BitString) (m : ℕ) =>
      (anchoredChangeTrace 𝒜 c
        ((decodeListCode bundle).getD 0 [])
        (bitsToNat ((decodeListCode bundle).getD 1 []))
        (bitsToNat ((decodeListCode bundle).getD 2 [])) m).map
        (fun p => decide
          (bitsToNat ((decodeListCode bundle).getD 3 []) ≤ p.1))) :=
    (Partrec.map hchange hcheckPost).to₂
  have hfind : Partrec (fun bundle : BitString => Nat.rfind (fun m =>
      (anchoredChangeTrace 𝒜 c
        ((decodeListCode bundle).getD 0 [])
        (bitsToNat ((decodeListCode bundle).getD 1 []))
        (bitsToNat ((decodeListCode bundle).getD 2 [])) m).map
        (fun p => decide
          (bitsToNat ((decodeListCode bundle).getD 3 []) ≤ p.1)))) :=
    Partrec.rfind hcheck
  have houtputPost : Computable₂ (fun (_r : BitString × ℕ)
      (p : ℕ × List BitString) => uniformCodeOfList p.2) :=
    (uniformCodeOfList_primrec.to_comp.comp
      (Computable.snd.comp Computable.snd)).to₂
  have hbody : Partrec₂ (fun (bundle : BitString) (m : ℕ) =>
      (anchoredChangeTrace 𝒜 c
        ((decodeListCode bundle).getD 0 [])
        (bitsToNat ((decodeListCode bundle).getD 1 []))
        (bitsToNat ((decodeListCode bundle).getD 2 [])) m).map
        (fun p => uniformCodeOfList p.2)) :=
    (Partrec.map hchange houtputPost).to₂
  exact (Partrec.bind hfind hbody).of_eq (fun _ => rfl)

end PackedOpaque

end Kolmogorov
