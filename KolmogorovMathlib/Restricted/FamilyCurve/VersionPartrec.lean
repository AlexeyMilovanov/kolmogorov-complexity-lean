import KolmogorovMathlib.Restricted.FamilyCurve.VersionDecoder

/-!
# M7: uniform computability layer of the version decoder

Partial-recursiveness of the version decoder, uniform in the encoded grid.
The decoder definitions themselves live in `VersionDecoder.lean`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open CodedFiniteDistribution

section PrimcodableOpaque

/- `Primcodable` instance terms stay opaque during definitional checks: the
uniform lemmas in this section compose at 4–5-component product types.  The
anchored initializer at the end of the file lives outside the section because
its `Partrec` argument needs the instances reducible. -/
attribute [local irreducible] Primcodable.prod Primcodable.list

/-- The raw bad-code enumeration is computable with the grid dimensions and
slack supplied as data, rather than baked into the program. -/
lemma restrictedSampledBadCodesRaw_computable_all (c : Code)
    (𝒜 : PreDescriptionFamily) :
    Computable (fun p : ((BitString × ℕ) × ℕ) × ℕ =>
      restrictedSampledBadCodesRaw c p.1.1.1 𝒜 p.1.1.2 p.1.2 p.2) := by
  let Q := ((BitString × ℕ) × ℕ) × ℕ
  have hcount : Computable (fun p : Q => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hbase : Computable (fun _p : Q => ([] : List BitString)) :=
    Computable.const []
  have hgrid : Computable (fun r : Q × (ℕ × List BitString) => r.1.1.1.1) :=
    Computable.fst.comp
      (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hindex : Computable (fun r : Q × (ℕ × List BitString) => r.2.1) :=
    Computable.fst.comp Computable.snd
  have hsample : Computable (fun r : Q × (ℕ × List BitString) =>
      decode_restrictedCurveGridCode_sample r.1.1.1.1 r.2.1) :=
    (decode_restrictedCurveGridCode_sample_primrec.to_comp.comp
      (Computable.pair hgrid hindex)).of_eq fun _ => rfl
  have hnextSample : Computable (fun r : Q × (ℕ × List BitString) =>
      decode_restrictedCurveGridCode_sample r.1.1.1.1 (r.2.1 + 1)) :=
    (decode_restrictedCurveGridCode_sample_primrec.to_comp.comp
      (Computable.pair hgrid (Computable.succ.comp hindex))).of_eq fun _ => rfl
  have hΔ : Computable (fun r : Q × (ℕ × List BitString) => r.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have ht : Computable (fun r : Q × (ℕ × List BitString) => r.1.2) :=
    Computable.snd.comp Computable.fst
  have hj : Computable (fun r : Q × (ℕ × List BitString) =>
      (decode_restrictedCurveGridCode_sample r.1.1.1.1 r.2.1).2 -
        (r.1.1.2 + 1)) :=
    (Primrec.nat_sub.to_comp.comp (Computable.snd.comp hsample)
      (Computable.succ.comp hΔ)).of_eq fun _ => rfl
  have hstage : Computable (fun r : Q × (ℕ × List BitString) =>
      familyStageModelCodesList c
        (decode_restrictedCurveGridCode_sample r.1.1.1.1 (r.2.1 + 1)).1
        𝒜
        ((decode_restrictedCurveGridCode_sample r.1.1.1.1 r.2.1).2 -
          (r.1.1.2 + 1)) r.1.2) :=
    ((familyStageModelCodesList_computable_uniform c 𝒜).comp
      (Computable.pair (Computable.fst.comp hnextSample)
        (Computable.pair hj ht))).of_eq fun _ => rfl
  have hstep : Computable₂ (fun (_p : Q) (r : ℕ × List BitString) =>
      r.2 ++ familyStageModelCodesList c
        (decode_restrictedCurveGridCode_sample _p.1.1.1 (r.1 + 1)).1 𝒜
        ((decode_restrictedCurveGridCode_sample _p.1.1.1 r.1).2 -
          (_p.1.2 + 1)) _p.2) :=
    ((Computable.list_append.comp
      (Computable.snd.comp Computable.snd) hstage).to₂).of_eq fun _ => rfl
  refine (Computable.nat_rec hcount hbase hstep).of_eq ?_
  rintro ⟨⟨⟨gridCode, gridSteps⟩, Δ⟩, time⟩
  induction gridSteps with
  | zero => simp [restrictedSampledBadCodesRaw]
  | succ gridSteps ih =>
      simp [restrictedSampledBadCodesRaw, List.range_succ,
        List.flatMap_append, ih]

/-- The density predicate with `q0` supplied as data. -/
lemma restrictedEffectiveDensityFailsBool_primrec_all :
    Primrec (fun p : ℕ × ((List ℕ × BitString × BitString) × ℕ) =>
      restrictedEffectiveDensityFailsBool p.1 p.2) := by
  have hlive : Primrec (fun p :
      ℕ × ((List ℕ × BitString × BitString) × ℕ) =>
      restrictedEffectiveLiveCodesAfterDelete p.2.1.2.1 p.2.1.2.2) :=
    restrictedEffectiveLiveCodesAfterDelete_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  have hsize : Primrec (fun p :
      ℕ × ((List ℕ × BitString × BitString) × ℕ) =>
      p.2.1.1.getD p.2.2 0) :=
    (Primrec.list_getD 0).comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hsizeSucc : Primrec (fun p :
      ℕ × ((List ℕ × BitString × BitString) × ℕ) =>
      p.2.1.1.getD (p.2.2 + 1) 0) :=
    (Primrec.list_getD 0).comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
  have hliveCode : Primrec (fun p :
      ℕ × ((List ℕ × BitString × BitString) × ℕ) =>
      (restrictedEffectiveLiveCodesAfterDelete p.2.1.2.1
        p.2.1.2.2).getD p.2.2 []) :=
    (Primrec.list_getD []).comp hlive (Primrec.snd.comp Primrec.snd)
  have hliveCodeSucc : Primrec (fun p :
      ℕ × ((List ℕ × BitString × BitString) × ℕ) =>
      (restrictedEffectiveLiveCodesAfterDelete p.2.1.2.1
        p.2.1.2.2).getD (p.2.2 + 1) []) :=
    (Primrec.list_getD []).comp hlive
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
  have htwoq : Primrec (fun p :
      ℕ × ((List ℕ × BitString × BitString) × ℕ) => 2 * p.1) :=
    Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst
  have hleft := Primrec.nat_mul.comp
    (Primrec.nat_mul.comp htwoq hsize)
    (restrictedDecodedCoverCard_primrec.comp hliveCodeSucc)
  have hright := Primrec.nat_mul.comp hsizeSucc
    (restrictedDecodedCoverCard_primrec.comp hliveCode)
  exact (PrimrecPred.decide (Primrec.nat_lt.comp hleft hright)).of_eq
    (fun _ => rfl)

/-- Least failed scale with `q0` supplied as data. -/
lemma restrictedEffectiveFirstFailedScale_primrec_all :
    Primrec (fun p : ℕ × (List ℕ × BitString × BitString) =>
      restrictedEffectiveFirstFailedScale p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hrange : Primrec (fun p : ℕ × (List ℕ × BitString × BitString) =>
      List.range (p.2.1.length - 1)) :=
    Primrec.list_range.comp (Primrec.nat_sub.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.const 1))
  have hp : Primrec₂ (fun (p : ℕ × (List ℕ × BitString × BitString))
      (s : ℕ) => restrictedEffectiveDensityFailsBool p.1 (p.2, s)) :=
    restrictedEffectiveDensityFailsBool_primrec_all.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)) |>.to₂
  exact (Primrec.list_findIdx hrange hp).of_eq (fun _ => rfl)

/-- Rebuild input with `q0` supplied as data. -/
lemma restrictedEffectiveSampledRunStepInput_primrec_all :
    Primrec (fun p : ℕ × (List ℕ × BitString × BitString) =>
      restrictedEffectiveSampledRunStepInput p.1 p.2) := by
  have hq := restrictedEffectiveFirstFailedScale_primrec_all
  have hmodels : Primrec (fun p : ℕ × (List ℕ × BitString × BitString) =>
      decodeListCode (restrictedSelectorField p.2.2.1 1)) :=
    decodeListCode_primrec.comp
      (restrictedSelectorField_primrec.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 1))
  have hlive : Primrec (fun p : ℕ × (List ℕ × BitString × BitString) =>
      restrictedEffectiveLiveCodesAfterDelete p.2.2.1 p.2.2.2) :=
    restrictedEffectiveLiveCodesAfterDelete_primrec.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hpredecessor := (Primrec.list_getD []).comp hmodels hq
  have hliveAtQ := (Primrec.list_getD []).comp hlive hq
  have hsuffix := Primrec.list_drop.comp (Primrec.succ.comp hq)
    (Primrec.fst.comp Primrec.snd)
  have hsuffixBits := Primrec.list_map hsuffix
    (primrecNatBits.comp Primrec.snd).to₂
  unfold restrictedEffectiveSampledRunStepInput
  unfold restrictedEffectiveRebuildSuffixInput
  exact listCode_primrec.comp
    (Primrec.list_cons.comp hpredecessor
      (Primrec.list_cons.comp hliveAtQ
        (Primrec.list_cons.comp (listCode_primrec.comp hsuffixBits)
          (Primrec.list_cons.comp (primrecNatBits.comp Primrec.fst)
            (Primrec.const [])))))

/-- The decoded size list is computable jointly in code and parameters. -/
lemma restrictedAnchoredSizesFromCode_computable_all :
    Computable (fun p : ((BitString × ℕ) × ℕ) × ℕ =>
      restrictedAnchoredSizesFromCode p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hsizes : Computable (fun p : ((BitString × ℕ) × ℕ) × ℕ =>
      restrictedEffectiveSampledSizes p.1.1.1 p.1.1.2 p.1.2) :=
    restrictedEffectiveSampledSizes_computable_all.comp
      (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.fst))
  have hhead : Computable (fun p : ((BitString × ℕ) × ℕ) × ℕ => 2 ^ p.2) :=
    twoPow_primrec.to_comp.comp Computable.snd
  unfold restrictedAnchoredSizesFromCode
  exact Computable.list_cons.comp hhead hsizes

/-- Packed-input anchored initializer: the grid code rides in the first
component, the four numeric parameters in one `Nat.pair` tower.  Every
computability step is built from primitives at pair arity, so no large
`Primcodable` product instances enter elaboration. -/
lemma restrictedAnchoredInitialFromCode_partrec_packed
    (𝒜 : DescriptionFamily) :
    Partrec (fun q : BitString × ℕ =>
      restrictedAnchoredInitialFromCode 𝒜 (Nat.unpair q.2).1 q.1
        (Nat.unpair (Nat.unpair q.2).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2) := by
  have hq0 : Primrec (fun q : BitString × ℕ => (Nat.unpair q.2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hgs : Primrec (fun q : BitString × ℕ =>
      (Nat.unpair (Nat.unpair q.2).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hΔ : Primrec (fun q : BitString × ℕ =>
      (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))
  have hamb : Primrec (fun q : BitString × ℕ =>
      (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))
  have hAcode : Primrec (fun q : BitString × ℕ =>
      (codedUniformOn
        (stringsOfLength (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2)
        (codedStringsOfLength_nonempty _)).code) :=
    fullCubeUniformCode_primrec.comp hamb
  have hsizes : Primrec (fun q : BitString × ℕ =>
      (List.range ((Nat.unpair (Nat.unpair q.2).2).1 + 1)).map (fun s =>
        2 ^ ((decode_restrictedCurveGridCode_sample q.1 s).2 -
          ((Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1 + 1)))) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp hgs))
      ((twoPow_primrec.comp (Primrec.nat_sub.comp
        (Primrec.snd.comp
          (decode_restrictedCurveGridCode_sample_primrec.comp
            (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)))
        (Primrec.succ.comp (hΔ.comp Primrec.fst)))).to₂)
  have hsizesBits : Primrec (fun q : BitString × ℕ =>
      ((List.range ((Nat.unpair (Nat.unpair q.2).2).1 + 1)).map (fun s =>
        2 ^ ((decode_restrictedCurveGridCode_sample q.1 s).2 -
          ((Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1 + 1)))).map
        Nat.bits) :=
    Primrec.list_map hsizes (primrecNatBits.comp Primrec.snd).to₂
  have hinput : Primrec (fun q : BitString × ℕ =>
      restrictedEffectiveRebuildSuffixInput
        (codedUniformOn
          (stringsOfLength (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2)
          (codedStringsOfLength_nonempty _)).code
        (codedUniformOn
          (stringsOfLength (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2)
          (codedStringsOfLength_nonempty _)).code
        (restrictedEffectiveSampledSizes q.1
          (Nat.unpair (Nat.unpair q.2).2).1
          (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1)
        (Nat.unpair q.2).1) := by
    unfold restrictedEffectiveRebuildSuffixInput
      restrictedEffectiveSampledSizes
    exact listCode_primrec.comp
      (Primrec.list_cons.comp hAcode
        (Primrec.list_cons.comp hAcode
          (Primrec.list_cons.comp (listCode_primrec.comp hsizesBits)
            (Primrec.list_cons.comp (primrecNatBits.comp hq0)
              (Primrec.const [])))))
  have hpost : Computable₂ (fun (q : BitString × ℕ) (output : BitString) =>
      restrictedEffectiveSampledStateCode
        (codedUniformOn
          (stringsOfLength (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2)
          (codedStringsOfLength_nonempty _)).code
        (decodeListCode output)) := by
    unfold restrictedEffectiveSampledStateCode
    exact ((listCode_primrec.comp
      (Primrec.list_cons.comp (hAcode.comp Primrec.fst)
        (Primrec.list_cons.comp
          (listCode_primrec.comp (decodeListCode_primrec.comp Primrec.snd))
          (Primrec.const [])))).to_comp).to₂
  exact (Partrec.map
    ((restrictedEffectiveRebuildSuffix_partrec 𝒜).comp hinput.to_comp)
    hpost).of_eq (fun _ => rfl)

/-- The anchored initializer is partial-recursive jointly in its explicit
overhead and all grid-derived numeric parameters. -/
lemma restrictedAnchoredInitialFromCode_partrec_all
    (𝒜 : DescriptionFamily) :
    Partrec (fun p : (((ℕ × BitString) × ℕ) × ℕ) × ℕ =>
      restrictedAnchoredInitialFromCode 𝒜 p.1.1.1.1 p.1.1.1.2
        p.1.1.2 p.1.2 p.2) := by
  have hpack : Computable (fun p : (((ℕ × BitString) × ℕ) × ℕ) × ℕ =>
      ((p.1.1.1.2 : BitString),
        Nat.pair p.1.1.1.1 (Nat.pair p.1.1.2 (Nat.pair p.1.2 p.2)))) :=
    Computable.pair
      (Computable.snd.comp (Computable.fst.comp
        (Computable.fst.comp Computable.fst)))
      (Primrec₂.natPair.to_comp.comp
        (Computable.fst.comp (Computable.fst.comp
          (Computable.fst.comp Computable.fst)))
        (Primrec₂.natPair.to_comp.comp
          (Computable.snd.comp (Computable.fst.comp Computable.fst))
          (Primrec₂.natPair.to_comp.comp
            (Computable.snd.comp Computable.fst)
            Computable.snd)))
  exact ((restrictedAnchoredInitialFromCode_partrec_packed 𝒜).comp
    hpack).of_eq (fun p => by simp)

end PrimcodableOpaque

end Kolmogorov
