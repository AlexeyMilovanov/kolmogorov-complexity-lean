import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRebuild
import KolmogorovMathlib.Restricted.FamilyCurve.SizeSchedule
import KolmogorovMathlib.Restricted.FamilyCurve.CoupledRun
import KolmogorovMathlib.Restricted.FamilyCurve.BadStream
import KolmogorovMathlib.Foundation.UnboundedSearch
import KolmogorovMathlib.Restricted.FamilyCurve.RunCoding
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun.StateCoding

/-!
# Computability of the restricted sampled run

This module assembles the computable ingredients of the sampled restricted-family construction.
It defines the fresh bad-code batches and the partial run
`restrictedEffectiveSampledRun`, and proves uniform computability of its sizes, initial state,
bad-batch lookup and iteration.

`DecodesToRestrictedSampledRunState` relates an encoded effective state to the mathematical
sampled-run state. The final initial-state lemmas construct the anchored model codes and shifted
live codes and prove that the encoded initial state satisfies this relation and the required
density bounds.

The step semantics and preservation contract are proved in `Part02` and `Part03`.
-/

namespace Kolmogorov
open Nat.Partrec (Code)

/-- Prefix monotonicity identifies the next stream as the old stream followed
by exactly `restrictedSampledNewBadBatch`. -/
lemma restrictedSampledNewBadBatch_append (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ time : ℕ) :
    restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ time ++
        restrictedSampledNewBadBatch c gridCode 𝒜 gridSteps Δ time =
      restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ (time + 1) := by
  obtain ⟨suffix, hsuffix⟩ :=
    restrictedSampledBadCodeStream_mono c gridCode 𝒜 gridSteps Δ time
  unfold restrictedSampledNewBadBatch
  rw [← hsuffix]
  simp

/-- Every code in the appended batch is genuinely fresh. -/
lemma restrictedSampledNewBadBatch_fresh (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ time : ℕ) {w : BitString}
    (hw : w ∈ restrictedSampledNewBadBatch c gridCode 𝒜 gridSteps Δ time) :
    w ∉ restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ time := by
  have hnodup := restrictedSampledBadCodeStream_nodup c gridCode 𝒜
    gridSteps Δ (time + 1)
  rw [← restrictedSampledNewBadBatch_append c gridCode 𝒜 gridSteps Δ time]
    at hnodup
  intro hold
  exact (List.nodup_append.mp hnodup).2.2 w hold w hw rfl

/-- The first batch is the stage-zero stream; subsequent batches are the new
suffix supplied by `restrictedSampledNewBadBatch`.  Thus every stream event is
processed, including events already visible at stage zero. -/
def restrictedSampledBadBatchAt (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) : ℕ → List BitString
  | 0 => restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ 0
  | time + 1 =>
      restrictedSampledNewBadBatch c gridCode 𝒜 gridSteps Δ time

/-- Chronological partial-recursive run.  Time zero is the initial state; the
transition to time `time + 1` processes `restrictedSampledBadBatchAt time`. -/
noncomputable def restrictedEffectiveSampledRun
    (𝒜 : DescriptionFamily) (c : Code) (gridCode : BitString)
    (ambientLength gridSteps Δ time : ℕ) : Part BitString :=
  let q0 := 𝒜.overhead ambientLength
  let sizes := restrictedEffectiveSampledSizes gridCode gridSteps Δ
  Nat.rec (motive := fun _ => Part BitString)
    (restrictedEffectiveSampledInitialState 𝒜 ambientLength sizes)
    (fun stage current => current.bind (fun state =>
      restrictedEffectiveSampledRunProcess 𝒜 q0 sizes state
        (restrictedSampledBadBatchAt c gridCode 𝒜.toPre gridSteps Δ stage)))
    time

/-- The requested cardinalities are computable in the coded grid, uniformly in the fixed number
of steps and the offset. -/
lemma restrictedEffectiveSampledSizes_computable_uniform
    (gridSteps Δ : ℕ) :
    Computable (fun gridCode : BitString =>
      restrictedEffectiveSampledSizes gridCode gridSteps Δ) := by
  unfold restrictedEffectiveSampledSizes;
  have h_computable : Computable (fun (p : BitString × ℕ) =>
      2 ^ ((decodeRestrictedCurveGridCodeSample p.1 p.2).2 - (Δ + 1))) := by
    have h_computable : Computable (fun (p : BitString × ℕ) =>
        (decodeRestrictedCurveGridCodeSample p.1 p.2).2 - (Δ + 1)) := by
      have h_computable : Computable (fun (p : BitString × ℕ) =>
          (decodeRestrictedCurveGridCodeSample p.1 p.2).2) := by
        exact Computable.snd.comp ( decode_restrictedCurveGridCode_sample_computable );
      have h_computable : Computable (fun (p : ℕ × ℕ) => p.1 - p.2) :=
        Primrec.nat_sub.to_comp
      exact (h_computable.comp
        (Computable.pair
          ‹Computable fun p : BitString × ℕ => (decodeRestrictedCurveGridCodeSample p.1 p.2).2›
          (Computable.const (Δ + 1)))).of_eq (fun _ => rfl)
    exact Computable.pow2.comp h_computable;
  generalize gridSteps + 1 = k
  induction k with
  | zero =>
      simp_all +decide only [List.range_zero, List.map_nil]
      exact Computable.const []
  | succ gridSteps ih =>
      simp_all +decide only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
      have h_append : Computable (fun (p : List ℕ × ℕ) => p.1 ++ [p.2]) := by
        exact (Computable.list_append.comp ( Computable.fst )
          ( Computable.list_cons.comp ( Computable.snd )
            ( Computable.const [] ) )).of_eq (fun _ => rfl)
      exact (h_append.comp ( Computable.pair ih ( h_computable.comp
        ( Computable.pair ( Computable.id )
          ( Computable.const gridSteps ) ) ) )).of_eq (fun _ => rfl)

/-- Assembling the input of the initial state from a coded grid is computable. -/
lemma restrictedEffectiveSampledInitialState_input_computable
    (𝒜 : DescriptionFamily) (ambientLength gridSteps Δ : ℕ) :
    Computable (fun gridCode : BitString =>
      let Acode := (codedUniformOn (stringsOfLength ambientLength)
        (codedStringsOfLength_nonempty ambientLength)).code
      restrictedEffectiveRebuildSuffixInput Acode Acode
        (restrictedEffectiveSampledSizes gridCode gridSteps Δ)
        (𝒜.overhead ambientLength)) := by
  have h_listCode_primrec : Computable (fun (l : List BitString) => listCode l) :=
    listCode_primrec.to_comp
  have h_listCode : Computable (fun (l : List BitString) => listCode l) :=
    listCode_primrec.to_comp
  have hc1 : Computable (fun _ : BitString => (codedUniformOn (stringsOfLength ambientLength)
      (codedStringsOfLength_nonempty ambientLength)).code) := Computable.const _
  have h_map : Computable (fun (l : List ℕ) => List.map Nat.bits l) :=
    Primrec.to_comp (Primrec.list_map Primrec.id (primrec_natBits.comp Primrec.snd))
  have hs : Computable (fun g : BitString => restrictedEffectiveSampledSizes g gridSteps Δ) :=
    restrictedEffectiveSampledSizes_computable_uniform gridSteps Δ
  have hl : Computable (fun g : BitString => listCode (List.map Nat.bits (
    restrictedEffectiveSampledSizes g gridSteps Δ))) :=
      (Computable.comp h_listCode (Computable.comp h_map hs)).of_eq (fun _ => rfl)
  have hc2 : Computable (fun _ : BitString => (𝒜.overhead ambientLength).bits) :=
    Computable.const _
  have hc : Computable (fun g : BitString =>
    (codedUniformOn (stringsOfLength ambientLength)
      (codedStringsOfLength_nonempty ambientLength)).code ::
    (codedUniformOn (stringsOfLength ambientLength)
      (codedStringsOfLength_nonempty ambientLength)).code ::
    listCode (List.map Nat.bits (restrictedEffectiveSampledSizes g gridSteps Δ)) ::
    (𝒜.overhead ambientLength).bits :: []) :=
    Computable₂.comp Computable.list_cons hc1 (Computable₂.comp Computable.list_cons hc1 (
      Computable₂.comp Computable.list_cons hl (
        Computable₂.comp Computable.list_cons hc2 (Computable.const [])
      )))
  exact (Computable.comp h_listCode hc).of_eq (fun x => rfl)

/-- Reading the initial state off the output is computable. -/
lemma restrictedEffectiveSampledInitialState_post_computable
    (ambientLength : ℕ) :
    Computable (fun output : BitString =>
      let Acode := (codedUniformOn (stringsOfLength ambientLength)
        (codedStringsOfLength_nonempty ambientLength)).code
      let modelCodes := (decodeListCode output).tail
      let rootLiveCode := restrictedLiveIntersectionCode Acode
        (modelCodes.headD [])
      restrictedEffectiveSampledStateCode rootLiveCode modelCodes) := by
  apply Computable.comp
  · exact listCode_computable
  · have h_restrictedLiveIntersectionCode :
        Primrec (fun (p : BitString × BitString) => restrictedLiveIntersectionCode p.1 p.2) := by
      exact restrictedLiveIntersectionCode_primrec
    have h_decodeListCode : Primrec (fun (a : BitString) => decodeListCode a) := by
      exact decodeListCode_primrec
    have h_encodeList : Primrec (fun (l : List BitString) => listCode l) := by
      exact listCode_primrec
    have h_stateFields : Primrec (fun (l : List BitString) =>
        [restrictedLiveIntersectionCode
            (codedUniformOn (stringsOfLength ambientLength)
              (codedStringsOfLength_nonempty ambientLength)).code (l.headD []),
          listCode l]) := by
      have h_rootLiveCode : Primrec (fun (l : List BitString) =>
          restrictedLiveIntersectionCode
            (codedUniformOn (stringsOfLength ambientLength)
              (codedStringsOfLength_nonempty ambientLength)).code (l.headD [])) := by
        have h_headD : Primrec (fun (l : List BitString) => l.headD []) := by
          have h : Primrec (fun (l : List BitString) => l.headI) := Primrec.list_headI
          exact h.of_eq (fun l => by cases l <;> rfl)
        exact (h_restrictedLiveIntersectionCode.comp
          (Primrec.const _ |> Primrec.pair <| h_headD)).of_eq (fun _ => rfl)
      exact Primrec.list_cons.comp h_rootLiveCode
        (Primrec.list_cons.comp h_encodeList (Primrec.const []));
    exact ((h_stateFields.comp (Primrec.list_tail.comp h_decodeListCode)).to_comp).of_eq
      (fun _ => rfl)

/-- The initial state of the sampled run is partial computable in the coded grid. -/
lemma restrictedEffectiveSampledInitialState_partrec_uniform
    (𝒜 : DescriptionFamily) (ambientLength gridSteps Δ : ℕ) :
    Partrec (fun gridCode : BitString =>
      restrictedEffectiveSampledInitialState 𝒜 ambientLength
        (restrictedEffectiveSampledSizes gridCode gridSteps Δ)) := by
  refine Partrec.map ?_ ?_
  · have h1 := @restrictedEffectiveSampledInitialState_input_computable;
    exact Partrec.comp (restrictedEffectiveRebuildSuffix_partrec 𝒜)
      (h1 𝒜 ambientLength gridSteps Δ)
  · exact (Computable.comp
      (restrictedEffectiveSampledInitialState_post_computable ambientLength)
        Computable.snd).of_eq (fun _ => rfl)

/-- The bad batch at a sampled scale is computable jointly in the coded grid and the scale. -/
lemma restrictedSampledBadBatchAt_computable_uniform
    (c : Code) (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) :
    Computable (fun p : BitString × ℕ =>
      restrictedSampledBadBatchAt c p.1 𝒜 gridSteps Δ p.2) := by
  have hstream : Computable (fun p : BitString × ℕ =>
      restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ p.2) :=
    restrictedSampledBadCodeStream_computable_uniform c 𝒜 gridSteps Δ
  have hstreamSucc : Computable (fun p : BitString × ℕ =>
      restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ (p.2 + 1)) :=
    hstream.comp
      (Computable.pair Computable.fst (Computable.succ.comp Computable.snd))
  have hbatch : Computable (fun p : BitString × ℕ =>
      (restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ (p.2 + 1)).drop
        (restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ p.2).length) := by
    have hdropLength : Computable (fun p : List BitString × List BitString =>
        p.1.drop p.2.length) := by
      have hdrop : Computable (fun p : List BitString × ℕ => p.1.drop p.2) := by
        have hdropPrimrec : Primrec₂ (fun (n : ℕ) (l : List BitString) =>
            l.drop n) := Primrec.list_drop (α := BitString)
        have hdropPrimrec2 : Primrec₂ (fun (l : List BitString) (n : ℕ) =>
            l.drop n) := Primrec₂.comp hdropPrimrec Primrec.snd Primrec.fst
        exact (hdropPrimrec2.to_comp).of_eq (fun _ => rfl)
      exact (hdrop.comp
        (Computable.fst.pair (Computable.list_length.comp Computable.snd))).of_eq (fun _ => rfl)
    exact (hdropLength.comp (Computable.pair hstreamSucc hstream)).of_eq (fun _ => rfl)
  have hc1 : Computable (fun p : BitString × ℕ => p.2) := Computable.snd
  have hc2 : Computable (fun p : BitString × ℕ =>
      restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ 0) :=
    (hstream.comp (Computable.pair Computable.fst (Computable.const 0))).of_eq (fun _ => rfl)
  have hc3 : Computable₂ (fun (p : BitString × ℕ) (n : ℕ) =>
      List.drop (restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ n).length
        (restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ (n + 1))) :=
    (hbatch.comp (Computable.pair (Computable.fst.comp Computable.fst)
      Computable.snd)).to₂.of_eq (fun _ => rfl)
  have h_cases := Computable.nat_casesOn
    (f := fun p : BitString × ℕ => p.2)
    (g := fun p => restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ 0)
    (h := fun p n =>
      List.drop (restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ n).length
        (restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ (n + 1)))
    hc1 hc2 hc3
  exact h_cases.of_eq (fun ⟨gridCode, time⟩ => by cases time <;> rfl)

/-- The executor is one uniform partial-recursive procedure in the encoded
grid and time.  Termination is deliberately separated into the validity
specifications below. -/
lemma restrictedEffectiveSampledRun_partrec_uniform
    (𝒜 : DescriptionFamily) (c : Code)
    (ambientLength gridSteps Δ : ℕ) :
    Partrec (fun p : BitString × ℕ =>
      restrictedEffectiveSampledRun 𝒜 c p.1 ambientLength gridSteps Δ p.2) := by
  let q0 := 𝒜.overhead ambientLength
  have hcount : Computable (fun p : BitString × ℕ => p.2) :=
    Computable.snd
  have hinitial : Partrec (fun p : BitString × ℕ =>
      restrictedEffectiveSampledInitialState 𝒜 ambientLength
        (restrictedEffectiveSampledSizes p.1 gridSteps Δ)) :=
    ((restrictedEffectiveSampledInitialState_partrec_uniform
      𝒜 ambientLength gridSteps Δ).comp
        (Computable.fst : Computable (fun p : BitString × ℕ => p.1))).of_eq fun _ => rfl
  have hsizes : Computable (fun q :
      (BitString × ℕ) × (ℕ × BitString) =>
      restrictedEffectiveSampledSizes q.1.1 gridSteps Δ) :=
    ((restrictedEffectiveSampledSizes_computable_uniform gridSteps Δ).comp
      ((Computable.fst.comp Computable.fst) : Computable (fun q :
        (BitString × ℕ) × (ℕ × BitString) => q.1.1))).of_eq fun _ => rfl
  have hbatch : Computable (fun q :
      (BitString × ℕ) × (ℕ × BitString) =>
      restrictedSampledBadBatchAt c q.1.1 𝒜.toPre gridSteps Δ q.2.1) := by
    have hgrid : Computable (fun q :
        (BitString × ℕ) × (ℕ × BitString) => q.1.1) :=
      Computable.fst.comp Computable.fst
    have htime : Computable (fun q :
        (BitString × ℕ) × (ℕ × BitString) => q.2.1) :=
      Computable.fst.comp Computable.snd
    exact ((restrictedSampledBadBatchAt_computable_uniform c 𝒜.toPre gridSteps Δ).comp
      (Computable.pair hgrid htime)).of_eq fun _ => rfl
  have hinput : Computable (fun q :
      (BitString × ℕ) × (ℕ × BitString) =>
      (restrictedEffectiveSampledSizes q.1.1 gridSteps Δ,
        q.2.2,
        restrictedSampledBadBatchAt c q.1.1 𝒜.toPre gridSteps Δ q.2.1)) := by
    have hstate : Computable (fun q :
        (BitString × ℕ) × (ℕ × BitString) => q.2.2) :=
      Computable.snd.comp Computable.snd
    exact (Computable.pair hsizes
      (Computable.pair hstate hbatch)).of_eq fun _ => rfl
  have hnext : Partrec₂ (fun p : BitString × ℕ =>
      fun indexed : ℕ × BitString =>
        restrictedEffectiveSampledRunProcess 𝒜 q0
          (restrictedEffectiveSampledSizes p.1 gridSteps Δ)
          indexed.2
          (restrictedSampledBadBatchAt c p.1 𝒜.toPre gridSteps Δ indexed.1)) :=
    ((restrictedEffectiveSampledRunProcess_partrec 𝒜 q0).comp hinput).to₂
  exact (Partrec.nat_rec hcount hinitial hnext).of_eq fun _ => rfl

/-- A code represents a sampled mathematical state when it contains all model
codes and the live codes reconstructed from its root agree at every scale. -/
def DecodesToRestrictedSampledRunState
    {𝒜 : DescriptionFamily} {N ambientLength overheadBound : ℕ}
    {t : ℕ → ℕ} (stateCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t) : Prop :=
  let rootLiveCode := restrictedSelectorField stateCode 0
  let modelCodes := decodeListCode (restrictedSelectorField stateCode 1)
  let liveCodes := restrictedEffectiveRebuildLiveCodes rootLiveCode modelCodes
  modelCodes.length = N + 1 ∧
    ∀ s ≤ N,
      decodeCoverCodeList (modelCodes.getD s []) =
          canonicalFinsetList (state.B s) ∧
      decodeCoverCodeList (liveCodes.getD s []) =
          canonicalFinsetList (state.live s)
/-- A size schedule whose entries are the powers `2 ^ t s`, `s ≤ N`, has positive entries. -/
private lemma sizeSchedule_pos_of_powers
    (N : ℕ) (t : ℕ → ℕ) (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s) :
    ∀ i < sizes.length, 0 < sizes.getD i 0 := by
  intro i hi
  have hiN : i ≤ N := by omega
  rw [hpowers i hiN]
  positivity

/-- The first entry `2 ^ t 0` of the size schedule is at most the full-cube size
`2 ^ ambientLength` whenever `t 0 ≤ ambientLength`. -/
private lemma sizeSchedule_head_le_of_powers
    (N ambientLength : ℕ) (t : ℕ → ℕ) (sizes : List ℕ)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (htop : t 0 ≤ ambientLength) :
    sizes.getD 0 0 ≤ 2 ^ ambientLength := by
  rw [hpowers 0 (Nat.zero_le N)]
  exact Nat.pow_le_pow_right (by decide) htop

/-- A size schedule whose entries are the powers `2 ^ t s` is antitone as soon as the
exponents `t` are. -/
private lemma sizeSchedule_antitone_of_powers
    (N : ℕ) (t : ℕ → ℕ) (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : IsPowerSizeSchedule sizes N t)
    (hmono : ExponentsAntitone t N) :
    ∀ i, i + 1 < sizes.length → sizes.getD (i + 1) 0 ≤ sizes.getD i 0 := by
  intro i hi
  have hiN : i < N := by omega
  rw [hpowers (i + 1) (by omega), hpowers i (by omega)]
  exact Nat.pow_le_pow_right (by decide) (hmono i hiN)

/-- The model-code list of an anchored rebuild: the predecessor code of the anchor, the model
code of the first stage, and the model codes of the remaining stages. -/
def restrictedAnchoredModelCodes (predecessorCode firstModelCode : BitString)
    (remainingModelCodes : List BitString) : List BitString :=
  predecessorCode :: firstModelCode :: remainingModelCodes

/-- The live-code list of an anchored rebuild read from the first stage on: the rebuild of the
model codes `firstModelCode :: remainingModelCodes` started at the root live code
`restrictedLiveIntersectionCode Acode firstModelCode`. -/
noncomputable def restrictedShiftedLiveCodes (Acode firstModelCode : BitString)
    (remainingModelCodes : List BitString) : List BitString :=
  restrictedEffectiveRebuildLiveCodes (restrictedLiveIntersectionCode Acode firstModelCode)
    (firstModelCode :: remainingModelCodes)

/-- The live codes of the rebuild at stages `s` and `s + 1` decode to `Cprev` and to
`Cprev ∩ Bnext`. -/
private lemma restrictedEffectiveSampledInitialState_live_step
    (Acode predecessorCode firstModelCode : BitString) (remainingModelCodes : List BitString)
    (N s : ℕ) (hsN : s < N) (hremainingLength : remainingModelCodes.length = N)
    (Cprev Bnext : Finset BitString)
    (hCprevCode : decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes Acode
      (restrictedAnchoredModelCodes predecessorCode firstModelCode
        remainingModelCodes)).getD (s + 1) []) = canonicalFinsetList Cprev)
    (hBnextCode : decodeCoverCodeList ((restrictedAnchoredModelCodes predecessorCode
      firstModelCode remainingModelCodes).getD (s + 2) []) = canonicalFinsetList Bnext) :
    decodeCoverCodeList
        ((restrictedShiftedLiveCodes Acode firstModelCode remainingModelCodes).getD s []) =
      canonicalFinsetList Cprev ∧
    decodeCoverCodeList ((restrictedShiftedLiveCodes Acode firstModelCode
        remainingModelCodes).getD (s + 1) []) = canonicalFinsetList (Cprev ∩ Bnext) := by
  set liveCodes := restrictedShiftedLiveCodes Acode firstModelCode remainingModelCodes
  have h1 : decodeCoverCodeList (liveCodes.getD s []) = canonicalFinsetList Cprev := hCprevCode
  have h2 : decodeCoverCodeList (liveCodes.getD (s + 1) []) =
      canonicalFinsetList (Cprev ∩ Bnext) := by
    have hliveAlign : liveCodes.getD (s + 1) [] =
        (restrictedEffectiveRebuildLiveCodes Acode
          (predecessorCode :: firstModelCode :: remainingModelCodes)).getD (s + 2) [] := rfl
    rw [hliveAlign, restrictedEffectiveRebuildLiveCodes_succ_getD Acode
      (predecessorCode :: firstModelCode :: remainingModelCodes) (s + 1) (by
        simp [hremainingLength]
        omega)]
    exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext hCprevCode hBnextCode
  exact ⟨h1, h2⟩

/-- The density inequality of the size schedule, rewritten in the powers `2 ^ t s` and with the
overhead factor doubled: `2 ^ t (s+1) * |Cprev| ≤ 2 * overhead * 2 ^ t s * |Cprev ∩ Bnext|`. -/
private lemma restrictedEffectiveSampledInitialState_density_le
    (𝒜 : DescriptionFamily) (ambientLength : ℕ) (sizes : List ℕ) (t : ℕ → ℕ)
    (N s : ℕ) (hsN : s < N) (Cprev Bnext : Finset BitString)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (hdensity : sizes.getD (s + 1) 0 * Cprev.card ≤
      (𝒜.overhead ambientLength * sizes.getD s 0) * (Bnext ∩ Cprev).card) :
    2 ^ t (s + 1) * Cprev.card ≤
      (2 * 𝒜.overhead ambientLength * 2 ^ t s) * (Cprev ∩ Bnext).card := by
  have hs1 : s + 1 ≤ N := by omega
  have hs0 : s ≤ N := by omega
  rw [← hpowers s hs0, ← hpowers (s + 1) hs1]
  have hdensity' : sizes.getD (s + 1) 0 * Cprev.card ≤
      (𝒜.overhead ambientLength * sizes.getD s 0) * (Cprev ∩ Bnext).card := by
    simpa [Finset.inter_comm] using hdensity
  exact hdensity'.trans (by gcongr; omega)

/-- A decreasing positive size schedule makes the initial full-cube search
terminate and decode to a genuine sampled state. -/
lemma restrictedEffectiveSampledInitialState_spec
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (htop : t 0 ≤ ambientLength)
    (hmono : ∀ s < N, t (s + 1) ≤ t s) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength) t,
        restrictedEffectiveSampledInitialState 𝒜 ambientLength sizes =
            Part.some output ∧
        DecodesToRestrictedSampledRunState output state := by
  let A := stringsOfLength ambientLength
  let hA : A.Nonempty := codedStringsOfLength_nonempty ambientLength
  let Acode := (codedUniformOn A hA).code
  have hAcode : decodeCoverCodeList Acode = canonicalFinsetList A :=
    decodeCoverCodeList_code A hA
  have hAmem : 𝒜.mem A := 𝒜.fullCube ambientLength
  have hAsub : A ⊆ A := Finset.Subset.rfl
  have hAlength : ∀ x ∈ A, x.length = ambientLength := fun x hx =>
    (mem_stringsOfLength ambientLength x).mp hx
  have hAcard : A.card ≤ 2 ^ ambientLength := by
    rw [show A = stringsOfLength ambientLength from rfl, card_stringsOfLength]
  have hsizes_pos := sizeSchedule_pos_of_powers N t sizes hlen hpowers
  have hsizes_head := sizeSchedule_head_le_of_powers N ambientLength t sizes
    hpowers htop
  have hsizes_mono := sizeSchedule_antitone_of_powers N t sizes hlen hpowers hmono
  obtain ⟨rawOutput, Afinal, Cfinal, codes, hrun, hrawOutput,
      htrace, hcodesLength, hsteps⟩ :=
    restrictedEffectiveRebuildSuffix_decodes_density 𝒜 Acode Acode sizes
      (𝒜.overhead ambientLength) ambientLength (2 ^ ambientLength)
      A A hAcode hAcode rfl hAmem hAsub hAlength hAcard
      hsizes_pos hsizes_head hsizes_mono
  rw [hlen] at hcodesLength
  have hcodes_ne : codes ≠ [] := by
    intro hnil; rw [hnil] at hcodesLength; simp at hcodesLength
  obtain ⟨predecessorCode, tail, hcodes⟩ := List.exists_cons_of_ne_nil hcodes_ne
  subst codes
  have htail_ne : tail ≠ [] := by
    intro hnil; rw [hnil] at hcodesLength; simp at hcodesLength
  obtain ⟨firstModelCode, remainingModelCodes, htail⟩ := List.exists_cons_of_ne_nil htail_ne
  subst tail
  have hremainingLength : remainingModelCodes.length = N := by
    simp only [List.length_cons] at hcodesLength; omega
  let modelCodes := firstModelCode :: remainingModelCodes
  let rootLiveCode := restrictedLiveIntersectionCode Acode firstModelCode
  let liveCodes := restrictedEffectiveRebuildLiveCodes rootLiveCode modelCodes
  let stateCode := restrictedEffectiveSampledStateCode rootLiveCode modelCodes
  have hmodelLength : modelCodes.length = N + 1 := by simp [modelCodes, hremainingLength]
  have hmodelAlign : ∀ s, modelCodes.getD s [] =
      (predecessorCode :: firstModelCode :: remainingModelCodes).getD (s + 1) [] := by
    intro s; cases s <;> simp [modelCodes]
  have hliveAlign : ∀ s, liveCodes.getD s [] =
      (restrictedEffectiveRebuildLiveCodes Acode
        (predecessorCode :: firstModelCode :: remainingModelCodes)).getD (s + 1) [] := fun _ => rfl
  have hstepData : ∀ s ≤ N, ∃ Cprev Bnext : Finset BitString,
      decodeCoverCodeList (modelCodes.getD s []) = canonicalFinsetList Bnext ∧
      decodeCoverCodeList (liveCodes.getD s []) = canonicalFinsetList (Cprev ∩ Bnext) ∧
      𝒜.mem Bnext ∧ Bnext.card ≤ sizes.getD s 0 ∧
      (∀ x ∈ Cprev, x.length = ambientLength) := by
    intro s hs
    obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode, hBnextCode, hBprevMem, hBprevCard,
      hCprevSub, hCprevLength, hBnextMem, hBnextCard, hdensity⟩ :=
      hsteps s (by rw [hlen]; exact Nat.lt_succ_of_le hs)
    refine ⟨Cprev, Bnext, ?_, ?_, hBnextMem, hBnextCard, hCprevLength⟩
    · rw [hmodelAlign]; exact hBnextCode
    · rw [hliveAlign, restrictedEffectiveRebuildLiveCodes_succ_getD Acode
          (predecessorCode :: firstModelCode :: remainingModelCodes) s (by
            simp [hremainingLength]; omega)]
      exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext hCprevCode hBnextCode
  let decodedModels : ℕ → Finset BitString := fun s =>
    (decodeCoverCodeList (modelCodes.getD s [])).toFinset
  let decodedLive : ℕ → Finset BitString := fun s =>
    (decodeCoverCodeList (liveCodes.getD s [])).toFinset
  have hdecoded : ∀ s ≤ N,
      decodeCoverCodeList (modelCodes.getD s []) = canonicalFinsetList (decodedModels s) ∧
      decodeCoverCodeList (liveCodes.getD s []) = canonicalFinsetList (decodedLive s) := by
    intro s hs
    obtain ⟨Cprev, Bnext, hBcode, hliveCode, hBmem, hBcard, hCprevLength⟩ := hstepData s hs
    constructor
    · dsimp [decodedModels]; rw [hBcode, canonicalFinsetList_toFinset]
    · dsimp [decodedLive]; rw [hliveCode, canonicalFinsetList_toFinset]
  let state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t :=
    { B := decodedModels
      live := decodedLive
      mem_family := by
        intro s hs
        obtain ⟨Cprev, Bnext, hBcode, hliveCode, hBmem, hBcard, hCprevLength⟩ := hstepData s hs
        dsimp [decodedModels]; rw [hBcode, canonicalFinsetList_toFinset]; exact hBmem
      size_bound := by
        intro s hs
        obtain ⟨Cprev, Bnext, hBcode, hliveCode, hBmem, hBcard, hCprevLength⟩ := hstepData s hs
        dsimp [decodedModels]; rw [hBcode, canonicalFinsetList_toFinset]
        rw [hpowers s hs] at hBcard; exact hBcard
      live_subset := by
        intro s hs
        obtain ⟨Cprev, Bnext, hBcode, hliveCode, hBmem, hBcard, hCprevLength⟩ := hstepData s hs
        dsimp [decodedLive, decodedModels]
        rw [hliveCode, hBcode, canonicalFinsetList_toFinset, canonicalFinsetList_toFinset]
        exact Finset.inter_subset_right
      live_ambient := by
        intro s hs x hx
        obtain ⟨Cprev, Bnext, hBcode, hliveCode, hBmem, hBcard, hCprevLength⟩ := hstepData s hs
        dsimp [decodedLive] at hx; rw [hliveCode, canonicalFinsetList_toFinset] at hx
        exact hCprevLength x (Finset.inter_subset_left hx)
      live_monotonic := by
        intro s hsN
        obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode, hBnextCode, hBprevMem, hBprevCard,
          hCprevSub, hCprevLength, hBnextMem, hBnextCard, hdensity⟩ :=
          hsteps (s + 1) (by rw [hlen]; exact Nat.succ_lt_succ hsN)
        obtain ⟨hcurrent, hnext⟩ := restrictedEffectiveSampledInitialState_live_step Acode
          predecessorCode firstModelCode remainingModelCodes N s hsN hremainingLength Cprev Bnext
          hCprevCode hBnextCode
        simp only [restrictedShiftedLiveCodes] at hcurrent hnext
        dsimp [decodedLive]
        rw [hnext, hcurrent, canonicalFinsetList_toFinset, canonicalFinsetList_toFinset]
        exact Finset.inter_subset_left
      density := by
        intro s hsN
        obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode, hBnextCode, hBprevMem, hBprevCard,
          hCprevSub, hCprevLength, hBnextMem, hBnextCard, hdensity⟩ :=
          hsteps (s + 1) (by rw [hlen]; exact Nat.succ_lt_succ hsN)
        obtain ⟨hcurrent, hnext⟩ := restrictedEffectiveSampledInitialState_live_step Acode
          predecessorCode firstModelCode remainingModelCodes N s hsN hremainingLength Cprev Bnext
          hCprevCode hBnextCode
        simp only [restrictedShiftedLiveCodes] at hcurrent hnext
        dsimp [decodedLive]
        rw [hcurrent, hnext, canonicalFinsetList_toFinset, canonicalFinsetList_toFinset]
        exact restrictedEffectiveSampledInitialState_density_le 𝒜 ambientLength sizes t N s hsN
          Cprev Bnext hpowers hdensity }
  refine ⟨stateCode, state, ?_, ?_⟩
  · unfold restrictedEffectiveSampledInitialState
    change Part.map _ (restrictedEffectiveRebuildSuffix 𝒜
      (restrictedEffectiveRebuildSuffixInput Acode Acode sizes (𝒜.overhead ambientLength))) =
      Part.some stateCode
    rw [hrun, Part.map_some, hrawOutput]
    apply congrArg Part.some
    simp only [decodeListCode_listCode, List.tail_cons, List.headD_cons]
    rfl
  · unfold DecodesToRestrictedSampledRunState
    simp only [stateCode, restrictedSelectorField_sampledState_zero,
      restrictedSelectorField_sampledState_one]
    refine ⟨hmodelLength, ?_⟩
    intro s hs
    exact hdecoded s hs

end Kolmogorov


