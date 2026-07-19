import KolmogorovMathlib.Restricted.FamilyCurve.Basic
import KolmogorovMathlib.Restricted.Improving
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

namespace Kolmogorov

open scoped ENNReal
open Nat.Partrec (Code)
open CodedFiniteDistribution

/-- Extracts the parameters `(i_s, j_s)` from the encoded sampled grid. -/
def decode_restrictedCurveGridCode_sample (code : BitString) (s : ℕ) : ℕ × ℕ :=
  let pair := (decodeListCode code).getD s []
  (bitsToNat (decodeFirst pair), bitsToNat (decodeSecond pair))

/-- Grid-coordinate decoding is computable jointly in the encoded grid and
the sample index. -/
lemma decode_restrictedCurveGridCode_sample_computable :
    Computable (fun p : BitString × ℕ =>
      decode_restrictedCurveGridCode_sample p.1 p.2) := by
  have hpair : Primrec (fun p : BitString × ℕ =>
      (decodeListCode p.1).getD p.2 []) :=
    (Primrec.list_getD []).comp
      (decodeListCode_primrec.comp Primrec.fst) Primrec.snd
  exact (Primrec.pair
    (bitsToNat_primrec.comp (decodeFirst_primrec.comp hpair))
    (bitsToNat_primrec.comp (decodeSecond_primrec.comp hpair))).to_comp

/-- Decoding the code of an actual grid recovers its sampled coordinates. -/
@[simp] lemma decode_restrictedCurveGridCode_sample_eq
    {n k gridSteps : ℕ} {t_func : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k gridSteps t_func) {s : ℕ}
    (hs : s ≤ gridSteps) :
    decode_restrictedCurveGridCode_sample (restrictedCurveGridCode grid) s =
      (grid.i s, grid.j s) := by
  unfold decode_restrictedCurveGridCode_sample restrictedCurveGridCode
  rw [decodeListCode_listCode]
  have hslen : s < (List.map
      (fun r => pairCode (Nat.bits (grid.i r)) (Nat.bits (grid.j r)))
      (List.range (gridSteps + 1))).length := by
    simp
    omega
  rw [List.getD_eq_getElem _ _ hslen]
  dsimp only
  have hget : (List.map
      (fun r => pairCode (Nat.bits (grid.i r)) (Nat.bits (grid.j r)))
      (List.range (gridSteps + 1)))[s] =
      pairCode (Nat.bits (grid.i s)) (Nat.bits (grid.j s)) := by
    simp
  rw [hget, decodeFirst_pairCode, decodeSecond_pairCode]
  simp only [bitsToNat_bits]

/-- Raw concatenation of all family descriptions visible at time `t` across
the sampled intervals. -/
def restrictedSampledBadCodesRaw (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) (t : ℕ) : List BitString :=
  (List.range gridSteps).flatMap (fun s =>
    let sample := decode_restrictedCurveGridCode_sample gridCode s
    let next_sample := decode_restrictedCurveGridCode_sample gridCode (s + 1)
    familyStageModelCodesList c next_sample.1 𝒜 (sample.2 - (Δ + 1)) t)

/-- Collects the distinct family descriptions visible up to time `t` across
all sampled intervals. -/
def restrictedSampledBadCodesUpToTime (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) (t : ℕ) : List BitString :=
  (restrictedSampledBadCodesRaw c gridCode 𝒜 gridSteps Δ t).eraseDups

/-- The chronological computable enumeration of bad descriptions.  At every
stage it retains the previous prefix and appends all codes newly visible at the
current family/snapshot stage; `eraseDups` prevents repeated events. -/
def restrictedSampledBadCodeStream (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) : ℕ → List BitString
  | 0 => restrictedSampledBadCodesUpToTime c gridCode 𝒜 gridSteps Δ 0
  | t + 1 => (restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t ++
      restrictedSampledBadCodesUpToTime c gridCode 𝒜 gridSteps Δ (t + 1)).eraseDups

/-- The chronological stream never repeats a code. -/
lemma restrictedSampledBadCodeStream_nodup (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ t : ℕ) :
    (restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t).Nodup := by
  cases t <;> simp [restrictedSampledBadCodeStream,
    restrictedSampledBadCodesUpToTime, nodup_eraseDups_bitString]

/-- The chronological stream grows monotonically with time. -/
lemma restrictedSampledBadCodeStream_mono (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) (t : ℕ) :
    restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t <+:
    restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ (t + 1) := by
  change restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t <+:
    (restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t ++
      restrictedSampledBadCodesUpToTime c gridCode 𝒜 gridSteps Δ (t + 1)).eraseDups
  exact prefix_eraseDups_append_of_nodup _ _
    (restrictedSampledBadCodeStream_nodup c gridCode 𝒜 gridSteps Δ t)

/-- Every raw code arises from a genuine stage description. -/
lemma restrictedSampledBadCodesRaw_sound (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ t : ℕ) {w : BitString}
    (hw : w ∈ restrictedSampledBadCodesRaw c gridCode 𝒜 gridSteps Δ t) :
    ∃ s < gridSteps,
      IsFamilyModelCode 𝒜
        ((decode_restrictedCurveGridCode_sample gridCode s).2 - (Δ + 1)) w := by
  rw [restrictedSampledBadCodesRaw, List.mem_flatMap] at hw
  obtain ⟨s, hs, hw⟩ := hw
  refine ⟨s, List.mem_range.mp hs, ?_⟩
  exact familyStageModelCodesList_sound c
    (decode_restrictedCurveGridCode_sample gridCode (s + 1)).1 𝒜
    ((decode_restrictedCurveGridCode_sample gridCode s).2 - (Δ + 1)) t w hw

/-- Every stage code arises from a genuine stage description. -/
lemma restrictedSampledBadCodesUpToTime_sound (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ t : ℕ) {w : BitString}
    (hw : w ∈ restrictedSampledBadCodesUpToTime c gridCode 𝒜 gridSteps Δ t) :
    ∃ s < gridSteps,
      IsFamilyModelCode 𝒜
        ((decode_restrictedCurveGridCode_sample gridCode s).2 - (Δ + 1)) w := by
  exact restrictedSampledBadCodesRaw_sound c gridCode 𝒜 gridSteps Δ t
    (mem_eraseDups_bitString.mp hw)

/-- Every event in the chronological stream is a genuine family-model code at
the advertised size bound of one sampled interval. -/
lemma restrictedSampledBadCodeStream_sound (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ t : ℕ) {w : BitString}
    (hw : w ∈ restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t) :
    ∃ s < gridSteps,
      IsFamilyModelCode 𝒜
        ((decode_restrictedCurveGridCode_sample gridCode s).2 - (Δ + 1)) w := by
  induction t with
  | zero =>
      exact restrictedSampledBadCodesUpToTime_sound c gridCode 𝒜 gridSteps Δ 0 hw
  | succ t ih =>
      have hw' := mem_eraseDups_bitString.mp hw
      rcases List.mem_append.mp hw' with hprev | hcurrent
      · exact ih hprev
      · exact restrictedSampledBadCodesUpToTime_sound c gridCode 𝒜
          gridSteps Δ (t + 1) hcurrent

/-- The raw enumeration is computable in time for a fixed grid. -/
lemma restrictedSampledBadCodesRaw_computable (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) :
    Computable (fun t =>
      restrictedSampledBadCodesRaw c gridCode 𝒜 gridSteps Δ t) := by
  induction gridSteps with
  | zero =>
      simpa [restrictedSampledBadCodesRaw] using
        (Computable.const ([] : List BitString))
  | succ gridSteps ih =>
      let sample := decode_restrictedCurveGridCode_sample gridCode gridSteps
      let nextSample := decode_restrictedCurveGridCode_sample gridCode (gridSteps + 1)
      have hlast : Computable (fun t =>
          familyStageModelCodesList c nextSample.1 𝒜 (sample.2 - (Δ + 1)) t) :=
        familyStageModelCodesList_computable c nextSample.1 𝒜 (sample.2 - (Δ + 1))
      have happ : Computable (fun t =>
          restrictedSampledBadCodesRaw c gridCode 𝒜 gridSteps Δ t ++
            familyStageModelCodesList c nextSample.1 𝒜
              (sample.2 - (Δ + 1)) t) :=
        Computable.list_append.comp ih hlast
      refine happ.of_eq (fun t => ?_)
      simp [restrictedSampledBadCodesRaw, List.range_succ,
        List.flatMap_append, sample, nextSample]

attribute [local irreducible] decode_restrictedCurveGridCode_sample
  familyStageModelCodesList restrictedSampledBadCodesRaw

/-- Uniform form: the encoded grid is an input to the enumeration algorithm,
not a constant baked into its program. -/
lemma restrictedSampledBadCodesRaw_computable_uniform (c : Code)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) :
    Computable (fun p : BitString × ℕ =>
      restrictedSampledBadCodesRaw c p.1 𝒜 gridSteps Δ p.2) := by
  induction gridSteps with
  | zero =>
      simpa [restrictedSampledBadCodesRaw] using
        (Computable.const ([] : List BitString))
  | succ gridSteps ih =>
      have hsample : Computable (fun p : BitString × ℕ =>
          decode_restrictedCurveGridCode_sample p.1 gridSteps) :=
        decode_restrictedCurveGridCode_sample_computable.comp
          (Computable.pair Computable.fst (Computable.const gridSteps))
      have hnext : Computable (fun p : BitString × ℕ =>
          decode_restrictedCurveGridCode_sample p.1 (gridSteps + 1)) :=
        decode_restrictedCurveGridCode_sample_computable.comp
          (Computable.pair Computable.fst (Computable.const (gridSteps + 1)))
      have hj : Computable (fun p : BitString × ℕ =>
          (decode_restrictedCurveGridCode_sample p.1 gridSteps).2 - (Δ + 1)) :=
        (Primrec.nat_sub.to_comp.comp (Computable.snd.comp hsample)
          (Computable.const (Δ + 1)))
      have hinput : Computable (fun p : BitString × ℕ =>
          ((decode_restrictedCurveGridCode_sample p.1 (gridSteps + 1)).1,
            (decode_restrictedCurveGridCode_sample p.1 gridSteps).2 - (Δ + 1), p.2)) :=
        Computable.pair (Computable.fst.comp hnext)
          (Computable.pair hj Computable.snd)
      have hlast : Computable (fun p : BitString × ℕ =>
          familyStageModelCodesList c
            (decode_restrictedCurveGridCode_sample p.1 (gridSteps + 1)).1 𝒜
            ((decode_restrictedCurveGridCode_sample p.1 gridSteps).2 - (Δ + 1)) p.2) :=
        (familyStageModelCodesList_computable_uniform c 𝒜).comp hinput
      have happ : Computable (fun p : BitString × ℕ =>
          restrictedSampledBadCodesRaw c p.1 𝒜 gridSteps Δ p.2 ++
            familyStageModelCodesList c
              (decode_restrictedCurveGridCode_sample p.1 (gridSteps + 1)).1 𝒜
              ((decode_restrictedCurveGridCode_sample p.1 gridSteps).2 - (Δ + 1)) p.2) :=
        Computable.list_append.comp ih hlast
      refine happ.of_eq (fun p => ?_)
      simp [restrictedSampledBadCodesRaw, List.range_succ, List.flatMap_append]

/-- The stage enumeration is computable in time for a fixed grid. -/
lemma restrictedSampledBadCodesUpToTime_computable (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) :
    Computable (fun t =>
      restrictedSampledBadCodesUpToTime c gridCode 𝒜 gridSteps Δ t) := by
  exact (Primrec.to_comp eraseDups_bitstring_primrec).comp
    (restrictedSampledBadCodesRaw_computable c gridCode 𝒜 gridSteps Δ)

/-- The stage enumeration is computable jointly in grid index and time. -/
lemma restrictedSampledBadCodesUpToTime_computable_uniform (c : Code)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) :
    Computable (fun p : BitString × ℕ =>
      restrictedSampledBadCodesUpToTime c p.1 𝒜 gridSteps Δ p.2) := by
  exact (Primrec.to_comp eraseDups_bitstring_primrec).comp
    (restrictedSampledBadCodesRaw_computable_uniform c 𝒜 gridSteps Δ)

/-- The chronological stream is computable in time for a fixed grid. -/
lemma restrictedSampledBadCodeStream_computable (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) :
    Computable (fun t => restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t) := by
  have hstage := restrictedSampledBadCodesUpToTime_computable
    c gridCode 𝒜 gridSteps Δ
  let f : ℕ → List BitString := fun n => Nat.rec
      (restrictedSampledBadCodesUpToTime c gridCode 𝒜 gridSteps Δ 0)
      (fun t previous => (previous ++
        restrictedSampledBadCodesUpToTime c gridCode 𝒜 gridSteps Δ (t + 1)).eraseDups)
      n
  have hf : Computable f := by
    convert Computable.nat_rec Computable.id
        (Computable.const
          (restrictedSampledBadCodesUpToTime c gridCode 𝒜 gridSteps Δ 0))
        (((Primrec.to_comp eraseDups_bitstring_primrec).comp
          (Computable.list_append.comp (Computable.snd.comp Computable.snd)
            (hstage.comp (Computable.succ.comp
              (Computable.fst.comp Computable.snd))))).to₂) using 1
  refine hf.of_eq (fun n => ?_)
  dsimp [f]
  induction n with
  | zero => rfl
  | succ n ih => simp [restrictedSampledBadCodeStream, ih]

/-- Uniform stream computability in both the encoded grid and the chronological
stage.  This is the form needed by fixed-length version coding. -/
lemma restrictedSampledBadCodeStream_computable_uniform (c : Code)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) :
    Computable (fun p : BitString × ℕ =>
      restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ p.2) := by
  have hstage := restrictedSampledBadCodesUpToTime_computable_uniform
    c 𝒜 gridSteps Δ
  let f : BitString × ℕ → List BitString := fun p => Nat.rec
      (restrictedSampledBadCodesUpToTime c p.1 𝒜 gridSteps Δ 0)
      (fun t previous => (previous ++
        restrictedSampledBadCodesUpToTime c p.1 𝒜 gridSteps Δ (t + 1)).eraseDups)
      p.2
  have hbase : Computable (fun p : BitString × ℕ =>
      restrictedSampledBadCodesUpToTime c p.1 𝒜 gridSteps Δ 0) :=
    hstage.comp (Computable.pair Computable.fst (Computable.const 0))
  have hstep : Computable₂ (fun (p : BitString × ℕ)
      (q : ℕ × List BitString) => (q.2 ++
        restrictedSampledBadCodesUpToTime c p.1 𝒜 gridSteps Δ (q.1 + 1)).eraseDups) := by
    have hnext : Computable (fun r : (BitString × ℕ) × (ℕ × List BitString) =>
        restrictedSampledBadCodesUpToTime c r.1.1 𝒜 gridSteps Δ (r.2.1 + 1)) :=
      hstage.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))
    exact ((Primrec.to_comp eraseDups_bitstring_primrec).comp
      (Computable.list_append.comp (Computable.snd.comp Computable.snd) hnext)).to₂
  have hf : Computable f := by
    exact (Computable.nat_rec Computable.snd hbase hstep).of_eq (fun p => rfl)
  refine hf.of_eq (fun p => ?_)
  dsimp [f]
  induction p.2 with
  | zero => rfl
  | succ n ih => simp [restrictedSampledBadCodeStream, ih]

/-- Stage members appear in the stream by that time. -/
lemma mem_restrictedSampledBadCodeStream_of_mem_upToTime
    {c : Code} {gridCode : BitString} {𝒜 : PreDescriptionFamily}
    {gridSteps Δ t : ℕ} {w : BitString}
    (hw : w ∈ restrictedSampledBadCodesUpToTime
      c gridCode 𝒜 gridSteps Δ t) :
    w ∈ restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t := by
  cases t with
  | zero => exact hw
  | succ t =>
      exact mem_eraseDups_bitString.mpr (List.mem_append_right _ hw)

/-- Any bad description is eventually caught by the stream. -/
lemma restrictedSampledBadCodeStream_catches_violation
    {n k gridSteps : ℕ} {t_func : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k gridSteps t_func)
    (U : Map) (c : Code) (hc : IsCodeFor c U) (Δ : ℕ)
    (hstrict : ∀ idx < k, t_func (idx + 1) < t_func idx)
    (x : BitString) (i : ℕ) (hi : i ≤ k)
    (𝒜 : DescriptionFamily)
    (hprof : InDescriptionProfileIn 𝒜 U x i (t_func i - (Δ + 1))) :
    ∃ (w : BitString) (t : ℕ) (s : ℕ),
      s < gridSteps ∧
      w ∈ restrictedSampledBadCodeStream c (restrictedCurveGridCode grid) 𝒜.toPre gridSteps Δ t ∧
      IsFamilyDescriptionCode 𝒜.toPre (grid.j s - (Δ + 1)) x w := by
  classical
  obtain ⟨s, hs, his, hisNext⟩ :=
    restrictedCurveGrid_covers n k gridSteps t_func grid i hi
  obtain ⟨S, hS, hSmem, hxS, hcomp, hcard⟩ := hprof
  have hs_le : s ≤ gridSteps := Nat.le_of_lt hs
  have hsNext_le : s + 1 ≤ gridSteps := hs
  have hti : t_func i ≤ grid.j s := by
    have hdrop := restricted_curve_drop_bound hstrict his hi
    exact (show t_func i ≤ t_func (grid.i s) by omega).trans
      (grid.cross_below s hs_le)
  have hsize : S.card ≤ 2 ^ (grid.j s - (Δ + 1)) := by
    refine hcard.trans (Nat.pow_le_pow_right (by decide) ?_)
    exact Nat.sub_le_sub_right hti (Δ + 1)
  have hcompNext : setComplexity U S hS ≤ (grid.i (s + 1) : ENat) := by
    exact hcomp.trans (by exact_mod_cast hisNext)
  let w := (codedUniformOn S hS).code
  obtain ⟨p, hp, hpOut⟩ :=
    exists_halting_program_of_complexity_le U (codedUniformOn S hS)
      (grid.i (s + 1)) hcompNext
  obtain ⟨tSnap, htSnapMax⟩ := exists_max_countHalts c (grid.i (s + 1))
  have hwSnap : w ∈ snapshotCodes c (grid.i (s + 1)) tSnap := by
    exact code_mem_snapshot_of_max hc (grid.i (s + 1)) tSnap htSnapMax hp
      (by simpa [w] using hpOut)
  obtain ⟨tEnum, htEnum⟩ := 𝒜.enumeration.complete S hS hSmem
  let stage := max tEnum tSnap
  have hwEnumStage : w ∈ 𝒜.enumeration.enum stage := by
    exact (familyEnumeration_prefix_of_le 𝒜.enumeration
      (le_max_left tEnum tSnap)).subset htEnum
  have hwSnapStage : w ∈ snapshotCodes c (grid.i (s + 1)) stage := by
    exact snapshotCodes_mem_of_le (le_max_right tEnum tSnap) hwSnap
  have hwBool : isFamilyModelCodeBool (grid.j s - (Δ + 1)) w = true := by
    unfold isFamilyModelCodeBool
    refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
    · rw [isCanonicalUniformCodeBool_iff]
      exact isCanonicalUniformCode_codedUniformOn S hS
    · refine decide_eq_true ?_
      simpa [w, dataPoints_codedUniformOn, canonicalFinsetList_toFinset] using hsize
  have hwCandidate : w ∈ familyCandidateModelCodesList c (grid.i (s + 1))
      𝒜.toPre (grid.j s - (Δ + 1)) stage := by
    rw [familyCandidateModelCodesList, List.mem_filter]
    exact ⟨hwEnumStage,
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true hwSnapStage, hwBool⟩⟩
  have hwStage : w ∈ familyStageModelCodesList c (grid.i (s + 1))
      𝒜.toPre (grid.j s - (Δ + 1)) stage :=
    mem_familyStageModelCodesList_of_candidate c (grid.i (s + 1)) 𝒜.toPre
      (grid.j s - (Δ + 1)) stage w hwCandidate
  have hwUpTo : w ∈ restrictedSampledBadCodesUpToTime c
      (restrictedCurveGridCode grid) 𝒜.toPre gridSteps Δ stage := by
    unfold restrictedSampledBadCodesUpToTime restrictedSampledBadCodesRaw
    apply mem_eraseDups_bitString.mpr
    rw [List.mem_flatMap]
    refine ⟨s, List.mem_range.mpr hs, ?_⟩
    simpa [decode_restrictedCurveGridCode_sample_eq grid hs_le,
      decode_restrictedCurveGridCode_sample_eq grid hsNext_le] using hwStage
  refine ⟨w, stage, s, hs,
    mem_restrictedSampledBadCodeStream_of_mem_upToTime hwUpTo, ?_⟩
  exact ⟨S, hS, hSmem, rfl, hsize, hxS⟩

end Kolmogorov
