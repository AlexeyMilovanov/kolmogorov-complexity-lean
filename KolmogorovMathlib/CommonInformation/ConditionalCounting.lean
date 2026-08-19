import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.Basic
import KolmogorovMathlib.CommonInformation.Counting

/-!
# Common Information: conditional bad-pair enumeration

The finite cardinality bounds in `Counting.lean` are noncomputable sets.  The
proof of SUV Theorem 223 additionally needs a computable staged enumeration:
its terminal count is the finite advice from which the completed bad list is
recovered.  This file starts that construction directly from a code for the
plain conditional decompressor.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- Run one program with an explicit condition for a finite number of
`Code.evaln` steps, decoding a successful output as a bitstring. -/
def conditionalRunOut
    (c : Code) (t : Nat) (p y : BitString) : Option BitString :=
  (Code.evaln t c (Encodable.encode (p, y))).bind
    (fun r => (Encodable.decode r : Option BitString))

/-- The finite snapshot of all outputs produced, with condition `y`, by
programs of length at most `k` within stage `t`. -/
def conditionalOutputSnapshot
    (c : Code) (y : BitString) (k t : Nat) : List BitString :=
  (boundedPrograms k).filterMap (conditionalRunOut c t · y)

/-- Pair one fixed left output with every currently visible right output. -/
def commonWitnessPairsForZXSnapshot
    (c : Code) (z x : BitString) (γ t : Nat) : List BitString :=
  (conditionalOutputSnapshot c z γ t).map fun y => pairCode x y

/-- At one finite stage and for one fixed common witness `z`, enumerate all
pairs of outputs of the `β`- and `γ`-bounded conditional programs. -/
def commonWitnessPairsForZSnapshot
    (c : Code) (z : BitString) (β γ t : Nat) : List BitString :=
  (conditionalOutputSnapshot c z β t).flatMap fun x =>
    commonWitnessPairsForZXSnapshot c z x γ t

/-- At one finite stage, enumerate every pair `(x,y)` for which the same
currently visible `z` has an `α`-bit unconditional program and `x,y` have
`β,γ`-bit conditional programs given that `z`. -/
def commonWitnessPairsSnapshot
    (c : Code) (α β γ t : Nat) : List BitString :=
  (conditionalOutputSnapshot c [] α t).flatMap fun z =>
    commonWitnessPairsForZSnapshot c z β γ t

/-- Prefix-monotone accumulation of the finite common-witness snapshots.
Duplicates are removed so a finite semantic range forces eventual
stabilization. -/
def commonWitnessPairsStage
    (c : Code) (α β γ : Nat) : Nat → List BitString
  | 0 => (commonWitnessPairsSnapshot c α β γ 0).eraseDups
  | t + 1 =>
      (commonWitnessPairsStage c α β γ t ++
        commonWitnessPairsSnapshot c α β γ (t + 1)).eraseDups

theorem commonWitnessPairsStage_nodup
    (c : Code) (α β γ t : Nat) :
    (commonWitnessPairsStage c α β γ t).Nodup := by
  cases t <;> exact nodup_eraseDups_bitString _

theorem commonWitnessPairsStage_prefix
    (c : Code) (α β γ t : Nat) :
    commonWitnessPairsStage c α β γ t <+:
      commonWitnessPairsStage c α β γ (t + 1) := by
  rw [commonWitnessPairsStage]
  exact prefix_eraseDups_append_of_nodup _ _
    (commonWitnessPairsStage_nodup c α β γ t)

theorem conditionalRunOut_sound
    {c : Code} {V : Map} (hc : IsCodeFor c V)
    {t : Nat} {p y out : BitString}
    (h : conditionalRunOut c t p y = some out) :
    produces V p y out := by
  unfold conditionalRunOut at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨a, ha₁, ha₂⟩ := h
  have heval := Nat.Partrec.Code.evaln_sound ha₁
  unfold IsCodeFor at hc
  aesop

theorem conditionalRunOut_complete
    {c : Code} {V : Map} (hc : IsCodeFor c V)
    {p y out : BitString} (h : produces V p y out) :
    ∃ t, conditionalRunOut c t p y = some out := by
  obtain ⟨t, ht⟩ :
      ∃ t, Encodable.encode out ∈
        Code.evaln t c (Encodable.encode (p, y)) := by
    have hEval : Encodable.encode out ∈
        c.eval (Encodable.encode (p, y)) := by
      simp_all +decide [produces, IsCodeFor]
    exact Code.evaln_complete.mp hEval
  refine ⟨t, ?_⟩
  simp [conditionalRunOut]
  simp_all +decide [Encodable.encodek]

theorem conditionalRunOut_mono
    (c : Code) {t t' : Nat} (htt' : t ≤ t')
    {p y out : BitString}
    (h : conditionalRunOut c t p y = some out) :
    conditionalRunOut c t' p y = some out := by
  unfold conditionalRunOut at h ⊢
  rw [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨a, ha₁, ha₂⟩ := h
  exact ⟨a, Nat.Partrec.Code.evaln_mono htt' ha₁, ha₂⟩

theorem mem_conditionalOutputSnapshot_of_run
    {c : Code} {p y out : BitString} {k t : Nat}
    (hp : p.length ≤ k)
    (hout : conditionalRunOut c t p y = some out) :
    out ∈ conditionalOutputSnapshot c y k t := by
  unfold conditionalOutputSnapshot
  rw [List.mem_filterMap]
  exact ⟨p, mem_boundedPrograms_iff p k |>.2 hp, hout⟩

theorem mem_commonWitnessPairsSnapshot_sound
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {α β γ t : Nat} {w : BitString}
    (hw : w ∈ commonWitnessPairsSnapshot c α β γ t) :
    ∃ x y z, w = pairCode x y ∧
      plainK V z ≤ (α : ENat) ∧
      condK V x z ≤ (β : ENat) ∧
      condK V y z ≤ (γ : ENat) := by
  unfold commonWitnessPairsSnapshot commonWitnessPairsForZSnapshot
    commonWitnessPairsForZXSnapshot at hw
  simp only [List.mem_flatMap, List.mem_map] at hw
  obtain ⟨z, hz, x, hx, y, hy, rfl⟩ := hw
  unfold conditionalOutputSnapshot at hz hx hy
  rw [List.mem_filterMap] at hz hx hy
  obtain ⟨pz, hpz, hpzRun⟩ := hz
  obtain ⟨px, hpx, hpxRun⟩ := hx
  obtain ⟨py, hpy, hpyRun⟩ := hy
  refine ⟨x, y, z, rfl, ?_, ?_, ?_⟩
  · apply (condKLeIff V z [] α).2
    exact ⟨pz, (mem_boundedPrograms_iff pz α).1 hpz,
      conditionalRunOut_sound hc hpzRun⟩
  · apply (condKLeIff V x z β).2
    exact ⟨px, (mem_boundedPrograms_iff px β).1 hpx,
      conditionalRunOut_sound hc hpxRun⟩
  · apply (condKLeIff V y z γ).2
    exact ⟨py, (mem_boundedPrograms_iff py γ).1 hpy,
      conditionalRunOut_sound hc hpyRun⟩

theorem mem_commonWitnessPairsStage_sound
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {α β γ t : Nat} {w : BitString}
    (hw : w ∈ commonWitnessPairsStage c α β γ t) :
    ∃ x y z, w = pairCode x y ∧
      plainK V z ≤ (α : ENat) ∧
      condK V x z ≤ (β : ENat) ∧
      condK V y z ≤ (γ : ENat) := by
  induction t with
  | zero =>
      exact mem_commonWitnessPairsSnapshot_sound hc
        (by simpa [commonWitnessPairsStage,
          mem_eraseDups_bitString] using hw)
  | succ t ih =>
      have hw' :
          w ∈ commonWitnessPairsStage c α β γ t ∨
            w ∈ commonWitnessPairsSnapshot c α β γ (t + 1) := by
        simpa [commonWitnessPairsStage,
          mem_eraseDups_bitString] using hw
      exact hw'.elim ih (mem_commonWitnessPairsSnapshot_sound hc)

theorem commonWitnessPairsSnapshot_mem_stage
    (c : Code) (α β γ t : Nat) {w : BitString}
    (hw : w ∈ commonWitnessPairsSnapshot c α β γ t) :
    w ∈ commonWitnessPairsStage c α β γ t := by
  cases t with
  | zero =>
      simpa [commonWitnessPairsStage,
        mem_eraseDups_bitString] using hw
  | succ t =>
      simp only [commonWitnessPairsStage, mem_eraseDups_bitString,
        List.mem_append]
      exact Or.inr hw

/-- A conditional finite-stage output list is primitive recursive uniformly in
the condition, program bound, and stage. -/
theorem conditionalOutputSnapshot_primrec (c : Code) :
    Primrec
      (fun q : (BitString × Nat) × Nat =>
        conditionalOutputSnapshot c q.1.1 q.1.2 q.2) := by
  apply Primrec.listFilterMap
    (primrec_boundedPrograms.comp (Primrec.snd.comp Primrec.fst))
  apply Primrec.option_bind
  · exact (evaln_primrec c).comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.encode.comp
        (Primrec.pair Primrec.snd
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  · exact Primrec.decode.comp Primrec.snd

/-- Mapping `pairCode` with a fixed left component over a list is primitive
recursive. -/
theorem map_pairCode_primrec :
    Primrec (fun q : BitString × List BitString =>
      q.2.map (pairCode q.1)) := by
  exact Primrec.list_map Primrec.snd
    ((pairCode_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)

/-- Pairing a fixed visible left output with all visible right outputs is
primitive recursive uniformly in the witness, left output, bound, and stage. -/
theorem commonWitnessPairsForZXSnapshot_primrec (c : Code) :
    Primrec
      (fun q : ((BitString × BitString) × Nat) × Nat =>
        commonWitnessPairsForZXSnapshot c
          q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  unfold commonWitnessPairsForZXSnapshot
  have hz : Primrec
      (fun q : ((BitString × BitString) × Nat) × Nat => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec
      (fun q : ((BitString × BitString) × Nat) × Nat => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hγ : Primrec
      (fun q : ((BitString × BitString) × Nat) × Nat => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have ht : Primrec
      (fun q : ((BitString × BitString) × Nat) × Nat => q.2) :=
    Primrec.snd
  have hsnap : Primrec
      (fun q : ((BitString × BitString) × Nat) × Nat =>
        conditionalOutputSnapshot c q.1.1.1 q.1.2 q.2) :=
    (conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair hz hγ) ht)
  exact map_pairCode_primrec.comp (Primrec.pair hx hsnap)

/-- Enumerating both conditional outputs for one fixed common witness is
primitive recursive uniformly in both bounds and the stage. -/
theorem commonWitnessPairsForZSnapshot_primrec (c : Code) :
    Primrec
      (fun q : (BitString × Nat × Nat) × Nat =>
        commonWitnessPairsForZSnapshot c
          q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  unfold commonWitnessPairsForZSnapshot
  have hz : Primrec
      (fun q : (BitString × Nat × Nat) × Nat => q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hβ : Primrec
      (fun q : (BitString × Nat × Nat) × Nat => q.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hγ : Primrec
      (fun q : (BitString × Nat × Nat) × Nat => q.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec
      (fun q : (BitString × Nat × Nat) × Nat => q.2) := Primrec.snd
  have hsnap : Primrec
      (fun q : (BitString × Nat × Nat) × Nat =>
        conditionalOutputSnapshot c q.1.1 q.1.2.1 q.2) :=
    (conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair hz hβ) ht)
  have hz' : Primrec
      (fun r : ((BitString × Nat × Nat) × Nat) × BitString => r.1.1.1) :=
    hz.comp Primrec.fst
  have hγ' : Primrec
      (fun r : ((BitString × Nat × Nat) × Nat) × BitString => r.1.1.2.2) :=
    hγ.comp Primrec.fst
  have ht' : Primrec
      (fun r : ((BitString × Nat × Nat) × Nat) × BitString => r.1.2) :=
    ht.comp Primrec.fst
  have hbody : Primrec₂
      (fun (q : (BitString × Nat × Nat) × Nat) (x : BitString) =>
        commonWitnessPairsForZXSnapshot c q.1.1 x q.1.2.2 q.2) :=
    ((commonWitnessPairsForZXSnapshot_primrec c).comp
      (Primrec.pair
        (Primrec.pair (Primrec.pair hz' Primrec.snd) hγ') ht')).to₂
  exact Primrec.list_flatMap hsnap hbody

/-- One common-witness snapshot is primitive recursive uniformly in the three
program bounds and the finite stage. -/
theorem commonWitnessPairsSnapshot_primrec (c : Code) :
    Primrec
      (fun q : (Nat × Nat × Nat) × Nat =>
        commonWitnessPairsSnapshot c q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  unfold commonWitnessPairsSnapshot
  have hα : Primrec (fun q : (Nat × Nat × Nat) × Nat => q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hβ : Primrec (fun q : (Nat × Nat × Nat) × Nat => q.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hγ : Primrec (fun q : (Nat × Nat × Nat) × Nat => q.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec (fun q : (Nat × Nat × Nat) × Nat => q.2) :=
    Primrec.snd
  have hsnap : Primrec (fun q : (Nat × Nat × Nat) × Nat =>
      conditionalOutputSnapshot c [] q.1.1 q.2) :=
    (conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair (Primrec.const []) hα) ht)
  have hβ' : Primrec
      (fun r : ((Nat × Nat × Nat) × Nat) × BitString => r.1.1.2.1) :=
    hβ.comp Primrec.fst
  have hγ' : Primrec
      (fun r : ((Nat × Nat × Nat) × Nat) × BitString => r.1.1.2.2) :=
    hγ.comp Primrec.fst
  have ht' : Primrec
      (fun r : ((Nat × Nat × Nat) × Nat) × BitString => r.1.2) :=
    ht.comp Primrec.fst
  have hbody : Primrec₂
      (fun (q : (Nat × Nat × Nat) × Nat) (z : BitString) =>
        commonWitnessPairsForZSnapshot c z q.1.2.1 q.1.2.2 q.2) :=
    ((commonWitnessPairsForZSnapshot_primrec c).comp
      (Primrec.pair
        (Primrec.pair Primrec.snd (Primrec.pair hβ' hγ')) ht')).to₂
  exact Primrec.list_flatMap hsnap hbody

/-- The conditional bad-pair stages are computable uniformly in all three
program bounds and the stage number, for each fixed decompressor code. -/
theorem commonWitnessPairsStage_computable (c : Code) :
    Computable
      (fun q : (Nat × Nat × Nat) × Nat =>
        commonWitnessPairsStage c q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have hSnapshot := commonWitnessPairsSnapshot_primrec c
  have hbase :
      Primrec
        (fun p : (Nat × Nat × Nat) × Nat =>
          (commonWitnessPairsSnapshot c
            p.1.1 p.1.2.1 p.1.2.2 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      (hSnapshot.comp
        (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep :
      Primrec₂
        (fun (p : (Nat × Nat × Nat) × Nat)
          (z : Nat × List BitString) =>
          (z.2 ++ commonWitnessPairsSnapshot c
            p.1.1 p.1.2.1 p.1.2.2 (z.1 + 1)).eraseDups) :=
    (eraseDups_bitstring_primrec.comp
      (Primrec.list_append.comp
        (Primrec.snd.comp Primrec.snd)
        (hSnapshot.comp
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.succ.comp
              (Primrec.fst.comp Primrec.snd)))))).to₂
  apply Primrec.to_comp
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  rintro ⟨⟨α, β, γ⟩, t⟩
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [commonWitnessPairsStage]
      rw [← ih]

/-- Exact semantics of the staged enumeration: a pair eventually appears iff
there is a common witness satisfying the three non-strict program bounds.
Using `≤` here is deliberate and matches `commonWitnessPairsLe`; source-level
strict thresholds are obtained by decrementing positive integer bounds. -/
theorem mem_commonWitnessPairsStage_eventually_iff
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    (α β γ : Nat) (x y : BitString) :
    (∃ t, pairCode x y ∈ commonWitnessPairsStage c α β γ t) ↔
      ∃ z,
        plainK V z ≤ (α : ENat) ∧
        condK V x z ≤ (β : ENat) ∧
        condK V y z ≤ (γ : ENat) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨x', y', z, hpair, hz, hx, hy⟩ :=
      mem_commonWitnessPairsStage_sound hc ht
    have hxy : (x', y') = (x, y) :=
      pairCode_injective hpair.symm
    cases hxy
    exact ⟨z, hz, hx, hy⟩
  · rintro ⟨z, hz, hx, hy⟩
    obtain ⟨pz, hpzLen, hpz⟩ :=
      (condKLeIff V z [] α).1 hz
    obtain ⟨px, hpxLen, hpx⟩ :=
      (condKLeIff V x z β).1 hx
    obtain ⟨py, hpyLen, hpy⟩ :=
      (condKLeIff V y z γ).1 hy
    obtain ⟨tz, htz⟩ := conditionalRunOut_complete hc hpz
    obtain ⟨tx, htx⟩ := conditionalRunOut_complete hc hpx
    obtain ⟨ty, hty⟩ := conditionalRunOut_complete hc hpy
    let T := max tz (max tx ty)
    have hzT : z ∈ conditionalOutputSnapshot c [] α T :=
      mem_conditionalOutputSnapshot_of_run hpzLen
        (conditionalRunOut_mono c (le_max_left _ _) htz)
    have hxT : x ∈ conditionalOutputSnapshot c z β T :=
      mem_conditionalOutputSnapshot_of_run hpxLen
        (conditionalRunOut_mono c
          (le_trans (le_max_left _ _) (le_max_right _ _)) htx)
    have hyT : y ∈ conditionalOutputSnapshot c z γ T :=
      mem_conditionalOutputSnapshot_of_run hpyLen
        (conditionalRunOut_mono c
          (le_trans (le_max_right _ _) (le_max_right _ _)) hty)
    refine ⟨T, commonWitnessPairsSnapshot_mem_stage c α β γ T ?_⟩
    unfold commonWitnessPairsSnapshot commonWitnessPairsForZSnapshot
      commonWitnessPairsForZXSnapshot
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨z, hzT, x, hxT, y, hyT, rfl⟩

end Kolmogorov
