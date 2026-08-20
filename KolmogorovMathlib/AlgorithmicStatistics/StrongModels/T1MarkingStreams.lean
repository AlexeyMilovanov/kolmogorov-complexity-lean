import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.BusyBeaver
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingCount

/-!
# Computable marking streams for the strange-string construction

The source proof of Theorem `t1` enumerates four families:

* `B`: small finite models of plain complexity at most `epsilon`;
* `C'`: finite models of plain complexity at most `k`;
* `C''`: small finite models grouped into portions, one portion for every
  short description of a set of model codes;
* `D`: length-`n` strings of plain complexity strictly below `k`.

All streams below are concrete filters/maps of `boundedOutputStage`.  Finite
models are accepted only when their output round-trips as the repository's
canonical uniform code.  Thus the streams are computable and prefix-stable,
and their soundness/completeness statements use `plainSetComplexity` rather
than an arbitrary caller-supplied set representation.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- Test whether `w` is the canonical uniform code of a nonempty finite model
of cardinality at most `bound`. -/
noncomputable def t1ModelCodeValid (bound : Nat) (w : BitString) : Bool :=
  isCanonicalUniformCodeBool w &&
    decide ((canonicalPointListOfCode w).length ≤ bound)

theorem t1ModelCodeValid_primrec :
    Primrec (fun p : Nat × BitString => t1ModelCodeValid p.1 p.2) := by
  have hcanon : Primrec (fun p : Nat × BitString =>
      isCanonicalUniformCodeBool p.2) :=
    isCanonicalUniformCodeBool_primrec.comp Primrec.snd
  have hlen : Primrec (fun p : Nat × BitString =>
      (canonicalPointListOfCode p.2).length) :=
    Primrec.list_length.comp
      (canonicalPointListOfCode_primrec.comp Primrec.snd)
  have hle : Primrec (fun p : Nat × BitString =>
      decide ((canonicalPointListOfCode p.2).length ≤ p.1)) :=
    PrimrecPred.decide (Primrec.nat_le.comp hlen Primrec.fst)
  exact Primrec.and.comp hcanon hle

theorem t1ModelCodeValid_computable :
    Computable (fun p : Nat × BitString => t1ModelCodeValid p.1 p.2) :=
  t1ModelCodeValid_primrec.to_comp

theorem t1ModelCodeValid_eq_true (bound : Nat) (w : BitString) :
    t1ModelCodeValid bound w = true ↔
      ∃ (M : Finset BitString) (hM : M.Nonempty),
        w = (codedUniformOn M hM).code ∧ M.card ≤ bound := by
  constructor
  · intro hw
    rw [t1ModelCodeValid, Bool.and_eq_true_iff, decide_eq_true_eq] at hw
    obtain ⟨hM, hcode⟩ :=
      eq_codedUniformOn_of_isCanonicalUniformCodeBool hw.1
    refine ⟨t1CodeToSet w, hM, hcode, ?_⟩
    have hlen :
        (canonicalPointListOfCode w).length = (t1CodeToSet w).card := by
      unfold canonicalPointListOfCode t1CodeToSet
      exact length_canonicalFinsetList _
    simpa [hlen] using hw.2
  · rintro ⟨M, hM, rfl, hcard⟩
    rw [t1ModelCodeValid, Bool.and_eq_true_iff, decide_eq_true_eq]
    refine ⟨(isCanonicalUniformCodeBool_iff _).2
      (isCanonicalUniformCode_codedUniformOn M hM), ?_⟩
    rw [canonicalPointListOfCode_codedUniformOn,
      length_canonicalFinsetList]
    exact hcard

/-- Canonical model codes of complexity at most `m`, in first-appearance order. -/
def t1CanonicalModelStage (c : Code) (m t : Nat) : List BitString :=
  (boundedOutputStage c m t).filter isCanonicalUniformCodeBool

theorem t1CanonicalModelStage_primrec (c : Code) :
    Primrec (fun p : Nat × Nat => t1CanonicalModelStage c p.1 p.2) := by
  exact list_filter_primrec (boundedOutputStage_primrec c)
    (isCanonicalUniformCodeBool_primrec.comp Primrec.snd)

theorem t1CanonicalModelStage_computable (c : Code) :
    Computable (fun p : Nat × Nat => t1CanonicalModelStage c p.1 p.2) :=
  (t1CanonicalModelStage_primrec c).to_comp

theorem t1CanonicalModelStage_prefix (c : Code) (m t : Nat) :
    t1CanonicalModelStage c m t <+: t1CanonicalModelStage c m (t + 1) := by
  obtain ⟨rest, hrest⟩ := boundedOutputStage_prefix c m t
  unfold t1CanonicalModelStage
  rw [← hrest, List.filter_append]
  exact List.prefix_append _ _

theorem t1CanonicalModelStage_sound
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {m t : Nat} {w : BitString}
    (hw : w ∈ t1CanonicalModelStage c m t) :
    ∃ (M : Finset BitString) (hM : M.Nonempty),
      w = (codedUniformOn M hM).code ∧
      plainSetComplexity V M hM ≤ (m : ENat) := by
  rw [t1CanonicalModelStage, List.mem_filter] at hw
  obtain ⟨hM, hcode⟩ :=
    eq_codedUniformOn_of_isCanonicalUniformCodeBool hw.2
  have hcode' :
      w = (codedUniformOn (t1CodeToSet w) hM).code := by
    simpa [t1CodeToSet] using hcode
  refine ⟨t1CodeToSet w, hM, hcode', ?_⟩
  have hcompleted : w ∈ completedBoundedOutput c m := by
    apply (boundedOutputStage_prefix_completed c m t).sublist.subset
    exact hw.1
  have hcomp := (mem_completedBoundedOutput_iff_plainK_le hc m w).mp hcompleted
  unfold plainSetComplexity
  rw [← hcode']
  exact hcomp

theorem t1CanonicalModelStage_complete
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {m : Nat} (M : Finset BitString) (hM : M.Nonempty)
    (hcomp : plainSetComplexity V M hM ≤ (m : ENat)) :
    ∃ t, (codedUniformOn M hM).code ∈ t1CanonicalModelStage c m t := by
  let t := boundedOutputCompletionTime c m
  refine ⟨t, ?_⟩
  rw [t1CanonicalModelStage, List.mem_filter]
  refine ⟨?_, (isCanonicalUniformCodeBool_iff _).2
    (isCanonicalUniformCode_codedUniformOn M hM)⟩
  rw [boundedOutputStage_eq_completed_at_completion]
  exact (mem_completedBoundedOutput_iff_plainK_le hc m _).2 hcomp

theorem t1CanonicalModelStage_length_lt (c : Code) (m t : Nat) :
    (t1CanonicalModelStage c m t).length < 2 ^ (m + 1) :=
  (List.length_filter_le _ _).trans_lt
    (boundedOutputStage_length_lt c m t)

theorem t1CanonicalModelStage_stabilizes (c : Code) (m : Nat) :
    ∃ T, ∀ t, T ≤ t →
      t1CanonicalModelStage c m t = t1CanonicalModelStage c m T := by
  refine ⟨boundedOutputCompletionTime c m, fun t ht => ?_⟩
  unfold t1CanonicalModelStage
  rw [boundedOutputStage_eq_completed_of_completion_le c m t ht,
    boundedOutputStage_eq_completed_at_completion]

/-- The `B` stream: small canonical models of complexity at most `epsilon`. -/
noncomputable def t1BStage (c : Code) (n epsilon t : Nat) : List BitString :=
  (boundedOutputStage c epsilon t).filter
    (t1ModelCodeValid (2 ^ (n - epsilon - 4)))

theorem t1BStage_primrec (c : Code) :
    Primrec (fun p : (Nat × Nat) × Nat =>
      t1BStage c p.1.1 p.1.2 p.2) := by
  have hbase : Primrec (fun p : (Nat × Nat) × Nat =>
      boundedOutputStage c p.1.2 p.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hbound : Primrec (fun p : ((Nat × Nat) × Nat) × BitString =>
      2 ^ (p.1.1.1 - p.1.1.2 - 4)) :=
    twoPow_primrec.comp
      (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp
          (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))
        (Primrec.const 4))
  have hvalid : Primrec₂ (fun (p : (Nat × Nat) × Nat) (w : BitString) =>
      t1ModelCodeValid (2 ^ (p.1.1 - p.1.2 - 4)) w) :=
    (t1ModelCodeValid_primrec.comp
      (Primrec.pair hbound Primrec.snd)).to₂
  exact list_filter_primrec hbase hvalid

theorem t1BStage_computable (c : Code) :
    Computable (fun p : (Nat × Nat) × Nat =>
      t1BStage c p.1.1 p.1.2 p.2) :=
  (t1BStage_primrec c).to_comp

theorem t1BStage_prefix (c : Code) (n epsilon t : Nat) :
    t1BStage c n epsilon t <+: t1BStage c n epsilon (t + 1) := by
  obtain ⟨rest, hrest⟩ := boundedOutputStage_prefix c epsilon t
  unfold t1BStage
  rw [← hrest, List.filter_append]
  exact List.prefix_append _ _

theorem t1BStage_sound
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n epsilon t : Nat} {w : BitString}
    (hw : w ∈ t1BStage c n epsilon t) :
    ∃ (S : Finset BitString) (hS : S.Nonempty),
      w = (codedUniformOn S hS).code ∧
      plainSetComplexity V S hS ≤ (epsilon : ENat) ∧
      S.card ≤ 2 ^ (n - epsilon - 4) := by
  rw [t1BStage, List.mem_filter] at hw
  obtain ⟨S, hS, hcode, hcard⟩ :=
    (t1ModelCodeValid_eq_true _ _).1 hw.2
  refine ⟨S, hS, hcode, ?_, hcard⟩
  have hcompleted : w ∈ completedBoundedOutput c epsilon := by
    apply (boundedOutputStage_prefix_completed c epsilon t).sublist.subset
    exact hw.1
  have hcomp :=
    (mem_completedBoundedOutput_iff_plainK_le hc epsilon w).1 hcompleted
  unfold plainSetComplexity
  rw [← hcode]
  exact hcomp

theorem t1BStage_complete
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n epsilon : Nat} (S : Finset BitString) (hS : S.Nonempty)
    (hcomp : plainSetComplexity V S hS ≤ (epsilon : ENat))
    (hcard : S.card ≤ 2 ^ (n - epsilon - 4)) :
    ∃ t, (codedUniformOn S hS).code ∈ t1BStage c n epsilon t := by
  refine ⟨boundedOutputCompletionTime c epsilon, ?_⟩
  rw [t1BStage, List.mem_filter,
    boundedOutputStage_eq_completed_at_completion]
  exact ⟨(mem_completedBoundedOutput_iff_plainK_le hc epsilon _).2 hcomp,
    (t1ModelCodeValid_eq_true _ _).2 ⟨S, hS, rfl, hcard⟩⟩

theorem t1BStage_length_lt (c : Code) (n epsilon t : Nat) :
    (t1BStage c n epsilon t).length < 2 ^ (epsilon + 1) :=
  (List.length_filter_le _ _).trans_lt
    (boundedOutputStage_length_lt c epsilon t)

theorem t1BStage_stabilizes (c : Code) (n epsilon : Nat) :
    ∃ T, ∀ t, T ≤ t → t1BStage c n epsilon t = t1BStage c n epsilon T := by
  refine ⟨boundedOutputCompletionTime c epsilon, fun t ht => ?_⟩
  unfold t1BStage
  rw [boundedOutputStage_eq_completed_of_completion_le c epsilon t ht,
    boundedOutputStage_eq_completed_at_completion]

/-- The `C'` stream: all canonical finite models of complexity at most `k`. -/
def t1CPrimeStage (c : Code) (k t : Nat) : List BitString :=
  t1CanonicalModelStage c k t

theorem t1CPrimeStage_computable (c : Code) :
    Computable (fun p : Nat × Nat => t1CPrimeStage c p.1 p.2) :=
  t1CanonicalModelStage_computable c

theorem t1CPrimeStage_prefix (c : Code) (k t : Nat) :
    t1CPrimeStage c k t <+: t1CPrimeStage c k (t + 1) :=
  t1CanonicalModelStage_prefix c k t

theorem t1CPrimeStage_sound
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {k t : Nat} {w : BitString} (hw : w ∈ t1CPrimeStage c k t) :
    ∃ (M : Finset BitString) (hM : M.Nonempty),
      w = (codedUniformOn M hM).code ∧
      plainSetComplexity V M hM ≤ (k : ENat) :=
  t1CanonicalModelStage_sound hc hw

theorem t1CPrimeStage_complete
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {k : Nat} (M : Finset BitString) (hM : M.Nonempty)
    (hcomp : plainSetComplexity V M hM ≤ (k : ENat)) :
    ∃ t, (codedUniformOn M hM).code ∈ t1CPrimeStage c k t :=
  t1CanonicalModelStage_complete hc M hM hcomp

theorem t1CPrimeStage_length_lt (c : Code) (k t : Nat) :
    (t1CPrimeStage c k t).length < 2 ^ (k + 1) :=
  t1CanonicalModelStage_length_lt c k t

theorem t1CPrimeStage_stabilizes (c : Code) (k : Nat) :
    ∃ T, ∀ t, T ≤ t →
      t1CPrimeStage c k t = t1CPrimeStage c k T :=
  t1CanonicalModelStage_stabilizes c k

/-- Canonical description-set codes of complexity at most `d` and cardinality
at most `2^n`.  These codes index the `C''` portions. -/
noncomputable def t1DescriptionStage
    (c : Code) (n d t : Nat) : List BitString :=
  (boundedOutputStage c d t).filter
    (t1ModelCodeValid (2 ^ n))

theorem t1DescriptionStage_primrec (c : Code) :
    Primrec (fun p : (Nat × Nat) × Nat =>
      t1DescriptionStage c p.1.1 p.1.2 p.2) := by
  have hbase : Primrec (fun p : (Nat × Nat) × Nat =>
      boundedOutputStage c p.1.2 p.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hbound : Primrec (fun p : ((Nat × Nat) × Nat) × BitString =>
      2 ^ p.1.1.1) :=
    twoPow_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hvalid : Primrec₂
      (fun (p : (Nat × Nat) × Nat) (w : BitString) =>
        t1ModelCodeValid (2 ^ p.1.1) w) :=
    (t1ModelCodeValid_primrec.comp
      (Primrec.pair hbound Primrec.snd)).to₂
  exact list_filter_primrec hbase hvalid

theorem t1DescriptionStage_computable (c : Code) :
    Computable (fun p : (Nat × Nat) × Nat =>
      t1DescriptionStage c p.1.1 p.1.2 p.2) :=
  (t1DescriptionStage_primrec c).to_comp

theorem t1DescriptionStage_prefix (c : Code) (n d t : Nat) :
    t1DescriptionStage c n d t <+:
      t1DescriptionStage c n d (t + 1) := by
  obtain ⟨rest, hrest⟩ := boundedOutputStage_prefix c d t
  unfold t1DescriptionStage
  rw [← hrest, List.filter_append]
  exact List.prefix_append _ _

theorem t1DescriptionStage_sound
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n d t : Nat} {w : BitString}
    (hw : w ∈ t1DescriptionStage c n d t) :
    ∃ (D : Finset BitString) (hD : D.Nonempty),
      w = (codedUniformOn D hD).code ∧
      plainSetComplexity V D hD ≤ (d : ENat) ∧
      D.card ≤ 2 ^ n := by
  rw [t1DescriptionStage, List.mem_filter] at hw
  obtain ⟨D, hD, hcode, hcard⟩ :=
    (t1ModelCodeValid_eq_true _ _).1 hw.2
  refine ⟨D, hD, hcode, ?_, hcard⟩
  have hcompleted : w ∈ completedBoundedOutput c d := by
    apply (boundedOutputStage_prefix_completed c d t).sublist.subset
    exact hw.1
  have hcomp :=
    (mem_completedBoundedOutput_iff_plainK_le hc d w).1 hcompleted
  unfold plainSetComplexity
  rw [← hcode]
  exact hcomp

theorem t1DescriptionStage_complete
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n d : Nat} (D : Finset BitString) (hD : D.Nonempty)
    (hcomp : plainSetComplexity V D hD ≤ (d : ENat))
    (hcard : D.card ≤ 2 ^ n) :
    ∃ t, (codedUniformOn D hD).code ∈ t1DescriptionStage c n d t := by
  refine ⟨boundedOutputCompletionTime c d, ?_⟩
  rw [t1DescriptionStage, List.mem_filter,
    boundedOutputStage_eq_completed_at_completion]
  exact ⟨(mem_completedBoundedOutput_iff_plainK_le hc d _).2 hcomp,
    (t1ModelCodeValid_eq_true _ _).2 ⟨D, hD, rfl, hcard⟩⟩

theorem t1DescriptionStage_length_lt (c : Code) (n d t : Nat) :
    (t1DescriptionStage c n d t).length < 2 ^ (d + 1) :=
  (List.length_filter_le _ _).trans_lt
    (boundedOutputStage_length_lt c d t)

theorem t1DescriptionStage_stabilizes (c : Code) (n d : Nat) :
    ∃ T, ∀ t, T ≤ t →
      t1DescriptionStage c n d t = t1DescriptionStage c n d T := by
  refine ⟨boundedOutputCompletionTime c d, fun t ht => ?_⟩
  unfold t1DescriptionStage
  rw [boundedOutputStage_eq_completed_of_completion_le c d t ht,
    boundedOutputStage_eq_completed_at_completion]

/-- One `C''` portion: the canonical small-model codes contained in a decoded
description set. -/
noncomputable def t1CDoublePrimeBatch (n k : Nat) (descriptionCode : BitString) :
    List BitString :=
  (canonicalPointListOfCode descriptionCode).filter
    (t1ModelCodeValid (2 ^ (n - k - 4)))

theorem t1CDoublePrimeBatch_primrec :
    Primrec (fun p : (Nat × Nat) × BitString =>
      t1CDoublePrimeBatch p.1.1 p.1.2 p.2) := by
  have hlist : Primrec (fun p : (Nat × Nat) × BitString =>
      canonicalPointListOfCode p.2) :=
    canonicalPointListOfCode_primrec.comp Primrec.snd
  have hbound : Primrec (fun p : ((Nat × Nat) × BitString) × BitString =>
      2 ^ (p.1.1.1 - p.1.1.2 - 4)) :=
    twoPow_primrec.comp
      (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp
          (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))
        (Primrec.const 4))
  have hvalid : Primrec₂
      (fun (p : (Nat × Nat) × BitString) (w : BitString) =>
        t1ModelCodeValid (2 ^ (p.1.1 - p.1.2 - 4)) w) :=
    (t1ModelCodeValid_primrec.comp
      (Primrec.pair hbound Primrec.snd)).to₂
  exact list_filter_primrec hlist hvalid

/-- The `C''` stream.  Each short canonical description-set code contributes
one portion, preserving the source's batching by descriptions. -/
noncomputable def t1CDoublePrimeBatches
    (c : Code) (n k d t : Nat) : List (List BitString) :=
  (t1DescriptionStage c n d t).map (t1CDoublePrimeBatch n k)

theorem t1CDoublePrimeBatches_primrec (c : Code) :
    Primrec (fun p : ((Nat × Nat) × Nat) × Nat =>
      t1CDoublePrimeBatches c p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hdescs : Primrec (fun p : ((Nat × Nat) × Nat) × Nat =>
      t1DescriptionStage c p.1.1.1 p.1.2 p.2) :=
    (t1DescriptionStage_primrec c).comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have hbatch : Primrec₂
      (fun (p : ((Nat × Nat) × Nat) × Nat) (w : BitString) =>
        t1CDoublePrimeBatch p.1.1.1 p.1.1.2 w) :=
    (t1CDoublePrimeBatch_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        Primrec.snd)).to₂
  exact Primrec.list_map hdescs hbatch

theorem t1CDoublePrimeBatches_computable (c : Code) :
    Computable (fun p : ((Nat × Nat) × Nat) × Nat =>
      t1CDoublePrimeBatches c p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  (t1CDoublePrimeBatches_primrec c).to_comp

theorem t1CDoublePrimeBatches_prefix
    (c : Code) (n k d t : Nat) :
    t1CDoublePrimeBatches c n k d t <+:
      t1CDoublePrimeBatches c n k d (t + 1) := by
  unfold t1CDoublePrimeBatches
  have hprefix := t1DescriptionStage_prefix c n d t
  obtain ⟨rest, hrest⟩ := hprefix
  rw [← hrest, List.map_append]
  exact List.prefix_append _ _

/-- The `C''` batch stream is prefix-monotone at arbitrary stages. -/
theorem t1CDoublePrimeBatches_mono
    (c : Code) (n k d : Nat) {t u : Nat} (htu : t ≤ u) :
    t1CDoublePrimeBatches c n k d t <+:
      t1CDoublePrimeBatches c n k d u := by
  induction u, htu using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ u htu ih =>
      exact ih.trans (t1CDoublePrimeBatches_prefix c n k d u)

theorem t1CDoublePrimeBatches_sound
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n k d t : Nat} {batch : List BitString}
    (hbatch : batch ∈ t1CDoublePrimeBatches c n k d t) :
    ∃ (D : Finset BitString) (hD : D.Nonempty),
      plainSetComplexity V D hD ≤ (d : ENat) ∧
      D.card ≤ 2 ^ n ∧
      ∀ w ∈ batch,
        w ∈ D ∧
        ∃ (M : Finset BitString) (hM : M.Nonempty),
          w = (codedUniformOn M hM).code ∧
          M.card ≤ 2 ^ (n - k - 4) := by
  rw [t1CDoublePrimeBatches, List.mem_map] at hbatch
  obtain ⟨descriptionCode, hdescription, rfl⟩ := hbatch
  obtain ⟨D, hD, hcode, hcomp, hcard⟩ :=
    t1DescriptionStage_sound hc hdescription
  refine ⟨D, hD, hcomp, hcard, ?_⟩
  intro w hw
  rw [t1CDoublePrimeBatch, List.mem_filter] at hw
  refine ⟨?_, (t1ModelCodeValid_eq_true _ _).1 hw.2⟩
  have hpoints :
      canonicalPointListOfCode descriptionCode = canonicalFinsetList D := by
    rw [hcode, canonicalPointListOfCode_codedUniformOn]
  rw [hpoints, mem_canonicalFinsetList] at hw
  exact hw.1

theorem t1CDoublePrimeBatches_complete
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n k d : Nat} (M : Finset BitString) (hM : M.Nonempty)
    (hcard : M.card ≤ 2 ^ (n - k - 4))
    (hprofile :
      InPlainDescriptionProfile V (codedUniformOn M hM).code d n) :
    ∃ t batch,
      batch ∈ t1CDoublePrimeBatches c n k d t ∧
      (codedUniformOn M hM).code ∈ batch := by
  obtain ⟨D, hD, hmem, hcomp, hDcard⟩ := hprofile
  obtain ⟨t, hDt⟩ :=
    t1DescriptionStage_complete hc D hD hcomp hDcard
  refine ⟨t, t1CDoublePrimeBatch n k (codedUniformOn D hD).code, ?_, ?_⟩
  · rw [t1CDoublePrimeBatches, List.mem_map]
    exact ⟨(codedUniformOn D hD).code, hDt, rfl⟩
  · rw [t1CDoublePrimeBatch, List.mem_filter]
    refine ⟨?_, (t1ModelCodeValid_eq_true _ _).2
      ⟨M, hM, rfl, hcard⟩⟩
    rw [canonicalPointListOfCode_codedUniformOn,
      mem_canonicalFinsetList]
    exact hmem

theorem t1CDoublePrimeBatches_length_lt
    (c : Code) (n k d t : Nat) :
    (t1CDoublePrimeBatches c n k d t).length < 2 ^ (d + 1) := by
  unfold t1CDoublePrimeBatches
  rw [List.length_map]
  exact t1DescriptionStage_length_lt c n d t

theorem t1CDoublePrimeBatch_length_le
    {c : Code} {n k d t : Nat} {batch : List BitString}
    (hbatch : batch ∈ t1CDoublePrimeBatches c n k d t) :
    batch.length ≤ 2 ^ n := by
  rw [t1CDoublePrimeBatches, List.mem_map] at hbatch
  obtain ⟨descriptionCode, hdescription, rfl⟩ := hbatch
  rw [t1DescriptionStage, List.mem_filter] at hdescription
  have hvalid := (t1ModelCodeValid_eq_true _ _).1 hdescription.2
  obtain ⟨D, hD, hcode, hcard⟩ := hvalid
  unfold t1CDoublePrimeBatch
  refine (List.length_filter_le _ _).trans ?_
  rw [hcode, canonicalPointListOfCode_codedUniformOn,
    length_canonicalFinsetList]
  exact hcard

/-- Every model code in a visible `C″` portion decodes to a model satisfying
the source's small-cardinality bound.  This is the pointwise form used when
the chronological run turns the visible model codes into selector constraints. -/
theorem t1CDoublePrimeBatch_model_card_le
    {c : Code} {n k d t : Nat} {batch : List BitString}
    (hbatch : batch ∈ t1CDoublePrimeBatches c n k d t)
    {w : BitString} (hw : w ∈ batch) :
    (canonicalPointListOfCode w).toFinset.card ≤
      2 ^ (n - k - 4) := by
  rw [t1CDoublePrimeBatches, List.mem_map] at hbatch
  obtain ⟨descriptionCode, _hdescription, rfl⟩ := hbatch
  rw [t1CDoublePrimeBatch, List.mem_filter] at hw
  obtain ⟨M, hM, hcode, hcard⟩ :=
    (t1ModelCodeValid_eq_true _ _).1 hw.2
  rw [hcode, canonicalPointListOfCode_codedUniformOn,
    canonicalFinsetList_toFinset]
  exact hcard

private theorem t1_flatten_length_le_mul
    {α : Type} (L : List (List α)) (bound : Nat)
    (hL : ∀ l ∈ L, l.length ≤ bound) :
    L.flatten.length ≤ L.length * bound := by
  induction L with
  | nil => simp
  | cons l L ih =>
      have hl : l.length ≤ bound := hL l (by simp)
      have htail : ∀ l' ∈ L, l'.length ≤ bound := by
        intro l' hl'
        exact hL l' (by simp [hl'])
      have hih := ih htail
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      calc
        l.length + L.flatten.length ≤ bound + L.length * bound :=
          Nat.add_le_add hl hih
        _ = (L.length + 1) * bound := by ring

theorem t1CDoublePrime_join_card_le
    (c : Code) (n k d t : Nat) :
    ((t1CDoublePrimeBatches c n k d t).flatten.toFinset).card ≤
      2 ^ (n + d + 1) := by
  calc
    ((t1CDoublePrimeBatches c n k d t).flatten.toFinset).card
        ≤ (t1CDoublePrimeBatches c n k d t).flatten.length :=
      List.toFinset_card_le _
    _ ≤ (t1CDoublePrimeBatches c n k d t).length * 2 ^ n :=
      t1_flatten_length_le_mul _ _ (fun batch hbatch =>
        t1CDoublePrimeBatch_length_le hbatch)
    _ ≤ 2 ^ (d + 1) * 2 ^ n := by
      gcongr
      exact (t1CDoublePrimeBatches_length_lt c n k d t).le
    _ = 2 ^ (n + d + 1) := by
      rw [← pow_add]
      congr 1
      omega

/-- Any duplicate-free or duplicate-containing list of already-seen `C″`
model codes inherits the global visible-family bound.  Mapping the codes to
their decoded finite models can only identify more elements, never increase
the number of distinct constraints. -/
theorem t1_seen_cdouble_family_card_le
    (c : Code) (n k d t : Nat) (seen : List BitString)
    (hseen : seen.toFinset ⊆
      (t1CDoublePrimeBatches c n k d t).flatten.toFinset) :
    ((seen.map fun w =>
      (canonicalPointListOfCode w).toFinset).toFinset).card ≤
        2 ^ (n + d + 1) := by
  calc
    ((seen.map fun w =>
        (canonicalPointListOfCode w).toFinset).toFinset).card
        ≤ seen.toFinset.card := by
          have himage :
              (seen.map fun w =>
                (canonicalPointListOfCode w).toFinset).toFinset =
                seen.toFinset.image (fun w =>
                  (canonicalPointListOfCode w).toFinset) := by
            ext M
            simp
          rw [himage]
          exact Finset.card_image_le
    _ ≤ (t1CDoublePrimeBatches c n k d t).flatten.toFinset.card :=
      Finset.card_le_card hseen
    _ ≤ 2 ^ (n + d + 1) :=
      t1CDoublePrime_join_card_le c n k d t

/-- Every already-seen `C″` code inherits the pointwise small-model bound
from the visible batch that introduced it. -/
theorem t1_seen_cdouble_model_card_le
    (c : Code) (n k d t : Nat) (seen : List BitString)
    (hseen : seen.toFinset ⊆
      (t1CDoublePrimeBatches c n k d t).flatten.toFinset)
    {w : BitString} (hw : w ∈ seen) :
    (canonicalPointListOfCode w).toFinset.card ≤
      2 ^ (n - k - 4) := by
  have hw_flat :
      w ∈ (t1CDoublePrimeBatches c n k d t).flatten := by
    rw [← List.mem_toFinset]
    exact hseen (List.mem_toFinset.mpr hw)
  rw [List.mem_flatten] at hw_flat
  obtain ⟨batch, hbatch, hw_batch⟩ := hw_flat
  exact t1CDoublePrimeBatch_model_card_le hbatch hw_batch

theorem t1CDoublePrimeBatches_stabilizes
    (c : Code) (n k d : Nat) :
    ∃ T, ∀ t, T ≤ t →
      t1CDoublePrimeBatches c n k d t =
        t1CDoublePrimeBatches c n k d T := by
  refine ⟨boundedOutputCompletionTime c d, fun t ht => ?_⟩
  unfold t1CDoublePrimeBatches t1DescriptionStage
  rw [boundedOutputStage_eq_completed_of_completion_le c d t ht,
    boundedOutputStage_eq_completed_at_completion]

/-- The `D` stream: length-`n` strings of plain complexity strictly below `k`.
The `k = 0` branch is explicit. -/
def t1DStage (c : Code) (n k t : Nat) : List BitString :=
  match k with
  | 0 => []
  | k + 1 =>
      (boundedOutputStage c k t).filter
        (fun w => decide (w.length = n))

theorem t1DStage_primrec (c : Code) :
    Primrec (fun p : (Nat × Nat) × Nat =>
      t1DStage c p.1.1 p.1.2 p.2) := by
  have hbase : Primrec (fun p : (Nat × Nat) × Nat =>
      ([] : List BitString)) := Primrec.const []
  have hstage : Primrec (fun p : (Nat × Nat) × Nat =>
      boundedOutputStage c p.1.2.pred p.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair
        (Primrec.pred.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have hlen : Primrec₂
      (fun (p : (Nat × Nat) × Nat) (w : BitString) =>
        decide (w.length = p.1.1)) := by
    have heq : Primrec (fun q : ((Nat × Nat) × Nat) × BitString =>
        decide (q.2.length = q.1.1.1)) :=
      PrimrecPred.decide
        (Primrec.eq.comp
          (Primrec.list_length.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    exact heq.to₂
  have hfiltered : Primrec (fun p : (Nat × Nat) × Nat =>
      (boundedOutputStage c p.1.2.pred p.2).filter
        (fun w => decide (w.length = p.1.1))) :=
    list_filter_primrec hstage hlen
  have hzero : Primrec (fun p : (Nat × Nat) × Nat =>
      decide (p.1.2 = 0)) :=
    PrimrecPred.decide
      (Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.const 0))
  refine (Primrec.cond hzero hbase hfiltered).of_eq ?_
  intro p
  unfold t1DStage
  cases p.1.2 <;> rfl

theorem t1DStage_computable (c : Code) :
    Computable (fun p : (Nat × Nat) × Nat =>
      t1DStage c p.1.1 p.1.2 p.2) :=
  (t1DStage_primrec c).to_comp

theorem t1DStage_zero (c : Code) (n t : Nat) :
    t1DStage c n 0 t = [] := rfl

theorem t1DStage_prefix (c : Code) (n k t : Nat) :
    t1DStage c n k t <+: t1DStage c n k (t + 1) := by
  cases k with
  | zero => exact List.prefix_refl []
  | succ k =>
      obtain ⟨rest, hrest⟩ := boundedOutputStage_prefix c k t
      change
        (boundedOutputStage c k t).filter
            (fun w => decide (w.length = n)) <+:
          (boundedOutputStage c k (t + 1)).filter
            (fun w => decide (w.length = n))
      rw [← hrest, List.filter_append]
      exact List.prefix_append _ _

theorem t1DStage_sound
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n k t : Nat} {w : BitString} (hw : w ∈ t1DStage c n k t) :
    w.length = n ∧ plainK V w < (k : ENat) := by
  cases k with
  | zero => simp [t1DStage] at hw
  | succ k =>
      rw [t1DStage, List.mem_filter, decide_eq_true_eq] at hw
      refine ⟨hw.2, ?_⟩
      have hcompleted : w ∈ completedBoundedOutput c k := by
        apply (boundedOutputStage_prefix_completed c k t).sublist.subset
        exact hw.1
      have hle :=
        (mem_completedBoundedOutput_iff_plainK_le hc k w).1 hcompleted
      exact hle.trans_lt (by exact_mod_cast Nat.lt_succ_self k)

theorem t1DStage_complete
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n k : Nat} {w : BitString}
    (hlen : w.length = n) (hcomp : plainK V w < (k : ENat)) :
    ∃ t, w ∈ t1DStage c n k t := by
  cases k with
  | zero => exact absurd hcomp (by simp)
  | succ k =>
      have hle : plainK V w ≤ (k : ENat) := by
        have hne : plainK V w ≠ ⊤ := ne_top_of_lt hcomp
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
        rw [← hm] at hcomp ⊢
        exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hcomp)
      refine ⟨boundedOutputCompletionTime c k, ?_⟩
      rw [t1DStage, List.mem_filter, decide_eq_true_eq,
        boundedOutputStage_eq_completed_at_completion]
      exact ⟨(mem_completedBoundedOutput_iff_plainK_le hc k w).2 hle,
        hlen⟩

theorem t1DStage_length_lt (c : Code) (n k t : Nat) :
    (t1DStage c n k t).length < 2 ^ k := by
  cases k with
  | zero => simp [t1DStage]
  | succ k =>
      refine (List.length_filter_le _ _).trans_lt ?_
      exact boundedOutputStage_length_lt c k t

theorem t1DStage_stabilizes (c : Code) (n k : Nat) :
    ∃ T, ∀ t, T ≤ t → t1DStage c n k t = t1DStage c n k T := by
  cases k with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | succ k =>
      refine ⟨boundedOutputCompletionTime c k, fun t ht => ?_⟩
      change
        (boundedOutputStage c k t).filter
            (fun w => decide (w.length = n)) =
          (boundedOutputStage c k (boundedOutputCompletionTime c k)).filter
            (fun w => decide (w.length = n))
      rw [boundedOutputStage_eq_completed_of_completion_le c k t ht,
        boundedOutputStage_eq_completed_at_completion]

end Kolmogorov
