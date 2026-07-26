/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.Selection
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionSnapshot

/-!
# Effective selection inside a restricted family

This file makes the selection argument of `Restricted/Selection.lean` effective:
the candidate model codes of a family are enumerated by a genuinely computable
online strategy rather than chosen non-constructively.

The main ingredients are:
* `familyCandidateModelCodesList` — the stage-`t` list of codes that pass the
  primitive-recursive model test `isFamilyModelCodeBool`, together with its
  soundness, monotonicity and nodup lemmas;
* `selectionStrategyOnline` — the online dyadic selection strategy, shown
  computable and shown to cover every candidate (`selectionStrategyOnline_covers_of_list`);
* `familyMarkedCodeStream` — the resulting stream of marked codes, with its
  length bound (`familyMarkedCodeStream_length_bound`) and covering property
  (`familyMarkedCodeStream_covers`).
-/

namespace Kolmogorov

open CodedFiniteDistribution
open Nat.Partrec (Code)

/-- `List.sublists` (defined by a `foldr`) is primitive recursive. -/
theorem primrec_sublists_gen {α β} [Primcodable α] [Primcodable β]
    {f : α → List β} (hf : Primrec f) : Primrec (fun a => (f a).sublists) := by
  have hstep : Primrec₂ (fun (a : α) (p : β × List (List β)) =>
      List.flatMap (fun s => [s, p.1 :: s]) p.2) := by
    have hf' : Primrec (fun q : α × (β × List (List β)) => q.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hg' : Primrec₂ (fun (q : α × (β × List (List β))) (s : List β) =>
        [s, q.2.1 :: s]) := by
      have h2 : Primrec (fun r : (α × (β × List (List β))) × List β => r.1.2.1 :: r.2) :=
        Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
      exact (Primrec.list_cons.comp Primrec.snd
        (Primrec.list_cons.comp h2 (Primrec.const []))).to₂
    exact (Primrec.list_flatMap hf' hg').to₂
  exact Primrec.list_foldr hf (Primrec.const ([[]] : List (List β))) hstep

/-- Deciding list membership is primitive recursive jointly in the list and the
element (via a `foldr` of boolean equalities). -/
theorem decide_mem_primrec {β} [Primcodable β] [DecidableEq β] :
    Primrec₂ (fun (L : List β) (w : β) => decide (w ∈ L)) := by
  have heq : (fun (L : List β) (w : β) => decide (w ∈ L))
      = (fun L w => L.foldr (fun x acc => (w == x) || acc) false) := by
    funext L w
    induction L with
    | nil => simp
    | cons a t ih => simp [List.foldr_cons, ih, Bool.beq_eq_decide_eq]
  rw [heq]
  have hstep : Primrec₂ (fun (p : List β × β) (q : β × Bool) => (p.2 == q.1) || q.2) :=
    (Primrec.or.comp (Primrec.beq.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr Primrec.fst (Primrec.const false) hstep

/-- `List.all` with a primrec list and primrec predicate is primrec. -/
theorem list_all_primrec {α β} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).all (p a)) := by
  have heq : (fun a => (f a).all (p a))
      = (fun a => (f a).foldr (fun b acc => p a b && acc) true) := by
    funext a; induction f a with
    | nil => rfl
    | cons b t ih => simp [List.all_cons, ih]
  rw [heq]
  have hstep : Primrec₂ (fun (a : α) (q : β × Bool) => p a q.1 && q.2) :=
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const true) hstep

def isFamilyModelCodeBool (j : ℕ) (w : BitString) : Bool :=
  isCanonicalUniformCodeBool w &&
  decide (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset.card ≤ 2 ^ j)

def familyCandidateModelCodesList (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (j t : ℕ) :
    List BitString :=
  (𝒜.enumeration.enum t).filter (fun w =>
    decide (w ∈ (snapshotCodes c i t)) && isFamilyModelCodeBool j w)

/-
The family-model-code boolean test is primitive recursive in the code `w`
(for fixed `j`).
-/
theorem isFamilyModelCodeBool_primrec (j : ℕ) :
    Primrec (fun w : BitString => isFamilyModelCodeBool j w) := by
      refine Primrec.and.comp ?_ ?_
      · exact isCanonicalUniformCodeBool_primrec
      · -- The function that checks if the cardinality of the set is less than or equal to 2^j
        -- is primitive recursive.
        have h_card_le : Primrec (fun w => (canonicalFinsetList
          (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset)).length) := by
          convert Primrec.list_length.comp
            (Kolmogorov.canonicalFinsetList_toFinset_primrec.comp _) using 1;
          exact Primrec.list_map decodeDistributionData_primrec
            (entry_point_primrec.comp (Primrec.snd));
        convert Primrec.nat_le.comp h_card_le (Primrec.const (2 ^ j)) using 1
        simp +decide [PrimrecPred]

theorem familyCandidateModelCodesList_sound (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j t : ℕ) :
    ∀ w ∈ familyCandidateModelCodesList c i 𝒜 j t, IsFamilyModelCode 𝒜 j w := by
  intro w hw
  rw [familyCandidateModelCodesList, List.mem_filter] at hw
  rcases hw with ⟨hw_enum, hw_bool⟩
  have hmodel_bool : isFamilyModelCodeBool j w = true :=
    (Bool.and_eq_true_iff.mp hw_bool).2
  have hsize_bool : decide (((decodeDistributionData w).map
      CodedDistributionEntry.point).toFinset.card ≤ 2 ^ j) = true := by
    exact (Bool.and_eq_true_iff.mp hmodel_bool).2
  obtain ⟨S, hS, hmem, hcode⟩ := 𝒜.enumeration.sound t w hw_enum
  have hcard : S.card ≤ 2 ^ j := by
    have hdecoded : ((decodeDistributionData w).map
        CodedDistributionEntry.point).toFinset.card ≤ 2 ^ j :=
      decide_eq_true_eq.mp hsize_bool
    rw [hcode, dataPoints_codedUniformOn S hS, canonicalFinsetList_toFinset] at hdecoded
    exact hdecoded
  exact ⟨S, hS, hmem, hcode, hcard⟩

/-- Prefix-stable visible family model codes.  This deliberately accumulates
stage candidates instead of recomputing a filtered stage list: `snapshotCodes`
is monotone only as a membership predicate, so recomputation can insert newly
halting earlier programs before old outputs and break prefix monotonicity. -/
def familyStageModelCodesList (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (j : ℕ) :
    ℕ → List BitString
  | 0 => (familyCandidateModelCodesList c i 𝒜 j 0).eraseDups
  | t + 1 => (familyStageModelCodesList c i 𝒜 j t ++
      familyCandidateModelCodesList c i 𝒜 j (t + 1)).eraseDups

theorem familyStageModelCodesList_nodup (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j t : ℕ) :
    (familyStageModelCodesList c i 𝒜 j t).Nodup := by
  cases t <;> simp [familyStageModelCodesList, eraseDups_bitstring_nodup]

theorem familyStageModelCodesList_mono (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j t : ℕ) :
    familyStageModelCodesList c i 𝒜 j t <+:
      familyStageModelCodesList c i 𝒜 j (t + 1) := by
  change familyStageModelCodesList c i 𝒜 j t <+:
    (familyStageModelCodesList c i 𝒜 j t ++
      familyCandidateModelCodesList c i 𝒜 j (t + 1)).eraseDups
  exact prefix_eraseDups_append_of_nodup _ _ (familyStageModelCodesList_nodup c i 𝒜 j t)

theorem familyStageModelCodesList_sound (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j t : ℕ) :
    ∀ w ∈ familyStageModelCodesList c i 𝒜 j t, IsFamilyModelCode 𝒜 j w := by
  induction t with
  | zero =>
      intro w hw
      exact familyCandidateModelCodesList_sound c i 𝒜 j 0 w
        (List.mem_eraseDups.mp hw)
  | succ t ih =>
      intro w hw
      have hw' : w ∈ familyStageModelCodesList c i 𝒜 j t ++
          familyCandidateModelCodesList c i 𝒜 j (t + 1) := by
        exact List.mem_eraseDups.mp hw
      rcases List.mem_append.mp hw' with hprev | hnew
      · exact ih w hprev
      · exact familyCandidateModelCodesList_sound c i 𝒜 j (t + 1) w hnew

/-- Every accumulated family-model code visible by stage `t` is a snapshot code of
complexity `≤ i` at stage `t` (using snapshot-membership monotonicity for the
codes carried over from earlier stages). -/
theorem familyStageModelCodesList_mem_snapshot (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j t : ℕ) :
    ∀ w ∈ familyStageModelCodesList c i 𝒜 j t, w ∈ snapshotCodes c i t := by
  induction t with
  | zero =>
      intro w hw
      have hw' : w ∈ familyCandidateModelCodesList c i 𝒜 j 0 :=
        List.mem_eraseDups.mp hw
      rw [familyCandidateModelCodesList, List.mem_filter] at hw'
      exact decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp hw'.2).1
  | succ t ih =>
      intro w hw
      have hw' : w ∈ familyStageModelCodesList c i 𝒜 j t ++
          familyCandidateModelCodesList c i 𝒜 j (t + 1) :=
        List.mem_eraseDups.mp hw
      rcases List.mem_append.mp hw' with hprev | hnew
      · exact snapshotCodes_mem_of_le (Nat.le_succ t) (ih w hprev)
      · rw [familyCandidateModelCodesList, List.mem_filter] at hnew
        exact decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp hnew.2).1

/-- **Input-stream length bound.** The number of distinct family-model codes
visible by stage `t` is at most `2 ^ (i + 1)` (distinct snapshot codes of
complexity `≤ i`).  This is the `S.length ≤ 2 ^ (i + 1)` fact consumed by any
proof of `familyMarkedCodeStream_length_bound`; it is independent of the
`blockSelection` internals. -/
theorem familyStageModelCodesList_length_le (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j t : ℕ) :
    (familyStageModelCodesList c i 𝒜 j t).length ≤ 2 ^ (i + 1) := by
  classical
  have hsub : (familyStageModelCodesList c i 𝒜 j t).toFinset ⊆
      (snapshotCodes c i t).toFinset := by
    intro w hw
    rw [List.mem_toFinset] at hw ⊢
    exact familyStageModelCodesList_mem_snapshot c i 𝒜 j t w hw
  calc (familyStageModelCodesList c i 𝒜 j t).length
      = (familyStageModelCodesList c i 𝒜 j t).toFinset.card :=
        (List.toFinset_card_of_nodup (familyStageModelCodesList_nodup c i 𝒜 j t)).symm
    _ ≤ (snapshotCodes c i t).toFinset.card := Finset.card_le_card hsub
    _ ≤ (snapshotCodes c i t).length := List.toFinset_card_le _
    _ ≤ (boundedPrograms i).length := by
          unfold snapshotCodes; exact List.length_filterMap_le _ _
    _ ≤ 2 ^ (i + 1) := le_of_lt (length_boundedPrograms_lt i)

def computableGreedyCover {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : List α) (S : List β) (cover : β → List α) (_m : ℕ) (bound : ℕ) : List β :=
  match S.sublists.find? (fun C =>
      (T.all (fun x => decide (0 < (C.filter (fun b => decide (x ∈ cover b))).length)))
      && decide (C.length ≤ bound)) with
  | some C => C
  | none => []

theorem computableGreedyCover_sublist {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : List α) (S : List β) (cover : β → List α) (m bound : ℕ) :
    (computableGreedyCover T S cover m bound).Sublist S := by
  unfold computableGreedyCover
  cases hfind : S.sublists.find? (fun C =>
      (T.all (fun x => decide (0 < (C.filter (fun b => decide (x ∈ cover b))).length))) &&
        decide (C.length ≤ bound)) with
  | none =>
      exact List.nil_sublist S
  | some C =>
      rw [List.find?_eq_some_iff_getElem] at hfind
      obtain ⟨_hprop, r, hr, hget, _hmin⟩ := hfind
      have hmem : C ∈ S.sublists := by
        rw [List.mem_iff_getElem]
        exact ⟨r, hr, hget⟩
      exact (List.mem_sublists.mp hmem)

/-- `computableGreedyCover` written via `Option.getD` instead of the `match`. -/
theorem computableGreedyCover_eq {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : List α) (S : List β) (cover : β → List α) (m bound : ℕ) :
    computableGreedyCover T S cover m bound =
      (S.sublists.find? (fun C =>
        (T.all (fun x => decide (0 < (C.filter (fun b => decide (x ∈ cover b))).length))) &&
          decide (C.length ≤ bound))).getD [] := by
  unfold computableGreedyCover
  cases S.sublists.find? (fun C =>
      (T.all (fun x => decide (0 < (C.filter (fun b => decide (x ∈ cover b))).length))) &&
        decide (C.length ≤ bound)) <;> rfl

/-
With an empty target, the empty subcover already satisfies the predicate, and
since it is the first sublist examined, the greedy cover returns `[]`.
-/
theorem computableGreedyCover_eq_nil_of_target_nil {α β : Type} [DecidableEq α] [DecidableEq β]
    (S : List β) (cover : β → List α) (m bound : ℕ) :
    computableGreedyCover ([] : List α) S cover m bound = [] := by
      -- By definition of computableGreedyCover, when the target list is empty,
      -- the predicate is always true.
      simp [computableGreedyCover];
      cases h : List.find? (fun C => decide (C.length ≤ bound)) S.sublists
      <;> simp_all +decide [List.sublists]
      induction S <;> simp_all +decide [ List.foldr ];
      rw [ List.findSome?_eq_some_iff ] at h;
      grind

/-
The greedy cover never returns more than `bound` elements.
-/
theorem computableGreedyCover_length_le {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : List α) (S : List β) (cover : β → List α) (m bound : ℕ) :
    (computableGreedyCover T S cover m bound).length ≤ bound := by
      unfold computableGreedyCover;
      grind

/-- **Conditional coverage.** Whenever the greedy search finds a subcover (i.e.
the returned cover is nonempty, so `find?` returned `some C`), that subcover
covers every target `x ∈ T` at least once. The multiplicity parameter `m` is
used to define the target set in `blockSelection`; selected subcovers only need
to hit each target. -/
theorem computableGreedyCover_covers {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : List α) (S : List β) (cover : β → List α) (m bound : ℕ)
    (h : computableGreedyCover T S cover m bound ≠ [])
    (x : α) (hx : x ∈ T) :
    0 < ((computableGreedyCover T S cover m bound).filter
      (fun b => decide (x ∈ cover b))).length := by
  cases hfind : S.sublists.find? (fun C =>
      (T.all (fun x => decide (0 < (C.filter (fun b => decide (x ∈ cover b))).length))) &&
        decide (C.length ≤ bound)) with
  | none =>
      exfalso
      apply h
      unfold computableGreedyCover
      rw [hfind]
  | some C =>
      have hpred := List.find?_some hfind
      rw [Bool.and_eq_true_iff] at hpred
      have hall := hpred.1
      rw [List.all_eq_true] at hall
      have := hall x hx
      simp only [decide_eq_true_eq] at this
      unfold computableGreedyCover
      rw [hfind]
      simpa using this

/-- The `cover` map used inside `blockSelection` is primitive recursive. -/
theorem cover_primrec :
    Primrec (fun b : BitString =>
      canonicalFinsetList (((decodeDistributionData b).map
        CodedDistributionEntry.point).toFinset)) :=
  canonicalFinsetList_toFinset_primrec.comp
    (Primrec.list_map decodeDistributionData_primrec (entry_point_primrec.comp Primrec.snd))

/-- Membership of `x` in the cover of `b` is primitive recursive jointly. -/
theorem coverMem_primrec :
    Primrec₂ (fun (x : BitString) (b : BitString) =>
      decide (x ∈ canonicalFinsetList
        (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset))) :=
  ((decide_mem_primrec.comp (cover_primrec.comp Primrec.snd) Primrec.fst).to₂).of_eq
    (fun _ _ => by congr 1)

/-- The count of block elements whose cover contains `x` is primitive recursive
jointly in the block `C` and the string `x`. -/
theorem coverFilterCount_primrec :
    Primrec₂ (fun (C : List BitString) (x : BitString) =>
      (C.filter (fun b => decide (x ∈ canonicalFinsetList
        (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length) := by
  have hfilter : Primrec (fun r : (List BitString × BitString) =>
      r.1.filter (fun b => decide (r.2 ∈ canonicalFinsetList
        (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))) :=
    list_filter_primrec Primrec.fst
      (coverMem_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact (Primrec.list_length.comp hfilter).to₂

def selectionThreshold (i k : ℕ) : ℕ := (2 ^ k + i) / (i + 1)

theorem selectionThreshold_pos (i k : ℕ) : 0 < selectionThreshold i k := by
  unfold selectionThreshold
  have hp : 0 < 2 ^ k := pow_pos (by decide : 0 < 2) k
  have hle : i + 1 ≤ 2 ^ k + i := by omega
  exact Nat.div_pos hle (Nat.succ_pos i)

theorem pow_le_mul_selectionThreshold (i k : ℕ) : 2 ^ k ≤ (i + 1) * selectionThreshold i k := by
  unfold selectionThreshold
  set q := (2 ^ k + i) / (i + 1) with hq
  set r := (2 ^ k + i) % (i + 1) with hr
  have hdiv : (i + 1) * q + r = 2 ^ k + i := by
    rw [hq, hr]
    exact Nat.div_add_mod _ _
  have hr : r ≤ i := by
    have hlt : r < i + 1 := by
      rw [hr]
      exact Nat.mod_lt _ (Nat.succ_pos i)
    omega
  omega

def blockSelection (n i _j k _s : ℕ) (B : List BitString) : List BitString :=
  let m := selectionThreshold i k
  let bound := B.length * (n + 1) / m
  let cover w := canonicalFinsetList (((decodeDistributionData w).map
      CodedDistributionEntry.point).toFinset)
  let T := (allStrings n).filter (fun x =>
      decide (m ≤ (B.filter (fun b => decide (x ∈ cover b))).length))
  computableGreedyCover T B cover m bound

theorem blockSelection_sublist (n i j k s : ℕ) (B : List BitString) :
    (blockSelection n i j k s B).Sublist B := by
  unfold blockSelection
  exact computableGreedyCover_sublist _ _ _ _ _

/-
Length bound for a single block selection: at most `B.length*(n+1)/m0`
elements are returned, where `m0 = selectionThreshold i k`.
-/
theorem blockSelection_length_le (n i j k s : ℕ) (B : List BitString) :
    (blockSelection n i j k s B).length ≤
      B.length * (n + 1) / selectionThreshold i k := by
        unfold blockSelection;
        convert computableGreedyCover_length_le _ _ _ _ _ using 1

/-
If a nonempty block selection is returned, the window must have been at
least as long as the required multiplicity `m0 = selectionThreshold i k`.  (Covering
each target string `m0` times needs at least `m0` distinct block elements.)
-/
theorem blockSelection_length_ge_of_ne_nil (n i j k s : ℕ) (B : List BitString)
    (h : blockSelection n i j k s B ≠ []) :
    selectionThreshold i k ≤ B.length := by
  let m := selectionThreshold i k
  let cover := fun w : BitString =>
    canonicalFinsetList (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset)
  let T := (allStrings n).filter (fun x =>
    decide (m ≤ (B.filter (fun b => decide (x ∈ cover b))).length))
  let bound := B.length * (n + 1) / m
  have hblock :
      blockSelection n i j k s B = computableGreedyCover T B cover m bound := by
    rfl
  have hTne : T ≠ [] := by
    intro hT
    have hnil : computableGreedyCover T B cover m bound = [] := by
      rw [hT]
      exact computableGreedyCover_eq_nil_of_target_nil B cover m bound
    exact h (by rw [hblock, hnil])
  obtain ⟨x, hxT⟩ := List.exists_mem_of_ne_nil T hTne
  rw [List.mem_filter] at hxT
  have hcount : m ≤ (B.filter (fun b => decide (x ∈ cover b))).length :=
    decide_eq_true_eq.mp hxT.2
  have hfilter : (B.filter (fun b => decide (x ∈ cover b))).length ≤ B.length :=
    List.length_filter_le _ _
  exact hcount.trans hfilter

/-- A window shorter than the required multiplicity yields no selection. -/
theorem blockSelection_eq_nil_of_length_lt (n i j k s : ℕ) (B : List BitString)
    (h : B.length < selectionThreshold i k) :
    blockSelection n i j k s B = [] := by
  by_contra hne
  exact absurd (blockSelection_length_ge_of_ne_nil n i j k s B hne) (by omega)

/-
`blockSelection` (which ignores its `s` argument) is a primitive-recursive
function of the block `B`.
-/
theorem blockSelection_primrec (n i j k s : ℕ) :
    Primrec (fun B : List BitString => blockSelection n i j k s B) := by
  set m := selectionThreshold i k with hm
  have hpT : Primrec₂ (fun (B : List BitString) (x : BitString) =>
      decide (m ≤ (B.filter (fun b => decide (x ∈ canonicalFinsetList
        (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length)) :=
    (PrimrecPred.decide (Primrec.nat_le.comp (Primrec.const m)
      (coverFilterCount_primrec.comp Primrec.fst Primrec.snd))).to₂
  have hT : Primrec (fun B : List BitString =>
      (allStrings n).filter (fun x => decide (m ≤ (B.filter (fun b =>
        decide (x ∈ canonicalFinsetList
          (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length))) :=
    list_filter_primrec (Primrec.const (allStrings n)) hpT
  have hAllPred : Primrec₂ (fun (r : List BitString × List BitString) (x : BitString) =>
      decide (0 < (r.2.filter (fun b => decide (x ∈ canonicalFinsetList
        (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length)) :=
    (PrimrecPred.decide (Primrec.nat_lt.comp (Primrec.const 0)
      (coverFilterCount_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
  have hAll : Primrec (fun r : List BitString × List BitString =>
      ((allStrings n).filter (fun x => decide (m ≤ (r.1.filter (fun b =>
        decide (x ∈ canonicalFinsetList
          (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length))).all
        (fun x => decide (0 < (r.2.filter (fun b =>
          decide (x ∈ canonicalFinsetList
            (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length))) :=
    list_all_primrec (hT.comp Primrec.fst) hAllPred
  have hBound : Primrec (fun r : List BitString × List BitString =>
      decide (r.2.length ≤ r.1.length * (n + 1) / m)) :=
    PrimrecPred.decide (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.nat_div.comp
        (Primrec.nat_mul.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const (n + 1)))
        (Primrec.const m)))
  have hP : Primrec₂ (fun (B : List BitString) (C : List BitString) =>
      ((allStrings n).filter (fun x => decide (m ≤ (B.filter (fun b =>
        decide (x ∈ canonicalFinsetList
          (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length))).all
        (fun x => decide (0 < (C.filter (fun b =>
          decide (x ∈ canonicalFinsetList
            (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length)) &&
        decide (C.length ≤ B.length * (n + 1) / m)) :=
    (Primrec.and.comp hAll hBound).to₂
  have hg : Primrec (fun B : List BitString =>
      (B.sublists.find? (fun C =>
        ((allStrings n).filter (fun x => decide (m ≤ (B.filter (fun b =>
          decide (x ∈ canonicalFinsetList
            (((decodeDistributionData b).map
              CodedDistributionEntry.point).toFinset)))).length))).all
          (fun x => decide (0 < (C.filter (fun b =>
            decide (x ∈ canonicalFinsetList
              (((decodeDistributionData b).map
                CodedDistributionEntry.point).toFinset)))).length)) &&
          decide (C.length ≤ B.length * (n + 1) / m))).getD []) :=
    Primrec.option_getD.comp
      (list_find?_primrec (primrec_sublists_gen Primrec.id) hP) (Primrec.const [])
  apply hg.of_eq
  intro B
  unfold blockSelection
  rw [computableGreedyCover_eq]
  congr!

def selectionStrategyOnline (n i j k : ℕ) (S : List BitString) : List BitString :=
  (List.range S.length).flatMap (fun m =>
    let M := m + 1
    let S_acc := S.take M
    let blocks := List.range (i + 2) |>.filter (fun s => M % 2^s == 0)
    blocks.flatMap (fun s => blockSelection n i j k s (S_acc.drop (M - 2^s))))

theorem selectionStrategyOnline_mem_input (n i j k : ℕ) (S : List BitString) :
    ∀ w ∈ selectionStrategyOnline n i j k S, w ∈ S := by
  intro w hw
  unfold selectionStrategyOnline at hw
  rw [List.mem_flatMap] at hw
  rcases hw with ⟨m, _hm, hw⟩
  rw [List.mem_flatMap] at hw
  rcases hw with ⟨s, _hs, hw⟩
  have hsub := blockSelection_sublist n i j k s
    ((S.take (m + 1)).drop (m + 1 - 2 ^ s))
  exact List.mem_of_mem_take (List.mem_of_mem_drop (hsub.subset hw))

theorem selectionStrategyOnline_prefix_append_singleton
    (n i j k : ℕ) (S : List BitString) (a : BitString) :
    selectionStrategyOnline n i j k S <+:
      selectionStrategyOnline n i j k (S ++ [a]) := by
  unfold selectionStrategyOnline
  rw [show (S ++ [a]).length = S.length + 1 by simp]
  change
    (List.range S.length).flatMap (fun m =>
      let M := m + 1
      let S_acc := S.take M
      let blocks := List.range (i + 2) |>.filter (fun s => M % 2 ^ s == 0)
      blocks.flatMap (fun s => blockSelection n i j k s (S_acc.drop (M - 2 ^ s)))) <+:
    (List.range (S.length + 1)).flatMap (fun m =>
      let M := m + 1
      let S_acc := (S ++ [a]).take M
      let blocks := List.range (i + 2) |>.filter (fun s => M % 2 ^ s == 0)
      blocks.flatMap (fun s => blockSelection n i j k s (S_acc.drop (M - 2 ^ s))))
  rw [show List.range (S.length + 1) = List.range S.length ++ [S.length] by
    rw [show S.length + 1 = S.length.succ by omega, List.range_succ],
    List.flatMap_append]
  have hsame :
      (List.range S.length).flatMap (fun m =>
        let M := m + 1
        let S_acc := S.take M
        let blocks := List.range (i + 2) |>.filter (fun s => M % 2 ^ s == 0)
        blocks.flatMap (fun s => blockSelection n i j k s (S_acc.drop (M - 2 ^ s)))) =
      (List.range S.length).flatMap (fun m =>
        let M := m + 1
        let S_acc := (S ++ [a]).take M
        let blocks := List.range (i + 2) |>.filter (fun s => M % 2 ^ s == 0)
        blocks.flatMap (fun s => blockSelection n i j k s (S_acc.drop (M - 2 ^ s)))) := by
    apply List.flatMap_congr
    intro m hm
    have hM : m + 1 ≤ S.length := Nat.succ_le_of_lt (List.mem_range.mp hm)
    simp [List.take_append_of_le_length hM]
  rw [← hsame]
  exact List.prefix_append _ _

theorem selectionStrategyOnline_prefix_of_prefix (n i j k : ℕ)
    {S S' : List BitString} (h : S <+: S') :
    selectionStrategyOnline n i j k S <+:
      selectionStrategyOnline n i j k S' := by
  obtain ⟨r, rfl⟩ := h
  induction r using List.reverseRecOn with
  | nil =>
      simp
  | append_singleton r a ih =>
      have h1 : selectionStrategyOnline n i j k S <+:
          selectionStrategyOnline n i j k (S ++ r) := ih
      have h2 : selectionStrategyOnline n i j k (S ++ r) <+:
          selectionStrategyOnline n i j k ((S ++ r) ++ [a]) :=
        selectionStrategyOnline_prefix_append_singleton n i j k (S ++ r) a
      rw [← List.append_assoc]
      exact List.IsPrefix.trans h1 h2

def familyMarkedCodeStream (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (n j k t : ℕ) :
    List BitString :=
  selectionStrategyOnline n i j k (familyStageModelCodesList c i 𝒜 j t)

/-
The per-stage candidate list is computable as a function of the stage `t`
(the only non-primrec ingredient is `𝒜.enumeration.enum`, which is `Computable`).
-/
theorem familyCandidateModelCodesList_computable (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j : ℕ) :
    Computable (fun t => familyCandidateModelCodesList c i 𝒜 j t) := by
      unfold familyCandidateModelCodesList;
      have h_filter : Primrec (fun q : List BitString × ℕ => q.1.filter (fun w =>
          decide (w ∈ snapshotCodes c i q.2) && isFamilyModelCodeBool j w)) := by
        have h_mem : Primrec (fun a : (List BitString × ℕ) × BitString =>
            decide (a.2 ∈ snapshotCodes c i a.1.2)) :=
          (decide_mem_primrec.comp
              ((snapshotCodes_primrec c).comp
                (Primrec.pair (Primrec.const i) (Primrec.snd.comp Primrec.fst)))
              Primrec.snd).of_eq fun _ => decide_eq_decide.mpr Iff.rfl
        have h_pred : Primrec (fun a : (List BitString × ℕ) × BitString =>
            decide (a.2 ∈ snapshotCodes c i a.1.2) && isFamilyModelCodeBool j a.2) :=
          Primrec.and.comp h_mem ((isFamilyModelCodeBool_primrec j).comp Primrec.snd)
        exact list_filter_primrec Primrec.fst h_pred.to₂
      exact (h_filter.to_comp.comp
        (Computable.pair (𝒜.enumeration.computable) Computable.id)).of_eq fun _ => rfl

/-
The accumulated prefix-stable stage list is computable (via `Computable.nat_rec`
on `familyCandidateModelCodesList_computable` together with `eraseDups`).
-/
theorem familyStageModelCodesList_computable (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j : ℕ) :
    Computable (fun t => familyStageModelCodesList c i 𝒜 j t) := by
      refine Computable.of_eq
        (f := fun n => Nat.rec
          ( ( familyCandidateModelCodesList c i 𝒜 j 0 ).eraseDups )
          ( fun n IH =>
            ( IH ++ familyCandidateModelCodesList c i 𝒜 j ( n + 1 )
              ).eraseDups ) n) ?_ ?_;
      · convert Computable.nat_rec _ _ _ using 1
        rotate_left
        · exact fun n => n
        · exact fun _ => (familyCandidateModelCodesList c i 𝒜 j 0).eraseDups
        · exact fun n p => (p.2 ++ familyCandidateModelCodesList c i 𝒜 j (p.1 + 1)).eraseDups
        · exact Computable.id;
        · exact Computable.const _;
        · have h_eraseDups : Primrec (fun l : List BitString => l.eraseDups) :=
            eraseDups_bitstring_primrec
          have h_append : Primrec₂ (fun (l1 l2 : List BitString) => l1 ++ l2) :=
            Primrec.list_append
          exact h_eraseDups.to_comp.comp (h_append.to_comp.comp (Computable.snd.comp Computable.snd)
            ((familyCandidateModelCodesList_computable c i 𝒜 j).comp
            (Computable.succ.comp (Computable.fst.comp Computable.snd))))
        · rfl;
      · intro n; induction n <;> aesop;

/-- The online selection strategy is a total primitive-recursive list operation
(built from `range`, `take`, `drop`, `filter`, `flatMap`, `sublists`, `find?`). -/
theorem selectionStrategyOnline_primrec (n i j k : ℕ) :
    Primrec (fun S : List BitString => selectionStrategyOnline n i j k S) := by
  have hbs : Primrec₂ (fun (s : ℕ) (L : List BitString) => blockSelection n i j k s L) :=
    ((blockSelection_primrec n i j k 0).comp Primrec.snd).of_eq (fun _ => rfl)
  have key : Primrec (fun S : List BitString =>
      (List.range S.length).flatMap (fun m =>
        ((List.range (i + 2)).filter (fun s => (m + 1) % 2 ^ s == 0)).flatMap
          (fun s => blockSelection n i j k s ((S.take (m + 1)).drop ((m + 1) - 2 ^ s))))) := by
    refine Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) ?_
    refine Primrec.list_flatMap ?_ ?_
    · exact list_filter_primrec (Primrec.const (List.range (i + 2)))
        ((Primrec.beq.comp
          (Primrec.nat_mod.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
            (primrec_two_pow.comp Primrec.snd))
          (Primrec.const 0)).to₂)
    · exact hbs.comp Primrec.snd
        (Primrec.list_drop_listFirst.comp
          (Primrec.list_take_listFirst.comp (Primrec.fst.comp Primrec.fst)
            (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.nat_sub.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
            (primrec_two_pow.comp Primrec.snd)))
  exact key.of_eq (fun S => rfl)

theorem familyMarkedCodeStream_computable (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k : ℕ) :
  Computable (fun t => familyMarkedCodeStream c i 𝒜 n j k t) := by
  have h := (selectionStrategyOnline_primrec n i j k).to_comp.comp
    (familyStageModelCodesList_computable c i 𝒜 j)
  exact h

theorem familyMarkedCodeStream_mono (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (n j k t : ℕ) :
  familyMarkedCodeStream c i 𝒜 n j k t <+: familyMarkedCodeStream c i 𝒜 n j k (t + 1) := by
  exact selectionStrategyOnline_prefix_of_prefix n i j k
    (familyStageModelCodesList_mono c i 𝒜 j t)

theorem familyMarkedCodeStream_sound (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (n j k t : ℕ) :
  ∀ w ∈ familyMarkedCodeStream c i 𝒜 n j k t, IsFamilyModelCode 𝒜 j w := by
  intro w hw
  exact familyStageModelCodesList_sound c i 𝒜 j t w
    (selectionStrategyOnline_mem_input n i j k _ w hw)

/-- Each window `(S.take (m+1)).drop (m+1 - 2^s)` used by the online strategy has
length at most `2^s`. -/
theorem online_window_length_le (S : List BitString) (m s : ℕ) :
    ((S.take (m + 1)).drop (m + 1 - 2 ^ s)).length ≤ 2 ^ s := by
  rw [List.length_drop, List.length_take]
  exact (Nat.sub_le_sub_right (Nat.min_le_left _ _) _).trans
    (by rw [Nat.sub_sub_eq_min]; exact Nat.min_le_right _ _)

/-- Per-block bound: multiplying the number of selected block elements by the
selection threshold is at most `B.length * (n+1)`. -/
theorem blockSelection_length_mul_threshold (n i j k s : ℕ) (B : List BitString) :
    (blockSelection n i j k s B).length * selectionThreshold i k ≤ B.length * (n + 1) := by
  calc (blockSelection n i j k s B).length * selectionThreshold i k
      ≤ (B.length * (n + 1) / selectionThreshold i k) * selectionThreshold i k := by
        gcongr
        exact blockSelection_length_le n i j k s B
    _ ≤ B.length * (n + 1) := Nat.div_mul_le_self _ _

/-
Abstract combinatorial core of the online length bound.  Given per-pair data
`f m s` (the number of selected elements) and `w m s` (the window length) with
`f m s * m0 ≤ w m s * c` and `w m s ≤ 2 ^ s`, the total over the dyadic online
schedule is bounded by `cnt * L * c`.  The key point is that for each fixed block
size `s`, the windows are disjoint dyadic blocks, so their total length is at most
`L` (there are at most `L / 2^s` of them, each of length at most `2^s`).
-/
theorem online_double_sum_bound {cnt L m0 c : ℕ} (f w : ℕ → ℕ → ℕ)
    (hfw : ∀ m s, f m s * m0 ≤ w m s * c)
    (hw : ∀ m s, w m s ≤ 2 ^ s) :
    (((List.range L).map (fun m =>
        (((List.range cnt).filter (fun s => (m + 1) % 2 ^ s == 0)).map
          (fun s => f m s)).sum)).sum) * m0 ≤ cnt * L * c := by
            -- By Fubini's theorem, we can interchange the order of summation.
            have h_fubini : ∑ m ∈ Finset.range L,
                ∑ s ∈ Finset.filter (fun s => (m + 1) % 2 ^ s == 0) (Finset.range cnt), w m s ≤
                ∑ s ∈ Finset.range cnt,
                ∑ m ∈ Finset.filter (fun m => (m + 1) % 2 ^ s == 0) (Finset.range L), w m s := by
              simp +decide only [Finset.sum_filter];
              rw [ Finset.sum_comm ];
            -- By Fubini's theorem, we can interchange the order of summation in the goal.
            have h_fubini_goal : ∑ m ∈ Finset.range L,
                ∑ s ∈ Finset.filter (fun s => (m + 1) % 2 ^ s == 0) (Finset.range cnt), f m s * m0 ≤
                ∑ s ∈ Finset.range cnt,
                ∑ m ∈ Finset.filter (fun m => (m + 1) % 2 ^ s == 0) (Finset.range L),
                w m s * c := by
              refine le_trans (Finset.sum_le_sum fun m hm =>
                Finset.sum_le_sum fun s hs => hfw m s) ?_
              simpa only [ ← Finset.sum_mul _ _ _ ] using Nat.mul_le_mul_right _ h_fubini;
            -- Normalize the `List.sum` form of the goal into explicit `Finset.range` sums.
            have hrange : ∀ (N : ℕ) (g : ℕ → ℕ),
                ((List.range N).map g).sum = ∑ m ∈ Finset.range N, g m := by
              intro N g
              induction N with
              | zero => simp
              | succ N ih =>
                  rw [List.range_succ, List.map_append, List.sum_append, ih,
                    Finset.sum_range_succ]
                  simp
            have hrangeFilter : ∀ (N : ℕ) (p : ℕ → Bool) (g : ℕ → ℕ),
                (((List.range N).filter p).map g).sum
                  = ∑ s ∈ Finset.filter (fun s => p s = true) (Finset.range N), g s := by
              intro N p g
              induction N with
              | zero => simp
              | succ N ih =>
                  rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
                    Finset.range_add_one, Finset.filter_insert]
                  by_cases hp : p N = true
                  · rw [if_pos hp, Finset.sum_insert (by simp)]
                    simp [hp, Nat.add_comm]
                  · rw [if_neg hp]
                    simp [hp]
            rw [hrange]
            simp only [hrangeFilter]
            rw [Finset.sum_mul]
            simp only [Finset.sum_mul]
            refine h_fubini_goal.trans ?_;
            · refine le_trans (Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun m hm =>
                Nat.mul_le_mul_right _ (hw m s)) ?_
              norm_num [mul_assoc]
              refine le_trans (Finset.sum_le_sum fun i hi => Nat.mul_le_mul_right _ <|
                show Finset.card (Finset.filter (fun m => (m + 1) % 2 ^ i = 0) (Finset.range L)) ≤
                L / 2 ^ i from ?_) ?_
              · have hset : Finset.filter (fun m => (m + 1) % 2 ^ i = 0) (Finset.range L)
                    = Finset.filter (fun e => 2 ^ i ∣ e + 1) (Finset.range L) := by
                  ext x
                  simp [Nat.dvd_iff_mod_eq_zero]
                rw [hset]
                exact (Nat.card_multiples L (2 ^ i)).le
              · exact le_trans (Finset.sum_le_sum fun _ _ => show L / 2 ^ _ * (2 ^ _ * c) ≤ L * c by
                  nlinarith [Nat.div_mul_le_self L (2 ^ ‹_›), pow_pos (zero_lt_two' ℕ) ‹_›])
                  (by norm_num)

theorem selectionStrategyOnline_length_mul_threshold (n i j k : ℕ) (S : List BitString) :
    (selectionStrategyOnline n i j k S).length * selectionThreshold i k ≤
      (i + 2) * S.length * (n + 1) := by
  have heq : (selectionStrategyOnline n i j k S).length =
      ((List.range S.length).map (fun m =>
        (((List.range (i + 2)).filter (fun s => (m + 1) % 2 ^ s == 0)).map (fun s =>
          (blockSelection n i j k s
            ((S.take (m + 1)).drop (m + 1 - 2 ^ s))).length)).sum)).sum := by
    unfold selectionStrategyOnline
    simp only [List.length_flatMap]
  rw [heq]
  have h := online_double_sum_bound
      (cnt := i + 2) (L := S.length) (m0 := selectionThreshold i k) (c := n + 1)
      (f := fun m s => (blockSelection n i j k s ((S.take (m + 1)).drop (m + 1 - 2 ^ s))).length)
      (w := fun m s => ((S.take (m + 1)).drop (m + 1 - 2 ^ s)).length)
      (fun m s => blockSelection_length_mul_threshold n i j k s _)
      (fun m s => online_window_length_le S m s)
  exact h

theorem bound_of_mul_pow_le_mul_pow {L C i k : ℕ} (h : L * 2 ^ k ≤ C * 2 ^ (i + 1)) :
    L ≤ C * 2 ^ (i + 1 - k) := by
  by_cases hk : k ≤ i + 1
  · have hpow :
        C * 2 ^ (i + 1) = (C * 2 ^ (i + 1 - k)) * 2 ^ k := by
      calc
        C * 2 ^ (i + 1) = C * 2 ^ (i + 1 - k + k) := by
          rw [Nat.sub_add_cancel hk]
        _ = C * (2 ^ (i + 1 - k) * 2 ^ k) := by
          rw [pow_add]
        _ = (C * 2 ^ (i + 1 - k)) * 2 ^ k := by
          ring
    have hmul : L * 2 ^ k ≤ (C * 2 ^ (i + 1 - k)) * 2 ^ k := by
      simpa [hpow] using h
    exact Nat.le_of_mul_le_mul_right hmul (pow_pos (by decide : 0 < 2) k)
  · have hk' : i + 1 ≤ k := by omega
    have hpowle : 2 ^ (i + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hk'
    have hmul : L * 2 ^ k ≤ C * 2 ^ k :=
      h.trans (Nat.mul_le_mul_left C hpowle)
    have hLC : L ≤ C :=
      Nat.le_of_mul_le_mul_right hmul (pow_pos (by decide : 0 < 2) k)
    have hsub : i + 1 - k = 0 := by omega
    simpa [hsub] using hLC

theorem selectionStrategyOnline_length_bound_of_le (n i j k : ℕ) (S : List BitString)
    (h : S.length ≤ 2 ^ (i + 1)) :
    (selectionStrategyOnline n i j k S).length ≤ (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) := by
  have h1 : (selectionStrategyOnline n i j k S).length * selectionThreshold i k ≤
      (i + 2) * S.length * (n + 1) :=
    selectionStrategyOnline_length_mul_threshold n i j k S
  have h2 : (i + 2) * S.length * (n + 1) ≤ (i + 2) * 2 ^ (i + 1) * (n + 1) := by gcongr
  have h3 : (selectionStrategyOnline n i j k S).length * 2 ^ k ≤
      (selectionStrategyOnline n i j k S).length * ((i + 1) * selectionThreshold i k) := by
    gcongr
    exact pow_le_mul_selectionThreshold i k
  have h4 : (selectionStrategyOnline n i j k S).length * ((i + 1) * selectionThreshold i k) =
      (i + 1) * ((selectionStrategyOnline n i j k S).length * selectionThreshold i k) := by ring
  have h5 : (i + 1) * ((selectionStrategyOnline n i j k S).length * selectionThreshold i k) ≤
      (i + 1) * ((i + 2) * 2 ^ (i + 1) * (n + 1)) :=
    Nat.mul_le_mul_left (i + 1) (le_trans h1 h2)
  have h6 : (i + 1) * ((i + 2) * 2 ^ (i + 1) * (n + 1)) =
      (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1) := by ring
  have h7 : (selectionStrategyOnline n i j k S).length * 2 ^ k ≤
      (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1) :=
    calc (selectionStrategyOnline n i j k S).length * 2 ^ k
      _ ≤ (selectionStrategyOnline n i j k S).length * ((i + 1) * selectionThreshold i k) := h3
      _ = (i + 1) * ((selectionStrategyOnline n i j k S).length * selectionThreshold i k) := h4
      _ ≤ (i + 1) * ((i + 2) * 2 ^ (i + 1) * (n + 1)) := h5
      _ = (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1) := h6
  exact bound_of_mul_pow_le_mul_pow h7

/-- Membership completeness for the accumulated stage list: every candidate code
visible at stage `t` is retained in the accumulated list at stage `t`. -/
theorem mem_familyStageModelCodesList_of_candidate (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j t : ℕ) (w : BitString)
    (hw : w ∈ familyCandidateModelCodesList c i 𝒜 j t) :
    w ∈ familyStageModelCodesList c i 𝒜 j t := by
  cases t with
  | zero =>
      change w ∈ (familyCandidateModelCodesList c i 𝒜 j 0).eraseDups
      exact List.mem_eraseDups.mpr hw
  | succ t =>
      change w ∈ (familyStageModelCodesList c i 𝒜 j t ++
        familyCandidateModelCodesList c i 𝒜 j (t + 1)).eraseDups
      exact List.mem_eraseDups.mpr (List.mem_append_right _ hw)

/-- Completeness + cover: every visible family-description code of `x` is present
in the accumulated stage list, and its decoded model cover contains `x`. -/
theorem mem_familyStageModelCodesList_and_cover_of_description (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j t : ℕ) (x w : BitString)
    (hw : w ∈ familyStageDescriptionCodes c i 𝒜 j t x) :
    w ∈ familyStageModelCodesList c i 𝒜 j t ∧
      x ∈ canonicalFinsetList
        (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset) := by
  rw [mem_familyStageDescriptionCodes] at hw
  obtain ⟨hmem, hdesc⟩ := hw
  obtain ⟨hEnum, hSnap⟩ := Finset.mem_inter.mp hmem
  rw [List.mem_toFinset] at hEnum hSnap
  obtain ⟨Sset, hSne, hSmem, hcode, hScard, hxS⟩ := hdesc
  -- cover contains x
  have hcover : x ∈ canonicalFinsetList
      (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset) := by
    rw [hcode, dataPoints_codedUniformOn, canonicalFinsetList_toFinset,
      mem_canonicalFinsetList]
    exact hxS
  refine ⟨?_, hcover⟩
  -- w is in the candidate list, hence in the stage list
  have hbool : isFamilyModelCodeBool j w = true := by
    unfold isFamilyModelCodeBool
    refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
    · rw [isCanonicalUniformCodeBool_iff, hcode]
      exact isCanonicalUniformCode_codedUniformOn Sset hSne
    · refine decide_eq_true ?_
      rw [hcode, dataPoints_codedUniformOn, canonicalFinsetList_toFinset]
      exact hScard
  have hcand : w ∈ familyCandidateModelCodesList c i 𝒜 j t := by
    rw [familyCandidateModelCodesList, List.mem_filter]
    exact ⟨hEnum, Bool.and_eq_true_iff.mpr ⟨decide_eq_true hSnap, hbool⟩⟩
  exact mem_familyStageModelCodesList_of_candidate c i 𝒜 j t w hcand

/-- A family-model code whose decoded model cover contains `x` is a
family-description code of `x`. -/
theorem isFamilyDescriptionCode_of_model_cover (𝒜 : PreDescriptionFamily) (j : ℕ)
    (x w : BitString) (hmodel : IsFamilyModelCode 𝒜 j w)
    (hxw : x ∈ canonicalFinsetList
      (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset)) :
    IsFamilyDescriptionCode 𝒜 j x w := by
  obtain ⟨Sset, hSne, hmem, hcode, hcard⟩ := hmodel
  refine ⟨Sset, hSne, hmem, hcode, hcard, ?_⟩
  rw [hcode, dataPoints_codedUniformOn, canonicalFinsetList_toFinset,
    mem_canonicalFinsetList] at hxw
  exact hxw

theorem computableGreedyCover_covers_of_exists {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : List α) (S : List β) (cover : β → List α) (m bound : ℕ)
    (h_exists : ∃ C : List β, C.Sublist S ∧ C.length ≤ bound ∧
      ∀ x ∈ T, 0 < (C.filter (fun b => decide (x ∈ cover b))).length) :
    ∀ x ∈ T, 0 < ((computableGreedyCover T S cover m bound).filter (fun b =>
      decide (x ∈ cover b))).length := by
  let good : List β → Bool := fun C =>
    (T.all (fun x => decide (0 < (C.filter (fun b => decide (x ∈ cover b))).length))) &&
      decide (C.length ≤ bound)
  have hgood : ∃ C ∈ S.sublists, good C = true := by
    obtain ⟨C, hCS, hlen, hcov⟩ := h_exists
    refine ⟨C, List.mem_sublists.mpr hCS, ?_⟩
    rw [Bool.and_eq_true_iff]
    refine ⟨?_, decide_eq_true hlen⟩
    rw [List.all_eq_true]
    intro x hx
    exact decide_eq_true (hcov x hx)
  unfold computableGreedyCover
  cases hfind : S.sublists.find? (fun C =>
      (T.all (fun x => decide (0 < (C.filter (fun b => decide (x ∈ cover b))).length))) &&
        decide (C.length ≤ bound)) with
  | none =>
      obtain ⟨C, hCS, hCgood⟩ := hgood
      have hfind_good : S.sublists.find? good = none := by
        simpa [good] using hfind
      have hfalse := List.find?_eq_none.mp hfind_good C hCS
      simp [hCgood] at hfalse
  | some C =>
      have hpred : good C = true := List.find?_some hfind
      rw [Bool.and_eq_true_iff] at hpred
      have hall := hpred.1
      rw [List.all_eq_true] at hall
      intro x hx
      have hx' := hall x hx
      simpa using (decide_eq_true_eq.mp hx')

theorem zipIdx_nodup {α : Type} (L : List α) (start : ℕ) : (L.zipIdx start).Nodup := by
  apply List.Nodup.of_map Prod.snd
  rw [List.zipIdx_map_snd]
  exact List.nodup_range'

theorem zipIdx_map_fst {α : Type} (L : List α) (start : ℕ) :
    (L.zipIdx start).map Prod.fst = L := by
  induction L generalizing start with
  | nil => simp [List.zipIdx]
  | cons a as ih => simp [List.zipIdx, ih]

theorem zipIdx_filter_map_fst {α : Type} (L : List α) (P : α → Bool) (start : ℕ) :
    ((L.zipIdx start).filter (fun p => P p.1)).map Prod.fst = L.filter P := by
  induction L generalizing start with
  | nil => simp [List.zipIdx]
  | cons a as ih =>
      by_cases h : P a = true
      · simp [List.zipIdx, h, ih]
      · have hf : P a = false := by
          cases hpa : P a <;> simp_all
        simp [List.zipIdx, hf, ih]

theorem zipIdx_filter_mem_map_fst_sublist {α : Type} [DecidableEq α]
    (L : List α) (C : Finset (α × ℕ)) :
    (((L.zipIdx 0).filter (fun p => decide (p ∈ C))).map Prod.fst).Sublist L := by
  have hsub : ((L.zipIdx 0).filter (fun p => decide (p ∈ C))).Sublist (L.zipIdx 0) :=
    List.filter_sublist
  have hmap := hsub.map Prod.fst
  simpa [zipIdx_map_fst] using hmap

theorem blockSelection_covers_of_count (n i j k s : ℕ) (B : List BitString) (x : BitString)
    (hxlen : x.length = n)
    (hcount : selectionThreshold i k ≤ (B.filter (fun b => decide (x ∈ canonicalFinsetList
      (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length) :
    0 < ((blockSelection n i j k s B).filter (fun b => decide (x ∈ canonicalFinsetList
      (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length := by
  classical
  let m := selectionThreshold i k
  let cover : BitString → List BitString := fun b =>
    canonicalFinsetList (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)
  let T : List BitString := (allStrings n).filter (fun y =>
    decide (m ≤ (B.filter (fun b => decide (y ∈ cover b))).length))
  let Sidx : Finset (BitString × ℕ) := (B.zipIdx 0).toFinset
  let coverIdx : BitString × ℕ → Finset BitString := fun p => (cover p.1).toFinset
  let bound := B.length * (n + 1) / m
  let targetPred : BitString → Bool := fun b => decide (x ∈ cover b)
  have hxT : x ∈ T := by
    rw [List.mem_filter]
    refine ⟨(mem_allStrings n x).mpr hxlen, ?_⟩
    exact decide_eq_true (by simpa [m, cover] using hcount)
  have hm_pos : 0 < m := by simpa [m] using selectionThreshold_pos i k
  have hm : ∀ y ∈ T.toFinset, m ≤ (Sidx.filter (fun p => y ∈ coverIdx p)).card := by
    intro y hy
    have hyT : y ∈ T := List.mem_toFinset.mp hy
    rw [List.mem_filter] at hyT
    have hycount : m ≤ (B.filter (fun b => decide (y ∈ cover b))).length :=
      decide_eq_true_eq.mp hyT.2
    let Lidx : List (BitString × ℕ) := (B.zipIdx 0).filter (fun p => decide (y ∈ cover p.1))
    have hnod : Lidx.Nodup := by
      exact List.Sublist.nodup (l₁ := Lidx) (l₂ := B.zipIdx 0)
        List.filter_sublist (zipIdx_nodup B 0)
    have hfin : Lidx.toFinset = Sidx.filter (fun p => y ∈ coverIdx p) := by
      ext p
      simp [Lidx, Sidx, coverIdx]
    have hlen : Lidx.length = (B.filter (fun b => decide (y ∈ cover b))).length := by
      have hmap : Lidx.map Prod.fst = B.filter (fun b => decide (y ∈ cover b)) := by
        simpa [Lidx] using zipIdx_filter_map_fst B (fun b => decide (y ∈ cover b)) 0
      simpa using congrArg List.length hmap
    calc m ≤ (B.filter (fun b => decide (y ∈ cover b))).length := hycount
      _ = Lidx.length := hlen.symm
      _ = Lidx.toFinset.card := (List.toFinset_card_of_nodup hnod).symm
      _ = (Sidx.filter (fun p => y ∈ coverIdx p)).card := by rw [hfin]
  obtain ⟨C, hCS, hcov, hCbound⟩ := greedy_cover_indexed T.toFinset Sidx coverIdx m hm_pos hm
  have hTlog : Nat.log2 T.toFinset.card + 1 ≤ n + 1 := by
    have hcard : T.toFinset.card ≤ 2 ^ n := by
      calc T.toFinset.card ≤ T.length := List.toFinset_card_le _
        _ ≤ (allStrings n).length := List.Sublist.length_le List.filter_sublist
        _ = 2 ^ n := length_allStrings n
    by_cases hzero : T.toFinset.card = 0
    · simp [hzero]
    · have hltpow : T.toFinset.card < 2 ^ (n + 1) :=
        lt_of_le_of_lt hcard (Nat.pow_lt_pow_succ (by norm_num : 1 < 2))
      have hloglt : Nat.log 2 T.toFinset.card < n + 1 :=
        Nat.log_lt_of_lt_pow hzero hltpow
      have hlogle : Nat.log2 T.toFinset.card ≤ n := by
        rw [Nat.log2_eq_log_two]
        omega
      omega
  have hSidx_card : Sidx.card = B.length := by
    simp [Sidx, List.toFinset_card_of_nodup (zipIdx_nodup B 0), List.length_zipIdx]
  have hCmul : C.card * m ≤ B.length * (n + 1) := by
    calc C.card * m ≤ Sidx.card * (Nat.log2 T.toFinset.card + 1) := hCbound
      _ ≤ B.length * (n + 1) := by
        exact Nat.mul_le_mul (le_of_eq hSidx_card) hTlog
  have hCcard : C.card ≤ bound := by
    simpa [bound] using (Nat.le_div_iff_mul_le hm_pos).mpr hCmul
  let CList : List BitString := ((B.zipIdx 0).filter (fun p => decide (p ∈ C))).map Prod.fst
  have hCList_sub : CList.Sublist B := by
    simpa [CList] using zipIdx_filter_mem_map_fst_sublist B C
  have hCList_len : CList.length ≤ bound := by
    have hnod : ((B.zipIdx 0).filter (fun p => decide (p ∈ C))).Nodup := by
      exact List.Sublist.nodup
        (l₁ := (B.zipIdx 0).filter (fun p => decide (p ∈ C)))
        (l₂ := B.zipIdx 0) List.filter_sublist (zipIdx_nodup B 0)
    have hsubC : ((B.zipIdx 0).filter (fun p => decide (p ∈ C))).toFinset ⊆ C := by
      intro p hp
      rw [List.mem_toFinset, List.mem_filter] at hp
      exact decide_eq_true_eq.mp hp.2
    calc CList.length = ((B.zipIdx 0).filter (fun p => decide (p ∈ C))).length := by simp [CList]
      _ = ((B.zipIdx 0).filter (fun p => decide (p ∈ C))).toFinset.card :=
          (List.toFinset_card_of_nodup hnod).symm
      _ ≤ C.card := Finset.card_le_card hsubC
      _ ≤ bound := hCcard
  letI : BEq BitString := instBEqOfDecidableEq
  letI : LawfulBEq BitString := inferInstance
  have h_exists : ∃ C' : List BitString, C'.Sublist B ∧ C'.length ≤ bound ∧
      ∀ y ∈ T, 0 < (C'.filter (fun b => decide (y ∈ cover b))).length := by
    refine ⟨CList, hCList_sub, hCList_len, ?_⟩
    intro y hyT
    have hyFin : y ∈ T.toFinset := List.mem_toFinset.mpr hyT
    have hyUnion : y ∈ C.biUnion coverIdx := hcov hyFin
    rw [Finset.mem_biUnion] at hyUnion
    rcases hyUnion with ⟨p, hpC, hyp⟩
    have hpS : p ∈ Sidx := hCS hpC
    have hpZip : p ∈ B.zipIdx 0 := by
      exact List.mem_toFinset.mp hpS
    have hpFilt : p ∈ (B.zipIdx 0).filter (fun p => decide (p ∈ C)) := by
      rw [List.mem_filter]
      exact ⟨hpZip, decide_eq_true hpC⟩
    have hyCover : y ∈ cover p.1 := List.mem_toFinset.mp hyp
    have hyMem : p.1 ∈ CList.filter (fun b => decide (y ∈ cover b)) := by
      rw [List.mem_filter]
      refine ⟨?_, decide_eq_true hyCover⟩
      exact List.mem_map.mpr ⟨p, hpFilt, rfl⟩
    exact List.length_pos_of_mem hyMem
  have hgreedy := computableGreedyCover_covers_of_exists T B cover m bound h_exists x hxT
  have hfilter_eq :
      ((computableGreedyCover T B cover m bound).filter targetPred).length =
        ((computableGreedyCover T B cover m bound).filter (fun b =>
          decide (x ∈ cover b))).length := by
    congr 1
    apply List.filter_congr
    intro b _hb
    dsimp [targetPred]
    by_cases h : x ∈ cover b <;> simp [h]
  have hfinal : 0 < ((computableGreedyCover T B cover m bound).filter targetPred).length := by
    rw [hfilter_eq]
    exact hgreedy
  simpa [blockSelection, m, cover, T, bound, targetPred] using hfinal

/-- Arithmetic bridge: `selectionThreshold i k = (2^k + i)/(i+1)`, so a count `c`
with `2^k ≤ (i+1) * c` already reaches the threshold. -/
theorem selectionThreshold_le_of_pow_le (i k c : ℕ) (h : 2 ^ k ≤ (i + 1) * c) :
    selectionThreshold i k ≤ c := by
  unfold selectionThreshold
  rw [Nat.div_le_iff_le_mul_add_pred (Nat.succ_pos i)]
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  nlinarith [h, Nat.mul_comm c (i + 1)]

/-
**Dyadic averaging core.** For any list of length `≤ 2^b` (with `b ≥ 1`), the
whole segment `[0, len)` decomposes into at most `b` aligned dyadic windows (one
per set bit of `len`), so by pigeonhole one such window `[M - 2^s, M)` carries at
least a `1/b` share of the total filtered count. Proved by induction on `b`,
splitting `L` at the midpoint `2^(b-1)` into a full left dyadic block and a right
remainder handled by the induction hypothesis.
-/
theorem dyadic_core {α : Type} (b : ℕ) (hb : 1 ≤ b) (L : List α) (P : α → Bool)
    (hL : L.length ≤ 2 ^ b) :
    ∃ M s, M ≤ L.length ∧ s ≤ b ∧ M % 2 ^ s = 0 ∧
      (L.filter P).length ≤ b * (((L.take M).drop (M - 2 ^ s)).filter P).length := by
  induction b, Nat.succ_le_iff.mpr hb using Nat.le_induction generalizing L P with
  | base =>
    simp_all +decide only [Nat.succ_eq_add_one, zero_add, pow_succ', pow_zero,
      mul_one, one_mul, exists_and_left]
    rcases L with ( _ | ⟨ x, _ | ⟨ y, L ⟩ ⟩ )
    · exact ⟨0, by simp, 0, by simp, by simp, by simp⟩
    · exact ⟨1, by simp, 0, by simp, by simp, by cases P x <;> simp⟩
    · rw [List.filter_cons, List.filter_cons]
      aesop
  | succ b hb ih =>
    simp_all +decide only [Nat.succ_eq_add_one, zero_add, exists_and_left, forall_const,
      le_add_iff_nonneg_left, zero_le, pow_succ']
    -- Consider two cases: $L.length \leq 2^b$ and $2^b < L.length \leq 2^{b+1}$.
    by_cases h_case : L.length ≤ 2^b;
    · obtain ⟨ M, hM₁, x, hx₁, hx₂, hx₃ ⟩ := ih L P h_case
      exact ⟨ M, hM₁, x, Nat.le_succ_of_le hx₁, hx₂, by nlinarith ⟩
    · obtain ⟨M', s', hM's', hs', hM's'_mod, hM's'_bound⟩ :
          ∃ M' s', M' ≤ L.length - 2^b ∧ s' ≤ b ∧ M' % 2^s' = 0 ∧
          ((List.filter P (L.drop (2^b))).length ≤
            b * ((List.filter P ((L.drop (2^b)).take M' |>.drop (M' - 2^s'))).length)) := by
        specialize ih (L.drop (2^b)) P (by
        grind);
        aesop;
      by_cases h_case2 : (b + 1) * ((List.filter P (L.take (2^b))).length) ≥
        (List.filter P L).length
      · refine ⟨ 2 ^ b, ?_, b, ?_, ?_, ?_ ⟩ <;> norm_num;
        · linarith;
        · lia;
      · refine ⟨ 2 ^ b + M', ?_, s', ?_, ?_, ?_ ⟩ <;> try omega;
        · exact Nat.mod_eq_zero_of_dvd
            (dvd_add (pow_dvd_pow _ hs') (Nat.dvd_of_mod_eq_zero hM's'_mod))
        · have h_take_add : List.take (2 ^ b + M') L =
              List.take (2 ^ b) L ++ List.take M' (List.drop (2 ^ b) L) := by
            rw [List.take_add]
          have h_drop_add : List.drop (2 ^ b + M' - 2 ^ s')
              (List.take (2 ^ b) L ++ List.take M' (List.drop (2 ^ b) L)) =
              List.drop (M' - 2 ^ s') (List.take M' (List.drop (2 ^ b) L)) := by
            rw [ Nat.add_sub_assoc ]
            · rw [ List.drop_append ]
              rw [ List.drop_eq_nil_of_le ] <;> norm_num
              grind
            · by_cases hM'_zero : M' = 0
              · have h_eq : List.filter P L = List.filter P ( List.take ( 2 ^ b ) L ) := by
                  rw [ ← List.take_append_drop ( 2 ^ b ) L, List.filter_append ] ; aesop
                rw [ h_eq ] at h_case2
                nlinarith
              · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hM'_zero)
                  (Nat.dvd_of_mod_eq_zero hM's'_mod)
          rw [ h_take_add, h_drop_add ]
          have h_eq : List.filter P L = List.filter P (List.take (2 ^ b) L) ++
              List.filter P (List.drop (2 ^ b) L) := by
            rw [ ← List.filter_append, List.take_append_drop ]
          rw [ h_eq ]
          rw [ h_eq ] at h_case2
          norm_num at *
          nlinarith

theorem dyadic_block_of_many_positions {α : Type} (L : List α) (P : α → Bool)
    (i k : ℕ) (hL : L.length ≤ 2 ^ (i + 1)) (hP : 2 ^ k ≤ (L.filter P).length) :
    ∃ M s, M ≤ L.length ∧ s ≤ i + 1 ∧ M % 2 ^ s = 0 ∧
      selectionThreshold i k ≤ (((L.take M).drop (M - 2 ^ s)).filter P).length := by
  obtain ⟨M, s, hM, hs, hmod, hcount⟩ :=
    dyadic_core (i + 1) (Nat.le_add_left 1 i) L P hL
  exact ⟨M, s, hM, hs, hmod,
    selectionThreshold_le_of_pow_le i k _ (le_trans hP hcount)⟩

theorem selectionStrategyOnline_covers_of_list (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k t : ℕ)
    (S : List BitString) (hS : S = familyStageModelCodesList c i 𝒜 j t) :
    ∀ x : BitString, x.length = n →
      2 ^ k ≤ (familyStageDescriptionCodes c i 𝒜 j t x).card →
      ∃ w ∈ selectionStrategyOnline n i j k S, IsFamilyDescriptionCode 𝒜 j x w := by
  intro x hxlen hcount
  let P := fun (w : BitString) => decide (x ∈ canonicalFinsetList
      (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset))
  have hSlen : S.length ≤ 2 ^ (i + 1) := by
    rw [hS]
    exact familyStageModelCodesList_length_le c i 𝒜 j t
  have hP : 2 ^ k ≤ (S.filter P).length := by
    have hsub :
        familyStageDescriptionCodes c i 𝒜 j t x ⊆ (S.filter P).toFinset := by
      intro w hw
      obtain ⟨hwS, hcover⟩ :=
        mem_familyStageModelCodesList_and_cover_of_description c i 𝒜 j t x w hw
      rw [List.mem_toFinset, List.mem_filter]
      exact ⟨by simpa [hS] using hwS, decide_eq_true hcover⟩
    have hcard_le :
        (familyStageDescriptionCodes c i 𝒜 j t x).card ≤ (S.filter P).toFinset.card :=
      Finset.card_le_card hsub
    exact hcount.trans (hcard_le.trans (List.toFinset_card_le _))
  obtain ⟨M, s, hM, hs, hmod, hthresh⟩ := dyadic_block_of_many_positions S P i k hSlen hP
  have hM_pos : 0 < M := by
    by_contra h0
    have : M = 0 := by omega
    subst this
    simp at hthresh
    have := selectionThreshold_pos i k
    omega
  set m_idx := M - 1
  have hM_eq : M = m_idx + 1 := by omega
  have hthresh2 : selectionThreshold i k ≤
      (((S.take (m_idx + 1)).drop ((m_idx + 1) - 2 ^ s)).filter P).length := by
    rwa [← hM_eq]
  have hsel : 0 < ((blockSelection n i j k s
      ((S.take (m_idx + 1)).drop ((m_idx + 1) - 2 ^ s))).filter P).length := by
    exact blockSelection_covers_of_count n i j k s _ x hxlen hthresh2
  obtain ⟨w, hw⟩ := List.length_pos_iff_exists_mem.mp hsel
  rw [List.mem_filter] at hw
  refine ⟨w, ?_, ?_⟩
  · unfold selectionStrategyOnline
    rw [List.mem_flatMap]
    refine ⟨m_idx, ?_, ?_⟩
    · rw [List.mem_range]
      omega
    · rw [List.mem_flatMap]
      refine ⟨s, ?_, hw.1⟩
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [List.mem_range]
        omega
      · have heq : (m_idx + 1) % 2 ^ s = 0 := by
          rwa [← hM_eq]
        exact decide_eq_true heq
  · have hsub := blockSelection_sublist n i j k s ((S.take (m_idx + 1)).drop ((m_idx + 1) - 2 ^ s))
    have hwS : w ∈ ((S.take (m_idx + 1)).drop ((m_idx + 1) - 2 ^ s)) := hsub.subset hw.1
    have hwS2 : w ∈ S := List.mem_of_mem_take (List.mem_of_mem_drop hwS)
    have hmodel : IsFamilyModelCode 𝒜 j w := by
      rw [hS] at hwS2
      exact familyStageModelCodesList_sound c i 𝒜 j t w hwS2
    exact isFamilyDescriptionCode_of_model_cover 𝒜 j x w hmodel (decide_eq_true_eq.mp hw.2)

theorem familyMarkedCodeStream_length_bound (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k t : ℕ) :
  (familyMarkedCodeStream c i 𝒜 n j k t).length ≤
      (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) := by
  unfold familyMarkedCodeStream
  apply selectionStrategyOnline_length_bound_of_le
  exact familyStageModelCodesList_length_le c i 𝒜 j t

theorem familyMarkedCodeStream_covers (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (n j k t : ℕ) :
  ∀ x : BitString, x.length = n →
    2 ^ k ≤ (familyStageDescriptionCodes c i 𝒜 j t x).card →
    ∃ w ∈ familyMarkedCodeStream c i 𝒜 n j k t, IsFamilyDescriptionCode 𝒜 j x w := by
  intro x hxlen hmany
  unfold familyMarkedCodeStream
  exact selectionStrategyOnline_covers_of_list c i 𝒜 n j k t
    (familyStageModelCodesList c i 𝒜 j t) rfl x hxlen hmany

end Kolmogorov
