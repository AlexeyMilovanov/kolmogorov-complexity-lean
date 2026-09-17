import KolmogorovMathlib.Restricted.Selection

/-!
# Enumerating the candidate model codes of a family

The effective layer under the selection strategy: at each stage the codes the family has
enumerated so far are filtered down to those that are canonical uniform codes of sets with at
most `2 ^ j` points (`isFamilyModelCodeBool`, `familyCandidateModelCodesList`, with soundness
`familyCandidateModelCodesList_sound`), and everything in sight is shown primitive recursive or
computable — including the list primitives `primrec_sublists_gen` and `decide_mem_primrec` that
mathlib does not provide. `familyMarkedCodeStream` is the resulting stream of marked model codes:
the online selection applied to the accumulated stage codes.
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

/-- Decides that a string is a canonical uniform code whose set has at most `2 ^ j` points. -/
def isFamilyModelCodeBool (j : ℕ) (w : BitString) : Bool :=
  isCanonicalUniformCodeBool w &&
  decide (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset.card ≤ 2 ^ j)

/-- The codes enumerated by the family at stage `t` that also occur in the stage-`t` snapshot of
codes of complexity at most `i` and describe a set of at most `2 ^ j` points. -/
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
      · -- The cardinality bound is primitive recursive.
        have h_card_le : Primrec (fun w =>
            (canonicalFinsetList (((decodeDistributionData w).map
              CodedDistributionEntry.point).toFinset)).length) := by
          convert Primrec.list_length.comp (
              Kolmogorov.canonicalFinsetList_toFinset_primrec.comp _ ) using 1;
          exact Primrec.list_map decodeDistributionData_primrec ( entry_point_primrec.comp (
              Primrec.snd ) );
        convert Primrec.nat_le.comp h_card_le (Primrec.const (2 ^ j)) using 1
        simp +decide [PrimrecPred]

/-- Every candidate code is a family model code for the size bound `j`. -/
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

/-- The accumulated list of stage model codes has no repetitions. -/
theorem familyStageModelCodesList_nodup (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j t : ℕ) :
    (familyStageModelCodesList c i 𝒜 j t).Nodup := by
  cases t <;> simp [familyStageModelCodesList, nodup_eraseDups_bitString]

/-- Each stage of the accumulated model codes is a prefix of the next. -/
theorem familyStageModelCodesList_mono (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j t : ℕ) :
    familyStageModelCodesList c i 𝒜 j t <+:
      familyStageModelCodesList c i 𝒜 j (t + 1) := by
  change familyStageModelCodesList c i 𝒜 j t <+:
    (familyStageModelCodesList c i 𝒜 j t ++
      familyCandidateModelCodesList c i 𝒜 j (t + 1)).eraseDups
  exact prefix_eraseDups_append_of_nodup _ _ (familyStageModelCodesList_nodup c i 𝒜 j t)

/-- Every accumulated stage code is a family model code for the size bound `j`. -/
theorem familyStageModelCodesList_sound (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j t : ℕ) :
    ∀ w ∈ familyStageModelCodesList c i 𝒜 j t, IsFamilyModelCode 𝒜 j w := by
  induction t with
  | zero =>
      intro w hw
      exact familyCandidateModelCodesList_sound c i 𝒜 j 0 w
        (mem_eraseDups_bitString.mp hw)
  | succ t ih =>
      intro w hw
      have hw' : w ∈ familyStageModelCodesList c i 𝒜 j t ++
          familyCandidateModelCodesList c i 𝒜 j (t + 1) := by
        exact mem_eraseDups_bitString.mp hw
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
        mem_eraseDups_bitString.mp hw
      rw [familyCandidateModelCodesList, List.mem_filter] at hw'
      exact decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp hw'.2).1
  | succ t ih =>
      intro w hw
      have hw' : w ∈ familyStageModelCodesList c i 𝒜 j t ++
          familyCandidateModelCodesList c i 𝒜 j (t + 1) :=
        mem_eraseDups_bitString.mp hw
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

/-- A sublist of `S` of length at most `bound` that covers every element of `T`, found by
exhaustive search; the empty list if there is none. -/
def computableGreedyCover {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : List α) (S : List β) (cover : β → List α) (_m : ℕ) (bound : ℕ) : List β :=
  match S.sublists.find? (fun C => (T.all (fun x => decide (0 < (C.filter (fun b =>
      decide (x ∈ cover b))).length))) && decide (C.length ≤ bound)) with
  | some C => C
  | none => []

/-- The cover returned by the search is a sublist of the list it was chosen from. -/
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
  -- With an empty target, the empty subcover (the first sublist examined)
  -- already satisfies the predicate, so `find?` returns `[]`.
  rw [computableGreedyCover_eq]
  obtain ⟨t, ht⟩ : ∃ t, S.sublists = [] :: t := by
    induction S with
    | nil => exact ⟨[], rfl⟩
    | cons a l ih =>
        obtain ⟨t, ht⟩ := ih
        exact ⟨[a] :: t.flatMap fun x => [x, a :: x], by
          rw [List.sublists_cons, ht]
          rfl⟩
  rw [ht, List.find?_cons_of_pos (by simp)]
  rfl

/-
The greedy cover never returns more than `bound` elements.
-/
theorem computableGreedyCover_length_le {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : List α) (S : List β) (cover : β → List α) (m bound : ℕ) :
    (computableGreedyCover T S cover m bound).length ≤ bound := by
  unfold computableGreedyCover
  generalize hfind : S.sublists.find? _ = result
  cases result with
  | none => exact Nat.zero_le _
  | some C =>
      have hpred := List.find?_some hfind
      exact decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp hpred).2

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

/-- The multiplicity threshold `⌈2 ^ k / (i + 1)⌉` a string must reach in a block to be selected. -/
def selectionThreshold (i k : ℕ) : ℕ := (2 ^ k + i) / (i + 1)

/-- The selection threshold is positive. -/
theorem selectionThreshold_pos (i k : ℕ) : 0 < selectionThreshold i k := by
  unfold selectionThreshold
  have hp : 0 < 2 ^ k := pow_pos (by decide : 0 < 2) k
  have hle : i + 1 ≤ 2 ^ k + i := by omega
  exact Nat.div_pos hle (Nat.succ_pos i)

/-- The threshold is large enough: `2 ^ k ≤ (i + 1) · selectionThreshold i k`. -/
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

/-- The models selected from one block: a small subfamily covering every length-`n` string that
the block describes at least `selectionThreshold i k` times. -/
def blockSelection (n i _j k _s : ℕ) (B : List BitString) : List BitString :=
  let m := selectionThreshold i k
  let bound := B.length * (n + 1) / m
  let cover w :=
      canonicalFinsetList (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset)
  let T :=
      (allStrings n).filter (fun x =>
        decide (m ≤ (B.filter (fun b => decide (x ∈ cover b))).length))
  computableGreedyCover T B cover m bound

/-- The models selected from a block form a sublist of the block. -/
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

/-- The online selection: for every prefix of the input and every dyadic block ending there, the
models selected from that block. -/
def selectionStrategyOnline (n i j k : ℕ) (S : List BitString) : List BitString :=
  (List.range S.length).flatMap (fun m =>
    let M := m + 1
    let S_acc := S.take M
    let blocks := List.range (i + 2) |>.filter (fun s => M % 2^s == 0)
    blocks.flatMap (fun s => blockSelection n i j k s (S_acc.drop (M - 2^s))))

/-- Every selected model comes from the input list. -/
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

/-- Appending one code to the input extends the selection without changing its beginning. -/
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

/-- The selection is monotone under extension of the input: a prefix of the input yields a prefix
of the selection. -/
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

/-- The stream of marked model codes: the online selection applied to the accumulated stage list
of family model codes. -/
def familyMarkedCodeStream (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k t : ℕ) : List BitString :=
  selectionStrategyOnline n i j k (familyStageModelCodesList c i 𝒜 j t)

/-
The per-stage candidate list is computable as a function of the stage `t`
(the only non-primrec ingredient is `𝒜.enumeration.enum`, which is `Computable`).
-/
theorem familyCandidateModelCodesList_computable (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j : ℕ) :
    Computable (fun t => familyCandidateModelCodesList c i 𝒜 j t) := by
  unfold familyCandidateModelCodesList
  have harg : Primrec (fun a : (List BitString × ℕ) × BitString =>
      (i, a.1.2)) :=
    Primrec.pair (Primrec.const i) (Primrec.snd.comp Primrec.fst)
  have hw : Primrec (fun a : (List BitString × ℕ) × BitString => a.2) :=
    Primrec.snd
  have hmem := decide_mem_primrec.comp
    ((snapshotCodes_primrec c).comp harg) hw
  have hmodel : Primrec (fun a : (List BitString × ℕ) × BitString =>
      isFamilyModelCodeBool j a.2) :=
    (isFamilyModelCodeBool_primrec j).comp Primrec.snd
  have hpred := (Primrec.and.comp hmem hmodel).to₂
  have hfilter := list_filter_primrec Primrec.fst hpred
  refine (hfilter.to_comp.comp
    (Computable.pair 𝒜.enumeration.computable Computable.id)).of_eq ?_
  intro t
  apply List.filter_congr
  intro w _
  apply Bool.eq_iff_iff.mpr
  simp

/-
The accumulated prefix-stable stage list is computable (via `Computable.nat_rec`
on `familyCandidateModelCodesList_computable` together with `eraseDups`).
-/
theorem familyStageModelCodesList_computable (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j : ℕ) :
    Computable (fun t => familyStageModelCodesList c i 𝒜 j t) := by
  have herase : Primrec (fun l : List BitString => l.eraseDups) :=
    eraseDups_bitstring_primrec
  have happend : Primrec₂ (fun (l₁ l₂ : List BitString) => l₁ ++ l₂) :=
    Primrec.list_append
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × List BitString) =>
      (p.2 ++ familyCandidateModelCodesList c i 𝒜 j p.1.succ).eraseDups) :=
    (herase.to_comp.comp
      (happend.to_comp.comp
        (Computable.snd.comp Computable.snd)
        ((familyCandidateModelCodesList_computable c i 𝒜 j).comp
          (Computable.succ.comp (Computable.fst.comp Computable.snd))))).to₂
  refine (Computable.nat_rec Computable.id
    (Computable.const (familyCandidateModelCodesList c i 𝒜 j 0).eraseDups)
    hstep).of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [id, Nat.succ_eq_add_one] at ih
      simp only [id, familyStageModelCodesList, Nat.succ_eq_add_one]
      rw [ih]

end Kolmogorov
