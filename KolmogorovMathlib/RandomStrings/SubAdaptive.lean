/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.SubAdaptive.Basic

/-!
# Sub-adaptive oracle machines

Definitions for the classes of sub-adaptive polynomial-time reductions (Milovanov, CiE 2023: "in
the first step `M` asks non-adaptively several queries; in the second step `M` works strictly
sub-adaptively").

* `queryList M B x T`: the strings asked by `M` with oracle `B` on `x` at the times `t < T`, in
  order and with repetitions (one entry per `ask` step); its set of elements is `queries M B x T`.
* `answers M B x t`: the answers received at the asks made before time `t`, in order.  The nodes
  of the reduction tree are these answer histories (as in the paper), not configurations: equal
  histories give equal asks (`eq_of_answers_eq`, determinism), but branches that merge into one
  configuration remain distinct nodes.
* `StrictlySA M x T`: two asks at times `< T` (under arbitrary oracles) after distinct answer
  histories carry distinct query strings ("all nodes of the reduction tree carry distinct
  queries"); in particular no string is asked twice on one run, and distinct query configurations
  carry distinct strings (`StrictlySA.ne_of_run_ne`).  Equivalently (`strictlySA_iff_tree`), a
  string is asked at one time, after the same answers to all earlier queries (`answers_eq_iff`).
  `StrictlySubAdaptiveOn c e x` is this property of the clocked coded machine `(c, e)` on `x`.
* `SubAdaptive M x T` (two-stage version): for some `k`, the *set* of the first `k` strings asked
  within `T` steps does not depend on the oracle (stage 1), and two asks at times `< T` (under
  arbitrary oracles) made after at least `k` earlier asks, after distinct answer histories, carry
  distinct query strings (stage 2).  The stage boundary is the `k`-th ask, not a time: stage 1
  may take an answer-dependent number of steps.  `SubAdaptiveOn c e x` for clocked coded
  machines.
* `PolyTimeSA B`, `PolyTimeStrictSA B`: the sets decided with oracle `B` by machines that halt
  within a polynomial time bound under every oracle and are (strictly) sub-adaptive within it.
* Simple facts: a machine that never asks is strictly sub-adaptive; strict sub-adaptivity implies
  the two-stage version (`k = 0`), and so does non-adaptivity (`k = T`); the boundary can be taken
  `≤ T` (`subAdaptive_iff_exists_le`); a strictly sub-adaptive machine has fewer than
  `2 ^ (T + 1)` query configurations (and `querySet M x T` has fewer than `2 ^ (T + 1)` elements
  for every machine).
* Stage 1 (`stage1Set`, `card_stage1Set_le`, `stage1Set_subset_queries`,
  `mem_stage1Set_of_askedAt`, `run_eq_of_agree_stage1`, `stage1End`,
  `run_stage1End_eq_of_agree_stage1`, `eq_of_not_mem_stage1Set`, `SubAdaptive.exists_boundary`):
  with boundary `k`, the stage-1 set (the first `k` strings asked with the empty oracle) has at
  most `min k T` elements, lies on every run and contains every string asked after fewer than `k`
  earlier asks; up to the end of stage 1 (the time at which the `k`-th ask has been answered, or
  `T`) the run depends only on the oracle's restriction to it; and every string outside it is
  asked at a single node of the reduction tree.
* `exists_clocked_sa`, `exists_clocked_strictSA`: sets in `PolyTimeSA B` (`PolyTimeStrictSA B`) are
  decided by clocked coded machines that are (strictly) sub-adaptive on every input.
* `strictlySubAdaptiveB m e x`, `subAdaptiveB m e x`: decision procedures for
  `StrictlySubAdaptiveOn (decodeCode m) e x` and `SubAdaptiveOn (decodeCode m) e x`, by
  simulation with the finite oracles `L ⊆ queryListCode m e x`, which represent all oracles
  within the clock (`askNodes`: answer history and string of every ask), with their
  specifications and computability (the data of a `Family`, see `AFG/Instances.lean`).
* `SubAdaptiveTree M x T` (boundary-free two-stage version): every string asked within `T` steps
  is asked under every oracle, or is asked at a single node of the reduction tree (at one time,
  after the same answers to all earlier queries).  `SubAdaptiveTreeOn c e x` for clocked coded
  machines, `PolyTimeSATree B` for the class.  It is implied by the other notions
  (`StrictlySA.subAdaptiveTree`, `SubAdaptive.subAdaptiveTree`, `subAdaptiveTree_of_nonAdaptive`;
  class inclusions `polyTimeSA_subset_polyTimeSATree`, `polyTimeStrictSA_subset_polyTimeSATree`,
  `polyTimeTT_subset_polyTimeSATree`); `exists_clocked_saTree`; the always-asked set
  `alwaysAsked M x T` (at most `T` elements, on every run) outside which every asked string is
  asked at a unique node (`SubAdaptiveTree.eq_of_not_mem_alwaysAsked`: same time, configuration
  and answers), with the membership by address and nested histories properties
  (`SubAdaptiveTree.mem_queries_iff_agree`, `SubAdaptiveTree.history_subset`); the
  decision procedure `subAdaptiveTreeB` (`subAdaptiveTreeB_iff`, `subAdaptiveTreeB_computable`)
  and the computed always-asked set (`alwaysAskedB`, `alwaysAsked_eq_filter`).

Times are counted as in `queries M B x T` and `querySet M x T`: a query asked at time `t` (i.e. by
the configuration `run M B x t`) counts within `T` steps iff `t < T`; these are exactly the
queries on which the clocked verdict (`ClockedAccepts`, times `≤ clock`) depends.

The definitions and basic facts live in `SubAdaptive.Basic`; this module contains the decision
procedures for (strict and two-stage) sub-adaptivity, their computability, and boundary-free
two-stage sub-adaptivity.
-/

namespace Kolmogorov.RandomStrings

/-! ### Deciding (strict and two-stage) sub-adaptivity

Within the clock, the run depends only on the oracle's restriction to the possible queries
`queryListCode m e x`, so every oracle is represented by a finite oracle `{w | w ∈ L}` with `L` a
sublist of `queryListCode m e x` (`exists_allSub_agree`).  With a finite oracle, the asks are
computed by `queriesC` (`AFG/TT.lean`), the answers by `answersC` and the configurations by
`runC`. -/

/-- `queriesC` is the list of asks with the finite oracle `{w | w ∈ ans}`. -/
theorem queriesC_eq_queryList (m : ℕ) (ans : List BitString) (x : BitString) (T : ℕ) :
    queriesC m ans x T = queryList (decodeCode m).toOTM {w | w ∈ ans} x T := by
  unfold queriesC queryList
  congr 1
  funext s
  rw [askedAt_eq_of_rep m _ _ (runC_represents m ans x s)]
  cases askB m (runC m ans x s) <;> rfl

/-- Within `T` steps the run depends only on the oracle's restriction to the possible queries. -/
theorem run_eq_of_agree_querySet (M : OTM) (B B' : Set BitString) (x : BitString) (T : ℕ)
    (h : ∀ z ∈ querySet M x T, (z ∈ B ↔ z ∈ B')) {t : ℕ} (ht : t ≤ T) :
    run M B x t = run M B' x t :=
  run_eq_of_agree M B B' x t fun z hz =>
    h z (by rw [querySet, Set.Finite.mem_toFinset]; exact ⟨B, queries_mono M B x ht hz⟩)

/-- Within `T` steps the sequence of queries depends only on the oracle's restriction to the
possible queries. -/
theorem queryList_eq_of_agree_querySet (M : OTM) (B B' : Set BitString) (x : BitString) (T : ℕ)
    (h : ∀ z ∈ querySet M x T, (z ∈ B ↔ z ∈ B')) {t : ℕ} (ht : t ≤ T) :
    queryList M B x t = queryList M B' x t :=
  queryList_eq_of_run_eq fun _ hs => run_eq_of_agree_querySet M B B' x T h (hs.le.trans ht)

/-- Within `T` steps the sequence of answers depends only on the oracle's restriction to the
possible queries. -/
theorem answers_eq_of_agree_querySet (M : OTM) (B B' : Set BitString) (x : BitString) (T : ℕ)
    (h : ∀ z ∈ querySet M x T, (z ∈ B ↔ z ∈ B')) {t : ℕ} (ht : t ≤ T) :
    answers M B x t = answers M B' x t :=
  answers_congr (fun s hs => by rw [run_eq_of_agree_querySet M B B' x T h (hs.le.trans ht)])
    fun s hs z hz => h z (by
      rw [querySet, Set.Finite.mem_toFinset]
      exact ⟨B, (mem_queries M B x T z).2 ⟨s, by omega, hz⟩⟩)

/-- The answers received by the coded machine `decodeCode m` with the finite oracle
`{w | w ∈ ans}` on `x` at the asks made at times `s < t`, as a list. -/
def answersC (m : ℕ) (ans : List BitString) (x : BitString) (t : ℕ) : List Bool :=
  (List.range t).flatMap fun s =>
    bif askB m (runC m ans x s) then [memStr (runC m ans x s).buf ans] else []

/-- The sequence of answers with a finite oracle equals the sequence of answers computed by
`answersC`. -/
theorem answersC_eq_answers (m : ℕ) (ans : List BitString) (x : BitString) (t : ℕ) :
    answersC m ans x t = answers (decodeCode m).toOTM {w | w ∈ ans} x t := by
  unfold answersC answers
  congr 1
  funext s
  rw [askedAt_eq_of_rep m _ _ (runC_represents m ans x s)]
  cases askB m (runC m ans x s)
  · rfl
  · simp only [Bool.cond_true, Option.map_some, Option.toList_some, List.cons.injEq, and_true]
    exact Bool.eq_iff_iff.2
      ((memStr_iff _ _).trans (@decide_eq_true_iff _ (Classical.propDecidable _)).symm)

/-- Every oracle agrees on the possible queries with a finite oracle given by a sublist of
`queryListCode m e x`. -/
theorem exists_allSub_agree (m e : ℕ) (x : BitString) (B : Set BitString) :
    ∃ L ∈ allSub (queryListCode m e x),
      ∀ z ∈ querySet (decodeCode m).toOTM x (clock e x.length), (z ∈ B ↔ z ∈ {w | w ∈ L}) := by
  classical
  obtain ⟨L, hL, hLT⟩ := exists_allSub (queryListCode m e x)
    ((queryListCode m e x).toFinset.filter fun z => z ∈ B)
    fun z hz => List.mem_toFinset.1 (Finset.mem_filter.1 hz).1
  refine ⟨L, hL, fun z hz => ?_⟩
  rw [querySet_eq_toFinset] at hz
  change z ∈ B ↔ z ∈ L
  rw [← List.mem_toFinset (l := L), hLT, Finset.mem_filter]
  exact ⟨fun hB => ⟨hz, hB⟩, fun h' => h'.2⟩

/-- Equality of the sets of elements of two lists, as a test. -/
def sameSetB (S S' : List BitString) : Bool := subB S S' && subB S' S

/-- The sets of elements of two lists are equal iff `sameSetB` returns `true`. -/
theorem sameSetB_iff (S S' : List BitString) : sameSetB S S' = true ↔ S.toFinset = S'.toFinset := by
  simp only [sameSetB, Bool.and_eq_true, subB_iff]
  constructor
  · rintro ⟨h1, h2⟩
    ext z
    simp only [List.mem_toFinset]
    exact ⟨h1 z, h2 z⟩
  · intro h
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have hz' : z ∈ S.toFinset := List.mem_toFinset.2 hz
      rw [h] at hz'
      exact List.mem_toFinset.1 hz'
    · have hz' : z ∈ S'.toFinset := List.mem_toFinset.2 hz
      rw [← h] at hz'
      exact List.mem_toFinset.1 hz'

/-- The first stage with boundary `k`: for every finite oracle `L ⊆ queryListCode m e x`, the
first `k` asks within the clock form the same set as with the empty oracle. -/
def stage1B (m e : ℕ) (x : BitString) (k : ℕ) : Bool :=
  allB (allSub (queryListCode m e x)) fun L =>
    sameSetB ((queriesC m L x (clock e x.length)).take k)
      ((queriesC m [] x (clock e x.length)).take k)

/-- The stage-1 condition holds for boundary `k` iff `stage1B` returns `true`. -/
theorem stage1B_iff (m e : ℕ) (x : BitString) (k : ℕ) :
    stage1B m e x k = true ↔ ∀ B : Set BitString,
      ((queryList (decodeCode m).toOTM B x (clock e x.length)).take k).toFinset =
        ((queryList (decodeCode m).toOTM ∅ x (clock e x.length)).take k).toFinset := by
  unfold stage1B
  simp only [allB_iff, sameSetB_iff, queriesC_eq_queryList, setOf_mem_nil]
  constructor
  · intro h B
    obtain ⟨L, hL, hag⟩ := exists_allSub_agree m e x B
    rw [queryList_eq_of_agree_querySet _ B {w | w ∈ L} x _ hag le_rfl]
    exact h L hL
  · intro h L _
    exact h _

/-- The asks within the clock made after at least `k` earlier asks, under the finite oracles
`L ⊆ queryListCode m e x`: pairs (answers received before the ask, asked string). -/
def askNodes (m e : ℕ) (x : BitString) (k : ℕ) : List (List Bool × BitString) :=
  (allSub (queryListCode m e x)).flatMap fun L => (List.range (clock e x.length)).flatMap fun t =>
    bif decide (k ≤ (queriesC m L x t).length) && askB m (runC m L x t) then
      [(answersC m L x t, (runC m L x t).buf)] else []

/-- A pair `(ans, z)` is in `askNodes` iff `z` is asked after answers `ans` at a time `>= k`. -/
theorem mem_askNodes (m e : ℕ) (x : BitString) (k : ℕ) (p : List Bool × BitString) :
    p ∈ askNodes m e x k ↔ ∃ L ∈ allSub (queryListCode m e x), ∃ t < clock e x.length,
      k ≤ (queriesC m L x t).length ∧ askB m (runC m L x t) = true ∧
        (answersC m L x t, (runC m L x t).buf) = p := by
  simp only [askNodes, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨L, hL, t, ht, hc⟩
    cases hb : (decide (k ≤ (queriesC m L x t).length) && askB m (runC m L x t))
    · rw [hb] at hc
      simp at hc
    · rw [hb] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [Bool.cond_true, List.mem_singleton] at hc
      exact ⟨L, hL, t, ht, hb.1, hb.2, hc.symm⟩
  · rintro ⟨L, hL, t, ht, hk, ha, rfl⟩
    refine ⟨L, hL, t, ht, ?_⟩
    rw [decide_eq_true hk, ha]
    simp

/-- Every ask node is an ask after at least `k` earlier asks, with its answer history. -/
theorem askNodes_sound {m e : ℕ} {x : BitString} {k : ℕ} {p : List Bool × BitString}
    (hp : p ∈ askNodes m e x k) :
    ∃ (B : Set BitString) (t : ℕ), t < clock e x.length ∧
      k ≤ (queryList (decodeCode m).toOTM B x t).length ∧
      askedAt (decodeCode m).toOTM (run (decodeCode m).toOTM B x t) = some p.2 ∧
      answers (decodeCode m).toOTM B x t = p.1 := by
  obtain ⟨L, -, t, ht, hk, ha, rfl⟩ := (mem_askNodes m e x k p).1 hp
  refine ⟨{w | w ∈ L}, t, ht, by rwa [← queriesC_eq_queryList], ?_,
    (answersC_eq_answers m L x t).symm⟩
  rw [askedAt_eq_of_rep m _ _ (runC_represents m L x t), ha]
  rfl

/-- Every ask within the clock after at least `k` earlier asks is an ask node, with its answer
history. -/
theorem askNodes_complete {m e : ℕ} {x : BitString} {k : ℕ} {B : Set BitString} {t : ℕ}
    {z : BitString}
    (ht : t < clock e x.length) (hk : k ≤ (queryList (decodeCode m).toOTM B x t).length)
    (hz : askedAt (decodeCode m).toOTM (run (decodeCode m).toOTM B x t) = some z) :
    (answers (decodeCode m).toOTM B x t, z) ∈ askNodes m e x k := by
  obtain ⟨L, hL, hag⟩ := exists_allSub_agree m e x B
  have hrun := run_eq_of_agree_querySet _ B {w | w ∈ L} x _ hag ht.le
  have hql := queryList_eq_of_agree_querySet _ B {w | w ∈ L} x _ hag ht.le
  have hans := answers_eq_of_agree_querySet _ B {w | w ∈ L} x _ hag ht.le
  have hask := askedAt_eq_of_rep m _ _ (runC_represents m L x t)
  rw [← hrun, hz] at hask
  cases ha : askB m (runC m L x t)
  · rw [ha] at hask
    simp at hask
  · rw [ha] at hask
    simp only [Bool.cond_true, Option.some.injEq] at hask
    refine (mem_askNodes m e x k _).2 ⟨L, hL, t, ht, ?_, ha, ?_⟩
    · rw [queriesC_eq_queryList, ← hql]
      exact hk
    · rw [answersC_eq_answers, ← hans, hask]

/-- The history test with boundary `k`: two ask nodes (after at least `k` earlier asks) with the
same string have the same answer history. -/
def stage2B (m e : ℕ) (x : BitString) (k : ℕ) : Bool :=
  allB (askNodes m e x k) fun p => allB (askNodes m e x k) fun p' =>
    !decide (p.2 = p'.2) || decide (p.1 = p'.1)

/-- The stage-2 condition holds for boundary `k` iff `stage2B` returns `true`. -/
theorem stage2B_iff (m e : ℕ) (x : BitString) (k : ℕ) :
    stage2B m e x k = true ↔ ∀ (B B' : Set BitString) (t t' : ℕ) (z z' : BitString),
      t < clock e x.length → t' < clock e x.length →
      k ≤ (queryList (decodeCode m).toOTM B x t).length →
      k ≤ (queryList (decodeCode m).toOTM B' x t').length →
      askedAt (decodeCode m).toOTM (run (decodeCode m).toOTM B x t) = some z →
      askedAt (decodeCode m).toOTM (run (decodeCode m).toOTM B' x t') = some z' →
      answers (decodeCode m).toOTM B x t ≠ answers (decodeCode m).toOTM B' x t' → z ≠ z' := by
  unfold stage2B
  simp only [allB_iff, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq]
  constructor
  · intro h B B' t t' z z' ht ht' hk hk' hz hz' hne hzz
    rcases h _ (askNodes_complete ht hk hz) _ (askNodes_complete ht' hk' hz') with hb | ha
    · exact hb hzz
    · exact hne ha
  · intro h p hp p' hp'
    obtain ⟨B, t, ht, hk, hz, h1⟩ := askNodes_sound hp
    obtain ⟨B', t', ht', hk', hz', h1'⟩ := askNodes_sound hp'
    rw [← h1, ← h1']
    by_cases ha : answers (decodeCode m).toOTM B x t = answers (decodeCode m).toOTM B' x t'
    · exact Or.inr ha
    · exact Or.inl (h B B' t t' _ _ ht ht' hk hk' hz hz' ha)

/-- Decision procedure for the strict sub-adaptivity of the clocked coded machine
`(decodeCode m, e)` on `x`: the history test with boundary `0`. -/
def strictlySubAdaptiveB (m e : ℕ) (x : BitString) : Bool := stage2B m e x 0

/-- A clocked coded machine is strictly sub-adaptive iff `strictlySubAdaptiveB` returns `true`. -/
theorem strictlySubAdaptiveB_iff (m e : ℕ) (x : BitString) :
    strictlySubAdaptiveB m e x = true ↔ StrictlySubAdaptiveOn (decodeCode m) e x := by
  rw [strictlySubAdaptiveB, stage2B_iff]
  unfold StrictlySubAdaptiveOn StrictlySA
  constructor
  · intro h B B' t t' z z' ht ht' hz hz' hne
    exact h B B' t t' z z' ht ht' (Nat.zero_le _) (Nat.zero_le _) hz hz' hne
  · intro h B B' t t' z z' ht ht' _ _ hz hz' hne
    exact h B B' t t' z z' ht ht' hz hz' hne

/-- Decision procedure for the (two-stage) sub-adaptivity of the clocked coded machine
`(decodeCode m, e)` on `x`: some boundary `k ≤ clock e |x|` passes both stage tests. -/
def subAdaptiveB (m e : ℕ) (x : BitString) : Bool :=
  anyB (List.range (clock e x.length + 1)) fun k => stage1B m e x k && stage2B m e x k

/-- A clocked coded machine is sub-adaptive iff `subAdaptiveB` returns `true`. -/
theorem subAdaptiveB_iff (m e : ℕ) (x : BitString) :
    subAdaptiveB m e x = true ↔ SubAdaptiveOn (decodeCode m) e x := by
  rw [SubAdaptiveOn, subAdaptive_iff_exists_le]
  unfold subAdaptiveB
  simp only [anyB_iff, List.mem_range, Bool.and_eq_true, stage1B_iff, stage2B_iff]
  constructor
  · rintro ⟨k, hk, h1, h2⟩
    exact ⟨k, Nat.lt_succ_iff.1 hk, h1, h2⟩
  · rintro ⟨k, hk, h1, h2⟩
    exact ⟨k, Nat.lt_succ_of_le hk, h1, h2⟩

/-! ### Computability of the decision procedures -/

/-- The function `sameSetB` is primitive recursive. -/
theorem sameSetB_primrec : Primrec₂ sameSetB :=
  (Primrec.and.comp (subB_primrec.comp Primrec.fst Primrec.snd)
    (subB_primrec.comp Primrec.snd Primrec.fst)).of_eq fun _ => rfl

attribute [local irreducible] sameSetB queriesC allSub queryListCode clock in
/-- The function `stage1B` is primitive recursive. -/
theorem stage1B_primrec :
    Primrec fun a : (ℕ × ℕ × BitString) × ℕ => stage1B a.1.1 a.1.2.1 a.1.2.2 a.2 := by
  have hT : Primrec fun a : (ℕ × ℕ × BitString) × ℕ => clock a.1.2.1 a.1.2.2.length :=
    clock_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hQ : Primrec fun a : (ℕ × ℕ × BitString) × ℕ =>
      allSub (queryListCode a.1.1 a.1.2.1 a.1.2.2) :=
    allSub_primrec.comp (queryListCode_primrec.comp Primrec.fst)
  have harg : Primrec fun q : ((ℕ × ℕ × BitString) × ℕ) × (List BitString × Bool) =>
      (q.1.1.1, q.2.1, q.1.1.2.2, clock q.1.1.2.1 q.1.1.2.2.length) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair ((Primrec.fst.comp Primrec.snd).pair
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (hT.comp Primrec.fst)))
  have harg0 : Primrec fun q : ((ℕ × ℕ × BitString) × ℕ) × (List BitString × Bool) =>
      (q.1.1.1, ([] : List BitString), q.1.1.2.2, clock q.1.1.2.1 q.1.1.2.2.length) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair ((Primrec.const []).pair
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (hT.comp Primrec.fst)))
  have hk : Primrec fun q : ((ℕ × ℕ × BitString) × ℕ) × (List BitString × Bool) => q.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hL := Primrec.list_take.comp hk (queriesC_primrec.comp harg)
  have h0 := Primrec.list_take.comp hk (queriesC_primrec.comp harg0)
  have hh := Primrec.and.comp (sameSetB_primrec.comp hL h0) (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.id : Primrec fun q : ((ℕ × ℕ × BitString) × ℕ) × (List BitString × Bool) => q)))
  exact (Primrec.list_foldr hQ (Primrec.const true) hh.to₂).of_eq fun _ => rfl

/-- The function `answersC` is primitive recursive. -/
theorem answersC_primrec :
    Primrec fun p : ℕ × List BitString × BitString × ℕ => answersC p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hrun : Primrec fun q : (ℕ × List BitString × BitString × ℕ) × ℕ =>
      runC q.1.1 q.1.2.1 q.1.2.2.1 q.2 :=
    runC_primrec.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.snd.comp
      Primrec.fst)).pair ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        Primrec.fst))).pair Primrec.snd)))
  have hinner : Primrec₂ fun (q : ℕ × List BitString × BitString × ℕ) (s : ℕ) =>
      bif askB q.1 (runC q.1 q.2.1 q.2.2.1 s) then [memStr (runC q.1 q.2.1 q.2.2.1 s).buf q.2.1]
      else [] :=
    (Primrec.cond (askB_primrec.comp (Primrec.fst.comp Primrec.fst) hrun)
      (Primrec.list_cons.comp (memStr_primrec.comp (CC.primrec_buf.comp hrun)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const []))
      (Primrec.const [])).to₂
  exact (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.snd.comp (Primrec.snd.comp
    Primrec.snd))) hinner).of_eq fun _ => rfl

attribute [local irreducible] answersC queriesC runC askB allSub queryListCode clock in
/-- The function `askNodes` is primitive recursive. -/
theorem askNodes_primrec :
    Primrec fun a : (ℕ × ℕ × BitString) × ℕ => askNodes a.1.1 a.1.2.1 a.1.2.2 a.2 := by
  have hT : Primrec fun a : (ℕ × ℕ × BitString) × ℕ => clock a.1.2.1 a.1.2.2.length :=
    clock_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hQ : Primrec fun a : (ℕ × ℕ × BitString) × ℕ =>
      allSub (queryListCode a.1.1 a.1.2.1 a.1.2.2) :=
    allSub_primrec.comp (queryListCode_primrec.comp Primrec.fst)
  have harg : Primrec fun r : (((ℕ × ℕ × BitString) × ℕ) × List BitString) × ℕ =>
      (r.1.1.1.1, r.1.2, r.1.1.1.2.2, r.2) :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
      ((Primrec.snd.comp Primrec.fst).pair
        ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
          Primrec.fst)))).pair Primrec.snd))
  have hm : Primrec fun r : (((ℕ × ℕ × BitString) × ℕ) × List BitString) × ℕ => r.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hk : Primrec fun r : (((ℕ × ℕ × BitString) × ℕ) × List BitString) × ℕ => r.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hrun := runC_primrec.comp harg
  have hlen := Primrec.list_length.comp (queriesC_primrec.comp harg)
  have hnode := (answersC_primrec.comp harg).pair (CC.primrec_buf.comp hrun)
  have hinner := Primrec.cond (Primrec.and.comp (Primrec.nat_le.decide.comp hk hlen)
    (askB_primrec.comp hm hrun)) (Primrec.list_cons.comp hnode (Primrec.const []))
    (Primrec.const [])
  have hrange : Primrec fun p : ((ℕ × ℕ × BitString) × ℕ) × List BitString =>
      List.range (clock p.1.1.2.1 p.1.1.2.2.length) :=
    Primrec.list_range.comp (hT.comp Primrec.fst)
  have hmid := Primrec.list_flatMap hrange hinner.to₂
  exact (Primrec.list_flatMap hQ hmid.to₂).of_eq fun _ => rfl

attribute [local irreducible] askNodes in
/-- The function `stage2B` is primitive recursive. -/
theorem stage2B_primrec :
    Primrec fun a : (ℕ × ℕ × BitString) × ℕ => stage2B a.1.1 a.1.2.1 a.1.2.2 a.2 := by
  have hL := askNodes_primrec
  have hF : Primrec₂ fun (p p' : List Bool × BitString) =>
      (!decide (p.2 = p'.2) || decide (p.1 = p'.1)) :=
    (Primrec.or.comp (Primrec.not.comp (Primrec.eq.decide.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))) (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))).to₂
  have hin : Primrec fun b : ((ℕ × ℕ × BitString) × ℕ) × (List Bool × BitString) =>
      allB (askNodes b.1.1.1 b.1.1.2.1 b.1.1.2.2 b.1.2) fun p' =>
        !decide (b.2.2 = p'.2) || decide (b.2.1 = p'.1) :=
    (Primrec.list_foldr
      (f := fun b : ((ℕ × ℕ × BitString) × ℕ) × (List Bool × BitString) =>
        askNodes b.1.1.1 b.1.1.2.1 b.1.1.2.2 b.1.2)
      (g := fun _ => true)
      (h := fun b q => (!decide (b.2.2 = q.1.2) || decide (b.2.1 = q.1.1)) && q.2)
      (hL.comp Primrec.fst) (Primrec.const true)
      (Primrec.and.comp (hF.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  exact (Primrec.list_foldr
    (f := fun a : (ℕ × ℕ × BitString) × ℕ => askNodes a.1.1 a.1.2.1 a.1.2.2 a.2)
    (g := fun _ => true)
    (h := fun a q => (allB (askNodes a.1.1 a.1.2.1 a.1.2.2 a.2) fun p' =>
      !decide (q.1.2 = p'.2) || decide (q.1.1 = p'.1)) && q.2) hL (Primrec.const true)
    (Primrec.and.comp (hin.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

attribute [local irreducible] stage2B in
/-- The decision procedure `strictlySubAdaptiveB` is primitive recursive. -/
theorem strictlySubAdaptiveB_primrec :
    Primrec fun p : ℕ × ℕ × BitString => strictlySubAdaptiveB p.1 p.2.1 p.2.2 :=
  (stage2B_primrec.comp (Primrec.id.pair (Primrec.const 0))).of_eq fun _ => rfl

/-- The decision procedure `strictlySubAdaptiveB` is computable. -/
theorem strictlySubAdaptiveB_computable :
    Computable fun p : ℕ × ℕ × BitString => strictlySubAdaptiveB p.1 p.2.1 p.2.2 :=
  strictlySubAdaptiveB_primrec.to_comp

attribute [local irreducible] stage1B stage2B clock in
/-- The decision procedure `subAdaptiveB` is primitive recursive. -/
theorem subAdaptiveB_primrec :
    Primrec fun p : ℕ × ℕ × BitString => subAdaptiveB p.1 p.2.1 p.2.2 := by
  have hT : Primrec fun p : ℕ × ℕ × BitString => clock p.2.1 p.2.2.length :=
    clock_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  have h1 := stage1B_primrec
  have h2 := stage2B_primrec
  exact (Primrec.list_foldr
    (f := fun p : ℕ × ℕ × BitString => List.range (clock p.2.1 p.2.2.length + 1))
    (g := fun _ => false)
    (h := fun p q => (stage1B p.1 p.2.1 p.2.2 q.1 && stage2B p.1 p.2.1 p.2.2 q.1) || q.2)
    (Primrec.list_range.comp (Primrec.nat_add.comp hT (Primrec.const 1))) (Primrec.const false)
    (Primrec.or.comp (Primrec.and.comp (h1.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (h2.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))) (Primrec.snd.comp
        Primrec.snd)).to₂).of_eq fun _ => rfl

/-- The decision procedure `subAdaptiveB` is computable. -/
theorem subAdaptiveB_computable :
    Computable fun p : ℕ × ℕ × BitString => subAdaptiveB p.1 p.2.1 p.2.2 :=
  subAdaptiveB_primrec.to_comp

/-! ### Boundary-free two-stage sub-adaptivity

The two-stage notion without a stage boundary: every string asked within `T` steps is asked
under every oracle (it lies in the *always-asked set*
`alwaysAsked M x T`, the stage-1 queries), or is asked at a single node of the reduction tree
(at one time, after the same answers to all earlier queries).  It is implied by the other
notions: strict sub-adaptivity (`StrictlySA.subAdaptiveTree`, right disjunct), the ask-count
two-stage notion (`SubAdaptive.subAdaptiveTree`, with no extra hypothesis: by its stage-1
condition the set of the first `k` asks *within `T` steps* lies on every run, so stage 1 need not
be completed within `T` steps), and non-adaptivity (`subAdaptiveTree_of_nonAdaptive`, left
disjunct). -/

/-- Every query within `T` steps is asked under every oracle, or is asked at a single node of the
reduction tree (same time, same answers to all earlier queries). -/
def SubAdaptiveTree (M : OTM) (x : BitString) (T : ℕ) : Prop :=
  ∀ (B B' : Set BitString) (t t' : ℕ) (z : BitString), t < T → t' < T →
    askedAt M (run M B x t) = some z → askedAt M (run M B' x t') = some z →
    (∀ B'' : Set BitString, z ∈ queries M B'' x T) ∨
      (t = t' ∧ ∀ w ∈ queries M B x t, (w ∈ B ↔ w ∈ B'))

/-- The clocked coded machine `(c, e)` is sub-adaptive on `x` (boundary-free two-stage
version). -/
def SubAdaptiveTreeOn (c : OTMCode) (e : ℕ) (x : BitString) : Prop :=
  SubAdaptiveTree c.toOTM x (clock e x.length)

/-- The sets decided with oracle `B` by a machine which, under *every* oracle, halts on every
input `x` within `p(|x|)` steps, and which is sub-adaptive (boundary-free two-stage version) on
every input within `p(|x|)` steps. -/
def PolyTimeSATree (B : Set BitString) : Set (Set BitString) :=
  {A | ∃ (M : OTM) (p : Polynomial ℕ),
    (∀ (B' : Set BitString) (x : BitString), ∃ t ≤ p.eval x.length, Halted M (run M B' x t)) ∧
    (∀ x : BitString, SubAdaptiveTree M x (p.eval x.length)) ∧
    ∀ x : BitString, x ∈ A ↔ Accepts M B x}

/-- The right disjunct of `SubAdaptiveTree` says that the two asks are at the same node of the
reduction tree: after equal answer histories (`answers_eq_iff`). -/
theorem subAdaptiveTree_iff_answers {M : OTM} {x : BitString} {T : ℕ} :
    SubAdaptiveTree M x T ↔ ∀ (B B' : Set BitString) (t t' : ℕ) (z : BitString), t < T → t' < T →
      askedAt M (run M B x t) = some z → askedAt M (run M B' x t') = some z →
      (∀ B'' : Set BitString, z ∈ queries M B'' x T) ∨ answers M B x t = answers M B' x t' := by
  constructor
  · intro h B B' t t' z ht ht' hz hz'
    exact (h B B' t t' z ht ht' hz hz').imp_right (answers_eq_iff hz hz').2
  · intro h B B' t t' z ht ht' hz hz'
    exact (h B B' t t' z ht ht' hz hz').imp_right (answers_eq_iff hz hz').1

/-- Strict sub-adaptivity implies the boundary-free two-stage version (right disjunct). -/
theorem StrictlySA.subAdaptiveTree {M : OTM} {x : BitString} {T : ℕ} (h : StrictlySA M x T) :
    SubAdaptiveTree M x T := fun B B' t t' z ht ht' hz hz' =>
  Or.inr (strictlySA_iff_tree.1 h B B' t t' z ht ht' hz hz')

/-- The ask-count two-stage notion implies the boundary-free one: a string of the stage-1 set is
asked under every oracle (left disjunct, `stage1Set_subset_queries`), and a string outside it is
asked at a single node (right disjunct, `eq_of_not_mem_stage1Set`).  No hypothesis on the
completion of stage 1 is needed: the stage-1 condition of `SubAdaptive` concerns the first `k`
asks within `T` steps, so a run making fewer than `k` asks within `T` steps asks the whole stage-1
set.  (The boundaries `k = 0` and `k = T` are the strict and the non-adaptive cases, see
`StrictlySA.subAdaptiveTree` and `subAdaptiveTree_of_nonAdaptive`.) -/
theorem SubAdaptive.subAdaptiveTree {M : OTM} {x : BitString} {T : ℕ} (h : SubAdaptive M x T) :
    SubAdaptiveTree M x T := by
  obtain ⟨k, h1, h2⟩ := h
  intro B B' t t' z ht ht' hz hz'
  by_cases hQ : z ∈ stage1Set M x T k
  · exact Or.inl fun B'' => stage1Set_subset_queries h1 B'' hQ
  · exact Or.inr ((answers_eq_iff hz hz').1 (eq_of_not_mem_stage1Set h1 h2 ht ht' hz hz' hQ).1)

/-- A machine whose queries within `T` steps do not depend on the oracle is sub-adaptive in the
boundary-free sense (left disjunct). -/
theorem subAdaptiveTree_of_nonAdaptive {M : OTM} {x : BitString} {T : ℕ}
    (h : ∀ B : Set BitString, queries M B x T = queries M ∅ x T) : SubAdaptiveTree M x T := by
  intro B B' t t' z ht _ hz _
  refine Or.inl fun B'' => ?_
  rw [h B'', ← h B]
  exact (mem_queries M B x T z).2 ⟨t, ht, hz⟩

/-- Strict sub-adaptivity implies boundary-free sub-adaptivity. -/
theorem StrictlySubAdaptiveOn.subAdaptiveTreeOn {c : OTMCode} {e : ℕ} {x : BitString}
    (h : StrictlySubAdaptiveOn c e x) : SubAdaptiveTreeOn c e x :=
  StrictlySA.subAdaptiveTree h

/-- Two-stage sub-adaptivity implies boundary-free sub-adaptivity. -/
theorem SubAdaptiveOn.subAdaptiveTreeOn {c : OTMCode} {e : ℕ} {x : BitString}
    (h : SubAdaptiveOn c e x) : SubAdaptiveTreeOn c e x :=
  SubAdaptive.subAdaptiveTree h

/-- Non-adaptivity implies boundary-free sub-adaptivity. -/
theorem NonAdaptiveOn.subAdaptiveTreeOn {c : OTMCode} {e : ℕ} {x : BitString}
    (h : NonAdaptiveOn c e x) : SubAdaptiveTreeOn c e x :=
  subAdaptiveTree_of_nonAdaptive h

/-- The class `PolyTimeSA` is contained in `PolyTimeSATree`. -/
theorem polyTimeSA_subset_polyTimeSATree (B : Set BitString) : PolyTimeSA B ⊆ PolyTimeSATree B := by
  rintro A ⟨M, p, hh, hsa, hA⟩
  exact ⟨M, p, hh, fun x => (hsa x).subAdaptiveTree, hA⟩

/-- The class `PolyTimeStrictSA` is contained in `PolyTimeSATree`. -/
theorem polyTimeStrictSA_subset_polyTimeSATree (B : Set BitString) :
    PolyTimeStrictSA B ⊆ PolyTimeSATree B := by
  rintro A ⟨M, p, hh, hsa, hA⟩
  exact ⟨M, p, hh, fun x => (hsa x).subAdaptiveTree, hA⟩

/-- Truth-table reductions are sub-adaptive in the boundary-free sense. -/
theorem polyTimeTT_subset_polyTimeSATree (B : Set BitString) : PolyTimeTT B ⊆ PolyTimeSATree B := by
  rintro A ⟨M, p, hh, hna, hA⟩
  exact ⟨M, p, hh, fun x => subAdaptiveTree_of_nonAdaptive fun B' => hna B' x, hA⟩

/-- Boundary-free sub-adaptivity extends to longer time bounds for machines halted at time `T`
under every oracle. -/
theorem SubAdaptiveTree.mono_of_halted {M : OTM} {x : BitString} {T T' : ℕ}
    (h : SubAdaptiveTree M x T)
    (hTT : T ≤ T') (hH : ∀ B : Set BitString, Halted M (run M B x T)) : SubAdaptiveTree M x T' := by
  intro B B' t t' z _ _ hz hz'
  exact (h B B' t t' z (lt_of_askedAt_of_halted (hH B) hz) (lt_of_askedAt_of_halted (hH B') hz')
    hz hz').imp_left fun hall B'' => queries_mono M B'' x hTT (hall B'')

/-- A machine is boundary-free sub-adaptive iff its coded equivalent is. -/
theorem SubAdaptiveTree.code {M : OTM} {x : BitString} {T : ℕ} (h : SubAdaptiveTree M x T) :
    SubAdaptiveTree M.code.toOTM x T := by
  intro B B' t t' z ht ht' hz hz'
  simp only [OTM.run_code, OTM.askedAt_code] at hz hz'
  simp only [OTM.queries_code]
  exact h B B' t t' z ht ht' hz hz'

/-- Any set in `PolyTimeSATree B` is decided by a clocked coded machine with oracle `B` which is
sub-adaptive (boundary-free) on every input. -/
theorem exists_clocked_saTree (B A : Set BitString) (h : A ∈ PolyTimeSATree B) :
    ∃ (c : OTMCode) (e : ℕ), (∀ x, SubAdaptiveTreeOn c e x) ∧ ClockedDecides c e B A := by
  obtain ⟨M, p, hp, hsa, hA⟩ := h
  obtain ⟨e, he⟩ := exists_clock_ge p
  exact ⟨M.code, e, fun x => ((hsa x).mono_of_halted (he _)
    fun B' => halted_at_bound hp B' x).code,
    clockedDecides_code M p B A e he (hp B) hA⟩

/-! #### The always-asked set and unique nodes -/

open Classical in
/-- The always-asked set: the strings asked within `T` steps under every oracle (for a machine
sub-adaptive in the boundary-free sense, the stage-1 queries). -/
noncomputable def alwaysAsked (M : OTM) (x : BitString) (T : ℕ) : Finset BitString :=
  (querySet M x T).filter fun z => ∀ B : Set BitString, z ∈ queries M B x T

open Classical in
/-- A string is always asked iff it is asked under every oracle. -/
theorem mem_alwaysAsked {M : OTM} {x : BitString} {T : ℕ} {z : BitString} :
    z ∈ alwaysAsked M x T ↔ ∀ B : Set BitString, z ∈ queries M B x T := by
  unfold alwaysAsked
  rw [Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rw [querySet, Set.Finite.mem_toFinset]
  exact ⟨∅, h ∅⟩

/-- The always-asked set lies on every run. -/
theorem alwaysAsked_subset_queries (M : OTM) (x : BitString) (T : ℕ) (B : Set BitString) :
    alwaysAsked M x T ⊆ queries M B x T := fun _ hz => mem_alwaysAsked.1 hz B

/-- The always-asked set has at most `T` elements. -/
theorem card_alwaysAsked_le (M : OTM) (x : BitString) (T : ℕ) : (alwaysAsked M x T).card ≤ T :=
  (Finset.card_le_card (alwaysAsked_subset_queries M x T ∅)).trans (card_queries_le M ∅ x T)

/-- `SubAdaptiveTree` in terms of the always-asked set: every string asked within `T` steps
outside `alwaysAsked M x T` is asked at a single node of the reduction tree. -/
theorem subAdaptiveTree_iff_alwaysAsked {M : OTM} {x : BitString} {T : ℕ} :
    SubAdaptiveTree M x T ↔ ∀ (B B' : Set BitString) (t t' : ℕ) (z : BitString), t < T → t' < T →
      askedAt M (run M B x t) = some z → askedAt M (run M B' x t') = some z →
      z ∉ alwaysAsked M x T → t = t' ∧ ∀ w ∈ queries M B x t, (w ∈ B ↔ w ∈ B') := by
  constructor
  · intro h B B' t t' z ht ht' hz hz' hQ
    exact (h B B' t t' z ht ht' hz hz').resolve_left fun hall => hQ (mem_alwaysAsked.2 hall)
  · intro h B B' t t' z ht ht' hz hz'
    by_cases hQ : z ∈ alwaysAsked M x T
    · exact Or.inl (mem_alwaysAsked.1 hQ)
    · exact Or.inr (h B B' t t' z ht ht' hz hz' hQ)

/-- **Unique nodes outside the always-asked set** (ingredient of `exists_pathData`): for a
machine sub-adaptive in the boundary-free sense, a string outside `alwaysAsked M x T` asked
within `T` steps under the oracles `B` and `B'` is asked at the same time, in the same
configuration, after the same answers. -/
theorem SubAdaptiveTree.eq_of_not_mem_alwaysAsked {M : OTM} {x : BitString} {T : ℕ}
    (h : SubAdaptiveTree M x T) {B B' : Set BitString} {t t' : ℕ} {z : BitString} (ht : t < T)
    (ht' : t' < T) (hz : askedAt M (run M B x t) = some z)
    (hz' : askedAt M (run M B' x t') = some z) (hQ : z ∉ alwaysAsked M x T) :
    t = t' ∧ run M B x t = run M B' x t' ∧ answers M B x t = answers M B' x t' := by
  have he := (answers_eq_iff hz hz').2
    ((subAdaptiveTree_iff_alwaysAsked.1 h) B B' t t' z ht ht' hz hz' hQ)
  obtain ⟨e1, e2⟩ := eq_of_answers_eq hz hz' he
  exact ⟨e1, e2, he⟩

/-- **Membership by address** (machine side): for a machine sub-adaptive in the boundary-free
sense, if `z ∉ alwaysAsked M x T` is asked under `B₀` at a time
`t₀ < T`, then `z` is asked within `T` steps under an oracle `B` iff `B` agrees with `B₀` on the
queries asked under `B₀` before `t₀`. -/
theorem SubAdaptiveTree.mem_queries_iff_agree {M : OTM} {x : BitString} {T : ℕ}
    (h : SubAdaptiveTree M x T) {B₀ : Set BitString} {t₀ : ℕ} {z : BitString} (ht₀ : t₀ < T)
    (hz : askedAt M (run M B₀ x t₀) = some z) (hQ : z ∉ alwaysAsked M x T) (B : Set BitString) :
    z ∈ queries M B x T ↔ ∀ w ∈ queries M B₀ x t₀, (w ∈ B ↔ w ∈ B₀) := by
  constructor
  · intro hB
    obtain ⟨t, ht, hzB⟩ := (mem_queries M B x T z).1 hB
    obtain ⟨-, hag⟩ := (subAdaptiveTree_iff_alwaysAsked.1 h) B₀ B t₀ t z ht₀ ht hz hzB hQ
    exact fun w hw => (hag w hw).symm
  · intro hag
    refine (mem_queries M B x T z).2 ⟨t₀, ht₀, ?_⟩
    rw [← run_eq_of_agree M B₀ B x t₀ fun w hw => (hag w hw).symm]
    exact hz

/-- **Nested histories** (machine side): for a machine sub-adaptive in the boundary-free sense,
if `w ∉ alwaysAsked M x T` was asked under `B` before
time `t ≤ T`, and is asked under `B'` at a time `t' < T`, then the queries asked under `B'`
before `t'` were asked under `B` before `t`, with the same answers. -/
theorem SubAdaptiveTree.history_subset {M : OTM} {x : BitString} {T : ℕ} (h : SubAdaptiveTree M x T)
    {B B' : Set BitString} {t t' : ℕ} {w : BitString} (ht : t ≤ T) (ht' : t' < T)
    (hw : w ∈ queries M B x t) (hw' : askedAt M (run M B' x t') = some w)
    (hQ : w ∉ alwaysAsked M x T) :
    ∀ w' ∈ queries M B' x t', w' ∈ queries M B x t ∧ (w' ∈ B' ↔ w' ∈ B) := by
  intro w' hw'q
  obtain ⟨s, hs, hws⟩ := (mem_queries M B x t w).1 hw
  obtain ⟨hst, hag⟩ :=
    (subAdaptiveTree_iff_alwaysAsked.1 h) B B' s t' w (by omega) ht' hws hw' hQ
  rw [← hst, ← queries_eq_of_agree M B B' x s hag] at hw'q
  exact ⟨queries_mono M B x hs.le hw'q, (hag w' hw'q).symm⟩

/-! #### Deciding boundary-free sub-adaptivity -/

/-- The test that `z` is asked within the clock under every finite oracle
`L ⊆ queryListCode m e x` (hence under every oracle, `alwaysAskedB_iff`). -/
def alwaysAskedB (m e : ℕ) (x z : BitString) : Bool :=
  allB (allSub (queryListCode m e x)) fun L => memStr z (queriesC m L x (clock e x.length))

/-- A string is always asked iff `alwaysAskedB` returns `true`. -/
theorem alwaysAskedB_iff (m e : ℕ) (x z : BitString) :
    alwaysAskedB m e x z = true ↔
      ∀ B : Set BitString, z ∈ queries (decodeCode m).toOTM B x (clock e x.length) := by
  unfold alwaysAskedB
  simp only [allB_iff, memStr_iff, mem_queriesC]
  constructor
  · intro h B
    obtain ⟨L, hL, hag⟩ := exists_allSub_agree m e x B
    rw [queries_eq_of_agree_querySet _ B {w | w ∈ L} x _ hag]
    exact h L hL
  · intro h L _
    exact h _

/-- The always-asked set of a clocked coded machine, computed: the possible queries
`queryListCode m e x` passing the test `alwaysAskedB`. -/
theorem alwaysAsked_eq_filter (m e : ℕ) (x : BitString) :
    alwaysAsked (decodeCode m).toOTM x (clock e x.length) =
      ((queryListCode m e x).filter (alwaysAskedB m e x)).toFinset := by
  ext z
  rw [mem_alwaysAsked, List.mem_toFinset, List.mem_filter, alwaysAskedB_iff]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  rw [← List.mem_toFinset, ← querySet_eq_toFinset, querySet, Set.Finite.mem_toFinset]
  exact ⟨∅, h ∅⟩

/-- Decision procedure for `SubAdaptiveTreeOn (decodeCode m) e x`: two ask nodes (answer history,
string) of the finite oracles `L ⊆ queryListCode m e x` within the clock carrying the same string
have the same history, unless that string is asked under every finite oracle. -/
def subAdaptiveTreeB (m e : ℕ) (x : BitString) : Bool :=
  allB (askNodes m e x 0) fun p => alwaysAskedB m e x p.2 ||
    allB (askNodes m e x 0) fun p' => !decide (p.2 = p'.2) || decide (p.1 = p'.1)

/-- A clocked coded machine is boundary-free sub-adaptive iff `subAdaptiveTreeB` returns `true`. -/
theorem subAdaptiveTreeB_iff (m e : ℕ) (x : BitString) :
    subAdaptiveTreeB m e x = true ↔ SubAdaptiveTreeOn (decodeCode m) e x := by
  rw [SubAdaptiveTreeOn, subAdaptiveTree_iff_answers]
  unfold subAdaptiveTreeB
  simp only [allB_iff, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, alwaysAskedB_iff]
  constructor
  · intro h B B' t t' z ht ht' hz hz'
    rcases h _ (askNodes_complete (k := 0) ht (Nat.zero_le _) hz) with hall | hrest
    · exact Or.inl hall
    · rcases hrest _ (askNodes_complete (k := 0) ht' (Nat.zero_le _) hz') with hne | ha
      · exact (hne rfl).elim
      · exact Or.inr ha
  · intro h p hp
    obtain ⟨B, t, ht, -, hz, h1⟩ := askNodes_sound hp
    by_cases hall : ∀ B'' : Set BitString,
      p.2 ∈ queries (decodeCode m).toOTM B'' x (clock e x.length)
    · exact Or.inl hall
    · refine Or.inr fun p' hp' => ?_
      obtain ⟨B', t', ht', -, hz', h1'⟩ := askNodes_sound hp'
      by_cases hzz : p.2 = p'.2
      · rw [← hzz] at hz'
        rw [← h1, ← h1']
        exact Or.inr ((h B B' t t' p.2 ht ht' hz hz').resolve_left hall)
      · exact Or.inl hzz

attribute [local irreducible] queriesC allSub queryListCode clock in
/-- The function `alwaysAskedB` is primitive recursive. -/
theorem alwaysAskedB_primrec :
    Primrec fun a : (ℕ × ℕ × BitString) × BitString => alwaysAskedB a.1.1 a.1.2.1 a.1.2.2 a.2 := by
  have hT : Primrec fun a : (ℕ × ℕ × BitString) × BitString => clock a.1.2.1 a.1.2.2.length :=
    clock_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hQ : Primrec fun a : (ℕ × ℕ × BitString) × BitString =>
      allSub (queryListCode a.1.1 a.1.2.1 a.1.2.2) :=
    allSub_primrec.comp (queryListCode_primrec.comp Primrec.fst)
  have harg : Primrec fun q : ((ℕ × ℕ × BitString) × BitString) × (List BitString × Bool) =>
      (q.1.1.1, q.2.1, q.1.1.2.2, clock q.1.1.2.1 q.1.1.2.2.length) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair ((Primrec.fst.comp Primrec.snd).pair
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (hT.comp Primrec.fst)))
  have hz : Primrec fun q : ((ℕ × ℕ × BitString) × BitString) × (List BitString × Bool) => q.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hb : Primrec fun q : ((ℕ × ℕ × BitString) × BitString) × (List BitString × Bool) => q.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hh := Primrec.and.comp (memStr_primrec.comp hz (queriesC_primrec.comp harg)) hb
  exact (Primrec.list_foldr hQ (Primrec.const true) hh.to₂).of_eq fun _ => rfl

attribute [local irreducible] askNodes alwaysAskedB in
/-- The decision procedure `subAdaptiveTreeB` is primitive recursive. -/
theorem subAdaptiveTreeB_primrec :
    Primrec fun a : ℕ × ℕ × BitString => subAdaptiveTreeB a.1 a.2.1 a.2.2 := by
  have hL : Primrec fun a : ℕ × ℕ × BitString => askNodes a.1 a.2.1 a.2.2 0 :=
    (askNodes_primrec.comp (Primrec.id.pair (Primrec.const 0))).of_eq fun _ => rfl
  have hA : Primrec fun b : (ℕ × ℕ × BitString) × (List Bool × BitString) =>
      alwaysAskedB b.1.1 b.1.2.1 b.1.2.2 b.2.2 :=
    (alwaysAskedB_primrec.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).of_eq
      fun _ => rfl
  have hF : Primrec₂ fun (p p' : List Bool × BitString) =>
      (!decide (p.2 = p'.2) || decide (p.1 = p'.1)) :=
    (Primrec.or.comp (Primrec.not.comp (Primrec.eq.decide.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))) (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))).to₂
  have hin : Primrec fun b : (ℕ × ℕ × BitString) × (List Bool × BitString) =>
      allB (askNodes b.1.1 b.1.2.1 b.1.2.2 0) fun p' =>
        !decide (b.2.2 = p'.2) || decide (b.2.1 = p'.1) :=
    (Primrec.list_foldr
      (f := fun b : (ℕ × ℕ × BitString) × (List Bool × BitString) =>
        askNodes b.1.1 b.1.2.1 b.1.2.2 0)
      (g := fun _ => true)
      (h := fun b q => (!decide (b.2.2 = q.1.2) || decide (b.2.1 = q.1.1)) && q.2)
      (hL.comp Primrec.fst) (Primrec.const true)
      (Primrec.and.comp (hF.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  exact (Primrec.list_foldr
    (f := fun a : ℕ × ℕ × BitString => askNodes a.1 a.2.1 a.2.2 0)
    (g := fun _ => true)
    (h := fun a q => (alwaysAskedB a.1 a.2.1 a.2.2 q.1.2 ||
      allB (askNodes a.1 a.2.1 a.2.2 0) fun p' =>
        !decide (q.1.2 = p'.2) || decide (q.1.1 = p'.1)) && q.2) hL (Primrec.const true)
    (Primrec.and.comp (Primrec.or.comp (hA.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (hin.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- The decision procedure `subAdaptiveTreeB` is computable. -/
theorem subAdaptiveTreeB_computable :
    Computable fun p : ℕ × ℕ × BitString => subAdaptiveTreeB p.1 p.2.1 p.2.2 :=
  subAdaptiveTreeB_primrec.to_comp

/-! The families `Family.sa` and `Family.strictSA` are defined in `AFG/Instances.lean`. -/

end Kolmogorov.RandomStrings
