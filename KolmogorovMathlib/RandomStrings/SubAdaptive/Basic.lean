/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TT

/-!
# Sub-adaptive oracle machines: definitions and basic facts

The list of asked strings, answer histories, the definitions of (strict and two-stage)
sub-adaptivity and of the classes `PolyTimeSA`, `PolyTimeStrictSA`, simple facts, stage 1,
longer time bounds and coded machines, and the counting of query configurations.

Part of `KolmogorovMathlib.RandomStrings.SubAdaptive`.
-/

namespace Kolmogorov.RandomStrings

/-! ### The list of asked strings -/

/-- The strings asked by `M` with oracle `B` on input `x` at the times `t < T`, in order and with
repetitions (one entry for every `ask` step). -/
noncomputable def queryList (M : OTM) (B : Set BitString) (x : BitString) (T : ℕ) :
    List BitString :=
  (List.range T).flatMap fun t => (askedAt M (run M B x t)).toList

/-- No strings are asked in zero steps. -/
theorem queryList_zero (M : OTM) (B : Set BitString) (x : BitString) : queryList M B x 0 = [] := by
  simp [queryList]

/-- The list of strings asked within `T + 1` steps is the list of strings asked within `T` steps,
followed by the string asked at step `T` if any. -/
theorem queryList_succ (M : OTM) (B : Set BitString) (x : BitString) (T : ℕ) :
    queryList M B x (T + 1) = queryList M B x T ++ (askedAt M (run M B x T)).toList := by
  simp [queryList, List.range_succ, List.flatMap_append]

/-- Membership in `queryList`: `z` was asked at some time `s < T`. -/
theorem mem_queryList (M : OTM) (B : Set BitString) (x : BitString) (T : ℕ) (z : BitString) :
    z ∈ queryList M B x T ↔ ∃ s < T, askedAt M (run M B x s) = some z := by
  simp [queryList]

/-- The asked strings form the set `queries M B x T`. -/
theorem queryList_toFinset (M : OTM) (B : Set BitString) (x : BitString) (T : ℕ) :
    (queryList M B x T).toFinset = queries M B x T := by
  ext z
  rw [List.mem_toFinset, mem_queryList, mem_queries]

/-- At most one ask per step. -/
theorem length_queryList_succ_le (M : OTM) (B : Set BitString) (x : BitString) (T : ℕ) :
    (queryList M B x (T + 1)).length ≤ (queryList M B x T).length + 1 := by
  rw [queryList_succ, List.length_append]
  cases askedAt M (run M B x T) <;> simp

/-- At most `T` strings are asked within `T` steps. -/
theorem length_queryList_le (M : OTM) (B : Set BitString) (x : BitString) (T : ℕ) :
    (queryList M B x T).length ≤ T := by
  induction T with
  | zero => simp [queryList_zero]
  | succ T ih => exact (length_queryList_succ_le M B x T).trans (by omega)

/-- The asks made within `t ≤ T` steps are an initial segment of those made within `T` steps. -/
theorem queryList_prefix (M : OTM) (B : Set BitString) (x : BitString) {t T : ℕ} (h : t ≤ T) :
    queryList M B x t <+: queryList M B x T := by
  induction T, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ T _ ih =>
    rw [queryList_succ]
    exact ih.trans (List.prefix_append _ _)

/-- The number of asked strings is non-decreasing in time. -/
theorem length_queryList_mono (M : OTM) (B : Set BitString) (x : BitString) {t T : ℕ} (h : t ≤ T) :
    (queryList M B x t).length ≤ (queryList M B x T).length :=
  (queryList_prefix M B x h).length_le

/-- Taking the length of `queryList` at time `t` from the `queryList` at time `T ≥ t` returns the
`queryList` at time `t`. -/
theorem take_length_queryList (M : OTM) (B : Set BitString) (x : BitString) {t T : ℕ} (h : t ≤ T) :
    (queryList M B x T).take (queryList M B x t).length = queryList M B x t :=
  (List.prefix_iff_eq_take.1 (queryList_prefix M B x h)).symm

/-- If at most `k` asks are made before `t ≤ T`, they are among the first `k` asks made
within `T` steps. -/
theorem queryList_subset_take (M : OTM) (B : Set BitString) (x : BitString) {t T k : ℕ} (ht : t ≤ T)
    (hk : (queryList M B x t).length ≤ k) {z : BitString} (hz : z ∈ queryList M B x t) :
    z ∈ (queryList M B x T).take k := by
  have e : queryList M B x t = ((queryList M B x T).take k).take (queryList M B x t).length := by
    rw [List.take_take, min_eq_left hk, take_length_queryList M B x ht]
  rw [e] at hz
  exact List.mem_of_mem_take hz

/-- A string asked at a time `t < T` after fewer than `k` earlier asks is among the first `k`
asks made within `T` steps. -/
theorem mem_take_of_askedAt (M : OTM) (B : Set BitString) (x : BitString) {t T k : ℕ}
    {z : BitString} (ht : t < T) (hk : (queryList M B x t).length < k)
    (hz : askedAt M (run M B x t) = some z) :
    z ∈ (queryList M B x T).take k :=
  queryList_subset_take M B x (Nat.succ_le_of_lt ht)
    ((length_queryList_succ_le M B x t).trans (Nat.succ_le_of_lt hk))
    ((mem_queryList M B x (t + 1) z).2 ⟨t, Nat.lt_succ_self t, hz⟩)

/-- After halting, no further asks. -/
theorem queryList_eq_of_halted (M : OTM) (B : Set BitString) (x : BitString) {t T : ℕ} (hle : t ≤ T)
    (h : Halted M (run M B x t)) : queryList M B x T = queryList M B x t := by
  induction T, hle using Nat.le_induction with
  | base => rfl
  | succ T hT ih =>
    rw [queryList_succ, ih, run_of_halted_le M B x hT h, askedAt_eq_none_of_halted M _ h]
    simp

/-- Runs asking the same strings at every time make the same asks. -/
theorem queryList_congr {M M' : OTM} {B B' : Set BitString} {x : BitString} {T : ℕ}
    (h : ∀ s < T, askedAt M (run M B x s) = askedAt M' (run M' B' x s)) :
    queryList M B x T = queryList M' B' x T := by
  induction T with
  | zero => rw [queryList_zero, queryList_zero]
  | succ T ih =>
    rw [queryList_succ, queryList_succ, ih fun s hs => h s (by omega), h T (by omega)]

/-- Runs with identical configurations up to time `T` make the same asks within `T` steps. -/
theorem queryList_eq_of_run_eq {M : OTM} {B B' : Set BitString} {x : BitString} {T : ℕ}
    (h : ∀ s < T, run M B x s = run M B' x s) : queryList M B x T = queryList M B' x T :=
  queryList_congr fun s hs => by rw [h s hs]

/-- The coded machine `M.code.toOTM` asks the same strings as `M` within any time bound. -/
theorem OTM.queryList_code (M : OTM) (B : Set BitString) (x : BitString) (T : ℕ) :
    queryList M.code.toOTM B x T = queryList M B x T :=
  queryList_congr fun s _ => by rw [OTM.run_code, OTM.askedAt_code]

/-! ### Answer histories (nodes of the reduction tree) -/

open Classical in
/-- The answers received by `M` with oracle `B` on input `x` to the asks made at the times
`s < t`, in order (one bit for every `ask` step).  An ask at time `t` is at the node
`answers M B x t` of the reduction tree. -/
noncomputable def answers (M : OTM) (B : Set BitString) (x : BitString) (t : ℕ) : List Bool :=
  (List.range t).flatMap fun s => ((askedAt M (run M B x s)).map fun z => decide (z ∈ B)).toList

/-- In zero steps, an empty history of answers is received. -/
theorem answers_zero (M : OTM) (B : Set BitString) (x : BitString) : answers M B x 0 = [] := by
  simp [answers]

open Classical in
/-- The answer history at time `t + 1` is the history at time `t` appended with the answer to the
string asked at time `t`, if any. -/
theorem answers_succ (M : OTM) (B : Set BitString) (x : BitString) (t : ℕ) :
    answers M B x (t + 1) =
      answers M B x t ++ ((askedAt M (run M B x t)).map fun z => decide (z ∈ B)).toList := by
  simp [answers, List.range_succ, List.flatMap_append]

/-- The answer history at time `t` is a prefix of the history at time `T ≥ t`. -/
theorem answers_prefix (M : OTM) (B : Set BitString) (x : BitString) {t T : ℕ} (h : t ≤ T) :
    answers M B x t <+: answers M B x T := by
  induction T, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ T _ ih =>
    rw [answers_succ]
    exact ih.trans (List.prefix_append _ _)

/-- Runs asking the same strings, with oracles giving the same answers to them, receive the same
answers. -/
theorem answers_congr {M M' : OTM} {B B' : Set BitString} {x : BitString} {T : ℕ}
    (h : ∀ s < T, askedAt M (run M B x s) = askedAt M' (run M' B' x s))
    (hB : ∀ s < T, ∀ z, askedAt M (run M B x s) = some z → (z ∈ B ↔ z ∈ B')) :
    answers M B x T = answers M' B' x T := by
  induction T with
  | zero => rw [answers_zero, answers_zero]
  | succ T ih =>
    rw [answers_succ, answers_succ, ih (fun s hs => h s (by omega)) (fun s hs => hB s (by omega)),
      ← h T (by omega)]
    rcases hz : askedAt M (run M B x T) with _ | z
    · rfl
    · simp only [Option.map_some, Option.toList_some, List.append_cancel_left_eq,
        List.cons.injEq, and_true]
      exact decide_eq_decide.2 (hB T (by omega) z hz)

/-- The coded machine `M.code.toOTM` receives the same answers as `M`. -/
theorem OTM.answers_code (M : OTM) (B : Set BitString) (x : BitString) (T : ℕ) :
    answers M.code.toOTM B x T = answers M B x T :=
  answers_congr (fun s _ => by rw [OTM.run_code, OTM.askedAt_code]) fun _ _ _ _ => Iff.rfl

/-- **Determinism.**  If the answers received before `t` with `B` and before `t'` with `B'` are
equal, the two runs coincide up to `min t t'` and receive the same answers there. -/
theorem run_eq_of_answers_eq_aux {M : OTM} {B B' : Set BitString} {x : BitString} {t t' : ℕ}
    (h : answers M B x t = answers M B' x t') :
    ∀ n, n ≤ t → n ≤ t' →
      (∀ s ≤ n, run M B x s = run M B' x s) ∧ answers M B x n = answers M B' x n := by
  intro n
  induction n with
  | zero =>
    intro _ _
    refine ⟨fun s hs => ?_, by rw [answers_zero, answers_zero]⟩
    rw [Nat.le_zero.1 hs]
    rfl
  | succ n ih =>
    intro hn hn'
    obtain ⟨hrun, hans⟩ := ih (by omega) (by omega)
    have hc := hrun n le_rfl
    have hlen : (answers M B x (n + 1)).length = (answers M B' x (n + 1)).length := by
      rw [answers_succ, answers_succ, List.length_append, List.length_append, hans, hc]
      cases askedAt M (run M B' x n) <;> rfl
    have hpre := answers_prefix M B x hn
    have hpre' := answers_prefix M B' x hn'
    rw [h] at hpre
    have hans1 : answers M B x (n + 1) = answers M B' x (n + 1) := by
      rw [List.prefix_iff_eq_take.1 hpre, List.prefix_iff_eq_take.1 hpre', hlen]
    have hagree : ∀ z, askedAt M (run M B x n) = some z → (z ∈ B ↔ z ∈ B') := by
      intro z hz
      rw [answers_succ, answers_succ, hans, ← hc, hz] at hans1
      simpa using hans1
    refine ⟨fun s hs => ?_, hans1⟩
    rcases Nat.lt_or_ge s (n + 1) with hs' | hs'
    · exact hrun s (by omega)
    · rw [show s = n + 1 by omega]
      change step M B (run M B x n) = step M B' (run M B' x n)
      rw [← hc]
      exact step_eq_of_agree M B B' _ hagree

/-- Under equal answer histories, an ask made at time `t ≤ t'` must be at time `t = t'` with equal
configurations. -/
theorem eq_of_answers_eq_of_le {M : OTM} {B B' : Set BitString} {x : BitString} {t t' : ℕ}
    {z : BitString} (hz : askedAt M (run M B x t) = some z)
    (h : answers M B x t = answers M B' x t')
    (hle : t ≤ t') : t = t' ∧ run M B x t = run M B' x t' := by
  obtain ⟨hrun, hans⟩ := run_eq_of_answers_eq_aux h t le_rfl hle
  have heq : t = t' := by
    by_contra hne
    have hl := (answers_prefix M B' x (show t + 1 ≤ t' by omega)).length_le
    have h1 : (answers M B' x (t + 1)).length = (answers M B' x t').length + 1 := by
      rw [answers_succ, List.length_append, ← hrun t le_rfl, hz, ← hans, h]
      simp
    omega
  subst heq
  exact ⟨rfl, hrun t le_rfl⟩

/-- **Equal histories give equal asks:** two asks (under oracles `B`, `B'` at times `t`, `t'`) after
the same answers are made at the same time and configuration. -/
theorem eq_of_answers_eq {M : OTM} {B B' : Set BitString} {x : BitString} {t t' : ℕ}
    {z z' : BitString} (hz : askedAt M (run M B x t) = some z)
    (hz' : askedAt M (run M B' x t') = some z')
    (h : answers M B x t = answers M B' x t') : t = t' ∧ run M B x t = run M B' x t' := by
  rcases le_total t t' with hle | hle
  · exact eq_of_answers_eq_of_le hz h hle
  · obtain ⟨e1, e2⟩ := eq_of_answers_eq_of_le hz' h.symm hle
    exact ⟨e1.symm, e2.symm⟩

/-- Two asks are at the same node of the reduction tree (equal answer histories) iff they are made
at the same time with oracles agreeing on the earlier queries. -/
theorem answers_eq_iff {M : OTM} {B B' : Set BitString} {x : BitString} {t t' : ℕ}
    {z z' : BitString} (hz : askedAt M (run M B x t) = some z)
    (hz' : askedAt M (run M B' x t') = some z') :
    answers M B x t = answers M B' x t' ↔ t = t' ∧ ∀ w ∈ queries M B x t, (w ∈ B ↔ w ∈ B') := by
  constructor
  · intro h
    obtain ⟨rfl, -⟩ := eq_of_answers_eq hz hz' h
    refine ⟨rfl, fun w hw => ?_⟩
    obtain ⟨s, hs, hws⟩ := (mem_queries M B x t w).1 hw
    obtain ⟨hrun, hans⟩ := run_eq_of_answers_eq_aux h (s + 1) (by omega) (by omega)
    obtain ⟨-, hans0⟩ := run_eq_of_answers_eq_aux h s (by omega) (by omega)
    rw [answers_succ, answers_succ, hans0, ← hrun s (by omega), hws] at hans
    simpa using hans
  · rintro ⟨rfl, hag⟩
    have hrun : ∀ s ≤ t, run M B x s = run M B' x s := fun s hs =>
      run_eq_of_agree M B B' x s fun w hw => hag w (queries_mono M B x hs hw)
    exact answers_congr (fun s hs => by rw [hrun s hs.le])
      fun s hs w hw => hag w ((mem_queries M B x t w).2 ⟨s, hs, hw⟩)

/-! ### Definitions -/

/-- `M` is *strictly sub-adaptive* on `x` within `T` steps (the paper's notion: all nodes of the
reduction tree carry distinct queries): two asks (under arbitrary oracles `B`, `B'`, at times
`t, t' < T`) at distinct nodes of the reduction tree, i.e. after distinct answer histories
(`answers`), carry distinct query strings.  In particular no string is asked twice on one run, and
distinct query configurations carry distinct strings (`StrictlySA.ne_of_run_ne`). -/
def StrictlySA (M : OTM) (x : BitString) (T : ℕ) : Prop :=
  ∀ (B B' : Set BitString) (t t' : ℕ) (z z' : BitString), t < T → t' < T →
    askedAt M (run M B x t) = some z → askedAt M (run M B' x t') = some z' →
    answers M B x t ≠ answers M B' x t' → z ≠ z'

/-- `M` is *sub-adaptive* on `x` within `T` steps (two-stage version, the stage boundary being
the `k`-th ask): for some `k`,
* (stage 1) the set of the first `k` strings asked within `T` steps is the same under every
  oracle `B` (as with the empty oracle);
* (stage 2) two asks (under arbitrary oracles `B`, `B'`, at times `t, t' < T`) made after at least
  `k` earlier asks, at distinct nodes of the reduction tree (after distinct answer histories),
  carry distinct query strings. -/
def SubAdaptive (M : OTM) (x : BitString) (T : ℕ) : Prop :=
  ∃ k : ℕ, (∀ B : Set BitString,
      ((queryList M B x T).take k).toFinset = ((queryList M ∅ x T).take k).toFinset) ∧
    ∀ (B B' : Set BitString) (t t' : ℕ) (z z' : BitString), t < T → t' < T →
      k ≤ (queryList M B x t).length → k ≤ (queryList M B' x t').length →
      askedAt M (run M B x t) = some z → askedAt M (run M B' x t') = some z' →
      answers M B x t ≠ answers M B' x t' → z ≠ z'

/-- The clocked coded machine `(c, e)` is strictly sub-adaptive on `x`. -/
def StrictlySubAdaptiveOn (c : OTMCode) (e : ℕ) (x : BitString) : Prop :=
  StrictlySA c.toOTM x (clock e x.length)

/-- The clocked coded machine `(c, e)` is sub-adaptive on `x` (two-stage version). -/
def SubAdaptiveOn (c : OTMCode) (e : ℕ) (x : BitString) : Prop :=
  SubAdaptive c.toOTM x (clock e x.length)

/-- `P^B_sa`: the sets decided with oracle `B` by a machine which, under *every* oracle, halts on
every input `x` within `p(|x|)` steps, and which is sub-adaptive (two-stage version) on every
input within `p(|x|)` steps. -/
def PolyTimeSA (B : Set BitString) : Set (Set BitString) :=
  {A | ∃ (M : OTM) (p : Polynomial ℕ),
    (∀ (B' : Set BitString) (x : BitString), ∃ t ≤ p.eval x.length, Halted M (run M B' x t)) ∧
    (∀ x : BitString, SubAdaptive M x (p.eval x.length)) ∧
    ∀ x : BitString, x ∈ A ↔ Accepts M B x}

/-- The strict version of `PolyTimeSA`. -/
def PolyTimeStrictSA (B : Set BitString) : Set (Set BitString) :=
  {A | ∃ (M : OTM) (p : Polynomial ℕ),
    (∀ (B' : Set BitString) (x : BitString), ∃ t ≤ p.eval x.length, Halted M (run M B' x t)) ∧
    (∀ x : BitString, StrictlySA M x (p.eval x.length)) ∧
    ∀ x : BitString, x ∈ A ↔ Accepts M B x}

/-! ### Simple facts -/

/-- A machine that asks nothing within `T` steps is strictly sub-adaptive. -/
theorem strictlySA_of_noAsk {M : OTM} {x : BitString} {T : ℕ}
    (h : ∀ (B : Set BitString) (t : ℕ), t < T → askedAt M (run M B x t) = none) :
    StrictlySA M x T := by
  intro B B' t t' z z' ht _ hz _ _
  rw [h B t ht] at hz
  exact absurd hz (by simp)

/-- A machine without `ask` transitions never asks. -/
theorem askedAt_eq_none_of_noAsk {M : OTM} (hM : ∀ q a q₁ q₂, M.δ q a ≠ .ask q₁ q₂)
    (c : Config M) : askedAt M c = none := by
  unfold askedAt
  by_cases hc : Halted M c
  · rw [ite_eq_left hc]
  · rw [ite_eq_right hc]
    cases hδ : M.δ c.q (c.tape c.head) with
    | step q' a mv => rfl
    | push q' b => rfl
    | ask q₁ q₂ => exact absurd hδ (hM _ _ _ _)

/-- A machine without `ask` transitions is strictly sub-adaptive. -/
theorem strictlySA_of_noAskδ {M : OTM} (hM : ∀ q a q₁ q₂, M.δ q a ≠ .ask q₁ q₂) (x : BitString)
    (T : ℕ) : StrictlySA M x T :=
  strictlySA_of_noAsk fun _ _ _ => askedAt_eq_none_of_noAsk hM _

/-- A clocked coded machine that asks nothing within the clock is strictly sub-adaptive. -/
theorem strictlySubAdaptiveOn_of_noAsk {c : OTMCode} {e : ℕ} {x : BitString}
    (h : ∀ (B : Set BitString) (t : ℕ), t < clock e x.length →
      askedAt c.toOTM (run c.toOTM B x t) = none) :
    StrictlySubAdaptiveOn c e x :=
  strictlySA_of_noAsk h

/-- A coded machine without `ask` transitions is strictly sub-adaptive. -/
theorem strictlySubAdaptiveOn_of_noAskδ {c : OTMCode} (hc : ∀ q a q₁ q₂, c.δ q a ≠ .ask q₁ q₂)
    (e : ℕ) (x : BitString) : StrictlySubAdaptiveOn c e x :=
  strictlySA_of_noAskδ (M := c.toOTM) hc x _

/-- No queries are made in `0` steps. -/
theorem queries_zero (M : OTM) (B : Set BitString) (x : BitString) : queries M B x 0 = ∅ := by
  simp [queries]

/-- The queries made within `s + 1` steps: those within `s` steps and the one asked at time `s`. -/
theorem queries_succ (M : OTM) (B : Set BitString) (x : BitString) (s : ℕ) :
    queries M B x (s + 1) = (askedAt M (run M B x s)).toFinset ∪ queries M B x s := by
  unfold queries
  rw [Finset.range_add_one, Finset.biUnion_insert]

/-- The stage boundary of a sub-adaptive machine can be taken `≤ T`: for `k ≥ T` the first `k`
asks are all the asks, and stage 2 is empty (fewer than `t` asks are made before `t`). -/
theorem subAdaptive_iff_exists_le {M : OTM} {x : BitString} {T : ℕ} :
    SubAdaptive M x T ↔ ∃ k ≤ T, (∀ B : Set BitString,
      ((queryList M B x T).take k).toFinset = ((queryList M ∅ x T).take k).toFinset) ∧
    ∀ (B B' : Set BitString) (t t' : ℕ) (z z' : BitString), t < T → t' < T →
      k ≤ (queryList M B x t).length → k ≤ (queryList M B' x t').length →
      askedAt M (run M B x t) = some z → askedAt M (run M B' x t') = some z' →
      answers M B x t ≠ answers M B' x t' → z ≠ z' := by
  constructor
  · rintro ⟨k, h1, h2⟩
    by_cases hk : k ≤ T
    · exact ⟨k, hk, h1, h2⟩
    · refine ⟨T, le_rfl, fun B => ?_, fun B B' t t' z z' ht _ hT _ _ _ _ =>
        absurd (hT.trans (length_queryList_le M B x t)) (Nat.not_le.2 ht)⟩
      have e : ∀ B' : Set BitString, (queryList M B' x T).take T = (queryList M B' x T).take k :=
        fun B' => by
          rw [List.take_of_length_le (length_queryList_le M B' x T),
            List.take_of_length_le ((length_queryList_le M B' x T).trans (by omega))]
      rw [e, e]
      exact h1 B
  · rintro ⟨k, -, h1, h2⟩
    exact ⟨k, h1, h2⟩

/-- Strict sub-adaptivity implies the two-stage version (with the boundary `k = 0`). -/
theorem StrictlySA.subAdaptive {M : OTM} {x : BitString} {T : ℕ} (h : StrictlySA M x T) :
    SubAdaptive M x T :=
  ⟨0, fun B => by simp, fun B B' t t' z z' ht ht' _ _ => h B B' t t' z z' ht ht'⟩

/-- The history version implies the configuration version: under `StrictlySA`, two distinct
configurations of the computation tree at which a query is asked carry distinct strings (equal
histories give equal configurations, `eq_of_answers_eq`). -/
theorem StrictlySA.ne_of_run_ne {M : OTM} {x : BitString} {T : ℕ} (h : StrictlySA M x T)
    {B B' : Set BitString} {t t' : ℕ} {z z' : BitString} (ht : t < T) (ht' : t' < T)
    (hne : run M B x t ≠ run M B' x t') (hz : askedAt M (run M B x t) = some z)
    (hz' : askedAt M (run M B' x t') = some z') : z ≠ z' :=
  h B B' t t' z z' ht ht' hz hz' fun he => hne (eq_of_answers_eq hz hz' he).2

/-- A strictly sub-adaptive machine asks any given string at most once across the entire reduction
tree: at a single time and after a single sequence of answers to all earlier queries. -/
theorem strictlySA_iff_tree {M : OTM} {x : BitString} {T : ℕ} :
    StrictlySA M x T ↔ ∀ (B B' : Set BitString) (t t' : ℕ) (z : BitString), t < T → t' < T →
      askedAt M (run M B x t) = some z → askedAt M (run M B' x t') = some z →
      t = t' ∧ ∀ w ∈ queries M B x t, (w ∈ B ↔ w ∈ B') := by
  constructor
  · intro h B B' t t' z ht ht' hz hz'
    refine (answers_eq_iff hz hz').1 ?_
    by_contra hne
    exact h B B' t t' z z ht ht' hz hz' hne rfl
  · intro h B B' t t' z z' ht ht' hz hz' hne hzz
    subst hzz
    exact hne ((answers_eq_iff hz hz').2 (h B B' t t' z ht ht' hz hz'))

/-- A strictly sub-adaptive machine on input `x` with clock `e` is sub-adaptive on `x`. -/
theorem StrictlySubAdaptiveOn.subAdaptiveOn {c : OTMCode} {e : ℕ} {x : BitString}
    (h : StrictlySubAdaptiveOn c e x) : SubAdaptiveOn c e x :=
  StrictlySA.subAdaptive h

/-- Every set decidable in polynomial time by a strictly sub-adaptive machine is decidable in
polynomial time by a sub-adaptive machine. -/
theorem polyTimeStrictSA_subset_polyTimeSA (B : Set BitString) :
    PolyTimeStrictSA B ⊆ PolyTimeSA B := by
  rintro A ⟨M, p, hh, hsa, hA⟩
  exact ⟨M, p, hh, fun x => (hsa x).subAdaptive, hA⟩

/-- A machine whose queries within `T` steps do not depend on the oracle (non-adaptive) is
sub-adaptive (two-stage version, with the boundary `k = T`: all asks are in stage 1, and stage 2
is empty since fewer than `t < T` asks are made before `t`). -/
theorem subAdaptive_of_nonAdaptive {M : OTM} {x : BitString} {T : ℕ}
    (h : ∀ B : Set BitString, queries M B x T = queries M ∅ x T) : SubAdaptive M x T := by
  refine ⟨T, fun B => ?_, fun B B' t t' z z' ht _ hT _ _ _ _ =>
    absurd (hT.trans (length_queryList_le M B x t)) (Nat.not_le.2 ht)⟩
  rw [List.take_of_length_le (length_queryList_le M B x T),
    List.take_of_length_le (length_queryList_le M ∅ x T), queryList_toFinset,
    queryList_toFinset, h B]

/-- A clocked coded machine whose queries within the clock do not depend on the oracle
is sub-adaptive. -/
theorem subAdaptiveOn_of_nonAdaptive {c : OTMCode} {e : ℕ} {x : BitString}
    (h : ∀ B : Set BitString, queries c.toOTM B x (clock e x.length) =
      queries c.toOTM ∅ x (clock e x.length)) : SubAdaptiveOn c e x :=
  subAdaptive_of_nonAdaptive h

/-- Polynomial-time machines (under every oracle) whose queries do not depend on the oracle
decide sets in `PolyTimeSA`. -/
theorem mem_polyTimeSA_of_nonAdaptive {B A : Set BitString} (M : OTM) (p : Polynomial ℕ)
    (hp : ∀ (B' : Set BitString) (x : BitString), ∃ t ≤ p.eval x.length, Halted M (run M B' x t))
    (hna : ∀ (B' : Set BitString) (x : BitString),
      queries M B' x (p.eval x.length) = queries M ∅ x (p.eval x.length))
    (hA : ∀ x : BitString, x ∈ A ↔ Accepts M B x) : A ∈ PolyTimeSA B :=
  ⟨M, p, hp, fun x => subAdaptive_of_nonAdaptive fun B' => hna B' x, hA⟩

/-! ### Stage 1

For a boundary `k` satisfying stage 1 of `SubAdaptive` (hypothesis `h1` below, in the form of the
definition), the stage-1 set `Q₁ = stage1Set M x T k` has at most `min k T` elements, the first
`k` asks of every run lie in `Q₁`, and up to the end of stage 1 the run depends only on the
oracle's restriction to `Q₁`: the boundary configuration (reached when the `k`-th ask has been
answered, or at time `T` if fewer than `k` asks are made) is determined by `B ∩ Q₁`. -/

/-- The stage-1 set for the boundary `k`: the set of the first `k` strings asked within `T` steps
with the empty oracle (by stage 1, with every oracle). -/
noncomputable def stage1Set (M : OTM) (x : BitString) (T k : ℕ) : Finset BitString :=
  ((queryList M ∅ x T).take k).toFinset

/-- The stage-1 set has at most `k` elements, and at most `T`. -/
theorem card_stage1Set_le (M : OTM) (x : BitString) (T k : ℕ) :
    (stage1Set M x T k).card ≤ min k T := by
  unfold stage1Set
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_take]
  exact min_le_min_left k (length_queryList_le M ∅ x T)

/-- Under stage 1, a string asked at a time `t < T` after fewer than `k` earlier asks lies in the
stage-1 set. -/
theorem mem_stage1Set_of_askedAt {M : OTM} {x : BitString} {T k : ℕ}
    (h1 : ∀ B : Set BitString, ((queryList M B x T).take k).toFinset = stage1Set M x T k)
    {B : Set BitString} {t : ℕ} {z : BitString} (ht : t < T) (hk : (queryList M B x t).length < k)
    (hz : askedAt M (run M B x t) = some z) : z ∈ stage1Set M x T k := by
  rw [← h1 B, List.mem_toFinset]
  exact mem_take_of_askedAt M B x ht hk hz

/-- **Stage 1 depends only on the stage-1 set** (the analogue of `run_eq_of_agree`): under stage
1, if the oracles `B` and `B'` agree on the stage-1 set, the runs coincide at every time `t ≤ T`
at which at most `k` asks have been made with `B`; in particular at all times up to and including
the end of stage 1 (`stage1End`). -/
theorem run_eq_of_agree_stage1 {M : OTM} {x : BitString} {T k : ℕ}
    (h1 : ∀ B : Set BitString, ((queryList M B x T).take k).toFinset = stage1Set M x T k)
    {B B' : Set BitString} (hBB' : ∀ z ∈ stage1Set M x T k, (z ∈ B ↔ z ∈ B')) {t : ℕ} (ht : t ≤ T)
    (hk : (queryList M B x t).length ≤ k) : run M B x t = run M B' x t := by
  refine run_eq_of_agree M B B' x t fun z hz => hBB' z ?_
  rw [← h1 B, List.mem_toFinset]
  rw [← queryList_toFinset, List.mem_toFinset] at hz
  exact queryList_subset_take M B x ht hk hz

/-- Under the hypotheses of `run_eq_of_agree_stage1`, the asks made before `t` with `B` and `B'`
are the same. -/
theorem queryList_eq_of_agree_stage1 {M : OTM} {x : BitString} {T k : ℕ}
    (h1 : ∀ B : Set BitString, ((queryList M B x T).take k).toFinset = stage1Set M x T k)
    {B B' : Set BitString} (hBB' : ∀ z ∈ stage1Set M x T k, (z ∈ B ↔ z ∈ B')) {t : ℕ} (ht : t ≤ T)
    (hk : (queryList M B x t).length ≤ k) : queryList M B x t = queryList M B' x t :=
  queryList_eq_of_run_eq fun _ hs => run_eq_of_agree_stage1 h1 hBB' (hs.le.trans ht)
    ((length_queryList_mono M B x hs.le).trans hk)

/-- The end of stage 1 with oracle `B`: the first time at which `k` asks have been made (so
`run M B x (stage1End M B x T k)` is the configuration reached when the `k`-th ask has been
answered), or `T` if fewer than `k` asks are made within `T` steps. -/
noncomputable def stage1End (M : OTM) (B : Set BitString) (x : BitString) (T k : ℕ) : ℕ :=
  Nat.find (⟨T, Or.inr le_rfl⟩ : ∃ t, k ≤ (queryList M B x t).length ∨ T ≤ t)

/-- The end of stage 1 is `t₀` if and only if `t₀` is the first time at which either `k` asks
have been made or time `T` has been reached. -/
theorem stage1End_eq_iff {M : OTM} {B : Set BitString} {x : BitString} {T k t₀ : ℕ} :
    stage1End M B x T k = t₀ ↔ (k ≤ (queryList M B x t₀).length ∨ T ≤ t₀) ∧
      ∀ t < t₀, (queryList M B x t).length < k ∧ t < T := by
  unfold stage1End
  rw [Nat.find_eq_iff]
  simp only [not_or, not_le]

/-- The end of stage 1 is at most `T`. -/
theorem stage1End_le (M : OTM) (B : Set BitString) (x : BitString) (T k : ℕ) :
    stage1End M B x T k ≤ T :=
  Nat.find_min' _ (Or.inr le_rfl)

/-- Before the end of stage 1, fewer than `k` asks have been made. -/
theorem length_queryList_lt_of_lt_stage1End {M : OTM} {B : Set BitString} {x : BitString}
    {T k t : ℕ} (ht : t < stage1End M B x T k) : (queryList M B x t).length < k :=
  ((stage1End_eq_iff.1 rfl).2 t ht).1

/-- At the end of stage 1, at most `k` asks have been made. -/
theorem length_queryList_stage1End_le (M : OTM) (B : Set BitString) (x : BitString) (T k : ℕ) :
    (queryList M B x (stage1End M B x T k)).length ≤ k := by
  rcases h : stage1End M B x T k with _ | s
  · rw [queryList_zero]
    exact Nat.zero_le _
  · have h1 := length_queryList_lt_of_lt_stage1End (M := M) (B := B) (x := x) (T := T) (k := k)
      (t := s) (by omega)
    have h2 := length_queryList_succ_le M B x s
    omega

/-- At the end of stage 1, exactly `k` asks have been made, unless it is the time `T`. -/
theorem stage1End_spec (M : OTM) (B : Set BitString) (x : BitString) (T k : ℕ) :
    (queryList M B x (stage1End M B x T k)).length = k ∨ stage1End M B x T k = T := by
  rcases (stage1End_eq_iff.1 rfl).1 with h | h
  · exact Or.inl (le_antisymm (length_queryList_stage1End_le M B x T k) h)
  · exact Or.inr (le_antisymm (stage1End_le M B x T k) h)

/-- Under stage 1, oracles agreeing on the stage-1 set have the same end of stage 1. -/
theorem stage1End_eq_of_agree_stage1 {M : OTM} {x : BitString} {T k : ℕ}
    (h1 : ∀ B : Set BitString, ((queryList M B x T).take k).toFinset = stage1Set M x T k)
    {B B' : Set BitString} (hBB' : ∀ z ∈ stage1Set M x T k, (z ∈ B ↔ z ∈ B')) :
    stage1End M B' x T k = stage1End M B x T k := by
  have hq : ∀ t ≤ stage1End M B x T k, queryList M B x t = queryList M B' x t := fun t ht =>
    queryList_eq_of_agree_stage1 h1 hBB' (ht.trans (stage1End_le M B x T k))
      ((length_queryList_mono M B x ht).trans (length_queryList_stage1End_le M B x T k))
  obtain ⟨hs, hmin⟩ := stage1End_eq_iff.1 (rfl : stage1End M B x T k = _)
  refine stage1End_eq_iff.2 ⟨by rwa [← hq _ le_rfl], fun t ht => ?_⟩
  rw [← hq t ht.le]
  exact hmin t ht

/-- **The boundary configuration depends only on the stage-1 set:** under stage 1, if the oracles
`B` and `B'` agree on the stage-1 set, the configurations at the end of stage 1 coincide. -/
theorem run_stage1End_eq_of_agree_stage1 {M : OTM} {x : BitString} {T k : ℕ}
    (h1 : ∀ B : Set BitString, ((queryList M B x T).take k).toFinset = stage1Set M x T k)
    {B B' : Set BitString} (hBB' : ∀ z ∈ stage1Set M x T k, (z ∈ B ↔ z ∈ B')) :
    run M B' x (stage1End M B' x T k) = run M B x (stage1End M B x T k) := by
  rw [stage1End_eq_of_agree_stage1 h1 hBB']
  exact (run_eq_of_agree_stage1 h1 hBB' (stage1End_le M B x T k)
    (length_queryList_stage1End_le M B x T k)).symm

/-- Under stage 1, the stage-1 set lies on every run: it is asked within `T` steps under
every oracle. -/
theorem stage1Set_subset_queries {M : OTM} {x : BitString} {T k : ℕ}
    (h1 : ∀ B : Set BitString, ((queryList M B x T).take k).toFinset = stage1Set M x T k)
    (B : Set BitString) : stage1Set M x T k ⊆ queries M B x T := by
  intro z hz
  rw [← h1 B, List.mem_toFinset] at hz
  rw [← queryList_toFinset, List.mem_toFinset]
  exact List.mem_of_mem_take hz

/-- For a sub-adaptive machine with boundary `k`, a string outside the stage-1 set is asked
(within `T` steps, under any oracles) at a single node of the reduction tree: after the same
answers, at the same time, in the same configuration. -/
theorem eq_of_not_mem_stage1Set {M : OTM} {x : BitString} {T k : ℕ}
    (h1 : ∀ B : Set BitString, ((queryList M B x T).take k).toFinset = stage1Set M x T k)
    (h2 : ∀ (B B' : Set BitString) (t t' : ℕ) (z z' : BitString), t < T → t' < T →
      k ≤ (queryList M B x t).length → k ≤ (queryList M B' x t').length →
      askedAt M (run M B x t) = some z → askedAt M (run M B' x t') = some z' →
      answers M B x t ≠ answers M B' x t' → z ≠ z')
    {B B' : Set BitString} {t t' : ℕ} {z : BitString} (ht : t < T) (ht' : t' < T)
    (hz : askedAt M (run M B x t) = some z) (hz' : askedAt M (run M B' x t') = some z)
    (hQ : z ∉ stage1Set M x T k) :
    answers M B x t = answers M B' x t' ∧ t = t' ∧ run M B x t = run M B' x t' := by
  have hk : k ≤ (queryList M B x t).length :=
    Nat.le_of_not_lt fun hlt => hQ (mem_stage1Set_of_askedAt h1 ht hlt hz)
  have hk' : k ≤ (queryList M B' x t').length :=
    Nat.le_of_not_lt fun hlt => hQ (mem_stage1Set_of_askedAt h1 ht' hlt hz')
  have he : answers M B x t = answers M B' x t' := by
    by_contra hne
    exact h2 B B' t t' z z ht ht' hk hk' hz hz' hne rfl
  exact ⟨he, eq_of_answers_eq hz hz' he⟩

/-- The data of a sub-adaptive machine: a boundary `k ≤ T` whose stage-1
set `Q₁` has at most `k` elements, lies on every run and contains every string asked with
fewer than `k` earlier asks; up to the end of stage 1 the runs depend only on the oracle's
restriction to `Q₁`; every string outside `Q₁` is asked at a single node of the reduction tree;
and asks after the `k`-th one at distinct nodes carry distinct strings. -/
theorem SubAdaptive.exists_boundary {M : OTM} {x : BitString} {T : ℕ} (h : SubAdaptive M x T) :
    ∃ k ≤ T, (stage1Set M x T k).card ≤ k ∧
      (∀ B : Set BitString, stage1Set M x T k ⊆ queries M B x T) ∧
      (∀ (B : Set BitString) (t : ℕ) (z : BitString), t < T → (queryList M B x t).length < k →
        askedAt M (run M B x t) = some z → z ∈ stage1Set M x T k) ∧
      (∀ B B' : Set BitString, (∀ z ∈ stage1Set M x T k, (z ∈ B ↔ z ∈ B')) →
        ∀ t ≤ T, (queryList M B x t).length ≤ k → run M B x t = run M B' x t) ∧
      (∀ (B B' : Set BitString) (t t' : ℕ) (z : BitString), t < T → t' < T →
        askedAt M (run M B x t) = some z → askedAt M (run M B' x t') = some z →
        z ∉ stage1Set M x T k →
        answers M B x t = answers M B' x t' ∧ t = t' ∧ run M B x t = run M B' x t') ∧
      ∀ (B B' : Set BitString) (t t' : ℕ) (z z' : BitString), t < T → t' < T →
        k ≤ (queryList M B x t).length → k ≤ (queryList M B' x t').length →
        askedAt M (run M B x t) = some z → askedAt M (run M B' x t') = some z' →
        answers M B x t ≠ answers M B' x t' → z ≠ z' := by
  obtain ⟨k, hk, h1, h2⟩ := subAdaptive_iff_exists_le.1 h
  exact ⟨k, hk, (card_stage1Set_le M x T k).trans (min_le_left _ _),
    stage1Set_subset_queries h1,
    fun B t z ht hlt hz => mem_stage1Set_of_askedAt h1 ht hlt hz,
    fun B B' hBB' t ht hle => run_eq_of_agree_stage1 h1 hBB' ht hle,
    fun B B' t t' z ht ht' hz hz' hQ => eq_of_not_mem_stage1Set h1 h2 ht ht' hz hz' hQ, h2⟩

/-! ### Longer time bounds and coded machines -/

/-- A machine halted at time `T` asks nothing at later times. -/
theorem lt_of_askedAt_of_halted {M : OTM} {B : Set BitString} {x : BitString} {T t : ℕ}
    {z : BitString} (hH : Halted M (run M B x T)) (hz : askedAt M (run M B x t) = some z) :
    t < T := by
  by_contra hge
  rw [run_of_halted_le M B x (Nat.le_of_not_lt hge) hH] at hz
  unfold askedAt at hz
  rw [ite_eq_left hH] at hz
  exact absurd hz (by simp)

/-- Strict sub-adaptivity extends to longer time bounds for machines halted at time `T` under
every oracle. -/
theorem StrictlySA.mono_of_halted {M : OTM} {x : BitString} {T T' : ℕ} (h : StrictlySA M x T)
    (hH : ∀ B : Set BitString, Halted M (run M B x T)) : StrictlySA M x T' :=
  fun B B' t t' z z' _ _ hz hz' hne => h B B' t t' z z' (lt_of_askedAt_of_halted (hH B) hz)
    (lt_of_askedAt_of_halted (hH B') hz') hz hz' hne

/-- Sub-adaptivity extends to longer time bounds for machines halted at time `T` under every
oracle (with the same boundary: no asks are made after time `T`). -/
theorem SubAdaptive.mono_of_halted {M : OTM} {x : BitString} {T T' : ℕ} (h : SubAdaptive M x T)
    (hTT : T ≤ T') (hH : ∀ B : Set BitString, Halted M (run M B x T)) : SubAdaptive M x T' := by
  obtain ⟨k, h1, h2⟩ := h
  have hq : ∀ B : Set BitString, queryList M B x T' = queryList M B x T :=
    fun B => queryList_eq_of_halted M B x hTT (hH B)
  refine ⟨k, fun B => by rw [hq, hq]; exact h1 B, ?_⟩
  intro B B' t t' z z' _ _ hk hk' hz hz' hne
  exact h2 B B' t t' z z' (lt_of_askedAt_of_halted (hH B) hz)
    (lt_of_askedAt_of_halted (hH B') hz') hk hk' hz hz' hne

/-- The encoding of an `OTM` configuration into a configuration of the coded machine is
injective. -/
theorem OTM.codeConfig_injective (M : OTM) : Function.Injective M.codeConfig := by
  intro c c' h
  have hq : Fintype.equivFin M.Q c.q = Fintype.equivFin M.Q c'.q := congrArg Config.q h
  have ht : c.tape = c'.tape := congrArg (Config.tape (M := M.code.toOTM)) h
  have hh : c.head = c'.head := congrArg (Config.head (M := M.code.toOTM)) h
  have hb : c.buf = c'.buf := congrArg (Config.buf (M := M.code.toOTM)) h
  have hq' : c.q = c'.q := (Fintype.equivFin M.Q).injective hq
  cases c
  cases c'
  simp only at hq' ht hh hb
  rw [hq', ht, hh, hb]

/-- An encoded configuration is in the accepting state of the coded machine if and only if the
original configuration is in the accepting state. -/
theorem OTM.code_accept_iff (M : OTM) (c : Config M) :
    (M.codeConfig c).q = M.code.toOTM.accept ↔ c.q = M.accept := by
  simp [OTM.codeConfig, OTM.code, OTMCode.toOTM]

/-- The coded machine `M.code.toOTM` asks the same set of queries as `M`. -/
theorem OTM.queries_code (M : OTM) (B : Set BitString) (x : BitString) (t : ℕ) :
    queries M.code.toOTM B x t = queries M B x t := by
  unfold queries
  simp only [OTM.run_code, OTM.askedAt_code]

/-- The coded machine `M.code.toOTM` is strictly sub-adaptive if `M` is. -/
theorem StrictlySA.code {M : OTM} {x : BitString} {T : ℕ} (h : StrictlySA M x T) :
    StrictlySA M.code.toOTM x T := by
  intro B B' t t' z z' ht ht' hz hz' hne
  simp only [OTM.run_code, OTM.askedAt_code] at hz hz'
  rw [OTM.answers_code, OTM.answers_code] at hne
  exact h B B' t t' z z' ht ht' hz hz' hne

/-- The coded machine `M.code.toOTM` is sub-adaptive if `M` is. -/
theorem SubAdaptive.code {M : OTM} {x : BitString} {T : ℕ} (h : SubAdaptive M x T) :
    SubAdaptive M.code.toOTM x T := by
  obtain ⟨k, h1, h2⟩ := h
  refine ⟨k, fun B => by rw [OTM.queryList_code, OTM.queryList_code]; exact h1 B, ?_⟩
  intro B B' t t' z z' ht ht' hk hk' hz hz' hne
  rw [OTM.queryList_code] at hk hk'
  simp only [OTM.run_code, OTM.askedAt_code] at hz hz'
  rw [OTM.answers_code, OTM.answers_code] at hne
  exact h2 B B' t t' z z' ht ht' hk hk' hz hz' hne

/-- A machine halting within `p(|x|)` steps under the oracle `B` decides its language as the
clocked code `(M.code, e)` for any clock `e` dominating `p`. -/
theorem clockedDecides_code (M : OTM) (p : Polynomial ℕ) (B A : Set BitString) (e : ℕ)
    (he : ∀ n, p.eval n ≤ clock e n)
    (hp : ∀ x : BitString, ∃ t ≤ p.eval x.length, Halted M (run M B x t))
    (hA : ∀ x : BitString, x ∈ A ↔ Accepts M B x) : ClockedDecides M.code e B A := by
  intro x
  rw [hA x]
  obtain ⟨t, ht, hh⟩ := hp x
  constructor
  · intro hacc
    have h1 := (accepts_iff_of_halted M B x t hh).1 hacc
    exact ⟨t, ht.trans (he _), by rw [OTM.run_code, OTM.code_accept_iff]; exact h1⟩
  · rintro ⟨s, -, h'⟩
    rw [OTM.run_code, OTM.code_accept_iff] at h'
    exact ⟨s, h'⟩

/-- A machine halting within a given time bound is halted at exactly that time bound. -/
theorem halted_at_bound {M : OTM} {p : Polynomial ℕ}
    (hp : ∀ (B' : Set BitString) (x : BitString), ∃ t ≤ p.eval x.length, Halted M (run M B' x t))
    (B' : Set BitString) (x : BitString) : Halted M (run M B' x (p.eval x.length)) := by
  obtain ⟨t, ht, hh⟩ := hp B' x
  rw [run_of_halted_le M B' x ht hh]
  exact hh

/-- Any set in `P^B_sa` is decided by a clocked coded machine with oracle `B` which is
sub-adaptive on every input. -/
theorem exists_clocked_sa (B A : Set BitString) (h : A ∈ PolyTimeSA B) :
    ∃ (c : OTMCode) (e : ℕ), (∀ x, SubAdaptiveOn c e x) ∧ ClockedDecides c e B A := by
  obtain ⟨M, p, hp, hsa, hA⟩ := h
  obtain ⟨e, he⟩ := exists_clock_ge p
  exact ⟨M.code, e, fun x => ((hsa x).mono_of_halted (he _)
    fun B' => halted_at_bound hp B' x).code,
    clockedDecides_code M p B A e he (hp B) hA⟩

/-- Any set in the strict class is decided by a clocked coded machine with oracle `B` which is
strictly sub-adaptive on every input. -/
theorem exists_clocked_strictSA (B A : Set BitString) (h : A ∈ PolyTimeStrictSA B) :
    ∃ (c : OTMCode) (e : ℕ), (∀ x, StrictlySubAdaptiveOn c e x) ∧ ClockedDecides c e B A := by
  obtain ⟨M, p, hp, hsa, hA⟩ := h
  obtain ⟨e, he⟩ := exists_clock_ge p
  exact ⟨M.code, e, fun x => ((hsa x).mono_of_halted fun B' => halted_at_bound hp B' x).code,
    clockedDecides_code M p B A e he (hp B) hA⟩

/-! ### Counting query configurations -/

/-- All strings of length at most `n`. -/
def strsUpTo : ℕ → Finset BitString
  | 0 => {[]}
  | n + 1 => insert [] ((strsUpTo n).image (List.cons false) ∪ (strsUpTo n).image (List.cons true))

/-- A string of length at most `n` belongs to the set of strings of length at most `n`. -/
theorem mem_strsUpTo {n : ℕ} {z : BitString} (hz : z.length ≤ n) : z ∈ strsUpTo n := by
  induction n generalizing z with
  | zero =>
    have : z = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hz)
    subst this
    simp [strsUpTo]
  | succ n ih =>
    rcases z with _ | ⟨b, z⟩
    · simp [strsUpTo]
    · have hz' : z ∈ strsUpTo n := ih (by simp only [List.length_cons] at hz; omega)
      cases b
      · simp [strsUpTo, hz']
      · simp [strsUpTo, hz']

/-- There are fewer than `2 ^ (n + 1)` strings of length at most `n`. -/
theorem card_strsUpTo_lt (n : ℕ) : (strsUpTo n).card < 2 ^ (n + 1) := by
  induction n with
  | zero => simp [strsUpTo]
  | succ n ih =>
    have h1 := Finset.card_insert_le ([] : BitString)
      ((strsUpTo n).image (List.cons false) ∪ (strsUpTo n).image (List.cons true))
    have h2 := Finset.card_union_le ((strsUpTo n).image (List.cons false))
      ((strsUpTo n).image (List.cons true))
    have h3 := Finset.card_image_le (s := strsUpTo n) (f := List.cons false)
    have h4 := Finset.card_image_le (s := strsUpTo n) (f := List.cons true)
    rw [strsUpTo, pow_succ]
    omega

/-- The possible queries within `T` steps are strings of length at most `T`. -/
theorem querySet_subset_strsUpTo (M : OTM) (x : BitString) (T : ℕ) :
    querySet M x T ⊆ strsUpTo T := by
  intro z hz
  rw [querySet, Set.Finite.mem_toFinset] at hz
  exact mem_strsUpTo (length_le_of_mem_queryAll M x T z hz)

/-- Every machine has fewer than `2 ^ (T + 1)` possible queries within `T` steps. -/
theorem card_querySet_lt (M : OTM) (x : BitString) (T : ℕ) : (querySet M x T).card < 2 ^ (T + 1) :=
  (Finset.card_le_card (querySet_subset_strsUpTo M x T)).trans_lt (card_strsUpTo_lt T)

/-- The query configurations of the computation tree of `M` on `x` within `T` steps: the
configurations reached at times `t < T` under some oracle at which a query is asked. -/
def queryConfigs (M : OTM) (x : BitString) (T : ℕ) : Set (Config M) :=
  {cfg | ∃ (B : Set BitString) (t : ℕ), t < T ∧ run M B x t = cfg ∧ (askedAt M cfg).isSome}

/-- The possible queries are the buffers of the query configurations. -/
theorem coe_querySet_eq_image (M : OTM) (x : BitString) (T : ℕ) :
    (querySet M x T : Set BitString) = Config.buf '' queryConfigs M x T := by
  ext z
  rw [querySet, Set.Finite.coe_toFinset]
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨t, ht, hz⟩ := (mem_queries M B x T z).1 hB
    exact ⟨run M B x t, ⟨B, t, ht, rfl, by rw [hz]; rfl⟩, (askedAt_eq_buf M _ z hz).symm⟩
  · rintro ⟨cfg, ⟨B, t, ht, rfl, hs⟩, rfl⟩
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨B, (mem_queries M B x T _).2 ⟨t, ht, ?_⟩⟩
    rw [hw, ← askedAt_eq_buf M _ w hw]

/-- The buffer of a query configuration within `T` steps has length at most `T`. -/
theorem buf_mem_strsUpTo {M : OTM} {x : BitString} {T : ℕ} (cfg : Config M)
    (hc : cfg ∈ queryConfigs M x T) : cfg.buf ∈ strsUpTo T := by
  obtain ⟨B, t, ht, rfl, -⟩ := hc
  exact mem_strsUpTo ((buf_length_le M B x t).trans ht.le)

/-- For a strictly sub-adaptive machine, a query configuration is determined by its query. -/
theorem StrictlySA.injOn_buf {M : OTM} {x : BitString} {T : ℕ} (h : StrictlySA M x T) :
    Set.InjOn Config.buf (queryConfigs M x T) := by
  rintro c ⟨B, t, ht, rfl, hs⟩ c' ⟨B', t', ht', rfl, hs'⟩ hbuf
  by_contra hne
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨z', hz'⟩ := Option.isSome_iff_exists.1 hs'
  exact h.ne_of_run_ne ht ht' hne hz hz'
    (by rw [askedAt_eq_buf M _ z hz, askedAt_eq_buf M _ z' hz']; exact hbuf)

/-- A strictly sub-adaptive machine has finitely many query configurations. -/
theorem StrictlySA.queryConfigs_finite {M : OTM} {x : BitString} {T : ℕ} (h : StrictlySA M x T) :
    (queryConfigs M x T).Finite :=
  Set.Finite.of_finite_image ((Finset.finite_toSet (strsUpTo T)).subset
    (by rintro _ ⟨cfg, hc, rfl⟩; exact buf_mem_strsUpTo cfg hc)) h.injOn_buf

/-- A strictly sub-adaptive machine has at most as many query configurations as there are
strings of length at most `T`, hence fewer than `2 ^ (T + 1)`. -/
theorem StrictlySA.ncard_queryConfigs_le {M : OTM} {x : BitString} {T : ℕ} (h : StrictlySA M x T) :
    (queryConfigs M x T).ncard ≤ (strsUpTo T).card := by
  have := Set.ncard_le_ncard_of_injOn Config.buf (t := (strsUpTo T : Set BitString))
    (fun cfg hc => buf_mem_strsUpTo cfg hc) h.injOn_buf (Finset.finite_toSet _)
  rwa [Set.ncard_coe_finset] at this

/-- A strictly sub-adaptive machine has fewer than `2 ^ (T + 1)` query configurations. -/
theorem StrictlySA.ncard_queryConfigs_lt {M : OTM} {x : BitString} {T : ℕ} (h : StrictlySA M x T) :
    (queryConfigs M x T).ncard < 2 ^ (T + 1) :=
  h.ncard_queryConfigs_le.trans_lt (card_strsUpTo_lt T)

/-- For a strictly sub-adaptive machine, the possible queries are in bijection with the query
configurations. -/
theorem StrictlySA.card_querySet_eq {M : OTM} {x : BitString} {T : ℕ} (h : StrictlySA M x T) :
    (querySet M x T).card = (queryConfigs M x T).ncard := by
  rw [← Set.ncard_coe_finset, coe_querySet_eq_image, h.injOn_buf.ncard_image]

/-- A strictly sub-adaptive coded machine has fewer than `2 ^ (T + 1)` query configurations
within the clock bound. -/
theorem StrictlySubAdaptiveOn.ncard_queryConfigs_lt {c : OTMCode} {e : ℕ} {x : BitString}
    (h : StrictlySubAdaptiveOn c e x) :
    (queryConfigs c.toOTM x (clock e x.length)).ncard < 2 ^ (clock e x.length + 1) :=
  StrictlySA.ncard_queryConfigs_lt h

/-- A strictly sub-adaptive coded machine makes fewer than `2 ^ (T + 1)` possible queries
within the clock bound. -/
theorem StrictlySubAdaptiveOn.card_querySet_lt {c : OTMCode} {e : ℕ} {x : BitString}
    (h : StrictlySubAdaptiveOn c e x) :
    (querySet c.toOTM x (clock e x.length)).card < 2 ^ (clock e x.length + 1) := by
  rw [StrictlySA.card_querySet_eq h]
  exact h.ncard_queryConfigs_lt

end Kolmogorov.RandomStrings
