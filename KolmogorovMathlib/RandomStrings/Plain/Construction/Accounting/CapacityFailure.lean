/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.EarlierTargets
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.AllocationLengths

/-!
# Counting allocations at a failed target

A failed fighter state contains a saturated input pool. Using disjoint target ranges
and the exact input lengths of successful allocations, this module turns that witness
into a lower bound on the number of directives at one level and target
(`exists_saturated_target_count_of_failed`).

It also defines the ledger invariant `PayoffLedger` (payoff directives are pairwise distinct as
pairs `(output, target)` and recorded in the `fulfilled` table) together with the lemmas that the
cancellation, abortion and allocation primitives of the fighter state preserve the permanent
graph `allocated` and the table `fulfilled`. These are used by the allocation-counting arguments
in `OutputSet`.
-/

namespace Kolmogorov.Milovanov

/-- At padding zero no allocation is ever made, so the inputs of a given length cannot all be
allocated. -/
private lemma not_all_inputs_allocated_of_padding_zero (P : FighterParams) (t r : ℕ)
    (hall : ∀ p ∈ fighterInputs 0 (r - 1),
      (fighterState P 0 t).allocated.any (fun a ↦ a.input == p) = true) :
    False := by
  have hempty : (fighterState P 0 t).allocated = [] := by
    cases t with
    | zero => rfl
    | succ t =>
      change (fighter_actions P 0 (t + 1) (fighterState P 0 t)).allocated = []
      simp [fighter_actions, initialFighterState]
  have hpool : ∀ n : ℕ, ∃ p : BitString, p ∈ fighterInputs 0 n := by
    intro n
    induction n with
    | zero => exact ⟨[], by simp [fighterInputs]⟩
    | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨false :: p, ?_⟩
      simp only [fighterInputs, List.mem_append, List.mem_map]
      exact Or.inl ⟨p, hp, rfl⟩
  obtain ⟨p, hp⟩ := hpool (r - 1)
  have h := hall p hp
  simp [hempty] at h

/-- Every allocation in a positive-padding state has its target length exactly one more than its
input length. -/
theorem fighterState_target_eq_input_length_add_one (P : FighterParams) (d t : ℕ) (hd : 1 ≤ d) :
    ∀ a ∈ (fighterState P d t).allocated, a.input.length + 1 = a.target := by
  induction t with
  | zero => simp [fighterState, initialFighterState]
  | succ t ih =>
    intro a ha
    rcases (fighter_actions_allocation_lengths
      P d (t + 1) (fighterState P d t) hd).2 a ha with hold | hlen
    · exact ih a hold
    · exact hlen

private lemma scale_add_le_of_fighterTargetRange {d l : ℕ} {kind : DirectiveKind} {r : ℕ}
    (hr : FighterTargetRange d l kind r) : levelScale l + d ≤ r := by
  have hscale := levelScale_lt_levelUpper l
  cases kind <;> simp only [FighterTargetRange] at hr <;> omega

private lemma levelUpper_lt_levelScale_of_lt {a b : ℕ} (hab : a < b) :
    levelUpper a < levelScale b := by
  change tower (2 * a + 1) < tower (2 * b)
  exact (tower_lt_tower_add_one (2 * a + 1)).trans_le (tower_le_tower (by omega))

/-- Target ranges are disjoint across all levels and kinds. -/
private lemma level_eq_and_kind_eq_of_fighterTargetRange (d l1 l2 r : ℕ) (k1 k2 : DirectiveKind)
    (h1 : FighterTargetRange d l1 k1 r) (h2 : FighterTargetRange d l2 k2 r) :
    l1 = l2 ∧ k1 = k2 := by
  rcases lt_trichotomy l1 l2 with hlt | heq | hgt
  · have hu1 := target_le_upper_add d l1 r k1 h1
    have hl2 := scale_add_le_of_fighterTargetRange h2
    have hgap := levelUpper_lt_levelScale_of_lt hlt
    omega
  · rcases heq with rfl
    refine ⟨rfl, ?_⟩
    have hscale := levelScale_lt_levelUpper l1
    have hrange := levelRangeBound_le_upper l1
    cases k1 <;> cases k2
    · rfl
    · simp only [FighterTargetRange] at h1 h2; omega
    · simp only [FighterTargetRange] at h1 h2; omega
    · simp only [FighterTargetRange] at h1 h2; omega
    · rfl
    · simp only [FighterTargetRange] at h1 h2; omega
    · simp only [FighterTargetRange] at h1 h2; omega
    · simp only [FighterTargetRange] at h1 h2; omega
    · rfl
  · have hu2 := target_le_upper_add d l2 r k2 h2
    have hl1 := scale_add_le_of_fighterTargetRange h1
    have hgap := levelUpper_lt_levelScale_of_lt hgt
    omega

/-- If every input string of length `r - 1` occurs among the allocated directives, and the
directives of that input length all have level `l`, kind `kind` and target `r`, then at least
`2 ^ (r - 1)` allocated directives have this level, kind and target. -/
private lemma pow_le_length_filter_of_all_inputs_allocated (r l : ℕ) (kind : DirectiveKind)
    (allocated : List AllocatedDirective) (d : ℕ)
    (h_prop : ∀ a ∈ allocated,
      a.input.length = r - 1 → a.level = l ∧ a.kind = kind ∧ a.target = r)
    (hall : ∀ p ∈ fighterInputs d (r - 1), allocated.any (fun a ↦ a.input == p) = true) :
    2 ^ (r - 1) ≤
      (allocated.filter (fun a ↦ decide (a.level = l ∧ a.kind = kind ∧ a.target = r))).length := by
  have heq : fighterInputs d (r - 1) = allStrings (r - 1) := by
    induction r - 1 with
    | zero => rfl
    | succ n ih => simp only [fighterInputs, allStrings, ih]
  have hlen : (fighterInputs d (r - 1)).length = 2 ^ (r - 1) := by
    rw [heq, length_allStrings]
  have hnodup : (fighterInputs d (r - 1)).Nodup := by
    rw [heq]
    exact allStrings_nodup (r - 1)
  let alloc_filtered :=
    allocated.filter (fun a ↦ decide (a.level = l ∧ a.kind = kind ∧ a.target = r))
  have hsubset : ∀ p ∈ fighterInputs d (r - 1), ∃ a ∈ alloc_filtered, a.input = p := by
    intro p hp
    obtain ⟨a, ha, ha_eq⟩ := List.any_eq_true.mp (hall p hp)
    have ha_eq := eq_of_beq ha_eq
    have hp_len : p.length = r - 1 := by
      rw [heq] at hp
      exact (mem_allStrings (r - 1) p).mp hp
    have ha_len : a.input.length = r - 1 := by rw [ha_eq, hp_len]
    exact ⟨a, List.mem_filter.mpr ⟨ha, decide_eq_true (h_prop a ha ha_len)⟩, ha_eq⟩
  have h_le := hnodup.length_le_of_subset
    (show fighterInputs d (r - 1) ⊆ alloc_filtered.map AllocatedDirective.input from
      fun p hp ↦ List.mem_map.mpr (hsubset p hp))
  simpa only [hlen, List.length_map] using h_le

/-- If all strings of length `r - 1` are allocated and `r` lies in the target range of level `l`
and kind `kind`, then the number of allocations with this level, kind and target `r` is at least
`2 ^ (r - 1)`: target ranges are disjoint, so every allocation of that input length falls
in this class. -/
private lemma pow_le_length_filter_allocated (P : FighterParams) (d t r l : ℕ)
    (kind : DirectiveKind) (hr : 0 < r) (hrange : FighterTargetRange d l kind r)
    (hall : ∀ p ∈ fighterInputs d (r - 1),
      (fighterState P d t).allocated.any (fun a ↦ a.input == p) = true) :
    2 ^ (r - 1) ≤ ((fighterState P d t).allocated.filter
      (fun a ↦ decide (a.level = l ∧ a.kind = kind ∧ a.target = r))).length := by
  by_cases hd : d = 0
  · subst hd
    exact (not_all_inputs_allocated_of_padding_zero P t r hall).elim
  · refine pow_le_length_filter_of_all_inputs_allocated r l kind
      (fighterState P d t).allocated d (fun a ha hal ↦ ?_) hall
    have htarget_eq : a.target = r := by
      have := fighterState_target_eq_input_length_add_one P d t (Nat.one_le_iff_ne_zero.mpr hd) a ha
      omega
    have hrange_a := (fighter_directive_target_ranges P d t a ha).2
    rw [htarget_eq] at hrange_a
    have hdisj := level_eq_and_kind_eq_of_fighterTargetRange d a.level l r a.kind kind
      hrange_a hrange
    exact ⟨hdisj.1, hdisj.2, htarget_eq⟩

/-- If some tick of the fighter run with padding `d` has a failed allocation, then at some tick
`tick` there are a level `l` activated and a kind `kind` whose target range contains a target `r`
for which the capacity `2 ^ (r - 1)` is exhausted: at least `2 ^ (r - 1)` allocated directives
have level `l`, kind `kind` and target `r`. -/
lemma exists_saturated_target_count_of_failed (P : FighterParams) (d : ℕ)
    (h : ∃ tick, (fighterState P d tick).failed = true) :
    ∃ tick r l kind,
      FighterActivated P d l tick ∧
      FighterTargetRange d l kind r ∧
      2 ^ (r - 1) ≤ ((fighterState P d tick).allocated.filter (fun a ↦ decide (a.level = l ∧
        a.kind = kind ∧ a.target = r))).length := by
  obtain ⟨t, r, l, kind, h_act, h_range, hr, h_all⟩ := saturated_target_of_failure P d h
  exact ⟨t, r, l, kind, h_act, h_range,
    pow_le_length_filter_allocated P d t r l kind hr h_range h_all⟩

/-- Cancellation keeps the permanent graph and the global fulfilled table. -/
lemma fighterCancel_allocated_fulfilled
    (d l : ℕ) (reason : PhaseEnd) (cause : ℕ) (state : FighterState) :
    (fighterCancel d l reason cause state).allocated = state.allocated ∧
      (fighterCancel d l reason cause state).fulfilled = state.fulfilled := by
  unfold fighterCancel
  split <;> exact ⟨rfl, rfl⟩

/-- Abortion of larger levels keeps the permanent graph and the global fulfilled table. -/
lemma fighterAbortAbove_allocated_fulfilled
    (d l : ℕ) (state : FighterState) :
    (fighterAbortAbove d l state).allocated = state.allocated ∧
      (fighterAbortAbove d l state).fulfilled = state.fulfilled := by
  unfold fighterAbortAbove
  suffices h : ∀ (ps : List FighterPhase) (s : FighterState),
      (ps.foldl (fun s phase ↦
          if l < phase.level then fighterCancel d phase.level .aborted l s else s) s).allocated =
          s.allocated ∧
        (ps.foldl (fun s phase ↦
          if l < phase.level then fighterCancel d phase.level .aborted l s else s) s).fulfilled =
          s.fulfilled from h _ _
  intro ps
  induction ps with
  | nil => intro s; exact ⟨rfl, rfl⟩
  | cons p ps ih =>
    intro s
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (if l < p.level then fighterCancel d p.level .aborted l s else s)
    rw [h1, h2]
    split_ifs
    · exact fighterCancel_allocated_fulfilled d p.level .aborted l s
    · exact ⟨rfl, rfl⟩

/-- An allocation keeps the fulfilled table; on failure it keeps the permanent graph, and on
success it appends exactly one entry of the requested kind, target, and output. -/
lemma fighterAllocate_fulfilled_allocated
    (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (output : BitString) (state : FighterState) :
    (fighterAllocate d l kind target output state).1.fulfilled = state.fulfilled ∧
      (((fighterAllocate d l kind target output state).2 = false ∧
          (fighterAllocate d l kind target output state).1.allocated = state.allocated) ∨
        ((fighterAllocate d l kind target output state).2 = true ∧
          ∃ entry : AllocatedDirective, entry.kind = kind ∧ entry.target = target ∧
            entry.output = output ∧
            (fighterAllocate d l kind target output state).1.allocated =
              state.allocated ++ [entry])) := by
  unfold fighterAllocate
  split
  · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rename_i phase _
    dsimp only
    split
    · obtain ⟨h1, h2⟩ := fighterCancel_allocated_fulfilled d l .saturated l
        { state with failed := true }
      exact ⟨h2, Or.inl ⟨rfl, h1⟩⟩
    · rename_i p _
      obtain ⟨h1, h2⟩ := fighterAbortAbove_allocated_fulfilled d l
        { state with allocated := state.allocated ++
          [AllocatedDirective.mk l phase.candidate state.tick kind target p output] }
      exact ⟨h2, Or.inr ⟨rfl, _, rfl, rfl, rfl, h1⟩⟩

/-- Payoff directives are pairwise distinct as pairs `(output, target)`, and each of them was
recorded in the global `fulfilled` table. -/
def PayoffLedger (state : FighterState) : Prop :=
  ((state.allocated.filter (fun a ↦ a.kind = .payoff)).map
      (fun a ↦ (a.output, a.target))).Nodup ∧
    ∀ a ∈ state.allocated, a.kind = .payoff → (a.output, a.target) ∈ state.fulfilled

/-- The ledger invariant holds in the initial state. -/
lemma payoffLedger_initialFighterState (d : ℕ) : PayoffLedger (initialFighterState d) := by
  unfold PayoffLedger initialFighterState
  exact ⟨List.nodup_nil, fun a ha ↦ absurd ha List.not_mem_nil⟩

/-- Allocation of a directive of a kind other than `payoff` preserves the ledger invariant. -/
lemma payoffLedger_fighterAllocate_of_ne_payoff
    (d l target : ℕ) (kind : DirectiveKind) (output : BitString) (state : FighterState)
    (h_kind : kind ≠ .payoff) (h_inv : PayoffLedger state) :
    PayoffLedger (fighterAllocate d l kind target output state).1 := by
  obtain ⟨hful, hcases⟩ := fighterAllocate_fulfilled_allocated d l kind target output state
  obtain ⟨h_nodup, h_ful⟩ := h_inv
  unfold PayoffLedger
  rcases hcases with ⟨-, ha⟩ | ⟨-, entry, hk, -, -, ha⟩
  · rw [ha, hful]
    exact ⟨h_nodup, h_ful⟩
  · rw [ha, hful, List.filter_append]
    have hentry : [entry].filter (fun a ↦ decide (a.kind = .payoff)) = [] := by
      simp [hk, h_kind]
    rw [hentry, List.append_nil]
    refine ⟨h_nodup, fun a ha' hpay ↦ ?_⟩
    rcases List.mem_append.mp ha' with ha' | ha'
    · exact h_ful a ha' hpay
    · rw [List.mem_singleton] at ha'
      subst ha'
      exact absurd (hk.symm.trans hpay) h_kind

end Kolmogorov.Milovanov
