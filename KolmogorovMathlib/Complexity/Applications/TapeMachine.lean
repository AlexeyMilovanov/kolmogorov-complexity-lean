/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# One-tape Turing machines and crossing sequences (SUV Section 8.2, pp. 233-235)

The book assumes the reader is familiar with Turing machines; this module fixes the model.

* A machine has a set of states `Q`, a tape alphabet `Γ` with a blank, and a transition function
  that in one step writes a symbol, moves the head by at most one cell and changes the state, or
  halts.
* The tape is infinite in both directions, indexed by `ℤ`.  A configuration is a state, the whole
  tape and the head position.  The tape is an arbitrary function, as the left zone `L` of
  Theorem 152 is arbitrary.
* After the machine has halted the configuration does not change, so "the configuration after `t`
  steps" is defined for all `t`, and `run` is the computation.
* The input `x` is written from cell `0`, with the head on cell `0`, and all other cells blank.

The border between the cells `p` and `p + 1` is *crossed from left to right* at step `s` when the
head goes from `p` to `p + 1`.  The crossing sequence is the list of states of the machine right
after these crossings, which is the only thing the right part of the tape learns from the left part:
this is `replayRight` and its statement `run_right_eq_replayRight`.

Everything in this module is Mathlib-only and states no complexity bound.  The complexity bounds are
in `Complexity/Applications/CrossingSequences.lean`.
-/

namespace Kolmogorov.Applications

/-- The moves of the head. -/
inductive TapeMove
  | left | stay | right
  deriving DecidableEq

/-- The displacement of a head move. -/
def TapeMove.delta : TapeMove → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- A one-tape deterministic Turing machine.  `step q a = none` means that the machine halts in
state `q` on symbol `a`. -/
structure TuringMachine (Q Γ : Type*) where
  /-- The blank symbol. -/
  blank : Γ
  /-- The transition function: new state, symbol to write, move of the head. -/
  step : Q → Γ → Option (Q × Γ × TapeMove)

/-- A configuration: the state, the content of the whole tape, the position of the head. -/
structure TapeConfig (Q Γ : Type*) where
  /-- The current state. -/
  state : Q
  /-- The content of the two-way infinite tape. -/
  tape : ℤ → Γ
  /-- The position of the head. -/
  head : ℤ

variable {Q Γ : Type*}

namespace TuringMachine

/-- `c` is a halting configuration of `M`. -/
def IsHalted (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) : Prop :=
  M.step c.state (c.tape c.head) = none

/-- One step of the computation; a halted configuration does not change. -/
def next (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) : TapeConfig Q Γ :=
  match M.step c.state (c.tape c.head) with
  | none => c
  | some (q, a, d) =>
    { state := q
      tape := Function.update c.tape c.head a
      head := c.head + d.delta }

/-- The configuration after `t` steps. -/
def run (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) (t : ℕ) : TapeConfig Q Γ := M.next^[t] c

/-- The computation from `c` halts at step `t` exactly. -/
def HaltsAt (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) (t : ℕ) : Prop :=
  M.IsHalted (M.run c t) ∧ ∀ s < t, ¬ M.IsHalted (M.run c s)

/-- The tape with the string `x` written from cell `0` through the input encoding `sym`, and blank
elsewhere. -/
def inputTape (M : TuringMachine Q Γ) (sym : Bool → Γ) (x : List Bool) : ℤ → Γ := fun i =>
  match i with
  | .ofNat n => (x[n]?.map sym).getD M.blank
  | .negSucc _ => M.blank

/-- The initial configuration on input `x`, with the head on the first cell. -/
def initial (M : TuringMachine Q Γ) (q₀ : Q) (sym : Bool → Γ) (x : List Bool) : TapeConfig Q Γ where
  state := q₀
  tape := M.inputTape sym x
  head := 0

/-- A proper input encoding: the two bits have different symbols, neither of them blank. -/
structure IsInputEncoding (M : TuringMachine Q Γ) (sym : Bool → Γ) : Prop where
  injective : Function.Injective sym
  ne_blank : ∀ b, sym b ≠ M.blank

/-- **SUV p. 235.**  `M` *duplicates its input*: on every binary string `x` it halts, with the tape
holding `x x` from cell `0`, followed by blanks.  Nothing is required of the cells to the left of
`0` or of the head position.  The origin and trailing blanks are an explicit output convention
for the book's informal "contains the string `x x`"; Theorem 153 below is restricted to machines
satisfying this convention. -/
def Duplicates (M : TuringMachine Q Γ) (q₀ : Q) (sym : Bool → Γ) : Prop :=
  ∀ x : List Bool, ∃ t, M.HaltsAt (M.initial q₀ sym x) t ∧
    ∀ i : ℕ, (M.run (M.initial q₀ sym x) t).tape i =
      (((x ++ x)[i]?).map sym).getD M.blank

open Classical in
/-- The number of cells after the cell `b` needed to contain all non-blank symbols on the right of
`b`, when these are finitely many, and `0` otherwise.  In Theorem 152 they are finitely many. -/
noncomputable def contentLength (M : TuringMachine Q Γ) (tape : ℤ → Γ) (b : ℤ) : ℕ :=
  if h : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → tape (b + 1 + k) = M.blank then Nat.find h else 0

/-- **SUV p. 234.**  The content `R` of the right part of the tape, the cells after `b`: the cells
up to the last non-blank one. -/
noncomputable def rightContents (M : TuringMachine Q Γ) (tape : ℤ → Γ) (b : ℤ) : List Γ :=
  (List.range (M.contentLength tape b)).map fun k => tape (b + 1 + k)

/-! ### Crossing sequences -/

/-- The head goes from cell `p` to cell `p + 1` at step `s`. -/
def CrossesAt (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) (p : ℤ) (s : ℕ) : Prop :=
  (M.run c s).head = p ∧ (M.run c (s + 1)).head = p + 1

open Classical in
/-- The steps before `t` at which the border between `p` and `p + 1` is crossed from left to
right. -/
noncomputable def crossingSteps (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) (p : ℤ) (t : ℕ) :
    Finset ℕ :=
  (Finset.range t).filter (M.CrossesAt c p)

open Classical in
/-- **SUV p. 234.**  The *crossing sequence* of the border between `p` and `p + 1` up to time `t`:
the states of the machine right after it crosses the border from left to right. -/
noncomputable def crossingSequence (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) (p : ℤ) (t : ℕ) :
    List Q :=
  ((List.range t).filter (M.CrossesAt c p)).map fun s => (M.run c (s + 1)).state

/-- At one step the head crosses at most one border. -/
lemma crossesAt_unique (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) {p p' : ℤ} {s : ℕ}
    (h : M.CrossesAt c p s) (h' : M.CrossesAt c p' s) : p = p' :=
  h.1.symm.trans h'.1

/-- **SUV p. 235.**  The crossing steps of `b + 1` consecutive borders are at most `t` in total: at
each step only one of the positions is crossed. -/
theorem sum_card_crossingSteps_le (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) (a : ℤ) (b t : ℕ) :
    ∑ k ∈ Finset.range (b + 1), (M.crossingSteps c (a + k) t).card ≤ t := by
  classical
  rw [← Finset.card_biUnion]
  · calc ((Finset.range (b + 1)).biUnion fun k => M.crossingSteps c (a + k) t).card
        ≤ (Finset.range t).card := by
          refine Finset.card_le_card fun s hs => ?_
          obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp hs
          exact (Finset.mem_filter.mp hk).1
      _ = t := Finset.card_range t
  · intro k _ l _ hkl
    refine Finset.disjoint_left.mpr fun s hs hs' => hkl ?_
    have h := M.crossesAt_unique c (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp hs').2
    exact_mod_cast add_left_cancel h

/-- **SUV p. 235.**  Among `b + 1` borders there is one whose crossing sequence up to time `t` has
at most `t / (b + 1)` elements: precisely, `(b + 1) · length ≤ t`. -/
theorem exists_crossingSteps_short (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) (a : ℤ) (b t : ℕ) :
    ∃ k ≤ b, (b + 1) * (M.crossingSteps c (a + k) t).card ≤ t := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ k ∈ Finset.range (b + 1), t < (b + 1) * (M.crossingSteps c (a + k) t).card :=
    fun k hk => hcon k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hsum := M.sum_card_crossingSteps_le c a b t
  have hmul : (b + 1) * t < (b + 1) * ∑ k ∈ Finset.range (b + 1),
      (M.crossingSteps c (a + k) t).card := by
    rw [Finset.mul_sum]
    calc (b + 1) * t = ∑ _k ∈ Finset.range (b + 1), t := by simp
      _ < ∑ k ∈ Finset.range (b + 1), (b + 1) * (M.crossingSteps c (a + k) t).card :=
        Finset.sum_lt_sum_of_nonempty (by simp) hlt
  exact absurd (Nat.mul_le_mul_left (b + 1) hsum) (not_le.mpr hmul)

/-! ### The computation on the right of a border -/

/-- The state of the replay of the part of the computation on the right of a border.  `inside` holds
the state and head position while the head is on the right; `pending` the crossing states not yet
used. -/
structure ReplayState (Q Γ : Type*) where
  /-- The right part of the tape. -/
  tape : ℤ → Γ
  /-- The state and head position when the head is on the right of the border. -/
  inside : Option (Q × ℤ)
  /-- The crossing states not yet used. -/
  pending : List Q

/-- One step of the replay on the right of the border between `p` and `p + 1`.  If the head is
outside, the next crossing state puts it on cell `p + 1`: this costs no time on the right.  If it is
inside, the machine makes a step, and if that takes it to the cell `p`, it is outside again.  If the
machine halts, or there is no crossing state left, the replay stops. -/
def replayStep (M : TuringMachine Q Γ) (p : ℤ) (r : ReplayState Q Γ) : ReplayState Q Γ :=
  match r.inside with
  | none =>
    match r.pending with
    | [] => r
    | q :: rest => { tape := r.tape, inside := some (q, p + 1), pending := rest }
  | some (q, h) =>
    match M.step q (r.tape h) with
    | none => r
    | some (q', a, d) =>
      { tape := Function.update r.tape h a
        inside := if h + d.delta ≤ p then none else some (q', h + d.delta)
        pending := r.pending }

/-- The replay on the right of a border, from the given right tape and crossing sequence. -/
def replayRight (M : TuringMachine Q Γ) (p : ℤ) (tape : ℤ → Γ) (S : List Q) (s : ℕ) :
    ReplayState Q Γ :=
  (M.replayStep p)^[s] { tape := tape, inside := none, pending := S }

open Classical in
/-- One more step of the computation adds its crossing to the crossing sequence, if there is one. -/
private lemma crossingSequence_succ (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) (p : ℤ) (t : ℕ) :
    M.crossingSequence c p (t + 1) = M.crossingSequence c p t ++
      (if M.CrossesAt c p t then [(M.run c (t + 1)).state] else []) := by
  unfold crossingSequence
  rw [List.range_succ, List.filter_append, List.map_append]
  congr 1
  by_cases h : M.CrossesAt c p t <;> simp [h]

/-- The invariant of the replay: after a suitable number of its steps, with the crossing states used
up to `rest`, the replay has the same right part of the tape as the computation after `t` steps, and
the same state and head position if the head is on the right. -/
private lemma replay_invariant (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) {p : ℤ}
    (hc : c.head ≤ p) {τ : ℤ → Γ} (hτ : ∀ i, p < i → τ i = c.tape i) (t : ℕ) :
    ∀ rest : List Q, ∃ s ≤ t + (M.crossingSequence c p t).length,
      (∀ i, p < i → ((M.replayStep p)^[s]
          { tape := τ, inside := none, pending := M.crossingSequence c p t ++ rest }).tape i =
        (M.run c t).tape i) ∧
      ((M.replayStep p)^[s]
          { tape := τ, inside := none, pending := M.crossingSequence c p t ++ rest }).pending =
        rest ∧
      ((M.replayStep p)^[s]
          { tape := τ, inside := none, pending := M.crossingSequence c p t ++ rest }).inside =
        if p < (M.run c t).head then some ((M.run c t).state, (M.run c t).head) else none := by
  classical
  induction t with
  | zero =>
    intro rest
    refine ⟨0, Nat.zero_le _, fun i hi => hτ i hi, ?_, ?_⟩
    · simp [crossingSequence]
    · have h : ¬ p < (M.run c 0).head := not_lt.mpr hc
      rw [ite_eq_right h]
      rfl
  | succ t ih =>
    intro rest
    set cfg := M.run c t with hcfg
    have hrun : M.run c (t + 1) = M.next cfg := Function.iterate_succ_apply' _ _ _
    rcases hstep : M.step cfg.state (cfg.tape cfg.head) with _ | ⟨q', a, d⟩
    · -- The machine has halted: nothing changes.
      have hnext : M.next cfg = cfg := by simp [next, hstep]
      have hnotcross : ¬ M.CrossesAt c p t := by
        rintro ⟨h1, h2⟩
        rw [hrun, hnext] at h2
        rw [← hcfg] at h1
        omega
      rw [crossingSequence_succ, ite_eq_right hnotcross, List.append_nil, hrun, hnext]
      obtain ⟨s, hs, h1, h2, h3⟩ := ih rest
      exact ⟨s, by omega, h1, h2, h3⟩
    · have hnext : M.next cfg =
          { state := q', tape := Function.update cfg.tape cfg.head a,
            head := cfg.head + d.delta } := by simp [next, hstep]
      have hδ : d.delta ≤ 1 := by cases d <;> simp [TapeMove.delta]
      by_cases hin : p < cfg.head
      · -- The head is on the right: one step of the replay.
        have hnotcross : ¬ M.CrossesAt c p t := by
          rintro ⟨h1, -⟩
          rw [← hcfg] at h1
          omega
        rw [crossingSequence_succ, ite_eq_right hnotcross, List.append_nil]
        obtain ⟨s, hs, h1, h2, h3⟩ := ih rest
        rw [ite_eq_left hin] at h3
        refine ⟨s + 1, by omega, ?_⟩
        rw [Function.iterate_succ_apply']
        have hread : ((M.replayStep p)^[s]
            { tape := τ, inside := none,
              pending := M.crossingSequence c p t ++ rest }).tape cfg.head =
            cfg.tape cfg.head := h1 _ hin
        simp only [replayStep, h3, hread, hstep, hrun, hnext]
        refine ⟨fun i hi => ?_, h2, ?_⟩
        · by_cases hih : i = cfg.head
          · simp [hih]
          · rw [Function.update_of_ne hih, Function.update_of_ne hih]
            exact h1 i hi
        · by_cases hle : cfg.head + d.delta ≤ p
          · simp [hle, not_lt.mpr hle]
          · simp [hle, not_le.mp hle]
      · -- The head is on the left.
        have hle : cfg.head ≤ p := not_lt.mp hin
        have hright : ∀ {r : ℤ → Γ}, (∀ i, p < i → r i = cfg.tape i) → ∀ i, p < i →
            r i = Function.update cfg.tape cfg.head a i := by
          intro r hr i hi
          rw [Function.update_of_ne (by omega)]
          exact hr i hi
        by_cases hcross : M.CrossesAt c p t
        · have hhead : cfg.head = p := hcross.1
          have hnew : cfg.head + d.delta = p + 1 := by
            have := hcross.2
            rwa [hrun, hnext] at this
          rw [crossingSequence_succ, ite_eq_left hcross, hrun, hnext]
          obtain ⟨s, hs, h1, h2, h3⟩ := ih (q' :: rest)
          rw [ite_eq_right hin] at h3
          refine ⟨s + 1, by simp; omega, ?_⟩
          rw [List.append_assoc, List.singleton_append, Function.iterate_succ_apply']
          have hnextr : ∀ r : ReplayState Q Γ, r.inside = none → r.pending = q' :: rest →
              M.replayStep p r =
                { tape := r.tape, inside := some (q', p + 1), pending := rest } := by
            intro r hr1 hr2
            simp only [replayStep, hr1, hr2]
          rw [hnextr _ h3 h2]
          refine ⟨fun i hi => hright (fun j hj => h1 j hj) i hi, rfl, ?_⟩
          simp [hnew]
        · have hnotin : ¬ p < cfg.head + d.delta := by
            intro hlt
            refine hcross ⟨by rw [← hcfg]; omega, ?_⟩
            rw [hrun, hnext]
            change cfg.head + d.delta = p + 1
            omega
          rw [crossingSequence_succ, ite_eq_right hcross, List.append_nil, hrun, hnext]
          obtain ⟨s, hs, h1, h2, h3⟩ := ih rest
          rw [ite_eq_right hin] at h3
          exact ⟨s, by omega, fun i hi => hright (fun j hj => h1 j hj) i hi, h2,
            by simpa [hnotin] using h3⟩

/-- **SUV p. 234, the main point of Theorem 152.**  Knowing the crossing sequence one can
reconstruct the behaviour of `M` on the right of the border without using the tape on the left: if
the head starts on the left of the border, and `τ` is any tape that agrees with the initial one on
the right of the border, at some stage of the replay the cells on the right of `p` are exactly those
of the real computation after `t` steps, and that stage is at most `t` plus the number of
crossings. -/
theorem run_right_eq_replayRight (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) {p : ℤ}
    (hc : c.head ≤ p) {τ : ℤ → Γ} (hτ : ∀ i, p < i → τ i = c.tape i) (t : ℕ) :
    ∃ s ≤ t + (M.crossingSequence c p t).length, ∀ i, p < i →
      (M.replayRight p τ (M.crossingSequence c p t) s).tape i = (M.run c t).tape i := by
  obtain ⟨s, hs, h1, -, -⟩ := M.replay_invariant c hc hτ t []
  rw [List.append_nil] at h1
  exact ⟨s, hs, h1⟩

end TuringMachine

end Kolmogorov.Applications
