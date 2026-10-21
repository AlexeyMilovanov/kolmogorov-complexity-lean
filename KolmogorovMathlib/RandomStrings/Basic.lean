/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib
import KolmogorovMathlib.Prefix.EntropyFunctions

/-!
# Decidable sets polynomial-time Turing-reducible to the a-priori-random strings lie in `EXPSPACE`

This file states a deterministic, a-priori-complexity consequence of Theorem 10 of
Allender, Friedman and Gasarch, *Limits on the Computational Power of Random Strings*
(ECCC TR10-139, rev. 1, 2011; Information and Computation 222 (2013)). It is not a verbatim
restatement of the published theorem:

  every decidable set `A` which, for *every* universal a priori complexity `H`, is decided by some
  polynomial-time oracle Turing machine with oracle `R_H = {x : H(x) ≥ |x|}`, belongs to `EXPSPACE`.

All notions are defined from scratch below, on binary strings `BitString = List Bool`:

* a priori complexity functions (`AprioriComplexity`), their universality, and the sets `RA H`;
* deterministic oracle Turing machines (`OTM`) with one two-way infinite work tape, on which the
  input is written, and a write-only query buffer; running a machine with an oracle `B`; the
  polynomial-time oracle class `PolyTimeOracle B` (`P^B`); and the class `EXPSPACE` of sets decided
  by such machines with no oracle (oracle `∅`) using exponentially many tape cells.
-/

namespace Kolmogorov.RandomStrings

/-! ## Strings, a priori complexity, random strings -/

/-- An *a priori complexity function*: a total `H : BitString → ℕ` such that `m(x) = 2 ^ (-H x)`
is a lower semicomputable discrete semimeasure, i.e. the Kraft sum `∑_x 2 ^ (-H x)` is at most `1`
(stated through its finite partial sums) and the overgraph `{(x, y) | H x ≤ y}` is computably
enumerable (Mathlib's `REPred`).  These are exactly the prefix-free entropy functions of
Muchnik–Positselsky and Allender–Friedman–Gasarch (`Kolmogorov.IsEntropyFun`). -/
structure AprioriComplexity where
  /-- The complexity function `H = -log m`. -/
  H : BitString → ℕ
  /-- Kraft: `∑_{x ∈ S} 2 ^ (-H x) ≤ 1` for every finite set `S` of strings. -/
  kraft : IsKraftFun H
  /-- The overgraph `{(x, y) | H x ≤ y}` is computably enumerable. -/
  re : HasREOvergraph H

/-- `H` is *universal* if it is additively optimal: for every a priori complexity function `F`
there is a constant `c` with `H x ≤ F x + c` for all `x`.  Equivalently, `2 ^ (-H)` is a maximal
lower semicomputable discrete semimeasure, a discrete a priori probability. -/
def AprioriComplexity.Universal (K : AprioriComplexity) : Prop :=
  ∀ F : AprioriComplexity, ∃ c : ℕ, ∀ x : BitString, K.H x ≤ F.H x + c

/-- `R_H = {x : H(x) ≥ |x|}`, the set of strings that are random for `H`. -/
def RA (K : AprioriComplexity) : Set BitString :=
  {x | x.length ≤ K.H x}

/-! ## Oracle Turing machines -/

/-- Tape symbols: a bit, or the blank `none`. -/
abbrev Sym : Type := Option Bool

/-- Head movements. -/
inductive Move where
  | left
  | stay
  | right

/-- The action taken by an oracle machine with state set `Q` in a non-halting state, as a
function of the current state and the scanned symbol. -/
inductive Act (Q : Type) where
  /-- Write the symbol `a` in the scanned cell, move the head by `m`, enter state `q'`. -/
  | step (q' : Q) (a : Sym) (m : Move)
  /-- Append the bit `b` to the query buffer, enter state `q'`. -/
  | push (q' : Q) (b : Bool)
  /-- Submit the query buffer to the oracle: enter `qyes` if the buffered string belongs to the
  oracle set and `qno` otherwise; the buffer is emptied. -/
  | ask (qyes qno : Q)

/-- A deterministic oracle Turing machine: a finite set of states with distinguished initial,
accepting and rejecting states, one two-way infinite tape over `Sym`, a write-only query
buffer, and a transition function. -/
structure OTM where
  /-- The states. -/
  Q : Type
  /-- There are finitely many states. -/
  [fin : Fintype Q]
  /-- The initial state. -/
  start : Q
  /-- The accepting (halting) state. -/
  accept : Q
  /-- The rejecting (halting) state. -/
  reject : Q
  /-- The transition function. -/
  δ : Q → Sym → Act Q

attribute [instance] OTM.fin

/-- A configuration of the machine `M`: the state, the tape, the head position, and the
contents of the query buffer. -/
structure Config (M : OTM) where
  /-- The current state. -/
  q : M.Q
  /-- The tape contents. -/
  tape : ℤ → Sym
  /-- The head position. -/
  head : ℤ
  /-- The query buffer. -/
  buf : BitString

/-- The initial configuration on input `x`: the input occupies the cells `0, …, |x| - 1`, all
other cells are blank, the head scans cell `0`, and the query buffer is empty. -/
def init (M : OTM) (x : BitString) : Config M :=
  ⟨M.start, fun i => if 0 ≤ i then x[i.toNat]? else none, 0, []⟩

/-- A configuration is halted when its state is the accepting or the rejecting state. -/
def Halted (M : OTM) (c : Config M) : Prop :=
  c.q = M.accept ∨ c.q = M.reject

/-- Moving the head. -/
def moveHead : Move → ℤ → ℤ
  | .left, i => i - 1
  | .stay, i => i
  | .right, i => i + 1

open Classical in
/-- One step of the machine `M` with oracle `B`.  Halted configurations are left unchanged. -/
noncomputable def step (M : OTM) (B : Set BitString) (c : Config M) : Config M :=
  if Halted M c then c
  else
    match M.δ c.q (c.tape c.head) with
    | .step q' a m => ⟨q', Function.update c.tape c.head a, moveHead m c.head, c.buf⟩
    | .push q' b => ⟨q', c.tape, c.head, c.buf ++ [b]⟩
    | .ask qyes qno => ⟨if c.buf ∈ B then qyes else qno, c.tape, c.head, []⟩

/-- The configuration of `M` with oracle `B` on input `x` after `t` steps. -/
noncomputable def run (M : OTM) (B : Set BitString) (x : BitString) : ℕ → Config M
  | 0 => init M x
  | t + 1 => step M B (run M B x t)

/-- `M` with oracle `B` accepts `x`: it reaches the accepting state. -/
def Accepts (M : OTM) (B : Set BitString) (x : BitString) : Prop :=
  ∃ t : ℕ, (run M B x t).q = M.accept

/-- The set of head positions of `M` (with oracle `B`, on input `x`) at times `0, …, t`. -/
noncomputable def visited (M : OTM) (B : Set BitString) (x : BitString) (t : ℕ) : Finset ℤ :=
  (Finset.range (t + 1)).image fun s => (run M B x s).head

/-! ## The classes `P^B` and `EXPSPACE` -/

/-- `P^B`: the sets decided by an oracle machine with oracle `B` which halts on every input `x`
within `p(|x|)` steps for a polynomial `p` (every step, including each `push` and each `ask`,
counts as one step). -/
def PolyTimeOracle (B : Set BitString) : Set (Set BitString) :=
  {A | ∃ (M : OTM) (p : Polynomial ℕ),
    (∀ x : BitString, ∃ t : ℕ, t ≤ p.eval x.length ∧ Halted M (run M B x t)) ∧
    ∀ x : BitString, x ∈ A ↔ Accepts M B x}

/-- `EXPSPACE`: the sets decided by a machine without oracle (oracle `∅`, so that every query is
answered negatively) which halts on every input `x` having scanned at most `2 ^ p(|x|)` tape
cells, for a polynomial `p`. -/
def EXPSPACE : Set (Set BitString) :=
  {A | ∃ (M : OTM) (p : Polynomial ℕ),
    (∀ x : BitString, ∃ t : ℕ, Halted M (run M ∅ x t) ∧
        (visited M ∅ x t).card ≤ 2 ^ p.eval x.length) ∧
    ∀ x : BitString, x ∈ A ↔ Accepts M ∅ x}

/-- `PSPACE`: the sets decided by a machine without oracle that visits at most `p(|x|)` cells. -/
def PSPACE : Set (Set BitString) :=
  {A | ∃ (M : OTM) (p : Polynomial ℕ),
    (∀ x : BitString, ∃ t : ℕ, Halted M (run M ∅ x t) ∧ (visited M ∅ x t).card ≤ p.eval x.length) ∧
    ∀ x : BitString, x ∈ A ↔ Accepts M ∅ x}

/-- `EXP`: the sets decided by a machine without oracle that halts within `2 ^ p(|x|)` steps. -/
def EXP : Set (Set BitString) :=
  {A | ∃ (M : OTM) (p : Polynomial ℕ),
    (∀ x : BitString, ∃ t : ℕ, t ≤ 2 ^ p.eval x.length ∧ Halted M (run M ∅ x t)) ∧
    ∀ x : BitString, x ∈ A ↔ Accepts M ∅ x}

/-! ## Basic facts about runs -/

/-- Halted configurations are fixed by `step`. -/
theorem step_of_halted (M : OTM) (B : Set BitString) (c : Config M) (h : Halted M c) :
    step M B c = c := by
  unfold step; rw [ite_eq_left h]

/-- Once halted, the run stays in the same configuration. -/
theorem run_of_halted_le (M : OTM) (B : Set BitString) (x : BitString) {t s : ℕ} (hle : t ≤ s)
    (h : Halted M (run M B x t)) : run M B x s = run M B x t := by
  induction s with
  | zero =>
    have : t = 0 := Nat.le_zero.mp hle
    subst this; rfl
  | succ s ih =>
    rcases Nat.lt_or_ge s t with hlt | hge
    · have : t = s + 1 := by omega
      subst this; rfl
    · rw [run, ih hge, step_of_halted _ _ _ h]

open Classical in
/-- The string submitted by an `ask` at configuration `c`, if the next action is an `ask`. -/
noncomputable def askedAt (M : OTM) (c : Config M) : Option BitString :=
  if Halted M c then none
  else match M.δ c.q (c.tape c.head) with
    | .ask _ _ => some c.buf
    | _ => none

/-- The queries made by `M` with oracle `B` on input `x` during the first `t` steps. -/
noncomputable def queries (M : OTM) (B : Set BitString) (x : BitString) (t : ℕ) :
    Finset BitString :=
  (Finset.range t).biUnion fun s => (askedAt M (run M B x s)).toFinset

/-- Membership in `queries`: `z` was asked at some step `s < t`. -/
theorem mem_queries (M : OTM) (B : Set BitString) (x : BitString) (t : ℕ) (z : BitString) :
    z ∈ queries M B x t ↔ ∃ s < t, askedAt M (run M B x s) = some z := by
  simp [queries]

/-- `queries` is monotone in the time bound. -/
theorem queries_mono (M : OTM) (B : Set BitString) (x : BitString) {t T : ℕ} (h : t ≤ T) :
    queries M B x t ⊆ queries M B x T := by
  intro z hz
  obtain ⟨s, hs, hz⟩ := (mem_queries M B x t z).1 hz
  exact (mem_queries M B x T z).2 ⟨s, by omega, hz⟩

/-- The string asked at a configuration is its query buffer. -/
theorem askedAt_eq_buf (M : OTM) (c : Config M) (z : BitString) (h : askedAt M c = some z) :
    z = c.buf := by
  unfold askedAt at h
  by_cases hc : Halted M c
  · rw [ite_eq_left hc] at h; simp at h
  · rw [ite_eq_right hc] at h
    cases hδ : M.δ c.q (c.tape c.head) with
    | step q' a m => rw [hδ] at h; simp at h
    | push q' b => rw [hδ] at h; simp at h
    | ask qyes qno => rw [hδ] at h; simp at h; exact h.symm

/-- The query buffer after `s` steps has length at most `s`: only a `push` lengthens it, by one
bit. -/
theorem buf_length_le (M : OTM) (B : Set BitString) (x : BitString) (s : ℕ) :
    (run M B x s).buf.length ≤ s := by
  induction s with
  | zero => simp [run, init]
  | succ s ih =>
    change (step M B (run M B x s)).buf.length ≤ s + 1
    unfold step
    by_cases h : Halted M (run M B x s)
    · rw [ite_eq_left h]; omega
    · rw [ite_eq_right h]
      split <;> (try simp) <;> omega

/-- The query made at step `s` has length at most `s` (each pushed bit costs a step). -/
theorem length_le_of_askedAt (M : OTM) (B : Set BitString) (x : BitString) (s : ℕ) (z : BitString)
    (hz : askedAt M (run M B x s) = some z) : z.length ≤ s := by
  rw [askedAt_eq_buf M _ z hz]
  exact buf_length_le M B x s

/-- One step does not depend on the oracle beyond the string asked (if any). -/
theorem step_eq_of_agree (M : OTM) (B B' : Set BitString) (c : Config M)
    (h : ∀ z, askedAt M c = some z → (z ∈ B ↔ z ∈ B')) : step M B c = step M B' c := by
  unfold step
  by_cases hc : Halted M c
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]
    cases hδ : M.δ c.q (c.tape c.head) with
    | step q' a m => rfl
    | push q' b => rfl
    | ask qyes qno =>
      have hiff : c.buf ∈ B ↔ c.buf ∈ B' := by
        apply h
        unfold askedAt
        rw [ite_eq_right hc, hδ]
      dsimp only
      rw [hiff]

/-- If two oracles agree on every query made with the first one during the first `t` steps,
the two runs coincide for `t` steps. -/
theorem run_eq_of_agree (M : OTM) (B B' : Set BitString) (x : BitString) (t : ℕ)
    (h : ∀ z ∈ queries M B x t, (z ∈ B ↔ z ∈ B')) : run M B x t = run M B' x t := by
  have key : ∀ s ≤ t, run M B x s = run M B' x s := by
    intro s hs
    induction s with
    | zero => rfl
    | succ s ih =>
      have e := ih (by omega)
      change step M B (run M B x s) = step M B' (run M B' x s)
      rw [← e]
      apply step_eq_of_agree
      intro z hz
      exact h z ((mem_queries M B x t z).2 ⟨s, by omega, hz⟩)
  exact key t le_rfl

/-- Once the run has halted at time `T`, acceptance is read off the configuration at `T`. -/
theorem accepts_iff_of_halted (M : OTM) (B : Set BitString) (x : BitString) (T : ℕ)
    (hT : Halted M (run M B x T)) : Accepts M B x ↔ (run M B x T).q = M.accept := by
  constructor
  · rintro ⟨t, ht⟩
    rcases le_total t T with hle | hle
    · rw [run_of_halted_le M B x hle (Or.inl ht)]; exact ht
    · rw [← run_of_halted_le M B x hle hT]; exact ht
  · intro h; exact ⟨T, h⟩

/-- `Accepts` is monotone under the identification of runs: with equal runs the verdicts agree. -/
theorem accepts_iff_of_agree (M : OTM) (B B' : Set BitString) (x : BitString) (T : ℕ)
    (hT : Halted M (run M B x T)) (h : ∀ z ∈ queries M B x T, (z ∈ B ↔ z ∈ B')) :
    (Accepts M B x ↔ Accepts M B' x) := by
  have e := run_eq_of_agree M B B' x T h
  have hT' : Halted M (run M B' x T) := e ▸ hT
  rw [accepts_iff_of_halted M B x T hT, accepts_iff_of_halted M B' x T hT', e]

/-- In `t` steps at most `t + 1` cells are scanned. -/
theorem visited_card_le (M : OTM) (B : Set BitString) (x : BitString) (t : ℕ) :
    (visited M B x t).card ≤ t + 1 := by
  unfold visited
  exact Finset.card_image_le.trans (by simp)

/-- `P^∅ ⊆ EXPSPACE`: a polynomially clocked machine scans at most `p(n) + 1 ≤ 2 ^ (p(n) + 1)`
cells. -/
theorem polyTimeOracle_empty_subset_EXPSPACE : PolyTimeOracle ∅ ⊆ EXPSPACE := by
  rintro A ⟨M, p, hp, hA⟩
  refine ⟨M, p, fun x => ?_, hA⟩
  obtain ⟨t, ht, hh⟩ := hp x
  refine ⟨t, hh, ?_⟩
  calc (visited M ∅ x t).card ≤ t + 1 := visited_card_le M ∅ x t
    _ ≤ 2 ^ t := Nat.lt_two_pow_self
    _ ≤ 2 ^ p.eval x.length := Nat.pow_le_pow_right (by norm_num) ht

end Kolmogorov.RandomStrings
