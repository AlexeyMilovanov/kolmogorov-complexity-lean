/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algorithm

The Moser–Tardos resampling algorithm for a CNF in which every clause has exactly `m` different
variables, as described in the proof of the constructive Lovász local lemma in the book by Shen,
Uspensky and Vereshchagin (Theorem 163, p. 252).

The algorithm reads random bits from a tape: the first `n` bits give the initial values of the
variables, and every call `Fix(d)` replaces the variables of a false clause `d` by `m` fresh bits,
then recursively fixes its false neighbours.  The recursion is realised by an explicit call stack.

## Main declarations

* `UniformCNF`, `UniformCNF.IsFalse`, `UniformCNF.Satisfies`, `UniformCNF.HasFewNeighbors`: the
  CNF, its false clauses, satisfying assignments and the hypothesis on the number of neighbours.
* `UniformCNF.State`, `UniformCNF.step`, `UniformCNF.run`: the state of the algorithm, one step of
  it, and the state after `t` steps.
* `UniformCNF.satisfies_of_isHalted`: when the algorithm halts, all clauses are true (p. 253).
* `UniformCNF.random_bits_determined`: the random bits used so far are determined by the current
  assignment and the log of the calls (p. 253).
-/

namespace Kolmogorov.Applications

/-- **SUV p. 252.**  A CNF with `n` variables and `N` clauses of `m` variables each.  `bad d` is the
combination of values of the variables of `d` for which the clause `d` is false. -/
structure UniformCNF (n N m : ℕ) where
  /-- The variables of each clause. -/
  vars : Fin N → Fin m → Fin n
  /-- A clause has `m` different variables. -/
  vars_injective : ∀ d, Function.Injective (vars d)
  /-- The values for which the clause is false. -/
  bad : Fin N → Fin m → Bool

namespace UniformCNF

variable {n N m : ℕ}

/-- The clause `d` is false under the assignment `a`. -/
def IsFalse (cnf : UniformCNF n N m) (a : Fin n → Bool) (d : Fin N) : Prop :=
  ∀ j, a (cnf.vars d j) = cnf.bad d j

instance (cnf : UniformCNF n N m) (a : Fin n → Bool) (d : Fin N) : Decidable (cnf.IsFalse a d) :=
  inferInstanceAs (Decidable (∀ j, a (cnf.vars d j) = cnf.bad d j))

/-- The assignment `a` satisfies the CNF. -/
def Satisfies (cnf : UniformCNF n N m) (a : Fin n → Bool) : Prop := ∀ d, ¬ cnf.IsFalse a d

/-- Two clauses are neighbours if they have a common variable. -/
def IsNeighbor (cnf : UniformCNF n N m) (d d' : Fin N) : Prop :=
  ∃ j j', cnf.vars d j = cnf.vars d' j'

instance (cnf : UniformCNF n N m) (d d' : Fin N) : Decidable (cnf.IsNeighbor d d') :=
  inferInstanceAs (Decidable (∃ j j', cnf.vars d j = cnf.vars d' j'))

/-- The neighbours of a clause, in the fixed order of the clauses. -/
def neighbors (cnf : UniformCNF n N m) (d : Fin N) : List (Fin N) :=
  (List.finRange N).filter (cnf.IsNeighbor d)

/-- **SUV Theorem 163, hypothesis.**  Each clause has at most `2^m / 8` neighbours. -/
def HasFewNeighbors (cnf : UniformCNF n N m) : Prop :=
  ∀ d, 8 * (cnf.neighbors d).length ≤ 2 ^ m

/-- The assignment `a` with the variables of `d` replaced by the random bits from position `pos`. -/
def resample (cnf : UniformCNF n N m) (r : ℕ → Bool) (pos : ℕ) (a : Fin n → Bool) (d : Fin N) :
    Fin n → Bool :=
  (List.finRange m).foldl (fun a j => Function.update a (cnf.vars d j) (r (pos + j))) a

/-- The state of the algorithm. -/
structure State (n N : ℕ) where
  /-- The current values of the variables. -/
  assign : Fin n → Bool
  /-- The call stack: the clause of each active call of `Fix`, and the index of its next
  neighbour. -/
  stack : List (Fin N × ℕ)
  /-- The next clause of the main loop. -/
  next : ℕ
  /-- The number of random bits used. -/
  pos : ℕ
  /-- The clauses for which `Fix` was called, last call first. -/
  log : List (Fin N)

/-- The call `Fix(d)` as a change of state: resample `d`, record it and use `m` more random bits.
The frames are given separately, since the caller's frame may also change. -/
def callFix (cnf : UniformCNF n N m) (r : ℕ → Bool) (s : State n N) (d : Fin N)
    (frames : List (Fin N × ℕ)) (nextClause : ℕ) : State n N where
  assign := cnf.resample r s.pos s.assign d
  stack := (d, 0) :: frames
  next := nextClause
  pos := s.pos + m
  log := d :: s.log

/-- One step of the algorithm, with an explicit stack.  With an empty stack, the main loop tests the
next clause, and stops after the last one.  With a frame `(d, j)` on top, `Fix(d)` tests its `j`-th
neighbour, and returns when there are no more neighbours. -/
def step (cnf : UniformCNF n N m) (r : ℕ → Bool) (s : State n N) : State n N :=
  match s.stack with
  | [] =>
    if h : s.next < N then
      if cnf.IsFalse s.assign ⟨s.next, h⟩ then
        cnf.callFix r s ⟨s.next, h⟩ [] (s.next + 1)
      else { s with next := s.next + 1 }
    else s
  | (d, j) :: rest =>
    match (cnf.neighbors d)[j]? with
    | none => { s with stack := rest }
    | some d' =>
      if cnf.IsFalse s.assign d' then
        cnf.callFix r s d' ((d, j + 1) :: rest) s.next
      else { s with stack := (d, j + 1) :: rest }

/-- The initial state: the first `n` random bits are the initial values of the variables. -/
def initial (r : ℕ → Bool) : State n N where
  assign := fun v => r v
  stack := []
  next := 0
  pos := n
  log := []

/-- The state after `t` steps. -/
def run (cnf : UniformCNF n N m) (r : ℕ → Bool) (t : ℕ) : State n N :=
  (cnf.step r)^[t] (initial r)

end UniformCNF

/-- The algorithm has finished: the call stack is empty and the main loop has passed all clauses. -/
def UniformCNF.State.IsHalted {n N : ℕ} (s : UniformCNF.State n N) : Prop :=
  s.stack = [] ∧ N ≤ s.next

/-- A finite tape of random bits, read as a function. -/
def tapeOf {L : ℕ} (ρ : Fin L → Bool) : ℕ → Bool := fun i => if h : i < L then ρ ⟨i, h⟩ else false

namespace UniformCNF

variable {n N m : ℕ}

/-- The invariant of the procedure: a false clause is still to be examined, by the main loop or by
an active call of `Fix`. -/
private def FixInvariant (cnf : UniformCNF n N m) (s : State n N) : Prop :=
  ∀ d, cnf.IsFalse s.assign d → s.next ≤ d.val ∨
    ∃ f ∈ s.stack, ∃ j', f.2 ≤ j' ∧ (cnf.neighbors f.1)[j']? = some d

/-- Resampling a clause does not change the variables outside it. -/
private lemma resample_apply (cnf : UniformCNF n N m) (r : ℕ → Bool) (pos : ℕ) (a : Fin n → Bool)
    (d : Fin N) (v : Fin n) (hv : ∀ j, cnf.vars d j ≠ v) : cnf.resample r pos a d v = a v := by
  have key : ∀ (l : List (Fin m)) (a : Fin n → Bool),
      (l.foldl (fun a j => Function.update a (cnf.vars d j) (r (pos + j))) a) v = a v := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons j l ih =>
      intro a
      rw [List.foldl_cons, ih, Function.update_of_ne (hv j).symm]
  exact key _ _

/-- A clause that is false after resampling a clause it does not meet was false before. -/
private lemma isFalse_of_not_neighbor (cnf : UniformCNF n N m) {d' d : Fin N}
    (hn : ¬ cnf.IsNeighbor d' d) {r : ℕ → Bool} {pos : ℕ} {a : Fin n → Bool}
    (h : cnf.IsFalse (cnf.resample r pos a d') d) : cnf.IsFalse a d := by
  intro j
  rw [← h j, cnf.resample_apply r pos a d' _ fun j' heq => hn ⟨j', j, heq⟩]

/-- A neighbour has an index in the list of neighbours. -/
private lemma exists_index_of_neighbor (cnf : UniformCNF n N m) {d' d : Fin N}
    (h : cnf.IsNeighbor d' d) : ∃ j' : ℕ, (cnf.neighbors d')[j']? = some d :=
  List.mem_iff_getElem?.mp (List.mem_filter.mpr ⟨List.mem_finRange d, decide_eq_true h⟩)

/-- The call `Fix(d₀)` keeps the invariant if the false clauses not meeting `d₀` are examined by
the rest of the program. -/
private lemma fixInvariant_callFix (cnf : UniformCNF n N m) (r : ℕ → Bool) (s : State n N)
    (d₀ : Fin N) (frames : List (Fin N × ℕ)) (nc : ℕ)
    (h : ∀ d, cnf.IsFalse s.assign d → ¬ cnf.IsNeighbor d₀ d →
      nc ≤ d.val ∨ ∃ f ∈ frames, ∃ j', f.2 ≤ j' ∧ (cnf.neighbors f.1)[j']? = some d) :
    cnf.FixInvariant (cnf.callFix r s d₀ frames nc) := by
  intro d hd
  by_cases hn : cnf.IsNeighbor d₀ d
  · obtain ⟨j', hj'⟩ := cnf.exists_index_of_neighbor hn
    exact Or.inr ⟨(d₀, 0), by simp [callFix], j', Nat.zero_le _, hj'⟩
  · rcases h d (cnf.isFalse_of_not_neighbor hn hd) hn with h1 | ⟨f, hf, hrest⟩
    · exact Or.inl h1
    · exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, hrest⟩

/-- Every step keeps the invariant. -/
private lemma fixInvariant_step (cnf : UniformCNF n N m) (hm : 0 < m) (r : ℕ → Bool) (s : State n N)
    (hs : cnf.FixInvariant s) : cnf.FixInvariant (cnf.step r s) := by
  have hself : ∀ d, cnf.IsNeighbor d d := fun d => ⟨⟨0, hm⟩, ⟨0, hm⟩, rfl⟩
  rcases hst : s.stack with _ | ⟨⟨e, j⟩, rest⟩
  · have hmain : ∀ d, cnf.IsFalse s.assign d → s.next ≤ d.val := by
      intro d hd
      rcases hs d hd with h | ⟨f, hf, -⟩
      · exact h
      · simp [hst] at hf
    simp only [step, hst]
    split_ifs with hlt hfalse
    · refine cnf.fixInvariant_callFix r s _ [] _ fun d hd hn => Or.inl ?_
      have hne : d.val ≠ s.next := fun heq => hn (by
        have hd0 : d = ⟨s.next, hlt⟩ := Fin.ext heq
        rw [← hd0]
        exact hself d)
      have := hmain d hd
      omega
    · intro d hd
      have hd' : cnf.IsFalse s.assign d := hd
      have hne : d.val ≠ s.next := fun heq => hfalse (by
        have hd0 : d = ⟨s.next, hlt⟩ := Fin.ext heq
        rw [← hd0]
        exact hd')
      have := hmain d hd'
      refine Or.inl ?_
      change s.next + 1 ≤ d.val
      omega
    · exact hs
  · have hfr : ∀ d, cnf.IsFalse s.assign d → s.next ≤ d.val ∨
        (∃ j', j ≤ j' ∧ (cnf.neighbors e)[j']? = some d) ∨
        ∃ f ∈ rest, ∃ j', f.2 ≤ j' ∧ (cnf.neighbors f.1)[j']? = some d := by
      intro d hd
      rcases hs d hd with h | ⟨f, hf, hj⟩
      · exact Or.inl h
      · rw [hst, List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact Or.inr (Or.inl hj)
        · exact Or.inr (Or.inr ⟨f, hf, hj⟩)
    -- An index past `j` is either `j` itself, the clause `d'`, or still ahead of the frame.
    have hnext : ∀ {d d' : Fin N}, (cnf.neighbors e)[j]? = some d' → d ≠ d' →
        (∃ j', j ≤ j' ∧ (cnf.neighbors e)[j']? = some d) →
        ∃ f ∈ (e, j + 1) :: rest, ∃ j', f.2 ≤ j' ∧ (cnf.neighbors f.1)[j']? = some d := by
      rintro d d' hd' hne ⟨j', hj', hget⟩
      rcases hj'.eq_or_lt with rfl | hlt
      · rw [hd'] at hget
        exact absurd (Option.some.inj hget).symm hne
      · exact ⟨(e, j + 1), by simp, j', hlt, hget⟩
    simp only [step, hst]
    rcases hn : (cnf.neighbors e)[j]? with _ | d'
    · intro d hd
      rcases hfr d hd with h | ⟨j', hj', hget⟩ | h
      · exact Or.inl h
      · have hlen := List.getElem?_eq_none_iff.mp hn
        rw [List.getElem?_eq_none (hlen.trans hj')] at hget
        exact absurd hget (by simp)
      · exact Or.inr h
    · simp only
      split_ifs with hfalse
      · refine cnf.fixInvariant_callFix r s d' _ _ fun d hd hnb => ?_
        have hne : d ≠ d' := fun heq => hnb (heq ▸ hself d)
        rcases hfr d hd with h | hj | ⟨f, hf, hj⟩
        · exact Or.inl h
        · exact Or.inr (hnext hn hne hj)
        · exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, hj⟩
      · intro d hd
        have hd' : cnf.IsFalse s.assign d := hd
        have hne : d ≠ d' := fun heq => hfalse (heq ▸ hd')
        rcases hfr d hd' with h | hj | ⟨f, hf, hj⟩
        · exact Or.inl h
        · exact Or.inr (hnext hn hne hj)
        · exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, hj⟩

/-- The invariant holds along the whole run. -/
private lemma fixInvariant_run (cnf : UniformCNF n N m) (hm : 0 < m) (r : ℕ → Bool) (t : ℕ) :
    cnf.FixInvariant (cnf.run r t) := by
  induction t with
  | zero => exact fun d _ => Or.inl (Nat.zero_le _)
  | succ t ih =>
    have hrun : cnf.run r (t + 1) = cnf.step r (cnf.run r t) := Function.iterate_succ_apply' _ _ _
    rw [hrun]
    exact cnf.fixInvariant_step hm r _ ih

/-- **SUV p. 253.**  The correctness of the procedure: when the algorithm has finished, all clauses
are true.  This holds for every tape.  The hypothesis `0 < m` makes each clause its own neighbour,
which the argument of the book uses; a clause with no variables is always false. -/
theorem satisfies_of_isHalted (cnf : UniformCNF n N m) (hm : 0 < m) (r : ℕ → Bool) {t : ℕ}
    (ht : (cnf.run r t).IsHalted) : cnf.Satisfies (cnf.run r t).assign := by
  intro d hd
  rcases cnf.fixInvariant_run hm r t d hd with h | ⟨f, hf, -⟩
  · have hlt := d.isLt
    have hN := ht.2
    omega
  · rw [ht.1] at hf
    simp at hf


/-- Step 1 of the proof of `random_bits_determined`: The position is determined by the
length of the log. -/
private lemma random_bits_determined_log_length {n N m : ℕ} (cnf : UniformCNF n N m) (r : ℕ →
    Bool) (t : ℕ) :
    (cnf.run r t).pos = n + m * (cnf.run r t).log.length := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih =>
    have hrun : cnf.run r (t + 1) = cnf.step r (cnf.run r t) := Function.iterate_succ_apply' _ _ _
    rw [hrun]
    generalize cnf.run r t = s at ih
    rcases hst : s.stack with _ | ⟨⟨e, j⟩, rest⟩
    · simp only [step, hst]
      split_ifs with hlt hfalse
      · simp only [callFix, List.length_cons, Nat.mul_succ]
        omega
      · exact ih
      · exact ih
    · simp only [step, hst]
      rcases hn : (cnf.neighbors e)[j]? with _ | d'
      · exact ih
      · simp only
        split_ifs with hfalse
        · simp only [callFix, List.length_cons, Nat.mul_succ]
          omega
        · exact ih

/-- Step 2of the proof of `random_bits_determined`: The positions match if the logs match.
-/
private lemma random_bits_determined_same_pos {n N m : ℕ} (cnf : UniformCNF n N m) (r r' : ℕ →
    Bool) {t t' : ℕ}
    (hlog : (cnf.run r t).log = (cnf.run r' t').log) :
    (cnf.run r t).pos = (cnf.run r' t').pos := by
  rw [random_bits_determined_log_length _ r t, random_bits_determined_log_length _ r'
      t', hlog]

private lemma random_bits_determined_zero_log_assign_aux {n N m : ℕ} (cnf : UniformCNF n N m)
    (r : ℕ → Bool)
    (s : UniformCNF.State n N) (h : (cnf.step r s).log = []) :
    s.log = [] ∧ (cnf.step r s).assign = s.assign := by
  rcases hst : s.stack with _ | ⟨⟨d, j⟩, rest⟩
  · simp only [UniformCNF.step, hst] at h ⊢
    split_ifs at h ⊢ <;> simp_all [UniformCNF.callFix]
  · simp only [UniformCNF.step, hst] at h ⊢
    rcases hnb : (cnf.neighbors d)[j]? with _ | d'
    · simp_all
    · simp only [hnb] at h ⊢
      split_ifs at h ⊢ <;> simp_all [UniformCNF.callFix]

/-- Step 3 of the proof of `random_bits_determined`: The assignments match the original
variables for empty log. -/
private lemma random_bits_determined_zero_log_assign {n N m : ℕ} (cnf : UniformCNF n N m) (r :
    ℕ → Bool) (t : ℕ) :
    (cnf.run r t).log = [] →
    ∀ v : Fin n, (cnf.run r t).assign v = r v := by
  induction t with
  | zero => intro _ v; rfl
  | succ t ih =>
    intro h v
    rw [UniformCNF.run, Function.iterate_succ_apply'] at h ⊢
    obtain ⟨h1, h2⟩ := random_bits_determined_zero_log_assign_aux cnf r _ h
    rw [h2]
    exact ih h1 v

/-- One step either leaves `assign` and `log` unchanged, or is a call `Fix(d)` of a false clause. -/
private lemma random_bits_determined_step_cases {n N m : ℕ} (cnf : UniformCNF n N m)
    (r : ℕ → Bool) (s : State n N) :
    ((cnf.step r s).assign = s.assign ∧ (cnf.step r s).log = s.log) ∨
    ∃ d, cnf.IsFalse s.assign d ∧ (cnf.step r s).assign = cnf.resample r s.pos s.assign d ∧
      (cnf.step r s).log = d :: s.log := by
  rcases hst : s.stack with _ | ⟨⟨e, j⟩, rest⟩
  · simp only [step, hst]
    split_ifs with hlt hfalse
    · exact Or.inr ⟨_, hfalse, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · simp only [step, hst]
    rcases hn : (cnf.neighbors e)[j]? with _ | d'
    · exact Or.inl ⟨rfl, rfl⟩
    · simp only
      split_ifs with hfalse
      · exact Or.inr ⟨d', hfalse, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩

/-- Step 4 of the proof of `random_bits_determined`: We can reverse execution to get
previous state. -/
private lemma random_bits_determined_prev_state {n N m : ℕ} (cnf : UniformCNF n N m) (r : ℕ →
    Bool) (t : ℕ)
    (d : Fin N) (l : List (Fin N)) :
    (cnf.run r t).log = d :: l →
    ∃ t' < t, (cnf.run r t').log = l ∧
      (cnf.run r t).assign = cnf.resample r (cnf.run r t').pos (cnf.run r t').assign d ∧
      cnf.IsFalse (cnf.run r t').assign d := by
  induction t generalizing d l with
  | zero => intro h; simp [run, initial] at h
  | succ t ih =>
    intro h
    have hrun : cnf.run r (t + 1) = cnf.step r (cnf.run r t) := Function.iterate_succ_apply' _ _ _
    rw [hrun] at h ⊢
    rcases random_bits_determined_step_cases cnf r (cnf.run r t) with ⟨ha, hl⟩ | ⟨d0, hf, ha,
        hl⟩
    · rw [hl] at h
      obtain ⟨t', ht', h1, h2, h3⟩ := ih d l h
      exact ⟨t', Nat.lt_succ_of_lt ht', h1, ha.trans h2, h3⟩
    · rw [hl] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact ⟨t, Nat.lt_succ_self t, rfl, ha, hf⟩

/-- Auxiliary: resampling writes the random bit `r (pos + j)` at the variable `vars d j`. -/
private lemma random_bits_determined_resample_inj_aux_vars (cnf : UniformCNF n N m)
    (r : ℕ → Bool) (pos : ℕ) (a : Fin n → Bool) (d : Fin N) (j : Fin m) :
    cnf.resample r pos a d (cnf.vars d j) = r (pos + j) := by
  have hnot : ∀ (l : List (Fin m)) (a : Fin n → Bool), j ∉ l →
      (l.foldl (fun a j => Function.update a (cnf.vars d j) (r (pos + j))) a) (cnf.vars d j)
        = a (cnf.vars d j) := by
    intro l
    induction l with
    | nil => intro a _; rfl
    | cons k l ih =>
      intro a hj
      rw [List.mem_cons, not_or] at hj
      rw [List.foldl_cons, ih _ hj.2,
        Function.update_of_ne (fun h => hj.1 (cnf.vars_injective d h))]
  have key : ∀ (l : List (Fin m)) (a : Fin n → Bool), l.Nodup → j ∈ l →
      (l.foldl (fun a j => Function.update a (cnf.vars d j) (r (pos + j))) a) (cnf.vars d j)
        = r (pos + j) := by
    intro l
    induction l with
    | nil => intro a _ h; simp at h
    | cons k l ih =>
      intro a hnd hj
      rw [List.nodup_cons] at hnd
      rw [List.foldl_cons]
      by_cases hk : j = k
      · subst hk
        rw [hnot l _ hnd.1, Function.update_self]
      · have hjl : j ∈ l := by
          rcases List.mem_cons.mp hj with h | h
          · exact absurd h hk
          · exact h
        exact ih _ hnd.2 hjl
  exact key _ _ (List.nodup_finRange m) (List.mem_finRange j)

/-- Step 5 of the proof of `random_bits_determined`: Resampling is injective. -/
private lemma random_bits_determined_resample_inj {n N m : ℕ} (cnf : UniformCNF n N m)
    (r r' : ℕ → Bool) (pos : ℕ) (a a' : Fin n → Bool) (d : Fin N) :
    cnf.resample r pos a d = cnf.resample r' pos a' d →
    cnf.IsFalse a d → cnf.IsFalse a' d →
    a = a' ∧ ∀ j < m, r (pos + j) = r' (pos + j) := by
  intro h hf hf'
  refine ⟨?_, ?_⟩
  · funext v
    by_cases hv : ∃ j, cnf.vars d j = v
    · obtain ⟨j, rfl⟩ := hv
      rw [hf j, hf' j]
    · push Not at hv
      rw [← cnf.resample_apply r pos a d v hv, h, cnf.resample_apply r' pos a' d v hv]
  · intro j hj
    have := congrFun h (cnf.vars d ⟨j, hj⟩)
    rwa [random_bits_determined_resample_inj_aux_vars,
      random_bits_determined_resample_inj_aux_vars] at this

/-- Step 6 of the proof of `random_bits_determined`: Full induction. -/
private lemma random_bits_determined_induction {n N m : ℕ} (cnf : UniformCNF n N m) (r r' : ℕ
    → Bool)
    (l : List (Fin N)) :
    ∀ t t', (cnf.run r t).log = l → (cnf.run r' t').log = l →
    (cnf.run r t).assign = (cnf.run r' t').assign →
    ∀ i < (cnf.run r t).pos, r i = r' i := by
  induction l with
  | nil =>
    intro t t' hlog hlog' hass i hi
    have hpos : (cnf.run r t).pos = n := by
      rw [random_bits_determined_log_length _ r t, hlog, List.length_nil, Nat.mul_zero,
          add_zero]
    have hr : ∀ v : Fin n, r v = (cnf.run r t).assign v := by
      intro v
      exact (random_bits_determined_zero_log_assign cnf r t hlog v).symm
    have hr' : ∀ v : Fin n, r' v = (cnf.run r' t').assign v := by
      intro v
      exact (random_bits_determined_zero_log_assign cnf r' t' hlog' v).symm
    rw [hpos] at hi
    have h1 := hr ⟨i, hi⟩
    have h2 := hr' ⟨i, hi⟩
    rw [hass] at h1
    exact h1.trans h2.symm
  | cons d l ih =>
    intro t t' hlog hlog' hass i hi
    obtain ⟨t1, -, hl1, hass1, hfalse1⟩ := random_bits_determined_prev_state cnf r t d l hlog
    obtain ⟨t1', -, hl1', hass1', hfalse1'⟩ := random_bits_determined_prev_state cnf r' t' d l
        hlog'
    have hpos1 : (cnf.run r t1).pos = (cnf.run r' t1').pos := by
      exact random_bits_determined_same_pos cnf r r' (hl1.trans hl1'.symm)
    have hass_eq : cnf.resample r (cnf.run r t1).pos (cnf.run r t1).assign d = 
                   cnf.resample r' (cnf.run r t1).pos (cnf.run r' t1').assign d := by
      rw [← hpos1] at hass1'
      rw [← hass1, ← hass1']
      exact hass
    have hres_inj := random_bits_determined_resample_inj cnf r r' (cnf.run r t1).pos
      (cnf.run r t1).assign (cnf.run r' t1').assign d hass_eq hfalse1 hfalse1'
    have hass1_eq := hres_inj.1
    have hrand_eq := hres_inj.2
    have ih_res := ih t1 t1' hl1 hl1' hass1_eq
    have hpos_t : (cnf.run r t).pos = (cnf.run r t1).pos + m := by
      rw [random_bits_determined_log_length _ r t, random_bits_determined_log_length _ r
          t1,
          hlog, hl1, List.length_cons, Nat.mul_succ]
      omega
    by_cases hlt : i < (cnf.run r t1).pos
    · exact ih_res i hlt
    · have h_range : ∃ j < m, i = (cnf.run r t1).pos + j := by
        use i - (cnf.run r t1).pos
        constructor
        · omega
        · omega
      obtain ⟨j, hj, rfl⟩ := h_range
      exact hrand_eq j hj

/-- **SUV p. 253, the crucial observation.**  The random bits used so far are determined by the
current values of the variables and the list of calls: unrolling the execution backwards, a call
`Fix(d)` happens only when `d` is false, which determines the values before the call. -/
theorem random_bits_determined (cnf : UniformCNF n N m) (r r' : ℕ → Bool) {t t' : ℕ}
    (hassign : (cnf.run r t).assign = (cnf.run r' t').assign)
    (hlog : (cnf.run r t).log = (cnf.run r' t').log) :
    ∀ i < (cnf.run r t).pos, r i = r' i := by
  exact random_bits_determined_induction cnf r r' (cnf.run r t).log t t' rfl hlog.symm hassign

end UniformCNF
end Kolmogorov.Applications
