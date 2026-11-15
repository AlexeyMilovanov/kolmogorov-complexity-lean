/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.MoserTardos.Algorithm

/-!
# Success Probability

The probability analysis of the Moser–Tardos algorithm for a uniform CNF in which every clause has
few neighbours.  The configurations reachable after `k` calls of `Fix` form a tree, and a
compression argument bounds the number of random tapes on which `Fix` is called many times.

Main declarations:

* `card_tapes_many_calls_le`: at most a `2^{-c}` fraction of the tapes lead to `N + c` calls of
  `Fix`.
* `isHalted_run_of_calls_le`: if `Fix` is called at most `N` times, the algorithm halts within
  `(N + 2)²` steps.
* `card_tapes_success`: at least half of the tapes yield a halted run whose assignment satisfies
  the CNF.
* `exists_satisfies`: such a CNF is satisfiable.

This formalizes the constructive proof of the Lovász local lemma in the book by Shen, Uspensky and
Vereshchagin ("Kolmogorov complexity and algorithmic randomness"), pp. 252–255.
-/

namespace Kolmogorov.Applications
namespace UniformCNF
variable {n N m : ℕ}

/-! ### The tree of calls: the possible configurations after `k` calls -/

/-- The part of a state that determines the tree of calls: the clauses of the frames of the stack
(top first), the pointer of the main loop, and the log. -/
private abbrev card_tapes_many_calls_le_Cfg (N : ℕ) : Type := List (Fin N) × ℕ × List (Fin N)

/-- The configuration of a state. -/
private def card_tapes_many_calls_le_cfgOf {n N : ℕ} (s : State n N) :
    card_tapes_many_calls_le_Cfg N :=
  (s.stack.map Prod.fst, s.next, s.log)

/-- The configurations after a call `Fix(d')` made from the frame at some position of the stack `st`
(the frames above it are popped), for a neighbour `d'` of the clause of that frame. -/
private def card_tapes_many_calls_le_callCfgs {n N m : ℕ} (cnf : UniformCNF n N m) (nx : ℕ)
    (lg : List (Fin N)) : List (Fin N) → List (card_tapes_many_calls_le_Cfg N)
  | [] => []
  | d :: rest => (cnf.neighbors d).map (fun d' => (d' :: d :: rest, nx, d' :: lg)) ++
      card_tapes_many_calls_le_callCfgs cnf nx lg rest

/-- The configurations after a call from the main loop, for a clause of position `≥ nx`
(`f` is the fuel; `f ≥ N - nx` suffices). -/
private def card_tapes_many_calls_le_mainCfgs {N : ℕ} (lg : List (Fin N)) :
    ℕ → ℕ → List (card_tapes_many_calls_le_Cfg N)
  | _, 0 => []
  | nx, f + 1 => (if h : nx < N then [([⟨nx, h⟩], nx + 1, ⟨nx, h⟩ :: lg)] else []) ++
      card_tapes_many_calls_le_mainCfgs lg (nx + 1) f

/-- All the configurations that may follow a configuration by the next call. -/
private def card_tapes_many_calls_le_succs {n N m : ℕ} (cnf : UniformCNF n N m)
    (c : card_tapes_many_calls_le_Cfg N) : List (card_tapes_many_calls_le_Cfg N) :=
  card_tapes_many_calls_le_callCfgs cnf c.2.1 c.2.2 c.1 ++
    card_tapes_many_calls_le_mainCfgs c.2.2 c.2.1 N

/-- The configurations that are possible right after the `k`-th call (a list with repetitions). -/
private def card_tapes_many_calls_le_paths {n N m : ℕ} (cnf : UniformCNF n N m) :
    ℕ → List (card_tapes_many_calls_le_Cfg N)
  | 0 => [([], 0, [])]
  | k + 1 => (card_tapes_many_calls_le_paths cnf k).flatMap (card_tapes_many_calls_le_succs cnf)

/-- The weight of a configuration: `2 ^ (height of the stack) * 2 ^ (number of clauses not yet
passed by the main loop)`. -/
private def card_tapes_many_calls_le_weight {N : ℕ} (c : card_tapes_many_calls_le_Cfg N) : ℕ :=
  2 ^ c.1.length * 2 ^ (N - c.2.1)

/-- The sum of a constant over a list is its length times the constant. -/
private lemma card_tapes_many_calls_le_sum_map_const {α : Type*} (l : List α) (a : ℕ) :
    (l.map (fun _ => a)).sum = l.length * a := by
  rw [List.map_const', List.sum_const_nat]

/-- Weights of the configurations after a call from a frame of `st`: the sum over the frames, plus
`4 t 2 ^ (N - nx)`, is at most `t 2 ^ (|st| + 2) 2 ^ (N - nx)`. -/
private lemma card_tapes_many_calls_le_weight_callCfgs {n N m : ℕ} (cnf : UniformCNF n N m)
    (t : ℕ) (ht : ∀ d, (cnf.neighbors d).length ≤ t) (nx : ℕ) (lg : List (Fin N))
    (st : List (Fin N)) :
    ((card_tapes_many_calls_le_callCfgs cnf nx lg st).map card_tapes_many_calls_le_weight).sum +
        4 * t * 2 ^ (N - nx) ≤ t * 2 ^ (st.length + 2) * 2 ^ (N - nx) := by
  induction st with
  | nil =>
    simp only [card_tapes_many_calls_le_callCfgs, List.map_nil, List.sum_nil, List.length_nil,
      zero_add]
    nlinarith
  | cons d rest ih =>
    have hhead : (((cnf.neighbors d).map
        (fun d' => (d' :: d :: rest, nx, d' :: lg))).map
          card_tapes_many_calls_le_weight).sum ≤
        t * 2 ^ (rest.length + 2) * 2 ^ (N - nx) := by
      rw [List.map_map]
      have hfun : (card_tapes_many_calls_le_weight ∘
          (fun d' : Fin N => ((d' :: d :: rest, nx, d' :: lg) :
            card_tapes_many_calls_le_Cfg N))) =
          fun _ => 2 ^ (rest.length + 2) * 2 ^ (N - nx) := by
        funext d'
        simp [card_tapes_many_calls_le_weight, Function.comp]
      rw [hfun, card_tapes_many_calls_le_sum_map_const, mul_assoc t]
      exact Nat.mul_le_mul_right _ (ht d)
    simp only [card_tapes_many_calls_le_callCfgs, List.map_append, List.sum_append,
      List.length_cons]
    have hpow : 2 ^ (rest.length + 1 + 2) = 2 * 2 ^ (rest.length + 2) := by
      rw [show rest.length + 1 + 2 = (rest.length + 2) + 1 by omega, pow_succ, Nat.mul_comm]
    rw [hpow]
    nlinarith

/-- Weights of the configurations after a call from the main loop: the sum, plus `2`, is at most
`2 * 2 ^ (N - nx)`. -/
private lemma card_tapes_many_calls_le_weight_mainCfgs {N : ℕ} (lg : List (Fin N)) (nx f : ℕ)
    (hf : N - nx ≤ f) :
    ((card_tapes_many_calls_le_mainCfgs lg nx f).map card_tapes_many_calls_le_weight).sum + 2 ≤
      2 * 2 ^ (N - nx) := by
  induction f generalizing nx with
  | zero =>
    simp only [card_tapes_many_calls_le_mainCfgs, List.map_nil, List.sum_nil, zero_add]
    have h1 : 1 ≤ 2 ^ (N - nx) := Nat.one_le_two_pow
    omega
  | succ f ih =>
    have ih' := ih (nx + 1) (by omega)
    by_cases h : nx < N
    · simp only [card_tapes_many_calls_le_mainCfgs, h, ↓reduceDIte, List.map_append,
        List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        card_tapes_many_calls_le_weight, List.length_cons, List.length_nil]
      have hpow : 2 ^ (N - nx) = 2 * 2 ^ (N - (nx + 1)) := by
        rw [show N - nx = (N - (nx + 1)) + 1 by omega, pow_succ, Nat.mul_comm]
      rw [hpow]
      have h2 : 2 ^ (0 + 1) * 2 ^ (N - (nx + 1)) = 2 * 2 ^ (N - (nx + 1)) := by
        rw [zero_add, pow_one]
      omega
    · have e1 : N - nx = 0 := by omega
      have e2 : N - (nx + 1) = 0 := by omega
      simp only [card_tapes_many_calls_le_mainCfgs, h, ↓reduceDIte, List.nil_append]
      rw [e1]
      rw [e2] at ih'
      exact ih'

/-- The weights of the possible next configurations are at most `4 t` times the weight of a
configuration (`t ≥ 1` bounds the number of neighbours of a clause). -/
private lemma card_tapes_many_calls_le_weight_succs {n N m : ℕ} (cnf : UniformCNF n N m)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : ∀ d, (cnf.neighbors d).length ≤ t)
    (c : card_tapes_many_calls_le_Cfg N) :
    ((card_tapes_many_calls_le_succs cnf c).map card_tapes_many_calls_le_weight).sum ≤
      4 * t * card_tapes_many_calls_le_weight c := by
  have h1 := card_tapes_many_calls_le_weight_callCfgs cnf t ht c.2.1 c.2.2 c.1
  have h2 := card_tapes_many_calls_le_weight_mainCfgs c.2.2 c.2.1 N (Nat.sub_le _ _)
  have h3 : 2 * 2 ^ (N - c.2.1) ≤ 4 * t * 2 ^ (N - c.2.1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : t * 2 ^ (c.1.length + 2) * 2 ^ (N - c.2.1) =
      4 * t * (2 ^ c.1.length * 2 ^ (N - c.2.1)) := by
    rw [pow_add]
    ring
  have h5 : card_tapes_many_calls_le_weight c = 2 ^ c.1.length * 2 ^ (N - c.2.1) := rfl
  simp only [card_tapes_many_calls_le_succs, List.map_append, List.sum_append]
  rw [h5]
  linarith

/-- The weights of the possible next configurations of a list of configurations are at most `4 t`
times the total weight of the list. -/
private lemma card_tapes_many_calls_le_weight_flatMap_succs {n N m : ℕ} (cnf : UniformCNF n N m)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : ∀ d, (cnf.neighbors d).length ≤ t)
    (L : List (card_tapes_many_calls_le_Cfg N)) :
    ((L.flatMap (card_tapes_many_calls_le_succs cnf)).map card_tapes_many_calls_le_weight).sum ≤
      4 * t * (L.map card_tapes_many_calls_le_weight).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      Nat.mul_add]
    exact Nat.add_le_add (card_tapes_many_calls_le_weight_succs cnf t ht1 ht c) ih

/-- The total weight of the configurations after `k` calls is at most `(4 t) ^ k 2 ^ N`. -/
private lemma card_tapes_many_calls_le_weight_paths {n N m : ℕ} (cnf : UniformCNF n N m)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : ∀ d, (cnf.neighbors d).length ≤ t) (k : ℕ) :
    ((card_tapes_many_calls_le_paths cnf k).map card_tapes_many_calls_le_weight).sum ≤
      (4 * t) ^ k * 2 ^ N := by
  induction k with
  | zero =>
    simp [card_tapes_many_calls_le_paths, card_tapes_many_calls_le_weight]
  | succ k ih =>
    have hflat := card_tapes_many_calls_le_weight_flatMap_succs cnf t ht1 ht
      (card_tapes_many_calls_le_paths cnf k)
    calc ((card_tapes_many_calls_le_paths cnf (k + 1)).map card_tapes_many_calls_le_weight).sum
        ≤ 4 * t * ((card_tapes_many_calls_le_paths cnf k).map
            card_tapes_many_calls_le_weight).sum := hflat
      _ ≤ 4 * t * ((4 * t) ^ k * 2 ^ N) := Nat.mul_le_mul_left _ ih
      _ = (4 * t) ^ (k + 1) * 2 ^ N := by ring

/-- There are at most `(4 t) ^ k 2 ^ N` different configurations after `k` calls. -/
private lemma card_tapes_many_calls_le_card_paths {n N m : ℕ} (cnf : UniformCNF n N m)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : ∀ d, (cnf.neighbors d).length ≤ t) (k : ℕ) :
    (card_tapes_many_calls_le_paths cnf k).toFinset.card ≤ (4 * t) ^ k * 2 ^ N := by
  calc (card_tapes_many_calls_le_paths cnf k).toFinset.card
      ≤ (card_tapes_many_calls_le_paths cnf k).length := List.toFinset_card_le _
    _ = ((card_tapes_many_calls_le_paths cnf k).map card_tapes_many_calls_le_weight).length :=
        (List.length_map _).symm
    _ ≤ ((card_tapes_many_calls_le_paths cnf k).map card_tapes_many_calls_le_weight).sum := by
        apply List.length_le_sum_of_one_le
        intro i hi
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hi
        exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    _ ≤ (4 * t) ^ k * 2 ^ N := card_tapes_many_calls_le_weight_paths cnf t ht1 ht k

/-- A step of the algorithm either makes no call (and then the stack only loses its top frame, or
keeps its clauses, or the main loop advances with an empty stack), or calls `Fix` for the next
clause
of the main loop (empty stack), or calls `Fix` for a neighbour of the clause of the top frame. -/
private lemma card_tapes_many_calls_le_step_cases {n N m : ℕ} (cnf : UniformCNF n N m)
    (r : ℕ → Bool) (s : State n N) :
    ((cnf.step r s).log = s.log ∧ (cnf.step r s).pos = s.pos ∧
      ((s.stack = [] ∧ (cnf.step r s).stack = [] ∧ s.next ≤ (cnf.step r s).next) ∨
       (∃ f rest, s.stack = f :: rest ∧
          (cnf.step r s).stack.map Prod.fst = rest.map Prod.fst ∧ (cnf.step r s).next = s.next) ∨
       ((cnf.step r s).stack.map Prod.fst = s.stack.map Prod.fst ∧
          (cnf.step r s).next = s.next))) ∨
    (∃ h : s.next < N, s.stack = [] ∧
      card_tapes_many_calls_le_cfgOf (cnf.step r s) =
        ([⟨s.next, h⟩], s.next + 1, ⟨s.next, h⟩ :: s.log) ∧ (cnf.step r s).pos = s.pos + m) ∨
    (∃ (d : Fin N) (j : ℕ) (rest : List (Fin N × ℕ)) (d' : Fin N), s.stack = (d, j) :: rest ∧
      d' ∈ cnf.neighbors d ∧
      card_tapes_many_calls_le_cfgOf (cnf.step r s) =
        (d' :: d :: rest.map Prod.fst, s.next, d' :: s.log) ∧
      (cnf.step r s).pos = s.pos + m) := by
  rcases hst : s.stack with _ | ⟨⟨e, j⟩, rest⟩
  · have hstep : cnf.step r s = (if h : s.next < N then
        (if cnf.IsFalse s.assign ⟨s.next, h⟩ then cnf.callFix r s ⟨s.next, h⟩ [] (s.next + 1)
          else { s with next := s.next + 1 }) else s) := by
      simp only [step, hst]
    rw [hstep]
    split_ifs with hlt hfalse
    · right; left
      exact ⟨hlt, rfl, rfl, rfl⟩
    · left
      exact ⟨rfl, rfl, Or.inl ⟨rfl, hst, Nat.le_succ _⟩⟩
    · left
      exact ⟨rfl, rfl, Or.inl ⟨rfl, hst, le_refl _⟩⟩
  · rcases hn : (cnf.neighbors e)[j]? with _ | d'
    · have hstep : cnf.step r s = { s with stack := rest } := by
        simp only [step, hst, hn]
      rw [hstep]
      left
      exact ⟨rfl, rfl, Or.inr (Or.inl ⟨(e, j), rest, rfl, rfl, rfl⟩)⟩
    · have hstep : cnf.step r s = (if cnf.IsFalse s.assign d' then
          cnf.callFix r s d' ((e, j + 1) :: rest) s.next
          else { s with stack := (e, j + 1) :: rest }) := by
        simp only [step, hst, hn]
      rw [hstep]
      split_ifs with hfalse
      · right; right
        exact ⟨e, j, rest, d', rfl, List.mem_of_getElem? hn, rfl, rfl⟩
      · left
        exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-- The position of the tape is `n + m` times the number of calls. -/
private lemma card_tapes_many_calls_le_pos_eq {n N m : ℕ} (cnf : UniformCNF n N m)
    (r : ℕ → Bool) (t : ℕ) : (cnf.run r t).pos = n + m * (cnf.run r t).log.length := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hrun : cnf.run r (t + 1) = cnf.step r (cnf.run r t) :=
      Function.iterate_succ_apply' _ _ _
    rw [hrun]
    rcases card_tapes_many_calls_le_step_cases cnf r (cnf.run r t) with
      ⟨hlog, hpos, -⟩ | ⟨h, -, hcfg, hpos⟩ | ⟨d, j, rest, d', -, -, hcfg, hpos⟩
    · rw [hlog, hpos]
      exact ih
    · have hlog : (cnf.step r (cnf.run r t)).log = ⟨(cnf.run r t).next, h⟩ :: (cnf.run r t).log :=
        congrArg (fun c => c.2.2) hcfg
      rw [hlog, hpos, List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega
    · have hlog : (cnf.step r (cnf.run r t)).log = d' :: (cnf.run r t).log :=
        congrArg (fun c => c.2.2) hcfg
      rw [hlog, hpos, List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

/-- One step does not decrease the number of calls. -/
private lemma card_tapes_many_calls_le_step_length_le {n N m : ℕ} (cnf : UniformCNF n N m)
    (r : ℕ → Bool) (s : State n N) : s.log.length ≤ (cnf.step r s).log.length := by
  rcases card_tapes_many_calls_le_step_cases cnf r s with
    ⟨hlog, -, -⟩ | ⟨h, -, hcfg, -⟩ | ⟨d, j, rest, d', -, -, hcfg, -⟩
  · rw [hlog]
  · have hlog : (cnf.step r s).log = ⟨s.next, h⟩ :: s.log := congrArg (fun c => c.2.2) hcfg
    rw [hlog, List.length_cons]
    exact Nat.le_succ _
  · have hlog : (cnf.step r s).log = d' :: s.log := congrArg (fun c => c.2.2) hcfg
    rw [hlog, List.length_cons]
    exact Nat.le_succ _

/-- The number of calls does not decrease. -/
private lemma card_tapes_many_calls_le_length_mono {n N m : ℕ} (cnf : UniformCNF n N m)
    (r : ℕ → Bool) {a b : ℕ} (hab : a ≤ b) :
    (cnf.run r a).log.length ≤ (cnf.run r b).log.length := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ b hab ih =>
    have hrun : cnf.run r (b + 1) = cnf.step r (cnf.run r b) :=
      Function.iterate_succ_apply' _ _ _
    rw [hrun]
    exact ih.trans (card_tapes_many_calls_le_step_length_le cnf r _)

/-- A neighbour `d'` of the clause of the frame at position `p` of `st` gives a configuration of
`callCfgs`. -/
private lemma card_tapes_many_calls_le_mem_callCfgs {n N m : ℕ} (cnf : UniformCNF n N m)
    (nx : ℕ) (lg : List (Fin N)) :
    ∀ (st : List (Fin N)) (p : ℕ) (d : Fin N) (rest : List (Fin N)) (d' : Fin N),
      st.drop p = d :: rest → d' ∈ cnf.neighbors d →
      (d' :: d :: rest, nx, d' :: lg) ∈ card_tapes_many_calls_le_callCfgs cnf nx lg st := by
  intro st
  induction st with
  | nil =>
    intro p d rest d' h _
    simp at h
  | cons e st' ih =>
    intro p d rest d' h hd'
    cases p with
    | zero =>
      simp only [List.drop_zero, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [card_tapes_many_calls_le_callCfgs, List.mem_append, List.mem_map]
      exact Or.inl ⟨d', hd', rfl⟩
    | succ p =>
      simp only [List.drop_succ_cons] at h
      simp only [card_tapes_many_calls_le_callCfgs, List.mem_append]
      exact Or.inr (ih p d rest d' h hd')

/-- The configuration after a call from the main loop for the clause `x`, `nx ≤ x < N`, is one of
`mainCfgs` (enough fuel). -/
private lemma card_tapes_many_calls_le_mem_mainCfgs {N : ℕ} (lg : List (Fin N)) (x : ℕ)
    (hx : x < N) :
    ∀ (f nx : ℕ), nx ≤ x → x - nx < f →
      ([⟨x, hx⟩], x + 1, ⟨x, hx⟩ :: lg) ∈ card_tapes_many_calls_le_mainCfgs lg nx f := by
  intro f
  induction f with
  | zero =>
    intro nx _ h
    omega
  | succ f ih =>
    intro nx hnx hf
    have hnxN : nx < N := lt_of_le_of_lt hnx hx
    simp only [card_tapes_many_calls_le_mainCfgs, hnxN, ↓reduceDIte, List.mem_append,
      List.mem_singleton]
    by_cases hxe : x = nx
    · subst hxe
      exact Or.inl rfl
    · exact Or.inr (ih (nx + 1) (by omega) (by omega))

/-- The configuration `c` is reached from `c0` without a call: the log is the same, some frames were
popped (and then the main loop advanced), or the main loop advanced with the stack of `c0` popped.
-/
private def card_tapes_many_calls_le_Rel {N : ℕ} (c0 c : card_tapes_many_calls_le_Cfg N) : Prop :=
  c.2.2 = c0.2.2 ∧ ∃ p, p ≤ c0.1.length ∧ c.1 = c0.1.drop p ∧ c0.2.1 ≤ c.2.1 ∧
    (p < c0.1.length → c.2.1 = c0.2.1)

private lemma card_tapes_many_calls_le_Rel_refl {N : ℕ} (c : card_tapes_many_calls_le_Cfg N) :
    card_tapes_many_calls_le_Rel c c :=
  ⟨rfl, 0, Nat.zero_le _, List.drop_zero.symm, le_rfl, fun _ => rfl⟩

/-- A step without a call keeps the relation `Rel`. -/
private lemma card_tapes_many_calls_le_Rel_step {n N m : ℕ} (cnf : UniformCNF n N m)
    (r : ℕ → Bool) (c0 : card_tapes_many_calls_le_Cfg N) (s : State n N)
    (hrel : card_tapes_many_calls_le_Rel c0 (card_tapes_many_calls_le_cfgOf s))
    (hlog : (cnf.step r s).log = s.log)
    (hnc : (s.stack = [] ∧ (cnf.step r s).stack = [] ∧ s.next ≤ (cnf.step r s).next) ∨
       (∃ f rest, s.stack = f :: rest ∧
          (cnf.step r s).stack.map Prod.fst = rest.map Prod.fst ∧
            (cnf.step r s).next = s.next) ∨
       ((cnf.step r s).stack.map Prod.fst = s.stack.map Prod.fst ∧
          (cnf.step r s).next = s.next)) :
    card_tapes_many_calls_le_Rel c0 (card_tapes_many_calls_le_cfgOf (cnf.step r s)) := by
  obtain ⟨hl, p, hp, hstk, hnx, hnp⟩ := hrel
  unfold card_tapes_many_calls_le_Rel
  simp only [card_tapes_many_calls_le_cfgOf] at hl hstk hnx hnp ⊢
  refine ⟨hlog.trans hl, ?_⟩
  rcases hnc with ⟨hs, hs', hle⟩ | ⟨f, rest, hs, hs', hnext⟩ | ⟨hs', hnext⟩
  · rw [hs] at hstk
    simp only [List.map_nil] at hstk
    have hlen : c0.1.length ≤ p := List.drop_eq_nil_iff.mp hstk.symm
    refine ⟨p, hp, ?_, le_trans hnx hle, fun h => absurd h (not_lt.mpr hlen)⟩
    rw [hs', ← hstk]
    rfl
  · rw [hs] at hstk
    simp only [List.map_cons] at hstk
    have hlt : p < c0.1.length := by
      by_contra hcon
      have : c0.1.drop p = [] := List.drop_eq_nil_iff.mpr (not_lt.mp hcon)
      rw [this] at hstk
      exact List.cons_ne_nil _ _ hstk
    have hnx' : s.next = c0.2.1 := hnp hlt
    refine ⟨p + 1, hlt, ?_, by omega, fun _ => by omega⟩
    rw [hs', ← List.tail_drop, ← hstk]
    rfl
  · exact ⟨p, hp, hs'.trans hstk, by omega, fun h => by rw [hnext]; exact hnp h⟩

/-- A call of `Fix` for the next clause of the main loop gives a configuration of `succs`. -/
private lemma card_tapes_many_calls_le_succs_main {n N m : ℕ} (cnf : UniformCNF n N m)
    (c0 : card_tapes_many_calls_le_Cfg N) (s : State n N)
    (hrel : card_tapes_many_calls_le_Rel c0 (card_tapes_many_calls_le_cfgOf s))
    (h : s.next < N) :
    ([⟨s.next, h⟩], s.next + 1, ⟨s.next, h⟩ :: s.log) ∈ card_tapes_many_calls_le_succs cnf c0 := by
  obtain ⟨hl, p, hp, hstk, hnx, hnp⟩ := hrel
  simp only [card_tapes_many_calls_le_cfgOf] at hl hstk hnx hnp
  unfold card_tapes_many_calls_le_succs
  rw [List.mem_append]
  refine Or.inr ?_
  rw [hl]
  exact card_tapes_many_calls_le_mem_mainCfgs c0.2.2 s.next h N c0.2.1 hnx (by omega)

/-- A call of `Fix` for a neighbour of the clause of the top frame gives a configuration of
`succs`. -/
private lemma card_tapes_many_calls_le_succs_frame {n N m : ℕ} (cnf : UniformCNF n N m)
    (c0 : card_tapes_many_calls_le_Cfg N) (s : State n N)
    (hrel : card_tapes_many_calls_le_Rel c0 (card_tapes_many_calls_le_cfgOf s))
    (d : Fin N) (j : ℕ) (rest : List (Fin N × ℕ)) (d' : Fin N)
    (hs : s.stack = (d, j) :: rest) (hd' : d' ∈ cnf.neighbors d) :
    (d' :: d :: rest.map Prod.fst, s.next, d' :: s.log) ∈
      card_tapes_many_calls_le_succs cnf c0 := by
  obtain ⟨hl, p, hp, hstk, hnx, hnp⟩ := hrel
  simp only [card_tapes_many_calls_le_cfgOf] at hl hstk hnx hnp
  rw [hs] at hstk
  simp only [List.map_cons] at hstk
  have hlt : p < c0.1.length := by
    by_contra hcon
    have : c0.1.drop p = [] := List.drop_eq_nil_iff.mpr (not_lt.mp hcon)
    rw [this] at hstk
    exact List.cons_ne_nil _ _ hstk
  have hnx' : s.next = c0.2.1 := hnp hlt
  unfold card_tapes_many_calls_le_succs
  rw [List.mem_append]
  refine Or.inl ?_
  rw [hnx', hl]
  exact card_tapes_many_calls_le_mem_callCfgs cnf c0.2.1 c0.2.2 c0.1 p d (rest.map Prod.fst) d'
    hstk.symm hd'

/-- If another call is made after time `t`, the first one gives a configuration in
`succs` of the configuration at time `t`. -/
private lemma card_tapes_many_calls_le_next_call {n N m : ℕ} (cnf : UniformCNF n N m)
    (r : ℕ → Bool) (t u : ℕ)
    (hu : (cnf.run r t).log.length < (cnf.run r (t + u)).log.length) :
    ∃ v, (cnf.run r v).log.length = (cnf.run r t).log.length + 1 ∧
      card_tapes_many_calls_le_cfgOf (cnf.run r v) ∈
        card_tapes_many_calls_le_succs cnf (card_tapes_many_calls_le_cfgOf (cnf.run r t)) := by
  have key : ∀ q : ℕ, ((cnf.run r (t + q)).log = (cnf.run r t).log ∧
      card_tapes_many_calls_le_Rel (card_tapes_many_calls_le_cfgOf (cnf.run r t))
        (card_tapes_many_calls_le_cfgOf (cnf.run r (t + q)))) ∨
      ∃ v, (cnf.run r v).log.length = (cnf.run r t).log.length + 1 ∧
        card_tapes_many_calls_le_cfgOf (cnf.run r v) ∈
          card_tapes_many_calls_le_succs cnf (card_tapes_many_calls_le_cfgOf (cnf.run r t)) := by
    intro q
    induction q with
    | zero => exact Or.inl ⟨rfl, card_tapes_many_calls_le_Rel_refl _⟩
    | succ q ih =>
      rcases ih with ⟨hlog, hrel⟩ | hex
      · have hrun : cnf.run r (t + (q + 1)) = cnf.step r (cnf.run r (t + q)) := by
          rw [← Nat.add_assoc]
          exact Function.iterate_succ_apply' _ _ _
        rcases card_tapes_many_calls_le_step_cases cnf r (cnf.run r (t + q)) with
          ⟨hlog', -, hnc⟩ | ⟨h, -, hcfg, -⟩ | ⟨d, j, rest, d', hs, hd', hcfg, -⟩
        · refine Or.inl ⟨?_, ?_⟩
          · rw [hrun]
            exact hlog'.trans hlog
          · rw [hrun]
            exact card_tapes_many_calls_le_Rel_step cnf r _ _ hrel hlog' hnc
        · refine Or.inr ⟨t + (q + 1), ?_, ?_⟩
          · rw [hrun]
            have h3 := congrArg (fun c => c.2.2) hcfg
            simp only [card_tapes_many_calls_le_cfgOf] at h3
            rw [h3, List.length_cons, hlog]
          · rw [hrun, hcfg]
            exact card_tapes_many_calls_le_succs_main cnf _ _ hrel h
        · refine Or.inr ⟨t + (q + 1), ?_, ?_⟩
          · rw [hrun]
            have h3 := congrArg (fun c => c.2.2) hcfg
            simp only [card_tapes_many_calls_le_cfgOf] at h3
            rw [h3, List.length_cons, hlog]
          · rw [hrun, hcfg]
            exact card_tapes_many_calls_le_succs_frame cnf _ _ hrel d j rest d' hs hd'
      · exact Or.inr hex
  rcases key u with ⟨hlog, -⟩ | hex
  · rw [hlog] at hu
    exact absurd hu (lt_irrefl _)
  · exact hex

/-- If `i` calls are made, then at some time the configuration after the `i`-th call is one of the
configurations of `paths`. -/
private lemma card_tapes_many_calls_le_reach {n N m : ℕ} (cnf : UniformCNF n N m)
    (r : ℕ → Bool) (i : ℕ) (h : ∃ t, i ≤ (cnf.run r t).log.length) :
    ∃ t, (cnf.run r t).log.length = i ∧
      card_tapes_many_calls_le_cfgOf (cnf.run r t) ∈ card_tapes_many_calls_le_paths cnf i := by
  induction i with
  | zero =>
    refine ⟨0, rfl, ?_⟩
    change ([], 0, []) ∈ [(([] : List (Fin N)), 0, ([] : List (Fin N)))]
    exact List.mem_singleton_self _
  | succ i ih =>
    obtain ⟨t', ht'⟩ := h
    obtain ⟨t, hlen, hmem⟩ := ih ⟨t', by omega⟩
    have hT : (cnf.run r t).log.length < (cnf.run r (max t t')).log.length := by
      have := card_tapes_many_calls_le_length_mono cnf r (le_max_right t t')
      omega
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le (le_max_left t t')
    rw [hu] at hT
    obtain ⟨v, hv1, hv2⟩ := card_tapes_many_calls_le_next_call cnf r t u hT
    refine ⟨v, by omega, ?_⟩
    simp only [card_tapes_many_calls_le_paths, List.mem_flatMap]
    exact ⟨_, hmem, hv2⟩
/-- Without neighbours, only the main loop makes calls, so at most `N`. -/
private lemma card_tapes_many_calls_le_length_le_of_neighbors_nil {n N m : ℕ}
    (cnf : UniformCNF n N m) (hnb : ∀ d, cnf.neighbors d = []) (r : ℕ → Bool) (t : ℕ) :
    (cnf.run r t).log.length ≤ (cnf.run r t).next ∧ (cnf.run r t).next ≤ N := by
  induction t with
  | zero => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | succ t ih =>
    have hrun : cnf.run r (t + 1) = cnf.step r (cnf.run r t) := Function.iterate_succ_apply' _ _ _
    rw [hrun]
    generalize cnf.run r t = s at ih
    obtain ⟨ih1, ih2⟩ := ih
    rcases hst : s.stack with _ | ⟨⟨e, j⟩, rest⟩
    · simp only [step, hst]
      split_ifs with hlt hfalse
      · simp only [callFix, List.length_cons]
        omega
      · simp only
        omega
      · exact ⟨ih1, ih2⟩
    · simp only [step, hst, hnb e, List.getElem?_nil]
      exact ⟨ih1, ih2⟩

/-- The arithmetic of the final bound. -/
private lemma card_tapes_many_calls_le_arith (n N m c : ℕ) (hm : 3 ≤ m) :
    2 ^ n * ((4 * (2 ^ m / 8)) ^ (N + c) * 2 ^ N) * 2 ^ c = 2 ^ (n + (N + c) * m) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
  have h8 : 2 ^ (m' + 3) / 8 = 2 ^ m' := by
    rw [pow_add]
    exact Nat.mul_div_cancel _ (by norm_num)
  have h4 : 4 * 2 ^ m' = 2 ^ (m' + 2) := by
    rw [pow_add]
    ring
  rw [h8, h4, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

open Classical in
/-- **SUV p. 255.**  The number of tapes on which `Fix` is called at least `N + c` times is at most
a `2^{-c}` fraction, if each clause has at most `2^m / 8` neighbours.  The length of the tape is
what `N + c` calls use. -/
theorem card_tapes_many_calls_le (cnf : UniformCNF n N m) (hdeg : cnf.HasFewNeighbors) (c : ℕ) :
    (Finset.univ.filter fun ρ : Fin (n + (N + c) * m) → Bool =>
        ∃ t, N + c ≤ (cnf.run (tapeOf ρ) t).log.length).card * 2 ^ c ≤
      2 ^ (n + (N + c) * m) := by
  generalize hS : (Finset.univ.filter fun ρ : Fin (n + (N + c) * m) → Bool =>
        ∃ t, N + c ≤ (cnf.run (tapeOf ρ) t).log.length) = S
  have hmem : ∀ ρ, ρ ∈ S ↔ ∃ t, N + c ≤ (cnf.run (tapeOf ρ) t).log.length := by
    intro ρ
    rw [← hS]
    simp
  by_cases hm : 3 ≤ m
  · have ht : ∀ d, (cnf.neighbors d).length ≤ 2 ^ m / 8 := fun d =>
      (Nat.le_div_iff_mul_le (by norm_num)).2 (by have := hdeg d; omega)
    have ht1 : 1 ≤ 2 ^ m / 8 := by
      have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    have hpaths := card_tapes_many_calls_le_card_paths cnf (2 ^ m / 8) ht1 ht (N + c)
    -- a time at which the configuration after the `(N + c)`-th call is reached
    let G : (Fin (n + (N + c) * m) → Bool) → ℕ → Prop := fun ρ t =>
      (cnf.run (tapeOf ρ) t).log.length = N + c ∧
        card_tapes_many_calls_le_cfgOf (cnf.run (tapeOf ρ) t) ∈
          card_tapes_many_calls_le_paths cnf (N + c)
    have hG : ∀ ρ ∈ S, ∃ t, G ρ t := fun ρ hρ =>
      card_tapes_many_calls_le_reach cnf (tapeOf ρ) (N + c) ((hmem ρ).1 hρ)
    let key : (Fin (n + (N + c) * m) → Bool) → (Fin n → Bool) × card_tapes_many_calls_le_Cfg N :=
      fun ρ => if h : ∃ t, G ρ t then
        ((cnf.run (tapeOf ρ) h.choose).assign,
          card_tapes_many_calls_le_cfgOf (cnf.run (tapeOf ρ) h.choose))
      else (fun _ => false, ([], 0, []))
    have hkey : ∀ ρ ∈ S, ∃ t, G ρ t ∧ key ρ =
        ((cnf.run (tapeOf ρ) t).assign, card_tapes_many_calls_le_cfgOf (cnf.run (tapeOf ρ) t)) := by
      intro ρ hρ
      have h := hG ρ hρ
      refine ⟨h.choose, h.choose_spec, ?_⟩
      simp [key, h]
    have hinj : S.card ≤ ((Finset.univ : Finset (Fin n → Bool)) ×ˢ
        (card_tapes_many_calls_le_paths cnf (N + c)).toFinset).card := by
      refine Finset.card_le_card_of_injOn key ?_ ?_
      · intro ρ hρ
        obtain ⟨t, ⟨h1, h2⟩, hk⟩ := hkey ρ hρ
        rw [hk]
        simp [h2]
      · intro ρ hρ ρ' hρ' heq
        obtain ⟨t, ⟨h1, h2⟩, hk⟩ := hkey ρ hρ
        obtain ⟨t', ⟨h1', h2'⟩, hk'⟩ := hkey ρ' hρ'
        rw [hk, hk'] at heq
        have hassign : (cnf.run (tapeOf ρ) t).assign = (cnf.run (tapeOf ρ') t').assign :=
          congrArg Prod.fst heq
        have hlog : (cnf.run (tapeOf ρ) t).log = (cnf.run (tapeOf ρ') t').log :=
          congrArg (fun p => p.2.2.2) heq
        have hdet := random_bits_determined cnf (tapeOf ρ) (tapeOf ρ') hassign hlog
        have hpos : (cnf.run (tapeOf ρ) t).pos = n + (N + c) * m := by
          rw [card_tapes_many_calls_le_pos_eq, h1]
          ring
        funext ⟨i, hi⟩
        have := hdet i (by rw [hpos]; exact hi)
        simpa [tapeOf, hi] using this
    have hcard : ((Finset.univ : Finset (Fin n → Bool)) ×ˢ
        (card_tapes_many_calls_le_paths cnf (N + c)).toFinset).card =
        2 ^ n * (card_tapes_many_calls_le_paths cnf (N + c)).toFinset.card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin]
    calc S.card * 2 ^ c ≤ (2 ^ n * (card_tapes_many_calls_le_paths cnf (N + c)).toFinset.card) *
          2 ^ c := Nat.mul_le_mul_right _ (hcard ▸ hinj)
      _ ≤ 2 ^ n * ((4 * (2 ^ m / 8)) ^ (N + c) * 2 ^ N) * 2 ^ c :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpaths)
      _ = 2 ^ (n + (N + c) * m) := card_tapes_many_calls_le_arith n N m c hm
  · have hm3 : m < 3 := by omega
    by_cases hc : c = 0
    · subst hc
      have h1 : S.card ≤ 2 ^ (n + (N + 0) * m) := by
        calc S.card ≤ Fintype.card (Fin (n + (N + 0) * m) → Bool) := Finset.card_le_univ _
          _ = 2 ^ (n + (N + 0) * m) := by
            rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      simpa using h1
    · have hnb : ∀ d, cnf.neighbors d = [] := by
        intro d
        have h1 := hdeg d
        have h2 : 2 ^ m ≤ 4 := by
          have hm2 : m ≤ 2 := by omega
          calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
            _ = 4 := by norm_num
        have h3 : (cnf.neighbors d).length = 0 := by omega
        exact List.length_eq_zero_iff.mp h3
      have hS0 : S = ∅ := by
        refine Finset.eq_empty_of_forall_notMem ?_
        intro ρ hρ
        obtain ⟨t, ht⟩ := (hmem ρ).1 hρ
        have := card_tapes_many_calls_le_length_le_of_neighbors_nil cnf hnb (tapeOf ρ) t
        omega
      rw [hS0]
      simp

/-- Auxiliary invariant for the time bound. -/
private theorem isHalted_run_of_calls_le_time_aux {n N m : ℕ}
    (cnf : UniformCNF n N m) (r : ℕ → Bool) (t : ℕ)
    (hnot : ¬ (cnf.run r t).IsHalted) :
    t + (N + 1) * (cnf.run r t).stack.length ≤ (cnf.run r t).next +
      (N + 1) * (cnf.run r t).log.length +
      ((cnf.run r t).stack.map (fun p => min p.2 N)).sum := by
  induction t with
  | zero => simp [UniformCNF.run, initial]
  | succ t ih =>
    have hrun : cnf.run r (t + 1) = cnf.step r (cnf.run r t) := by
      unfold UniformCNF.run; exact Function.iterate_succ_apply' _ _ _
    rw [hrun] at hnot ⊢
    generalize cnf.run r t = s at *
    by_cases hs : s.IsHalted
    · exfalso
      apply hnot
      obtain ⟨h1, h2⟩ := hs
      have : cnf.step r s = s := by simp [step, h1, not_lt.mpr h2]
      rw [this]; exact ⟨h1, h2⟩
    · have ih := ih hs
      obtain ⟨assign, stack, next, pos, log⟩ := s
      simp only at ih hs
      rcases stack with _ | ⟨⟨d, j⟩, rest⟩
      · have hn : next < N := by
          by_contra hc
          exact hs ⟨rfl, not_lt.mp hc⟩
        by_cases hf : cnf.IsFalse assign ⟨next, hn⟩
        · simp [step, hn, hf, callFix] at ih ⊢
          simp only [Nat.mul_add, Nat.mul_one] at ih ⊢
          omega
        · simp [step, hn, hf] at ih ⊢
          omega
      · simp only [List.length_cons, List.map_cons, List.sum_cons] at ih
        simp only [step]
        rcases hd : (cnf.neighbors d)[j]? with _ | d'
        · have := min_le_right j N
          simp
          simp only [Nat.mul_add, Nat.mul_one] at ih ⊢
          omega
        · have hj : j < N := by
            have h1 := (List.getElem?_eq_some_iff.mp hd).1
            have h2 : (cnf.neighbors d).length ≤ N := by
              unfold neighbors
              exact (List.length_filter_le _ _).trans (by simp)
            omega
          by_cases hf : cnf.IsFalse assign d'
          · simp [hf, callFix]
            simp only [Nat.mul_add, Nat.mul_one] at ih ⊢
            omega
          · simp [hf]
            omega

/-- Step 1 of the proof of `isHalted_run_of_calls_le`: before halting, each main-loop
clause and each call's neighbor checks and return account for the elapsed steps. -/
private theorem isHalted_run_of_calls_le_time {n N m : ℕ}
    (cnf : UniformCNF n N m) (r : ℕ → Bool) {t : ℕ}
    (hnot : ¬ (cnf.run r t).IsHalted) :
    t ≤ (cnf.run r t).next + (cnf.run r t).log.length * (N + 1) +
      (cnf.run r t).stack.length := by
  have h := isHalted_run_of_calls_le_time_aux cnf r t hnot
  have hsum : ((cnf.run r t).stack.map (fun p => min p.2 N)).sum ≤
      N * (cnf.run r t).stack.length := by
    generalize (cnf.run r t).stack = L
    induction L with
    | nil => simp
    | cons p L ihL =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      have := min_le_right p.2 N
      omega
  nlinarith

private theorem isHalted_run_of_calls_le_stack_len_aux {n N m : ℕ}
    (cnf : UniformCNF n N m) (r : ℕ → Bool) (s : State n N)
    (h : s.stack.length ≤ s.log.length) :
    (cnf.step r s).stack.length ≤ (cnf.step r s).log.length := by
  unfold step
  rcases hs : s.stack with _ | ⟨⟨d, j⟩, rest⟩
  · simp only
    split_ifs <;> simp_all [callFix]
  · simp only
    rw [hs] at h
    rcases hn : (cnf.neighbors d)[j]? with _ | d'
    · simp only
      simp at h ⊢
      omega
    · simp only
      split_ifs <;> simp_all [callFix]

/-- Step 2 of the proof of `isHalted_run_of_calls_le`: active calls are recorded in the
call log. -/
private theorem isHalted_run_of_calls_le_stack_len {n N m : ℕ}
    (cnf : UniformCNF n N m) (r : ℕ → Bool) (t : ℕ) :
    (cnf.run r t).stack.length ≤ (cnf.run r t).log.length := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih =>
    have : cnf.run r (t + 1) = cnf.step r (cnf.run r t) := by
      simp only [run]
      exact Function.iterate_succ_apply' _ _ _
    rw [this]
    exact isHalted_run_of_calls_le_stack_len_aux cnf r _ ih

private theorem isHalted_run_of_calls_le_next_le_step_aux {n N m : ℕ}
    (cnf : UniformCNF n N m) (r : ℕ → Bool) (s : UniformCNF.State n N) (h : s.next ≤ N) :
    (cnf.step r s).next ≤ N := by
  unfold UniformCNF.step
  rcases hs : s.stack with _ | ⟨⟨d, j⟩, rest⟩
  · simp only
    split_ifs with h1 h2
    · simp [UniformCNF.callFix]; omega
    · simp; omega
    · exact h
  · simp only
    rcases hn : (cnf.neighbors d)[j]? with _ | d'
    · simpa using h
    · simp only
      split_ifs with h1
      · simpa [UniformCNF.callFix] using h
      · simpa using h

/-- Step 3 of the proof of `isHalted_run_of_calls_le`: the main loop advances at most
through all `N` clauses. -/
private theorem isHalted_run_of_calls_le_next_le {n N m : ℕ}
    (cnf : UniformCNF n N m) (r : ℕ → Bool) (t : ℕ) :
    (cnf.run r t).next ≤ N := by
  induction t with
  | zero => simp [UniformCNF.run, UniformCNF.initial]
  | succ t ih =>
    rw [UniformCNF.run, Function.iterate_succ_apply', ← UniformCNF.run]
    exact isHalted_run_of_calls_le_next_le_step_aux cnf r _ ih

/-- As long as `Fix` was called at most `N` times, the algorithm finishes within `(N + 2)²` steps:
the main loop has `N` steps, and each call has at most `N + 1` steps of its own. -/
theorem isHalted_run_of_calls_le (cnf : UniformCNF n N m) (r : ℕ → Bool)
    (hcalls : ∀ t, (cnf.run r t).log.length ≤ N) : (cnf.run r ((N + 2) ^ 2)).IsHalted := by
  by_contra hnot
  have h1 := isHalted_run_of_calls_le_time cnf r hnot
  have h2 := isHalted_run_of_calls_le_stack_len cnf r ((N + 2) ^ 2)
  have h3 := isHalted_run_of_calls_le_next_le cnf r ((N + 2) ^ 2)
  have h4 := hcalls ((N + 2) ^ 2)
  have h5 : (cnf.run r ((N + 2) ^ 2)).log.length * (N + 1) ≤ N * (N + 1) := Nat.mul_le_mul_right (N
      + 1) h4
  nlinarith

open Classical in
/-- **SUV Theorem 163, p. 253.**  The algorithm finds a satisfying assignment for a CNF with `n`
variables and `N` clauses of size `m`, each with at most `2^m / 8` neighbours, within `(N + 2)²` of
its steps and with success probability at least `1/2` over a tape of `n + (N + 1) m` random bits.
Each step costs time polynomial in `n + N`, so the time is polynomial in `n + N`.  The hypothesis
`0 < m` excludes the clauses with no variables, which are always false and have no neighbours, so
that the theorem would fail for them.  The book's "clause of size `m`" has `m ≥ 1`.  The
amplification by repetition, mentioned in parentheses on p. 253, is not modelled. -/
theorem card_tapes_success (cnf : UniformCNF n N m) (hm : 0 < m) (hdeg : cnf.HasFewNeighbors) :
    2 ^ (n + (N + 1) * m) ≤ 2 * (Finset.univ.filter fun ρ : Fin (n + (N + 1) * m) → Bool =>
      (cnf.run (tapeOf ρ) ((N + 2) ^ 2)).IsHalted ∧
        cnf.Satisfies (cnf.run (tapeOf ρ) ((N + 2) ^ 2)).assign).card := by
  let S := Finset.univ.filter (fun ρ : Fin (n + (N + 1) * m) → Bool =>
        ∃ t, N + 1 ≤ (cnf.run (tapeOf ρ) t).log.length)
  let T := Finset.univ.filter (fun ρ : Fin (n + (N + 1) * m) → Bool =>
      (cnf.run (tapeOf ρ) ((N + 2) ^ 2)).IsHalted ∧
        cnf.Satisfies (cnf.run (tapeOf ρ) ((N + 2) ^ 2)).assign)
  have hS : S.card * 2 ≤ 2 ^ (n + (N + 1) * m) := by
    have := cnf.card_tapes_many_calls_le hdeg 1
    exact this
  have h_univ : Finset.univ ⊆ S ∪ T := by
    intro ρ _
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h : ∃ t, N + 1 ≤ (cnf.run (tapeOf ρ) t).log.length
    · exact Or.inl ⟨Finset.mem_univ _, h⟩
    · right
      refine ⟨Finset.mem_univ _, ?_⟩
      push Not at h
      have h1 : ∀ t, (cnf.run (tapeOf ρ) t).log.length ≤ N := fun t => by
        have := h t
        omega
      have h2 := cnf.isHalted_run_of_calls_le (tapeOf ρ) h1
      exact ⟨h2, cnf.satisfies_of_isHalted hm (tapeOf ρ) h2⟩
  have h_card : 2 ^ (n + (N + 1) * m) ≤ S.card + T.card := by
    calc
      2 ^ (n + (N + 1) * m) = Fintype.card (Fin (n + (N + 1) * m) → Bool) := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      _ = Finset.univ.card := Finset.card_univ.symm
      _ ≤ (S ∪ T).card := Finset.card_le_card h_univ
      _ ≤ S.card + T.card := Finset.card_union_le S T
  have hT_eq : T.card = (Finset.univ.filter fun ρ : Fin (n + (N + 1) * m) → Bool =>
      (cnf.run (tapeOf ρ) ((N + 2) ^ 2)).IsHalted ∧
        cnf.Satisfies (cnf.run (tapeOf ρ) ((N + 2) ^ 2)).assign).card := rfl
  omega

/-- A finite set with at least half of the `2^L` elements is non-empty. -/
private lemma nonempty_of_two_pow_le {α : Type*} {L : ℕ} (s : Finset α) (h : 2 ^ L ≤ 2 * s.card) :
    s.Nonempty := by
  refine Finset.card_pos.mp (Nat.pos_of_ne_zero fun h0 => ?_)
  rw [h0, Nat.mul_zero] at h
  exact absurd h (Nat.not_le_of_gt (Nat.two_pow_pos _))

open Classical in
/-- **SUV p. 252.**  In particular, such a CNF is satisfiable: the constructive proof gives this
special case of the local lemma. -/
theorem exists_satisfies (cnf : UniformCNF n N m) (hm : 0 < m) (hdeg : cnf.HasFewNeighbors) :
    ∃ a, cnf.Satisfies a := by
  obtain ⟨ρ, hρ⟩ := nonempty_of_two_pow_le _ (cnf.card_tapes_success hm hdeg)
  exact ⟨_, (Finset.mem_filter.mp hρ).2.2⟩

end UniformCNF

end Kolmogorov.Applications
