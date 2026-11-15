/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Game
import KolmogorovMathlib.RandomStrings.TTMeet2014.TruthTable
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Winning sets of the `n`-bit game (§4.1.3 of the paper)

The board of the `n`-bit game is the set of queries of the first `n` truth tables, and the outcome
of a position is the vector of table values.  A set `S` of outcome vectors is *winning* if we can
force the outcome into `S`.

## Generic layer (a value function `v` into a finite set `D`)

* `forces_or_compl`, `not_forces_and_compl`: `S` or its complement is winning, not both.
* `families_eq_of_no_split`: if no `S` is winning on one board with its complement winning on
  another, the two boards have the same collection of winning sets (the "disagreement" branch).
* `exists_generator`: a collection of winning sets closed under intersection is the principal
  ultrafilter of some `σ` (the "ultrafilter" branch).

## Arena layer

* Units: `unitWeight N τ` is `2 ^ (N + 1 - |τ|)`, which is `realCost τ = 2 ^ (1 - |τ|)` in units of
  `2 ^ (-N)` (`unitWeight_eq_realCost`).  This is the paper's cost of the move `⟨|τ| - 1, τ⟩`.
* `arenaOf c tables`: for `ε = 2 ^ (-c)` the unit is `2 ^ (-(c + L + 1))`, with `L` the maximal
  query length, so that `levelBudget tables ℓ = 2 ^ (L + 1 - ℓ)` is `ε / 2 ^ ℓ`.  Every string whose
  cost does not exceed `ε` has length greater than `c` (`length_gt_of_weight_le`): this is what
  insulates higher-priority boards.
* `zero_level`: at level `L` nobody can move, so the stack ends in the zero game.
* `forces_lift_iff`: compatibility.  Forcing a set of `n`-bit vectors in the `(n+m)`-bit game has
  the same value as in the `n`-bit game, despite the different board and unit; hence the generators
  for `n + m` and `n` bits have compatible initial segments (`generator_take`).
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

section Generic

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- `S` is winning at the position `A` for `G(a, b)`, for the outcome function `v`. -/
def Forces (w : α → ℕ) (v : Finset α → β) (S : Finset β) (A : Finset α) (a b : ℕ) : Prop :=
  Wins w (fun B => v B ∈ S) A a b

variable {w : α → ℕ} {v : Finset α → β} {D S S' : Finset β} {A : Finset α} {a b : ℕ}

omit [DecidableEq β] in
/-- A superset of a winning set is winning, at the same position and budgets. -/
theorem Forces.mono (h : Forces w v S A a b) (hS : S ⊆ S') : Forces w v S' A a b :=
  Wins.mono_target h fun _ hB => hS hB

/-- `S` or its complement in `D` is winning, in a symmetric game. -/
theorem forces_or_compl (hD : ∀ B, v B ∈ D) (S : Finset β) (A : Finset α) (a : ℕ) :
    Forces w v S A a a ∨ Forces w v (D \ S) A a a := by
  rcases wins_or_compl w (fun B => v B ∈ S) A a with h | h
  · exact Or.inl h
  · exact Or.inr (Wins.mono_target h fun B hB => mem_sdiff.2 ⟨hD B, hB⟩)

/-- `S` and its complement are not both winning, in a symmetric game. -/
theorem not_forces_and_compl (h : Forces w v S A a a) : ¬ Forces w v (D \ S) A a a := fun h' =>
  not_wins_and_compl h (Wins.mono_target h' fun _ hB => (mem_sdiff.1 hB).2)

omit [DecidableEq β] in
/-- The empty set is never winning in a symmetric game. -/
theorem not_forces_empty : ¬ Forces w v ∅ A a a := by
  classical
  intro h
  exact not_forces_and_compl (D := ∅) h (Forces.mono h (empty_subset _))

/-- If there is no split between two boards, they have the same collection of winning sets. -/
theorem families_eq_of_no_split {A A' : Finset α} (hD : ∀ B, v B ∈ D)
    (hno : ∀ S ⊆ D, ¬ (Forces w v S A a a ∧ Forces w v (D \ S) A' a a)) :
    ∀ S ⊆ D, (Forces w v S A a a ↔ Forces w v S A' a a) := by
  intro S hS
  constructor
  · intro h
    rcases forces_or_compl hD S A' a with h' | h'
    · exact h'
    · exact absurd ⟨h, h'⟩ (hno S hS)
  · intro h'
    rcases forces_or_compl hD S A a with h | h
    · exact h
    · have hc : D \ (D \ S) = S := by
        ext x
        simp only [mem_sdiff]
        constructor
        · rintro ⟨hx, hn⟩
          by_contra hxS
          exact hn ⟨hx, hxS⟩
        · exact fun hx => ⟨hS hx, fun hn => hn.2 hx⟩
      exact absurd ⟨h, by rwa [hc]⟩ (hno (D \ S) sdiff_subset)

/-- With intersections available, every winning set contains a winning singleton. -/
theorem exists_singleton_of_forces (hD : ∀ B, v B ∈ D)
    (hmeet : ∀ S T, S ⊆ D → T ⊆ D → Forces w v S A a a → Forces w v T A a a →
      Forces w v (S ∩ T) A a a) :
    ∀ S, S ⊆ D → Forces w v S A a a → ∃ σ ∈ S, Forces w v {σ} A a a := by
  intro S
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hSD hS
    have hne : S.Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      subst hemp
      exact not_forces_empty hS
    obtain ⟨σ, hσ⟩ := hne
    rcases forces_or_compl (w := w) hD {σ} A a with h | h
    · exact ⟨σ, hσ, h⟩
    · have hsub : S ∩ (D \ {σ}) ⊆ D := inter_subset_left.trans hSD
      have hF := hmeet S _ hSD sdiff_subset hS h
      have hcard : (S ∩ (D \ {σ})).card < S.card := by
        refine card_lt_card ⟨inter_subset_left, fun hall => ?_⟩
        have := mem_inter.1 (hall hσ)
        exact (mem_sdiff.1 this.2).2 (mem_singleton_self σ)
      obtain ⟨σ', hσ', hF'⟩ := ih _ (hn ▸ hcard) _ rfl hsub hF
      exact ⟨σ', (mem_inter.1 hσ').1, hF'⟩

/-- **Principal ultrafilter.**  A collection of winning sets in a symmetric game that is closed
under intersection is generated by one vector `σ`, and `{σ}` is winning. -/
theorem exists_generator (hD : ∀ B, v B ∈ D)
    (hmeet : ∀ S T, S ⊆ D → T ⊆ D → Forces w v S A a a → Forces w v T A a a →
      Forces w v (S ∩ T) A a a) :
    ∃ σ ∈ D, Forces w v {σ} A a a ∧ ∀ S ⊆ D, (Forces w v S A a a ↔ σ ∈ S) := by
  have hDwin : Forces w v D A a a := by
    rcases forces_or_compl (w := w) (A := A) (a := a) hD ∅ with h | h
    · exact Forces.mono h (empty_subset _)
    · simpa using h
  obtain ⟨σ, hσ, hF⟩ := exists_singleton_of_forces hD hmeet D (Subset.refl _) hDwin
  refine ⟨σ, hσ, hF, fun S hS => ⟨fun hS' => ?_, fun hσS => ?_⟩⟩
  · by_contra hσS
    have := hmeet S {σ} hS (singleton_subset_iff.2 hσ) hS' hF
    have hemp : S ∩ {σ} = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨hxS, hxσ⟩ := mem_inter.1 hx
      rw [mem_singleton.1 hxσ] at hxS
      exact hσS hxS
    rw [hemp] at this
    exact not_forces_empty this
  · exact Forces.mono hF (singleton_subset_iff.2 hσS)

omit [DecidableEq β] in
/-- The zero game: `{σ}` is winning iff the current outcome is `σ`. -/
theorem forces_singleton_zero {σ : β} (ha : ∀ τ ∈ A, a < w τ) (hb : ∀ τ ∈ A, b < w τ) :
    Forces w v {σ} A a b ↔ v A = σ := by
  unfold Forces
  rw [wins_zero_game ha hb, mem_singleton]

end Generic

/-! ### Units -/

/-- The cost of compressing `τ` to length `|τ| - 1`, as a rational: `2 ^ (1 - |τ|)`.  This is the
weight of the request `⟨|τ| - 1, τ⟩` of §4.3. -/
def realCost (τ : Str) : ℚ := 2 / 2 ^ τ.length

/-- The same cost in units of `2 ^ (-N)`.  It is exact for `|τ| ≤ N + 1`. -/
def unitWeight (N : ℕ) (τ : Str) : ℕ := 2 ^ (N + 1 - τ.length)

/-- For `|τ| ≤ N + 1` the weight in units of `2 ^ (-N)` is exact:
`unitWeight N τ = realCost τ * 2 ^ N`. -/
theorem unitWeight_eq_realCost {N : ℕ} {τ : Str} (h : τ.length ≤ N + 1) :
    (unitWeight N τ : ℚ) = realCost τ * 2 ^ N := by
  have hN : N + 1 = (N + 1 - τ.length) + τ.length := by omega
  have h2 : (2 : ℚ) ^ (N + 1) = 2 ^ (N + 1 - τ.length) * 2 ^ τ.length := by
    rw [← pow_add, ← hN]
  have hne : (2 : ℚ) ^ τ.length ≠ 0 := by positivity
  simp only [unitWeight, realCost]
  push_cast
  field_simp
  rw [← h2, pow_succ]
  ring

/-- The cost of every string is positive. -/
theorem realCost_pos (τ : Str) : 0 < realCost τ := by
  unfold realCost
  positivity

/-! ### Arenas -/

/-- The maximal length of a query of the tables. -/
def maxLen (tables : List TTable) : ℕ :=
  (tables.flatMap TTable.queries).foldr (fun z n => max z.length n) 0

/-- Each string of a list is at most as long as the maximum length, computed by a right fold. -/
theorem length_le_foldr_max {L : List Str} {z : Str} (h : z ∈ L) :
    z.length ≤ L.foldr (fun z n => max z.length n) 0 := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    rcases List.mem_cons.1 h with rfl | h'
    · exact le_max_left _ _
    · exact (ih h').trans (le_max_right _ _)

/-- The board and the unit of a game: the first `n` tables, for the starting measure `2 ^ (-c)`.
The unit is `2 ^ (-scale)`. -/
structure Arena where
  /-- The truth tables of the first `n` bits. -/
  tables : List TTable
  /-- `1` unit is `2 ^ (-scale)`. -/
  scale : ℕ

/-- The arena for the first bits with tables `tables` and starting measure `ε = 2 ^ (-c)`. -/
def arenaOf (c : ℕ) (tables : List TTable) : Arena := ⟨tables, c + maxLen tables + 1⟩

/-- The board, as a duplicate-free list. -/
def Arena.boardList (ar : Arena) : List Str := (ar.tables.flatMap TTable.queries).dedup

/-- The board. -/
def Arena.board (ar : Arena) : Finset Str := ar.boardList.toFinset

/-- The weights of the moves. -/
def Arena.w (ar : Arena) : Str → ℕ := unitWeight ar.scale

/-- The outcome vector of a position: the values of the tables when `B` is the set of alive strings.
Only `B ∩ board` matters (`Arena.value_inter`). -/
def Arena.value (ar : Arena) (B : Finset Str) : List Bool :=
  ar.tables.map fun t => t.evalB fun z => decide (z ∈ B)

/-- The set `S` of outcome vectors is winning in `G(a, b)` at the position `A`. -/
def Arena.Forces (ar : Arena) (S : Finset (List Bool)) (A : Finset Str) (a b : ℕ) : Prop :=
  TTMeet.Forces ar.w ar.value S A a b

/-- The budget at level `ℓ` of the stack: `ε / 2 ^ ℓ`, in the units of `arenaOf c tables`. -/
def levelBudget (tables : List TTable) (ℓ : ℕ) : ℕ := 2 ^ (maxLen tables + 1 - ℓ)

/-- All Boolean vectors of length `n`, as a list. -/
def allVec : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allVec n).flatMap fun v => [v ++ [false], v ++ [true]]

/-- `allVec n` lists exactly the Boolean vectors of length `n`. -/
theorem mem_allVec {n : ℕ} {v : List Bool} : v ∈ allVec n ↔ v.length = n := by
  induction n generalizing v with
  | zero =>
    simp only [allVec, List.mem_singleton]
    exact ⟨fun h => by simp [h], List.length_eq_zero_iff.1⟩
  | succ n ih =>
    simp only [allVec, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨u, hu, rfl | rfl⟩ <;> simp [ih.1 hu]
    · intro hv
      obtain ⟨u, b, rfl⟩ : ∃ u b, v = u ++ [b] := by
        have hne : v ≠ [] := by
          intro h
          simp [h] at hv
        exact ⟨v.dropLast, v.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      refine ⟨u, ih.2 (by simpa using hv), ?_⟩
      cases b <;> simp

/-- All Boolean vectors of length `n`. -/
def vectors (n : ℕ) : Finset (List Bool) := (allVec n).toFinset

/-- `vectors n` consists exactly of the Boolean vectors of length `n`. -/
theorem mem_vectors {n : ℕ} {v : List Bool} : v ∈ vectors n ↔ v.length = n := by
  simp [vectors, mem_allVec]

/-- The outcome vector of a position has one bit per table. -/
theorem Arena.value_mem_vectors (ar : Arena) (B : Finset Str) :
    ar.value B ∈ vectors ar.tables.length := by
  simp [mem_vectors, Arena.value]

/-- A string is on the board iff it is a query of one of the tables. -/
theorem Arena.mem_board {ar : Arena} {z : Str} :
    z ∈ ar.board ↔ ∃ t ∈ ar.tables, z ∈ t.queries := by
  simp [Arena.board, Arena.boardList]

/-- Every string of the board has length at most `maxLen`. -/
theorem length_le_maxLen {tables : List TTable} {z : Str} (h : ∃ t ∈ tables, z ∈ t.queries) :
    z.length ≤ maxLen tables := by
  apply length_le_foldr_max
  simpa using h

/-- The value depends only on the board. -/
theorem Arena.value_inter (ar : Arena) (B : Finset Str) : ar.value (B ∩ ar.board) = ar.value B := by
  unfold Arena.value
  refine List.map_congr_left fun t ht => TTable.evalB_congr fun z hz => ?_
  have : z ∈ ar.board := Arena.mem_board.2 ⟨t, ht, hz⟩
  simp [this]

/-- A move within budget `ε = 2 ^ (-c)` only touches strings longer than `c`.  This is the
insulation of higher-priority boards: `c` exceeds the length of every string on them. -/
theorem length_gt_of_weight_le {c : ℕ} {tables : List TTable} {τ : Str}
    (hτ : τ.length ≤ maxLen tables)
    (h : (arenaOf c tables).w τ ≤ levelBudget tables 0) : c < τ.length := by
  simp only [Arena.w, arenaOf, unitWeight, levelBudget, Nat.sub_zero] at h
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
  omega

/-- At level `maxLen` both players are unable to move: the stack ends in the zero game. -/
theorem zero_level (c : ℕ) (tables : List TTable) {τ : Str} (hτ : τ.length ≤ maxLen tables) :
    levelBudget tables (maxLen tables) < (arenaOf c tables).w τ := by
  simp only [Arena.w, arenaOf, unitWeight, levelBudget]
  refine Nat.pow_lt_pow_right (by norm_num) ?_
  omega

/-- The levels of the stack are dyadic. -/
theorem levelBudget_succ (tables : List TTable) {ℓ : ℕ} (h : ℓ ≤ maxLen tables) :
    levelBudget tables ℓ = 2 * levelBudget tables (ℓ + 1) := by
  unfold levelBudget
  rw [show maxLen tables + 1 - ℓ = (maxLen tables + 1 - (ℓ + 1)) + 1 by omega, pow_succ]
  ring

/-- In the zero level, the only winning singleton is the current outcome. -/
theorem forces_zero_level {c : ℕ} {tables : List TTable} {A : Finset Str} {σ : List Bool}
    (hA : A ⊆ (arenaOf c tables).board) :
    (arenaOf c tables).Forces {σ} A (levelBudget tables (maxLen tables))
      (levelBudget tables (maxLen tables)) ↔ (arenaOf c tables).value A = σ := by
  have hsmall : ∀ τ ∈ A, levelBudget tables (maxLen tables) < (arenaOf c tables).w τ := fun τ hτ =>
    zero_level c tables (length_le_maxLen (Arena.mem_board.1 (hA hτ)))
  exact forces_singleton_zero hsmall hsmall

/-! ### Compatibility of initial segments -/

/-- Appending tables does not decrease the maximal query length. -/
theorem maxLen_le_of_prefix (tables more : List TTable) :
    maxLen tables ≤ maxLen (tables ++ more) := by
  simp only [maxLen, List.flatMap_append, List.foldr_append]
  induction tables.flatMap TTable.queries with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons]
    exact max_le (le_max_left _ _) (ih.trans (le_max_right _ _))

/-- The vectors of the longer game whose initial segment lies in `S`. -/
def liftSet (n m : ℕ) (S : Finset (List Bool)) : Finset (List Bool) :=
  (vectors (n + m)).filter fun v => v.take n ∈ S

/-- **Compatibility.**  Forcing `S ⊆ 2 ^ n` in the `(n + m)`-bit game is the same as in the `n`-bit
game, on the restricted position: extra strings do not matter (`wins_restrict_iff`), and the change
of unit is harmless (`wins_scale_iff`). -/
theorem forces_lift_iff (c : ℕ) (tables more : List TTable) (S : Finset (List Bool))
    (A : Finset Str) :
    (arenaOf c (tables ++ more)).Forces (liftSet tables.length more.length S) A
        (levelBudget (tables ++ more) 0) (levelBudget (tables ++ more) 0) ↔
      (arenaOf c tables).Forces S (A ∩ (arenaOf c tables).board)
        (levelBudget tables 0) (levelBudget tables 0) := by
  set L := maxLen tables with hL
  set L' := maxLen (tables ++ more) with hL'
  have hLL : L ≤ L' := maxLen_le_of_prefix tables more
  set Q := (arenaOf c tables).board with hQ
  have hval : ∀ B : Finset Str, (arenaOf c (tables ++ more)).value B ∈
      liftSet tables.length more.length S ↔ (arenaOf c tables).value (B ∩ Q) ∈ S := by
    intro B
    rw [Arena.value_inter]
    simp only [liftSet, mem_filter, mem_vectors, Arena.value, arenaOf, List.map_append,
      List.length_append, List.length_map, true_and]
    rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  have hk : 0 < 2 ^ (L' - L) := by positivity
  have hbudget : levelBudget (tables ++ more) 0 = 2 ^ (L' - L) * levelBudget tables 0 := by
    simp only [levelBudget, Nat.sub_zero, ← hL, ← hL']
    rw [← pow_add]
    congr 1
    omega
  have hweight : ∀ τ ∈ A ∩ Q, (arenaOf c (tables ++ more)).w τ =
      2 ^ (L' - L) * (arenaOf c tables).w τ := by
    intro τ hτ
    have hτL : τ.length ≤ L := length_le_maxLen (Arena.mem_board.1 (mem_inter.1 hτ).2)
    simp only [Arena.w, arenaOf, unitWeight, ← hL, ← hL']
    rw [← pow_add]
    congr 1
    omega
  unfold Arena.Forces TTMeet.Forces
  rw [wins_congr_target hval, wins_restrict_iff (T := fun B => (arenaOf c tables).value B ∈ S),
    wins_congr_weight (w' := fun τ => 2 ^ (L' - L) * (arenaOf c tables).w τ) hweight, hbudget]
  exact wins_scale_iff hk

/-- **Compatible initial segments.**  If `{σ}` is winning in the `(n + m)`-bit game, its initial
segment is winning in the `n`-bit game. -/
theorem generator_take {c : ℕ} {tables more : List TTable} {A : Finset Str} {σ : List Bool}
    (hσ : σ.length = tables.length + more.length)
    (h : (arenaOf c (tables ++ more)).Forces {σ} A
      (levelBudget (tables ++ more) 0) (levelBudget (tables ++ more) 0)) :
    (arenaOf c tables).Forces {σ.take tables.length} (A ∩ (arenaOf c tables).board)
      (levelBudget tables 0) (levelBudget tables 0) := by
  refine (forces_lift_iff c tables more _ A).1 (Forces.mono h ?_)
  intro v hv
  rw [mem_singleton.1 hv]
  simp [liftSet, mem_vectors, hσ]

end Kolmogorov.RandomStrings.TTMeet
