/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Insulation

/-!
# Tools for the invariants of the games

* `mem_position`, `position_between_visits`: how a position evolves between visits.
* `oppSpend_add`, `oppSpend_self`, `forces_after_stage`: unanswered opponent moves (§4.1.2).
* `forces_all_of_no_split`, `topOutcome_split_forces`, `topOutcome_meet_forces`: the verdicts of an
  examination give winning positions on the right boards.
* `firstStackSplit_some`, `firstStackSplit_none`: the stack of games.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

variable {I : Input}

/-- Membership in a position. -/
theorem mem_position {st : ConState} {ar : Arena} {t : ℕ} {j : Fin 3} {z : Str} :
    z ∈ st.position I ar t j ↔ z ∈ ar.board ∧ I.opp t z = false ∧ z ∉ st.ours j := by
  simp only [ConState.position, ConState.positionList, List.mem_toFinset, List.mem_filter,
    ConState.alive, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Arena.board]

/-- A string is in `boardOf tables` iff it is on the board of `arenaOf c tables`, for any `c`. -/
theorem mem_boardOf_iff {c : ℕ} {tables : List TTable} {z : Str} :
    z ∈ boardOf tables ↔ z ∈ (arenaOf c tables).board := by
  rw [boardOf, Arena.mem_board, Arena.mem_board]
  rfl

/-- **The board changes only by the opponent between visits.**  Between two consecutive visits of
`R_i` with no reset at the second one, the position changes only by the opponent's moves. -/
theorem position_between_visits (hI : I.Valid) {i s s' c : ℕ} {tables : List TTable}
    (hvisit : (Nat.unpair s).1 = i) (hlt : s < s')
    (hbetween : ∀ s'', s < s'' → s'' < s' → (Nat.unpair s'').1 ≠ i)
    (hno : mustReset I (stateAt I s') i (Nat.unpair s').2 (s' + 1) = false)
    (ht : (rsAt I (s + 1) i).tables = tables) (j : Fin 3) :
    (stateAt I s').position I (arenaOf c tables) (s' + 1) j =
      ((stateAt I (s + 1)).position I (arenaOf c tables) (s + 1) j).filter
        fun τ => !(I.opp (s' + 1) τ) := by
  ext z
  rw [mem_filter, mem_position, mem_position]
  simp only [Bool.not_eq_true']
  constructor
  · rintro ⟨hb, ho, hn⟩
    refine ⟨⟨hb, ?_, fun hmem => hn (oursAt_mono I j (show s + 1 ≤ s' by omega) hmem)⟩, ho⟩
    by_contra hne
    have : I.opp (s + 1) z = true := by simpa using hne
    have := hI.opp_mono (show s + 1 ≤ s' + 1 by omega) this
    rw [ho] at this
    cases this
  · rintro ⟨⟨hb, -, hn⟩, ho⟩
    refine ⟨hb, ho, fun hmem => hn ?_⟩
    refine ours_eq_between I hlt hbetween hvisit hno j ?_ hmem
    rw [ht]
    exact mem_boardOf_iff.2 hb

/-- The opponent's spending over no time is zero. -/
theorem oppSpend_self (ar : Arena) (t : ℕ) : oppSpend I ar t t = 0 := by
  unfold oppSpend
  have : ar.board.filter (fun τ => I.opp t τ && !(I.opp t τ)) = ∅ := by
    refine filter_eq_empty_iff.2 fun τ _ => ?_
    cases I.opp t τ <;> simp
  rw [this]
  rfl

/-- The opponent's spending is additive over time. -/
theorem oppSpend_add (hI : I.Valid) (ar : Arena) {t₀ t₁ t₂ : ℕ} (h₀₁ : t₀ ≤ t₁) (h₁₂ : t₁ ≤ t₂) :
    oppSpend I ar t₀ t₂ = oppSpend I ar t₀ t₁ + oppSpend I ar t₁ t₂ := by
  unfold oppSpend cost
  rw [← sum_union]
  · refine sum_congr ?_ fun _ _ => rfl
    ext τ
    simp only [mem_filter, mem_union, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · rintro ⟨hb, h2, h0⟩
      cases h1 : I.opp t₁ τ
      · exact Or.inr ⟨hb, h2, rfl⟩
      · exact Or.inl ⟨hb, rfl, h0⟩
    · rintro (⟨hb, h1, h0⟩ | ⟨hb, h2, h1⟩)
      · exact ⟨hb, hI.opp_mono h₁₂ h1, h0⟩
      · refine ⟨hb, h2, ?_⟩
        by_contra hne
        have h0 : I.opp t₀ τ = true := by simpa using hne
        have := hI.opp_mono h₀₁ h0
        rw [h1] at this
        cases this
  · refine disjoint_left.2 fun τ h h' => ?_
    have h1 := (mem_filter.1 h).2
    have h2 := (mem_filter.1 h').2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1 h2
    rw [h1.1] at h2
    cases h2.2

/-- **Unanswered opponent moves between two stages** (`Wins.after_opponent` for the
construction). -/
theorem forces_after_stage {ar : Arena} {T : Finset (List Bool)} {A₀ : Finset Str}
    {a a' b t₀ t₁ : ℕ}
    (hA : ∀ τ ∈ A₀, τ ∈ ar.board ∧ I.opp t₀ τ = false)
    (h : ar.Forces T A₀ a b) (ha : a' + oppSpend I ar t₀ t₁ ≤ a) :
    ar.Forces T (A₀.filter fun τ => !(I.opp t₁ τ)) a' b := by
  classical
  set m := A₀.filter fun τ => I.opp t₁ τ = true with hm
  have hsub : m ⊆ ar.board.filter fun τ => I.opp t₁ τ && !(I.opp t₀ τ) := by
    intro τ hτ
    obtain ⟨hτ₀, hτ₁⟩ := mem_filter.1 hτ
    obtain ⟨hb, ho⟩ := hA τ hτ₀
    simp [hb, hτ₁, ho]
  have hcost : cost ar.w m ≤ oppSpend I ar t₀ t₁ := cost_mono ar.w hsub
  have hstep := Wins.after_opponent h (m := m) (filter_subset _ _) (by omega)
  have hset : A₀ \ m = A₀.filter fun τ => !(I.opp t₁ τ) := by
    ext τ
    simp only [hm, mem_sdiff, mem_filter, not_and, Bool.not_eq_true']
    constructor
    · rintro ⟨h₀, hn⟩
      refine ⟨h₀, ?_⟩
      cases h₁ : I.opp t₁ τ
      · rfl
      · exact absurd h₁ (hn h₀)
    · rintro ⟨h₀, h₁⟩
      exact ⟨h₀, fun _ => by rw [h₁]; simp⟩
  rw [hset] at hstep
  exact Wins.mono_budget hstep (by omega) le_rfl

/-! ### The answer of a strategy -/

/-- Every subset of the position is available as a move. -/
theorem exists_mem_moves (La : List Str) {p : Finset Str} (hp : p ⊆ La.toFinset) :
    p ∈ La.sublists.map List.toFinset := by
  classical
  refine List.mem_map.2 ⟨La.filter fun z => decide (z ∈ p), List.mem_sublists.2 List.filter_sublist,
      ?_⟩
  ext z
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.1 (hp h), h⟩⟩

/-- **The strategy.**  From a winning position, the answer keeps the position winning; if it is a
pass, the outcome is on target. -/
theorem respond_spec {ar : Arena} {g : BoardGame} {La : List Str} {a b : ℕ}
    (h : ar.Forces g.target La.toFinset a b) :
    (respond ar g La a b = ∅ ∧ ar.value La.toFinset ∈ g.target ∧
        ar.Forces g.target La.toFinset a b) ∨
      (respond ar g La a b ≠ ∅ ∧ ar.Forces g.target (La.toFinset \ respond ar g La a b) a
        (b - cost ar.w (respond ar g La a b))) := by
  unfold respond
  dsimp only
  set ok : Finset Str → Bool := fun p =>
      decide (cost ar.w p ≤ b) &&
        (if p = ∅ then decide (ar.value La.toFinset ∈ g.target) &&
            decide (ar.Forces g.target La.toFinset a b)
         else decide (ar.Forces g.target (La.toFinset \ p) a (b - cost ar.w p))) with hok
  have hex : ∃ p ∈ La.sublists.map List.toFinset, ok p = true := by
    obtain ⟨p, hp, hc, hcase⟩ := Wins.pass_response h
    refine ⟨p, exists_mem_moves La hp, ?_⟩
    simp only [hok, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hc, ?_⟩
    rcases hcase with ⟨rfl, hT⟩ | ⟨hp0, hw⟩
    · simp only [ite_true, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hT, h⟩
    · rw [ite_eq_right hp0]
      exact decide_eq_true hw
  cases hf : (La.sublists.map List.toFinset).find? ok with
  | none =>
    obtain ⟨p, hp, hpok⟩ := hex
    exact absurd hpok (by simpa using List.find?_eq_none.1 hf p hp)
  | some p =>
    simp only [Option.getD_some]
    have hpok := List.find?_some hf
    simp only [hok, Bool.and_eq_true, decide_eq_true_eq] at hpok
    obtain ⟨-, hif⟩ := hpok
    by_cases hp0 : p = ∅
    · subst hp0
      simp only [ite_true, Bool.and_eq_true, decide_eq_true_eq] at hif
      exact Or.inl ⟨rfl, hif.1, hif.2⟩
    · rw [ite_eq_right hp0] at hif
      exact Or.inr ⟨hp0, of_decide_eq_true hif⟩

/-! ### Verdicts -/

/-- Every set listed by `subsetsOf n` consists of vectors of length `n`. -/
theorem subset_of_mem_subsetsOf {n : ℕ} {S : Finset (List Bool)} (h : S ∈ subsetsOf n) :
    S ⊆ vectors n := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
  intro z hz
  have h1 := (List.mem_sublists.1 hl).subset (List.mem_toFinset.1 hz)
  exact List.mem_toFinset.2 h1

/-- Every board is listed in `allBoards`. -/
theorem mem_allBoards (j : Fin 3) : j ∈ allBoards := by
  fin_cases j <;> simp [allBoards]

/-- With no split at the top, winning sets are the same on all boards. -/
theorem forces_all_of_no_split {ar : Arena} {A : Fin 3 → Finset Str} {E : ℕ}
    (hsplit : ((allBoards.product allBoards).product (subsetsOf ar.tables.length)).find?
      (fun q => decide (q.1.1 ≠ q.1.2) && decide (ar.Forces q.2 (A q.1.1) E E) &&
        decide (ar.Forces (vectors ar.tables.length \ q.2) (A q.1.2) E E)) = none)
    {U : Finset (List Bool)} (hU : U ⊆ vectors ar.tables.length)
    (h0 : ar.Forces U (A 0) E E) (k : Fin 3) : ar.Forces U (A k) E E := by
  by_cases hk : k = 0
  · subst hk
    exact h0
  · rcases forces_or_compl (w := ar.w) (Arena.value_mem_vectors ar) U (A k) E with h' | h'
    · exact h'
    · exfalso
      have hmem : ((((0 : Fin 3), k), U) : (Fin 3 × Fin 3) × Finset (List Bool)) ∈
          (allBoards.product allBoards).product (subsetsOf ar.tables.length) :=
        List.pair_mem_product.2 ⟨List.pair_mem_product.2 ⟨mem_allBoards _, mem_allBoards _⟩,
          mem_subsetsOf hU⟩
      apply List.find?_eq_none.1 hsplit _ hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨fun hk0 => hk hk0.symm, h0⟩, h'⟩

/-- A split verdict. -/
theorem topOutcome_split_forces {ar : Arena} {A : Fin 3 → Finset Str} {E : ℕ} {j k : Fin 3}
    {S : Finset (List Bool)} (h : topOutcome ar A E = .split j k S) :
    j ≠ k ∧ ar.Forces S (A j) E E ∧ ar.Forces (vectors ar.tables.length \ S) (A k) E E := by
  unfold topOutcome at h
  dsimp only at h
  split at h
  · rename_i q hq
    cases h
    have hok := List.find?_some hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨hok.1.1, hok.1.2, hok.2⟩
  · split at h
    · cases h
    · split at h <;> cases h

/-- A failed intersection: the three games are winning on their boards. -/
theorem topOutcome_meet_forces {ar : Arena} {A : Fin 3 → Finset Str} {E : ℕ}
    {S T : Finset (List Bool)} (h : topOutcome ar A E = .meet S T) :
    ar.Forces S (A 0) E E ∧ ar.Forces T (A 1) E E ∧
      ar.Forces (vectors ar.tables.length \ (S ∩ T)) (A 2) E E := by
  unfold topOutcome at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hsplit
    split at h
    · rename_i q hq
      cases h
      have hok := List.find?_some hq
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not] at hok
      obtain ⟨⟨hS, hT⟩, hnot⟩ := hok
      have hmem := List.mem_of_find?_eq_some hq
      obtain ⟨hmS, hmT⟩ := List.pair_mem_product.1 (show (q.1, q.2) ∈ _ from hmem)
      refine ⟨hS, forces_all_of_no_split hsplit (subset_of_mem_subsetsOf hmT) hT 1,
        forces_all_of_no_split hsplit sdiff_subset ?_ 2⟩
      rcases forces_or_compl (w := ar.w) (Arena.value_mem_vectors ar) (q.1 ∩ q.2) (A 0) E with
        h' | h'
      · exact absurd h' hnot
      · exact h'
    · split at h <;> cases h

/-! ### The stack -/

/-- The first split of the stack: the level is at least one, and all earlier levels force `σ`. -/
theorem firstStackSplit_some {ar : Arena} {A : Fin 3 → Finset Str} {σ : List Bool}
    {ℓ : ℕ} {j : Fin 3} (h : firstStackSplit ar A σ = some (ℓ, j))
    (h0 : ∀ k, ar.Forces {σ} (A k) (levelBudget ar.tables 0) (levelBudget ar.tables 0)) :
    1 ≤ ℓ ∧ ar.Forces (vectors ar.tables.length \ {σ}) (A j) (levelBudget ar.tables ℓ)
        (levelBudget ar.tables ℓ) ∧
      ∀ k, ar.Forces {σ} (A k) (levelBudget ar.tables (ℓ - 1)) (levelBudget ar.tables (ℓ - 1)) := by
  unfold firstStackSplit at h
  dsimp only at h
  split at h
  · cases h
  · rename_i r hr
    obtain ⟨j', hj', heq⟩ := Option.map_eq_some_iff.1 h
    cases heq
    have hp := List.find?_some hj'
    refine ⟨by omega, of_decide_eq_true hp, fun k => ?_⟩
    simp only [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos r with rfl | hpos
    · exact h0 k
    · have hrng := List.find?_range_eq_some.1 hr
      have hprev := hrng.2.2 (r - 1) (by omega)
      have hk : decide (ar.Forces (vectors ar.tables.length \ {σ}) (A k)
          (levelBudget ar.tables (r - 1 + 1)) (levelBudget ar.tables (r - 1 + 1))) = false := by
        simp only [Bool.not_eq_true', List.any_eq_false] at hprev
        have := hprev k (mem_allBoards k)
        simpa using this
      rw [show r - 1 + 1 = r by omega] at hk
      rcases forces_or_compl (w := ar.w) (Arena.value_mem_vectors ar) {σ} (A k)
          (levelBudget ar.tables r) with h' | h'
      · exact h'
      · exact absurd (show ar.Forces _ _ _ _ from h') (of_decide_eq_false hk)

/-- No split in the stack: `σ` is winning at all levels on all boards. -/
theorem firstStackSplit_none {ar : Arena} {A : Fin 3 → Finset Str} {σ : List Bool}
    (h : firstStackSplit ar A σ = none) (k : Fin 3) {r : ℕ} (hr : r < maxLen ar.tables) :
    ar.Forces {σ} (A k) (levelBudget ar.tables (r + 1)) (levelBudget ar.tables (r + 1)) := by
  unfold firstStackSplit at h
  dsimp only at h
  have hnone : (List.range (maxLen ar.tables)).find? (fun r => allBoards.any fun j =>
      decide (ar.Forces (vectors ar.tables.length \ {σ}) (A j) (levelBudget ar.tables (r + 1))
        (levelBudget ar.tables (r + 1)))) = none := by
    cases hc : (List.range (maxLen ar.tables)).find? (fun r => allBoards.any fun j =>
      decide (ar.Forces (vectors ar.tables.length \ {σ}) (A j) (levelBudget ar.tables (r + 1))
        (levelBudget ar.tables (r + 1)))) with
    | none => rfl
    | some r' =>
      exfalso
      rw [hc] at h
      dsimp only at h
      have hp := List.find?_some hc
      obtain ⟨j, hj, hjp⟩ := List.any_eq_true.1 hp
      cases hf : allBoards.find? (fun j =>
        decide (ar.Forces (vectors ar.tables.length \ {σ}) (A j) (levelBudget ar.tables (r' + 1))
          (levelBudget ar.tables (r' + 1)))) with
      | none => exact absurd hjp (by simpa using List.find?_eq_none.1 hf j hj)
      | some j' =>
        rw [hf] at h
        cases h
  have hno := List.find?_eq_none.1 hnone r (List.mem_range.2 hr)
  rcases forces_or_compl (w := ar.w) (Arena.value_mem_vectors ar) {σ} (A k)
      (levelBudget ar.tables (r + 1)) with h' | h'
  · exact h'
  · exact absurd (List.any_eq_true.2 ⟨k, mem_allBoards k,
      decide_eq_true (show ar.Forces _ _ _ _ from h')⟩) hno

/-! ### Boards of the games -/

/-- `otherBoard j` is a board other than `j`. -/
theorem otherBoard_ne (j : Fin 3) : otherBoard j ≠ j := by
  fin_cases j <;> decide

/-- For distinct boards `j` and `k`, `thirdBoard j k` is the remaining board: it differs from both,
and any board different from it is `j` or `k`. -/
theorem thirdBoard_spec (j k : Fin 3) (h : k ≠ j) :
    thirdBoard j k ≠ j ∧ thirdBoard j k ≠ k ∧ ∀ l, l ≠ thirdBoard j k → l = j ∨ l = k := by
  revert j k
  decide

/-- The limit of the opponent's spending in a play bounds the budgets of the games. -/
theorem foldr_min_le {g : BoardGame} {l : List BoardGame} {E : ℕ} (hg : g ∈ l) :
    l.foldr (fun g n => min g.oppLimit n) E ≤ g.oppLimit := by
  induction l with
  | nil => simp at hg
  | cons a l ih =>
    rcases List.mem_cons.1 hg with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

end Kolmogorov.RandomStrings.TTMeet
