/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.BoundedSolver

/-!
# Determinacy of the finite counter game and exchange of the two roles

This module finishes the study of the finite counter game
(blueprint nodes `constr:determinacy` and `constr:flip`).

* `finite_counter_game_computable_winner`: the explicit solver `solveCounterGameCode` is
  computable, and the positional strategy extracted from it wins for the player that the solver
  names as winner, along every play that respects the strategy.
* `FiniteCounterGame.exchangeRoles` swaps the names of the equality and inequality players while
  keeping the counters and the virtual target; `counter_game_role_exchange` shows that this
  preserves legal moves and strategy choices and complements the winner.
* `FiniteCounterGame.controlWinningPlayer` uses the exchange to make player `false` (the
  constructor) the winner, and `FiniteCounterGame.flippedTarget` is the real target for which the
  winning objective of that player is refuted (`symmetric_game_target_flip`).
* `dummyAnswer` and `fresh_dummy_target_flip` express that one new description of a string outside
  the query tree of the referee leaves the referee output unchanged, so the equality
  objective fails for the incremented target.

These facts are used by the construction modules to choose the game that the constructor controls
and to make the real target differ from the winner's equality goal.
-/

namespace Kolmogorov.Milovanov

/-- The first legal vector of the move box after which the solver declares the active player the
winner; `none` if there is no such vector. -/
private def FiniteCounterGame.selectedMove (game : FiniteCounterGame)
    (position : CounterPosition game) : Option CounterMove :=
  (counterMoveBox game.budget game.coordinates.length).find? (fun move ↦
    if _hmove : game.LegalMove position move then
      (game.solve (game.afterMove position move)).1 == game.activePlayer position
    else false)

private lemma FiniteCounterGame.solve_eq_selectedMove (game : FiniteCounterGame)
    (position : CounterPosition game) :
    game.solve position = match game.selectedMove position with
      | some move => (game.activePlayer position, some move)
      | none => (!game.activePlayer position, none) := by
  rw [FiniteCounterGame.solve]
  rfl

private lemma FiniteCounterGame.strategy_eq_selectedMove (game : FiniteCounterGame)
    (position : CounterPosition game) :
    game.strategy position = game.selectedMove position := by
  rw [FiniteCounterGame.strategy, solve_eq_selectedMove]
  cases game.selectedMove position <;> rfl

private lemma FiniteCounterGame.winner_eq_activePlayer_iff (game : FiniteCounterGame)
    (position : CounterPosition game) :
    game.winner position = game.activePlayer position ↔ game.strategy position ≠ none := by
  rw [FiniteCounterGame.winner, strategy_eq_selectedMove, solve_eq_selectedMove]
  cases game.selectedMove position <;> simp

/-- A selected successor is legal and wins for the active player. -/
private lemma FiniteCounterGame.legalMove_of_strategy_eq_some (game : FiniteCounterGame)
    (position : CounterPosition game) (move : CounterMove)
    (h : game.strategy position = some move) :
    game.LegalMove position move ∧
      game.winner (game.afterMove position move) = game.activePlayer position := by
  rw [strategy_eq_selectedMove] at h
  have hpred := List.find?_some h
  split at hpred
  · next hmove => exact ⟨hmove, eq_of_beq hpred⟩
  · exact absurd hpred Bool.false_ne_true

/-- If no successor is selected, no legal successor wins for the active player. -/
private lemma FiniteCounterGame.winner_ne_activePlayer_of_strategy_eq_none
    (game : FiniteCounterGame) (position : CounterPosition game)
    (h : game.strategy position = none) (move : CounterMove)
    (hmove : game.LegalMove position move) :
    game.winner (game.afterMove position move) ≠ game.activePlayer position := by
  rw [strategy_eq_selectedMove] at h
  have hpred := List.find?_eq_none.mp h move (legal_move_mem_box game position move hmove)
  simp only [hmove, dite_true, beq_iff_eq] at hpred
  exact hpred

/-- The solver's winner does not change along plays in which the controlled player follows the
solver's strategy. -/
private lemma FiniteCounterGame.winner_eq_of_reflTransGen_strategyStep (game : FiniteCounterGame)
    (player : Bool) (initial position : CounterPosition game)
    (hwin : game.winner initial = player)
    (hpath : Relation.ReflTransGen (game.StrategyStep player game.strategy) initial position) :
    game.winner position = player := by
  have hbool : ∀ a p w : Bool, a ≠ p → w ≠ a → w = p := by decide
  induction hpath with
  | refl => exact hwin
  | @tail b c _ hbc ih =>
    obtain ⟨move, hlegal, hnext, hstrategy⟩ := hbc
    subst hnext
    by_cases hactive : game.activePlayer b = player
    · rw [(game.legalMove_of_strategy_eq_some b move (hstrategy hactive)).2, hactive]
    · have hnone : game.strategy b = none := by
        by_contra hne
        have hw := (game.winner_eq_activePlayer_iff b).mpr hne
        exact hactive (hw.symm.trans ih)
      exact hbool _ _ _ hactive
        (game.winner_ne_activePlayer_of_strategy_eq_none b hnone move hlegal)

/-- The explicit solver is computable and its positional strategy wins for its returned player.
Blueprint node `constr:determinacy`. Computability is uniform in all finite game data
and the current position; it therefore computes strategy responses after every opponent move. -/
theorem finite_counter_game_computable_winner : Computable solveCounterGameCode ∧
    ∀ (game : FiniteCounterGame) (position : CounterPosition game),
      game.StrategyWins (game.winner position) game.strategy position := by
  refine ⟨computable_solveCounterGameCode, ?_⟩
  intro game initial pos hpath
  have hwin : game.winner pos = game.winner initial :=
    game.winner_eq_of_reflTransGen_strategyStep _ initial pos rfl hpath
  have hbool : ∀ a w : Bool, w = a → w ≠ a → False := by decide
  refine ⟨fun hterm ↦ ?_, fun hactive hnotterm ↦ ?_⟩
  · have hnone : game.strategy pos = none := by
      by_contra hne
      obtain ⟨move, hmove⟩ := Option.ne_none_iff_exists'.mp hne
      exact hterm move (game.legalMove_of_strategy_eq_some pos move hmove).1
    have hactive : game.activePlayer pos ≠ game.winner initial := fun heq ↦
      (game.winner_eq_activePlayer_iff pos).not.mpr (not_not.mpr hnone) (hwin.trans heq.symm)
    have hnot : game.winner initial = !game.activePlayer pos := by
      revert hactive; cases game.activePlayer pos <;> cases game.winner initial <;> decide
    rw [hnot]
    exact (counter_game_active_objectives game pos).2
  · have hselected : game.strategy pos ≠ none :=
      (game.winner_eq_activePlayer_iff pos).mp (hwin.trans hactive.symm)
    obtain ⟨move, hmove⟩ := Option.ne_none_iff_exists'.mp hselected
    exact ⟨move, hmove, (game.legalMove_of_strategy_eq_some pos move hmove).1⟩

/-- Exchange player names and objectives without changing the virtual target or counter rules.
Blueprint node `constr:flip`. -/
def FiniteCounterGame.exchangeRoles (game : FiniteCounterGame) : FiniteCounterGame :=
  { game with equalityPlayer := !game.equalityPlayer }

/-- Exchange the two remaining budgets when the player names are exchanged. -/
def CounterPosition.exchangeRoles {game : FiniteCounterGame} (position : CounterPosition game) :
    CounterPosition game.exchangeRoles :=
  ⟨position.counters, position.rightBudget, position.leftBudget,
    position.right_le, position.left_le⟩

private theorem counter_game_role_exchange_activePlayer (game : FiniteCounterGame)
    (position : CounterPosition game) :
    game.exchangeRoles.activePlayer position.exchangeRoles = !game.activePlayer position := by
  dsimp only [FiniteCounterGame.activePlayer]
  have hout : game.exchangeRoles.output position.exchangeRoles = game.output position := rfl
  have htarget : game.exchangeRoles.target = game.target := rfl
  have hplayer : game.exchangeRoles.equalityPlayer = !game.equalityPlayer := rfl
  rw [hout, htarget, hplayer]
  split_ifs <;> simp

private theorem counter_game_role_exchange_remaining (game : FiniteCounterGame)
    (position : CounterPosition game) (player : Bool) :
    position.exchangeRoles.remaining player = position.remaining (!player) := by
  cases player <;> rfl

private theorem counter_game_role_exchange_objective (game : FiniteCounterGame)
    (player : Bool) (out : ℕ) :
    game.exchangeRoles.objective player out = game.objective (!player) out := by
  dsimp [FiniteCounterGame.objective, FiniteCounterGame.exchangeRoles]
  cases player <;> simp

private theorem counter_game_role_exchange_LegalMove (game : FiniteCounterGame)
    (position : CounterPosition game) (move : CounterMove) :
    game.exchangeRoles.LegalMove position.exchangeRoles move ↔
      game.LegalMove position move := by
  dsimp [FiniteCounterGame.LegalMove]
  rw [counter_game_role_exchange_activePlayer, counter_game_role_exchange_remaining,
    counter_game_role_exchange_objective]
  simp only [Bool.not_not]
  rfl

private theorem counter_game_role_exchange_afterMove (game : FiniteCounterGame)
    (position : CounterPosition game) (move : CounterMove) :
    game.exchangeRoles.afterMove position.exchangeRoles move =
      (game.afterMove position move).exchangeRoles := by
  have hactive := counter_game_role_exchange_activePlayer game position
  dsimp [FiniteCounterGame.afterMove, CounterPosition.exchangeRoles]
  congr 1
  · dsimp [CounterPosition.exchangeRoles] at hactive
    rw [hactive]
    cases game.activePlayer position <;> rfl
  · dsimp [CounterPosition.exchangeRoles] at hactive
    rw [hactive]
    cases game.activePlayer position <;> rfl

/-- Induction on remaining budget preserves the first winning move and complements its winner. -/
private theorem counter_game_role_exchange_solve (game : FiniteCounterGame)
    (position : CounterPosition game) :
    game.exchangeRoles.solve position.exchangeRoles =
      (!(game.solve position).1, (game.solve position).2) := by
  induction hsum : position.budgetSum using Nat.strong_induction_on generalizing position with
  | h total ih =>
    have hselected :
        (counterMoveBox game.exchangeRoles.budget game.exchangeRoles.coordinates.length).find?
          (fun move => if _hmove : game.exchangeRoles.LegalMove position.exchangeRoles move then
            (game.exchangeRoles.solve
              (game.exchangeRoles.afterMove position.exchangeRoles move)).1 ==
                game.exchangeRoles.activePlayer position.exchangeRoles
            else false) =
        (counterMoveBox game.budget game.coordinates.length).find?
          (fun move => if _hmove : game.LegalMove position move then
            (game.solve (game.afterMove position move)).1 == game.activePlayer position
            else false) := by
      change (counterMoveBox game.budget game.coordinates.length).find? _ = _
      apply List.find?_congr
      intro move _
      by_cases hmove : game.LegalMove position move
      · have hexchanged := (counter_game_role_exchange_LegalMove game position move).mpr hmove
        have hless : (game.afterMove position move).budgetSum < total := by
          rw [← hsum]
          exact counter_move_decreases_budget game position move hmove
        have hchild := ih _ hless (game.afterMove position move) rfl
        simp only [dite_eq_left hexchanged, dite_eq_left hmove,
          counter_game_role_exchange_afterMove, hchild,
          counter_game_role_exchange_activePlayer]
        cases (game.solve (game.afterMove position move)).1 <;>
          cases game.activePlayer position <;> rfl
      · have hexchanged : ¬ game.exchangeRoles.LegalMove position.exchangeRoles move :=
          fun h => hmove ((counter_game_role_exchange_LegalMove game position move).mp h)
        simp only [dite_eq_right hexchanged, dite_eq_right hmove]
    rw [FiniteCounterGame.solve.eq_1 game.exchangeRoles position.exchangeRoles,
      FiniteCounterGame.solve.eq_1 game position]
    rw [hselected, counter_game_role_exchange_activePlayer]
    split <;> rfl

/-- Symmetry preserves legal vectors and strategy choices, and exchanges the winner's name.
Blueprint node `constr:flip`. Counters, numeric output, and the virtual target stay fixed. -/
theorem counter_game_role_exchange (game : FiniteCounterGame)
    (position : CounterPosition game) :
    game.exchangeRoles.output position.exchangeRoles = game.output position ∧
    game.exchangeRoles.activePlayer position.exchangeRoles = !game.activePlayer position ∧
    (∀ move, game.exchangeRoles.LegalMove position.exchangeRoles move ↔
      game.LegalMove position move) ∧
    game.exchangeRoles.winner position.exchangeRoles = !game.winner position ∧
    game.exchangeRoles.strategy position.exchangeRoles = game.strategy position := by
  refine ⟨rfl, counter_game_role_exchange_activePlayer game position,
    counter_game_role_exchange_LegalMove game position, ?_, ?_⟩
  · simpa only [FiniteCounterGame.winner] using
      congrArg Prod.fst (counter_game_role_exchange_solve game position)
  · simpa only [FiniteCounterGame.strategy] using
      congrArg Prod.snd (counter_game_role_exchange_solve game position)

/-- Assign the winning objective to the constructor, named player `false`.
Blueprint node `constr:flip`. The common initial budget permits either role assignment. -/
def FiniteCounterGame.controlWinningPlayer (game : FiniteCounterGame) : FiniteCounterGame :=
  if game.winner game.initialPosition then game.exchangeRoles else game

/-- The prospective real target: add one precisely when the original winner seeks equality.
This is a numeric choice, not a claim about actual stage counts or true-marker exactness. -/
def FiniteCounterGame.flippedTarget (game : FiniteCounterGame) : ℕ :=
  game.target + if game.winner game.initialPosition = game.equalityPlayer then 1 else 0

private lemma controlWinningPlayer_of_winner_eq_false (game : FiniteCounterGame)
    (h : game.winner game.initialPosition = false) : game.controlWinningPlayer = game := by
  simp [FiniteCounterGame.controlWinningPlayer, h]

private lemma controlWinningPlayer_of_winner_eq_true (game : FiniteCounterGame)
    (h : game.winner game.initialPosition = true) :
    game.controlWinningPlayer = game.exchangeRoles := by
  simp [FiniteCounterGame.controlWinningPlayer, h]

/-- The constructor can control a winner, whose objective contradicts the chosen real target.
Blueprint node `constr:flip`. The virtual target remains the original `K`. -/
theorem symmetric_game_target_flip (game : FiniteCounterGame) :
    game.controlWinningPlayer.winner game.controlWinningPlayer.initialPosition = false ∧
    game.controlWinningPlayer.target = game.target ∧
    ∀ out, game.controlWinningPlayer.objective false out = true →
      out ≠ game.flippedTarget := by
  have hexchanged : game.exchangeRoles.winner game.exchangeRoles.initialPosition =
      !game.winner game.initialPosition :=
    (counter_game_role_exchange game game.initialPosition).2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · cases h : game.winner game.initialPosition
    · rw [controlWinningPlayer_of_winner_eq_false game h]
      exact h
    · rw [controlWinningPlayer_of_winner_eq_true game h, hexchanged]
      exact congrArg not h
  · unfold FiniteCounterGame.controlWinningPlayer
    split_ifs <;> rfl
  · intro out hobj
    cases h : game.winner game.initialPosition
    · rw [controlWinningPlayer_of_winner_eq_false game h] at hobj
      cases hp : game.equalityPlayer <;>
        simp only [FiniteCounterGame.objective, FiniteCounterGame.flippedTarget, h, hp,
          ↓reduceIte, Bool.false_eq_true, decide_eq_true_eq, ne_eq, add_zero] at hobj ⊢ <;>
        omega
    · rw [controlWinningPlayer_of_winner_eq_true game h] at hobj
      cases hp : game.equalityPlayer <;>
        simp only [FiniteCounterGame.objective, FiniteCounterGame.exchangeRoles,
          FiniteCounterGame.flippedTarget, h, hp, ↓reduceIte, Bool.false_eq_true,
          Bool.true_eq_false, Bool.not_true, Bool.not_false, decide_eq_true_eq, ne_eq,
          add_zero] at hobj ⊢ <;>
        omega

/-- Add the oracle consequences of one new description of `dummy` at threshold `m`. -/
def dummyAnswer (m : ℕ) (dummy : BitString) (answer : Coordinate → Bool)
    (query : Coordinate) : Bool :=
  decide (query.1 = dummy ∧ m ≤ query.2) || answer query

/-- A dummy outside the entire tree preserves every run; equality to `K` then misses `K + 1`.
Blueprint node `constr:flip`. The actual count being exactly `K + 1` is a later marker lemma,
not a conclusion about arbitrary false-candidate phases. -/
theorem fresh_dummy_target_flip (tree : QueryTree) (m K : ℕ) (dummy : BitString)
    (hfresh : ∀ query ∈ tree.queries, query.1 ≠ dummy) (answer : Coordinate → Bool) :
    tree.eval (dummyAnswer m dummy answer) = tree.eval answer ∧
    (tree.eval answer = K → tree.eval (dummyAnswer m dummy answer) ≠ K + 1) := by
  have houtput : tree.eval (dummyAnswer m dummy answer) = tree.eval answer := by
    apply QueryTree.eval_eq_of_agree
    intro query hquery
    simp [dummyAnswer, hfresh query hquery]
  refine ⟨houtput, ?_⟩
  intro htarget
  rw [houtput, htarget]
  omega

end Kolmogorov.Milovanov
