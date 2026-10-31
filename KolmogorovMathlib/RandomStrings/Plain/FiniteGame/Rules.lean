/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Referees

/-!
# Finite counter games

This module defines the finite counter game of blueprint node `constr:game`: the referee's
answers, complementary player objectives, legal moves, and budget updates. Every legal move
switches the active player and strictly decreases the sum of the remaining budgets.

For blueprint node `constr:determinacy`, we enumerate a finite box containing every legal move
and define a winner and strategy by recursion on the remaining budget. Primitive encodings
connect this solver to the computability proofs in `LegalMoves` and `BoundedSolver`; the
strategy specification is used by `RoleExchange` to establish the finite-play winning property.
-/

namespace Kolmogorov.Milovanov

/-- A finite counter game with complementary equality and inequality objectives.
Blueprint node `constr:game`. `false` and `true` name the two players.
The referee supplied at phase initialization is already normalized. -/
structure FiniteCounterGame where
  /-- A finite presentation of the coordinate set; first occurrences fix the vector order. -/
  coordinateTable : List Coordinate
  /-- Prices in the deduplicated coordinate order, with default zero. -/
  prices : List ℕ
  /-- Initial counters in that same order, with default zero. -/
  initialCounters : List ℕ
  /-- The finite table of queries initially answered yes. -/
  initialYes : List Coordinate
  /-- The common initial budget of both players. -/
  budget : ℕ
  /-- The preprocessed finite referee, including its natural outputs. -/
  referee : QueryTree
  /-- The fixed virtual target, never changed during play or role exchange. -/
  target : ℕ
  /-- The player seeking equality; the other seeks inequality. -/
  equalityPlayer : Bool

/-- Initialize the standard naming: player `false` seeks inequality, `true` equality.
Blueprint node `constr:game`. All tables are explicit finite data. -/
def finite_counter_game (coordinates : List Coordinate) (prices counters : List ℕ)
    (initialYes : List Coordinate) (R : ℕ) (referee : QueryTree) (K : ℕ) :
    FiniteCounterGame :=
  ⟨coordinates, prices, counters, initialYes, R, referee, K, true⟩

/-- The canonical order of the finite coordinate vector. -/
def FiniteCounterGame.coordinates (game : FiniteCounterGame) : List Coordinate :=
  game.coordinateTable.eraseDups

/-- The actual finite coordinate set `J`, independent of duplicate table entries. -/
def FiniteCounterGame.J (game : FiniteCounterGame) : Finset Coordinate :=
  game.coordinateTable.toFinset

/-- A move vector encoded as a list in the game's coordinate order. -/
abbrev CounterMove := List ℕ

/-- Counters and two remaining budgets, each bounded by the common initial budget.
Blueprint node `constr:game`. Missing counter entries are zero. -/
structure CounterPosition (game : FiniteCounterGame) where
  /-- Current counter values in coordinate order. -/
  counters : List ℕ
  /-- Remaining budget for player `false`. -/
  leftBudget : ℕ
  /-- Remaining budget for player `true`. -/
  rightBudget : ℕ
  /-- The first player's budget never exceeds its initial allocation. -/
  left_le : leftBudget ≤ game.budget
  /-- The second player's budget never exceeds its initial allocation. -/
  right_le : rightBudget ≤ game.budget

/-- Initial counters and equal budgets. -/
def FiniteCounterGame.initialPosition (game : FiniteCounterGame) : CounterPosition game :=
  ⟨game.initialCounters, game.budget, game.budget, le_rfl, le_rfl⟩

/-- The sum of remaining budgets, which strictly decreases on every legal move. -/
def CounterPosition.budgetSum {game : FiniteCounterGame} (position : CounterPosition game) : ℕ :=
  position.leftBudget + position.rightBudget

/-- Read the named player's remaining budget. -/
def CounterPosition.remaining {game : FiniteCounterGame} (position : CounterPosition game)
    (player : Bool) : ℕ :=
  if player then position.rightBudget else position.leftBudget

/-- Interpret a finite table as a function on coordinates, with zero outside its support. -/
def FiniteCounterGame.coordinateValue (game : FiniteCounterGame) (values : List ℕ)
    (query : Coordinate) : ℕ :=
  if query ∈ game.coordinates then values[game.coordinates.idxOf query]?.getD 0 else 0

/-- The price function on coordinates, represented by the game's finite price table. -/
def FiniteCounterGame.price (game : FiniteCounterGame) : Coordinate → ℕ :=
  game.coordinateValue game.prices

/-- A query is true initially or is covered by a retained coordinate reaching its price.
Blueprint node `constr:game`. Zero prices are active even at zero counters. -/
def FiniteCounterGame.counterAnswer (game : FiniteCounterGame) (counters : List ℕ)
    (query : Coordinate) : Bool :=
  decide (query ∈ game.initialYes) || game.coordinates.any (fun retained ↦
    decide (retained.1 = query.1 ∧ retained.2 ≤ query.2 ∧
      game.price retained ≤ game.coordinateValue counters retained))

/-- The finite counter rule is exactly upward closure of retained coordinates reaching price.
Blueprint node `constr:game`. The threshold comparison includes equality. -/
theorem counter_answer_eq_true (game : FiniteCounterGame) (counters : List ℕ)
    (query : Coordinate) : game.counterAnswer counters query = true ↔
      query ∈ game.initialYes ∨ ∃ retained ∈ game.J,
        retained.1 = query.1 ∧ retained.2 ≤ query.2 ∧
        game.price retained ≤ game.coordinateValue counters retained := by
  simp [FiniteCounterGame.counterAnswer, FiniteCounterGame.J,
    FiniteCounterGame.coordinates, List.any_eq_true]

/-- The referee's numeric output at the current counter position. -/
def FiniteCounterGame.output (game : FiniteCounterGame) (position : CounterPosition game) : ℕ :=
  game.referee.eval (game.counterAnswer position.counters)

/-- The complementary output predicates, parameterized by the role assignment.
Blueprint node `constr:game`. Only equality or inequality to the frozen target matters. -/
def FiniteCounterGame.objective (game : FiniteCounterGame) (player : Bool) (out : ℕ) : Bool :=
  if player = game.equalityPlayer then decide (out = game.target)
  else decide (out ≠ game.target)

/-- The unique player whose objective currently fails. -/
def FiniteCounterGame.activePlayer (game : FiniteCounterGame)
    (position : CounterPosition game) : Bool :=
  if game.output position = game.target then !game.equalityPlayer else game.equalityPlayer

/-- Exactly the active player's predicate fails; the inactive player's predicate holds. -/
theorem counter_game_active_objectives (game : FiniteCounterGame)
    (position : CounterPosition game) :
    game.objective (game.activePlayer position) (game.output position) = false ∧
    game.objective (!game.activePlayer position) (game.output position) = true := by
  cases hplayer : game.equalityPlayer <;>
    by_cases hout : game.output position = game.target <;>
    simp [FiniteCounterGame.activePlayer, FiniteCounterGame.objective, hplayer, hout]

/-- Add a finite vector coordinatewise, ignoring nonexistent coordinates. -/
def FiniteCounterGame.addCounters (game : FiniteCounterGame) (counters : List ℕ)
    (move : CounterMove) : List ℕ :=
  (List.range game.coordinates.length).map (fun i ↦
    counters[i]?.getD 0 + move[i]?.getD 0)

/-- Positive affordable vectors which make the active player's predicate true.
Blueprint node `constr:game`. Changing one unequal output to another is insufficient. -/
def FiniteCounterGame.LegalMove (game : FiniteCounterGame) (position : CounterPosition game)
    (move : CounterMove) : Prop :=
  move.length = game.coordinates.length ∧ 0 < move.sum ∧
    move.sum ≤ position.remaining (game.activePlayer position) ∧
    game.objective (game.activePlayer position)
      (game.referee.eval (game.counterAnswer (game.addCounters position.counters move))) = true

/-- Legality is a decidable finite calculation. -/
instance (game : FiniteCounterGame) (position : CounterPosition game) (move : CounterMove) :
    Decidable (game.LegalMove position move) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Apply a vector and charge only the currently active player.
Unaffordable inputs are totalized by natural subtraction; only legal moves enter play. -/
def FiniteCounterGame.afterMove (game : FiniteCounterGame) (position : CounterPosition game)
    (move : CounterMove) : CounterPosition game where
  counters := game.addCounters position.counters move
  leftBudget := position.leftBudget - if game.activePlayer position then 0 else move.sum
  rightBudget := position.rightBudget - if game.activePlayer position then move.sum else 0
  left_le := (Nat.sub_le _ _).trans position.left_le
  right_le := (Nat.sub_le _ _).trans position.right_le

/-- Every legal move switches the active player, because it changes which predicate holds. -/
theorem legal_counter_move_switches_player (game : FiniteCounterGame)
    (position : CounterPosition game) (move : CounterMove)
    (hmove : game.LegalMove position move) :
    game.activePlayer (game.afterMove position move) = !game.activePlayer position := by
  have hsuccess := hmove.2.2.2
  change game.objective (game.activePlayer position)
    (game.output (game.afterMove position move)) = true at hsuccess
  cases hplayer : game.equalityPlayer <;>
    by_cases hout : game.output position = game.target <;>
    by_cases hnext : game.output (game.afterMove position move) = game.target <;>
    simp_all [FiniteCounterGame.objective, FiniteCounterGame.activePlayer]

/-- A legal move spends a positive amount and strictly decreases the recursion measure. -/
theorem counter_move_decreases_budget (game : FiniteCounterGame)
    (position : CounterPosition game) (move : CounterMove)
    (hmove : game.LegalMove position move) :
    (game.afterMove position move).budgetSum < position.budgetSum := by
  have hpos := hmove.2.1
  have hbudget := hmove.2.2.1
  cases hactive : game.activePlayer position <;>
    simp only [CounterPosition.remaining, hactive, Bool.false_eq_true,
      ite_false, ite_true] at hbudget <;>
    simp only [FiniteCounterGame.afterMove, CounterPosition.budgetSum, hactive,
      Bool.false_eq_true, ite_false, ite_true, Nat.sub_zero] <;> omega

/-- Enumerate the whole finite box `{0,...,R}^size` in a fixed lexicographic order. -/
def counterMoveBox (R : ℕ) : ℕ → List CounterMove
  | 0 => [[]]
  | size + 1 => (List.range (R + 1)).flatMap (fun value ↦
      (counterMoveBox R size).map (fun tail ↦ value :: tail))

private lemma mem_counter_move_box_iff (R : ℕ) (size : ℕ) (move : List ℕ) :
    move ∈ counterMoveBox R size ↔ move.length = size ∧ ∀ x ∈ move, x ≤ R := by
  induction size generalizing move with
  | zero => cases move <;> simp [counterMoveBox]
  | succ size ih =>
    cases move with
    | nil => simp [counterMoveBox]
    | cons value tail =>
      simp [counterMoveBox, ih, and_assoc, and_left_comm]

/-- The box contains every legal move, including at positions reached after role exchange. -/
theorem legal_move_mem_box (game : FiniteCounterGame) (position : CounterPosition game)
    (move : CounterMove) (hmove : game.LegalMove position move) :
    move ∈ counterMoveBox game.budget game.coordinates.length := by
  apply (mem_counter_move_box_iff game.budget game.coordinates.length move).mpr
  constructor
  · exact hmove.1
  · intro x hx
    have h1 : x ≤ move.sum := List.single_le_sum (fun _ _ ↦ Nat.zero_le _) x hx
    have h2 : move.sum ≤ position.remaining (game.activePlayer position) := hmove.2.2.1
    have h3 : position.remaining (game.activePlayer position) ≤ game.budget := by
      dsimp [CounterPosition.remaining]
      split
      · exact position.right_le
      · exact position.left_le
    omega

/-- Compute the winner and the first winning move, recursing on total remaining budget.
Blueprint node `constr:determinacy`. If no winning move exists, the inactive player wins
and the selector returns `none`. In particular this is the terminal-state rule. -/
def FiniteCounterGame.solve (game : FiniteCounterGame) (position : CounterPosition game) :
    Bool × Option CounterMove :=
  let active := game.activePlayer position
  let selected := (counterMoveBox game.budget game.coordinates.length).find? (fun move ↦
    if _hmove : game.LegalMove position move then
      (game.solve (game.afterMove position move)).1 == active
    else false)
  match selected with
  | some move => (active, some move)
  | none => (!active, none)
termination_by position.budgetSum
decreasing_by exact counter_move_decreases_budget game position move _hmove

/-- The winner returned by the explicit decreasing-budget recursion. -/
def FiniteCounterGame.winner (game : FiniteCounterGame) (position : CounterPosition game) : Bool :=
  (game.solve position).1

/-- A winning position for the named player, as decided by the finite recursion. -/
def FiniteCounterGame.WinningPosition (game : FiniteCounterGame) (player : Bool)
    (position : CounterPosition game) : Prop := game.winner position = player

/-- The explicit positional strategy; it acts exactly when the active player can win. -/
def FiniteCounterGame.strategy (game : FiniteCounterGame) (position : CounterPosition game) :
    Option CounterMove := (game.solve position).2

/-- A terminal position has no positive affordable move satisfying the active objective. -/
def FiniteCounterGame.Terminal (game : FiniteCounterGame) (position : CounterPosition game) :
    Prop := ∀ move, ¬ game.LegalMove position move

/-- A legal transition where the controlled player follows the supplied strategy. -/
def FiniteCounterGame.StrategyStep (game : FiniteCounterGame) (player : Bool)
    (strategy : CounterPosition game → Option CounterMove)
    (position next : CounterPosition game) : Prop :=
  ∃ move, game.LegalMove position move ∧ next = game.afterMove position move ∧
    (game.activePlayer position = player → strategy position = some move)

/-- A strategy always supplies a legal move on its turn and wins every reachable terminal play.
Together with strict budget descent, this is the finite-play winning-strategy specification. -/
def FiniteCounterGame.StrategyWins (game : FiniteCounterGame) (player : Bool)
    (strategy : CounterPosition game → Option CounterMove)
    (initial : CounterPosition game) : Prop :=
  ∀ position, Relation.ReflTransGen (game.StrategyStep player strategy) initial position →
    (game.Terminal position → game.objective player (game.output position) = true) ∧
    (game.activePlayer position = player → ¬ game.Terminal position →
      ∃ move, strategy position = some move ∧ game.LegalMove position move)

/-- Primitive finite-data encoding of a complete game, including its referee program. -/
abbrev CounterGameCode := List Coordinate × List ℕ × List ℕ × List Coordinate ×
  ℕ × QueryTree.Code × ℕ × Bool

/-- Primitive finite-data encoding of counters and both remaining budgets. -/
abbrev CounterPositionCode := List ℕ × ℕ × ℕ

/-- Serialize the entire finite game, preserving all supplied tables. -/
def FiniteCounterGame.encode (game : FiniteCounterGame) : CounterGameCode :=
  (game.coordinateTable, game.prices, game.initialCounters, game.initialYes,
    game.budget, game.referee.encode, game.target, game.equalityPlayer)

/-- Decode finite game data; an invalid referee code denotes the constant-zero tree. -/
def decodeCounterGame (code : CounterGameCode) : FiniteCounterGame :=
  ⟨code.1, code.2.1, code.2.2.1, code.2.2.2.1, code.2.2.2.2.1,
    (QueryTree.decode code.2.2.2.2.2.1).getD (.leaf 0),
    code.2.2.2.2.2.2.1, code.2.2.2.2.2.2.2⟩

/-- Serialize a game position, omitting the proof of the remaining-budget bounds. -/
def CounterPosition.encode {game : FiniteCounterGame} (position : CounterPosition game) :
    CounterPositionCode := (position.counters, position.leftBudget, position.rightBudget)

/-- Decode a position, clamping malformed oversized budgets to the game's common budget. -/
def decodeCounterPosition (game : FiniteCounterGame) (code : CounterPositionCode) :
    CounterPosition game :=
  ⟨code.1, min code.2.1 game.budget, min code.2.2 game.budget,
    min_le_right _ _, min_le_right _ _⟩

/-- Game data round-trip through primitive codes without changing the referee or objectives. -/
theorem decode_encode_counter_game (game : FiniteCounterGame) :
    decodeCounterGame game.encode = game := by
  cases game
  simp [decodeCounterGame, FiniteCounterGame.encode, QueryTree.decode_encode]

/-- Valid positions round-trip exactly; clamping only affects malformed encoded budgets. -/
theorem decode_encode_counter_position (game : FiniteCounterGame)
    (position : CounterPosition game) : decodeCounterPosition game position.encode = position := by
  cases position with
  | mk counters left right hl hr =>
    simp [decodeCounterPosition, CounterPosition.encode, min_eq_left hl, min_eq_left hr]

/-- The solver on primitive encoded inputs, returning a winner and an optional vector.
Blueprint node `constr:determinacy`. This is the same recursion as the semantic game solver. -/
def solveCounterGameCode (input : CounterGameCode × CounterPositionCode) :
    Bool × Option CounterMove :=
  let game := decodeCounterGame input.1
  game.solve (decodeCounterPosition game input.2)

/-- Encoded computation agrees with the solver at every valid finite position. -/
theorem solve_counter_game_code_agrees (game : FiniteCounterGame)
    (position : CounterPosition game) :
    solveCounterGameCode (game.encode, position.encode) = game.solve position := by
  dsimp only [solveCounterGameCode]
  rw [decode_encode_counter_game, decode_encode_counter_position]


private lemma primrec_counter_move_box : Primrec₂ counterMoveBox := by
  have hrange : Primrec (fun x : ℕ × (ℕ × List CounterMove) ↦ List.range (x.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
  have htails : Primrec (fun x : (ℕ × (ℕ × List CounterMove)) × ℕ ↦ x.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hcons : Primrec₂ (fun (x : (ℕ × (ℕ × List CounterMove)) × ℕ) (tail : CounterMove) ↦
      x.2 :: tail) :=
    Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hstep : Primrec₂ (fun (R : ℕ) (p : ℕ × List CounterMove) ↦
      (List.range (R + 1)).flatMap (fun value ↦ p.2.map (fun tail ↦ value :: tail))) :=
    Primrec.list_flatMap hrange (Primrec.list_map htails hcons)
  refine (Primrec.nat_rec (Primrec.const [[]]) hstep).of_eq ?_
  intro R size
  induction size with
  | zero => rfl
  | succ size ih =>
    simpa only [Nat.rec_add_one, counterMoveBox] using
      congrArg (fun tails ↦
        (List.range (R + 1)).flatMap (fun value ↦ tails.map (fun tail ↦ value :: tail))) ih

/-- The finite box of candidate moves is computable from its bound and dimension.
Blueprint node `constr:determinacy`. -/
lemma computable_counter_move_box :
    Computable (fun x : ℕ × ℕ ↦ counterMoveBox x.1 x.2) :=
  primrec_counter_move_box.to_comp

end Kolmogorov.Milovanov
