/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.LegalMoves

/-!
# A computable bounded solver

For blueprint node `constr:determinacy`, this module computes the finite counter game's
winner and strategy using bounded iterations on lists of encoded positions. Expanding from
the root for twice the initial budget gives a successor-closed list. Synchronous table
updates then agree with the recursive solver at every position whose remaining budget is
within the number of completed rounds. `RoleExchange` uses the resulting computability
theorem together with the solver's winning-strategy properties.
-/

namespace Kolmogorov.Milovanov

private lemma computable_after_left_budget :
    Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      let g := decodeCounterGame x.1.1
      let pos := decodeCounterPosition g x.1.2
      pos.leftBudget - if g.activePlayer pos then 0 else x.2.sum) := by
  have hbudget : Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      (decodeCounterGame x.1.1).budget) :=
    computable_game_budget.comp (Computable.fst.comp Computable.fst)
  have hremaining : Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2).leftBudget) :=
    Primrec.nat_min.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))) hbudget
  have hs : Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      x.2.sum) := computable_nat_list_sum.comp Computable.snd
  have ha : Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      (decodeCounterGame x.1.1).activePlayer
        (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2)) :=
    computable_activePlayer.comp Computable.fst
  exact (Primrec.nat_sub.to_comp.comp hremaining
    (Computable.cond ha (Computable.const 0) hs)).of_eq (fun x ↦ by
      dsimp only
      cases (decodeCounterGame x.1.1).activePlayer
        (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2) <;> rfl)

private lemma computable_after_right_budget :
    Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      let g := decodeCounterGame x.1.1
      let pos := decodeCounterPosition g x.1.2
      pos.rightBudget - if g.activePlayer pos then x.2.sum else 0) := by
  have hbudget : Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      (decodeCounterGame x.1.1).budget) :=
    computable_game_budget.comp (Computable.fst.comp Computable.fst)
  have hremaining : Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2).rightBudget) :=
    Primrec.nat_min.to_comp.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))) hbudget
  have hs : Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      x.2.sum) := computable_nat_list_sum.comp Computable.snd
  have ha : Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      (decodeCounterGame x.1.1).activePlayer
        (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2)) :=
    computable_activePlayer.comp Computable.fst
  exact (Primrec.nat_sub.to_comp.comp hremaining
    (Computable.cond ha hs (Computable.const 0))).of_eq (fun x ↦ by
      dsimp only
      cases (decodeCounterGame x.1.1).activePlayer
        (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2) <;> rfl)

private lemma computable_after_move :
    Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      let g := decodeCounterGame x.1.1
      (g.afterMove (decodeCounterPosition g x.1.2) x.2).encode) := by
  exact (computable_addCounters.pair
    (computable_after_left_budget.pair
      computable_after_right_budget)).of_eq (fun x ↦ by
        dsimp only
        simp only [FiniteCounterGame.afterMove, CounterPosition.encode, decodeCounterPosition]
      )

private def expandPositions
    (game : FiniteCounterGame) (U : List (CounterPosition game)) : List (CounterPosition game) :=
  U ++ U.flatMap (fun pos ↦
    (counterMoveBox game.budget game.coordinates.length).filterMap (fun move ↦
      if game.LegalMove pos move then
        some (game.afterMove pos move)
      else none))

private def reachablePositions
    (game : FiniteCounterGame) (root : CounterPosition game) : List (CounterPosition game) :=
  (List.range (2 * game.budget)).foldl (fun U _ ↦ expandPositions game U) [root]

private def updateTable
    (game : FiniteCounterGame) (U : List (CounterPosition game))
    (table : List (CounterPositionCode × (Bool × Option CounterMove))) :
    List (CounterPositionCode × (Bool × Option CounterMove)) :=
  U.map (fun pos ↦
    let active := game.activePlayer pos
    let selected := (counterMoveBox game.budget game.coordinates.length).find? (fun move ↦
      if _hmove : game.LegalMove pos move then
        let after_pos := game.afterMove pos move
        let after_res := match table.find? (fun p ↦ p.1 == after_pos.encode) with
          | some res => res.2
          | none => (false, none)
        after_res.1 == active
      else false)
    match selected with
    | some move => (pos.encode, (active, some move))
    | none => (pos.encode, (!active, none)))

private def solveBounded (n : ℕ) (input : CounterGameCode × CounterPositionCode) :
    Bool × Option CounterMove :=
  let game := decodeCounterGame input.1
  let root := decodeCounterPosition game input.2
  let U := reachablePositions game root
  let init_table := U.map (fun pos ↦ (pos.encode, (false, (none : Option CounterMove))))
  let final_table := (List.range (n + 1)).foldl (fun table _ ↦ updateTable game U table) init_table
  match final_table.find? (fun p ↦ p.1 == root.encode) with
  | some res => res.2
  | none => (false, none)

-- Use primitive position codes for intermediate lists and tables. The root is
-- normalized before it becomes a table key, including on malformed budget inputs.
private abbrev SolverTable :=
  List (CounterPositionCode × (Bool × Option CounterMove))

/-- `List.find?` with a computable list and a computable predicate is computable. -/
theorem computable_find?
    {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a ↦ (f a).find? (p a)) := by
  have heq : (fun a ↦ (f a).find? (p a)) =
      (fun a ↦ (f a).foldr (fun b acc ↦ bif p a b then some b else acc) none) := by
    funext a
    induction f a with
    | nil => rfl
    | cons b t ih => cases h : p a b <;> simp [h, ih]
  rw [heq]
  exact Computable.list_foldr hf (Computable.const none)
    ((Computable.cond (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.option_some.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂)

/-- `List.filterMap` with a computable list and a computable partial map is computable. -/
theorem computable_filterMap
    {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → β → Option σ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a ↦ (f a).filterMap (g a)) := by
  have hstep : Computable₂ (fun (a : α) (p : β × List σ) ↦
      Option.casesOn (motive := fun _ ↦ List σ) (g a p.1) p.2 (fun q ↦ q :: p.2)) := by
    apply Computable.option_casesOn
    · exact hg.comp Computable.fst (Computable.fst.comp Computable.snd)
    · exact Computable.snd.comp Computable.snd
    · exact Computable.list_cons.comp Computable.snd
        (Computable.snd.comp (Computable.snd.comp Computable.fst))
  refine (Computable.list_foldr hf (Computable.const []) hstep).of_eq (fun a ↦ ?_)
  induction f a with
  | nil => rfl
  | cons b l ih => cases hgb : g a b <;> simp [hgb, ih]

private lemma computable_list_flat_map
    {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → β → List σ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a ↦ (f a).flatMap (g a)) :=
  Primrec.list_flatten.to_comp.comp (Computable.list_map hf hg)

private def normalizePositionCode (c : CounterGameCode) (z : CounterPositionCode) :
    CounterPositionCode :=
  (decodeCounterPosition (decodeCounterGame c) z).encode

private lemma computable_normalize_position_code :
    Computable (fun x : CounterGameCode × CounterPositionCode ↦
      normalizePositionCode x.1 x.2) := by
  have hb : Computable (fun x : CounterGameCode × CounterPositionCode ↦
      (decodeCounterGame x.1).budget) := computable_game_budget.comp Computable.fst
  exact (Computable.fst.comp Computable.snd).pair
    ((Primrec.nat_min.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp Computable.snd)) hb).pair
      (Primrec.nat_min.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)) hb))

private def gameMoveBox (c : CounterGameCode) : List CounterMove :=
  counterMoveBox (decodeCounterGame c).budget (decodeCounterGame c).coordinates.length

private lemma computable_game_move_box : Computable gameMoveBox := by
  -- Adding two empty vectors still emits one counter per coordinate.
  have hcounters : Computable (fun c : CounterGameCode ↦
      (decodeCounterGame c).addCounters [] []) :=
    computable_addCounters.comp
      ((Computable.id.pair (Computable.const ([], 0, 0))).pair (Computable.const []))
  have hsize : Computable (fun c : CounterGameCode ↦
      (decodeCounterGame c).coordinates.length) :=
    (Computable.list_length.comp hcounters).of_eq (fun c ↦ by
      simp [FiniteCounterGame.addCounters])
  exact computable_counter_move_box.comp
    (computable_game_budget.pair hsize)

private def expandPositionCodes (c : CounterGameCode) (U : List CounterPositionCode) :
    List CounterPositionCode :=
  U ++ U.flatMap (fun z ↦
    let g := decodeCounterGame c
    let pos := decodeCounterPosition g z
    (gameMoveBox c).filterMap (fun move ↦
      if g.LegalMove pos move then some (g.afterMove pos move).encode else none))

private lemma computable_expand_position_codes :
    Computable (fun x : CounterGameCode × List CounterPositionCode ↦
      expandPositionCodes x.1 x.2) := by
  have hsucc : Computable₂ (fun (x : CounterGameCode × List CounterPositionCode)
      (z : CounterPositionCode) =>
      let g := decodeCounterGame x.1
      let pos := decodeCounterPosition g z
      (gameMoveBox x.1).filterMap (fun move ↦
        if g.LegalMove pos move then some (g.afterMove pos move).encode else none)) := by
    apply computable_filterMap
    · exact computable_game_move_box.comp (Computable.fst.comp Computable.fst)
    · have hargs : Computable (fun y :
          ((CounterGameCode × List CounterPositionCode) × CounterPositionCode) × CounterMove =>
          ((y.1.1.1, y.1.2), y.2)) :=
        ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
          (Computable.snd.comp Computable.fst)).pair Computable.snd
      have hl := computable_decide_legalMove.comp hargs
      have ha := computable_after_move.comp hargs
      exact (Computable.cond hl (Computable.option_some.comp ha)
        (Computable.const none)).of_eq (fun y ↦ by
          dsimp only
          simp only [Bool.cond_decide])
  exact Computable.list_append.comp Computable.snd (computable_list_flat_map Computable.snd hsucc)

/-- Encoding commutes with a single expansion, preserving order and duplicates. -/
private lemma expand_position_codes_encode (c : CounterGameCode)
    (U : List (CounterPosition (decodeCounterGame c))) :
    expandPositionCodes c (U.map CounterPosition.encode) =
      (expandPositions (decodeCounterGame c) U).map
        CounterPosition.encode := by
  simp only [expandPositionCodes, gameMoveBox,
    expandPositions, List.map_append,
    List.map_flatMap, List.flatMap_map, List.map_filterMap,
    decode_encode_counter_position]
  congr 1
  apply congrArg (fun f ↦ U.flatMap f)
  funext pos
  apply List.filterMap_congr
  intro move _
  split <;> simp_all

private lemma computable_fold_range
    {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β → β} (hf : Computable₂ f) :
    Computable (fun x : ℕ × (α × β) ↦
      (List.range x.1).foldl (fun s _ ↦ f x.2.1 s) x.2.2) := by
  have hrange : Computable (fun x : ℕ × (α × β) ↦ List.range x.1) :=
    Primrec.list_range.to_comp.comp Computable.fst
  have hinit : Computable (fun x : ℕ × (α × β) ↦ x.2.2) :=
    Computable.snd.comp Computable.snd
  have hstep : Computable₂ (fun (x : ℕ × (α × β)) (p : β × ℕ) ↦ f x.2.1 p.1) :=
    hf.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.fst.comp Computable.snd)
  exact Computable.list_foldl hrange hinit hstep

private lemma computable_map_with_parameters
    {α β γ δ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]
    {f : (α × β) × γ → δ} (hf : Computable f) :
    Computable (fun x : α × List β × γ ↦ x.2.1.map (fun b ↦ f ((x.1, b), x.2.2))) := by
  exact Computable.list_map (Computable.fst.comp Computable.snd)
    (hf.comp
      (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
        (Computable.snd.comp (Computable.snd.comp Computable.fst))))

private def reachablePositionCodes (c : CounterGameCode) (z : CounterPositionCode) :
    List CounterPositionCode :=
  (List.range (2 * (decodeCounterGame c).budget)).foldl
    (fun U _ ↦ expandPositionCodes c U) [normalizePositionCode c z]

private lemma computable_reachable_position_codes :
    Computable (fun x : CounterGameCode × CounterPositionCode ↦
      reachablePositionCodes x.1 x.2) := by
  have hn : Computable (fun x : CounterGameCode × CounterPositionCode ↦
      2 * (decodeCounterGame x.1).budget) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2) (computable_game_budget.comp Computable.fst)
  have hinit : Computable (fun x : CounterGameCode × CounterPositionCode ↦
      [normalizePositionCode x.1 x.2]) :=
    Computable.list_cons.comp computable_normalize_position_code (Computable.const [])
  exact ((computable_fold_range computable_expand_position_codes).comp
    (hn.pair (Computable.fst.pair hinit))).of_eq (fun _ ↦ rfl)

/-- The expansion representation bridge persists through every expansion round. -/
private lemma reachable_position_codes_encode (c : CounterGameCode) (z : CounterPositionCode) :
    reachablePositionCodes c z =
      (reachablePositions (decodeCounterGame c)
        (decodeCounterPosition (decodeCounterGame c) z)).map CounterPosition.encode := by
  dsimp only [reachablePositionCodes, normalizePositionCode,
    reachablePositions]
  exact List.foldl_hom (fun U : List (CounterPosition (decodeCounterGame c)) ↦
    U.map CounterPosition.encode)
    (g₁ := fun U (_ : ℕ) ↦ expandPositions
      (decodeCounterGame c) U)
    (g₂ := fun U (_ : ℕ) ↦ expandPositionCodes c U)
    (l := List.range (2 * (decodeCounterGame c).budget))
    (init := [decodeCounterPosition (decodeCounterGame c) z])
    (fun U _ ↦ expand_position_codes_encode c U)

private lemma computable_beq
    {α : Type*} [Primcodable α] [BEq α] [LawfulBEq α] :
    Computable₂ (fun a b : α ↦ a == b) := by
  let : DecidableEq α := fun a b ↦ decidable_of_iff (a == b) beq_iff_eq
  have h : Primrec₂ (fun a b : α ↦ decide (a = b)) := Primrec.eq.decide
  exact h.to_comp.of_eq (fun x ↦ Bool.eq_iff_iff.mpr (by simp))

/-- First matching table value, using the bounded evaluator's default when absent. -/
private def lookupTable (table : SolverTable) (z : CounterPositionCode) :
    Bool × Option CounterMove :=
  match table.find? (fun p ↦ p.1 == z) with
  | some res => res.2
  | none => (false, none)

private lemma computable_lookup_table :
    Computable (fun x : SolverTable × CounterPositionCode ↦ lookupTable x.1 x.2) := by
  have hfind : Computable (fun x : SolverTable × CounterPositionCode ↦
      x.1.find? (fun p ↦ p.1 == x.2)) :=
    computable_find? Computable.fst
      (computable_beq.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.fst))
  have hsome : Computable₂ (fun (_ : SolverTable × CounterPositionCode)
      (res : CounterPositionCode × (Bool × Option CounterMove)) => res.2) :=
    Computable.snd.comp Computable.snd
  exact (Computable.option_casesOn hfind (Computable.const (false, none)) hsome).of_eq
    (fun x ↦ by
      unfold lookupTable
      cases x.1.find? (fun p ↦ p.1 == x.2) <;> rfl)

/-- Compute one table entry from the previous synchronous table. -/
private def evaluateRow (input : CounterGameCode × CounterPositionCode) (table : SolverTable) :
    CounterPositionCode × (Bool × Option CounterMove) :=
  let g := decodeCounterGame input.1
  let pos := decodeCounterPosition g input.2
  let active := g.activePlayer pos
  let selected := (gameMoveBox input.1).find? (fun move ↦
    if g.LegalMove pos move then
      (lookupTable table (g.afterMove pos move).encode).1 == active
    else false)
  match selected with
  | some move => (input.2, (active, some move))
  | none => (input.2, (!active, none))

private lemma computable_evaluate_row :
    Computable (fun x : (CounterGameCode × CounterPositionCode) × SolverTable ↦
      evaluateRow x.1 x.2) := by
  have hactive : Computable (fun x : (CounterGameCode × CounterPositionCode) × SolverTable ↦
      (decodeCounterGame x.1.1).activePlayer
        (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2)) :=
    computable_activePlayer.comp Computable.fst
  have hselected : Computable (fun x : (CounterGameCode × CounterPositionCode) × SolverTable ↦
      (gameMoveBox x.1.1).find? (fun move ↦
        if (decodeCounterGame x.1.1).LegalMove
            (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2) move then
          (lookupTable x.2 ((decodeCounterGame x.1.1).afterMove
            (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2) move).encode).1 ==
              (decodeCounterGame x.1.1).activePlayer
                (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2)
        else false)) := by
    apply computable_find? (computable_game_move_box.comp (Computable.fst.comp Computable.fst))
    have hargs : Computable (fun y :
        ((CounterGameCode × CounterPositionCode) × SolverTable) × CounterMove =>
        (y.1.1, y.2)) :=
      (Computable.fst.comp Computable.fst).pair Computable.snd
    have hlegal := computable_decide_legalMove.comp hargs
    have hafter := computable_after_move.comp hargs
    have hlookup := computable_lookup_table.comp
      ((Computable.snd.comp Computable.fst).pair hafter)
    have hwinner := computable_beq.comp (Computable.fst.comp hlookup)
      (hactive.comp Computable.fst)
    exact (Computable.cond hlegal hwinner (Computable.const false)).of_eq
      (fun _ ↦ by simp only [Bool.cond_decide])
  have hnone : Computable (fun x : (CounterGameCode × CounterPositionCode) × SolverTable ↦
      (x.1.2, (!(decodeCounterGame x.1.1).activePlayer
        (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2),
          (none : Option CounterMove)))) :=
    (Computable.snd.comp Computable.fst).pair
      ((Primrec.not.to_comp.comp hactive).pair (Computable.const none))
  have hsome : Computable₂ (fun (x : (CounterGameCode × CounterPositionCode) × SolverTable)
      (move : CounterMove) =>
      (x.1.2, ((decodeCounterGame x.1.1).activePlayer
        (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2), some move))) :=
    (Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
      ((hactive.comp Computable.fst).pair (Computable.option_some.comp Computable.snd))
  exact (Computable.option_casesOn hselected hnone hsome).of_eq (fun x ↦ by
    dsimp only [evaluateRow]
    split <;> rename_i h <;> rw [h])

private def updateCodeTable (c : CounterGameCode) (U : List CounterPositionCode)
    (table : SolverTable) : SolverTable :=
  U.map (fun z ↦ evaluateRow (c, z) table)

private lemma computable_update_code_table :
    Computable (fun x : CounterGameCode × List CounterPositionCode × SolverTable ↦
      updateCodeTable x.1 x.2.1 x.2.2) := by
  exact (computable_map_with_parameters computable_evaluate_row).of_eq (fun _ ↦ rfl)

/-- The code update agrees on every list of valid positions and every previous table. -/
private lemma update_code_table_encode (c : CounterGameCode)
    (U : List (CounterPosition (decodeCounterGame c))) (table : SolverTable) :
    updateCodeTable c (U.map CounterPosition.encode) table =
      updateTable (decodeCounterGame c) U table := by
  simp only [updateCodeTable, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro pos _
  simp only [evaluateRow, gameMoveBox, decode_encode_counter_position,
    lookupTable, dite_eq_ite]

private lemma computable_reassociate
    {α β γ δ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]
    {f : α × β × γ → δ} (hf : Computable f) :
    Computable (fun x : (α × β) × γ ↦ f (x.1.1, x.1.2, x.2)) :=
  hf.comp ((Computable.fst.comp Computable.fst).pair
    ((Computable.snd.comp Computable.fst).pair Computable.snd))

private lemma computable_fold_range_with_parameters
    {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α × β × γ → γ} (hf : Computable f) :
    Computable (fun x : ℕ × ((α × β) × γ) ↦
      (List.range x.1).foldl (fun s _ ↦ f (x.2.1.1, x.2.1.2, s)) x.2.2) := by
  apply computable_fold_range (α := α × β) (β := γ)
    (f := fun (p : α × β) (s : γ) ↦ f (p.1, p.2, s))
  change Computable (fun x : (α × β) × γ ↦ f (x.1.1, x.1.2, x.2))
  exact computable_reassociate (α := α) (β := β) (γ := γ) (δ := γ) (f := f) hf

private def initialTable (U : List CounterPositionCode) : SolverTable :=
  U.map (fun z ↦ (z, (false, (none : Option CounterMove))))

private lemma computable_initial_table : Computable initialTable := by
  have hrow : Primrec₂ (fun (_ : List CounterPositionCode) (z : CounterPositionCode) ↦
      (z, (false, (none : Option CounterMove)))) :=
    (Primrec.snd.pair (Primrec.const (false, none))).to₂
  exact (Primrec.list_map Primrec.id hrow).to_comp

private lemma computable_update_rounds :
    Computable (fun x : ℕ × ((CounterGameCode × List CounterPositionCode) × SolverTable) ↦
      (List.range x.1).foldl
        (fun table _ ↦ updateCodeTable x.2.1.1 x.2.1.2 table) x.2.2) := by
  exact (computable_fold_range_with_parameters computable_update_code_table).of_eq (fun _ ↦ rfl)

private def iterateCodeTable (n : ℕ) (input : CounterGameCode × CounterPositionCode) :
    SolverTable :=
  (List.range (n + 1)).foldl
    (fun table _ ↦ updateCodeTable input.1 (reachablePositionCodes input.1 input.2) table)
    (initialTable (reachablePositionCodes input.1 input.2))

private lemma computable_iterate_code_table :
    Computable (fun x : ℕ × (CounterGameCode × CounterPositionCode) ↦
      iterateCodeTable x.1 x.2) := by
  have hU : Computable (fun x : ℕ × (CounterGameCode × CounterPositionCode) ↦
      reachablePositionCodes x.2.1 x.2.2) := computable_reachable_position_codes.comp Computable.snd
  have hinit : Computable (fun x : ℕ × (CounterGameCode × CounterPositionCode) ↦
      initialTable (reachablePositionCodes x.2.1 x.2.2)) := computable_initial_table.comp hU
  have hcontext : Computable (fun x : ℕ × (CounterGameCode × CounterPositionCode) ↦
      (x.2.1, reachablePositionCodes x.2.1 x.2.2)) :=
    (Computable.fst.comp Computable.snd).pair hU
  exact (computable_update_rounds.comp
    ((Computable.succ.comp Computable.fst).pair (hcontext.pair hinit))).of_eq (fun _ ↦ rfl)

private lemma computable_solve_bounded :
    Computable (fun x : ℕ × (CounterGameCode × CounterPositionCode) ↦
      solveBounded x.1 x.2) := by
  have hresult := computable_lookup_table.comp
    (computable_iterate_code_table.pair (computable_normalize_position_code.comp Computable.snd))
  refine hresult.of_eq (fun x ↦ ?_)
  dsimp only [iterateCodeTable]
  simp only [reachable_position_codes_encode, update_code_table_encode, initialTable, List.map_map]
  rfl

private lemma counter_position_encode_injective
    {game : FiniteCounterGame} (p1 p2 : CounterPosition game) :
    p1.encode = p2.encode → p1 = p2 := by
  intro h
  have h1 : decodeCounterPosition game p1.encode = decodeCounterPosition game p2.encode := by rw [h]
  rw [decode_encode_counter_position, decode_encode_counter_position] at h1
  exact h1

private lemma find_encoded_position
    {game : FiniteCounterGame} (U : List (CounterPosition game))
    (pos : CounterPosition game) (hpos : pos ∈ U)
    (f_table : CounterPosition game → Bool × Option CounterMove) :
    (U.map (fun a ↦ (a.encode, f_table a))).find? (fun p ↦ p.1 == pos.encode) =
      some (pos.encode, f_table pos) := by
  induction U with
  | nil =>
    cases hpos
  | cons head tail ih =>
    simp only [List.map_cons, List.find?_cons]
    if heq : head.encode = pos.encode then
      have : (head.encode == pos.encode) = true := beq_iff_eq.mpr heq
      rw [this]
      have : head = pos := counter_position_encode_injective head pos heq
      subst this
      rfl
    else
      have : (head.encode == pos.encode) = false := beq_false_of_ne heq
      rw [this]
      have hx_tail : pos ∈ tail := by
        cases hpos with
        | head _ => exact False.elim (heq rfl)
        | tail _ h => exact h
      exact ih hx_tail

/-- A table update agrees with the solver when every legal successor already has its value. -/
private lemma find_update_table_eq_solve
    (game : FiniteCounterGame) (U : List (CounterPosition game))
    (table : List (CounterPositionCode × (Bool × Option CounterMove)))
    (pos : CounterPosition game) (hpos : pos ∈ U)
    (hcorrect : ∀ move, (hmove : game.LegalMove pos move) →
      table.find? (fun p ↦ p.1 == (game.afterMove pos move).encode) =
        some ((game.afterMove pos move).encode, game.solve (game.afterMove pos move))) :
    (updateTable game U table).find?
      (fun p ↦ p.1 == pos.encode) = some (pos.encode, game.solve pos) := by
  let f_table := fun (a : CounterPosition game) ↦
    let active := game.activePlayer a
    let selected := (counterMoveBox game.budget game.coordinates.length).find? (fun move ↦
      if _hmove : game.LegalMove a move then
        let after_pos := game.afterMove a move
        let after_res := match table.find? (fun p ↦ p.1 == after_pos.encode) with
          | some res => res.2
          | none => (false, none)
        after_res.1 == active
      else false)
    match selected with
    | some move => (active, some move)
    | none => (!active, none)
  have h_eq : updateTable game U table = U.map (fun a ↦ (a.encode, f_table a)) := by
    dsimp [updateTable, f_table]
    apply congr_arg (List.map · U)
    funext a
    split
    · rfl
    · rfl
  rw [h_eq]
  have h_aux : f_table pos = game.solve pos := by
    rw [FiniteCounterGame.solve]
    dsimp only [f_table]
    congr 1
    apply List.find?_congr
    intro move _hmove_box
    split_ifs with hmove
    · have h_table := hcorrect move hmove
      rw [h_table]
    · rfl
  rw [find_encoded_position U pos hpos f_table, h_aux]

/-- Each update resolves positions with one more unit of total remaining budget. -/
private lemma find_iterate_table_eq_solve
    (game : FiniteCounterGame) (U : List (CounterPosition game))
    (hclosed : ∀ q, q ∈ U → ∀ move, game.LegalMove q move →
      game.afterMove q move ∈ U)
    (k : ℕ) (pos : CounterPosition game) (hpos : pos ∈ U) (hbudget : pos.budgetSum ≤ k) :
    ((List.range (k + 1)).foldl (fun table _ ↦ updateTable game U table)
      (U.map (fun pos ↦ (pos.encode, (false, (none : Option CounterMove)))))).find?
        (fun p ↦ p.1 == pos.encode) = some (pos.encode, game.solve pos) := by
  induction k generalizing pos with
  | zero =>
    apply find_update_table_eq_solve game U _ pos hpos
    intro move hmove
    have hdecrease := counter_move_decreases_budget game pos move hmove
    omega
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    apply find_update_table_eq_solve game U _ pos hpos
    intro move hmove
    have hdecrease := counter_move_decreases_budget game pos move hmove
    exact ih (game.afterMove pos move) (hclosed pos hpos move hmove) (by omega)


private lemma mem_expand_positions_iff
    (game : FiniteCounterGame) (U : List (CounterPosition game)) (q : CounterPosition game) :
    q ∈ expandPositions game U ↔
      q ∈ U ∨ ∃ p ∈ U, ∃ m, game.LegalMove p m ∧ q = game.afterMove p m := by
  dsimp [expandPositions]
  rw [List.mem_append]
  apply or_congr_right
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hm⟩
    rw [List.mem_filterMap] at hm
    rcases hm with ⟨m, hm_mem, hm_eq⟩
    split_ifs at hm_eq with hl
    · rcases hm_eq
      exact ⟨p, hp, m, hl, rfl⟩
  · rintro ⟨p, hp, m, hl, rfl⟩
    exact ⟨p, hp, List.mem_filterMap.mpr
      ⟨m, legal_move_mem_box _ _ _ hl, by simp only [hl, ↓reduceIte]⟩⟩

private lemma expand_positions_fold_succ
    (game : FiniteCounterGame) (root : CounterPosition game) (n : ℕ) :
    let T := fun n ↦ (List.range n).foldl (fun U _ ↦ expandPositions game U) [root]
    T (n + 1) = expandPositions game (T n) := by
  simp [List.range_succ, List.foldl_append]

private lemma mem_previous_round_or_budget_le
    (game : FiniteCounterGame) (root : CounterPosition game) (n : ℕ) (q : CounterPosition game) :
    let T := fun n ↦ (List.range n).foldl (fun U _ ↦ expandPositions game U) [root]
    q ∈ T (n + 1) → q ∈ T n ∨ q.budgetSum + (n + 1) ≤ root.budgetSum := by
  intro T
  have hrec (k : ℕ) :
      T (k + 1) =
        expandPositions game (T k) :=
    expand_positions_fold_succ
      game root k
  have hexp :=
    mem_expand_positions_iff
      game
  induction n generalizing q with
  | zero =>
      intro hq
      rw [hrec 0] at hq
      rcases (hexp (T 0) q).mp hq with hq | hq
      · exact Or.inl hq
      · rcases hq with ⟨p, hp, m, hm, rfl⟩
        have hp' : p = root := by simpa [T] using hp
        subst p
        have hd := counter_move_decreases_budget game root m hm
        exact Or.inr (by omega)
  | succ n ih =>
      intro hq
      rw [hrec (n + 1)] at hq
      rcases (hexp (T (n + 1)) q).mp hq with hq | hq
      · exact Or.inl hq
      · rcases hq with ⟨p, hp, m, hm, rfl⟩
        rcases ih p hp with hpold | hpbound
        · apply Or.inl
          rw [hrec n]
          exact (hexp (T n) (game.afterMove p m)).mpr
            (Or.inr ⟨p, hpold, m, hm, rfl⟩)
        · have hd := counter_move_decreases_budget game p m hm
          exact Or.inr (by omega)

private lemma root_mem_expansion_rounds
    (game : FiniteCounterGame) (root : CounterPosition game) (n : ℕ) :
    let T := fun n ↦ (List.range n).foldl (fun U _ ↦ expandPositions game U) [root]
    root ∈ T n := by
  intro T
  induction n with
  | zero => simp [T]
  | succ n ih =>
    have hr := expand_positions_fold_succ game root n
    change T (n + 1) = expandPositions game (T n) at hr
    rw [hr]
    have hE := mem_expand_positions_iff game (T n) root
    exact hE.mpr (Or.inl ih)

/-- Bounded expansion retains the root and includes every legal successor of its positions. -/
private lemma reachable_positions_closed
    (game : FiniteCounterGame) (root : CounterPosition game) :
    root ∈ reachablePositions game root ∧
    ∀ q, q ∈ reachablePositions game root →
      ∀ move, game.LegalMove q move →
        game.afterMove q move ∈ reachablePositions game root := by
  let T := fun n : ℕ ↦ (List.range n).foldl (fun U _ ↦ expandPositions game U) [root]
  have hb : root.budgetSum ≤ 2 * game.budget := by
    have hl := root.left_le
    have hr := root.right_le
    dsimp [CounterPosition.budgetSum]
    omega
  constructor
  · change root ∈ T (2 * game.budget)
    exact root_mem_expansion_rounds game root (2 * game.budget)
  · intro q hq m hm
    change q ∈ T (2 * game.budget) at hq
    change game.afterMove q m ∈ T (2 * game.budget)
    have hn : game.afterMove q m ∈ T (2 * game.budget + 1) := by
      have hr := expand_positions_fold_succ game root (2 * game.budget)
      change T (2 * game.budget + 1) = expandPositions game (T (2 * game.budget)) at hr
      rw [hr]
      have hE := mem_expand_positions_iff game (T (2 * game.budget)) (game.afterMove q m)
      exact hE.mpr (Or.inr ⟨q, hq, m, hm, rfl⟩)
    have hf := mem_previous_round_or_budget_le game root (2 * game.budget) (game.afterMove q m)
    rcases hf hn with h | h
    · exact h
    · omega

private lemma solve_bounded_eq_solve
    (input : CounterGameCode × CounterPositionCode) :
    solveBounded
      (2 * (decodeCounterGame input.1).budget) input =
        solveCounterGameCode input := by
  dsimp only [solveBounded]
  let game := decodeCounterGame input.1
  let root := decodeCounterPosition game input.2
  have hroot_budget : root.budgetSum ≤ 2 * game.budget := by
    have hl := root.left_le
    have hr := root.right_le
    dsimp [CounterPosition.budgetSum]
    omega
  have hroot := reachable_positions_closed game root
  have h_inv := find_iterate_table_eq_solve game
    (reachablePositions game root) hroot.2
    (2 * game.budget) root hroot.1 hroot_budget
  rw [h_inv]
  unfold solveCounterGameCode
  rfl

/-- The decreasing-budget solver is computable on encoded game and position data.
Blueprint node `constr:determinacy`. -/
lemma computable_solveCounterGameCode :
    Computable solveCounterGameCode := by
  have hb : Primrec (fun input : CounterGameCode × CounterPositionCode ↦
      (decodeCounterGame input.1).budget) := by
    change Primrec (fun input : CounterGameCode × CounterPositionCode ↦
      input.1.2.2.2.2.1)
    exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hn : Computable (fun input : CounterGameCode × CounterPositionCode ↦
      2 * (decodeCounterGame input.1).budget) :=
    (Primrec.nat_mul.comp (Primrec.const 2) hb).to_comp
  exact (computable_solve_bounded.comp
    (hn.pair Computable.id)).of_eq
      solve_bounded_eq_solve

end Kolmogorov.Milovanov
