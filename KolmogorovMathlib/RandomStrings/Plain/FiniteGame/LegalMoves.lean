/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.Rules

/-!
# Computability of the finite counter game's rules

For blueprint node `constr:determinacy`, the solver of the finite counter game works on primitive
codes of games, positions and moves (`CounterGameCode`, `CounterPositionCode`, `CounterMove`).
This module shows that the rules of the game of `Rules`, read off such codes, are computable:

* the deduplicated coordinate list, the price and counter lookups, and the answer
  `counterAnswer` of the counter oracle;
* the referee's output at a vector of counters, obtained by running a stack machine on the
  referee's postfix code;
* the active player (`computable_activePlayer`), the sum and sizes of a move, the vector sum
  `addCounters`, and finally legality of a move (`computable_decide_legalMove`).

`BoundedSolver` composes these facts to compute the game's winner and strategy.
-/

namespace Kolmogorov.Milovanov

/-! ### Coordinate deduplication -/

/-! ### Generic list facts -/

/-- `List.any` along a computable list with a computable predicate is computable. -/
private lemma computable_list_any {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a ↦ (f a).any (p a)) := by
  have hstep : Computable₂ (fun (a : α) (q : β × Bool) ↦ p a q.1 || q.2) :=
    (Primrec.or.to_comp.comp
      (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  refine (Computable.list_foldr hf (Computable.const false) hstep).of_eq (fun a ↦ ?_)
  induction f a with
  | nil => rfl
  | cons b t ih => simp [List.any_cons, ih]

/-- The sum of a list of naturals is computable. -/
theorem computable_nat_list_sum : Computable (List.sum : List ℕ → ℕ) := by
  have hadd : Primrec₂ (fun (_ : List ℕ) (p : ℕ × ℕ) ↦ p.1 + p.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldl Primrec.id (Primrec.const 0) hadd).to_comp.of_eq
    (fun xs ↦ (List.sum_eq_foldl (xs := xs)).symm)

/-! ### Fields of a decoded game -/

/-- The initial budget of a decoded game is computable from its code. -/
theorem computable_game_budget :
    Computable (fun c : CounterGameCode ↦ (decodeCounterGame c).budget) := by
  change Computable (fun c : CounterGameCode ↦ c.2.2.2.2.1)
  exact Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp Computable.snd)))

/-- The fixed target of a decoded game is computable from its code. -/
private lemma computable_game_target :
    Computable (fun c : CounterGameCode ↦ (decodeCounterGame c).target) := by
  change Computable (fun c : CounterGameCode ↦ c.2.2.2.2.2.2.1)
  exact Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp Computable.snd)))))

/-- The equality player of a decoded game is computable from its code. -/
private lemma computable_game_equalityPlayer :
    Computable (fun c : CounterGameCode ↦ (decodeCounterGame c).equalityPlayer) := by
  change Computable (fun c : CounterGameCode ↦ c.2.2.2.2.2.2.2)
  exact Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp Computable.snd)))))

/-- The deduplicated coordinate list of a decoded game is computable from its code. -/
private lemma computable_game_coordinates :
    Computable (fun c : CounterGameCode ↦ (decodeCounterGame c).coordinates) := by
  change Computable (fun c : CounterGameCode ↦ c.1.eraseDups)
  exact primrec_eraseDups.to_comp.comp Computable.fst

/-! ### The counter oracle -/

/-- The value of a counter vector at a coordinate: the index of the coordinate in the
deduplicated list, the table lookup with default zero, and the membership test are computable. -/
private lemma computable₂_coordinateValue :
    Computable₂ (fun (c : CounterGameCode) (p : List ℕ × Coordinate) ↦
      (decodeCounterGame c).coordinateValue p.1 p.2) := by
  have hc : Computable (fun t : CounterGameCode × (List ℕ × Coordinate) ↦
      (decodeCounterGame t.1).coordinates) :=
    computable_game_coordinates.comp Computable.fst
  have hq : Computable (fun t : CounterGameCode × (List ℕ × Coordinate) ↦ t.2.2) :=
    Computable.snd.comp Computable.snd
  have hv : Computable (fun t : CounterGameCode × (List ℕ × Coordinate) ↦ t.2.1) :=
    Computable.fst.comp Computable.snd
  have hm := Computable₂.comp listMemDecide_primrec.to_comp hq hc
  have hi : Computable (fun t : CounterGameCode × (List ℕ × Coordinate) ↦
      (decodeCounterGame t.1).coordinates.idxOf t.2.2) := by
    refine (Computable₂.comp Primrec.list_idxOf.to_comp hq hc).of_eq ?_
    intro t
    unfold List.idxOf
    congr 1
    funext a
    exact Bool.eq_iff_iff.mpr (by simp)
  have hg := Computable.option_getD
    (Computable.list_getElem?.comp hv hi) (Computable.const 0)
  refine (Computable.cond hm hg (Computable.const 0)).of_eq ?_
  intro t
  by_cases h : t.2.2 ∈ (decodeCounterGame t.1).coordinates <;>
    simp [FiniteCounterGame.coordinateValue, h]

/-- The price of a coordinate is the lookup of the price table. -/
private lemma computable₂_price :
    Computable₂ (fun (c : CounterGameCode) (q : Coordinate) ↦
      (decodeCounterGame c).price q) := by
  have hargs : Computable (fun t : CounterGameCode × Coordinate ↦ (t.1, (t.1.2.1, t.2))) :=
    Computable.fst.pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
  have h := Computable.comp computable₂_coordinateValue hargs
  exact h

/-- A retained coordinate covers a query when the two share their string, the query's threshold
is at least the retained one, and the retained counter reaches its price. -/
private lemma computable₂_covers :
    Computable₂ (fun (x : CounterGameCode × List ℕ) (p : Coordinate × Coordinate) ↦
      decide (p.1.1 = p.2.1 ∧ p.1.2 ≤ p.2.2 ∧
        (decodeCounterGame x.1).price p.1 ≤ (decodeCounterGame x.1).coordinateValue x.2 p.1)) := by
  let T := (CounterGameCode × List ℕ) × (Coordinate × Coordinate)
  have hprice : Computable (fun t : T ↦ (decodeCounterGame t.1.1).price t.2.1) := by
    have hargs : Computable (fun t : T ↦ (t.1.1, t.2.1)) :=
      (Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd)
    have h := Computable.comp computable₂_price hargs
    exact h
  have hvalue : Computable (fun t : T ↦
      (decodeCounterGame t.1.1).coordinateValue t.1.2 t.2.1) := by
    have hargs : Computable (fun t : T ↦ (t.1.1, (t.1.2, t.2.1))) :=
      (Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp Computable.fst).pair (Computable.fst.comp Computable.snd))
    have h := Computable.comp computable₂_coordinateValue hargs
    exact h
  have hle_price : Computable (fun t : T ↦ decide ((decodeCounterGame t.1.1).price t.2.1 ≤
      (decodeCounterGame t.1.1).coordinateValue t.1.2 t.2.1)) :=
    Computable₂.comp Primrec.nat_le.decide.to_comp hprice hvalue
  have heq : Computable (fun t : T ↦ decide (t.2.1.1 = t.2.2.1)) :=
    Computable₂.comp Primrec.eq.decide.to_comp
      (Computable.fst.comp (Computable.fst.comp Computable.snd))
      (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have hle : Computable (fun t : T ↦ decide (t.2.1.2 ≤ t.2.2.2)) :=
    Computable₂.comp Primrec.nat_le.decide.to_comp
      (Computable.snd.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact (Computable₂.comp Primrec.and.to_comp heq
    (Computable₂.comp Primrec.and.to_comp hle hle_price)).of_eq
      (fun _ ↦ by simp only [Bool.decide_and])

/-- The answers of the counter oracle at a vector of counters are computable from the game
code and the counters. -/
private lemma computable₂_counterAnswer :
    Computable₂ (fun (x : CounterGameCode × List ℕ) (q : Coordinate) ↦
      (decodeCounterGame x.1).counterAnswer x.2 q) := by
  let T := (CounterGameCode × List ℕ) × Coordinate
  have hcoordinates : Computable (fun t : T ↦ (decodeCounterGame t.1.1).coordinates) :=
    computable_game_coordinates.comp (Computable.fst.comp Computable.fst)
  have hcovers : Computable₂ (fun (t : T) (r : Coordinate) ↦
      decide (r.1 = t.2.1 ∧ r.2 ≤ t.2.2 ∧
        (decodeCounterGame t.1.1).price r ≤
          (decodeCounterGame t.1.1).coordinateValue t.1.2 r)) := by
    have hargs : Computable (fun z : T × Coordinate ↦ (z.1.1, (z.2, z.1.2))) :=
      (Computable.fst.comp Computable.fst).pair
        (Computable.snd.pair (Computable.snd.comp Computable.fst))
    have h := Computable.comp computable₂_covers hargs
    exact h
  have hany := computable_list_any hcoordinates hcovers
  have hyes : Computable (fun t : T ↦ decide (t.2 ∈ (decodeCounterGame t.1.1).initialYes)) := by
    have hargs : Computable (fun t : T ↦ (t.2, t.1.1.2.2.2.1)) :=
      Computable.snd.pair (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.snd.comp (Computable.fst.comp Computable.fst)))))
    exact (Computable.comp (listMemDecide_primrec (β := Coordinate)).to_comp hargs).of_eq
      (fun _ ↦ decide_eq_decide.mpr Iff.rfl)
  exact (Computable₂.comp Primrec.or.to_comp hyes hany).of_eq (fun _ ↦ rfl)

/-! ### Evaluating a referee code -/

/-- A decoding-stack entry paired with the value the tree takes against the answers of `u`. -/
private def evalEntry {α : Type} (answer : α → Coordinate → Bool) (u : α) (t : QueryTree) :
    QueryTree.Code × ℕ :=
  (t.encode, t.eval (answer u))

/-- One instruction of the stack machine which, instead of trees, keeps pairs of a tree's code
and its value against the answers of `u`. -/
private def evalStep {α : Type} (answer : α → Coordinate → Bool) (u : α)
    (stack : List (QueryTree.Code × ℕ)) : ℕ ⊕ Coordinate → List (QueryTree.Code × ℕ)
  | .inl out => ([.inl out], out) :: stack
  | .inr q =>
    match stack with
    | yes :: no :: rest =>
      (no.1 ++ yes.1 ++ [.inr q], if answer u q then yes.2 else no.2) :: rest
    | _ => []

/-- The decoding step of `QueryTree.decode`, which is not exported from its file. -/
private def treeStep (stack : List QueryTree) : ℕ ⊕ Coordinate → List QueryTree
  | .inl out => .leaf out :: stack
  | .inr query =>
    match stack with
    | yes :: no :: rest => .node query no yes :: rest
    | _ => []

/-- A single instruction of the evaluating stack machine is computable. -/
private lemma computable₂_evalStep {α : Type} [Primcodable α]
    (answer : α → Coordinate → Bool) (hanswer : Computable₂ answer) :
    Computable₂ (fun (u : α) (p : List (QueryTree.Code × ℕ) × (ℕ ⊕ Coordinate)) ↦
      evalStep answer u p.1 p.2) := by
  let S := List (QueryTree.Code × ℕ)
  let X := α × (S × (ℕ ⊕ Coordinate))
  let Q := X × Coordinate
  have hl : Computable₂ (fun (x : X) (n : ℕ) ↦ (([Sum.inl n], n) :: x.2.1 : S)) :=
    (Computable.list_cons.comp
      ((Computable.list_cons.comp (Computable.sumInl.comp Computable.snd)
        (Computable.const [])).pair Computable.snd)
      (Computable.fst.comp (Computable.snd.comp Computable.fst))).to₂
  let s : Q → S := fun z ↦ z.1.2.1
  let t : Q → S := fun z ↦ (s z).tail
  let y : Q → QueryTree.Code × ℕ := fun z ↦ (s z).head?.getD ([], 0)
  let n : Q → QueryTree.Code × ℕ := fun z ↦ (t z).head?.getD ([], 0)
  have hs : Computable s := Computable.fst.comp (Computable.snd.comp Computable.fst)
  have ht : Computable t := Primrec.list_tail.to_comp.comp hs
  have hy : Computable y := Computable.option_getD
    (Primrec.list_head?.to_comp.comp hs) (Computable.const ([], 0))
  have hn : Computable n := Computable.option_getD
    (Primrec.list_head?.to_comp.comp ht) (Computable.const ([], 0))
  have hb : Computable (fun z : Q ↦ answer z.1.1 z.2) :=
    hanswer.comp (Computable.fst.comp Computable.fst) Computable.snd
  have hv := Computable.cond hb (Computable.snd.comp hy) (Computable.snd.comp hn)
  have hc : Computable (fun z : Q ↦ (n z).1 ++ (y z).1 ++ [Sum.inr z.2]) :=
    Computable.list_append.comp
      (Computable.list_append.comp (Computable.fst.comp hn) (Computable.fst.comp hy))
      (Computable.list_cons.comp (Computable.sumInr.comp Computable.snd) (Computable.const []))
  have hok : Computable (fun z : Q ↦ decide (2 ≤ (s z).length)) :=
    Primrec.nat_le.decide.to_comp.comp (Computable.const 2) (Computable.list_length.comp hs)
  have hq := Computable.cond hok
    (Computable.list_cons.comp (hc.pair hv) (Primrec.list_tail.to_comp.comp ht))
    (Computable.const [])
  change Computable (fun x : X ↦ evalStep answer x.1 x.2.1 x.2.2)
  refine (Computable.sumCasesOn (Computable.snd.comp Computable.snd) hl hq.to₂).of_eq ?_
  intro x
  rcases x with ⟨u, stack, i⟩
  cases i with
  | inl out => rfl
  | inr q =>
    rcases stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · rfl
    · cases ha : answer u q <;> simp [s, t, y, n, ha, evalStep]

/-- The evaluating machine keeps, for each tree on the decoding stack, its code and value. -/
private lemma map_treeStep {α : Type} (answer : α → Coordinate → Bool) (u : α)
    (stack : List QueryTree) (i : ℕ ⊕ Coordinate) :
    (treeStep stack i).map (evalEntry answer u) =
      evalStep answer u (stack.map (evalEntry answer u)) i := by
  cases i with
  | inl out => simp [treeStep, evalStep, evalEntry, QueryTree.encode, QueryTree.eval]
  | inr q =>
    rcases stack with _ | ⟨yes, _ | ⟨no, rest⟩⟩
    · rfl
    · rfl
    · simp [treeStep, evalStep, evalEntry, QueryTree.encode, QueryTree.eval]

/-- Running the evaluating machine on a code commutes with mapping to stack entries. -/
private lemma map_foldl_treeStep {α : Type} (answer : α → Coordinate → Bool) (u : α)
    (code : QueryTree.Code) (stack : List QueryTree) :
    (code.foldl treeStep stack).map (evalEntry answer u) =
      code.foldl (evalStep answer u) (stack.map (evalEntry answer u)) := by
  induction code generalizing stack with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldl_cons, List.foldl_cons, ← map_treeStep answer u stack head]
    exact ih _

/-- Executing a tree's code pushes that tree onto any existing decoding stack. -/
private lemma foldl_treeStep_encode (tree : QueryTree) (stack : List QueryTree) :
    tree.encode.foldl treeStep stack = tree :: stack := by
  induction tree generalizing stack with
  | leaf out => rfl
  | node query no yes ihno ihyes =>
    simp [QueryTree.encode, List.foldl_append, treeStep, ihno, ihyes]

/-- A code decodes to a tree exactly when it is that tree's canonical code. -/
private lemma decode_eq_some_iff (code : QueryTree.Code) (tree : QueryTree) :
    QueryTree.decode code = some tree ↔ tree.encode = code := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ QueryTree.decode_encode tree⟩
  unfold QueryTree.decode at h
  split at h
  · split_ifs at h with henc
    · injection h with ht
      exact ht ▸ henc
  · contradiction

/-- The value computed by the evaluating machine on a code: the top entry's value when the
final stack is a single entry whose code is the input, and `0` otherwise. -/
private def evalRun {α : Type} (answer : α → Coordinate → Bool) (code : QueryTree.Code)
    (u : α) : ℕ :=
  let stack := code.foldl (evalStep answer u) []
  if stack.length = 1 ∧ (stack.head?.getD ([], 0)).1 = code then
    (stack.head?.getD ([], 0)).2 else 0

/-- The evaluating machine computes the value of the decoded tree, and `0` for invalid codes. -/
private lemma evalRun_eq {α : Type} (answer : α → Coordinate → Bool) (code : QueryTree.Code)
    (u : α) :
    evalRun answer code u = ((QueryTree.decode code).getD (.leaf 0)).eval (answer u) := by
  have hfold : code.foldl (evalStep answer u) [] =
      (code.foldl treeStep []).map (evalEntry answer u) :=
    (map_foldl_treeStep answer u code []).symm
  rw [evalRun, hfold]
  rcases hdec : QueryTree.decode code with _ | tree
  · rcases hstack : code.foldl treeStep [] with _ | ⟨tree, _ | ⟨_, _⟩⟩
    · simp [QueryTree.eval]
    · have hne : tree.encode ≠ code := fun h ↦ by
        rw [← decode_eq_some_iff, hdec] at h
        cases h
      simp [evalEntry, hne, QueryTree.eval]
    · simp [QueryTree.eval]
  · have hcode := (decode_eq_some_iff code tree).mp hdec
    rw [← hcode, foldl_treeStep_encode]
    simp [evalEntry]

/-- Evaluating the referee coded by the first component against a computable family of
answers is computable. Invalid codes evaluate as the constant-zero tree. -/
private lemma computable_eval_decode {α : Type} [Primcodable α]
    (answer : α → Coordinate → Bool) (hanswer : Computable₂ answer) :
    Computable (fun x : QueryTree.Code × α ↦
      ((QueryTree.decode x.1).getD (.leaf 0)).eval (answer x.2)) := by
  have hstep : Computable₂ (fun (x : QueryTree.Code × α)
      (p : List (QueryTree.Code × ℕ) × (ℕ ⊕ Coordinate)) ↦ evalStep answer x.2 p.1 p.2) :=
    (computable₂_evalStep answer hanswer).comp (Computable.snd.comp Computable.fst)
      Computable.snd
  have hstack : Computable (fun x : QueryTree.Code × α ↦ x.1.foldl (evalStep answer x.2) []) :=
    Computable.list_foldl Computable.fst (Computable.const []) hstep
  have htop : Computable (fun x : QueryTree.Code × α ↦
      (x.1.foldl (evalStep answer x.2) []).head?.getD ([], 0)) :=
    Computable.option_getD (Primrec.list_head?.to_comp.comp hstack) (Computable.const ([], 0))
  have hlength : Computable (fun x : QueryTree.Code × α ↦
      decide ((x.1.foldl (evalStep answer x.2) []).length = 1)) :=
    Primrec.eq.decide.to_comp.comp (Computable.list_length.comp hstack) (Computable.const 1)
  have hcode : Computable (fun x : QueryTree.Code × α ↦
      decide (((x.1.foldl (evalStep answer x.2) []).head?.getD ([], 0)).1 = x.1)) :=
    Primrec.eq.decide.to_comp.comp (Computable.fst.comp htop) Computable.fst
  have hrun : Computable (fun x : QueryTree.Code × α ↦ evalRun answer x.1 x.2) :=
    (Computable.cond (Primrec.and.to_comp.comp hlength hcode) (Computable.snd.comp htop)
      (Computable.const 0)).of_eq (fun x ↦ by
        simp only [evalRun, ← Bool.decide_and, Bool.cond_decide])
  exact hrun.of_eq (fun x ↦ evalRun_eq answer x.1 x.2)

/-- The referee's output at a vector of counters is computable from the game code and the
counters. -/
private lemma computable_referee_eval :
    Computable (fun x : CounterGameCode × List ℕ ↦
      (decodeCounterGame x.1).referee.eval ((decodeCounterGame x.1).counterAnswer x.2)) := by
  have hcode : Computable (fun x : CounterGameCode × List ℕ ↦ (x.1.2.2.2.2.2.1, x)) :=
    (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))))).pair Computable.id
  exact ((computable_eval_decode _ computable₂_counterAnswer).comp hcode).of_eq (fun _ ↦ rfl)

/-! ### The active player -/

/-- The active player of a decoded position is computable from the codes of game and
position. -/
theorem computable_activePlayer :
    Computable (fun x : CounterGameCode × CounterPositionCode ↦
      let g := decodeCounterGame x.1
      g.activePlayer (decodeCounterPosition g x.2)) := by
  have hout : Computable (fun x : CounterGameCode × CounterPositionCode ↦
      (decodeCounterGame x.1).output (decodeCounterPosition (decodeCounterGame x.1) x.2)) :=
    (computable_referee_eval.comp
      (Computable.fst.pair (Computable.fst.comp Computable.snd))).of_eq (fun _ ↦ rfl)
  have htest := Primrec.eq.decide.to_comp.comp hout (computable_game_target.comp Computable.fst)
  have hplayer := computable_game_equalityPlayer.comp
    (Computable.fst : Computable (fun x : CounterGameCode × CounterPositionCode ↦ x.1))
  refine (Computable.cond htest (Primrec.not.to_comp.comp hplayer) hplayer).of_eq (fun x ↦ ?_)
  by_cases h : (decodeCounterGame x.1).output
      (decodeCounterPosition (decodeCounterGame x.1) x.2) = (decodeCounterGame x.1).target <;>
    simp [FiniteCounterGame.activePlayer, h]

/-! ### Legality of a move -/

/-- The objective of a player at an output, as a function of the game code, the player and the
output, is computable. -/
private lemma computable_objective :
    Computable (fun t : CounterGameCode × Bool × ℕ ↦
      (decodeCounterGame t.1).objective t.2.1 t.2.2) := by
  have hplayer : Computable (fun t : CounterGameCode × Bool × ℕ ↦
      decide (t.2.1 = (decodeCounterGame t.1).equalityPlayer)) :=
    Primrec.eq.decide.to_comp.comp (Computable.fst.comp Computable.snd)
      (computable_game_equalityPlayer.comp Computable.fst)
  have hout : Computable (fun t : CounterGameCode × Bool × ℕ ↦
      decide (t.2.2 = (decodeCounterGame t.1).target)) :=
    Primrec.eq.decide.to_comp.comp (Computable.snd.comp Computable.snd)
      (computable_game_target.comp Computable.fst)
  refine (Computable.cond hplayer hout (Primrec.not.to_comp.comp hout)).of_eq (fun t ↦ ?_)
  by_cases h : t.2.1 = (decodeCounterGame t.1).equalityPlayer <;>
    simp [FiniteCounterGame.objective, h]

/-- Adding a move to a vector of counters is computable. -/
theorem computable_addCounters :
    Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      (decodeCounterGame x.1.1).addCounters x.1.2.1 x.2) := by
  let X := (CounterGameCode × CounterPositionCode) × CounterMove
  have hcoordinates : Computable (fun x : X ↦ (decodeCounterGame x.1.1).coordinates) :=
    computable_game_coordinates.comp (Computable.fst.comp Computable.fst)
  have hrange : Computable (fun x : X ↦ List.range (decodeCounterGame x.1.1).coordinates.length) :=
    Primrec.list_range.to_comp.comp (Computable.list_length.comp hcoordinates)
  have hcounters : Computable₂ (fun (x : X) (i : ℕ) ↦ x.1.2.1[i]?.getD 0) := by
    have hl : Computable (fun p : X × ℕ ↦ p.1.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    exact Computable.option_getD (Computable.list_getElem?.comp hl Computable.snd)
      (Computable.const 0)
  have hmove : Computable₂ (fun (x : X) (i : ℕ) ↦ x.2[i]?.getD 0) := by
    have hm : Computable (fun p : X × ℕ ↦ p.1.2) := Computable.snd.comp Computable.fst
    exact Computable.option_getD (Computable.list_getElem?.comp hm Computable.snd)
      (Computable.const 0)
  have hsum : Computable₂ (fun (x : X) (i : ℕ) ↦ x.1.2.1[i]?.getD 0 + x.2[i]?.getD 0) :=
    Computable₂.comp Primrec.nat_add.to_comp hcounters hmove
  exact (Computable.list_map hrange hsum).of_eq (fun _ ↦ rfl)

/-- The length of a move equals the number of coordinates: this part of legality is
computable. -/
private lemma computable_move_length_eq :
    Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      decide (x.2.length = (decodeCounterGame x.1.1).coordinates.length)) :=
  Primrec.eq.decide.to_comp.comp (Computable.list_length.comp Computable.snd)
    (Computable.list_length.comp (computable_game_coordinates.comp
      (Computable.fst.comp Computable.fst)))

/-- Positivity of the sum of a move is computable. -/
private lemma computable_move_sum_pos :
    Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      decide (0 < x.2.sum)) := by
  have hzero : Computable (fun _ : (CounterGameCode × CounterPositionCode) × CounterMove ↦ 0) :=
    Computable.const 0
  have h := Computable₂.comp (PrimrecRel.decide Primrec.nat_lt).to_comp hzero
    (computable_nat_list_sum.comp Computable.snd)
  exact h

/-- Affordability of a move by the active player is computable. -/
private lemma computable_move_sum_le_remaining :
    Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      let g := decodeCounterGame x.1.1
      let p := decodeCounterPosition g x.1.2
      decide (x.2.sum ≤ p.remaining (g.activePlayer p))) := by
  let X := (CounterGameCode × CounterPositionCode) × CounterMove
  have hbudget : Computable (fun x : X ↦ (decodeCounterGame x.1.1).budget) :=
    computable_game_budget.comp (Computable.fst.comp Computable.fst)
  have hleft : Computable (fun x : X ↦ min x.1.2.2.1 (decodeCounterGame x.1.1).budget) :=
    Computable₂.comp Primrec.nat_min.to_comp
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))) hbudget
  have hright : Computable (fun x : X ↦ min x.1.2.2.2 (decodeCounterGame x.1.1).budget) :=
    Computable₂.comp Primrec.nat_min.to_comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))) hbudget
  have hactive := computable_activePlayer.comp (Computable.fst : Computable (fun x : X ↦ x.1))
  have hremaining := Computable.cond hactive hright hleft
  have hle := Computable₂.comp Primrec.nat_le.decide.to_comp
    (computable_nat_list_sum.comp Computable.snd) hremaining
  refine hle.of_eq (fun x ↦ ?_)
  dsimp only
  cases (decodeCounterGame x.1.1).activePlayer
    (decodeCounterPosition (decodeCounterGame x.1.1) x.1.2) <;> rfl

/-- The active player's objective holding after a move is computable. -/
private lemma computable_move_objective :
    Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      let g := decodeCounterGame x.1.1
      let p := decodeCounterPosition g x.1.2
      decide (g.objective (g.activePlayer p)
        (g.referee.eval (g.counterAnswer (g.addCounters p.counters x.2))) = true)) := by
  let X := (CounterGameCode × CounterPositionCode) × CounterMove
  have hactive := computable_activePlayer.comp (Computable.fst : Computable (fun x : X ↦ x.1))
  have hvalue := computable_referee_eval.comp
    ((Computable.fst.comp Computable.fst).pair computable_addCounters)
  have hobjective := computable_objective.comp (Computable.fst.comp Computable.fst |>.pair
    (hactive.pair hvalue))
  exact (Primrec.eq.decide.to_comp.comp hobjective (Computable.const true)).of_eq
    (fun _ ↦ rfl)

/-- Legality of a move in a decoded game is computable from the codes of game, position and
move. -/
theorem computable_decide_legalMove :
    Computable (fun x : (CounterGameCode × CounterPositionCode) × CounterMove ↦
      let g := decodeCounterGame x.1.1
      decide (g.LegalMove (decodeCounterPosition g x.1.2) x.2)) := by
  have hall := Computable₂.comp Primrec.and.to_comp computable_move_length_eq
    (Computable₂.comp Primrec.and.to_comp computable_move_sum_pos
      (Computable₂.comp Primrec.and.to_comp computable_move_sum_le_remaining
        computable_move_objective))
  refine hall.of_eq (fun x ↦ ?_)
  simp only [← Bool.decide_and]
  exact decide_eq_decide.mpr Iff.rfl

end Kolmogorov.Milovanov
