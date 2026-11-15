/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Effectivity.GameTable
import KolmogorovMathlib.RandomStrings.TTMeet2014.Structure

/-!
# Effectivity of the construction through a list based state

The twin below keeps every field read by `step` and erases the rational accounting fields.
Finite sets are represented by lists; the unbounded family of requirements is a padded list.
`Tracks` relates the twin to the original construction, without any well formedness assumption.
The final computability theorems follow from simulation and computable iteration of the twin step.

Of `Effectivity/GameTable.lean`, only its six-declaration interface is used.  The design is
described in `docs/random_strings_tt_meet_2014.md`, section 8.
-/

namespace Kolmogorov.RandomStrings.TTMeet
namespace StateTwin

/-- A board game with its target represented by a list. -/
structure BoardGameL where
  /-- The board on which this game is played. -/
  board : Fin 3
  /-- The target vectors; multiplicities have no meaning. -/
  target : List (List Bool)
  /-- The opponent's budget. -/
  oppLimit : ℕ
  /-- Our budget. -/
  ourLimit : ℕ
  /-- Our spending so far. -/
  spent : ℕ

/-- A play with list based board games. -/
structure PlayL where
  /-- The arena of the play. -/
  arena : Arena
  /-- The stage at which the play started. -/
  start : ℕ
  /-- The kind of the play. -/
  kind : PlayKind
  /-- The games being played, in the original order. -/
  games : List BoardGameL

/-- The observable part of the state of a requirement. -/
structure ReqStateL where
  /-- The current starting exponent. -/
  c : Option ℕ := none
  /-- The truth tables examined so far. -/
  tables : List TTable := []
  /-- The remembered agreement and its base stages. -/
  baseline : Option Baseline := none
  /-- The play in progress. -/
  play : Option PlayL := none
  /-- The most recent visit. -/
  lastVisit : ℕ := 0
  /-- The most recent action. -/
  lastActed : ℕ := 0

/-- The observable construction state with finitely stored requirements. -/
structure ConStateL where
  /-- The number of completed stages. -/
  stage : ℕ := 0
  /-- The strings compressed by us, on each board. -/
  ours : Fin 3 → List Str := fun _ => []
  /-- The lower bound on the next starting exponent. -/
  nextC : ℕ := 0
  /-- The finitely stored requirement states; missing entries mean the default state. -/
  req : List ReqStateL := []

/-- An arena is encoded by its tables and scale. -/
def Arena.equiv : Arena ≃ List TTable × ℕ where
  toFun ar := (ar.tables, ar.scale)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The explicit arena encoding. -/
instance arenaPrimcodable : Primcodable Arena := Primcodable.ofEquiv _ Arena.equiv

/-- Primitive recursive access to an arena's tables. -/
theorem Arena.tables_primrec : Primrec Arena.tables :=
  (Primrec.fst.comp (Primrec.of_equiv (e := Arena.equiv))).of_eq fun _ => rfl

/-- Primitive recursive access to an arena's scale. -/
theorem Arena.scale_primrec : Primrec Arena.scale :=
  (Primrec.snd.comp (Primrec.of_equiv (e := Arena.equiv))).of_eq fun _ => rfl

/-- Primitive recursive construction of an arena. -/
theorem Arena.mk_primrec : Primrec fun p : List TTable × ℕ => (⟨p.1, p.2⟩ : Arena) :=
  Primrec.of_equiv_symm (e := Arena.equiv)

/-- A nested option encoding of the three play kinds. -/
def PlayKind.equiv : PlayKind ≃ Option (Option (List Bool × Fin 3)) where
  toFun
    | .balanced => none
    | .unbalanced => some none
    | .stacked σ j => some (some (σ, j))
  invFun
    | none => .balanced
    | some none => .unbalanced
    | some (some (σ, j)) => .stacked σ j
  left_inv k := by cases k <;> rfl
  right_inv p := by rcases p with _ | (_ | ⟨σ, j⟩) <;> rfl

/-- The explicit play kind encoding. -/
instance playKindPrimcodable : Primcodable PlayKind :=
  Primcodable.ofEquiv _ PlayKind.equiv

/-- Primitive recursive encoding of a play kind. -/
theorem PlayKind.code_primrec : Primrec PlayKind.equiv :=
  Primrec.of_equiv (e := PlayKind.equiv)

/-- Primitive recursive decoding of a play kind. -/
theorem PlayKind.decode_primrec : Primrec PlayKind.equiv.symm :=
  Primrec.of_equiv_symm (e := PlayKind.equiv)

/-- The balanced play-kind constructor is primitive recursive. -/
theorem PlayKind.balanced_primrec : Primrec fun _ : Unit => PlayKind.balanced :=
  Primrec.const _

/-- The unbalanced play-kind constructor is primitive recursive. -/
theorem PlayKind.unbalanced_primrec : Primrec fun _ : Unit => PlayKind.unbalanced :=
  Primrec.const _

/-- Primitive recursive construction of a stacked play kind. -/
theorem PlayKind.stacked_primrec :
    Primrec fun p : List Bool × Fin 3 => PlayKind.stacked p.1 p.2 :=
  (PlayKind.decode_primrec.comp (Primrec.option_some.comp Primrec.option_some)).of_eq
    fun _ => rfl

/-- A baseline is encoded by its vector and its three base stages. -/
def Baseline.equiv : Baseline ≃ List Bool × (Fin 3 → ℕ) where
  toFun bl := (bl.σ, bl.base)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The explicit baseline encoding, using `Primcodable.finArrow`. -/
instance baselinePrimcodable : Primcodable Baseline :=
  Primcodable.ofEquiv _ Baseline.equiv

/-- Primitive recursive access to the agreed vector. -/
theorem Baseline.σ_primrec : Primrec Baseline.σ :=
  (Primrec.fst.comp (Primrec.of_equiv (e := Baseline.equiv))).of_eq fun _ => rfl

/-- Primitive recursive access to the three base stages. -/
theorem Baseline.base_primrec : Primrec Baseline.base :=
  (Primrec.snd.comp (Primrec.of_equiv (e := Baseline.equiv))).of_eq fun _ => rfl

/-- Primitive recursive construction of a baseline. -/
theorem Baseline.mk_primrec :
    Primrec fun p : List Bool × (Fin 3 → ℕ) => (⟨p.1, p.2⟩ : Baseline) :=
  Primrec.of_equiv_symm (e := Baseline.equiv)

/-- The product encoding of `BoardGameL`. -/
def BoardGameL.equiv : BoardGameL ≃ Fin 3 × List (List Bool) × ℕ × ℕ × ℕ where
  toFun x := (x.board, x.target, x.oppLimit, x.ourLimit, x.spent)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The explicit primitive coding of `BoardGameL`. -/
instance boardGameLPrimcodable : Primcodable BoardGameL :=
  Primcodable.ofEquiv _ BoardGameL.equiv

/-- Primitive recursive projection of `BoardGameL.board`. -/
theorem BoardGameL.board_primrec : Primrec BoardGameL.board :=
  (Primrec.fst.comp (Primrec.of_equiv (e := BoardGameL.equiv))).of_eq fun _ => rfl

/-- Primitive recursive projection of `BoardGameL.target`. -/
theorem BoardGameL.target_primrec : Primrec BoardGameL.target :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := BoardGameL.equiv)))).of_eq fun _ =>
    rfl

/-- Primitive recursive projection of `BoardGameL.oppLimit`. -/
theorem BoardGameL.oppLimit_primrec : Primrec BoardGameL.oppLimit :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e :=
    BoardGameL.equiv))))).of_eq fun _ => rfl

/-- Primitive recursive projection of `BoardGameL.ourLimit`. -/
theorem BoardGameL.ourLimit_primrec : Primrec BoardGameL.ourLimit :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e :=
    BoardGameL.equiv)))))).of_eq fun _ => rfl

/-- Primitive recursive projection of `BoardGameL.spent`. -/
theorem BoardGameL.spent_primrec : Primrec BoardGameL.spent :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e :=
    BoardGameL.equiv)))))).of_eq fun _ => rfl

/-- Primitive recursive construction of `BoardGameL` from its product encoding. -/
theorem BoardGameL.mk_primrec :
    Primrec fun p : Fin 3 × List (List Bool) × ℕ × ℕ × ℕ => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1,
      p.2.2.2.2⟩ : BoardGameL) :=
  Primrec.of_equiv_symm (e := BoardGameL.equiv)

/-- The product encoding of `PlayL`. -/
def PlayL.equiv : PlayL ≃ Arena × ℕ × PlayKind × List BoardGameL where
  toFun x := (x.arena, x.start, x.kind, x.games)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The explicit primitive coding of `PlayL`. -/
instance playLPrimcodable : Primcodable PlayL :=
  Primcodable.ofEquiv _ PlayL.equiv

/-- Primitive recursive projection of `PlayL.arena`. -/
theorem PlayL.arena_primrec : Primrec PlayL.arena :=
  (Primrec.fst.comp (Primrec.of_equiv (e := PlayL.equiv))).of_eq fun _ => rfl

/-- Primitive recursive projection of `PlayL.start`. -/
theorem PlayL.start_primrec : Primrec PlayL.start :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := PlayL.equiv)))).of_eq fun _ => rfl

/-- Primitive recursive projection of `PlayL.kind`. -/
theorem PlayL.kind_primrec : Primrec PlayL.kind :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e :=
    PlayL.equiv))))).of_eq fun _ => rfl

/-- Primitive recursive projection of `PlayL.games`. -/
theorem PlayL.games_primrec : Primrec PlayL.games :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e :=
    PlayL.equiv))))).of_eq fun _ => rfl

/-- Primitive recursive construction of `PlayL` from its product encoding. -/
theorem PlayL.mk_primrec :
    Primrec fun p : Arena × ℕ × PlayKind × List BoardGameL => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩ :
      PlayL) :=
  Primrec.of_equiv_symm (e := PlayL.equiv)

/-- The product encoding of `ReqStateL`. -/
def ReqStateL.equiv : ReqStateL ≃ Option ℕ × List TTable × Option Baseline × Option PlayL × ℕ × ℕ
    where
  toFun x := (x.c, x.tables, x.baseline, x.play, x.lastVisit, x.lastActed)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The explicit primitive coding of `ReqStateL`. -/
instance reqStateLPrimcodable : Primcodable ReqStateL :=
  Primcodable.ofEquiv _ ReqStateL.equiv

/-- Primitive recursive projection of `ReqStateL.c`. -/
theorem ReqStateL.c_primrec : Primrec ReqStateL.c :=
  (Primrec.fst.comp (Primrec.of_equiv (e := ReqStateL.equiv))).of_eq fun _ => rfl

/-- Primitive recursive projection of `ReqStateL.tables`. -/
theorem ReqStateL.tables_primrec : Primrec ReqStateL.tables :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := ReqStateL.equiv)))).of_eq fun _ => rfl

/-- Primitive recursive projection of `ReqStateL.baseline`. -/
theorem ReqStateL.baseline_primrec : Primrec ReqStateL.baseline :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e :=
    ReqStateL.equiv))))).of_eq fun _ => rfl

/-- Primitive recursive projection of `ReqStateL.play`. -/
theorem ReqStateL.play_primrec : Primrec ReqStateL.play :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e :=
    ReqStateL.equiv)))))).of_eq fun _ => rfl

/-- Primitive recursive projection of `ReqStateL.lastVisit`. -/
theorem ReqStateL.lastVisit_primrec : Primrec ReqStateL.lastVisit :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.of_equiv (e := ReqStateL.equiv))))))).of_eq fun _ => rfl

/-- Primitive recursive projection of `ReqStateL.lastActed`. -/
theorem ReqStateL.lastActed_primrec : Primrec ReqStateL.lastActed :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.of_equiv (e := ReqStateL.equiv))))))).of_eq fun _ => rfl

/-- Primitive recursive construction of `ReqStateL` from its product encoding. -/
theorem ReqStateL.mk_primrec :
    Primrec fun p : Option ℕ × List TTable × Option Baseline × Option PlayL × ℕ × ℕ => (⟨p.1,
      p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩ : ReqStateL) :=
  Primrec.of_equiv_symm (e := ReqStateL.equiv)

/-- The product encoding of `ConStateL`. -/
def ConStateL.equiv : ConStateL ≃ ℕ × (Fin 3 → List Str) × ℕ × List ReqStateL where
  toFun x := (x.stage, x.ours, x.nextC, x.req)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The explicit primitive coding of `ConStateL`. -/
instance conStateLPrimcodable : Primcodable ConStateL :=
  Primcodable.ofEquiv _ ConStateL.equiv

/-- Primitive recursive projection of `ConStateL.stage`. -/
theorem ConStateL.stage_primrec : Primrec ConStateL.stage :=
  (Primrec.fst.comp (Primrec.of_equiv (e := ConStateL.equiv))).of_eq fun _ => rfl

/-- Primitive recursive projection of `ConStateL.ours`. -/
theorem ConStateL.ours_primrec : Primrec ConStateL.ours :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := ConStateL.equiv)))).of_eq fun _ => rfl

/-- Primitive recursive projection of `ConStateL.nextC`. -/
theorem ConStateL.nextC_primrec : Primrec ConStateL.nextC :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e :=
    ConStateL.equiv))))).of_eq fun _ => rfl

/-- Primitive recursive projection of `ConStateL.req`. -/
theorem ConStateL.req_primrec : Primrec ConStateL.req :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e :=
    ConStateL.equiv))))).of_eq fun _ => rfl

/-- Primitive recursive construction of `ConStateL` from its product encoding. -/
theorem ConStateL.mk_primrec :
    Primrec fun p : ℕ × (Fin 3 → List Str) × ℕ × List ReqStateL => (⟨p.1, p.2.1, p.2.2.1,
      p.2.2.2⟩ : ConStateL) :=
  Primrec.of_equiv_symm (e := ConStateL.equiv)

/-- Forget the list representation of the target. -/
def BoardGameL.toBoardGame (g : BoardGameL) : BoardGame :=
  ⟨g.board, g.target.toFinset, g.oppLimit, g.ourLimit, g.spent⟩

/-- Forget the list representations in a play. -/
def PlayL.toPlay (pl : PlayL) : Play :=
  ⟨pl.arena, pl.start, pl.kind, pl.games.map BoardGameL.toBoardGame⟩

/-- Missing requirement entries have the default state. -/
def reqL (st : ConStateL) (i : ℕ) : ReqStateL := st.req.getD i {}

/-- Pad a list before updating a requirement. -/
def setReq (l : List ReqStateL) (i : ℕ) (x : ReqStateL) : List ReqStateL :=
  (l ++ List.replicate (i + 1 - l.length) ({} : ReqStateL)).set i x

/-- Reading an updated entry returns the new state. -/
theorem getD_setReq_self (l : List ReqStateL) (i : ℕ) (x : ReqStateL) :
    (setReq l i x).getD i {} = x := by
  unfold setReq List.getD
  rw [List.getElem?_set_self (by simp; omega)]
  rfl

/-- Reading a different entry is unaffected by padding and updating. -/
theorem getD_setReq_ne (l : List ReqStateL) (i k : ℕ) (x : ReqStateL) (h : i ≠ k) :
    (setReq l i x).getD k {} = l.getD k {} := by
  unfold setReq
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]
  change (l ++ List.replicate (i + 1 - l.length) ({} : ReqStateL)).getD k {} = _
  by_cases hk : k < l.length
  · exact List.getD_append _ _ _ _ hk
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    change _ = l.getD k {}
    rw [List.getD_eq_default l _ (by omega)]
    simp [List.getD_eq_getElem?_getD]

/-- A vector complement represented by a filter of `allVec`. -/
def complL (n : ℕ) (S : List (List Bool)) : List (List Bool) :=
  (allVec n).filter fun σ => decide (σ ∉ S)

/-- An intersection represented by filtering the left operand. -/
def interL (S T : List (List Bool)) : List (List Bool) :=
  S.filter fun σ => decide (σ ∈ T)

/-- A difference of string lists, interpreted as a difference of finite sets. -/
def diffL (A B : List Str) : List Str := A.filter fun τ => decide (τ ∉ B)

/-- A list complement represents the finite set complement. -/
theorem complL_toFinset (n : ℕ) (S : List (List Bool)) :
    (complL n S).toFinset = vectors n \ S.toFinset := by
  ext σ
  simp [complL, vectors]

/-- A list intersection represents intersection of finite sets. -/
theorem interL_toFinset (S T : List (List Bool)) :
    (interL S T).toFinset = S.toFinset ∩ T.toFinset := by
  ext σ
  simp [interL]

/-- A list difference represents difference of finite sets. -/
theorem diffL_toFinset (A B : List Str) :
    (diffL A B).toFinset = A.toFinset \ B.toFinset := by
  ext τ
  simp [diffL]

/-- Charging a deduplicated list charges its finite set exactly. -/
theorem costU_dedup (ar : Arena) (l : List Str) :
    costU ar.scale l.dedup = cost ar.w l.toFinset := by
  simpa [Arena.w] using (costU_eq (N := ar.scale) (List.nodup_dedup l))

/-- A string is alive exactly when neither player has compressed it. -/
def aliveL (I : Input) (ours : Fin 3 → List Str) (t : ℕ) (j : Fin 3) (τ : Str) : Bool :=
  !(I.opp t τ) && !(decide (τ ∈ ours j))

/-- The position in the same list order as `ConState.positionList`. -/
def positionL (I : Input) (ours : Fin 3 → List Str) (ar : Arena) (t : ℕ) (j : Fin 3) :
    List Str := ar.boardList.filter (aliveL I ours t j)

/-- Opponent spending, with each string on the arena board charged once. -/
def oppSpendL (I : Input) (ar : Arena) (t₀ t : ℕ) : ℕ :=
  costU ar.scale (ar.boardList.filter fun τ => I.opp t τ && !(I.opp t₀ τ))

/-- Encoded top verdict: split, meet, principal, or `none` for stuck. -/
abbrev TopOutcomeL :=
  Option ((Fin 3 × Fin 3 × List (List Bool)) ⊕
    ((List (List Bool) × List (List Bool)) ⊕ List Bool))

/-- Interpret the encoded verdict in the original construction. -/
def toTopOutcome : TopOutcomeL → TopOutcome
  | none => .stuck
  | some (.inl (j, k, S)) => .split j k S.toFinset
  | some (.inr (.inl (S, T))) => .meet S.toFinset T.toFinset
  | some (.inr (.inr σ)) => .principal σ

/-- The ordered search for a split at the top of the stack. -/
def splitSearchL (ar : Arena) (A : Fin 3 → List Str) (E : ℕ) :
    Option ((Fin 3 × Fin 3) × List (List Bool)) :=
  ((allBoards.product allBoards).product (allVec ar.tables.length).sublists).find? fun q =>
    decide (q.1.1 ≠ q.1.2) && forcesB ar q.2 (A q.1.1) E E &&
      forcesB ar (complL ar.tables.length q.2) (A q.1.2) E E

/-- The ordered search for a failed intersection at the top of the stack. -/
def meetSearchL (ar : Arena) (A : Fin 3 → List Str) (E : ℕ) :
    Option (List (List Bool) × List (List Bool)) :=
  ((allVec ar.tables.length).sublists.product (allVec ar.tables.length).sublists).find? fun q =>
    forcesB ar q.1 (A 0) E E && forcesB ar q.2 (A 0) E E &&
      !(forcesB ar (interL q.1 q.2) (A 0) E E)

/-- The ordered search for a principal generator at the top of the stack. -/
def principalSearchL (ar : Arena) (A : Fin 3 → List Str) (E : ℕ) : Option (List Bool) :=
  (allVec ar.tables.length).find? fun σ => forcesB ar [σ] (A 0) E E

/-- Examine the symmetric game, with precisely the original three searches and their order. -/
def topOutcomeL (ar : Arena) (A : Fin 3 → List Str) (E : ℕ) : TopOutcomeL :=
  match splitSearchL ar A E with
  | some q => some (.inl (q.1.1, q.1.2, q.2))
  | none =>
    match meetSearchL ar A E with
    | some q => some (.inr (.inl q))
    | none => (principalSearchL ar A E).map fun σ => .inr (.inr σ)

/-- Search the stack levels in the same order as `firstStackSplit`. -/
def firstStackSplitL (ar : Arena) (A : Fin 3 → List Str) (σ : List Bool) :
    Option (ℕ × Fin 3) :=
  let p : ℕ → Fin 3 → Bool := fun ℓ j =>
    forcesB ar (complL ar.tables.length [σ]) (A j)
      (levelBudget ar.tables ℓ) (levelBudget ar.tables ℓ)
  match (List.range (maxLen ar.tables)).find? (fun r => allBoards.any (p (r + 1))) with
  | none => none
  | some r => (allBoards.find? (p (r + 1))).map fun j => (r + 1, j)

/-- The queries of a requirement as a duplicate free list. -/
def boardOfL (tables : List TTable) : List Str := (arenaOf 0 tables).boardList

/-- Whether an opponent move has hit this requirement since its last visit. -/
def pendingHitL (I : Input) (rs : ReqStateL) (t : ℕ) : Bool :=
  (boardOfL rs.tables).any fun τ => I.opp t τ && !(I.opp rs.lastVisit τ)

/-- The next exponent, depending only on the observable lower bound. -/
def newCL (nextC i t : ℕ) : ℕ :=
  max (i + 7) (max nextC ((definedStrings i t).foldr (fun z n => max z.length n) 0))

/-- The original reset test on the finitely stored requirements. -/
def mustResetL (I : Input) (st : ConStateL) (i e t : ℕ) : Bool :=
  decide (e = 0) || (reqL st i).c.isNone ||
    (List.range i).any fun m =>
      decide ((reqL st i).lastVisit < (reqL st m).lastActed) ||
        pendingHitL I (reqL st m) t

/-- Case 1 with the accounting fields erased. -/
def caseOneL (st : ConStateL) (i t : ℕ) : ReqStateL × ℕ :=
  let c' := newCL st.nextC i t
  ({ reqL st i with c := some c', baseline := none, play := none }, c' + 2)

/-- A symmetric game with a list target. -/
def symGameL (j : Fin 3) (S : List (List Bool)) (E : ℕ) : BoardGameL :=
  ⟨j, S, E, E, 0⟩

/-- Start balanced games for the encoded split or meet verdict. -/
def balancedPlayL (ar : Arena) (t E : ℕ) : TopOutcomeL → Option PlayL
  | some (.inl (j, k, S)) =>
    some ⟨ar, t, .balanced, [symGameL j S E, symGameL k (complL ar.tables.length S) E]⟩
  | some (.inr (.inl (S, T))) =>
    some ⟨ar, t, .balanced, [symGameL 0 S E, symGameL 1 T E,
      symGameL 2 (complL ar.tables.length (interL S T)) E]⟩
  | _ => none

/-- Construct the unbalanced knight and bishop games from their finite data. -/
def unbalancedPlayL (ar : Arena) (t E a : ℕ) (σ : List Bool) (j k : Fin 3) : PlayL :=
  ⟨ar, t, .unbalanced,
    [symGameL j (complL ar.tables.length [σ]) E, ⟨k, [σ], a, E, 0⟩]⟩

/-- Remember a principal verdict or start balanced games during a fresh examination. -/
def examineVerdictL (ar : Arena) (t E : ℕ) (rs : ReqStateL) (v : TopOutcomeL) :
    (ReqStateL × Bool) ⊕ (ReqStateL × List Bool) :=
  match v with
  | some (.inr (.inr σ)) =>
    .inr ({ rs with baseline := some ⟨σ, fun _ => t⟩ }, σ)
  | v =>
    match balancedPlayL ar t E v with
    | some pl => .inl ({ rs with play := some pl }, true)
    | none => .inl (rs, false)

/-- The observable first part of Case 2, including the baseline repair. -/
def examineTopL (I : Input) (st : ConStateL) (_i t c : ℕ) (rs : ReqStateL) :
    (ReqStateL × Bool) ⊕ (ReqStateL × List Bool) :=
  let ar := arenaOf c rs.tables
  let E := levelBudget rs.tables 0
  let A := positionL I st.ours ar t
  match rs.baseline with
  | some bl =>
    if allBoards.any (fun j => decide (E < oppSpendL I ar (bl.base j) t)) then
      .inl ({ rs with baseline := none }, false)
    else
      match allBoards.find? (fun j => forcesB ar (complL rs.tables.length [bl.σ]) (A j) E E) with
      | some j =>
        let k := otherBoard j
        .inl ({ rs with
          play := some (unbalancedPlayL ar t E
            (E - oppSpendL I ar (bl.base k) t) bl.σ j k) }, true)
      | none => .inr ({ rs with baseline := some ⟨bl.σ, fun _ => t⟩ }, bl.σ)
  | none => examineVerdictL ar t E rs (topOutcomeL ar A E)

/-- Consume the top verdict on newly extended tables. -/
def extensionVerdictL (ar : Arena) (t E : ℕ) (rs : ReqStateL) (tables : List TTable)
    (v : TopOutcomeL) : ReqStateL × Bool :=
  match v with
  | some (.inr (.inr σ)) =>
    ({ rs with tables := tables, baseline := some ⟨σ, fun _ => t⟩ }, true)
  | v =>
    match balancedPlayL ar t E v with
    | some pl => ({ rs with tables := tables, baseline := none, play := some pl }, true)
    | none => (rs, false)

/-- Examine the newly extended tables in Case 2. -/
def caseTwoTableL (I : Input) (st : ConStateL) (t c : ℕ)
    (rs rs₁ : ReqStateL) (tbl : TTable) : ReqStateL × Bool :=
  let tables' := rs.tables ++ [tbl]
  let ar' := arenaOf c tables'
  let E' := levelBudget tables' 0
  extensionVerdictL ar' t E' rs₁ tables'
    (topOutcomeL ar' (positionL I st.ours ar' t) E')

/-- Compare an agreed vector with X and, if possible, examine one further table. -/
def caseTwoExtendL (I : Input) (st : ConStateL) (i t c : ℕ)
    (rs rs₁ : ReqStateL) (σ : List Bool) : ReqStateL × Bool :=
  if σ ≠ xPrefix I t rs.tables.length then (rs₁, false) else
  match tableAt i rs.tables.length t with
  | none => (rs₁, false)
  | some tbl => caseTwoTableL I st t c rs rs₁ tbl

/-- Continue Case 2 after an examination has produced an agreed vector. -/
def caseTwoAgreeL (I : Input) (st : ConStateL) (i t c : ℕ)
    (rs rs₁ : ReqStateL) (σ : List Bool) : ReqStateL × Bool :=
  let n := rs.tables.length
  let ar := arenaOf c rs.tables
  let A := positionL I st.ours ar t
  match firstStackSplitL ar A σ with
  | some (ℓ, j) =>
    let k := otherBoard j
    let Eℓ := levelBudget rs.tables ℓ
    let Eℓ' := levelBudget rs.tables (ℓ - 1)
    ({ rs₁ with
      play := some ⟨ar, t, .stacked σ (thirdBoard j k),
        [symGameL j (complL n [σ]) Eℓ, symGameL k [σ] Eℓ']⟩ }, true)
  | none => caseTwoExtendL I st i t c rs rs₁ σ

/-- Case 2 with list based positions and targets. -/
def caseTwoL (I : Input) (st : ConStateL) (i t c : ℕ) (rs : ReqStateL) : ReqStateL × Bool :=
  match examineTopL I st i t c rs with
  | .inl r => r
  | .inr (rs₁, σ) => caseTwoAgreeL I st i t c rs rs₁ σ

/-- The response predicate; deduplication makes set costs exact even on repeated list entries. -/
def respondOkL (ar : Arena) (g : BoardGameL) (La : List Str) (a b : ℕ)
    (p : List Str) : Bool :=
  decide (costU ar.scale p.dedup ≤ b) &&
    (if p = [] then decide (valueL ar La ∈ g.target) && forcesB ar g.target La a b
     else forcesB ar g.target (diffL La p) a (b - costU ar.scale p.dedup))

/-- Search the sublists in precisely the original response order. -/
def respondL (ar : Arena) (g : BoardGameL) (La : List Str) (a b : ℕ) : List Str :=
  (La.sublists.find? (respondOkL ar g La a b)).getD []

/-- The ordered responses of the participating board games in Case 3a. -/
def movesL (I : Input) (ours : Fin 3 → List Str) (ar : Arena) (t lam : ℕ)
    (games : List BoardGameL) : List (BoardGameL × List Str) :=
  games.map fun g => (g, respondL ar g (positionL I ours ar t g.board)
    (g.oppLimit - lam) (g.ourLimit - g.spent))

/-- Charge each game's response once, in arena units. -/
def advanceGamesL (ar : Arena) (moves : List (BoardGameL × List Str)) : List BoardGameL :=
  moves.map fun q => { q.1 with spent := q.1.spent + costU ar.scale q.2.dedup }

/-- Add the responses to the relevant boards in the original fold order. -/
def mergeMovesL (ours : Fin 3 → List Str) (moves : List (BoardGameL × List Str)) :
    Fin 3 → List Str := fun j =>
  moves.foldr (fun q acc => if q.1.board = j then q.2 ++ acc else acc) (ours j)

/-- The observable response and spending updates of Case 3a. -/
def caseThreeMoveL (I : Input) (st : ConStateL) (t : ℕ) (rs : ReqStateL)
    (pl : PlayL) (lam : ℕ) : ReqStateL × (Fin 3 → List Str) × Bool :=
  let moves := movesL I st.ours pl.arena t lam pl.games
  ({ rs with play := some { pl with games := advanceGamesL pl.arena moves } },
    mergeMovesL st.ours moves, moves.any fun q => decide (q.2 ≠ []))

/-- Keep a bishop's base stage and refresh the other two base stages. -/
def bishopBaselineL (bl : Baseline) (bishop : Fin 3) (t : ℕ) : Baseline :=
  { bl with base := fun j => if j = bishop then bl.base j else t }

/-- The knight search and bishop baseline update of Case 3b. -/
def caseThreeBishopL (I : Input) (st : ConStateL) (t : ℕ) (rs : ReqStateL)
    (pl : PlayL) (lam : ℕ) (σ : List Bool) (bishop : Fin 3) :
    ReqStateL × (Fin 3 → List Str) × Bool :=
  let ar := pl.arena
  let E := levelBudget ar.tables 0
  let knights := pl.games.map BoardGameL.board
  let A := positionL I st.ours ar t
  match knights.find? (fun j => forcesB ar (complL ar.tables.length [σ]) (A j) E E) with
  | some j =>
    ({ rs with
      play := some (unbalancedPlayL ar t E (E - lam) σ j bishop) },
      st.ours, true)
  | none =>
    ({ rs with play := none, baseline := rs.baseline.map fun bl =>
      bishopBaselineL bl bishop t }, st.ours, true)

/-- Clear the observable agreement and play in Case 3c. -/
def caseThreeStopL (st : ConStateL) (rs : ReqStateL) :
    ReqStateL × (Fin 3 → List Str) × Bool :=
  ({ rs with play := none, baseline := none }, st.ours, true)

/-- Choose between the bishop continuation and stopping after a game limit is exceeded. -/
def caseThreeAfterL (I : Input) (st : ConStateL) (t : ℕ) (rs : ReqStateL)
    (pl : PlayL) (lam : ℕ) : ReqStateL × (Fin 3 → List Str) × Bool :=
  match pl.kind with
  | .stacked σ bishop =>
    if lam ≤ levelBudget pl.arena.tables 0 then
      caseThreeBishopL I st t rs pl lam σ bishop
    else caseThreeStopL st rs
  | _ => caseThreeStopL st rs

/-- Case 3 with all the accounting data erased. -/
def caseThreeL (I : Input) (st : ConStateL) (_i t _c : ℕ) (rs : ReqStateL) (pl : PlayL) :
    ReqStateL × (Fin 3 → List Str) × Bool :=
  let ar := pl.arena
  let lam := oppSpendL I ar pl.start t
  let limit := pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget ar.tables 0)
  if lam ≤ limit then caseThreeMoveL I st t rs pl lam
  else caseThreeAfterL I st t rs pl lam

/-- The reset output of the stage case distinction. -/
def resetCoreL (st : ConStateL) : ReqStateL × (Fin 3 → List Str) × ℕ × Bool :=
  let r := caseOneL st (Nat.unpair st.stage).1 (st.stage + 1)
  (r.1, st.ours, r.2, true)

/-- Continue the stage after the reset test has failed. -/
def continueCoreL (I : Input) (st : ConStateL) :
    ReqStateL × (Fin 3 → List Str) × ℕ × Bool :=
  let t := st.stage + 1
  let i := (Nat.unpair st.stage).1
  let rs := reqL st i
  match rs.c with
  | none => (rs, st.ours, st.nextC, false)
  | some c =>
    match rs.play with
    | none =>
      let r := caseTwoL I st i t c rs
      (r.1, st.ours, st.nextC, r.2)
    | some pl =>
      let r := caseThreeL I st i t c rs pl
      (r.1, r.2.1, st.nextC, r.2.2)

/-- The original stage case distinction on observable data. -/
def stepCoreL (I : Input) (st : ConStateL) :
    ReqStateL × (Fin 3 → List Str) × ℕ × Bool :=
  if mustResetL I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2 (st.stage + 1) then
    resetCoreL st
  else continueCoreL I st

/-- Store a core result and update the visited requirement's timestamps. -/
def finishStepL (st : ConStateL) (r : ReqStateL × (Fin 3 → List Str) × ℕ × Bool)
    (hit : Bool) : ConStateL :=
  let t := st.stage + 1
  { stage := t
    ours := r.2.1
    nextC := r.2.2.1
    req := setReq st.req (Nat.unpair st.stage).1
      { r.1 with
        lastVisit := t
        lastActed := if r.2.2.2 || hit then t else r.1.lastActed } }

/-- Complete a visit and pad the finitely stored requirement array when necessary. -/
def stepL (I : Input) (st : ConStateL) : ConStateL :=
  finishStepL st (stepCoreL I st)
    (pendingHitL I (reqL st (Nat.unpair st.stage).1) (st.stage + 1))

/-- Iterate the observable step in the form required by `Computable.nat_rec`. -/
def stateAtL (I : Input) : ℕ → ConStateL :=
  fun s => Nat.rec {} (fun _ st => stepL I st) s

/-- Read a board's enumeration from the twin. -/
def oursBL (I : Input) (j : Fin 3) (s : ℕ) (τ : Str) : Bool :=
  decide (τ ∈ (stateAtL I s).ours j)

/-- Read an agreed bit from the twin. -/
def agreedBitL (I : Input) (i s k : ℕ) : Option Bool :=
  (reqL (stateAtL I s) i).baseline.bind fun bl => bl.σ[k]?

/-! ## Simulation of the original state -/

/-- Equality of all observable fields of a requirement. -/
structure TracksReq (rsL : ReqStateL) (rs : ReqState) : Prop where
  /-- Equality of current exponents. -/
  c : rsL.c = rs.c
  /-- Equality of examined truth tables. -/
  tables : rsL.tables = rs.tables
  /-- Equality of the remembered baseline. -/
  baseline : rsL.baseline = rs.baseline
  /-- Equality of the plays after interpreting the list targets. -/
  play : rsL.play.map PlayL.toPlay = rs.play
  /-- Equality of the last visit stages. -/
  lastVisit : rsL.lastVisit = rs.lastVisit
  /-- Equality of the last action stages. -/
  lastActed : rsL.lastActed = rs.lastActed

/-- The list state represents precisely the observable part of the original state. -/
structure Tracks (stL : ConStateL) (st : ConState) : Prop where
  /-- Both states are at the same stage. -/
  stage : stL.stage = st.stage
  /-- The enumerated lists represent the original finite sets. -/
  ours : ∀ j, (stL.ours j).toFinset = st.ours j
  /-- The next exponent has the same bound. -/
  nextC : stL.nextC = st.nextC
  /-- Every stored or default requirement tracks the original family. -/
  req : ∀ i, TracksReq (reqL stL i) (st.req i)

/-- Relation on the two alternatives returned by the first part of Case 2. -/
def TracksExam : (ReqStateL × Bool) ⊕ (ReqStateL × List Bool) →
    (ReqState × Bool) ⊕ (ReqState × List Bool) → Prop
  | .inl a, .inl b => TracksReq a.1 b.1 ∧ a.2 = b.2
  | .inr a, .inr b => TracksReq a.1 b.1 ∧ a.2 = b.2
  | _, _ => False

/-- Simulation relation on the triple returned by Case 3. -/
def TracksThree (a : ReqStateL × (Fin 3 → List Str) × Bool)
    (b : ReqState × (Fin 3 → Finset Str) × Bool) : Prop :=
  TracksReq a.1 b.1 ∧ (∀ j, (a.2.1 j).toFinset = b.2.1 j) ∧ a.2.2 = b.2.2

/-- Simulation relation on the four outputs of the case distinction. -/
def TracksCore (a : ReqStateL × (Fin 3 → List Str) × ℕ × Bool)
    (b : ReqState × (Fin 3 → Finset Str) × ℕ × Bool) : Prop :=
  TracksReq a.1 b.1 ∧ (∀ j, (a.2.1 j).toFinset = b.2.1 j) ∧
    a.2.2.1 = b.2.2.1 ∧ a.2.2.2 = b.2.2.2

/-- The default requirement has exactly the original default observable fields. -/
theorem tracksReq_default : TracksReq {} {} := by
  constructor <;> rfl

/-- Closing a window changes only ghost fields, so it preserves tracking. -/
theorem tracksReq_closeEpoch {rsL : ReqStateL} {rs : ReqState} (h : TracksReq rsL rs)
    (i c stop t : ℕ) (final : Bool) : TracksReq rsL (rs.closeEpoch i c stop t final) := by
  exact ⟨h.c, h.tables, h.baseline, h.play, h.lastVisit, h.lastActed⟩

/-- The two initial construction states track each other. -/
theorem tracks_default : Tracks {} {} := by
  refine ⟨rfl, fun _ => rfl, rfl, fun i => ?_⟩
  simpa [reqL, List.getD_nil] using tracksReq_default

/-- List positions agree in their original order; set equality suffices for the membership test. -/
theorem positionL_eq (I : Input) {ours : Fin 3 → List Str} {st : ConState}
    (h : ∀ j, (ours j).toFinset = st.ours j) (ar : Arena) (t : ℕ) (j : Fin 3) :
    positionL I ours ar t j = st.positionList I ar t j := by
  apply List.filter_congr
  intro τ _
  have hm : (τ ∈ ours j) ↔ τ ∈ st.ours j := by rw [← h j]; simp
  simp only [aliveL, ConState.alive, hm]

/-- Opponent spending agrees because the arena's board list is duplicate free. -/
theorem oppSpendL_eq (I : Input) (ar : Arena) (t₀ t : ℕ) :
    oppSpendL I ar t₀ t = oppSpend I ar t₀ t := by
  unfold oppSpendL oppSpend
  have hn : (ar.boardList.filter fun τ => I.opp t τ && !(I.opp t₀ τ)).Nodup :=
    (List.nodup_dedup _).filter _
  rw [costU_eq hn, List.toFinset_filter]
  rfl

/-- List search for a pending hit is equivalent to nonemptiness of the filtered board. -/
theorem pendingHitL_eq (I : Input) {rsL : ReqStateL} {rs : ReqState}
    (h : TracksReq rsL rs) (t : ℕ) : pendingHitL I rsL t = pendingHit I rs t := by
  apply Bool.eq_iff_iff.mpr
  simp [pendingHitL, pendingHit, boardOfL, boardOf, Arena.board, h.tables, h.lastVisit,
    Finset.nonempty_iff_ne_empty,
    Finset.filter_eq_empty_iff]

/-- Erasing accounting does not change the reset test. -/
theorem mustResetL_eq (I : Input) {stL : ConStateL} {st : ConState} (h : Tracks stL st)
    (i e t : ℕ) : mustResetL I stL i e t = mustReset I st i e t := by
  unfold mustResetL mustReset
  rw [(h.req i).c]
  congr 1
  apply List.any_congr rfl
  intro m
  rw [(h.req i).lastVisit, (h.req m).lastActed, pendingHitL_eq I (h.req m)]

/-- Only the next exponent bound of the state is read by `newC`. -/
theorem newCL_eq (st : ConState) (i t : ℕ) : newCL st.nextC i t = newC st i t := rfl

/-- Mapping a product's right list commutes with forming the product. -/
theorem product_map_right {α β γ : Type*} (l : List α) (r : List β) (f : β → γ) :
    l.product (r.map f) = (l.product r).map (fun q => (q.1, f q.2)) := by
  simp [List.product, List.map_flatMap, List.map_map, Function.comp_def]

/-- Mapping both lists commutes with their ordered product. -/
theorem product_map_both {α β γ δ : Type*} (l : List α) (r : List β)
    (f : α → γ) (g : β → δ) :
    (l.map f).product (r.map g) = (l.product r).map (fun q => (f q.1, g q.2)) := by
  simp [List.product, List.flatMap_map, List.map_flatMap, List.map_map,
    Function.comp_def]

/-- The split search commutes with replacing each list target by its finite set. -/
theorem splitSearchL_eq (ar : Arena) (A : Fin 3 → List Str) (E : ℕ) :
    (splitSearchL ar A E).map (fun q => (q.1, q.2.toFinset)) =
      ((allBoards.product allBoards).product (subsetsOf ar.tables.length)).find?
        (fun q => decide (q.1.1 ≠ q.1.2) &&
          decide (ar.Forces q.2 (A q.1.1).toFinset E E) &&
          decide (ar.Forces (vectors ar.tables.length \ q.2) (A q.1.2).toFinset E E)) := by
  unfold splitSearchL subsetsOf
  rw [product_map_right, List.find?_map]
  congr 2
  funext q
  simp [forcesB, complL_toFinset]

/-- The failed intersection search commutes with interpreting both targets. -/
theorem meetSearchL_eq (ar : Arena) (A : Fin 3 → List Str) (E : ℕ) :
    (meetSearchL ar A E).map (fun q => (q.1.toFinset, q.2.toFinset)) =
      ((subsetsOf ar.tables.length).product (subsetsOf ar.tables.length)).find?
        (fun q => decide (ar.Forces q.1 (A 0).toFinset E E) &&
          decide (ar.Forces q.2 (A 0).toFinset E E) &&
          !(decide (ar.Forces (q.1 ∩ q.2) (A 0).toFinset E E))) := by
  unfold meetSearchL subsetsOf
  rw [product_map_both, List.find?_map]
  congr 2
  funext q
  simp [forcesB, interL_toFinset]

/-- A singleton target is interpreted without changing the generator search. -/
theorem principalSearchL_eq (ar : Arena) (A : Fin 3 → List Str) (E : ℕ) :
    principalSearchL ar A E = (allVec ar.tables.length).find?
      (fun σ => decide (ar.Forces {σ} (A 0).toFinset E E)) := by
  simp [principalSearchL, forcesB]

/-- The three ordered searches give the same top verdict. -/
theorem topOutcomeL_eq (ar : Arena) (A : Fin 3 → List Str) (E : ℕ) :
    toTopOutcome (topOutcomeL ar A E) = topOutcome ar (fun j => (A j).toFinset) E := by
  unfold topOutcomeL topOutcome
  dsimp only
  rw [← splitSearchL_eq, ← meetSearchL_eq, ← principalSearchL_eq]
  cases hs : splitSearchL ar A E with
  | some q => rfl
  | none =>
    cases hm : meetSearchL ar A E with
    | some q => rfl
    | none => cases principalSearchL ar A E <;> rfl

/-- The level search and the selected first board are unchanged. -/
theorem firstStackSplitL_eq (ar : Arena) (A : Fin 3 → List Str) (σ : List Bool) :
    firstStackSplitL ar A σ = firstStackSplit ar (fun j => (A j).toFinset) σ := by
  unfold firstStackSplitL firstStackSplit
  dsimp only
  congr 1
  · apply congrArg (fun p : ℕ → Bool => (List.range (maxLen ar.tables)).find? p)
    funext r
    apply List.any_congr rfl
    intro j
    unfold forcesB
    apply decide_eq_decide.mpr
    simp [complL_toFinset]
  · funext r
    apply congrArg (Option.map (fun j : Fin 3 => (r + 1, j)))
    apply congrArg (fun p : Fin 3 → Bool => allBoards.find? p)
    funext j
    unfold forcesB
    apply decide_eq_decide.mpr
    simp [complL_toFinset]

/-- The response predicate is exactly the original predicate on the corresponding finite set. -/
theorem respondOkL_eq (ar : Arena) (g : BoardGameL) (La : List Str) (a b : ℕ)
    (p : List Str) : respondOkL ar g La a b p =
      (decide (cost ar.w p.toFinset ≤ b) &&
        (if p.toFinset = ∅ then decide (ar.value La.toFinset ∈ g.toBoardGame.target) &&
            decide (ar.Forces g.toBoardGame.target La.toFinset a b)
         else decide (ar.Forces g.toBoardGame.target (La.toFinset \ p.toFinset)
            a (b - cost ar.w p.toFinset)))) := by
  simp only [respondOkL, costU_dedup, valueL_eq, forcesB, diffL_toFinset,
    List.toFinset_eq_empty_iff, BoardGameL.toBoardGame, List.mem_toFinset]
  split_ifs <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [Bool.and_eq_true, decide_eq_true_eq]
  · constructor
    · rintro ⟨hc, hv, hf⟩; exact ⟨hc, hv, decide_eq_true hf⟩
    · rintro ⟨hc, hv, hf⟩; exact ⟨hc, hv, of_decide_eq_true hf⟩
  · constructor
    · rintro ⟨hc, hf⟩; exact ⟨hc, decide_eq_true hf⟩
    · rintro ⟨hc, hf⟩; exact ⟨hc, of_decide_eq_true hf⟩

/-- The first successful response represents the original response even for lists with repeats. -/
theorem respondL_toFinset (ar : Arena) (g : BoardGameL) (La : List Str) (a b : ℕ) :
    (respondL ar g La a b).toFinset = respond ar g.toBoardGame La a b := by
  unfold respondL respond
  dsimp only
  rw [List.find?_map]
  have hp := funext (fun p => respondOkL_eq ar g La a b p)
  simp only [Function.comp_def] at *
  rw [← hp]
  cases La.sublists.find? (respondOkL ar g La a b) <;> rfl

/-- A symmetric list game represents the original symmetric game. -/
theorem symGameL_eq (j : Fin 3) (S : List (List Bool)) (E : ℕ) :
    (symGameL j S E).toBoardGame = symGame j S.toFinset E := rfl

/-- Balanced games agree for each encoded verdict. -/
theorem balancedPlayL_eq (ar : Arena) (t E : ℕ) (v : TopOutcomeL) :
    (balancedPlayL ar t E v).map PlayL.toPlay = balancedPlay ar t E (toTopOutcome v) := by
  rcases v with _ | (⟨j, k, S⟩ | (⟨S, T⟩ | σ)) <;>
    simp [balancedPlayL, balancedPlay, toTopOutcome, PlayL.toPlay, symGameL_eq,
      complL_toFinset, interL_toFinset]

/-- Case 1 preserves all observable fields and chooses the same new exponent. -/
theorem caseOneL_tracks {stL : ConStateL} {st : ConState} (h : Tracks stL st) (i t : ℕ) :
    TracksReq (caseOneL stL i t).1 (caseOne st i t).1 ∧
      (caseOneL stL i t).2 = (caseOne st i t).2 := by
  have hc' : newCL stL.nextC i t = newC st i t := by rw [h.nextC]; rfl
  have hr := h.req i
  cases hci : (st.req i).c <;>
    simp only [caseOneL, caseOne, hci, hc'] <;>
    exact ⟨⟨rfl, hr.tables, rfl, rfl, hr.lastVisit, hr.lastActed⟩, trivial⟩

/-- With an existing baseline, the repair of Case 2 is simulated. -/
theorem examineTopL_tracks_some (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) (bl : Baseline) (hb : rsL.baseline = some bl) :
    TracksExam (examineTopL I stL i t c rsL) (examineTop I st i t c rs) := by
  obtain ⟨hc, htab, hbl, hpl, hlv, hla⟩ := hr
  have hbl' : rs.baseline = some bl := hbl.symm.trans hb
  have e : rs.tables = rsL.tables := htab.symm
  unfold examineTopL examineTop
  dsimp only
  simp only [hb, hbl', e]
  have hany : (allBoards.any fun j => decide (levelBudget rsL.tables 0 <
        oppSpendL I (arenaOf c rsL.tables) (bl.base j) t)) =
      (allBoards.any fun j => decide (levelBudget rsL.tables 0 <
        oppSpend I (arenaOf c rsL.tables) (bl.base j) t)) := by
    simp only [oppSpendL_eq]
  rw [hany]
  by_cases hq : (allBoards.any fun j => decide (levelBudget rsL.tables 0 <
        oppSpend I (arenaOf c rsL.tables) (bl.base j) t)) = true
  · simp only [hq, ↓reduceIte]
    have hnone : TracksReq { rsL with baseline := none }
        { rs with tables := rsL.tables, baseline := none } := by
      apply TracksReq.mk
      · exact hc
      · exact rfl
      · rfl
      · exact hpl
      · exact hlv
      · exact hla
    exact ⟨tracksReq_closeEpoch hnone i c t t false, rfl⟩
  · simp only [hq]
    have hs : (allBoards.find? fun j => forcesB (arenaOf c rsL.tables)
          (complL rsL.tables.length [bl.σ]) (positionL I stL.ours (arenaOf c rsL.tables) t j)
          (levelBudget rsL.tables 0) (levelBudget rsL.tables 0)) =
        (allBoards.find? fun j => decide ((arenaOf c rsL.tables).Forces
          (vectors rsL.tables.length \ {bl.σ}) (st.position I (arenaOf c rsL.tables) t j)
          (levelBudget rsL.tables 0) (levelBudget rsL.tables 0))) := by
      congr 1; funext j
      simp only [forcesB, complL_toFinset, positionL_eq I h.ours]
      congr 3
    rw [hs]
    cases hf : (allBoards.find? fun j => decide ((arenaOf c rsL.tables).Forces
          (vectors rsL.tables.length \ {bl.σ}) (st.position I (arenaOf c rsL.tables) t j)
          (levelBudget rsL.tables 0) (levelBudget rsL.tables 0)))
    · dsimp only
      change TracksReq _ _ ∧ _ = _
      have hnone : TracksReq { rsL with baseline := some ⟨bl.σ, fun _ => t⟩ }
          { rs with tables := rsL.tables, baseline := some ⟨bl.σ, fun _ => t⟩ } := by
        apply TracksReq.mk
        · exact hc
        · exact rfl
        · rfl
        · exact hpl
        · exact hlv
        · exact hla
      exact ⟨tracksReq_closeEpoch hnone i c t t false, rfl⟩
    · rename_i j
      dsimp only
      change TracksReq _ _ ∧ _ = _
      have htab' :
          ({ rsL with baseline := some bl,
                      play := some (unbalancedPlayL (arenaOf c rsL.tables) t
          (levelBudget rsL.tables 0)
          (levelBudget rsL.tables 0 - oppSpendL I (arenaOf c rsL.tables) (bl.base (otherBoard j)) t)
          bl.σ j (otherBoard j)) } : ReqStateL).tables =
          ({ rs with tables := rsL.tables, baseline := some bl,
                     play := some { arena := arenaOf c rsL.tables, start := t,
                                    kind := PlayKind.unbalanced,
                                    games := [symGame j (vectors rsL.tables.length \ {bl.σ})
          (levelBudget rsL.tables 0),
          { board := otherBoard j, target := {bl.σ},
            oppLimit := levelBudget rsL.tables 0 - oppSpend I (arenaOf c rsL.tables) (bl.base
          (otherBoard j)) t, ourLimit := levelBudget rsL.tables 0, spent := 0 }] } } :
          ReqState).tables := rfl
      refine ⟨⟨hc, htab', rfl, ?_, hlv, hla⟩, rfl⟩
      simp only [unbalancedPlayL, oppSpendL_eq, Option.map_some, PlayL.toPlay, List.map_cons,
        BoardGameL.toBoardGame, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        List.map_nil, Option.some.injEq, Play.mk.injEq, List.cons.injEq, and_true, true_and]
      congr 1
      · ext z
        simp [symGameL, complL_toFinset]
        tauto

/-- Without a baseline, the same verdict starts the same games or remembers the same vector. -/
theorem examineTopL_tracks_none (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) (hb : rsL.baseline = none) :
    TracksExam (examineTopL I stL i t c rsL) (examineTop I st i t c rs) := by
  dsimp [examineTopL, examineTop]
  rw [hb]
  have h_base : rs.baseline = none := by rw [←hr.baseline, hb]
  rw [h_base]
  dsimp [examineVerdictL]
  have htop_eq :=
    topOutcomeL_eq (arenaOf c rsL.tables) (positionL I stL.ours (arenaOf c rsL.tables) t)
        (levelBudget rsL.tables 0)
  have hpos_eq : (fun j => List.toFinset (positionL I stL.ours (arenaOf c rsL.tables) t j)) =
      st.position I (arenaOf c rsL.tables) t := by
    ext j
    rw [positionL_eq I h.ours]
    rfl
  rw [hpos_eq] at htop_eq
  have htop_eq_2 : topOutcome (arenaOf c rsL.tables) (st.position I (arenaOf c rsL.tables) t)
      (levelBudget rsL.tables 0) =
      topOutcome (arenaOf c rs.tables) (st.position I (arenaOf c rs.tables) t)
          (levelBudget rs.tables 0) := by rw [hr.tables]
  rw [htop_eq_2] at htop_eq
  generalize h_top_L : topOutcomeL (arenaOf c rsL.tables)
      (positionL I stL.ours (arenaOf c rsL.tables) t) (levelBudget rsL.tables 0) = vL
  generalize h_top_R : topOutcome (arenaOf c rs.tables) (st.position I (arenaOf c rs.tables) t)
      (levelBudget rs.tables 0) = vR
  have htop_eq3 : toTopOutcome vL = vR := by
    rw [← h_top_L, ← h_top_R]
    exact htop_eq
  cases vL with
  | none =>
    have htop_stuck : vR = TopOutcome.stuck := by
      rw [← htop_eq3]
      rfl
    rw [htop_stuck]
    dsimp
    have hbal : balancedPlay (arenaOf c rs.tables) t (levelBudget rs.tables 0) TopOutcome.stuck =
        none := rfl
    rw [hbal]
    constructor
    · exact hr
    · rfl
  | some v =>
    cases v with
    | inl v2 =>
      rcases v2 with ⟨j, k, S⟩
      have htop_split : vR = TopOutcome.split j k S.toFinset := by
        rw [← htop_eq3]
        rfl
      rw [htop_split]
      dsimp
      have h_bal_eq := balancedPlayL_eq (arenaOf c rsL.tables) t (levelBudget rsL.tables 0)
          (some (Sum.inl ⟨j, k, S⟩))
      cases h_bal : balancedPlayL (arenaOf c rsL.tables) t (levelBudget rsL.tables 0)
        (some (Sum.inl (j, k, S))) with
      | none =>
        rw [h_bal] at h_bal_eq
        dsimp at h_bal_eq
        have h_bal_eq2 : balancedPlay (arenaOf c rs.tables) t (levelBudget rs.tables 0)
          (TopOutcome.split j k S.toFinset) = none := by
          rw [← hr.tables]
          exact h_bal_eq.symm
        rw [h_bal_eq2]
        constructor
        · exact hr
        · rfl
      | some pl =>
        rw [h_bal] at h_bal_eq
        dsimp at h_bal_eq
        have h_bal_eq2 : balancedPlay (arenaOf c rs.tables) t (levelBudget rs.tables 0)
          (TopOutcome.split j k S.toFinset) = some pl.toPlay := by
          rw [← hr.tables]
          exact h_bal_eq.symm
        rw [h_bal_eq2]
        dsimp
        constructor
        · apply TracksReq.mk
          · exact hr.c
          · exact hr.tables
          · change rsL.baseline = none
            exact hb
          · change Option.map PlayL.toPlay (some pl) = some pl.toPlay
            rfl
          · exact hr.lastVisit
          · exact hr.lastActed
        · rfl
    | inr v2 =>
      cases v2 with
      | inl v3 =>
        rcases v3 with ⟨S, T⟩
        have htop_meet : vR = TopOutcome.meet S.toFinset T.toFinset := by
          rw [← htop_eq3]
          rfl
        rw [htop_meet]
        dsimp
        have h_bal_eq := balancedPlayL_eq (arenaOf c rsL.tables) t (levelBudget rsL.tables 0)
            (some (Sum.inr (Sum.inl ⟨S, T⟩)))
        cases h_bal : balancedPlayL (arenaOf c rsL.tables) t (levelBudget rsL.tables 0)
          (some (Sum.inr (Sum.inl (S, T)))) with
        | none =>
          rw [h_bal] at h_bal_eq
          dsimp at h_bal_eq
          have h_bal_eq2 : balancedPlay (arenaOf c rs.tables) t (levelBudget rs.tables 0)
            (TopOutcome.meet S.toFinset T.toFinset) = none := by
            rw [← hr.tables]
            exact h_bal_eq.symm
          rw [h_bal_eq2]
          constructor
          · exact hr
          · rfl
        | some pl =>
          rw [h_bal] at h_bal_eq
          dsimp at h_bal_eq
          have h_bal_eq2 : balancedPlay (arenaOf c rs.tables) t (levelBudget rs.tables 0)
            (TopOutcome.meet S.toFinset T.toFinset) = some pl.toPlay := by
            rw [← hr.tables]
            exact h_bal_eq.symm
          rw [h_bal_eq2]
          dsimp
          constructor
          · apply TracksReq.mk
            · exact hr.c
            · exact hr.tables
            · change rsL.baseline = none
              exact hb
            · change Option.map PlayL.toPlay (some pl) = some pl.toPlay
              rfl
            · exact hr.lastVisit
            · exact hr.lastActed
          · rfl
      | inr σ =>
        have htop_principal : vR = TopOutcome.principal σ := by
          rw [← htop_eq3]
          rfl
        rw [htop_principal]
        dsimp
        constructor
        · apply tracksReq_closeEpoch
          apply TracksReq.mk
          · exact hr.c
          · exact hr.tables
          · change some _ = some _
            rfl
          · exact hr.play
          · exact hr.lastVisit
          · exact hr.lastActed
        · rfl

/-- Assemble the two baseline cases of the first part of Case 2. -/
theorem examineTopL_tracks (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) :
    TracksExam (examineTopL I stL i t c rsL) (examineTop I st i t c rs) := by
  cases hb : rsL.baseline with
  | none => exact examineTopL_tracks_none I h hr i t c hb
  | some bl => exact examineTopL_tracks_some I h hr i t c bl hb

/-- The stack split branch starts matching stacked games. -/
theorem caseTwoL_tracks_stack (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) {rL : ReqStateL} {r : ReqState} {σ : List Bool}
    (hr₁ : TracksReq rL r)
    (heL : examineTopL I stL i t c rsL = .inr (rL, σ))
    (he : examineTop I st i t c rs = .inr (r, σ))
    {ℓ : ℕ} {j : Fin 3}
    (hf : firstStackSplitL (arenaOf c rsL.tables)
      (positionL I stL.ours (arenaOf c rsL.tables) t) σ = some (ℓ, j)) :
    TracksReq (caseTwoL I stL i t c rsL).1 (caseTwo I st i t c rs).1 ∧
      (caseTwoL I stL i t c rsL).2 = (caseTwo I st i t c rs).2 := by
  dsimp [caseTwoL, caseTwoAgreeL, caseTwo]
  rw [heL, he]
  dsimp
  have hpos : (fun j => List.toFinset (positionL I stL.ours (arenaOf c rsL.tables) t j)) =
      st.position I (arenaOf c rsL.tables) t := by
    ext j'
    rw [positionL_eq I h.ours]
    rfl
  have hf_eq : firstStackSplit (arenaOf c rsL.tables) (st.position I (arenaOf c rsL.tables) t) σ =
      some (ℓ, j) := by
    rw [← hpos, ← firstStackSplitL_eq]
    exact hf
  have h_tables : rsL.tables = rs.tables := hr.tables
  have hf_eq2 : firstStackSplit (arenaOf c rs.tables) (st.position I (arenaOf c rs.tables) t) σ =
      some (ℓ, j) := by
    rw [← h_tables]
    exact hf_eq
  rw [hf, hf_eq2]
  dsimp
  constructor
  · apply TracksReq.mk
    · exact hr₁.c
    · exact hr₁.tables
    · exact hr₁.baseline
    · rw [hr.tables, hr₁.tables]
      dsimp [PlayL.toPlay, Option.map]
      congr 1
      simp [symGameL_eq, complL_toFinset]
    · exact hr₁.lastVisit
    · exact hr₁.lastActed
  · rfl

/-- Case 2 keeps the examination result if X disagrees or no new table is defined. -/
theorem caseTwoL_tracks_extend_stop (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) {rL : ReqStateL} {r : ReqState} {σ : List Bool}
    (hr₁ : TracksReq rL r)
    (heL : examineTopL I stL i t c rsL = .inr (rL, σ))
    (he : examineTop I st i t c rs = .inr (r, σ))
    (hf : firstStackSplitL (arenaOf c rsL.tables)
      (positionL I stL.ours (arenaOf c rsL.tables) t) σ = none)
    (hstop : σ ≠ xPrefix I t rsL.tables.length ∨
      tableAt i rsL.tables.length t = none) :
    TracksReq (caseTwoL I stL i t c rsL).1 (caseTwo I st i t c rs).1 ∧
      (caseTwoL I stL i t c rsL).2 = (caseTwo I st i t c rs).2 := by
  have hpos : (fun j => List.toFinset (positionL I stL.ours (arenaOf c rsL.tables) t j)) =
      st.position I (arenaOf c rsL.tables) t := by
    funext j'
    rw [positionL_eq I h.ours]
    rfl
  have hf1 : firstStackSplit (arenaOf c rsL.tables)
      (st.position I (arenaOf c rsL.tables) t) σ = none := by
    rw [← hpos, ← firstStackSplitL_eq]
    exact hf
  have hf2 : firstStackSplit (arenaOf c rs.tables)
      (st.position I (arenaOf c rs.tables) t) σ = none := by
    rw [← hr.tables]
    exact hf1
  have hstop2 : σ ≠ xPrefix I t rs.tables.length ∨ tableAt i rs.tables.length t = none := by
    rw [← hr.tables]
    exact hstop
  have hL : caseTwoL I stL i t c rsL = (rL, false) := by
    simp only [caseTwoL, caseTwoAgreeL, heL, hf, caseTwoExtendL]
    rcases hstop with h1 | h1
    · simp [h1]
    · by_cases hx : σ ≠ xPrefix I t rsL.tables.length <;> simp [hx, h1]
  have hO : caseTwo I st i t c rs = (r, false) := by
    simp only [caseTwo, he, hf2]
    rcases hstop2 with h1 | h1
    · simp [h1]
    · by_cases hx : σ ≠ xPrefix I t rs.tables.length <;> simp [hx, h1]
  rw [hL, hO]
  exact ⟨hr₁, rfl⟩

/-- With a new table available, Case 2 interprets the same extended-table verdict. -/
theorem caseTwoL_tracks_extend_table (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) {rL : ReqStateL} {r : ReqState} {σ : List Bool}
    (hr₁ : TracksReq rL r)
    (heL : examineTopL I stL i t c rsL = .inr (rL, σ))
    (he : examineTop I st i t c rs = .inr (r, σ))
    (hf : firstStackSplitL (arenaOf c rsL.tables)
      (positionL I stL.ours (arenaOf c rsL.tables) t) σ = none)
    (hx : σ = xPrefix I t rsL.tables.length) (tbl : TTable)
    (htbl : tableAt i rsL.tables.length t = some tbl) :
    TracksReq (caseTwoL I stL i t c rsL).1 (caseTwo I st i t c rs).1 ∧
      (caseTwoL I stL i t c rsL).2 = (caseTwo I st i t c rs).2 := by
  dsimp [caseTwoL, caseTwoAgreeL, caseTwoExtendL, caseTwoTableL, extensionVerdictL, caseTwo]
  rw [heL, he]
  dsimp
  have hpos : (fun j => List.toFinset (positionL I stL.ours (arenaOf c rsL.tables) t j)) =
      st.position I (arenaOf c rsL.tables) t := by
    ext j'
    rw [positionL_eq I h.ours]
    rfl
  have hf_eq : firstStackSplit (arenaOf c rsL.tables) (st.position I (arenaOf c rsL.tables) t) σ =
      none := by
    rw [← hpos, ← firstStackSplitL_eq]
    exact hf
  have h_tables : rsL.tables = rs.tables := hr.tables
  have hf_eq2 : firstStackSplit (arenaOf c rs.tables) (st.position I (arenaOf c rs.tables) t) σ =
      none := by
    rw [← h_tables]
    exact hf_eq
  rw [hf, hf_eq2]
  dsimp
  have hx_eq : σ = xPrefix I t rs.tables.length := by
    rw [← h_tables]
    exact hx
  have hx_eq2 : (xPrefix I t rsL.tables.length = xPrefix I t rs.tables.length) = True := by
    have h_eq : xPrefix I t rsL.tables.length = xPrefix I t rs.tables.length := by rw [h_tables]
    simp [h_eq]
  simp only [hx, hx_eq2, not_true_eq_false, ite_false]
  have htbl2 : tableAt i rs.tables.length t = some tbl := by
    rw [← h_tables]
    exact htbl
  rw [htbl, htbl2]
  dsimp
  have htop_eq : toTopOutcome (topOutcomeL (arenaOf c (rsL.tables ++ [tbl]))
      (positionL I stL.ours (arenaOf c (rsL.tables ++ [tbl])) t)
      (levelBudget (rsL.tables ++ [tbl]) 0)) =
      topOutcome (arenaOf c (rs.tables ++ [tbl]))
      (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
      (levelBudget (rs.tables ++ [tbl]) 0) := by
    have hpos2 :
        (fun j => List.toFinset (positionL I stL.ours (arenaOf c (rsL.tables ++ [tbl])) t j)) =
        st.position I (arenaOf c (rs.tables ++ [tbl])) t := by
      ext j'
      rw [positionL_eq I h.ours, ← hr.tables]
      rfl
    have h_top_eq_1 := topOutcomeL_eq (arenaOf c (rsL.tables ++ [tbl]))
      (positionL I stL.ours (arenaOf c (rsL.tables ++ [tbl])) t)
      (levelBudget (rsL.tables ++ [tbl]) 0)
    rw [hpos2] at h_top_eq_1
    have h_top_eq_2 : topOutcome (arenaOf c (rsL.tables ++ [tbl]))
      (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
      (levelBudget (rsL.tables ++ [tbl]) 0) =
      topOutcome (arenaOf c (rs.tables ++ [tbl]))
      (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
      (levelBudget (rs.tables ++ [tbl]) 0) := by rw [hr.tables]
    rw [h_top_eq_1, h_top_eq_2]
  generalize h_top_L : topOutcomeL (arenaOf c (rsL.tables ++ [tbl]))
      (positionL I stL.ours (arenaOf c (rsL.tables ++ [tbl])) t)
      (levelBudget (rsL.tables ++ [tbl]) 0) = vL
  generalize h_top_R : topOutcome (arenaOf c (rs.tables ++ [tbl]))
      (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
      (levelBudget (rs.tables ++ [tbl]) 0) = vR
  have htop_eq2 : toTopOutcome vL = vR := by
    rw [← h_top_L, ← h_top_R]
    exact htop_eq
  cases vL with
  | none =>
    have htop2 : vR = .stuck := by
      rw [← htop_eq2]
      rfl
    subst htop2
    dsimp
    constructor
    · exact hr₁
    · rfl
  | some q =>
    cases q with
    | inl q1 =>
      obtain ⟨j, k, S⟩ := q1
      have htop2 : vR = .split j k S.toFinset := by
        rw [← htop_eq2]
        rfl
      subst htop2
      dsimp
      cases h_bal : balancedPlayL (arenaOf c (rsL.tables ++ [tbl])) t
          (levelBudget (rsL.tables ++ [tbl]) 0)
          (some (Sum.inl (j, k, S))) with
      | none =>
        have h_bal_eq :=
          balancedPlayL_eq (arenaOf c (rsL.tables ++ [tbl])) t (levelBudget (rsL.tables ++ [tbl]) 0)
            (some (Sum.inl (j, k, S)))
        rw [h_bal] at h_bal_eq
        dsimp at h_bal_eq
        have h_bal_eq2 : balancedPlay (arenaOf c (rs.tables ++ [tbl])) t
            (levelBudget (rs.tables ++ [tbl]) 0)
          (TopOutcome.split j k S.toFinset) = none := by
          rw [hr.tables] at h_bal_eq
          exact h_bal_eq.symm
        rw [h_bal_eq2]
        dsimp
        constructor
        · exact hr₁
        · rfl
      | some pl =>
        have h_bal_eq :=
          balancedPlayL_eq (arenaOf c (rsL.tables ++ [tbl])) t (levelBudget (rsL.tables ++ [tbl]) 0)
            (some (Sum.inl (j, k, S)))
        rw [h_bal] at h_bal_eq
        dsimp at h_bal_eq
        have h_bal_eq2 : balancedPlay (arenaOf c (rs.tables ++ [tbl])) t
            (levelBudget (rs.tables ++ [tbl]) 0)
          (TopOutcome.split j k S.toFinset) = some pl.toPlay := by
          rw [hr.tables] at h_bal_eq
          exact h_bal_eq.symm
        rw [h_bal_eq2]
        dsimp
        constructor
        · apply TracksReq.mk
          · exact hr₁.c
          · exact (by simp [hr.tables])
          · rfl
          · rfl
          · exact hr₁.lastVisit
          · exact hr₁.lastActed
        · rfl
    | inr q2 =>
      cases q2 with
      | inl S_T =>
        obtain ⟨S, T⟩ := S_T
        have htop2 : vR = .meet S.toFinset T.toFinset := by
          rw [← htop_eq2]
          rfl
        subst htop2
        dsimp
        cases h_bal : balancedPlayL (arenaOf c (rsL.tables ++ [tbl])) t
            (levelBudget (rsL.tables ++ [tbl]) 0)
          (some (Sum.inr (Sum.inl (S, T)))) with
        | none =>
          have h_bal_eq :=
            balancedPlayL_eq (arenaOf c (rsL.tables ++ [tbl])) t
                (levelBudget (rsL.tables ++ [tbl]) 0)
              (some (Sum.inr (Sum.inl (S, T))))
          rw [h_bal] at h_bal_eq
          dsimp at h_bal_eq
          have h_bal_eq2 : balancedPlay (arenaOf c (rs.tables ++ [tbl])) t
              (levelBudget (rs.tables ++ [tbl]) 0)
            (TopOutcome.meet S.toFinset T.toFinset) = none := by
            rw [hr.tables] at h_bal_eq
            exact h_bal_eq.symm
          rw [h_bal_eq2]
          dsimp
          constructor
          · exact hr₁
          · rfl
        | some pl =>
          have h_bal_eq :=
            balancedPlayL_eq (arenaOf c (rsL.tables ++ [tbl])) t
                (levelBudget (rsL.tables ++ [tbl]) 0)
              (some (Sum.inr (Sum.inl (S, T))))
          rw [h_bal] at h_bal_eq
          dsimp at h_bal_eq
          have h_bal_eq2 : balancedPlay (arenaOf c (rs.tables ++ [tbl])) t
              (levelBudget (rs.tables ++ [tbl]) 0)
            (TopOutcome.meet S.toFinset T.toFinset) = some pl.toPlay := by
            rw [hr.tables] at h_bal_eq
            exact h_bal_eq.symm
          rw [h_bal_eq2]
          dsimp
          constructor
          · apply TracksReq.mk
            · exact hr₁.c
            · exact (by simp [hr.tables])
            · rfl
            · rfl
            · exact hr₁.lastVisit
            · exact hr₁.lastActed
          · rfl
      | inr σ2 =>
        have htop2 : vR = .principal σ2 := by
          rw [← htop_eq2]
          rfl
        subst htop2
        dsimp
        constructor
        · apply TracksReq.mk
          · exact hr₁.c
          · exact (by simp [hr.tables])
          · rfl
          · exact hr₁.play
          · exact hr₁.lastVisit
          · exact hr₁.lastActed
        · rfl

/-- Assemble the no-extension and available-table branches after a failed stack search. -/
theorem caseTwoL_tracks_extend (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) {rL : ReqStateL} {r : ReqState} {σ : List Bool}
    (hr₁ : TracksReq rL r)
    (heL : examineTopL I stL i t c rsL = .inr (rL, σ))
    (he : examineTop I st i t c rs = .inr (r, σ))
    (hf : firstStackSplitL (arenaOf c rsL.tables)
      (positionL I stL.ours (arenaOf c rsL.tables) t) σ = none) :
    TracksReq (caseTwoL I stL i t c rsL).1 (caseTwo I st i t c rs).1 ∧
      (caseTwoL I stL i t c rsL).2 = (caseTwo I st i t c rs).2 := by
  by_cases hx : σ = xPrefix I t rsL.tables.length
  · cases htbl : tableAt i rsL.tables.length t with
    | none =>
      exact caseTwoL_tracks_extend_stop I h hr i t c hr₁ heL he hf (Or.inr htbl)
    | some tbl =>
      exact caseTwoL_tracks_extend_table I h hr i t c hr₁ heL he hf hx tbl htbl
  · exact caseTwoL_tracks_extend_stop I h hr i t c hr₁ heL he hf (Or.inl hx)

/-- Assemble Case 2 from the examination, stack split, and extension simulations. -/
theorem caseTwoL_tracks (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) :
    TracksReq (caseTwoL I stL i t c rsL).1 (caseTwo I st i t c rs).1 ∧
      (caseTwoL I stL i t c rsL).2 = (caseTwo I st i t c rs).2 := by
  have he := examineTopL_tracks I h hr i t c
  cases heL : examineTopL I stL i t c rsL with
  | inl a =>
    cases heS : examineTop I st i t c rs with
    | inl b => simpa only [caseTwoL, caseTwo, heL, heS, TracksExam] using he
    | inr b => simp only [heL, heS, TracksExam] at he
  | inr a =>
    cases heS : examineTop I st i t c rs with
    | inl b => simp only [heL, heS, TracksExam] at he
    | inr b =>
      have hh : TracksReq a.1 b.1 ∧ a.2 = b.2 := by
        simpa only [heL, heS, TracksExam] using he
      obtain ⟨rL, σ⟩ := a
      obtain ⟨r, σ'⟩ := b
      dsimp only at hh
      obtain ⟨hh, hσ⟩ := hh
      subst σ'
      cases hf : firstStackSplitL (arenaOf c rsL.tables)
          (positionL I stL.ours (arenaOf c rsL.tables) t) σ with
      | none => exact caseTwoL_tracks_extend I h hr i t c hh heL heS hf
      | some q => exact caseTwoL_tracks_stack I h hr i t c hh heL heS hf

/-- Folding list unions represents folding finite set unions, for arbitrary repeated entries. -/
theorem fold_moves_toFinset (moves : List (BoardGameL × List Str)) (A : List Str)
    (j : Fin 3) :
    (moves.foldr (fun q acc => if q.1.board = j then q.2 ++ acc else acc) A).toFinset =
      moves.foldr (fun q acc => if q.1.board = j then q.2.toFinset ∪ acc else acc) A.toFinset := by
  induction moves with
  | nil => rfl
  | cons q qs ih =>
    by_cases hq : q.1.board = j <;> simp [List.foldr_cons, hq, ih]

/-- The ordered response list represents the original ordered list of game moves. -/
theorem movesL_toFinset (I : Input) {ours : Fin 3 → List Str} {st : ConState}
    (h : ∀ j, (ours j).toFinset = st.ours j) (ar : Arena) (t lam : ℕ)
    (games : List BoardGameL) :
    (movesL I ours ar t lam games).map (fun q => (q.1.toBoardGame, q.2.toFinset)) =
      (games.map BoardGameL.toBoardGame).map (fun g =>
        (g, respond ar g (st.positionList I ar t g.board)
          (g.oppLimit - lam) (g.ourLimit - g.spent))) := by
  simp only [movesL, List.map_map]
  apply List.map_congr_left
  intro g _
  dsimp only [Function.comp_apply]
  rw [positionL_eq I h, respondL_toFinset]
  rfl

/-- Charging list responses gives exactly the original finite set spending updates. -/
theorem advanceGamesL_toBoardGames (ar : Arena) (moves : List (BoardGameL × List Str)) :
    (advanceGamesL ar moves).map BoardGameL.toBoardGame =
      moves.map (fun q => { q.1.toBoardGame with
        spent := q.1.spent + cost ar.w q.2.toFinset }) := by
  simp only [advanceGamesL, List.map_map]
  apply List.map_congr_left
  intro q _
  simp [BoardGameL.toBoardGame, costU_dedup]

/-- The list and finite set tests for a nonempty response agree. -/
theorem movesL_any_eq (moves : List (BoardGameL × List Str)) :
    moves.any (fun q => decide (q.2 ≠ [])) =
      (moves.map (fun q => (q.1.toBoardGame, q.2.toFinset))).any
        (fun q => decide q.2.Nonempty) := by
  rw [List.any_map]
  apply List.any_congr rfl
  intro q
  apply decide_eq_decide.mpr
  simp

/-- Interpreting board games leaves their minimum opponent limit unchanged. -/
theorem gameLimit_toPlay (pl : PlayL) (E : ℕ) :
    pl.toPlay.games.foldr (fun g n => min g.oppLimit n) E =
      pl.games.foldr (fun g n => min g.oppLimit n) E := by
  simp only [PlayL.toPlay, List.foldr_map, BoardGameL.toBoardGame]

/-- In Case 3a, responses, budgets, unions, and action flags have the same interpretation. -/
theorem caseThreeL_tracks_3a (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) (pl : PlayL)
    (hle : oppSpendL I pl.arena pl.start t ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)) :
    TracksThree (caseThreeL I stL i t c rsL pl)
      (caseThree I st i t c rs pl.toPlay) := by
  have hle' : oppSpend I pl.arena pl.start t ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0) := by
    rw [← oppSpendL_eq]; exact hle
  have hc : oppSpend I pl.toPlay.arena pl.toPlay.start t ≤
      pl.toPlay.games.foldr (fun g n => min g.oppLimit n)
        (levelBudget pl.toPlay.arena.tables 0) := by
    rw [gameLimit_toPlay]; exact hle'
  
  simp only [caseThreeL, caseThree, caseThreeMoveL, oppSpendL_eq, hle', hc, ite_true]
  
  have hm := movesL_toFinset I h.ours pl.arena t (oppSpend I pl.arena pl.start t) pl.games
  refine ⟨⟨hr.c, hr.tables, hr.baseline, ?_, hr.lastVisit, hr.lastActed⟩, ?_, ?_⟩
  · change some (PlayL.toPlay _) = some _
    congr 1
    show PlayL.toPlay _ = Play.mk _ _ _ _
    simp only [PlayL.toPlay]
    congr 1
    have key : ∀ M : List (BoardGameL × List Str),
        List.map BoardGameL.toBoardGame (advanceGamesL pl.arena M) =
        List.map
        (fun q =>
        { board := q.1.board, target := q.1.target, oppLimit := q.1.oppLimit,
          ourLimit := q.1.ourLimit, spent := q.1.spent + cost pl.arena.w q.2 })
        (List.map (fun q => (q.1.toBoardGame, q.2.toFinset)) M) := by
      intro M
      rw [advanceGamesL_toBoardGames, List.map_map]
      rfl
    rw [key, hm]
  · intro j
    simp only [mergeMovesL]
    have key : List.map
        (fun g =>
        (g,
        respond pl.toPlay.arena g (ConState.positionList I st pl.toPlay.arena t g.board)
        (g.oppLimit - oppSpend I pl.toPlay.arena pl.toPlay.start t) (g.ourLimit - g.spent)))
        pl.toPlay.games =
        List.map (fun q => (q.1.toBoardGame, q.2.toFinset))
        (movesL I stL.ours pl.arena t (oppSpend I pl.arena pl.start t) pl.games) := by
      exact hm.symm
    rw [key]
    rw [fold_moves_toFinset, h.ours j, List.foldr_map]
    rfl
  · have key : List.map
        (fun g =>
        (g,
        respond pl.toPlay.arena g (ConState.positionList I st pl.toPlay.arena t g.board)
        (g.oppLimit - oppSpend I pl.toPlay.arena pl.toPlay.start t) (g.ourLimit - g.spent)))
        pl.toPlay.games =
        List.map (fun q => (q.1.toBoardGame, q.2.toFinset))
        (movesL I stL.ours pl.arena t (oppSpend I pl.arena pl.start t) pl.games) := by
      exact hm.symm
    rw [key]
    exact movesL_any_eq (movesL I stL.ours pl.arena t (oppSpend I pl.arena pl.start t) pl.games)


/-- Interpreting the list targets of an unbalanced play gives the unbalanced play of the
construction. -/
private theorem unbalancedPlayL_toPlay (ar : Arena) (t E a : ℕ) (σ : List Bool)
    (j k : Fin 3) :
    (unbalancedPlayL ar t E a σ j k).toPlay =
      ⟨ar, t, .unbalanced,
        [symGame j (vectors ar.tables.length \ {σ}) E, ⟨k, {σ}, a, E, 0⟩]⟩ := by
  have hσ : ([σ] : List (List Bool)).toFinset = {σ} := by simp
  have hc : (complL ar.tables.length [σ]).toFinset = vectors ar.tables.length \ {σ} := by
    rw [complL_toFinset, hσ]
  change (⟨ar, t, .unbalanced,
    [(⟨j, complL ar.tables.length [σ], E, E, 0⟩ : BoardGameL).toBoardGame,
     (⟨k, [σ], a, E, 0⟩ : BoardGameL).toBoardGame]⟩ : Play) = _
  simp only [BoardGameL.toBoardGame, symGame, hc, hσ]

/-- In Case 3b, the twin selects the same knight as the construction, or retains the same bishop
baseline. -/
theorem caseThreeL_tracks_3b (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) (pl : PlayL) (σ : List Bool) (bishop : Fin 3)
    (hk : pl.kind = .stacked σ bishop)
    (hgt : ¬ oppSpendL I pl.arena pl.start t ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0))
    (hle : oppSpendL I pl.arena pl.start t ≤ levelBudget pl.arena.tables 0) :
    TracksThree (caseThreeL I stL i t c rsL pl)
      (caseThree I st i t c rs pl.toPlay) := by
  unfold caseThreeL caseThree caseThreeAfterL caseThreeBishopL
  dsimp [PlayL.toPlay]
  have h_opp : oppSpend I pl.arena pl.start t = oppSpendL I pl.arena pl.start t := by
    rw [oppSpendL_eq]
  have h_limit : (List.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)
          (List.map BoardGameL.toBoardGame pl.games)) = 
      (List.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0) pl.games) := by
    rw [List.foldr_map]
    rfl
  simp only [h_opp, h_limit, hgt, ite_false, hk, ite_eq_left hle]
  have hkn : (pl.games.map BoardGameL.toBoardGame).map BoardGame.board =
      pl.games.map BoardGameL.board := by
    simp [List.map_map, Function.comp_def, BoardGameL.toBoardGame]
  have hs :
      (List.find?
      (fun j =>
      forcesB pl.arena (complL pl.arena.tables.length [σ]) (positionL I stL.ours pl.arena t j)
      (levelBudget pl.arena.tables 0) (levelBudget pl.arena.tables 0))
      (pl.games.map BoardGameL.board)) =
      (List.find?
      (fun j =>
      decide (Arena.Forces pl.arena (vectors pl.arena.tables.length \ {σ})
      (ConState.position I st pl.arena t j) (levelBudget pl.arena.tables 0)
      (levelBudget pl.arena.tables 0)))
      (List.map BoardGame.board (List.map BoardGameL.toBoardGame pl.games))) := by
    rw [hkn]
    congr 1; funext j
    simp only [forcesB, complL_toFinset, positionL_eq I h.ours]
    congr 3
  rw [hs]
  cases hf : List.find?
      (fun j =>
      decide (Arena.Forces pl.arena (vectors pl.arena.tables.length \ {σ})
      (ConState.position I st pl.arena t j) (levelBudget pl.arena.tables 0)
      (levelBudget pl.arena.tables 0)))
      (List.map BoardGame.board (List.map BoardGameL.toBoardGame pl.games))
  · refine ⟨⟨hr.c, hr.tables, ?_, rfl, hr.lastVisit, hr.lastActed⟩, h.ours, rfl⟩
    rw [hr.baseline]; rfl
  · rename_i j
    refine ⟨⟨hr.c, hr.tables, hr.baseline, ?_, hr.lastVisit, hr.lastActed⟩, h.ours, rfl⟩
    exact congrArg some
        (unbalancedPlayL_toPlay pl.arena t (levelBudget pl.arena.tables 0)
        (levelBudget pl.arena.tables 0 - oppSpendL I pl.arena pl.start t) σ j bishop)


/-- Case 3c only clears the baseline and play and closes a ghost accounting window. -/
theorem caseThreeL_tracks_3c (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) (pl : PlayL)
    (hgt : ¬ oppSpendL I pl.arena pl.start t ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0))
    (hstop : ∀ σ bishop, pl.kind = .stacked σ bishop →
      ¬ oppSpendL I pl.arena pl.start t ≤ levelBudget pl.arena.tables 0) :
    TracksThree (caseThreeL I stL i t c rsL pl)
      (caseThree I st i t c rs pl.toPlay) := by
  unfold caseThreeL caseThree caseThreeAfterL caseThreeStopL
  dsimp [PlayL.toPlay]
  have h_opp : oppSpend I pl.arena pl.start t = oppSpendL I pl.arena pl.start t := by
    rw [oppSpendL_eq]
  have h_limit : (List.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)
          (List.map BoardGameL.toBoardGame pl.games)) = 
      (List.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0) pl.games) := by
    rw [List.foldr_map]
    rfl
  simp only [h_opp, h_limit, hgt, ite_false]
  have hr' : TracksReq { rsL with play := none, baseline := none }
      { rs with play := none, baseline := none } := by
    cases hr
    constructor <;> try assumption
    · exact rfl
    · exact rfl
  have res := tracksReq_closeEpoch hr' i c t t false
  cases hk : pl.kind
  case balanced =>
    exact ⟨res, h.ours, rfl⟩
  case unbalanced =>
    exact ⟨res, h.ours, rfl⟩
  case stacked σ bishop =>
    have hd : ¬oppSpendL I pl.arena pl.start t ≤ levelBudget pl.arena.tables 0 := hstop _ _ hk
    simp only [hd, ite_false]
    exact ⟨res, h.ours, rfl⟩

/-- Assemble the three branches of Case 3. -/
theorem caseThreeL_tracks (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st) {rsL : ReqStateL} {rs : ReqState} (hr : TracksReq rsL rs)
    (i t c : ℕ) (pl : PlayL) :
    TracksThree (caseThreeL I stL i t c rsL pl)
      (caseThree I st i t c rs pl.toPlay) := by
  by_cases hle : oppSpendL I pl.arena pl.start t ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)
  · exact caseThreeL_tracks_3a I h hr i t c pl hle
  · by_cases hb : oppSpendL I pl.arena pl.start t ≤ levelBudget pl.arena.tables 0
    · cases hk : pl.kind with
      | balanced =>
        exact caseThreeL_tracks_3c I h hr i t c pl hle (by simp [hk])
      | unbalanced =>
        exact caseThreeL_tracks_3c I h hr i t c pl hle (by simp [hk])
      | stacked σ bishop => exact caseThreeL_tracks_3b I h hr i t c pl σ bishop hk hle hb
    · exact caseThreeL_tracks_3c I h hr i t c pl hle (fun _ _ _ => hb)

/-- Reset branch of the stage case distinction. -/
theorem stepCoreL_tracks_reset (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st)
    (hb : mustResetL I stL (Nat.unpair stL.stage).1 (Nat.unpair stL.stage).2
      (stL.stage + 1) = true) : TracksCore (stepCoreL I stL) (stepCore I st) := by
  have hbS : mustReset I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2
      (st.stage + 1) = true := by
    rw [← h.stage, ← mustResetL_eq I h]
    exact hb
  have hr := caseOneL_tracks h (Nat.unpair stL.stage).1 (stL.stage + 1)
  unfold stepCoreL stepCore
  simp only [hb, hbS, ↓reduceIte]
  unfold resetCoreL
  exact ⟨by simpa only [h.stage] using hr.1, h.ours,
    by simpa only [h.stage] using hr.2, rfl⟩

/-- Nonreset branches of the stage case distinction. -/
theorem stepCoreL_tracks_continue (I : Input) {stL : ConStateL} {st : ConState}
    (h : Tracks stL st)
    (hb : mustResetL I stL (Nat.unpair stL.stage).1 (Nat.unpair stL.stage).2
      (stL.stage + 1) = false) : TracksCore (stepCoreL I stL) (stepCore I st) := by
  have hbS : mustReset I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2
      (st.stage + 1) = false := by
    rw [← h.stage, ← mustResetL_eq I h]
    exact hb
  unfold stepCoreL stepCore
  simp only [hb, hbS, Bool.false_eq_true, ↓reduceIte]
  unfold continueCoreL
  simp only [h.stage]
  have hr := h.req (Nat.unpair st.stage).1
  cases hcL : (reqL stL (Nat.unpair st.stage).1).c with
  | none =>
    have hcS : (st.req (Nat.unpair st.stage).1).c = none := hr.c.symm.trans hcL
    simp only [hcS]
    exact ⟨hr, h.ours, h.nextC, rfl⟩
  | some c =>
    have hcS : (st.req (Nat.unpair st.stage).1).c = some c := hr.c.symm.trans hcL
    simp only [hcS]
    cases hpL : (reqL stL (Nat.unpair st.stage).1).play with
    | none =>
      have hpS : (st.req (Nat.unpair st.stage).1).play = none := by
        rw [← hr.play, hpL]
        rfl
      simp only [hpS]
      have htwo := caseTwoL_tracks I h hr (Nat.unpair st.stage).1 (st.stage + 1) c
      exact ⟨htwo.1, h.ours, h.nextC, htwo.2⟩
    | some pl =>
      have hpS : (st.req (Nat.unpair st.stage).1).play = some pl.toPlay := by
        rw [← hr.play, hpL]
        rfl
      simp only [hpS]
      have hthree := caseThreeL_tracks I h hr (Nat.unpair st.stage).1 (st.stage + 1) c pl
      exact ⟨hthree.1, hthree.2.1, h.nextC, hthree.2.2⟩

/-- The stage case distinction preserves tracking. -/
theorem stepCoreL_tracks (I : Input) {stL : ConStateL} {st : ConState} (h : Tracks stL st) :
    TracksCore (stepCoreL I stL) (stepCore I st) := by
  cases hb : mustResetL I stL (Nat.unpair stL.stage).1 (Nat.unpair stL.stage).2
      (stL.stage + 1) with
  | false => exact stepCoreL_tracks_continue I h hb
  | true => exact stepCoreL_tracks_reset I h hb

/-- Finishing a simulated core result preserves the padded requirement representation. -/
theorem finishStepL_tracks {stL : ConStateL} {st : ConState} (h : Tracks stL st)
    {rL : ReqStateL × (Fin 3 → List Str) × ℕ × Bool}
    {r : ReqState × (Fin 3 → Finset Str) × ℕ × Bool} (hr : TracksCore rL r)
    (hit : Bool) : Tracks (finishStepL stL rL hit)
      { stage := st.stage + 1, ours := r.2.1, nextC := r.2.2.1
        req := Function.update st.req (Nat.unpair st.stage).1
          { r.1 with
            lastVisit := st.stage + 1
            lastActed := if r.2.2.2 || hit then st.stage + 1 else r.1.lastActed } } := by
  obtain ⟨hr, ho, hc, ha⟩ := hr
  refine ⟨by dsimp [finishStepL]; rw [h.stage], ho, hc, ?_⟩
  intro k
  dsimp only [finishStepL, reqL]
  rw [← h.stage]
  by_cases hk : (Nat.unpair stL.stage).1 = k
  · subst k
    rw [getD_setReq_self, Function.update_self]
    exact ⟨hr.c, hr.tables, hr.baseline, hr.play, rfl, by rw [ha, hr.lastActed]⟩
  · rw [getD_setReq_ne _ _ _ _ hk, Function.update_of_ne (Ne.symm hk)]
    exact h.req k

/-- Updating the visited requirement and its action stage preserves tracking. -/
theorem stepL_tracks (I : Input) {stL : ConStateL} {st : ConState} (h : Tracks stL st) :
    Tracks (stepL I stL) (step I st) := by
  unfold stepL step
  rw [pendingHitL_eq I (h.req _), h.stage]
  exact finishStepL_tracks h (stepCoreL_tracks I h) _

/-- Iteration of the twin simulates every stage of the construction. -/
theorem stateAtL_tracks (I : Input) (s : ℕ) : Tracks (stateAtL I s) (stateAt I s) := by
  induction s with
  | zero => exact tracks_default
  | succ s ih => exact stepL_tracks I ih

/-- Board membership can be read from the simulated state. -/
theorem oursBL_eq (I : Input) (j : Fin 3) (s : ℕ) (τ : Str) :
    oursBL I j s τ = oursB I j s τ := by
  have h := (stateAtL_tracks I s).ours j
  simp only [oursBL, oursB, oursAt, ← h, List.mem_toFinset]

/-- The stored agreement can be read from the simulated state. -/
theorem agreedBitL_eq (I : Input) (i s k : ℕ) :
    agreedBitL I i s k = agreedBit I i s k := by
  unfold agreedBitL agreedBit
  rw [((stateAtL_tracks I s).req i).baseline]

/-! ## Mathlib-only list and finite-function computability tools -/

section ListTools

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

/-- One total left-fold step, consuming the head when present. -/
def listFoldStep (H : β × γ → γ) (p : List β × γ) : List β × γ :=
  (p.1.tail, p.1.head?.elim p.2 fun b => H (b, p.2))

omit [Primcodable β] [Primcodable γ] in
/-- Iterating the total fold step for the list length computes a left fold. -/
theorem listFoldStep_iterate (H : β × γ → γ) (l : List β) (acc : γ) :
    (listFoldStep H)^[l.length] (l, acc) = ([], l.foldl (fun s b => H (b, s)) acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    exact ih (H (b, acc))

omit [Primcodable γ] in
/-- Constant-step natural recursion agrees with function iteration. -/
theorem nat_rec_eq_iterate (f : γ → γ) (z : γ) (n : ℕ) :
    Nat.rec z (fun _ s => f s) n = f^[n] z := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply'] using congrArg f ih

/-- Folds with an oracle-computable body are computable. -/
theorem computable_list_foldr {f : α → List β} {g : α → γ} {h : α → β × γ → γ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a => (f a).foldr (fun b s => h a (b, s)) (g a) := by
  have hl : Computable fun p : α × (List β × γ) => p.2.1 :=
    Computable.fst.comp Computable.snd
  have hb : Computable fun p : (α × (List β × γ)) × β => h p.1.1 (p.2, p.1.2.2) :=
    hh.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.pair (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hstep : Computable fun p : α × (List β × γ) => listFoldStep (h p.1) p.2 := by
    have ht := Primrec.list_tail.to_comp.comp hl
    have ha := Computable.option_casesOn (Primrec.list_head?.to_comp.comp hl)
      (Computable.snd.comp Computable.snd) hb.to₂
    exact (ht.pair ha).of_eq fun p => by
      unfold listFoldStep
      cases p.2.1.head? <;> rfl
  have hr := Computable.nat_rec (Computable.list_length.comp hf)
    ((Computable.list_reverse.comp hf).pair hg)
    (hstep.comp (Computable.fst.pair (Computable.snd.comp Computable.snd))).to₂
  refine (Computable.snd.comp hr).of_eq fun a => ?_
  change (Nat.rec (motive := fun _ => List β × γ) ((f a).reverse, g a) (fun _ s => listFoldStep
    (h a) s)
    (f a).length).2 = _
  rw [nat_rec_eq_iterate]
  rw [← List.length_reverse (as := f a), listFoldStep_iterate]
  exact List.foldl_reverse

/-- Mapping with an oracle-computable body is a fold with computable cons. -/
theorem computable_list_map {f : α → List β} {g : α → β → γ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) := by
  refine (computable_list_foldr hf (Computable.const [])
    (Computable.list_cons.comp
      (hg.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂).of_eq fun a => ?_
  simp only [List.map_eq_foldr]

/-- Filtering with an oracle-computable predicate is a fold with a conditional cons. -/
theorem computable_list_filter {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) :
    Computable fun a => (f a).filter (p a) := by
  refine (computable_list_foldr hf (Computable.const [])
    (Computable.cond
      (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.list_cons.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂).of_eq fun a => ?_
  simpa only [] using (List.filter_eq_foldr (p a) (f a)).symm

omit [Primcodable β] in
/-- The list existential Boolean test is a right fold. -/
theorem any_eq_foldr (p : β → Bool) (l : List β) :
    l.any p = l.foldr (fun b s => p b || s) false := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

omit [Primcodable β] in
/-- The first satisfying element is computed by a right fold. -/
theorem find_eq_foldr (p : β → Bool) (l : List β) :
    l.find? p = l.foldr (fun b s => bif p b then some b else s) none := by
  induction l with
  | nil => rfl
  | cons b l ih => cases hb : p b <;> simp [hb, ih]

/-- Finite existential search with an oracle-computable predicate is computable. -/
theorem computable_list_any {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) :
    Computable fun a => (f a).any (p a) := by
  refine (computable_list_foldr hf (Computable.const false)
    (Primrec.or.to_comp.comp
      (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂).of_eq fun a => ?_
  simpa only [] using (any_eq_foldr (p a) (f a)).symm

/-- First-element search with an oracle-computable predicate is computable. -/
theorem computable_list_find {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) :
    Computable fun a => (f a).find? (p a) := by
  refine (computable_list_foldr hf (Computable.const none)
    (Computable.cond
      (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.option_some.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂).of_eq fun a => ?_
  simpa only [] using (find_eq_foldr (p a) (f a)).symm

/-- A computable family indexed by a fixed finite type is a computable finite function. -/
theorem computable_fin_curry {n : ℕ} {f : α → Fin n → β} (hf : Computable₂ f) :
    Computable f := by
  refine (Primrec.vector_get'.to_comp.comp
    (Computable.vector_ofFn fun i => hf.comp Computable.id (Computable.const i))).of_eq
      fun a => ?_
  funext i
  simp

/-- Filtering primitive recursive lists by a primitive recursive predicate is primitive
recursive, using a conditional-cons fold. -/
theorem primrec_list_filter {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).filter (p a) := by
  refine (Primrec.list_foldr hf (Primrec.const [])
    (Primrec.cond
      (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => ?_
  simpa only [] using (List.filter_eq_foldr (p a) (f a)).symm

/-- Decidable membership in a finite list is primitive recursive. -/
theorem list_mem_primrec [DecidableEq β] :
    Primrec fun q : β × List β => decide (q.1 ∈ q.2) := by
  refine (Primrec.list_foldr Primrec.snd (Primrec.const false)
    (Primrec.or.comp
      (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq ?_
  intro ⟨a, l⟩
  induction l with
  | nil => rfl
  | cons b l ih =>
    apply Bool.eq_iff_iff.mpr
    simp [List.foldr_cons, ih]

/-- Deduplication is primitive recursive. -/
theorem list_dedup_primrec [DecidableEq β] : Primrec (@List.dedup β _) := by
  have hh : Primrec fun p : List β × (β × List β) =>
      bif decide (p.2.1 ∈ p.2.2) then p.2.2 else p.2.1 :: p.2.2 :=
    Primrec.cond (list_mem_primrec.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd) (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  refine (Primrec.list_foldr Primrec.id (Primrec.const []) hh.to₂).of_eq fun l => ?_
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.dedup_cons']
    cases h : decide (b ∈ l.dedup) <;> simp_all

/-- Enumerating sublists in the original list order is primitive recursive. -/
theorem list_sublists_primrec : Primrec (@List.sublists β) := by
  have hb : Primrec₂ fun (p : List β × (β × List (List β))) (v : List β) =>
      [v, p.2.1 :: v] :=
    (Primrec.list_cons.comp Primrec.snd
      (Primrec.list_cons.comp (Primrec.list_cons.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
        (Primrec.const []))).to₂
  refine (Primrec.list_foldr Primrec.id (Primrec.const [[]])
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) hb).to₂).of_eq fun l => ?_
  change l.foldr (fun a out => out.flatMap fun v => [v, a :: v]) [[]] = l.sublists
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.foldr_cons, List.sublists_cons, ih, List.bind_eq_flatMap]

/-- The ordered product of two lists is primitive recursive. -/
theorem list_product_primrec : Primrec fun q : List β × List γ => q.1.product q.2 := by
  exact Primrec.list_flatMap Primrec.fst
    (Primrec.list_map (Primrec.snd.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂

/-- Repeating a fixed default element is primitive recursive. -/
theorem list_replicate_primrec (b : β) : Primrec fun n : ℕ => List.replicate n b := by
  have hh : Primrec₂ fun (_ : Unit) (q : ℕ × List β) => b :: q.2 :=
    (Primrec.list_cons.comp (Primrec.const b) (Primrec.snd.comp Primrec.snd)).to₂
  exact ((Primrec.nat_rec (Primrec.const []) hh).comp
    (Primrec.const ()) Primrec.id).of_eq fun n => by
      change Nat.rec [] (fun _ s => b :: s) n = List.replicate n b
      induction n with
      | zero => rfl
      | succ n ih => simpa [List.replicate_succ] using congrArg (List.cons b) ih

end ListTools

/-! ## Primitive recursive finite data operations -/

/-- Requirement lookup uses a primitive recursive projection and `List.getD`. -/
theorem reqL_primrec : Primrec fun p : ConStateL × ℕ => reqL p.1 p.2 := by
  exact (Primrec.list_getD ({} : ReqStateL)).comp
    (ConStateL.req_primrec.comp Primrec.fst) Primrec.snd

/-- Padding and overwriting a requirement are primitive recursive. -/
theorem setReq_primrec :
    Primrec fun p : List ReqStateL × ℕ × ReqStateL => setReq p.1 p.2.1 p.2.2 := by
  have hp : Primrec fun p : List ReqStateL × ℕ × ReqStateL =>
      List.replicate (p.2.1 + 1 - p.1.length) ({} : ReqStateL) :=
    (list_replicate_primrec ({} : ReqStateL)).comp
      (Primrec.nat_sub.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_length.comp Primrec.fst))
  exact (Primrec.list_set.comp (Primrec.list_append.comp Primrec.fst hp) Primrec.snd).of_eq
    fun _ => rfl

/-- Table queries are primitive recursive, using two nested list operations. -/
theorem queries_primrec : Primrec TTable.queries := by
  exact Primrec.list_flatMap Primrec.id
    (Primrec.list_map Primrec.snd (Primrec.fst.comp Primrec.snd).to₂).to₂

/-- The maximum of the lengths of a list of strings is primitive recursive. -/
theorem maxStrings_primrec :
    Primrec fun l : List Str => l.foldr (fun z n => max z.length n) 0 := by
  exact Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- The maximal query length is primitive recursive. -/
theorem maxLen_primrec : Primrec maxLen := by
  exact maxStrings_primrec.comp
    (Primrec.list_flatMap Primrec.id (queries_primrec.comp Primrec.snd).to₂)

/-- Constructing an arena from an exponent and tables is primitive recursive. -/
theorem arenaOf_primrec : Primrec fun p : ℕ × List TTable => arenaOf p.1 p.2 := by
  exact (Arena.mk_primrec.comp (Primrec.snd.pair
    (Primrec.succ.comp (Primrec.nat_add.comp Primrec.fst
      (maxLen_primrec.comp Primrec.snd))))).of_eq fun _ => rfl

/-- The arena board list is primitive recursive. -/
theorem boardList_primrec : Primrec Arena.boardList := by
  exact list_dedup_primrec.comp
    (Primrec.list_flatMap Arena.tables_primrec (queries_primrec.comp Primrec.snd).to₂)

/-- The budget of a stack level is primitive recursive. -/
theorem levelBudget_primrec :
    Primrec fun p : List TTable × ℕ => levelBudget p.1 p.2 := by
  have hp : Primrec₂ fun a b : ℕ => a ^ b := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact (hp.comp (Primrec.const 2) (Primrec.nat_sub.comp
    (Primrec.succ.comp (maxLen_primrec.comp Primrec.fst)) Primrec.snd)).of_eq fun _ => rfl

/-- All outcome vectors can be enumerated by primitive recursion. -/
theorem allVec_primrec : Primrec allVec := by
  have hb : Primrec₂ fun (_ : Unit × (ℕ × List (List Bool))) (v : List Bool) =>
      [v ++ [false], v ++ [true]] :=
    (Primrec.list_cons.comp (Primrec.list_concat.comp Primrec.snd (Primrec.const false))
      (Primrec.list_cons.comp (Primrec.list_concat.comp Primrec.snd (Primrec.const true))
        (Primrec.const []))).to₂
  have hh : Primrec₂ fun (_ : Unit) (q : ℕ × List (List Bool)) =>
      q.2.flatMap (fun v => [v ++ [false], v ++ [true]]) :=
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) hb).to₂
  refine ((Primrec.nat_rec (Primrec.const [[]]) hh).comp
    (Primrec.const ()) Primrec.id).of_eq fun n => ?_
  change Nat.rec [[]] (fun _ l => l.flatMap fun v => [v ++ [false], v ++ [true]]) n = allVec n
  induction n with
  | zero => rfl
  | succ n ih => simp only [allVec, ih]

/-- The list complement is primitive recursive. -/
theorem complL_primrec :
    Primrec fun p : ℕ × List (List Bool) => complL p.1 p.2 := by
  refine (primrec_list_filter (allVec_primrec.comp Primrec.fst)
    (Primrec.not.comp (list_mem_primrec.comp
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))).to₂).of_eq fun p => ?_
  apply List.filter_congr
  intro σ _
  apply Bool.eq_iff_iff.mpr
  simp

/-- The list intersection is primitive recursive. -/
theorem interL_primrec :
    Primrec fun p : List (List Bool) × List (List Bool) => interL p.1 p.2 := by
  refine (primrec_list_filter Primrec.fst
    (list_mem_primrec.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂).of_eq
    fun p => ?_
  apply List.filter_congr
  intro σ _
  exact decide_eq_decide.mpr Iff.rfl

/-- List difference is primitive recursive. -/
theorem diffL_primrec : Primrec fun p : List Str × List Str => diffL p.1 p.2 := by
  refine (primrec_list_filter Primrec.fst
    (Primrec.not.comp (list_mem_primrec.comp
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))).to₂).of_eq fun p => ?_
  apply List.filter_congr
  intro τ _
  apply Bool.eq_iff_iff.mpr
  simp

/-- A string's cost in units is primitive recursive. -/
theorem unitWeight_primrec : Primrec fun p : ℕ × Str => unitWeight p.1 p.2 := by
  have hp : Primrec₂ fun a b : ℕ => a ^ b := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact (hp.comp (Primrec.const 2) (Primrec.nat_sub.comp
    (Primrec.succ.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd))).of_eq
      fun _ => rfl

/-- Summation of a list of natural numbers is primitive recursive. -/
theorem list_sum_primrec : Primrec fun l : List ℕ => l.sum := by
  refine (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun l => ?_
  change l.foldr (fun b s => b + s) 0 = l.sum
  induction l with
  | nil => rfl
  | cons n l ih => simp only [List.foldr_cons, List.sum_cons, ih]

/-- Summing list costs is primitive recursive. -/
theorem costU_primrec : Primrec fun p : ℕ × List Str => costU p.1 p.2 := by
  exact list_sum_primrec.comp
    (Primrec.list_map Primrec.snd
      (unitWeight_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂)

/-- The outcome of a list position is primitive recursive. -/
theorem valueL_primrec : Primrec fun p : Arena × List Str => valueL p.1 p.2 := by
  exact Kolmogorov.RandomStrings.TTMeet.valueL_primrec

/-- The other-board choice is primitive recursive on its finite domain. -/
theorem otherBoard_primrec : Primrec otherBoard := Primrec.dom_finite _

/-- The third-board choice is primitive recursive on its finite product domain. -/
theorem thirdBoard_primrec : Primrec fun p : Fin 3 × Fin 3 => thirdBoard p.1 p.2 :=
  Primrec.fin_curry₁.mpr fun j => Primrec.dom_finite (thirdBoard j)

/-- The queries defined so far are primitive recursive in the requirement and stage bounds. -/
theorem definedStrings_primrec :
    Primrec fun p : ℕ × ℕ => definedStrings p.1 p.2 := by
  have ht : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ =>
      ((tableAt p.1.2 p.2 p.1.1.2).getD []).queries :=
    queries_primrec.comp (Primrec.option_getD.comp
      (tableAt_primrec.comp ((Primrec.snd.comp Primrec.fst).pair
        (Primrec.snd.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
      (Primrec.const []))
  exact Primrec.list_flatMap (Primrec.list_range.comp Primrec.fst)
    (Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.snd.comp Primrec.fst)) ht.to₂).to₂

/-- The new exponent is primitive recursive. -/
theorem newCL_primrec : Primrec fun p : ℕ × ℕ × ℕ => newCL p.1 p.2.1 p.2.2 := by
  exact Primrec.nat_max.comp
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 7))
    (Primrec.nat_max.comp Primrec.fst
      (maxStrings_primrec.comp (definedStrings_primrec.comp Primrec.snd)))

/-- Case 1 uses only primitive recursive field projections and the new exponent. -/
theorem caseOneL_primrec :
    Primrec fun p : ConStateL × ℕ × ℕ => caseOneL p.1 p.2.1 p.2.2 := by
  have hr : Primrec fun p : ConStateL × ℕ × ℕ => reqL p.1 p.2.1 :=
    reqL_primrec.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have hc : Primrec fun p : ConStateL × ℕ × ℕ => newCL p.1.nextC p.2.1 p.2.2 :=
    newCL_primrec.comp ((ConStateL.nextC_primrec.comp Primrec.fst).pair Primrec.snd)
  have hu : Primrec fun p : ConStateL × ℕ × ℕ =>
      ({ reqL p.1 p.2.1 with
        c := some (newCL p.1.nextC p.2.1 p.2.2)
        baseline := none
        play := none } : ReqStateL) :=
    ReqStateL.mk_primrec.comp
      ((Primrec.option_some.comp hc).pair ((ReqStateL.tables_primrec.comp hr).pair
        ((Primrec.const none).pair ((Primrec.const none).pair
          ((ReqStateL.lastVisit_primrec.comp hr).pair (ReqStateL.lastActed_primrec.comp hr))))))
  exact (hu.pair (Primrec.succ.comp (Primrec.succ.comp hc))).of_eq fun _ => rfl

/-- Symmetric list games have primitive recursive construction. -/
theorem symGameL_primrec :
    Primrec fun p : Fin 3 × List (List Bool) × ℕ => symGameL p.1 p.2.1 p.2.2 := by
  exact BoardGameL.mk_primrec.comp
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      ((Primrec.snd.comp Primrec.snd).pair
        ((Primrec.snd.comp Primrec.snd).pair (Primrec.const 0)))))

/-- Step 1 of the proof of `balancedPlayL_primrec`: the balanced play started on a split verdict
is primitive recursive. -/
private theorem balancedPlayL_primrec_step1_inl :
    Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
      (some
          ⟨p.1, p.2.1, .balanced,
          [symGameL p.2.2.2.1 p.2.2.2.2.2 p.2.2.1,
          symGameL p.2.2.2.2.1 (complL p.1.tables.length p.2.2.2.2.2) p.2.2.1]⟩ :
          Option PlayL) := by
  apply Primrec.option_some.comp
  have h_ar : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) => p.1 :=
    Primrec.fst
  have h_t : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have h_g : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
      [symGameL p.2.2.2.1 p.2.2.2.2.2 p.2.2.1,
      symGameL p.2.2.2.2.1 (complL p.1.tables.length p.2.2.2.2.2) p.2.2.1] := by
    have h_g1 : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
        symGameL p.2.2.2.1 p.2.2.2.2.2 p.2.2.1 := by
      have h_j : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) => p.2.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      have h_S : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
          p.2.2.2.2.2 :=
        Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      have h_E : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) => p.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
      exact symGameL_primrec.comp (h_j.pair (h_S.pair h_E))
    have h_g2 : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
        symGameL p.2.2.2.2.1 (complL p.1.tables.length p.2.2.2.2.2) p.2.2.1 := by
      have h_k : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
          p.2.2.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      have h_S2 : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
          complL p.1.tables.length p.2.2.2.2.2 := by
        have h_len : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
            p.1.tables.length := Primrec.list_length.comp (Arena.tables_primrec.comp Primrec.fst)
        have h_S : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
            p.2.2.2.2.2 :=
          Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        exact complL_primrec.comp (h_len.pair h_S)
      have h_E : Primrec fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) => p.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
      exact symGameL_primrec.comp (h_k.pair (h_S2.pair h_E))
    exact Primrec₂.comp Primrec.list_cons h_g1
        (Primrec₂.comp Primrec.list_cons h_g2 (Primrec.const []))
  exact PlayL.mk_primrec.comp (h_ar.pair (h_t.pair ((Primrec.const _).pair h_g)))

private theorem balancedPlayL_primrec_step2_inr_inl :
    Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
      (some
          ⟨p.1, p.2.1, .balanced,
          [symGameL 0 p.2.2.2.1 p.2.2.1, symGameL 1 p.2.2.2.2 p.2.2.1,
          symGameL 2 (complL p.1.tables.length (interL p.2.2.2.1 p.2.2.2.2)) p.2.2.1]⟩ :
          Option PlayL) := by
  apply Primrec.option_some.comp
  have h_ar : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) => p.1 :=
    Primrec.fst
  have h_t : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have h_g : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
      [symGameL 0 p.2.2.2.1 p.2.2.1, symGameL 1 p.2.2.2.2 p.2.2.1,
      symGameL 2 (complL p.1.tables.length (interL p.2.2.2.1 p.2.2.2.2)) p.2.2.1] := by
    have h_g1 : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
        symGameL 0 p.2.2.2.1 p.2.2.1 := by
      have h_S : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
          p.2.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      have h_E : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) => p.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
      exact symGameL_primrec.comp ((Primrec.const 0).pair (h_S.pair h_E))
    have h_g2 : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
        symGameL 1 p.2.2.2.2 p.2.2.1 := by
      have h_S : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
          p.2.2.2.2 := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      have h_E : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) => p.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
      exact symGameL_primrec.comp ((Primrec.const 1).pair (h_S.pair h_E))
    have h_g3 : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
        symGameL 2 (complL p.1.tables.length (interL p.2.2.2.1 p.2.2.2.2)) p.2.2.1 := by
      have h_len : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
          p.1.tables.length := Primrec.list_length.comp (Arena.tables_primrec.comp Primrec.fst)
      have h_inter : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
          interL p.2.2.2.1 p.2.2.2.2 :=
        interL_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      have h_S : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
          complL p.1.tables.length (interL p.2.2.2.1 p.2.2.2.2) :=
        complL_primrec.comp (h_len.pair h_inter)
      have h_E : Primrec fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) => p.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
      exact symGameL_primrec.comp ((Primrec.const 2).pair (h_S.pair h_E))
    exact Primrec₂.comp Primrec.list_cons h_g1
        (Primrec₂.comp Primrec.list_cons h_g2
        (Primrec₂.comp Primrec.list_cons h_g3 (Primrec.const [])))
  exact PlayL.mk_primrec.comp (h_ar.pair (h_t.pair ((Primrec.const _).pair h_g)))

private theorem balancedPlayL_primrec_step3_none :
    Primrec fun _p : Arena × ℕ × ℕ × List Bool =>
      (none : Option PlayL) := Primrec.const none

/-- Starting balanced games is primitive recursive in the encoded verdict. -/
theorem balancedPlayL_primrec :
    Primrec fun p : Arena × ℕ × ℕ × TopOutcomeL => balancedPlayL p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  let InnerType :=
    ((Fin 3 × Fin 3 × List (List Bool)) ⊕ ((List (List Bool) × List (List Bool)) ⊕ List Bool))
  have H : (fun p : Arena × ℕ × ℕ × TopOutcomeL => balancedPlayL p.1 p.2.1 p.2.2.1 p.2.2.2)
         =
             (fun p : Arena × ℕ × ℕ × TopOutcomeL =>
             Option.casesOn (motive := fun _ => Option PlayL) p.2.2.2 none (fun v : InnerType =>
           Sum.casesOn (motive := fun _ => Option PlayL) v
             (fun v_inl =>
               (fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
                 some
                     (⟨p.1, p.2.1, .balanced,
                     [symGameL p.2.2.2.1 p.2.2.2.2.2 p.2.2.1,
                     symGameL p.2.2.2.2.1 (complL p.1.tables.length p.2.2.2.2.2) p.2.2.1]⟩ : PlayL))
               (p.1, p.2.1, p.2.2.1, v_inl))
             (fun v_inr =>
               Sum.casesOn (motive := fun _ => Option PlayL) v_inr
                 (fun v_inr_inl =>
                   (fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
                     some
                         (⟨p.1, p.2.1, .balanced,
                         [symGameL 0 p.2.2.2.1 p.2.2.1, symGameL 1 p.2.2.2.2 p.2.2.1,
                         symGameL 2 (complL p.1.tables.length (interL p.2.2.2.1 p.2.2.2.2))
                         p.2.2.1]⟩ : PlayL))
                   (p.1, p.2.1, p.2.2.1, v_inr_inl))
                 (fun v_inr_inr =>
                   (fun _ : Arena × ℕ × ℕ × List Bool => (none : Option PlayL))
                   (p.1, p.2.1, p.2.2.1, v_inr_inr))))) := by
    funext p
    rcases p with ⟨ar, t, E, v⟩
    cases v with
    | none => rfl
    | some v' =>
      cases v' with
      | inl v_inl =>
        rcases v_inl with ⟨j, k, S⟩
        rfl
      | inr v_inr =>
        cases v_inr with
        | inl v_inr_inl =>
          rcases v_inr_inl with ⟨S, T⟩
          rfl
        | inr v_inr_inr =>
          rfl
  rw [H]
  have h_inner : Primrec fun p : (Arena × ℕ × ℕ × TopOutcomeL) × InnerType =>
      Sum.casesOn (motive := fun _ => Option PlayL) p.2
      (fun v_inl =>
      (fun p : Arena × ℕ × ℕ × (Fin 3 × Fin 3 × List (List Bool)) =>
      some
      (⟨p.1, p.2.1, .balanced,
      [symGameL p.2.2.2.1 p.2.2.2.2.2 p.2.2.1,
      symGameL p.2.2.2.2.1 (complL p.1.tables.length p.2.2.2.2.2) p.2.2.1]⟩ : PlayL))
      (p.1.1, p.1.2.1, p.1.2.2.1, v_inl))
      (fun v_inr =>
      Sum.casesOn (motive := fun _ => Option PlayL) v_inr
      (fun v_inr_inl =>
      (fun p : Arena × ℕ × ℕ × (List (List Bool) × List (List Bool)) =>
      some
      (⟨p.1, p.2.1, .balanced,
      [symGameL 0 p.2.2.2.1 p.2.2.1, symGameL 1 p.2.2.2.2 p.2.2.1,
      symGameL 2 (complL p.1.tables.length (interL p.2.2.2.1 p.2.2.2.2)) p.2.2.1]⟩ : PlayL))
      (p.1.1, p.1.2.1, p.1.2.2.1, v_inr_inl))
      (fun v_inr_inr =>
      (fun p : Arena × ℕ × ℕ × List Bool => (none : Option PlayL))
      (p.1.1, p.1.2.1, p.1.2.2.1, v_inr_inr))) := by
    apply Primrec.sumCasesOn Primrec.snd
    · have h_trans1 : Primrec
          fun p :
          (((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) × (Fin 3 × Fin 3 × List (List Bool))) =>
          (p.1.1.1, p.1.1.2.1, p.1.1.2.2.1, p.2) := by
        have h1 : Primrec
            fun p :
            (((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) × (Fin 3 × Fin 3 × List (List Bool))) =>
            p.1.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
        have h2 : Primrec
            fun p :
            (((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) × (Fin 3 × Fin 3 × List (List Bool))) =>
            p.1.1.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        have h3 : Primrec
            fun p :
            (((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) × (Fin 3 × Fin 3 × List (List Bool))) =>
            p.1.1.2.2.1 :=
          Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        exact h1.pair (h2.pair (h3.pair Primrec.snd))
      exact balancedPlayL_primrec_step1_inl.comp h_trans1
    · apply Primrec.sumCasesOn Primrec.snd
      · have h_trans2 : Primrec
            fun p :
            ((((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) ×
            ((List (List Bool) × List (List Bool)) ⊕ List Bool)) ×
            (List (List Bool) × List (List Bool))) =>
            (p.1.1.1.1, p.1.1.1.2.1, p.1.1.1.2.2.1, p.2) := by
          have h1 : Primrec
              fun p :
              ((((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) ×
              ((List (List Bool) × List (List Bool)) ⊕ List Bool)) ×
              (List (List Bool) × List (List Bool))) => p.1.1.1.1 :=
            Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          have h2 : Primrec
              fun p :
              ((((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) ×
              ((List (List Bool) × List (List Bool)) ⊕ List Bool)) ×
              (List (List Bool) × List (List Bool))) => p.1.1.1.2.1 :=
            Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          have h3 : Primrec
              fun p :
              ((((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) ×
              ((List (List Bool) × List (List Bool)) ⊕ List Bool)) ×
              (List (List Bool) × List (List Bool))) => p.1.1.1.2.2.1 :=
            Primrec.fst.comp
                (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
          exact h1.pair (h2.pair (h3.pair Primrec.snd))
        exact balancedPlayL_primrec_step2_inr_inl.comp h_trans2
      · have h_trans3 : Primrec
            fun p :
            ((((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) ×
            ((List (List Bool) × List (List Bool)) ⊕ List Bool)) × List Bool) =>
            (p.1.1.1.1, p.1.1.1.2.1, p.1.1.1.2.2.1, p.2) := by
          have h1 : Primrec
              fun p :
              ((((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) ×
              ((List (List Bool) × List (List Bool)) ⊕ List Bool)) × List Bool) => p.1.1.1.1 :=
            Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          have h2 : Primrec
              fun p :
              ((((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) ×
              ((List (List Bool) × List (List Bool)) ⊕ List Bool)) × List Bool) => p.1.1.1.2.1 :=
            Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          have h3 : Primrec
              fun p :
              ((((Arena × ℕ × ℕ × TopOutcomeL) × InnerType) ×
              ((List (List Bool) × List (List Bool)) ⊕ List Bool)) × List Bool) => p.1.1.1.2.2.1 :=
            Primrec.fst.comp
                (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
          exact h1.pair (h2.pair (h3.pair Primrec.snd))
        exact balancedPlayL_primrec_step3_none.comp h_trans3
  have h_cond : Primrec fun p : Arena × ℕ × ℕ × TopOutcomeL => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.option_casesOn h_cond (Primrec.const none) h_inner

/-- Unbalanced game construction is primitive recursive. -/
theorem unbalancedPlayL_primrec :
    Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 =>
      unbalancedPlayL p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 := by
  dsimp only [unbalancedPlayL]
  have hgames : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 =>
      [symGameL p.2.2.2.2.2.1 (complL p.1.tables.length [p.2.2.2.2.1]) p.2.2.1,
        (⟨p.2.2.2.2.2.2, [p.2.2.2.2.1], p.2.2.2.1, p.2.2.1, 0⟩ : BoardGameL)] := by
    have hl1 : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 => 
      symGameL p.2.2.2.2.2.1 (complL p.1.tables.length [p.2.2.2.2.1]) p.2.2.1 := by
      have hj : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 => p.2.2.2.2.2.1 := by
        exact Primrec.fst.comp
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      have hcompl : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 =>
          complL p.1.tables.length [p.2.2.2.2.1] := by
        have hlen : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 =>
            p.1.tables.length := by
          exact Primrec.list_length.comp (Arena.tables_primrec.comp Primrec.fst)
        have hsig : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 =>
            [p.2.2.2.2.1] := by
          exact Primrec.of_eq
              (Primrec₂.comp Primrec.list_cons
              (Primrec.fst.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
              (Primrec.const [])) (fun _ => rfl)
        exact complL_primrec.comp (hlen.pair hsig)
      have hE : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 => p.2.2.1 := by
        exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
      exact symGameL_primrec.comp (hj.pair (hcompl.pair hE))
    have hl2 : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 => 
      [(⟨p.2.2.2.2.2.2, [p.2.2.2.2.1], p.2.2.2.1, p.2.2.1, 0⟩ : BoardGameL)] := by
      have hbg : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 => 
        (⟨p.2.2.2.2.2.2, [p.2.2.2.2.1], p.2.2.2.1, p.2.2.1, 0⟩ : BoardGameL) := by
        have hk : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 =>
            p.2.2.2.2.2.2 := by
          exact Primrec.snd.comp
              (Primrec.snd.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
        have hsig : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 =>
            [p.2.2.2.2.1] := by
          exact Primrec.of_eq
              (Primrec₂.comp Primrec.list_cons
              (Primrec.fst.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
              (Primrec.const [])) (fun _ => rfl)
        have ha : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 => p.2.2.2.1 := by
          exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        have hE : Primrec fun p : Arena × ℕ × ℕ × ℕ × List Bool × Fin 3 × Fin 3 => p.2.2.1 := by
          exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
        exact BoardGameL.mk_primrec.comp (hk.pair (hsig.pair (ha.pair (hE.pair (Primrec.const 0)))))
      exact Primrec.of_eq (Primrec₂.comp Primrec.list_cons hbg (Primrec.const [])) (fun _ => rfl)
    exact Primrec.of_eq (Primrec₂.comp Primrec.list_cons hl1 hl2) (fun _ => rfl)
  exact PlayL.mk_primrec.comp (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair
      ((Primrec.const .unbalanced).pair
        hgames)))

/-- Consuming a fresh top verdict is primitive recursive. -/
theorem examineVerdictL_primrec :
    Primrec fun p : Arena × ℕ × ℕ × ReqStateL × TopOutcomeL =>
      examineVerdictL p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have ht : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × TopOutcomeL => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hrs : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × TopOutcomeL => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hv : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × TopOutcomeL => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hbal : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × TopOutcomeL =>
      balancedPlayL p.1 p.2.1 p.2.2.1 p.2.2.2.2 :=
    balancedPlayL_primrec.comp
        (Primrec.fst.pair (ht.pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair hv)))
  
  have hupd : Primrec₂ fun (p : Arena × ℕ × ℕ × ReqStateL × TopOutcomeL) pl =>
      (Sum.inl ({p.2.2.2.1 with play := some pl}, true) : (ReqStateL × Bool) ⊕
          (ReqStateL × List Bool)) :=
    Primrec.sumInl.comp (Primrec.pair
      (ReqStateL.mk_primrec.comp ((ReqStateL.c_primrec.comp (hrs.comp Primrec.fst)).pair
        ((ReqStateL.tables_primrec.comp (hrs.comp Primrec.fst)).pair
          ((ReqStateL.baseline_primrec.comp (hrs.comp Primrec.fst)).pair
            ((Primrec.option_some.comp Primrec.snd).pair
              ((ReqStateL.lastVisit_primrec.comp (hrs.comp Primrec.fst)).pair
                (ReqStateL.lastActed_primrec.comp (hrs.comp Primrec.fst))))))))
      (Primrec.const true))
  have hdef : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × TopOutcomeL =>
      match balancedPlayL p.1 p.2.1 p.2.2.1 p.2.2.2.2 with
      | some pl => Sum.inl ({p.2.2.2.1 with play := some pl}, true)
      | none => Sum.inl (p.2.2.2.1, false) :=
    (Primrec.option_casesOn hbal (Primrec.sumInl.comp (hrs.pair (Primrec.const false))) hupd).of_eq
      fun p => by cases balancedPlayL p.1 p.2.1 p.2.2.1 p.2.2.2.2 <;> rfl
  have hprin : Primrec₂ fun (p : Arena × ℕ × ℕ × ReqStateL × TopOutcomeL) (σ : List Bool) =>
      (Sum.inr ({p.2.2.2.1 with baseline := some ⟨σ, fun _ => p.2.1⟩}, σ) : (ReqStateL × Bool) ⊕
          (ReqStateL × List Bool)) :=
    Primrec.sumInr.comp (Primrec.pair
      (ReqStateL.mk_primrec.comp ((ReqStateL.c_primrec.comp (hrs.comp Primrec.fst)).pair
        ((ReqStateL.tables_primrec.comp (hrs.comp Primrec.fst)).pair
          ((Primrec.option_some.comp
              (Baseline.mk_primrec.comp
              (Primrec.snd.pair
              (Primrec.fin_curry.mpr (ht.comp (Primrec.fst.comp Primrec.fst)).to₂)))).pair
            ((ReqStateL.play_primrec.comp (hrs.comp Primrec.fst)).pair
              ((ReqStateL.lastVisit_primrec.comp (hrs.comp Primrec.fst)).pair
                (ReqStateL.lastActed_primrec.comp (hrs.comp Primrec.fst))))))))
      Primrec.snd)
      
  have hsome : Primrec₂ fun (p : Arena × ℕ × ℕ × ReqStateL × TopOutcomeL)
      (w : (Fin 3 × Fin 3 × List (List Bool)) ⊕
      ((List (List Bool) × List (List Bool)) ⊕ List Bool)) =>
      Sum.casesOn (motive := fun _ => (ReqStateL × Bool) ⊕ (ReqStateL × List Bool)) w
        (fun _ => match balancedPlayL p.1 p.2.1 p.2.2.1 p.2.2.2.2 with
                  | some pl => Sum.inl ({p.2.2.2.1 with play := some pl}, true)
                  | none => Sum.inl (p.2.2.2.1, false))
        (fun w' => Sum.casesOn (motive := fun _ => (ReqStateL × Bool) ⊕ (ReqStateL × List Bool)) w'
                    (fun _ => match balancedPlayL p.1 p.2.1 p.2.2.1 p.2.2.2.2 with
                              | some pl => Sum.inl ({p.2.2.2.1 with play := some pl}, true)
                              | none => Sum.inl (p.2.2.2.1, false))
                    (fun σ =>
                        Sum.inr ({p.2.2.2.1 with baseline := some ⟨σ, fun _ => p.2.1⟩}, σ))) :=
    ((Primrec.sumCasesOn Primrec.snd (hdef.comp (Primrec.fst.comp Primrec.fst)).to₂
      (Primrec.sumCasesOn Primrec.snd
          (hdef.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to₂
          (hprin.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd).to₂).to₂).to₂).of_eq fun p w => by rfl
      
  exact (Primrec.option_casesOn hv hdef hsome).of_eq fun p => by
    rcases p with ⟨ar, t, E, rs, v⟩
    unfold examineVerdictL
    cases v with
    | none => rfl
    | some w =>
      cases w with
      | inl a => rfl
      | inr b =>
        cases b with
        | inl c => rfl
        | inr d => rfl

/-- Extracting the principal vector of an encoded top verdict is primitive recursive. -/
private theorem extensionVerdictL_primrec_aux_principal :
    Primrec fun v : TopOutcomeL =>
      Option.bind v fun x : (Fin 3 × Fin 3 × List (List Bool)) ⊕
          ((List (List Bool) × List (List Bool)) ⊕ List Bool) =>
        Sum.casesOn (motive := fun _ => Option (List Bool)) x (fun _ => none)
          (fun y => Sum.casesOn (motive := fun _ => Option (List Bool)) y (fun _ => none)
            (fun σ => some σ)) := by
  have h2 : Primrec fun y : (List (List Bool) × List (List Bool)) ⊕ List Bool =>
      Sum.casesOn (motive := fun _ => Option (List Bool)) y (fun _ => none) (fun σ => some σ) :=
    Primrec.sumCasesOn Primrec.id (Primrec.const none).to₂
      (Primrec.option_some.comp Primrec.snd).to₂
  have h1 : Primrec fun x : (Fin 3 × Fin 3 × List (List Bool)) ⊕
      ((List (List Bool) × List (List Bool)) ⊕ List Bool) =>
      Sum.casesOn (motive := fun _ => Option (List Bool)) x (fun _ => none)
        (fun y => Sum.casesOn (motive := fun _ => Option (List Bool)) y (fun _ => none)
          (fun σ => some σ)) :=
    Primrec.sumCasesOn Primrec.id (Primrec.const none).to₂ (h2.comp Primrec.snd).to₂
  exact Primrec.option_bind₁ h1

/-- Consuming a top verdict after extension is primitive recursive. -/
theorem extensionVerdictL_primrec :
    Primrec fun p : Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL =>
      extensionVerdictL p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
  have hAr : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL => p.1 :=
    Primrec.fst
  have ht : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hE : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hrs : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL =>
      p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have htb : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL =>
      p.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hv : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL =>
      p.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hbal : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL =>
      balancedPlayL p.1 p.2.1 p.2.2.1 p.2.2.2.2.2 :=
    balancedPlayL_primrec.comp (hAr.pair (ht.pair (hE.pair hv)))
  -- principal branch: remember the principal vector as the new baseline
  have hprinc : Primrec₂ fun (p : Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL)
      (σ : List Bool) =>
      ((⟨p.2.2.2.1.c, p.2.2.2.2.1, some ⟨σ, fun _ => p.2.1⟩, p.2.2.2.1.play,
        p.2.2.2.1.lastVisit, p.2.2.2.1.lastActed⟩ : ReqStateL), true) := by
    unfold Primrec₂
    have hrs' : Primrec fun q : (Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL) ×
        List Bool => q.1.2.2.2.1 := hrs.comp Primrec.fst
    have htb' : Primrec fun q : (Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL) ×
        List Bool => q.1.2.2.2.2.1 := htb.comp Primrec.fst
    have ht' : Primrec fun q : (Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL) ×
        List Bool => q.1.2.1 := ht.comp Primrec.fst
    have hconst : Primrec fun q : (Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL) ×
        List Bool => fun _ : Fin 3 => q.1.2.1 :=
      Primrec.fin_curry.mpr (ht'.comp Primrec.fst)
    have hbase : Primrec fun q : (Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL) ×
        List Bool => (⟨q.2, fun _ => q.1.2.1⟩ : Baseline) :=
      Baseline.mk_primrec.comp (Primrec.snd.pair hconst)
    have hmk := ReqStateL.mk_primrec.comp
      ((ReqStateL.c_primrec.comp hrs').pair
        (htb'.pair
          ((Primrec.option_some.comp hbase).pair
            ((ReqStateL.play_primrec.comp hrs').pair
              ((ReqStateL.lastVisit_primrec.comp hrs').pair
                (ReqStateL.lastActed_primrec.comp hrs'))))))
    exact hmk.pair (Primrec.const true)
  -- balanced branch: start the balanced play
  have hplay : Primrec fun q : (Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL) ×
      PlayL =>
      ((⟨q.1.2.2.2.1.c, q.1.2.2.2.2.1, none, some q.2, q.1.2.2.2.1.lastVisit,
        q.1.2.2.2.1.lastActed⟩ : ReqStateL), true) := by
    have hrs' : Primrec fun q : (Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL) ×
        PlayL => q.1.2.2.2.1 := hrs.comp Primrec.fst
    have htb' : Primrec fun q : (Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL) ×
        PlayL => q.1.2.2.2.2.1 := htb.comp Primrec.fst
    have hmk := ReqStateL.mk_primrec.comp
      ((ReqStateL.c_primrec.comp hrs').pair
        (htb'.pair
          ((Primrec.const (none : Option Baseline)).pair
            ((Primrec.option_some.comp Primrec.snd).pair
              ((ReqStateL.lastVisit_primrec.comp hrs').pair
                (ReqStateL.lastActed_primrec.comp hrs'))))))
    exact hmk.pair (Primrec.const true)
  have hrest : Primrec fun p : Arena × ℕ × ℕ × ReqStateL × List TTable × TopOutcomeL =>
      Option.casesOn (motive := fun _ => ReqStateL × Bool)
        (balancedPlayL p.1 p.2.1 p.2.2.1 p.2.2.2.2.2) (p.2.2.2.1, false)
        (fun pl => (⟨p.2.2.2.1.c, p.2.2.2.2.1, none, some pl, p.2.2.2.1.lastVisit,
          p.2.2.2.1.lastActed⟩, true)) :=
    Primrec.option_casesOn hbal (hrs.pair (Primrec.const false)) hplay
  refine (Primrec.option_casesOn
    (extensionVerdictL_primrec_aux_principal.comp hv) hrest hprinc).of_eq ?_
  intro p
  rcases p with ⟨ar, t, E, rs, tables, v⟩
  rcases v with _ | (⟨j, k, S⟩ | ⟨S, T⟩ | σ) <;> rfl

/-- Refreshing a bishop baseline is primitive recursive. -/
theorem bishopBaselineL_primrec :
    Primrec fun p : Baseline × Fin 3 × ℕ => bishopBaselineL p.1 p.2.1 p.2.2 := by
  have hb : Primrec fun p : Baseline × Fin 3 × ℕ =>
      fun j => if j = p.2.1 then p.1.base j else p.2.2 :=
    Primrec.fin_curry.mpr (Primrec.ite
      (Primrec.eq.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fin_app.comp (Baseline.base_primrec.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂
  exact (Baseline.mk_primrec.comp ((Baseline.σ_primrec.comp Primrec.fst).pair hb)).of_eq
    fun _ => rfl

/-! ## Computability of the observable step -/

variable {I : Input}

/-- The fixed game interface composed with the explicit arena encoding. -/
theorem forcesL_computable :
    Computable fun p : Arena × List (List Bool) × List Str × ℕ × ℕ =>
      forcesB p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have he : Computable fun ar : Arena => (ar.tables, ar.scale) :=
    Arena.tables_primrec.to_comp.pair Arena.scale_primrec.to_comp
  refine (forcesB_computable.comp
    ((he.comp Computable.fst).pair Computable.snd)).of_eq fun p => ?_
  rcases p with ⟨⟨tables, scale⟩, S, A, a, b⟩
  rfl

/-- The alive test is computable using the opponent oracle and finite-list membership. -/
theorem aliveL_computable (hI : I.Valid) :
    Computable fun p : (Fin 3 → List Str) × ℕ × Fin 3 × Str =>
      aliveL I p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have ho : Computable fun p : (Fin 3 → List Str) × ℕ × Fin 3 × Str =>
      I.opp p.2.1 p.2.2.2 := hI.opp_computable.comp
        ((Computable.fst.comp Computable.snd).pair
          (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hm : Computable fun p : (Fin 3 → List Str) × ℕ × Fin 3 × Str =>
      decide (p.2.2.2 ∈ p.1 p.2.2.1) := by
    refine (list_mem_primrec.to_comp.comp
      ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair
        (Computable.fin_app.comp Computable.fst
          (Computable.fst.comp (Computable.snd.comp Computable.snd))))).of_eq fun p => ?_
    exact decide_eq_decide.mpr Iff.rfl
  exact (Primrec.and.to_comp.comp (Primrec.not.to_comp.comp ho)
    (Primrec.not.to_comp.comp hm)).of_eq fun _ => rfl

/-- Positions are computed by filtering the explicit arena board. -/
theorem positionL_computable (hI : I.Valid) :
    Computable fun p : (Fin 3 → List Str) × Arena × ℕ × Fin 3 =>
      positionL I p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have ha : Primrec fun p : ((Fin 3 → List Str) × Arena × ℕ × Fin 3) × Str =>
      (p.1.1, p.1.2.2.1, p.1.2.2.2, p.2) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
        ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd))
  exact (computable_list_filter
    (boardList_primrec.to_comp.comp (Computable.fst.comp Computable.snd))
    ((aliveL_computable hI).comp ha.to_comp).to₂).of_eq fun _ => rfl

/-- Opponent spending is a computable filtered sum. -/
theorem oppSpendL_computable (hI : I.Valid) :
    Computable fun p : Arena × ℕ × ℕ => oppSpendL I p.1 p.2.1 p.2.2 := by
  have ht : Computable fun p : (Arena × ℕ × ℕ) × Str => I.opp p.1.2.2 p.2 :=
    (hI.opp_computable.comp
      ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)).of_eq
        fun _ => rfl
  have hb : Computable fun p : (Arena × ℕ × ℕ) × Str => I.opp p.1.2.1 p.2 :=
    (hI.opp_computable.comp
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)).of_eq
        fun _ => rfl
  have hl : Computable fun p : Arena × ℕ × ℕ =>
      p.1.boardList.filter (fun τ => I.opp p.2.2 τ && !(I.opp p.2.1 τ)) :=
    computable_list_filter (boardList_primrec.to_comp.comp Computable.fst)
      (Primrec.and.to_comp.comp ht (Primrec.not.to_comp.comp hb)).to₂
  exact (costU_primrec.to_comp.comp
    ((Arena.scale_primrec.to_comp.comp Computable.fst).pair hl)).of_eq fun _ => rfl

/-- Step 1 of the proof of `splitSearchL_computable`: the search predicate, board inequality and
the two complementary forcing tests, is computable. -/
private theorem splitSearchL_computable_step1_pred :
    Computable₂ fun (p : Arena × (Fin 3 → List Str) × ℕ)
        (q : (Fin 3 × Fin 3) × List (List Bool)) =>
      decide (q.1.1 ≠ q.1.2) &&
        forcesB p.1 q.2 (p.2.1 q.1.1) p.2.2 p.2.2 &&
        forcesB p.1 (complL p.1.tables.length q.2)
          (p.2.1 q.1.2) p.2.2 p.2.2 := by
  have har : Computable fun x : (Arena × (Fin 3 → List Str) × ℕ) ×
      ((Fin 3 × Fin 3) × List (List Bool)) => x.1.1 := Computable.fst.comp Computable.fst
  have hA : Computable fun x : (Arena × (Fin 3 → List Str) × ℕ) ×
      ((Fin 3 × Fin 3) × List (List Bool)) => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hE : Computable fun x : (Arena × (Fin 3 → List Str) × ℕ) ×
      ((Fin 3 × Fin 3) × List (List Bool)) => x.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hj : Computable fun x : (Arena × (Fin 3 → List Str) × ℕ) ×
      ((Fin 3 × Fin 3) × List (List Bool)) => x.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hk : Computable fun x : (Arena × (Fin 3 → List Str) × ℕ) ×
      ((Fin 3 × Fin 3) × List (List Bool)) => x.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hS : Computable fun x : (Arena × (Fin 3 → List Str) × ℕ) ×
      ((Fin 3 × Fin 3) × List (List Bool)) => x.2.2 := Computable.snd.comp Computable.snd
  
  have heq : Computable fun x : (Arena × (Fin 3 → List Str) × ℕ) ×
      ((Fin 3 × Fin 3) × List (List Bool)) => decide (x.2.1.1 = x.2.1.2) :=
    Computable₂.comp Primrec.eq.decide.to_comp hj hk
  have hneq : Computable fun x : (Arena × (Fin 3 → List Str) × ℕ) ×
      ((Fin 3 × Fin 3) × List (List Bool)) => decide (x.2.1.1 ≠ x.2.1.2) :=
    (Primrec.not.to_comp.comp heq).of_eq fun x => by simp only [ne_eq, decide_not]
    
  have hAj := (@Computable.fin_app _ _ 3).comp hA hj
  have hAk := (@Computable.fin_app _ _ 3).comp hA hk
  have hcompl :=
    complL_primrec.to_comp.comp
        ((Primrec.list_length.to_comp.comp (Arena.tables_primrec.to_comp.comp har)).pair hS)
  have hforces1 := forcesL_computable.comp (har.pair (hS.pair (hAj.pair (hE.pair hE))))
  have hforces2 := forcesL_computable.comp (har.pair (hcompl.pair (hAk.pair (hE.pair hE))))
  exact (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp hneq hforces1) hforces2).of_eq fun _ =>
      rfl

/-- Step 2 of the proof of `splitSearchL_computable`: the searched list of board pairs and sets of
outcome vectors is computable. -/
private theorem splitSearchL_computable_step2_list :
    Computable fun p : Arena × (Fin 3 → List Str) × ℕ =>
      (allBoards.product allBoards).product
        (allVec p.1.tables.length).sublists := by
  have hp := Computable.fst
    (α := Arena) (β := (Fin 3 → List Str) × ℕ)
  have ht := Computable.comp Arena.tables_primrec.to_comp hp
  have hn := Computable.comp Primrec.list_length.to_comp ht
  have hv := Computable.comp allVec_primrec.to_comp hn
  have hs := Computable.comp list_sublists_primrec.to_comp hv
  have hc := Computable.const
    (α := Arena × (Fin 3 → List Str) × ℕ)
    (allBoards.product allBoards)
  have hl := Computable.comp list_product_primrec.to_comp
    (Computable.pair hc hs)
  exact hl.of_eq (fun _ => rfl)

/-- The split search is a computable first-element search. -/
theorem splitSearchL_computable :
    Computable fun p : Arena × (Fin 3 → List Str) × ℕ => splitSearchL p.1 p.2.1 p.2.2 := by
  unfold splitSearchL
  exact computable_list_find
    splitSearchL_computable_step2_list
    splitSearchL_computable_step1_pred


/-- Step 1 of the proof of `meetSearchL_computable`: the search predicate is computable. -/
private lemma meetSearchL_computable_step1_pred :
    Computable fun pq : (Arena × (Fin 3 → List Str) × ℕ) × (List (List Bool) × List (List Bool)) =>
      forcesB pq.1.1 pq.2.1 (pq.1.2.1 0) pq.1.2.2 pq.1.2.2 &&
      forcesB pq.1.1 pq.2.2 (pq.1.2.1 0) pq.1.2.2 pq.1.2.2 &&
      !(forcesB pq.1.1 (interL pq.2.1 pq.2.2) (pq.1.2.1 0) pq.1.2.2 pq.1.2.2) := by
  have har : Computable fun pq : (Arena × (Fin 3 → List Str) × ℕ) ×
      (List (List Bool) × List (List Bool)) => pq.1.1 :=
    Computable.fst.comp Computable.fst
  have hS : Computable fun pq : (Arena × (Fin 3 → List Str) × ℕ) ×
      (List (List Bool) × List (List Bool)) => pq.2.1 :=
    Computable.fst.comp Computable.snd
  have hT : Computable fun pq : (Arena × (Fin 3 → List Str) × ℕ) ×
      (List (List Bool) × List (List Bool)) => pq.2.2 :=
    Computable.snd.comp Computable.snd
  have hA : Computable fun pq : (Arena × (Fin 3 → List Str) × ℕ) ×
      (List (List Bool) × List (List Bool)) => pq.1.2.1 0 :=
    (@Computable.fin_app _ _ 3).comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.const 0)
  have hE : Computable fun pq : (Arena × (Fin 3 → List Str) × ℕ) ×
      (List (List Bool) × List (List Bool)) => pq.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hint : Computable fun pq : (Arena × (Fin 3 → List Str) × ℕ) ×
      (List (List Bool) × List (List Bool)) => interL pq.2.1 pq.2.2 :=
    interL_primrec.to_comp.comp Computable.snd
  exact (Primrec.and.to_comp.comp
    (Primrec.and.to_comp.comp
      (forcesL_computable.comp (har.pair (hS.pair (hA.pair (hE.pair hE)))))
      (forcesL_computable.comp (har.pair (hT.pair (hA.pair (hE.pair hE))))))
    (Primrec.not.to_comp.comp
      (forcesL_computable.comp (har.pair (hint.pair (hA.pair (hE.pair hE))))))).of_eq fun _ => rfl

/-- Step 2 of the proof of `meetSearchL_computable`: the searched list of pairs of sets of outcome
vectors is computable. -/
private lemma meetSearchL_computable_step2_list :
    Computable fun p : Arena × (Fin 3 → List Str) × ℕ =>
      ((allVec p.1.tables.length).sublists.product (allVec p.1.tables.length).sublists) := by
  have hn : Computable fun p : Arena × (Fin 3 → List Str) × ℕ => allVec p.1.tables.length :=
    allVec_primrec.to_comp.comp
        (Primrec.list_length.to_comp.comp (Arena.tables_primrec.to_comp.comp Computable.fst))
  have hs : Computable fun p : Arena × (Fin 3 → List Str) × ℕ =>
      (allVec p.1.tables.length).sublists :=
    list_sublists_primrec.to_comp.comp hn
  exact (list_product_primrec.to_comp.comp (hs.pair hs)).of_eq fun _ => rfl

/-- The failed-intersection search is a computable first-element search. -/
theorem meetSearchL_computable :
    Computable fun p : Arena × (Fin 3 → List Str) × ℕ => meetSearchL p.1 p.2.1 p.2.2 := by
  dsimp [meetSearchL]
  exact computable_list_find meetSearchL_computable_step2_list meetSearchL_computable_step1_pred

-- The components of the arguments of the forcing test in `principalSearchL_computable`.
private def p_to_tuple_fun1 (p_σ : (Arena × (Fin 3 → List Str) × ℕ) × List Bool) : Arena := p_σ.1.1
private def p_to_tuple_fun2 (p_σ : (Arena × (Fin 3 → List Str) × ℕ) × List Bool) : List
    (List Bool) := [p_σ.2]
private def p_to_tuple_fun3 (p_σ : (Arena × (Fin 3 → List Str) × ℕ) × List Bool) : List Str :=
  p_σ.1.2.1 0
private def p_to_tuple_fun4 (p_σ : (Arena × (Fin 3 → List Str) × ℕ) × List Bool) : ℕ := p_σ.1.2.2
private def p_to_tuple_fun5 (p_σ : (Arena × (Fin 3 → List Str) × ℕ) × List Bool) : ℕ := p_σ.1.2.2

private theorem p_to_tuple_fun1_comp : Computable p_to_tuple_fun1 :=
  Computable.fst.comp Computable.fst
private theorem p_to_tuple_fun2_comp : Computable p_to_tuple_fun2 :=
  Computable₂.comp Computable.list_cons Computable.snd (Primrec.const []).to_comp
private theorem p_to_tuple_fun3_comp : Computable p_to_tuple_fun3 :=
  Computable.fin_app.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Primrec.const 0).to_comp
private theorem p_to_tuple_fun4_comp : Computable p_to_tuple_fun4 :=
  Computable.snd.comp (Computable.snd.comp Computable.fst)
private theorem p_to_tuple_fun5_comp : Computable p_to_tuple_fun5 :=
  Computable.snd.comp (Computable.snd.comp Computable.fst)

/-- The generator search is a computable first-element search. -/
theorem principalSearchL_computable :
    Computable fun p : Arena × (Fin 3 → List Str) × ℕ =>
      principalSearchL p.1 p.2.1 p.2.2 := by
  dsimp [principalSearchL]
  apply computable_list_find
  · exact allVec_primrec.to_comp.comp
        (Primrec.list_length.to_comp.comp (Arena.tables_primrec.to_comp.comp Computable.fst))
  · have h_comp :=
      forcesL_computable.comp
          (p_to_tuple_fun1_comp.pair
          (p_to_tuple_fun2_comp.pair
          (p_to_tuple_fun3_comp.pair (p_to_tuple_fun4_comp.pair p_to_tuple_fun5_comp))))
    exact h_comp

/-- The three ordered searches assemble to a computable encoded verdict. -/
theorem topOutcomeL_computable :
    Computable fun p : Arena × (Fin 3 → List Str) × ℕ => topOutcomeL p.1 p.2.1 p.2.2 := by
  have hp : Computable fun p : Arena × (Fin 3 → List Str) × ℕ =>
      (principalSearchL p.1 p.2.1 p.2.2).map fun σ =>
        (.inr (.inr σ) : (Fin 3 × Fin 3 × List (List Bool)) ⊕
          ((List (List Bool) × List (List Bool)) ⊕ List Bool)) :=
    Computable.option_map principalSearchL_computable
      ((Primrec.sumInr.comp Primrec.sumInr).to_comp.comp Computable.snd).to₂
  have hm := Computable.option_casesOn meetSearchL_computable hp
    ((Primrec.option_some.comp (Primrec.sumInr.comp Primrec.sumInl)).to_comp.comp
      Computable.snd).to₂
  have hs : Primrec fun q : (Fin 3 × Fin 3) × List (List Bool) =>
      (some (.inl (q.1.1, q.1.2, q.2)) : TopOutcomeL) :=
    Primrec.option_some.comp (Primrec.sumInl.comp
      ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
  exact (Computable.option_casesOn splitSearchL_computable hm
    (hs.to_comp.comp Computable.snd).to₂).of_eq fun p => by
      unfold topOutcomeL
      cases splitSearchL p.1 p.2.1 p.2.2 <;> cases meetSearchL p.1 p.2.1 p.2.2 <;> rfl

/-- Step 1 of the proof of `firstStackSplitL_computable`: the test whether the complement of `{σ}`
is forced on a given board at a given level is computable. -/
private lemma firstStackSplitL_computable_step1 :
    Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 =>
        forcesB pr.1.1 (complL pr.1.1.tables.length [pr.1.2.2]) (pr.1.2.1 pr.2.2)
          (levelBudget pr.1.1.tables (pr.2.1 + 1)) (levelBudget pr.1.1.tables (pr.2.1 + 1)) := by
  have h_arena : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 =>
      pr.1.1 :=
    Computable.fst.comp Computable.fst
  have h_tables : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 =>
      pr.1.1.tables :=
    (Arena.tables_primrec.to_comp.comp h_arena).of_eq fun _ => rfl
  have h_tables_len : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 =>
      pr.1.1.tables.length :=
    (Computable.list_length.comp h_tables).of_eq fun _ => rfl
  have h_sigma : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 =>
      pr.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have h_sigma_list : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 =>
      [pr.1.2.2] :=
    (Computable.list_cons.comp h_sigma (Computable.const [])).of_eq fun _ => rfl
  have h_complL : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 =>
      complL pr.1.1.tables.length [pr.1.2.2] :=
    (complL_primrec.to_comp.comp (h_tables_len.pair h_sigma_list)).of_eq fun _ => rfl
  have h_A : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 => pr.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have h_j : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 => pr.2.2 :=
    Computable.snd.comp Computable.snd
  have h_Aj : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 =>
      pr.1.2.1 pr.2.2 :=
    (Computable.fin_app.comp h_A h_j).of_eq fun _ => rfl
  have h_r : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 => pr.2.1 :=
    Computable.fst.comp Computable.snd
  have h_r_plus_1 : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 =>
      pr.2.1 + 1 :=
    (Computable.succ.comp h_r).of_eq fun _ => rfl
  have h_budget : Computable fun pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ × Fin 3 =>
      levelBudget pr.1.1.tables (pr.2.1 + 1) :=
    (levelBudget_primrec.to_comp.comp (h_tables.pair h_r_plus_1)).of_eq fun _ => rfl
  exact (forcesL_computable.comp
      (h_arena.pair (h_complL.pair (h_Aj.pair (h_budget.pair h_budget))))).of_eq fun _ => rfl

/-- Step 2 of the proof of `firstStackSplitL_computable`: the test whether some board forces the
complement of `{σ}` at a given level is computable. -/
private lemma firstStackSplitL_computable_step2 :
    Computable₂ fun (p : Arena × (Fin 3 → List Str) × List Bool) (r : ℕ) =>
      allBoards.any fun j =>
        forcesB p.1 (complL p.1.tables.length [p.2.2]) (p.2.1 j)
          (levelBudget p.1.tables (r + 1)) (levelBudget p.1.tables (r + 1)) := by
  have H : Computable₂ fun (pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ) (j : Fin 3) =>
    forcesB pr.1.1 (complL pr.1.1.tables.length [pr.1.2.2]) (pr.1.2.1 j)
      (levelBudget pr.1.1.tables (pr.2 + 1)) (levelBudget pr.1.1.tables (pr.2 + 1)) := by
    have h1 := firstStackSplitL_computable_step1
    refine (h1.comp
        ((Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))).of_eq fun _ => rfl
  exact (computable_list_any (Computable.const allBoards) H).of_eq fun _ => rfl

/-- Step 3 of the proof of `firstStackSplitL_computable`: the search for the first such level is
computable. -/
private lemma firstStackSplitL_computable_step3 :
    Computable fun p : Arena × (Fin 3 → List Str) × List Bool =>
      (List.range (maxLen p.1.tables)).find?
          (fun r =>
          allBoards.any
          (fun j =>
          forcesB p.1 (complL p.1.tables.length [p.2.2]) (p.2.1 j) (levelBudget p.1.tables (r + 1))
          (levelBudget p.1.tables (r + 1)))) := by
  have hl : Computable fun (p : Arena × (Fin 3 → List Str) × List Bool) =>
      List.range (maxLen p.1.tables) :=
    Primrec.list_range.to_comp.comp
        (maxLen_primrec.to_comp.comp (Arena.tables_primrec.to_comp.comp Computable.fst))
  exact (computable_list_find hl firstStackSplitL_computable_step2).of_eq fun _ => rfl

/-- Step 5 of the proof of `firstStackSplitL_computable`: the search for the first board that
forces the complement of `{σ}` at a given level is computable. -/
private lemma firstStackSplitL_computable_step5 :
    Computable₂ fun (p : Arena × (Fin 3 → List Str) × List Bool) (r : ℕ) =>
      List.find?
          (fun j =>
          forcesB p.1 (complL p.1.tables.length [p.2.2]) (p.2.1 j) (levelBudget p.1.tables (r + 1))
          (levelBudget p.1.tables (r + 1))) allBoards := by
  have H : Computable₂ fun (pr : (Arena × (Fin 3 → List Str) × List Bool) × ℕ) (j : Fin 3) =>
    forcesB pr.1.1 (complL pr.1.1.tables.length [pr.1.2.2]) (pr.1.2.1 j)
      (levelBudget pr.1.1.tables (pr.2 + 1)) (levelBudget pr.1.1.tables (pr.2 + 1)) := by
    have h1 := firstStackSplitL_computable_step1
    refine (h1.comp
        ((Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))).of_eq fun _ => rfl
  exact (computable_list_find (Computable.const allBoards) H).of_eq fun _ => rfl

/-- Step 4 of the proof of `firstStackSplitL_computable`: pairing the board found in step 5 with
its level is computable. -/
private lemma firstStackSplitL_computable_step4 :
    Computable₂ fun (p : Arena × (Fin 3 → List Str) × List Bool) (r : ℕ) =>
      Option.map (fun j => (r + 1, j))
          (List.find?
          (fun j =>
          forcesB p.1 (complL p.1.tables.length [p.2.2]) (p.2.1 j) (levelBudget p.1.tables (r + 1))
          (levelBudget p.1.tables (r + 1))) allBoards) := by
  exact (Computable.option_map firstStackSplitL_computable_step5
      (Computable.pair (Computable.succ.comp (Computable.snd.comp Computable.fst))
      Computable.snd).to₂).of_eq fun _ => rfl

/-- The first stack split is found by two computable bounded searches. -/
theorem firstStackSplitL_computable :
    Computable fun p : Arena × (Fin 3 → List Str) × List Bool =>
      firstStackSplitL p.1 p.2.1 p.2.2 := by
  dsimp only [firstStackSplitL]
  let o : (Arena × (Fin 3 → List Str) × List Bool) → Option ℕ := fun p =>
    (List.range (maxLen p.1.tables)).find? fun r =>
      allBoards.any fun j =>
          forcesB p.1 (complL p.1.tables.length [p.2.2]) (p.2.1 j) (levelBudget p.1.tables (r + 1))
          (levelBudget p.1.tables (r + 1))
  let f : (Arena × (Fin 3 → List Str) × List Bool) → Option (ℕ × Fin 3) := fun _ => none
  let g : (Arena × (Fin 3 → List Str) × List Bool) → ℕ → Option (ℕ × Fin 3) := fun p r =>
    (allBoards.find? fun j =>
        forcesB p.1 (complL p.1.tables.length [p.2.2]) (p.2.1 j) (levelBudget p.1.tables (r + 1))
        (levelBudget p.1.tables (r + 1))).map (fun j => (r + 1, j))
  have h_eq : (fun (p : Arena × (Fin 3 → List Str) × List Bool) =>
      (match (List.range (maxLen p.1.tables)).find? fun r =>
        allBoards.any fun j =>
            forcesB p.1 (complL p.1.tables.length [p.2.2]) (p.2.1 j)
            (levelBudget p.1.tables (r + 1)) (levelBudget p.1.tables (r + 1)) with
      | none => none
      | some r =>
          (allBoards.find? fun j =>
          forcesB p.1 (complL p.1.tables.length [p.2.2]) (p.2.1 j) (levelBudget p.1.tables (r + 1))
          (levelBudget p.1.tables (r + 1))).map fun j => (r + 1, j))
      ) = fun p => Option.casesOn (o p) (f p) (g p) := by
    ext p
    dsimp only [o, f, g]
    cases (List.range (maxLen p.1.tables)).find? fun r =>
      allBoards.any fun j =>
          forcesB p.1 (complL p.1.tables.length [p.2.2]) (p.2.1 j) (levelBudget p.1.tables (r + 1))
          (levelBudget p.1.tables (r + 1))
    · rfl
    · rfl
  rw [h_eq]
  exact Computable.option_casesOn firstStackSplitL_computable_step3 (Computable.const _)
      firstStackSplitL_computable_step4

/-- The requirement board list is primitive recursive. -/
theorem boardOfL_primrec : Primrec boardOfL := by
  exact boardList_primrec.comp (arenaOf_primrec.comp ((Primrec.const 0).pair Primrec.id))

/-- The pending-hit test is a computable finite existential test. -/
theorem pendingHitL_computable (hI : I.Valid) :
    Computable fun p : ReqStateL × ℕ => pendingHitL I p.1 p.2 := by
  have hl : Computable fun p : ReqStateL × ℕ => boardOfL p.1.tables :=
    boardOfL_primrec.to_comp.comp (ReqStateL.tables_primrec.to_comp.comp Computable.fst)
  have ht : Computable fun p : (ReqStateL × ℕ) × Str => I.opp p.1.2 p.2 :=
    (hI.opp_computable.comp
      ((Computable.snd.comp Computable.fst).pair Computable.snd)).of_eq fun _ => rfl
  have hb : Computable fun p : (ReqStateL × ℕ) × Str => I.opp p.1.1.lastVisit p.2 :=
    (hI.opp_computable.comp
      ((ReqStateL.lastVisit_primrec.to_comp.comp (Computable.fst.comp Computable.fst)).pair
        Computable.snd)).of_eq fun _ => rfl
  exact (computable_list_any hl
    (Primrec.and.to_comp.comp ht (Primrec.not.to_comp.comp hb)).to₂).of_eq fun _ => rfl

-- `hI` is not needed here; the step lemmas of one proof take the same arguments.
set_option linter.unusedVariables false in
/-- Step 1 of the proof of `mustResetL_computable`, first part: the comparison of the last visit of
`R_i` with the last action of `R_m` is computable. -/
private lemma mustResetL_computable_step1_1 {I : RandomStrings.TTMeet.Input} (hI : I.Valid) :
    Computable fun p : (ConStateL × ℕ × ℕ × ℕ) × ℕ =>
        decide ((reqL p.1.1 p.1.2.1).lastVisit < (reqL p.1.1 p.2).lastActed) := by
  have f1 : Primrec fun p : (ConStateL × ℕ × ℕ × ℕ) × ℕ => (reqL p.1.1 p.1.2.1).lastVisit :=
    ReqStateL.lastVisit_primrec.comp
        (reqL_primrec.comp
        ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp Primrec.snd).comp Primrec.fst)))
  have f2 : Primrec fun p : (ConStateL × ℕ × ℕ × ℕ) × ℕ => (reqL p.1.1 p.2).lastActed :=
    ReqStateL.lastActed_primrec.comp
        (reqL_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
  exact (Primrec.nat_lt.comp f1 f2).decide.to_comp

/-- Step 1 of the proof of `mustResetL_computable`, second part: the pending-hit test for `R_m`
is computable. -/
private lemma mustResetL_computable_step1_2 (hI : I.Valid) :
    Computable fun p : (ConStateL × ℕ × ℕ × ℕ) × ℕ => pendingHitL I (reqL p.1.1 p.2) p.1.2.2.2 := by
  have f1 : Primrec fun p : (ConStateL × ℕ × ℕ × ℕ) × ℕ => reqL p.1.1 p.2 := 
    reqL_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have f2 : Primrec fun p : (ConStateL × ℕ × ℕ × ℕ) × ℕ => p.1.2.2.2 := 
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp Primrec.fst
  have f : Computable fun p : (ConStateL × ℕ × ℕ × ℕ) × ℕ => (reqL p.1.1 p.2, p.1.2.2.2) :=
    f1.to_comp.pair f2.to_comp
  have H : Computable fun p : ReqStateL × ℕ => pendingHitL I p.1 p.2 := pendingHitL_computable hI
  exact (H.comp f).of_eq (fun _ => rfl)

/-- Step 1 of the proof of `mustResetL_computable`: the reset condition contributed by one
requirement `R_m` is computable. -/
private lemma mustResetL_computable_step1 (hI : I.Valid) :
    Computable₂ fun (p : ConStateL × ℕ × ℕ × ℕ) (m : ℕ) =>
      decide ((reqL p.1 p.2.1).lastVisit < (reqL p.1 m).lastActed) ||
        pendingHitL I (reqL p.1 m) p.2.2.2 := by
  have f1 : Computable fun p : (ConStateL × ℕ × ℕ × ℕ) × ℕ =>
      decide ((reqL p.1.1 p.1.2.1).lastVisit < (reqL p.1.1 p.2).lastActed) :=
    mustResetL_computable_step1_1 hI
  have f2 : Computable fun p : (ConStateL × ℕ × ℕ × ℕ) × ℕ =>
      pendingHitL I (reqL p.1.1 p.2) p.1.2.2.2 :=
    mustResetL_computable_step1_2 hI
  have H : Computable fun p : (ConStateL × ℕ × ℕ × ℕ) × ℕ =>
      decide ((reqL p.1.1 p.1.2.1).lastVisit < (reqL p.1.1 p.2).lastActed) || pendingHitL I
      (reqL p.1.1 p.2) p.1.2.2.2 := by
    have h_or : Computable fun p : Bool × Bool => p.1 || p.2 := Primrec.or.to_comp
    exact (h_or.comp (f1.pair f2)).of_eq (fun _ => rfl)
  exact H.to₂

/-- The reset test is a computable finite existential test. -/
theorem mustResetL_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ℕ × ℕ => mustResetL I p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have p1 : Primrec fun p : ConStateL × ℕ × ℕ × ℕ => p.1 := Primrec.fst
  have p21 : Primrec fun p : ConStateL × ℕ × ℕ × ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have p221 : Primrec fun p : ConStateL × ℕ × ℕ × ℕ => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  
  have hd : Primrec fun p : ConStateL × ℕ × ℕ × ℕ => decide (p.2.2.1 = 0) :=
    (Primrec.eq.comp p221 (Primrec.const 0)).decide
  
  have hc : Primrec fun p : ConStateL × ℕ × ℕ × ℕ => (reqL p.1 p.2.1).c :=
    ReqStateL.c_primrec.comp (reqL_primrec.comp (p1.pair p21))
  
  have hn : Primrec fun p : ConStateL × ℕ × ℕ × ℕ => (reqL p.1 p.2.1).c.isNone :=
    (Primrec.option_casesOn hc (Primrec.const true)
        (Primrec.const false |>.comp Primrec.fst).to₂).of_eq
        (fun x => by cases (reqL x.1 x.2.1).c <;> rfl)
  have hl : Computable fun p : ConStateL × ℕ × ℕ × ℕ => List.range p.2.1 :=
    Primrec.list_range.to_comp.comp p21.to_comp
  have hany : Computable fun p : ConStateL × ℕ × ℕ × ℕ => (List.range p.2.1).any fun m =>
      decide ((reqL p.1 p.2.1).lastVisit < (reqL p.1 m).lastActed) ||
        pendingHitL I (reqL p.1 m) p.2.2.2 :=
    (computable_list_any hl (mustResetL_computable_step1 hI)).of_eq (fun _ => rfl)
    
  have h_or : Computable fun p : Bool × Bool => p.1 || p.2 := Primrec.or.to_comp
  have ho1 : Computable fun p : ConStateL × ℕ × ℕ × ℕ =>
      decide (p.2.2.1 = 0) || (reqL p.1 p.2.1).c.isNone :=
    (h_or.comp (hd.to_comp.pair hn.to_comp)).of_eq (fun _ => rfl)
    
  have ho2 : Computable fun p : ConStateL × ℕ × ℕ × ℕ =>
      decide (p.2.2.1 = 0) || (reqL p.1 p.2.1).c.isNone || ((List.range p.2.1).any fun m =>
      decide ((reqL p.1 p.2.1).lastVisit < (reqL p.1 m).lastActed) ||
        pendingHitL I (reqL p.1 m) p.2.2.2) :=
    (h_or.comp (ho1.pair hany)).of_eq (fun _ => by simp only [Bool.or_assoc])
    
  exact ho2.of_eq (fun x => by unfold mustResetL; simp only [Bool.or_assoc])

/-- The finite prefix of the approximation to X is computable. -/
theorem xPrefix_computable (hI : I.Valid) :
    Computable fun p : ℕ × ℕ => xPrefix I p.1 p.2 := by
  exact computable_list_map (Primrec.list_range.to_comp.comp Computable.snd)
    (hI.X_computable.comp ((Computable.fst.comp Computable.fst).pair
      (strOf_primrec.to_comp.comp Computable.snd))).to₂
/-- Step 1 of the proof of `examineTopL_some_computable`: the overbudget test, whether the
opponent has spent more than the budget since the base stage of some board, is computable. -/
private lemma examineTopL_some_computable_step1_any (hI : I.Valid) :
  Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
    allBoards.any
        (fun j =>
        decide (levelBudget p.2.2.2.2.1.tables 0 <
        oppSpendL I (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) (p.2.2.2.2.2.base j) p.2.2.1)) := by
  let P := ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline
  have hp_req : Computable fun (p : P) => p.2.2.2.2.1 :=
    Computable.fst.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))) |>.of_eq
        fun _ => rfl
  have hp_base : Computable fun (p : P) => p.2.2.2.2.2 :=
    Computable.snd.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))) |>.of_eq
        fun _ => rfl
  have hp_c : Computable fun (p : P) => p.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)) |>.of_eq fun _ =>
        rfl
  have hp_t : Computable fun (p : P) => p.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd) |>.of_eq fun _ => rfl
  have hp_tables : Computable fun (p : P) => p.2.2.2.2.1.tables :=
    ReqStateL.tables_primrec.to_comp.comp hp_req |>.of_eq fun _ => rfl
  have h_budget : Computable fun (p : P) => levelBudget p.2.2.2.2.1.tables 0 :=
    levelBudget_primrec.to_comp.comp (Computable.pair hp_tables (Computable.const 0)) |>.of_eq
        fun _ => rfl
  have h_arena : Computable fun (p : P) => arenaOf p.2.2.2.1 p.2.2.2.2.1.tables :=
    arenaOf_primrec.to_comp.comp (Computable.pair hp_c hp_tables) |>.of_eq fun _ => rfl
  have h_base_fn : Computable₂ fun (p : P) (j : Fin 3) => p.2.2.2.2.2.base j :=
    Primrec.fin_app.to_comp.comp (Baseline.base_primrec.to_comp.comp hp_base |>.comp Computable.fst)
        Computable.snd |>.of_eq fun _ => rfl
  have h_opp : Computable₂ fun (p : P) (j : Fin 3) =>
      oppSpendL I (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) (p.2.2.2.2.2.base j) p.2.2.1 :=
    oppSpendL_computable hI |>.comp
        (Computable.pair (h_arena.comp Computable.fst)
        (Computable.pair h_base_fn (hp_t.comp Computable.fst))) |>.of_eq fun _ => rfl
  have h_cmp : Computable₂ fun (p : P) (j : Fin 3) =>
      decide (levelBudget p.2.2.2.2.1.tables 0 <
      oppSpendL I (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) (p.2.2.2.2.2.base j) p.2.2.1) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp (h_budget.comp Computable.fst) h_opp |>.of_eq
        fun p => by
      cases p
      rfl
  exact computable_list_any (Computable.const allBoards) h_cmp |>.of_eq fun _ => rfl

/-- Step 2 of the proof of `examineTopL_some_computable`: the search for a board on which the
complement of the agreed value wins the symmetric game is computable. -/
private lemma examineTopL_some_computable_step2_find (hI : I.Valid) :
  Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
    allBoards.find?
        (fun j =>
        forcesB (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables)
        (complL p.2.2.2.2.1.tables.length [p.2.2.2.2.2.σ])
        (positionL I p.1.ours (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) p.2.2.1 j)
        (levelBudget p.2.2.2.2.1.tables 0) (levelBudget p.2.2.2.2.1.tables 0)) := by
  let P := ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline
  have hp_req : Computable fun (p : P) => p.2.2.2.2.1 :=
    Computable.of_eq
        (Computable.fst.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))))
        (fun _ => rfl)
  have hp_base : Computable fun (p : P) => p.2.2.2.2.2 :=
    Computable.of_eq
        (Computable.snd.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))))
        (fun _ => rfl)
  have hp_c : Computable fun (p : P) => p.2.2.2.1 :=
    Computable.of_eq
        (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
        (fun _ => rfl)
  have hp_t : Computable fun (p : P) => p.2.2.1 :=
    Computable.of_eq (Computable.fst.comp (Computable.snd.comp Computable.snd)) (fun _ => rfl)
  have hp_ours : Computable fun (p : P) => p.1.ours :=
    Computable.of_eq (ConStateL.ours_primrec.to_comp.comp Computable.fst) (fun _ => rfl)
  have hp_tables : Computable fun (p : P) => p.2.2.2.2.1.tables :=
    Computable.of_eq (ReqStateL.tables_primrec.to_comp.comp hp_req) (fun _ => rfl)
  
  have h_arena : Computable fun (p : P) => arenaOf p.2.2.2.1 p.2.2.2.2.1.tables :=
    Computable.of_eq (arenaOf_primrec.to_comp.comp (Computable.pair hp_c hp_tables)) (fun _ => rfl)
  
  have hp_sigma : Computable fun (p : P) => p.2.2.2.2.2.σ :=
    Computable.of_eq (Baseline.σ_primrec.to_comp.comp hp_base) (fun _ => rfl)
    
  have hp_tables_length : Computable fun (p : P) => p.2.2.2.2.1.tables.length :=
    Computable.of_eq (Primrec.list_length.to_comp.comp hp_tables) (fun _ => rfl)
    
  have hp_sigma_list : Computable fun (p : P) => [p.2.2.2.2.2.σ] :=
    Computable.of_eq ((Primrec₂.to_comp Primrec.list_cons).comp hp_sigma (Computable.const []))
        (fun _ => rfl)
    
  have h_complL : Computable fun (p : P) => complL p.2.2.2.2.1.tables.length [p.2.2.2.2.2.σ] :=
    Computable.of_eq (complL_primrec.to_comp.comp (Computable.pair hp_tables_length hp_sigma_list))
        (fun _ => rfl)
  have h_budget : Computable fun (p : P) => levelBudget p.2.2.2.2.1.tables 0 :=
    Computable.of_eq
        (levelBudget_primrec.to_comp.comp (Computable.pair hp_tables (Computable.const 0)))
        (fun _ => rfl)
  have h_pos : Computable₂ fun (p : P) (j : Fin 3) =>
      positionL I p.1.ours (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) p.2.2.1 j :=
    Computable.of_eq
        ((positionL_computable hI).comp
        (Computable.pair (hp_ours.comp Computable.fst)
        (Computable.pair (h_arena.comp Computable.fst)
        (Computable.pair (hp_t.comp Computable.fst) Computable.snd)))) (fun _ => rfl)
  have h_cmp : Computable₂ fun (p : P) (j : Fin 3) =>
      forcesB (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables)
      (complL p.2.2.2.2.1.tables.length [p.2.2.2.2.2.σ])
      (positionL I p.1.ours (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) p.2.2.1 j)
      (levelBudget p.2.2.2.2.1.tables 0) (levelBudget p.2.2.2.2.1.tables 0) :=
    Computable.of_eq
        (forcesL_computable.comp
        (Computable.pair (h_arena.comp Computable.fst)
        (Computable.pair (h_complL.comp Computable.fst)
        (Computable.pair h_pos
        (Computable.pair (h_budget.comp Computable.fst) (h_budget.comp Computable.fst))))))
        (fun p => by
      cases p
      rfl)
      
  exact Computable.of_eq (computable_list_find (Computable.const allBoards) h_cmp) (fun _ => rfl)

/-- Step 3 of the proof of `examineTopL_some_computable`: the overbudget result, which drops the
baseline and ends the visit, is computable. -/
private lemma examineTopL_some_computable_step3_inl_none :
  Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
    ((Sum.inl
        (ReqStateL.mk p.2.2.2.2.1.c p.2.2.2.2.1.tables none p.2.2.2.2.1.play p.2.2.2.2.1.lastVisit
        p.2.2.2.2.1.lastActed, false)) : (ReqStateL × Bool) ⊕ (ReqStateL × List Bool)) := by
  have hrs : Primrec fun (p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline) => p.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hc : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline => p.2.2.2.2.1.c :=
    ReqStateL.c_primrec.comp hrs
  have htables : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      p.2.2.2.2.1.tables :=
    ReqStateL.tables_primrec.comp hrs
  have hplay : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline => p.2.2.2.2.1.play :=
    ReqStateL.play_primrec.comp hrs
  have hlastVisit : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      p.2.2.2.2.1.lastVisit :=
    ReqStateL.lastVisit_primrec.comp hrs
  have hlastActed : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      p.2.2.2.2.1.lastActed :=
    ReqStateL.lastActed_primrec.comp hrs
  have hmk : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      ReqStateL.mk p.2.2.2.2.1.c p.2.2.2.2.1.tables none p.2.2.2.2.1.play p.2.2.2.2.1.lastVisit
      p.2.2.2.2.1.lastActed :=
    ReqStateL.mk_primrec.comp
        (hc.pair
        (htables.pair ((Primrec.const none).pair (hplay.pair (hlastVisit.pair hlastActed)))))
  exact (Computable.sumInl.comp (hmk.pair (Primrec.const false)).to_comp).of_eq fun _ => rfl

/-- Step 4 of the proof of `examineTopL_some_computable`: the result that starts the unbalanced
game for the agreed value against the board found in step 2 is computable. -/
private lemma examineTopL_some_computable_step4_inl_some (hI : I.Valid) :
  Computable₂ fun (p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline) (j : Fin 3) =>
    ((Sum.inl
        (ReqStateL.mk p.2.2.2.2.1.c p.2.2.2.2.1.tables (some p.2.2.2.2.2)
        (some
        (unbalancedPlayL (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) p.2.2.1
        (levelBudget p.2.2.2.2.1.tables 0)
        (levelBudget p.2.2.2.2.1.tables 0 -
        oppSpendL I (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) (p.2.2.2.2.2.base (otherBoard j))
        p.2.2.1) p.2.2.2.2.2.σ j (otherBoard j))) p.2.2.2.2.1.lastVisit p.2.2.2.2.1.lastActed,
        true)) : (ReqStateL × Bool) ⊕ (ReqStateL × List Bool)) := by
  let P := ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline
  have hp : Computable fun (p : P × Fin 3) => p.1 := Computable.fst
  have hj : Computable fun (p : P × Fin 3) => p.2 := Computable.snd
  have hbase : Primrec fun p : P => p.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hc : Primrec fun p : P => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ht : Primrec fun p : P => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hreq : Primrec fun p : P => p.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have htables : Primrec fun p : P => p.2.2.2.2.1.tables :=
    ReqStateL.tables_primrec.comp hreq
  have harena : Primrec fun p : P => arenaOf p.2.2.2.1 p.2.2.2.2.1.tables :=
    arenaOf_primrec.comp (hc.pair htables)
  have hbudget : Primrec fun p : P => levelBudget p.2.2.2.2.1.tables 0 :=
    levelBudget_primrec.comp (htables.pair (Primrec.const 0))
  have hbasek : Computable (fun (p : P × Fin 3) => p.1.2.2.2.2.2.base (otherBoard p.2)) :=
    Computable.of_eq
        (Computable₂.comp Primrec.fin_app.to_comp
        (Baseline.base_primrec.to_comp.comp (hbase.to_comp.comp hp))
        (otherBoard_primrec.to_comp.comp hj)) fun _ => rfl
  have hopp : Computable
      (fun (p : P × Fin 3) =>
      oppSpendL I (arenaOf p.1.2.2.2.1 p.1.2.2.2.2.1.tables) (p.1.2.2.2.2.2.base (otherBoard p.2))
      p.1.2.2.1) :=
    Computable.of_eq
        (oppSpendL_computable hI |>.comp
        (Computable.pair (harena.to_comp.comp hp) (Computable.pair hbasek (ht.to_comp.comp hp))))
        fun _ => rfl
  have hrem : Computable
      (fun (p : P × Fin 3) =>
      levelBudget p.1.2.2.2.2.1.tables 0 -
      oppSpendL I (arenaOf p.1.2.2.2.1 p.1.2.2.2.2.1.tables) (p.1.2.2.2.2.2.base (otherBoard p.2))
      p.1.2.2.1) :=
    Computable.of_eq
        (Computable₂.comp Primrec.nat_sub.to_comp (hbudget.to_comp.comp hp).to₂ hopp.to₂) fun _ =>
        rfl
  have hsigma : Primrec fun p : P => p.2.2.2.2.2.σ :=
    Baseline.σ_primrec.comp hbase
  have hplay : Computable
      (fun (p : P × Fin 3) =>
      unbalancedPlayL (arenaOf p.1.2.2.2.1 p.1.2.2.2.2.1.tables) p.1.2.2.1
      (levelBudget p.1.2.2.2.2.1.tables 0)
      (levelBudget p.1.2.2.2.2.1.tables 0 -
      oppSpendL I (arenaOf p.1.2.2.2.1 p.1.2.2.2.2.1.tables) (p.1.2.2.2.2.2.base (otherBoard p.2))
      p.1.2.2.1) p.1.2.2.2.2.2.σ p.2 (otherBoard p.2)) :=
    Computable.of_eq
        (unbalancedPlayL_primrec.to_comp.comp
        (Computable.pair (harena.to_comp.comp hp)
        (Computable.pair (ht.to_comp.comp hp)
        (Computable.pair (hbudget.to_comp.comp hp)
        (Computable.pair hrem
        (Computable.pair (hsigma.to_comp.comp hp)
        (Computable.pair hj (otherBoard_primrec.to_comp.comp hj)))))))) fun _ => rfl
  have hlastVisit : Primrec fun p : P => p.2.2.2.2.1.lastVisit :=
    ReqStateL.lastVisit_primrec.comp hreq
  have hlastActed : Primrec fun p : P => p.2.2.2.2.1.lastActed :=
    ReqStateL.lastActed_primrec.comp hreq
  have hc_req : Primrec fun p : P => p.2.2.2.2.1.c :=
    ReqStateL.c_primrec.comp hreq
  have h_req : Computable
      (fun (p : P × Fin 3) =>
      ReqStateL.mk p.1.2.2.2.2.1.c p.1.2.2.2.2.1.tables (some p.1.2.2.2.2.2)
      (some
      (unbalancedPlayL (arenaOf p.1.2.2.2.1 p.1.2.2.2.2.1.tables) p.1.2.2.1
      (levelBudget p.1.2.2.2.2.1.tables 0)
      (levelBudget p.1.2.2.2.2.1.tables 0 -
      oppSpendL I (arenaOf p.1.2.2.2.1 p.1.2.2.2.2.1.tables) (p.1.2.2.2.2.2.base (otherBoard p.2))
      p.1.2.2.1) p.1.2.2.2.2.2.σ p.2 (otherBoard p.2))) p.1.2.2.2.2.1.lastVisit
      p.1.2.2.2.2.1.lastActed) :=
    Computable.of_eq
        (ReqStateL.mk_primrec.to_comp.comp
        (Computable.pair (hc_req.to_comp.comp hp)
        (Computable.pair (htables.to_comp.comp hp)
        (Computable.pair (Computable.option_some.comp (hbase.to_comp.comp hp))
        (Computable.pair (Computable.option_some.comp hplay)
        (Computable.pair (hlastVisit.to_comp.comp hp) (hlastActed.to_comp.comp hp))))))) fun _ =>
        rfl
  exact Computable.of_eq (Computable.sumInl.comp (Computable.pair h_req (Computable.const true)))
      fun _ => rfl

/-- Step 5 of the proof of `examineTopL_some_computable`: the result without conflict, which
refreshes the base stages and passes the agreed value on, is computable. -/
private lemma examineTopL_some_computable_step5_inr :
  Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
    ((Sum.inr
        (ReqStateL.mk p.2.2.2.2.1.c p.2.2.2.2.1.tables
        (some (Baseline.mk p.2.2.2.2.2.σ (fun _ => p.2.2.1))) p.2.2.2.2.1.play p.2.2.2.2.1.lastVisit
        p.2.2.2.2.1.lastActed, p.2.2.2.2.2.σ)) : (ReqStateL × Bool) ⊕ (ReqStateL × List Bool)) := by
  have hp : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline => p := Primrec.id
  have h_const_t : Primrec fun (p : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline) × Fin 3) =>
      p.1.2.2.1 :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hp))).comp Primrec.fst
  have h_base_fun : Primrec fun (p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline) =>
      fun (_ : Fin 3) => p.2.2.1 :=
    Primrec.fin_curry.mpr h_const_t.to₂
  have hp_base : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline => p.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp))))
  have hp22222_sigma : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      Baseline.σ p.2.2.2.2.2 :=
    Baseline.σ_primrec.comp hp_base
  have h_baseline_mk : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      Baseline.mk (Baseline.σ p.2.2.2.2.2) (fun _ => p.2.2.1) :=
    Baseline.mk_primrec.comp (hp22222_sigma.pair h_base_fun)
  have hp22221 : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline => p.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp))))
  have h_c : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline => p.2.2.2.2.1.c :=
    ReqStateL.c_primrec.comp hp22221
  have h_tables : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      p.2.2.2.2.1.tables :=
    ReqStateL.tables_primrec.comp hp22221
  have h_play : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline => p.2.2.2.2.1.play :=
    ReqStateL.play_primrec.comp hp22221
  have h_lastVisit : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      p.2.2.2.2.1.lastVisit :=
    ReqStateL.lastVisit_primrec.comp hp22221
  have h_lastActed : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      p.2.2.2.2.1.lastActed :=
    ReqStateL.lastActed_primrec.comp hp22221
  have h_req : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      ReqStateL.mk p.2.2.2.2.1.c p.2.2.2.2.1.tables
      (some (Baseline.mk (Baseline.σ p.2.2.2.2.2) (fun _ => p.2.2.1))) p.2.2.2.2.1.play
      p.2.2.2.2.1.lastVisit p.2.2.2.2.1.lastActed :=
    ReqStateL.mk_primrec.comp
        (h_c.pair
        (h_tables.pair
        ((Primrec.option_some.comp h_baseline_mk).pair
        (h_play.pair (h_lastVisit.pair h_lastActed)))))
  have h_inr : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      (Sum.inr
      (ReqStateL.mk p.2.2.2.2.1.c p.2.2.2.2.1.tables
      (some (Baseline.mk (Baseline.σ p.2.2.2.2.2) (fun _ => p.2.2.1))) p.2.2.2.2.1.play
      p.2.2.2.2.1.lastVisit p.2.2.2.2.1.lastActed, Baseline.σ p.2.2.2.2.2) : (ReqStateL × Bool) ⊕
      (ReqStateL × List Bool)) :=
    (@Primrec.sumInr (ReqStateL × Bool) (ReqStateL × List Bool) _ _).comp (h_req.pair hp22222_sigma)
  exact h_inr.to_comp.of_eq fun p => rfl

/-- The baseline branch of the examination is computable on a supplied baseline. -/
theorem examineTopL_some_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × Baseline =>
      examineTopL I p.1 p.2.1 p.2.2.1 p.2.2.2.1
        { p.2.2.2.2.1 with baseline := some p.2.2.2.2.2 } := by
  have h_any := examineTopL_some_computable_step1_any hI
  have h_find := examineTopL_some_computable_step2_find hI
  have h_inl_none := examineTopL_some_computable_step3_inl_none
  have h_inl_some := examineTopL_some_computable_step4_inl_some hI
  have h_inr := examineTopL_some_computable_step5_inr
  have h_find_match := Computable.option_casesOn h_find h_inr h_inl_some
  exact (Computable.cond h_any h_inl_none h_find_match).of_eq fun p => by
    dsimp only [examineTopL]
    cases ha : allBoards.any (fun j => decide
      (levelBudget p.2.2.2.2.1.tables 0 <
        oppSpendL I (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables)
          (p.2.2.2.2.2.base j) p.2.2.1)) <;>
      cases hf : allBoards.find? (fun j =>
        forcesB (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables)
          (complL p.2.2.2.2.1.tables.length [p.2.2.2.2.2.σ])
          (positionL I p.1.ours
            (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) p.2.2.1 j)
          (levelBudget p.2.2.2.2.1.tables 0)
          (levelBudget p.2.2.2.2.1.tables 0)) <;> rfl

/-- The fresh examination is computable from its top verdict. -/
theorem examineTopL_none_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL =>
      examineTopL I p.1 p.2.1 p.2.2.1 p.2.2.2.1 { p.2.2.2.2 with baseline := none } := by
  have hst : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL => p.1 := Primrec.fst
  have ht : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hrs : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have htab : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL => p.2.2.2.2.tables :=
    ReqStateL.tables_primrec.comp hrs
  have har : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL =>
      arenaOf p.2.2.2.1 p.2.2.2.2.tables :=
    arenaOf_primrec.comp (hc.pair htab)
  have hE : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL =>
      levelBudget p.2.2.2.2.tables 0 :=
    levelBudget_primrec.comp (htab.pair (Primrec.const 0))
  have hrs' : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL =>
      ({ p.2.2.2.2 with baseline := none } : ReqStateL) :=
    (ReqStateL.mk_primrec.comp ((ReqStateL.c_primrec.comp hrs).pair
      (htab.pair ((Primrec.const none).pair ((ReqStateL.play_primrec.comp hrs).pair
        ((ReqStateL.lastVisit_primrec.comp hrs).pair
          (ReqStateL.lastActed_primrec.comp hrs))))))).of_eq fun _ => rfl
  have hpos : Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL =>
      positionL I p.1.ours (arenaOf p.2.2.2.1 p.2.2.2.2.tables) p.2.2.1 := by
    refine computable_fin_curry ?_
    have hq : Computable fun q : (ConStateL × ℕ × ℕ × ℕ × ReqStateL) × Fin 3 =>
        ((q.1.1.ours, arenaOf q.1.2.2.2.1 q.1.2.2.2.2.tables, q.1.2.2.1, q.2) :
          (Fin 3 → List Str) × Arena × ℕ × Fin 3) :=
      ((ConStateL.ours_primrec.comp (hst.comp Primrec.fst)).pair
        ((har.comp Primrec.fst).pair
          ((ht.comp Primrec.fst).pair Primrec.snd))).to_comp
    exact ((positionL_computable hI).comp hq).of_eq fun _ => rfl
  have htup : Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL =>
      (arenaOf p.2.2.2.1 p.2.2.2.2.tables,
        positionL I p.1.ours (arenaOf p.2.2.2.1 p.2.2.2.2.tables) p.2.2.1,
        levelBudget p.2.2.2.2.tables 0) :=
    har.to_comp.pair (hpos.pair hE.to_comp)
  have hv : Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL =>
      topOutcomeL (arenaOf p.2.2.2.1 p.2.2.2.2.tables)
        (positionL I p.1.ours (arenaOf p.2.2.2.1 p.2.2.2.2.tables) p.2.2.1)
        (levelBudget p.2.2.2.2.tables 0) :=
    (topOutcomeL_computable.comp htup).of_eq fun _ => rfl
  have hargs : Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL =>
      (arenaOf p.2.2.2.1 p.2.2.2.2.tables, p.2.2.1, levelBudget p.2.2.2.2.tables 0,
        ({ p.2.2.2.2 with baseline := none } : ReqStateL),
        topOutcomeL (arenaOf p.2.2.2.1 p.2.2.2.2.tables)
          (positionL I p.1.ours (arenaOf p.2.2.2.1 p.2.2.2.2.tables) p.2.2.1)
          (levelBudget p.2.2.2.2.tables 0)) :=
    har.to_comp.pair (ht.to_comp.pair (hE.to_comp.pair (hrs'.to_comp.pair hv)))
  exact (examineVerdictL_primrec.to_comp.comp hargs).of_eq fun _ => rfl

/-- The first part of Case 2 is computable by a case distinction on the stored baseline. -/
theorem examineTopL_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL =>
      examineTopL I p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have ha : Primrec fun p : (ConStateL × ℕ × ℕ × ℕ × ReqStateL) × Baseline =>
      (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2, p.2) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          ((Primrec.fst.comp (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair
            ((Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair Primrec.snd))))
  have hb : Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL => p.2.2.2.2.baseline :=
    ReqStateL.baseline_primrec.to_comp.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  exact (Computable.option_casesOn hb (examineTopL_none_computable hI)
    ((examineTopL_some_computable hI).comp ha.to_comp).to₂).of_eq fun p => by
      rcases p with ⟨st, i, t, c, ⟨c₀, tables, bl, pl, lv, la⟩⟩
      cases bl <;> rfl

/-- The newly extended tables have a computable examination. -/
theorem caseTwoTableL_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable =>
      caseTwoTableL I p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
  have h_st : Primrec fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable => p.1 :=
    Primrec.fst
  have h_t : Primrec fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have h_c : Primrec fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h_rs : Primrec fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h_rs1 : Primrec fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable => p.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have h_tbl : Primrec fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable => p.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have htab : Primrec fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable =>
      p.2.2.2.1.tables ++ [p.2.2.2.2.2] :=
    Primrec.list_append.comp (ReqStateL.tables_primrec.comp h_rs)
      (Primrec.list_cons.comp h_tbl (Primrec.const []))
  have har : Primrec fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable =>
      arenaOf p.2.2.1 (p.2.2.2.1.tables ++ [p.2.2.2.2.2]) :=
    arenaOf_primrec.comp (h_c.pair htab)
  have hE : Primrec fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable =>
      levelBudget (p.2.2.2.1.tables ++ [p.2.2.2.2.2]) 0 :=
    levelBudget_primrec.comp (htab.pair (Primrec.const 0))
  have hpos : Computable fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable =>
      positionL I p.1.ours (arenaOf p.2.2.1 (p.2.2.2.1.tables ++ [p.2.2.2.2.2])) p.2.1 := by
    refine computable_fin_curry ?_
    have hq : Computable fun q : (ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable) × Fin 3 =>
        ((q.1.1.ours, arenaOf q.1.2.2.1 (q.1.2.2.2.1.tables ++ [q.1.2.2.2.2.2]), q.1.2.1, q.2) :
          (Fin 3 → List Str) × Arena × ℕ × Fin 3) :=
      ((ConStateL.ours_primrec.comp (h_st.comp Primrec.fst)).pair
        ((har.comp Primrec.fst).pair
          ((h_t.comp Primrec.fst).pair Primrec.snd))).to_comp
    exact ((positionL_computable hI).comp hq).of_eq fun _ => rfl
  have htup : Computable fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable =>
      (arenaOf p.2.2.1 (p.2.2.2.1.tables ++ [p.2.2.2.2.2]),
        positionL I p.1.ours (arenaOf p.2.2.1 (p.2.2.2.1.tables ++ [p.2.2.2.2.2])) p.2.1,
        levelBudget (p.2.2.2.1.tables ++ [p.2.2.2.2.2]) 0) :=
    har.to_comp.pair (hpos.pair hE.to_comp)
  have hv : Computable fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable =>
      topOutcomeL (arenaOf p.2.2.1 (p.2.2.2.1.tables ++ [p.2.2.2.2.2]))
        (positionL I p.1.ours (arenaOf p.2.2.1 (p.2.2.2.1.tables ++ [p.2.2.2.2.2])) p.2.1)
        (levelBudget (p.2.2.2.1.tables ++ [p.2.2.2.2.2]) 0) :=
    (topOutcomeL_computable.comp htup).of_eq fun _ => rfl
  have hargs : Computable fun p : ConStateL × ℕ × ℕ × ReqStateL × ReqStateL × TTable =>
      (arenaOf p.2.2.1 (p.2.2.2.1.tables ++ [p.2.2.2.2.2]), p.2.1,
        levelBudget (p.2.2.2.1.tables ++ [p.2.2.2.2.2]) 0,
        p.2.2.2.2.1,
        p.2.2.2.1.tables ++ [p.2.2.2.2.2],
        topOutcomeL (arenaOf p.2.2.1 (p.2.2.2.1.tables ++ [p.2.2.2.2.2]))
          (positionL I p.1.ours (arenaOf p.2.2.1 (p.2.2.2.1.tables ++ [p.2.2.2.2.2])) p.2.1)
          (levelBudget (p.2.2.2.1.tables ++ [p.2.2.2.2.2]) 0)) :=
    har.to_comp.pair
        (h_t.to_comp.pair (hE.to_comp.pair (h_rs1.to_comp.pair (htab.to_comp.pair hv))))
  exact (extensionVerdictL_primrec.to_comp.comp hargs).of_eq fun _ => rfl


/-- Step 1 of the proof of `caseTwoExtendL_computable`: the comparison of the agreed value with
`X_t` is computable. -/
private lemma caseTwoExtendL_computable_step1_f {I : Input} (hI : I.Valid) :
  Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
    decide (p.2.2.2.2.2.2 ≠ xPrefix I p.2.2.1 p.2.2.2.2.1.tables.length) := by
  have ht : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have h_rs : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.2.2.1) :=
    Computable.fst.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hσ : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.2.2.2.2) :=
    Computable.snd.comp
        (Computable.snd.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have hlen : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.2.2.1.tables.length) :=
    Primrec.list_length.to_comp.comp (ReqStateL.tables_primrec.to_comp.comp h_rs)
  have hargs : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      (p.2.2.1, p.2.2.2.2.1.tables.length)) := Computable.pair ht hlen
  have hprefix : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      xPrefix I p.2.2.1 p.2.2.2.2.1.tables.length) :=
    ((xPrefix_computable hI).comp hargs).of_eq fun _ => rfl
  have hpair : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      (p.2.2.2.2.2.2, xPrefix I p.2.2.1 p.2.2.2.2.1.tables.length)) :=
    (hσ.pair hprefix).of_eq fun _ => rfl
  have hneq : Computable (fun q : List Bool × List Bool => decide (q.1 ≠ q.2)) := by
    have heq : Computable (fun q : List Bool × List Bool => decide (q.1 = q.2)) :=
      Computable₂.comp Primrec.eq.decide.to_comp Computable.fst Computable.snd
    exact (Primrec.not.to_comp.comp heq).of_eq fun q => by
      simp only [ne_eq, decide_not]
  exact (hneq.comp hpair).of_eq fun _ => rfl

-- `hI` is not needed here; the step lemmas of one proof take the same arguments.
set_option linter.unusedVariables false in
/-- Step 2 of the proof of `caseTwoExtendL_computable`: the projection to the updated requirement
state is computable. -/
private lemma caseTwoExtendL_computable_step2_rs1 {I : Input} (hI : I.Valid) :
  Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
    p.2.2.2.2.2.1 :=
      Computable.fst.comp
          (Computable.snd.comp
          (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))))

-- `hI` is not needed here; the step lemmas of one proof take the same arguments.
set_option linter.unusedVariables false in
/-- Step 3 of the proof of `caseTwoExtendL_computable`: the lookup of the next truth table is
computable. -/
private lemma caseTwoExtendL_computable_step3_tableAt {I : Input} (hI : I.Valid) :
  Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
    tableAt p.2.1 p.2.2.2.2.1.tables.length p.2.2.1 := by
  have hi : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.1) :=
    Computable.fst.comp Computable.snd
  have ht : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have h_rs : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.2.2.1) :=
    Computable.fst.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hlen : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.2.2.1.tables.length) :=
    Primrec.list_length.to_comp.comp (ReqStateL.tables_primrec.to_comp.comp h_rs)
  have htriple : Computable (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      (p.2.1, p.2.2.2.2.1.tables.length, p.2.2.1)) :=
    Computable.pair hi (Computable.pair hlen ht)
  exact Computable.of_eq (tableAt_primrec.to_comp.comp htriple) fun _ => rfl

/-- Step 4 of the proof of `caseTwoExtendL_computable`: the examination with the new table
(`caseTwoTableL`) is computable. -/
private lemma caseTwoExtendL_computable_step4_caseTwoTableL {I : Input} (hI : I.Valid) :
  Computable₂ fun (p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) (tbl : TTable) =>
    caseTwoTableL I p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 tbl := by
  have h : Computable
      (fun (x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) × TTable) =>
      (x.1.1, x.1.2.2.1, x.1.2.2.2.1, x.1.2.2.2.2.1, x.1.2.2.2.2.2.1, x.2)) :=
    Computable.pair (Computable.fst.comp Computable.fst)
    (Computable.pair
        (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
    (Computable.pair
        (Computable.fst.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))))
    (Computable.pair
        (Computable.fst.comp
        (Computable.snd.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))))
    (Computable.pair
        (Computable.fst.comp
        (Computable.snd.comp
        (Computable.snd.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))))))
    Computable.snd))))
  exact ((caseTwoTableL_computable hI).comp h).of_eq fun _ => rfl

/-- The comparison with X and the possible table lookup are computable. -/
theorem caseTwoExtendL_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      caseTwoExtendL I p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 := by
  have h_eq : (fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      caseTwoExtendL I p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) = 
      fun p => 
        let rs := p.2.2.2.2.1
        let rs₁ := p.2.2.2.2.2.1
        let σ := p.2.2.2.2.2.2
        let t := p.2.2.1
        let i := p.2.1
        let c := p.2.2.2.1
        let st := p.1
        cond (decide (σ ≠ xPrefix I t rs.tables.length)) (rs₁, false) 
        (Option.casesOn (tableAt i rs.tables.length t)
          (rs₁, false)
          (fun tbl => caseTwoTableL I st t c rs rs₁ tbl)) := by
    funext p
    unfold caseTwoExtendL
    dsimp
    rw [← Bool.cond_decide]
    congr
    cases h_tbl : tableAt p.2.1 p.2.2.2.2.1.tables.length p.2.2.1 <;> rfl
  rw [h_eq]
  apply Computable.cond (caseTwoExtendL_computable_step1_f hI)
  · exact Computable.pair (caseTwoExtendL_computable_step2_rs1 hI) (Computable.const false)
  · exact Computable.option_casesOn (caseTwoExtendL_computable_step3_tableAt hI)
      (Computable.pair (caseTwoExtendL_computable_step2_rs1 hI) (Computable.const false))
      (caseTwoExtendL_computable_step4_caseTwoTableL hI)



private def caseTwoAgreeL_args_split (I : Input)
    (p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) : Option (ℕ × Fin 3) :=
  let rs := p.2.2.2.2.1
  let σ := p.2.2.2.2.2.2
  let ar := arenaOf p.2.2.2.1 rs.tables
  let A := positionL I p.1.ours ar p.2.2.1
  firstStackSplitL ar A σ

/-- Step 1 of the proof of `caseTwoAgreeL_computable`: the search for the first stack split is
computable. -/
private lemma caseTwoAgreeL_computable_step1 (hI : I.Valid) :
    Computable (caseTwoAgreeL_args_split I) := by
  have hst : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool => p.1 :=
    Primrec.fst
  have ht : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hrs : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have htab : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.2.2.1.tables :=
    ReqStateL.tables_primrec.comp hrs
  have har : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      arenaOf p.2.2.2.1 p.2.2.2.2.1.tables :=
    arenaOf_primrec.comp (hc.pair htab)
  have hpos : Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      positionL I p.1.ours (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) p.2.2.1 := by
    refine computable_fin_curry ?_
    have hq : Computable fun q : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
        Fin 3 =>
        ((q.1.1.ours, arenaOf q.1.2.2.2.1 q.1.2.2.2.2.1.tables, q.1.2.2.1, q.2) :
          (Fin 3 → List Str) × Arena × ℕ × Fin 3) :=
      ((ConStateL.ours_primrec.comp (hst.comp Primrec.fst)).pair
        ((har.comp Primrec.fst).pair
          ((ht.comp Primrec.fst).pair Primrec.snd))).to_comp
    exact ((positionL_computable hI).comp hq).of_eq fun _ => rfl
  have hsigma : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      p.2.2.2.2.2.2 :=
    Primrec.snd.comp
        (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))
  have hargs : Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables,
        positionL I p.1.ours (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) p.2.2.1,
        p.2.2.2.2.2.2) :=
    har.to_comp.pair (hpos.pair hsigma.to_comp)
  exact (firstStackSplitL_computable.comp hargs).of_eq fun _ => rfl

private def caseTwoAgreeL_args_some (p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool)
    (lj : ℕ × Fin 3) : ReqStateL × Bool :=
  let rs := p.2.2.2.2.1
  let rs₁ := p.2.2.2.2.2.1
  let σ := p.2.2.2.2.2.2
  let ar := arenaOf p.2.2.2.1 rs.tables
  let ℓ := lj.1
  let j := lj.2
  let k := otherBoard j
  let Eℓ := levelBudget rs.tables ℓ
  let Eℓ' := levelBudget rs.tables (ℓ - 1)
  ({ rs₁ with
    play := some ⟨ar, p.2.2.1, .stacked σ (thirdBoard j k),
      [symGameL j (complL rs.tables.length [σ]) Eℓ, symGameL k [σ] Eℓ']⟩ : ReqStateL }, true)

-- `hI` is not needed here; the step lemmas of one proof take the same arguments.
set_option linter.unusedVariables false in
/-- Step 2 of the proof of `caseTwoAgreeL_computable`: the stacked play started at the split found
in step 1 is computable. -/
private lemma caseTwoAgreeL_computable_step2 (hI : I.Valid) :
    Computable₂ caseTwoAgreeL_args_some := by
  have h_c : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.1.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have h_t : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.1.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have h_rs : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.1.2.2.2.2.1 :=
    Primrec.fst.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have h_rs1 : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.1.2.2.2.2.2.1 :=
    Primrec.fst.comp
        (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  have h_sigma : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.1.2.2.2.2.2.2 :=
    Primrec.snd.comp
        (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  have h_l : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.2.1 := Primrec.fst.comp Primrec.snd
  have h_j : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.2.2 := Primrec.snd.comp Primrec.snd
  have h_rs_tables : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.1.2.2.2.2.1.tables := ReqStateL.tables_primrec.comp h_rs
  have h_ar : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => arenaOf x.1.2.2.2.1 x.1.2.2.2.2.1.tables :=
    arenaOf_primrec.comp (h_c.pair h_rs_tables)
  have h_k : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => otherBoard x.2.2 := otherBoard_primrec.comp h_j
  have h_El : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => levelBudget x.1.2.2.2.2.1.tables x.2.1 :=
    levelBudget_primrec.comp (h_rs_tables.pair h_l)
  have h_l_minus_1 : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.2.1 - 1 := Primrec₂.comp Primrec.nat_sub h_l (Primrec.const 1)
  have h_El_prime : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => levelBudget x.1.2.2.2.2.1.tables (x.2.1 - 1) :=
    levelBudget_primrec.comp (h_rs_tables.pair h_l_minus_1)
  have h_len : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.1.2.2.2.2.1.tables.length := Primrec.list_length.comp h_rs_tables
  have h_sigma_list : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => [x.1.2.2.2.2.2.2] := Primrec₂.comp Primrec.list_cons h_sigma (Primrec.const [])
  have h_compl : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => complL x.1.2.2.2.2.1.tables.length [x.1.2.2.2.2.2.2] :=
    complL_primrec.comp (h_len.pair h_sigma_list)
  have h_game1 : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) =>
      symGameL x.2.2 (complL x.1.2.2.2.2.1.tables.length [x.1.2.2.2.2.2.2])
      (levelBudget x.1.2.2.2.2.1.tables x.2.1) :=
    symGameL_primrec.comp (h_j.pair (h_compl.pair h_El))
  have h_game2 : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) =>
      symGameL (otherBoard x.2.2) [x.1.2.2.2.2.2.2]
      (levelBudget x.1.2.2.2.2.1.tables (x.2.1 - 1)) :=
    symGameL_primrec.comp (h_k.pair (h_sigma_list.pair h_El_prime))
  have h_games : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) =>
      [symGameL x.2.2 (complL x.1.2.2.2.2.1.tables.length [x.1.2.2.2.2.2.2])
      (levelBudget x.1.2.2.2.2.1.tables x.2.1),
      symGameL (otherBoard x.2.2) [x.1.2.2.2.2.2.2]
      (levelBudget x.1.2.2.2.2.1.tables (x.2.1 - 1))] :=
    Primrec₂.comp Primrec.list_cons h_game1
        (Primrec₂.comp Primrec.list_cons h_game2 (Primrec.const []))
  have h_third : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => thirdBoard x.2.2 (otherBoard x.2.2) := thirdBoard_primrec.comp (h_j.pair h_k)
  have h_kind : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => PlayKind.stacked x.1.2.2.2.2.2.2 (thirdBoard x.2.2 (otherBoard x.2.2)) :=
    PlayKind.stacked_primrec.comp (h_sigma.pair h_third)
  have h_play : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) =>
      PlayL.mk (arenaOf x.1.2.2.2.1 x.1.2.2.2.2.1.tables) x.1.2.2.1
      (PlayKind.stacked x.1.2.2.2.2.2.2 (thirdBoard x.2.2 (otherBoard x.2.2)))
      [symGameL x.2.2 (complL x.1.2.2.2.2.1.tables.length [x.1.2.2.2.2.2.2])
      (levelBudget x.1.2.2.2.2.1.tables x.2.1),
      symGameL (otherBoard x.2.2) [x.1.2.2.2.2.2.2]
      (levelBudget x.1.2.2.2.2.1.tables (x.2.1 - 1))] :=
    PlayL.mk_primrec.comp (h_ar.pair (h_t.pair (h_kind.pair h_games)))
  have h_play_opt : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) =>
      some
      (PlayL.mk (arenaOf x.1.2.2.2.1 x.1.2.2.2.2.1.tables) x.1.2.2.1
      (PlayKind.stacked x.1.2.2.2.2.2.2 (thirdBoard x.2.2 (otherBoard x.2.2)))
      [symGameL x.2.2 (complL x.1.2.2.2.2.1.tables.length [x.1.2.2.2.2.2.2])
      (levelBudget x.1.2.2.2.2.1.tables x.2.1),
      symGameL (otherBoard x.2.2) [x.1.2.2.2.2.2.2]
      (levelBudget x.1.2.2.2.2.1.tables (x.2.1 - 1))]) := Primrec.option_some.comp h_play
  have h_rs1_c : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.1.2.2.2.2.2.1.c := ReqStateL.c_primrec.comp h_rs1
  have h_rs1_tables : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) => x.1.2.2.2.2.2.1.tables := ReqStateL.tables_primrec.comp h_rs1
  have h_rs1_baseline : Primrec
      fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) × (ℕ × Fin 3) =>
      x.1.2.2.2.2.2.1.baseline := ReqStateL.baseline_primrec.comp h_rs1
  have h_rs1_lastVisit : Primrec
      fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) × (ℕ × Fin 3) =>
      x.1.2.2.2.2.2.1.lastVisit := ReqStateL.lastVisit_primrec.comp h_rs1
  have h_rs1_lastActed : Primrec
      fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) × (ℕ × Fin 3) =>
      x.1.2.2.2.2.2.1.lastActed := ReqStateL.lastActed_primrec.comp h_rs1
  have h_rs1_new : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) =>
      ReqStateL.mk x.1.2.2.2.2.2.1.c x.1.2.2.2.2.2.1.tables x.1.2.2.2.2.2.1.baseline
      (some
      (PlayL.mk (arenaOf x.1.2.2.2.1 x.1.2.2.2.2.1.tables) x.1.2.2.1
      (PlayKind.stacked x.1.2.2.2.2.2.2 (thirdBoard x.2.2 (otherBoard x.2.2)))
      [symGameL x.2.2 (complL x.1.2.2.2.2.1.tables.length [x.1.2.2.2.2.2.2])
      (levelBudget x.1.2.2.2.2.1.tables x.2.1),
      symGameL (otherBoard x.2.2) [x.1.2.2.2.2.2.2]
      (levelBudget x.1.2.2.2.2.1.tables (x.2.1 - 1))])) x.1.2.2.2.2.2.1.lastVisit
      x.1.2.2.2.2.2.1.lastActed :=
    ReqStateL.mk_primrec.comp
        (h_rs1_c.pair
        (h_rs1_tables.pair
        (h_rs1_baseline.pair (h_play_opt.pair (h_rs1_lastVisit.pair h_rs1_lastActed)))))
  have h_res : Primrec fun x : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool) ×
      (ℕ × Fin 3) =>
      (ReqStateL.mk x.1.2.2.2.2.2.1.c x.1.2.2.2.2.2.1.tables x.1.2.2.2.2.2.1.baseline
      (some
      (PlayL.mk (arenaOf x.1.2.2.2.1 x.1.2.2.2.2.1.tables) x.1.2.2.1
      (PlayKind.stacked x.1.2.2.2.2.2.2 (thirdBoard x.2.2 (otherBoard x.2.2)))
      [symGameL x.2.2 (complL x.1.2.2.2.2.1.tables.length [x.1.2.2.2.2.2.2])
      (levelBudget x.1.2.2.2.2.1.tables x.2.1),
      symGameL (otherBoard x.2.2) [x.1.2.2.2.2.2.2]
      (levelBudget x.1.2.2.2.2.1.tables (x.2.1 - 1))])) x.1.2.2.2.2.2.1.lastVisit
      x.1.2.2.2.2.2.1.lastActed, true) := h_rs1_new.pair (Primrec.const true)
  exact h_res.to_comp.of_eq fun _ => rfl

/-- Continuing an agreement is a computable stack search with two computable alternatives. -/
theorem caseTwoAgreeL_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      caseTwoAgreeL I p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 := by
  have h_split : Computable (caseTwoAgreeL_args_split I) := caseTwoAgreeL_computable_step1 hI
  have h_some : Computable₂ caseTwoAgreeL_args_some := caseTwoAgreeL_computable_step2 hI
  have h_none : Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × ReqStateL × List Bool =>
      caseTwoExtendL I p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 :=
    caseTwoExtendL_computable hI
  exact (Computable.option_casesOn h_split h_none h_some).of_eq fun p => by
    dsimp only [caseTwoAgreeL, caseTwoAgreeL_args_split, caseTwoAgreeL_args_some]
    cases firstStackSplitL (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables)
        (positionL I p.1.ours (arenaOf p.2.2.2.1 p.2.2.2.2.1.tables) p.2.2.1) p.2.2.2.2.2.2
    · rfl
    · rename_i lj
      cases lj
      rfl


/-- Assemble the examination and its agreement continuation to compute Case 2. -/
theorem caseTwoL_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL =>
      caseTwoL I p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have ha : Primrec fun p :
      (ConStateL × ℕ × ℕ × ℕ × ReqStateL) × (ReqStateL × List Bool) =>
      (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2, p.2.1, p.2.2) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          ((Primrec.fst.comp (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair
            ((Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair Primrec.snd))))
  have hc := (caseTwoAgreeL_computable hI).comp ha.to_comp
  exact (Computable.sumCasesOn (examineTopL_computable hI)
    Computable.snd.to₂ hc.to₂).of_eq fun p => by
      unfold caseTwoL
      cases examineTopL I p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 <;> rfl

/-- The response predicate is computable on all its arguments. -/
theorem respondOkL_computable :
    Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      respondOkL p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
  dsimp [respondOkL]
  have h_ar : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str => p.1 :=
    Primrec.fst
  have h_g : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have h_La : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h_a : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h_b : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str => p.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have h_p : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str => p.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  
  have h_costU : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      costU p.1.scale p.2.2.2.2.2.dedup := by
    exact costU_primrec.comp
        (Primrec.pair (Arena.scale_primrec.comp h_ar) (list_dedup_primrec.comp h_p))
      
  have h_le : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      decide (costU p.1.scale p.2.2.2.2.2.dedup ≤ p.2.2.2.2.1) := by
    exact (Primrec.nat_le.decide.comp h_costU h_b).to_comp
    
  have h_p_eq_nil : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      decide (p.2.2.2.2.2 = []) := by
    exact (Primrec.beq.comp h_p (Primrec.const [])).to_comp
    
  have h_target : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      p.2.1.target :=
    BoardGameL.target_primrec.comp h_g
    
  have h_valueL : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      valueL p.1 p.2.2.1 := by
    exact valueL_primrec.comp (Primrec.pair h_ar h_La)
    
  have h_mem_args : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      (valueL p.1 p.2.2.1, p.2.1.target) :=
    Computable.pair h_valueL.to_comp h_target.to_comp
  have h_mem_target : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      decide (valueL p.1 p.2.2.1 ∈ p.2.1.target) := by
    refine ((list_mem_primrec (β := List Bool)).to_comp.comp h_mem_args).of_eq fun p => ?_
    exact decide_eq_decide.mpr Iff.rfl
      
  have h_forcesB_then : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      forcesB p.1 p.2.1.target p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 := by
    exact (forcesL_computable.comp
        (Computable.pair h_ar.to_comp
        (Computable.pair h_target.to_comp
        (Computable.pair h_La.to_comp (Computable.pair h_a.to_comp h_b.to_comp))))).of_eq fun _ =>
        rfl
  
  have h_diff : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      diffL p.2.2.1 p.2.2.2.2.2 := by
    exact diffL_primrec.comp (Primrec.pair h_La h_p)
    
  have h_cost_sub : Primrec fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      p.2.2.2.2.1 - costU p.1.scale p.2.2.2.2.2.dedup := by
    exact (Primrec.nat_sub.comp h_b h_costU)
    
  have h_forcesB_else : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      forcesB p.1 p.2.1.target (diffL p.2.2.1 p.2.2.2.2.2) p.2.2.2.1
          (p.2.2.2.2.1 - costU p.1.scale p.2.2.2.2.2.dedup) := by
    exact (forcesL_computable.comp
        (Computable.pair h_ar.to_comp
        (Computable.pair h_target.to_comp
        (Computable.pair h_diff.to_comp (Computable.pair h_a.to_comp h_cost_sub.to_comp))))).of_eq
        fun _ => rfl
  have h_then : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      decide (valueL p.1 p.2.2.1 ∈ p.2.1.target) && forcesB p.1 p.2.1.target p.2.2.1 p.2.2.2.1
          p.2.2.2.2.1 := by
    have H : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      (decide (valueL p.1 p.2.2.1 ∈ p.2.1.target),
          forcesB p.1 p.2.1.target p.2.2.1 p.2.2.2.1 p.2.2.2.2.1) :=
        Computable.pair h_mem_target h_forcesB_then
    exact ((Primrec.and.comp Primrec.fst Primrec.snd).to_comp.comp H).of_eq fun _ => rfl
      
  have h_if : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      if p.2.2.2.2.2 = [] then
        decide (valueL p.1 p.2.2.1 ∈ p.2.1.target) && forcesB p.1 p.2.1.target p.2.2.1 p.2.2.2.1
            p.2.2.2.2.1
      else
        forcesB p.1 p.2.1.target (diffL p.2.2.1 p.2.2.2.2.2) p.2.2.2.1
            (p.2.2.2.2.1 - costU p.1.scale p.2.2.2.2.2.dedup) := by
    exact (Computable.cond h_p_eq_nil h_then h_forcesB_else).of_eq fun p => by
      by_cases h : p.2.2.2.2.2 = []
      · simp [h]
      · simp [h]
      
  have H : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ × List Str =>
      (decide (costU p.1.scale p.2.2.2.2.2.dedup ≤ p.2.2.2.2.1),
      (if p.2.2.2.2.2 = [] then
        decide (valueL p.1 p.2.2.1 ∈ p.2.1.target) && forcesB p.1 p.2.1.target p.2.2.1 p.2.2.2.1
            p.2.2.2.2.1
      else
        forcesB p.1 p.2.1.target (diffL p.2.2.1 p.2.2.2.2.2) p.2.2.2.1
            (p.2.2.2.2.1 - costU p.1.scale p.2.2.2.2.2.dedup))) := Computable.pair h_le h_if
  exact ((Primrec.and.comp Primrec.fst Primrec.snd).to_comp.comp H).of_eq fun _ => rfl

/-- Responding is a computable ordered sublist search. -/
theorem respondL_computable :
    Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ =>
      respondL p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have ha : Primrec fun p : (Arena × BoardGameL × List Str × ℕ × ℕ) × List Str =>
      (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2, p.2) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          ((Primrec.fst.comp (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair
            ((Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair Primrec.snd))))
  have hl : Computable fun p : Arena × BoardGameL × List Str × ℕ × ℕ => p.2.2.1.sublists :=
    list_sublists_primrec.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.snd))
  exact (Computable.option_getD
    (computable_list_find hl (respondOkL_computable.comp ha.to_comp).to₂)
    (Computable.const [])).of_eq fun _ => rfl

private theorem movesL_computable_aux1 (hI : I.Valid) :
  Computable₂ fun (p : (Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) (g : BoardGameL) =>
    (g,
        respondL p.2.1 g (positionL I p.1 p.2.1 p.2.2.1 g.board) (g.oppLimit - p.2.2.2.1)
        (g.ourLimit - g.spent)) := by
  have h_g : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL => p.2 := Computable.snd
  have ha1 : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL => p.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have ha2 : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL => p.2 :=
    Computable.snd
  have ht : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL =>
      (p.1.1, p.1.2.1, p.1.2.2.1, p.2.board) := by
    exact (Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
        (BoardGameL.board_primrec.to_comp.comp Computable.snd)))
  have ha4 : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL =>
      positionL I p.1.1 p.1.2.1 p.1.2.2.1 p.2.board :=
    @Computable.comp (((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) × BoardGameL)
        ((Fin 3 → List Str) × Arena × ℕ × Fin 3) (List Str) _ _ _
        (fun p : (Fin 3 → List Str) × Arena × ℕ × Fin 3 => positionL I p.1 p.2.1 p.2.2.1 p.2.2.2)
        (fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) × BoardGameL =>
        (p.1.1, p.1.2.1, p.1.2.2.1, p.2.board)) (positionL_computable hI) ht
  have ho1 : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL => p.2.oppLimit := BoardGameL.oppLimit_primrec.to_comp.comp Computable.snd
  have ho2 : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL => p.1.2.2.2.1 :=
    Computable.fst.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have ha5 : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL => p.2.oppLimit - p.1.2.2.2.1 :=
    @Computable₂.comp (((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) × BoardGameL) ℕ ℕ ℕ _
        _ _ _ (fun a b => a - b)
        (fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) × BoardGameL =>
        p.2.oppLimit)
        (fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) × BoardGameL => p.1.2.2.2.1)
        (Primrec₂.to_comp Primrec.nat_sub) ho1 ho2
  have hu1 : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL => p.2.ourLimit := BoardGameL.ourLimit_primrec.to_comp.comp Computable.snd
  have hu2 : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL => p.2.spent := BoardGameL.spent_primrec.to_comp.comp Computable.snd
  have ha6 : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL => p.2.ourLimit - p.2.spent :=
    @Computable₂.comp (((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) × BoardGameL) ℕ ℕ ℕ _
        _ _ _ (fun a b => a - b)
        (fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) × BoardGameL =>
        p.2.ourLimit)
        (fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) × BoardGameL => p.2.spent)
        (Primrec₂.to_comp Primrec.nat_sub) hu1 hu2
  have h_arg : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL =>
    (p.1.2.1, p.2, positionL I p.1.1 p.1.2.1 p.1.2.2.1 p.2.board, p.2.oppLimit - p.1.2.2.2.1,
        p.2.ourLimit - p.2.spent) := ha1.pair (ha2.pair (ha4.pair (ha5.pair ha6)))
  have h_respond : Computable fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) ×
      BoardGameL => 
      respondL p.1.2.1 p.2 (positionL I p.1.1 p.1.2.1 p.1.2.2.1 p.2.board)
          (p.2.oppLimit - p.1.2.2.2.1) (p.2.ourLimit - p.2.spent) :=
    @Computable.comp (((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) × BoardGameL)
        (Arena × BoardGameL × List Str × ℕ × ℕ) (List Str) _ _ _
        (fun p : Arena × BoardGameL × List Str × ℕ × ℕ =>
        respondL p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
        (fun p : ((Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL) × BoardGameL =>
        (p.1.2.1, p.2, positionL I p.1.1 p.1.2.1 p.1.2.2.1 p.2.board, p.2.oppLimit - p.1.2.2.2.1,
        p.2.ourLimit - p.2.spent)) respondL_computable h_arg
  exact h_g.pair h_respond

/-- Response generation is a computable map in the original game order. -/
theorem movesL_computable (hI : I.Valid) :
    Computable fun p : (Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL =>
      movesL I p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  dsimp only [movesL]
  have h_list : Computable fun p : (Fin 3 → List Str) × Arena × ℕ × ℕ × List BoardGameL =>
      p.2.2.2.2 := 
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact computable_list_map h_list (movesL_computable_aux1 hI)

/-- Spending updates are primitive recursive maps of the list of responses. -/
theorem advanceGamesL_primrec :
    Primrec fun p : Arena × List (BoardGameL × List Str) => advanceGamesL p.1 p.2 := by
  dsimp only [advanceGamesL]
  apply Primrec.list_map Primrec.snd
  apply Primrec.of_eq
      (Primrec.comp BoardGameL.mk_primrec
      (Primrec.pair (Primrec.comp BoardGameL.board_primrec (Primrec.comp Primrec.fst Primrec.snd))
    (Primrec.pair (Primrec.comp BoardGameL.target_primrec (Primrec.comp Primrec.fst Primrec.snd))
    (Primrec.pair (Primrec.comp BoardGameL.oppLimit_primrec (Primrec.comp Primrec.fst Primrec.snd))
    (Primrec.pair (Primrec.comp BoardGameL.ourLimit_primrec (Primrec.comp Primrec.fst Primrec.snd))
    (Primrec₂.comp Primrec.nat_add
        (Primrec.comp BoardGameL.spent_primrec (Primrec.comp Primrec.fst Primrec.snd))
      (Primrec.comp StateTwin.costU_primrec
          (Primrec.pair (Primrec.comp Arena.scale_primrec (Primrec.comp Primrec.fst Primrec.fst)) 
        (Primrec.comp list_dedup_primrec (Primrec.comp Primrec.snd Primrec.snd))))
    ))))))
  intro x
  rfl

/-- Merging moves into the three board lists is primitive recursive. -/
theorem mergeMovesL_primrec :
    Primrec fun p : (Fin 3 → List Str) × List (BoardGameL × List Str) =>
      mergeMovesL p.1 p.2 := by
  have h_eq : (fun (p : (Fin 3 → List Str) × List (BoardGameL × List Str)) =>
      mergeMovesL p.1 p.2) = 
      fun p j => (mergeMovesL p.1 p.2 j) := by rfl
  rw [h_eq]
  apply Primrec.fin_curry.mpr
  dsimp only [mergeMovesL]
  exact @Primrec.list_foldr (((Fin 3 → List Str) × List (BoardGameL × List Str)) × Fin 3)
      (BoardGameL × List Str) (List Str)
    _ _ _ (fun p => p.1.2) (fun p => p.1.1 p.2) 
    (fun p q => if q.1.1.board = p.2 then q.1.2 ++ q.2 else q.2)
    (Primrec.snd.comp Primrec.fst)
    (Primrec.fin_app.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (by
      apply Primrec.ite
      · exact Primrec.eq.comp
            (BoardGameL.board_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp Primrec.fst)
      · exact Primrec.list_append.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.snd.comp Primrec.snd)
      · exact Primrec.snd.comp Primrec.snd)

/-- Step 1 of the proof of `caseThreeMoveL_computable`: our responses (`movesL`) are computable. -/
private lemma caseThreeMoveL_computable_step1_moves {I : Input} (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ =>
      movesL I p.1.ours p.2.2.2.1.arena p.2.1 p.2.2.2.2 p.2.2.2.1.games := by
  have h_st : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ => p.1.ours :=
    ConStateL.ours_primrec.to_comp.comp Computable.fst
  have h_pl : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ => p.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have h_ar : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ => p.2.2.2.1.arena :=
    PlayL.arena_primrec.to_comp.comp h_pl
  have h_t : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ => p.2.1 :=
    Computable.fst.comp Computable.snd
  have h_lam : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ => p.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have h_games : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ => p.2.2.2.1.games :=
    PlayL.games_primrec.to_comp.comp h_pl
  have h_arg : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ =>
    (p.1.ours, p.2.2.2.1.arena, p.2.1, p.2.2.2.2, p.2.2.2.1.games) :=
    h_st.pair (h_ar.pair (h_t.pair (h_lam.pair h_games)))
  have h := (movesL_computable hI).comp h_arg
  exact h

/-- Step 2 of the proof of `caseThreeMoveL_computable`: the updated requirement state is
computable. -/
private lemma caseThreeMoveL_computable_step2_req {I : Input} (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ =>
      ({ p.2.2.1 with play := some { p.2.2.2.1 with games := advanceGamesL p.2.2.2.1.arena (movesL I
          p.1.ours p.2.2.2.1.arena p.2.1 p.2.2.2.2 p.2.2.2.1.games) } } : ReqStateL) := by
  exact (ReqStateL.mk_primrec.to_comp.comp
    ((ReqStateL.c_primrec.to_comp.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair
      ((ReqStateL.tables_primrec.to_comp.comp
          (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair
        ((ReqStateL.baseline_primrec.to_comp.comp
            (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair
          ((Computable.option_some.comp (PlayL.mk_primrec.to_comp.comp
            ((PlayL.arena_primrec.to_comp.comp
                (Computable.fst.comp
                (Computable.snd.comp (Computable.snd.comp Computable.snd)))).pair
              ((PlayL.start_primrec.to_comp.comp
                  (Computable.fst.comp
                  (Computable.snd.comp (Computable.snd.comp Computable.snd)))).pair
                ((PlayL.kind_primrec.to_comp.comp
                    (Computable.fst.comp
                    (Computable.snd.comp (Computable.snd.comp Computable.snd)))).pair
                  (advanceGamesL_primrec.to_comp.comp
                      ((PlayL.arena_primrec.to_comp.comp
                      (Computable.fst.comp
                      (Computable.snd.comp (Computable.snd.comp Computable.snd)))).pair
                      (caseThreeMoveL_computable_step1_moves hI)))))))).pair
            ((ReqStateL.lastVisit_primrec.to_comp.comp
                (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair
              (ReqStateL.lastActed_primrec.to_comp.comp
                  (Computable.fst.comp (Computable.snd.comp Computable.snd))))))))).of_eq fun _ =>
                  rfl

/-- Step 3 of the proof of `caseThreeMoveL_computable`: the boards after our moves (`mergeMovesL`)
are computable. -/
private lemma caseThreeMoveL_computable_step3_merge {I : Input} (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ =>
      mergeMovesL p.1.ours (movesL I p.1.ours p.2.2.2.1.arena p.2.1 p.2.2.2.2 p.2.2.2.1.games) := by
  have hm1 := caseThreeMoveL_computable_step1_moves hI
  have h :=
    mergeMovesL_primrec.to_comp.comp ((ConStateL.ours_primrec.comp Primrec.fst).to_comp.pair hm1)
  exact h

/-- Step 4 of the proof of `caseThreeMoveL_computable`: the test whether some response is a
nonempty move is computable. -/
private lemma caseThreeMoveL_computable_step4_any {I : Input} (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ =>
      (movesL I p.1.ours p.2.2.2.1.arena p.2.1 p.2.2.2.2 p.2.2.2.1.games).any fun q =>
          decide (q.2 ≠ []) := by
  have hm1 := caseThreeMoveL_computable_step1_moves hI
  have h_pred : Computable₂ fun (_ : ConStateL × ℕ × ReqStateL × PlayL × ℕ)
      (q : BoardGameL × List (List Bool)) => decide (q.2 ≠ []) := by
    have h1 : Primrec₂ fun (_ : ConStateL × ℕ × ReqStateL × PlayL × ℕ)
        (q : BoardGameL × List (List Bool)) => decide (q.2 ≠ []) := by
      have h2 : Primrec fun q : BoardGameL × List (List Bool) => decide (q.2 ≠ []) := by
        have h3 : Primrec fun q : BoardGameL × List (List Bool) => q.2.head?.isSome :=
          Primrec.option_isSome.comp (Primrec.list_head?.comp Primrec.snd)
        apply h3.of_eq
        intro q
        cases q.2 with
        | nil => rfl
        | cons head tail => rfl
      exact h2.comp Primrec.snd
    exact h1.to_comp
  apply computable_list_any hm1 h_pred


/-- The response branch is computable by combining responses and primitive recursive updates. -/
theorem caseThreeMoveL_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ =>
      caseThreeMoveL I p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have hm1 := caseThreeMoveL_computable_step2_req hI
  have hm2 := caseThreeMoveL_computable_step3_merge hI
  have hm3 := caseThreeMoveL_computable_step4_any hI
  exact hm1.pair (hm2.pair hm3)

/-- Step 1 of the proof of `caseThreeBishopL_computable`: the search for a knight on which the
complement of the agreed value wins the symmetric game is computable. -/
private theorem caseThreeBishopL_computable_step1_opt {I : Input} (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      let st := p.1
      let t := p.2.1
      let pl := p.2.2.2.1
      let σ := p.2.2.2.2.2.1
      let ar := pl.arena
      let E := levelBudget ar.tables 0
      let knights := pl.games.map BoardGameL.board
      let A := positionL I st.ours ar t
      knights.find? (fun j => forcesB ar (complL ar.tables.length [σ]) (A j) E E) := by
  have h_st : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 => p.1 :=
    Computable.fst
  have h_t : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.1 :=
    Computable.fst.comp Computable.snd
  have h_pl : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have h_sigma : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.2.2.2.1 :=
    Computable.fst.comp
        (Computable.snd.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have h_ar : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.2.1.arena :=
    (PlayL.arena_primrec.to_comp.comp h_pl).of_eq fun _ => rfl
  have h_tables : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.2.1.arena.tables :=
    (Arena.tables_primrec.to_comp.comp h_ar).of_eq fun _ => rfl
  have h_E : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      levelBudget p.2.2.2.1.arena.tables 0 := 
    (levelBudget_primrec.to_comp.comp (h_tables.pair (Computable.const 0))).of_eq fun _ => rfl
  have h_games : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.2.1.games :=
    (PlayL.games_primrec.to_comp.comp h_pl).of_eq fun _ => rfl
  have h_f : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.2.1.games.map BoardGameL.board :=
    (computable_list_map h_games (BoardGameL.board_primrec.to_comp.comp Computable.snd).to₂).of_eq
        fun _ => rfl
  have h_j : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.2 := Computable.snd
  have h_p : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1 := Computable.fst
  have h_ar_j : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.2.1.arena := (h_ar.comp h_p).of_eq fun _ => rfl
  have h_tables_j : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.2.1.arena.tables := (h_tables.comp h_p).of_eq fun _ => rfl
  have h_sigma_j : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.2.2.2.1 := (h_sigma.comp h_p).of_eq fun _ => rfl
  have h_E_j : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => levelBudget p.1.2.2.2.1.arena.tables 0 := (h_E.comp h_p).of_eq fun _ => rfl
  
  have h_len : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.2.1.arena.tables.length :=
    (Computable.list_length.comp h_tables_j).of_eq fun _ => rfl
  have h_sig_list : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => [p.1.2.2.2.2.2.1] :=
    (Computable.list_cons.comp h_sigma_j (Computable.const [])).of_eq fun _ => rfl
  have h_compl : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => complL p.1.2.2.2.1.arena.tables.length [p.1.2.2.2.2.2.1] :=
    (complL_primrec.to_comp.comp (h_len.pair h_sig_list)).of_eq fun _ => rfl
  have h_A_j : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => positionL I p.1.1.ours p.1.2.2.2.1.arena p.1.2.1 p.2 := by
    have h_ours : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
        Fin 3 => p.1.1.ours :=
      (ConStateL.ours_primrec.to_comp.comp (h_st.comp h_p)).of_eq fun _ => rfl
    have h_t_j : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
        Fin 3 => p.1.2.1 := (h_t.comp h_p).of_eq fun _ => rfl
    have h_args : Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
        Fin 3 => (p.1.1.ours, p.1.2.2.2.1.arena, p.1.2.1, p.2) :=
      (h_ours.pair (h_ar_j.pair (h_t_j.pair h_j))).of_eq fun _ => rfl
    exact ((positionL_computable hI).comp h_args).of_eq fun _ => rfl
  have h_forces_arg : Computable
      fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      (p.1.2.2.2.1.arena, complL p.1.2.2.2.1.arena.tables.length [p.1.2.2.2.2.2.1],
      positionL I p.1.1.ours p.1.2.2.2.1.arena p.1.2.1 p.2, levelBudget p.1.2.2.2.1.arena.tables 0,
      levelBudget p.1.2.2.2.1.arena.tables 0) := by
    exact (h_ar_j.pair (h_compl.pair (h_A_j.pair (h_E_j.pair h_E_j)))).of_eq fun _ => rfl
  have h_forces : Computable₂ fun (p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3)
      (j : Fin 3) =>
      forcesB p.2.2.2.1.arena (complL p.2.2.2.1.arena.tables.length [p.2.2.2.2.2.1])
      (positionL I p.1.ours p.2.2.2.1.arena p.2.1 j) (levelBudget p.2.2.2.1.arena.tables 0)
      (levelBudget p.2.2.2.1.arena.tables 0) := by
    exact ((forcesL_computable.comp h_forces_arg).of_eq fun _ => rfl).to₂
  exact (computable_list_find h_f h_forces).of_eq fun _ => rfl

private theorem caseThreeBishopL_computable_step2_some :
    Computable fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      let st := p.1.1
      let t := p.1.2.1
      let rs := p.1.2.2.1
      let pl := p.1.2.2.2.1
      let lam := p.1.2.2.2.2.1
      let σ := p.1.2.2.2.2.2.1
      let bishop := p.1.2.2.2.2.2.2
      let ar := pl.arena
      let E := levelBudget ar.tables 0
      let j := p.2
      ({ rs with
        play := some (unbalancedPlayL ar t E (E - lam) σ j bishop) },
        st.ours, true) := by
  have h_st : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      p.1.1 := Primrec.fst.comp Primrec.fst
  have h_t : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      p.1.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have h_rs : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      p.1.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have h_pl : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      p.1.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have h_lam : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.2.2.1 :=
    Primrec.fst.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have h_sigma : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.2.2.2.1 :=
    Primrec.fst.comp
        (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  have h_bishop : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.2.2.2.2 :=
    Primrec.snd.comp
        (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  have h_j : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      p.2 := Primrec.snd
  
  have h_ar : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      p.1.2.2.2.1.arena := PlayL.arena_primrec.comp h_pl
  have h_tables : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.2.1.arena.tables := Arena.tables_primrec.comp h_ar
  have h_E : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      levelBudget p.1.2.2.2.1.arena.tables 0 :=
    levelBudget_primrec.comp (h_tables.pair (Primrec.const 0))
  have h_sub : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => levelBudget p.1.2.2.2.1.arena.tables 0 - p.1.2.2.2.2.1 :=
    Primrec₂.comp Primrec.nat_sub h_E h_lam
  
  have h_args : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 =>
      (p.1.2.2.2.1.arena, p.1.2.1, levelBudget p.1.2.2.2.1.arena.tables 0,
      levelBudget p.1.2.2.2.1.arena.tables 0 - p.1.2.2.2.2.1, p.1.2.2.2.2.2.1, p.2,
      p.1.2.2.2.2.2.2) :=
    h_ar.pair (h_t.pair (h_E.pair (h_sub.pair (h_sigma.pair (h_j.pair h_bishop)))))
  
  have h_play : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 =>
      unbalancedPlayL p.1.2.2.2.1.arena p.1.2.1 (levelBudget p.1.2.2.2.1.arena.tables 0)
      (levelBudget p.1.2.2.2.1.arena.tables 0 - p.1.2.2.2.2.1) p.1.2.2.2.2.2.1 p.2
      p.1.2.2.2.2.2.2 := unbalancedPlayL_primrec.comp h_args
  
  have h_play_opt : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 =>
      some
      (unbalancedPlayL p.1.2.2.2.1.arena p.1.2.1 (levelBudget p.1.2.2.2.1.arena.tables 0)
      (levelBudget p.1.2.2.2.1.arena.tables 0 - p.1.2.2.2.2.1) p.1.2.2.2.2.2.1 p.2
      p.1.2.2.2.2.2.2) := Primrec.option_some.comp h_play
  
  have h_rs_c : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.1.c := ReqStateL.c_primrec.comp h_rs
  have h_rs_tables : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.1.tables := ReqStateL.tables_primrec.comp h_rs
  have h_rs_baseline : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.2.2.1.baseline := ReqStateL.baseline_primrec.comp h_rs
  have h_rs_lastVisit : Primrec
      fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      p.1.2.2.1.lastVisit := ReqStateL.lastVisit_primrec.comp h_rs
  have h_rs_lastActed : Primrec
      fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) × Fin 3 =>
      p.1.2.2.1.lastActed := ReqStateL.lastActed_primrec.comp h_rs
  
  have h_new_rs_args : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 =>
      (p.1.2.2.1.c, p.1.2.2.1.tables, p.1.2.2.1.baseline,
      some
      (unbalancedPlayL p.1.2.2.2.1.arena p.1.2.1 (levelBudget p.1.2.2.2.1.arena.tables 0)
      (levelBudget p.1.2.2.2.1.arena.tables 0 - p.1.2.2.2.2.1) p.1.2.2.2.2.2.1 p.2 p.1.2.2.2.2.2.2),
      p.1.2.2.1.lastVisit, p.1.2.2.1.lastActed) :=
    h_rs_c.pair
        (h_rs_tables.pair
        (h_rs_baseline.pair (h_play_opt.pair (h_rs_lastVisit.pair h_rs_lastActed))))
  
  have h_new_rs : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 =>
      { p.1.2.2.1 with play := some (unbalancedPlayL p.1.2.2.2.1.arena p.1.2.1
      (levelBudget p.1.2.2.2.1.arena.tables 0)
      (levelBudget p.1.2.2.2.1.arena.tables 0 - p.1.2.2.2.2.1) p.1.2.2.2.2.2.1 p.2
      p.1.2.2.2.2.2.2) } := ReqStateL.mk_primrec.comp h_new_rs_args
  
  have h_st_ours : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 => p.1.1.ours := ConStateL.ours_primrec.comp h_st
  
  have h_res : Primrec fun p : (ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3) ×
      Fin 3 =>
      ({ p.1.2.2.1 with play := some (unbalancedPlayL p.1.2.2.2.1.arena p.1.2.1
      (levelBudget p.1.2.2.2.1.arena.tables 0)
      (levelBudget p.1.2.2.2.1.arena.tables 0 - p.1.2.2.2.2.1) p.1.2.2.2.2.2.1 p.2
      p.1.2.2.2.2.2.2) }, p.1.1.ours, true) := h_new_rs.pair (h_st_ours.pair (Primrec.const true))
  
  exact h_res.to_comp.of_eq fun _ => rfl

private theorem caseThreeBishopL_computable_step3_none :
    Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      let st := p.1
      let t := p.2.1
      let rs := p.2.2.1
      let bishop := p.2.2.2.2.2.2
      ({ rs with play := none, baseline := rs.baseline.map fun bl =>
        bishopBaselineL bl bishop t }, st.ours, true) := by
  have h_rs : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.1 :=
    (Computable.fst.comp (Computable.snd.comp Computable.snd)).of_eq fun _ => rfl
  have h_t : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.1 :=
    (Computable.fst.comp Computable.snd).of_eq fun _ => rfl
  have h_bishop : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.2.2.2.2 :=
    (Computable.snd.comp
        (Computable.snd.comp
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))))).of_eq
        fun _ => rfl
  have h_bl_mapped : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.1.baseline.map fun bl => bishopBaselineL bl p.2.2.2.2.2.2 p.2.1 :=
    Computable.option_map (ReqStateL.baseline_primrec.to_comp.comp h_rs)
        (bishopBaselineL_primrec.to_comp.comp
        (Computable.snd.pair ((h_bishop.comp Computable.fst).pair (h_t.comp Computable.fst)))).to₂
  have h_c : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.1.c :=
    ReqStateL.c_primrec.to_comp.comp h_rs
  have h_tables : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.1.tables :=
    ReqStateL.tables_primrec.to_comp.comp h_rs
  have h_lastVisit : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.1.lastVisit :=
    ReqStateL.lastVisit_primrec.to_comp.comp h_rs
  have h_lastActed : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.2.2.1.lastActed :=
    ReqStateL.lastActed_primrec.to_comp.comp h_rs
  have h_none : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      (none : Option PlayL) :=
    Computable.const none
  have h_rs_args : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      (p.2.2.1.c, p.2.2.1.tables, p.2.2.1.baseline.map fun bl =>
      bishopBaselineL bl p.2.2.2.2.2.2 p.2.1, (none : Option PlayL), p.2.2.1.lastVisit,
      p.2.2.1.lastActed) :=
    h_c.pair (h_tables.pair (h_bl_mapped.pair (h_none.pair (h_lastVisit.pair h_lastActed))))
  have h_rs_new : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      ReqStateL.mk p.2.2.1.c p.2.2.1.tables
      (p.2.2.1.baseline.map fun bl => bishopBaselineL bl p.2.2.2.2.2.2 p.2.1) none p.2.2.1.lastVisit
      p.2.2.1.lastActed :=
    (ReqStateL.mk_primrec.to_comp.comp h_rs_args).of_eq fun _ => rfl
  have h_ours : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      p.1.ours :=
    ConStateL.ours_primrec.to_comp.comp Computable.fst
  have h_true : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      true :=
    Computable.const true
  have h_final : Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      (ReqStateL.mk p.2.2.1.c p.2.2.1.tables
      (p.2.2.1.baseline.map fun bl => bishopBaselineL bl p.2.2.2.2.2.2 p.2.1) none p.2.2.1.lastVisit
      p.2.2.1.lastActed, p.1.ours, true) :=
    Computable.pair h_rs_new (Computable.pair h_ours h_true)
  exact h_final.of_eq fun _ => rfl

/-- The bishop branch is a computable search with primitive recursive output updates. -/
theorem caseThreeBishopL_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ × List Bool × Fin 3 =>
      caseThreeBishopL I p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 := by
  have h1 := caseThreeBishopL_computable_step1_opt hI
  have h2 := caseThreeBishopL_computable_step3_none
  have h3 := caseThreeBishopL_computable_step2_some
  exact (Computable.option_casesOn h1 h2 h3.to₂).of_eq fun p => by
    dsimp [caseThreeBishopL, positionL]
    cases p.2.2.2.1.games.map BoardGameL.board |>.find?
        (fun j =>
        forcesB p.2.2.2.1.arena (complL p.2.2.2.1.arena.tables.length [p.2.2.2.2.2.1])
        (List.filter (aliveL I p.1.ours p.2.1 j) p.2.2.2.1.arena.boardList)
        (levelBudget p.2.2.2.1.arena.tables 0) (levelBudget p.2.2.2.1.arena.tables 0)) <;> rfl

/-- Clearing the baseline and play is primitive recursive. -/
theorem caseThreeStopL_primrec :
    Primrec fun p : ConStateL × ReqStateL => caseThreeStopL p.1 p.2 := by
  have hr : Primrec fun p : ConStateL × ReqStateL =>
      ({ p.2 with play := none, baseline := none } : ReqStateL) :=
    ReqStateL.mk_primrec.comp
      ((ReqStateL.c_primrec.comp Primrec.snd).pair
        ((ReqStateL.tables_primrec.comp Primrec.snd).pair
          ((Primrec.const none).pair ((Primrec.const none).pair
            ((ReqStateL.lastVisit_primrec.comp Primrec.snd).pair
              (ReqStateL.lastActed_primrec.comp Primrec.snd))))))
  exact hr.pair ((ConStateL.ours_primrec.comp Primrec.fst).pair (Primrec.const true))

/-- The postlimit choice is computable by decoding the play kind. -/
theorem caseThreeAfterL_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ReqStateL × PlayL × ℕ =>
      caseThreeAfterL I p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  let P := ConStateL × ℕ × ReqStateL × PlayL × ℕ
  have hst : Computable fun p : P => p.1 := Computable.fst
  have ht : Computable fun p : P => p.2.1 := Computable.fst.comp Computable.snd
  have hrs : Computable fun p : P => p.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hpl : Computable fun p : P => p.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hlam : Computable fun p : P => p.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hstop : Computable fun p : P => caseThreeStopL p.1 p.2.2.1 :=
    (caseThreeStopL_primrec.to_comp.comp (hst.pair hrs)).of_eq fun _ => rfl
  have hbudget : Computable fun p : P => levelBudget p.2.2.2.1.arena.tables 0 :=
    (levelBudget_primrec.to_comp.comp
      ((Arena.tables_primrec.to_comp.comp (PlayL.arena_primrec.to_comp.comp hpl)).pair
        (Computable.const 0))).of_eq fun _ => rfl
  have hle : Computable fun p : P =>
      decide (p.2.2.2.2 ≤ levelBudget p.2.2.2.1.arena.tables 0) :=
    (Primrec.nat_le.decide.to_comp.comp hlam hbudget).of_eq fun _ => rfl
  have hargs : Computable fun q : P × (List Bool × Fin 3) =>
      (q.1.1, q.1.2.1, q.1.2.2.1, q.1.2.2.2.1, q.1.2.2.2.2, q.2.1, q.2.2) :=
    (hst.comp Computable.fst).pair ((ht.comp Computable.fst).pair
      ((hrs.comp Computable.fst).pair ((hpl.comp Computable.fst).pair
        ((hlam.comp Computable.fst).pair ((Computable.fst.comp Computable.snd).pair
          (Computable.snd.comp Computable.snd))))))
  have hstack : Computable fun q : P × (List Bool × Fin 3) =>
      if q.1.2.2.2.2 ≤ levelBudget q.1.2.2.2.1.arena.tables 0 then
        caseThreeBishopL I q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 q.2.1 q.2.2
      else caseThreeStopL q.1.1 q.1.2.2.1 := by
    exact (Computable.cond (hle.comp Computable.fst)
      ((caseThreeBishopL_computable hI).comp hargs)
      (hstop.comp Computable.fst)).of_eq fun q => by simp only [Bool.cond_decide]
  have hinner := Computable.option_casesOn
    (show Computable fun q : P × Option (List Bool × Fin 3) => q.2 from Computable.snd)
    (hstop.comp Computable.fst)
    (hstack.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
  exact (Computable.option_casesOn
    (PlayKind.code_primrec.to_comp.comp (PlayL.kind_primrec.to_comp.comp hpl))
    hstop hinner.to₂).of_eq fun p => by
      unfold caseThreeAfterL
      cases p.2.2.2.1.kind <;> rfl

/-- The minimum game limit is a primitive recursive fold. -/
theorem gameLimit_primrec : Primrec fun pl : PlayL =>
    pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0) := by
  have he := levelBudget_primrec.comp
    ((Arena.tables_primrec.comp PlayL.arena_primrec).pair (Primrec.const 0))
  exact Primrec.list_foldr PlayL.games_primrec he
    (Primrec.nat_min.comp (BoardGameL.oppLimit_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- Case 3 compares computable opponent spending with the primitive recursive game limit. -/
theorem caseThreeL_computable (hI : I.Valid) :
    Computable fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × PlayL =>
      caseThreeL I p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
  have hp : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × PlayL => p.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have ht : Primrec fun p : ConStateL × ℕ × ℕ × ℕ × ReqStateL × PlayL => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl := (oppSpendL_computable hI).comp
    ((PlayL.arena_primrec.comp hp).to_comp.pair
      ((PlayL.start_primrec.comp hp).to_comp.pair ht.to_comp))
  have hlim := gameLimit_primrec.to_comp.comp hp.to_comp
  have ha : Primrec fun p : (ConStateL × ℕ × ℕ × ℕ × ReqStateL × PlayL) × ℕ =>
      (p.1.1, p.1.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2, p.2) :=
    (Primrec.fst.comp Primrec.fst).pair ((ht.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).pair
          ((hp.comp Primrec.fst).pair Primrec.snd)))
  have hargs := ha.to_comp.comp (Computable.id.pair hl)
  exact (Computable.cond (Primrec.nat_le.decide.to_comp.comp hl hlim)
    ((caseThreeMoveL_computable hI).comp hargs)
    ((caseThreeAfterL_computable hI).comp hargs)).of_eq fun p => by
      unfold caseThreeL
      by_cases hle : oppSpendL I p.2.2.2.2.2.arena p.2.2.2.2.2.start p.2.2.1 ≤
          p.2.2.2.2.2.games.foldr (fun g n => min g.oppLimit n)
            (levelBudget p.2.2.2.2.2.arena.tables 0) <;> simp [hle]

/-- The reset branch of a stage is primitive recursive. -/
theorem resetCoreL_primrec : Primrec resetCoreL := by
  have hs := ConStateL.stage_primrec
  have hi := Primrec.fst.comp (Primrec.unpair.comp hs)
  have hr := caseOneL_primrec.comp (Primrec.id.pair (hi.pair (Primrec.succ.comp hs)))
  exact ((Primrec.fst.comp hr).pair
    (ConStateL.ours_primrec.pair ((Primrec.snd.comp hr).pair (Primrec.const true)))).of_eq
      fun _ => rfl

/-- The nonreset branch of a stage is computable. -/
theorem continueCoreL_computable (hI : I.Valid) : Computable (continueCoreL I) := by
  have hs := ConStateL.stage_primrec.to_comp
  have hi := Computable.fst.comp (Computable.unpair.comp hs)
  have ht := Computable.succ.comp hs
  have hr : Computable fun st : ConStateL => reqL st (Nat.unpair st.stage).1 :=
    (reqL_primrec.to_comp.comp (Computable.id.pair hi)).of_eq fun _ => rfl
  have ho := ConStateL.ours_primrec.to_comp
  have hn := ConStateL.nextC_primrec.to_comp
  have htwo : Computable fun p : ConStateL × ℕ =>
      caseTwoL I p.1 (Nat.unpair p.1.stage).1 (p.1.stage + 1) p.2
        (reqL p.1 (Nat.unpair p.1.stage).1) :=
    ((caseTwoL_computable hI).comp
      (Computable.fst.pair ((hi.comp Computable.fst).pair
        ((ht.comp Computable.fst).pair (Computable.snd.pair (hr.comp Computable.fst)))))).of_eq
      fun _ => rfl
  have hthree : Computable fun p : (ConStateL × ℕ) × PlayL =>
      caseThreeL I p.1.1 (Nat.unpair p.1.1.stage).1 (p.1.1.stage + 1) p.1.2
        (reqL p.1.1 (Nat.unpair p.1.1.stage).1) p.2 :=
    ((caseThreeL_computable hI).comp
      ((Computable.fst.comp Computable.fst).pair
        ((hi.comp (Computable.fst.comp Computable.fst)).pair
          ((ht.comp (Computable.fst.comp Computable.fst)).pair
            ((Computable.snd.comp Computable.fst).pair
              ((hr.comp (Computable.fst.comp Computable.fst)).pair Computable.snd)))))).of_eq
      fun _ => rfl
  have hnone := hr.pair (ho.pair (hn.pair (Computable.const false)))
  have htwo' := (Computable.fst.comp htwo).pair
    ((ho.comp Computable.fst).pair ((hn.comp Computable.fst).pair (Computable.snd.comp htwo)))
  have hthree' := (Computable.fst.comp hthree).pair
    ((Computable.fst.comp (Computable.snd.comp hthree)).pair
      ((hn.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.snd.comp (Computable.snd.comp hthree))))
  have hplay := Computable.option_casesOn
    (ReqStateL.play_primrec.to_comp.comp (hr.comp Computable.fst)) htwo' hthree'.to₂
  exact (Computable.option_casesOn (ReqStateL.c_primrec.to_comp.comp hr)
    hnone hplay.to₂).of_eq fun st => by
      dsimp only [continueCoreL]
      cases (reqL st (Nat.unpair st.stage).1).c <;>
        cases (reqL st (Nat.unpair st.stage).1).play <;> rfl

/-- The stage reset predicate is computable in the state alone. -/
theorem resetTestL_computable (hI : I.Valid) : Computable fun st : ConStateL =>
    mustResetL I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2 (st.stage + 1) := by
  have hs := ConStateL.stage_primrec.to_comp
  have hu := Computable.unpair.comp hs
  exact ((mustResetL_computable hI).comp
    (Computable.id.pair ((Computable.fst.comp hu).pair
      ((Computable.snd.comp hu).pair (Computable.succ.comp hs))))).of_eq fun _ => rfl

/-- Assemble the reset test and its two computable branches to compute a stage core. -/
theorem stepCoreL_computable (hI : I.Valid) : Computable (stepCoreL I) := by
  exact (Computable.cond (resetTestL_computable hI) resetCoreL_primrec.to_comp
    (continueCoreL_computable hI)).of_eq fun st => by
      unfold stepCoreL
      cases mustResetL I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2
        (st.stage + 1) <;> rfl

/-- Timestamping and padding a computed core result is primitive recursive. -/
theorem finishStepL_primrec :
    Primrec fun p : ConStateL × (ReqStateL × (Fin 3 → List Str) × ℕ × Bool) × Bool =>
      finishStepL p.1 p.2.1 p.2.2 := by
  have ht : Primrec fun p : ConStateL × (ReqStateL × (Fin 3 → List Str) × ℕ × Bool) × Bool =>
      p.1.stage + 1 :=
    Primrec.succ.comp (ConStateL.stage_primrec.comp Primrec.fst)
  have hrs : Primrec fun p : ConStateL × (ReqStateL × (Fin 3 → List Str) × ℕ × Bool) × Bool =>
      p.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hcond : Primrec fun p : ConStateL × (ReqStateL × (Fin 3 → List Str) × ℕ × Bool) × Bool =>
      p.2.1.2.2.2 || p.2.2 :=
    Primrec.or.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  have hacted : Primrec fun p : ConStateL × (ReqStateL × (Fin 3 → List Str) × ℕ × Bool) × Bool =>
      if p.2.1.2.2.2 || p.2.2 then p.1.stage + 1 else p.2.1.1.lastActed := by
    exact (Primrec.cond hcond ht (ReqStateL.lastActed_primrec.comp hrs)).of_eq fun p => by
      cases p.2.1.2.2.2 || p.2.2 <;> rfl
  have hnewreq : Primrec fun p : ConStateL × (ReqStateL × (Fin 3 → List Str) × ℕ × Bool) × Bool =>
      { p.2.1.1 with lastVisit := p.1.stage + 1,
                     lastActed :=
                       if p.2.1.2.2.2 || p.2.2 then p.1.stage + 1 else p.2.1.1.lastActed } :=
    ReqStateL.mk_primrec.comp
      ((ReqStateL.c_primrec.comp hrs).pair
        ((ReqStateL.tables_primrec.comp hrs).pair
          ((ReqStateL.baseline_primrec.comp hrs).pair
            ((ReqStateL.play_primrec.comp hrs).pair
              (ht.pair hacted)))))
  have hreq : Primrec fun p : ConStateL × (ReqStateL × (Fin 3 → List Str) × ℕ × Bool) × Bool =>
      setReq p.1.req (Nat.unpair p.1.stage).1
        { p.2.1.1 with lastVisit := p.1.stage + 1,
                       lastActed :=
                         if p.2.1.2.2.2 || p.2.2 then p.1.stage + 1 else p.2.1.1.lastActed } :=
    setReq_primrec.comp
      ((ConStateL.req_primrec.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.unpair.comp (ConStateL.stage_primrec.comp Primrec.fst))).pair
          hnewreq))
  exact (ConStateL.mk_primrec.comp
    (ht.pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))).pair
        ((Primrec.fst.comp
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))).pair
          hreq)))).of_eq fun p => by
    rfl

/-- A full observable stage combines its core result and pending-hit test. -/
theorem stepL_computable (hI : I.Valid) : Computable (stepL I) := by
  have hs := ConStateL.stage_primrec.to_comp
  have hi := Computable.fst.comp (Computable.unpair.comp hs)
  have hr := reqL_primrec.to_comp.comp (Computable.id.pair hi)
  have hh := (pendingHitL_computable hI).comp (hr.pair (Computable.succ.comp hs))
  exact (finishStepL_primrec.to_comp.comp
    (Computable.id.pair ((stepCoreL_computable hI).pair hh))).of_eq fun _ => rfl

/-- Iterating the computable twin step computes every stage. -/
theorem stateAtL_computable (hI : I.Valid) : Computable (stateAtL I) := by
  have hh : Computable₂ fun (_ : ℕ) (q : ℕ × ConStateL) => stepL I q.2 :=
    ((stepL_computable hI).comp (Computable.snd.comp Computable.snd)).to₂
  exact (Computable.nat_rec Computable.id (Computable.const ({} : ConStateL)) hh).of_eq
    fun _ => rfl

/-- Membership in a twin board is computable after computing its stage. -/
theorem oursBL_computable (hI : I.Valid) (j : Fin 3) :
    Computable fun p : ℕ × Str => oursBL I j p.1 p.2 := by
  have hs : Computable fun p : ℕ × Str => (stateAtL I p.1).ours j :=
    Computable.fin_app.comp
      (ConStateL.ours_primrec.to_comp.comp ((stateAtL_computable hI).comp Computable.fst))
      (Computable.const j)
  exact ((list_mem_primrec (β := Str)).to_comp.comp
    (Computable.snd.pair hs)).of_eq fun p => by
      apply Bool.eq_iff_iff.mpr
      simp [oursBL]

/-- Reading an agreed bit from a supplied state is primitive recursive. -/
theorem readAgreedL_primrec : Primrec fun p : ConStateL × ℕ × ℕ =>
    (reqL p.1 p.2.1).baseline.bind fun bl => bl.σ[p.2.2]? := by
  have hb : Primrec fun p : ConStateL × ℕ × ℕ => (reqL p.1 p.2.1).baseline :=
    ReqStateL.baseline_primrec.comp
      (reqL_primrec.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
  exact Primrec.option_bind hb
    (Primrec.list_getElem?.comp (Baseline.σ_primrec.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂

/-- Baseline lookup and optional bit lookup are computable after computing the stage. -/
theorem agreedBitL_computable (hI : I.Valid) :
    Computable fun p : ℕ × ℕ × ℕ => agreedBitL I p.1 p.2.1 p.2.2 := by
  have hs : Computable fun p : ℕ × ℕ × ℕ => stateAtL I p.2.1 :=
    (stateAtL_computable hI).comp (Computable.fst.comp Computable.snd)
  exact (readAgreedL_primrec.to_comp.comp
    (hs.pair (Computable.fst.pair (Computable.snd.comp Computable.snd)))).of_eq
      fun _ => rfl

end StateTwin

/-- The construction's enumeration is computable, by reading the tracked list state. -/
theorem oursB_computable' {I : Input} (hI : I.Valid) (j : Fin 3) :
    Computable fun p : ℕ × Str => oursB I j p.1 p.2 := by
  exact (StateTwin.oursBL_computable hI j).of_eq fun p => StateTwin.oursBL_eq I j p.1 p.2

/-- The construction's agreement is computable, by reading the tracked list state. -/
theorem agreedBit_computable' {I : Input} (hI : I.Valid) :
    Computable fun p : ℕ × ℕ × ℕ => agreedBit I p.1 p.2.1 p.2.2 := by
  exact (StateTwin.agreedBitL_computable hI).of_eq fun p =>
    StateTwin.agreedBitL_eq I p.1 p.2.1 p.2.2

end Kolmogorov.RandomStrings.TTMeet
