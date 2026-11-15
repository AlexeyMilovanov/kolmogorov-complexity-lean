/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.WinningSets

/-!
# The stage construction (§4.2, §4.3 of the paper, with the repair of Case 2)

The inputs are the two stage approximations (`Input`): the strings compressed by the opponent by
stage `s`, and `X_s`.  The output is, for each board `j : Fin 3`, the growing set
`(stateAt I s).ours j` of strings we have compressed.  Every definition below is an ordinary
computable Lean definition (none is marked `noncomputable`, and `Classical.choice` is not used to
make a decision): all the searches are over explicit finite lists.  The final oracles are defined
only in `Requirements.lean`, and no stage transition reads them.

## Correspondence with the paper

| Lean | paper |
| --- | --- |
| `step` | stage `s + 1`, `s = ⟨i, e⟩`; the opponent's moves are visible at `t = s + 1` |
| `mustReset`, `caseOne` | Case 1, new `ε_i = 2 ^ (-c)` |
| `caseTwo` | Case 2, examining the stack and comparing with `X_s` |
| `caseThree` | Case 3a (play), Case 3b (knight and bishop), Case 3c (stop) |
| `ReqState.lastActed` | Remark 4.2 |
| `topOutcome`, `firstStackSplit` | §4.1.1, §4.1.3: splits, intersections, generator, stack |

## Deviations from the printed construction

They are explained in `docs/random_strings_tt_meet_2014.md`, sections 3 and 4.

1. **Baseline (repair of Case 2).**  The agreed value `σ` is remembered with a *base stage per
   board* (`Baseline`).  At each visit, if the current symmetric game on some board has `{σ}ᶜ`
   winning, we play it against `G(ε - λ, ε)` for `{σ}` on another board, where `λ` is the opponent's
   spending since the base stage of that board.  This extends the knight and bishop move of Case 3b
   to all stages.  Without it the agreed value can change on all three boards at once with no game
   in progress (`ParityExample.lean`), and the printed proof of Lemma 4.3 does not go through.
2. **One extension per visit, bits never reset.**  The number of examined bits is kept
   (`ReqState.tables`) and grows by at most one per visit.  By `forces_lift_iff`, re-examining
   shorter games brings nothing new.  The paper remarks that these steps are repeated unnecessarily.
3. **Hits (no double counting).**  An opponent move on the board of `R_m` counts as an action of
   `R_m` as soon as it happens, also for requirements visited before `R_m`'s next stage
   (`pendingHit`).  This makes the no-double-counting claim in the proof of Lemma 4.4 hold under the
   one-requirement-per-stage schedule.
4. **Constants.**  The exact realisation available in the library is `min (K_V + 5, F + 3)`, so the
   opponent's budget is `1/32` instead of `1/8` and ours is `3/32` instead of `7/8`.  Accordingly
   `c ≥ i + 7` instead of `c ≥ i + 4`, which scales the paper's `1/4 + 1/4` to `1/32 + 1/16`.  The
   cost of a move is unchanged.
5. **Stages.**  After Case 3c we go to the next visit instead of proceeding to Case 2 at the same
   stage.  A table is one index instead of a pair `⟨i_f, i_g⟩`.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

/-- The inputs of the construction, as stage approximations. -/
structure Input where
  /-- `opp s τ`: by stage `s` the opponent has compressed `τ`, that is `K_V[s](τ) + 5 < |τ|`. -/
  opp : ℕ → Str → Bool
  /-- The approximation `X_s` of the characteristic function of `X`. -/
  X : ℕ → Str → Bool

/-- A game in progress on one board. -/
structure BoardGame where
  /-- The board. -/
  board : Fin 3
  /-- The target set of outcome vectors. -/
  target : Finset (List Bool)
  /-- The opponent's budget in this game, in units. -/
  oppLimit : ℕ
  /-- Our budget in this game, in units. -/
  ourLimit : ℕ
  /-- Our spending in this game so far, in units. -/
  spent : ℕ

/-- The type of the games being played. -/
inductive PlayKind where
  /-- `G(ε, ε)` on two boards (a split) or on three (a failed intersection). -/
  | balanced
  /-- Consecutive levels of the stack on two boards, for `{σ}ᶜ` and `{σ}`; the third board waits. -/
  | stacked (σ : List Bool) (bishop : Fin 3)
  /-- `G(ε, ε)` on one board and `G(ε - λ, ε)` on another, for `{σ}ᶜ` and `{σ}`. -/
  | unbalanced

/-- The games of one requirement in progress. -/
structure Play where
  /-- The board and the unit. -/
  arena : Arena
  /-- The stage at which the games started; the opponent's spending is counted from here. -/
  start : ℕ
  /-- The type of the games. -/
  kind : PlayKind
  /-- One game per participating board. -/
  games : List BoardGame

/-- The value agreed on by the last examination, with the stage at which each board was last known
to have `{σ}` winning in the symmetric game. -/
structure Baseline where
  /-- The agreed outcome vector. -/
  σ : List Bool
  /-- The base stage of each board. -/
  base : Fin 3 → ℕ

/-- A closed accounting window of a requirement.  This is ghost data for Lemma 4.4: no decision of
the construction reads it. -/
structure Epoch where
  /-- The requirement. -/
  req : ℕ
  /-- The starting measure was `2 ^ (-c)`. -/
  c : ℕ
  /-- First stage of the window. -/
  start : ℕ
  /-- Last stage of the window: the last visit that was not a reset. -/
  stop : ℕ
  /-- The board of the requirement during the window. -/
  board : Finset Str
  /-- Our spending per board in the window, in true measure. -/
  spent : Fin 3 → ℚ
  /-- The window ended in a reset, so up to `2 ^ (-c)` may be left uncharged. -/
  final : Bool

/-- The state of one requirement. -/
structure ReqState where
  /-- The starting measure `ε_i = 2 ^ (-c)`, if currently defined. -/
  c : Option ℕ := none
  /-- The truth tables examined so far, for bits `0, 1, …`.  They are never forgotten. -/
  tables : List TTable := []
  /-- The agreed value, if any. -/
  baseline : Option Baseline := none
  /-- The games in progress, if any. -/
  play : Option Play := none
  /-- The stage of the last visit. -/
  lastVisit : ℕ := 0
  /-- The stage of the last action in the sense of Remark 4.2. -/
  lastActed : ℕ := 0
  /-- Ghost: the first stage of the current accounting window. -/
  epochStart : ℕ := 0
  /-- Ghost: our spending per board in the current window, in true measure. -/
  epochSpent : Fin 3 → ℚ := fun _ => 0
  /-- Ghost: the closed accounting windows. -/
  closed : List Epoch := []

/-- The state of the construction. -/
structure ConState where
  /-- The number of completed stages. -/
  stage : ℕ := 0
  /-- The strings compressed by us, per board: the requests `⟨|τ| - 1, τ⟩` of §4.3. -/
  ours : Fin 3 → Finset Str := fun _ => ∅
  /-- The next value of `c` must be at least this: `2 ^ (-c) < ε_m / 2` for all earlier values. -/
  nextC : ℕ := 0
  /-- The states of the requirements. -/
  req : ℕ → ReqState := fun _ => {}

/-! ### Positions -/

/-- `τ` looks random on board `j` at stage `t`.  This is the stage approximation of the oracle; the
final oracle is `finalR` in `Requirements.lean`. -/
def ConState.alive (I : Input) (st : ConState) (t : ℕ) (j : Fin 3) (τ : Str) : Bool :=
  !(I.opp t τ) && !(decide (τ ∈ st.ours j))

/-- The position on board `j` at stage `t`, as a list. -/
def ConState.positionList (I : Input) (st : ConState) (ar : Arena) (t : ℕ) (j : Fin 3) : List Str :=
  ar.boardList.filter (st.alive I t j)

/-- The position on board `j` at stage `t`. -/
def ConState.position (I : Input) (st : ConState) (ar : Arena) (t : ℕ) (j : Fin 3) : Finset Str :=
  (st.positionList I ar t j).toFinset

/-- The opponent's spending on the board between the stages `t₀` and `t`, in units.  It counts every
string once, whatever its status on the individual boards, so it is common to the three boards and
bounds the actual cost on each of them. -/
def oppSpend (I : Input) (ar : Arena) (t₀ t : ℕ) : ℕ :=
  cost ar.w (ar.board.filter fun τ => I.opp t τ && !(I.opp t₀ τ))

/-- The vector `X_t ↾ n`. -/
def xPrefix (I : Input) (t n : ℕ) : List Bool :=
  (List.range n).map fun k => I.X t (strOf k)

/-- Winning sets are decidable. -/
instance (ar : Arena) (S : Finset (List Bool)) (A : Finset Str) (a b : ℕ) :
    Decidable (ar.Forces S A a b) :=
  inferInstanceAs (Decidable (Wins ar.w (fun B => ar.value B ∈ S) A a b))

/-! ### Examining the top of the stack -/

/-- The three boards. -/
def allBoards : List (Fin 3) := [0, 1, 2]

/-- All subsets of the outcome vectors of length `n`, as a list. -/
def subsetsOf (n : ℕ) : List (Finset (List Bool)) := (allVec n).sublists.map List.toFinset

/-- The verdict on the collections of winning sets of the symmetric game. -/
inductive TopOutcome where
  /-- `S` is winning on board `j` and its complement on board `k` (§4.1.3). -/
  | split (j k : Fin 3) (S : Finset (List Bool))
  /-- `S` and `T` are winning on all boards, `S ∩ T` is not (§4.1.3). -/
  | meet (S T : Finset (List Bool))
  /-- The collection is the principal ultrafilter of `σ`. -/
  | principal (σ : List Bool)
  /-- Not possible, by `exists_generator`; kept to make the definition total without a proof. -/
  | stuck

/-- Examination of `G(E, E)` on the three boards, in the order of Case 2. -/
def topOutcome (ar : Arena) (A : Fin 3 → Finset Str) (E : ℕ) : TopOutcome :=
  let n := ar.tables.length
  let D := vectors n
  let F : Fin 3 → Finset (List Bool) → Bool := fun j S => decide (ar.Forces S (A j) E E)
  let splits := (allBoards.product allBoards).product (subsetsOf n)
  match splits.find? (fun q => decide (q.1.1 ≠ q.1.2) && F q.1.1 q.2 && F q.1.2 (D \ q.2)) with
  | some q => .split q.1.1 q.1.2 q.2
  | none =>
    let pairs := (subsetsOf n).product (subsetsOf n)
    match pairs.find? (fun q => F 0 q.1 && F 0 q.2 && !(F 0 (q.1 ∩ q.2))) with
    | some q => .meet q.1 q.2
    | none =>
      match (allVec n).find? (fun σ => F 0 {σ}) with
      | some σ => .principal σ
      | none => .stuck

/-- The first board other than `j`. -/
def otherBoard (j : Fin 3) : Fin 3 := if j = 0 then 1 else 0

/-- The board other than `j` and `k`. -/
def thirdBoard (j k : Fin 3) : Fin 3 :=
  (allBoards.find? fun l => decide (l ≠ j) && decide (l ≠ k)).getD 0

/-- The first level `ℓ ≥ 1` of the stack and a board on which `{σ}ᶜ` is winning, in the order of
levels (§4.1.1: "different from all previous games"). -/
def firstStackSplit (ar : Arena) (A : Fin 3 → Finset Str) (σ : List Bool) : Option (ℕ × Fin 3) :=
  let D := vectors ar.tables.length
  let p : ℕ → Fin 3 → Bool := fun ℓ j =>
    decide (ar.Forces (D \ {σ}) (A j) (levelBudget ar.tables ℓ) (levelBudget ar.tables ℓ))
  match (List.range (maxLen ar.tables)).find? (fun r => allBoards.any (p (r + 1))) with
  | none => none
  | some r => (allBoards.find? (p (r + 1))).map fun j => (r + 1, j)

/-! ### Requirements -/

/-- The set of strings on the examined tables, independently of the unit. -/
def boardOf (tables : List TTable) : Finset Str := (arenaOf 0 tables).board

/-- The opponent has hit the board of the requirement since its last visit. -/
def pendingHit (I : Input) (rs : ReqState) (t : ℕ) : Bool :=
  decide ((boardOf rs.tables).filter fun τ => I.opp t τ && !(I.opp rs.lastVisit τ)).Nonempty

/-- All strings on the tables defined by stage `t` for requirements `m < i`. -/
def definedStrings (i t : ℕ) : List Str :=
  (List.range i).flatMap fun m => (List.range t).flatMap fun k => ((tableAt m k t).getD []).queries

/-- The new starting measure: the greatest `2 ^ (-c)` with `c ≥ i + 7`, below half of all earlier
values, and with no string on a currently defined higher-priority table longer than `c`. -/
def newC (st : ConState) (i t : ℕ) : ℕ :=
  max (i + 7) (max st.nextC ((definedStrings i t).foldr (fun z n => max z.length n) 0))

/-- Close the current accounting window. -/
def ReqState.closeEpoch (rs : ReqState) (i c stop t : ℕ) (final : Bool) : ReqState :=
  { rs with
    closed := ⟨i, c, rs.epochStart, stop, boardOf rs.tables, rs.epochSpent, final⟩ :: rs.closed
    epochStart := t
    epochSpent := fun _ => 0 }

/-- Case 1 applies at the stage `s + 1 = t`, with `s = ⟨i, e⟩`. -/
def mustReset (I : Input) (st : ConState) (i e t : ℕ) : Bool :=
  decide (e = 0) || (st.req i).c.isNone ||
    (List.range i).any fun m =>
      decide ((st.req i).lastVisit < (st.req m).lastActed) || pendingHit I (st.req m) t

/-- **Case 1.**  A new starting measure; the games and the agreement are forgotten. -/
def caseOne (st : ConState) (i t : ℕ) : ReqState × ℕ :=
  let rs := st.req i
  let c' := newC st i t
  let rs' := match rs.c with
    | some c => rs.closeEpoch i c rs.lastVisit t true
    | none => { rs with epochStart := t }
  ({ rs' with c := some c', baseline := none, play := none }, c' + 2)

/-- A symmetric game. -/
def symGame (j : Fin 3) (S : Finset (List Bool)) (E : ℕ) : BoardGame := ⟨j, S, E, E, 0⟩

/-- Start the balanced games for a verdict of the examination. -/
def balancedPlay (ar : Arena) (t : ℕ) (E : ℕ) : TopOutcome → Option Play
  | .split j k S =>
      some ⟨ar, t, .balanced, [symGame j S E, symGame k (vectors ar.tables.length \ S) E]⟩
  | .meet S T => some ⟨ar, t, .balanced, [symGame 0 S E, symGame 1 T E,
      symGame 2 (vectors ar.tables.length \ (S ∩ T)) E]⟩
  | _ => none

/-- The result of the first part of Case 2: either the visit is over (`Sum.inl`), or the requirement
has the agreed value `σ` with its window closed at `t` (`Sum.inr`). -/
def examineTop (I : Input) (st : ConState) (i t c : ℕ) (rs : ReqState) :
    (ReqState × Bool) ⊕ (ReqState × List Bool) :=
  let ar := arenaOf c rs.tables
  let E := levelBudget rs.tables 0
  let D := vectors rs.tables.length
  let A := st.position I ar t
  match rs.baseline with
  | some bl =>
    if allBoards.any (fun j => decide (E < oppSpend I ar (bl.base j) t)) then
      -- The opponent has spent more than `ε` since a base stage: nothing to defend any more.
      .inl (({ rs with baseline := none }).closeEpoch i c t t false, false)
    else
      match allBoards.find? (fun j => decide (ar.Forces (D \ {bl.σ}) (A j) E E)) with
      | some j =>
        -- The repair of Case 2: the current game on `j` against the old value on another board.
        let k := otherBoard j
        .inl ({ rs with
          play := some ⟨ar, t, .unbalanced,
            [symGame j (D \ {bl.σ}) E, ⟨k, {bl.σ}, E - oppSpend I ar (bl.base k) t, E, 0⟩]⟩ }, true)
      | none =>
        .inr (({ rs with baseline := some ⟨bl.σ, fun _ => t⟩ }).closeEpoch i c t t false, bl.σ)
  | none =>
    match topOutcome ar A E with
    | .principal σ =>
      .inr (({ rs with baseline := some ⟨σ, fun _ => t⟩ }).closeEpoch i c t t false, σ)
    | v =>
      match balancedPlay ar t E v with
      | some pl => .inl ({ rs with play := some pl }, true)
      | none => .inl (rs, false)

/-- **Case 2.**  Examine the stack on the current tables; if it agrees with `X_t`, try one more bit.
No move is made, so the opponent moves first in any game begun here. -/
def caseTwo (I : Input) (st : ConState) (i t c : ℕ) (rs : ReqState) : ReqState × Bool :=
  match examineTop I st i t c rs with
  | .inl r => r
  | .inr (rs₁, σ) =>
    let n := rs.tables.length
    let ar := arenaOf c rs.tables
    let D := vectors n
    let A := st.position I ar t
    match firstStackSplit ar A σ with
    | some (ℓ, j) =>
      let k := otherBoard j
      let Eℓ := levelBudget rs.tables ℓ
      let Eℓ' := levelBudget rs.tables (ℓ - 1)
      ({ rs₁ with
        play := some ⟨ar, t, .stacked σ (thirdBoard j k),
          [symGame j (D \ {σ}) Eℓ, symGame k {σ} Eℓ']⟩ }, true)
    | none =>
      if σ ≠ xPrefix I t n then (rs₁, false) else
      match tableAt i n t with
      | none => (rs₁, false)
      | some tbl =>
        let tables' := rs.tables ++ [tbl]
        let ar' := arenaOf c tables'
        let E' := levelBudget tables' 0
        match topOutcome ar' (st.position I ar' t) E' with
        | .principal σ' =>
          ({ rs₁ with tables := tables', baseline := some ⟨σ', fun _ => t⟩ }, true)
        | v =>
          match balancedPlay ar' t E' v with
          | some pl => ({ rs₁ with tables := tables', baseline := none, play := some pl }, true)
          | none => (rs₁, false)

/-- Our answer in a game at the current position `La` (Case 3a): a first move keeping the position
winning.  If the opponent is silent and the outcome is on target we may pass.  The default is never
reached while the game invariant holds (`respond_spec`). -/
def respond (ar : Arena) (g : BoardGame) (La : List Str) (a b : ℕ) : Finset Str :=
  let A := La.toFinset
  let ok : Finset Str → Bool := fun p =>
    decide (cost ar.w p ≤ b) &&
      (if p = ∅ then decide (ar.value A ∈ g.target) && decide (ar.Forces g.target A a b)
       else decide (ar.Forces g.target (A \ p) a (b - cost ar.w p)))
  ((La.sublists.map List.toFinset).find? ok).getD ∅

/-- The true measure of a set of strings. -/
def trueCost (p : Finset Str) : ℚ := ∑ τ ∈ p, realCost τ

/-- **Case 3.**  The opponent's spending is compared with the limits. -/
def caseThree (I : Input) (st : ConState) (i t c : ℕ) (rs : ReqState) (pl : Play) :
    ReqState × (Fin 3 → Finset Str) × Bool :=
  let ar := pl.arena
  let E := levelBudget ar.tables 0
  let lam := oppSpend I ar pl.start t
  let limit := pl.games.foldr (fun g n => min g.oppLimit n) E
  let D := vectors ar.tables.length
  let stop : ReqState × (Fin 3 → Finset Str) × Bool :=
    -- Case 3c.
    (({ rs with play := none, baseline := none }).closeEpoch i c t t false, st.ours, true)
  if lam ≤ limit then
    -- Case 3a.
    let moves := pl.games.map fun g =>
      (g, respond ar g (st.positionList I ar t g.board) (g.oppLimit - lam) (g.ourLimit - g.spent))
    let games' := moves.map fun q => { q.1 with spent := q.1.spent + cost ar.w q.2 }
    let ours' : Fin 3 → Finset Str := fun j =>
      moves.foldr (fun q acc => if q.1.board = j then q.2 ∪ acc else acc) (st.ours j)
    let spent' : Fin 3 → ℚ := fun j =>
      moves.foldr (fun q acc => if q.1.board = j then trueCost q.2 + acc else acc) (rs.epochSpent j)
    ({ rs with play := some { pl with games := games' }, epochSpent := spent' }, ours',
      moves.any fun q => decide q.2.Nonempty)
  else
    match pl.kind with
    | .stacked σ bishop =>
      if lam ≤ E then
        -- Case 3b: knight and bishop.
        let knights := pl.games.map BoardGame.board
        let A := st.position I ar t
        match knights.find? (fun j => decide (ar.Forces (D \ {σ}) (A j) E E)) with
        | some j =>
          ({ rs with
            play := some ⟨ar, t, .unbalanced,
              [symGame j (D \ {σ}) E, ⟨bishop, {σ}, E - lam, E, 0⟩]⟩ }, st.ours, true)
        | none =>
          ({ rs with
            play := none
            baseline := rs.baseline.map fun bl =>
              { bl with base := fun j => if j = bishop then bl.base j else t } }, st.ours, true)
      else stop
    | _ => stop

/-- The case distinction of a stage: the new state of the requirement, the strings compressed, the
bound for the next `c`, and whether the requirement acted. -/
def stepCore (I : Input) (st : ConState) : ReqState × (Fin 3 → Finset Str) × ℕ × Bool :=
  let t := st.stage + 1
  let i := (Nat.unpair st.stage).1
  let e := (Nat.unpair st.stage).2
  let rs := st.req i
  if mustReset I st i e t then
    let r := caseOne st i t
    (r.1, st.ours, r.2, true)
  else
    match rs.c with
    | none => (rs, st.ours, st.nextC, false)
    | some c =>
      match rs.play with
      | none =>
        let r := caseTwo I st i t c rs
        (r.1, st.ours, st.nextC, r.2)
      | some pl =>
        let r := caseThree I st i t c rs pl
        (r.1, r.2.1, st.nextC, r.2.2)

/-- **Stage `s + 1`, `s = ⟨i, e⟩`.**  The opponent's moves up to `t = s + 1` are visible. -/
def step (I : Input) (st : ConState) : ConState :=
  let t := st.stage + 1
  let i := (Nat.unpair st.stage).1
  let r := stepCore I st
  { stage := t
    ours := r.2.1
    nextC := r.2.2.1
    req := Function.update st.req i
      { r.1 with
        lastVisit := t
        lastActed := if r.2.2.2 || pendingHit I (st.req i) t then t else r.1.lastActed } }

/-- The state after `s` stages. -/
def stateAt (I : Input) : ℕ → ConState
  | 0 => {}
  | s + 1 => step I (stateAt I s)

/-- The strings compressed by us on board `j` by stage `s`. -/
def oursAt (I : Input) (j : Fin 3) (s : ℕ) : Finset Str := (stateAt I s).ours j

/-- Membership in `oursAt`, as a Boolean: the function required to be computable. -/
def oursB (I : Input) (j : Fin 3) (s : ℕ) (τ : Str) : Bool := decide (τ ∈ oursAt I j s)

/-- The bit `k` of the value agreed on by requirement `i` after `s` stages, if any. -/
def agreedBit (I : Input) (i s k : ℕ) : Option Bool :=
  ((stateAt I s).req i).baseline.bind fun bl => bl.σ[k]?

end Kolmogorov.RandomStrings.TTMeet
