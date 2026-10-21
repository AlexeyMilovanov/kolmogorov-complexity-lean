/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Apriori
import KolmogorovMathlib.RandomStrings.Game
import KolmogorovMathlib.RandomStrings.Effective
import KolmogorovMathlib.RandomStrings.Family

/-!
# The state and the stages of the construction

The output interface `Built` and the initial values `F₀`; the abstract state of the construction
(`CState`: the enumerated parts of `ov K` and `ov F`, the games in progress, the injury counters);
the stage transition `stageStep` and the stages `stage A γ enumK s`; and the effectiveness of the
enumerations used by the stages.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-- The random strings of a complexity function `H`. -/
def RH (H : BitString → ℕ) : Set BitString := {x | x.length ≤ H x}

/-- The output of the construction. -/
structure Built (A : Set BitString) (K : AprioriComplexity) where
  /-- The constructed function `F`. -/
  F : BitString → ℕ
  /-- `F` is a prefix-free entropy function (Property 1 and Property 3). -/
  entropy : IsEntropyFun F
  /-- Property 4: no clocked machine of the family decides `A` with oracle `R_H`,
  `H = min (K + 5, F + 3)`. -/
  foils : ∀ (c : OTMCode) (e : ℕ), (∀ x, Family.Φ c e x) →
    ¬ ClockedDecidesW Family.clk c e (RH (Hmin K F)) A

/-- The initial values `F₀(x) = 2|x| + 3`. -/
def F₀ (x : BitString) : ℕ := 2 * x.length + 3

/-! ### The state of the construction

At each stage the construction keeps the current enumerated parts of `ov K` and `ov F`, the
games in progress, and the injury counters.  We record the state abstractly and specify the
stage transition by its effect; the computability of the whole process is the content of
`stages_computable`. -/

/-- The state at the beginning of a stage. -/
structure CState where
  /-- The current `F*`, a total function (initially `F₀`). -/
  Fstar : BitString → ℕ
  /-- The current `K*` (`⊤` where nothing has been enumerated yet). -/
  Kstar : BitString → ℕ∞
  /-- The game in progress for each requirement, if any: the witness `x`, the strings in play,
  the budget exponent, and the game state. -/
  game : ℕ → Option (BitString × Finset BitString × ℕ × GState)
  /-- The injury counters `i_e`. -/
  inj : ℕ → ℕ

/-- The current `H* = min (K* + 5, F* + 3)`. -/
noncomputable def CState.Hstar (σ : CState) (x : BitString) : ℕ∞ :=
  min (σ.Kstar x + 5) ((σ.Fstar x : ℕ∞) + 3)

/-- The initial state. -/
def CState.init : CState := ⟨F₀, fun _ => ⊤, fun _ => none, fun _ => 0⟩

omit [Family] in
/-- A nonempty predicate on a countable type is the range of a total function `ℕ → α`
(classically; for a c.e. predicate the enumeration can be taken computable, but this is not
needed here). -/
theorem exists_surj_of_rePred {α : Type} [Primcodable α] {P : α → Prop}
    (hne : ∃ a, P a) : ∃ f : ℕ → α, ∀ a, P a ↔ ∃ n, f n = a := by
  obtain ⟨f, hf⟩ := (Set.to_countable {a | P a}).exists_eq_range hne
  refine ⟨f, fun a => ?_⟩
  have : a ∈ {a | P a} ↔ a ∈ Set.range f := by rw [hf]
  simpa using this

omit [Family] in
/-- A fixed enumeration of `ov K`: `enumK s` is the `s`-th enumerated pair (the overgraph is
c.e. and nonempty, since `(x, K.H x)` belongs to it). -/
theorem exists_enumK (K : AprioriComplexity) :
    ∃ enumK : ℕ → BitString × ℕ, (∀ s, K.H (enumK s).1 ≤ (enumK s).2) ∧
      ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 → ∃ s, enumK s = p := by
  obtain ⟨f, hf⟩ := exists_surj_of_rePred (P := fun p : BitString × ℕ => K.H p.1 ≤ p.2)
    ⟨([], K.H []), le_rfl⟩
  exact ⟨f, fun s => (hf (f s)).2 ⟨s, rfl⟩, fun p hp => (hf p).1 hp⟩

/-- The strings in play for requirement `e` on witness `x` at state `σ`: the strings of the
guarded game (`qsetF`: the possible queries of the clocked machine if it belongs to the family on
`x`, otherwise none), minus the strings in play for higher-priority requirements. -/
noncomputable def playSet (γ : ℕ → OTMCode × ℕ) (σ : CState) (e : ℕ) (x : BitString) :
    Finset BitString :=
  qsetF (γ e).1 (γ e).2 x \
    (Finset.range e).biUnion fun e' => (σ.game e').elim ∅ fun g => g.2.1

/-- The values `h` used by a game: `H*` as a natural number (`H*` is finite on strings whose
`F*` is finite, which is always the case). -/
noncomputable def CState.hval (σ : CState) (x : BitString) : ℕ := (σ.Hstar x).toNat

/-- The game that requirement `e` would start on witness `x` at state `σ` (the guarded game
`gameOfF`: off the family its outcome is constant, `x ∉ A`). -/
noncomputable def newGame (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ : CState) (e : ℕ)
    (x : BitString) : GameData :=
  gameOfF A (γ e).1 (γ e).2 x σ.hval ((2 : ℝ)⁻¹ ^ (e + σ.inj e + 6)) (playSet γ σ e x)

/-- A witness for `e` at state `σ`: a string whose game value disagrees with `A`. -/
def IsWitness (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ : CState) (e : ℕ)
    (x : BitString) : Prop :=
  (val (newGame A γ σ e x) = true) ↔ x ∉ A

omit [Family] in
/-- With finitely many changes, `hval` is a hardwired modification of `2|z| + 6`. -/
theorem exists_table_hval (σ : CState) (hfin : {x | σ.Fstar x ≠ F₀ x}.Finite)
    (hfinK : {x | σ.Kstar x ≠ ⊤}.Finite) : ∃ T : Table, ∀ z, σ.hval z = T.fn z := by
  classical
  refine ⟨⟨hfin.toFinset ∪ hfinK.toFinset, σ.hval⟩, fun z => ?_⟩
  unfold Table.fn
  split_ifs with hz
  · rfl
  · simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or,
      not_not] at hz
    obtain ⟨h1, h2⟩ := hz
    change (min (σ.Kstar z + 5) ((σ.Fstar z : ℕ∞) + 3)).toNat = 2 * z.length + 6
    rw [h1, h2, top_add, min_eq_right le_top]
    change (((2 * z.length + 3 : ℕ) : ℕ∞) + 3).toNat = 2 * z.length + 6
    rw [show ((2 * z.length + 3 : ℕ) : ℕ∞) + 3 = ((2 * z.length + 6 : ℕ) : ℕ∞) by
      push_cast; ring]
    exact ENat.toNat_natCast _

omit [Family] in
/-- The strings of code at most `y` form a finite set. -/
theorem exists_finset_encode_le (y : ℕ) :
    ∃ Z : Finset BitString, ∀ x : BitString, x ∉ Z → y < Encodable.encode x := by
  have hfin : {x : BitString | Encodable.encode x ≤ y}.Finite :=
    Set.Finite.preimage Encodable.encode_injective.injOn (Set.finite_Iic y)
  refine ⟨hfin.toFinset, fun x hx => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx
  omega

/-- Claim 4 as a hypothesis: at every state with finitely many changes, every requirement has
witnesses of arbitrarily large code.  (For `A ∉ EXPSPACE` this is the content of Claim 4; in
general it is derived from `A ∉ 𝓒` in `AFG/General.lean`.) -/
def WitnessesExist (A : Set BitString) (γ : ℕ → OTMCode × ℕ) : Prop :=
  ∀ (σ : CState) (e y : ℕ), {x | σ.Fstar x ≠ F₀ x}.Finite → {x | σ.Kstar x ≠ ⊤}.Finite →
    ∃ x : BitString, y < Encodable.encode x ∧ IsWitness A γ σ e x

/-! ### Stages

`stage A γ enumK s` is the state at the beginning of stage `s`; `stageStep` performs one
stage: it updates `K*` with the `s`-th enumerated pair of `ov K`, then processes the
requirements `R_1, …, R_s` in priority order as in §3.2 (new game on a fresh witness; destroy a
game on which `K` cheated; answer a legal move of `K` by the winning strategy; injure the lower
priority requirements when acting). -/

/-- Stage `s` first updates `K*` with the `s`-th enumerated pair `(x', y')` of `ov K`:
`K*(x') := min (K*(x'), y')`. -/
noncomputable def updateK (enumK : ℕ → BitString × ℕ) (s : ℕ) (σ : CState) : CState :=
  { σ with
    Kstar := Function.update σ.Kstar (enumK s).1 (min (σ.Kstar (enumK s).1) ((enumK s).2 : ℕ∞)) }

/-- The strings of `X` that are non-random at state `σ` (`H*(z) < |z|`). -/
noncomputable def flipped (σ : CState) (X : Finset BitString) : Finset BitString :=
  X.filter fun z => σ.hval z < z.length

/-- The real increase of `∑_{z ∈ X} 2^{-H*(z)}` from the state `σ₀` (the beginning of the
current stage) to the state `σ`.  Inside a stage, before requirement `e` is processed, only `K*`
has changed on the play set of `e` (the play sets of live games are disjoint and nobody acted
earlier in the stage), so this is the real mass spent by `K` on `X_e` during the stage. -/
noncomputable def kCost (σ₀ σ : CState) (X : Finset BitString) : ℝ :=
  ∑ z ∈ X, ((2 : ℝ)⁻¹ ^ σ.hval z - (2 : ℝ)⁻¹ ^ σ₀.hval z)

/-- The game data of a game record `g = (x, X, m, st)` at state `σ`: the guarded game on `X`
with the *current* values `H*` and budget `2^{-m}`.  At the creation of the game it is `newGame`.
(Partial
decreases of `H*` by `K` on `X` are charged to `K`'s score through `kCost`, which compensates for
the use of the current values in the costs.) -/
noncomputable def curGame (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ : CState) (e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) : GameData :=
  gameOfF A (γ e).1 (γ e).2 g.1 σ.hval ((2 : ℝ)⁻¹ ^ g.2.2.1) g.2.1

/-- The score of the player to move. -/
def GState.moverScore (st : GState) : ℝ := if st.yesTurn then st.scoreY else st.scoreN

/-- Charge the player to move the (real) amount `c`. -/
def GState.charge (st : GState) (c : ℝ) : GState :=
  if st.yesTurn then { st with scoreY := st.scoreY + c } else { st with scoreN := st.scoreN + c }

/-- The move of `K` (the player to move in a stored game state): the token goes to `S'`, `K` is
charged its real cost `c`, and the turn passes to us. -/
def GState.kMove (st : GState) (S' : Finset BitString) (c : ℝ) : GState :=
  { st.charge c with S := S', yesTurn := !st.yesTurn }

/-- `K` cheats if its score plus the real cost `c` of its latest changes exceeds the budget. -/
def Cheats (ε : ℝ) (st : GState) (c : ℝ) : Prop := ε < st.moverScore + c

/-- Safety for the side `we` (`true`: YES, `false`: NO) at a state where the opponent moves. -/
def SafeFor (d : GameData) (we : Bool) (st : GState) : Prop :=
  if we then SafeYes d st else SafeNo d st

/-- Our reply at state `st` (our turn) in the game `d`: the legal move given by the list of least
code after which we are safe (`SafeFor d we`); passing (`st.S`) if there is no such move (this
does not happen along the construction, see `live_game_safe`).  (Codes of lists, not of finite
sets: the `Encodable (Finset _)` instance is not usable for computation.) -/
noncomputable def ourReply (d : GameData) (we : Bool) (st : GState) : Finset BitString := by
  classical
  exact if h : ∃ k : ℕ, LegalMove d st
      (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.S) ∧
      SafeFor d we (applyMove d st
        (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.S))
    then ((Encodable.decode (Nat.find h) : Option (List BitString)).map List.toFinset).getD st.S
    else st.S

/-- Our flips: `F*(z) := min (F*(z), |z| - 4)` for `z ∈ T`, so that `H*(z) ≤ |z| - 1`
(for `|z| ≥ 4`; shorter strings are never affordable, their flip cost is `≥ 1/8`). -/
def applyFlips (T : Finset BitString) (σ : CState) : CState :=
  { σ with Fstar := fun z => if z ∈ T then min (σ.Fstar z) (z.length - 4) else σ.Fstar z }

/-- `R_e` acts: destroy the games of all `e' > e` and increase their injury counters. -/
def injure (e : ℕ) (σ : CState) : CState :=
  { σ with game := fun e' => if e < e' then none else σ.game e',
           inj := fun e' => if e < e' then σ.inj e' + 1 else σ.inj e' }

/-- Destroy the game of `e` (its injury counter is unchanged). -/
def destroy (e : ℕ) (σ : CState) : CState :=
  { σ with game := Function.update σ.game e none }

/-- Record the game `g` for `e`. -/
def setGame (e : ℕ) (g : BitString × Finset BitString × ℕ × GState) (σ : CState) : CState :=
  { σ with game := Function.update σ.game e (some g) }

/-- The witness of least code for `e` at state `σ`, if any (under `WitnessesExist` there is
one).  (Simplification: the witness is not required to be fresh.) -/
noncomputable def chooseWitness (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ : CState) (e : ℕ) :
    Option BitString := by
  classical
  exact if h : ∃ k : ℕ, IsWitness A γ σ e ((Encodable.decode k).getD []) then
      some ((Encodable.decode (Nat.find h)).getD []) else none

/-- The state of a new game from which we make our first move: the initial state if we are YES
(`we = true`); if we are NO, the state after a pass of `K` (= YES), so that our first move is the
answer to `K` not moving (the later moves of `K` are answered as they come). -/
noncomputable def firstState (d : GameData) (we : Bool) : GState :=
  if we then GState.init else applyMove d GState.init ∅

/-- Start the game `d = newGame A γ σ e x` with budget exponent `e + i_e + 6`.  We play YES iff
`val d = true` and make our first move at once (to a position safe for us); starting a game
always counts as acting (flag `true`), so the games of lower priority are destroyed and their
later play sets avoid the new one (`live_playSets_disjoint`). -/
noncomputable def startOn (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (e : ℕ) (σ : CState)
    (x : BitString) : CState × Bool :=
  (injure e (applyFlips
    (ourReply (newGame A γ σ e x) (val (newGame A γ σ e x))
      (firstState (newGame A γ σ e x) (val (newGame A γ σ e x))))
    (setGame e (x, playSet γ σ e x, e + σ.inj e + 6,
      applyMove (newGame A γ σ e x) (firstState (newGame A γ σ e x) (val (newGame A γ σ e x)))
        (ourReply (newGame A γ σ e x) (val (newGame A γ σ e x))
          (firstState (newGame A γ σ e x) (val (newGame A γ σ e x))))) σ)), true)

/-- Case 1 (no game in progress): start a game on the chosen witness (nothing if none). -/
noncomputable def startGame (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (e : ℕ) (σ : CState) :
    CState × Bool :=
  match chooseWitness A γ σ e with
  | none => (σ, false)
  | some x => startOn A γ e σ x

/-- Case 2 (game `g = (x, X, m, st)` in progress, `K` to move in `st`).  Let `c` be the real
cost of `K`'s changes on `X` during this stage and `S' = st.S ∪ flipped σ X`.
(b) if `K` cheats (`2^{-m} < score_K + c`): destroy the game and injure `e' > e` (acting);
(a) if `S' = st.S` (no new flip): only record the charge `c` (not acting);
(c) otherwise `K` played the legal move `S'`; we answer with `ourReply` (a move to a position
safe for us),
flip the new strings by lowering `F*`, and injure `e' > e` (acting). -/
noncomputable def processGame (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) (σ : CState) : CState × Bool := by
  classical
  exact if Cheats ((2 : ℝ)⁻¹ ^ g.2.2.1) g.2.2.2 (kCost σ₀ σ g.2.1) then
      (injure e (destroy e σ), true)
    else if g.2.2.2.S ∪ flipped σ g.2.1 = g.2.2.2.S then
      (setGame e (g.1, g.2.1, g.2.2.1, g.2.2.2.charge (kCost σ₀ σ g.2.1)) σ, false)
    else
      (injure e (applyFlips
        (ourReply (curGame A γ σ e g) (!g.2.2.2.yesTurn)
            (g.2.2.2.kMove (g.2.2.2.S ∪ flipped σ g.2.1) (kCost σ₀ σ g.2.1)) \
          (g.2.2.2.S ∪ flipped σ g.2.1))
        (setGame e (g.1, g.2.1, g.2.2.1,
          applyMove (curGame A γ σ e g)
            (g.2.2.2.kMove (g.2.2.2.S ∪ flipped σ g.2.1) (kCost σ₀ σ g.2.1))
            (ourReply (curGame A γ σ e g) (!g.2.2.2.yesTurn)
              (g.2.2.2.kMove (g.2.2.2.S ∪ flipped σ g.2.1) (kCost σ₀ σ g.2.1)))) σ)), true)

/-- Process requirement `e` on the pair (state, "somebody acted in this stage").  Once a
requirement has acted, the rest of the stage is skipped (as in the paper). -/
noncomputable def processReq (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (p : CState × Bool) : CState × Bool :=
  if p.2 then p else
    match p.1.game e with
    | none => startGame A γ e p.1
    | some g => processGame A γ σ₀ e g p.1

/-- Requirement `e ≥ 1` handles the clocked machine `γ (e - 1)` (so that every machine is
handled while the budgets `2^{-e-i-6}`, `e ≥ 1`, sum to `1/32`). -/
def reqγ (γ : ℕ → OTMCode × ℕ) (e : ℕ) : OTMCode × ℕ := γ (e - 1)

/-- One stage of the construction: update `K*` with the pair `enumK (s - 1)` (so that stage
`s + 1` uses `enumK s` and every enumerated pair, including `enumK 0`, is used), then process
`R_1, …, R_s` in priority order (`processReq`, with `σ` itself as the state at the beginning of
the stage). -/
noncomputable def stageStep (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) (σ : CState) : CState :=
  ((List.range s).foldl (fun p e => processReq A (reqγ γ) σ (e + 1) p)
    (updateK enumK (s - 1) σ, false)).1

omit [Family] in
/-- Applying flips does not increase the `F*` value of any string. -/
theorem applyFlips_Fstar_le (T : Finset BitString) (σ : CState) (x : BitString) :
    (applyFlips T σ).Fstar x ≤ σ.Fstar x := by
  simp only [applyFlips]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- Starting a game on a witness does not increase the `F*` value of any string. -/
theorem startOn_Fstar_le {A : Set BitString} (γ : ℕ → OTMCode × ℕ) (e : ℕ) (σ : CState)
    (y x : BitString) : (startOn A γ e σ y).1.Fstar x ≤ σ.Fstar x :=
  applyFlips_Fstar_le _ _ x

/-- Starting a game does not increase the `F*` value of any string. -/
theorem startGame_Fstar_le (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (e : ℕ) (σ : CState)
    (x : BitString) : (startGame A γ e σ).1.Fstar x ≤ σ.Fstar x := by
  unfold startGame
  split
  · exact le_rfl
  · exact startOn_Fstar_le _ _ _ _ x

/-- Processing a game does not increase the `F*` value of any string. -/
theorem processGame_Fstar_le {A : Set BitString} (γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) (σ : CState) (x : BitString) :
    (processGame A γ σ₀ e g σ).1.Fstar x ≤ σ.Fstar x := by
  unfold processGame
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · exact applyFlips_Fstar_le _ _ x

/-- Processing a requirement does not increase the `F*` value of any string. -/
theorem processReq_Fstar_le (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (p : CState × Bool) (x : BitString) : (processReq A γ σ₀ e p).1.Fstar x ≤ p.1.Fstar x := by
  unfold processReq
  split
  · exact le_rfl
  · split
    · exact startGame_Fstar_le _ _ _ _ x
    · exact processGame_Fstar_le _ _ _ _ _ x

/-- Processing a sequence of requirements does not increase the `F*` value of any string. -/
theorem foldl_processReq_Fstar_le (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ : CState)
    (l : List ℕ) (p : CState × Bool) (x : BitString) :
    (l.foldl (fun p e => processReq A γ σ₀ (e + 1) p) p).1.Fstar x ≤ p.1.Fstar x := by
  induction l generalizing p with
  | nil => exact le_rfl
  | cons a l ih =>
    exact (ih _).trans (processReq_Fstar_le _ _ _ _ _ x)

/-- A full stage step does not increase the `F*` value of any string. -/
theorem stageStep_Fstar_le (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) (σ : CState) (x : BitString) : (stageStep A γ enumK s σ).Fstar x ≤ σ.Fstar x :=
  foldl_processReq_Fstar_le A (reqγ γ) σ (List.range s) _ x

/-- The state at the beginning of stage `s`. -/
noncomputable def stage (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ) :
    ℕ → CState
  | 0 => CState.init
  | s + 1 => stageStep A γ enumK (s + 1) (stage A γ enumK s)

/-- `F*` only decreases along the stages. -/
theorem stage_Fstar_antitone (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) (x : BitString) : (stage A γ enumK (s + 1)).Fstar x ≤ (stage A γ enumK s).Fstar x :=
  stageStep_Fstar_le A γ enumK (s + 1) _ x

/-- The limit `F = lim_s F*_s` (the values stabilise since they only decrease). -/
noncomputable def Flim (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (x : BitString) : ℕ :=
  ⨅ s, (stage A γ enumK s).Fstar x

/-! ### Effectiveness of the enumerations -/

/-- A numbering of actions on the states `Fin k` (states as naturals). -/
def Act.code {k : ℕ} : Act (Fin k) → ℕ
  | .step q a m => Nat.pair 0 (Nat.pair (q : ℕ) (Nat.pair (Encodable.encode a) m.toNat))
  | .push q b => Nat.pair 1 (Nat.pair (q : ℕ) (Encodable.encode b))
  | .ask q₁ q₂ => Nat.pair 2 (Nat.pair (q₁ : ℕ) (q₂ : ℕ))

/-- The transition table of a code, as a function of naturals (`0` outside the state range). -/
def OTMCode.table (c : OTMCode) (i : ℕ) (a : Sym) : ℕ :=
  if h : i < c.k then Act.code (c.δ ⟨i, h⟩ a) else 0

/-- An enumeration of clocked machines is *effective* if the number of states, the distinguished
states, the transition table and the clock exponent of `γ e` are computable functions of `e`
(stated without a `Primcodable` structure on `OTMCode`). -/
structure EffEnum (γ : ℕ → OTMCode × ℕ) : Prop where
  k : Computable fun e => (γ e).1.k
  start : Computable fun e => ((γ e).1.start : ℕ)
  accept : Computable fun e => ((γ e).1.accept : ℕ)
  reject : Computable fun e => ((γ e).1.reject : ℕ)
  table : Computable fun p : ℕ × ℕ × Sym => (γ p.1).1.table p.2.1 p.2.2
  clock : Computable fun e => (γ e).2

omit [Family] in
/-- An effective enumeration of all clocked machines exists: decode `e` by `Nat.unpair` into the
number of states `k`, the three distinguished states, the clock exponent and a list coding the
transition table (`3k` entries, each an `Act.code`); ill-formed codes decode to a fixed
machine.  Surjectivity: encode the table of a given code. -/
theorem exists_enum_computable :
    ∃ γ : ℕ → OTMCode × ℕ, Function.Surjective γ ∧ EffEnum γ := by
  have hm : Primrec fun e : ℕ => e.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hcode : ∀ {k : ℕ} (a : Act (Fin k)), Act.code a = actNum a := by
    intro k a; cases a <;> rfl
  refine ⟨γ₀, γ₀_surjective, ⟨(codeK_primrec.comp hm).to_comp,
    (codeStart_primrec.comp hm).to_comp, (codeAcc_primrec.comp hm).to_comp,
    (codeRej_primrec.comp hm).to_comp, ?_, (Primrec.snd.comp Primrec.unpair).to_comp⟩⟩
  refine (tableNum_primrec.comp ((hm.comp Primrec.fst).pair Primrec.snd)).to_comp.of_eq
    fun p => ?_
  change tableNum p.1.unpair.1 p.2.1 p.2.2 = (decodeCode p.1.unpair.1).table p.2.1 p.2.2
  rw [← tableNum_spec]
  unfold OTMCode.table
  simp only [hcode]

omit [Family] in
/-- A computable enumeration of `ov K`: dovetail the c.e. overgraph (`K.re`, via
`Nat.Partrec.Code.evaln`), outputting `([], K.H [])`-style padding elements while nothing new
appears (the overgraph is nonempty). -/
theorem exists_enumK_computable (K : AprioriComplexity) :
    ∃ enumK : ℕ → BitString × ℕ, Computable enumK ∧ (∀ s, K.H (enumK s).1 ≤ (enumK s).2) ∧
      ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 → ∃ s, enumK s = p := by
  obtain ⟨f, hf, hfP⟩ := REPred.exists_stage K.re
  refine ⟨fun s => ((Encodable.decode₂ (BitString × ℕ) s.unpair.1).bind fun p =>
      bif f p s.unpair.2 then some p else none).getD ([], K.H []), ?_, fun s => ?_,
    fun p hp => ?_⟩
  · exact (Primrec.option_getD.comp (Primrec.option_bind
      ((Primrec.decode₂ (α := BitString × ℕ)).comp
      (Primrec.fst.comp Primrec.unpair)) (Primrec.cond (hf.comp Primrec.snd
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))) (Primrec.option_some.comp
          Primrec.snd) (Primrec.const none)).to₂) (Primrec.const ([], K.H []))).to_comp
  · dsimp only
    rcases h : ((Encodable.decode₂ (BitString × ℕ) s.unpair.1).bind fun p =>
        bif f p s.unpair.2 then some p else none) with _ | p
    · exact le_rfl
    · obtain ⟨p', -, h2⟩ := Option.bind_eq_some_iff.1 h
      cases hb : f p' s.unpair.2
      · rw [hb] at h2; simp at h2
      · rw [hb] at h2
        simp only [Bool.cond_true, Option.some.injEq] at h2
        subst h2
        exact (hfP _).2 ⟨_, hb⟩
  · obtain ⟨k, hk⟩ := (hfP p).1 hp
    refine ⟨Nat.pair (Encodable.encode p) k, ?_⟩
    simp [Nat.unpair_pair, hk]

end Kolmogorov.RandomStrings
