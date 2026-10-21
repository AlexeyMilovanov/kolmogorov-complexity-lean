/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.Stages

/-!
# The mirrored stage and its computability

`StateC`, a finite representation of a construction state, its meaning `StateC.toState`, and the
mirrored stage `stageStepC`, which calls the semantic functions only where their results are finite
data.  The module proves that the mirrored stage represents the stage and that the mirrored
stages are computable (towards `Flim_re`).

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-! ### Effective simulation of the construction (for `Flim_re`)

`StateC` is a finite representation of a construction state (tables instead of functions, lists
instead of finite sets, formal sums `∑ ±2^{-k}` instead of real scores); `StateC.toState` is its
meaning.  The mirrored stage `stageStepC` calls the (noncomputable) semantic functions only where
their results are finite data (`chooseWitness`, `val`, `ourReply`, `playSet`, `flipped` as sorted
lists, `Cheats` as a Boolean), so that `stageStepC_toState` is a bookkeeping statement, and its
computability (`stageStepC_computable`) reduces to the machine and game primitives of
`AFG/Effective.lean` (`queryListCode`, `valC`) and to `replyC_computable`. -/

/-- Formal sums `∑ ±2^{-k}` (`(true, k)` stands for `+2^{-k}`, `(false, k)` for `-2^{-k}`): all
real numbers occurring in the construction are of this form. -/
abbrev FSum : Type := List (Bool × ℕ)

/-- The value of a formal sum. -/
noncomputable def FSum.val (l : FSum) : ℝ :=
  (l.map fun p => if p.1 then (2 : ℝ)⁻¹ ^ p.2 else -((2 : ℝ)⁻¹ ^ p.2)).sum

omit [Family] in
/-- The value of the empty list of terms is `0`. -/
theorem FSum.val_nil : FSum.val [] = 0 := rfl

omit [Family] in
/-- The value of the concatenation of two lists of terms is the sum of their values. -/
theorem FSum.val_append (l₁ l₂ : FSum) : FSum.val (l₁ ++ l₂) = FSum.val l₁ + FSum.val l₂ := by
  simp [FSum.val, List.map_append, List.sum_append]

/-- The finite form of a game state: flipped list, the two scores, and the turn. -/
abbrev GStC : Type := List BitString × FSum × FSum × Bool

/-- The game state represented by a finite game state. -/
noncomputable def GStC.toG (st : GStC) : GState :=
  ⟨st.1.toFinset, FSum.val st.2.1, FSum.val st.2.2.1, st.2.2.2⟩

/-- A finite game record: the witness, the play list, the budget exponent and the game state. -/
abbrev GameC : Type := BitString × List BitString × ℕ × GStC

/-- The game record represented by a finite game record. -/
noncomputable def GameC.toRec (g : GameC) : BitString × Finset BitString × ℕ × GState :=
  (g.1, g.2.1.toFinset, g.2.2.1, g.2.2.2.toG)

/-- A finite representation of a construction state: the modifications of `F*` (the first entry
for `x` counts, otherwise `F₀ x`), the enumerated pairs of `ov K` (`K*(x)` is the minimum of the
entries for `x`), the game records (the first entry for `e` counts; `none` = destroyed), and the
list of acting requirements (`i_e` = the number of entries `< e`). -/
structure StateC where
  /-- Modifications of `F*`. -/
  fTab : List (BitString × ℕ)
  /-- Enumerated pairs of `ov K`. -/
  kTab : List (BitString × ℕ)
  /-- Game records. -/
  games : List (ℕ × Option GameC)
  /-- Acting requirements (injury events). -/
  injList : List ℕ

/-- `StateC` as a product of lists. -/
def StateC.equiv :
    StateC ≃ List (BitString × ℕ) × List (BitString × ℕ) × List (ℕ × Option GameC) × List ℕ where
  toFun σ := (σ.fTab, σ.kTab, σ.games, σ.injList)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable StateC := Primcodable.ofEquiv _ StateC.equiv

/-- `F*` from its table. -/
def fLook (l : List (BitString × ℕ)) (x : BitString) : ℕ :=
  l.foldr (fun p acc => if p.1 = x then p.2 else acc) (F₀ x)

/-- `K*` from its table. -/
noncomputable def kLook (l : List (BitString × ℕ)) (x : BitString) : ℕ∞ :=
  l.foldr (fun p acc => if p.1 = x then min (p.2 : ℕ∞) acc else acc) ⊤

/-- The game record of `e` from the list of records. -/
def gLook (l : List (ℕ × Option GameC)) (e : ℕ) : Option GameC :=
  l.foldr (fun p acc => if p.1 = e then p.2 else acc) none

/-- The injury counter of `e`: the number of recorded acting requirements `< e`. -/
def iLook (l : List ℕ) (e : ℕ) : ℕ := (l.filter (· < e)).length

/-- The construction state represented by `σC`. -/
noncomputable def StateC.toState (σC : StateC) : CState :=
  ⟨fLook σC.fTab, kLook σC.kTab, fun e => (gLook σC.games e).map GameC.toRec,
    iLook σC.injList⟩

/-- The initial finite state. -/
def StateC.init : StateC := ⟨[], [], [], []⟩

omit [Family] in
/-- The initial abstract state equals the translation of the initial concrete state. -/
theorem StateC.toState_init : StateC.init.toState = CState.init := rfl

/-- A finite set of strings as a canonical list: its elements in the order of their codes. -/
def sortStr (s : Finset BitString) : List BitString :=
  (List.range (s.sup Encodable.encode + 1)).filterMap fun n =>
    (Encodable.decode n : Option BitString).filter fun z => decide (z ∈ s)

omit [Family] in
/-- A string belongs to the sorted list of strings if and only if it belongs to the set. -/
theorem mem_sortStr (s : Finset BitString) (z : BitString) : z ∈ sortStr s ↔ z ∈ s := by
  unfold sortStr
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨n, -, hn⟩
    rw [Option.filter_eq_some_iff] at hn
    simpa using hn.2
  · intro hz
    refine ⟨Encodable.encode z, ?_, ?_⟩
    · rw [List.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := Encodable.encode) hz)
    · rw [Option.filter_eq_some_iff]
      exact ⟨Encodable.encodek z, by simpa using hz⟩

omit [Family] in
/-- The finite set of strings in the sorted list of strings is exactly the original finite set. -/
theorem sortStr_toFinset (s : Finset BitString) : (sortStr s).toFinset = s := by
  ext z; rw [List.mem_toFinset, mem_sortStr]

/-- The flip cost of `z` under the value `h`, as a formal sum. -/
def flipCostC (h : ℕ) (z : BitString) : FSum :=
  if z.length - 1 ≤ h then [(true, z.length - 1), (false, h)] else []

/-- The cost of the move `S ↦ R` under the current values of `σC`, as a formal sum. -/
noncomputable def moveCostC (σC : StateC) (S R : List BitString) : FSum :=
  (R.dedup.filter (· ∉ S)).flatMap fun z => flipCostC (σC.toState.hval z) z

/-- The real change of `∑_{z ∈ X} 2^{-H*}` from `σ₀C` to `σC`, as a formal sum. -/
noncomputable def kCostC (σ₀C σC : StateC) (X : List BitString) : FSum :=
  X.dedup.flatMap fun z => [(true, σC.toState.hval z), (false, σ₀C.toState.hval z)]

/-- Charge the player to move. -/
def GStC.charge (st : GStC) (c : FSum) : GStC :=
  if st.2.2.2 then (st.1, st.2.1 ++ c, st.2.2.1, st.2.2.2)
  else (st.1, st.2.1, st.2.2.1 ++ c, st.2.2.2)

/-- The move of `K`: charge, move the token, pass the turn. -/
def GStC.kMove (st : GStC) (S' : List BitString) (c : FSum) : GStC :=
  (S', (st.charge c).2.1, (st.charge c).2.2.1, !st.2.2.2)

/-- A move in the game evaluated with the values of `σC`. -/
noncomputable def GStC.applyMove (σC : StateC) (st : GStC) (R : List BitString) : GStC :=
  if st.2.2.2 then (R, st.2.1 ++ moveCostC σC st.1 R, st.2.2.1, false)
  else (R, st.2.1, st.2.2.1 ++ moveCostC σC st.1 R, true)

/-- Mirror of `updateK`. -/
def updateKC (enumK : ℕ → BitString × ℕ) (s : ℕ) (σC : StateC) : StateC :=
  { σC with kTab := enumK s :: σC.kTab }

/-- Mirror of `applyFlips`. -/
def applyFlipsC (T : List BitString) (σC : StateC) : StateC :=
  { σC with fTab := T.map (fun z => (z, min (fLook σC.fTab z) (z.length - 4))) ++ σC.fTab }

/-- Mirror of `injure`. -/
def injureC (e : ℕ) (σC : StateC) : StateC :=
  { σC with games := σC.games.filter (fun p => p.1 ≤ e), injList := e :: σC.injList }

/-- Mirror of `destroy`. -/
def destroyC (e : ℕ) (σC : StateC) : StateC :=
  { σC with games := (e, none) :: σC.games }

/-- Mirror of `setGame`. -/
def setGameC (e : ℕ) (g : GameC) (σC : StateC) : StateC :=
  { σC with games := (e, some g) :: σC.games }

/-- The finite form of `firstState`. -/
def firstStateC (we : Bool) : GStC := ([], [], [], we)

/-- Mirror of `startOn`. -/
noncomputable def startOnC (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (e : ℕ) (σC : StateC)
    (x : BitString) :
    StateC × Bool :=
  (injureC e (applyFlipsC
    (sortStr (ourReply (newGame A γ σC.toState e x) (val (newGame A γ σC.toState e x))
      (firstState (newGame A γ σC.toState e x) (val (newGame A γ σC.toState e x)))))
    (setGameC e (x, sortStr (playSet γ σC.toState e x), e + σC.toState.inj e + 6,
      GStC.applyMove σC (firstStateC (val (newGame A γ σC.toState e x)))
        (sortStr (ourReply (newGame A γ σC.toState e x) (val (newGame A γ σC.toState e x))
          (firstState (newGame A γ σC.toState e x) (val (newGame A γ σC.toState e x)))))) σC)),
    true)

/-- Mirror of `startGame`. -/
noncomputable def startGameC (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (e : ℕ) (σC : StateC) :
    StateC × Bool :=
  match chooseWitness A γ σC.toState e with
  | none => (σC, false)
  | some x => startOnC A γ e σC x

open Classical in
/-- Mirror of `processGame` (written with `g.toRec` exactly as `processGame`, plus the mirrored
bookkeeping of the record). -/
noncomputable def processGameC (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀C : StateC) (e : ℕ)
    (g : GameC)
    (σC : StateC) : StateC × Bool :=
  if Cheats ((2 : ℝ)⁻¹ ^ g.toRec.2.2.1) g.toRec.2.2.2
      (kCost σ₀C.toState σC.toState g.toRec.2.1) then
    (injureC e (destroyC e σC), true)
  else if g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1 = g.toRec.2.2.2.S then
    (setGameC e (g.1, g.2.1, g.2.2.1, g.2.2.2.charge (kCostC σ₀C σC g.2.1)) σC, false)
  else
    (injureC e (applyFlipsC
      (sortStr (ourReply (curGame A γ σC.toState e g.toRec) (!g.toRec.2.2.2.yesTurn)
          (g.2.2.2.kMove (sortStr (g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1))
            (kCostC σ₀C σC g.2.1)).toG \
        (g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1)))
      (setGameC e (g.1, g.2.1, g.2.2.1,
        GStC.applyMove σC
          (g.2.2.2.kMove (sortStr (g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1))
            (kCostC σ₀C σC g.2.1))
          (sortStr (ourReply (curGame A γ σC.toState e g.toRec) (!g.toRec.2.2.2.yesTurn)
            (g.2.2.2.kMove (sortStr (g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1))
              (kCostC σ₀C σC g.2.1)).toG))) σC)), true)

/-- Mirror of `processReq`. -/
noncomputable def processReqC (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀C : StateC) (e : ℕ)
    (p : StateC × Bool) : StateC × Bool :=
  if p.2 then p else
    match gLook p.1.games e with
    | none => startGameC A γ e p.1
    | some g => processGameC A γ σ₀C e g p.1

/-- Mirror of `stageStep`. -/
noncomputable def stageStepC (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) (σC : StateC) : StateC :=
  ((List.range s).foldl (fun p e => processReqC A (reqγ γ) σC (e + 1) p)
    (updateKC enumK (s - 1) σC, false)).1

/-- Mirror of `stage`. -/
noncomputable def stageC (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ) :
    ℕ → StateC
  | 0 => StateC.init
  | s + 1 => stageStepC A γ enumK (s + 1) (stageC A γ enumK s)

/-! #### The mirrored stage represents the stage -/

section

omit [Family]

/-- Looking up a string in a table extended with a new pair `p` returns the minimum of its value
in the new pair and its old value in the table; other strings keep their value. -/
theorem kLook_cons (p : BitString × ℕ) (l : List (BitString × ℕ)) (x : BitString) :
    kLook (p :: l) x = if p.1 = x then min (p.2 : ℕ∞) (kLook l x) else kLook l x := rfl

/-- Looking up an index in a game table extended with a new entry `p` returns the game in `p`
if it matches, and the old game otherwise. -/
theorem gLook_cons (p : ℕ × Option GameC) (l : List (ℕ × Option GameC)) (e : ℕ) :
    gLook (p :: l) e = if p.1 = e then p.2 else gLook l e := rfl

/-- The value of a string `z` in the flipped table is the minimum of its old value
and `z.length - 4` if it is in `T`, and its old value otherwise. -/
theorem fLook_flips (T : List BitString) (l : List (BitString × ℕ)) (z : BitString) :
    fLook (T.map (fun z => (z, min (fLook l z) (z.length - 4))) ++ l) z =
      if z ∈ T then min (fLook l z) (z.length - 4) else fLook l z := by
  induction T with
  | nil => simp [fLook]
  | cons t T ih =>
    have e1 : fLook ((t :: T).map (fun z => (z, min (fLook l z) (z.length - 4))) ++ l) z =
        if t = z then min (fLook l t) (t.length - 4)
        else fLook (T.map (fun z => (z, min (fLook l z) (z.length - 4))) ++ l) z := rfl
    rw [e1, ih]
    by_cases h : t = z
    · subst h; simp
    · rw [ite_eq_right h]
      have : z ∈ t :: T ↔ z ∈ T := by simp [Ne.symm h]
      simp only [this]

/-- Filtering a game table to entries with index at most `e` preserves the lookup result
for indices up to `e`; lookups above `e` return `none`. -/
theorem gLook_filter (l : List (ℕ × Option GameC)) (e e' : ℕ) :
    gLook (l.filter (fun p => p.1 ≤ e)) e' = if e < e' then none else gLook l e' := by
  induction l with
  | nil => simp [gLook]
  | cons p l ih =>
    by_cases hp : p.1 ≤ e
    · rw [List.filter_cons_of_pos (by simpa using hp), gLook_cons, gLook_cons, ih]
      by_cases h1 : p.1 = e'
      · subst h1; simp [show ¬ e < p.1 by omega]
      · simp [h1]
    · rw [List.filter_cons_of_neg (by simpa using hp), ih, gLook_cons]
      by_cases h1 : p.1 = e'
      · subst h1; simp [show e < p.1 by omega]
      · simp [h1]

/-- Updating the concrete `K` table translates to the abstract `updateK` operation. -/
theorem toState_updateKC (enumK : ℕ → BitString × ℕ) (s : ℕ) (σC : StateC) :
    (updateKC enumK s σC).toState = updateK enumK s σC.toState := by
  change CState.mk _ _ _ _ = CState.mk _ _ _ _
  congr 1
  funext x
  rw [Function.update_apply]
  change kLook (enumK s :: σC.kTab) x = _
  rw [kLook_cons]
  by_cases h : x = (enumK s).1
  · subst h; simp [min_comm]; rfl
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]; rfl

/-- Applying flips in the concrete state translates to applying flips in the abstract state. -/
theorem toState_applyFlipsC (T : List BitString) (σC : StateC) :
    (applyFlipsC T σC).toState = applyFlips T.toFinset σC.toState := by
  change CState.mk _ _ _ _ = CState.mk _ _ _ _
  congr 1
  funext z
  change fLook (T.map (fun z => (z, min (fLook σC.fTab z) (z.length - 4))) ++ σC.fTab) z = _
  rw [fLook_flips]
  simp only [List.mem_toFinset]
  rfl

/-- Injuring the game `e` in the concrete state translates to injuring the game `e`
in the abstract state. -/
theorem toState_injureC (e : ℕ) (σC : StateC) : (injureC e σC).toState = injure e σC.toState := by
  change CState.mk _ _ _ _ = CState.mk _ _ _ _
  congr 1
  · funext e'
    change (gLook (σC.games.filter (fun p => p.1 ≤ e)) e').map GameC.toRec = _
    rw [gLook_filter]
    split_ifs <;> rfl
  · funext e'
    change ((e :: σC.injList).filter (· < e')).length =
      if e < e' then iLook σC.injList e' + 1 else iLook σC.injList e'
    rw [List.filter_cons]
    by_cases h : e < e'
    · rw [ite_eq_left (by simpa using h), ite_eq_left h, List.length_cons]; rfl
    · rw [ite_eq_right (by simpa using h), ite_eq_right h]; rfl

/-- Destroying the game `e` in the concrete state translates to destroying the game `e`
in the abstract state. -/
theorem toState_destroyC (e : ℕ) (σC : StateC) :
    (destroyC e σC).toState = destroy e σC.toState := by
  change CState.mk _ _ _ _ = CState.mk _ _ _ _
  congr 1
  funext e'
  change (gLook ((e, none) :: σC.games) e').map GameC.toRec = _
  rw [gLook_cons, Function.update_apply]
  by_cases h : e = e'
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; rfl

/-- Recording the game record `g` for `e` in the concrete state translates to `setGame e g.toRec`
in the abstract state. -/
theorem toState_setGameC (e : ℕ) (g : GameC) (σC : StateC) :
    (setGameC e g σC).toState = setGame e g.toRec σC.toState := by
  change CState.mk _ _ _ _ = CState.mk _ _ _ _
  congr 1
  funext e'
  change (gLook ((e, some g) :: σC.games) e').map GameC.toRec = _
  rw [gLook_cons, Function.update_apply]
  by_cases h : e = e'
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; rfl

/-- The value of a flat-mapped sum over a list is the sum of the values over the elements. -/
theorem FSum.val_flatMap (l : List BitString) (f : BitString → FSum) :
    FSum.val (l.flatMap f) = (l.map fun z => FSum.val (f z)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, FSum.val_append, ih, List.map_cons, List.sum_cons]

/-- The value of a pair of positive and negative terms is the difference of their weights. -/
theorem FSum.val_pair (a b : ℕ) :
    FSum.val [(true, a), (false, b)] = (2 : ℝ)⁻¹ ^ a - (2 : ℝ)⁻¹ ^ b := by
  simp [FSum.val]; ring

/-- The value of `flipCostC (d.h₀ z) z` is `flipCost d z`. -/
theorem flipCostC_val (d : GameData) (z : BitString) :
    FSum.val (flipCostC (d.h₀ z) z) = flipCost d z := by
  unfold flipCostC flipCost
  split_ifs with h
  · rw [FSum.val_pair]
    have : (2 : ℝ)⁻¹ ^ d.h₀ z ≤ (2 : ℝ)⁻¹ ^ (z.length - 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    rw [max_eq_right (by linarith)]
  · have : (2 : ℝ)⁻¹ ^ (z.length - 1) < (2 : ℝ)⁻¹ ^ d.h₀ z :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
    rw [FSum.val_nil, max_eq_left (by linarith)]

/-- If the game data `d` has the values `σC.toState.hval`, the value of `moveCostC σC S R` is
`moveCost d S.toFinset R.toFinset`. -/
theorem moveCostC_val (σC : StateC) (S R : List BitString) (d : GameData)
    (hd : d.h₀ = σC.toState.hval) :
    FSum.val (moveCostC σC S R) = moveCost d S.toFinset R.toFinset := by
  classical
  unfold moveCostC moveCost
  rw [FSum.val_flatMap]
  have hnd : (R.dedup.filter (· ∉ S)).Nodup := (List.nodup_dedup R).filter _
  have hset : (R.dedup.filter (· ∉ S)).toFinset = R.toFinset \ S.toFinset := by
    ext z; simp
  rw [← hset, List.sum_toFinset _ hnd]
  congr 1
  apply List.map_congr_left
  intro z _
  rw [← flipCostC_val d z, hd]

/-- The value of `kCostC σ₀C σC X` is `kCost σ₀C.toState σC.toState X.toFinset`. -/
theorem kCostC_val (σ₀C σC : StateC) (X : List BitString) :
    FSum.val (kCostC σ₀C σC X) = kCost σ₀C.toState σC.toState X.toFinset := by
  classical
  unfold kCostC kCost
  have hset : X.dedup.toFinset = X.toFinset := by ext z; simp
  rw [FSum.val_flatMap, ← hset, List.sum_toFinset _ (List.nodup_dedup X)]
  congr 1
  apply List.map_congr_left
  intro z _
  exact FSum.val_pair _ _

/-- Charging a formal sum `c` to the player to move commutes with `GStC.toG`: it charges
`FSum.val c`. -/
theorem chargeC_toG (st : GStC) (c : FSum) :
    (st.charge c).toG = st.toG.charge (FSum.val c) := by
  unfold GStC.charge GState.charge GStC.toG
  cases st.2.2.2 <;> simp [FSum.val_append]

/-- The `K` move of the finite game state `st` to `S'` charging `c` represents the `K` move of
`st.toG` to `S'.toFinset` charging `FSum.val c`. -/
theorem kMoveC_toG (st : GStC) (S' : List BitString) (c : FSum) :
    (st.kMove S' c).toG = st.toG.kMove S'.toFinset (FSum.val c) := by
  unfold GStC.kMove GState.kMove GStC.charge GState.charge GStC.toG
  cases st.2.2.2 <;> simp [FSum.val_append]

/-- Applying a move in the concrete state yields the corresponding transition in the abstract
game state. -/
theorem applyMoveC_toG (σC : StateC) (st : GStC) (R : List BitString) (d : GameData)
    (hd : d.h₀ = σC.toState.hval) :
    (GStC.applyMove σC st R).toG = applyMove d st.toG R.toFinset := by
  unfold GStC.applyMove applyMove GStC.toG
  rw [← moveCostC_val σC st.1 R d hd]
  cases st.2.2.2 <;> simp [FSum.val_append]

/-- The first state in the concrete game setup corresponds to the first abstract game state. -/
theorem firstStateC_toG (d : GameData) (we : Bool) : (firstStateC we).toG = firstState d we := by
  unfold firstStateC firstState GStC.toG
  cases we
  · simp [applyMove, GState.init, moveCost_self, FSum.val_nil]
  · simp [GState.init, FSum.val_nil]

end

/-- The pair (state, flag) represented by a finite pair. -/
noncomputable def pairToState (p : StateC × Bool) : CState × Bool := (p.1.toState, p.2)

/-- `pairToState` of `startOnC A γ e σC x` is `startOn A γ e σC.toState x`. -/
theorem startOnC_toState {A : Set BitString} (γ : ℕ → OTMCode × ℕ) (e : ℕ) (σC : StateC)
    (x : BitString) :
    pairToState (startOnC A γ e σC x) = startOn A γ e σC.toState x := by
  unfold startOnC startOn pairToState
  rw [toState_injureC, toState_applyFlipsC, toState_setGameC, sortStr_toFinset]
  have hrec : GameC.toRec (x, sortStr (playSet γ σC.toState e x), e + σC.toState.inj e + 6,
      GStC.applyMove σC (firstStateC (val (newGame A γ σC.toState e x)))
        (sortStr (ourReply (newGame A γ σC.toState e x) (val (newGame A γ σC.toState e x))
          (firstState (newGame A γ σC.toState e x) (val (newGame A γ σC.toState e x)))))) =
      (x, playSet γ σC.toState e x, e + σC.toState.inj e + 6,
        applyMove (newGame A γ σC.toState e x)
          (firstState (newGame A γ σC.toState e x) (val (newGame A γ σC.toState e x)))
          (ourReply (newGame A γ σC.toState e x) (val (newGame A γ σC.toState e x))
            (firstState (newGame A γ σC.toState e x) (val (newGame A γ σC.toState e x))))) := by
    unfold GameC.toRec
    rw [sortStr_toFinset, applyMoveC_toG σC _ _ (newGame A γ σC.toState e x) rfl,
      firstStateC_toG (newGame A γ σC.toState e x), sortStr_toFinset]
  rw [hrec]

/-- `pairToState` of `startGameC A γ e σC` is `startGame A γ e σC.toState`. -/
theorem startGameC_toState (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (e : ℕ) (σC : StateC) :
    pairToState (startGameC A γ e σC) = startGame A γ e σC.toState := by
  unfold startGameC startGame
  cases chooseWitness A γ σC.toState e with
  | none => rfl
  | some x => exact startOnC_toState γ e σC x

omit [Family] in
/-- Setting the game with a constructed state matches the abstract state update. -/
theorem toState_setGameC_mk (e : ℕ) (g : GameC) (st : GStC) (σC : StateC) :
    (setGameC e (g.1, g.2.1, g.2.2.1, st) σC).toState =
      setGame e (g.toRec.1, g.toRec.2.1, g.toRec.2.2.1, st.toG) σC.toState :=
  toState_setGameC e _ σC

/-- `pairToState` of `processGameC A γ σ₀C e g` is `processGame A γ σ₀C.toState e g.toRec`. -/
theorem processGameC_toState {A : Set BitString} (γ : ℕ → OTMCode × ℕ) (σ₀C : StateC) (e : ℕ)
    (g : GameC) (σC : StateC) :
    pairToState (processGameC A γ σ₀C e g σC) =
      processGame A γ σ₀C.toState e g.toRec σC.toState := by
  have hK : (g.2.2.2.kMove (sortStr (g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1))
      (kCostC σ₀C σC g.2.1)).toG = g.toRec.2.2.2.kMove (g.toRec.2.2.2.S ∪
        flipped σC.toState g.toRec.2.1) (kCost σ₀C.toState σC.toState g.toRec.2.1) := by
    rw [kMoveC_toG, sortStr_toFinset, kCostC_val]; rfl
  have hC : (g.2.2.2.charge (kCostC σ₀C σC g.2.1)).toG =
      g.toRec.2.2.2.charge (kCost σ₀C.toState σC.toState g.toRec.2.1) := by
    rw [chargeC_toG, kCostC_val]; rfl
  unfold processGameC processGame pairToState
  rw [hK]
  split_ifs
  · rw [toState_injureC, toState_destroyC]
  · rw [toState_setGameC_mk, hC]
  · rw [toState_injureC, toState_applyFlipsC, toState_setGameC_mk, sortStr_toFinset,
      applyMoveC_toG σC _ _ (curGame A γ σC.toState e g.toRec) rfl, hK, sortStr_toFinset]

/-- `pairToState` of `processReqC A γ σ₀C e` is `processReq A γ σ₀C.toState e`. -/
theorem processReqC_toState (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀C : StateC) (e : ℕ)
    (p : StateC × Bool) :
    pairToState (processReqC A γ σ₀C e p) = processReq A γ σ₀C.toState e (pairToState p) := by
  unfold processReqC processReq pairToState
  by_cases hp : p.2 = true
  · simp [hp]
  · simp only [hp, Bool.false_eq_true, ite_false]
    change _ = match (gLook p.1.games e).map GameC.toRec with
      | none => startGame A γ e p.1.toState
      | some g => processGame A γ σ₀C.toState e g p.1.toState
    cases gLook p.1.games e with
    | none => exact startGameC_toState A γ e p.1
    | some g => exact processGameC_toState γ σ₀C e g p.1

/-- Folding over requirements in the concrete state matches folding in the abstract state. -/
theorem foldl_processReqC_toState (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀C : StateC)
    (l : List ℕ) (p : StateC × Bool) :
    pairToState (l.foldl (fun p e => processReqC A γ σ₀C (e + 1) p) p) =
      l.foldl (fun p e => processReq A γ σ₀C.toState (e + 1) p) (pairToState p) := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, List.foldl_cons, ih, processReqC_toState]

/-- A single step of a stage in the concrete state matches the abstract stage step. -/
theorem stageStepC_toState (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ)
    (σC : StateC) : (stageStepC A γ enumK s σC).toState = stageStep A γ enumK s σC.toState := by
  unfold stageStepC stageStep
  have h := foldl_processReqC_toState A (reqγ γ) σC (List.range s)
      (updateKC enumK (s - 1) σC, false)
  have h1 : pairToState (updateKC enumK (s - 1) σC, false) =
    (updateK enumK (s - 1) σC.toState, false) := by
    unfold pairToState; rw [toState_updateKC]
  rw [h1] at h
  exact congrArg Prod.fst h

/-- The mirrored stages represent the stages. -/
theorem stageC_toState (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) :
    (stageC A γ enumK s).toState = stage A γ enumK s := by
  induction s with
  | zero => rfl
  | succ s ih => rw [stageC, stage, stageStepC_toState, ih]

/-- The values in the `Fstar` table after a stage correspond to looking up values in the `fTab`. -/
theorem stage_Fstar_eq_fLook (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ)
    (x : BitString) : (stage A γ enumK s).Fstar x = fLook (stageC A γ enumK s).fTab x := by
  rw [← stageC_toState]; rfl

/-! #### Computability of the mirrored stages -/

section

omit [Family]

/-- The initial function `F₀` is primitive recursive. -/
theorem F₀_primrec : Primrec F₀ :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.list_length)
    (Primrec.const 3)

/-- The table lookup of `F*` is primitive recursive. -/
theorem fLook_primrec : Primrec₂ fLook := by
  have h : Primrec fun a : List (BitString × ℕ) × BitString =>
      a.1.foldr (fun p acc => if p.1 = a.2 then p.2 else acc) (F₀ a.2) :=
    Primrec.list_foldr Primrec.fst (F₀_primrec.comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact h

/-- The function computing the `fTab` of a state is primitive recursive. -/
theorem StateC.fTab_primrec : Primrec StateC.fTab :=
  Primrec.fst.comp (Primrec.of_equiv (e := StateC.equiv))

/-- The canonical list of the set of elements of a list is primitive recursive. -/
theorem sortStr_toFinset_primrec : Primrec fun l : List BitString => sortStr l.toFinset := by
  have hsup : ∀ l : List BitString,
      l.toFinset.sup Encodable.encode = (l.map Encodable.encode).foldr max 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.toFinset_cons, Finset.sup_insert, ih]; rfl
  have hmem : ∀ (l : List BitString) (z : BitString), decide (z ∈ l.toFinset) = memStr z l := by
    intro l z
    by_cases h : z ∈ l
    · rw [decide_eq_true (List.mem_toFinset.2 h), (memStr_iff z l).2 h]
    · rw [decide_eq_false (fun h' => h (List.mem_toFinset.1 h'))]
      cases hm : memStr z l
      · rfl
      · exact absurd ((memStr_iff z l).1 hm) h
  have hB : Primrec fun l : List BitString => (l.map Encodable.encode).foldr max 0 + 1 :=
    Primrec.nat_add.comp (Primrec.list_foldr (Primrec.list_map Primrec.id
      (Primrec.encode.comp Primrec.snd).to₂) (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂) (Primrec.const 1)
  have hg : Primrec₂ fun (l : List BitString) (n : ℕ) =>
      (Encodable.decode n : Option BitString).bind fun z =>
        if memStr z l = true then some z else none :=
    (Primrec.option_bind (Primrec.decode.comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp (memStr_primrec.comp Primrec.snd (Primrec.fst.comp
          Primrec.fst)) (Primrec.const true))
        (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂).to₂
  have h := Primrec.listFilterMap (Primrec.list_range.comp hB) hg
  refine h.of_eq fun l => ?_
  unfold sortStr
  rw [hsup]
  congr 1
  funext n
  cases (Encodable.decode n : Option BitString) with
  | none => rfl
  | some z =>
    change (if memStr z l = true then some z else none) =
      (if decide (z ∈ l.toFinset) = true then some z else none)
    rw [hmem]

/-- An effective enumeration has a computable numbering of its machines
(`exists_code_computable`). -/
theorem effEnum_code (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    ∃ code : ℕ → ℕ, Computable code ∧ ∀ e, decodeCode (code e) = (γ e).1 := by
  have hcode : ∀ {k : ℕ} (a : Act (Fin k)), Act.code a = actNum a := by
    intro k a; cases a <;> rfl
  refine exists_code_computable (fun e => (γ e).1) hγ.k hγ.start hγ.accept hγ.reject
    (hγ.table.of_eq fun p => ?_)
  unfold OTMCode.table actTable
  split_ifs <;> simp [hcode]

end

/-- The strings of the games of the `e`-th clocked machine of an effective enumeration (its
possible queries if it belongs to the family on the input, otherwise none), as a computable list
(`queryListCodeF`). -/
theorem queryList_computable (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    ∃ q : ℕ → BitString → List BitString, Computable₂ q ∧
      ∀ e x, (q e x).toFinset = qsetF (γ e).1 (γ e).2 x := by
  obtain ⟨code, hc, hcode⟩ := effEnum_code γ hγ
  refine ⟨fun e x => queryListCodeF (code e) (γ e).2 x, ?_, fun e x => ?_⟩
  · have h0 := queryListCodeF_computable.comp ((hc.comp Computable.fst).pair
      ((hγ.clock.comp Computable.fst).pair Computable.snd) :
        Computable fun p : ℕ × BitString => (code p.1, (γ p.1).2, p.2))
    exact h0
  · rw [queryListCodeF_toFinset, hcode e]

omit [Family] in
/-- The clocked verdict of the `e`-th machine with a finite oracle is computable
(`clockedOutcome`). -/
theorem clockedOutcome_computable (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    ∃ o : ℕ → List BitString × BitString → Bool, Computable₂ o ∧
      ∀ e ans x, (o e (ans, x) = true ↔ ClockedAccepts (γ e).1 (γ e).2 {z | z ∈ ans} x) := by
  obtain ⟨code, hc, hcode⟩ := effEnum_code γ hγ
  refine ⟨fun e p => clockedOutcome (code e) (γ e).2 p.1 p.2, ?_, fun e ans x => ?_⟩
  · have h0 := clockedOutcome_primrec.to_comp.comp ((hc.comp Computable.fst).pair
      ((hγ.clock.comp Computable.fst).pair
        ((Computable.fst.comp Computable.snd).pair (Computable.snd.comp Computable.snd))) :
        Computable fun p : ℕ × (List BitString × BitString) => (code p.1, (γ p.1).2, p.2.1, p.2.2))
    exact h0
  · rw [clockedOutcome_iff, hcode e]

/-- `K*` from its table as an optional natural number (`none` stands for `⊤`). -/
def kLookO (l : List (BitString × ℕ)) (x : BitString) : Option ℕ :=
  l.foldr (fun p acc => if p.1 = x then some (acc.elim p.2 (min p.2)) else acc) none

omit [Family] in
/-- Looking up a value with `kLook` is equivalent to evaluating `kLookO` and treating `none`
as `⊤`. -/
theorem kLook_eq_kLookO (l : List (BitString × ℕ)) (x : BitString) :
    kLook l x = (kLookO l x).elim ⊤ (fun a => (a : ℕ∞)) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change (if p.1 = x then min (p.2 : ℕ∞) (kLook l x) else kLook l x) =
      (if p.1 = x then some ((kLookO l x).elim p.2 (min p.2)) else kLookO l x).elim ⊤
        (fun a => (a : ℕ∞))
    rw [ih]
    split_ifs
    · cases kLookO l x with
      | none => exact min_eq_left le_top
      | some a => rfl
    · rfl

/-- `H*` from the tables. -/
def hvalTab (σC : StateC) (z : BitString) : ℕ :=
  (kLookO σC.kTab z).elim (fLook σC.fTab z + 3) (fun a => min (a + 5) (fLook σC.fTab z + 3))

omit [Family] in
/-- The abstract value of a string in the state equals the computed `hvalTab` value. -/
theorem hval_eq_hvalTab (σC : StateC) (z : BitString) : σC.toState.hval z = hvalTab σC z := by
  change (min (kLook σC.kTab z + 5) ((fLook σC.fTab z : ℕ∞) + 3)).toNat = hvalTab σC z
  rw [kLook_eq_kLookO]
  unfold hvalTab
  cases kLookO σC.kTab z with
  | none =>
    change (min (⊤ + 5) ((fLook σC.fTab z : ℕ∞) + 3)).toNat = fLook σC.fTab z + 3
    rw [top_add, min_eq_right le_top]
    exact ENat.toNat_natCast _
  | some a =>
    change (min ((a : ℕ∞) + 5) ((fLook σC.fTab z : ℕ∞) + 3)).toNat =
      min (a + 5) (fLook σC.fTab z + 3)
    rw [show min ((a : ℕ∞) + 5) ((fLook σC.fTab z : ℕ∞) + 3) =
      ((min (a + 5) (fLook σC.fTab z + 3) : ℕ) : ℕ∞) by rfl]
    exact ENat.toNat_natCast _

omit [Family] in
/-- The partial lookup function `kLookO` is primitive recursive. -/
theorem kLookO_primrec : Primrec₂ kLookO := by
  have h := Primrec.list_foldr (σ := Option ℕ)
      (Primrec.fst : Primrec fun a : List (BitString × ℕ) × BitString => a.1)
      (Primrec.const none)
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp (Primrec.option_casesOn (Primrec.snd.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.nat_min.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp
            Primrec.fst))) Primrec.snd).to₂))
        (Primrec.snd.comp Primrec.snd)).to₂
  refine h.of_eq fun a => ?_
  unfold kLookO
  congr 1
  funext p acc
  by_cases hp : p.1 = a.2
  · simp only [hp, ite_true]
    cases acc <;> rfl
  · simp only [hp, ite_false]

omit [Family] in
/-- The function computing the heuristic value table is primitive recursive. -/
theorem hvalTab_primrec : Primrec₂ hvalTab := by
  have hF : Primrec fun p : StateC × BitString => fLook p.1.fTab p.2 + 3 :=
    Primrec.nat_add.comp (fLook_primrec.comp (StateC.fTab_primrec.comp Primrec.fst) Primrec.snd)
      (Primrec.const 3)
  have hO : Primrec fun p : StateC × BitString => kLookO p.1.kTab p.2 :=
    kLookO_primrec.comp ((Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv
      (e := StateC.equiv))) : Primrec StateC.kTab).comp Primrec.fst) Primrec.snd
  have h := Primrec.option_casesOn hO hF
    (Primrec.nat_min.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 5))
      (hF.comp Primrec.fst)).to₂
  refine h.of_eq fun p => ?_
  unfold hvalTab
  cases kLookO p.1.kTab p.2 <;> rfl

/-- Finite data of a game `gameOfF A (γ e).1 (γ e).2 x h (2^{-m}) X`: the machine index `e`, the
witness `x`, the play list `X`, a table of the values `h` covering the strings `qsetF` of `x` and
`X`, and the budget exponent `m`. -/
abbrev GameDataC : Type := ℕ × BitString × List BitString × List (BitString × ℕ) × ℕ

/-- `D` describes the game `gameOfF A (γ e).1 (γ e).2 x h (2^{-m}) X.toFinset`: the table lists
the values `h` on a list covering the strings `qsetF` of `x` and the play list. -/
def GameDataC.Describes (γ : ℕ → OTMCode × ℕ) (D : GameDataC) (h : BitString → ℕ) : Prop :=
  ∃ L : List BitString, D.2.2.2.1 = L.map (fun z => (z, h z)) ∧
    (∀ z ∈ qsetF (γ D.1).1 (γ D.1).2 D.2.1, z ∈ L) ∧
    ∀ z ∈ D.2.2.1, z ∈ L

omit [Family] in
/-- Games that differ only in the values off the play set and in the outcome on non-reachable
positions have the same value. -/
theorem val_congr (d d' : GameData) (hX : d'.X = d.X) (hε : d'.ε = d.ε)
    (hh : ∀ z ∈ d.X, d'.h₀ z = d.h₀ z) (hout : ∀ S, S ⊆ d.X → d'.outcome S = d.outcome S) :
    val d' = val d := by
  have hf : ∀ z ∈ d.X, flipCost d' z = flipCost d z := fun z hz => by
    unfold flipCost; rw [hh z hz]
  have hm : ∀ S S', S' ⊆ d.X → moveCost d' S S' = moveCost d S S' := fun S S' hS' =>
    Finset.sum_congr rfl fun z hz => hf z (hS' (Finset.sdiff_subset hz))
  have hdir : ∀ (d₁ d₂ : GameData), d₂.X = d₁.X → d₂.ε = d₁.ε →
      (∀ z ∈ d₁.X, flipCost d₂ z = flipCost d₁ z) →
      (∀ S, S ⊆ d₁.X → d₂.outcome S = d₁.outcome S) → YesWinsInit d₁ → YesWinsInit d₂ := by
    intro d₁ d₂ hX hε hf hout h
    obtain ⟨S₁, ⟨h1, h2, h3⟩, hs⟩ := h
    have hm' : moveCost d₂ GState.init.S S₁ = moveCost d₁ GState.init.S S₁ :=
      Finset.sum_congr rfl fun z hz => hf z (h2 (Finset.sdiff_subset hz))
    refine ⟨S₁, ⟨h1, hX ▸ h2, ?_⟩, ?_⟩
    · rw [hm', hε]; exact h3
    · refine safeYes_transfer d₁ d₂ hX hε (fun _ => 0) (fun z hz => (hf z hz).le)
        (fun z hz => by rw [hf z hz]; simp) ∅ (fun S _ hS => hout S hS) _ hs _ rfl
        (Finset.empty_subset _) h2 rfl rfl ?_ ?_
      · change (if true = true then 0 + moveCost d₂ GState.init.S S₁ else 0) ≤
          (if true = true then 0 + moveCost d₁ GState.init.S S₁ else 0)
        rw [hm']
      · simp [applyMove, GState.init]
  unfold val
  congr 1
  exact propext ⟨hdir d' d hX.symm hε.symm (fun z hz => (hf z (hX ▸ hz)).symm)
      (fun S hS => (hout S (hX ▸ hS)).symm), hdir d d' hX hε hf hout⟩

omit [Family] in
/-- For `z ∈ L`, the table `L.map fun w => (w, h w)` returns `h z` at `z`. -/
theorem tableFn_map (L : List BitString) (h : BitString → ℕ) (z : BitString) (hz : z ∈ L) :
    tableFn (L.map fun w => (w, h w)) z = h z := by
  induction L with
  | nil => simp at hz
  | cons a L ih =>
    change (if a = z then h a else tableFn (L.map fun w => (w, h w)) z) = h z
    by_cases ha : a = z
    · rw [ite_eq_left ha, ha]
    · rw [ite_eq_right ha]
      exact ih ((List.mem_cons.1 hz).resolve_left (Ne.symm ha))

/-- The guard bits of the finite game of the data `D` (the machine belongs to the family on the
input; the default outcome `x ∉ A`) are computable. -/
theorem phiD_computable (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (code : ℕ → ℕ)
    (hc : Computable code)
    (hcode : ∀ e, decodeCode (code e) = (γ e).1) (hclock : Computable fun e => (γ e).2)
    [DecidablePred (· ∈ A)] (hAc : Computable fun x : BitString => decide (x ∈ A)) :
    ∃ ph : GameDataC → Bool × Bool, Computable ph ∧ ∀ D : GameDataC,
      ((ph D).1 = true ↔ Family.Φ (γ D.1).1 (γ D.1).2 D.2.1) ∧ ((ph D).2 = true ↔ D.2.1 ∉ A) := by
  refine ⟨fun D => (Family.ΦB (code D.1) (γ D.1).2 D.2.1, !(decide (D.2.1 ∈ A))), ?_,
    fun D => ⟨?_, ?_⟩⟩
  · have h1 := Family.ΦB_computable.comp ((hc.comp Computable.fst).pair
      ((hclock.comp Computable.fst).pair (Computable.fst.comp Computable.snd)) :
        Computable fun D : GameDataC => (code D.1, (γ D.1).2, D.2.1))
    have h2 := (Primrec.not.to_comp).comp (hAc.comp (Computable.fst.comp Computable.snd) :
        Computable fun D : GameDataC => decide (D.2.1 ∈ A))
    exact h1.pair h2
  · change Family.ΦB (code D.1) (γ D.1).2 D.2.1 = true ↔ _
    rw [Family.ΦB_iff, hcode]
  · change (!(decide (D.2.1 ∈ A))) = true ↔ D.2.1 ∉ A
    simp

/-- The finite game of described data has the values `h` on the strings in play. -/
theorem gameD_h₀ (γ : ℕ → OTMCode × ℕ) (D : GameDataC) (h : BitString → ℕ) (hD : D.Describes γ h)
    (z : BitString) (hz : z ∈ D.2.2.1.toFinset) : tableFn D.2.2.2.1 z = h z := by
  obtain ⟨L, hT, -, hXL⟩ := hD
  rw [hT]
  exact tableFn_map L h z (hXL z (List.mem_toFinset.1 hz))

/-- The finite game of described data (with guard bits for `Φ` and `x ∉ A`) has the outcomes of
the guarded game. -/
theorem gameD_outcome (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (code : ℕ → ℕ)
    (hcode : ∀ e, decodeCode (code e) = (γ e).1) (D : GameDataC) (b₁ b₂ : Bool)
    (h₁ : b₁ = true ↔ Family.Φ (γ D.1).1 (γ D.1).2 D.2.1) (h₂ : b₂ = true ↔ D.2.1 ∉ A)
    (h : BitString → ℕ) (hD : D.Describes γ h) (S : Finset BitString) :
    (GD.game ⟨code D.1, Family.clk (γ D.1).2 D.2.1.length, D.2.1, D.2.2.2.1, D.2.2.2.2, D.2.2.1,
      b₁, b₂⟩).outcome S =
      (gameOfF A (γ D.1).1 (γ D.1).2 D.2.1 h ((2 : ℝ)⁻¹ ^ D.2.2.2.2)
        D.2.2.1.toFinset).outcome S := by
  classical
  obtain ⟨L, hT, hQ, -⟩ := hD
  change (gameOfBT (decodeCode (code D.1)) (Family.clk (γ D.1).2 D.2.1.length) D.2.1
      (tableFn D.2.2.2.1) ((2 : ℝ)⁻¹ ^ D.2.2.2.2) D.2.2.1.toFinset b₁ b₂).outcome S = _
  rw [hcode, gameOfBT_eq_gameOfF A _ _ _ _ _ _ b₁ b₂ h₁ h₂]
  by_cases hΦ : Family.Φ (γ D.1).1 (γ D.1).2 D.2.1
  · rw [gameOfF_of_Φ A _ _ _ hΦ, gameOfF_of_Φ A _ _ _ hΦ]
    change decide _ = decide _
    apply decide_eq_decide.2
    apply clockedAcceptsT_iff_of_agree
    intro z hz
    have hzL := hQ z (by rw [qsetF_of_Φ hΦ]; exact hz)
    simp only [oracleOf, Set.mem_ofPred_eq, hT, tableFn_map L h z hzL]
  · rw [gameOfF_outcome_of_not A _ _ _ hΦ, gameOfF_outcome_of_not A _ _ _ hΦ]

/-- The value of the finite game of described data is the value of the guarded game. -/
theorem gameD_val_eq (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (code : ℕ → ℕ)
    (hcode : ∀ e, decodeCode (code e) = (γ e).1) (ph : GameDataC → Bool × Bool)
    (hphi : ∀ D : GameDataC,
      ((ph D).1 = true ↔ Family.Φ (γ D.1).1 (γ D.1).2 D.2.1) ∧ ((ph D).2 = true ↔ D.2.1 ∉ A))
    (D : GameDataC) (h : BitString → ℕ) (hD : D.Describes γ h) :
    val (gameOfF A (γ D.1).1 (γ D.1).2 D.2.1 h ((2 : ℝ)⁻¹ ^ D.2.2.2.2) D.2.2.1.toFinset) =
      val (GD.game ⟨code D.1, Family.clk (γ D.1).2 D.2.1.length, D.2.1, D.2.2.2.1, D.2.2.2.2,
        D.2.2.1, (ph D).1, (ph D).2⟩) := by
  apply val_congr
  · rfl
  · rfl
  · intro z hz
    exact (gameD_h₀ γ D h hD z hz).symm
  · intro S _
    exact (gameD_outcome A γ code hcode D _ _ (hphi D).1 (hphi D).2 h hD S).symm

/-- The value of a game given by finite data is computable (`valC` of `AFG/Effective.lean`). -/
theorem valD_computable (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    ∃ v : GameDataC → Bool, Computable v ∧
      ∀ (D : GameDataC) (h : BitString → ℕ), D.Describes γ h →
        v D = val (gameOfF A (γ D.1).1 (γ D.1).2 D.2.1 h ((2 : ℝ)⁻¹ ^ D.2.2.2.2)
          D.2.2.1.toFinset) := by
  classical
  obtain ⟨code, hc, hcode⟩ := effEnum_code γ hγ
  obtain ⟨_, hAc⟩ := hA
  obtain ⟨ph, hph, hphi⟩ := phiD_computable A γ code hc hcode hγ.clock hAc
  refine ⟨fun D => valC ⟨code D.1, Family.clk (γ D.1).2 D.2.1.length, D.2.1, D.2.2.2.1,
    D.2.2.2.2, D.2.2.1, (ph D).1, (ph D).2⟩, ?_, fun D h hD => ?_⟩
  · have hmk : Primrec fun p : ℕ × ℕ × BitString × List (BitString × ℕ) × ℕ ×
        List BitString × Bool × Bool =>
        GD.equiv.symm p := Primrec.of_equiv_symm
    have h0 := valC_computable.comp (hmk.to_comp.comp ((hc.comp Computable.fst).pair
      ((Family.clk_computable.comp (hγ.clock.comp Computable.fst)
        (Primrec.list_length.to_comp.comp (Computable.fst.comp Computable.snd))).pair
      ((Computable.fst.comp Computable.snd).pair
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))).pair
          ((Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))).pair
            ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
              ((Computable.fst.comp hph).pair (Computable.snd.comp hph)))))))))
    exact h0.of_eq fun D => rfl
  · change valC ⟨code D.1, Family.clk (γ D.1).2 D.2.1.length, D.2.1, D.2.2.2.1, D.2.2.2.2,
      D.2.2.1, (ph D).1, (ph D).2⟩ = _
    rw [valC_spec]
    exact (gameD_val_eq A γ code hcode ph hphi D h hD).symm

end Kolmogorov.RandomStrings
