/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Machines

/-!
# The threshold game `G_{e,x}` (§3.1 of the paper, specialised to the atoms `H(z) ≥ |z|`)

A game is played on a finite set `X` of query strings with current values `h₀`.  A position is
the set `S ⊆ X` of strings that have been *flipped* to non-random (their `H`-value lowered to
`|z| - 1`).  Flipping a random `z` costs `2^{-(|z|-1)} - 2^{-h₀ z}` of Kraft mass; flipping a
string that is already non-random costs nothing (and changes nothing).  Each player has a budget
`ε`; a player may always leave the token where it is (pass).  The outcome of a position is the
verdict of the clocked reduction with the oracle `{z | z random under h₀ and z ∉ S}`.

As in the paper, the winner is decided by *where the token ends up*: `SafeYes d st` (NO to move)
says that the current outcome is `true` and that every non-passing NO move can be answered by a
YES move (possibly a pass) to a position that is again safe for YES; `SafeNo` symmetrically.
These are inductive predicates; they describe finite game trees because every non-passing move
flips a new string of the finite set `X`.  `val d = true` iff YES has a first move (possibly a
pass) to a safe position; otherwise NO can always answer YES's first move by a move to a position
safe for NO (`noWinsInit_of_not_yesWinsInit`, determinacy).
-/

namespace Kolmogorov.RandomStrings

/-- The data of a game. -/
structure GameData where
  /-- The strings in play. -/
  X : Finset BitString
  /-- The current values of `H`. -/
  h₀ : BitString → ℕ
  /-- The budget of each player. -/
  ε : ℝ
  /-- The verdict of the reduction as a function of the flipped set. -/
  outcome : Finset BitString → Bool

/-- The mass needed to flip `z` to non-random: `2^{-(|z|-1)} - 2^{-h₀ z}`, truncated at `0`
(so that flipping an already non-random string costs nothing).  This is exactly the real increase
of `2^{-H(z)}` when `H(z)` is lowered to `min (H(z), |z| - 1)`. -/
noncomputable def flipCost (d : GameData) (z : BitString) : ℝ :=
  max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ d.h₀ z)

/-- The mass of a move `S ↦ S'`. -/
noncomputable def moveCost (d : GameData) (S S' : Finset BitString) : ℝ :=
  ∑ z ∈ S' \ S, flipCost d z

/-- A game state: the flipped set, both scores, and whose turn it is. -/
structure GState where
  /-- The flipped strings. -/
  S : Finset BitString
  /-- The YES player's score. -/
  scoreY : ℝ
  /-- The NO player's score. -/
  scoreN : ℝ
  /-- `true` if YES is to move. -/
  yesTurn : Bool

/-- The initial state. -/
def GState.init : GState := ⟨∅, 0, 0, true⟩

/-- The player to move may move the token to `S'`. -/
def LegalMove (d : GameData) (st : GState) (S' : Finset BitString) : Prop :=
  st.S ⊆ S' ∧ S' ⊆ d.X ∧
    (if st.yesTurn then st.scoreY + moveCost d st.S S' ≤ d.ε
      else st.scoreN + moveCost d st.S S' ≤ d.ε)

/-- The state after the move `S'`. -/
noncomputable def applyMove (d : GameData) (st : GState) (S' : Finset BitString) : GState :=
  { S := S',
    scoreY := if st.yesTurn then st.scoreY + moveCost d st.S S' else st.scoreY,
    scoreN := if st.yesTurn then st.scoreN else st.scoreN + moveCost d st.S S',
    yesTurn := !st.yesTurn }

/-- `SafeYes d st` (used with NO to move): the outcome of the current position is `true` (so if NO
never moves again, YES has won), and every legal non-passing NO move `S'` has a legal YES answer
`reply S'` (possibly a pass) after which YES is again safe. -/
inductive SafeYes (d : GameData) : GState → Prop
  | intro (st : GState) (reply : Finset BitString → Finset BitString)
      (hout : d.outcome st.S = true)
      (hlegal : ∀ S', LegalMove d st S' → S' ≠ st.S →
        LegalMove d (applyMove d st S') (reply S'))
      (hsafe : ∀ S', LegalMove d st S' → S' ≠ st.S →
        SafeYes d (applyMove d (applyMove d st S') (reply S'))) :
      SafeYes d st

/-- `SafeNo d st` (used with YES to move): the outcome of the current position is `false`, and
every legal non-passing YES move has a legal NO answer after which NO is again safe. -/
inductive SafeNo (d : GameData) : GState → Prop
  | intro (st : GState) (reply : Finset BitString → Finset BitString)
      (hout : d.outcome st.S = false)
      (hlegal : ∀ S', LegalMove d st S' → S' ≠ st.S →
        LegalMove d (applyMove d st S') (reply S'))
      (hsafe : ∀ S', LegalMove d st S' → S' ≠ st.S →
        SafeNo d (applyMove d (applyMove d st S') (reply S'))) :
      SafeNo d st

/-- YES wins: it has a first move (possibly a pass) to a position safe for YES. -/
def YesWinsInit (d : GameData) : Prop :=
  ∃ S₁, LegalMove d GState.init S₁ ∧ SafeYes d (applyMove d GState.init S₁)

/-- NO wins: every first move of YES (including a pass) has a NO answer (possibly a pass) to a
position safe for NO. -/
def NoWinsInit (d : GameData) : Prop :=
  ∀ S₁, LegalMove d GState.init S₁ →
    ∃ S₂, LegalMove d (applyMove d GState.init S₁) S₂ ∧
      SafeNo d (applyMove d (applyMove d GState.init S₁) S₂)

/-- The value of the game (`true` iff YES has a winning strategy). -/
noncomputable def val (d : GameData) : Bool := by
  classical exact decide (YesWinsInit d)

/-- The oracle determined by the values `h` and the flipped set `S`:
`z` is random iff `|z| ≤ h z` and `z ∉ S`. -/
def oracleOf (h : BitString → ℕ) (S : Finset BitString) : Set BitString :=
  {z | z.length ≤ h z ∧ z ∉ S}

/-- The game `G_{e,x}` for the clocked machine `(c, e)` on input `x`, current values `h`,
budget `ε`, played on the strings `X`. -/
noncomputable def gameOf (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) : GameData :=
  { X := X, h₀ := h, ε := ε,
    outcome := fun S => by classical exact decide (ClockedAccepts c e (oracleOf h S) x) }

/-- `val` reads off `YesWinsInit`. -/
theorem determined (d : GameData) : val d = true ↔ YesWinsInit d := by
  simp [val]

/-- Flipping a string never costs a negative amount of mass: `0 ≤ flipCost d z`. -/
theorem flipCost_nonneg (d : GameData) (z : BitString) : 0 ≤ flipCost d z := le_max_left _ _

/-- A move never costs a negative amount of mass: `0 ≤ moveCost d S S'`. -/
theorem moveCost_nonneg (d : GameData) (S S' : Finset BitString) : 0 ≤ moveCost d S S' :=
  Finset.sum_nonneg fun z _ => flipCost_nonneg d z

/-- Passing costs nothing. -/
theorem moveCost_self (d : GameData) (S : Finset BitString) : moveCost d S S = 0 := by
  simp [moveCost]

/-- Costs add up along successive moves. -/
theorem moveCost_add (d : GameData) {S S' S'' : Finset BitString} (h1 : S ⊆ S')
    (h2 : S' ⊆ S'') :
    moveCost d S S'' = moveCost d S S' + moveCost d S' S'' := by
  classical
  unfold moveCost
  have hdisj : Disjoint (S' \ S) (S'' \ S') := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    exact (Finset.mem_sdiff.1 hz2).2 (Finset.mem_sdiff.1 hz1).1
  have hunion : S'' \ S = (S' \ S) ∪ (S'' \ S') := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hz, hzS⟩
      by_cases hz' : z ∈ S'
      · exact Or.inl ⟨hz', hzS⟩
      · exact Or.inr ⟨hz, hz'⟩
    · rintro (⟨hz, hzS⟩ | ⟨hz, hz'⟩)
      · exact ⟨h2 hz, hzS⟩
      · exact ⟨hz, fun h => hz' (h1 h)⟩
  rw [hunion, Finset.sum_union hdisj]

/-- Passing is legal as long as the score of the player to move is within the budget. -/
theorem legalMove_pass (d : GameData) (st : GState) (hX : st.S ⊆ d.X)
    (h : (if st.yesTurn then st.scoreY else st.scoreN) ≤ d.ε) : LegalMove d st st.S := by
  refine ⟨subset_rfl, hX, ?_⟩
  rw [moveCost_self]
  split_ifs at h ⊢ <;> simpa using h

/-- A legal non-passing move strictly enlarges the flipped set. -/
theorem LegalMove.ssubset {d : GameData} {st : GState} {S' : Finset BitString}
    (h : LegalMove d st S') (hne : S' ≠ st.S) : st.S ⊂ S' :=
  Finset.ssubset_iff_subset_ne.2 ⟨h.1, fun h' => hne h'.symm⟩

/-- A legal move stays inside `X`. -/
theorem LegalMove.subset_X {d : GameData} {st : GState} {S' : Finset BitString}
    (h : LegalMove d st S') : S' ⊆ d.X :=
  h.2.1

/-- A safe position for YES has outcome `true`. -/
theorem SafeYes.outcome {d : GameData} {st : GState} (h : SafeYes d st) :
    d.outcome st.S = true := by
  cases h with
  | intro _ _ hout _ _ => exact hout

/-- A safe position for NO has outcome `false`. -/
theorem SafeNo.outcome {d : GameData} {st : GState} (h : SafeNo d st) :
    d.outcome st.S = false := by
  cases h with
  | intro _ _ hout _ _ => exact hout

/-! ### Transfer of safety under a decrease of the current values

During the construction the game of a requirement is evaluated with the *current* values `H*`.
When the values drop on the strings in play without flipping new strings, every future flip
becomes cheaper by at most `δ z = 2^{-h' z} - 2^{-h z}`; charging the opponent the potential
`∑_{z ∈ X \ S} δ z` keeps the position safe for us.  With `d' = d` and `δ = 0` these lemmas
say that safety is monotone in the scores. -/

/-- Under `flipCost d' ≤ flipCost d`, a move is not more expensive in `d'`. -/
theorem moveCost_le_moveCost (d d' : GameData) (h : ∀ z ∈ d.X, flipCost d' z ≤ flipCost d z)
    (S S' : Finset BitString) (hS' : S' ⊆ d.X) : moveCost d' S S' ≤ moveCost d S S' :=
  Finset.sum_le_sum fun z hz => h z (hS' (Finset.sdiff_subset hz))

/-- Under `flipCost d ≤ flipCost d' + δ`, a move is at most `∑ δ` cheaper in `d'`. -/
theorem moveCost_le_moveCost_add (d d' : GameData) (δ : BitString → ℝ)
    (h : ∀ z ∈ d.X, flipCost d z ≤ flipCost d' z + δ z) (S S' : Finset BitString)
    (hS' : S' ⊆ d.X) :
    moveCost d S S' ≤ moveCost d' S S' + ∑ z ∈ S' \ S, δ z := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun z hz => h z (hS' (Finset.sdiff_subset hz))

/-- The potential splits along a move: `∑_{S'∖S} δ + ∑_{X∖S'} δ ≤ ∑_{X∖S} δ`. -/
theorem potential_split (X S S' : Finset BitString) (δ : BitString → ℝ)
    (hδ : ∀ z ∈ X, 0 ≤ δ z) (hSS' : S ⊆ S') (hS'X : S' ⊆ X) :
    ∑ z ∈ S' \ S, δ z + ∑ z ∈ X \ S', δ z ≤ ∑ z ∈ X \ S, δ z := by
  classical
  have hdisj : Disjoint (S' \ S) (X \ S') := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    exact (Finset.mem_sdiff.1 h2).2 (Finset.mem_sdiff.1 h1).1
  rw [← Finset.sum_union hdisj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro z hz
    rw [Finset.mem_union] at hz
    rw [Finset.mem_sdiff]
    rcases hz with hz | hz
    · rw [Finset.mem_sdiff] at hz; exact ⟨hS'X hz.1, hz.2⟩
    · rw [Finset.mem_sdiff] at hz; exact ⟨hz.1, fun h => hz.2 (hSS' h)⟩
  · intro z hz _
    exact hδ z (Finset.mem_sdiff.1 hz).1

/-- The potential decreases along a move. -/
theorem potential_mono (X S S' : Finset BitString) (δ : BitString → ℝ)
    (hδ : ∀ z ∈ X, 0 ≤ δ z) (hSS' : S ⊆ S') :
    ∑ z ∈ X \ S', δ z ≤ ∑ z ∈ X \ S, δ z := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    exact ⟨hz.1, fun h => hz.2 (hSS' h)⟩
  · intro z hz _
    exact hδ z (Finset.mem_sdiff.1 hz).1

/-- Transfer, YES side: if YES is safe in `d` at `st` (NO to move), then YES is safe in `d'` at
`st'` (same position and turn, YES score not larger, NO score larger by at least the potential
of the unflipped strings), when flips are not more expensive and at most `δ` cheaper in `d'` and
the outcomes agree on all positions above `S₀`. -/
theorem safeYes_transfer (d d' : GameData) (hX : d'.X = d.X) (hε : d'.ε = d.ε)
    (δ : BitString → ℝ) (hc0 : ∀ z ∈ d.X, flipCost d' z ≤ flipCost d z)
    (hc1 : ∀ z ∈ d.X, flipCost d z ≤ flipCost d' z + δ z) (S₀ : Finset BitString)
    (hout : ∀ S, S₀ ⊆ S → S ⊆ d.X → d'.outcome S = d.outcome S)
    (st : GState) (hst : SafeYes d st) :
    ∀ st' : GState, st.yesTurn = false → S₀ ⊆ st.S → st.S ⊆ d.X → st'.S = st.S →
      st'.yesTurn = st.yesTurn → st'.scoreY ≤ st.scoreY →
      st.scoreN + ∑ z ∈ d.X \ st.S, δ z ≤ st'.scoreN → SafeYes d' st' := by
  have hδ : ∀ z ∈ d.X, 0 ≤ δ z := fun z hz => by linarith [hc0 z hz, hc1 z hz]
  induction hst with
  | intro st reply hout' hlegal hsafe ih =>
    intro st' hturn h0 hSX hS hT hY hN
    have hturn' : st'.yesTurn = false := hT.trans hturn
    -- a legal NO move in `d'` is legal in `d`
    have hLd : ∀ S', LegalMove d' st' S' → LegalMove d st S' := by
      intro S' hL
      obtain ⟨h1, h2, h3⟩ := hL
      rw [hS] at h1 h3
      rw [hX] at h2
      simp only [hturn', Bool.false_eq_true, ↓reduceIte] at h3
      have hle := moveCost_le_moveCost_add d d' δ hc1 st.S S' h2
      have hsplit := potential_split d.X st.S S' δ hδ h1 h2
      have hpos : 0 ≤ ∑ z ∈ d.X \ S', δ z :=
        Finset.sum_nonneg fun z hz => hδ z (Finset.mem_sdiff.1 hz).1
      refine ⟨h1, h2, ?_⟩
      simp only [hturn, Bool.false_eq_true, ↓reduceIte]
      rw [← hε]; linarith
    refine SafeYes.intro st' reply ?_ ?_ ?_
    · rw [hS, hout _ h0 hSX]; exact hout'
    · intro S' hL hne
      have hL' := hLd S' hL
      have hne' : S' ≠ st.S := hS ▸ hne
      obtain ⟨r1, r2, r3⟩ := hlegal S' hL' hne'
      have hcr := moveCost_le_moveCost d d' hc0 S' (reply S') r2
      refine ⟨r1, hX ▸ r2, ?_⟩
      simp only [applyMove, hturn, hturn', Bool.not_false, Bool.false_eq_true,
        ↓reduceIte] at r3 ⊢
      rw [hε]; linarith
    · intro S' hL hne
      have hL' := hLd S' hL
      have hne' : S' ≠ st.S := hS ▸ hne
      obtain ⟨r1, r2, r3⟩ := hlegal S' hL' hne'
      have h1 := hL'.1
      have h2 := hL'.2.1
      have hcr := moveCost_le_moveCost d d' hc0 S' (reply S') r2
      have hle := moveCost_le_moveCost_add d d' δ hc1 st.S S' h2
      have hsplit := potential_split d.X st.S S' δ hδ h1 h2
      have hmono := potential_mono d.X S' (reply S') δ hδ r1
      refine ih S' hL' hne' _ ?_ ?_ ?_ rfl ?_ ?_ ?_
      · simp [applyMove, hturn]
      · exact h0.trans (h1.trans r1)
      · exact r2
      · simp [applyMove, hT]
      · simp only [applyMove, hturn, hturn', Bool.not_false, Bool.false_eq_true, ↓reduceIte, hS]
        linarith
      · simp only [applyMove, hturn, hturn', Bool.not_false, Bool.false_eq_true, ↓reduceIte, hS]
        linarith

/-- Transfer, NO side: if NO is safe in `d` at `st` (YES to move), then NO is safe at `st'` in the
game `{ d with h₀ := h₀', outcome := outcome' }`, which has the same strings in play and the
same budget but the values `h₀'` and the verdicts `outcome'` (same position and turn, YES score
larger by at least the potential of the unflipped strings, NO score not larger), when flips are
not more expensive and at most `δ` cheaper in the new game and the verdicts agree on all
positions above `S₀`. -/
theorem safeNo_transfer (d : GameData) (h₀' : BitString → ℕ)
    (outcome' : Finset BitString → Bool) (δ : BitString → ℝ)
    (hc0 : ∀ z ∈ d.X,
      flipCost { d with h₀ := h₀', outcome := outcome' } z ≤ flipCost d z)
    (hc1 : ∀ z ∈ d.X,
      flipCost d z ≤ flipCost { d with h₀ := h₀', outcome := outcome' } z + δ z)
    (S₀ : Finset BitString) (hout : ∀ S, S₀ ⊆ S → S ⊆ d.X → outcome' S = d.outcome S)
    (st : GState) (hst : SafeNo d st) :
    ∀ st' : GState, st.yesTurn = true → S₀ ⊆ st.S → st.S ⊆ d.X → st'.S = st.S →
      st'.yesTurn = st.yesTurn → st.scoreY + ∑ z ∈ d.X \ st.S, δ z ≤ st'.scoreY →
      st'.scoreN ≤ st.scoreN → SafeNo { d with h₀ := h₀', outcome := outcome' } st' := by
  generalize hd' : ({ d with h₀ := h₀', outcome := outcome' } : GameData) = d' at hc0 hc1 ⊢
  obtain ⟨hX, hε, hout⟩ : d'.X = d.X ∧ d'.ε = d.ε ∧
      ∀ S, S₀ ⊆ S → S ⊆ d.X → d'.outcome S = d.outcome S := by
    subst hd'
    exact ⟨rfl, rfl, hout⟩
  have hδ : ∀ z ∈ d.X, 0 ≤ δ z := fun z hz => by linarith [hc0 z hz, hc1 z hz]
  induction hst with
  | intro st reply hout' hlegal hsafe ih =>
    intro st' hturn h0 hSX hS hT hY hN
    have hturn' : st'.yesTurn = true := hT.trans hturn
    -- a legal YES move in `d'` is legal in `d`
    have hLd : ∀ S', LegalMove d' st' S' → LegalMove d st S' := by
      intro S' hL
      obtain ⟨h1, h2, h3⟩ := hL
      rw [hS] at h1 h3
      rw [hX] at h2
      simp only [hturn', ↓reduceIte] at h3
      have hle := moveCost_le_moveCost_add d d' δ hc1 st.S S' h2
      have hsplit := potential_split d.X st.S S' δ hδ h1 h2
      have hpos : 0 ≤ ∑ z ∈ d.X \ S', δ z :=
        Finset.sum_nonneg fun z hz => hδ z (Finset.mem_sdiff.1 hz).1
      refine ⟨h1, h2, ?_⟩
      simp only [hturn, ↓reduceIte]
      rw [← hε]; linarith
    refine SafeNo.intro st' reply ?_ ?_ ?_
    · rw [hS, hout _ h0 hSX]; exact hout'
    · intro S' hL hne
      have hL' := hLd S' hL
      have hne' : S' ≠ st.S := hS ▸ hne
      obtain ⟨r1, r2, r3⟩ := hlegal S' hL' hne'
      have hcr := moveCost_le_moveCost d d' hc0 S' (reply S') r2
      refine ⟨r1, hX ▸ r2, ?_⟩
      simp only [applyMove, hturn, hturn', Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] at r3 ⊢
      rw [hε]; linarith
    · intro S' hL hne
      have hL' := hLd S' hL
      have hne' : S' ≠ st.S := hS ▸ hne
      obtain ⟨r1, r2, r3⟩ := hlegal S' hL' hne'
      have h1 := hL'.1
      have h2 := hL'.2.1
      have hcr := moveCost_le_moveCost d d' hc0 S' (reply S') r2
      have hle := moveCost_le_moveCost_add d d' δ hc1 st.S S' h2
      have hsplit := potential_split d.X st.S S' δ hδ h1 h2
      have hmono := potential_mono d.X S' (reply S') δ hδ r1
      refine ih S' hL' hne' _ ?_ ?_ ?_ rfl ?_ ?_ ?_
      · simp [applyMove, hturn]
      · exact h0.trans (h1.trans r1)
      · exact r2
      · simp [applyMove, hT]
      · simp only [applyMove, hturn, hturn', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hS]
        linarith
      · simp only [applyMove, hturn, hturn', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        linarith

/-- Safety for YES is monotone in the scores (lower YES score, higher NO score). -/
theorem SafeYes.mono {d : GameData} {st : GState} (h : SafeYes d st) (st' : GState)
    (hturn : st.yesTurn = false) (hSX : st.S ⊆ d.X) (hS : st'.S = st.S)
    (hT : st'.yesTurn = st.yesTurn) (hY : st'.scoreY ≤ st.scoreY)
    (hN : st.scoreN ≤ st'.scoreN) : SafeYes d st' :=
  safeYes_transfer d d rfl rfl (fun _ => 0) (fun _ _ => le_rfl) (fun _ _ => by simp) st.S
    (fun _ _ _ => rfl) st h st' hturn subset_rfl hSX hS hT hY (by simpa using hN)

/-- Safety for NO is monotone in the scores (higher YES score, lower NO score). -/
theorem SafeNo.mono {d : GameData} {st : GState} (h : SafeNo d st) (st' : GState)
    (hturn : st.yesTurn = true) (hSX : st.S ⊆ d.X) (hS : st'.S = st.S)
    (hT : st'.yesTurn = st.yesTurn) (hY : st.scoreY ≤ st'.scoreY)
    (hN : st'.scoreN ≤ st.scoreN) : SafeNo d st' :=
  safeNo_transfer d d.h₀ d.outcome (fun _ => 0) (fun _ _ => le_rfl) (fun _ _ => by simp)
    st.S (fun _ _ _ => rfl) st h st' hturn subset_rfl hSX hS hT (by simpa using hY) hN

/-- A non-passing move decreases the number of unflipped strings. -/
theorem card_sdiff_lt {X S S' : Finset BitString} (h1 : S ⊆ S') (h2 : S' ⊆ X) (hne : S' ≠ S) :
    (X \ S').card < (X \ S).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.sdiff_subset_sdiff (Finset.Subset.refl _) h1, fun heq => hne ?_⟩
  apply Finset.Subset.antisymm _ h1
  intro z hz
  by_contra hzS
  have hz' : z ∈ X \ S := Finset.mem_sdiff.2 ⟨h2 hz, hzS⟩
  rw [← heq] at hz'
  exact (Finset.mem_sdiff.1 hz').2 hz

/-- The key step of determinacy: if at `P` (NO to move) YES has no move — from the same
position and scores with YES to move — to a position safe for YES, then NO has a move (possibly
a pass) to a position safe for NO.  Strong induction on the number of unflipped strings. -/
theorem exists_safeNo_of_dom (d : GameData) (n : ℕ) : ∀ P : GState, (d.X \ P.S).card = n →
    P.yesTurn = false → P.S ⊆ d.X → P.scoreY ≤ d.ε → P.scoreN ≤ d.ε →
    (∀ T, LegalMove d ⟨P.S, P.scoreY, P.scoreN, true⟩ T →
      ¬ SafeYes d (applyMove d ⟨P.S, P.scoreY, P.scoreN, true⟩ T)) →
    ∃ S₂, LegalMove d P S₂ ∧ SafeNo d (applyMove d P S₂) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hturn hPX hPY hPN hdom
  have hAP : ∀ T, applyMove d P T = ⟨T, P.scoreY, P.scoreN + moveCost d P.S T, true⟩ := by
    intro T; simp [applyMove, hturn]
  have hAY : ∀ (S T : Finset BitString) (y z : ℝ),
      applyMove d ⟨S, y, z, true⟩ T = ⟨T, y + moveCost d S T, z, false⟩ := by
    intro S T y z; simp [applyMove]
  by_cases hout : d.outcome P.S = false
  · refine ⟨P.S, legalMove_pass d P hPX (by simp [hturn, hPN]), ?_⟩
    rw [hAP, moveCost_self, add_zero]
    have hex : ∀ S'', LegalMove d ⟨P.S, P.scoreY, P.scoreN, true⟩ S'' → S'' ≠ P.S →
        ∃ S₃, LegalMove d (applyMove d ⟨P.S, P.scoreY, P.scoreN, true⟩ S'') S₃ ∧
          SafeNo d (applyMove d (applyMove d ⟨P.S, P.scoreY, P.scoreN, true⟩ S'') S₃) := by
      intro S'' hL hne
      obtain ⟨h1, h2, h3⟩ := hL
      rw [ite_eq_left rfl] at h3
      dsimp only at h1 h3
      rw [hAY]
      refine ih _ ((card_sdiff_lt h1 h2 hne).trans_eq hn) _ rfl rfl h2 h3 hPN ?_
      intro T hT hsafe
      obtain ⟨t1, t2, t3⟩ := hT
      rw [ite_eq_left rfl] at t3
      dsimp only at t1 t3
      have hadd := moveCost_add d h1 t1
      refine hdom T ⟨h1.trans t1, t2, ?_⟩ ?_
      · rw [ite_eq_left rfl]; dsimp only; rw [hadd]; linarith
      · rw [hAY] at hsafe ⊢
        refine SafeYes.mono hsafe _ rfl t2 rfl rfl ?_ le_rfl
        dsimp only; rw [hadd]; linarith
    refine SafeNo.intro _ (fun S'' => if h : ∃ S₃,
        LegalMove d (applyMove d ⟨P.S, P.scoreY, P.scoreN, true⟩ S'') S₃ ∧
          SafeNo d (applyMove d (applyMove d ⟨P.S, P.scoreY, P.scoreN, true⟩ S'') S₃)
        then Classical.choose h else S'') hout ?_ ?_
    · intro S'' hL hne
      rw [dite_eq_left (hex S'' hL hne)]
      exact (Classical.choose_spec (hex S'' hL hne)).1
    · intro S'' hL hne
      rw [dite_eq_left (hex S'' hL hne)]
      exact (Classical.choose_spec (hex S'' hL hne)).2
  · have hout' : d.outcome P.S = true := by
      cases h : d.outcome P.S
      · exact absurd h hout
      · rfl
    have hnot : ¬ SafeYes d P := by
      intro hs
      refine hdom P.S (legalMove_pass d _ hPX (by simp [hPY])) ?_
      rw [hAY, moveCost_self, add_zero]
      exact SafeYes.mono hs _ hturn hPX rfl hturn.symm le_rfl le_rfl
    have hbad : ∃ S', LegalMove d P S' ∧ S' ≠ P.S ∧
        ∀ R, LegalMove d (applyMove d P S') R →
          ¬ SafeYes d (applyMove d (applyMove d P S') R) := by
      by_contra hcon
      push Not at hcon
      apply hnot
      refine SafeYes.intro P (fun S' => if h : ∃ R, LegalMove d (applyMove d P S') R ∧
          SafeYes d (applyMove d (applyMove d P S') R) then Classical.choose h else S')
        hout' ?_ ?_
      · intro S' hL hne
        have hh := hcon S' hL hne
        rw [dite_eq_left hh]; exact (Classical.choose_spec hh).1
      · intro S' hL hne
        have hh := hcon S' hL hne
        rw [dite_eq_left hh]; exact (Classical.choose_spec hh).2
    obtain ⟨S', ⟨h1, h2, h3⟩, hne, hS'⟩ := hbad
    rw [ite_eq_right (by rw [hturn]; exact Bool.false_ne_true)] at h3
    obtain ⟨S₃, ⟨g1, g2, g3⟩, hsafe⟩ := ih _ ((card_sdiff_lt h1 h2 hne).trans_eq hn)
      ⟨S', P.scoreY, P.scoreN + moveCost d P.S S', false⟩ rfl rfl h2 hPY h3
      (fun T hT hs => hS' T (by rw [hAP]; exact hT) (by rw [hAP]; exact hs))
    rw [ite_eq_right Bool.false_ne_true] at g3
    dsimp only at g1 g3
    have hadd := moveCost_add d h1 g1
    refine ⟨S₃, ⟨h1.trans g1, g2, ?_⟩, ?_⟩
    · rw [ite_eq_right (by rw [hturn]; exact Bool.false_ne_true), hadd]; linarith
    · rw [hAP]
      have hA3 : applyMove d ⟨S', P.scoreY, P.scoreN + moveCost d P.S S', false⟩ S₃ =
          ⟨S₃, P.scoreY, P.scoreN + moveCost d P.S S' + moveCost d S' S₃, true⟩ := by
        simp [applyMove]
      rw [hA3] at hsafe
      refine SafeNo.mono hsafe _ rfl g2 rfl rfl le_rfl ?_
      dsimp only; rw [hadd]; linarith

/-- Determinacy: if YES has no first move to a safe position, then NO can answer every first
move of YES by a move to a position safe for NO.  Proof plan: strong induction on
`(X \ S).card` of the claim "if YES has no move (from the position with YES to move, same scores)
to a `SafeYes` position, then NO has a move to a `SafeNo` position"; if the current outcome is
`false`, NO passes and answers each non-passing YES move by the induction hypothesis (YES moves
from there are YES moves from the earlier position, by `moveCost_add`); if it is `true`, take the
non-passing NO move witnessing `¬ SafeYes`, apply the induction hypothesis after a YES pass, and
merge the two NO moves into one (`moveCost_add`). -/
theorem noWinsInit_of_not_yesWinsInit (d : GameData) (h : ¬ YesWinsInit d) : NoWinsInit d := by
  intro S₁ hL
  obtain ⟨h1, h2, h3⟩ := hL
  have h3' : 0 + moveCost d ∅ S₁ ≤ d.ε := h3
  have hc := moveCost_nonneg d ∅ S₁
  have hP : applyMove d GState.init S₁ = ⟨S₁, 0 + moveCost d ∅ S₁, 0, false⟩ := by
    simp [applyMove, GState.init]
  rw [hP]
  refine exists_safeNo_of_dom d _ _ rfl rfl h2 h3' (by linarith) ?_
  intro T hT hs
  obtain ⟨t1, t2, t3⟩ := hT
  rw [ite_eq_left rfl] at t3
  dsimp only at t1 t3
  have hadd := moveCost_add d (Finset.empty_subset S₁) t1
  apply h
  refine ⟨T, ⟨Finset.empty_subset T, t2, ?_⟩, ?_⟩
  · change 0 + moveCost d ∅ T ≤ d.ε
    rw [hadd]; linarith
  · have hA : applyMove d GState.init T = ⟨T, 0 + moveCost d ∅ T, 0, false⟩ := by
      simp [applyMove, GState.init]
    have hA' : applyMove d ⟨S₁, 0 + moveCost d ∅ S₁, 0, true⟩ T =
        ⟨T, 0 + moveCost d ∅ S₁ + moveCost d S₁ T, 0, false⟩ := by
      simp [applyMove]
    rw [hA]
    rw [hA'] at hs
    refine SafeYes.mono hs _ rfl t2 rfl rfl ?_ le_rfl
    dsimp only; rw [hadd]; linarith

/-! ### Symmetries of the game

Negating the outcome exchanges the roles of the two players (`safeNo_iff_safeYes_dual`), and
exchanging the two scores together with the turn flag does not change the game
(`safeYes_swap`). -/

/-- The dual game: the outcome negated (the roles of YES and NO exchanged). -/
def GameData.dual (d : GameData) : GameData := { d with outcome := fun S => !d.outcome S }

/-- The dual game has the same legal moves as the game itself: negating the outcome changes
neither the strings in play nor the budget nor the costs. -/
theorem legalMove_dual (d : GameData) (st : GState) (S' : Finset BitString) :
    LegalMove d.dual st S' ↔ LegalMove d st S' :=
  Iff.rfl

/-- Making a move in the dual game gives the same state as making it in the game itself. -/
theorem applyMove_dual (d : GameData) (st : GState) (S' : Finset BitString) :
    applyMove d.dual st S' = applyMove d st S' :=
  rfl

/-- `NO` is safe in `d` iff `YES` is safe in the dual game (same state). -/
theorem safeNo_iff_safeYes_dual (d : GameData) (st : GState) :
    SafeNo d st ↔ SafeYes d.dual st := by
  constructor
  · intro h
    induction h with
    | intro st reply hout hlegal _ ih =>
      refine SafeYes.intro st reply ?_ ?_ ?_
      · change (!d.outcome st.S) = true
        simp [hout]
      · intro S' hL hne
        rw [applyMove_dual, legalMove_dual]
        exact hlegal S' ((legalMove_dual d st S').1 hL) hne
      · intro S' hL hne
        simp only [applyMove_dual]
        exact ih S' ((legalMove_dual d st S').1 hL) hne
  · intro h
    induction h with
    | intro st reply hout hlegal _ ih =>
      refine SafeNo.intro st reply ?_ ?_ ?_
      · have hout' : (!d.outcome st.S) = true := hout
        simpa using hout'
      · intro S' hL hne
        have h' := hlegal S' ((legalMove_dual d st S').2 hL) hne
        rwa [applyMove_dual, legalMove_dual] at h'
      · intro S' hL hne
        have h' := ih S' ((legalMove_dual d st S').2 hL) hne
        simpa only [applyMove_dual] using h'

/-- Exchanging the two scores together with the turn flag does not change the game. -/
theorem legalMove_swap (d : GameData) (S : Finset BitString) (α β : ℝ) (t : Bool)
    (S' : Finset BitString) :
    LegalMove d ⟨S, β, α, !t⟩ S' ↔ LegalMove d ⟨S, α, β, t⟩ S' := by
  cases t <;> exact Iff.rfl

/-- Making a move from the state with the two scores and the turn flag exchanged gives the
state obtained from the result of the same move by exchanging the two scores and the turn
flag. -/
theorem applyMove_swap (d : GameData) (S : Finset BitString) (α β : ℝ) (t : Bool)
    (S' : Finset BitString) :
    applyMove d ⟨S, β, α, !t⟩ S' =
      ⟨(applyMove d ⟨S, α, β, t⟩ S').S, (applyMove d ⟨S, α, β, t⟩ S').scoreN,
        (applyMove d ⟨S, α, β, t⟩ S').scoreY,
        !(applyMove d ⟨S, α, β, t⟩ S').yesTurn⟩ := by
  cases t <;> rfl

/-- One direction of `safeYes_swap`, for an arbitrary state: exchanging the two scores together
with the turn flag preserves safety for YES. -/
theorem safeYes_swap_aux (d : GameData) (st : GState) (h : SafeYes d st) :
    SafeYes d ⟨st.S, st.scoreN, st.scoreY, !st.yesTurn⟩ := by
  induction h with
  | intro st reply hout hlegal _ ih =>
    obtain ⟨S, α, β, t⟩ := st
    refine SafeYes.intro _ reply hout ?_ ?_
    · intro S' hL hne
      rw [applyMove_swap]
      exact (legalMove_swap d _ _ _ _ _).2 (hlegal S' ((legalMove_swap d S α β t S').1 hL) hne)
    · intro S' hL hne
      rw [applyMove_swap, applyMove_swap]
      exact ih S' ((legalMove_swap d S α β t S').1 hL) hne

/-- Exchanging the two scores together with the turn flag does not change whether a position is
safe for YES: `SafeYes d ⟨S, β, α, !t⟩ ↔ SafeYes d ⟨S, α, β, t⟩`. -/
theorem safeYes_swap (d : GameData) (S : Finset BitString) (α β : ℝ) (t : Bool) :
    SafeYes d ⟨S, β, α, !t⟩ ↔ SafeYes d ⟨S, α, β, t⟩ := by
  constructor
  · intro h
    have h' := safeYes_swap_aux d ⟨S, β, α, !t⟩ h
    cases t <;> exact h'
  · intro h
    exact safeYes_swap_aux d ⟨S, α, β, t⟩ h

/-! ### A guarded variant of the game and hardwired tables -/

/-- The game `gameOf` with a guard: for `phi = true` it is `gameOf`; for `phi = false` the
outcome is the constant `dflt` (used to switch off the requirements for machines outside the
family under study). -/
noncomputable def gameOfB (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (phi dflt : Bool) : GameData :=
  { X := X, h₀ := h, ε := ε,
    outcome := fun S => bif phi then
      (by classical exact decide (ClockedAccepts c e (oracleOf h S) x)) else dflt }

/-- With the guard `true`, the guarded game `gameOfB` is the game `gameOf`. -/
theorem gameOfB_true (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (dflt : Bool) :
    gameOfB c e x h ε X true dflt = gameOf c e x h ε X := rfl

/-- With the guard `false`, the outcome of the guarded game `gameOfB` is the constant `dflt` at
every position. -/
theorem gameOfB_false_outcome (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ)
    (ε : ℝ) (X : Finset BitString) (dflt : Bool) (S : Finset BitString) :
    (gameOfB c e x h ε X false dflt).outcome S = dflt := rfl

/-- A hardwired modification table: finitely many strings with prescribed values. -/
structure Table where
  /-- The modified strings. -/
  dom : Finset BitString
  /-- Their values. -/
  value : BitString → ℕ

/-- The function `2|z| + 6` modified by a table. -/
def Table.fn (T : Table) (z : BitString) : ℕ :=
  if z ∈ T.dom then T.value z else 2 * z.length + 6

end Kolmogorov.RandomStrings
