/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Effective.Codes
import KolmogorovMathlib.RandomStrings.Effective.Configs
import KolmogorovMathlib.RandomStrings.Effective.GameValues

/-!
# Effective machine-level computations

Concrete codes for oracle machines and their configurations, so that the computations used by
the stage construction are primitive recursive:

* `encodeCode` / `decodeCode`: a total decoding `ℕ → OTMCode` with a right inverse, and the
  computable surjection `γ₀ : ℕ → OTMCode × ℕ`;
* `CC`: finite codes of configurations (zipper tape, head position `hp - hn`, buffer), the
  representation relation `Rep`, and the primitive recursive step / run functions `stepC`,
  `runC` (and their versions `stepCode`, `runCode` on `ℕ`-codes) simulating `step` / `run` with a
  finite oracle `{z | z ∈ ans}`;
* `clockedOutcomeT`: the verdict within `T` steps of a coded machine with a finite oracle
  (`clockedOutcome`: the polynomial clock `T = clock e |x|`);
* `queryListCodeT`: the list of all strings that a coded machine can query within `T` steps
  under some oracle (exploration of all consistent answer sequences; `queryListCode`: the
  polynomial clock).

The development lives in the modules `KolmogorovMathlib.RandomStrings.Effective.*`: codes of
machines (`Codes`), codes of configurations and their runs (`Configs`), and computable game
values (`GameValues`).  This module decides `SafeYes` and `SafeNo` at arbitrary finite states.
-/

namespace Kolmogorov.RandomStrings

/-! ## Deciding `SafeYes`/`SafeNo` at arbitrary finite states -/

/-- `o` is the floor of `r` as an optional natural: `some ⌊r⌋₊` if `0 ≤ r`, `none` if `r < 0`. -/
def IsFloorO (r : ℝ) (o : Option ℕ) : Prop :=
  ∀ k : ℕ, ((k : ℝ) ≤ r ↔ ∃ E, o = some E ∧ k ≤ E)

/-- A finite game state relative to a game `g : GD`: the position (a list of strings), the
floors `⌊(ε - scoreY) * 2 ^ g.N⌋`, `⌊(ε - scoreN) * 2 ^ g.N⌋` of the scaled remaining budgets
(optional naturals, `none` if negative) and the turn flag. -/
abbrev GSt : Type := List BitString × Option ℕ × Option ℕ × Bool

/-- Budget test: `okB (some E) k ↔ k ≤ E`; `okB none k = false`. -/
def okB (E : Option ℕ) (k : ℕ) : Bool :=
  match E with
  | none => false
  | some E => decide (k ≤ E)

/-- The outcome of a position in the game (`neg = false`) or in the dual game (`neg = true`). -/
def GD.outN (g : GD) (neg : Bool) (S : List BitString) : Bool :=
  bif neg then !g.outC S else g.outC S

/-- One level of the evaluation of `SafeYes` (NO to move) with remaining scaled budgets `EY`, `EN`
measured from the scores at the root; `u = (S, a, b)` records the scaled scores spent since. -/
def GD.F' (g : GD) (neg : Bool) (EY EN : Option ℕ) (u : List BitString × ℕ × ℕ)
    (f : List BitString × ℕ × ℕ → Bool) : Bool :=
  g.outN neg u.1 && allB (allSub g.Xd) fun S' =>
    !(subB u.1 S' && okB EN (u.2.2 + g.mc u.1 S')) || subB S' u.1 ||
      anyB (allSub g.Xd) fun R =>
        subB S' R && okB EY (u.2.1 + g.mc S' R) &&
          f (R, u.2.1 + g.mc S' R, u.2.2 + g.mc u.1 S')

/-- The box of states for the budgets `EY`, `EN`. -/
def GD.U' (g : GD) (EY EN : Option ℕ) : List (List BitString × ℕ × ℕ) :=
  (allSub g.Xd).flatMap fun S => (List.range (EY.getD 0 + 1)).flatMap fun a =>
    (List.range (EN.getD 0 + 1)).map fun b => (S, a, b)

/-- The table of values at level `n` on the box `U'`. -/
def GD.tab' (g : GD) (neg : Bool) (EY EN : Option ℕ) : ℕ → Tbl
  | 0 => (g.U' EY EN).map fun u => (u, g.F' neg EY EN u fun v => lookupT v [])
  | n + 1 => (g.U' EY EN).map fun u => (u, g.F' neg EY EN u fun v => lookupT v (g.tab' neg EY EN n))

/-- The evaluation of `SafeYes` with fuel `n` (in the game or its dual): the value at `v` in the
table `g.tab' neg EY EN n`. -/
def GD.evS' (g : GD) (neg : Bool) (EY EN : Option ℕ) (n : ℕ) (v : List BitString × ℕ × ℕ) : Bool :=
  lookupT v (g.tab' neg EY EN n)

/-- The canonical position of a list of strings: the strings in play that belong to it. -/
def GD.canon (g : GD) (R : List BitString) : List BitString :=
  g.Xd.foldr (fun z acc => bif memStr z R then z :: acc else acc) []

/-- Decision of `SafeYes` at a finite state (the turn flag swaps the two budgets). -/
def safeYesC (g : GD) (u : GSt) : Bool :=
  bif u.2.2.2 then g.evS' false u.2.2.1 u.2.1 g.Xd.length (g.canon u.1, 0, 0)
  else g.evS' false u.2.1 u.2.2.1 g.Xd.length (g.canon u.1, 0, 0)

/-- Decision of `SafeNo` at a finite state (via the dual game). -/
def safeNoC (g : GD) (u : GSt) : Bool :=
  bif u.2.2.2 then g.evS' true u.2.2.1 u.2.1 g.Xd.length (g.canon u.1, 0, 0)
  else g.evS' true u.2.1 u.2.2.1 g.Xd.length (g.canon u.1, 0, 0)

/-! ### Correctness -/

/-- If `o` is the floor of `r` (`IsFloorO r o`), then the budget test `okB o k` succeeds exactly
when `(k : ℝ) ≤ r`. -/
theorem okB_iff_of_floor {r : ℝ} {o : Option ℕ} (h : IsFloorO r o) (k : ℕ) :
    okB o k = true ↔ (k : ℝ) ≤ r := by
  rw [h k]
  cases o with
  | none => simp [okB]
  | some E => simp [okB]

/-- A successful budget test `okB o k` gives `k ≤ o.getD 0`: the budget `o`, read as `0` if it is
`none`, bounds `k`. -/
theorem le_getD_of_okB {o : Option ℕ} {k : ℕ} (h : okB o k = true) : k ≤ o.getD 0 := by
  cases o with
  | none => simp [okB] at h
  | some E => simpa [okB] using h

/-- Clearing the denominator of a scaled score: `β + k / 2 ^ N ≤ ε` holds iff
`k ≤ (ε - β) * 2 ^ N`. -/
theorem add_div_le_iff (ε β : ℝ) (N k : ℕ) :
    β + (k : ℝ) / 2 ^ N ≤ ε ↔ (k : ℝ) ≤ (ε - β) * 2 ^ N := by
  rw [← le_sub_iff_add_le', div_le_iff₀ (by positivity)]

/-- The game or its dual. -/
noncomputable def GD.dd (g : GD) (neg : Bool) : GameData := bif neg then g.game.dual else g.game

/-- The game `g.dd neg` (the game or its dual) has the same legal moves as `g.game`. -/
theorem GD.dd_legal (g : GD) (neg : Bool) (st : GState) (T : Finset BitString) :
    LegalMove (g.dd neg) st T ↔ LegalMove g.game st T := by
  cases neg <;> exact Iff.rfl

/-- A move has the same effect in `g.dd neg` as in `g.game`: the dual game differs from the game
only in its outcome. -/
theorem GD.dd_apply (g : GD) (neg : Bool) (st : GState) (T : Finset BitString) :
    applyMove (g.dd neg) st T = applyMove g.game st T := by
  cases neg <;> rfl

/-- The game `g.dd neg` is played on the same strings as `g.game`. -/
theorem GD.dd_X (g : GD) (neg : Bool) : (g.dd neg).X = g.game.X := by
  cases neg <;> rfl

/-- The computable outcome `g.outN neg S` is the outcome of the game `g.dd neg` (the game or its
dual) at the position `S.toFinset`. -/
theorem GD.outN_eq (g : GD) (neg : Bool) (S : List BitString) :
    g.outN neg S = (g.dd neg).outcome S.toFinset := by
  cases neg
  · exact g.outC_eq S
  · change (!g.outC S) = !g.game.outcome S.toFinset
    rw [g.outC_eq]

/-- The state `(S, a, b)` relative to the root scores `α, β` (NO to move). -/
noncomputable def GD.st' (g : GD) (α β : ℝ) (u : List BitString × ℕ × ℕ) : GState :=
  ⟨u.1.toFinset, α + (u.2.1 : ℝ) / 2 ^ g.N, β + (u.2.2 : ℝ) / 2 ^ g.N, false⟩

/-- A state `(S, a, b)` is in the box `g.U' EY EN` iff `S` is a sublist of the strings in play and
the scaled scores satisfy `a ≤ EY.getD 0` and `b ≤ EN.getD 0`. -/
theorem GD.mem_U' (g : GD) (EY EN : Option ℕ) (S : List BitString) (a b : ℕ) :
    (S, a, b) ∈ g.U' EY EN ↔ S ∈ allSub g.Xd ∧ a ≤ EY.getD 0 ∧ b ≤ EN.getD 0 := by
  simp only [GD.U', List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨S₀, hS₀, a₀, ha₀, b₀, hb₀, rfl, rfl, rfl⟩
    exact ⟨hS₀, by omega, by omega⟩
  · rintro ⟨hS, ha, hb⟩
    exact ⟨S, hS, a, by omega, b, by omega, rfl, rfl, rfl⟩

/-- A NO move from the state `g.st' α β u` to a sublist `S'` of the strings in play is legal iff
`S'` contains the current position and the scaled cost `g.mc u.1 S'`, added to the scaled score
`u.2.2` of NO, fits in the budget `EN`, the floor of the scaled remaining budget of NO. -/
theorem GD.legal_no' (g : GD) (EN : Option ℕ) (α β : ℝ)
    (hN : IsFloorO ((g.game.ε - β) * 2 ^ g.N) EN) (u : List BitString × ℕ × ℕ) (S' : List BitString)
    (hS' : S' ∈ allSub g.Xd) :
    LegalMove g.game (g.st' α β u) S'.toFinset ↔
      subB u.1 S' = true ∧ okB EN (u.2.2 + g.mc u.1 S') = true := by
  have hX := g.mem_X_of_allSub hS'
  have hc := GD.moveCost_eq g u.1 S' (g.nodup_of_allSub hS') hX
  change (u.1.toFinset ⊆ S'.toFinset ∧ S'.toFinset ⊆ g.X.toFinset ∧
    (if false = true then
      α + (u.2.1 : ℝ) / 2 ^ g.N + moveCost g.game u.1.toFinset S'.toFinset ≤ g.game.ε
      else β + (u.2.2 : ℝ) / 2 ^ g.N + moveCost g.game u.1.toFinset S'.toFinset ≤ g.game.ε)) ↔ _
  rw [ite_eq_right Bool.false_ne_true, hc, okB_iff_of_floor hN, subB_iff, ← add_div_le_iff]
  push_cast
  rw [add_div, ← add_assoc]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨fun z hz => List.mem_toFinset.1 (h1 (List.mem_toFinset.2 hz)), h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨fun z hz => List.mem_toFinset.2 (h1 z (List.mem_toFinset.1 hz)), fun z hz => ?_, h3⟩
    rw [List.mem_toFinset] at hz ⊢
    exact hX z hz

/-- A YES move from a state with position `S'` and YES score `α + a / 2 ^ g.N` to a sublist `R`
of the strings in play is legal iff `R` contains `S'` and the scaled cost `g.mc S' R`, added to
`a`, fits in the budget `EY`, the floor of the scaled remaining budget of YES. -/
theorem GD.legal_yes' (g : GD) (EY : Option ℕ) (α y : ℝ)
    (hY : IsFloorO ((g.game.ε - α) * 2 ^ g.N) EY) (S' R : List BitString) (a : ℕ)
    (hR : R ∈ allSub g.Xd) :
    LegalMove g.game ⟨S'.toFinset, α + (a : ℝ) / 2 ^ g.N, y, true⟩ R.toFinset ↔
      subB S' R = true ∧ okB EY (a + g.mc S' R) = true := by
  have hX := g.mem_X_of_allSub hR
  have hc := GD.moveCost_eq g S' R (g.nodup_of_allSub hR) hX
  change (S'.toFinset ⊆ R.toFinset ∧ R.toFinset ⊆ g.X.toFinset ∧
    (if true = true then
      α + (a : ℝ) / 2 ^ g.N + moveCost g.game S'.toFinset R.toFinset ≤ g.game.ε
      else y + moveCost g.game S'.toFinset R.toFinset ≤ g.game.ε)) ↔ _
  rw [ite_eq_left rfl, hc, okB_iff_of_floor hY, subB_iff, ← add_div_le_iff]
  push_cast
  rw [add_div, ← add_assoc]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨fun z hz => List.mem_toFinset.1 (h1 (List.mem_toFinset.2 hz)), h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨fun z hz => List.mem_toFinset.2 (h1 z (List.mem_toFinset.1 hz)), fun z hz => ?_, h3⟩
    rw [List.mem_toFinset] at hz ⊢
    exact hX z hz

/-- Playing the NO move `S'` in the state `g.st' α β u` moves the position to `S'`, adds the scaled
cost `g.mc u.1 S'` to the score of NO and gives the turn to YES. -/
theorem GD.apply_no' (g : GD) (α β : ℝ) (u : List BitString × ℕ × ℕ) (S' : List BitString)
    (hS' : S' ∈ allSub g.Xd) :
    applyMove g.game (g.st' α β u) S'.toFinset =
      ⟨S'.toFinset, α + (u.2.1 : ℝ) / 2 ^ g.N,
        β + ((u.2.2 + g.mc u.1 S' : ℕ) : ℝ) / 2 ^ g.N, true⟩ := by
  have hc := GD.moveCost_eq g u.1 S' (g.nodup_of_allSub hS') (g.mem_X_of_allSub hS')
  change (⟨S'.toFinset, α + (u.2.1 : ℝ) / 2 ^ g.N,
    β + (u.2.2 : ℝ) / 2 ^ g.N + moveCost g.game u.1.toFinset S'.toFinset, true⟩ : GState) = _
  rw [hc]
  congr 1
  push_cast
  ring

/-- Playing the YES move `R` at the position `S'`, with YES score `α + a / 2 ^ g.N`, moves the
position to `R`, adds the scaled cost `g.mc S' R` to the score of YES and gives the turn to NO. -/
theorem GD.apply_yes' (g : GD) (α y : ℝ) (S' R : List BitString) (a : ℕ) (hR : R ∈ allSub g.Xd) :
    applyMove g.game ⟨S'.toFinset, α + (a : ℝ) / 2 ^ g.N, y, true⟩ R.toFinset =
      ⟨R.toFinset, α + ((a + g.mc S' R : ℕ) : ℝ) / 2 ^ g.N, y, false⟩ := by
  have hc := GD.moveCost_eq g S' R (g.nodup_of_allSub hR) (g.mem_X_of_allSub hR)
  change (⟨R.toFinset, α + (a : ℝ) / 2 ^ g.N + moveCost g.game S'.toFinset R.toFinset, y,
    false⟩ : GState) = _
  rw [hc]
  congr 1
  push_cast
  ring

/-- **Correctness of one level of the generalized evaluation.** If `f` decides the property `Pn`
of the states of the box `g.U' EY EN`, then `g.F' neg EY EN u f` holds iff, in the game `g.dd neg`,
the outcome of the position of `g.st' α β u` is `true` and every legal non-passing move of NO has
a legal answer of YES to a state with the property `Pn`. -/
theorem GD.F'_iff (g : GD) (neg : Bool) (EY EN : Option ℕ) (α β : ℝ)
    (hY : IsFloorO ((g.game.ε - α) * 2 ^ g.N) EY) (hN : IsFloorO ((g.game.ε - β) * 2 ^ g.N) EN)
    (u : List BitString × ℕ × ℕ) (hu : u ∈ g.U' EY EN)
    (f : List BitString × ℕ × ℕ → Bool) (Pn : GState → Prop)
    (hf : ∀ v ∈ g.U' EY EN, f v = true ↔ Pn (g.st' α β v)) :
    g.F' neg EY EN u f = true ↔ ((g.dd neg).outcome (g.st' α β u).S = true ∧
      ∀ T, LegalMove (g.dd neg) (g.st' α β u) T → T ≠ (g.st' α β u).S →
        ∃ Rf, LegalMove (g.dd neg) (applyMove (g.dd neg) (g.st' α β u) T) Rf ∧
          Pn (applyMove (g.dd neg) (applyMove (g.dd neg) (g.st' α β u) T) Rf)) := by
  obtain ⟨S, a, b⟩ := u
  obtain ⟨hS, ha, hb⟩ := (g.mem_U' EY EN S a b).1 hu
  have hsubX : ∀ T : Finset BitString, T ⊆ g.game.X → ∀ z ∈ T, z ∈ g.Xd := by
    intro T hT z hz
    have := hT hz
    rw [show g.game.X = g.X.toFinset from rfl, List.mem_toFinset] at this
    exact (g.mem_Xd z).2 this
  have hst : (g.st' α β (S, a, b)).S = S.toFinset := rfl
  simp only [GD.dd_legal, GD.dd_apply]
  simp only [GD.F', Bool.and_eq_true, allB_iff]
  rw [GD.outN_eq, hst]
  apply and_congr_right
  intro _
  constructor
  · intro hall T hT hne
    obtain ⟨S', hS', rfl⟩ := exists_allSub g.Xd T (hsubX T hT.2.1)
    have hleg : subB S S' = true ∧ okB EN (b + g.mc S S') = true :=
      (g.legal_no' EN α β hN (S, a, b) S' hS').1 hT
    have hP := hall S' hS'
    rw [hleg.1, hleg.2] at hP
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hP
    rcases hP with h2 | h2
    · exfalso
      apply hne
      apply Finset.Subset.antisymm
      · intro z hz
        rw [List.mem_toFinset] at hz ⊢
        exact (subB_iff _ _).1 h2 z hz
      · intro z hz
        rw [List.mem_toFinset] at hz ⊢
        exact (subB_iff _ _).1 hleg.1 z hz
    · obtain ⟨R, hR, hRt⟩ := (anyB_iff _ _).1 h2
      simp only [Bool.and_eq_true] at hRt
      obtain ⟨⟨hsub, hle⟩, hfv⟩ := hRt
      refine ⟨R.toFinset, ?_, ?_⟩
      · rw [g.apply_no' α β (S, a, b) S' hS']
        exact (g.legal_yes' EY α _ hY S' R a hR).2 ⟨hsub, hle⟩
      · rw [g.apply_no' α β (S, a, b) S' hS', g.apply_yes' α _ S' R a hR]
        have hv : (R, a + g.mc S' R, b + g.mc S S') ∈ g.U' EY EN :=
          (g.mem_U' _ _ _ _ _).2 ⟨hR, le_getD_of_okB hle, le_getD_of_okB hleg.2⟩
        exact (hf _ hv).1 hfv
  · intro hall S' hS'
    by_cases hg1 : subB S S' = true
    · by_cases hg2 : okB EN (b + g.mc S S') = true
      · rw [hg1, hg2]
        simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true]
        by_cases hback : subB S' S = true
        · exact Or.inl hback
        · right
          have hT := (g.legal_no' EN α β hN (S, a, b) S' hS').2 ⟨hg1, hg2⟩
          have hne : S'.toFinset ≠ S.toFinset := by
            intro heq
            apply hback
            rw [subB_iff]
            intro z hz
            have : z ∈ S'.toFinset := List.mem_toFinset.2 hz
            rw [heq] at this
            exact List.mem_toFinset.1 this
          obtain ⟨Rf, hRf, hPn⟩ := hall _ hT hne
          rw [g.apply_no' α β (S, a, b) S' hS'] at hRf hPn
          obtain ⟨R, hR, rfl⟩ := exists_allSub g.Xd Rf (hsubX Rf hRf.2.1)
          obtain ⟨hsub, hle⟩ := (g.legal_yes' EY α _ hY S' R a hR).1 hRf
          rw [g.apply_yes' α _ S' R a hR] at hPn
          have hv : (R, a + g.mc S' R, b + g.mc S S') ∈ g.U' EY EN :=
            (g.mem_U' _ _ _ _ _).2 ⟨hR, le_getD_of_okB hle, le_getD_of_okB hg2⟩
          rw [anyB_iff]
          refine ⟨R, hR, ?_⟩
          rw [hsub, hle, (hf _ hv).2 hPn]
          rfl
      · have hf2 : okB EN (b + g.mc S S') = false := by simpa using hg2
        rw [hg1, hf2]
        rfl
    · have h0 : subB S S' = false := by simpa using hg1
      rw [h0]
      rfl

/-- On the box `g.U' EY EN`, the evaluation with fuel `n + 1` is one level `GD.F'` applied to the
evaluation with fuel `n`. -/
theorem GD.evS'_succ (g : GD) (neg : Bool) (EY EN : Option ℕ) (n : ℕ) (u : List BitString × ℕ × ℕ)
    (hu : u ∈ g.U' EY EN) : g.evS' neg EY EN (n + 1) u = g.F' neg EY EN u (g.evS' neg EY EN n) := by
  unfold GD.evS'
  rw [GD.tab', lookupT_map _ _ _ hu]

/-- On the box `g.U' EY EN`, the evaluation with fuel `0` is one level `GD.F'` applied to the
constant function `false`. -/
theorem GD.evS'_zero (g : GD) (neg : Bool) (EY EN : Option ℕ) (u : List BitString × ℕ × ℕ)
    (hu : u ∈ g.U' EY EN) : g.evS' neg EY EN 0 u = g.F' neg EY EN u fun _ => false := by
  unfold GD.evS'
  rw [GD.tab', lookupT_map _ _ _ hu]
  rfl

/-- **Correctness of the evaluation with fuel.** If `EY` and `EN` are the floors of the scaled
remaining budgets of YES and NO, then `g.evS' neg EY EN n u` holds iff `SafeYesF` with fuel `n`
holds in the game `g.dd neg` at the state `g.st' α β u`. -/
theorem GD.evS'_iff (g : GD) (neg : Bool) (EY EN : Option ℕ) (α β : ℝ)
    (hY : IsFloorO ((g.game.ε - α) * 2 ^ g.N) EY) (hN : IsFloorO ((g.game.ε - β) * 2 ^ g.N) EN)
    (n : ℕ) (u : List BitString × ℕ × ℕ) (hu : u ∈ g.U' EY EN) :
    g.evS' neg EY EN n u = true ↔ SafeYesF (g.dd neg) n (g.st' α β u) := by
  induction n generalizing u with
  | zero =>
    rw [g.evS'_zero neg EY EN u hu,
      g.F'_iff neg EY EN α β hY hN u hu (fun _ => false) (fun _ => False) (fun v _ => by simp)]
    change _ ↔ ((g.dd neg).outcome (g.st' α β u).S = true ∧
      ∀ S', LegalMove (g.dd neg) (g.st' α β u) S' → S' = (g.st' α β u).S)
    apply and_congr_right
    intro _
    constructor
    · intro h S' hL
      by_contra hne
      obtain ⟨_, _, hF⟩ := h S' hL hne
      exact hF
    · intro h S' hL hne
      exact absurd (h S' hL) hne
  | succ n ih =>
    rw [g.evS'_succ neg EY EN n u hu, g.F'_iff neg EY EN α β hY hN u hu (g.evS' neg EY EN n)
      (SafeYesF (g.dd neg) n) (fun v hv => ih v hv)]
    rfl

/-- The right fold that keeps the strings of `L` that belong to `R` is the filter of `L` by
membership in `R`. -/
theorem foldr_canon (R L : List BitString) :
    L.foldr (fun z acc => bif memStr z R then z :: acc else acc) [] =
      L.filter fun z => memStr z R := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    cases memStr z R <;> rfl

/-- The canonical position `g.canon R` is a sublist of the strings in play `g.Xd`. -/
theorem GD.canon_mem (g : GD) (R : List BitString) : g.canon R ∈ allSub g.Xd := by
  unfold GD.canon
  rw [foldr_canon]
  exact (mem_allSub_iff _ _).2 List.filter_sublist

/-- If every string of `R` is in play, the canonical position `g.canon R` consists of the same
strings as `R`. -/
theorem GD.canon_toFinset (g : GD) (R : List BitString) (hR : ∀ z ∈ R, z ∈ g.X) :
    (g.canon R).toFinset = R.toFinset := by
  unfold GD.canon
  rw [foldr_canon]
  ext z
  simp only [List.mem_toFinset, List.mem_filter, memStr_iff]
  exact ⟨fun h => h.2, fun h => ⟨(g.mem_Xd z).2 (hR z h), h⟩⟩

/-- The number of strings in play in `g.game` is the length of the list `g.Xd` of the strings in
play without repetitions. -/
theorem GD.card_X (g : GD) : g.game.X.card = g.Xd.length := by
  change g.X.toFinset.card = (dedupL g.X).length
  rw [← List.toFinset_card_of_nodup (nodup_dedupL g.X)]
  congr 1
  ext z
  simp [mem_dedupL]

/-- The evaluator decides `SafeYes` in the game or its dual at `(R, α, β)` with NO to move. -/
theorem GD.safeYes_eval (g : GD) (neg : Bool) (EY EN : Option ℕ) (α β : ℝ)
    (hY : IsFloorO ((g.game.ε - α) * 2 ^ g.N) EY) (hN : IsFloorO ((g.game.ε - β) * 2 ^ g.N) EN)
    (R : List BitString) (hR : ∀ z ∈ R, z ∈ g.X) :
    g.evS' neg EY EN g.Xd.length (g.canon R, 0, 0) = true ↔
      SafeYes (g.dd neg) ⟨R.toFinset, α, β, false⟩ := by
  have hu : (g.canon R, 0, 0) ∈ g.U' EY EN :=
    (g.mem_U' EY EN _ 0 0).2 ⟨g.canon_mem R, Nat.zero_le _, Nat.zero_le _⟩
  rw [g.evS'_iff neg EY EN α β hY hN _ _ hu]
  have hst : g.st' α β (g.canon R, 0, 0) = ⟨R.toFinset, α, β, false⟩ := by
    simp [GD.st', g.canon_toFinset R hR]
  rw [hst]
  have hsub : R.toFinset ⊆ (g.dd neg).X := by
    intro z hz
    rw [g.dd_X, show g.game.X = g.X.toFinset from rfl, List.mem_toFinset]
    exact hR z (List.mem_toFinset.1 hz)
  have hcard : ((g.dd neg).X \ R.toFinset).card ≤ g.Xd.length := by
    rw [g.dd_X, ← g.card_X]
    exact Finset.card_le_card Finset.sdiff_subset
  exact (safeYes_iff_safeYesF (g.dd neg) g.Xd.length ⟨R.toFinset, α, β, false⟩ hsub hcard).symm

/-- **Correctness of `safeYesC`.** If the strings of `R` are in play and `EY`, `EN` are the floors
of the scaled remaining budgets of YES and NO, then `safeYesC g (R, EY, EN, t)` holds iff `SafeYes`
holds in `g.game` at the state with position `R`, scores `α`, `β` and turn flag `t`. -/
theorem safeYesC_spec (g : GD) (R : List BitString) (EY EN : Option ℕ) (t : Bool) (α β : ℝ)
    (hR : ∀ z ∈ R, z ∈ g.X)
    (hY : IsFloorO ((g.game.ε - α) * 2 ^ g.N) EY)
    (hN : IsFloorO ((g.game.ε - β) * 2 ^ g.N) EN) :
    safeYesC g (R, EY, EN, t) = true ↔ SafeYes g.game ⟨R.toFinset, α, β, t⟩ := by
  cases t
  · exact g.safeYes_eval false EY EN α β hY hN R hR
  · exact (g.safeYes_eval false EN EY β α hN hY R hR).trans
      (safeYes_swap g.game R.toFinset β α false).symm

/-- **Correctness of `safeNoC`.** If the strings of `R` are in play and `EY`, `EN` are the floors
of the scaled remaining budgets of YES and NO, then `safeNoC g (R, EY, EN, t)` holds iff `SafeNo`
holds in `g.game` at the state with position `R`, scores `α`, `β` and turn flag `t`. -/
theorem safeNoC_spec (g : GD) (R : List BitString) (EY EN : Option ℕ) (t : Bool) (α β : ℝ)
    (hR : ∀ z ∈ R, z ∈ g.X)
    (hY : IsFloorO ((g.game.ε - α) * 2 ^ g.N) EY)
    (hN : IsFloorO ((g.game.ε - β) * 2 ^ g.N) EN) :
    safeNoC g (R, EY, EN, t) = true ↔ SafeNo g.game ⟨R.toFinset, α, β, t⟩ := by
  rw [safeNo_iff_safeYes_dual]
  cases t
  · exact g.safeYes_eval true EY EN α β hY hN R hR
  · exact (g.safeYes_eval true EN EY β α hN hY R hR).trans
      (safeYes_swap g.game.dual R.toFinset β α false).symm

/-! ### Primitive recursiveness -/

/-- The budget test `okB` is primitive recursive. -/
theorem okB_primrec : Primrec₂ okB :=
  (Primrec.option_casesOn (o := fun p : Option ℕ × ℕ => p.1) (f := fun _ => false)
    (g := fun p E => decide (p.2 ≤ E)) Primrec.fst (Primrec.const false)
    (Primrec.nat_le.decide.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).of_eq fun p => by
    rcases p with ⟨_ | E, k⟩ <;> rfl

/-- If `E` and `k` are primitive recursive, so is `a ↦ okB (E a) (k a)`. -/
theorem okB_comp {α : Type} [Primcodable α] {E : α → Option ℕ} {k : α → ℕ} (hE : Primrec E)
    (hk : Primrec k) : Primrec fun a => okB (E a) (k a) :=
  okB_primrec.comp hE hk

attribute [local irreducible] GD.outC in
/-- The outcome `GD.outN` of a position in the game or its dual is primitive recursive in the game
data, the dual flag and the position. -/
theorem GD.primrec_outN : Primrec fun p : GD × Bool × List BitString => p.1.outN p.2.1 p.2.2 := by
  have h : Primrec fun p : GD × Bool × List BitString => p.1.outC p.2.2 :=
    GD.primrec_outC.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
  exact (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.not.comp h) h).of_eq fun _ => rfl

/-- Parameters of the generalized evaluation: the game, the dual flag and the two budgets. -/
abbrev EvPar : Type := GD × Bool × Option ℕ × Option ℕ

/-- The inner test of `GD.F'` (YES answer `R` to the NO move `S'`). -/
def Qp (pp : EvPar) (u : List BitString × ℕ × ℕ) (acc : Tbl) (S' R : List BitString) : Bool :=
  subB S' R && okB pp.2.2.1 (u.2.1 + pp.1.mc S' R) &&
    lookupT (R, u.2.1 + pp.1.mc S' R, u.2.2 + pp.1.mc u.1 S') acc

/-- The outer test of `GD.F'` (NO move `S'`). -/
def Pp (pp : EvPar) (u : List BitString × ℕ × ℕ) (acc : Tbl) (S' : List BitString) : Bool :=
  !(subB u.1 S' && okB pp.2.2.2 (u.2.2 + pp.1.mc u.1 S')) || subB S' u.1 ||
    anyB (allSub pp.1.Xd) (Qp pp u acc S')

/-- One level `GD.F'` whose next level is read from the table `acc` is the conjunction of the
outcome test `GD.outN` and the outer test `Pp` over all sublists `S'` of the strings in play. -/
theorem GD.F'_lookup (g : GD) (neg : Bool) (EY EN : Option ℕ) (u : List BitString × ℕ × ℕ)
    (acc : Tbl) : g.F' neg EY EN u (fun v => lookupT v acc) =
      (g.outN neg u.1 && allB (allSub g.Xd) (Pp (g, neg, EY, EN) u acc)) := rfl

attribute [local irreducible] subB GD.mc okB lookupT in
/-- The inner test `Qp` is primitive recursive in the parameters, the state, the table and the two
positions. -/
theorem primrec_Qp :
    Primrec fun x : (EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString) × List BitString =>
      Qp x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2 := by
  have hpp : Primrec fun x : (EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString) ×
      List BitString => x.1.1 := Primrec.fst.comp Primrec.fst
  have hg := Primrec.fst.comp hpp
  have hEY := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hpp))
  have hu : Primrec fun x : (EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString) ×
      List BitString => x.1.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hacc : Primrec fun x : (EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString) ×
      List BitString => x.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hS' : Primrec fun x : (EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString) ×
      List BitString => x.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hR : Primrec fun x : (EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString) ×
      List BitString => x.2 := Primrec.snd
  have hmc1 := GD.primrec_mc_comp hg hS' hR
  have hmc2 := GD.primrec_mc_comp hg (Primrec.fst.comp hu) hS'
  have hY := Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp hu)) hmc1
  have hN := Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp hu)) hmc2
  exact (Primrec.and.comp (Primrec.and.comp (subB_primrec.comp hS' hR) (okB_comp hEY hY))
    (lookupT_primrec.comp (hR.pair (hY.pair hN)) hacc)).of_eq fun _ => rfl

attribute [local irreducible] subB GD.mc okB Qp allSub GD.Xd in
/-- The outer test `Pp` is primitive recursive in the parameters, the state, the table and the NO
move. -/
theorem primrec_Pp : Primrec fun y : EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString =>
    Pp y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  have hpp : Primrec fun y : EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString => y.1 :=
    Primrec.fst
  have hg := Primrec.fst.comp hpp
  have hEN := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hpp))
  have hu : Primrec fun y : EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString => y.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hS' : Primrec fun y : EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString => y.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hany : Primrec fun y : EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString =>
      anyB (allSub y.1.1.Xd) (Qp y.1 y.2.1 y.2.2.1 y.2.2.2) :=
    (Primrec.list_foldr (f := fun y : EvPar × (List BitString × ℕ × ℕ) × Tbl × List BitString =>
        allSub y.1.1.Xd) (g := fun _ => false)
      (h := fun y p => Qp y.1 y.2.1 y.2.2.1 y.2.2.2 p.1 || p.2)
      (allSub_primrec.comp (GD.primrec_Xd.comp hg)) (Primrec.const false)
      (Primrec.or.comp (primrec_Qp.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  exact (Primrec.or.comp (Primrec.or.comp (Primrec.not.comp (Primrec.and.comp
    (subB_primrec.comp (Primrec.fst.comp hu) hS')
    (okB_comp hEN (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp hu))
      (GD.primrec_mc_comp hg (Primrec.fst.comp hu) hS')))))
    (subB_primrec.comp hS' (Primrec.fst.comp hu))) hany).of_eq fun _ => rfl

attribute [local irreducible] Pp GD.outN allSub GD.Xd in
/-- One level `GD.F'` whose next level is read from a table is primitive recursive in the
parameters, the state and the table. -/
theorem GD.primrec_F' : Primrec fun p : EvPar × (List BitString × ℕ × ℕ) × Tbl =>
    p.1.1.F' p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1 (fun v => lookupT v p.2.2) := by
  have hall : Primrec fun p : EvPar × (List BitString × ℕ × ℕ) × Tbl =>
      allB (allSub p.1.1.Xd) (Pp p.1 p.2.1 p.2.2) :=
    (Primrec.list_foldr (f := fun p : EvPar × (List BitString × ℕ × ℕ) × Tbl => allSub p.1.1.Xd)
      (g := fun _ => true) (h := fun p q => Pp p.1 p.2.1 p.2.2 q.1 && q.2)
      (allSub_primrec.comp (GD.primrec_Xd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.const true)
      (Primrec.and.comp (primrec_Pp.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair ((Primrec.snd.comp
          (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd)))))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  refine (Primrec.and.comp (GD.primrec_outN.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))) hall).of_eq fun p => ?_
  exact (GD.F'_lookup p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1 p.2.2).symm

attribute [local irreducible] allSub GD.Xd in
/-- The box of states `GD.U'` is primitive recursive in the game data and the two budgets. -/
theorem GD.primrec_U' : Primrec fun p : GD × Option ℕ × Option ℕ => p.1.U' p.2.1 p.2.2 :=
  (Primrec.list_flatMap (allSub_primrec.comp (GD.primrec_Xd.comp Primrec.fst))
    (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.nat_add.comp
      (Primrec.option_getD.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.const 0)) (Primrec.const 1)))
      (Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp
        (Primrec.option_getD.comp (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst))) (Primrec.const 0)) (Primrec.const 1)))
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂).to₂).of_eq fun _ => rfl

/-- The table `g.tab' neg EY EN n` is given by recursion on `n`: level `0` is computed from the
empty table and each further level from the table of the previous one. -/
theorem GD.tab'_eq (g : GD) (neg : Bool) (EY EN : Option ℕ) (n : ℕ) : g.tab' neg EY EN n =
    n.rec ((g.U' EY EN).map fun u => (u, g.F' neg EY EN u fun v => lookupT v []))
      (fun _ acc => (g.U' EY EN).map fun u => (u, g.F' neg EY EN u fun v => lookupT v acc)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [GD.tab', ih]

/-- If the game and the two budgets are primitive recursive functions of `a`, so is the box
`(g a).U' (EY a) (EN a)`. -/
theorem GD.primrec_U'_comp {α : Type} [Primcodable α] {g : α → GD} {EY EN : α → Option ℕ}
    (hg : Primrec g) (hY : Primrec EY) (hN : Primrec EN) :
    Primrec fun a => (g a).U' (EY a) (EN a) :=
  GD.primrec_U'.comp (hg.pair (hY.pair hN))

/-- If the game, the dual flag, the two budgets, the state and the table are primitive recursive
functions of `a`, so is the corresponding level `GD.F'` whose next level is read from the table. -/
theorem GD.primrec_F'_comp {α : Type} [Primcodable α] {g : α → GD} {neg : α → Bool}
    {EY EN : α → Option ℕ} {u : α → List BitString × ℕ × ℕ} {acc : α → Tbl} (hg : Primrec g)
    (hneg : Primrec neg) (hY : Primrec EY) (hN : Primrec EN) (hu : Primrec u)
    (hacc : Primrec acc) :
    Primrec fun a => (g a).F' (neg a) (EY a) (EN a) (u a) (fun v => lookupT v (acc a)) :=
  GD.primrec_F'.comp ((hg.pair (hneg.pair (hY.pair hN))).pair (hu.pair hacc))

attribute [local irreducible] GD.U' GD.F' lookupT in
/-- The table of values `GD.tab'` is primitive recursive in the parameters and the level. -/
theorem GD.primrec_tab' :
    Primrec₂ fun (pp : EvPar) (n : ℕ) => pp.1.tab' pp.2.1 pp.2.2.1 pp.2.2.2 n := by
  have hU : Primrec fun p : EvPar × Tbl => p.1.1.U' p.1.2.2.1 p.1.2.2.2 :=
    GD.primrec_U'_comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hF : Primrec fun y : (EvPar × Tbl) × (List BitString × ℕ × ℕ) =>
      (y.2, y.1.1.1.F' y.1.1.2.1 y.1.1.2.2.1 y.1.1.2.2.2 y.2 fun v => lookupT v y.1.2) :=
    Primrec.snd.pair (GD.primrec_F'_comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd (Primrec.snd.comp Primrec.fst))
  have hstep : Primrec fun p : EvPar × Tbl =>
      (p.1.1.U' p.1.2.2.1 p.1.2.2.2).map fun u =>
        (u, p.1.1.F' p.1.2.1 p.1.2.2.1 p.1.2.2.2 u fun v => lookupT v p.2) :=
    Primrec.list_map hU hF.to₂
  have h := Primrec.nat_rec (f := fun pp : EvPar => (pp.1.U' pp.2.2.1 pp.2.2.2).map fun u =>
      (u, pp.1.F' pp.2.1 pp.2.2.1 pp.2.2.2 u fun v => lookupT v []))
    (g := fun pp p => (pp.1.U' pp.2.2.1 pp.2.2.2).map fun u =>
      (u, pp.1.F' pp.2.1 pp.2.2.1 pp.2.2.2 u fun v => lookupT v p.2))
    (hstep.comp (Primrec.id.pair (Primrec.const [])))
    (hstep.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq fun pp n => (GD.tab'_eq pp.1 pp.2.1 pp.2.2.1 pp.2.2.2 n).symm

attribute [local irreducible] memStr GD.Xd in
/-- The canonical position `GD.canon` is primitive recursive in the game data and the position. -/
theorem GD.primrec_canon : Primrec fun p : GD × List BitString => p.1.canon p.2 :=
  (Primrec.list_foldr (f := fun p : GD × List BitString => p.1.Xd)
    (g := fun _ => ([] : List BitString))
    (h := fun p q => bif memStr q.1 p.2 then q.1 :: q.2 else q.2)
    (GD.primrec_Xd.comp Primrec.fst) (Primrec.const [])
    (Primrec.cond (memStr_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

attribute [local irreducible] GD.tab' lookupT GD.canon GD.Xd in
/-- For primitive recursive budgets `fY`, `fN` (functions of the game and the state), the
evaluation `GD.evS'` at the root `(g.canon R, 0, 0)` with fuel `g.Xd.length` is primitive
recursive. -/
theorem GD.primrec_evS'_root (neg : Bool) {fY fN : GD × GSt → Option ℕ} (hY : Primrec fY)
    (hN : Primrec fN) : Primrec fun p : GD × GSt =>
      p.1.evS' neg (fY p) (fN p) p.1.Xd.length (p.1.canon p.2.1, 0, 0) := by
  have hL : Primrec fun p : GD × GSt => p.1.Xd.length :=
    Primrec.list_length.comp (GD.primrec_Xd.comp Primrec.fst)
  have hv : Primrec fun p : GD × GSt => (p.1.canon p.2.1, 0, 0) :=
    (GD.primrec_canon.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))).pair
      ((Primrec.const 0).pair (Primrec.const 0))
  exact (lookupT_primrec.comp hv (GD.primrec_tab'.comp (Primrec.fst.pair
    ((Primrec.const neg).pair (hY.pair hN))) hL)).of_eq fun _ => rfl

attribute [local irreducible] GD.evS' GD.canon GD.Xd in
/-- The decision `safeYesC` of `SafeYes` is primitive recursive in the game data and the state. -/
theorem safeYesC_primrec : Primrec fun p : GD × GSt => safeYesC p.1 p.2 := by
  have hEY : Primrec fun p : GD × GSt => p.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hEN : Primrec fun p : GD × GSt => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ht : Primrec fun p : GD × GSt => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.cond ht (GD.primrec_evS'_root false hEN hEY)
    (GD.primrec_evS'_root false hEY hEN)).of_eq fun _ => rfl

attribute [local irreducible] GD.evS' GD.canon GD.Xd in
/-- The decision `safeNoC` of `SafeNo` is primitive recursive in the game data and the state. -/
theorem safeNoC_primrec : Primrec fun p : GD × GSt => safeNoC p.1 p.2 := by
  have hEY : Primrec fun p : GD × GSt => p.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hEN : Primrec fun p : GD × GSt => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ht : Primrec fun p : GD × GSt => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.cond ht (GD.primrec_evS'_root true hEN hEY)
    (GD.primrec_evS'_root true hEY hEN)).of_eq fun _ => rfl

/-- The floor of `(2⁻¹ ^ m - (pos - neg) / 2 ^ B) * 2 ^ N` as an optional natural (`none` if
negative), for `m ≤ B` and `N ≤ B`: the integer `2 ^ (B - m) + neg - pos` divided by
`2 ^ (B - N)`. -/
def floorOfScaled (pos neg B m N : ℕ) : Option ℕ :=
  if pos ≤ 2 ^ (B - m) + neg then some ((2 ^ (B - m) + neg - pos) / 2 ^ (B - N)) else none

/-- `floorOfScaled` is primitive recursive in its five arguments. -/
theorem floorOfScaled_primrec :
    Primrec fun p : ℕ × ℕ × ℕ × ℕ × ℕ => floorOfScaled p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have hpos : Primrec fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.1 := Primrec.fst
  have hneg : Primrec fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hB : Primrec fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hm : Primrec fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hN : Primrec fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hT : Primrec fun p : ℕ × ℕ × ℕ × ℕ × ℕ => 2 ^ (p.2.2.1 - p.2.2.2.1) + p.2.1 :=
    Primrec.nat_add.comp (pow_primrec.comp (Primrec.const 2) (Primrec.nat_sub.comp hB hm)) hneg
  have hc : PrimrecPred fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.1 ≤ 2 ^ (p.2.2.1 - p.2.2.2.1) + p.2.1 :=
    Primrec.nat_le.comp hpos hT
  exact (Primrec.ite hc (Primrec.option_some.comp (Primrec.nat_div.comp
    (Primrec.nat_sub.comp hT hpos) (pow_primrec.comp (Primrec.const 2)
      (Primrec.nat_sub.comp hB hN)))) (Primrec.const none)).of_eq fun _ => rfl

/-- For `m ≤ B` and `N ≤ B`, `floorOfScaled pos neg B m N` is the floor, in the sense of
`IsFloorO`, of `(2⁻¹ ^ m - (pos - neg) / 2 ^ B) * 2 ^ N`. -/
theorem isFloorO_floorOfScaled (pos neg B m N : ℕ) (hm : m ≤ B) (hN : N ≤ B) :
    IsFloorO (((2 : ℝ)⁻¹ ^ m - ((pos : ℝ) - neg) / 2 ^ B) * 2 ^ N)
      (floorOfScaled pos neg B m N) := by
  have hpowBN : (2 : ℝ) ^ B = 2 ^ (B - N) * 2 ^ N := by rw [← pow_add, Nat.sub_add_cancel hN]
  have hreal : ((2 : ℝ)⁻¹ ^ m - ((pos : ℝ) - neg) / 2 ^ B) * 2 ^ N =
      ((2 : ℝ) ^ (B - m) + neg - pos) / 2 ^ (B - N) := by
    rw [inv_two_pow_eq B m hm, hpowBN]
    have h1 : (2 : ℝ) ^ N ≠ 0 := by positivity
    have h2 : (2 : ℝ) ^ (B - N) ≠ 0 := by positivity
    field_simp
    ring
  intro k
  rw [hreal]
  unfold floorOfScaled
  split_ifs with h
  · have hq : ((2 ^ (B - m) + neg - pos : ℕ) : ℝ) = (2 : ℝ) ^ (B - m) + neg - pos := by
      rw [Nat.cast_sub h]
      push_cast
      ring
    rw [← hq, le_div_iff₀ (by positivity)]
    constructor
    · intro hk
      refine ⟨_, rfl, ?_⟩
      rw [Nat.le_div_iff_mul_le (by positivity)]
      exact_mod_cast hk
    · rintro ⟨E, hE, hkE⟩
      rw [Option.some.injEq] at hE
      subst hE
      rw [Nat.le_div_iff_mul_le (by positivity)] at hkE
      exact_mod_cast hkE
  · constructor
    · intro hk
      exfalso
      push Not at h
      have h' : ((2 ^ (B - m) + neg : ℕ) : ℝ) < pos := by exact_mod_cast h
      push_cast at h'
      have hneg' : (2 : ℝ) ^ (B - m) + neg - pos < 0 := by linarith
      have hlt : ((2 : ℝ) ^ (B - m) + neg - pos) / 2 ^ (B - N) < 0 :=
        div_neg_of_neg_of_pos hneg' (by positivity)
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    · rintro ⟨E, hE, -⟩
      cases hE

end Kolmogorov.RandomStrings
