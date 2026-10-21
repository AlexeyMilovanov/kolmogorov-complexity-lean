/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Effective
import KolmogorovMathlib.RandomStrings.Game

/-!
# Families of clocked oracle machines

The general theorem (`AFG/General.lean`) is parametrised by a family of clocked machines, given
by a computable clock function `clk` (the machine `(c, e)` runs for `clk e |x|` steps on the input
`x`; `clock e n = n ^ e + e` for polynomial time, `clkE e n = 2 ^ (n ^ e + e)` for exponential
time) and a property `Φ c e x` of the clocked machine `(c, e)` on the input `x` that is decidable
from the code of the machine (`ΦB`, computable).  A clocked machine belongs to the family if
`∀ x, Φ c e x`.  Since this is a `Π₁` property, the construction enumerates *all* clocked
machines and, on inputs with `¬ Φ`, plays an empty game whose outcome is fixed in advance to the
right value (`gameOfF`): such an input is always a witness, and a machine with `¬ Φ` on some input
is not in the family.

* `Family`: the class (`Φ`, its decision procedure `ΦB` on machine codes, the clock `clk`);
* `qsetF`: the strings of the game (the possible queries if `Φ`, otherwise none);
* `gameOfF`: the guarded game (`gameOf` if `Φ`, constant outcome `x ∉ A` otherwise);
* `queryListCodeF`: the computable form of `qsetF`;
* `Family.turing`: the family of all clocked machines (polynomial clock);
  `Family.turingE`: the family of all machines with the exponential clock `clkE`;
  `Family.ofClock`: the family given by a property within a time bound and a clock.
-/

namespace Kolmogorov.RandomStrings

/-- A family of clocked oracle machines, given by a clock function and a decidable property on
single inputs. -/
class Family where
  /-- Machine `c` with clock `e` belongs to the family on the input `x`. -/
  Φ : OTMCode → ℕ → BitString → Prop
  /-- A decision procedure on machine codes `m` (`decodeCode m`). -/
  ΦB : ℕ → ℕ → BitString → Bool
  ΦB_iff : ∀ (m e : ℕ) (x : BitString), ΦB m e x = true ↔ Φ (decodeCode m) e x
  ΦB_computable : Computable fun p : ℕ × ℕ × BitString => ΦB p.1 p.2.1 p.2.2
  /-- The clock function: the machine with clock index `e` runs for `clk e |x|` steps on `x`. -/
  clk : ℕ → ℕ → ℕ
  clk_computable : Computable₂ clk

open Classical in
/-- The strings of the game: the possible queries of the machine if `Φ`, otherwise none. -/
noncomputable def qsetF [Family] (c : OTMCode) (e : ℕ) (x : BitString) : Finset BitString :=
  if Family.Φ c e x then querySet c.toOTM x (Family.clk e x.length) else ∅

open Classical in
/-- The guarded game: for `Φ` the game `gameOfT` with the time bound `clk e |x|`, otherwise the
outcome is constant, equal to `x ∉ A`. -/
noncomputable def gameOfF [Family] (A : Set BitString) (c : OTMCode) (e : ℕ) (x : BitString)
    (h : BitString → ℕ) (ε : ℝ) (X : Finset BitString) : GameData :=
  gameOfBT c (Family.clk e x.length) x h ε X (decide (Family.Φ c e x)) (decide (x ∉ A))

/-- The Turing family: all clocked machines, with the polynomial clock `clock`. -/
@[instance_reducible] def Family.turing : Family :=
  ⟨fun _ _ _ => True, fun _ _ _ => true, by simp, Computable.const _, clock, clock_computable⟩

/-- The exponential Turing family: all machines, with the exponential clock `clkE`. -/
@[instance_reducible] def Family.turingE : Family :=
  ⟨fun _ _ _ => True, fun _ _ _ => true, by simp, Computable.const _, clkE, clkE_computable⟩

/-- The family of the clocked machines `(c, e)` with the property `P c T x` for the time bound
`T = clk e |x|`, given a decision procedure `PB` on codes and a computable clock `clk` (e.g. a
property of the computation tree within `T` steps, with the exponential clock `clkE`). -/
@[instance_reducible] def Family.ofClock (P : OTMCode → ℕ → BitString → Prop)
    (PB : ℕ → ℕ → BitString → Bool)
    (hPB : ∀ (m T : ℕ) (x : BitString), PB m T x = true ↔ P (decodeCode m) T x)
    (hPBc : Computable fun p : ℕ × ℕ × BitString => PB p.1 p.2.1 p.2.2)
    (clk : ℕ → ℕ → ℕ) (hclk : Computable₂ clk) : Family where
  Φ c e x := P c (clk e x.length) x
  ΦB m e x := PB m (clk e x.length) x
  ΦB_iff m e x := hPB m (clk e x.length) x
  ΦB_computable := (hPBc.comp (Computable.fst.pair ((hclk.comp
    (Computable.fst.comp Computable.snd) (Primrec.list_length.to_comp.comp
      (Computable.snd.comp Computable.snd))).pair (Computable.snd.comp Computable.snd)))).of_eq
        fun _ => rfl
  clk := clk
  clk_computable := hclk

/-- In the empty game there are no moves: YES wins iff the outcome of `∅` is `true` (for a
nonnegative budget). -/
theorem val_empty_iff (d : GameData) (hX : d.X = ∅) (hε : 0 ≤ d.ε) :
    val d = true ↔ d.outcome ∅ = true := by
  rw [determined]
  constructor
  · rintro ⟨S₁, hL, hs⟩
    have hS₁ : S₁ = ∅ := Finset.subset_empty.1 (hX ▸ hL.2.1)
    have := hs.outcome
    rw [hS₁] at this
    simpa [applyMove, GState.init] using this
  · intro hout
    have hL : LegalMove d GState.init ∅ := by
      refine ⟨subset_rfl, by rw [hX], ?_⟩
      simp only [GState.init, ite_true, moveCost_self, zero_add]
      exact hε
    refine ⟨∅, hL, SafeYes.intro _ id ?_ ?_ ?_⟩
    · simpa [applyMove, GState.init] using hout
    · intro S' hL' hne
      exact absurd (Finset.subset_empty.1 (hX ▸ hL'.2.1))
        (by simpa [applyMove, GState.init] using hne)
    · intro S' hL' hne
      exact absurd (Finset.subset_empty.1 (hX ▸ hL'.2.1))
        (by simpa [applyMove, GState.init] using hne)

section

variable [Family]

noncomputable local instance (c : OTMCode) (e : ℕ) (x : BitString) :
    Decidable (Family.Φ c e x) :=
  Classical.propDecidable _

noncomputable local instance (x : BitString) (A : Set BitString) : Decidable (x ∈ A) :=
  Classical.propDecidable _

noncomputable local instance (x : BitString) (A : Set BitString) : Decidable (x ∉ A) :=
  instDecidableNot

/-- If the clocked machine satisfies the property `Φ`, the query set of the game is the set of
queries made by the machine. -/
theorem qsetF_of_Φ {c : OTMCode} {e : ℕ} {x : BitString} (h : Family.Φ c e x) :
    qsetF c e x = querySet c.toOTM x (Family.clk e x.length) := by
  unfold qsetF
  rw [ite_eq_left h]

/-- If the clocked machine does not satisfy the property `Φ`, the query set of the game is
empty. -/
theorem qsetF_of_not {c : OTMCode} {e : ℕ} {x : BitString} (h : ¬ Family.Φ c e x) :
    qsetF c e x = ∅ := by
  unfold qsetF
  rw [ite_eq_right h]

/-- The query set of the game is a subset of the time-bounded query set of the machine. -/
theorem qsetF_subset (c : OTMCode) (e : ℕ) (x : BitString) :
    qsetF c e x ⊆ querySet c.toOTM x (Family.clk e x.length) := by
  unfold qsetF
  split_ifs
  · exact subset_rfl
  · exact Finset.empty_subset _

/-- If the clocked machine satisfies the property `Φ`, the guarded game equals the standard
time-bounded game `gameOfT`. -/
theorem gameOfF_of_Φ (A : Set BitString) {c : OTMCode} {e : ℕ} {x : BitString}
    (h : BitString → ℕ) (ε : ℝ) (X : Finset BitString) (hΦ : Family.Φ c e x) :
    gameOfF A c e x h ε X = gameOfT c (Family.clk e x.length) x h ε X := by
  unfold gameOfF
  rw [decide_eq_true hΦ]
  exact gameOfBT_true c _ x h ε X _

/-- If the clocked machine does not satisfy the property `Φ`, the outcome of the guarded game is
constant, evaluating to whether `x` is not in `A`. -/
theorem gameOfF_outcome_of_not (A : Set BitString) {c : OTMCode} {e : ℕ} {x : BitString}
    (h : BitString → ℕ) (ε : ℝ) (X : Finset BitString) (hΦ : ¬ Family.Φ c e x)
    (S : Finset BitString) :
    (gameOfF A c e x h ε X).outcome S = decide (x ∉ A) := by
  unfold gameOfF
  rw [decide_eq_false hΦ]
  exact gameOfBT_false_outcome c _ x h ε X _ S

/-- The strings in play of the guarded game `gameOfF A c e x h ε X` are `X`. -/
theorem gameOfF_X (A : Set BitString) (c : OTMCode) (e : ℕ) (x : BitString)
    (h : BitString → ℕ) (ε : ℝ) (X : Finset BitString) :
    (gameOfF A c e x h ε X).X = X := rfl

/-- The current values of `H` in the guarded game `gameOfF A c e x h ε X` are `h`. -/
theorem gameOfF_h₀ (A : Set BitString) (c : OTMCode) (e : ℕ) (x : BitString)
    (h : BitString → ℕ) (ε : ℝ) (X : Finset BitString) :
    (gameOfF A c e x h ε X).h₀ = h := rfl

/-- The budget of each player in the guarded game `gameOfF A c e x h ε X` is `ε`. -/
theorem gameOfF_ε (A : Set BitString) (c : OTMCode) (e : ℕ) (x : BitString)
    (h : BitString → ℕ) (ε : ℝ) (X : Finset BitString) :
    (gameOfF A c e x h ε X).ε = ε := rfl

/-- The outcome of the guarded game, by cases on the guard. -/
theorem gameOfF_outcome (A : Set BitString) (c : OTMCode) (e : ℕ) (x : BitString)
    (h : BitString → ℕ) (ε : ℝ) (X S : Finset BitString) :
    (gameOfF A c e x h ε X).outcome S = true ↔
      (Family.Φ c e x → ClockedAcceptsT c (Family.clk e x.length) (oracleOf h S) x) ∧
        (¬ Family.Φ c e x → x ∉ A) := by
  by_cases hΦ : Family.Φ c e x
  · rw [gameOfF_of_Φ A h ε X hΦ]
    simp only [gameOfT, decide_eq_true_eq]
    exact ⟨fun h1 => ⟨fun _ => h1, fun h2 => absurd hΦ h2⟩, fun h1 => h1.1 hΦ⟩
  · rw [gameOfF_outcome_of_not A h ε X hΦ, decide_eq_true_eq]
    exact ⟨fun h1 => ⟨fun h2 => absurd h2 hΦ, fun _ => h1⟩, fun h1 => h1.2 hΦ⟩

/-- A game `gameOfBT` with the time bound `clk e |x|` and guard bits describing `Φ` and `x ∉ A`
is the guarded game. -/
theorem gameOfBT_eq_gameOfF (A : Set BitString) (c : OTMCode) (e : ℕ) (x : BitString)
    (h : BitString → ℕ) (ε : ℝ) (X : Finset BitString) (b₁ b₂ : Bool)
    (h₁ : b₁ = true ↔ Family.Φ c e x) (h₂ : b₂ = true ↔ x ∉ A) :
    gameOfBT c (Family.clk e x.length) x h ε X b₁ b₂ = gameOfF A c e x h ε X := by
  unfold gameOfF
  congr 1
  · exact Bool.eq_iff_iff.2 (h₁.trans decide_eq_true_iff.symm)
  · exact Bool.eq_iff_iff.2 (h₂.trans decide_eq_true_iff.symm)

/-- Off the family the empty guarded game is won by YES iff `x ∉ A`. -/
theorem val_gameOfF_of_not (A : Set BitString) {c : OTMCode} {e : ℕ} {x : BitString}
    (h : BitString → ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hΦ : ¬ Family.Φ c e x) :
    val (gameOfF A c e x h ε ∅) = true ↔ x ∉ A := by
  rw [val_empty_iff _ rfl hε, gameOfF_outcome_of_not A h ε ∅ hΦ, decide_eq_true_eq]

/-! ### The computable form of `qsetF` -/

/-- The possible queries of the coded machine `m` if it belongs to the family on `x`, otherwise
none. -/
def queryListCodeF (m e : ℕ) (x : BitString) : List BitString :=
  bif Family.ΦB m e x then queryListCodeT m (Family.clk e x.length) x else []

/-- The finset of the entries of the computable list `queryListCodeF m e x` is the query set
`qsetF` of the machine `decodeCode m`. -/
theorem queryListCodeF_toFinset (m e : ℕ) (x : BitString) :
    (queryListCodeF m e x).toFinset = qsetF (decodeCode m) e x := by
  unfold queryListCodeF
  cases hb : Family.ΦB m e x
  · have hΦ : ¬ Family.Φ (decodeCode m) e x := fun h => by
      rw [← Family.ΦB_iff] at h
      rw [hb] at h
      exact Bool.false_ne_true h
    rw [qsetF_of_not hΦ]
    rfl
  · have hΦ : Family.Φ (decodeCode m) e x := (Family.ΦB_iff m e x).1 hb
    rw [qsetF_of_Φ hΦ, querySet_eq_toFinsetT]
    rfl

/-- The query list `queryListCodeF m e x` is a computable function of the triple `(m, e, x)`. -/
theorem queryListCodeF_computable :
    Computable fun p : ℕ × ℕ × BitString => queryListCodeF p.1 p.2.1 p.2.2 := by
  have hT : Computable fun p : ℕ × ℕ × BitString => Family.clk p.2.1 p.2.2.length :=
    Family.clk_computable.comp (Computable.fst.comp Computable.snd)
      (Primrec.list_length.to_comp.comp (Computable.snd.comp Computable.snd))
  have h := Computable.cond Family.ΦB_computable (queryListCodeT_primrec.to_comp.comp
    (Computable.fst.pair (hT.pair (Computable.snd.comp Computable.snd))))
    (Computable.const ([] : List BitString))
  exact h.of_eq fun p => rfl

end

end Kolmogorov.RandomStrings
