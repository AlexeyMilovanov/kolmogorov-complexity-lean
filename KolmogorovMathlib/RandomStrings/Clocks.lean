/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Game

/-!
# General clocks

The construction was first written for the polynomial clock `clock e n = n ^ e + e`
(`ClockedAccepts`, `ClockedDecides`, `gameOf`, `gameOfB`).  Here the same notions are given for
an arbitrary time bound `T`, so that families of machines with other clocks (e.g. the
exponential clock `clkE e n = 2 ^ (n ^ e + e)`, needed for `EXP^R_{sa,poly} ⊆ EXP`) are handled by
the same construction (the field `Family.clk` of `AFG/Family.lean`):

* `ClockedAcceptsT c T B x`: acceptance within `T` steps; `ClockedAccepts c e B x` is
  `ClockedAcceptsT c (clock e |x|) B x` by definition (`clockedAccepts_iff_T`);
* `ClockedDecidesW clk c e B A`: the machine `c`, run for `clk e |x|` steps on `x`, decides `A`
  with the oracle `B`; `ClockedDecidesW clock` is `ClockedDecides` (`clockedDecidesW_clock`);
* `gameOfT`, `gameOfBT`: the games `gameOf`, `gameOfB` for the time bound `T`; the polynomial
  clock gives the old games by `rfl` (`gameOfT_clock`, `gameOfBT_clock`);
* `clkE`: the exponential clock; `exists_clockedW_of_bound` (a machine halting within
  `clk e |x|` steps is a `clk`-clocked coded machine) and `exists_clockedE_of_expTime` (the
  oracle class `ExpTimeOracle B` of time `2 ^ p(|x|)` consists of `clkE`-clocked coded machines).
-/

namespace Kolmogorov.RandomStrings

/-- Acceptance within `T` steps. -/
def ClockedAcceptsT (c : OTMCode) (T : ℕ) (B : Set BitString) (x : BitString) : Prop :=
  ∃ t ≤ T, (run c.toOTM B x t).q = c.toOTM.accept

/-- The polynomial clock is the time bound `clock e |x|`. -/
theorem clockedAccepts_iff_T (c : OTMCode) (e : ℕ) (B : Set BitString) (x : BitString) :
    ClockedAccepts c e B x ↔ ClockedAcceptsT c (clock e x.length) B x := Iff.rfl

/-- The clocked machine `(c, e)` under the clock function `clk` (run for `clk e |x|` steps on the
input `x`) decides `A` with the oracle `B`. -/
def ClockedDecidesW (clk : ℕ → ℕ → ℕ) (c : OTMCode) (e : ℕ) (B A : Set BitString) : Prop :=
  ∀ x, x ∈ A ↔ ClockedAcceptsT c (clk e x.length) B x

/-- The polynomial clock gives `ClockedDecides`. -/
theorem clockedDecidesW_clock (c : OTMCode) (e : ℕ) (B A : Set BitString) :
    ClockedDecidesW clock c e B A ↔ ClockedDecides c e B A := Iff.rfl

/-- The verdict within `T` steps depends only on the oracle's restriction to the possible
queries within `T` steps. -/
theorem clockedAcceptsT_iff_of_agree (c : OTMCode) (T : ℕ) (B B' : Set BitString) (x : BitString)
    (h : ∀ z ∈ querySet c.toOTM x T, (z ∈ B ↔ z ∈ B')) :
    ClockedAcceptsT c T B x ↔ ClockedAcceptsT c T B' x := by
  have hrun : ∀ t ≤ T, run c.toOTM B x t = run c.toOTM B' x t := by
    intro t ht
    apply run_eq_of_agree
    intro z hz
    apply h
    rw [querySet, Set.Finite.mem_toFinset]
    exact ⟨B, queries_mono _ _ _ ht hz⟩
  unfold ClockedAcceptsT
  constructor
  · rintro ⟨t, ht, h'⟩
    exact ⟨t, ht, by rw [← hrun t ht]; exact h'⟩
  · rintro ⟨t, ht, h'⟩
    exact ⟨t, ht, by rw [hrun t ht]; exact h'⟩

/-- The game `gameOf` for the time bound `T`: the machine `c` on the input `x`, current values
`h`, budget `ε`, played on the strings `X`. -/
noncomputable def gameOfT (c : OTMCode) (T : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) : GameData :=
  { X := X, h₀ := h, ε := ε,
    outcome := fun S => by classical exact decide (ClockedAcceptsT c T (oracleOf h S) x) }

/-- The polynomial clock gives `gameOf`. -/
theorem gameOfT_clock (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) :
    gameOfT c (clock e x.length) x h ε X = gameOf c e x h ε X := rfl

/-- The guarded game `gameOfB` for the time bound `T`: for `phi = true` it is `gameOfT`; for
`phi = false` the outcome is the constant `dflt`. -/
noncomputable def gameOfBT (c : OTMCode) (T : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (phi dflt : Bool) : GameData :=
  { X := X, h₀ := h, ε := ε,
    outcome := fun S => bif phi then
      (by classical exact decide (ClockedAcceptsT c T (oracleOf h S) x)) else dflt }

/-- The guarded game `gameOfBT` reduces to `gameOfT` when the guard is `true`. -/
theorem gameOfBT_true (c : OTMCode) (T : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (dflt : Bool) :
    gameOfBT c T x h ε X true dflt = gameOfT c T x h ε X := rfl

/-- The outcome of the guarded game `gameOfBT` is constantly `dflt` when the guard is `false`. -/
theorem gameOfBT_false_outcome (c : OTMCode) (T : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (dflt : Bool) (S : Finset BitString) :
    (gameOfBT c T x h ε X false dflt).outcome S = dflt := rfl

/-- The polynomial clock gives `gameOfB`. -/
theorem gameOfBT_clock (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (phi dflt : Bool) :
    gameOfBT c (clock e x.length) x h ε X phi dflt = gameOfB c e x h ε X phi dflt := rfl

/-! ### Machines with a given clock function, and the exponential clock -/

/-- A machine with oracle `B` that halts within `clk e |x|` steps on every input `x` is, as a coded
machine, `clk`-clocked with the index `e`. -/
theorem exists_clockedW_of_bound (clk : ℕ → ℕ → ℕ) (M : OTM) (B A : Set BitString) (e : ℕ)
    (hb : ∀ x : BitString, ∃ t : ℕ, t ≤ clk e x.length ∧ Halted M (run M B x t))
    (hA : ∀ x : BitString, x ∈ A ↔ Accepts M B x) : ∃ c : OTMCode, ClockedDecidesW clk c e B A := by
  obtain ⟨c, hc⟩ := exists_code M
  refine ⟨c, fun x => ?_⟩
  obtain ⟨t, ht, hh⟩ := hb x
  rw [hA x]
  constructor
  · intro hacc
    have h1 := (accepts_iff_of_halted M B x t hh).1 hacc
    exact ⟨t, ht, (hc B x t).2.1.1 h1⟩
  · rintro ⟨s, -, h'⟩
    exact ⟨s, (hc B x s).2.1.2 h'⟩

/-- The exponential clock `2 ^ (n ^ e + e)`. -/
def clkE (e n : ℕ) : ℕ := 2 ^ (n ^ e + e)

/-- The exponential clock dominates the polynomial one. -/
theorem clock_le_clkE (e n : ℕ) : clock e n ≤ clkE e n :=
  Nat.lt_two_pow_self.le

/-- Every function `2 ^ p(n)` is dominated by some exponential clock, at every length. -/
theorem exists_clkE_ge (p : Polynomial ℕ) : ∃ e, ∀ n, 2 ^ p.eval n ≤ clkE e n := by
  obtain ⟨e, he⟩ := exists_clock_ge p
  exact ⟨e, fun n => Nat.pow_le_pow_right (by norm_num) (he n)⟩

/-- `EXP^B`: the sets decided by an oracle machine with oracle `B` which halts on every input `x`
within `2 ^ p(|x|)` steps for a polynomial `p`. -/
def ExpTimeOracle (B : Set BitString) : Set (Set BitString) :=
  {A | ∃ (M : OTM) (p : Polynomial ℕ),
    (∀ x : BitString, ∃ t : ℕ, t ≤ 2 ^ p.eval x.length ∧ Halted M (run M B x t)) ∧
    ∀ x : BitString, x ∈ A ↔ Accepts M B x}

/-- Any set in `EXP^B` is decided by a `clkE`-clocked coded machine with oracle `B`. -/
theorem exists_clockedE_of_expTime (B A : Set BitString) (h : A ∈ ExpTimeOracle B) :
    ∃ (c : OTMCode) (e : ℕ), ClockedDecidesW clkE c e B A := by
  obtain ⟨M, p, hp, hA⟩ := h
  obtain ⟨e, he⟩ := exists_clkE_ge p
  obtain ⟨c, hc⟩ := exists_clockedW_of_bound clkE M B A e (fun x => by
    obtain ⟨t, ht, hh⟩ := hp x
    exact ⟨t, ht.trans (he _), hh⟩) hA
  exact ⟨c, e, hc⟩

end Kolmogorov.RandomStrings
