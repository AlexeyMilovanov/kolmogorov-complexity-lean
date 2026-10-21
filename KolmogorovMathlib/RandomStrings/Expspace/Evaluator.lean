/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.QEnum

/-!
# The game evaluator: an exact finite recursion for `SafeYes`

When the flip costs and the budget are dyadic with a common precision, `SafeYes` is computed by
the finite recursion `safeYesB` over the positions; this module proves its correctness
(`safeYesB_iff`, `gameValB_eq_val`) and instantiates it for the game of `exists_gameProg` at the
precision `gameN`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

/-! ### The game evaluator: an exact finite recursion for `SafeYes`

When all flip costs and the budget are multiples of `2⁻¹ ^ N` (numerators `c z` and `E`), the
scores reachable in the game are `y / 2 ^ N` and `n / 2 ^ N` with `y n : ℕ`, and `SafeYes` (NO to
move) is computed by the finite recursion `safeYesB` over the positions `S ⊆ X`, with fuel
`≥ |X \ S|` (every non-passing move flips a new string).  `safeYesB_iff` and `gameValB_eq_val`
are its correctness (induction on the fuel, i.e. well-founded induction on the number of
unflipped strings); `gameValB_gameOf` instantiates it for the game of `exists_gameProg` at the
precision `gameN`; the stack program computing `gameValB` is `exists_evalStmt` (remaining). -/

/-- The numerator of the cost of the move `S ↦ S'`. -/
def costN (c : BitString → ℕ) (S S' : Finset BitString) : ℕ := ∑ z ∈ S' \ S, c z

/-- Safety for YES at the position `S` with scores `y / 2 ^ N` (YES) and `n / 2 ^ N` (NO), NO to
move, computed with fuel `f`: the outcome is `true`, and every legal non-passing NO move `S'` has
a legal YES answer `R ⊇ S'` (`R = S'` is a pass) to a position safe for YES. -/
def safeYesB (X : Finset BitString) (c : BitString → ℕ) (E : ℕ) (out : Finset BitString → Bool) :
    ℕ → Finset BitString → ℕ → ℕ → Bool
  | 0, S, _, _ => out S
  | f + 1, S, y, n => out S && decide (∀ S' ∈ X.powerset, S ⊂ S' → n + costN c S S' ≤ E →
      ∃ R ∈ X.powerset, S' ⊆ R ∧ y + costN c S' R ≤ E ∧
        safeYesB X c E out f R (y + costN c S' R) (n + costN c S S') = true)

/-- The value of the game by the finite recursion: YES has a legal first move `S₁` (`S₁ = ∅` is a
pass) to a position safe for YES. -/
def gameValB (X : Finset BitString) (c : BitString → ℕ) (E : ℕ)
    (out : Finset BitString → Bool) : Bool :=
  decide (∃ S₁ ∈ X.powerset, costN c ∅ S₁ ≤ E ∧
    safeYesB X c E out X.card S₁ (costN c ∅ S₁) 0 = true)

/-- Two rational fractions with the denominator `2 ^ N` sum to at most `E / 2 ^ N` if and only if
their numerators sum to at most `E`. -/
theorem natCast_div_two_pow_add_le_iff (a b E N : ℕ) :
    (a : ℝ) / 2 ^ N + (b : ℝ) / 2 ^ N ≤ (E : ℝ) / 2 ^ N ↔ a + b ≤ E := by
  rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

/-- The sum of two rational fractions with the denominator `2 ^ N` is the fraction of the sum of
their numerators. -/
theorem natCast_div_two_pow_add (a b N : ℕ) :
    (a : ℝ) / 2 ^ N + (b : ℝ) / 2 ^ N = ((a + b : ℕ) : ℝ) / 2 ^ N := by
  push_cast; ring

/-- `SafeYes` unfolded once. -/
theorem safeYes_iff_eval (d : GameData) (st : GState) : SafeYes d st ↔ d.outcome st.S = true ∧
    ∀ S', LegalMove d st S' → S' ≠ st.S → ∃ R, LegalMove d (applyMove d st S') R ∧
      SafeYes d (applyMove d (applyMove d st S') R) := by
  classical
  constructor
  · intro h
    cases h with
    | intro _ reply hout hlegal hsafe =>
      exact ⟨hout, fun S' hL hne => ⟨reply S', hlegal S' hL hne, hsafe S' hL hne⟩⟩
  · rintro ⟨hout, h⟩
    refine SafeYes.intro st (fun S' => if hh : LegalMove d st S' ∧ S' ≠ st.S then
      Classical.choose (h S' hh.1 hh.2) else S') hout ?_ ?_
    · intro S' hL hne
      rw [dite_eq_left ⟨hL, hne⟩]; exact (Classical.choose_spec (h S' hL hne)).1
    · intro S' hL hne
      rw [dite_eq_left ⟨hL, hne⟩]; exact (Classical.choose_spec (h S' hL hne)).2

section Evaluator

variable (d : GameData) (N : ℕ) (c : BitString → ℕ) (E : ℕ)

/-- The cost of the move `S ↦ S'` is `costN c S S' / 2 ^ N` if all flip costs are `c z / 2 ^ N`. -/
theorem moveCost_eq_costN (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N)
    {S S' : Finset BitString} (hS' : S' ⊆ d.X) : moveCost d S S' = (costN c S S' : ℝ) / 2 ^ N := by
  unfold moveCost costN
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun z hz => hc z (hS' (Finset.mem_sdiff.1 hz).1)

/-- A NO move from `S` to `S'` is legal with YES score `y / 2 ^ N` and NO score `n / 2 ^ N` if and
only if `S ⊆ S'`, `S' ⊆ d.X`, and the new NO score numerator `n + costN c S S'` is at most `E`. -/
theorem legalMove_no_iff_fix (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N)
    (hε : d.ε = (E : ℝ) / 2 ^ N) (S S' : Finset BitString) (y n : ℕ) :
    LegalMove d ⟨S, (y : ℝ) / 2 ^ N, (n : ℝ) / 2 ^ N, false⟩ S' ↔
      S ⊆ S' ∧ S' ⊆ d.X ∧ n + costN c S S' ≤ E := by
  change (S ⊆ S' ∧ S' ⊆ d.X ∧ (if false = true then (y : ℝ) / 2 ^ N + moveCost d S S' ≤ d.ε
    else (n : ℝ) / 2 ^ N + moveCost d S S' ≤ d.ε)) ↔ _
  rw [ite_eq_right Bool.false_ne_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [moveCost_eq_costN d N c hc h2, hε, natCast_div_two_pow_add_le_iff] at h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [moveCost_eq_costN d N c hc h2, hε, natCast_div_two_pow_add_le_iff]
    exact h3

/-- A YES move from `S'` to `R` is legal with YES score `y / 2 ^ N` and NO score `nn` if and only if
`S' ⊆ R`, `R ⊆ d.X`, and the new YES score numerator `y + costN c S' R` is at most `E`. -/
theorem legalMove_yes_iff_fix (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N)
    (hε : d.ε = (E : ℝ) / 2 ^ N) (S' R : Finset BitString) (y : ℕ) (nn : ℝ) :
    LegalMove d ⟨S', (y : ℝ) / 2 ^ N, nn, true⟩ R ↔
      S' ⊆ R ∧ R ⊆ d.X ∧ y + costN c S' R ≤ E := by
  change (S' ⊆ R ∧ R ⊆ d.X ∧ (if true = true then (y : ℝ) / 2 ^ N + moveCost d S' R ≤ d.ε
    else nn + moveCost d S' R ≤ d.ε)) ↔ _
  rw [ite_eq_left rfl]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [moveCost_eq_costN d N c hc h2, hε, natCast_div_two_pow_add_le_iff] at h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [moveCost_eq_costN d N c hc h2, hε, natCast_div_two_pow_add_le_iff]
    exact h3

/-- Applying a NO move to `S'` from `S` updates the NO score numerator to `n + costN c S S'` and
flips the turn to YES. -/
theorem applyMove_no_fix (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N)
    (S S' : Finset BitString)
    (y n : ℕ) (hS' : S' ⊆ d.X) :
    applyMove d ⟨S, (y : ℝ) / 2 ^ N, (n : ℝ) / 2 ^ N, false⟩ S' =
      ⟨S', (y : ℝ) / 2 ^ N, ((n + costN c S S' : ℕ) : ℝ) / 2 ^ N, true⟩ := by
  change (⟨S', if false = true then _ else (y : ℝ) / 2 ^ N,
    if false = true then (n : ℝ) / 2 ^ N else (n : ℝ) / 2 ^ N + moveCost d S S', !false⟩ :
      GState) = _
  rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
    moveCost_eq_costN d N c hc hS', natCast_div_two_pow_add]
  rfl

/-- Applying a YES move to `R` from `S'` updates the YES score numerator to `y + costN c S' R` and
flips the turn to NO. -/
theorem applyMove_yes_fix (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N)
    (S' R : Finset BitString)
    (y : ℕ) (nn : ℝ) (hR : R ⊆ d.X) :
    applyMove d ⟨S', (y : ℝ) / 2 ^ N, nn, true⟩ R =
      ⟨R, ((y + costN c S' R : ℕ) : ℝ) / 2 ^ N, nn, false⟩ := by
  change (⟨R, if true = true then (y : ℝ) / 2 ^ N + moveCost d S' R else (y : ℝ) / 2 ^ N,
    if true = true then nn else nn + moveCost d S' R, !true⟩ : GState) = _
  rw [ite_eq_left rfl, ite_eq_left rfl, moveCost_eq_costN d N c hc hR, natCast_div_two_pow_add]
  rfl

/-- **Correctness of the recursion** (induction on the fuel `≥ |X \ S|`). -/
theorem safeYesB_iff (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N)
    (hε : d.ε = (E : ℝ) / 2 ^ N) : ∀ (f : ℕ) (S : Finset BitString) (y n : ℕ), S ⊆ d.X →
      (d.X \ S).card ≤ f →
      (safeYesB d.X c E d.outcome f S y n = true ↔
        SafeYes d ⟨S, (y : ℝ) / 2 ^ N, (n : ℝ) / 2 ^ N, false⟩) := by
  intro f
  induction f with
  | zero =>
    intro S y n hSX hcard
    have hXS : d.X ⊆ S := by
      intro z hz
      by_contra hzS
      have h1 := Finset.card_pos.2 ⟨z, Finset.mem_sdiff.2 ⟨hz, hzS⟩⟩
      omega
    rw [safeYes_iff_eval]
    simp only [safeYesB]
    constructor
    · intro h
      refine ⟨h, fun S' hL hne => absurd ?_ hne⟩
      exact Finset.Subset.antisymm (hL.2.1.trans hXS) hL.1
    · intro h; exact h.1
  | succ f ih =>
    intro S y n hSX hcard
    rw [safeYes_iff_eval]
    simp only [safeYesB, Bool.and_eq_true, decide_eq_true_eq]
    refine and_congr Iff.rfl ⟨fun H S' hL hne => ?_, fun H S' hS'P hss hcost => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := (legalMove_no_iff_fix d N c E hc hε S S' y n).1 hL
      obtain ⟨R, hRP, hS'R, hRc, hsafe⟩ := H S' (Finset.mem_powerset.2 h2)
        (Finset.ssubset_iff_subset_ne.2 ⟨h1, fun h => hne h.symm⟩) h3
      have hRX := Finset.mem_powerset.1 hRP
      have hlt := card_sdiff_lt (h1.trans hS'R) hRX
        (fun h => hne (Finset.Subset.antisymm (hS'R.trans h.subset) h1))
      refine ⟨R, ?_, ?_⟩
      · rw [applyMove_no_fix d N c hc S S' y n h2, legalMove_yes_iff_fix d N c E hc hε]
        exact ⟨hS'R, hRX, hRc⟩
      · rw [applyMove_no_fix d N c hc S S' y n h2, applyMove_yes_fix d N c hc S' R y _ hRX]
        exact (ih R _ _ hRX (by omega)).1 hsafe
    · have h2 := Finset.mem_powerset.1 hS'P
      have h1 := (Finset.ssubset_iff_subset_ne.1 hss).1
      have hne : S' ≠ S := fun h => (Finset.ssubset_iff_subset_ne.1 hss).2 h.symm
      obtain ⟨R, hLR, hsafe⟩ :=
        H S' ((legalMove_no_iff_fix d N c E hc hε S S' y n).2 ⟨h1, h2, hcost⟩) hne
      rw [applyMove_no_fix d N c hc S S' y n h2] at hLR hsafe
      obtain ⟨hS'R, hRX, hRc⟩ := (legalMove_yes_iff_fix d N c E hc hε S' R y _).1 hLR
      rw [applyMove_yes_fix d N c hc S' R y _ hRX] at hsafe
      have hlt := card_sdiff_lt (h1.trans hS'R) hRX
        (fun h => hne (Finset.Subset.antisymm (hS'R.trans h.subset) h1))
      exact ⟨R, Finset.mem_powerset.2 hRX, hS'R, hRc, (ih R _ _ hRX (by omega)).2 hsafe⟩

/-- **The finite recursion computes the value of the game**, whenever the flip costs on `X` and
the budget are the multiples `c z / 2 ^ N` and `E / 2 ^ N`. -/
theorem gameValB_eq_val (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N)
    (hε : d.ε = (E : ℝ) / 2 ^ N) : gameValB d.X c E d.outcome = val d := by
  rw [Bool.eq_iff_iff, determined]
  unfold gameValB YesWinsInit
  rw [decide_eq_true_eq]
  have hinit : GState.init = ⟨∅, ((0 : ℕ) : ℝ) / 2 ^ N, 0, true⟩ := by simp [GState.init]
  have h0 : (0 : ℝ) = ((0 : ℕ) : ℝ) / 2 ^ N := by simp
  rw [hinit]
  constructor
  · rintro ⟨S₁, hP, hcost, hsafe⟩
    have hS₁ := Finset.mem_powerset.1 hP
    refine ⟨S₁, (legalMove_yes_iff_fix d N c E hc hε ∅ S₁ 0 0).2
      ⟨Finset.empty_subset _, hS₁, by simpa using hcost⟩, ?_⟩
    rw [applyMove_yes_fix d N c hc ∅ S₁ 0 0 hS₁, h0, Nat.zero_add]
    exact (safeYesB_iff d N c E hc hε _ S₁ _ 0 hS₁
      (Finset.card_le_card Finset.sdiff_subset)).1 hsafe
  · rintro ⟨S₁, hL, hsafe⟩
    obtain ⟨-, hS₁, hcost⟩ := (legalMove_yes_iff_fix d N c E hc hε ∅ S₁ 0 0).1 hL
    rw [applyMove_yes_fix d N c hc ∅ S₁ 0 0 hS₁, h0, Nat.zero_add] at hsafe
    refine ⟨S₁, Finset.mem_powerset.2 hS₁, by simpa using hcost, ?_⟩
    exact (safeYesB_iff d N c E hc hε _ S₁ _ 0 hS₁
      (Finset.card_le_card Finset.sdiff_subset)).2 hsafe

end Evaluator

/-! #### The game of `exists_gameProg` at the precision `gameN` -/

/-- The precision used for the game `G_{e,x}` on inputs of length `n`: every string in play has
length `≤ clock e n`, hence value `T.fn z ≤ 2 · clock e n + 6 + max T.value`, and the budget is
`2⁻¹ ^ m`. -/
def gameN (e : ℕ) (T : Table) (m n : ℕ) : ℕ := 2 * clock e n + 6 + m + T.dom.sup T.value

/-- The numerator, at precision `N`, of the cost of flipping a string of length `ℓ` and value
`h`: `2 ^ (N - (ℓ - 1)) - 2 ^ (N - h)` if `ℓ - 1 ≤ h`, else `0`. -/
def costNum (N h ℓ : ℕ) : ℕ := if ℓ - 1 ≤ h then 2 ^ (N - (ℓ - 1)) - 2 ^ (N - h) else 0

/-- The quotient `2 ^ (N - a) / 2 ^ N` is `2⁻¹ ^ a`. -/
theorem two_pow_sub_div_two_pow (N a : ℕ) (h : a ≤ N) :
    (2 : ℝ) ^ (N - a) / 2 ^ N = (2 : ℝ)⁻¹ ^ a := by
  have h2 : (2 : ℝ) ^ N = 2 ^ (N - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [h2, inv_pow]
  field_simp

/-- The maximum of `0` and `2⁻¹ ^ a - 2⁻¹ ^ b` is `(2 ^ (N - a) - 2 ^ (N - b)) / 2 ^ N` if `a ≤ b`,
else `0`. -/
theorem max_sub_eq_div (N a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) :
    max 0 ((2 : ℝ)⁻¹ ^ a - (2 : ℝ)⁻¹ ^ b) =
      ((if a ≤ b then 2 ^ (N - a) - 2 ^ (N - b) else 0 : ℕ) : ℝ) / 2 ^ N := by
  split_ifs with hab
  · have hle : 2 ^ (N - b) ≤ 2 ^ (N - a) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow : (2 : ℝ)⁻¹ ^ b ≤ (2 : ℝ)⁻¹ ^ a :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hab
    rw [max_eq_right (by linarith), Nat.cast_sub hle, sub_div]
    push_cast
    rw [two_pow_sub_div_two_pow N a ha, two_pow_sub_div_two_pow N b hb]
  · have hpow : (2 : ℝ)⁻¹ ^ a ≤ (2 : ℝ)⁻¹ ^ b :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [max_eq_left (by linarith)]
    simp

/-- The flip costs of the game of `exists_gameProg` are the multiples `costNum … / 2 ^ gameN`. -/
theorem gameOf_flipCost_eq (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString)
    (x z : BitString)
    (hz : z ∈ querySet c.toOTM x (clock e x.length) \ Y) :
    flipCost (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)) z =
      (costNum (gameN e T m x.length) (T.fn z) z.length : ℝ) / 2 ^ gameN e T m x.length := by
  have hlen : z.length ≤ clock e x.length := length_le_of_mem_queryAll _ _ _ z
    ((mem_querySet_iff_queryAll _ _ _ z).1 (Finset.mem_sdiff.1 hz).1)
  have hT : T.fn z ≤ 2 * z.length + 6 + T.dom.sup T.value := by
    unfold Table.fn
    split_ifs with h
    · have := Finset.le_sup (f := T.value) h; omega
    · omega
  change max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ T.fn z) = _
  rw [max_sub_eq_div (gameN e T m x.length) (z.length - 1) (T.fn z) (by unfold gameN; omega)
    (by unfold gameN; omega)]
  rfl

/-- The budget of the game of `exists_gameProg` is `2 ^ (gameN - m) / 2 ^ gameN`. -/
theorem gameOf_eps_eq (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (x : BitString)
    (X : Finset BitString) :
    (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) X).ε =
      ((2 ^ (gameN e T m x.length - m) : ℕ) : ℝ) / 2 ^ gameN e T m x.length := by
  change (2 : ℝ)⁻¹ ^ m = _
  push_cast
  rw [two_pow_sub_div_two_pow _ _ (by unfold gameN; omega)]

/-- The value of the game of `exists_gameProg` is computed by the finite recursion with the cost
numerators `costNum` and the budget numerator `2 ^ (gameN - m)`. -/
theorem gameValB_gameOf (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString)
    (x : BitString) :
    gameValB (querySet c.toOTM x (clock e x.length) \ Y)
        (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
        (2 ^ (gameN e T m x.length - m))
        (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)).outcome =
      val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)) :=
  gameValB_eq_val _ (gameN e T m x.length) _ _
    (fun z hz => gameOf_flipCost_eq c e T m Y x z hz) (gameOf_eps_eq c e T m x _)

/-- The value of the game of `exists_gameProg` is computed by the finite recursion at any
precision `N` bounding the exponents `|z| - 1` and `T.fn z` of the strings in play and the budget
exponent `m`. -/
theorem gameValB_gameOf_of_le (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (x : BitString)
    (X : Finset BitString) (N : ℕ) (hN : ∀ z ∈ X, z.length - 1 ≤ N ∧ T.fn z ≤ N) (hm : m ≤ N) :
    gameValB X (fun z => costNum N (T.fn z) z.length) (2 ^ (N - m))
        (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) X).outcome =
      val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) X) :=
  gameValB_eq_val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) X) N (fun z => costNum N (T.fn z) z.length)
    (2 ^ (N - m))
    (fun z hz => by
      change max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ T.fn z) = _
      rw [max_sub_eq_div N _ _ (hN z hz).1 (hN z hz).2]
      rfl)
    (by
      change (2 : ℝ)⁻¹ ^ m = _
      push_cast
      rw [two_pow_sub_div_two_pow _ _ hm])

/-- Stacks `0, …, |l| - 1` hold the entries of `l`, all the other stacks are empty. -/
def Stacks.layout (k : ℕ) (l : List BitString) : Stacks k := fun r => l.getD r.val []

/-- The `n`-th element of a list of length at most `n` is the default value, here the empty list. -/
theorem Stacks.getD_nil_of_le {l : List BitString} {n : ℕ} (h : l.length ≤ n) :
    l.getD n [] = [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- The input stacks for a string `x` are the layout of the singleton list `[x]`. -/
theorem Stacks.input_eq_layout (k : ℕ) (x : BitString) :
    Stacks.input k x = Stacks.layout k [x] := by
  funext r
  unfold Stacks.input Stacks.layout
  split_ifs with h
  · simp [h]
  · obtain ⟨n, hn⟩ : ∃ n, r.val = n + 1 := ⟨r.val - 1, by omega⟩
    simp [hn]

/-- Accessing the layout of `l` over `K` stacks with an index `< k` is the same as accessing its
layout over `k` stacks. -/
theorem Stacks.layout_castLE {k K : ℕ} (h : k ≤ K) (l : List BitString) :
    (fun r => Stacks.layout K l (Fin.castLE h r)) = Stacks.layout k l := by
  funext r
  simp [Stacks.layout]

/-- Extending the layout of `l` over `k` stacks to `K` stacks with the layout of `l'` is the layout
of `l` over `K` stacks, since both lists fit in the first `k` stacks and the rest are empty. -/
theorem Stacks.extend_castLE_layout {k K : ℕ} (h : k ≤ K) (l l' : List BitString)
    (hl : l.length ≤ k)
    (hl' : l'.length ≤ k) :
    Function.extend (Fin.castLE h) (Stacks.layout k l) (Stacks.layout K l') =
      Stacks.layout K l := by
  funext j
  by_cases hj : j.val < k
  · have e : j = Fin.castLE h ⟨j.val, hj⟩ := Fin.ext rfl
    rw [e, (Fin.castLE_injective h).extend_apply]
    simp [Stacks.layout]
  · rw [Function.extend_apply']
    · simp only [Stacks.layout]
      rw [Stacks.getD_nil_of_le (by omega), Stacks.getD_nil_of_le (by omega)]
    · rintro ⟨i, rfl⟩
      exact hj (by simp)

/-- The sum of the lengths of the stacks outside the first `k` stacks in the layout of `l` over `K`
stacks is zero, as `l` fits in the first `k` stacks. -/
theorem Stacks.rest_castLE_layout {k K : ℕ} (h : k ≤ K) (l : List BitString) (hl : l.length ≤ k) :
    Stacks.rest (Fin.castLE h) (Stacks.layout K l) = 0 := by
  classical
  unfold Stacks.rest
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjk : k ≤ j.val := by
    by_contra hlt
    have hlt' : j.val < k := by omega
    refine (Finset.mem_compl.1 hj) (Finset.mem_image.2 ⟨⟨j.val, hlt'⟩, Finset.mem_univ _, ?_⟩)
    exact Fin.ext rfl
  simp only [Stacks.layout]
  rw [Stacks.getD_nil_of_le (by omega)]
  rfl

/-- The position `S` as a bit vector aligned with the list `LX` of the board. -/
def Stacks.posBits (LX : List BitString) (S : Finset BitString) : BitString :=
  LX.map fun z => decide (z ∈ S)

/-- The space used by the layout of `l` over `K` stacks is the sum of the lengths of the strings
in `l`. -/
theorem Stacks.space_layout {K : ℕ} (l : List BitString) (hl : l.length ≤ K) :
    Stacks.space (Stacks.layout K l) = (l.map List.length).sum := by
  unfold Stacks.space Stacks.layout
  rw [Fin.sum_univ_eq_sum_range (fun n => (l.getD n []).length) K]
  induction l generalizing K with
  | nil => simp
  | cons a l ih =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by simp at hl; omega⟩
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [ih (by simp at hl; omega)]
    ring

/-- The length of a list of strings is at most the length of its stack encoding. -/
theorem Stacks.length_le_length_encList (L : List BitString) :
    L.length ≤ (Stacks.encList L).length := by
  rw [Stacks.length_encList]
  induction L with
  | nil => simp
  | cons z L ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-- The sum of the lengths of a subset of stacks is at most the total space used by all stacks. -/
theorem Stacks.rest_le_space {k k' : ℕ} (f : Fin k → Fin k') (τ : Stacks k') :
    Stacks.rest f τ ≤ τ.space := by
  unfold Stacks.rest Stacks.space
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end Kolmogorov.RandomStrings
