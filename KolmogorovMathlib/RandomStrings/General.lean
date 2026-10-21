/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction
import KolmogorovMathlib.RandomStrings.Family

/-!
# The general theorem (Theorem `general` of the paper)

Let `𝓜` be a family of clocked oracle machines (`Family`: a clock function `clk`, the machine
`(c, e)` running for `clk e |x|` steps on the input `x`, and a property `Φ c e x` of the clocked
machine `(c, e)` on the input `x`, decidable from the code; the machine belongs to the family if
`∀ x, Φ c e x`).  Let `𝓒` be a class of languages that is closed under finite modifications and
contains, for every machine that belongs to the family on all but finitely many inputs, every
language "YES wins the local game `G_{e,x}` played on the possible queries minus a fixed finite
set, with hardwired values `T` and budget `2^{-m}`".  Then every decidable `A` that, for every
universal a priori complexity function `K`, is decided by a machine of the family with the oracle
`R_K`, belongs to `𝓒`.

The proof is the stage construction (`exists_built`) with the guarded games of `AFG/Family.lean`;
its only hypothesis besides decidability is `WitnessesExist`, which follows from `A ∉ 𝓒`
(`witnessesExist_of_class`, Claim 4 of the paper).

`general_clock` is the form for families with the polynomial clock `clock` (the games `gameOf`,
`ClockedDecides`).
-/

namespace Kolmogorov.RandomStrings

/-- The set of random strings with respect to the a priori complexity `HminApriori` is extensionally
equal to `RH (Hmin K F)`. -/
theorem RA_HminApriori (K : AprioriComplexity) (F : BitString → ℕ) (hF : IsEntropyFun F) :
    RA (HminApriori K F hF) = RH (Hmin K F) := by
  ext x
  rfl

/-- Claim 4 for a class `𝓒`: if `A ∉ 𝓒`, witnesses always exist.  Otherwise, beyond a finite set
`Z` no input is a witness; an input off the family is always a witness (its guarded game is
empty and won by YES iff `x ∉ A`, `val_gameOfF_of_not`), so the machine belongs to the family off
`Z`, and off `Z` the set `A` is the set of inputs on which YES wins the game of the construction,
which is in `𝓒` by `hgame`; hence `A ∈ 𝓒` by `hclosed`. -/
theorem witnessesExist_of_class [Family] (𝓒 : Set (Set BitString))
    (hclosed : ∀ (A B : Set BitString) (Z : Finset BitString), B ∈ 𝓒 →
      (∀ x, x ∉ Z → (x ∈ A ↔ x ∈ B)) → A ∈ 𝓒)
    (hgame : ∀ (c : OTMCode) (e : ℕ) (Z : Finset BitString), (∀ x, x ∉ Z → Family.Φ c e x) →
      ∀ (T : Table) (m : ℕ) (Y : Finset BitString),
        {x : BitString | val (gameOfT c (Family.clk e x.length) x T.fn ((2 : ℝ)⁻¹ ^ m)
          (querySet c.toOTM x (Family.clk e x.length) \ Y)) = true} ∈ 𝓒)
    (A : Set BitString) (hAC : A ∉ 𝓒) (γ : ℕ → OTMCode × ℕ) : WitnessesExist A γ := by
  intro σ e y hfin hfinK
  by_contra hcon
  push Not at hcon
  apply hAC
  obtain ⟨T, hT⟩ := exists_table_hval σ hfin hfinK
  obtain ⟨Z, hZ⟩ := exists_finset_encode_le y
  have hfun : σ.hval = T.fn := funext hT
  have hΦ : ∀ x, x ∉ Z → Family.Φ (γ e).1 (γ e).2 x := by
    intro x hx
    by_contra hnΦ
    apply hcon x (hZ x hx)
    have hps : playSet γ σ e x = ∅ := by
      unfold playSet
      rw [qsetF_of_not hnΦ]
      exact Finset.empty_sdiff _
    unfold IsWitness newGame
    rw [hps]
    exact val_gameOfF_of_not A _ (by positivity) hnΦ
  refine hclosed A _ Z (hgame (γ e).1 (γ e).2 Z hΦ T (e + σ.inj e + 6)
    ((Finset.range e).biUnion fun e' => (σ.game e').elim ∅ fun g => g.2.1)) fun x hx => ?_
  rw [Set.mem_ofPred_eq]
  have h1 := hcon x (hZ x hx)
  unfold IsWitness newGame playSet at h1
  rw [qsetF_of_Φ (hΦ x hx), gameOfF_of_Φ A _ _ _ (hΦ x hx), hfun] at h1
  tauto

/-- **Theorem `general`.**  For a family of clocked machines and a class `𝓒` closed under finite
modifications and containing the game languages of the machines of the family, every decidable
set decided, for every universal a priori complexity `K`, by a machine of the family with the
oracle `R_K`, belongs to `𝓒`. -/
theorem general [Family] (𝓒 : Set (Set BitString))
    (hclosed : ∀ (A B : Set BitString) (Z : Finset BitString), B ∈ 𝓒 →
      (∀ x, x ∉ Z → (x ∈ A ↔ x ∈ B)) → A ∈ 𝓒)
    (hgame : ∀ (c : OTMCode) (e : ℕ) (Z : Finset BitString), (∀ x, x ∉ Z → Family.Φ c e x) →
      ∀ (T : Table) (m : ℕ) (Y : Finset BitString),
        {x : BitString | val (gameOfT c (Family.clk e x.length) x T.fn ((2 : ℝ)⁻¹ ^ m)
          (querySet c.toOTM x (Family.clk e x.length) \ Y)) = true} ∈ 𝓒)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal →
      ∃ (c : OTMCode) (e : ℕ), (∀ x, Family.Φ c e x) ∧ ClockedDecidesW Family.clk c e (RA K) A) :
    A ∈ 𝓒 := by
  by_contra hnot
  obtain ⟨K₀, hK₀⟩ := exists_universal_apriori
  obtain ⟨b⟩ := exists_built A hA (witnessesExist_of_class 𝓒 hclosed hgame A hnot) K₀
  obtain ⟨c, e, hΦ, hce⟩ :=
    hK (HminApriori K₀ b.F b.entropy) (HminApriori_universal K₀ hK₀ b.F b.entropy)
  rw [RA_HminApriori] at hce
  exact b.foils c e hΦ hce

/-- **Theorem `general` for a family with the polynomial clock** (`Family.clk = clock`), stated
with the games `gameOf` and `ClockedDecides` (the form used for `P^R`, `P^R_tt`, `P^R_sa`). -/
theorem general_clock [Family] (hclk : ∀ e n, Family.clk e n = clock e n) (𝓒 : Set (Set BitString))
    (hclosed : ∀ (A B : Set BitString) (Z : Finset BitString), B ∈ 𝓒 →
      (∀ x, x ∉ Z → (x ∈ A ↔ x ∈ B)) → A ∈ 𝓒)
    (hgame : ∀ (c : OTMCode) (e : ℕ) (Z : Finset BitString), (∀ x, x ∉ Z → Family.Φ c e x) →
      ∀ (T : Table) (m : ℕ) (Y : Finset BitString),
        {x : BitString | val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
          (querySet c.toOTM x (clock e x.length) \ Y)) = true} ∈ 𝓒)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal →
      ∃ (c : OTMCode) (e : ℕ), (∀ x, Family.Φ c e x) ∧ ClockedDecides c e (RA K) A) :
    A ∈ 𝓒 := by
  have hc : (Family.clk : ℕ → ℕ → ℕ) = clock := funext₂ hclk
  refine general 𝓒 hclosed (fun c e Z hZ T m Y => ?_) A hA fun K hKU => ?_
  · rw [hc]
    exact hgame c e Z hZ T m Y
  · rw [hc]
    exact hK K hKU

end Kolmogorov.RandomStrings
