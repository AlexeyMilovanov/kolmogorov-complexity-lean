/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.Stages
import KolmogorovMathlib.RandomStrings.Construction.Mirror
import KolmogorovMathlib.RandomStrings.Construction.MirrorReply
import KolmogorovMathlib.RandomStrings.Construction.MirrorPrimrec
import KolmogorovMathlib.RandomStrings.Construction.MirrorBookkeeping
import KolmogorovMathlib.RandomStrings.Construction.Claim3
import KolmogorovMathlib.RandomStrings.Construction.Flips
import KolmogorovMathlib.RandomStrings.Construction.Evolution
import KolmogorovMathlib.RandomStrings.Construction.LiveGames
import KolmogorovMathlib.RandomStrings.Construction.LiveInv
import KolmogorovMathlib.RandomStrings.Construction.Claim2Stage
import KolmogorovMathlib.RandomStrings.Construction.Changes

/-!
# The stage construction (§3.2) and its three claims

The construction is generic over a family of clocked machines (`[Family]`, `AFG/Family.lean`).
Given a universal a priori complexity function `K` and a decidable set `A` for which witnesses
always exist (`WitnessesExist`; it follows from `A ∉ 𝓒` for a class `𝓒` as in
`AFG/General.lean`, e.g. `A ∉ EXPSPACE`), the construction produces a total function `F` with
computably enumerable overgraph such that, for `H = Hmin K F = min (K + 5, F + 3)`:

* (Claim 3) `∑_x 2^{-H(x)} ≤ 1/8`, hence `F` is a prefix-free entropy function;
* (Claim 2) every requirement `R_e` ("the `e`-th clocked machine does not decide `A` with
  oracle `R_H`, unless it is outside the family on some input") is satisfied;
* (Claim 4) the witness search at every stage terminates (the hypothesis `WitnessesExist`).

The construction enumerates all clocked machines; the game of `R_e` on an input outside the
family (`¬ Φ`) is the empty guarded game `gameOfF` whose outcome is `x ∉ A`, so such an input is
always a witness and the requirement is satisfied trivially (the machine is not in the family).
The interface `Built` records exactly what the rest of the proof needs.

The development lives in the modules `KolmogorovMathlib.RandomStrings.Construction.*`, in
dependency order: the state and the stages (`Stages`), their effective simulation (`Mirror`,
`MirrorReply`, `MirrorPrimrec`, `MirrorBookkeeping`), Claim 3 (`Claim3`, `Flips`, `Evolution`),
the live-game invariants of Claim 2 (`LiveGames`, `LiveInv`), and its limit lemmas
(`Claim2Stage`, `Changes`).  This module proves `limit_game_foils`, `Flim_foils` and the final
result `exists_built`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-- A permanent game satisfies its requirement (for a machine of the family): if the game of `e`
is `g = (x, X, m, st)` from stage `s₀` on, take a stage `s ≥ s₀` at which `H*` agrees with `H` on
the (finite) query set; the stored state is safe for us there (`live_game_safe`), so the outcome
of the current position is ours; since the machine belongs to the family on `x`, this outcome is
its verdict (`gameOfF_of_Φ`); the flipped strings are non-random (`live_game_flipped`), hence the
clocked machine sees the oracle `R_H` on its queries and errs on `x` (`live_game_side`). -/
theorem limit_game_foils (A : Set BitString) (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ)
    (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p) (e : ℕ) (s₀ : ℕ)
    (g : BitString × Finset BitString × ℕ × GState)
    (hg : ∀ s, s₀ ≤ s → (stage A γ enumK s).game e = some g)
    (hΦ : ∀ x, Family.Φ (reqγ γ e).1 (reqγ γ e).2 x) :
    ¬ ClockedDecidesW Family.clk (reqγ γ e).1 (reqγ γ e).2 (RH (Hmin K (Flim A γ enumK))) A := by
  classical
  intro hdec
  choose f hf using fun z => hval_eventually_eq_Hmin A K γ enumK henum z
  set Q := querySet (reqγ γ e).1.toOTM g.1 (Family.clk (reqγ γ e).2 g.1.length) with hQdef
  set s := max s₀ (Q.sup f) with hsdef
  have hs0 : s₀ ≤ s := le_max_left _ _
  have hQ : ∀ z ∈ Q, (stage A γ enumK s).hval z = Hmin K (Flim A γ enumK) z := fun z hz =>
    hf z s ((Finset.le_sup hz).trans (le_max_right _ _))
  have hgs := hg s hs0
  have hside := live_game_side A γ enumK s e g hgs
  have hflip := (live_game_flipped A γ enumK s e g hgs).2
  have hsafe := live_game_safe A γ enumK s e g hgs
  have hagree : ∀ z ∈ Q, (z ∈ oracleOf (stage A γ enumK s).hval g.2.2.2.S ↔
      z ∈ RH (Hmin K (Flim A γ enumK))) := by
    intro z hz
    simp only [oracleOf, RH, Set.mem_ofPred_eq]
    rw [← hQ z hz]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, fun hzS => ?_⟩
      have := hflip z hzS
      omega
  have hiff := clockedAcceptsT_iff_of_agree (reqγ γ e).1 (Family.clk (reqγ γ e).2 g.1.length) _ _
    g.1 hagree
  cases hturn : g.2.2.2.yesTurn
  · have hxA : g.1 ∉ A := hside.1 hturn
    have hsafe' : SafeYes (curGame A (reqγ γ) (stage A γ enumK s) e g) g.2.2.2 := by
      simpa [SafeFor, hturn] using hsafe
    have ho := hsafe'.outcome
    simp only [curGame] at ho
    rw [gameOfF_of_Φ A _ _ _ (hΦ g.1)] at ho
    simp only [gameOfT] at ho
    exact hxA ((hdec g.1).2 (hiff.1 (of_decide_eq_true ho)))
  · have hxA : g.1 ∈ A := by
      by_contra hx
      have := hside.2 hx
      rw [hturn] at this
      exact Bool.noConfusion this
    have hsafe' : SafeNo (curGame A (reqγ γ) (stage A γ enumK s) e g) g.2.2.2 := by
      simpa [SafeFor, hturn] using hsafe
    have ho := hsafe'.outcome
    simp only [curGame] at ho
    rw [gameOfF_of_Φ A _ _ _ (hΦ g.1)] at ho
    simp only [gameOfT] at ho
    exact (of_decide_eq_false ho) (hiff.2 ((hdec g.1).1 hxA))

/-- Claim 2: every requirement for a machine of the family is eventually satisfied. -/
theorem Flim_foils (A : Set BitString) (hW : ∀ γ', WitnessesExist A γ') (K : AprioriComplexity)
    (γ : ℕ → OTMCode × ℕ) (hγ : Function.Surjective γ) (enumK : ℕ → BitString × ℕ)
    (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p)
    (c : OTMCode) (e : ℕ) (hΦ : ∀ x, Family.Φ c e x) :
    ¬ ClockedDecidesW Family.clk c e (RH (Hmin K (Flim A γ enumK))) A := by
  obtain ⟨k, hk⟩ := hγ (c, e)
  obtain ⟨s₀, g, hg⟩ :=
    game_eventually_const A hW K γ enumK henum (k + 1) (Nat.succ_pos k)
  have hre : reqγ γ (k + 1) = (c, e) := by simp [reqγ, hk]
  have h := limit_game_foils A K γ enumK henum (k + 1) s₀ g hg (by rw [hre]; exact hΦ)
  rw [hre] at h
  exact h

/-- The construction, packaged. -/
theorem exists_built (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hW : ∀ γ', WitnessesExist A γ') (K : AprioriComplexity) : Nonempty (Built A K) := by
  obtain ⟨γ, hγ, hγe⟩ := exists_enum_computable
  obtain ⟨enumK, hKc, h₁, h₂⟩ := exists_enumK_computable K
  have henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p := by
    intro p
    refine ⟨h₂ p, ?_⟩
    rintro ⟨s, rfl⟩
    exact h₁ s
  exact ⟨⟨Flim A γ enumK, Flim_entropy A hA hW K γ hγe enumK hKc henum,
    fun c e hΦ => Flim_foils A hW K γ hγ enumK henum c e hΦ⟩⟩

end Kolmogorov.RandomStrings
