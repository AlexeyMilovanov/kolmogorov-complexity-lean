/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Dynamics
import KolmogorovMathlib.Oracle.Joins
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Size
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Attained oracle minimization

A quantity `q` on oracles (valued in `EReal`, or in `ℝ≥0∞`) is *antitone* when a Turing-stronger
oracle never gives a larger value.  This file proves the order-theoretic part of the
point-to-set principles: if `Q` is a lower bound of `q` above a base oracle `C`, and for every
rational `r` with `Q < r` some oracle `A ≥ᵀ C` has `q A < r`, then the bound `Q` is *attained*,
i.e. some `B ≥ᵀ C` has `q B = Q`.  The witness is the join of `C` with a countable family of
almost-achieving oracles, so the proof never needs arithmetic on the infinite endpoints.

* `exists_achieving_oracle` is the attainment theorem for `EReal`-valued quantities
  (blueprint node `order:attainment`), with the companions
  `exists_achieving_oracle_stable` (every oracle above the witness also attains `Q`),
  `exists_achieving_oracle_all` (the bound `Q` holds for every oracle, not only above `C`) and
  `exists_achieving_oracle_cone` (the witness can be chosen above any prescribed oracle).
* The `exists_achieving_oracle_ennreal*` versions are the same statements for
  `ℝ≥0∞`-valued quantities, where it suffices to use positive rational thresholds.

These are used by the lower and upper point-to-set principles for pressure and for
Barreira–Schmeling dimension to turn "the infimum over oracles" into a minimum, attained in
every upper cone of oracles.
-/

namespace Kolmogorov.PointToSet
open scoped ENNReal Computability

/-- An extended real below every `-j` is `⊥`. -/
private lemma eq_bot_of_forall_le_neg_nat {y : EReal}
    (h : ∀ j : ℕ, y ≤ ((-(j : ℝ) : ℝ) : EReal)) : y = ⊥ := by
  induction y using EReal.rec with
  | bot => rfl
  | top => exact absurd (h 0) (not_le.mpr (EReal.coe_lt_top _))
  | coe y =>
    obtain ⟨j, hj⟩ := exists_nat_gt (-y)
    have := EReal.coe_le_coe_iff.mp (h j)
    linarith

/-- An extended real above `x` and below every `x + 1 / (j + 1)` equals `x`. -/
private lemma eq_of_le_add_inv_nat {y : EReal} {x : ℝ} (hxy : (x : EReal) ≤ y)
    (h : ∀ j : ℕ, y ≤ ((x + 1 / ((j : ℝ) + 1) : ℝ) : EReal)) : y = x := by
  induction y using EReal.rec with
  | bot => simp at hxy
  | top => exact absurd (h 0) (not_le.mpr (EReal.coe_lt_top _))
  | coe y =>
    refine congrArg _ (le_antisymm ?_ (EReal.coe_le_coe_iff.mp hxy))
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    have := EReal.coe_le_coe_iff.mp (h j)
    linarith

/-- If for every `j` some oracle above `C` has `q` at most `b j`, then a single oracle above `C`
has `q` at most `b j` for all `j` at once (take the join of `C` with the countable join of the
witnesses). -/
private lemma exists_oracle_below_all {α : Type*} [Preorder α] (q : Set ℕ → α) (C : Set ℕ)
    (b : ℕ → α) (hanti : ∀ A B, charOracle A ≤ᵀ charOracle B → q B ≤ q A)
    (h : ∀ j, ∃ A, charOracle C ≤ᵀ charOracle A ∧ q A ≤ b j) :
    ∃ B, charOracle C ≤ᵀ charOracle B ∧ ∀ j, q B ≤ b j := by
  choose A _ hqA using h
  refine ⟨oracleJoin C (oracleCountableJoin A), oracle_joins C _, fun j ↦ ?_⟩
  exact (hanti _ _ ((oracle_joins_countable A j).trans
    (oracle_joins_right C (oracleCountableJoin A)))).trans (hqA j)

/-- A signed oracle-antitone quantity with a cone lower bound and rational almost-achievers
attains the lower bound, including either infinite endpoint. Blueprint node `order:attainment`. -/
theorem exists_achieving_oracle (q : Set ℕ → EReal) (Q : EReal) (C : Set ℕ)
    (hanti : ∀ A B, charOracle A ≤ᵀ charOracle B → q B ≤ q A)
    (hlower : ∀ A, charOracle C ≤ᵀ charOracle A → Q ≤ q A)
    (happrox : ∀ r : ℚ, Q < ((r : ℝ) : EReal) →
      ∃ A, charOracle C ≤ᵀ charOracle A ∧ q A < ((r : ℝ) : EReal)) :
    ∃ B, charOracle C ≤ᵀ charOracle B ∧ q B = Q := by
  cases Q with
  | top =>
    exact ⟨C, TuringReducible.refl _, top_le_iff.mp (hlower C (TuringReducible.refl _))⟩
  | bot =>
    obtain ⟨B, hCB, hB⟩ := exists_oracle_below_all q C (fun j : ℕ ↦ ((-(j : ℝ) : ℝ) : EReal))
      hanti fun j ↦ by
        obtain ⟨A, hCA, hA⟩ := happrox (-(j : ℚ)) (EReal.bot_lt_coe _)
        exact ⟨A, hCA, by simpa using hA.le⟩
    exact ⟨B, hCB, eq_bot_of_forall_le_neg_nat hB⟩
  | coe x =>
    obtain ⟨B, hCB, hB⟩ := exists_oracle_below_all q C
      (fun j : ℕ ↦ ((x + 1 / ((j : ℝ) + 1) : ℝ) : EReal)) hanti fun j ↦ by
        have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
        obtain ⟨r, hxr, hr⟩ := exists_rat_btwn (show x < x + 1 / ((j : ℝ) + 1) by linarith)
        obtain ⟨A, hCA, hA⟩ := happrox r (EReal.coe_lt_coe_iff.mpr hxr)
        exact ⟨A, hCA, hA.le.trans (EReal.coe_le_coe_iff.mpr hr.le)⟩
    exact ⟨B, hCB, eq_of_le_add_inv_nat (hlower B hCB) hB⟩

/-- Once the signed lower bound is attained above the base, every stronger oracle attains
it as well. Blueprint node `order:attainment`. -/
theorem exists_achieving_oracle_stable (q : Set ℕ → EReal) (Q : EReal) (C B : Set ℕ)
    (hanti : ∀ A D, charOracle A ≤ᵀ charOracle D → q D ≤ q A)
    (hlower : ∀ A, charOracle C ≤ᵀ charOracle A → Q ≤ q A)
    (hCB : charOracle C ≤ᵀ charOracle B) (hB : q B = Q) :
    ∀ A, charOracle B ≤ᵀ charOracle A → q A = Q := fun A hBA ↦
  le_antisymm (hB ▸ hanti B A hBA) (hlower A (hCB.trans hBA))

/-- The signed cone lower bound holds for every oracle by joining with the base.
Blueprint node `order:attainment`. -/
theorem exists_achieving_oracle_all (q : Set ℕ → EReal) (Q : EReal) (C : Set ℕ)
    (hanti : ∀ A B, charOracle A ≤ᵀ charOracle B → q B ≤ q A)
    (hlower : ∀ A, charOracle C ≤ᵀ charOracle A → Q ≤ q A) : ∀ A, Q ≤ q A := fun A ↦
  (hlower _ (oracle_joins_right A C)).trans (hanti _ _ (oracle_joins A C))

/-- The signed minimum can be attained above any additional prescribed oracle.
Blueprint node `order:attainment`. -/
theorem exists_achieving_oracle_cone (q : Set ℕ → EReal) (Q : EReal) (C : Set ℕ)
    (hanti : ∀ A B, charOracle A ≤ᵀ charOracle B → q B ≤ q A)
    (hlower : ∀ A, charOracle C ≤ᵀ charOracle A → Q ≤ q A)
    (happrox : ∀ r : ℚ, Q < ((r : ℝ) : EReal) →
      ∃ A, charOracle C ≤ᵀ charOracle A ∧ q A < ((r : ℝ) : EReal)) (D : Set ℕ) :
    ∃ B, charOracle C ≤ᵀ charOracle B ∧ charOracle D ≤ᵀ charOracle B ∧ q B = Q := by
  obtain ⟨B, hCB, hqB⟩ := exists_achieving_oracle q Q C hanti hlower happrox
  have hCJ : charOracle C ≤ᵀ charOracle (oracleJoin B D) := hCB.trans (oracle_joins B D)
  exact ⟨oracleJoin B D, hCJ, oracle_joins_right B D,
    le_antisymm (hqB ▸ hanti B _ (oracle_joins B D)) (hlower _ hCJ)⟩

/-- Positive rational almost-achievers suffice for a nonnegative oracle-antitone quantity,
including the zero and infinity endpoints. Blueprint node `order:attainment`. -/
theorem exists_achieving_oracle_ennreal (q : Set ℕ → ℝ≥0∞) (Q : ℝ≥0∞) (C : Set ℕ)
    (hanti : ∀ A B, charOracle A ≤ᵀ charOracle B → q B ≤ q A)
    (hlower : ∀ A, charOracle C ≤ᵀ charOracle A → Q ≤ q A)
    (happrox : ∀ r : ℚ, 0 < r → Q < ENNReal.ofReal (r : ℝ) →
      ∃ A, charOracle C ≤ᵀ charOracle A ∧ q A < ENNReal.ofReal (r : ℝ)) :
    ∃ B, charOracle C ≤ᵀ charOracle B ∧ q B = Q := by
  have hcoe : ∀ r : ℚ, 0 < r → ((ENNReal.ofReal (r : ℝ) : ℝ≥0∞) : EReal) = ((r : ℝ) : EReal) :=
    fun r hr ↦ by
      rw [EReal.coe_ennreal_ofReal]
      exact max_eq_left (EReal.coe_nonneg.mpr (Rat.cast_pos.2 hr).le)
  obtain ⟨B, hCB, hB⟩ := exists_achieving_oracle (fun A ↦ (q A : EReal)) (Q : EReal) C
    (fun A B hAB ↦ EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hanti A B hAB))
    (fun A hCA ↦ EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hlower A hCA)) fun r hr ↦ by
      by_cases hr0 : 0 < r
      · rw [← hcoe r hr0] at hr ⊢
        obtain ⟨A, hCA, hA⟩ := happrox r hr0 (EReal.coe_ennreal_lt_coe_ennreal_iff.mp hr)
        exact ⟨A, hCA, EReal.coe_ennreal_lt_coe_ennreal_iff.mpr hA⟩
      · refine absurd (hr.trans_le (EReal.coe_le_coe_iff.mpr ?_)) (not_lt.mpr
          (EReal.coe_ennreal_nonneg Q))
        exact_mod_cast not_lt.mp hr0
  exact ⟨B, hCB, EReal.coe_ennreal_eq_coe_ennreal_iff.mp hB⟩

/-- An attained nonnegative cone lower bound persists above the achieving oracle.
Blueprint node `order:attainment`. -/
theorem exists_achieving_oracle_ennreal_stable (q : Set ℕ → ℝ≥0∞) (Q : ℝ≥0∞)
    (C B : Set ℕ) (hanti : ∀ A D, charOracle A ≤ᵀ charOracle D → q D ≤ q A)
    (hlower : ∀ A, charOracle C ≤ᵀ charOracle A → Q ≤ q A)
    (hCB : charOracle C ≤ᵀ charOracle B) (hB : q B = Q) :
    ∀ A, charOracle B ≤ᵀ charOracle A → q A = Q := fun A hBA ↦
  le_antisymm (hB ▸ hanti B A hBA) (hlower A (hCB.trans hBA))

/-- The nonnegative cone lower bound extends to all oracles.
Blueprint node `order:attainment`. -/
theorem exists_achieving_oracle_ennreal_all (q : Set ℕ → ℝ≥0∞) (Q : ℝ≥0∞) (C : Set ℕ)
    (hanti : ∀ A B, charOracle A ≤ᵀ charOracle B → q B ≤ q A)
    (hlower : ∀ A, charOracle C ≤ᵀ charOracle A → Q ≤ q A) : ∀ A, Q ≤ q A := fun A ↦
  (hlower _ (oracle_joins_right A C)).trans (hanti _ _ (oracle_joins A C))

/-- The nonnegative minimum can be attained in every prescribed upper cone.
Blueprint node `order:attainment`. -/
theorem exists_achieving_oracle_ennreal_cone (q : Set ℕ → ℝ≥0∞) (Q : ℝ≥0∞) (C : Set ℕ)
    (hanti : ∀ A B, charOracle A ≤ᵀ charOracle B → q B ≤ q A)
    (hlower : ∀ A, charOracle C ≤ᵀ charOracle A → Q ≤ q A)
    (happrox : ∀ r : ℚ, 0 < r → Q < ENNReal.ofReal (r : ℝ) →
      ∃ A, charOracle C ≤ᵀ charOracle A ∧ q A < ENNReal.ofReal (r : ℝ)) (D : Set ℕ) :
    ∃ B, charOracle C ≤ᵀ charOracle B ∧ charOracle D ≤ᵀ charOracle B ∧ q B = Q := by
  obtain ⟨B, hCB, hqB⟩ := exists_achieving_oracle_ennreal q Q (oracleJoin C D) hanti
    (fun A hA ↦ hlower A ((oracle_joins C D).trans hA)) fun r hr1 hr2 ↦ by
      obtain ⟨A, hCA, hqA⟩ := happrox r hr1 hr2
      refine ⟨oracleJoin A D, oracle_joins_least _ _ _ (hCA.trans (oracle_joins A D))
        (oracle_joins_right A D), ?_⟩
      exact (hanti A _ (oracle_joins A D)).trans_lt hqA
  exact ⟨B, (oracle_joins C D).trans hCB, (oracle_joins_right C D).trans hCB, hqB⟩

end Kolmogorov.PointToSet
