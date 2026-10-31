/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Order and limit lemmas for extended reals

General facts about `EReal`, `ℝ≥0∞` and real logarithms that the point-to-set modules use in
many places and that do not depend on anything specific to the formalization:

* the coercion `ℝ≥0∞ → EReal` commutes with infima, nonempty suprema and lower limits
  (`EReal.coe_ennreal_iInf`, `EReal.coe_ennreal_iSup`, `EReal.coe_ennreal_biSup`,
  `EReal.coe_ennreal_liminf`, `EReal.coe_ennreal_limsup`);

* adding a real constant commutes with suprema and infima of extended reals up to an inequality
  (`EReal.iSup_add_coe_le`, `EReal.iInf_add_coe_le`);
* a nonpositive power is antitone on `ℝ≥0∞` (`ENNReal.antitone_rpow_of_nonpos`);
* the logarithms of consecutive powers of a base in `(0, 1)` have ratio tending to `1`
  (`Real.tendsto_log_pow_succ_div_log_pow`).

They are candidates for Mathlib.
-/

open Filter
open scoped Topology ENNReal

namespace EReal

/-- The coercion `ℝ≥0∞ → EReal` commutes with infima. -/
theorem coe_ennreal_iInf {ι : Sort*} (f : ι → ℝ≥0∞) :
    ((⨅ i, f i : ℝ≥0∞) : EReal) = ⨅ i, (f i : EReal) :=
  Monotone.map_iInf_of_continuousAt (f := ((↑) : ℝ≥0∞ → EReal))
    continuous_coe_ennreal_ereal.continuousAt
    (fun _ _ h ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 h) EReal.coe_ennreal_top

/-- The coercion `ℝ≥0∞ → EReal` commutes with suprema over a nonempty index type. -/
theorem coe_ennreal_iSup {ι : Sort*} [Nonempty ι] (f : ι → ℝ≥0∞) :
    ((⨆ i, f i : ℝ≥0∞) : EReal) = ⨆ i, (f i : EReal) :=
  Monotone.map_ciSup_of_continuousAt (f := ((↑) : ℝ≥0∞ → EReal))
    continuous_coe_ennreal_ereal.continuousAt
    (fun _ _ h ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 h)

/-- The coercion `ℝ≥0∞ → EReal` commutes with suprema over a nonempty set. -/
theorem coe_ennreal_biSup {Y : Type*} {Z : Set Y} (hZ : Z.Nonempty) (f : Y → ℝ≥0∞) :
    ((⨆ x ∈ Z, f x : ℝ≥0∞) : EReal) = ⨆ x ∈ Z, (f x : EReal) := by
  have : Nonempty Z := hZ.to_subtype
  rw [iSup_subtype', iSup_subtype', coe_ennreal_iSup]

/-- The coercion `ℝ≥0∞ → EReal` commutes with lower limits of sequences. -/
theorem coe_ennreal_liminf (f : ℕ → ℝ≥0∞) :
    ((liminf f atTop : ℝ≥0∞) : EReal) = liminf (fun n ↦ (f n : EReal)) atTop :=
  Monotone.map_liminf_of_continuousAt (f := ((↑) : ℝ≥0∞ → EReal))
    (fun _ _ h ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 h) f
    continuous_coe_ennreal_ereal.continuousAt

/-- The coercion `ℝ≥0∞ → EReal` commutes with upper limits of sequences. -/
theorem coe_ennreal_limsup (f : ℕ → ℝ≥0∞) :
    ((limsup f atTop : ℝ≥0∞) : EReal) = limsup (fun n ↦ (f n : EReal)) atTop :=
  Monotone.map_limsup_of_continuousAt (f := ((↑) : ℝ≥0∞ → EReal))
    (fun _ _ h ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 h) f
    continuous_coe_ennreal_ereal.continuousAt

/-- A supremum of translated extended reals is bounded by the translated supremum. -/
theorem iSup_add_coe_le {ι : Sort*} (f : ι → EReal) (c : ℝ) :
    (⨆ i, f i + (c : EReal)) ≤ (⨆ i, f i) + (c : EReal) :=
  iSup_le fun i ↦ add_le_add (le_iSup f i) le_rfl

/-- An infimum of translated extended reals is bounded by the translated infimum. -/
theorem iInf_add_coe_le {ι : Sort*} (f : ι → EReal) (c : ℝ) :
    (⨅ i, f i + (c : EReal)) ≤ (⨅ i, f i) + (c : EReal) :=
  (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c))).mp
    (le_iInf fun i ↦ EReal.sub_le_of_le_add (iInf_le _ i))

end EReal

/-- Raising extended nonnegative reals to a nonpositive power reverses their order. -/
theorem ENNReal.antitone_rpow_of_nonpos (s : ℝ) (hs : s ≤ 0) :
    Antitone fun x : ENNReal ↦ x ^ s := by
  intro x y hxy
  simpa only [ENNReal.rpow_neg, inv_inv] using
    ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hxy (neg_nonneg.mpr hs))

/-- For a base `β ∈ (0, 1)`, the logarithms of consecutive powers of `β` have ratio tending
to `1`. -/
theorem Real.tendsto_log_pow_succ_div_log_pow {β : ℝ} (hβ : 0 < β) (hβ₁ : β < 1) :
    Tendsto (fun m : ℕ ↦ Real.log (β ^ (m + 1)) / Real.log (β ^ m)) atTop (𝓝 1) := by
  have hlog : Real.log β ≠ 0 := (Real.log_neg hβ hβ₁).ne
  have h : Tendsto (fun m : ℕ ↦ 1 + 1 / (m : ℝ)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [Real.log_pow, Real.log_pow, Nat.cast_succ, mul_div_mul_right _ _ hlog]
  field_simp
