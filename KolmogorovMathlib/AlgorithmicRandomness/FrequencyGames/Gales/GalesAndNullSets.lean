/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.LowerSemicomputable
import KolmogorovMathlib.MonotoneComplexity.Dimension.Hausdorff
import KolmogorovMathlib.MonotoneComplexity.Dimension.AlphaNullCriterion
import KolmogorovMathlib.Complexity.Applications.ComplexSubstrings
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison

/-!
# Gales And Null Sets

This module introduces `α`-gales and `α`-supergales on binary strings (Shen, Uspensky and
Vereshchagin, p. 285) and relates them to `α`-null sets of the Cantor space.

## Main declarations

* `IsGale`, `IsSupergale`: the notions of `α`-gale and `α`-supergale.
* `isGale_taxed_iff`: a uniform capital taxed at rate `2^{(1-α)|x|}` is exactly an `α`-gale.
* `isGale_iff_exists_measure`: `α`-gales are the rescaled cylinder masses of finite measures.
* `isAlphaNull_iff_exists_martingale` (Theorem 184): a set is `α`-null iff some taxed uniform
  martingale wins on it.
* `isAlphaNull_wins_of_isGale`: the set on which an `α`-gale is unbounded is `α`-null.
* `exists_isGale_wins_of_isAlphaNull`: every `α`-null set is won by an `α`-gale.
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology

/-- **SUV p. 285.**  An *`α`-gale*: non-negative with `2^α m(x) = m(x0) + m(x1)`. -/
structure IsGale (α : ℝ) (m : BitString → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ m x
  gale : ∀ x, (2 : ℝ) ^ α * m x = m (x ++ [false]) + m (x ++ [true])

/-- **SUV p. 285.**  An *`α`-supergale*: non-negative with `2^α m(x) ≥ m(x0) + m(x1)`. -/
structure IsSupergale (α : ℝ) (m : BitString → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ m x
  supergale : ∀ x, m (x ++ [false]) + m (x ++ [true]) ≤ (2 : ℝ) ^ α * m x

/-- A gale is a supergale. -/
lemma IsGale.isSupergale {α : ℝ} {m : BitString → ℝ} (h : IsGale α m) : IsSupergale α m :=
  ⟨h.nonneg, fun x => (h.gale x).symm.le⟩

/-- **SUV p. 285.**  The tax reading: `m` is a uniform capital exactly when
`x ↦ m(x) / 2^{(1-α)|x|}` is an `α`-gale. -/
theorem isGale_taxed_iff (α : ℝ) (m : BitString → ℝ) :
    IsGale α (fun x => m x / (2 : ℝ) ^ ((1 - α) * x.length)) ↔ IsFairCapital uniformMeasure m := by
  constructor
  · rintro ⟨hnonneg, hgale⟩
    rw [isFairCapital_uniform_iff]
    constructor
    · intro x
      have hx := hnonneg x
      have hpos : (0 : ℝ) < (2 : ℝ) ^ ((1 - α) * (x.length : ℝ)) := by positivity
      exact div_nonneg_iff.mp hx |>.resolve_right (fun hneg => not_lt.mpr hneg.2 hpos) |>.left
    · intro x
      have hx := hgale x
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.cast_add,
        Nat.cast_one] at hx
      have hpos : (0:ℝ) < (2:ℝ)^((1 - α) * (x.length : ℝ)) := by positivity
      have H1 : (2:ℝ)^α * (m x / (2:ℝ)^((1 - α) * (x.length : ℝ))) =
          (m (x ++ [false]) + m (x ++ [true])) / (2:ℝ)^((1 - α) * ((x.length : ℝ) + 1)) := by
        calc (2:ℝ)^α * (m x / (2:ℝ)^((1 - α) * (x.length : ℝ)))
          _ = m (x ++ [false]) / (2:ℝ)^((1 - α) * ((x.length : ℝ) + 1)) +
              m (x ++ [true]) / (2:ℝ)^((1 - α) * ((x.length : ℝ) + 1)) := hx
          _ = (m (x ++ [false]) + m (x ++ [true])) / (2:ℝ)^((1 - α) * ((x.length : ℝ) + 1)) := by
            ring
      have H2 : (2:ℝ)^α * m x / (2:ℝ)^((1 - α) * (x.length : ℝ)) =
          (m (x ++ [false]) + m (x ++ [true])) /
            ((2:ℝ)^((1 - α) * (x.length : ℝ)) * (2:ℝ)^(1 - α)) := by
        calc (2:ℝ)^α * m x / (2:ℝ)^((1 - α) * (x.length : ℝ))
          _ = (2:ℝ)^α * (m x / (2:ℝ)^((1 - α) * (x.length : ℝ))) := by ring
          _ = (m (x ++ [false]) + m (x ++ [true])) / (2:ℝ)^((1 - α) * ((x.length : ℝ) + 1)) := H1
          _ = (m (x ++ [false]) + m (x ++ [true])) /
              (2:ℝ)^((1 - α) * (x.length : ℝ) + (1 - α)) := by
            congr 2
            ring
          _ = (m (x ++ [false]) + m (x ++ [true])) /
              ((2:ℝ)^((1 - α) * (x.length : ℝ)) * (2:ℝ)^(1 - α)) := by rw [Real.rpow_add (by
                  norm_num)]
      have H3 : (2:ℝ)^α * m x = (m (x ++ [false]) + m (x ++ [true])) / (2:ℝ)^(1 - α) := by
        have H2' := congr_arg (fun y => y * (2:ℝ)^((1 - α) * (x.length : ℝ))) H2
        calc (2:ℝ)^α * m x
          _ = (2:ℝ)^α * m x / (2:ℝ)^((1 - α) * (x.length : ℝ)) *
              (2:ℝ)^((1 - α) * (x.length : ℝ)) := by rw [div_mul_cancel₀ _ hpos.ne']
          _ = (m (x ++ [false]) + m (x ++ [true])) /
              ((2:ℝ)^((1 - α) * (x.length : ℝ)) * (2:ℝ)^(1 - α)) *
              (2:ℝ)^((1 - α) * (x.length : ℝ)) := H2'
          _ = (m (x ++ [false]) + m (x ++ [true])) / (2:ℝ)^(1 - α) /
              (2:ℝ)^((1 - α) * (x.length : ℝ)) * (2:ℝ)^((1 - α) * (x.length : ℝ)) := by ring
          _ = (m (x ++ [false]) + m (x ++ [true])) / (2:ℝ)^(1 - α) := by
            rw [div_mul_cancel₀ _ hpos.ne']
      have H4 : m x = (m (x ++ [false]) + m (x ++ [true])) / 2 := by
        have H3' := congr_arg (fun y => y / (2:ℝ)^α) H3
        calc m x
          _ = (2:ℝ)^α * m x / (2:ℝ)^α := by rw [mul_div_cancel_left₀ _ (by positivity)]
          _ = (m (x ++ [false]) + m (x ++ [true])) / (2:ℝ)^(1 - α) / (2:ℝ)^α := H3'
          _ = (m (x ++ [false]) + m (x ++ [true])) / ((2:ℝ)^(1 - α) * (2:ℝ)^α) := by ring
          _ = (m (x ++ [false]) + m (x ++ [true])) / (2:ℝ)^((1 - α) + α) := by
            rw [Real.rpow_add (by norm_num)]
          _ = (m (x ++ [false]) + m (x ++ [true])) / (2:ℝ)^(1:ℝ) := by
            congr 2
            ring
          _ = (m (x ++ [false]) + m (x ++ [true])) / 2 := by
            have : (2:ℝ)^(1:ℝ) = 2 := Real.rpow_one 2
            rw [this]
      exact H4
  · rintro hfair
    rw [isFairCapital_uniform_iff] at hfair
    rcases hfair with ⟨hnonneg, hfair⟩
    constructor
    · intro x
      have hx := hnonneg x
      have hpos : (0 : ℝ) < 2 ^ ((1 - α) * (x.length : ℝ)) := by positivity
      exact div_nonneg hx hpos.le
    · intro x
      have hx := hfair x
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.cast_add,
        Nat.cast_one]
      have H1 : (2:ℝ)^α * (((m (x ++ [false]) + m (x ++ [true])) / 2) /
            (2:ℝ)^((1 - α) * (x.length : ℝ))) = (2:ℝ)^α * ((m (x ++ [false]) + m (x ++ [true])) /
            (2 * (2:ℝ)^((1 - α) * (x.length : ℝ)))) := by ring
      have H2 : (2:ℝ)^α * ((m (x ++ [false]) + m (x ++ [true])) /
            (2 * (2:ℝ)^((1 - α) * (x.length : ℝ)))) = (2:ℝ)^α * (m (x ++ [false]) + m (x ++ [true]))
                /
            ((2:ℝ)^(1:ℝ) * (2:ℝ)^((1 - α) * (x.length : ℝ))) := by
        have h2 : (2:ℝ) = (2:ℝ)^(1:ℝ) := (Real.rpow_one 2).symm
        calc (2:ℝ)^α * ((m (x ++ [false]) + m (x ++ [true])) /
            (2 * (2:ℝ)^((1 - α) * (x.length : ℝ))))
          _ = (2:ℝ)^α * (m (x ++ [false]) + m (x ++ [true])) /
              (2 * (2:ℝ)^((1 - α) * (x.length : ℝ))) := by ring
          _ = (2:ℝ)^α * (m (x ++ [false]) + m (x ++ [true])) /
              ((2:ℝ)^(1:ℝ) * (2:ℝ)^((1 - α) * (x.length : ℝ))) := by
            congr 1
            congr 1
      calc (2:ℝ)^α * (m x / (2:ℝ)^((1 - α) * (x.length : ℝ)))
        _ = (2:ℝ)^α * (((m (x ++ [false]) + m (x ++ [true])) / 2) /
            (2:ℝ)^((1 - α) * (x.length : ℝ))) := by rw [hx]
        _ = (2:ℝ)^α * ((m (x ++ [false]) + m (x ++ [true])) /
            (2 * (2:ℝ)^((1 - α) * (x.length : ℝ)))) := H1
        _ = (2:ℝ)^α * (m (x ++ [false]) + m (x ++ [true])) /
            ((2:ℝ)^(1:ℝ) * (2:ℝ)^((1 - α) * (x.length : ℝ))) := H2
        _ = (2:ℝ)^α * (m (x ++ [false]) + m (x ++ [true])) /
            (2:ℝ)^(1 + (1 - α) * (x.length : ℝ)) := by rw [Real.rpow_add (by norm_num)]
        _ = (m (x ++ [false]) + m (x ++ [true])) *
            ((2:ℝ)^α / (2:ℝ)^(1 + (1 - α) * (x.length : ℝ))) := by ring
        _ = (m (x ++ [false]) + m (x ++ [true])) *
            (2:ℝ)^(α - (1 + (1 - α) * (x.length : ℝ))) := by rw [← Real.rpow_sub (by norm_num)]
        _ = (m (x ++ [false]) + m (x ++ [true])) *
            (2:ℝ)^(-((1 - α) * ((x.length : ℝ) + 1))) := by
          congr 2
          ring
        _ = (m (x ++ [false]) + m (x ++ [true])) *
            ((2:ℝ)^((1 - α) * ((x.length : ℝ) + 1)))⁻¹ := by rw [Real.rpow_neg (by norm_num)]
        _ = (m (x ++ [false]) + m (x ++ [true])) /
            (2:ℝ)^((1 - α) * ((x.length : ℝ) + 1)) := by
          have H : (m (x ++ [false]) + m (x ++ [true])) *
              ((2:ℝ)^((1 - α) * (↑(List.length x) + 1)))⁻¹ =
              (m (x ++ [false]) + m (x ++ [true])) *
              (1 / ((2:ℝ)^((1 - α) * (↑(List.length x) + 1)))) := by
            exact congr_arg (HMul.hMul (m (x ++ [false]) + m (x ++ [true])))
              (inv_eq_one_div ((2:ℝ) ^ ((1 - α) * (↑(List.length x) + 1))))
          rw [H]
          exact mul_one_div (m (x ++ [false]) + m (x ++ [true]))
            ((2:ℝ)^((1 - α) * ((x.length : ℝ) + 1)))
        _ = m (x ++ [false]) / (2:ℝ)^((1 - α) * ((x.length : ℝ) + 1)) +
            m (x ++ [true]) / (2:ℝ)^((1 - α) * ((x.length : ℝ) + 1)) := by ring
private theorem isGale_iff_exists_measure_scaled_mass
    (α : ℝ) (m : BitString → ℝ) (hm : IsGale α m) :
    (∀ x, 0 ≤ m x * (2 : ℝ) ^ (-α * x.length)) ∧
    (∀ x, m x * (2 : ℝ) ^ (-α * x.length) =
      m (x ++ [false]) * (2 : ℝ) ^ (-α * (x ++ [false]).length) +
      m (x ++ [true]) * (2 : ℝ) ^ (-α * (x ++ [true]).length)) := by
  constructor
  · exact fun x => mul_nonneg (hm.nonneg x) (by positivity)
  · intro x
    have hgale := hm.gale x
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.cast_add,
      Nat.cast_one]
    have H : m (x ++ [false]) * 2 ^ (-α * (↑(List.length x) + 1)) +
        m (x ++ [true]) * 2 ^ (-α * (↑(List.length x) + 1)) =
      (m (x ++ [false]) + m (x ++ [true])) * 2 ^ (-α * (↑(List.length x) + 1)) := by ring
    rw [H, ← hgale]
    have H2 : 2 ^ α * m x * 2 ^ (-α * (↑(List.length x) + 1)) =
      m x * (2 ^ α * 2 ^ (-α * (↑(List.length x) + 1))) := by ring
    rw [H2, ← Real.rpow_add (by positivity)]
    congr 2
    ring

private lemma isGale_iff_exists_measure_massR_add_finite (ν : Measure CantorSeq) [IsFiniteMeasure ν]
    (x : BitString) :
    massR ν x = massR ν (x ++ [false]) + massR ν (x ++ [true]) := by
  have hne : ∀ y, cantorMass ν y ≠ ⊤ := fun y => measure_ne_top ν _
  simp only [massR]
  rw [cantorMass_add ν x, ENNReal.toReal_add (hne _) (hne _)]

private theorem isGale_iff_exists_measure_represent_additive
    {a : BitString → ℝ} (ha : ∀ x, 0 ≤ a x)
    (hadd : ∀ x, a x = a (x ++ [false]) + a (x ++ [true])) :
    ∃ ν : Measure CantorSeq, IsFiniteMeasure ν ∧ ∀ x, massR ν x = a x := by
  by_cases h0 : a [] = 0
  · have h_all_zero : ∀ x, a x = 0 := by
      intro x
      induction x using List.reverseRecOn with
      | nil => exact h0
      | append_singleton y b ih =>
        have hadd_y := hadd y
        rw [ih] at hadd_y
        have h1 := ha (y ++ [false])
        have h2 := ha (y ++ [true])
        cases b <;> linarith
    let ν₀ : MeasureTheory.Measure CantorSeq := 0
    have hfin : MeasureTheory.IsFiniteMeasure ν₀ := by
      exact MeasureTheory.isFiniteMeasureZero (α := CantorSeq)
    have hmass : ∀ x : BitString, massR ν₀ x = a x := by
      intro x
      rw [h_all_zero x]
      simp [ν₀, massR, cantorMass]
    exact Exists.intro ν₀ (And.intro hfin hmass)
  · have h_pos : 0 < a [] := (ha []).lt_of_ne' h0
    let a' (x : BitString) : ENNReal := ENNReal.ofReal (a x / a [])
    have ha'_cont : IsContinuousTreeSemimeasure a' := by
      refine ⟨?_, fun x => ?_⟩
      · simp [a', div_self h0]
      · dsimp [a']
        rw [← ENNReal.ofReal_add (div_nonneg (ha _) h_pos.le) (div_nonneg (ha _) h_pos.le)]
        rw [← add_div]
        rw [← hadd x]
    have ha'_add : ∀ x, a' x = a' (x ++ [false]) + a' (x ++ [true]) := by
      intro x
      dsimp [a']
      rw [← ENNReal.ofReal_add (div_nonneg (ha _) h_pos.le) (div_nonneg (ha _) h_pos.le)]
      rw [← add_div]
      rw [← hadd x]
    obtain ⟨μ, hμ⟩ := exists_measure_cantorSeq_of_isContinuousTreeSemimeasure_of_exact ha'_cont
        ha'_add
    let ν := ENNReal.ofReal (a []) • μ
    have H1 : μ Set.univ = cantorMass μ [] := by
      dsimp [cantorMass, cantorCylinder]
      have : {w : CantorSeq | IsCantorPrefix [] w} = Set.univ := by ext w; simp [IsCantorPrefix]
      rw [this]
    have hν_fin : IsFiniteMeasure ν := by
      constructor
      change (ENNReal.ofReal (a []) • μ) Set.univ < ⊤
      rw [Measure.smul_apply, smul_eq_mul]
      rw [H1, hμ, ha'_cont.1, mul_one]
      exact ENNReal.ofReal_lt_top
    refine ⟨ν, hν_fin, fun x => ?_⟩
    dsimp [massR, cantorMass]
    change ((ENNReal.ofReal (a []) • μ) (cantorCylinder x)).toReal = a x
    rw [Measure.smul_apply, smul_eq_mul]
    have H2 : μ (cantorCylinder x) = a' x := hμ x
    rw [H2]
    dsimp [a']
    rw [← ENNReal.ofReal_mul h_pos.le]
    have : a [] * (a x / a []) = a x := mul_div_cancel₀ (a x) h0
    rw [this, ENNReal.toReal_ofReal (ha x)]

/-- **SUV p. 285.**  An `α`-gale is a function `p(x) 2^{α|x|}` with `p(x) = ν(Ω_x)` for a finite
measure `ν`, which need not be a probability measure. -/
theorem isGale_iff_exists_measure (α : ℝ) (m : BitString → ℝ) :
    IsGale α m ↔ ∃ ν : Measure CantorSeq, IsFiniteMeasure ν ∧
      ∀ x, m x = massR ν x * (2 : ℝ) ^ (α * x.length) := by
  constructor
  · intro h
    have h1 := isGale_iff_exists_measure_scaled_mass α m h
    obtain ⟨ν, hν_fin, hν_eq⟩ := isGale_iff_exists_measure_represent_additive h1.1 h1.2
    refine ⟨ν, hν_fin, fun x => ?_⟩
    have h2 := hν_eq x
    rw [h2]
    rw [mul_assoc, ← Real.rpow_add (by positivity)]
    have H : -α * ↑(List.length x) + α * ↑(List.length x) = 0 := by ring
    rw [H, Real.rpow_zero, mul_one]
  · rintro ⟨ν, hν_fin, hν_eq⟩
    have _ : IsFiniteMeasure ν := hν_fin
    constructor
    · intro x
      have h1 := hν_eq x
      rw [h1]
      have H1 : 0 ≤ massR ν x := by
        dsimp [massR]
        exact ENNReal.toReal_nonneg
      have H2 : (0 : ℝ) ≤ (2 : ℝ) ^ (α * x.length) := by positivity
      exact mul_nonneg H1 H2
    · intro x
      have h1 := hν_eq x
      have h2 := hν_eq (x ++ [false])
      have h3 := hν_eq (x ++ [true])
      rw [h1, h2, h3]
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.cast_add,
        Nat.cast_one]
      have Hadd := isGale_iff_exists_measure_massR_add_finite ν x
      have H2 : massR ν (x ++ [false]) * 2 ^ (α * (↑(List.length x) + 1)) +
          massR ν (x ++ [true]) * 2 ^ (α * (↑(List.length x) + 1)) =
        (massR ν (x ++ [false]) + massR ν (x ++ [true])) * 2 ^ (α * (↑(List.length x) + 1)) :=
          by ring
      rw [H2, ← Hadd]
      have H3 : 2 ^ α * (massR ν x * 2 ^ (α * ↑(List.length x))) =
        massR ν x * (2 ^ α * 2 ^ (α * ↑(List.length x))) := by ring
      rw [H3, ← Real.rpow_add (by positivity)]
      congr 2
      ring


/-- Step 1 of the proof of `isAlphaNull_iff_exists_martingale`: a subset of an α-null set
is α-null. -/
private theorem isAlphaNull_iff_exists_martingale_isAlphaNull_mono_set
    {α : ℝ} {A B : Set CantorSeq} (hB : IsAlphaNull α B) (hAB : A ⊆ B) :
    IsAlphaNull α A := by
  intro ε hε
  rcases hB ε hε with ⟨I, hIcov, hIval⟩
  exact ⟨I, Set.Subset.trans hAB hIcov, hIval⟩

/-- Step 2 of the proof of `isAlphaNull_iff_exists_martingale`: from an α-gale winning on
A, obtain a martingale winning on A after taxation. -/
private theorem isAlphaNull_iff_exists_martingale_gale_to_martingale
    {α : ℝ} (m : BitString → ℝ) (hm : IsGale α m) :
    ∃ m', IsMartingale uniformMeasure m' ∧ ∀ w,
      Wins m w → Wins (fun x => m' x / (2 : ℝ) ^ ((1 - α) * x.length)) w := by
  obtain ⟨n, hn⟩ : ∃ n : BitString → ℝ, n = fun x => m x * (2 : ℝ) ^ ((1 - α) * x.length) :=
    ⟨_, rfl⟩
  have hpos : ∀ x : BitString, (0 : ℝ) < (2 : ℝ) ^ ((1 - α) * x.length) := fun x => by positivity
  have hmn : (fun x => n x / (2 : ℝ) ^ ((1 - α) * x.length)) = m := by
    funext x
    rw [hn]
    exact mul_div_cancel_right₀ _ (hpos x).ne'
  have hfair : IsFairCapital uniformMeasure n := by
    apply (isGale_taxed_iff α n).mp
    rw [hmn]
    exact hm
  obtain ⟨h1, h2⟩ := (isFairCapital_uniform_iff n).mp hfair
  have hn0 : n [] = m [] := by
    rw [hn]; simp
  have hc : 0 < m [] + 1 := by linarith [hm.nonneg []]
  refine ⟨fun x => (n x + 1) / (m [] + 1), ?_, ?_⟩
  · refine ⟨(isFairCapital_uniform_iff _).mpr ⟨fun x => ?_, fun x => ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [h1 x]) hc.le
    · have := h2 x
      field_simp
      linarith
    · show (n [] + 1) / (m [] + 1) = 1
      rw [hn0]
      exact div_self hc.ne'
  · intro w hw hbdd
    apply hw
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨(m [] + 1) * B, ?_⟩
    rintro _ ⟨k, rfl⟩
    have hk := hB ⟨k, rfl⟩
    simp only at hk ⊢
    generalize cantorPrefix w k = x at hk ⊢
    have hp := hpos x
    have hnx : n x = m x * (2 : ℝ) ^ ((1 - α) * x.length) := by rw [hn]
    have heq : (m [] + 1) * ((n x + 1) / (m [] + 1) / (2 : ℝ) ^ ((1 - α) * x.length)) =
        m x + 1 / (2 : ℝ) ^ ((1 - α) * x.length) := by
      rw [hnx]
      field_simp
    have : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ ((1 - α) * x.length) := by positivity
    calc m x ≤ (m [] + 1) * ((n x + 1) / (m [] + 1) / (2 : ℝ) ^ ((1 - α) * x.length)) := by
          rw [heq]; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hc.le

/-- Step 3 of the proof of `isAlphaNull_iff_exists_martingale`: from a martingale winning
on A after taxation, obtain an α-gale winning on A. -/
private theorem isAlphaNull_iff_exists_martingale_martingale_to_gale
    {α : ℝ} (m : BitString → ℝ) (hm : IsMartingale uniformMeasure m) :
    IsGale α (fun x => m x / (2 : ℝ) ^ ((1 - α) * x.length)) :=
  (isGale_taxed_iff α m).mpr hm.toIsFairCapital

/-- Step 4 of the proof of `isAlphaNull_iff_exists_martingale`: the set where an `α`-gale
is unbounded is an `α`-null set. -/
private theorem isAlphaNull_iff_exists_martingale_isAlphaNull_wins_of_isGale
    {α : ℝ} {m : BitString → ℝ} (hm : IsGale α m) :
    IsAlphaNull α {w | Wins m w} := by
  classical
  obtain ⟨ν, hν, hrepr⟩ := (isGale_iff_exists_measure α m).mp hm
  let : IsFiniteMeasure ν := hν
  have hnil : cantorCylinder ([] : BitString) = Set.univ := by
    ext w
    simp [cantorCylinder, IsCantorPrefix]
  have hinit : ν Set.univ = ENNReal.ofReal (m []) := by
    have hx := hrepr []
    simp only [List.length_nil, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at hx
    rw [hx, massR, cantorMass, hnil, ENNReal.ofReal_toReal (measure_ne_top ν _)]
  intro ε hε
  let k : ℝ := (m [] + 1) / ε
  have hk : 0 < k := div_pos (by linarith [hm.nonneg []]) hε
  have hεk : ε * k = m [] + 1 := by
    dsimp [k]
    field_simp
  have hratio : m [] / k < ε := (div_lt_iff₀ hk).2 (by linarith)
  -- Use the first threshold crossings, whose cylinders are pairwise disjoint.
  let S : Set BitString := {x | k ≤ m x}
  let F : Set BitString := minimalPrefixElements S
  -- Each string is listed once; strings outside the cover give missing entries.
  let I : ℕ → Option BitString := fun n =>
    if natToBitString n ∈ F then some (natToBitString n) else none
  refine ⟨I, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, ⟨n, rfl⟩, hn⟩ := (not_bddAbove_iff.mp hw) k
    obtain ⟨x, hx, hpre⟩ := exists_minimalPrefixElement (S := S) hn.le
    refine Set.mem_iUnion.mpr ⟨bitStringToNat x, ?_⟩
    simp only [I, natToBitString_bitStringToNat, show x ∈ F from hx, ↓reduceIte,
      Option.elim_some]
    exact cantorCylinder_subset_of_prefix hpre (mem_cantorCylinder_cantorPrefix w n)
  · have hdisj : Pairwise (fun x y : F =>
        Disjoint (cantorCylinder (x : BitString)) (cantorCylinder (y : BitString))) := by
      intro x y hxy
      apply cantorCylinder_disjoint_of_incompatible
      · intro hpre
        exact hxy (Subtype.ext (minimalPrefixElements_antichain S _ x.property _ y.property hpre))
      · intro hpre
        exact hxy (Subtype.ext (minimalPrefixElements_antichain S _ y.property _ x.property
            hpre).symm)
    have hmass : (∑' x : F, ν (cantorCylinder (x : BitString))) ≤ ν Set.univ :=
      tsum_measure_le_measure_univ
        (fun x => (measurableSet_cantorCylinder (x : BitString)).nullMeasurableSet)
        (fun x y hxy => (hdisj hxy).aedisjoint)
    have hweight (x : BitString) : intervalAlphaMass α x =
        ENNReal.ofReal ((2 : ℝ) ^ (-α * (x.length : ℝ))) := by
      rw [intervalAlphaMass_eq_inv_two_pow,
        ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ENNReal.inv_rpow,
        ← ENNReal.rpow_neg]
      congr 1
      ring
    -- At a threshold crossing, its α-weight is at most its ν-mass divided by k.
    have hterm (x : F) : intervalAlphaMass α (x : BitString) ≤
        (ENNReal.ofReal k)⁻¹ * ν (cantorCylinder (x : BitString)) := by
      have hx : k ≤ m (x : BitString) := x.property.1
      have hmul : (2 : ℝ) ^ (-α * ((x : BitString).length : ℝ)) *
          (2 : ℝ) ^ (α * ((x : BitString).length : ℝ)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]
        rw [show -α * ((x : BitString).length : ℝ) +
          α * ((x : BitString).length : ℝ) = 0 by ring, Real.rpow_zero]
      have hreal : (2 : ℝ) ^ (-α * ((x : BitString).length : ℝ)) ≤
          massR ν (x : BitString) / k := by
        rw [le_div_iff₀ hk]
        calc (2 : ℝ) ^ (-α * ((x : BitString).length : ℝ)) * k
            ≤ (2 : ℝ) ^ (-α * ((x : BitString).length : ℝ)) * m (x : BitString) :=
              mul_le_mul_of_nonneg_left hx (by positivity)
          _ = massR ν (x : BitString) := by
            rw [hrepr]
            calc (2 : ℝ) ^ (-α * ((x : BitString).length : ℝ)) *
                (massR ν (x : BitString) * (2 : ℝ) ^ (α * ((x : BitString).length : ℝ)))
                = ((2 : ℝ) ^ (-α * ((x : BitString).length : ℝ)) *
                  (2 : ℝ) ^ (α * ((x : BitString).length : ℝ))) * massR ν (x : BitString) := by ring
              _ = massR ν (x : BitString) := by rw [hmul, one_mul]
      rw [hweight]
      have h := ENNReal.ofReal_le_ofReal hreal
      rw [ENNReal.ofReal_div_of_pos hk, massR, cantorMass,
        ENNReal.ofReal_toReal (measure_ne_top ν _), div_eq_mul_inv] at h
      simpa only [mul_comm] using h
    have hsum : (∑' n, coverAlphaMass α (I n)) =
        ∑' x : F, intervalAlphaMass α (x : BitString) := by
      have heq (n : ℕ) : coverAlphaMass α (I n) =
          if natToBitString n ∈ F then intervalAlphaMass α (natToBitString n) else 0 := by
        dsimp [I]
        split_ifs <;> rfl
      simp_rw [heq]
      rw [tsum_comp_natToBitString (fun x => if x ∈ F then intervalAlphaMass α x else 0)]
      rw [tsum_subtype]
      rfl
    -- Sum the disjoint cylinder masses and use the chosen threshold.
    calc (∑' n, coverAlphaMass α (I n))
        = ∑' x : F, intervalAlphaMass α (x : BitString) := hsum
      _ ≤ ∑' x : F, (ENNReal.ofReal k)⁻¹ * ν (cantorCylinder (x : BitString)) :=
        ENNReal.tsum_le_tsum hterm
      _ = (ENNReal.ofReal k)⁻¹ * ∑' x : F, ν (cantorCylinder (x : BitString)) :=
        ENNReal.tsum_mul_left
      _ ≤ (ENNReal.ofReal k)⁻¹ * ν Set.univ := mul_le_mul' le_rfl hmass
      _ = ENNReal.ofReal (m [] / k) := by
        rw [hinit, ENNReal.ofReal_div_of_pos hk, div_eq_mul_inv, mul_comm]
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 hratio


/-- The elementary gale of the string `x`. -/
private noncomputable def isAlphaNull_iff_exists_martingale_elementary_gale_gx (α : ℝ)
    (x y : BitString) : ℝ :=
  if y <+: x then (2 : ℝ) ^ (α * ((y.length : ℝ) - (x.length : ℝ)))
  else if x <+: y then (2 : ℝ) ^ ((α - 1) * ((y.length : ℝ) - (x.length : ℝ)))
  else 0

private lemma isAlphaNull_iff_exists_martingale_elementary_gale_aux_eq (α : ℝ) (x y : BitString) :
    (2 : ℝ) ^ α * isAlphaNull_iff_exists_martingale_elementary_gale_gx α x y =
      isAlphaNull_iff_exists_martingale_elementary_gale_gx α x (y ++ [false]) +
      isAlphaNull_iff_exists_martingale_elementary_gale_gx α x (y ++ [true]) := by
  unfold isAlphaNull_iff_exists_martingale_elementary_gale_gx
  have hl : ∀ b : Bool, ((y ++ [b]).length : ℝ) = (y.length : ℝ) + 1 := fun b => by simp
  have hp : ∀ b : Bool, y <+: y ++ [b] := fun b => List.prefix_append y [b]
  by_cases hy : y <+: x
  · by_cases hyx : y = x
    · subst hyx
      have n1 : ∀ b : Bool, ¬ (y ++ [b]) <+: y := fun b h => by
        have := h.length_le; simp at this
      rw [ite_eq_left List.prefix_rfl, ite_eq_right (n1 false), ite_eq_right (n1 true), ite_eq_left
          (hp false),
        ite_eq_left (hp true), hl false, hl true, sub_self, mul_zero, Real.rpow_zero, mul_one]
      have e : (y.length : ℝ) + 1 - y.length = 1 := by ring
      rw [e, mul_one, ← two_mul]
      conv_lhs => rw [show α = (α - 1) + 1 by ring]
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
      ring
    · obtain ⟨t, rfl⟩ := hy
      cases t with
      | nil => simp at hyx
      | cons c t' =>
        have key : ∀ b : Bool, (y ++ [b]) <+: (y ++ c :: t') ↔ b = c := by
          intro b
          rw [List.prefix_append_right_inj]
          cases b <;> cases c <;> simp
        have key2 : ∀ b : Bool, b ≠ c → ¬ (y ++ c :: t') <+: (y ++ [b]) := by
          intro b hb h
          rw [List.prefix_append_right_inj] at h
          apply hb
          have := h.length_le
          have h3 : t'.length = 0 := by simpa using this
          have h4 : t' = [] := List.length_eq_zero_iff.1 h3
          subst h4
          cases b <;> cases c <;> simp_all
        have gb : ∀ b : Bool,
            (if (y ++ [b]) <+: (y ++ c :: t') then
              (2 : ℝ) ^ (α * (((y ++ [b]).length : ℝ) - ((y ++ c :: t').length : ℝ)))
            else if (y ++ c :: t') <+: (y ++ [b]) then
              (2 : ℝ) ^ ((α - 1) * (((y ++ [b]).length : ℝ) - ((y ++ c :: t').length : ℝ)))
            else 0) =
            if b = c then (2 : ℝ) ^ (α * ((y.length : ℝ) + 1 - ((y ++ c :: t').length : ℝ))) else 0
                := by
          intro b
          by_cases hb : b = c
          · rw [ite_eq_left ((key b).2 hb), ite_eq_left hb, hl b]
          · rw [ite_eq_right (fun h => hb ((key b).1 h)), ite_eq_right (key2 b hb), ite_eq_right hb]
        have hpow : (2 : ℝ) ^ α * (2 : ℝ) ^ (α * ((y.length : ℝ) - ((y ++ c :: t').length : ℝ))) =
            (2 : ℝ) ^ (α * ((y.length : ℝ) + 1 - ((y ++ c :: t').length : ℝ))) := by
          rw [← Real.rpow_add (by norm_num)]; congr 1; ring
        rw [ite_eq_left (List.prefix_append y _), gb false, gb true, hpow]
        cases c <;> simp
  · have hn : ∀ b : Bool, ¬ (y ++ [b]) <+: x := fun b h => hy ((hp b).trans h)
    rw [ite_eq_right hy, ite_eq_right (hn false), ite_eq_right (hn true)]
    by_cases hxy : x <+: y
    · rw [ite_eq_left hxy, ite_eq_left (hxy.trans (hp false)), ite_eq_left (hxy.trans (hp true)),
        hl false,
        hl true, ← two_mul]
      have e : (2 : ℝ) ^ α * (2 : ℝ) ^ ((α - 1) * ((y.length : ℝ) - (x.length : ℝ))) =
          2 * (2 : ℝ) ^ ((α - 1) * ((y.length : ℝ) + 1 - (x.length : ℝ))) := by
        have h2 : (2 : ℝ) * (2 : ℝ) ^ ((α - 1) * ((y.length : ℝ) + 1 - (x.length : ℝ))) =
            (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((α - 1) * ((y.length : ℝ) + 1 - (x.length : ℝ))) := by
          rw [Real.rpow_one]
        rw [h2, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]; congr 1; ring
      exact e
    · have hn2 : ∀ b : Bool, ¬ x <+: (y ++ [b]) := by
        intro b h
        by_cases hlen : x.length ≤ y.length
        · exact hxy (List.prefix_of_prefix_length_le h (hp b) hlen)
        · have : x.length = (y ++ [b]).length := by
            have := h.length_le; simp at this ⊢; omega
          exact hy (by rw [h.eq_of_length this]; exact hp b)
      rw [ite_eq_right hxy, ite_eq_right (hn2 false), ite_eq_right (hn2 true)]
      simp

/-- Step 1 of the proof of
`isAlphaNull_iff_exists_martingale_exists_isGale_wins_of_isAlphaNull`: elementary gale. -/
private lemma isAlphaNull_iff_exists_martingale_elementary_gale (α : ℝ) (x : BitString) :
    ∃ m : BitString → ℝ, IsGale α m ∧ m [] = (2 : ℝ) ^ (- α * (x.length : ℝ)) ∧ m x = 1 := by
  refine ⟨isAlphaNull_iff_exists_martingale_elementary_gale_gx α x, ⟨fun y => ?_, ?_⟩, ?_, ?_⟩
  · unfold isAlphaNull_iff_exists_martingale_elementary_gale_gx
    split_ifs <;> positivity
  · exact isAlphaNull_iff_exists_martingale_elementary_gale_aux_eq α x
  · unfold isAlphaNull_iff_exists_martingale_elementary_gale_gx
    rw [ite_eq_left (List.nil_prefix)]
    simp only [List.length_nil, Nat.cast_zero, zero_sub]
    congr 1; ring
  · unfold isAlphaNull_iff_exists_martingale_elementary_gale_gx
    rw [ite_eq_left List.prefix_rfl]
    simp

private noncomputable def
    isAlphaNull_iff_exists_martingale_sum_gales_gk (α
    : ℝ) (I : ℕ → Option BitString) (k : ℕ) : BitString → ℝ :=
  match I k with
  | none => fun _ => 0
  | some x => Classical.choose (isAlphaNull_iff_exists_martingale_elementary_gale α x)

private lemma isAlphaNull_iff_exists_martingale_gk_prop_ENNReal_toReal_pow_inv_two (α : ℝ) (n : ℕ) :
    ENNReal.toReal (( (2 : ENNReal)⁻¹ ^ n ) ^ α) = (2 : ℝ) ^ (- α * (n : ℝ)) := by
  rw [← ENNReal.toReal_rpow]
  have h1 : ENNReal.toReal ((2 : ENNReal)⁻¹ ^ n) = (2 : ℝ)⁻¹ ^ n := by
    rw [ENNReal.toReal_pow]
    simp
  rw [h1]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  rw [inv_eq_one_div, one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  congr 1
  ring

/-- Step 1 of the proof of
`isAlphaNull_iff_exists_martingale_sum_gales`:
properties of the chosen gales. -/
private lemma isAlphaNull_iff_exists_martingale_gk_prop (α : ℝ) (I : ℕ → Option BitString) (k : ℕ) :
    IsGale α (isAlphaNull_iff_exists_martingale_sum_gales_gk α I k) ∧
    (isAlphaNull_iff_exists_martingale_sum_gales_gk α
        I k) [] = (coverAlphaMass α (I k)).toReal ∧
    ∀ x, I k = some x → (isAlphaNull_iff_exists_martingale_sum_gales_gk α I k) x = 1 := by
  cases hk : I k with
  | none =>
    unfold isAlphaNull_iff_exists_martingale_sum_gales_gk
    rw [hk]
    refine ⟨⟨fun _ => le_refl _, by simp⟩, by simp, fun _ hx => by contradiction⟩
  | some x_k =>
    unfold isAlphaNull_iff_exists_martingale_sum_gales_gk
    rw [hk]
    dsimp
    have h_choose := Classical.choose_spec (isAlphaNull_iff_exists_martingale_elementary_gale α x_k)
    refine ⟨h_choose.1, ?_, fun x hx => by injection hx with hx_eq; subst hx_eq; exact h_choose.2.2⟩
    rw [h_choose.2.1]
    change _ = (coverAlphaMass α (some x_k)).toReal
    rw [coverAlphaMass_some, intervalAlphaMass_eq_inv_two_pow]
    exact (isAlphaNull_iff_exists_martingale_gk_prop_ENNReal_toReal_pow_inv_two α x_k.length).symm

/-- Step 2 of the proof of
`isAlphaNull_iff_exists_martingale_sum_gales`: bound
on gale growth. -/
private lemma isAlphaNull_iff_exists_martingale_growth (α : ℝ) (m : BitString → ℝ) (hm : IsGale α m)
    (y : BitString) :
    m y ≤ (2 : ℝ) ^ (α * y.length) * m [] := by
  refine List.reverseRecOn y ?_ ?_
  · simp
  · intro x b ih
    have hg := hm.gale x
    have h1 : m (x ++ [b]) ≤ (2 : ℝ) ^ α * m x := by
      cases b
      · have hn := hm.nonneg (x ++ [true])
        linarith
      · have hn := hm.nonneg (x ++ [false])
        linarith
    calc m (x ++ [b]) ≤ (2 : ℝ) ^ α * m x := h1
      _ ≤ (2 : ℝ) ^ α * ((2 : ℝ) ^ (α * x.length) * m []) := by gcongr
      _ = (2 : ℝ) ^ (α * (x ++ [b]).length) * m [] := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one, mul_add,
            mul_one, Real.rpow_add zero_lt_two]
        ring

/-- Step 4 of the proof of
`isAlphaNull_iff_exists_martingale_sum_gales`: sum is
an α-gale. -/
private lemma isAlphaNull_iff_exists_martingale_isGale (α : ℝ) (gk : ℕ → BitString → ℝ)
    (hgk_gale : ∀ k, IsGale α (gk k))
    (h_summable : ∀ y, Summable (fun k => gk k y)) :
    IsGale α (fun y => ∑' k, gk k y) := by
  constructor
  · intro x
    exact tsum_nonneg (fun k => (hgk_gale k).nonneg x)
  · intro x
    have h1 : (2 : ℝ) ^ α * ∑' k, gk k x = ∑' k, (2 : ℝ) ^ α * gk k x := by
      rw [tsum_mul_left]
    rw [h1]
    have h2 : ∀ k, (2 : ℝ) ^ α * gk k x = gk k (x ++ [false]) + gk k (x ++ [true]) := fun k =>
        (hgk_gale k).gale x
    simp_rw [h2]
    exact Summable.tsum_add (h_summable (x ++ [false])) (h_summable (x ++ [true]))

/-- Step 5 of the proof of
`isAlphaNull_iff_exists_martingale_sum_gales`: sum
initial value. -/
private lemma isAlphaNull_iff_exists_martingale_init (α : ℝ) (I : ℕ → Option BitString)
    (gk : ℕ → BitString → ℝ)
    (hgk_init : ∀ k, gk k [] = (coverAlphaMass α (I k)).toReal)
    (h_sum : (∑' k, coverAlphaMass α (I k)) ≠ ⊤) :
    (∑' k, gk k []) = (∑' k, coverAlphaMass α (I k)).toReal := by
  simp_rw [hgk_init]
  rw [ENNReal.tsum_toReal_eq]
  intro a
  exact ENNReal.ne_top_of_tsum_ne_top h_sum a

/-- Step 6 of the proof of
`isAlphaNull_iff_exists_martingale_sum_gales`:
reachability on cover. -/
private lemma isAlphaNull_iff_exists_martingale_reach (I : ℕ → Option BitString)
    (gk : ℕ → BitString → ℝ)
    (hgk_reach : ∀ k x, I k = some x → gk k x = 1)
    (hgk_nonneg : ∀ k y, 0 ≤ gk k y)
    (h_summable : ∀ y, Summable (fun k => gk k y)) :
    ∀ w ∈ ⋃ k, (I k).elim ∅ cantorCylinder, ∃ n, 1 ≤ ∑' k, gk k (cantorPrefix w n) := by
  intro w hw
  simp only [Set.mem_iUnion, Option.elim] at hw
  rcases hw with ⟨k, hk⟩
  cases hI : I k with
  | none =>
    rw [hI] at hk
    contradiction
  | some x =>
    rw [hI] at hk
    use x.length
    have hprefix : cantorPrefix w x.length = x := cantorPrefix_eq_of_mem_cantorCylinder rfl hk
    rw [hprefix]
    have h1 : gk k x = 1 := hgk_reach k x hI
    have h2 : gk k x ≤ ∑' i, gk i x := by
      calc
        gk k x ≤ ∑ i ∈ {k}, gk i x := by simp
        _ ≤ ∑' i, gk i x := (h_summable x).sum_le_tsum _ (fun i _ => hgk_nonneg i x)
    linarith

/-- Step 2 of the proof of
`isAlphaNull_iff_exists_martingale_exists_isGale_wins_of_isAlphaNull`: sum of gales. -/
private lemma isAlphaNull_iff_exists_martingale_sum_gales (α : ℝ) (I : ℕ → Option BitString)
    (h_sum : (∑' k, coverAlphaMass α (I k)) ≠ ⊤) :
    ∃ m : BitString → ℝ, IsGale α m ∧ m [] = (∑' k, coverAlphaMass α (I k)).toReal ∧
      ∀ w ∈ ⋃ k, (I k).elim ∅ cantorCylinder, ∃ n, 1 ≤ m (cantorPrefix w n) := by
  let gk := isAlphaNull_iff_exists_martingale_sum_gales_gk α I
  have hgk_gale : ∀ k, IsGale α (gk k) := fun k => (isAlphaNull_iff_exists_martingale_gk_prop α I
                                                     k).1
  have hgk_init : ∀ k, gk k [] = (coverAlphaMass α (I k)).toReal :=
      fun k => (isAlphaNull_iff_exists_martingale_gk_prop α I k).2.1
  have hgk_reach : ∀ k x, I k = some x → gk k x = 1 :=
      fun k => (isAlphaNull_iff_exists_martingale_gk_prop α I k).2.2
  have hgk_growth : ∀ k y, gk k y ≤ (2 : ℝ) ^ (α * y.length) * gk k [] :=
      fun k y => isAlphaNull_iff_exists_martingale_growth α (gk k) (hgk_gale k) y
  have hgk_nonneg : ∀ k y, 0 ≤ gk k y := fun k y => (hgk_gale k).1 y
  -- Step 3: pointwise summability, as `gk k y ≤ 2 ^ (α |y|) * gk k []` and the initial values
  -- `gk k []` are the masses of the cover, whose sum is finite
  have h_summable : ∀ y, Summable (fun k => gk k y) := by
    intro y
    have h1 : Summable (fun k => (coverAlphaMass α (I k)).toReal) :=
      ENNReal.summable_toReal h_sum
    have h2 : Summable (fun k => (2 : ℝ) ^ (α * y.length) * (coverAlphaMass α (I k)).toReal) :=
      h1.mul_left _
    refine Summable.of_nonneg_of_le (fun k => hgk_nonneg k y) (fun k => ?_) h2
    have := hgk_growth k y
    rwa [hgk_init k] at this
  refine ⟨fun y => ∑' k, gk k y, ?_, ?_, ?_⟩
  · exact isAlphaNull_iff_exists_martingale_isGale α gk hgk_gale h_summable
  · exact isAlphaNull_iff_exists_martingale_init α I gk hgk_init h_sum
  · exact isAlphaNull_iff_exists_martingale_reach I gk hgk_reach hgk_nonneg h_summable





/-- Step 3 of the proof of
`isAlphaNull_iff_exists_martingale_exists_isGale_wins_of_isAlphaNull`: sequence of gales. -/
private lemma isAlphaNull_iff_exists_martingale_gale_sequence {α : ℝ}
    {A : Set CantorSeq} (hA : IsAlphaNull α A) :
    ∃ m : ℕ → BitString → ℝ, (∀ k, IsGale α (m k)) ∧ (∀ k, m k [] ≤ (1 / 4 : ℝ) ^ k) ∧
      ∀ k, ∀ w ∈ A, ∃ n, 1 ≤ m k (cantorPrefix w n) := by
  have hex : ∀ k : ℕ, ∃ m : BitString → ℝ,
      IsGale α m ∧ m [] ≤ (1 / 4 : ℝ) ^ k ∧
        ∀ w ∈ A, ∃ n, 1 ≤ m (cantorPrefix w n) := by
    intro k
    obtain ⟨I, hcover, hmass⟩ := hA ((1 / 4 : ℝ) ^ k) (by positivity)
    obtain ⟨m, hgale, hinit, hreach⟩ :=
      isAlphaNull_iff_exists_martingale_sum_gales
        α I (ne_top_of_lt hmass)
    refine ⟨m, hgale, ?_, fun w hw => hreach w (hcover hw)⟩
    rw [hinit]
    have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass.le
    simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k)]
      using hle
  choose m hgale hinit hreach using hex
  exact ⟨m, hgale, hinit, hreach⟩

/-- Step 1 of the proof of
`isAlphaNull_iff_exists_martingale_final_gale`: define
M. -/
private noncomputable def isAlphaNull_iff_exists_martingale_M
    (m : ℕ → BitString → ℝ) :
    BitString → ℝ :=
  fun y => ∑' k : ℕ, (2 : ℝ) ^ k * m k y

/-- Step 2 of the proof of
`isAlphaNull_iff_exists_martingale_final_gale`: M is a
gale. -/
private lemma isAlphaNull_iff_exists_martingale_gale {α : ℝ}
    (m : ℕ → BitString → ℝ) (hm_gale : ∀ k, IsGale α (m k))
    (hm_init : ∀ k, m k [] ≤ (1 / 4 : ℝ) ^ k) :
    IsGale α (isAlphaNull_iff_exists_martingale_M m) := by
  have hnonneg : ∀ k y, 0 ≤ (2 : ℝ) ^ k * m k y := fun k y =>
    mul_nonneg (pow_nonneg (by norm_num) k) ((hm_gale k).nonneg y)
  have hsum : ∀ y, Summable (fun k : ℕ => (2 : ℝ) ^ k * m k y) := by
    intro y
    refine Summable.of_nonneg_of_le (fun k => hnonneg k y) (fun k => ?_)
      (summable_geometric_two.mul_left ((2 : ℝ) ^ (α * y.length)))
    have hg := isAlphaNull_iff_exists_martingale_growth
      α (m k) (hm_gale k) y
    have h4 : (2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = ((1 : ℝ) / 2) ^ k := by
      rw [← mul_pow]
      norm_num
    calc (2 : ℝ) ^ k * m k y
        ≤ (2 : ℝ) ^ k * ((2 : ℝ) ^ (α * y.length) * (1 / 4 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left
            (hg.trans (mul_le_mul_of_nonneg_left (hm_init k) (by positivity))) (by positivity)
      _ = (2 : ℝ) ^ (α * y.length) * ((1 : ℝ) / 2) ^ k := by
          rw [← h4]
          ring
  constructor
  · intro x
    exact tsum_nonneg (fun k => hnonneg k x)
  · intro x
    unfold isAlphaNull_iff_exists_martingale_M
    rw [← tsum_mul_left]
    have h2 : ∀ k : ℕ, (2 : ℝ) ^ α * ((2 : ℝ) ^ k * m k x) =
        (2 : ℝ) ^ k * m k (x ++ [false]) + (2 : ℝ) ^ k * m k (x ++ [true]) := by
      intro k
      rw [← mul_add, ← (hm_gale k).gale x]
      ring
    simp_rw [h2]
    exact Summable.tsum_add (hsum (x ++ [false])) (hsum (x ++ [true]))

/-- Step 3 of the proof of
`isAlphaNull_iff_exists_martingale_final_gale`: M
wins. -/
private lemma isAlphaNull_iff_exists_martingale_wins {α : ℝ} {A : Set CantorSeq}
    (m : ℕ → BitString → ℝ) (hm_gale : ∀ k, IsGale α (m k))
    (hm_init : ∀ k, m k [] ≤ (1 / 4 : ℝ) ^ k)
    (hm_reach : ∀ k, ∀ w ∈ A, ∃ n, 1 ≤ m k (cantorPrefix w n)) :
    ∀ w ∈ A, Wins (isAlphaNull_iff_exists_martingale_M m) w := by
  have hnonneg : ∀ k y, 0 ≤ (2 : ℝ) ^ k * m k y := fun k y =>
    mul_nonneg (pow_nonneg (by norm_num) k) ((hm_gale k).nonneg y)
  -- `2^k m_k(y) ≤ 2^{α|y|} 2^{-k}`, so the series defining `M y` converges.
  have hsum : ∀ y, Summable (fun k : ℕ => (2 : ℝ) ^ k * m k y) := by
    intro y
    refine Summable.of_nonneg_of_le (fun k => hnonneg k y) (fun k => ?_)
      (summable_geometric_two.mul_left ((2 : ℝ) ^ (α * y.length)))
    have hg := isAlphaNull_iff_exists_martingale_growth
      α (m k) (hm_gale k) y
    have h4 : (2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = ((1 : ℝ) / 2) ^ k := by
      rw [← mul_pow]
      norm_num
    calc (2 : ℝ) ^ k * m k y
        ≤ (2 : ℝ) ^ k * ((2 : ℝ) ^ (α * y.length) * (1 / 4 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left
            (hg.trans (mul_le_mul_of_nonneg_left (hm_init k) (by positivity))) (by positivity)
      _ = (2 : ℝ) ^ (α * y.length) * ((1 : ℝ) / 2) ^ k := by
          rw [← h4]
          ring
  -- If the prefix values were bounded by `B`, take `2^k > B` and a prefix where `m_k ≥ 1`.
  intro w hw hbdd
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 2)
  obtain ⟨n, hn⟩ := hm_reach k w hw
  have h1 : (2 : ℝ) ^ k * m k (cantorPrefix w n) ≤
      isAlphaNull_iff_exists_martingale_M m
        (cantorPrefix w n) :=
    (hsum _).le_tsum k (fun j _ => hnonneg j _)
  have h2 : isAlphaNull_iff_exists_martingale_M m
      (cantorPrefix w n) ≤ B := hB ⟨n, rfl⟩
  have h3 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k * m k (cantorPrefix w n) :=
    le_mul_of_one_le_right (by positivity) hn
  linarith

/-- Step 4 of the proof of
`isAlphaNull_iff_exists_martingale_exists_isGale_wins_of_isAlphaNull`: final gale bounding. -/
private lemma isAlphaNull_iff_exists_martingale_final_gale {α : ℝ} {A : Set CantorSeq}
    (m : ℕ → BitString → ℝ) (hm_gale : ∀ k, IsGale α (m k))
    (hm_init : ∀ k, m k [] ≤ (1 / 4 : ℝ) ^ k)
    (hm_reach : ∀ k, ∀ w ∈ A, ∃ n, 1 ≤ m k (cantorPrefix w n)) :
    ∃ M : BitString → ℝ, IsGale α M ∧ ∀ w ∈ A, Wins M w := by
  use isAlphaNull_iff_exists_martingale_M m
  exact ⟨isAlphaNull_iff_exists_martingale_gale m hm_gale hm_init,
         isAlphaNull_iff_exists_martingale_wins m hm_gale hm_init hm_reach⟩

/-- Step 5 of the proof of `isAlphaNull_iff_exists_martingale`: every `α`-null set is
contained in the set where some `α`-gale is unbounded. -/
private theorem isAlphaNull_iff_exists_martingale_exists_isGale_wins_of_isAlphaNull
    {α : ℝ} {A : Set CantorSeq} (hA : IsAlphaNull α A) :
    ∃ m, IsGale α m ∧ ∀ w ∈ A, Wins m w := by
  obtain ⟨m, hgale, hinit, hreach⟩ :=
      isAlphaNull_iff_exists_martingale_gale_sequence hA
  exact isAlphaNull_iff_exists_martingale_final_gale m
      hgale hinit hreach






/-- **SUV Theorem 184, p. 285.**  For `α > 0`, a set `A` is `α`-null exactly when some uniform
martingale `m` has `m(x) / 2^{(1-α)|x|}` unbounded on the prefixes of every `ω ∈ A`. -/
theorem isAlphaNull_iff_exists_martingale {α : ℝ} (_hα : 0 < α) (A : Set CantorSeq) :
    IsAlphaNull α A ↔ ∃ m, IsMartingale uniformMeasure m ∧ ∀ w ∈ A,
      Wins (fun x => m x / (2 : ℝ) ^ ((1 - α) * x.length)) w := by
  constructor
  · intro hA
    obtain ⟨m, hm, hwin⟩ :=
        isAlphaNull_iff_exists_martingale_exists_isGale_wins_of_isAlphaNull hA
    obtain ⟨m', hm', hwin'⟩ := isAlphaNull_iff_exists_martingale_gale_to_martingale m hm
    exact ⟨m', hm', fun w hw => hwin' w (hwin w hw)⟩
  · rintro ⟨m, hm, hwin⟩
    have hgale := isAlphaNull_iff_exists_martingale_martingale_to_gale (α := α) m hm
    have hwinsgale := isAlphaNull_iff_exists_martingale_isAlphaNull_wins_of_isGale hgale
    exact isAlphaNull_iff_exists_martingale_isAlphaNull_mono_set hwinsgale hwin

/-- **SUV p. 285**, first half of Theorem 184 for gales: the set where an `α`-gale is unbounded is
an `α`-null set. -/
theorem isAlphaNull_wins_of_isGale {α : ℝ} (hα : 0 < α) {m : BitString → ℝ} (hm : IsGale α m) :
    IsAlphaNull α {w | Wins m w} := by
  let m' (x : BitString) := m x * (2 : ℝ) ^ ((1 - α) * x.length)
  have hm'_fair : IsFairCapital uniformMeasure m' := by
    apply (isGale_taxed_iff α m').mp
    convert hm using 1
    ext x
    dsimp [m']
    rw [mul_div_cancel_right₀]
    positivity
  rcases eq_or_lt_of_le (hm'_fair.nonneg []) with h_zero | h_pos
  · have hm'_zero : ∀ x, m' x = 0 := by
      have h1 := (isFairCapital_uniform_iff m').mp hm'_fair
      have h_nonneg := h1.1
      have h_avg := h1.2
      intro x
      induction x using List.reverseRecOn with
      | nil => exact h_zero.symm
      | append_singleton y b ih =>
        have h_y := h_avg y
        rw [ih] at h_y
        have h_sum : m' (y ++ [false]) + m' (y ++ [true]) = 0 := by linarith
        have h_false := h_nonneg (y ++ [false])
        have h_true := h_nonneg (y ++ [true])
        cases b
        · linarith
        · linarith
    have hm_zero : ∀ x, m x = 0 := by
      intro x
      have h_m' := hm'_zero x
      dsimp [m'] at h_m'
      have h2 : (2 : ℝ) ^ ((1 - α) * x.length) ≠ 0 := by positivity
      exact mul_eq_zero.mp h_m' |>.resolve_right h2
    have hwins : {w | Wins m w} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, Wins, not_bddAbove_iff, Set.mem_empty_iff_false, iff_false]
      push Not
      use 1
      intro _ hx
      obtain ⟨n, rfl⟩ := hx
      change m (cantorPrefix w n) ≤ 1
      rw [hm_zero]
      exact zero_le_one
    rw [hwins]
    intro ε hε
    refine ⟨fun _ => none, Set.empty_subset _, ?_⟩
    simp only [Option.elim, coverAlphaMass, tsum_zero, ENNReal.ofReal_pos]
    exact hε
  · let m'' (x : BitString) := m' x / m' []
    have hm''_fair : IsFairCapital uniformMeasure m'' := by
      refine ⟨fun x => div_nonneg (hm'_fair.nonneg x) h_pos.le, fun x => ?_⟩
      dsimp [m'']
      calc m' x / m' [] * massR uniformMeasure x
        _ = (m' x * massR uniformMeasure x) / m' [] := by ring
        _ = (m' (x ++ [false]) * massR uniformMeasure (x ++ [false]) + m' (x ++ [true]) * massR
            uniformMeasure (x ++ [true])) / m' [] := by rw [hm'_fair.fair x]
        _ = m' (x ++ [false]) / m' [] * massR uniformMeasure (x ++ [false]) + m' (x ++ [true]) / m'
            [] * massR uniformMeasure (x ++ [true]) := by ring
    have hm''_mart : IsMartingale uniformMeasure m'' := by
      refine ⟨hm''_fair, div_self h_pos.ne'⟩
    have hm''_null : IsAlphaNull α {w | Wins (fun x => m'' x / (2 : ℝ) ^ ((1 - α) * x.length)) w} :=
        by
      apply (isAlphaNull_iff_exists_martingale hα _).mpr
      exact ⟨m'', hm''_mart, fun w hw => hw⟩
    have h_eq : (fun x => m'' x / (2 : ℝ) ^ ((1 - α) * x.length)) = fun x => m x / m' [] := by
      ext x
      dsimp [m'', m']
      calc (m x * (2 : ℝ) ^ ((1 - α) * x.length) / m' []) / (2 : ℝ) ^ ((1 - α) * x.length)
        _ = (m x * (2 : ℝ) ^ ((1 - α) * x.length) / (2 : ℝ) ^ ((1 - α) * x.length)) / m' [] := by
            ring
        _ = m x / m' [] := by
          congr 1
          rw [mul_div_cancel_right₀]
          positivity
    have hwins_eq : {w | Wins (fun x => m'' x / (2 : ℝ) ^ ((1 - α) * x.length)) w} = {w | Wins (fun
        x => m x / m' []) w} := by
      rw [h_eq]
    rw [hwins_eq] at hm''_null
    have hwins_eq2 : {w | Wins (fun x => m x / m' []) w} = {w | Wins m w} := by
      ext w
      simp only [Set.mem_ofPred_eq, Wins, not_bddAbove_iff]
      constructor
      · intro hw M
        obtain ⟨x, ⟨n, rfl⟩, hx⟩ := hw (M / m' [])
        refine ⟨m (cantorPrefix w n), ⟨n, rfl⟩, ?_⟩
        exact (div_lt_iff₀ h_pos).mp hx |>.trans_eq (by
          have : m (cantorPrefix w n) * m' [] / m' [] = m (cantorPrefix w n) := by
            rw [mul_div_cancel_right₀ _ h_pos.ne']
          rw [← this]
          ring)
      · intro hw M
        obtain ⟨x, ⟨n, rfl⟩, hx⟩ := hw (M * m' [])
        refine ⟨m (cantorPrefix w n) / m' [], ⟨n, rfl⟩, ?_⟩
        exact (lt_div_iff₀ h_pos).mpr hx
    rw [hwins_eq2] at hm''_null
    exact hm''_null

/-- Step 1 of the proof of `exists_isGale_wins_of_isAlphaNull`: an elementary gale for an
interval. -/
private lemma exists_isGale_wins_of_isAlphaNull_elementary_gale (α : ℝ) (x : BitString) :
    ∃ m : BitString → ℝ, IsGale α m ∧ m [] = (2 : ℝ) ^ (- α * (x.length : ℝ)) ∧ m x = 1 := by
  classical
  set w0 : CantorSeq := prependCantor x (fun _ => false) with hw0
  have key : ∀ (y : BitString) (b : Bool),
      cantorPrefix w0 (y ++ [b]).length = y ++ [b] ↔
        (cantorPrefix w0 y.length = y ∧ w0 y.length = b) := by
    intro y b
    rw [List.length_append, List.length_singleton, cantorPrefix_succ]
    constructor
    · intro h
      have := List.append_inj' h (by simp)
      exact ⟨this.1, by simpa using this.2⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
  refine ⟨fun y => if cantorPrefix w0 y.length = y
      then (2 : ℝ) ^ (α * ((y.length : ℝ) - x.length)) else 0,
    ⟨fun y => ?_, fun y => ?_⟩, ?_, ?_⟩
  · split_ifs
    · positivity
    · exact le_rfl
  · simp only [key]
    by_cases hy : cantorPrefix w0 y.length = y
    · cases hb : w0 y.length
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hy),
          ite_eq_left_of_eq_true _ _ (eq_true (show cantorPrefix w0 y.length = y ∧ false = false
            from ⟨hy, rfl⟩)),
          ite_eq_right_of_eq_false _ _
            (eq_false (show ¬(cantorPrefix w0 y.length = y ∧ false = true) by simp)),
          add_zero, ← Real.rpow_add (by norm_num)]
        congr 1
        rw [List.length_append, List.length_singleton]
        push_cast
        ring
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hy),
          ite_eq_right_of_eq_false _ _
            (eq_false (show ¬(cantorPrefix w0 y.length = y ∧ true = false) by simp)),
          ite_eq_left_of_eq_true _ _ (eq_true (show cantorPrefix w0 y.length = y ∧ true = true
            from ⟨hy, rfl⟩)),
          zero_add, ← Real.rpow_add (by norm_num)]
        congr 1
        rw [List.length_append, List.length_singleton]
        push_cast
        ring
    · simp [hy]
  · simp only [List.length_nil, cantorPrefix, List.ofFn_zero, ite_true, Nat.cast_zero, zero_sub]
    congr 1
    ring
  · have := cantorPrefix_prepend x (fun _ => false)
    simp only [← hw0] at this
    simp [this]

private noncomputable def exists_isGale_wins_of_isAlphaNull_sum_gales_gk (α : ℝ) (I : ℕ →
    Option BitString) (k : ℕ) : BitString → ℝ :=
  match I k with
  | none => fun _ => 0
  | some x => Classical.choose (exists_isGale_wins_of_isAlphaNull_elementary_gale α x)

private lemma exists_isGale_wins_of_isAlphaNull_sum_gales_aux_toReal (α : ℝ) (n : ℕ) :
    ENNReal.toReal (((2 : ENNReal)⁻¹ ^ n) ^ α) = (2 : ℝ) ^ (- α * (n : ℝ)) := by
  rw [← ENNReal.toReal_rpow]
  have h1 : ENNReal.toReal ((2 : ENNReal)⁻¹ ^ n) = (2 : ℝ)⁻¹ ^ n := by
    rw [ENNReal.toReal_pow]
    simp
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [inv_eq_one_div, one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  congr 1
  ring

private lemma exists_isGale_wins_of_isAlphaNull_sum_gales_aux_gk_prop (α : ℝ) (I : ℕ → Option
    BitString) (k : ℕ) :
    IsGale α (exists_isGale_wins_of_isAlphaNull_sum_gales_gk α I k) ∧
    (exists_isGale_wins_of_isAlphaNull_sum_gales_gk α I k) [] = (coverAlphaMass α (I
        k)).toReal ∧
    ∀ x, I k = some x → (exists_isGale_wins_of_isAlphaNull_sum_gales_gk α I k) x = 1 := by
  cases hk : I k with
  | none =>
    unfold exists_isGale_wins_of_isAlphaNull_sum_gales_gk
    rw [hk]
    refine ⟨⟨fun _ => le_refl _, by simp⟩, by simp, fun _ hx => by contradiction⟩
  | some x_k =>
    unfold exists_isGale_wins_of_isAlphaNull_sum_gales_gk
    rw [hk]
    dsimp
    have h_choose := Classical.choose_spec (exists_isGale_wins_of_isAlphaNull_elementary_gale
        α x_k)
    refine ⟨h_choose.1, ?_, fun x hx => by injection hx with hx_eq; subst hx_eq; exact h_choose.2.2⟩
    rw [h_choose.2.1]
    change _ = (coverAlphaMass α (some x_k)).toReal
    rw [coverAlphaMass_some, intervalAlphaMass_eq_inv_two_pow]
    exact (exists_isGale_wins_of_isAlphaNull_sum_gales_aux_toReal α x_k.length).symm

private lemma exists_isGale_wins_of_isAlphaNull_sum_gales_aux_growth (α : ℝ) (m : BitString →
    ℝ) (hm : IsGale α m) (y : BitString) :
    m y ≤ (2 : ℝ) ^ (α * y.length) * m [] := by
  refine List.reverseRecOn y ?_ ?_
  · simp
  · intro x b ih
    have hg := hm.gale x
    have h1 : m (x ++ [b]) ≤ (2 : ℝ) ^ α * m x := by
      cases b
      · have hn := hm.nonneg (x ++ [true])
        linarith
      · have hn := hm.nonneg (x ++ [false])
        linarith
    calc m (x ++ [b]) ≤ (2 : ℝ) ^ α * m x := h1
      _ ≤ (2 : ℝ) ^ α * ((2 : ℝ) ^ (α * x.length) * m []) := by gcongr
      _ = (2 : ℝ) ^ (α * (x ++ [b]).length) * m [] := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one, mul_add,
            mul_one, Real.rpow_add zero_lt_two]
        ring

private lemma exists_isGale_wins_of_isAlphaNull_sum_gales_aux_summable (α : ℝ) (I : ℕ → Option
    BitString) (gk : ℕ → BitString → ℝ)
    (hgk_gale : ∀ k, IsGale α (gk k))
    (hgk_init : ∀ k, gk k [] = (coverAlphaMass α (I k)).toReal)
    (h_sum : (∑' k, coverAlphaMass α (I k)) ≠ ⊤) (y : BitString) :
    Summable (fun k => gk k y) := by
  have hs : Summable (fun k => (coverAlphaMass α (I k)).toReal) := ENNReal.summable_toReal h_sum
  refine Summable.of_nonneg_of_le (fun k => (hgk_gale k).nonneg y)
    (fun k => ?_) (hs.mul_left ((2 : ℝ) ^ (α * y.length)))
  rw [← hgk_init k]
  exact exists_isGale_wins_of_isAlphaNull_sum_gales_aux_growth α (gk k) (hgk_gale k) y

/-- Step 2 of the proof of `exists_isGale_wins_of_isAlphaNull`: sum of elementary gales.
-/
private lemma exists_isGale_wins_of_isAlphaNull_sum_gales (α : ℝ) (I : ℕ → Option BitString)
    (h_sum : (∑' k, coverAlphaMass α (I k)) ≠ ⊤) :
    ∃ m : BitString → ℝ, IsGale α m ∧ m [] = (∑' k, coverAlphaMass α (I k)).toReal ∧
      ∀ w ∈ ⋃ k, (I k).elim ∅ cantorCylinder, ∃ n, 1 ≤ m (cantorPrefix w n) := by
  let gk := exists_isGale_wins_of_isAlphaNull_sum_gales_gk α I
  have hgk_gale : ∀ k, IsGale α (gk k) := fun k =>
      (exists_isGale_wins_of_isAlphaNull_sum_gales_aux_gk_prop α I k).1
  have hgk_init : ∀ k, gk k [] = (coverAlphaMass α (I k)).toReal := fun k =>
      (exists_isGale_wins_of_isAlphaNull_sum_gales_aux_gk_prop α I k).2.1
  have hgk_reach : ∀ k x, I k = some x → gk k x = 1 := fun k =>
      (exists_isGale_wins_of_isAlphaNull_sum_gales_aux_gk_prop α I k).2.2
  have h_summable : ∀ y, Summable (fun k => gk k y) := fun y =>
    exists_isGale_wins_of_isAlphaNull_sum_gales_aux_summable α I gk hgk_gale hgk_init h_sum y
  refine ⟨fun y => ∑' k, gk k y, ⟨fun x => tsum_nonneg (fun k => (hgk_gale k).nonneg x), fun x =>
      ?_⟩, ?_, ?_⟩
  · have h1 : (2 : ℝ) ^ α * ∑' k, gk k x = ∑' k, (2 : ℝ) ^ α * gk k x := by
      rw [tsum_mul_left]
    rw [h1]
    simp_rw [fun k => (hgk_gale k).gale x]
    exact Summable.tsum_add (h_summable (x ++ [false])) (h_summable (x ++ [true]))
  · change (∑' k, gk k []) = _
    simp_rw [hgk_init]
    rw [ENNReal.tsum_toReal_eq]
    intro a
    exact ENNReal.ne_top_of_tsum_ne_top h_sum a
  · intro w hw
    simp only [Set.mem_iUnion, Option.elim] at hw
    rcases hw with ⟨k, hk⟩
    cases hI : I k with
    | none =>
      rw [hI] at hk
      contradiction
    | some x =>
      rw [hI] at hk
      refine ⟨x.length, ?_⟩
      have hprefix : cantorPrefix w x.length = x := cantorPrefix_eq_of_mem_cantorCylinder rfl hk
      rw [hprefix]
      have h1 : gk k x = 1 := hgk_reach k x hI
      have h2 : gk k x ≤ ∑' i, gk i x :=
        (h_summable x).le_tsum k (fun i _ => (hgk_gale i).nonneg x)
      linarith

/-- Step 3 of the proof of `exists_isGale_wins_of_isAlphaNull`: gale sequence for a null
set. -/
private lemma exists_isGale_wins_of_isAlphaNull_gale_sequence {α : ℝ}
    {A : Set CantorSeq} (hA : IsAlphaNull α A) :
    ∃ m : ℕ → BitString → ℝ, (∀ k, IsGale α (m k)) ∧ (∀ k, m k [] ≤ (1 / 4 : ℝ) ^ k) ∧
      ∀ k, ∀ w ∈ A, ∃ n, 1 ≤ m k (cantorPrefix w n) := by
  have hex : ∀ k : ℕ, ∃ m : BitString → ℝ,
      IsGale α m ∧ m [] ≤ (1 / 4 : ℝ) ^ k ∧
        ∀ w ∈ A, ∃ n, 1 ≤ m (cantorPrefix w n) := by
    intro k
    obtain ⟨I, hcover, hmass⟩ := hA ((1 / 4 : ℝ) ^ k) (by positivity)
    obtain ⟨m, hgale, hinit, hreach⟩ :=
      exists_isGale_wins_of_isAlphaNull_sum_gales α I (ne_top_of_lt hmass)
    refine ⟨m, hgale, ?_, fun w hw => hreach w (hcover hw)⟩
    rw [hinit]
    have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass.le
    simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k)]
      using hle
  choose m hgale hinit hreach using hex
  exact ⟨m, hgale, hinit, hreach⟩

/-- Step 4 of the proof of `exists_isGale_wins_of_isAlphaNull`: final gale bounding. -/
private lemma exists_isGale_wins_of_isAlphaNull_final_gale {α : ℝ} {A : Set CantorSeq}
    (m : ℕ → BitString → ℝ) (hm_gale : ∀ k, IsGale α (m k))
    (hm_init : ∀ k, m k [] ≤ (1 / 4 : ℝ) ^ k)
    (hm_reach : ∀ k, ∀ w ∈ A, ∃ n, 1 ≤ m k (cantorPrefix w n)) :
    ∃ M : BitString → ℝ, IsGale α M ∧ ∀ w ∈ A, Wins M w := by
  have hnonneg : ∀ k y, 0 ≤ (2 : ℝ) ^ k * m k y := fun k y =>
    mul_nonneg (pow_nonneg (by norm_num) k) ((hm_gale k).nonneg y)
  have hsum : ∀ y, Summable (fun k : ℕ => (2 : ℝ) ^ k * m k y) := by
    intro y
    refine Summable.of_nonneg_of_le (fun k => hnonneg k y) (fun k => ?_)
      (summable_geometric_two.mul_left ((2 : ℝ) ^ (α * y.length)))
    have hg := isAlphaNull_iff_exists_martingale_growth
      α (m k) (hm_gale k) y
    have h4 : (2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = ((1 : ℝ) / 2) ^ k := by
      rw [← mul_pow]
      norm_num
    calc (2 : ℝ) ^ k * m k y
        ≤ (2 : ℝ) ^ k * ((2 : ℝ) ^ (α * y.length) * (1 / 4 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left
            (hg.trans (mul_le_mul_of_nonneg_left (hm_init k) (by positivity))) (by positivity)
      _ = (2 : ℝ) ^ (α * y.length) * ((1 : ℝ) / 2) ^ k := by
          rw [← h4]
          ring
  refine ⟨fun y => ∑' k : ℕ, (2 : ℝ) ^ k * m k y, ?_, ?_⟩
  · refine isAlphaNull_iff_exists_martingale_isGale
      α (fun k y => (2 : ℝ) ^ k * m k y) (fun k => ⟨hnonneg k, fun x => ?_⟩) hsum
    rw [← mul_add, ← (hm_gale k).gale x]
    ring
  · intro w hw hbdd
    obtain ⟨B, hB⟩ := hbdd
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 2)
    obtain ⟨n, hn⟩ := hm_reach k w hw
    have h1 : (2 : ℝ) ^ k * m k (cantorPrefix w n) ≤ ∑' j : ℕ, (2 : ℝ) ^ j * m j (cantorPrefix w n)
        :=
      (hsum _).le_tsum k (fun j _ => hnonneg j _)
    have h2 : ∑' j : ℕ, (2 : ℝ) ^ j * m j (cantorPrefix w n) ≤ B := hB ⟨n, rfl⟩
    have h3 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k * m k (cantorPrefix w n) :=
      le_mul_of_one_le_right (by positivity) hn
    linarith

/-- **SUV p. 285**, second half of Theorem 184 for gales: every `α`-null set is contained in the set
where some `α`-gale is unbounded. -/
theorem exists_isGale_wins_of_isAlphaNull {α : ℝ} (_hα : 0 < α) {A : Set CantorSeq}
    (hA : IsAlphaNull α A) : ∃ m, IsGale α m ∧ ∀ w ∈ A, Wins m w := by
  obtain ⟨m, hm_gale, hm_init, hm_reach⟩ := exists_isGale_wins_of_isAlphaNull_gale_sequence hA
  exact exists_isGale_wins_of_isAlphaNull_final_gale m hm_gale hm_init hm_reach

end Kolmogorov.FrequencyGames
