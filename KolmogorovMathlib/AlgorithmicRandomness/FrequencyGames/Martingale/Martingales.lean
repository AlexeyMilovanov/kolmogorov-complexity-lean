/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.LibraryAPI
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Stieltjes
import KolmogorovMathlib.MonotoneComplexity.MeasureRepresentation

/-!
# Martingales

Martingales and supermartingales with respect to a measure `π` on Cantor space, in the sense of
Shen, Uspensky and Vereshchagin, "Kolmogorov complexity and algorithmic randomness"
(pp. 271-278).

A martingale is a non-negative betting strategy `m : BitString → ℝ` that is fair for `π`, with
initial capital `1`; a supermartingale may give part of its capital away after each game.  The
module defines `IsFairCapital`, `IsMartingale`, `IsSuperfairCapital` and related notions, and
proves the basic properties relating martingales to measures and to open sets of small
measure.
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The mass `π(Ω_x)` as a real number. -/
noncomputable def massR (π : Measure CantorSeq) (x : BitString) : ℝ := (cantorMass π x).toReal

/-- A non-negative capital function that is fair for `π`; the initial capital is not fixed. -/
structure IsFairCapital (π : Measure CantorSeq) (m : BitString → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ m x
  fair : ∀ x, m x * massR π x =
    m (x ++ [false]) * massR π (x ++ [false]) + m (x ++ [true]) * massR π (x ++ [true])

/-- **SUV p. 271 (uniform), p. 274 (general).**  A *martingale* with respect to `π`: non-negative,
fair and with initial capital `1`. -/
structure IsMartingale (π : Measure CantorSeq) (m : BitString → ℝ) : Prop
    extends IsFairCapital π m where
  init : m [] = 1

/-- **SUV p. 278.**  A *supermartingale* with respect to `π`: a non-negative function where the
gambler may give part of the capital away after each game.  The initial capital is free. -/
structure IsSuperfairCapital (π : Measure CantorSeq) (m : BitString → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ m x
  superfair : ∀ x, m (x ++ [false]) * massR π (x ++ [false]) +
    m (x ++ [true]) * massR π (x ++ [true]) ≤ m x * massR π x

/-- A fair capital is a supermartingale. -/
lemma IsFairCapital.isSuperfairCapital {π : Measure CantorSeq} {m : BitString → ℝ}
    (hm : IsFairCapital π m) : IsSuperfairCapital π m :=
  ⟨hm.nonneg, fun x => (hm.fair x).symm.le⟩

/-- `m` *wins* on `ω`: its values on the prefixes of `ω` are not bounded.  SUV p. 272. -/
def Wins (m : BitString → ℝ) (w : CantorSeq) : Prop :=
  ¬ BddAbove (Set.range fun n => m (cantorPrefix w n))

/-- `m` *strongly wins* on `ω`: its values on the prefixes tend to `+∞`.  SUV p. 273. -/
def StronglyWins (m : BitString → ℝ) (w : CantorSeq) : Prop :=
  Tendsto (fun n => m (cantorPrefix w n)) atTop atTop

/-- The values of `m` on the prefixes of `ω` have a finite limit (Theorem 179). -/
def HasFiniteLimit (m : BitString → ℝ) (w : CantorSeq) : Prop :=
  ∃ L : ℝ, Tendsto (fun n => m (cantorPrefix w n)) atTop (𝓝 L)

/-- Strong winning is winning. -/
lemma StronglyWins.wins {m : BitString → ℝ} {w : CantorSeq} (h : StronglyWins m w) : Wins m w :=
  fun hb => not_bddAbove_of_tendsto_atTop h hb

/-- A strongly winning sequence has no finite limit. -/
lemma StronglyWins.not_hasFiniteLimit {m : BitString → ℝ} {w : CantorSeq}
    (h : StronglyWins m w) : ¬ HasFiniteLimit m w := by
  rintro ⟨L, hL⟩
  exact not_tendsto_nhds_of_tendsto_atTop h L hL

/-! ### The uniform measure -/

/-- The uniform mass of a cylinder, as a real number. -/
lemma massR_uniformMeasure (x : BitString) : massR uniformMeasure x = (2 : ℝ)⁻¹ ^ x.length := by
  simp [massR, cantorMass_uniformMeasure, ENNReal.toReal_pow, ENNReal.toReal_inv]

/-- **SUV p. 271.**  For the uniform measure, fairness says that the capital is the average of the
capitals after the two outcomes. -/
theorem isFairCapital_uniform_iff (m : BitString → ℝ) :
    IsFairCapital uniformMeasure m ↔
      (∀ x, 0 ≤ m x) ∧ ∀ x, m x = (m (x ++ [false]) + m (x ++ [true])) / 2 := by
  have hpos : ∀ x : BitString, (0 : ℝ) < (2 : ℝ)⁻¹ ^ x.length := fun x => by positivity
  refine ⟨fun h => ⟨h.nonneg, fun x => ?_⟩, fun h => ⟨h.1, fun x => ?_⟩⟩
  · have hx := h.fair x
    simp only [massR_uniformMeasure, List.length_append, List.length_cons, List.length_nil,
      zero_add, pow_succ] at hx
    have := hpos x
    have hcancel : m x * (2 : ℝ)⁻¹ ^ x.length =
        (m (x ++ [false]) + m (x ++ [true])) / 2 * (2 : ℝ)⁻¹ ^ x.length := by
      rw [hx]; ring
    exact mul_right_cancel₀ this.ne' hcancel
  · have hx := h.2 x
    simp only [massR_uniformMeasure, List.length_append, List.length_cons, List.length_nil,
      zero_add, pow_succ]
    rw [hx]; ring

/-! ### Measures and martingales -/

/-- **SUV p. 271 and Problem 263; p. 274 for general `π`.**  A `π`-martingale is the ratio of a
probability measure and `π`: in the product form that avoids division, `m(x) π(x)` is the mass
function of a probability measure.  Non-negativity is needed since `π(x)` may vanish. -/
theorem isMartingale_iff_exists_measure {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (m : BitString → ℝ) :
    IsMartingale π m ↔ (∀ x, 0 ≤ m x) ∧
      ∃ ν : Measure CantorSeq, IsProbabilityMeasure ν ∧ ∀ x, m x * massR π x = massR ν x := by
  constructor
  · intro h
    have hnn : ∀ x, 0 ≤ m x := h.nonneg
    refine ⟨hnn, ?_⟩
    have hmRnn : ∀ x, 0 ≤ massR π x := fun x => ENNReal.toReal_nonneg
    have ha : IsContinuousTreeSemimeasure (fun x => ENNReal.ofReal (m x * massR π x)) := by
      constructor
      · change ENNReal.ofReal (m [] * massR π []) = 1
        have hπ_nil : massR π ([] : BitString) = 1 := by
          have hcyl : cantorCylinder ([] : BitString) = Set.univ := by
            ext w
            simp [cantorCylinder, IsCantorPrefix]
          simp [massR, cantorMass, hcyl]
        rw [h.init, hπ_nil, mul_one, ENNReal.ofReal_one]
      · intro x
        change ENNReal.ofReal (m (x ++ [false]) * massR π (x ++ [false])) +
          ENNReal.ofReal (m (x ++ [true]) * massR π (x ++ [true])) ≤
          ENNReal.ofReal (m x * massR π x)
        have h0 : 0 ≤ m (x ++ [false]) * massR π (x ++ [false]) := mul_nonneg (hnn _) (hmRnn _)
        have h1 : 0 ≤ m (x ++ [true]) * massR π (x ++ [true]) := mul_nonneg (hnn _) (hmRnn _)
        rw [h.fair x, ENNReal.ofReal_add h0 h1]
    obtain ⟨ν, hν⟩ := exists_measure_cantorSeq_of_isContinuousTreeSemimeasure_of_exact ha (fun x =>
        by
      have h0 : 0 ≤ m (x ++ [false]) * massR π (x ++ [false]) := mul_nonneg (hnn _) (hmRnn _)
      have h1 : 0 ≤ m (x ++ [true]) * massR π (x ++ [true]) := mul_nonneg (hnn _) (hmRnn _)
      rw [h.fair x, ENNReal.ofReal_add h0 h1])
    refine ⟨ν, ?_, ?_⟩
    · constructor
      have := hν []
      change cantorMass ν [] = ENNReal.ofReal (m [] * massR π []) at this
      have hπ_nil : massR π ([] : BitString) = 1 := by
        have hcyl : cantorCylinder ([] : BitString) = Set.univ := by
          ext w
          simp [cantorCylinder, IsCantorPrefix]
        simp [massR, cantorMass, hcyl]
      rw [h.init, hπ_nil, mul_one, ENNReal.ofReal_one] at this
      have hcyl : cantorCylinder [] = Set.univ := by
        ext w
        simp [cantorCylinder, IsCantorPrefix]
      have h_univ : ν (cantorCylinder []) = 1 := this
      rw [hcyl] at h_univ
      exact h_univ
    · intro x
      have := hν x
      change cantorMass ν x = ENNReal.ofReal (m x * massR π x) at this
      have hc : (cantorMass ν x).toReal = (ENNReal.ofReal (m x * massR π x)).toReal := by rw [this]
      rw [ENNReal.toReal_ofReal (mul_nonneg (hnn _) (hmRnn _))] at hc
      exact hc.symm
  · rintro ⟨hnn, ν, hν, heq⟩
    constructor
    · constructor
      · exact hnn
      · intro x
        rw [heq, heq, heq]
        have hne : ∀ y, cantorMass ν y ≠ ∞ := fun y => measure_ne_top ν _
        have h_add := cantorMass_add ν x
        change (cantorMass ν x).toReal = _
        rw [h_add, ENNReal.toReal_add (hne _) (hne _)]
        rfl
    · have h0 := heq []
      have hπ_nil : massR π ([] : BitString) = 1 := by
        have hcyl : cantorCylinder ([] : BitString) = Set.univ := by
          ext w
          simp [cantorCylinder, IsCantorPrefix]
        simp [massR, cantorMass, hcyl]
      have hν_nil : massR ν ([] : BitString) = 1 := by
        have hcyl : cantorCylinder ([] : BitString) = Set.univ := by
          ext w
          simp [cantorCylinder, IsCantorPrefix]
        simp [massR, cantorMass, hcyl]
      rw [hπ_nil, hν_nil, mul_one] at h0
      exact h0

/-- **SUV Problem 263, p. 271.**  For the uniform measure `μ`, the martingales are exactly the
ratios `ν(Ω_x) / μ(Ω_x)` of a probability measure `ν` and `μ`; here `μ(Ω_x)` is never `0`. -/
theorem isMartingale_uniform_iff_exists_measure (m : BitString → ℝ) :
    IsMartingale uniformMeasure m ↔
      ∃ ν : Measure CantorSeq, IsProbabilityMeasure ν ∧
        ∀ x, m x = massR ν x / massR uniformMeasure x := by
  constructor
  · rintro hm
    let a := fun x => ENNReal.ofReal (m x * massR uniformMeasure x)
    have ha : IsContinuousTreeSemimeasure a := by
      constructor
      · have h1 : m [] = 1 := hm.init
        have h2 : massR uniformMeasure [] = 1 := by
          rw [massR_uniformMeasure]
          simp
        simp [a, h1, h2]
      · intro x
        have h_fair := hm.toIsFairCapital.fair x
        have hm1 := hm.toIsFairCapital.nonneg (x ++ [false])
        have hm2 := hm.toIsFairCapital.nonneg (x ++ [true])
        have hr1 : 0 ≤ massR uniformMeasure (x ++ [false]) := by
          rw [massR_uniformMeasure]
          positivity
        have hr2 : 0 ≤ massR uniformMeasure (x ++ [true]) := by
          rw [massR_uniformMeasure]
          positivity
        have h1 : 0 ≤ m (x ++ [false]) * massR uniformMeasure (x ++ [false]) :=
          mul_nonneg hm1 hr1
        have h2 : 0 ≤ m (x ++ [true]) * massR uniformMeasure (x ++ [true]) :=
          mul_nonneg hm2 hr2
        dsimp [a]
        rw [h_fair, ENNReal.ofReal_add h1 h2]
    have hadd : ∀ x, a x = a (x ++ [false]) + a (x ++ [true]) := by
      intro x
      have h_fair := hm.toIsFairCapital.fair x
      have hm1 := hm.toIsFairCapital.nonneg (x ++ [false])
      have hm2 := hm.toIsFairCapital.nonneg (x ++ [true])
      have hr1 : 0 ≤ massR uniformMeasure (x ++ [false]) := by
        rw [massR_uniformMeasure]
        positivity
      have hr2 : 0 ≤ massR uniformMeasure (x ++ [true]) := by
        rw [massR_uniformMeasure]
        positivity
      have h1 : 0 ≤ m (x ++ [false]) * massR uniformMeasure (x ++ [false]) :=
        mul_nonneg hm1 hr1
      have h2 : 0 ≤ m (x ++ [true]) * massR uniformMeasure (x ++ [true]) :=
        mul_nonneg hm2 hr2
      dsimp [a]
      rw [h_fair, ENNReal.ofReal_add h1 h2]
    obtain ⟨ν, hν⟩ := exists_measure_cantorSeq_of_isContinuousTreeSemimeasure_of_exact ha hadd
    use ν
    constructor
    · constructor
      have h_univ : cantorCylinder [] = Set.univ := by
        ext x
        simp [cantorCylinder, IsCantorPrefix]
      have h_empty : cantorMass ν [] = 1 := by
        rw [hν]
        exact ha.1
      rw [cantorMass, h_univ] at h_empty
      exact h_empty
    · intro x
      have hm_nn := hm.toIsFairCapital.nonneg x
      have hr_pos : 0 < massR uniformMeasure x := by
        rw [massR_uniformMeasure]
        positivity
      have h_eq : massR ν x = m x * massR uniformMeasure x := by
        dsimp [massR]
        rw [hν, ENNReal.toReal_ofReal (mul_nonneg hm_nn hr_pos.le)]
        rfl
      rw [h_eq, mul_div_cancel_right₀ _ hr_pos.ne']
  · rintro ⟨ν, hν, h_eq⟩
    constructor
    · constructor
      · intro x
        rw [h_eq]
        have h1 : 0 ≤ massR ν x := ENNReal.toReal_nonneg
        have h2 : 0 < massR uniformMeasure x := by
          rw [massR_uniformMeasure]
          positivity
        exact div_nonneg h1 h2.le
      · intro x
        rw [h_eq x, h_eq (x ++ [false]), h_eq (x ++ [true])]
        have hr : 0 < massR uniformMeasure x := by rw [massR_uniformMeasure]; positivity
        have hr0 : 0 < massR uniformMeasure (x ++ [false]) := by
          rw [massR_uniformMeasure]; positivity
        have hr1 : 0 < massR uniformMeasure (x ++ [true]) := by
          rw [massR_uniformMeasure]; positivity
        rw [div_mul_cancel₀ _ hr.ne', div_mul_cancel₀ _ hr0.ne', div_mul_cancel₀ _ hr1.ne']
        have hne : ∀ y, cantorMass ν y ≠ ∞ := fun y => measure_ne_top ν _
        have h_add := cantorMass_add ν x
        have h_add_real : (cantorMass ν x).toReal =
          (cantorMass ν (x ++ [false]) + cantorMass ν (x ++ [true])).toReal := by rw [h_add]
        rw [ENNReal.toReal_add (hne _) (hne _)] at h_add_real
        exact h_add_real
    · rw [h_eq []]
      have hr : massR uniformMeasure [] = 1 := by rw [massR_uniformMeasure]; simp
      have hn : massR ν [] = 1 := by
        dsimp [massR, cantorMass]
        have h_univ : cantorCylinder [] = Set.univ := by
          ext x; simp [cantorCylinder, IsCantorPrefix]
        rw [h_univ, hν.measure_univ]
        rfl
      rw [hr, hn, div_one]

/-! ### Ville's inequality and its converse -/

/-- The extensions of `x` on which `m` reaches `k` within `N` more bits. -/
private def hitWithin (m : BitString → ℝ) (k : ℝ) (x : BitString) (N : ℕ) : Set CantorSeq :=
  {w | IsCantorPrefix x w ∧ ∃ j ≤ N, k ≤ m (cantorPrefix w (x.length + j))}

/-- The mass of the empty string is `1`. -/
lemma massR_nil (π : Measure CantorSeq) [IsProbabilityMeasure π] : massR π [] = 1 := by
  have hcyl : cantorCylinder [] = Set.univ := by
    ext w
    simp [cantorCylinder, IsCantorPrefix]
  simp [massR, cantorMass, hcyl]

/-- The induction of Ville's inequality on the depth `N`: the expected capital bounds `k` times the
measure of the event of reaching `k`.  This is the book's "go home when the capital reaches `k`". -/
private lemma mul_measure_hitWithin_le {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsSuperfairCapital π m) {k : ℝ} (hk : 0 < k) (N : ℕ) :
    ∀ x, k * (π (hitWithin m k x N)).toReal ≤ m x * massR π x := by
  have hne : ∀ s : Set CantorSeq, π s ≠ ⊤ := fun s => measure_ne_top π s
  have hnn : ∀ x, 0 ≤ massR π x := fun x => ENNReal.toReal_nonneg
  have hreach : ∀ {x : BitString} {N : ℕ}, k ≤ m x →
      k * (π (hitWithin m k x N)).toReal ≤ m x * massR π x := by
    intro x N hx
    have hsub : (π (hitWithin m k x N)).toReal ≤ massR π x :=
      ENNReal.toReal_mono (hne _) (measure_mono fun w hw => hw.1)
    exact (mul_le_mul_of_nonneg_left hsub hk.le).trans
      (mul_le_mul_of_nonneg_right hx (hnn x))
  induction N with
  | zero =>
    intro x
    by_cases hx : k ≤ m x
    · exact hreach hx
    · have hempty : hitWithin m k x 0 = ∅ := by
        ext w
        simp only [hitWithin, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hw, j, hj, hjk⟩
        obtain rfl : j = 0 := Nat.le_zero.mp hj
        rw [Nat.add_zero, (isCantorPrefix_iff_cantorPrefix_eq x w).mp hw] at hjk
        exact hx hjk
      rw [hempty]
      simpa using mul_nonneg (hm.nonneg x) (hnn x)
  | succ N ih =>
    intro x
    by_cases hx : k ≤ m x
    · exact hreach hx
    · have hsub : hitWithin m k x (N + 1) ⊆
          hitWithin m k (x ++ [false]) N ∪ hitWithin m k (x ++ [true]) N := by
        rintro w ⟨hw, j, hj, hjk⟩
        have hj0 : j ≠ 0 := by
          rintro rfl
          rw [Nat.add_zero, (isCantorPrefix_iff_cantorPrefix_eq x w).mp hw] at hjk
          exact hx hjk
        obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        have hmem : w ∈ hitWithin m k (x ++ [w x.length]) N := by
          refine ⟨(isCantorPrefix_append_singleton x _ w).mpr ⟨hw, rfl⟩, i, by omega, ?_⟩
          have hlen : (x ++ [w x.length]).length + i = x.length + i.succ := by
            simp
            omega
          rwa [hlen]
        cases hb : w x.length with
        | false => exact Or.inl (hb ▸ hmem)
        | true => exact Or.inr (hb ▸ hmem)
      have hle : (π (hitWithin m k x (N + 1))).toReal ≤
          (π (hitWithin m k (x ++ [false]) N)).toReal +
            (π (hitWithin m k (x ++ [true]) N)).toReal := by
        rw [← ENNReal.toReal_add (hne _) (hne _)]
        exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne _, hne _⟩)
          ((measure_mono hsub).trans (measure_union_le _ _))
      have h0 := ih (x ++ [false])
      have h1 := ih (x ++ [true])
      have hs := hm.superfair x
      calc k * (π (hitWithin m k x (N + 1))).toReal
          ≤ k * ((π (hitWithin m k (x ++ [false]) N)).toReal +
              (π (hitWithin m k (x ++ [true]) N)).toReal) :=
            mul_le_mul_of_nonneg_left hle hk.le
        _ ≤ m x * massR π x := by linarith

/-- **SUV p. 278.**  Ville's inequality for a supermartingale, with free initial capital: the
`π`-measure of the sequences on some prefix of which `m` reaches `k` is at most `m(Λ) / k`. -/
theorem measure_exists_ge_le_of_superfair {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsSuperfairCapital π m) {k : ℝ} (hk : 0 < k) :
    π {w | ∃ n, k ≤ m (cantorPrefix w n)} ≤ ENNReal.ofReal (m [] / k) := by
  have hunion : {w | ∃ n, k ≤ m (cantorPrefix w n)} = ⋃ N, hitWithin m k [] N := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hitWithin]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, fun i hi => absurd hi (Nat.not_lt_zero i), n, le_rfl, by simpa using hn⟩
    · rintro ⟨_, _, j, _, hj⟩
      exact ⟨_, hj⟩
  have hmono : Monotone (hitWithin m k []) := by
    intro N N' hNN' w hw
    obtain ⟨hw0, j, hj, hjk⟩ := hw
    exact ⟨hw0, j, hj.trans hNN', hjk⟩
  rw [hunion, hmono.measure_iUnion]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top π (hitWithin m k [] N))]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := mul_measure_hitWithin_le hm hk N []
  rw [massR_nil, mul_one] at h
  rw [le_div_iff₀ hk]
  linarith

/-- **SUV (1), p. 274, with free initial capital.**  The `π`-measure of the sequences on some prefix
of which `m` reaches `k` is at most `m(Λ) / k`. -/
theorem measure_exists_ge_le {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsFairCapital π m) {k : ℝ} (hk : 0 < k) :
    π {w | ∃ n, k ≤ m (cantorPrefix w n)} ≤ ENNReal.ofReal (m [] / k) :=
  measure_exists_ge_le_of_superfair hm.isSuperfairCapital hk

/-- **SUV Theorem 175, p. 271 (Ville, Doob, Kolmogorov).**  For a uniform martingale and `k > 0`,
the uniform measure of the sequences having a prefix on which `m` is at least `k` is at most
`1 / k`.  The book says "exceeds `k`" in the statement and "`k` (or more)" in the proof; the form
with `≤` is the stronger one. -/
theorem measure_exists_ge_le_of_isMartingale {m : BitString → ℝ}
    (hm : IsMartingale uniformMeasure m) {k : ℝ} (hk : 0 < k) :
    uniformMeasure {w | ∃ n, k ≤ m (cantorPrefix w n)} ≤ ENNReal.ofReal (1 / k) := by
  have h := measure_exists_ge_le hm.toIsFairCapital hk
  rwa [hm.init] at h


/-- Step 1 of the proof of `exists_isMartingale_ge_of_isOpen`:
The measure `ν` defined as a linear combination of `uniformMeasure` restricted to `U`
and `uniformMeasure` globally is a probability measure. -/
private lemma exists_isMartingale_ge_of_isOpen_step1 {U : Set CantorSeq} {ε : ℝ} (hε : 0 < ε)
    (hμ : uniformMeasure U ≤ ENNReal.ofReal ε) :
    let μ := uniformMeasure
    let ε' := ENNReal.ofReal ε
    let ν₁ : Measure CantorSeq := (1 / ε') • (μ.restrict U)
    let ν₂ : Measure CantorSeq := (1 - μ U / ε') • μ
    let ν := ν₁ + ν₂
    IsProbabilityMeasure ν := by
  intro μ ε' ν₁ ν₂ ν
  have h0 : ε' ≠ 0 := by simpa [ε'] using hε
  have hT : ε' ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle : μ U / ε' ≤ 1 := by
    rw [ENNReal.div_le_iff h0 hT, one_mul]; exact hμ
  constructor
  show ν Set.univ = 1
  simp only [ν, ν₁, ν₂, Measure.add_apply, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, measure_univ, mul_one]
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  exact add_tsub_cancel_of_le hle

/-- Step 2 of the proof of `exists_isMartingale_ge_of_isOpen`:
The ratio of `massR ν x` and `massR uniformMeasure x` is at least `1 / ε`
when the cylinder of `x` is contained in `U`. -/
private lemma exists_isMartingale_ge_of_isOpen_step2 {U : Set CantorSeq} {ε : ℝ} (hε : 0 < ε) :
    let μ := uniformMeasure
    let ε' := ENNReal.ofReal ε
    let ν₁ : Measure CantorSeq := (1 / ε') • (μ.restrict U)
    let ν₂ : Measure CantorSeq := (1 - μ U / ε') • μ
    let ν := ν₁ + ν₂
    ∀ x, cantorCylinder x ⊆ U →
      massR ν x / massR μ x ≥ 1 / ε := by
  intro μ ε' ν₁ ν₂ ν x hx
  have hmeas : MeasurableSet (cantorCylinder x) := measurableSet_cantorCylinder x
  have hpos : 0 < massR μ x := by
    change 0 < massR uniformMeasure x
    rw [massR_uniformMeasure]; positivity
  have hεne : ε' ≠ 0 := by simpa [ε'] using hε
  have hνx : ν (cantorCylinder x) = ε'⁻¹ * μ (cantorCylinder x) +
      (1 - μ U / ε') * μ (cantorCylinder x) := by
    have hr : (μ.restrict U) (cantorCylinder x) = μ (cantorCylinder x) := by
      rw [Measure.restrict_apply hmeas, Set.inter_eq_left.mpr hx]
    simp only [ν, ν₁, ν₂, Measure.add_apply, Measure.smul_apply, smul_eq_mul, hr, one_div]
  have hfin : μ (cantorCylinder x) ≠ ∞ := by
    change uniformMeasure (cantorCylinder x) ≠ ∞
    exact measure_ne_top _ _
  have hle : ε'⁻¹ * μ (cantorCylinder x) ≤ ν (cantorCylinder x) := by
    rw [hνx]; exact le_self_add
  have hfinν : ν (cantorCylinder x) ≠ ∞ := by
    rw [hνx]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hεne) hfin,
      ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) hfin⟩
  have h2 := ENNReal.toReal_mono hfinν hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hε.le] at h2
  have h3 : ε⁻¹ * massR μ x ≤ massR ν x := h2
  rw [ge_iff_le, le_div_iff₀ hpos, one_div]
  exact h3

/-- **SUV Theorem 176, p. 272.**  For an open set `U` of uniform measure at most `ε`, with `ε > 0`,
there is a martingale reaching `1 / ε` on every element of `U`, and staying at or above it on all
sufficiently long prefixes (as the proof shows and p. 273 uses).  The published text says "measure
`ε`", the author's version "measure at most `ε`"; the latter is what is stated, and it implies the
former. -/
theorem exists_isMartingale_ge_of_isOpen {U : Set CantorSeq} (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε)
    (hμ : uniformMeasure U ≤ ENNReal.ofReal ε) :
    ∃ m, IsMartingale uniformMeasure m ∧
      ∀ w ∈ U, ∃ n, ∀ l, n ≤ l → 1 / ε ≤ m (cantorPrefix w l) := by
  let μ := uniformMeasure
  let ε' := ENNReal.ofReal ε
  let ν₁ : Measure CantorSeq := (1 / ε') • (μ.restrict U)
  let ν₂ : Measure CantorSeq := (1 - μ U / ε') • μ
  let ν := ν₁ + ν₂
  have hν : IsProbabilityMeasure ν := exists_isMartingale_ge_of_isOpen_step1 hε hμ
  let m : BitString → ℝ := fun x => massR ν x / massR μ x
  have hm : IsMartingale μ m := isMartingale_uniform_iff_exists_measure m |>.mpr ⟨ν, hν, fun x =>
      rfl⟩
  use m, hm
  intro w hw
  have h_open := isTopologicalBasis_cantorCylinders.isOpen_iff.mp hU w hw
  obtain ⟨B, hB_basis, hw_in_B, hB_sub_U⟩ := h_open
  obtain ⟨x, rfl⟩ := hB_basis
  let n := x.length
  use n
  intro l hl
  have h_sub : cantorCylinder (cantorPrefix w l) ⊆ U := by
    have h_prefix : x <+: cantorPrefix w l := by
      rw [List.prefix_iff_eq_take]
      apply List.ext_getElem
      · have hl' : x.length ≤ l := hl
        simp [hl']
      · intro i hi1 hi2
        have hi : i < x.length := by simpa using hi1
        have hw_eq := hw_in_B i hi
        simp only [List.getElem_take]
        have hil : i < l := lt_of_lt_of_le hi hl
        have hlen : (cantorPrefix w l).length = l := by simp [cantorPrefix]
        have h_il : i < (cantorPrefix w l).length := by omega
        rw [cantorPrefix_getElem _ _ _ h_il, ← hw_eq]
    exact (cantorCylinder_subset_of_prefix h_prefix).trans hB_sub_U
  have := exists_isMartingale_ge_of_isOpen_step2 hε (cantorPrefix w l) h_sub
  exact this

/-- **SUV (2), p. 274.**  For an open set `U` of positive `π`-measure there is a `π`-martingale
reaching `1 / π(U)` on all elements of `U`.  The set of positive measure is needed for the value to
make sense. -/
theorem exists_isMartingale_ge_of_isOpen' {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {U : Set CantorSeq} (hU : IsOpen U) (hpos : 0 < π U) :
    ∃ m, IsMartingale π m ∧ ∀ w ∈ U, ∃ n, ∀ l, n ≤ l →
      1 / (π U).toReal ≤ m (cantorPrefix w l) := by
  let ν : Measure CantorSeq := (π U)⁻¹ • (π.restrict U)
  have hν : IsProbabilityMeasure ν := by
    constructor
    have hne_top : π U ≠ ∞ := measure_ne_top π U
    have h1 : ν Set.univ = 1 := by
      change ((π U)⁻¹ • (π.restrict U)) Set.univ = 1
      rw [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Measure.restrict_apply MeasurableSet.univ]
      rw [Set.univ_inter]
      exact ENNReal.inv_mul_cancel hpos.ne' hne_top
    exact h1
  let m : BitString → ℝ := fun x =>
    if massR π x = 0 then 1 / (π U).toReal else massR ν x / massR π x
  have hm_nn : ∀ x, 0 ≤ m x := fun x => by
    dsimp [m]
    split_ifs with h
    · exact div_nonneg zero_le_one ENNReal.toReal_nonneg
    · exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have h_fair : ∀ x, m x * massR π x = massR ν x := fun x => by
    dsimp [m]
    split_ifs with h
    · have h_le : π (cantorCylinder x ∩ U) ≤ π (cantorCylinder x) := measure_mono
        (Set.inter_subset_left)
      have h_zero : π (cantorCylinder x) = 0 := by
        dsimp [massR, cantorMass] at h
        rw [ENNReal.toReal_eq_zero_iff] at h
        cases h with
        | inl h => exact h
        | inr h => exact (measure_ne_top π _ h).elim
      rw [h_zero] at h_le
      have h_int_zero : π (cantorCylinder x ∩ U) = 0 := le_antisymm h_le (zero_le)
      have h_ν_zero : massR ν x = 0 := by
        dsimp [massR, cantorMass, ν]
        change (((π U)⁻¹ • (π.restrict U)) (cantorCylinder x)).toReal = 0
        rw [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
        rw [Measure.restrict_apply (isOpen_cantorCylinder x).measurableSet]
        rw [h_int_zero, mul_zero]
        rfl
      rw [h, h_ν_zero, mul_zero]
    · rw [div_mul_cancel₀ _ h]
  have h_mart : IsMartingale π m := by
    rw [isMartingale_iff_exists_measure]
    exact ⟨hm_nn, ν, hν, h_fair⟩
  use m
  refine ⟨h_mart, fun w hw => ?_⟩
  have h_open := hU
  rw [isTopologicalBasis_cantorCylinders.isOpen_iff] at h_open
  obtain ⟨C, hC_mem, hw_mem, hC_sub⟩ := h_open w hw
  obtain ⟨x, rfl⟩ := hC_mem
  use x.length
  intro l hl
  dsimp [m]
  split_ifs with h_zero
  · exact le_rfl
  · have h_ν : massR ν (cantorPrefix w l) = ((π U)⁻¹ * π (cantorCylinder (cantorPrefix w l) ∩
      U)).toReal := by
      dsimp [massR, cantorMass, ν]
      change (((π U)⁻¹ • (π.restrict U)) (cantorCylinder (cantorPrefix w l))).toReal = _
      rw [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Measure.restrict_apply (isOpen_cantorCylinder _).measurableSet]
    rw [h_ν]
    have h_sub : cantorCylinder (cantorPrefix w l) ⊆ U := by
      intro y hy
      have h_pref_w : IsCantorPrefix x w := hw_mem
      have H2 : cantorPrefix y x.length = cantorPrefix w x.length := by
        have H_y : cantorPrefix y l = cantorPrefix w l := by
          have H_hy := (isCantorPrefix_iff_cantorPrefix_eq _ _).mp hy
          rw [cantorPrefix_length] at H_hy
          exact H_hy
        have h_take_y := cantorPrefix_take y x.length l hl
        have h_take_w := cantorPrefix_take w x.length l hl
        rw [H_y] at h_take_y
        rw [h_take_y] at h_take_w
        exact h_take_w
      have H1 := (isCantorPrefix_iff_cantorPrefix_eq _ _).mp h_pref_w
      have h_x_y : IsCantorPrefix x y := by
        apply (isCantorPrefix_iff_cantorPrefix_eq _ _).mpr
        rw [H2, H1]
      exact hC_sub h_x_y
    have h_int : cantorCylinder (cantorPrefix w l) ∩ U = cantorCylinder (cantorPrefix w l) :=
      Set.inter_eq_self_of_subset_left h_sub
    rw [h_int]
    have h_mul : ((π U)⁻¹ * π (cantorCylinder (cantorPrefix w l))).toReal =
      (π U)⁻¹.toReal * (π (cantorCylinder (cantorPrefix w l))).toReal := by
      rw [ENNReal.toReal_mul]
    rw [h_mul]
    dsimp [massR, cantorMass] at h_zero ⊢
    have hr1 : (π U)⁻¹.toReal = 1 / (π U).toReal := by
      rw [ENNReal.toReal_inv, inv_eq_one_div]
    rw [hr1]
    have h_ne_zero : (π (cantorCylinder (cantorPrefix w l))).toReal ≠ 0 := h_zero
    rw [mul_div_cancel_right₀ _ h_ne_zero]

/-! ### Ville's theorem -/

/-- **SUV Theorem 177(a), p. 273, and (3), p. 274.**  The sequences on which a `π`-martingale wins
form a `π`-null set. -/
theorem measure_wins_eq_zero {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsMartingale π m) : π {w | Wins m w} = 0 := by
  have hbound : ∀ n : ℕ, π {w | Wins m w} ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    have hk : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h := measure_exists_ge_le hm.toIsFairCapital hk
    rw [hm.init] at h
    refine (measure_mono fun w hw => ?_).trans h
    by_contra hcon
    refine hw ⟨(n : ℝ) + 1, ?_⟩
    rintro _ ⟨l, rfl⟩
    by_contra hl
    exact hcon ⟨l, (not_le.mp hl).le⟩
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_antisymm (ge_of_tendsto' hlim hbound) (zero_le)


/-- Auxiliary: for an open set `U` and `w ∈ U`, the cylinders of all long prefixes of `w` lie
in `U`. -/
private lemma exists_isMartingale_stronglyWins_of_null_seq_aux_cyl {U : Set CantorSeq}
    (hU : IsOpen U) {w : CantorSeq} (hw : w ∈ U) :
    ∃ n, ∀ l, n ≤ l → cantorCylinder (cantorPrefix w l) ⊆ U := by
  have h_open := isTopologicalBasis_cantorCylinders.isOpen_iff.mp hU w hw
  obtain ⟨B, hB_basis, hw_in_B, hB_sub_U⟩ := h_open
  obtain ⟨x, rfl⟩ := hB_basis
  refine ⟨x.length, fun l hl => ?_⟩
  have h_prefix : x <+: cantorPrefix w l := by
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem
    · have hl' : x.length ≤ l := hl
      simp [hl']
    · intro i hi1 hi2
      have hi : i < x.length := by simpa using hi1
      have hw_eq := hw_in_B i hi
      simp only [List.getElem_take]
      have hil : i < l := lt_of_lt_of_le hi hl
      have hlen : (cantorPrefix w l).length = l := by simp [cantorPrefix]
      have h_il : i < (cantorPrefix w l).length := by omega
      rw [cantorPrefix_getElem _ _ _ h_il, ← hw_eq]
  exact (cantorCylinder_subset_of_prefix h_prefix).trans hB_sub_U

/-- Auxiliary: masses add (real version of `cantorMass_add`). -/
private lemma exists_isMartingale_stronglyWins_of_null_seq_aux_add
    {π : Measure CantorSeq} [IsProbabilityMeasure π] (x : BitString) :
    massR π x = massR π (x ++ [false]) + massR π (x ++ [true]) := by
  have hne : ∀ y, cantorMass π y ≠ ∞ := fun y => measure_ne_top π _
  simp only [massR]
  rw [cantorMass_add π x, ENNReal.toReal_add (hne _) (hne _)]

/-- Step (a): one martingale per level `k`. -/
private lemma exists_isMartingale_stronglyWins_of_null_seq_aux_level
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {X : Set CantorSeq}
    (hX : π X = 0) (k : ℕ) :
    ∃ m : BitString → ℝ, IsMartingale π m ∧ ∀ w, w ∈ X → ∃ n, ∀ l, n ≤ l →
      (4 : ℝ) ^ k ≤ m (cantorPrefix w l) := by
  have hr : π X < ENNReal.ofReal ((1 / 4 : ℝ) ^ k) := by
    rw [hX]; exact ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨U, hXU, hUo, hUlt⟩ := Set.exists_isOpen_lt_of_lt X _ hr
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  by_cases hpos : 0 < π U
  · obtain ⟨m, hm, hge⟩ := exists_isMartingale_ge_of_isOpen' hUo hpos
    refine ⟨m, hm, fun w hw => ?_⟩
    obtain ⟨n, hn⟩ := hge w (hXU hw)
    refine ⟨n, fun l hl => le_trans ?_ (hn l hl)⟩
    have hpr : (0 : ℝ) < (π U).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top π _)
    have hlt : (π U).toReal < (1 / 4 : ℝ) ^ k := by
      have := (ENNReal.toReal_lt_toReal (measure_ne_top π _) ENNReal.ofReal_ne_top).mpr hUlt
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    rw [le_div_iff₀ hpr]
    have : (4 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = 1 := by
      rw [← mul_pow]; norm_num
    nlinarith
  · have hU0 : π U = 0 := le_antisymm (not_lt.mp hpos) zero_le
    classical
    let m : BitString → ℝ := fun y => if massR π y = 0 then (4 : ℝ) ^ k else 1
    have hmass : ∀ y, m y * massR π y = massR π y := fun y => by
      by_cases h : massR π y = 0 <;> simp [m, h]
    refine ⟨m, ⟨⟨fun y => ?_, fun y => ?_⟩, ?_⟩, fun w hw => ?_⟩
    · dsimp [m]; split_ifs <;> positivity
    · rw [hmass, hmass, hmass]
      exact exists_isMartingale_stronglyWins_of_null_seq_aux_add y
    · have : massR π [] = 1 := massR_nil π
      simp [m, this]
    · obtain ⟨n, hn⟩ := exists_isMartingale_stronglyWins_of_null_seq_aux_cyl hUo (hXU hw)
      refine ⟨n, fun l hl => ?_⟩
      have h0 : massR π (cantorPrefix w l) = 0 := by
        have : π (cantorCylinder (cantorPrefix w l)) = 0 :=
          le_antisymm ((measure_mono (hn l hl)).trans hU0.le) zero_le
        simp [massR, cantorMass, this]
      simp [m, h0]

/-- Step (b): make a sequence of martingales pointwise summable. -/
private lemma exists_isMartingale_stronglyWins_of_null_seq_aux_summable
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {X : Set CantorSeq}
    (ms : ℕ → BitString → ℝ) (hm : ∀ k, IsMartingale π (ms k))
    (hg : ∀ k w, w ∈ X → ∃ n, ∀ l, n ≤ l → (4 : ℝ) ^ k ≤ ms k (cantorPrefix w l)) :
    ∃ ms' : ℕ → BitString → ℝ,
      (∀ k, IsMartingale π (ms' k)) ∧
      (∀ k w, w ∈ X → ∃ n, ∀ l, n ≤ l → (4 : ℝ) ^ k ≤ ms' k (cantorPrefix w l)) ∧
      (∀ x, Summable (fun k => (1 / 2 : ℝ) ^ (k + 1) * ms' k x)) := by
  classical
  let ms' : ℕ → BitString → ℝ := fun k x =>
    if massR π x = 0 ∧ x.length < k then 0 else ms k x
  have hnn : ∀ y, 0 ≤ massR π y := fun y => ENNReal.toReal_nonneg
  have hmass : ∀ k y, ms' k y * massR π y = ms k y * massR π y := fun k y => by
    by_cases h : massR π y = 0 ∧ y.length < k
    · simp [ms', h.1]
    · simp [ms', h]
  refine ⟨ms', fun k => ⟨⟨fun y => ?_, fun y => ?_⟩, ?_⟩, fun k w hw => ?_, fun x => ?_⟩
  · dsimp [ms']; split_ifs
    · exact le_rfl
    · exact (hm k).nonneg y
  · rw [hmass, hmass, hmass]; exact (hm k).fair y
  · have : massR π [] = 1 := massR_nil π
    simp [ms', this, (hm k).init]
  · obtain ⟨n, hn⟩ := hg k w hw
    refine ⟨max n k, fun l hl => ?_⟩
    have hlen : ¬ ((cantorPrefix w l).length < k) := by
      have : (cantorPrefix w l).length = l := by simp [cantorPrefix]
      omega
    have := hn l (le_trans (le_max_left _ _) hl)
    have hlk : k ≤ l := le_trans (le_max_right _ _) hl
    have hlen' : ¬ (massR π (cantorPrefix w l) = 0 ∧ l < k) := fun h => by omega
    simpa [ms', hlen'] using this
  · by_cases hx : massR π x = 0
    · refine summable_of_ne_finset_zero (s := Finset.range (x.length + 1)) fun k hk => ?_
      have : x.length < k := by simpa using hk
      simp [ms', hx, this]
    · have hxpos : 0 < massR π x := lt_of_le_of_ne (hnn x) (Ne.symm hx)
      have hbound : ∀ k, ms' k x ≤ 1 / massR π x := fun k => by
        have h1 : ms' k x = ms k x := by simp [ms', hx]
        rw [h1, le_div_iff₀ hxpos]
        obtain ⟨hnn', ν, hν, hfair⟩ := (isMartingale_iff_exists_measure (ms k)).mp (hm k)
        rw [hfair x]
        have : cantorMass ν x ≤ 1 := prob_le_one
        simpa [massR] using ENNReal.toReal_mono ENNReal.one_ne_top this
      have hs : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) * (1 / massR π x)) := by
        have := ((summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)).mul_left (1 / 2)).mul_right (1 / massR π x)
        simpa [pow_succ, mul_comm] using this
      refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hs
      · have : 0 ≤ ms' k x := by
          dsimp [ms']; split_ifs
          · exact le_rfl
          · exact (hm k).nonneg x
        positivity
      · exact mul_le_mul_of_nonneg_left (hbound k) (by positivity)

/-- Step 1 of the proof of `exists_isMartingale_stronglyWins_of_null`: Construct a
sequence of martingales that strongly win and are pointwise summable. -/
private theorem exists_isMartingale_stronglyWins_of_null_seq
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {X : Set CantorSeq}
    (hX : π X = 0) :
    ∃ ms : ℕ → BitString → ℝ,
      (∀ k, IsMartingale π (ms k)) ∧
      (∀ k w, w ∈ X → ∃ n, ∀ l, n ≤ l →
        (4 : ℝ) ^ k ≤ ms k (cantorPrefix w l)) ∧
      (∀ x, Summable (fun k => (1 / 2 : ℝ) ^ (k + 1) * ms k x)) := by
  choose ms hm hg using exists_isMartingale_stronglyWins_of_null_seq_aux_level hX
  exact exists_isMartingale_stronglyWins_of_null_seq_aux_summable ms hm hg

/-- Step 2 of the proof of `exists_isMartingale_stronglyWins_of_null`: Prove that the
weighted sum of martingales is a martingale. -/
private theorem exists_isMartingale_stronglyWins_of_null_sum
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (ms : ℕ → BitString → ℝ)
    (hm : ∀ k, IsMartingale π (ms k))
    (hs : ∀ x, Summable (fun k => (1 / 2 : ℝ) ^ (k + 1) * ms k x)) :
    IsMartingale π (fun x => ∑' k, (1 / 2 : ℝ) ^ (k + 1) * ms k x) := by
  refine ⟨⟨fun x => tsum_nonneg fun k => mul_nonneg (by positivity) ((hm k).nonneg x),
    fun x => ?_⟩, ?_⟩
  · have h1 := hs (x ++ [false])
    have h2 := hs (x ++ [true])
    rw [← tsum_mul_right, ← tsum_mul_right, ← tsum_mul_right,
      ← (h1.mul_right (massR π (x ++ [false]))).tsum_add (h2.mul_right (massR π (x ++ [true])))]
    refine tsum_congr fun k => ?_
    have := (hm k).fair x
    calc (1 / 2 : ℝ) ^ (k + 1) * ms k x * massR π x
        = (1 / 2 : ℝ) ^ (k + 1) * (ms k x * massR π x) := by ring
      _ = _ := by rw [this]; ring
  · show ∑' k, (1 / 2 : ℝ) ^ (k + 1) * ms k [] = 1
    simp only [(hm _).init, mul_one, pow_succ]
    rw [tsum_mul_right, tsum_geometric_two]
    norm_num

/-- Step 3 of the proof of `exists_isMartingale_stronglyWins_of_null`: Prove that the
weighted sum strongly wins on the null set. -/
private theorem exists_isMartingale_stronglyWins_of_null_limit
    {X : Set CantorSeq} (ms : ℕ → BitString → ℝ)
    (hn : ∀ k x, 0 ≤ ms k x)
    (hs : ∀ x, Summable (fun k => (1 / 2 : ℝ) ^ (k + 1) * ms k x))
    (hg : ∀ k w, w ∈ X → ∃ n, ∀ l, n ≤ l →
      (4 : ℝ) ^ k ≤ ms k (cantorPrefix w l)) :
    ∀ w ∈ X, StronglyWins
      (fun x => ∑' k, (1 / 2 : ℝ) ^ (k + 1) * ms k x) w := by
  intro w hw
  rw [StronglyWins, Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (2 * b) (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨n, hn'⟩ := hg K w hw
  refine ⟨n, fun l hl => ?_⟩
  have h1 := (hs (cantorPrefix w l)).le_tsum K
    (fun j _ => mul_nonneg (by positivity) (hn j _))
  have h2 : (1 / 2 : ℝ) ^ (K + 1) * 4 ^ K = 2 ^ K / 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_succ, one_div, inv_pow]
    field_simp
  have h3 : (1 / 2 : ℝ) ^ (K + 1) * 4 ^ K ≤
      (1 / 2 : ℝ) ^ (K + 1) * ms K (cantorPrefix w l) :=
    mul_le_mul_of_nonneg_left (hn' l hl) (by positivity)
  change b ≤ ∑' k, (1 / 2 : ℝ) ^ (k + 1) * ms k (cantorPrefix w l)
  linarith

/-- **SUV Theorem 177(b), p. 273, the strong form of p. 273, and (3), p. 274.**  For a `π`-null set
`X` there is a `π`-martingale that strongly wins on all elements of `X`.  `X` need not be
measurable: `π X` is an outer measure. -/
theorem exists_isMartingale_stronglyWins_of_null {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {X : Set CantorSeq} (hX : π X = 0) : ∃ m, IsMartingale π m ∧ ∀ w ∈ X, StronglyWins m w := by
  obtain ⟨ms, hm, H2⟩ := exists_isMartingale_stronglyWins_of_null_seq hX
  obtain ⟨hg, hs⟩ := H2
  refine ⟨fun x => ∑' k, (1 / 2 : ℝ) ^ (k + 1) * ms k x, ?_, ?_⟩
  · exact exists_isMartingale_stronglyWins_of_null_sum ms hm hs
  · exact exists_isMartingale_stronglyWins_of_null_limit ms (fun k x => (hm k).nonneg x) hs hg

/-- **SUV (3), p. 274.**  A set is `π`-null exactly when some `π`-martingale wins on all its
elements. -/
theorem measure_eq_zero_iff_exists_wins {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (X : Set CantorSeq) : π X = 0 ↔ ∃ m, IsMartingale π m ∧ ∀ w ∈ X, Wins m w := by
  constructor
  · intro hX
    obtain ⟨m, hm, hw⟩ := exists_isMartingale_stronglyWins_of_null hX
    exact ⟨m, hm, fun w hwX => (hw w hwX).wins⟩
  · rintro ⟨m, hm, hw⟩
    exact measure_mono_null (fun w hwX => hw w hwX) (measure_wins_eq_zero hm)

/-- **SUV Theorem 178, p. 273.**  For every martingale there is another one strongly winning on all
sequences where the first one wins. -/
theorem exists_stronglyWins_of_wins {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsMartingale π m) :
    ∃ m', IsMartingale π m' ∧ ∀ w, Wins m w → StronglyWins m' w := by
  have h_null : π {w | Wins m w} = 0 := measure_wins_eq_zero hm
  obtain ⟨m', hm', hw⟩ := exists_isMartingale_stronglyWins_of_null h_null
  exact ⟨m', hm', fun w hw_wins => hw w hw_wins⟩

open Classical in
/-- The second construction of Theorem 178, p. 273: `m_c` imitates `m` until the capital reaches `c`
and then stops: the value on `x` is that of `m` on the shortest prefix of `x` where `m` is at least
`c`, or on `x` itself if there is none. -/
noncomputable def stoppedCapital (m : BitString → ℝ) (c : ℝ) (x : BitString) : ℝ :=
  m ((x.inits.find? fun y => decide (c ≤ m y)).getD x)

/-- The stopped capital is fair, for a probability measure: after stopping the capital is constant,
which uses the additivity of the masses as real numbers. -/
theorem IsFairCapital.stoppedCapital {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsFairCapital π m) (c : ℝ) :
    IsFairCapital π (stoppedCapital m c) := by
  constructor
  · intro x
    change 0 ≤ m ((x.inits.find? (fun y => decide (c ≤ m y))).getD x)
    exact hm.nonneg _
  · intro x
    change m ((x.inits.find? (fun y => decide (c ≤ m y))).getD x) * massR π x =
      m (((x ++ [false]).inits.find? (fun y => decide (c ≤ m y))).getD (x ++ [false])) * massR π (x
          ++ [false]) +
      m (((x ++ [true]).inits.find? (fun y => decide (c ≤ m y))).getD (x ++ [true])) * massR π (x ++
          [true])
    set p : BitString → Bool := fun y => decide (c ≤ m y)
    have hp1 : (x ++ [false]).inits = x.inits ++ [x ++ [false]] := by
      rw [List.inits_append]
      simp
    have hp2 : (x ++ [true]).inits = x.inits ++ [x ++ [true]] := by
      rw [List.inits_append]
      simp
    rw [hp1, hp2, List.find?_append, List.find?_append]
    cases h : List.find? p x.inits with
    | none =>
      dsimp [Option.or]
      have hf : Option.getD (List.find? p [x ++ [false]]) (x ++ [false]) = x ++ [false] := by
        cases h2 : List.find? p [x ++ [false]]
        · rfl
        · dsimp [List.find?] at h2
          split at h2
          · injection h2 with eq; rw [eq]; rfl
          · contradiction
      have ht : Option.getD (List.find? p [x ++ [true]]) (x ++ [true]) = x ++ [true] := by
        cases h2 : List.find? p [x ++ [true]]
        · rfl
        · dsimp [List.find?] at h2
          split at h2
          · injection h2 with eq; rw [eq]; rfl
          · contradiction
      rw [hf, ht]
      exact hm.fair x
    | some val =>
      dsimp [Option.or]
      have hmR_add : massR π x = massR π (x ++ [false]) + massR π (x ++ [true]) := by
        dsimp [massR]
        rw [cantorMass_add]
        exact ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
      calc m val * massR π x = m val * (massR π (x ++ [false]) + massR π (x ++ [true])) := by rw
          [hmR_add]
        _ = m val * massR π (x ++ [false]) + m val * massR π (x ++ [true]) := by ring

/-- Once `m` has reached `c` on a prefix, the stopped capital is at least `c` on all extensions. -/
theorem le_stoppedCapital_of_prefix {m : BitString → ℝ} {c : ℝ} {x y : BitString}
    (hx : c ≤ m x) (hxy : x <+: y) : c ≤ stoppedCapital m c y := by
  dsimp [stoppedCapital]
  have H : x ∈ y.inits := (List.mem_inits _ _).2 hxy
  have h_some : (y.inits.find? (fun y => decide (c ≤ m y))).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨x, H, decide_eq_true hx⟩
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp h_some
  rw [hz]
  dsimp [Option.getD]
  have H' := List.find?_some hz
  exact of_decide_eq_true H'

end Kolmogorov.FrequencyGames
