import KolmogorovMathlib.AlgorithmicRandomness.EffectiveReal
import KolmogorovMathlib.AlgorithmicRandomness.Measure
import Mathlib.Data.ENNReal.Inv

/-!
# Computable measures on Cantor space

A measure is *computable* (`IsComputableMeasure`) when the masses of the cylinders are
uniformly computable reals: one computable family of dyadic approximations whose stage `s` is
accurate to `2 ^ (-s)` on both sides.  `isComputableMeasure_of_dyadicFloorApprox` shows an
approximation from below is enough, and `IsComputableMeasure.isComputableENNReal_mass` and
`IsComputableMeasure.isLowerSemicomputable_mass` are the two forms in which the definition is
used later.

The masses of the standard measures are computed here — `cantorMass_bernoulliMeasure`,
`cantorMass_uniformMeasure` — and `isComputableMeasure_uniform` shows the uniform measure is
computable, through the explicit approximation `uniformApprox` of `2 ^ (-|x|)`.

Martin-Löf tests, in `MartinLof`, are taken with respect to a measure that is computable in
this sense.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- A measure `μ` on Cantor space is computable if the masses of all cylinders
are uniformly computable reals: there is one computable family of dyadic
approximations, the `s`-th accurate to within `2^{-s}` on both sides.  This is
the uniform form of `IsComputableENNReal` and matches the source definition
("measures of all intervals are computable reals, with one approximation
algorithm for all of them").

The historically first rendering of this notion, `IsFloorComputableMeasure`
(now in `KolmogorovCounterexamples/FloorComputableMeasure.lean`), anchored the approximant
*below* the mass on the same dyadic grid as the error, which silently forces a
computable floor selector `⌊2^s ⬝ μ(Ω_x)⌋` and is strictly stronger:
`not_forall_exists_isFloorComputableMeasure_of_exact` refutes the representation
theorem 77(b) for it. -/
def IsComputableMeasure (μ : Measure CantorSeq) : Prop :=
  ∃ a : BitString → ℕ → ℕ, Computable₂ a ∧ ∀ x s,
    dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s

-- The floor-selector strengthening `IsFloorComputableMeasure` and its refutation
-- live in `KolmogorovCounterexamples/FloorComputableMeasure.lean`.

/-- A measure whose cylinder masses admit a computable dyadic approximation from
*below*, accurate to `2^{-s}`, is computable. -/
lemma isComputableMeasure_of_dyadicFloorApprox {μ : Measure CantorSeq}
    {a : BitString → ℕ → ℕ} (hcomp : Computable₂ a)
    (hbound : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s) :
    IsComputableMeasure μ :=
  ⟨a, hcomp, fun x s => ⟨le_add_right (hbound x s).1, (hbound x s).2⟩⟩

/-- Each cylinder mass of a computable measure is a computable extended nonnegative real. -/
lemma IsComputableMeasure.isComputableENNReal_mass {μ : Measure CantorSeq}
    (h : IsComputableMeasure μ) (x : BitString) :
    IsComputableENNReal (cantorMass μ x) := by
  rcases h with ⟨a, hcomp, hbound⟩
  use fun s => a x s
  constructor
  · intro s
    exact ⟨(hbound x s).2, (hbound x s).1⟩
  · exact @Computable.comp ℕ (BitString × ℕ) ℕ _ _ _
      (fun p => a p.1 p.2) (fun s => (x, s)) hcomp
      (Computable.pair (Computable.const x) Computable.id)

/-- Each cylinder mass of a computable measure is lower semicomputable. -/
lemma IsComputableMeasure.isLowerSemicomputable_mass {μ : Measure CantorSeq}
    (h : IsComputableMeasure μ) (x : BitString) :
    IsLowerSemicomputableENNReal (cantorMass μ x) := by
  apply isLowerSemicomputableENNReal_of_isComputableENNReal
  apply h.isComputableENNReal_mass x

/-- A cylinder is the product set constraining the first `|x|` coordinates to the bits of `x`
and leaving the remaining coordinates free. -/
lemma cantorCylinder_eq_pi_dite (x : BitString) :
    cantorCylinder x = Set.pi ↑(Finset.range x.length) (fun i =>
      if hi : i < x.length then {x[i]'hi} else Set.univ) := by
  ext w
  simp only [cantorCylinder, Set.mem_setOf_eq, IsCantorPrefix, Set.mem_pi, Finset.mem_range,
    Finset.mem_coe]
  constructor
  · intro h i hi
    simp only [hi, dite_true, Set.mem_singleton_iff]
    exact h i hi
  · intro h i hi
    have h1 := h i hi
    simp only [hi, dite_true, Set.mem_singleton_iff] at h1
    exact h1

/-- The Bernoulli measure of a cylinder is the product over its positions of `p` for a one bit
and `1 - p` for a zero bit. -/
lemma cantorMass_bernoulliMeasure (p : NNReal) (hp : p ≤ 1) (x : BitString) :
    cantorMass (bernoulliMeasure p hp) x =
      ∏ i < x.length, (if hi : i < x.length then
        if x[i]'hi then (p : ℝ≥0∞) else 1 - (p : ℝ≥0∞) else 0) := by
  unfold cantorMass bernoulliMeasure
  rw [cantorCylinder_eq_pi_dite]
  have hpi := Measure.infinitePi_pi (fun (i : ℕ) => PMF.toMeasure (PMF.bernoulli p hp))
    (t := fun i => if hi : i < x.length then {x[i]'hi} else Set.univ)
    (s := Finset.range x.length) (by
      intro i hi
      dsimp only
      split_ifs
      · exact measurableSet_singleton _
      · exact MeasurableSet.univ )
  rw [hpi]
  have h_range : Finset.range x.length = Finset.Iio x.length := by ext; simp
  rw [h_range]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.mem_Iio] at hi
  have hi' : i < x.length := hi
  simp only [hi', dite_true]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [PMF.bernoulli_apply hp]
  cases hx : x[i]'hi'
  · simp only [cond_false, ENNReal.coe_sub, ENNReal.coe_one]
    rfl
  · simp only [cond_true]
    rfl

/-- The uniform measure of the cylinder of `x` is `2^{-|x|}`. -/
lemma cantorMass_uniformMeasure (x : BitString) :
    cantorMass uniformMeasure x = (2 : ℝ≥0∞)⁻¹ ^ x.length := by
  unfold uniformMeasure
  rw [cantorMass_bernoulliMeasure (1 / 2 : NNReal) (by norm_num) x]
  have h_prob : ∀ b : Bool, (if b then ((1 / 2 : NNReal) : ℝ≥0∞)
      else (1 : ℝ≥0∞) - ((1 / 2 : NNReal) : ℝ≥0∞)) = (2 : ℝ≥0∞)⁻¹ := by
    intro b
    have h1 : ((1 / 2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by
      have : ((1 / 2 : NNReal) : ℝ≥0∞) = (1 : ℝ≥0∞) / (2 : ℝ≥0∞) := ENNReal.coe_div (by norm_num)
      rw [this, div_eq_mul_inv, one_mul]
    cases b
    · simp only [h1]
      have h_add : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := by
        calc
          (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ * 2 := by ring
          _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
      rw [← h_add]
      exact ENNReal.add_sub_cancel_right (by norm_num)
    · simp only [ite_true, h1]
  have h_prod : (∏ i ∈ Finset.Iio (List.length x), if hi : i < List.length x then
      if x[i] = true then ↑(1 / 2 : NNReal) else (1 : ℝ≥0∞) - ↑(1 / 2 : NNReal) else 0) =
      ∏ i ∈ Finset.Iio (List.length x), (2 : ℝ≥0∞)⁻¹ := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_Iio] at hi
    simp only [hi, dite_true]
    exact h_prob (x[i]'hi)
  rw [h_prod]
  rw [Finset.prod_const]
  simp

/-- The stage-`s` dyadic numerator approximating the uniform mass `2^{-|x|}` of the cylinder
of `x`. -/
def uniformApprox (x : BitString) (s : ℕ) : ℕ :=
  if x.length ≤ s then 2 ^ (s - x.length) else 0

/-- The dyadic approximation of the uniform cylinder masses is computable in the string and the
stage. -/
lemma uniformApprox_computable :
    Computable₂ uniformApprox := by
  have h_len : Primrec (fun (p : BitString × ℕ) => p.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have h_s : Primrec (fun (p : BitString × ℕ) => p.2) := Primrec.snd
  have h_le : PrimrecPred (fun (p : BitString × ℕ) => p.1.length ≤ p.2) :=
    Primrec.nat_le.comp h_len h_s
  have h_sub : Primrec (fun (p : BitString × ℕ) => p.2 - p.1.length) :=
    Primrec.nat_sub.comp h_s h_len
  have h_pow : Primrec (fun (p : BitString × ℕ) => 2 ^ (p.2 - p.1.length)) :=
    primrec_two_pow_aux.comp h_sub
  have h_zero : Primrec (fun (p : BitString × ℕ) => 0) := Primrec.const 0
  have h_ite : Primrec (fun (p : BitString × ℕ) =>
      if p.1.length ≤ p.2 then 2 ^ (p.2 - p.1.length) else 0) :=
    Primrec.ite h_le h_pow h_zero
  exact h_ite.to_comp

/-- The dyadic approximation never exceeds the uniform mass of the cylinder. -/
lemma uniformApprox_le_mass (x : BitString) (s : ℕ) :
    dyadicValue (uniformApprox x s) s ≤ cantorMass uniformMeasure x := by
  unfold uniformApprox
  split_ifs with h
  · rw [dyadicValue_two_pow_sub h]
    rw [cantorMass_uniformMeasure]
  · simp [dyadicValue]

/-- The dyadic approximation underestimates the uniform cylinder mass by at most `2^{-s}`. -/
lemma mass_le_uniformApprox_add (x : BitString) (s : ℕ) :
    cantorMass uniformMeasure x ≤ dyadicValue (uniformApprox x s) s + dyadicValue 1 s := by
  unfold uniformApprox
  split_ifs with h
  · rw [dyadicValue_two_pow_sub h]
    rw [cantorMass_uniformMeasure]
    exact le_add_right (le_refl _)
  · rw [cantorMass_uniformMeasure, dyadicValue_one_eq_inv_two_pow' s]
    have h_zero : dyadicValue 0 s = 0 := by simp [dyadicValue]
    rw [h_zero, zero_add]
    push_neg at h
    have h_eq : (2 : ℝ≥0∞)⁻¹ ^ x.length = (2 : ℝ≥0∞)⁻¹ ^ s * (2 : ℝ≥0∞)⁻¹ ^ (x.length - s) := by
      rw [← pow_add]
      congr 1
      exact Nat.add_sub_of_le (le_of_lt h) |>.symm
    rw [h_eq]
    have h_le_one : (2 : ℝ≥0∞)⁻¹ ^ (x.length - s) ≤ 1 := by
      have h1 : (2 : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (by norm_num)
      have h2 := pow_le_pow_left' h1 (x.length - s)
      simp only [one_pow] at h2
      exact h2
    calc
      (2 : ℝ≥0∞)⁻¹ ^ s * (2 : ℝ≥0∞)⁻¹ ^ (x.length - s) ≤ (2 : ℝ≥0∞)⁻¹ ^ s * 1 := by gcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ s := mul_one _

/-- The uniform measure on Cantor space is a computable measure. -/
lemma isComputableMeasure_uniform :
    IsComputableMeasure uniformMeasure :=
  isComputableMeasure_of_dyadicFloorApprox uniformApprox_computable
    (fun x s => ⟨uniformApprox_le_mass x s, mass_le_uniformApprox_add x s⟩)

end Kolmogorov
