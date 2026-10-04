import KolmogorovMathlib.AlgorithmicRandomness.EffectiveNull
import KolmogorovMathlib.AlgorithmicRandomness.Measure
import Mathlib.Basic.Real.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

/-!
# Strong Law of Large Numbers (Non-effective)

This module states and proves the non-effective strong law of large numbers
(SUV Theorem 27), which serves as the foundation for SUV Chapter 3.2.

Theorem 27 is the *general* Bernoulli statement: for parameters `p, q` with
`p + q = 1`, the set `A_p` of sequences whose limit frequency of ones equals `p`
has Bernoulli-`p` measure `1`. The source proves the uniform case `p = 1/2` by
explicit calculation and leaves general `p` as Problem 67; we prove the general
theorem `strongLaw_bernoulli` and derive `strongLaw_uniform` from it.

This is a genuinely measure-theoretic (`= 1`) statement; the *effective* version
(Theorem 32, with an explicit effective tail cover) belongs to M4 and must not be
conflated with this one.
-/

namespace Kolmogorov

open MeasureTheory ProbabilityTheory Filter Topology Finset

/-- The frequency of 1s (true) in the first `n` bits of a sequence, i.e.
`(ω₀ + … + ω_{n-1}) / n` in SUV's notation. -/
def freqOne (w : CantorSeq) (n : ℕ) : ℚ :=
  (cantorPrefix w n).count true / n

/-- The real-valued indicator of a bit: `1` for `true` and `0` for `false`. -/
def bitVal (b : Bool) : ℝ := if b then 1 else 0

/-- The numerical value of a bit, as a function `Bool → ℝ`, is measurable. -/
lemma measurable_bitVal : Measurable bitVal := measurable_from_top

/-- The partial sum of the coordinate indicators counts the ones in the prefix. -/
lemma sum_bitVal_eq_count (w : CantorSeq) (n : ℕ) :
    ∑ i ∈ range n, bitVal (w i) = ((cantorPrefix w n).count true : ℝ) := by
  induction n with
  | zero => simp [cantorPrefix]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, cantorPrefix_succ, List.count_append]
    cases w n <;> simp [bitVal]

/-- `freqOne` is the Cesàro average of the coordinate indicators. -/
lemma freqOne_eq (w : CantorSeq) (n : ℕ) :
    (freqOne w n : ℝ) = (∑ i ∈ range n, bitVal (w i)) / n := by
  rw [sum_bitVal_eq_count]
  simp [freqOne]

instance instIsProbabilityMeasureBernoulliMeasure (p : NNReal) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure p hp) := by
  unfold bernoulliMeasure; infer_instance

/-- The coordinate indicators are (fully, hence pairwise) independent under the
Bernoulli product measure. -/
lemma bernoulli_iIndepFun (p : NNReal) (hp : p ≤ 1) :
    iIndepFun (fun (i : ℕ) (w : CantorSeq) => bitVal (w i)) (bernoulliMeasure p hp) :=
  iIndepFun_infinitePi (X := fun _ : ℕ => bitVal) (fun _ => measurable_bitVal)

/-- Every coordinate indicator pushes the Bernoulli measure forward to the same law. -/
lemma bernoulli_map_coord (p : NNReal) (hp : p ≤ 1) (i : ℕ) :
    (bernoulliMeasure p hp).map (fun w : CantorSeq => bitVal (w i))
      = (ProbabilityTheory.bernoulliMeasure true false
          ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩).map bitVal := by
  have hmp := measurePreserving_eval_infinitePi
    (fun _ : ℕ => ProbabilityTheory.bernoulliMeasure true false
      ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩) i
  rw [show (fun w : CantorSeq => bitVal (w i)) = bitVal ∘ (Function.eval i) from rfl,
    ← Measure.map_map measurable_bitVal (measurable_pi_apply i)]
  unfold bernoulliMeasure
  rw [show (Measure.map (Function.eval i) (Measure.infinitePi
      (fun _ : ℕ => ProbabilityTheory.bernoulliMeasure true false
        ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩)))
      = ProbabilityTheory.bernoulliMeasure true false
        ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩ from hmp.map_eq]

/-- The coordinate indicators are identically distributed. -/
lemma bernoulli_identDistrib (p : NNReal) (hp : p ≤ 1) (i : ℕ) :
    IdentDistrib (fun w : CantorSeq => bitVal (w i)) (fun w : CantorSeq => bitVal (w 0))
      (bernoulliMeasure p hp) (bernoulliMeasure p hp) :=
  { aemeasurable_fst := (measurable_bitVal.comp (measurable_pi_apply i)).aemeasurable
    aemeasurable_snd := (measurable_bitVal.comp (measurable_pi_apply 0)).aemeasurable
    map_eq := by rw [bernoulli_map_coord, bernoulli_map_coord] }

/-- The first coordinate of a Cantor sequence is integrable for every Bernoulli measure, being
a bounded measurable function on a probability space. -/
lemma bernoulli_integrable_coord (p : NNReal) (hp : p ≤ 1) :
    Integrable (fun w : CantorSeq => bitVal (w 0)) (bernoulliMeasure p hp) := by
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_bitVal.comp (measurable_pi_apply 0)).aestronglyMeasurable
    (ae_of_all _ fun w => ?_)
  simp only [bitVal]
  split <;> norm_num

/-- The expectation of a coordinate indicator is `p`. -/
lemma bernoulli_integral_coord (p : NNReal) (hp : p ≤ 1) :
    ∫ w, bitVal (w 0) ∂(bernoulliMeasure p hp) = (p : ℝ) := by
  have h : ∫ w, bitVal (w 0) ∂(bernoulliMeasure p hp)
      = ∫ b, bitVal b ∂((bernoulliMeasure p hp).map (fun w : CantorSeq => w 0)) :=
    (integral_map (measurable_pi_apply 0).aemeasurable
      measurable_bitVal.aestronglyMeasurable).symm
  rw [h]
  have hmp := measurePreserving_eval_infinitePi
    (fun _ : ℕ => ProbabilityTheory.bernoulliMeasure true false
      ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩) 0
  unfold bernoulliMeasure
  rw [show (Measure.map (fun w : CantorSeq => w 0) (Measure.infinitePi
      (fun _ : ℕ => ProbabilityTheory.bernoulliMeasure true false
        ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩)))
      = ProbabilityTheory.bernoulliMeasure true false
        ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩ from hmp.map_eq,
    ProbabilityTheory.integral_bernoulliMeasure]
  simp [bitVal]

/-- SUV **Theorem 27** (classical, general Bernoulli case): with respect to the
Bernoulli measure with parameter `p` (probability of a one), the set of sequences
whose limit frequency of ones equals `p` has measure `1`. -/
theorem strongLaw_bernoulli (p : NNReal) (hp : p ≤ 1) :
    bernoulliMeasure p hp
      {w : CantorSeq | Tendsto (fun n => (freqOne w n : ℝ)) atTop (𝓝 (p : ℝ))} = 1 := by
  have hae := strong_law_ae_real (μ := bernoulliMeasure p hp)
    (fun (i : ℕ) (w : CantorSeq) => bitVal (w i))
    (bernoulli_integrable_coord p hp)
    (fun i j hij => (bernoulli_iIndepFun p hp).indepFun hij)
    (bernoulli_identDistrib p hp)
  rw [bernoulli_integral_coord p hp] at hae
  have hsub :
      {w : CantorSeq | Tendsto (fun n => (freqOne w n : ℝ)) atTop (𝓝 (p : ℝ))}
        =ᵐ[bernoulliMeasure p hp] (Set.univ : Set CantorSeq) := by
    change ∀ᵐ w ∂bernoulliMeasure p hp,
      (Tendsto (fun n => (freqOne w n : ℝ)) atTop (𝓝 (p : ℝ)) : Prop) = True
    filter_upwards [hae] with w hw
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      simpa only [freqOne_eq] using hw
  rw [measure_congr hsub, measure_univ]

/-- SUV Theorem 27, uniform case `p = 1/2`: the uniform-measure special case of
`strongLaw_bernoulli`. -/
theorem strongLaw_uniform :
    uniformMeasure
      {w : CantorSeq | Tendsto (fun n => (freqOne w n : ℝ)) atTop (𝓝 (1 / 2))} = 1 := by
  have h := strongLaw_bernoulli (1 / 2) (by norm_num)
  simpa [uniformMeasure] using h

end Kolmogorov
