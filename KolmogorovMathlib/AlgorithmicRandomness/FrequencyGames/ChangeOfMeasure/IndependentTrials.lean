/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz

/-!
# Independent Trials

The product measure `independentTrials p` on Cantor space, in which the `i`-th bit is `true` with
probability `p i` independently of the others. We compute the mass of a cylinder, show that the
measure is computable when the sequence `p` is computable (`isComputableMeasure_independentTrials`),
compute the conditional probability of a one (`condOne_independentTrials`), and characterize
Martin-Löf randomness for the measure `firstTrialBiased` in which only the first trial is biased
(`isMartinLofRandom_firstTrialBiased_iff`). This is part of the change-of-measure material in the
chapter on frequency games of the book by Shen, Uspensky and Vereshchagin.
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### Independent trials -/

/-- The measure on `Ω` of independent trials with success probability `p i` in trial `i`. -/
noncomputable def independentTrials (p : ℕ → NNReal) (hp : ∀ i, p i ≤ 1) : Measure CantorSeq :=
  Measure.infinitePi fun i =>
    ProbabilityTheory.bernoulliMeasure true false ⟨p i, (p i).2, NNReal.coe_le_one.mpr (hp i)⟩

instance (p : ℕ → NNReal) (hp : ∀ i, p i ≤ 1) : IsProbabilityMeasure (independentTrials p hp) := by
  dsimp [independentTrials]; infer_instance

/-- The mass of a cylinder under independent trials: the product of the `p i` over the ones of `x`
and of the `1 - p i` over its zeros. -/
theorem massR_independentTrials (p : ℕ → NNReal) (hp : ∀ i, p i ≤ 1) (x : BitString) :
    massR (independentTrials p hp) x =
      ∏ i : Fin x.length, if x[i] then (p i : ℝ) else 1 - (p i : ℝ) := by
  dsimp [massR, cantorMass, independentTrials]
  have h1 : cantorCylinder x = Set.pi ↑(Finset.range x.length)
      (fun i => if h : i < x.length then {x[i]} else Set.univ) := by
    ext w
    simp only [cantorCylinder, IsCantorPrefix, Finset.mem_coe, Finset.mem_range, Set.mem_pi]
    constructor
    · intro h i hi
      have h2 := h i hi
      simp only [hi, dite_eq_left, h2, Set.mem_singleton_iff]
    · intro h i hi
      have h2 := h i hi
      simp only [hi, dite_eq_left, Set.mem_singleton_iff] at h2
      exact h2
  rw [h1, Measure.infinitePi_pi]
  · simp only [ENNReal.toReal_prod]
    rw [← Fin.prod_univ_eq_prod_range]
    apply Fintype.prod_congr
    intro i
    have hi : (i : ℕ) < x.length := i.2
    simp only [hi, dite_eq_left]
    cases x[i]
    · simp [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem]
    · simp
  · intro i hi
    split_ifs
    · exact MeasurableSet.of_discrete
    · exact MeasurableSet.of_discrete

/-- `p` is a computable sequence of computable reals, uniformly. -/
def IsComputableProbSeq (p : ℕ → NNReal) : Prop :=
  ∃ q : ℕ × ℕ → ℚ, Computable q ∧ ∀ i s, |(q (i, s) : ℝ) - (p i : ℝ)| ≤ (2 : ℝ)⁻¹ ^ s

/-- Clamping to the unit interval does not increase distance from a point of that interval. -/
private lemma isComputableMeasure_independentTrials_approx_clamp
    {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    |a - max 0 (min 1 b)| ≤ |a - b| := by
  by_cases hb₀ : b ≤ 0
  · rw [min_eq_right (hb₀.trans zero_le_one), max_eq_left hb₀, sub_zero, abs_of_nonneg ha₀,
      abs_of_nonneg (sub_nonneg.mpr (hb₀.trans ha₀))]
    linarith
  · have hb₀' : 0 ≤ b := le_of_not_ge hb₀
    by_cases hb₁ : b ≤ 1
    · rw [min_eq_right hb₁, max_eq_right hb₀']
    · have hb₁' : 1 ≤ b := le_of_not_ge hb₁
      rw [min_eq_left hb₁', max_eq_right zero_le_one, abs_of_nonpos (sub_nonpos.mpr ha₁),
        abs_of_nonpos (sub_nonpos.mpr (ha₁.trans hb₁'))]
      linarith

/-- Increasing the precision by `n` absorbs the error from multiplying `n` factors. -/
private lemma isComputableMeasure_independentTrials_approx_dyadic (n s : ℕ) :
    (n : ℝ) * (2 : ℝ)⁻¹ ^ (s + 2 + n) ≤ (2 : ℝ)⁻¹ ^ (s + 2) := by
  have hnReal : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  calc
    (n : ℝ) * (2 : ℝ)⁻¹ ^ (s + 2 + n)
        ≤ (2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ (s + 2 + n) := by gcongr
    _ = (2 : ℝ)⁻¹ ^ (s + 2) := by
      rw [pow_add]
      calc
        (2 : ℝ) ^ n * ((2 : ℝ)⁻¹ ^ (s + 2) * (2 : ℝ)⁻¹ ^ n) =
            (2 : ℝ)⁻¹ ^ (s + 2) * ((2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n) := by ring
        _ = (2 : ℝ)⁻¹ ^ (s + 2) := by rw [← mul_pow]; norm_num

/-- Products of factors in the unit interval accumulate at most the sum of the factor errors. -/
private lemma isComputableMeasure_independentTrials_approx_prod_error
    (a b : ℕ → ℝ) (ε : ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) (hab : ∀ i, |a i - b i| ≤ ε) (n : ℕ) :
    |(∏ i ∈ Finset.range n, a i) - ∏ i ∈ Finset.range n, b i| ≤ n * ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb₀ : 0 ≤ ∏ i ∈ Finset.range n, b i :=
      Finset.prod_nonneg fun i _ => (hb i).1
    have hb₁ : (∏ i ∈ Finset.range n, b i) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => (hb i).1) (fun i _ => (hb i).2)
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    calc
      |(∏ i ∈ Finset.range n, a i) * a n - (∏ i ∈ Finset.range n, b i) * b n|
          = |((∏ i ∈ Finset.range n, a i) - ∏ i ∈ Finset.range n, b i) * a n +
              (∏ i ∈ Finset.range n, b i) * (a n - b n)| := by congr 1; ring
      _ ≤ |((∏ i ∈ Finset.range n, a i) - ∏ i ∈ Finset.range n, b i) * a n| +
          |(∏ i ∈ Finset.range n, b i) * (a n - b n)| := abs_add_le _ _
      _ = |(∏ i ∈ Finset.range n, a i) - ∏ i ∈ Finset.range n, b i| * a n +
          (∏ i ∈ Finset.range n, b i) * |a n - b n| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (ha n).1, abs_of_nonneg hb₀]
      _ ≤ |(∏ i ∈ Finset.range n, a i) - ∏ i ∈ Finset.range n, b i| * 1 +
          1 * |a n - b n| :=
            add_le_add (mul_le_mul_of_nonneg_left (ha n).2 (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hb₁ (abs_nonneg _))
      _ = |(∏ i ∈ Finset.range n, a i) - ∏ i ∈ Finset.range n, b i| +
          |a n - b n| := by ring
      _ ≤ n * ε + ε := add_le_add ih (hab n)
      _ = (n + 1 : ℕ) * ε := by push_cast; ring

/-- A rational approximation to the probability of one prescribed bit. -/
private def isComputableMeasure_independentTrials_approx_factor
    (q : ℕ × ℕ → ℚ) (x : BitString) (s i : ℕ) : ℚ :=
  let r := max 0 (min 1 (q (i, s + 2 + x.length)))
  cond (x.getD i false) r (1 - r)

/-- Multiply the clamped rational probabilities at precision `s + 2 + x.length`. -/
private def isComputableMeasure_independentTrials_approx_Q
    (q : ℕ × ℕ → ℚ) (x : BitString) (s : ℕ) : ℚ :=
  (List.range x.length).foldl
    (fun acc i => acc * isComputableMeasure_independentTrials_approx_factor q x s i) 1

/-- The finite product of rational approximations is uniformly computable. -/
private lemma isComputableMeasure_independentTrials_approx_computable
    (q : ℕ × ℕ → ℚ) (hq : Computable q) :
    Computable₂ (isComputableMeasure_independentTrials_approx_Q q) := by
  have hl : Computable (fun z : BitString × ℕ => List.range z.1.length) :=
    Primrec.list_range.to_comp.comp (Primrec.list_length.to_comp.comp Computable.fst)
  have hx : Computable (fun z : (BitString × ℕ) × (ℚ × ℕ) => z.1.1) :=
    Computable.fst.comp Computable.fst
  have hs : Computable (fun z : (BitString × ℕ) × (ℚ × ℕ) => z.1.2) :=
    Computable.snd.comp Computable.fst
  have hi : Computable (fun z : (BitString × ℕ) × (ℚ × ℕ) => z.2.2) :=
    Computable.snd.comp Computable.snd
  have ht : Computable (fun z : (BitString × ℕ) × (ℚ × ℕ) =>
      z.1.2 + 2 + z.1.1.length) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp hs (Computable.const 2))
      (Primrec.list_length.to_comp.comp hx)
  have hr : Computable (fun z : (BitString × ℕ) × (ℚ × ℕ) =>
      max 0 (min 1 (q (z.2.2, z.1.2 + 2 + z.1.1.length)))) :=
    ComputableReals.primrec_ratMax.to_comp.comp (Computable.const 0)
      (ComputableReals.primrec_ratMin.to_comp.comp (Computable.const 1)
        (hq.comp (hi.pair ht)))
  have hbit : Computable (fun z : (BitString × ℕ) × (ℚ × ℕ) =>
      z.1.1.getD z.2.2 false) :=
    Computable₂.comp (f := fun l n => l.getD n false) (Primrec.list_getD false).to_comp hx hi
  have hfac : Computable (fun z : (BitString × ℕ) × (ℚ × ℕ) =>
      isComputableMeasure_independentTrials_approx_factor q z.1.1 z.1.2 z.2.2) :=
    (Computable.cond hbit hr (computable₂_ratSub.comp (Computable.const 1) hr)).of_eq
      fun _ => rfl
  have hstep : Computable₂ (fun (z : BitString × ℕ) (v : ℚ × ℕ) =>
      v.1 * isComputableMeasure_independentTrials_approx_factor q z.1 z.2 v.2) :=
    (computable₂_ratMul.comp (Computable.fst.comp Computable.snd) hfac).to₂
  exact (Computable.list_foldl hl (Computable.const 1) hstep).to₂

/-- Express the computable fold as a finite product for the error estimate. -/
private lemma isComputableMeasure_independentTrials_approx_Q_prod
    (q : ℕ × ℕ → ℚ) (x : BitString) (s : ℕ) :
    isComputableMeasure_independentTrials_approx_Q q x s =
      ∏ i ∈ Finset.range x.length,
        isComputableMeasure_independentTrials_approx_factor q x s i := by
  rw [← List.toFinset_range, List.prod_toFinset _ List.nodup_range,
    List.prod_eq_foldl, List.foldl_map]
  rfl

/-- Step 1 of the proof of `isComputableMeasure_independentTrials`: a computable rational
approximation Q of massR (independentTrials p hp) x to within 2^-(s+2) with 0 <= Q <= 1 -/
private lemma isComputableMeasure_independentTrials_approx {p : ℕ → NNReal} (hp : ∀ i, p i ≤
    1)
    (hc : IsComputableProbSeq p) :
    ∃ Q : BitString → ℕ → ℚ, Computable₂ Q ∧ ∀ x s,
      0 ≤ Q x s ∧ Q x s ≤ 1 ∧
      |(Q x s : ℝ) - massR (independentTrials p hp) x| ≤ (2 : ℝ)⁻¹ ^ (s + 2) := by
  obtain ⟨q, hq, herr⟩ := hc
  refine ⟨isComputableMeasure_independentTrials_approx_Q q,
    isComputableMeasure_independentTrials_approx_computable q hq, ?_⟩
  intro x s
  have hfac : ∀ i, 0 ≤ isComputableMeasure_independentTrials_approx_factor q x s i ∧
      isComputableMeasure_independentTrials_approx_factor q x s i ≤ 1 := by
    intro i
    have hr₀ : (0 : ℚ) ≤ max 0 (min 1 (q (i, s + 2 + x.length))) := le_max_left _ _
    have hr₁ : max 0 (min 1 (q (i, s + 2 + x.length))) ≤ (1 : ℚ) :=
      max_le zero_le_one (min_le_left _ _)
    unfold isComputableMeasure_independentTrials_approx_factor
    cases x.getD i false <;> simp only [Bool.cond_false, Bool.cond_true]
    · exact ⟨sub_nonneg.mpr hr₁, by linarith⟩
    · exact ⟨hr₀, hr₁⟩
  rw [isComputableMeasure_independentTrials_approx_Q_prod]
  refine ⟨Finset.prod_nonneg (fun i _ => (hfac i).1),
    Finset.prod_le_one₀ (fun i _ => (hfac i).1) (fun i _ => (hfac i).2), ?_⟩
  let a : ℕ → ℝ := fun i => isComputableMeasure_independentTrials_approx_factor q x s i
  let b : ℕ → ℝ := fun i => if x.getD i false then (p i : ℝ) else 1 - (p i : ℝ)
  have ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1 := by
    intro i
    dsimp [a]
    exact ⟨by exact_mod_cast (hfac i).1, by exact_mod_cast (hfac i).2⟩
  have hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1 := by
    intro i
    have hp₀ : (0 : ℝ) ≤ p i := (p i).coe_nonneg
    have hp₁ : (p i : ℝ) ≤ 1 := NNReal.coe_le_one.mpr (hp i)
    dsimp [b]
    cases x.getD i false <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact ⟨sub_nonneg.mpr hp₁, by linarith⟩
    · exact ⟨hp₀, hp₁⟩
  have hab : ∀ i, |a i - b i| ≤ (2 : ℝ)⁻¹ ^ (s + 2 + x.length) := by
    intro i
    have hclip := isComputableMeasure_independentTrials_approx_clamp
      (p i).coe_nonneg (NNReal.coe_le_one.mpr (hp i)) (b := (q (i, s + 2 + x.length) : ℝ))
    have hr : |((max 0 (min 1 (q (i, s + 2 + x.length))) : ℚ) : ℝ) - (p i : ℝ)| ≤
        (2 : ℝ)⁻¹ ^ (s + 2 + x.length) := by
      rw [Rat.cast_max, Rat.cast_min, Rat.cast_zero, Rat.cast_one, abs_sub_comm]
      exact hclip.trans (by simpa only [abs_sub_comm] using herr i (s + 2 + x.length))
    dsimp [a, b, isComputableMeasure_independentTrials_approx_factor]
    cases x.getD i false <;> simp only [Bool.cond_false, Bool.cond_true,
      Bool.false_eq_true, ite_false, ite_true, Rat.cast_sub, Rat.cast_one]
    · simpa only [show ∀ r v : ℝ, (1 - r) - (1 - v) = -(r - v) by intros; ring,
        abs_neg] using hr
    · exact hr
  have hmass : massR (independentTrials p hp) x = ∏ i ∈ Finset.range x.length, b i := by
    rw [massR_independentTrials, ← Fin.prod_univ_eq_prod_range]
    apply Fintype.prod_congr
    intro i
    dsimp [b]
    rw [List.getD_eq_getElem x false i.isLt]
  push_cast
  change |(∏ i ∈ Finset.range x.length, a i) - massR (independentTrials p hp) x| ≤ _
  rw [hmass]
  exact (isComputableMeasure_independentTrials_approx_prod_error a b _ ha hb hab _).trans
    (isComputableMeasure_independentTrials_approx_dyadic x.length s)

private lemma ennreal_pair_bounds_of_toReal_abs_le {a b e : ENNReal}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (he : e ≠ ⊤)
    (h : |a.toReal - b.toReal| ≤ e.toReal) : a ≤ b + e ∧ b ≤ a + e := by
  rw [abs_le] at h
  constructor
  · rw [← ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.mpr ⟨hb, he⟩),
      ENNReal.toReal_add hb he]
    linarith
  · rw [← ENNReal.toReal_le_toReal hb (ENNReal.add_ne_top.mpr ⟨ha, he⟩),
      ENNReal.toReal_add ha he]
    linarith

/-- Step 2 of the proof of `isComputableMeasure_independentTrials`: a general rounding
lemma from such Q to IsComputableMeasure for a probability measure. -/
private lemma isComputableMeasure_independentTrials_rounding {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ]
    (Q : BitString → ℕ → ℚ) (hQ_comp : Computable₂ Q)
    (hQ_bound : ∀ x s, 0 ≤ Q x s ∧ Q x s ≤ 1 ∧ |(Q x s : ℝ) - massR μ x| ≤ (2 : ℝ)⁻¹ ^ (s + 2)) :
    IsComputableMeasure μ := by
  let a (x : BitString) (s : ℕ) : ℕ := (ratDyadicFloor (Q x s) (s + 1) + 1) / 2
  have ha_comp : Computable₂ a := by
    have hs : Computable (fun z : BitString × ℕ => z.2 + 1) :=
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)).to_comp
    have hfloor : Computable (fun z : BitString × ℕ =>
        ratDyadicFloor (Q z.1 z.2) (z.2 + 1)) :=
      computable_ratDyadicFloor.comp hQ_comp hs
    have hadd : Computable (fun z : BitString × ℕ =>
        ratDyadicFloor (Q z.1 z.2) (z.2 + 1) + 1) :=
      Primrec.nat_add.to_comp.comp hfloor (Computable.const 1)
    exact (Primrec.nat_div.to_comp.comp hadd (Computable.const 2)).to₂.of_eq fun _ => rfl
  use a, ha_comp
  intro x s
  let A := ratDyadicFloor (Q x s) (s + 1)
  have hq0 : 0 ≤ Q x s := (hQ_bound x s).1
  have hA_bounds : A ≤ 2 * a x s ∧ 2 * a x s ≤ A + 1 := by
    dsimp [a, A]
    have hmod := Nat.mod_lt (ratDyadicFloor (Q x s) (s + 1) + 1) (by omega : 0 < 2)
    have hdivmod := Nat.div_add_mod (ratDyadicFloor (Q x s) (s + 1) + 1) 2
    omega
  have hQ_A_bounds : (A : ℝ) ≤ (Q x s : ℝ) * (2 : ℝ) ^ (s + 1) ∧
      (Q x s : ℝ) * (2 : ℝ) ^ (s + 1) ≤ A + 1 := by
    dsimp [A]
    have heq := ratDyadicFloor_eq_floor (Q x s) (s + 1)
    rw [heq]
    constructor
    · have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (s + 1) := by positivity
      have hm : (0:ℝ) ≤ (Q x s : ℝ) * 2 ^ (s + 1) := mul_nonneg (by exact_mod_cast hq0) hpos
      have hm2 : (0:ℚ) ≤ Q x s * 2 ^ (s + 1) := mul_nonneg hq0 (by positivity)
      have hl := Nat.floor_le hm2
      exact_mod_cast hl
    · have hlt := Nat.lt_floor_add_one ((Q x s) * (2 : ℚ) ^ (s + 1))
      exact_mod_cast hlt.le
  have habs_bound : |((a x s : ℝ) / (2 : ℝ) ^ s) - (Q x s : ℝ)| ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
    have heq : ((a x s : ℝ) / (2 : ℝ) ^ s) - (Q x s : ℝ) =
        ((2 * (a x s : ℝ) : ℝ) - (Q x s : ℝ) * (2 : ℝ) ^ (s + 1)) / (2 : ℝ) ^ (s + 1) := by
      calc
        (a x s : ℝ) / (2 : ℝ) ^ s - (Q x s : ℝ)
          = ((a x s : ℝ) / (2 : ℝ) ^ s) * ((2:ℝ)/2) - (Q x s : ℝ) *
              (((2:ℝ) ^ (s+1)) / ((2:ℝ) ^ (s+1))) := by
            have ht1 : (2:ℝ) / 2 = 1 := by norm_num
            have ht2 : ((2:ℝ)^(s+1)) / ((2:ℝ)^(s+1)) = 1 := by
              have ht2a : (2:ℝ)^(s+1) ≠ 0 := by positivity
              exact div_self ht2a
            rw [ht1, ht2, mul_one, mul_one]
        _ = ((a x s : ℝ) * 2) / ((2 : ℝ) ^ s * 2) - ((Q x s : ℝ) * (2 : ℝ) ^ (s + 1)) / (2 : ℝ) ^
            (s + 1) := by
            have h1 : (a x s : ℝ) / (2 : ℝ) ^ s * (2 / 2) = ((a x s : ℝ) * 2) / ((2 : ℝ) ^ s * 2) :=
                by ring
            have h2 : (Q x s : ℝ) * (2 ^ (s + 1) / 2 ^ (s + 1)) = (Q x s : ℝ) * 2 ^ (s + 1) /
                2 ^ (s + 1) := by ring
            rw [h1, h2]
        _ = (2 * (a x s : ℝ)) / (2 : ℝ) ^ (s + 1) - ((Q x s : ℝ) * (2 : ℝ) ^ (s + 1)) / (2 : ℝ) ^
            (s + 1) := by
            have h1 : (2:ℝ) ^ s * 2 = (2:ℝ) ^ (s+1) := by 
              rw [pow_add, pow_one, mul_comm]
            rw [h1, mul_comm (a x s : ℝ) 2]
        _ = (2 * (a x s : ℝ) - (Q x s : ℝ) * (2 : ℝ) ^ (s + 1)) / (2 : ℝ) ^ (s + 1) := by
            rw [sub_div]
    rw [heq, abs_div, abs_of_pos (pow_pos (by norm_num : (0:ℝ) < 2) _)]
    have h1 : |2 * (a x s : ℝ) - (Q x s : ℝ) * (2 : ℝ) ^ (s + 1)| ≤ 1 := by
      rcases hA_bounds with ⟨hA1, hA2⟩
      rcases hQ_A_bounds with ⟨hQ1, hQ2⟩
      have hA1R : (A : ℝ) ≤ 2 * (a x s : ℝ) := by exact_mod_cast hA1
      have hA2R : 2 * (a x s : ℝ) ≤ (A : ℝ) + 1 := by exact_mod_cast hA2
      rw [abs_le]
      constructor
      · linarith
      · linarith
    calc
      |2 * (a x s : ℝ) - (Q x s : ℝ) * (2 : ℝ) ^ (s + 1)| / (2 : ℝ) ^ (s + 1)
        ≤ 1 / (2 : ℝ) ^ (s + 1) := div_le_div_of_nonneg_right h1 (pow_nonneg (by norm_num) _)
      _ = (2 : ℝ)⁻¹ ^ (s + 1) := by
        rw [inv_pow, one_div]
  
  have h_total_bound : |(dyadicValue (a x s) s).toReal - massR μ x| ≤ (dyadicValue 1 s).toReal := by
    have hd_eq : (dyadicValue (a x s) s).toReal = (a x s : ℝ) / (2 : ℝ) ^ s := by
      unfold dyadicValue
      simp
    rw [hd_eq]
    have h_diff_mass := (hQ_bound x s).2.2
    calc
      |((a x s : ℝ) / (2 : ℝ) ^ s) - massR μ x|
        ≤ |((a x s : ℝ) / (2 : ℝ) ^ s) - (Q x s : ℝ)| + |(Q x s : ℝ) - massR μ x| :=
            abs_sub_le _ _ _
      _ ≤ (2 : ℝ)⁻¹ ^ (s + 1) + (2 : ℝ)⁻¹ ^ (s + 2) := add_le_add habs_bound h_diff_mass
      _ ≤ (dyadicValue 1 s).toReal := by
        suffices hfin : ((2:ℝ)^(s+1))⁻¹ + ((2:ℝ)^(s+2))⁻¹ ≤ ((2:ℝ)^s)⁻¹ by
          unfold dyadicValue
          simpa using hfin
        have ht1 : ((2:ℝ)^(s+1))⁻¹ = (1/2:ℝ)^(s+1) := by
          rw [← inv_pow, one_div]
        have ht2 : ((2:ℝ)^(s+2))⁻¹ = (1/2:ℝ)^(s+2) := by
          rw [← inv_pow, one_div]
        have ht3 : ((2:ℝ)^s)⁻¹ = (1/2:ℝ)^s := by
          rw [← inv_pow, one_div]
        rw [ht1, ht2, ht3]
        have h1 : (1/2:ℝ)^(s+1) = (1/2) * (1/2:ℝ)^s := by 
          rw [pow_add, pow_one, mul_comm]
        have h2 : (1/2:ℝ)^(s+2) = (1/4) * (1/2:ℝ)^s := by 
          have h2a : (s+2) = 2+s := by omega
          rw [h2a, pow_add]
          norm_num
        rw [h1, h2, ← add_mul]
        have h3 : (1/2:ℝ) + 1/4 = 3/4 := by norm_num
        rw [h3]
        have h4 : (3/4:ℝ) ≤ 1 := by norm_num
        have h5 : (3/4:ℝ) * (1/2)^s ≤ 1 * (1/2)^s := mul_le_mul_of_nonneg_right h4 (by positivity)
        rw [one_mul] at h5
        exact h5
        
  have hd_top : dyadicValue (a x s) s ≠ ⊤ := (dyadicValue_lt_top _ _).ne
  have hmass_top : cantorMass μ x ≠ ⊤ := (measure_lt_top _ _).ne
  have he_top : dyadicValue 1 s ≠ ⊤ := (dyadicValue_lt_top _ _).ne
  
  have heq : massR μ x = (cantorMass μ x).toReal := rfl
  rw [heq] at h_total_bound
  
  have h_bound_rw : |(dyadicValue (a x s) s).toReal - (cantorMass μ x).toReal| ≤
      (dyadicValue 1 s).toReal := h_total_bound
  rw [abs_le] at h_bound_rw
  constructor
  · rw [← ENNReal.toReal_le_toReal hd_top (ENNReal.add_ne_top.mpr ⟨hmass_top, he_top⟩),
      ENNReal.toReal_add hmass_top he_top]
    linarith
  · rw [← ENNReal.toReal_le_toReal hmass_top (ENNReal.add_ne_top.mpr ⟨hd_top, he_top⟩),
      ENNReal.toReal_add hd_top he_top]
    linarith

/-- Independent trials with a computable sequence of probabilities form a computable measure. -/
theorem isComputableMeasure_independentTrials {p : ℕ → NNReal} (hp : ∀ i, p i ≤ 1)
    (hc : IsComputableProbSeq p) : IsComputableMeasure (independentTrials p hp) := by
  obtain ⟨Q, hQ_comp, hQ_bound⟩ := isComputableMeasure_independentTrials_approx hp hc
  exact isComputableMeasure_independentTrials_rounding Q hQ_comp hQ_bound

/-- The conditional probability of `1` after `x`. -/
noncomputable def condOne (μ : Measure CantorSeq) (x : BitString) : ℝ :=
  condProb (cantorMass μ) x true

/-- Under independent trials, the conditional probability of `1` after `x` is `p |x|`, provided the
history `x` has positive probability. -/
theorem condOne_independentTrials (p : ℕ → NNReal) (hp : ∀ i, p i ≤ 1) {x : BitString}
    (hx : cantorMass (independentTrials p hp) x ≠ 0) :
    condOne (independentTrials p hp) x = (p x.length : ℝ) := by
  have hm := massR_independentTrials p hp x
  have hm1 := massR_independentTrials p hp (x ++ [true])
  dsimp [condOne, condProb]
  dsimp [massR] at hm hm1
  
  have hlen : (x ++ [true]).length = x.length + 1 := by simp
  have h1 : (∏ i : Fin (x ++ [true]).length, if (x ++ [true])[i] then (p i : ℝ) else 1 - (p i : ℝ))
      =
    ∏ i : Fin (x.length + 1), if (x ++ [true])[i.val]'(by omega) then (p i.val : ℝ) else
      1 - (p i.val : ℝ) := by
    exact Fintype.prod_equiv (finCongr hlen) _ _ (fun i => rfl)
  
  have h_prod : (∏ i : Fin (x ++ [true]).length, if (x ++ [true])[i] then (p i : ℝ) else
    1 - (p i : ℝ)) =
    (∏ i : Fin x.length, if x[i] then (p i : ℝ) else 1 - (p i : ℝ)) * (p x.length : ℝ) := by
    rw [h1, Fin.prod_univ_castSucc]
    congr 1
    · apply Fintype.prod_congr
      intro i
      have h2 : (x ++ [true])[i.castSucc.val]'(by omega) = x[i] := List.getElem_append_left i.isLt
      have hcast : i.castSucc.val = i.val := rfl
      have heq : (if (x ++ [true])[i.castSucc.val]'(by omega) = true then
        (p i.castSucc.val : ℝ) else 1 - (p i.castSucc.val : ℝ)) = 
        if x[i] = true then (p i.val : ℝ) else 1 - (p i.val : ℝ) := by
        rw [h2, hcast]
      exact heq
    · have eq1 : (Fin.last x.length).val = x.length := rfl
      have h3 : (x ++ [true])[(Fin.last x.length).val]'(by omega) = true := by
        simp only [eq1]
        have h3_eq : (x ++ [true])[x.length]'(by simp) = [true][x.length - x.length]'(by simp) :=
            List.getElem_append_right (by omega)
        have h3_sub : x.length - x.length = 0 := by omega
        simp only [h3_sub, List.getElem_singleton] at h3_eq
        exact h3_eq
      have heq : (if (x ++ [true])[(Fin.last x.length).val]'(by omega) = true then
        (p (Fin.last x.length).val : ℝ) else 1 - (p (Fin.last x.length).val : ℝ)) =
        (p x.length : ℝ) := by
        rw [h3, eq1]
        simp
      exact heq
  rw [hm, hm1]
  have h_prod2 : (∏ i : Fin (x ++ [true]).length, if (x ++ [true])[i.val]'(i.isLt) = true then
    (p i.val : ℝ) else 1 - (p i.val : ℝ)) = 
    (∏ i : Fin x.length, if x[i.val]'(i.isLt) = true then (p i.val : ℝ) else 1 - (p i.val : ℝ)) *
        (p x.length : ℝ) := h_prod
  rw [h_prod2]
  
  have hx_real : (cantorMass (independentTrials p hp) x).toReal ≠ 0 := by
    intro hc
    apply hx
    exact (ENNReal.toReal_eq_zero_iff _).mp hc |>.resolve_right (by
      exact MeasureTheory.measure_ne_top _ _)
  
  have hm_neq : (∏ i : Fin x.length, if x[i.val]'(i.isLt) = true then (p i.val : ℝ) else
    1 - (p i.val : ℝ)) ≠ 0 := by
    rw [← hm]
    exact hx_real
    
  have h_mul_div : ((∏ i : Fin x.length, if x[i.val]'(i.isLt) = true then (p i.val : ℝ) else
    1 - (p i.val : ℝ)) * (p x.length : ℝ)) /
    (∏ i : Fin x.length, if x[i.val]'(i.isLt) = true then (p i.val : ℝ) else 1 - (p i.val : ℝ)) =
        (p x.length : ℝ) := by
    rw [mul_comm]
    exact mul_div_cancel_right₀ (p x.length : ℝ) hm_neq
  exact h_mul_div

/-! ### Randomness with respect to two measures -/

/-- The measure of **Example 1, SUV p. 296**: fair trials except the first one, where the success
probability is `2/3`. -/
noncomputable def firstTrialBiased : Measure CantorSeq :=
  independentTrials (fun i => if i = 0 then 2 / 3 else 1 / 2) (by
    intro i; split_ifs <;> norm_num [← NNReal.coe_le_coe])

/-- The probability sequence of `firstTrialBiased` is computable. -/
private lemma isMartinLofRandom_firstTrialBiased_iff_computable :
    IsComputableProbSeq (fun i : ℕ => if i = 0 then (2 / 3 : NNReal) else 1 / 2) := by
  refine ⟨fun a => if a.1 = 0 then (2 / 3 : ℚ) else 1 / 2, ?_, fun i s => ?_⟩
  · have hc : Computable (fun a : ℕ × ℕ => decide (a.1 = 0)) :=
      (Primrec.eq.comp Primrec.fst (Primrec.const 0)).decide.to_comp
    exact (Computable.cond hc (Computable.const (2 / 3 : ℚ)) (Computable.const (1 / 2 : ℚ))).of_eq
      fun a => by by_cases h : a.1 = 0 <;> simp [h]
  · by_cases hi : i = 0
    · subst hi
      simp
    · simp [hi]

/-- The mass of a nonempty cylinder under `firstTrialBiased`. -/
private lemma isMartinLofRandom_firstTrialBiased_iff_massR_cons (b : Bool) (y : BitString) :
    massR firstTrialBiased (b :: y) = (if b then (2 / 3 : ℝ) else 1 / 3) * (2 : ℝ)⁻¹ ^ y.length :=
        by
  unfold firstTrialBiased
  rw [massR_independentTrials]
  erw [Fin.prod_univ_succ]
  congr 1
  · cases b <;> norm_num
  · have : ∀ i : Fin y.length, (if (b :: y)[(i.succ : Fin (y.length + 1))] then
        (((if (i.succ : ℕ) = 0 then (2 / 3 : NNReal) else 1 / 2 : NNReal)) : ℝ)
        else 1 - (((if (i.succ : ℕ) = 0 then (2 / 3 : NNReal) else 1 / 2 : NNReal)) : ℝ))
        = (2 : ℝ)⁻¹ := by
      intro i
      cases h : y[i] <;> simp <;> norm_num
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

/-- Cylinder masses of `firstTrialBiased` and of the uniform measure agree up to the factors
`4/3` and `3/2`. -/
private lemma isMartinLofRandom_firstTrialBiased_iff_massR_bounds (x : BitString) :
    massR firstTrialBiased x ≤ 4 / 3 * massR uniformMeasure x ∧
      massR uniformMeasure x ≤ 3 / 2 * massR firstTrialBiased x := by
  rw [massR_uniformMeasure]
  cases x with
  | nil =>
    have : massR firstTrialBiased [] = 1 := by
      unfold firstTrialBiased
      simp [massR_independentTrials]
    rw [this]; norm_num
  | cons b y =>
    rw [isMartinLofRandom_firstTrialBiased_iff_massR_cons, List.length_cons, pow_succ]
    have hp : 0 < (2 : ℝ)⁻¹ ^ y.length := by positivity
    generalize (2 : ℝ)⁻¹ ^ y.length = t at hp ⊢
    cases b <;> norm_num <;> constructor <;> linarith

/-- Step 4 of the proof of `isMartinLofRandom_firstTrialBiased_iff`: if `w` is
Martin-Löf random for `μ` and `μ(w↾n) ≤ C · μ'(w↾n)` for all `n`, then `w` is Martin-Löf random for
`μ'` (bounded a priori deficiency criterion in both directions). -/
private theorem isMartinLofRandom_firstTrialBiased_iff_transfer {μ μ' : Measure CantorSeq}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hμ : IsComputableMeasure μ)
    (hμ' : IsComputableMeasure μ') {w : CantorSeq} (hw : IsMartinLofRandom μ w) (C : ℝ)
    (hC : ∀ n, cantorMass μ (cantorPrefix w n) ≤
      ENNReal.ofReal C * cantorMass μ' (cantorPrefix w n)) :
    IsMartinLofRandom μ' w := by
  obtain ⟨c, hc⟩ := boundedAPrioriDeficiency_of_isMartinLofRandom hμ hw
  refine isMartinLofRandom_of_boundedAPrioriDeficiency hμ' ⟨c + ⌈C⌉₊, fun n => ?_⟩
  have hCle : ENNReal.ofReal C ≤ (2 : ℝ≥0∞) ^ ⌈C⌉₊ :=
    calc ENNReal.ofReal C ≤ ENNReal.ofReal (⌈C⌉₊ : ℝ) := ENNReal.ofReal_le_ofReal (Nat.le_ceil C)
      _ = (⌈C⌉₊ : ℝ≥0∞) := ENNReal.ofReal_natCast _
      _ ≤ (2 : ℝ≥0∞) ^ ⌈C⌉₊ := by exact_mod_cast (Nat.lt_two_pow_self (n := ⌈C⌉₊)).le
  calc universalContinuousSemimeasure (cantorPrefix w n)
      ≤ (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n) := hc n
    _ ≤ (2 : ℝ≥0∞) ^ c * (ENNReal.ofReal C * cantorMass μ' (cantorPrefix w n)) := by
        gcongr
        exact hC n
    _ ≤ (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞) ^ ⌈C⌉₊ * cantorMass μ' (cantorPrefix w n)) := by
        gcongr
    _ = (2 : ℝ≥0∞) ^ (c + ⌈C⌉₊) * cantorMass μ' (cantorPrefix w n) := by
        rw [pow_add]; ring

/-- **SUV Example 1, p. 297, and Problem 274.**  The same sequences are Martin-Löf random for the
uniform measure and for `firstTrialBiased`.  Problem 274 asks for the proof through the complexity
criterion. -/
theorem isMartinLofRandom_firstTrialBiased_iff (w : CantorSeq) :
    IsMartinLofRandom firstTrialBiased w ↔ IsMartinLofRandom uniformMeasure w := by
  have : IsProbabilityMeasure firstTrialBiased := by unfold firstTrialBiased; infer_instance
  have hcomp : IsComputableMeasure firstTrialBiased :=
    isComputableMeasure_independentTrials _ isMartinLofRandom_firstTrialBiased_iff_computable
  have hfin (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (x : BitString) :
      cantorMass μ x = ENNReal.ofReal (massR μ x) :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hle : ∀ x : BitString,
      cantorMass firstTrialBiased x ≤ ENNReal.ofReal (4 / 3) * cantorMass uniformMeasure x ∧
      cantorMass uniformMeasure x ≤ ENNReal.ofReal (3 / 2) * cantorMass firstTrialBiased x := by
    intro x
    obtain ⟨h1, h2⟩ := isMartinLofRandom_firstTrialBiased_iff_massR_bounds x
    rw [hfin firstTrialBiased x, hfin uniformMeasure x, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ⟨ENNReal.ofReal_le_ofReal h1, ENNReal.ofReal_le_ofReal h2⟩
  constructor
  · intro hw
    exact isMartinLofRandom_firstTrialBiased_iff_transfer hcomp isComputableMeasure_uniform
      hw (4 / 3) fun n => (hle _).1
  · intro hw
    exact isMartinLofRandom_firstTrialBiased_iff_transfer isComputableMeasure_uniform hcomp
      hw (3 / 2) fun n => (hle _).2

end Kolmogorov.FrequencyGames
