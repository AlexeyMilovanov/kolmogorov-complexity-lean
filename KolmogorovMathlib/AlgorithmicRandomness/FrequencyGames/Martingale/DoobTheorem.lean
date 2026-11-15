/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Martingale.Martingales

/-!
# Doob's martingale convergence theorem

This module formalizes Doob's theorem on the convergence of martingales on the Cantor space,
following the book by Shen, Uspensky and Vereshchagin.  The main declarations are:

* `exists_martingale_of_integral_bound`: a martingale can be boosted by a function `f` with
  `∫_1^∞ f(t)/t² dt ≤ 1` (SUV p. 273, after Theorem 178);
* `exists_martingale_wins_of_oscillation` and `measure_not_hasFiniteLimit_eq_zero`: a martingale
  has a finite limit almost surely (SUV Theorem 179, the "buy low, sell high" strategy);
* `ae_exists_tendsto_condSecond`: conditional probabilities converge almost surely (SUV p. 275);
* `exists_forall_prefix_le_one`: for every martingale there is a sequence on which it stays
  bounded by `1` on all prefixes, so it does not win (SUV Theorem 180).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

open Set in
private lemma exists_martingale_of_integral_bound_weights_aux_real (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => 1 / s ^ 2) (Ioi t) ∧ ∫ s in Ioi t, 1 / s ^ 2 = 1 / t := by
  have hI := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) ht
  have hR := integral_Ioi_rpow_of_lt (a := -2) (by norm_num) ht
  have hcongr : ∀ s ∈ Ioi t, s ^ (-2 : ℝ) = 1 / s ^ 2 := by
    intro s hs
    have hs0 : 0 < s := ht.trans hs
    rw [Real.rpow_neg hs0.le, Real.rpow_two, one_div]
  refine ⟨(integrableOn_congr_fun hcongr measurableSet_Ioi).1 hI, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr, hR]
  norm_num
  rw [Real.rpow_neg_one]

open Set in
private lemma exists_martingale_of_integral_bound_weights_aux_lint (t : ℝ) (ht : 0 < t) :
    ∫⁻ s in Ioi t, ENNReal.ofReal (1 / s ^ 2) = ENNReal.ofReal (1 / t) := by
  obtain ⟨hI, hR⟩ := exists_martingale_of_integral_bound_weights_aux_real t ht
  rw [← hR, ofReal_integral_eq_lintegral_ofReal hI]
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have : 0 < s := ht.trans hs
  positivity

open Set in
/-- Step 1 of the proof of `exists_martingale_of_integral_bound`: the weight measure.
With `μ` the Stieltjes measure of `t ↦ f (max t 1)` (continuous and monotone on `ℝ`), let `ρ` be
the measure `(1/t) dμ(t)` on `(1, ∞)`. Then `ρ` is finite,
`ρ(ℝ) = ∫_1^∞ f(t)/t² dt - f(1) ≤ 1 - f(1)` (Tonelli: `1/t = ∫_t^∞ s⁻² ds`, and
`μ((1,s)) = f(s) - f(1)` by continuity), and for `c ≥ 1`,
`∫_{(1,c]} t dρ = μ((1,c]) = f(c) - f(1)`. -/
private lemma exists_martingale_of_integral_bound_weights {f : ℝ → ℝ}
    (hfmono : MonotoneOn f (Set.Ici 1))
    (hfcont : ContinuousOn f (Set.Ici 1))
    (hfint : IntegrableOn (fun t => f t / t ^ 2) (Set.Ioi 1))
    (hfle : ∫ t in Set.Ioi (1 : ℝ), f t / t ^ 2 ≤ 1) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ (ρ Set.univ).toReal ≤ 1 - f 1 ∧
      ∀ c : ℝ, 1 ≤ c → f c - f 1 ≤ ∫ t in Set.Ioc 1 c, t ∂ρ := by
  set g : ℝ → ℝ := fun t => f (max t 1) with hg
  have hg_mono : Monotone g := fun a b hab =>
    hfmono (mem_Ici.2 (le_max_right a 1)) (mem_Ici.2 (le_max_right b 1)) (max_le_max hab le_rfl)
  have hg_cont : Continuous g :=
    hfcont.comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 1)
  let F : StieltjesFunction ℝ := ⟨g, hg_mono, fun x => hg_cont.continuousWithinAt⟩
  set μ : Measure ℝ := F.measure with hμ
  have hμIoc : ∀ a b, μ (Ioc a b) = ENNReal.ofReal (g b - g a) := fun a b => F.measure_Ioc a b
  have hgf : ∀ t, 1 ≤ t → g t = f t := fun t ht => by simp [hg, max_eq_left ht]
  have hdens : Measurable (fun t : ℝ => ENNReal.ofReal (1 / t)) := by fun_prop
  set ρ : Measure ℝ := (μ.restrict (Ioi 1)).withDensity (fun t => ENNReal.ofReal (1 / t)) with hρ
  have hρuniv : ρ univ = ∫⁻ t in Ioi 1, ENNReal.ofReal (1 / t) ∂μ := by
    rw [hρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  -- integrability facts
  have hI1 := (exists_martingale_of_integral_bound_weights_aux_real 1 one_pos).1
  have hint2 : IntegrableOn (fun s => (f s - f 1) / s ^ 2) (Ioi 1) := by
    have := hfint.sub (hI1.const_mul (f 1))
    refine this.congr_fun (fun s hs => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have hnn2 : ∀ s ∈ Ioi (1 : ℝ), 0 ≤ (f s - f 1) / s ^ 2 := by
    intro s hs
    have := hfmono (mem_Ici.2 le_rfl) (mem_Ici.2 (le_of_lt hs)) (le_of_lt hs)
    have : 0 ≤ f s - f 1 := by linarith
    positivity
  have hval : ∫ s in Ioi (1 : ℝ), (f s - f 1) / s ^ 2 = (∫ s in Ioi (1 : ℝ), f s / s ^ 2) - f 1 :=
      by
    have h1 : ∫ s in Ioi (1 : ℝ), (f s - f 1) / s ^ 2 =
        ∫ s in Ioi (1 : ℝ), (f s / s ^ 2 - f 1 * (1 / s ^ 2)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      ring
    rw [h1, integral_sub hfint (hI1.const_mul (f 1)), integral_const_mul,
      (exists_martingale_of_integral_bound_weights_aux_real 1 one_pos).2]
    simp
  -- Tonelli
  have hmass : ρ univ ≤ ENNReal.ofReal ((∫ s in Ioi (1 : ℝ), f s / s ^ 2) - f 1) := by
    rw [hρuniv, ← hval, ofReal_integral_eq_lintegral_ofReal hint2
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hnn2))]
    let S : Set (ℝ × ℝ) := {p | 1 < p.1} ∩ {p | p.1 < p.2}
    have hS : MeasurableSet S :=
      (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_snd)
    let F2 : ℝ → ℝ → ℝ≥0∞ := fun t s => S.indicator (fun p => ENNReal.ofReal (1 / p.2 ^ 2)) (t, s)
    have hF2 : Measurable (Function.uncurry F2) := by
      have : Function.uncurry F2 = S.indicator (fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
        funext p; rfl
      rw [this]
      exact Measurable.indicator (by fun_prop) hS
    have hswap := lintegral_lintegral_swap (μ := μ) (ν := volume) hF2.aemeasurable
    have hL : ∀ t, ∫⁻ s, F2 t s = (Ioi 1).indicator (fun t => ENNReal.ofReal (1 / t)) t := by
      intro t
      by_cases ht : 1 < t
      · have : (fun s => F2 t s) = (Ioi t).indicator (fun s => ENNReal.ofReal (1 / s ^ 2)) := by
          funext s
          simp only [F2, S, Set.indicator, mem_inter_iff, Set.mem_ofPred_eq, mem_Ioi]
          simp [ht]
        rw [this, lintegral_indicator measurableSet_Ioi,
          exists_martingale_of_integral_bound_weights_aux_lint t (by linarith)]
        simp [ht]
      · have : (fun s => F2 t s) = fun _ => 0 := by
          funext s
          simp [F2, S, Set.indicator, ht]
        rw [this]
        simp [ht]
    have hR : ∀ s, ∫⁻ t, F2 t s ∂μ =
        (Ioi 1).indicator (fun s => ENNReal.ofReal (1 / s ^ 2) * μ (Ioo 1 s)) s := by
      intro s
      by_cases hs : 1 < s
      · have : (fun t => F2 t s) =
            (Ioo 1 s).indicator (fun _ => ENNReal.ofReal (1 / s ^ 2)) := by
          funext t
          simp only [F2, S, Set.indicator, mem_inter_iff, Set.mem_ofPred_eq, mem_Ioo]
        rw [this, lintegral_indicator_const measurableSet_Ioo]
        simp [hs]
      · have : (fun t => F2 t s) = fun _ => 0 := by
          funext t
          simp only [F2, S, Set.indicator, mem_inter_iff, Set.mem_ofPred_eq]
          rw [ite_eq_right]
          intro h; exact hs (h.1.trans h.2)
        simp only [this, lintegral_zero]
        simp [hs]
    simp only [hL, hR] at hswap
    rw [← lintegral_indicator measurableSet_Ioi, hswap, lintegral_indicator measurableSet_Ioi]
    refine setLIntegral_mono' measurableSet_Ioi (fun s hs => ?_)
    have hs1 : (1 : ℝ) < s := hs
    calc ENNReal.ofReal (1 / s ^ 2) * μ (Ioo 1 s)
        ≤ ENNReal.ofReal (1 / s ^ 2) * μ (Ioc 1 s) :=
          mul_le_mul' le_rfl (measure_mono Ioo_subset_Ioc_self)
      _ = ENNReal.ofReal ((f s - f 1) / s ^ 2) := by
          rw [hμIoc, hgf s hs1.le, hgf 1 le_rfl, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hXnn : 0 ≤ (∫ s in Ioi (1 : ℝ), f s / s ^ 2) - f 1 := by
    rw [← hval]
    exact setIntegral_nonneg measurableSet_Ioi hnn2
  have hfin : ρ univ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  refine ⟨ρ, ⟨hfin.lt_top⟩, ?_, ?_⟩
  · exact ENNReal.toReal_le_of_le_ofReal (by linarith)
      (hmass.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  · intro c hc
    have hsm : MeasurableSet (Ioc (1 : ℝ) c) := measurableSet_Ioc
    rw [hρ, setIntegral_withDensity_eq_setIntegral_toReal_smul hdens
      (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top) _ hsm,
      Measure.restrict_restrict hsm, Set.inter_eq_left.2 Ioc_subset_Ioi_self]
    have : ∫ t in Ioc 1 c, (ENNReal.ofReal (1 / t)).toReal • t ∂μ =
        ∫ t in Ioc 1 c, (1 : ℝ) ∂μ := by
      refine setIntegral_congr_fun hsm (fun t ht => ?_)
      have : 0 < t := by linarith [ht.1]
      simp only [smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by positivity)]
      field_simp
    rw [this, setIntegral_const, hμ, Measure.real, hμIoc, ENNReal.toReal_ofReal
      (by
        rw [hgf c hc, hgf 1 le_rfl]
        have := hfmono (mem_Ici.2 le_rfl) (mem_Ici.2 hc) hc
        linarith),
      hgf c hc, hgf 1 le_rfl]
    simp

open Classical in
/-- Step 2a of the proof of `exists_martingale_of_integral_bound`: the stopped capital is
a measurable function of the level `t`, for each fixed history `y`. -/
private lemma exists_martingale_of_integral_bound_measurable (m : BitString → ℝ)
    (y : BitString) : Measurable (fun t : ℝ => stoppedCapital m t y) := by
  induction y using List.reverseRecOn with
  | nil =>
    have : ∀ t : ℝ, stoppedCapital m t [] = m [] := by
      intro t
      unfold stoppedCapital
      by_cases h : t ≤ m []
      · simp [h]
      · simp [h]
    simp only [this]
    exact measurable_const
  | append_singleton x b ih =>
    have key : ∀ t : ℝ, stoppedCapital m t (x ++ [b]) =
        if (∃ z ∈ x.inits, t ≤ m z) then stoppedCapital m t x else m (x ++ [b]) := by
      intro t
      unfold stoppedCapital
      have hp1 : (x ++ [b]).inits = x.inits ++ [x ++ [b]] := by
        rw [List.inits_append]
        simp
      rw [hp1, List.find?_append]
      cases h : List.find? (fun y => decide (t ≤ m y)) x.inits with
      | some z =>
        have hz := List.find?_some h
        have hzm := List.mem_of_find?_eq_some h
        have : ∃ z ∈ x.inits, t ≤ m z := ⟨z, hzm, of_decide_eq_true hz⟩
        simp only [this, ite_true, Option.some_or, Option.getD_some]
      | none =>
        have : ¬ ∃ z ∈ x.inits, t ≤ m z := by
          rintro ⟨z, hz, hzt⟩
          have := List.find?_eq_none.mp h z hz
          simp [hzt] at this
        simp only [this, ite_false, Option.none_or]
        by_cases hp : t ≤ m (x ++ [b])
        · simp [List.find?, hp]
        · simp [List.find?, hp]
    simp only [key]
    have hset : {t : ℝ | ∃ z ∈ x.inits, t ≤ m z} =
        ⋃ z ∈ {z | z ∈ x.inits}, Set.Iic (m z) := by
      ext t; simp
    refine Measurable.ite ?_ ih measurable_const
    rw [hset]
    exact MeasurableSet.biUnion (List.finite_toSet _).countable (fun _ _ => measurableSet_Iic)

/-- Step 2b of the proof of `exists_martingale_of_integral_bound`: for a fixed history `y`
the stopped capital is bounded in the level `t`. -/
private lemma exists_martingale_of_integral_bound_bounded (m : BitString → ℝ)
    (y : BitString) : ∃ B : ℝ, ∀ t : ℝ, |stoppedCapital m t y| ≤ B := by
  refine ⟨∑ z ∈ y.inits.toFinset, |m z|, fun t => ?_⟩
  have hmem : ((y.inits.find? fun z => decide (t ≤ m z)).getD y) ∈ y.inits.toFinset := by
    rw [List.mem_toFinset]
    cases h : y.inits.find? (fun z => decide (t ≤ m z)) with
    | some z => exact List.mem_of_find?_eq_some h
    | none => exact (List.mem_inits _ _).2 (List.prefix_refl y)
  exact Finset.single_le_sum (f := fun z => |m z|) (fun z _ => abs_nonneg _) hmem

/-- **SUV p. 273, after Theorem 178**, cited there to [170, 47] and not proved in the book.  If
`f : [1, ∞) → [0, ∞)` is non-decreasing and continuous with `∫_1^∞ f(t)/t² dt ≤ 1`, then for every
uniform martingale `m` there is `m'` such that once `m` has reached `c` at a moment, `m'` has
reached `f(c)` at that moment and never goes below it later. -/
theorem exists_martingale_of_integral_bound {f : ℝ → ℝ}
    (hf0 : ∀ t, 1 ≤ t → 0 ≤ f t) (hfmono : MonotoneOn f (Set.Ici 1))
    (hfcont : ContinuousOn f (Set.Ici 1))
    (hfint : IntegrableOn (fun t => f t / t ^ 2) (Set.Ioi 1))
    (hfle : ∫ t in Set.Ioi (1 : ℝ), f t / t ^ 2 ≤ 1)
    {m : BitString → ℝ} (hm : IsMartingale uniformMeasure m) :
    ∃ m', IsMartingale uniformMeasure m' ∧
      ∀ x y, x <+: y → 1 ≤ m x → f (m x) ≤ m' y := by
  obtain ⟨ρ, hρ, hρle, hρint⟩ :=
    exists_martingale_of_integral_bound_weights hfmono hfcont hfint hfle
  have hf1 : 0 ≤ f 1 := hf0 1 le_rfl
  have hint : ∀ y, Integrable (fun t : ℝ => stoppedCapital m t y) ρ := by
    intro y
    obtain ⟨B, hB⟩ := exists_martingale_of_integral_bound_bounded m y
    exact Integrable.of_bound
      (exists_martingale_of_integral_bound_measurable m y).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun t => by simpa using hB t)
  have hS : ∀ t : ℝ, IsFairCapital uniformMeasure (stoppedCapital m t) :=
    fun t => hm.toIsFairCapital.stoppedCapital t
  have hSnn : ∀ t y, 0 ≤ stoppedCapital m t y := fun t y => (hS t).nonneg y
  have hrest : 0 ≤ 1 - f 1 - (ρ Set.univ).toReal := by linarith
  let m' : BitString → ℝ := fun y =>
    f 1 + (∫ t, stoppedCapital m t y ∂ρ) + (1 - f 1 - (ρ Set.univ).toReal)
  have hnn : ∀ y, 0 ≤ m' y := fun y => by
    have : 0 ≤ ∫ t, stoppedCapital m t y ∂ρ := integral_nonneg fun t => hSnn t y
    simp only [m']; linarith
  have hfair : ∀ x, m' x = (m' (x ++ [false]) + m' (x ++ [true])) / 2 := by
    intro x
    have h1 : (fun t : ℝ => stoppedCapital m t x) = fun t =>
        (stoppedCapital m t (x ++ [false]) + stoppedCapital m t (x ++ [true])) / 2 :=
      funext fun t => ((isFairCapital_uniform_iff _).1 (hS t)).2 x
    have h2 : ∫ t, stoppedCapital m t x ∂ρ =
        ((∫ t, stoppedCapital m t (x ++ [false]) ∂ρ) +
          ∫ t, stoppedCapital m t (x ++ [true]) ∂ρ) / 2 := by
      rw [h1, integral_div, integral_add (hint _) (hint _)]
    simp only [m']
    rw [h2]; ring
  have hinit : m' [] = 1 := by
    have h1 : (fun t : ℝ => stoppedCapital m t []) = fun _ => 1 := by
      funext t
      unfold stoppedCapital
      by_cases h : t ≤ 1
      · simp [h, hm.init]
      · simp [h, hm.init]
    simp only [m']
    rw [h1, integral_const]
    simp [Measure.real]
  refine ⟨m', ⟨(isFairCapital_uniform_iff m').2 ⟨hnn, hfair⟩, hinit⟩, ?_⟩
  intro x y hxy hx1
  have hmono : ∫ t in Set.Ioc 1 (m x), t ∂ρ ≤ ∫ t in Set.Ioc 1 (m x),
      stoppedCapital m t y ∂ρ := by
    refine setIntegral_mono_on ?_ (hint y).integrableOn measurableSet_Ioc ?_
    · exact (Continuous.integrableOn_Ioc continuous_id) |>.mono_measure le_rfl
    · intro t ht
      exact le_stoppedCapital_of_prefix ht.2 hxy
  have hle : ∫ t in Set.Ioc 1 (m x), stoppedCapital m t y ∂ρ ≤ ∫ t, stoppedCapital m t y ∂ρ :=
    setIntegral_le_integral (hint y) (Filter.Eventually.of_forall fun t => hSnn t y)
  have := hρint (m x) hx1
  simp only [m']
  linarith

/-! ### Doob's theorem -/

/-- The mass of a cylinder is the sum of the masses of its two children, as real numbers
(a private copy: the public `massR_add` is declared after the target). -/
private lemma exists_martingale_wins_of_oscillation_massR_add {π : Measure CantorSeq}
    [IsProbabilityMeasure π] (x : BitString) :
    massR π x = massR π (x ++ [false]) + massR π (x ++ [true]) := by
  have hne : ∀ y, cantorMass π y ≠ ∞ := fun y => measure_ne_top π _
  simp only [massR]
  rw [cantorMass_add π x, ENNReal.toReal_add (hne _) (hne _)]

/-- The "buy low, sell high" gambler of Theorem 179, run along the REVERSED history `r` (so that the
recursion is structural): the pair (holding, capital) after the history `r.reverse`.  He starts
waiting with capital `1`; while waiting he keeps his capital and starts holding once `m < p`; while
holding he multiplies his capital by `m(xb) / m(x)` (by `1` if `m(x) = 0`) and goes back to waiting
once `q < m`. -/
private noncomputable def exists_martingale_wins_of_oscillation_aux (m : BitString → ℝ) (p q : ℝ) :
    List Bool → Bool × ℝ
  | [] => (false, 1)
  | b :: r =>
    ((if (exists_martingale_wins_of_oscillation_aux m p q r).1 then
        decide (m (r.reverse ++ [b]) ≤ q)
      else decide (m (r.reverse ++ [b]) < p)),
     (exists_martingale_wins_of_oscillation_aux m p q r).2 *
       (if (exists_martingale_wins_of_oscillation_aux m p q r).1 then
          (if m r.reverse = 0 then 1 else m (r.reverse ++ [b]) / m r.reverse) else 1))

/-- Whether the gambler is holding (following `m`) after the history `x`. -/
private noncomputable def exists_martingale_wins_of_oscillation_state
    (m : BitString → ℝ) (p q : ℝ) (x : BitString) : Bool :=
  (exists_martingale_wins_of_oscillation_aux m p q x.reverse).1

/-- The capital of the gambler after the history `x`. -/
private noncomputable def exists_martingale_wins_of_oscillation_mult
    (m : BitString → ℝ) (p q : ℝ) (x : BitString) : ℝ :=
  (exists_martingale_wins_of_oscillation_aux m p q x.reverse).2

/-- The gambler starts waiting. -/
private lemma exists_martingale_wins_of_oscillation_state_nil (m : BitString → ℝ) (p q : ℝ) :
    exists_martingale_wins_of_oscillation_state m p q [] = false := by
  simp [exists_martingale_wins_of_oscillation_state, exists_martingale_wins_of_oscillation_aux]

/-- The gambler starts with capital `1`. -/
private lemma exists_martingale_wins_of_oscillation_mult_nil (m : BitString → ℝ) (p q : ℝ) :
    exists_martingale_wins_of_oscillation_mult m p q [] = 1 := by
  simp [exists_martingale_wins_of_oscillation_mult, exists_martingale_wins_of_oscillation_aux]

/-- The recurrence of the state after one more bit. -/
private lemma exists_martingale_wins_of_oscillation_state_snoc (m : BitString → ℝ) (p q : ℝ)
    (x : BitString) (b : Bool) :
    exists_martingale_wins_of_oscillation_state m p q (x ++ [b]) =
      (if exists_martingale_wins_of_oscillation_state m p q x then
        decide (m (x ++ [b]) ≤ q) else decide (m (x ++ [b]) < p)) := by
  have hrev : (x ++ [b]).reverse = b :: x.reverse := by simp
  simp only [exists_martingale_wins_of_oscillation_state, hrev,
    exists_martingale_wins_of_oscillation_aux, List.reverse_reverse]
  rfl

/-- The recurrence of the capital after one more bit. -/
private lemma exists_martingale_wins_of_oscillation_mult_snoc (m : BitString → ℝ) (p q : ℝ)
    (x : BitString) (b : Bool) :
    exists_martingale_wins_of_oscillation_mult m p q (x ++ [b]) =
      exists_martingale_wins_of_oscillation_mult m p q x *
        (if exists_martingale_wins_of_oscillation_state m p q x then
          (if m x = 0 then 1 else m (x ++ [b]) / m x) else 1) := by
  have hrev : (x ++ [b]).reverse = b :: x.reverse := by simp
  simp only [exists_martingale_wins_of_oscillation_mult,
    exists_martingale_wins_of_oscillation_state, hrev,
    exists_martingale_wins_of_oscillation_aux, List.reverse_reverse]
  rfl

/-- The capital of the gambler is non-negative. -/
private lemma exists_martingale_wins_of_oscillation_mult_nonneg {π : Measure CantorSeq}
    [IsProbabilityMeasure π] {m : BitString → ℝ} (hm : IsMartingale π m) (p q : ℝ) (x : BitString) :
    0 ≤ exists_martingale_wins_of_oscillation_mult m p q x := by
  induction x using List.reverseRecOn with
  | nil => rw [exists_martingale_wins_of_oscillation_mult_nil]; exact zero_le_one
  | append_singleton x b ih =>
    rw [exists_martingale_wins_of_oscillation_mult_snoc]
    refine mul_nonneg ih ?_
    split_ifs
    · exact zero_le_one
    · exact div_nonneg (hm.nonneg _) (hm.nonneg _)
    · exact zero_le_one

/-- The capital of the gambler is a `π`-martingale, for every `π` and every `π`-martingale `m`:
while holding he follows `m` up to the constant factor, and otherwise he does not bet. -/
private lemma exists_martingale_wins_of_oscillation_isMartingale {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsMartingale π m) (p q : ℝ) :
    IsMartingale π (exists_martingale_wins_of_oscillation_mult m p q) := by
  refine { nonneg := exists_martingale_wins_of_oscillation_mult_nonneg hm p q, fair := ?_,
           init := exists_martingale_wins_of_oscillation_mult_nil m p q }
  intro x
  rw [exists_martingale_wins_of_oscillation_mult_snoc,
    exists_martingale_wins_of_oscillation_mult_snoc]
  have hfair := hm.fair x
  have hadd := exists_martingale_wins_of_oscillation_massR_add (π := π) x
  cases hst : exists_martingale_wins_of_oscillation_state m p q x
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    rw [hadd]; ring
  · by_cases hmx : m x = 0
    · simp only [hmx, ↓reduceIte, mul_one]
      rw [hadd]; ring
    · simp only [hmx, ↓reduceIte]
      field_simp
      linear_combination (exists_martingale_wins_of_oscillation_mult m p q x) * hfair

/-- The sequence-level core of the proof: if the positive values `a n` go below `p` and above `q`
infinitely often (`0 < p < q`), the non-negative capitals `c n` of a gambler who starts waiting with
capital `1`, starts holding when `a < p`, stops holding when `q < a`, and multiplies his capital by
`a (n + 1) / a n` while holding, are unbounded.  The potential `P n = c n / a n` (holding) or
`c n / p` (waiting) never decreases and is multiplied by `q / p` along each cycle. -/
private lemma exists_martingale_wins_of_oscillation_abstract {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (a c : ℕ → ℝ) (h : ℕ → Bool)
    (ha : ∀ n, 0 < a n) (hc : ∀ n, 0 ≤ c n)
    (h0 : h 0 = false) (c0 : c 0 = 1)
    (hh : ∀ n, h (n + 1) =
      (if h n then decide (a (n + 1) ≤ q) else decide (a (n + 1) < p)))
    (hcc : ∀ n, c (n + 1) = c n * (if h n then a (n + 1) / a n else 1))
    (hlow : ∃ᶠ n in atTop, a n < p) (hhigh : ∃ᶠ n in atTop, q < a n) :
    ¬ BddAbove (Set.range c) := by
  have hq : 0 < q := hp.trans hpq
  have hqp : 0 ≤ q / p := (div_pos hq hp).le
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℝ, ∀ n, P n = if h n then c n / a n else c n / p :=
    ⟨_, fun _ => rfl⟩
  -- the four transitions of the potential `P`
  have E1 : ∀ n, h n = false → a (n + 1) < p → h (n + 1) = true ∧ P n ≤ P (n + 1) := by
    intro n hn hlt
    have h1 : h (n + 1) = true := by rw [hh n, hn]; simpa using hlt
    have hc1 : c (n + 1) = c n := by rw [hcc n, hn]; simp
    refine ⟨h1, ?_⟩
    rw [hP n, hP (n + 1), hn, h1, hc1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact div_le_div_of_nonneg_left (hc n) (ha _) hlt.le
  have E2 : ∀ n, h n = false → ¬ a (n + 1) < p → h (n + 1) = false ∧ P (n + 1) = P n := by
    intro n hn hge
    have h1 : h (n + 1) = false := by rw [hh n, hn]; simpa using hge
    have hc1 : c (n + 1) = c n := by rw [hcc n, hn]; simp
    refine ⟨h1, ?_⟩
    rw [hP n, hP (n + 1), hn, h1, hc1]
    simp only [Bool.false_eq_true, ↓reduceIte]
  have E3 : ∀ n, h n = true → ¬ q < a (n + 1) → h (n + 1) = true ∧ P (n + 1) = P n := by
    intro n hn hle
    have h1 : h (n + 1) = true := by rw [hh n, hn]; simpa using hle
    have hc1 : c (n + 1) = c n * (a (n + 1) / a n) := by rw [hcc n, hn]; simp
    refine ⟨h1, ?_⟩
    rw [hP n, hP (n + 1), hn, h1, hc1]
    have := (ha n).ne'
    have := (ha (n + 1)).ne'
    simp only [↓reduceIte]
    field_simp
  have E4 : ∀ n, h n = true → q < a (n + 1) →
      h (n + 1) = false ∧ (q / p) * P n ≤ P (n + 1) := by
    intro n hn hlt
    have h1 : h (n + 1) = false := by rw [hh n, hn]; simpa using hlt
    have hc1 : c (n + 1) = c n * (a (n + 1) / a n) := by rw [hcc n, hn]; simp
    refine ⟨h1, ?_⟩
    rw [hP n, hP (n + 1), hn, h1, hc1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have := (ha n).ne'
    have hnn : 0 ≤ c n / (a n * p) := div_nonneg (hc n) (mul_pos (ha n) hp).le
    have key : (q / p) * (c n / a n) = (c n / (a n * p)) * q := by field_simp
    have key2 : c n * (a (n + 1) / a n) / p = (c n / (a n * p)) * a (n + 1) := by field_simp
    rw [key, key2]
    exact mul_le_mul_of_nonneg_left hlt.le hnn
  -- a holding stretch ends with a gain by the factor `q / p`
  have H : ∀ d n, h n = true → q < a (n + d + 1) →
      ∃ n', n < n' ∧ h n' = false ∧ (q / p) * P n ≤ P n' := by
    intro d
    induction d with
    | zero =>
      intro n hn hq1
      exact ⟨n + 1, Nat.lt_succ_self n, (E4 n hn hq1).1, (E4 n hn hq1).2⟩
    | succ d ih =>
      intro n hn hq1
      by_cases hq2 : q < a (n + 1)
      · exact ⟨n + 1, Nat.lt_succ_self n, (E4 n hn hq2).1, (E4 n hn hq2).2⟩
      · obtain ⟨hn1, hP1⟩ := E3 n hn hq2
        have hq1' : q < a (n + 1 + d + 1) := by
          have : n + 1 + d + 1 = n + (d + 1) + 1 := by omega
          rw [this]; exact hq1
        obtain ⟨n', hlt, hn', hP'⟩ := ih (n + 1) hn1 hq1'
        refine ⟨n', by omega, hn', ?_⟩
        rw [hP1] at hP'
        exact hP'
  -- a waiting stretch ends by buying
  have L : ∀ d n, h n = false → a (n + d + 1) < p →
      ∃ n', n < n' ∧ h n' = true ∧ P n ≤ P n' := by
    intro d
    induction d with
    | zero =>
      intro n hn hlt
      exact ⟨n + 1, Nat.lt_succ_self n, (E1 n hn hlt).1, (E1 n hn hlt).2⟩
    | succ d ih =>
      intro n hn hlt
      by_cases hlt2 : a (n + 1) < p
      · exact ⟨n + 1, Nat.lt_succ_self n, (E1 n hn hlt2).1, (E1 n hn hlt2).2⟩
      · obtain ⟨hn1, hP1⟩ := E2 n hn hlt2
        have hlt' : a (n + 1 + d + 1) < p := by
          have : n + 1 + d + 1 = n + (d + 1) + 1 := by omega
          rw [this]; exact hlt
        obtain ⟨n', hlt'', hn', hP'⟩ := ih (n + 1) hn1 hlt'
        refine ⟨n', by omega, hn', ?_⟩
        rw [hP1] at hP'
        exact hP'
  -- one cycle: from any time there is a later waiting time with `P` multiplied by `q / p`
  have fromHold : ∀ n1, h n1 = true →
      ∃ n', n1 < n' ∧ h n' = false ∧ (q / p) * P n1 ≤ P n' := by
    intro n1 hn1
    obtain ⟨k, hk, hqk⟩ := Filter.frequently_atTop.mp hhigh (n1 + 1)
    obtain ⟨d, rfl⟩ : ∃ d, k = n1 + d + 1 := ⟨k - n1 - 1, by omega⟩
    exact H d n1 hn1 hqk
  have Cyc : ∀ n, ∃ n', n < n' ∧ h n' = false ∧ (q / p) * P n ≤ P n' := by
    intro n
    cases hn : h n
    · obtain ⟨k, hk, hlk⟩ := Filter.frequently_atTop.mp hlow (n + 1)
      obtain ⟨d, rfl⟩ : ∃ d, k = n + d + 1 := ⟨k - n - 1, by omega⟩
      obtain ⟨n1, hlt1, hn1, hP1⟩ := L d n hn hlk
      obtain ⟨n', hlt2, hn', hP2⟩ := fromHold n1 hn1
      exact ⟨n', hlt1.trans hlt2, hn', le_trans (mul_le_mul_of_nonneg_left hP1 hqp) hP2⟩
    · exact fromHold n hn
  have Gr : ∀ k : ℕ, ∃ n, h n = false ∧ (q / p) ^ k ≤ c n := by
    intro k
    induction k with
    | zero => exact ⟨0, h0, by simp [c0]⟩
    | succ k ih =>
      obtain ⟨n, hn, hcn⟩ := ih
      obtain ⟨n', _, hn', hP'⟩ := Cyc n
      refine ⟨n', hn', ?_⟩
      have e1 : P n = c n / p := by rw [hP n, hn]; simp
      have e2 : P n' = c n' / p := by rw [hP n', hn']; simp
      rw [e1, e2] at hP'
      have hP'' : (q / p) * c n ≤ c n' := by
        have h3 := (le_div_iff₀ hp).mp hP'
        have h4 : (q / p) * (c n / p) * p = (q / p) * c n := by field_simp
        linarith
      calc (q / p) ^ (k + 1) = (q / p) ^ k * (q / p) := pow_succ _ _
        _ ≤ c n * (q / p) := mul_le_mul_of_nonneg_right hcn hqp
        _ = (q / p) * c n := mul_comm _ _
        _ ≤ c n' := hP''
  rintro ⟨B, hB⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B ((one_lt_div hp).mpr hpq)
  obtain ⟨n, -, hn⟩ := Gr k
  have := hB ⟨n, rfl⟩
  linarith

/-- Along a path all of whose prefixes carry mass, a martingale that exceeds `q > 0` infinitely
often never vanishes: zero propagates along the path by fairness. -/
private lemma exists_martingale_wins_of_oscillation_pos_along {π : Measure CantorSeq}
    [IsProbabilityMeasure π] {m : BitString → ℝ} (hm : IsMartingale π m) {q : ℝ} (hq : 0 < q)
    (w : CantorSeq) (hw : ∀ n, 0 < massR π (cantorPrefix w n))
    (hhigh : ∃ᶠ n in atTop, q < m (cantorPrefix w n)) :
    ∀ n, 0 < m (cantorPrefix w n) := by
  have hprop : ∀ k, m (cantorPrefix w k) = 0 → m (cantorPrefix w (k + 1)) = 0 := by
    intro k hk
    have hfair := hm.fair (cantorPrefix w k)
    rw [hk, zero_mul] at hfair
    have hpos := hw (k + 1)
    rw [cantorPrefix_succ] at hpos ⊢
    have t0 : 0 ≤ m (cantorPrefix w k ++ [false]) * massR π (cantorPrefix w k ++ [false]) :=
      mul_nonneg (hm.nonneg _) ENNReal.toReal_nonneg
    have t1 : 0 ≤ m (cantorPrefix w k ++ [true]) * massR π (cantorPrefix w k ++ [true]) :=
      mul_nonneg (hm.nonneg _) ENNReal.toReal_nonneg
    generalize w k = b at hpos ⊢
    cases b
    · have h0 : m (cantorPrefix w k ++ [false]) * massR π (cantorPrefix w k ++ [false]) = 0 := by
        linarith
      exact (mul_eq_zero.mp h0).resolve_right hpos.ne'
    · have h1 : m (cantorPrefix w k ++ [true]) * massR π (cantorPrefix w k ++ [true]) = 0 := by
        linarith
      exact (mul_eq_zero.mp h1).resolve_right hpos.ne'
  intro n
  by_contra hcon
  have h0 : m (cantorPrefix w n) = 0 := le_antisymm (not_lt.mp hcon) (hm.nonneg _)
  have hall : ∀ j, m (cantorPrefix w (n + j)) = 0 := by
    intro j
    induction j with
    | zero => simpa using h0
    | succ j ih => exact hprop _ ih
  obtain ⟨k, hk, hqk⟩ := Filter.frequently_atTop.mp hhigh n
  have h2 := hall (k - n)
  rw [show n + (k - n) = k by omega] at h2
  rw [h2] at hqk
  linarith

/-- **Proof of Theorem 179, SUV p. 274 ("buy low, sell high").**  For `0 < p < q` there is a
martingale winning on all sequences where the capital of `m` goes below `p` and above `q` infinitely
often. -/
theorem exists_martingale_wins_of_oscillation {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsMartingale π m) {p q : ℚ} (hp : 0 < p) (hpq : p < q) :
    ∃ m', IsMartingale π m' ∧ ∀ w,
      (∃ᶠ n in atTop, m (cantorPrefix w n) < p) → (∃ᶠ n in atTop, (q : ℝ) < m (cantorPrefix w n)) →
        Wins m' w := by
  have hp' : (0 : ℝ) < (p : ℝ) := Rat.cast_pos.mpr hp
  have hpq' : (p : ℝ) < (q : ℝ) := Rat.cast_lt.mpr hpq
  have hM := exists_martingale_wins_of_oscillation_isMartingale hm (p : ℝ) (q : ℝ)
  -- the witness: the gambler's capital, and a free `|x| + 1` on null cylinders
  refine ⟨fun x => if massR π x = 0 then (x.length : ℝ) + 1
    else exists_martingale_wins_of_oscillation_mult m p q x, ?_, ?_⟩
  · have key : ∀ y, (if massR π y = 0 then (y.length : ℝ) + 1
          else exists_martingale_wins_of_oscillation_mult m p q y) * massR π y
        = exists_martingale_wins_of_oscillation_mult m p q y * massR π y := by
      intro y
      by_cases hy : massR π y = 0
      · simp [hy]
      · simp [hy]
    refine { nonneg := ?_, fair := ?_, init := ?_ }
    · intro x
      split_ifs
      · positivity
      · exact hM.nonneg x
    · intro x
      rw [key, key, key]
      exact hM.fair x
    · rw [massR_nil]
      simp [exists_martingale_wins_of_oscillation_mult_nil]
  · intro w h1 h2
    by_cases hw : ∀ n, 0 < massR π (cantorPrefix w n)
    · -- all prefixes carry mass: the gambler's capital is a genuine product
      have hpos := exists_martingale_wins_of_oscillation_pos_along hm (hp'.trans hpq') w hw h2
      have heq : ∀ n, (if massR π (cantorPrefix w n) = 0 then
            ((cantorPrefix w n).length : ℝ) + 1
          else exists_martingale_wins_of_oscillation_mult m p q (cantorPrefix w n)) =
          exists_martingale_wins_of_oscillation_mult m p q (cantorPrefix w n) := by
        intro n
        simp [(hw n).ne']
      have habs := exists_martingale_wins_of_oscillation_abstract hp' hpq'
        (fun n => m (cantorPrefix w n))
        (fun n => exists_martingale_wins_of_oscillation_mult m p q (cantorPrefix w n))
        (fun n => exists_martingale_wins_of_oscillation_state m p q (cantorPrefix w n)) hpos
        (fun n => exists_martingale_wins_of_oscillation_mult_nonneg hm _ _ _)
        (exists_martingale_wins_of_oscillation_state_nil m p q)
        (exists_martingale_wins_of_oscillation_mult_nil m p q)
        (fun n => by
          show exists_martingale_wins_of_oscillation_state m p q (cantorPrefix w (n + 1)) = _
          rw [cantorPrefix_succ]
          exact exists_martingale_wins_of_oscillation_state_snoc m p q _ _)
        (fun n => by
          show exists_martingale_wins_of_oscillation_mult m p q (cantorPrefix w (n + 1)) = _
          rw [cantorPrefix_succ, exists_martingale_wins_of_oscillation_mult_snoc]
          simp only [(hpos n).ne', ↓reduceIte])
        h1 h2
      unfold Wins
      simp only [heq]
      exact habs
    · -- some prefix is a null cylinder, and then so are all longer ones: `m' (prefix n) = n + 1`
      push Not at hw
      obtain ⟨n0, hn0⟩ := hw
      have hnn : ∀ y, 0 ≤ massR π y := fun y => ENNReal.toReal_nonneg
      have hstep : ∀ n, massR π (cantorPrefix w n) = 0 →
          massR π (cantorPrefix w (n + 1)) = 0 := by
        intro n hn
        have hadd := exists_martingale_wins_of_oscillation_massR_add (π := π) (cantorPrefix w n)
        rw [cantorPrefix_succ]
        have r0 := hnn (cantorPrefix w n ++ [false])
        have r1 := hnn (cantorPrefix w n ++ [true])
        generalize w n = b
        cases b <;> linarith
      have hz : ∀ j, massR π (cantorPrefix w (n0 + j)) = 0 := by
        intro j
        induction j with
        | zero => exact le_antisymm hn0 (hnn _)
        | succ j ih => exact hstep _ ih
      unfold Wins
      rintro ⟨B, hB⟩
      obtain ⟨N, hN⟩ := exists_nat_gt B
      have hmem := hB ⟨n0 + N, rfl⟩
      simp only [hz N, ↓reduceIte, cantorPrefix_length] at hmem
      push_cast at hmem
      have : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
      linarith


/-- Step 1 of the proof of `measure_not_hasFiniteLimit_eq_zero`: the sequences where `m`
does not have a finite limit are contained in the union of the sequences where `m` wins and those
where it oscillates between two rationals. -/
private theorem measure_not_hasFiniteLimit_eq_zero_union_bound
    {m : BitString → ℝ} (h_nn : ∀ x, 0 ≤ m x) :
    {w : CantorSeq | ¬ HasFiniteLimit m w} ⊆
      {w | Wins m w} ∪ ⋃ (pq : ℚ × ℚ) (_ : 0 < pq.1 ∧ pq.1 < pq.2),
        {w | (∃ᶠ n in atTop, m (cantorPrefix w n) < (pq.1 : ℝ)) ∧
            (∃ᶠ n in atTop, (pq.2 : ℝ) < m (cantorPrefix w n))} := by
  intro w hw
  by_cases hb : BddAbove (Set.range fun n => m (cantorPrefix w n))
  · right
    obtain ⟨B, hB⟩ := hb
    set a : ℕ → ℝ := fun n => m (cantorPrefix w n) with ha
    have hbu : IsBoundedUnder (· ≤ ·) atTop a :=
      isBoundedUnder_of ⟨B, fun n => hB ⟨n, rfl⟩⟩
    have hbl : IsBoundedUnder (· ≥ ·) atTop a :=
      isBoundedUnder_of ⟨0, fun n => h_nn _⟩
    have hlt : liminf a atTop < limsup a atTop := by
      refine lt_of_le_of_ne (liminf_le_limsup hbu hbl) ?_
      intro h
      exact hw ⟨_, tendsto_of_liminf_eq_limsup rfl h.symm hbu hbl⟩
    have h0 : 0 ≤ liminf a atTop :=
      le_liminf_of_le hbu.isCoboundedUnder_ge (Filter.Eventually.of_forall fun n => h_nn _)
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hp2
    have hp0 : (0 : ℝ) < p := lt_of_le_of_lt h0 hp1
    have hpq : (p : ℝ) < q := hq1
    simp only [Set.mem_iUnion]
    refine ⟨(p, q), ⟨by exact_mod_cast hp0, by exact_mod_cast hpq⟩, ?_, ?_⟩
    · exact frequently_lt_of_liminf_lt hbu.isCoboundedUnder_ge hp1
    · exact frequently_lt_of_lt_limsup hbl.isCoboundedUnder_le hq2
  · left
    exact hb

/-- **SUV Theorem 179, p. 274 (Doob).**  For every `π`-martingale, for `π`-almost every `ω` the
values of `m` on the prefixes of `ω` have a finite limit. -/
theorem measure_not_hasFiniteLimit_eq_zero {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsMartingale π m) : π {w | ¬ HasFiniteLimit m w} = 0 := by
  have h_sub : {w : CantorSeq | ¬ HasFiniteLimit m w} ⊆
      {w | Wins m w} ∪ ⋃ (pq : ℚ × ℚ) (h : 0 < pq.1 ∧ pq.1 < pq.2),
        {w | (∃ᶠ n in atTop, m (cantorPrefix w n) < (pq.1 : ℝ)) ∧
            (∃ᶠ n in atTop, (pq.2 : ℝ) < m (cantorPrefix w n))} :=
    measure_not_hasFiniteLimit_eq_zero_union_bound hm.toIsFairCapital.nonneg
  have hs1 : π {w | Wins m w} = 0 := measure_wins_eq_zero hm
  have hs2 : ∀ pq : ℚ × ℚ, ∀ h : 0 < pq.1 ∧ pq.1 < pq.2,
    π {w | (∃ᶠ n in atTop, m (cantorPrefix w n) < (pq.1 : ℝ)) ∧
            (∃ᶠ n in atTop, (pq.2 : ℝ) < m (cantorPrefix w n))} = 0 := by
    intro pq hpq
    have ⟨m', hm', h_wins⟩ := exists_martingale_wins_of_oscillation hm hpq.1 hpq.2
    have h_sub2 : {w : CantorSeq | (∃ᶠ n in atTop, m (cantorPrefix w n) < (pq.1 : ℝ)) ∧
      (∃ᶠ n in atTop, (pq.2 : ℝ) < m (cantorPrefix w n))} ⊆ {w | Wins m' w} := by
      intro w hw
      exact h_wins w hw.1 hw.2
    have h_zero : π {w | Wins m' w} = 0 := measure_wins_eq_zero hm'
    exact measure_mono_null h_sub2 h_zero
  have hs3 : π (⋃ (pq : ℚ × ℚ) (h : 0 < pq.1 ∧ pq.1 < pq.2),
        {w | (∃ᶠ n in atTop, m (cantorPrefix w n) < (pq.1 : ℝ)) ∧
            (∃ᶠ n in atTop, (pq.2 : ℝ) < m (cantorPrefix w n))}) = 0 := by
    exact measure_iUnion_null (fun pq => measure_iUnion_null (fun h => hs2 pq h))
  exact measure_mono_null h_sub (by simp [hs1, hs3])

/-- The conditional probability of `A` for the second coordinate, given that the first coordinate
has prefix `a`.  When that event has probability `0` the value is the junk value `0`; the statement
below is about almost every first coordinate, and such `a` occur only on a null set. -/
noncomputable def condSecond (P : Measure (CantorSeq × CantorSeq)) (A : Set CantorSeq)
    (a : BitString) : ℝ :=
  (P (cantorCylinder a ×ˢ A)).toReal / (P (cantorCylinder a ×ˢ Set.univ)).toReal



/-- Step 1 of the proof of `ae_exists_tendsto_condSecond`: fairness and bound. -/
private theorem ae_exists_tendsto_condSecond_fair
    (P : Measure (CantorSeq × CantorSeq)) [IsProbabilityMeasure P]
    {A : Set CantorSeq} (hA : MeasurableSet A) :
    IsFairCapital (P.map Prod.fst) (condSecond P A) ∧
      ∀ x : BitString, condSecond P A x ≤ 1 := by
  have hmass : ∀ x : BitString, massR (P.map Prod.fst) x
      = (P (cantorCylinder x ×ˢ Set.univ)).toReal := by
    intro x
    rw [massR, cantorMass, Measure.map_apply measurable_fst (measurableSet_cantorCylinder x),
      Set.prod_univ]
  have hadd : ∀ (B : Set CantorSeq), MeasurableSet B → ∀ x : BitString,
      (P (cantorCylinder x ×ˢ B)).toReal
        = (P (cantorCylinder (x ++ [false]) ×ˢ B)).toReal
          + (P (cantorCylinder (x ++ [true]) ×ˢ B)).toReal := by
    intro B hB x
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    congr 1
    conv_lhs => rw [cantorCylinder_eq_union_children x, Set.union_prod]
    exact measure_union (Set.disjoint_prod.2 (Or.inl (cantorCylinder_children_disjoint x)))
      ((measurableSet_cantorCylinder _).prod hB)
  have hle : ∀ x : BitString, (P (cantorCylinder x ×ˢ A)).toReal
      ≤ (P (cantorCylinder x ×ˢ Set.univ)).toReal := fun x =>
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (Set.prod_mono le_rfl (Set.subset_univ _)))
  have hkey : ∀ x : BitString, condSecond P A x * (P (cantorCylinder x ×ˢ Set.univ)).toReal
      = (P (cantorCylinder x ×ˢ A)).toReal := by
    intro x
    unfold condSecond
    by_cases hd : (P (cantorCylinder x ×ˢ Set.univ)).toReal = 0
    · have := hle x
      have hn : (P (cantorCylinder x ×ˢ A)).toReal = 0 :=
        le_antisymm (hd ▸ this) ENNReal.toReal_nonneg
      rw [hd, hn, mul_zero]
    · field_simp
  refine ⟨⟨fun x => ?_, fun x => ?_⟩, fun x => ?_⟩
  · unfold condSecond
    positivity
  · rw [hmass, hmass, hmass, hkey, hkey, hkey]
    exact hadd A hA x
  · unfold condSecond
    by_cases hd : (P (cantorCylinder x ×ˢ Set.univ)).toReal = 0
    · rw [hd, div_zero]; exact zero_le_one
    · exact div_le_one_of_le₀ (hle x) ENNReal.toReal_nonneg

/-- Step 2 of the proof of `ae_exists_tendsto_condSecond`: shifted martingale. -/
private theorem ae_exists_tendsto_condSecond_shifted_martingale
    (P : Measure (CantorSeq × CantorSeq)) [IsProbabilityMeasure P]
    {A : Set CantorSeq} (hA : MeasurableSet A) :
    IsMartingale (P.map Prod.fst)
      (fun x => condSecond P A x + (1 - condSecond P A [])) := by
  obtain ⟨hF, hle⟩ := ae_exists_tendsto_condSecond_fair P hA
  have hs : 0 ≤ 1 - condSecond P A [] := sub_nonneg.mpr (hle [])
  have hfin : ∀ y, cantorMass (P.map Prod.fst) y ≠ ∞ := fun y => measure_ne_top _ _
  have hadd : ∀ x, massR (P.map Prod.fst) x =
      massR (P.map Prod.fst) (x ++ [false]) + massR (P.map Prod.fst) (x ++ [true]) := by
    intro x
    unfold massR
    rw [cantorMass_add (P.map Prod.fst) x, ENNReal.toReal_add (hfin _) (hfin _)]
  refine ⟨⟨fun x => add_nonneg (hF.nonneg x) hs, fun x => ?_⟩, by simp⟩
  have h := hF.fair x
  have h2 := hadd x
  linear_combination h + (1 - condSecond P A []) * h2

/-- Step 3 of the proof of `ae_exists_tendsto_condSecond`: limit transfer. -/
private theorem ae_exists_tendsto_condSecond_limit_of_shifted
    (P : Measure (CantorSeq × CantorSeq)) {A : Set CantorSeq}
    (α : CantorSeq)
    (h : HasFiniteLimit
      (fun x => condSecond P A x + (1 - condSecond P A [])) α) :
    ∃ L, Tendsto (fun n => condSecond P A (cantorPrefix α n)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L - (1 - condSecond P A []), by simpa using hL.sub_const (1 - condSecond P A [])⟩

/-- **SUV p. 275.**  Conditional probabilities through Doob's theorem: for a measure on `Ω × Ω`
and measurable `A`, for almost every first coordinate `α` the conditional probabilities of `A` given
the prefixes of `α` have a limit. -/
theorem ae_exists_tendsto_condSecond (P : Measure (CantorSeq × CantorSeq))
    [IsProbabilityMeasure P] {A : Set CantorSeq} (hA : MeasurableSet A) :
    ∀ᵐ α ∂(P.map Prod.fst), ∃ L,
      Tendsto (fun n => condSecond P A (cantorPrefix α n)) atTop (𝓝 L) := by
  have h_doob := measure_not_hasFiniteLimit_eq_zero
      (ae_exists_tendsto_condSecond_shifted_martingale P hA)
  rw [ae_iff]
  apply measure_mono_null _ h_doob
  intro α h_not
  change ¬ (HasFiniteLimit (fun x => condSecond P A x + (1 - condSecond P A [])) α)
  intro h_lim
  apply h_not
  exact ae_exists_tendsto_condSecond_limit_of_shifted P α h_lim


/-! ### A sequence on which a martingale does not win -/

/-- The mass of a cylinder is the sum of the masses of its two children, as real numbers. -/
lemma massR_add {π : Measure CantorSeq} [IsProbabilityMeasure π] (x : BitString) :
    massR π x = massR π (x ++ [false]) + massR π (x ++ [true]) := by
  have hne : ∀ y, cantorMass π y ≠ ∞ := fun y => measure_ne_top π _
  simp only [massR]
  rw [cantorMass_add π x, ENNReal.toReal_add (hne _) (hne _)]

/-- From a history of positive mass, some child of positive mass does not increase the capital. -/
lemma exists_child_le {π : Measure CantorSeq} [IsProbabilityMeasure π] {m : BitString → ℝ}
    (hm : IsSuperfairCapital π m) {x : BitString} (hx : 0 < massR π x) :
    ∃ b, 0 < massR π (x ++ [b]) ∧ m (x ++ [b]) ≤ m x := by
  by_contra hcon
  push Not at hcon
  have hadd := massR_add (π := π) x
  have hs := hm.superfair x
  have hnn : ∀ y, 0 ≤ massR π y := fun y => ENNReal.toReal_nonneg
  have h0 := hnn (x ++ [false])
  have h1 := hnn (x ++ [true])
  rw [hadd] at hs
  rcases h0.eq_or_lt with h0' | h0'
  · have hpos1 : 0 < massR π (x ++ [true]) := by rw [← h0'] at hadd; linarith
    have hlt := mul_pos (sub_pos.mpr (hcon true hpos1)) hpos1
    rw [← h0'] at hs
    nlinarith
  · have hlt0 := mul_pos (sub_pos.mpr (hcon false h0')) h0'
    rcases h1.eq_or_lt with h1' | h1'
    · rw [← h1'] at hs
      nlinarith
    · have hlt1 := mul_pos (sub_pos.mpr (hcon true h1')) h1'
      nlinarith

open Classical in
/-- The history built by always moving to a child of positive mass not increasing the capital. -/
noncomputable def lowHistory (π : Measure CantorSeq) (m : BitString → ℝ) : ℕ → BitString
  | 0 => []
  | n + 1 =>
    let x := lowHistory π m n
    x ++ [if 0 < massR π (x ++ [true]) ∧ m (x ++ [true]) ≤ m x then true else false]

/-- **SUV Theorem 180, p. 275.**  For every `π`-martingale there is a sequence on which it is
bounded by `1` on all prefixes, and so does not win.  The book states this after introducing general
`π`; the proof goes through cylinders of positive mass, so it covers measures with null cylinders
too. -/
theorem exists_forall_prefix_le_one {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsMartingale π m) :
    ∃ w, (∀ n, m (cantorPrefix w n) ≤ 1) ∧ ¬ Wins m w := by
  have hsuper := hm.toIsFairCapital.isSuperfairCapital
  have hinv : ∀ n, 0 < massR π (lowHistory π m n) ∧ m (lowHistory π m n) ≤ 1 := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, hm.init.le⟩
      have hroot : cantorMass π [] = 1 := by
        have : cantorCylinder [] = Set.univ := by
          ext w; simp [cantorCylinder, IsCantorPrefix]
        simp [cantorMass, this]
      simp [lowHistory, massR, hroot]
    | succ n ih =>
      obtain ⟨b, hb, hle⟩ := exists_child_le hsuper ih.1
      simp only [lowHistory]
      split_ifs with h
      · exact ⟨h.1, h.2.trans ih.2⟩
      · cases b with
        | true => exact absurd ⟨hb, hle⟩ h
        | false => exact ⟨hb, hle.trans ih.2⟩
  -- The sequence reads off the last bit of each history.
  let w : CantorSeq := fun n => decide (0 < massR π (lowHistory π m n ++ [true]) ∧
    m (lowHistory π m n ++ [true]) ≤ m (lowHistory π m n))
  have hprefix : ∀ n, cantorPrefix w n = lowHistory π m n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [cantorPrefix_succ, ih]
      simp only [lowHistory, w]
      congr 2
      split_ifs with h <;> simp [h]
  have hle : ∀ n, m (cantorPrefix w n) ≤ 1 := fun n => by
    rw [hprefix]
    exact (hinv n).2
  refine ⟨w, hle, fun hwin => hwin ⟨1, ?_⟩⟩
  rintro _ ⟨n, rfl⟩
  exact hle n

end Kolmogorov.FrequencyGames
