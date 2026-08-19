import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems

/-!
# Budget-scale stochasticity bookkeeping

The remaining S4 obligation `BudgetedRandomNoiseTransportStatement` measures all
logarithmic overhead against the *visible complexity budget* `baseBudget`
(`plainK V x ≤ baseBudget`), never against the length `l(x)` or against the
stochasticity parameters `alpha, beta`.  The proved §3 route
(`stochastic_to_plain_profile_corner`) instead produces slack
`logSlack c (l(x) + alpha + beta)`.

This module collects the *budget-scale* pieces of that comparison which can be
proved outright:

* `setComplexity_singleton_le_KPPlain_add_const` /
  `plainSetComplexity_singleton_le_plainK_add_const`: the canonical code of a
  singleton costs only an additive constant over the element itself — the
  length-free form of the singleton gate.
* `inPlainDescriptionProfile_singleton_of_plainK`: the plain `(C(x)+O(1), 0)`
  corner of any string.
* `isStochastic_dirac_of_plainK`: every `x` is `(C(x) + O(log C(x)), 0)`-stochastic.
* `isStochastic_alpha_le_budget`: **the `alpha` reduction.**  A stochasticity
  witness can always be replaced by one whose complexity parameter is at most
  `baseBudget + O(log baseBudget)`; so in any budgeted statement one may assume
  `alpha ≤ baseBudget + O(log baseBudget)` for free.
* `levelSet_level_bound_of_KPPlain_le`: the level bound of a dyadic bracket at
  the *complexity* scale, `k ≤ K(x) + beta + O(1)`, strengthening
  `levelSet_level_bound` (which pays `l(x) + beta + O(log l(x))`).
* `exists_uniform_witness_of_isStochastic_budget`: the model-to-uniform-set
  bridge with slack `logSlack c (K(x) + beta)` — neither `l(x)` nor `alpha`
  occurs any more.
* `stochastic_to_plain_profile_corner_alpha_free`: the forward plain corner with
  the `alpha`-dependence of the slack replaced by the visible budget.
* `budgeted_stochasticity_to_plain_corner_of_length_le`: the budgeted forward
  corner in the regime where the length and the deficiency parameter are
  themselves within the budget.  The `alpha` parameter needs no such hypothesis,
  thanks to the reduction above.

Nothing here weakens or replaces a frozen interface; these are additional
lemmas.  The genuinely open part of the budgeted corner is the regime
`l(x) > baseBudget` or `beta > baseBudget`, where the level of `x` inside its
own witness can be a complex number whose description does not fit into
`logSlack c baseBudget`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution
open scoped ENNReal

/-- **Length-free singleton gate (prefix form).**  The canonical uniform code of
`{x}` has plain prefix complexity at most `KPPlain U x + O(1)`.  This is
`singletonSetComplexityGate` with the `logSlack c (l x)` overhead replaced by an
additive constant. -/
theorem setComplexity_singleton_le_KPPlain_add_const
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString,
      setComplexity U {x} (Finset.singleton_nonempty x) ≤ KPPlain U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU (fun x => canonicalUniformCodeOfList [x])
    (canonicalUniformCodeOfList_computable.comp
      (Computable.list_cons.comp Computable.id (Computable.const [])))
  refine ⟨c, fun x => ?_⟩
  have hcode : (codedUniformOn {x} (Finset.singleton_nonempty x)).code
      = canonicalUniformCodeOfList [x] := by
    rw [← canonicalUniformCodeOfList_canonicalFinsetList {x} (Finset.singleton_nonempty x)]
    unfold canonicalFinsetList
    aesop
  change KPPlain U (codedUniformOn {x} (Finset.singleton_nonempty x)).code ≤ _
  rw [hcode]
  exact hc x

/-- **Length-free singleton gate (ordinary plain form).** -/
theorem plainSetComplexity_singleton_le_plainK_add_const
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString,
      plainSetComplexity V {x} (Finset.singleton_nonempty x) ≤ plainK V x + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainK_partrec_map_le V hV
    (fun x => Part.some (canonicalUniformCodeOfList [x]))
    ((canonicalUniformCodeOfList_computable.comp
      (Computable.list_cons.comp Computable.id (Computable.const []))).partrec)
  refine ⟨c, fun x => ?_⟩
  have hcode : (codedUniformOn {x} (Finset.singleton_nonempty x)).code
      = canonicalUniformCodeOfList [x] := by
    rw [← canonicalUniformCodeOfList_canonicalFinsetList {x} (Finset.singleton_nonempty x)]
    unfold canonicalFinsetList
    aesop
  change plainK V (codedUniformOn {x} (Finset.singleton_nonempty x)).code ≤ _
  rw [hcode]
  exact hc x _ (Part.mem_some _)

/-- **The singleton plain corner.**  Every string has an ordinary plain
`(C(x) + O(1), 0)` description profile point. -/
theorem inPlainDescriptionProfile_singleton_of_plainK
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (kx : ℕ),
      plainK V x = (kx : ENat) → InPlainDescriptionProfile V x (kx + c) 0 := by
  obtain ⟨c, hc⟩ := plainSetComplexity_singleton_le_plainK_add_const V hV
  refine ⟨c, fun x kx hkx => ?_⟩
  refine ⟨{x}, Finset.singleton_nonempty x, Finset.mem_singleton_self x, ?_, ?_⟩
  · have h := hc x
    rw [hkx] at h
    refine h.trans ?_
    push_cast
    exact le_rfl
  · simp

/-- **Budget-scale corner in the singleton regime.**  If the allowed model
complexity `alpha` already reaches `C(x)`, the canonical singleton description
has the required two-part sum, independently of the string length and of
`beta`. -/
theorem budgeted_plain_corner_of_kx_le_alpha
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ alpha →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨c, hc⟩ := inPlainDescriptionProfile_singleton_of_plainK V hV
  refine ⟨c, fun x kx baseBudget alpha beta hkx hkxAlpha => ?_⟩
  have hcSlack : c ≤ logSlack c baseBudget := by
    unfold logSlack
    omega
  exact ⟨kx + c, 0, hc x kx hkx, by omega, by omega⟩

/-- **Dirac stochasticity at the complexity budget.**  Every `x` is
`(C(x) + O(log C(x)), 0)`-stochastic: the uniform model on `{x}` has zero
randomness deficiency, and its code costs `C(x) + O(log C(x))` prefix bits. -/
theorem isStochastic_dirac_of_plainK
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx : ℕ),
      plainK V x = (kx : ENat) → IsStochastic U x (kx + logSlack c kx) 0 := by
  obtain ⟨cS, hS⟩ := setComplexity_singleton_le_KPPlain_add_const U hU
  obtain ⟨cKP, hKP⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨2 + cBits + cKP + cS, fun x kx hkx => ?_⟩
  set c := 2 + cBits + cKP + cS with hc
  have hcomp :
      setComplexity U {x} (Finset.singleton_nonempty x) ≤ ((kx + logSlack c kx : ℕ) : ENat) := by
    refine (hS x).trans ?_
    have hchain : KPPlain U x ≤ ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) := by
      calc
        KPPlain U x ≤ (kx : ENat) + KPPlain U (Nat.bits kx) + (cKP : ENat) := hKP x kx hkx
        _ ≤ (kx : ENat) + ((2 * (Nat.bits kx).length + cBits : ℕ) : ENat) + (cKP : ENat) := by
              gcongr
              exact hBits (Nat.bits kx)
        _ = ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) := by push_cast; ring
    refine le_trans (by gcongr : KPPlain U x + (cS : ENat) ≤
        ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) + (cS : ENat)) ?_
    have harith : kx + 2 * (Nat.bits kx).length + cBits + cKP + cS ≤ kx + logSlack c kx := by
      unfold logSlack
      have : 2 * (Nat.bits kx).length ≤ c * (Nat.bits kx).length := by
        exact Nat.mul_le_mul_right _ (by omega)
      omega
    exact_mod_cast harith
  refine isStochastic_of_model U x (codedUniformOn {x} (Finset.singleton_nonempty x))
    (kx + logSlack c kx) 0 (codedUniformOn_isProbability _ _) hcomp ?_
  refine deficiencyLe_zero_of_mass_one U _ x ?_
  rw [codedUniformOn_mass_of_mem _ _ _ (Finset.mem_singleton_self x)]
  simp

/-- **The `alpha` reduction for budgeted statements.**  If `plainK V x` fits in
the visible budget, then any `(alpha, beta)`-stochasticity witness may be
replaced by one whose complexity parameter is capped at
`baseBudget + O(log baseBudget)`: for larger `alpha` the singleton model is
already available and has zero deficiency.

Consequently no budgeted statement needs an `alpha`-dependent slack: one may
always assume `alpha ≤ baseBudget + logSlack c baseBudget`. -/
theorem isStochastic_alpha_le_budget
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      IsStochastic U x alpha beta →
      IsStochastic U x (min alpha (baseBudget + logSlack c baseBudget)) beta := by
  obtain ⟨c, hc⟩ := isStochastic_dirac_of_plainK V U hV hU
  refine ⟨c, fun x kx baseBudget alpha beta hkx hkxB hstoch => ?_⟩
  rcases le_total alpha (baseBudget + logSlack c baseBudget) with hle | hge
  · rw [min_eq_left hle]
    exact hstoch
  · rw [min_eq_right hge]
    refine IsStochastic.mono_beta (Nat.zero_le beta) (IsStochastic.mono_alpha ?_ (hc x kx hkx))
    have hslack : logSlack c kx ≤ logSlack c baseBudget := logSlack_mono_right c hkxB
    omega

/-- **Level bound at the complexity scale.**  If `k` dyadically over-brackets the
mass of `x` under `P` and the randomness deficiency of `x` under `P` is at most
`beta`, then `k ≤ K(x) + beta + O(1)`.

This strengthens `levelSet_level_bound`, whose bound `k ≤ l(x) + beta +
O(log l(x))` is stated at the length scale: the proof only ever needs an upper
bound for `KP U x P.code`, and any complexity budget `m` for `KPPlain U x`
supplies one. -/
theorem levelSet_level_bound_of_KPPlain_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : CodedFiniteDistribution) (x : BitString) (m beta k : ℕ),
      KPPlain U x ≤ (m : ENat) →
      DeficiencyLe U P x beta →
      P.mass x ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ k →
      k ≤ m + beta + c := by
  obtain ⟨c₁, hc₁⟩ := KP_le_KPPlain U hU
  refine ⟨c₁ + 1, ?_⟩
  intro P x m beta k hm hdef hub
  set M := m + c₁ with hM_def
  have hM : KP U x P.code ≤ (M : ENat) := by
    refine (hc₁ x P.code).trans ?_
    rw [hM_def]
    push_cast
    gcongr
  have h1 : (2 : ℝ≥0∞)⁻¹ ^ M ≤ (2 : ℝ≥0∞) ^ beta * P.mass x := by
    refine le_trans ?_ hdef
    rw [← complexityWeight_coe]
    exact complexityWeight_le_of_le hM
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ M ≤ (2 : ℝ≥0∞) ^ beta * (2 * (2 : ℝ≥0∞)⁻¹ ^ k) :=
    h1.trans (by gcongr)
  have hkle : k ≤ M + beta + 1 := by
    by_contra hcon
    push Not at hcon
    have hpow : (2 : ℝ≥0∞)⁻¹ ^ k ≤ (2 : ℝ≥0∞)⁻¹ ^ (M + beta + 2) :=
      pow_le_pow_right_of_le_one' (by norm_num) (by omega)
    have hcancel : ((2 : ℝ≥0∞) ^ (beta + 1)) * ((2 : ℝ≥0∞)⁻¹ ^ (beta + 1)) = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    have hstep : (2 : ℝ≥0∞) ^ beta * (2 * (2 : ℝ≥0∞)⁻¹ ^ k) ≤ (2 : ℝ≥0∞)⁻¹ ^ M * 2⁻¹ := by
      calc (2 : ℝ≥0∞) ^ beta * (2 * (2 : ℝ≥0∞)⁻¹ ^ k)
          ≤ (2 : ℝ≥0∞) ^ beta * (2 * (2 : ℝ≥0∞)⁻¹ ^ (M + beta + 2)) := by gcongr
        _ = ((2 : ℝ≥0∞) ^ (beta + 1) * (2 : ℝ≥0∞)⁻¹ ^ (beta + 1)) *
              ((2 : ℝ≥0∞)⁻¹ ^ M * 2⁻¹) := by
              rw [show M + beta + 2 = (beta + 1) + (M + 1) by ring, pow_add, pow_succ, pow_succ]
              ring
        _ = (2 : ℝ≥0∞)⁻¹ ^ M * 2⁻¹ := by rw [hcancel, one_mul]
    have hfin : (2 : ℝ≥0∞)⁻¹ ^ M ≤ (2 : ℝ≥0∞)⁻¹ ^ M * 2⁻¹ := h2.trans hstep
    have hne0 : (2 : ℝ≥0∞)⁻¹ ^ M ≠ 0 := by simp
    have hnetop : (2 : ℝ≥0∞)⁻¹ ^ M ≠ ⊤ := by simp
    have hlt : (2 : ℝ≥0∞)⁻¹ ^ M * 2⁻¹ < (2 : ℝ≥0∞)⁻¹ ^ M := by
      rw [mul_comm, ← ENNReal.div_eq_inv_mul]
      exact ENNReal.half_lt_self hne0 hnetop
    exact absurd hfin (not_le.mpr hlt)
  omega

/-- **Budget-scale uniform-witness bridge.**  Every `(alpha, beta)`-stochasticity
witness for `x` is matched by a *uniform finite-set* witness `A ∋ x` with

* `setComplexity U A ≤ alpha + logSlack c (m + beta)`,
* randomness deficiency at most `beta + logSlack c (m + beta)`,
* `A.card ≤ 2 ^ (m + beta + c)`,

where `m` is any complexity budget for `x` (`KPPlain U x ≤ m`).

This strengthens `exists_uniform_witness_of_isStochastic`, whose slack
`logSlack C (l(x) + alpha + beta)` is measured at the length scale and grows
with `alpha`: the level of `x` inside its own witness is controlled by
`levelSet_level_bound_of_KPPlain_le` at the complexity scale, and the level-set
complexity/deficiency gates only ever pay `O(log k)`.  The residual `beta`
inside the slack is genuine: the level itself can be as large as `K(x) + beta`. -/
theorem exists_uniform_witness_of_isStochastic_budget
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (m alpha beta : ℕ),
      KPPlain U x ≤ (m : ENat) →
      IsStochastic U x alpha beta →
      ∃ (A : Finset BitString) (hA : A.Nonempty), x ∈ A ∧
        setComplexity U A hA ≤ ((alpha + logSlack c (m + beta) : ℕ) : ENat) ∧
        DeficiencyLe U (codedUniformOn A hA) x (beta + logSlack c (m + beta)) ∧
        A.card ≤ 2 ^ (m + beta + c) := by
  obtain ⟨cL, hL⟩ := levelSet_level_bound_of_KPPlain_le U hU
  obtain ⟨cC, hC⟩ := levelSetModel_setComplexity_le U hU
  obtain ⟨cG, hG⟩ := levelSet_randomness_deficiency_le_gate U hU
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound (cC + cG) 1 cL
  refine ⟨cL + cFold, ?_⟩
  intro x m alpha beta hm hstoch
  obtain ⟨P, hprob, hcomp, hdef⟩ := hstoch
  have hmass_pos : P.mass x > 0 :=
    mass_pos_of_deficiencyLe_of_KP_ne_top hdef (KP_ne_top_of_optimal U hU x P.code)
  have hmass_le1 : P.mass x ≤ 1 := mass_le_one_of_isProbability P hprob x
  obtain ⟨k, hk_lower, hk_upper⟩ := exists_k_mass P x hmass_pos hmass_le1
  have hsupp : x ∈ P.support := by
    by_contra hx
    exact absurd (CodedFiniteDistribution.mass_eq_zero_of_not_mem_support P x hx)
      (ne_of_gt hmass_pos)
  have hkbound : k ≤ m + beta + cL := hL P x m beta k hm hdef hk_upper
  set A := levelSet P k with hA_def
  have hA : A.Nonempty := levelSet_nonempty_of_mass_ge P x k hsupp hk_lower
  have hxA : x ∈ A := mem_levelSet hsupp hk_lower
  obtain ⟨d, hd_def, hd_le⟩ := hG P x k hprob hsupp hk_lower hk_upper beta hdef
  have hslackfold : ∀ cc : ℕ, cc ≤ cC + cG →
      logSlack cc k ≤ logSlack cFold (m + beta) := by
    intro cc hcc
    calc logSlack cc k ≤ logSlack (cC + cG) k := logSlack_mono_left hcc k
      _ ≤ logSlack (cC + cG) (1 * (m + beta) + cL) := by
          refine logSlack_mono_right _ ?_
          omega
      _ ≤ logSlack cFold (m + beta) := hFold (m + beta)
  refine ⟨A, hA, hxA, ?_, ?_, ?_⟩
  · refine (hC P k hA).trans ?_
    have h2 : logSlack cC k ≤ logSlack (cL + cFold) (m + beta) :=
      (hslackfold cC (by omega)).trans (logSlack_mono_left (by omega) _)
    calc P.complexity U + (logSlack cC k : ENat)
        ≤ (alpha : ENat) + ((logSlack (cL + cFold) (m + beta) : ℕ) : ENat) := by gcongr
      _ = ((alpha + logSlack (cL + cFold) (m + beta) : ℕ) : ENat) := by push_cast; ring
  · refine DeficiencyLe.mono_beta ?_ hd_def
    have h2 : logSlack cG k ≤ logSlack (cL + cFold) (m + beta) :=
      (hslackfold cG (by omega)).trans (logSlack_mono_left (by omega) _)
    omega
  · have hcard : ((levelSet P k).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ k := levelSet_card_le P k hprob
    have hcard' : (levelSet P k).card ≤ 2 ^ k := by exact_mod_cast hcard
    calc A.card ≤ 2 ^ k := hcard'
      _ ≤ 2 ^ (m + beta + (cL + cFold)) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The forward plain corner from stochasticity (§3 chain).**  A stochasticity
witness `(alpha, beta)` for `x` yields an ordinary *plain* `(i, j)` description
with `i ≤ alpha + O(log)` and two-part sum `i + j ≤ C(x) + beta + O(log)`, the
slack measured against `l(x) + alpha + beta`.

Proof: cap the complexity budget by the `alpha`-reduction
(`isStochastic_alpha_le_budget`), convert to an optimal finite-set model
(`stochasticity_to_optimal_set_thm`), extract a prefix description profile point
at the tight size coordinate `j = K(x) + beta - alpha`
(`isOptimalSetStochastic_imp_profile`), and transport it to the ordinary plain
profile (`inPlainDescriptionProfile_of_inDescriptionProfile`).  The
`alpha`-reduction is what keeps the two-part sum tracking `C(x) + beta` rather
than an arbitrarily large `alpha`. -/
theorem stochastic_to_plain_profile_corner
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c (x.length + alpha + beta) ∧
        i + j ≤ kx + beta + logSlack c (x.length + alpha + beta) := by
  obtain ⟨cR, hR⟩ := isStochastic_alpha_le_budget V U hV hU
  obtain ⟨cOpt, hOpt⟩ := stochasticity_to_optimal_set_thm U hU
  obtain ⟨cProf, hProf⟩ := isOptimalSetStochastic_imp_profile U hU
  obtain ⟨cBr, hBr⟩ := inPlainDescriptionProfile_of_inDescriptionProfile V U hV hU
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cKP, hKP⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨bOpt, hbOpt⟩ := logSlack_le_add_const cOpt
  obtain ⟨CR, hCR⟩ := logSlack_linear_bound cR 1 cLen
  obtain ⟨C2, hC2⟩ := logSlack_linear_bound 2 1 cLen
  set bTotal := 3 * bOpt + 3 * cLen + cBits + cKP with hbTotal
  obtain ⟨CProf, hCProf⟩ := logSlack_linear_bound cProf 9 bTotal
  set C := CR + cOpt + C2 + CProf + cBits + cKP + cBr + 1 with hCdef
  refine ⟨C, fun x kx alpha beta hkx hstoch => ?_⟩
  set M := x.length + alpha + beta with hM
  -- `alpha`-reduction: cap the complexity budget at `kx + O(log kx)`.
  have hstoch'' : IsStochastic U x (min alpha (kx + logSlack cR kx)) beta :=
    hR x kx kx alpha beta hkx (le_refl kx) hstoch
  set alpha'' := min alpha (kx + logSlack cR kx) with halpha''
  have halpha''_le : alpha'' ≤ alpha := by rw [halpha'']; exact min_le_left _ _
  have halpha''_bud : alpha'' ≤ kx + logSlack cR kx := by rw [halpha'']; exact min_le_right _ _
  -- optimal finite-set model.
  have hopt : IsOptimalSetStochastic U x
      (alpha'' + logSlack cOpt (x.length + alpha'' + beta))
      (beta + logSlack cOpt (x.length + alpha'' + beta)) :=
    hOpt x x.length alpha'' beta rfl hstoch''
  set sOpt := logSlack cOpt (x.length + alpha'' + beta) with hsOpt
  set A1 := alpha'' + sOpt with hA1
  set B1 := beta + sOpt with hB1
  -- prefix complexity value of `x`.
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp (KPPlain_ne_top_of_optimal U hU x)
  set j := (p + B1) - A1 with hj
  have harith : KPPlain U x + (B1 : ENat) ≤ (A1 : ENat) + (j : ENat) := by
    rw [← hp]
    have hnat : p + B1 ≤ A1 + j := by omega
    exact_mod_cast hnat
  have hprofU : InDescriptionProfile U x (A1 + logSlack cProf (A1 + B1 + j)) (j + 1) :=
    hProf x A1 B1 j hopt harith
  set iPre := A1 + logSlack cProf (A1 + B1 + j) with hiPre
  have hplain : InPlainDescriptionProfile V x (iPre + cBr) (j + 1) :=
    hBr x iPre (j + 1) hprofU
  -- length / complexity budgets.
  have hkxM : kx ≤ x.length + cLen := by
    have h := hLen x; rw [hkx] at h; exact_mod_cast h
  have hp_bd : p ≤ kx + 2 * (Nat.bits kx).length + cBits + cKP := by
    have h3 : (p : ENat) ≤ ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) := by
      calc (p : ENat) = KPPlain U x := hp
        _ ≤ (kx : ENat) + KPPlain U (Nat.bits kx) + (cKP : ENat) := hKP x kx hkx
        _ ≤ (kx : ENat) + ((2 * (Nat.bits kx).length + cBits : ℕ) : ENat) + (cKP : ENat) := by
              gcongr; exact hBits (Nat.bits kx)
        _ = ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) := by push_cast; ring
    exact_mod_cast h3
  have hbits_self : (Nat.bits kx).length ≤ kx := length_natBits_le_self kx
  -- slack conversions to the visible budget `M`.
  have hsOptM : sOpt ≤ logSlack cOpt M := by
    rw [hsOpt]; exact logSlack_mono_right cOpt (by omega)
  have hsOpt_ac : sOpt ≤ M + bOpt := hsOptM.trans (hbOpt M)
  have hcR_le : logSlack cR kx ≤ logSlack CR M :=
    (logSlack_mono_right cR (by omega : kx ≤ 1 * M + cLen)).trans (hCR M)
  have hbits_le : 2 * (Nat.bits kx).length ≤ logSlack C2 M := by
    have h1 : 2 * (Nat.bits kx).length ≤ logSlack 2 kx := by unfold logSlack; omega
    exact h1.trans ((logSlack_mono_right 2 (by omega : kx ≤ 1 * M + cLen)).trans (hC2 M))
  have hABj : A1 + B1 + j ≤ 9 * M + bTotal := by omega
  have hcprof_le : logSlack cProf (A1 + B1 + j) ≤ logSlack CProf M :=
    (logSlack_mono_right cProf hABj).trans (hCProf M)
  have hMasterA : logSlack cOpt M + logSlack CProf M + cBr ≤ logSlack C M := by
    calc logSlack cOpt M + logSlack CProf M + cBr
        = logSlack (cOpt + CProf) M + cBr := by rw [logSlack_add_const]
      _ ≤ logSlack (cOpt + CProf + cBr) M := logSlack_add_nat_le _ _ _
      _ ≤ logSlack C M := logSlack_mono_left (by omega) M
  have hMaster : logSlack CR M + logSlack cOpt M + logSlack C2 M + logSlack CProf M
        + (cBits + cKP + cBr + 1) ≤ logSlack C M := by
    calc logSlack CR M + logSlack cOpt M + logSlack C2 M + logSlack CProf M
            + (cBits + cKP + cBr + 1)
        = logSlack (CR + cOpt) M + logSlack C2 M + logSlack CProf M
            + (cBits + cKP + cBr + 1) := by rw [logSlack_add_const]
      _ = logSlack (CR + cOpt + C2) M + logSlack CProf M + (cBits + cKP + cBr + 1) := by
          rw [logSlack_add_const]
      _ = logSlack (CR + cOpt + C2 + CProf) M + (cBits + cKP + cBr + 1) := by
          rw [logSlack_add_const]
      _ ≤ logSlack (CR + cOpt + C2 + CProf + (cBits + cKP + cBr + 1)) M :=
          logSlack_add_nat_le _ _ _
      _ ≤ logSlack C M := logSlack_mono_left (by omega) M
  refine ⟨iPre + cBr, j + 1, hplain, ?_, ?_⟩
  · omega
  · omega

/-- **The forward plain corner with an `alpha`-free slack.**  Same conclusion as
`stochastic_to_plain_profile_corner`, but the slack is measured against the
visible budget `baseBudget` instead of the stochasticity parameter `alpha`,
which may be arbitrarily large.  Immediate from the `alpha` reduction. -/
theorem stochastic_to_plain_profile_corner_alpha_free
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c (x.length + baseBudget + beta) ∧
        i + j ≤ kx + beta + logSlack c (x.length + baseBudget + beta) := by
  obtain ⟨cR, hR⟩ := isStochastic_alpha_le_budget V U hV hU
  obtain ⟨cF, hF⟩ := stochastic_to_plain_profile_corner V U hV hU
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cF (1 + cR) cR
  refine ⟨cFold, fun x kx baseBudget alpha beta hkx hkxB hstoch => ?_⟩
  set alpha' := min alpha (baseBudget + logSlack cR baseBudget) with halpha'
  have hstoch' : IsStochastic U x alpha' beta := hR x kx baseBudget alpha beta hkx hkxB hstoch
  obtain ⟨i, j, hprof, hi, hij⟩ := hF x kx alpha' beta hkx hstoch'
  have halphaB : alpha' ≤ baseBudget + logSlack cR baseBudget := min_le_right _ _
  have halphale : alpha' ≤ alpha := min_le_left _ _
  have hlinear : logSlack cR baseBudget ≤ cR * baseBudget + cR := by
    unfold logSlack
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left cR (length_natBits_le_self baseBudget)) cR
  have hM : x.length + alpha' + beta ≤ (1 + cR) * (x.length + baseBudget + beta) + cR := by
    nlinarith [Nat.zero_le baseBudget, Nat.zero_le x.length, Nat.zero_le beta]
  have hslack : logSlack cF (x.length + alpha' + beta) ≤
      logSlack cFold (x.length + baseBudget + beta) :=
    (logSlack_mono_right cF hM).trans (hFold (x.length + baseBudget + beta))
  exact ⟨i, j, hprof, by omega, by omega⟩

/-- **The budgeted forward corner, in the regime where length and deficiency fit
the budget.**  An `(alpha, beta)`-stochasticity witness for `x` yields an
ordinary plain `(i, j)` description with the *budget-scale* slack
`logSlack c baseBudget`:

* `i ≤ alpha + logSlack c baseBudget`,
* `i + j ≤ C(x) + beta + logSlack c baseBudget`.

No hypothesis on `alpha` is needed (it is removed by
`isStochastic_alpha_le_budget`); the hypotheses `l(x) ≤ baseBudget` and
`beta ≤ baseBudget` delimit exactly the regime where the proved corner
`stochastic_to_plain_profile_corner` (whose slack is
`logSlack c (l(x) + alpha + beta)`) can be folded into the visible budget. -/
theorem budgeted_stochasticity_to_plain_corner_of_length_le
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      x.length ≤ baseBudget →
      beta ≤ baseBudget →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨cR, hR⟩ := isStochastic_alpha_le_budget V U hV hU
  obtain ⟨cF, hF⟩ := stochastic_to_plain_profile_corner V U hV hU
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cF (3 + cR) cR
  refine ⟨cFold, fun x kx baseBudget alpha beta hkx hkxB hlenB hbetaB hstoch => ?_⟩
  set alpha' := min alpha (baseBudget + logSlack cR baseBudget) with halpha'
  have hstoch' : IsStochastic U x alpha' beta := hR x kx baseBudget alpha beta hkx hkxB hstoch
  obtain ⟨i, j, hprof, hi, hij⟩ := hF x kx alpha' beta hkx hstoch'
  have halphaB : alpha' ≤ baseBudget + logSlack cR baseBudget := min_le_right _ _
  have halphale : alpha' ≤ alpha := min_le_left _ _
  have hlinear : logSlack cR baseBudget ≤ cR * baseBudget + cR := by
    unfold logSlack
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left cR (length_natBits_le_self baseBudget)) cR
  have hM : x.length + alpha' + beta ≤ (3 + cR) * baseBudget + cR := by
    have : alpha' ≤ baseBudget + (cR * baseBudget + cR) := by omega
    nlinarith [Nat.zero_le baseBudget]
  have hslack : logSlack cF (x.length + alpha' + beta) ≤ logSlack cFold baseBudget :=
    (logSlack_mono_right cF hM).trans (hFold baseBudget)
  exact ⟨i, j, hprof, by omega, by omega⟩

end Kolmogorov
