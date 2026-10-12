import KolmogorovMathlib.Solomonoff.SelectedBits.Demand

/-!
# Stage limits and the product lower bound

Along a branch `ω` of a tree `T` decided by an index `e`, the certified demand masses dominate
the universal mass times the limit multipliers of the forced errors (blueprint node L10):

  `ofReal (M(ω_{<n}) * ∏_{i < n} branchTargetFactor G T ω i) ≤ demandMass G q e ω_{<n}`
  (`ofReal_mul_prod_le_demandMass`),

where `branchTargetFactor G T ω i` is `G.target (normalizedError M ω i)` at a forced position
`i` and `1` elsewhere, and `q` is a simple tree approximation of `M`.  The ingredients:

* the rational stages converge to the universal mass (`tendsto_qStage`) and the stage ratios to
  the normalized sibling probabilities (`tendsto_childRatio_qStage`), since all masses of `M`
  are positive and finite;
* the stage factors along the branch (`branchStageFactor`) reach their limit factors in the
  lower-limit sense (`eventually_lt_branchStageFactor`, from `GainFamily.target_liminf`), and a
  finite product of such lower limits is a lower limit of the product
  (`eventually_lt_mul_of_eventually_lt`, `eventually_lt_prod_of_eventually_lt`);
* the certified demand of a word of `T` is eventually its stage demand
  (`eventually_demand_eq_stageDemand`), which along the branch is the stage mass times the
  product of the stage factors (`stageDemand_cantorPrefix`), so it eventually exceeds every
  value below the bound (`eventually_lt_demand_cantorPrefix`).

The logarithmic bridge to the loss is `kappa_mul_partialPowerLoss_le_log_prod`.
-/

namespace Kolmogorov.SelectedBits

open Filter Topology
open scoped ENNReal

/-! ### Normalized errors lie in `[0, 1]` -/

/-- Normalized sibling probabilities are nonnegative. -/
theorem normalizedSiblingProb_nonneg (a : BitString → ℝ≥0∞) (x : BitString) (b : Bool) :
    0 ≤ normalizedSiblingProb a x b :=
  div_nonneg ENNReal.toReal_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- Normalized sibling probabilities are at most `1`. -/
theorem normalizedSiblingProb_le_one (a : BitString → ℝ≥0∞) (x : BitString) (b : Bool) :
    normalizedSiblingProb a x b ≤ 1 := by
  unfold normalizedSiblingProb
  refine div_le_one_of_le₀ ?_ (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  cases b
  · exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  · exact le_add_of_nonneg_left ENNReal.toReal_nonneg

/-- Normalized errors are nonnegative. -/
theorem normalizedError_nonneg (a : BitString → ℝ≥0∞) (ω : CantorSeq) (i : ℕ) :
    0 ≤ normalizedError a ω i :=
  normalizedSiblingProb_nonneg a _ _

/-- Normalized errors are at most `1`. -/
theorem normalizedError_le_one (a : BitString → ℝ≥0∞) (ω : CantorSeq) (i : ℕ) :
    normalizedError a ω i ≤ 1 :=
  normalizedSiblingProb_le_one a _ _

/-! ### Convergence of the stages -/

/-- The rational stages of a simple tree approximation of a finite-valued semimeasure converge to
its real values. -/
theorem tendsto_qStage {a : BitString → ℝ≥0∞} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) (ha : ∀ x, a x ≠ ⊤) (x : BitString) :
    Tendsto (fun s => (qStage q s x : ℝ)) atTop (𝓝 (a x).toReal) := by
  have hmono : Monotone (fun s => dyadicValue (q s x) s) :=
    monotone_nat_of_le_succ fun s => hq.2.2.2.1 s x
  have h1 : Tendsto (fun s => dyadicValue (q s x) s) atTop (𝓝 (a x)) := by
    rw [← hq.2.2.2.2.1 x]
    exact tendsto_atTop_iSup hmono
  have h2 := (ENNReal.tendsto_toReal (ha x)).comp h1
  simpa only [Function.comp_def, cast_qStage] using h2

/-- **Convergence of the stage ratios.**  For a simple tree approximation of a semimeasure with
positive finite values, the stage ratio of the sibling `z ++ [!b]` converges to its normalized
sibling probability.

Proof: `cast_childRatio`, `tendsto_qStage` for both children and `Tendsto.div` with the
positive limit denominator `a (z b) + a (z (!b))` (the order of the sum in
`normalizedSiblingProb` is restored by `cases b`). -/
theorem tendsto_childRatio_qStage {a : BitString → ℝ≥0∞} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) (ha : ∀ x, a x ≠ ⊤) (hpos : ∀ x, 0 < a x)
    (z : BitString) (b : Bool) :
    Tendsto (fun s => (childRatio (qStage q) s z b : ℝ)) atTop
      (𝓝 (normalizedSiblingProb a z (!b))) := by
  have hden : (a (z ++ [b])).toReal + (a (z ++ [!b])).toReal ≠ 0 :=
    (add_pos (ENNReal.toReal_pos (hpos _).ne' (ha _))
      (ENNReal.toReal_pos (hpos _).ne' (ha _))).ne'
  have hlim : normalizedSiblingProb a z (!b) =
      (a (z ++ [!b])).toReal / ((a (z ++ [b])).toReal + (a (z ++ [!b])).toReal) := by
    unfold normalizedSiblingProb
    cases b
    · rfl
    · rw [Bool.not_true, add_comm]
  rw [hlim]
  simp only [cast_childRatio, ratioOf]
  exact (tendsto_qStage hq ha _).div
    ((tendsto_qStage hq ha _).add (tendsto_qStage hq ha _)) hden

/-! ### Lower limits of finite products -/

/-- **A product of two lower limits is a lower limit of the product.**  If nonnegative
sequences `u` and `v` eventually exceed every value below `A ≥ 0` and below `B ≥ 0`
respectively, then `u * v` eventually exceeds every value below `A * B`: for `0 ≤ c < A * B`
choose `c / B < c₁ < A` and use `c = c₁ * (c / c₁)` with `c / c₁ < B`. -/
theorem eventually_lt_mul_of_eventually_lt {u v : ℕ → ℝ} {A B : ℝ} (hu : ∀ s, 0 ≤ u s)
    (hv : ∀ s, 0 ≤ v s) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu' : ∀ c < A, ∀ᶠ s in atTop, c < u s) (hv' : ∀ c < B, ∀ᶠ s in atTop, c < v s) :
    ∀ c < A * B, ∀ᶠ s in atTop, c < u s * v s := by
  intro c hc
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact Filter.Eventually.of_forall fun s => hc0.trans_le (mul_nonneg (hu s) (hv s))
  have hB' : 0 < B := pos_of_mul_pos_right (hc0.trans_lt hc) hA
  have h1 : c / B < A := by rwa [div_lt_iff₀ hB']
  obtain ⟨c₁, hc₁, hc₁A⟩ := exists_between h1
  have hc₁0 : 0 < c₁ := (div_nonneg hc0 hB).trans_lt hc₁
  have h2 : c / c₁ < B := by
    rw [div_lt_iff₀ hB'] at hc₁
    rw [div_lt_iff₀ hc₁0]
    linarith
  filter_upwards [hu' c₁ hc₁A, hv' (c / c₁) h2] with s h1s h2s
  calc c = c₁ * (c / c₁) := (mul_div_cancel₀ c hc₁0.ne').symm
    _ < u s * v s := mul_lt_mul_of_nonneg h1s h2s hc₁0.le (div_nonneg hc0 hc₁0.le)

/-- **A finite product of lower limits is a lower limit of the product.**  If nonnegative
functions `f s i` eventually exceed every value below `L i ≥ 0`, for each `i` in a finite set,
then their product eventually exceeds every value below `∏ L i`.

Proof: induction over the finite set with the two-factor case
`eventually_lt_mul_of_eventually_lt`. -/
theorem eventually_lt_prod_of_eventually_lt {ι : Type*} (I : Finset ι) (f : ℕ → ι → ℝ)
    (L : ι → ℝ) (hf : ∀ s i, 0 ≤ f s i) (hL : ∀ i ∈ I, 0 ≤ L i)
    (h : ∀ i ∈ I, ∀ c < L i, ∀ᶠ s in atTop, c < f s i) :
    ∀ c < ∏ i ∈ I, L i, ∀ᶠ s in atTop, c < ∏ i ∈ I, f s i := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    intro c hc
    simp only [Finset.prod_empty] at hc ⊢
    exact Filter.Eventually.of_forall fun _ => hc
  | @insert j I hj ih =>
    simp only [Finset.prod_insert hj]
    exact eventually_lt_mul_of_eventually_lt (fun s => hf s j)
      (fun s => Finset.prod_nonneg fun i _ => hf s i) (hL j (Finset.mem_insert_self j I))
      (Finset.prod_nonneg fun i hi => hL i (Finset.mem_insert_of_mem hi))
      (h j (Finset.mem_insert_self j I))
      (ih (fun i hi => hL i (Finset.mem_insert_of_mem hi))
        fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### Factors along a branch -/

open Classical in
/-- The stage factor at position `i` of the branch `ω`: the gain at the stage ratio of the
forbidden sibling when the position is forced by `T`, and `1` otherwise. -/
noncomputable def branchStageFactor (G : GainFamily) (T : Set BitString)
    (Ms : ℕ → BitString → ℚ) (ω : CantorSeq) (s i : ℕ) : ℚ :=
  if ForcedPosition T ω i then G.gain s (childRatio Ms s (cantorPrefix ω i) (ω i)) else 1

open Classical in
/-- The limit factor at position `i` of the branch `ω`: the limit multiplier of the normalized
error of the universal semimeasure when the position is forced by `T`, and `1` otherwise. -/
noncomputable def branchTargetFactor (G : GainFamily) (T : Set BitString) (ω : CantorSeq)
    (i : ℕ) : ℝ :=
  if ForcedPosition T ω i then G.target (normalizedError universalContinuousSemimeasure ω i)
  else 1

/-- Every limit factor is at least `1`. -/
theorem one_le_branchTargetFactor (G : GainFamily) (T : Set BitString) (ω : CantorSeq)
    (i : ℕ) : 1 ≤ branchTargetFactor G T ω i := by
  unfold branchTargetFactor
  split_ifs
  · exact G.one_le_target _ (normalizedError_nonneg _ ω i) (normalizedError_le_one _ ω i)
  · exact le_rfl

/-- Every stage factor is at least `1`. -/
theorem one_le_branchStageFactor (G : GainFamily) (T : Set BitString)
    (Ms : ℕ → BitString → ℚ) (ω : CantorSeq) (s i : ℕ) : 1 ≤ branchStageFactor G T Ms ω s i := by
  unfold branchStageFactor
  split_ifs
  · exact G.one_le _ _
  · exact le_rfl

/-- **The stage demand along a branch.**  The stage demand of the prefix `cantorPrefix ω n` of a
branch of `T` is its stage mass times the stage factors of the positions `i < n`: along a
branch the valid child is in `T`, so the sibling test of `nodeFactor` is `ForcedPosition`. -/
theorem stageDemand_cantorPrefix (G : GainFamily) {T : Set BitString}
    (Ms : ℕ → BitString → ℚ) {ω : CantorSeq} (hω : Branch T ω) (s n : ℕ) :
    stageDemand G T Ms s (cantorPrefix ω n) =
      Ms s (cantorPrefix ω n) * ∏ i ∈ Finset.range n, branchStageFactor G T Ms ω s i := by
  rw [stageDemand, ite_eq_left (hω n)]
  congr 1
  rw [forcedGainProd, List.length_nil, cantorPrefix_length, ← Finset.range_eq_Ico]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  have hget : (cantorPrefix ω n).getD i false = ω i := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi')]
    simp
  rw [cantorPrefix_take ω i n hi'.le, hget]
  have hvalid : cantorPrefix ω i ++ [ω i] ∈ T := by
    rw [← Kolmogorov.cantorPrefix_succ]
    exact hω (i + 1)
  unfold nodeFactor branchStageFactor
  by_cases hf : ForcedPosition T ω i
  · rw [ite_eq_left hf, ite_eq_right hf.2]
  · have hsib : cantorPrefix ω i ++ [!ω i] ∈ T := by
      by_contra h
      exact hf ⟨hvalid, h⟩
    rw [ite_eq_right hf, ite_eq_left hsib]

/-- **Lower limit of a stage factor.**  For a simple tree approximation `q` of the universal
semimeasure, the stage factors at every position eventually exceed every value below the limit
factor: at a forced position by `GainFamily.target_liminf` applied to the converging stage
ratios (`tendsto_childRatio_qStage`), and trivially elsewhere. -/
theorem eventually_lt_branchStageFactor (G : GainFamily) {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation universalContinuousSemimeasure q) (T : Set BitString)
    (ω : CantorSeq) (i : ℕ) :
    ∀ c < branchTargetFactor G T ω i,
      ∀ᶠ s in atTop, c < (branchStageFactor G T (qStage q) ω s i : ℝ) := by
  intro c hc
  unfold branchTargetFactor at hc
  unfold branchStageFactor
  split_ifs at hc ⊢ with hf
  · have hM := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
    exact G.target_liminf _ (normalizedError_nonneg _ ω i) (normalizedError_le_one _ ω i)
      (fun s => childRatio (qStage q) s (cantorPrefix ω i) (ω i))
      (tendsto_childRatio_qStage hq hM.ne_top universalContinuousSemimeasure_pos _ _) c hc
  · exact Filter.Eventually.of_forall fun s => by exact_mod_cast hc

/-! ### The product lower bound -/

/-- **The stage demands along a branch are eventually large.**  Under the hypotheses of
`ofReal_mul_prod_le_demandMass`, the certified demand of `cantorPrefix ω n` eventually exceeds
every value below `M(ω_{<n}) * ∏_{i < n} branchTargetFactor G T ω i`: eventually it is the stage
demand, the stage mass times the stage factors (`stageDemand_cantorPrefix`), and the stage mass
and the product of the stage factors are lower limits of their limits (`tendsto_qStage`,
`eventually_lt_branchStageFactor`, `eventually_lt_prod_of_eventually_lt`). -/
theorem eventually_lt_demand_cantorPrefix (G : GainFamily) {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation universalContinuousSemimeasure q) {e : ℕ}
    {T : Set BitString} (hdec : DecidesTree e T) {ω : CantorSeq} (hω : Branch T ω) (n : ℕ) :
    ∀ c < (universalContinuousSemimeasure (cantorPrefix ω n)).toReal *
        ∏ i ∈ Finset.range n, branchTargetFactor G T ω i,
      ∀ᶠ s in atTop, c < (demand G q e s (cantorPrefix ω n) : ℝ) := by
  intro c hc
  have hM := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  have hfac : ∀ s i, (0 : ℝ) ≤ (branchStageFactor G T (qStage q) ω s i : ℝ) := fun s i => by
    exact_mod_cast zero_le_one.trans (one_le_branchStageFactor G T (qStage q) ω s i)
  have htarget : ∀ i ∈ Finset.range n, 0 ≤ branchTargetFactor G T ω i := fun i _ =>
    zero_le_one.trans (one_le_branchTargetFactor G T ω i)
  have hstage : ∀ᶠ s in atTop, c < (qStage q s (cantorPrefix ω n) : ℝ) *
      ∏ i ∈ Finset.range n, (branchStageFactor G T (qStage q) ω s i : ℝ) :=
    eventually_lt_mul_of_eventually_lt (fun s => by exact_mod_cast qStage_nonneg q s _)
      (fun s => Finset.prod_nonneg fun i _ => hfac s i) ENNReal.toReal_nonneg
      (Finset.prod_nonneg htarget)
      (fun c' hc' => (tendsto_qStage hq hM.ne_top _).eventually_const_lt hc')
      (eventually_lt_prod_of_eventually_lt _ _ _ hfac htarget
        fun i _ => eventually_lt_branchStageFactor G hq T ω i) c hc
  filter_upwards [eventually_demand_eq_stageDemand G q hdec (cantorPrefix ω n), hstage]
    with s hs h's
  rw [hs, stageDemand_cantorPrefix G (qStage q) hω s n]
  push_cast
  exact h's

/-- **The product lower bound.**  Let `q` be a simple tree approximation of the universal
semimeasure `M`, let `e` decide `T` and let `ω` be a branch of `T`.  The demand mass of the
prefix `cantorPrefix ω n` is at least `M(ω_{<n})` times the limit factors of the positions
`i < n`.

Proof: every `c` below the left side is below some certified demand
(`eventually_lt_demand_cantorPrefix`), hence below the supremum `demandMass`. -/
theorem ofReal_mul_prod_le_demandMass (G : GainFamily) {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation universalContinuousSemimeasure q) {e : ℕ}
    {T : Set BitString} (hdec : DecidesTree e T) {ω : CantorSeq} (hω : Branch T ω) (n : ℕ) :
    ENNReal.ofReal ((universalContinuousSemimeasure (cantorPrefix ω n)).toReal *
        ∏ i ∈ Finset.range n, branchTargetFactor G T ω i) ≤
      demandMass G q e (cantorPrefix ω n) := by
  refine le_of_forall_lt fun c hc => ?_
  have hc_top : c ≠ ⊤ := ne_top_of_lt hc
  rw [ENNReal.lt_ofReal_iff_toReal_lt hc_top] at hc
  obtain ⟨s, hs⟩ := (eventually_lt_demand_cantorPrefix G hq hdec hω n c.toReal hc).exists
  exact ((ENNReal.lt_ofReal_iff_toReal_lt hc_top).mpr hs).trans_le
    (le_iSup (fun s => ENNReal.ofReal (demand G q e s (cantorPrefix ω n) : ℝ)) s)

/-! ### The logarithmic bridge -/

/-- The logarithm of a limit factor dominates `kappa` times the forced error term with the
exponent `beta`. -/
theorem kappa_mul_forcedErrorTerm_le_log (G : GainFamily) (T : Set BitString) (ω : CantorSeq)
    (i : ℕ) :
    G.kappa * forcedErrorTerm universalContinuousSemimeasure T ω G.beta i ≤
      Real.log (branchTargetFactor G T ω i) := by
  unfold forcedErrorTerm branchTargetFactor
  split_ifs
  · exact G.log_target _ (normalizedError_nonneg _ ω i) (normalizedError_le_one _ ω i)
  · simp

/-- **The logarithmic bridge.**  `kappa` times the `beta`-power loss on the first `n` positions
is at most the logarithm of the product of the limit factors. -/
theorem kappa_mul_partialPowerLoss_le_log_prod (G : GainFamily) (T : Set BitString)
    (ω : CantorSeq) (n : ℕ) :
    G.kappa * partialPowerLoss universalContinuousSemimeasure T ω G.beta n ≤
      Real.log (∏ i ∈ Finset.range n, branchTargetFactor G T ω i) := by
  rw [Real.log_prod fun i _ => (zero_lt_one.trans_le (one_le_branchTargetFactor G T ω i)).ne',
    partialPowerLoss, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => kappa_mul_forcedErrorTerm_le_log G T ω i

end Kolmogorov.SelectedBits
