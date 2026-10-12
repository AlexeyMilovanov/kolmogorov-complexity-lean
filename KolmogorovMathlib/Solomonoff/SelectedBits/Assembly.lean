import KolmogorovMathlib.Solomonoff.Domination.UniformFamily
import KolmogorovMathlib.Solomonoff.SelectedBits.Gain.Square
import KolmogorovMathlib.Solomonoff.SelectedBits.Gain.Staircase
import KolmogorovMathlib.Solomonoff.SelectedBits.Limit

/-!
# Assembly of the selected-bit bounds

The glue between the numerical and effective core of the selected-bit argument and the headline
statements of `SelectedBits/Statements.lean` (blueprint nodes L20, P14, L21 and C10).  Here
`M = universalContinuousSemimeasure` and `K(e) = KPNat U e`.

* `prod_branchTargetFactor_le_two_pow`: for a gain family `G` there is a constant `C` such that
  the product of the limit factors along a branch of a tree decided by `e` is at most
  `2 ^ (K(e) + C)`.  The constant is the one of the generic domination theorem
  `exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree` for the demand masses
  `demandMass G q` of a fixed simple tree approximation `q` of `M`: the demand mass of
  `ω_{<n}` dominates `M(ω_{<n})` times the product (`ofReal_mul_prod_le_demandMass`),
  `2^{-(K(e) + C)}` times it is at most `M(ω_{<n})`, and `M(ω_{<n})` is positive and finite
  (`le_two_pow_of_two_inv_pow_mul_ofReal_le`).
* `kappa_mul_partialPowerLoss_le_index_complexity`: taking logarithms, `kappa` times the
  `beta`-power loss is at most `log 2 · (K(e) + C)` (`kappa_mul_partialPowerLoss_le_log_prod`).
* `staircase_partialPowerLoss_le`: for the staircase family of `m ≥ 1` the loss with exponent
  `1 + 1/m` is at most `2^(m+1) (K(e) + C)`; the errors lie in `[0, 1]`, so the power loss is
  antitone in the exponent (`partialPowerLoss_le_of_le_exponent`), which reduces every
  exponent `γ > 1` to a staircase family with `1 + 1/m ≤ γ`.
* `summable_forcedErrorTerm_and_tsum_le`: the forced error terms are nonnegative, so bounded
  partial sums give a summable series with the same bound.
* `exists_decidesTree_of_isComputablePrefixTree`: a computable membership test of a prefix tree
  is implemented by a code, whose index decides the tree; the infimum defining
  `treeComplexity` is attained (`exists_decidesTree_KPNat_eq_treeComplexity`).
-/

namespace Kolmogorov.SelectedBits

open scoped ENNReal

/-! ### Errors and the power loss -/

/-- The forced error terms are nonnegative. -/
theorem forcedErrorTerm_nonneg (a : BitString → ℝ≥0∞) (T : Set BitString) (ω : CantorSeq)
    (γ : ℝ) (i : ℕ) : 0 ≤ forcedErrorTerm a T ω γ i := by
  unfold forcedErrorTerm
  split_ifs
  · exact Real.rpow_nonneg (normalizedError_nonneg a ω i) γ
  · exact le_rfl

/-- A forced error term is antitone in the exponent on the nonnegative exponents, since the
normalized errors lie in `[0, 1]`. -/
theorem forcedErrorTerm_le_of_le_exponent (a : BitString → ℝ≥0∞) (T : Set BitString)
    (ω : CantorSeq) {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) (i : ℕ) :
    forcedErrorTerm a T ω γ i ≤ forcedErrorTerm a T ω β i := by
  unfold forcedErrorTerm
  split_ifs
  · exact Real.rpow_le_rpow_of_exponent_ge' (normalizedError_nonneg a ω i)
      (normalizedError_le_one a ω i) hβ hβγ
  · exact le_rfl

/-- The power loss is antitone in the exponent on the nonnegative exponents. -/
theorem partialPowerLoss_le_of_le_exponent (a : BitString → ℝ≥0∞) (T : Set BitString)
    (ω : CantorSeq) {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) (n : ℕ) :
    partialPowerLoss a T ω γ n ≤ partialPowerLoss a T ω β n :=
  Finset.sum_le_sum fun i _ => forcedErrorTerm_le_of_le_exponent a T ω hβ hβγ i

/-! ### The product bound for a gain family -/

/-- The product of the limit factors along a branch is at least `1`. -/
theorem one_le_prod_branchTargetFactor (G : GainFamily) (T : Set BitString) (ω : CantorSeq)
    (n : ℕ) : 1 ≤ ∏ i ∈ Finset.range n, branchTargetFactor G T ω i :=
  Finset.one_le_prod₀ fun i _ => one_le_branchTargetFactor G T ω i

/-- **Cancelling a positive finite mass.**  If `2^{-k}` times `ofReal (m.toReal * P)` is at most
the positive finite mass `m`, then `P ≤ 2 ^ k`. -/
theorem le_two_pow_of_two_inv_pow_mul_ofReal_le {m : ℝ≥0∞} (hm0 : 0 < m) (hmt : m ≠ ⊤)
    {P : ℝ} (hP : 0 ≤ P) (k : ℕ)
    (h : (2 : ℝ≥0∞)⁻¹ ^ k * ENNReal.ofReal (m.toReal * P) ≤ m) : P ≤ 2 ^ k := by
  have hm : 0 < m.toReal := ENNReal.toReal_pos hm0.ne' hmt
  have h' := ENNReal.toReal_mono hmt h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (mul_nonneg hm.le hP), inv_pow,
    inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)] at h'
  exact le_of_mul_le_mul_left (by linarith : m.toReal * P ≤ m.toReal * 2 ^ k) hm

/-- **The product bound.**  For a gain family `G` there is a constant `C` such that for every
tree `T` decided by the index `e`, every branch `ω` of `T` and every `n`, the product of the
limit factors of the positions `i < n` is at most `2 ^ (KPNat U e + C)`.

The constant is the one of the generic domination theorem for the demand masses of a fixed
simple tree approximation of the universal semimeasure `M`; the demand mass of `ω_{<n}`
dominates `M(ω_{<n})` times the product, and `M(ω_{<n})` is positive and finite. -/
theorem prod_branchTargetFactor_le_two_pow (G : GainFamily) (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (T : Set BitString) (e : ℕ) (ω : CantorSeq) (n : ℕ),
      DecidesTree e T → Branch T ω →
        ∏ i ∈ Finset.range n, branchTargetFactor G T ω i ≤ 2 ^ ((KPNat U e).toNat + C) := by
  have hM := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure
  obtain ⟨q, hq⟩ := exists_simpleTreeApproximation hM hM.1.1
  obtain ⟨C, hC⟩ := exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree U hU
    (demandMass G q) (isUniformlyLowerSemicomputableTreeFamily_demandMass G hq.2.2.2.2.2)
    (fun e S hS => sum_demandMass_le_one G hq e S hS)
  refine ⟨C, fun T e ω n hdec hω => ?_⟩
  refine le_two_pow_of_two_inv_pow_mul_ofReal_le
    (universalContinuousSemimeasure_pos (cantorPrefix ω n)) (hM.1.ne_top _)
    (zero_le_one.trans (one_le_prod_branchTargetFactor G T ω n)) _ ?_
  refine le_trans ?_ (hC e (cantorPrefix ω n))
  gcongr
  exact ofReal_mul_prod_le_demandMass G hq hdec hω n

/-- **The logarithmic bound for a gain family.**  For a gain family `G` there is a constant `C`
such that for every tree `T` decided by the index `e`, every branch `ω` of `T` and every `n`,
`kappa` times the `beta`-power loss at the forced positions `i < n` is at most
`log 2 · (KPNat U e + C)`. -/
theorem kappa_mul_partialPowerLoss_le_index_complexity (G : GainFamily) (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (T : Set BitString) (e : ℕ) (ω : CantorSeq) (n : ℕ),
      DecidesTree e T → Branch T ω →
        G.kappa * partialPowerLoss universalContinuousSemimeasure T ω G.beta n ≤
          Real.log 2 * (((KPNat U e).toNat : ℝ) + C) := by
  obtain ⟨C, hC⟩ := prod_branchTargetFactor_le_two_pow G U hU
  refine ⟨C, fun T e ω n hdec hω => ?_⟩
  have hpos : 0 < ∏ i ∈ Finset.range n, branchTargetFactor G T ω i :=
    zero_lt_one.trans_le (one_le_prod_branchTargetFactor G T ω n)
  calc G.kappa * partialPowerLoss universalContinuousSemimeasure T ω G.beta n
      ≤ Real.log (∏ i ∈ Finset.range n, branchTargetFactor G T ω i) :=
        kappa_mul_partialPowerLoss_le_log_prod G T ω n
    _ ≤ Real.log (2 ^ ((KPNat U e).toNat + C)) := Real.log_le_log hpos (hC T e ω n hdec hω)
    _ = Real.log 2 * (((KPNat U e).toNat : ℝ) + C) := by
        rw [Real.log_pow]
        push_cast
        ring

/-! ### The staircase instance -/

/-- **The staircase bound.**  With the staircase gain family of `m ≥ 1`
(`kappa = 2^{-(m+1)} log 2`, `beta = 1 + 1/m`) the logarithmic bound reads
`partialPowerLoss M T ω (1 + 1/m) n ≤ 2^(m+1) (KPNat U e + C)`. -/
theorem staircase_partialPowerLoss_le (U : Map) (hU : IsOptimalPrefixConditional U) (m : ℕ)
    (hm : 0 < m) :
    ∃ C : ℕ, ∀ (T : Set BitString) (e : ℕ) (ω : CantorSeq) (n : ℕ),
      DecidesTree e T → Branch T ω →
        partialPowerLoss universalContinuousSemimeasure T ω (1 + 1 / (m : ℝ)) n ≤
          2 ^ (m + 1) * (((KPNat U e).toNat : ℝ) + C) := by
  obtain ⟨C, hC⟩ := kappa_mul_partialPowerLoss_le_index_complexity
    (staircaseGainFamily m hm) U hU
  refine ⟨C, fun T e ω n hdec hω => ?_⟩
  have h := hC T e ω n hdec hω
  rw [staircaseGainFamily_kappa, staircaseGainFamily_beta, mul_comm _ (Real.log 2),
    mul_assoc] at h
  have h' := le_of_mul_le_mul_left h (Real.log_pos one_lt_two)
  calc partialPowerLoss universalContinuousSemimeasure T ω (1 + 1 / (m : ℝ)) n
      = 2 ^ (m + 1) * ((1 / 2) ^ (m + 1) *
          partialPowerLoss universalContinuousSemimeasure T ω (1 + 1 / (m : ℝ)) n) := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
    _ ≤ 2 ^ (m + 1) * (((KPNat U e).toNat : ℝ) + C) := by gcongr

/-! ### The series -/

/-- **Summability.**  Nonnegative terms whose partial sums `partialPowerLoss a T ω γ n` are
bounded by `B` form a summable series with sum at most `B`. -/
theorem summable_forcedErrorTerm_and_tsum_le (a : BitString → ℝ≥0∞) (T : Set BitString)
    (ω : CantorSeq) (γ B : ℝ) (h : ∀ n, partialPowerLoss a T ω γ n ≤ B) :
    Summable (forcedErrorTerm a T ω γ) ∧ ∑' i : ℕ, forcedErrorTerm a T ω γ i ≤ B :=
  ⟨summable_of_sum_range_le (forcedErrorTerm_nonneg a T ω γ) h,
    Real.tsum_le_of_sum_range_le (forcedErrorTerm_nonneg a T ω γ) h⟩

/-! ### Tree complexity -/

/-- **A computable prefix tree is decided by an index.**  The membership test is implemented
by a code (`Nat.Partrec.Code.exists_code`), which on the encoding of a word outputs the encoding
`1` or `0` of the Boolean answer. -/
theorem exists_decidesTree_of_isComputablePrefixTree {T : Set BitString}
    (hT : IsComputablePrefixTree T) : ∃ e, DecidesTree e T := by
  obtain ⟨hTree, d, hd, hdT⟩ := hT
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hd
  refine ⟨Encodable.encode c, hTree, fun x => ⟨d x, ?_, hdT x⟩⟩
  rw [Denumerable.ofNat_encode, hc]
  cases h : d x <;> simp [Encodable.encodek, h]

/-- The tree complexity is at most the prefix complexity of every deciding index. -/
theorem treeComplexity_le_KPNat (U : Map) {T : Set BitString} {e : ℕ} (he : DecidesTree e T) :
    treeComplexity U T ≤ KPNat U e :=
  iInf₂_le e he

/-- **The tree complexity is attained.**  For a computable prefix tree some index deciding the
tree has prefix complexity exactly `treeComplexity U T`. -/
theorem exists_decidesTree_KPNat_eq_treeComplexity (U : Map) {T : Set BitString}
    (hT : IsComputablePrefixTree T) :
    ∃ e, DecidesTree e T ∧ KPNat U e = treeComplexity U T := by
  obtain ⟨e₀, he₀⟩ := exists_decidesTree_of_isComputablePrefixTree hT
  have : Nonempty {e : ℕ | DecidesTree e T} := ⟨⟨e₀, he₀⟩⟩
  obtain ⟨⟨e, he⟩, h⟩ := ENat.exists_eq_iInf
    (fun e : {e : ℕ | DecidesTree e T} => KPNat U e)
  exact ⟨e, he, h.trans (iInf_subtype'' {e : ℕ | DecidesTree e T} (KPNat U))⟩

end Kolmogorov.SelectedBits
