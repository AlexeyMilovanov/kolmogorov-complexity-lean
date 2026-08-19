import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedAddNoisePolySize

/-!
# Tightening the free parameters of the budgeted pair projection

`BudgetedPairProjectionStatement V` (`BudgetedAddNoiseLowBranch.lean`) is the
remaining low-branch input of `prop:add-noise`.  Its body carries two free
parameters that are only loosely constrained:

* the visible complexity budget `baseBudget`, subject to `i ≤ baseBudget`, and
* the conditional-randomness slack `epsilon`, subject to
  `l(y) ≤ C(y | x) + epsilon`.

Both may be tightened without loss of generality:

* `budgetedPairProjection_iff_tight_budget` — the statement is *equivalent* to
  its special case `baseBudget = i`, because `baseBudget` occurs only inside a
  slack term that is monotone in it;
* `budgetedPairProjection_of_minimal_epsilon` — it suffices to prove the
  statement for the *least* admissible `epsilon`, because the conclusion is
  monotone in the complexity coordinate `i + epsilon + ...`;
* `budgetedPairProjection_of_tight_minimal` — the two reductions combined, so
  the open statement may be proved with `baseBudget = i` and with `epsilon`
  minimal.

Everything below is a reduction between formulations of an open statement; no
open statement is assumed, and no frozen interface is edited.
-/

namespace Kolmogorov

/-- **The visible budget of the pair projection may be taken tight.**  Since
`baseBudget` enters the conclusion only through `logSlack c baseBudget`, which is
monotone in its argument, the general statement follows from its instance at
`baseBudget = i`, and conversely. -/
theorem budgetedPairProjection_iff_tight_budget (V : Map) :
    BudgetedPairProjectionStatement V ↔
      ∃ c : Nat, ∀ (x y : BitString) (epsilon i j : Nat),
        InPlainDescriptionProfile V (pairCode x y) i j →
        (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
        InPlainDescriptionProfile V x
          (i + epsilon + logSlack c i + logSlack c y.length)
          (j - y.length + logSlack c i + logSlack c y.length) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun x y epsilon i j hprofile hrandom =>
      hc x y epsilon i j i hprofile hrandom le_rfl⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, fun x y epsilon i j baseBudget hprofile hrandom hbudget => ?_⟩
    have hslack : logSlack c i ≤ logSlack c baseBudget := logSlack_mono_right c hbudget
    exact ((hc x y epsilon i j hprofile hrandom).mono_i (by omega)).mono_j (by omega)

/-- **The randomness slack of the pair projection may be taken minimal.**  If the
body of `BudgetedPairProjectionStatement` holds for every *least* admissible
`epsilon` — that is, whenever no smaller slack satisfies
`l(y) ≤ C(y | x) + epsilon` — then it holds for every admissible `epsilon`: a
conclusion obtained at a smaller slack is stronger, by monotonicity of the
description profile in its complexity coordinate. -/
theorem budgetedPairProjection_of_minimal_epsilon (V : Map)
    (hMin : ∃ c : Nat, ∀ (x y : BitString) (epsilon i j baseBudget : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      (∀ e : Nat, e < epsilon → ¬ (y.length : ENat) ≤ condK V y x + (e : ENat)) →
      i ≤ baseBudget →
      InPlainDescriptionProfile V x
        (i + epsilon + logSlack c baseBudget + logSlack c y.length)
        (j - y.length + logSlack c baseBudget + logSlack c y.length)) :
    BudgetedPairProjectionStatement V := by
  classical
  obtain ⟨c, hc⟩ := hMin
  refine ⟨c, fun x y epsilon i j baseBudget hprofile hrandom hbudget => ?_⟩
  have hex : ∃ e : Nat, (y.length : ENat) ≤ condK V y x + (e : ENat) := ⟨epsilon, hrandom⟩
  set e0 := Nat.find hex with he0
  have he0le : e0 ≤ epsilon := Nat.find_le hrandom
  have he0spec : (y.length : ENat) ≤ condK V y x + (e0 : ENat) := Nat.find_spec hex
  have he0min : ∀ e : Nat, e < e0 → ¬ (y.length : ENat) ≤ condK V y x + (e : ENat) :=
    fun e hlt => Nat.find_min hex hlt
  exact (hc x y e0 i j baseBudget hprofile he0spec he0min hbudget).mono_i (by omega)

/-- **The budgeted pair projection with both free parameters tightened.**  It
suffices to prove the low branch with the tight budget `baseBudget = i` and with
the least admissible randomness slack `epsilon`. -/
theorem budgetedPairProjection_of_tight_minimal (V : Map)
    (hTight : ∃ c : Nat, ∀ (x y : BitString) (epsilon i j : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      (∀ e : Nat, e < epsilon → ¬ (y.length : ENat) ≤ condK V y x + (e : ENat)) →
      InPlainDescriptionProfile V x
        (i + epsilon + logSlack c i + logSlack c y.length)
        (j - y.length + logSlack c i + logSlack c y.length)) :
    BudgetedPairProjectionStatement V := by
  obtain ⟨c, hc⟩ := hTight
  refine budgetedPairProjection_of_minimal_epsilon V ⟨c, ?_⟩
  intro x y epsilon i j baseBudget hprofile hrandom hmin hbudget
  have hslack : logSlack c i ≤ logSlack c baseBudget := logSlack_mono_right c hbudget
  exact ((hc x y epsilon i j hprofile hrandom hmin).mono_i (by omega)).mono_j (by omega)

/-- **The budgeted pair projection reduces to its superpolynomial-size regime.**
For every fixed exponent `k`, the full `BudgetedPairProjectionStatement V`
follows from its instance restricted to pair models whose size coordinate
exceeds `(baseBudget + l(y)) ^ k`: the complementary regime is the proved
polynomial-size branch
`inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le_pow`.

The hypothesis `hHard` is a faithful statement of what is still missing; it is
not assumed to hold. -/
theorem budgetedPairProjection_of_hard_regime_superpoly
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : Nat)
    (hHard : ∃ c : Nat, ∀ (x y : BitString) (epsilon i j baseBudget : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      i ≤ baseBudget →
      (baseBudget + y.length) ^ k < j →
      InPlainDescriptionProfile V x
        (i + epsilon + logSlack c baseBudget + logSlack c y.length)
        (j - y.length + logSlack c baseBudget + logSlack c y.length)) :
    BudgetedPairProjectionStatement V := by
  obtain ⟨cH, hH⟩ := hHard
  obtain ⟨cP, hP⟩ :=
    inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le_pow V U hV hU k
  refine ⟨max cP cH, fun x y epsilon i j baseBudget hprofile hrandom hbudget => ?_⟩
  have hcP : logSlack cP baseBudget ≤ logSlack (max cP cH) baseBudget :=
    logSlack_mono_left (le_max_left _ _) baseBudget
  have hcPy : logSlack cP y.length ≤ logSlack (max cP cH) y.length :=
    logSlack_mono_left (le_max_left _ _) y.length
  have hcH : logSlack cH baseBudget ≤ logSlack (max cP cH) baseBudget :=
    logSlack_mono_left (le_max_right _ _) baseBudget
  have hcHy : logSlack cH y.length ≤ logSlack (max cP cH) y.length :=
    logSlack_mono_left (le_max_right _ _) y.length
  by_cases hpoly : j ≤ (baseBudget + y.length) ^ k
  · exact ((hP x y epsilon i j baseBudget hprofile hrandom hbudget hpoly).mono_i
      (by omega)).mono_j (by omega)
  · push Not at hpoly
    exact ((hH x y epsilon i j baseBudget hprofile hrandom hbudget hpoly).mono_i
      (by omega)).mono_j (by omega)

/-- **The budgeted pair projection with every free parameter tightened.**  For
every fixed exponent `k` the full statement follows from its instance with

* the tight budget `baseBudget = i`,
* the least admissible randomness slack `epsilon`, and
* a size coordinate `j` beyond `(i + l(y)) ^ k`.

This is the joint sharpening of `budgetedPairProjection_of_tight_minimal` and
`budgetedPairProjection_of_hard_regime_superpoly`. -/
theorem budgetedPairProjection_of_hard_regime_superpoly_tight_minimal
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : Nat)
    (hHard : ∃ c : Nat, ∀ (x y : BitString) (epsilon i j : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      (∀ e : Nat, e < epsilon → ¬ (y.length : ENat) ≤ condK V y x + (e : ENat)) →
      (i + y.length) ^ k < j →
      InPlainDescriptionProfile V x
        (i + epsilon + logSlack c i + logSlack c y.length)
        (j - y.length + logSlack c i + logSlack c y.length)) :
    BudgetedPairProjectionStatement V := by
  obtain ⟨cH, hH⟩ := hHard
  obtain ⟨cP, hP⟩ :=
    inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le_pow V U hV hU k
  refine budgetedPairProjection_of_minimal_epsilon V ⟨max cP cH, ?_⟩
  intro x y epsilon i j baseBudget hprofile hrandom hmin hbudget
  have hcP : logSlack cP baseBudget ≤ logSlack (max cP cH) baseBudget :=
    logSlack_mono_left (le_max_left _ _) baseBudget
  have hcPy : logSlack cP y.length ≤ logSlack (max cP cH) y.length :=
    logSlack_mono_left (le_max_left _ _) y.length
  have hcH : logSlack cH i ≤ logSlack (max cP cH) baseBudget :=
    le_trans (logSlack_mono_right cH hbudget) (logSlack_mono_left (le_max_right _ _) baseBudget)
  have hcHy : logSlack cH y.length ≤ logSlack (max cP cH) y.length :=
    logSlack_mono_left (le_max_right _ _) y.length
  by_cases hpoly : j ≤ (baseBudget + y.length) ^ k
  · exact ((hP x y epsilon i j baseBudget hprofile hrandom hbudget hpoly).mono_i
      (by omega)).mono_j (by omega)
  · push Not at hpoly
    have hpow : (i + y.length) ^ k ≤ (baseBudget + y.length) ^ k :=
      Nat.pow_le_pow_left (by omega) k
    exact ((hH x y epsilon i j hprofile hrandom hmin (by omega)).mono_i
      (by omega)).mono_j (by omega)

end Kolmogorov
