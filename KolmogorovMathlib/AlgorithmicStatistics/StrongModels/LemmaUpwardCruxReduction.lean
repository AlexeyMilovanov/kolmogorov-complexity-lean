import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PropUpwardFrontier
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerHardRegime
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LemmaUpwardCruxStatement

/-!
# Narrowing the upward crux to its hard regime

`LemmaUpwardCruxStatement U` (see `LemmaUpwardCruxStatement.lean`) is the exact
`alpha, beta`-independent optimal-set conversion on which the unconditional
`prop_upward` still depends.  This module shows that only a *proper sub-regime*
of that statement is genuinely open: for every fixed exponent `k`, the
conversion has to be established only for Pareto-minimal witnesses with

```text
alpha < K(x),   K(x) ^ k < beta,   and a non-simple length.
```

Three boundary regimes are discharged outright:

* `K(x) ≤ alpha`: the canonical singleton `{x}` is already an optimal set model
  of complexity `K(x) + O(1)` and optimality deficiency `O(1)`
  (`isOptimalSetStochastic_singleton_of_KPPlain`);
* `beta ≤ K(x) ^ k`: the proved complexity-scale conversion
  `stochasticity_to_optimal_set_budget` charges `logSlack c (K(x)+alpha+beta)`,
  and in this regime that charge folds into a single `logSlack C (K(x))` by
  `logSlack_linear_bound` and `logSlack_le_of_le_pow`;
* `l(x) + m ≤ K(x) + beta` for some bound `m ≤ alpha` on `K(l(x))`: the full
  cube at the length of `x` is then already an optimal set model
  (`isOptimalSetStochastic_fullCube_of_simple_length`, built on the
  complexity-scale cube gate `setComplexity_fullCube_le_KPPlain_natCode`).

A fourth, free reduction passes to a Pareto-minimal stochasticity witness.

Consequently `LemmaUpwardCruxStatement` follows from the strictly weaker
`LemmaUpwardCruxHardRegimeStatement`, and so does `prop:upward`
(`propUpward_of_hardRegimeCrux`).  Nothing is assumed here: the hard-regime
statement is only ever taken as a hypothesis.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution
open scoped ENNReal

/-- **Pareto-minimal stochasticity witness.**  Below any stochasticity pair
`(alpha, beta)` for `x` there is a pair `(a, b) ≤ (alpha, beta)` which is still a
stochasticity pair and which is minimal in each coordinate separately: no
strictly smaller second parameter works with `a`, and no strictly smaller first
parameter works with `b`.  Take a pair below `(alpha, beta)` minimizing the sum
`a + b`. -/
theorem exists_pareto_minimal_stochastic_witness
    (U : Map) (x : BitString) (alpha beta : ℕ) (hst : IsStochastic U x alpha beta) :
    ∃ a b : ℕ, a ≤ alpha ∧ b ≤ beta ∧ IsStochastic U x a b ∧
      (∀ b' : ℕ, b' < b → ¬ IsStochastic U x a b') ∧
      (∀ a' : ℕ, a' < a → ¬ IsStochastic U x a' b) := by
  classical
  set T : Set ℕ :=
    {s | ∃ a b : ℕ, a ≤ alpha ∧ b ≤ beta ∧ a + b = s ∧ IsStochastic U x a b} with hT
  have hTne : (alpha + beta) ∈ T := ⟨alpha, beta, le_rfl, le_rfl, rfl, hst⟩
  obtain ⟨a, b, ha, hb, hab, hstab⟩ : sInf T ∈ T := Nat.sInf_mem ⟨alpha + beta, hTne⟩
  refine ⟨a, b, ha, hb, hstab, ?_, ?_⟩
  · intro b' hb' hcon
    have hmem : a + b' ∈ T := ⟨a, b', ha, le_trans hb'.le hb, rfl, hcon⟩
    have hle := Nat.sInf_le hmem
    omega
  · intro a' ha' hcon
    have hmem : a' + b ∈ T := ⟨a', b, le_trans ha'.le ha, hb, rfl, hcon⟩
    have hle := Nat.sInf_le hmem
    omega

/-- **The singleton optimal-set model.**  For every `x` the canonical uniform
model on `{x}` witnesses `IsOptimalSetStochastic U x (K(x) + c) beta` as soon as
the optimality-deficiency budget `beta` absorbs the additive constant `c` of the
singleton gate. -/
theorem isOptimalSetStochastic_singleton_of_KPPlain
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (p beta : ℕ),
      KPPlain U x = (p : ENat) → c ≤ beta →
      IsOptimalSetStochastic U x (p + c) beta := by
  obtain ⟨c, hc⟩ := setComplexity_singleton_le_KPPlain_add_const U hU
  refine ⟨c, fun x p beta hp hcbeta => ?_⟩
  refine ⟨{x}, Finset.singleton_nonempty x, Finset.mem_singleton_self x, ?_, ?_⟩
  · have h := hc x
    rw [hp] at h
    refine h.trans ?_
    push_cast
    exact le_rfl
  · -- the multiplicative optimality-deficiency inequality
    have hmass : (codedUniformOn {x} (Finset.singleton_nonempty x)).mass x = 1 := by
      rw [codedUniformOn_mass_of_mem _ _ _ (Finset.mem_singleton_self x)]
      simp
    have hcomp : (codedUniformOn {x} (Finset.singleton_nonempty x)).complexity U
        ≤ (p : ENat) + (c : ENat) := by
      have h := hc x
      rw [hp] at h
      exact h
    have hw : complexityWeight ((p : ENat) + (c : ENat))
        ≤ complexityWeight ((codedUniformOn {x} (Finset.singleton_nonempty x)).complexity U) :=
      complexityWeight_le_of_le hcomp
    have hone : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ beta * (2 : ℝ≥0∞)⁻¹ ^ c := by
      calc (1 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ c := by
            rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
        _ ≤ (2 : ℝ≥0∞) ^ beta * (2 : ℝ≥0∞)⁻¹ ^ c := by
            gcongr
            exact one_le_two
    have hgoal : complexityWeight (KPPlain U x) ≤ (2 : ℝ≥0∞) ^ beta *
        (complexityWeight ((codedUniformOn {x} (Finset.singleton_nonempty x)).complexity U) *
          (codedUniformOn {x} (Finset.singleton_nonempty x)).mass x) := by
      rw [hmass, mul_one, hp]
      refine le_trans ?_ (mul_le_mul' (le_refl ((2 : ℝ≥0∞) ^ beta)) hw)
      rw [complexityWeight_add_nat, complexityWeight_coe]
      calc (2 : ℝ≥0∞)⁻¹ ^ p
          = 1 * (2 : ℝ≥0∞)⁻¹ ^ p := (one_mul _).symm
        _ ≤ ((2 : ℝ≥0∞) ^ beta * (2 : ℝ≥0∞)⁻¹ ^ c) * (2 : ℝ≥0∞)⁻¹ ^ p := by gcongr
        _ = (2 : ℝ≥0∞) ^ beta * ((2 : ℝ≥0∞)⁻¹ ^ p * (2 : ℝ≥0∞)⁻¹ ^ c) := by ring
    exact hgoal

/-- **The full-cube gate at the complexity scale.**  The canonical uniform code
of the length-`n` cube has prefix complexity at most `K(natCode n) + O(1)`; this
is the prefix-level counterpart of
`plainSetComplexity_fullCube_le_KPPlain_natCode`, sharpening the `O(log n)`
bound of `fullSetComplexityGate`. -/
theorem setComplexity_fullCube_le_KPPlain_natCode
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ,
      setComplexity U (stringsOfLength n) (codedStringsOfLength_nonempty n)
        ≤ KPPlain U (natCode n) + (c : ENat) := by
  obtain ⟨c₁, hc₁⟩ := KPPlain_map_le U hU
    (fun w => canonicalUniformCodeOfList
      (canonicalFinsetList (stringsOfLength (decodeNatCode w)))) (by
        convert canonicalUniformCodeOfList_computable.comp
          (_ : Computable fun w => canonicalFinsetList (stringsOfLength (decodeNatCode w)))
          using 1
        convert canonicalFinsetList_toFinset_primrec.comp
          (allStrings_primrec.comp decodeNatCode_primrec) |>.to_comp using 1
        ext a
        rfl)
  refine ⟨c₁, fun n => ?_⟩
  have hcode : canonicalUniformCodeOfList (canonicalFinsetList (stringsOfLength n))
      = (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).code :=
    canonicalUniformCodeOfList_canonicalFinsetList _ (codedStringsOfLength_nonempty n)
  have hmap := hc₁ (natCode n)
  rw [decodeNatCode_natCode, hcode] at hmap
  exact hmap

/-- **The full-cube optimal-set model.**  If the length of `x` is describable
with `m` bits and `l(x) + m + c ≤ K(x) + beta`, then the cube of all strings of
the length of `x` is an optimal set model for `x` with complexity `m + c` and
optimality deficiency `beta`. -/
theorem isOptimalSetStochastic_fullCube_of_simple_length
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (p m beta : ℕ),
      KPPlain U x = (p : ENat) →
      KPPlain U (natCode x.length) ≤ (m : ENat) →
      x.length + m + c ≤ p + beta →
      IsOptimalSetStochastic U x (m + c) beta := by
  obtain ⟨c, hc⟩ := setComplexity_fullCube_le_KPPlain_natCode U hU
  refine ⟨c, fun x p m beta hp hm hsum => ?_⟩
  set n := x.length with hn
  have hxmem : x ∈ stringsOfLength n := (memStringsOfLength n x).mpr rfl
  have hcomp : setComplexity U (stringsOfLength n) (codedStringsOfLength_nonempty n)
      ≤ ((m + c : ℕ) : ENat) := by
    refine (hc n).trans ?_
    have : KPPlain U (natCode n) + (c : ENat) ≤ (m : ENat) + (c : ENat) := by gcongr
    simpa [Nat.cast_add] using this
  refine ⟨stringsOfLength n, codedStringsOfLength_nonempty n, hxmem, hcomp, ?_⟩
  have hmass : (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).mass x
      = (2 : ℝ≥0∞)⁻¹ ^ n := by
    rw [codedUniformOn_mass_of_mem _ _ _ hxmem, cardStringsOfLength]
    push_cast
    rw [← ENNReal.inv_pow]
  have hw : complexityWeight (((m + c : ℕ) : ENat))
      ≤ complexityWeight ((codedUniformOn (stringsOfLength n)
          (codedStringsOfLength_nonempty n)).complexity U) :=
    complexityWeight_le_of_le hcomp
  have hgoal : complexityWeight (KPPlain U x) ≤ (2 : ℝ≥0∞) ^ beta *
      (complexityWeight ((codedUniformOn (stringsOfLength n)
          (codedStringsOfLength_nonempty n)).complexity U) *
        (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).mass x) := by
    rw [hmass, hp]
    refine le_trans ?_ (mul_le_mul' (le_refl ((2 : ℝ≥0∞) ^ beta))
      (mul_le_mul' hw (le_refl ((2 : ℝ≥0∞)⁻¹ ^ n))))
    rw [complexityWeight_coe]
    have hsplit : (2 : ℝ≥0∞)⁻¹ ^ p = (2 : ℝ≥0∞) ^ beta * (2 : ℝ≥0∞)⁻¹ ^ (p + beta) := by
      rw [pow_add]
      rw [← mul_assoc, mul_comm ((2 : ℝ≥0∞) ^ beta) ((2 : ℝ≥0∞)⁻¹ ^ p), mul_assoc,
        ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, mul_one]
    rw [hsplit]
    have hmono : (2 : ℝ≥0∞)⁻¹ ^ (p + beta) ≤ (2 : ℝ≥0∞)⁻¹ ^ (m + c + n) :=
      pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two) (by omega)
    calc (2 : ℝ≥0∞) ^ beta * (2 : ℝ≥0∞)⁻¹ ^ (p + beta)
        ≤ (2 : ℝ≥0∞) ^ beta * (2 : ℝ≥0∞)⁻¹ ^ (m + c + n) := by gcongr
      _ = (2 : ℝ≥0∞) ^ beta * ((2 : ℝ≥0∞)⁻¹ ^ (m + c) * (2 : ℝ≥0∞)⁻¹ ^ n) := by
          rw [pow_add]
  exact hgoal

/-- **The hard regime of the upward crux.**  The `alpha, beta`-independent
optimal-set conversion, restricted to the only regime that is not already
available:

* the model-complexity parameter is below the complexity of `x`;
* the deficiency parameter exceeds the fixed power `K(x) ^ k`;
* the length of `x` is not simple enough for the full cube to be a model
  (`K(x) + beta < l(x) + m` for every bound `m ≤ alpha` on `K(l(x))`);
* the stochasticity witness is Pareto-minimal in both coordinates. -/
def LemmaUpwardCruxHardRegimeStatement (U : Map) (k : ℕ) : Prop :=
  ∃ c : ℕ, ∀ (x : BitString) (p alpha beta : ℕ),
    KPPlain U x = (p : ENat) →
    alpha < p →
    p ^ k < beta →
    (∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) → m ≤ alpha →
      p + beta < x.length + m) →
    IsStochastic U x alpha beta →
    (∀ b : ℕ, b < beta → ¬ IsStochastic U x alpha b) →
    (∀ a : ℕ, a < alpha → ¬ IsStochastic U x a beta) →
    IsOptimalSetStochastic U x
      (alpha + logSlack c p) (beta + logSlack c p)

/-- **The upward crux is only open in its hard regime.**  For every fixed
exponent `k`, four reductions are carried out here, none of them assumed:

* passing to a Pareto-minimal witness below the given one
  (`exists_pareto_minimal_stochastic_witness`), which is harmless because both
  conclusions are monotone in the two parameters;
* the boundary regime `K(x) ≤ alpha`, discharged by the canonical singleton
  model `isOptimalSetStochastic_singleton_of_KPPlain`;
* the polynomial regime `beta ≤ K(x) ^ k`, discharged by the proved
  complexity-scale conversion `stochasticity_to_optimal_set_budget`, whose
  charge `logSlack c (K(x)+alpha+beta)` folds there into a single
  `logSlack C (K(x))` by `logSlack_linear_bound` and `logSlack_le_of_le_pow`;
* the simple-length regime `l(x) + m ≤ K(x) + beta` for some bound `m ≤ alpha`
  on `K(l(x))`, discharged by the full cube
  (`isOptimalSetStochastic_fullCube_of_simple_length`).

Hence the full `alpha, beta`-independent conversion follows from its restriction
to Pareto-minimal witnesses with `alpha < K(x)`, `K(x) ^ k < beta` and a
non-simple length. -/
theorem lemmaUpwardCrux_of_hardRegime
    (U : Map) (hU : IsOptimalPrefixConditional U) (k : ℕ)
    (hHard : LemmaUpwardCruxHardRegimeStatement U k) :
    LemmaUpwardCruxStatement U := by
  classical
  obtain ⟨c1, h1⟩ := isOptimalSetStochastic_singleton_of_KPPlain U hU
  obtain ⟨cCube, hCube⟩ := isOptimalSetStochastic_fullCube_of_simple_length U hU
  obtain ⟨c0, h0⟩ := stochasticity_to_optimal_set_budget U hU
  obtain ⟨C, hC⟩ := logSlack_linear_bound c0 3 0
  obtain ⟨C2, hC2⟩ := logSlack_le_of_le_pow C (k + 1)
  obtain ⟨cH, hH⟩ := hHard
  refine ⟨max (max (max c1 cCube) C2) cH, fun x p alpha beta hp hst => ?_⟩
  set c := max (max (max c1 cCube) C2) cH with hcdef
  have hcs : c ≤ logSlack c p := by unfold logSlack; omega
  have hc1 : c1 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hcCube : cCube ≤ c :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  obtain ⟨a, b, hale, hble, hstab, hbmin, hamin⟩ :=
    exists_pareto_minimal_stochastic_witness U x alpha beta hst
  rcases Nat.lt_or_ge a p with hpa | hpa
  · rcases Nat.lt_or_ge (p ^ k) b with hbp | hbp
    · by_cases hlen : ∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) → m ≤ a →
          p + b < x.length + m
      · -- the genuinely open regime
        have hfold : logSlack cH p ≤ logSlack c p := logSlack_mono_left (le_max_right _ _) p
        exact ((hH x p a b hp hpa hbp hlen hstab hbmin hamin).mono_alpha
          (by omega)).mono_beta (by omega)
      · -- simple-length regime: the full cube at the length of `x` is a model
        push Not at hlen
        obtain ⟨m, hm, hma, hmlen⟩ := hlen
        have hsum : x.length + m + cCube ≤ p + (beta + logSlack c p) := by omega
        exact (hCube x p m (beta + logSlack c p) hp hm hsum).mono_alpha (by omega)
    · -- polynomial-`beta` regime: the proved conversion folds into a single `logSlack C2 p`
      have hp1 : 1 ≤ p := by omega
      have hmax : max p b ≤ p ^ (k + 1) := by
        refine max_le (Nat.le_self_pow (by omega) p) (le_trans hbp ?_)
        exact Nat.pow_le_pow_right hp1 (Nat.le_succ k)
      have hfold : logSlack c0 (p + a + b) ≤ logSlack c p := by
        have h3 : logSlack c0 (p + a + b) ≤ logSlack c0 (3 * max p b + 0) := by
          refine logSlack_mono_right c0 ?_
          have hh1 : p ≤ max p b := le_max_left _ _
          have hh2 : b ≤ max p b := le_max_right _ _
          omega
        have hCp : logSlack c0 (3 * max p b + 0) ≤ logSlack C (max p b) := hC (max p b)
        have hC2p : logSlack C (max p b) ≤ logSlack C2 p := hC2 p (max p b) hmax
        have hCc : logSlack C2 p ≤ logSlack c p :=
          logSlack_mono_left (le_trans (le_max_right _ _) (le_max_left _ _)) p
        omega
      exact ((h0 x p a b hp hstab).mono_alpha (by omega)).mono_beta (by omega)
  · -- singleton regime `K(x) ≤ alpha`
    have hbeta : c1 ≤ beta + logSlack c p := by omega
    exact (h1 x p (beta + logSlack c p) hp hbeta).mono_alpha (by omega)

/-- **`prop:upward` from the hard-regime crux.**  Composes
`lemmaUpwardCrux_of_hardRegime` with `propUpward_of_optimalSetConversion_budget`:
for every fixed `k`, the entire remaining distance to an unconditional
`prop:upward` is the optimal-set conversion for Pareto-minimal witnesses in the
single regime `alpha < K(x)`, `K(x) ^ k < beta`, non-simple length. -/
theorem propUpward_of_hardRegimeCrux
    (V U T : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) (k : ℕ)
    (hHard : LemmaUpwardCruxHardRegimeStatement U k) :
    PropUpwardStatement U T :=
  propUpward_of_optimalSetConversion_budget V U T hV hU hT
    (lemmaUpwardCrux_of_hardRegime U hU k hHard)

end Kolmogorov
