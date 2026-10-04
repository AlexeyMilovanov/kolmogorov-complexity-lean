/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Interface.StandardMachine
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.NonStochasticFinal
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Core.Invariance
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure.Part01
import KolmogorovMathlib.Prefix.SelfDelimitingMachines
import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs
import KolmogorovMathlib.AlgorithmicProbability.HaltingProbabilityApproximation
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part01
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part02
import KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse
import KolmogorovMathlib.Prefix.BlockingReadMachines
import KolmogorovMathlib.Prefix.ExtensionTheorem
import KolmogorovMathlib.Prefix.NumericalValues
import KolmogorovMathlib.Prefix.PairComplexity
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.Restricted.HammingGap
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedStochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CubeStochasticity
import KolmogorovMathlib.Restricted.DeficiencyEquiv
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure

/-!
# Numerical randomness deficiency and the mass of the non-stochastic strings

The randomness deficiency `d(x | A) = log #A - K(x | A)` and the optimality
deficiency `delta(x | A) = log #A + K(A) - K(x)` as `ℕ∞`-valued functions
(`deficiencyValue`, `optimalityDeficiencyValue`), the fraction of a finite set
taken up by strings of large deficiency, the passage from a probability model to
a uniform set model, and the mass `nonStochasticMass` of the non-stochastic
strings of a given length together with its two-sided bound.

As everywhere in this library these notions are based on the *prefix*
complexity, which differs from the book's plain complexity by `O(log)` terms
absorbed in the explicit `logSlack` slacks; `sqrtLogSlack` is the
`O(sqrt (n log n))` slack of the Hamming-ball statements.

SUV Chapter 14 (algorithmic statistics), Sections 14.1-14.4.
-/

namespace Kolmogorov


open CodedFiniteDistribution
open scoped ENNReal
open Nat.Partrec (Code)

/-! ### Numerical randomness deficiency -/

/-- The randomness deficiency `d(x | A) = log #A - K(x | A)` of `x` in the finite
set `A`, as the least bound accepted by the library predicate `DeficiencyLe`. -/
noncomputable def deficiencyValue (U : Map) (A : Finset BitString) (hA : A.Nonempty)
    (x : BitString) : ℕ∞ :=
  sInf {b : ℕ∞ | ∃ beta : ℕ, (beta : ℕ∞) = b ∧ DeficiencyLe U (codedUniformOn A hA) x beta}

/-- The optimality deficiency `δ(x | A) = log #A + K(A) - K(x)` of `x` in `A`, as
the least bound accepted by `SetOptimalityDeficiencyLe`. -/
noncomputable def optimalityDeficiencyValue (U : Map) (A : Finset BitString) (hA : A.Nonempty)
    (x : BitString) : ℕ∞ :=
  sInf {b : ℕ∞ | ∃ beta : ℕ, (beta : ℕ∞) = b ∧ SetOptimalityDeficiencyLe U A hA x beta}

/-- An `O(√(n log n))` slack, used for the precision of the Hamming-ball
statements of Section 14.4. -/
def sqrtLogSlack (c n : ℕ) : ℕ := c * (Nat.sqrt (n * (Nat.log 2 n + 1)) + 1)

/-- A deficiency test: a lower-semicomputable function of a string and the code
of a finite set. -/
def IsLowerSemicomputableTest (delta : BitString → BitString → ℕ) : Prop :=
  IsRE (fun p : (BitString × BitString) × ℕ => p.2 < delta p.1.1 p.1.2)

open Classical in
/-- **Exercise 345.** In every finite set, the fraction of elements of randomness
deficiency greater than `k` is at most `2^{-k}` (up to a constant factor). -/
theorem fraction_deficiency_gt_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (k : ℕ),
      (A.filter (fun x => ¬ DeficiencyLe U (codedUniformOn A hA) x k)).card * 2 ^ k
        ≤ 2 ^ c * A.card := by
  use 0
  intro A hA k
  simp only [pow_zero, one_mul]
  set P := codedUniformOn A hA
  set S := A.filter (fun x => ¬ DeficiencyLe U P x k)
  have hA_pos : 0 < A.card := Finset.Nonempty.card_pos hA
  have hA_ne_zero : (A.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hA_pos
  have hA_ne_top : (A.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h_sum : ∑ x ∈ S, ((2 : ℝ≥0∞) ^ k * (A.card : ℝ≥0∞)⁻¹) ≤ 1 := by
    calc ∑ x ∈ S, ((2 : ℝ≥0∞) ^ k * (A.card : ℝ≥0∞)⁻¹)
      _ ≤ ∑ x ∈ S, complexityWeight (KP U x P.code) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_filter] at hx
        have h_mass : P.mass x = (A.card : ℝ≥0∞)⁻¹ := codedUniformOn_mass_of_mem A hA x hx.1
        have h_not_def : ¬ complexityWeight (KP U x P.code) ≤ (2 : ℝ≥0∞) ^ k * P.mass x := hx.2
        rw [h_mass] at h_not_def
        exact le_of_lt (not_le.mp h_not_def)
      _ ≤ ∑' x : BitString, complexityWeight (KP U x P.code) := ENNReal.sum_le_tsum S
      _ ≤ 1 := _root_.Kolmogorov.KP_kraft_sum_le_one U hU.isPrefixDecompressor P.code
  rw [Finset.sum_const, nsmul_eq_mul] at h_sum
  have h_mul' : (S.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k * ((A.card : ℝ≥0∞)⁻¹ * (A.card : ℝ≥0∞))
      ≤ (A.card : ℝ≥0∞) := by
    calc (S.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k * ((A.card : ℝ≥0∞)⁻¹ * (A.card : ℝ≥0∞))
      _ = ((S.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ k * (A.card : ℝ≥0∞)⁻¹)) * (A.card : ℝ≥0∞) := by ring
      _ ≤ 1 * (A.card : ℝ≥0∞) := by gcongr
      _ = (A.card : ℝ≥0∞) := one_mul _
  rw [ENNReal.inv_mul_cancel hA_ne_zero hA_ne_top, mul_one] at h_mul'
  exact_mod_cast h_mul'

/-- `PlainDeficiencyLe U P x beta` asserts that the plain randomness deficiency of `x` with
respect to the model `P` is bounded by `beta`. -/
noncomputable def PlainDeficiencyLe (U : Map) (P : CodedFiniteDistribution)
    (x : BitString) (beta : ℕ) : Prop :=
  complexityWeight (condK U x P.code) ≤ (2 : ℝ≥0∞) ^ beta * P.mass x

/-- The plain randomness deficiency `d(x | A) = log #A - C(x | A)` of `x` in the finite
set `A`, as the least bound accepted by the library predicate `PlainDeficiencyLe`. -/
noncomputable def plainDeficiencyValue (U : Map) (A : Finset BitString) (hA : A.Nonempty)
    (x : BitString) : ℕ∞ :=
  sInf {b : ℕ∞ | ∃ beta : ℕ, (beta : ℕ∞) = b ∧ PlainDeficiencyLe U (codedUniformOn A hA) x beta}

-- `exercise346_deficiency_maximal` (ch14-exercise-346) is archived; see `docs/ARCHIVED_TARGETS.md`.

/-- **Exercise 348.** An arbitrary finite hypothesis can be replaced by a uniform
finite-set hypothesis with logarithmic overhead in both complexity and
deficiency. -/
theorem distribution_to_uniform_set_model (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n k l : ℕ) (P : CodedFiniteDistribution),
      x.length = n → P.IsProbability → P.complexity U ≤ (k : ℕ∞) →
      DeficiencyLe U P x l →
      ∃ (A : Finset BitString) (hA : A.Nonempty), x ∈ A ∧
        setComplexity U A hA ≤ ((k + logSlack c (l + n) : ℕ) : ℕ∞) ∧
        DeficiencyLe U (codedUniformOn A hA) x (l + logSlack c (l + n)) := by
  obtain ⟨c_gate, h_gate⟩ := levelSet_randomness_deficiency_le_gate U hU
  obtain ⟨c_comp, h_comp⟩ := levelSetModel_setComplexity_le U hU
  obtain ⟨c_lb, h_lb⟩ := levelSet_level_bound U hU
  obtain ⟨C_comp, hC_comp⟩ := logSlack_fold_level c_comp c_lb
  obtain ⟨C_gate, hC_gate⟩ := logSlack_fold_level c_gate c_lb
  refine ⟨C_comp + C_gate + 1, ?_⟩
  intro x n k l P h_len hP h_comp_P h_def_P
  have h_mass_pos : P.mass x > 0 :=
    mass_pos_of_deficiencyLe_of_KP_ne_top h_def_P (KP_ne_top_of_optimal U hU x P.code)
  have h_mass_le1 : P.mass x ≤ 1 := mass_le_one_of_isProbability P hP x
  obtain ⟨k_level, h_k_lower, h_k_upper⟩ := exists_k_mass P x h_mass_pos h_mass_le1
  have h_supp : x ∈ P.support := by
    by_contra hx
    exact absurd (CodedFiniteDistribution.mass_eq_zero_of_not_mem_support P x hx)
      (ne_of_gt h_mass_pos)
  let A := levelSet P k_level
  have hA : A.Nonempty := levelSet_nonempty_of_mass_ge P x k_level h_supp h_k_lower
  have hxA : x ∈ A := mem_levelSet h_supp h_k_lower
  obtain ⟨d0, hd0_def, hd0_le⟩ :=
    h_gate P x k_level hP h_supp h_k_lower h_k_upper l h_def_P
  use A, hA
  refine ⟨hxA, ?_, ?_⟩
  · have h1 : setComplexity U A hA ≤ P.complexity U + (logSlack c_comp k_level : ENat) :=
      h_comp P k_level hA
    have h_k_bound : k_level ≤ n + l + logSlack c_lb n :=
      h_lb P x n l k_level h_len h_def_P h_k_upper
    have h_fold : logSlack c_comp k_level ≤ logSlack C_comp (n + 0 + l) :=
      hC_comp n 0 l k_level h_k_bound
    have h_eq : n + 0 + l = l + n := by omega
    rw [h_eq] at h_fold
    have h_slack_mono : logSlack C_comp (l + n) ≤ logSlack (C_comp + C_gate + 1) (l + n) :=
      logSlack_mono_left (by omega) _
    have h2 : setComplexity U A hA ≤
        (k : ENat) + (logSlack (C_comp + C_gate + 1) (l + n) : ENat) := by
      calc setComplexity U A hA ≤ P.complexity U + (logSlack c_comp k_level : ENat) := h1
        _ ≤ (k : ENat) + (logSlack C_comp (l + n) : ENat) := by gcongr
        _ ≤ (k : ENat) + (logSlack (C_comp + C_gate + 1) (l + n) : ENat) := by gcongr
    have h3 : (k : ENat) + (logSlack (C_comp + C_gate + 1) (l + n) : ENat) =
        (((k + logSlack (C_comp + C_gate + 1) (l + n) : ℕ) : ENat)) := by
      push_cast; rfl
    rwa [h3] at h2
  · have h_k_bound : k_level ≤ n + l + logSlack c_lb n :=
      h_lb P x n l k_level h_len h_def_P h_k_upper
    have h_fold : logSlack c_gate k_level ≤ logSlack C_gate (n + 0 + l) :=
      hC_gate n 0 l k_level h_k_bound
    have h_eq : n + 0 + l = l + n := by omega
    rw [h_eq] at h_fold
    have h_slack_mono : logSlack C_gate (l + n) ≤ logSlack (C_comp + C_gate + 1) (l + n) :=
      logSlack_mono_left (by omega) _
    have hd0_bound : d0 ≤ l + logSlack (C_comp + C_gate + 1) (l + n) := by
      calc d0 ≤ l + logSlack c_gate k_level := hd0_le
        _ ≤ l + logSlack C_gate (l + n) := by gcongr
        _ ≤ l + logSlack (C_comp + C_gate + 1) (l + n) := by gcongr
    exact DeficiencyLe.mono_beta hd0_bound hd0_def

/-! ### Martin-Löf randomness with respect to a computable measure

Problem 349 speaks of an arbitrary computable measure on the Cantor space, i.e.
one whose cylinder masses are uniformly computable *reals*.  That notion is the
library's `Kolmogorov.IsComputableMeasure` on `MeasureTheory.Measure CantorSeq`
(`AlgorithmicRandomness/ComputableMeasure.lean`), and Martin-Löf randomness for
it is `Kolmogorov.IsMartinLofRandom` (`AlgorithmicRandomness/MartinLof.lean`).
An earlier rendering of this exercise introduced a private notion of computable
measure with *exactly rational* cylinder masses; that class is a strict subclass
of the computable measures, so it weakened both halves of the problem (the first
by assuming more of `ν`, the second by defeating fewer `ν`).  It has been removed
in favour of the general API. -/

-- `exercise349_random_prefixes_stochastic` (ch14-exercise-349) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

/-- **Exercise 349, second part.** There is an infinite sequence that is not
Martin-Löf random with respect to any computable measure.  This is SUV
Theorem 122; the library proves it in
`MonotoneComplexity/Dimension/ChangeOfMeasure.lean`. -/
theorem exists_not_martinLofRandom_computableMeasure :
    ∃ w : _root_.CantorSeq, ∀ mu : MeasureTheory.Measure _root_.CantorSeq,
      MeasureTheory.IsProbabilityMeasure mu → Kolmogorov.IsComputableMeasure mu →
        ¬ Kolmogorov.IsMartinLofRandom mu w :=
  Kolmogorov.exists_not_isMartinLofRandom_forall_isComputableMeasure_diag

/-! ### Stochasticity: the universal bound and the counting lower bounds -/

/-- **Theorem 249.** If `alpha + beta ≥ n + O(log n)` and `alpha ≥ O(log n)`, then every string
of length `n` is `(alpha, beta)`-stochastic. -/
theorem isStochastic_of_add_ge (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n alpha beta : ℕ), x.length = n →
      logSlack c n ≤ alpha →
      n + logSlack c n ≤ alpha + beta → IsStochastic U x alpha beta := by
  obtain ⟨c1, hc1⟩ := structureFunction_prefix_upper_of_optimal U hU
  obtain ⟨c2, hc2⟩ := isStochastic_of_inDescriptionProfile U hU
  refine ⟨c1 + c2, fun x n alpha beta h_len h_alpha h_sum => ?_⟩
  set k := n - min n beta
  have hk_le_n : k ≤ n := Nat.sub_le n (min n beta)
  have hprof := hc1 x n k h_len hk_le_n
  have hstoch := hc2 x (k + logSlack c1 n) (n - k) hprof
  have h_alpha_bound : k + logSlack c1 n + c2 ≤ alpha := by
    have h1 : logSlack c1 n + c2 ≤ logSlack (c1 + c2) n := by
      unfold logSlack
      have : c1 * (Nat.bits n).length + c2 * (Nat.bits n).length =
          (c1 + c2) * (Nat.bits n).length := by ring
      omega
    have h2 : k + logSlack (c1 + c2) n ≤ alpha := by
      dsimp [k]
      by_cases h_beta : beta ≤ n
      · rw [min_eq_right h_beta]
        omega
      · have h_n_lt : n < beta := not_le.mp h_beta
        rw [min_eq_left (le_of_lt h_n_lt), Nat.sub_self, zero_add]
        exact h_alpha
    omega
  have h_beta_bound : n - k ≤ beta := by
    dsimp [k]
    by_cases h_beta : beta ≤ n
    · rw [min_eq_right h_beta, Nat.sub_sub_self h_beta]
    · have h_n_lt : n < beta := not_le.mp h_beta
      rw [min_eq_left (le_of_lt h_n_lt), Nat.sub_self, Nat.sub_zero]
      exact le_of_lt h_n_lt
  exact isStochastic_mono h_alpha_bound h_beta_bound hstoch

-- `theorem250_nonstochastic_fraction` (ch14-theorem-250) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

/-- The five selector parameters `(n, alpha, max_k, h, i)`, each in binary, packed
into one string by nested pairing. -/
def pack5 (n alpha max_k h i : ℕ) : BitString :=
  pairCode (natBits n)
    (pairCode (natBits alpha)
      (pairCode (natBits max_k)
        (pairCode (natBits h) (natBits i))))

/-- The string length `n` read off a five-parameter selector input. -/
def selector5Length (s : BitString) : ℕ := Kolmogorov.bitsToNat (decodeFirst s)
/-- The complexity bound `alpha` read off a five-parameter selector input. -/
def selector5Alpha (s : BitString) : ℕ := Kolmogorov.bitsToNat (decodeFirst (decodeSecond s))
/-- The level bound `max_k` read off a five-parameter selector input. -/
def selector5MaxK (s : BitString) : ℕ :=
  Kolmogorov.bitsToNat (decodeFirst (decodeSecond (decodeSecond s)))
/-- The halting-count advice read off a five-parameter selector input. -/
def selector5HaltCount (s : BitString) : ℕ :=
  Kolmogorov.bitsToNat (decodeFirst (decodeSecond (decodeSecond (decodeSecond s))))
/-- The index of the wanted uncovered string, read off a five-parameter selector
input. -/
def selector5Index (s : BitString) : ℕ :=
  Kolmogorov.bitsToNat (decodeSecond (decodeSecond (decodeSecond (decodeSecond s))))

/-- Reading the complexity bound off the input is primitive recursive. -/
theorem selector5Alpha_primrec : Primrec selector5Alpha :=
  Kolmogorov.bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp
    CodedFiniteDistribution.decodeSecond_primrec)

/-- Reading the level bound off the input is primitive recursive. -/
theorem selector5MaxK_primrec : Primrec selector5MaxK :=
  Kolmogorov.bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp
    (CodedFiniteDistribution.decodeSecond_primrec.comp
    CodedFiniteDistribution.decodeSecond_primrec))

/-- Reading the halting-count advice off the input is primitive recursive. -/
theorem selector5HaltCount_primrec : Primrec selector5HaltCount :=
  Kolmogorov.bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp
    (CodedFiniteDistribution.decodeSecond_primrec.comp
    (CodedFiniteDistribution.decodeSecond_primrec.comp
      CodedFiniteDistribution.decodeSecond_primrec)))

/-- Reading the index off the input is primitive recursive. -/
theorem selector5Index_primrec : Primrec selector5Index :=
  Kolmogorov.bitsToNat_primrec.comp (CodedFiniteDistribution.decodeSecond_primrec.comp
    (CodedFiniteDistribution.decodeSecond_primrec.comp
    (CodedFiniteDistribution.decodeSecond_primrec.comp
      CodedFiniteDistribution.decodeSecond_primrec)))

/-- The strings of length `n` that no distribution enumerated within `t` steps
covers at any level up to `max_k`. -/
def uncoveredStrings (c : Code) (st : BitString × ℕ) : List BitString :=
  (allStrings (selector5Length st.1)).filter
    (fun x => !coveredBool (snapshotCodes c (selector5Alpha st.1) st.2) (selector5MaxK st.1) x)

/-- The uncovered string of the index requested by the input, if there is one. -/
def uncoveredStringAt (c : Code) (st : BitString × ℕ) : Option BitString :=
  (uncoveredStrings c st)[selector5Index st.1]?

/-- Testing whether the number of programs that have halted by stage `t` equals the
advice is computable. -/
theorem selector5HaltCheck_computable (c : Code) :
    Computable (fun (st : BitString × ℕ) =>
      decide (countHalts c (selector5Alpha st.1) st.2 = selector5HaltCount st.1)) := by
  have h_eq : Computable (fun (p : ℕ × ℕ) => decide (p.1 = p.2)) :=
    (Primrec.eq : PrimrecRel (α := ℕ) Eq).decide.to_comp
  have h_selAlpha : Computable (fun (st : BitString × ℕ) => selector5Alpha st.1) :=
    @Computable.comp (BitString × ℕ) BitString ℕ _ _ _ selector5Alpha (fun st =>
      st.1) selector5Alpha_primrec.to_comp Computable.fst
  have h_count : Computable (fun (st : BitString × ℕ) => countHalts c (selector5Alpha st.1) st.2) :=
    @Computable.comp (BitString × ℕ) (ℕ × ℕ) ℕ _ _ _ (fun p => countHalts c p.1 p.2) (fun st =>
      (selector5Alpha st.1, st.2)) (countHalts_computable c)
      (Computable.pair h_selAlpha Computable.snd)
  have h_selH : Computable (fun (st : BitString × ℕ) => selector5HaltCount st.1) :=
    @Computable.comp (BitString × ℕ) BitString ℕ _ _ _ selector5HaltCount (fun st =>
      st.1) selector5HaltCount_primrec.to_comp Computable.fst
  exact @Computable.comp (BitString × ℕ) (ℕ × ℕ) Bool _ _ _ (fun p => decide (p.1 = p.2)) (fun st =>
    (countHalts c (selector5Alpha st.1) st.2, selector5HaltCount st.1)) h_eq
    (Computable.pair h_count h_selH)

/-- The canonical input string of the five-parameter selector. -/
def selectorInput5 (n alpha max_k h i : ℕ) : BitString := pack5 n alpha max_k h i

/-- The length parameter is read back from the packed input. -/
@[simp] theorem selector5Length_selectorInput5 (n alpha max_k h i : ℕ) :
    selector5Length (selectorInput5 n alpha max_k h i) = n := by
  dsimp [selector5Length, selectorInput5, pack5]
  rw [decodeFirst_pairCode]
  exact Kolmogorov.bitsToNat_bits n

/-- The complexity bound is read back from the packed input. -/
@[simp] theorem selector5Alpha_selectorInput5 (n alpha max_k h i : ℕ) :
    selector5Alpha (selectorInput5 n alpha max_k h i) = alpha := by
  dsimp [selector5Alpha, selectorInput5, pack5]
  rw [decodeSecond_pairCode, decodeFirst_pairCode]
  exact Kolmogorov.bitsToNat_bits alpha

/-- The level bound is read back from the packed input. -/
@[simp] theorem selector5MaxK_selectorInput5 (n alpha max_k h i : ℕ) :
    selector5MaxK (selectorInput5 n alpha max_k h i) = max_k := by
  dsimp [selector5MaxK, selectorInput5, pack5]
  rw [decodeSecond_pairCode, decodeSecond_pairCode, decodeFirst_pairCode]
  exact Kolmogorov.bitsToNat_bits max_k

/-- The halting-count advice is read back from the packed input. -/
@[simp] theorem selector5HaltCount_selectorInput5 (n alpha max_k h i : ℕ) :
    selector5HaltCount (selectorInput5 n alpha max_k h i) = h := by
  dsimp [selector5HaltCount, selectorInput5, pack5]
  rw [decodeSecond_pairCode, decodeSecond_pairCode, decodeSecond_pairCode, decodeFirst_pairCode]
  exact Kolmogorov.bitsToNat_bits h

/-- The index is read back from the packed input. -/
@[simp] theorem selector5Index_selectorInput5 (n alpha max_k h i : ℕ) :
    selector5Index (selectorInput5 n alpha max_k h i) = i := by
  dsimp [selector5Index, selectorInput5, pack5]
  rw [decodeSecond_pairCode, decodeSecond_pairCode, decodeSecond_pairCode, decodeSecond_pairCode]
  exact Kolmogorov.bitsToNat_bits i

/-- Reading the length parameter off the input is primitive recursive. -/
theorem selector5Length_primrec : Primrec selector5Length :=
  Kolmogorov.bitsToNat_primrec.comp CodedFiniteDistribution.decodeFirst_primrec

private theorem uncoveredStrings_primrec (c : Code) : Primrec (uncoveredStrings c) := by
  unfold uncoveredStrings
  have h_snap : Primrec (fun (st : BitString × ℕ) => snapshotCodes c (selector5Alpha st.1) st.2) :=
    (snapshotCodes_primrec c).comp
      (Primrec.pair (selector5Alpha_primrec.comp Primrec.fst) Primrec.snd)
  have h_maxK : Primrec (fun (st : BitString × ℕ) => selector5MaxK st.1) :=
    selector5MaxK_primrec.comp Primrec.fst
  have h_pair : Primrec (fun (st : BitString × ℕ) =>
      (snapshotCodes c (selector5Alpha st.1) st.2, selector5MaxK st.1)) :=
    Primrec.pair h_snap h_maxK
  have h_cov : Primrec₂ (fun (st : BitString × ℕ) (x : BitString) =>
      coveredBool (snapshotCodes c (selector5Alpha st.1) st.2) (selector5MaxK st.1) x) :=
    (coveredBool_primrec.comp (Primrec.pair (h_pair.comp Primrec.fst) Primrec.snd)).to₂
  have h_notCov : Primrec₂ (fun (st : BitString × ℕ) (x : BitString) =>
      !coveredBool (snapshotCodes c (selector5Alpha st.1) st.2) (selector5MaxK st.1) x) :=
    Primrec.not.comp h_cov
  have h_all : Primrec (fun (st : BitString × ℕ) => allStrings (selector5Length st.1)) :=
    CodedFiniteDistribution.allStrings_primrec.comp (selector5Length_primrec.comp Primrec.fst)
  exact list_filter_primrec h_all h_notCov

private theorem uncoveredStringAt_primrec (c : Code) : Primrec (uncoveredStringAt c) :=
  Primrec.list_getElem?.comp (uncoveredStrings_primrec c) (selector5Index_primrec.comp Primrec.fst)

/-- The requested uncovered string at stage `t`, as a partial value. -/
def uncoveredStringPart (c : Code) (s : BitString) (t : ℕ) : Part BitString :=
  Part.ofOption (uncoveredStringAt c (s, t))

private theorem uncoveredStringPart_partrec₂ (c : Code) : Partrec₂ (uncoveredStringPart c) :=
  (Computable.ofOption (uncoveredStringAt_primrec c).to_comp).to₂

/-- The selector that waits for the stage at which the halting count matches the
advice and then returns the uncovered string of the requested index. -/
noncomputable def uncoveredStringSelector (c : Code) : BitString →. BitString := fun s =>
  (Nat.rfind (fun t =>
      Part.some (decide (countHalts c (selector5Alpha s) t = selector5HaltCount s)))).bind
    (fun t => uncoveredStringPart c s t)

private theorem uncoveredStringSelector_spec (c : Code) (s : BitString) (t : ℕ) (x : BitString)
    (ht : countHalts c (selector5Alpha s) t = selector5HaltCount s)
    (ht_min : ∀ m < t, countHalts c (selector5Alpha s) m ≠ selector5HaltCount s)
    (hx : uncoveredStringAt c (s, t) = some x) :
    x ∈ uncoveredStringSelector c s := by
  dsimp [uncoveredStringSelector, uncoveredStringPart]
  rw [Part.mem_bind_iff]
  refine ⟨t, ?_, ?_⟩
  · refine Nat.mem_rfind.mpr ⟨by simp [ht], ?_⟩
    intro m hm
    rw [Part.mem_some_iff]
    exact (decide_eq_false_iff_not.mpr (ht_min m hm)).symm
  · rw [Part.mem_ofOption]
    exact hx

/-- The uncovered-string selector is a partial recursive function of its input. -/
theorem partrec_uncoveredStringSelector (c : Code) : Partrec (uncoveredStringSelector c) := by
  have h_search : Partrec (fun s : BitString =>
      Nat.rfind (fun t =>
        Part.some (decide (countHalts c (selector5Alpha s) t = selector5HaltCount s)))) :=
    Partrec.rfind (selector5HaltCheck_computable c).partrec
  exact (Partrec.bind h_search (uncoveredStringPart_partrec₂ c)).of_eq (fun s => rfl)

attribute [irreducible] selectorInput5 uncoveredStringSelector uncoveredStringPart

/-- The number of entries satisfying a disjunction is at most the sum of the two
counts. -/
theorem countP_or_le {α} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.countP_cons]
    by_cases hp : p x = true <;> by_cases hq : q x = true <;> simp [hp, hq] <;> omega

/-- The number of entries satisfying at least one of a list of tests is at most the
sum of the counts of the individual tests. -/
theorem countP_any_le {α β} (l : List α) (codes : List β) (f : α → β → Bool) :
    l.countP (fun x => codes.any (f x)) ≤ (codes.map (fun w => l.countP (f · w))).sum := by
  induction codes with
  | nil => simp
  | cons w ws ih =>
    simp only [List.any_cons, List.map_cons, List.sum_cons]
    have h_step := countP_or_le l (f · w) (fun x => ws.any (f x))
    omega

open CodedFiniteDistribution

/-- A probability distribution has at most `2 ^ k` strings in its `k`-th level set. -/
theorem countP_levelSetMemBool_le (w : BitString) (k n : ℕ) (hprob : isProbBool w = true) :
    (allStrings n).countP (fun x => levelSetMemBool w k x) ≤ 2 ^ k := by
  have h_sub : ((allStrings n).filter (fun x => levelSetMemBool w k x)).toFinset ⊆
      levelSet (decodeCodedFiniteDistribution w) k := by
    intro x hx
    rw [List.mem_toFinset, List.mem_filter] at hx
    rw [levelSetMemBool_iff w k x] at hx
    exact hx.2
  have h_card1 : ((allStrings n).filter (fun x => levelSetMemBool w k x)).length =
      ((allStrings n).filter (fun x => levelSetMemBool w k x)).toFinset.card := by
    rw [List.toFinset_card_of_nodup ((allStrings_nodup n).filter _)]
  have h_card2 : ((allStrings n).filter (fun x => levelSetMemBool w k x)).toFinset.card ≤
      (levelSet (decodeCodedFiniteDistribution w) k).card := Finset.card_le_card h_sub
  have h_prob_is := (isProbBool_iff w).mp hprob
  have h_level := levelSet_card_le (decodeCodedFiniteDistribution w) k h_prob_is
  have h_level_nat : (levelSet (decodeCodedFiniteDistribution w) k).card ≤ 2 ^ k := by
    exact_mod_cast h_level
  rw [List.countP_eq_length_filter, h_card1]
  exact h_card2.trans h_level_nat

/-- Fewer than `2 ^ (alpha + 1)` programs of length at most `alpha` can halt. -/
theorem countHalts_lt_pow (c : Code) (alpha t : ℕ) : countHalts c alpha t < 2 ^ (alpha + 1) := by
  dsimp [countHalts]
  exact (List.countP_le_length).trans_lt (length_boundedPrograms_lt alpha)

/-- The strings of length `n` covered by a snapshot at some level up to `max_k`
number at most `snap.length * (max_k + 1) * 2 ^ max_k`. -/
theorem countP_coveredBool_le (snap : List BitString) (max_k n : ℕ) :
    (allStrings n).countP (coveredBool snap max_k) ≤ snap.length * (max_k + 1) * 2 ^ max_k := by
  unfold coveredBool
  have h1 := countP_any_le (allStrings n) snap (fun x w =>
    isValidCodeBool w && isProbBool w && (List.range (max_k + 1)).any (fun k =>
      levelSetMemBool w k x))
  have h2 : ∀ w ∈ snap,
    (allStrings n).countP (fun x =>
    isValidCodeBool w && isProbBool w && (List.range (max_k + 1)).any (fun k =>
    levelSetMemBool w k x)) ≤ (max_k + 1) * 2 ^ max_k := by
    intro w _
    by_cases hw : isValidCodeBool w && isProbBool w
    · have h_eq : (fun x =>
      isValidCodeBool w && isProbBool w && (List.range (max_k + 1)).any (fun k =>
      levelSetMemBool w k x)) =
          (fun x => (List.range (max_k + 1)).any (fun k => levelSetMemBool w k x)) := by
        ext x; simp [hw]
      rw [h_eq]
      have h3 :=
        countP_any_le (allStrings n) (List.range (max_k + 1)) (fun x k => levelSetMemBool w k x)
      have h4 : ((List.range (max_k + 1)).map (fun k => (allStrings n).countP (fun x =>
        levelSetMemBool w k x))).sum ≤ (max_k + 1) * 2 ^ max_k := by
        have h_sum_le : ∀ k ∈ List.range (max_k + 1),
          (allStrings n).countP (fun x => levelSetMemBool w k x) ≤ 2 ^ max_k := by
          intro k hk
          rw [List.mem_range, Nat.lt_succ_iff] at hk
          exact (countP_levelSetMemBool_le w k n (Bool.and_elim_right
            hw)).trans (Nat.pow_le_pow_right (by decide) hk)
        have h_sum :=
          List.sum_le_length_nsmul ((List.range (max_k + 1)).map (fun k =>
          (allStrings n).countP (fun x => levelSetMemBool w k x))) (2 ^ max_k) (by
          intro y hy
          rw [List.mem_map] at hy
          obtain ⟨k, hk, rfl⟩ := hy
          exact h_sum_le k hk)
        simp only [List.length_map, List.length_range] at h_sum
        exact h_sum
      exact h3.trans h4
    · have h_false : (fun x =>
      isValidCodeBool w && isProbBool w && (List.range (max_k + 1)).any (fun k =>
      levelSetMemBool w k x)) = fun _ => false := by
        ext x; simp [hw]
      rw [h_false, List.countP_false]
      positivity
  have h_sum_snap :=
    List.sum_le_length_nsmul (snap.map (fun w => (allStrings n).countP (fun x =>
    isValidCodeBool w && isProbBool w && (List.range (max_k + 1)).any (fun k =>
    levelSetMemBool w k x)))) ((max_k + 1) * 2 ^ max_k) (by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact h2 w hw)
  simp only [List.length_map] at h_sum_snap
  have h_mul_assoc : snap.length * ((max_k + 1) * 2 ^ max_k) = snap.length * (max_k + 1)
    * 2 ^ max_k := by ring
  exact h1.trans (h_sum_snap.trans_eq h_mul_assoc)

/-- The arithmetic behind the deficiency bound: with the stated constants, the
selector's program length plus its overhead stays below `n - beta - c₂`. -/
theorem selector_length_arith_bridge (n alpha beta c_2 c_partrec c_len c0 c L_s B : ℕ)
    (hc0 : c0 = c_2 + c_partrec + c_len + 30)
    (hc : c = 2 * c0 + 40)
    (hB : B = (Nat.bits n).length)
    (h_bits : 1 ≤ B)
    (hgap : alpha + beta + logSlack c n < n)
    (h_s_len : L_s ≤ (n - alpha - beta - logSlack c n) + 10 * B + 20) :
    L_s + 2 * (B + 5) + c_len + c_partrec ≤ n - beta - c_2 := by
  have h_log : logSlack c n = c * B + c := by rw [hB]; rfl
  have h_cB : c * B + c ≥ c_2 + c_partrec + c_len + 12 * B + 30 := by
    have h1 : c_2 ≤ c_2 * B := Nat.le_mul_of_pos_right _ h_bits
    have h2 : c_partrec ≤ c_partrec * B := Nat.le_mul_of_pos_right _ h_bits
    have h3 : c_len ≤ c_len * B := Nat.le_mul_of_pos_right _ h_bits
    subst hc hc0
    nlinarith [h1, h2, h3, h_bits]
  rw [h_log] at hgap h_s_len
  omega

private theorem KP_le_of_selector_bounds (KP_x KP_s : ENat) (c_partrec c_len L_s B n beta c_2 : ℕ)
    (h_eval : KP_x ≤ KP_s + (c_partrec : ENat))
    (h_s_KP : KP_s ≤ ((L_s + 2 * B + c_len : ℕ) : ENat))
    (h_s_bound : L_s + 2 * B + c_len + c_partrec ≤ n - beta - c_2) :
    KP_x ≤ ((n - beta - c_2 : ℕ) : ENat) := by
  have h1 : KP_s + (c_partrec : ENat) ≤ ((L_s + 2 * B + c_len : ℕ) : ENat) + (c_partrec : ENat) :=
    add_le_add h_s_KP le_rfl
  have h2 : ((L_s + 2 * B + c_len : ℕ) : ENat) + (c_partrec : ENat) =
      ((L_s + 2 * B + c_len + c_partrec : ℕ) : ENat) := by push_cast; rfl
  have h3 : ((L_s + 2 * B + c_len + c_partrec : ℕ) : ENat) ≤ ((n - beta - c_2 : ℕ) : ENat) := by
    exact_mod_cast h_s_bound
  exact h_eval.trans (h1.trans (h2.le.trans h3))

private theorem selector_cover_bound (n alpha beta c_2 c_partrec c_len c0 c max_k K B : ℕ)
    (hc0 : c0 = c_2 + c_partrec + c_len + 30)
    (hc : c = 2 * c0 + 40)
    (hB : B = (Nat.bits n).length)
    (hmk : max_k = n - alpha - beta - B - 3)
    (hK : K = 2 ^ (n - (alpha + beta + logSlack c n)))
    (h_bits : 1 ≤ B)
    (hgap : alpha + beta + logSlack c n < n) :
    2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k + K ≤ 2 ^ n := by
  have h_c : c ≥ 100 := by subst hc hc0; omega
  have h_sum : alpha + beta + B + 3 ≤ n := by
    have h_slack : logSlack c n ≥ B + 3 := by
      unfold logSlack
      rw [hB]
      nlinarith [h_bits, h_c]
    omega
  have h1 : max_k + 1 ≤ 2 ^ B := by
    have : max_k + 1 < n := by subst hmk; omega
    have h_pow : n ≤ 2 ^ B := by rw [hB]; exact (lt_two_pow_length_natBits n).le
    exact this.le.trans h_pow
  have h2 : 2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k ≤ 2 ^ (n - 2) := by
    have h_exp : B + (alpha + 1 + max_k) ≤ n - 2 := by
      subst hmk
      omega
    have h_c1 : 2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k = (max_k + 1) * 2 ^ (alpha + 1 + max_k) :=
      by ring_nf
    have h_c2 : (max_k + 1) * 2 ^ (alpha + 1 + max_k) ≤ 2 ^ B * 2 ^ (alpha + 1 + max_k) :=
      Nat.mul_le_mul_right _ h1
    have h_c3 : 2 ^ B * 2 ^ (alpha + 1 + max_k) = 2 ^ (B + (alpha + 1 + max_k)) := by rw [← pow_add]
    have h_c4 : 2 ^ (B + (alpha + 1 + max_k)) ≤ 2 ^ (n - 2) :=
      Nat.pow_le_pow_right (by decide) h_exp
    omega
  have h3 : K ≤ 2 ^ (n - 2) := by
    have h_K_exp : n - (alpha + beta + logSlack c n) ≤ n - 2 := by
      have h_slack : logSlack c n ≥ 2 := by unfold logSlack; subst hc hc0; omega
      omega
    rw [hK]
    exact Nat.pow_le_pow_right (by decide) h_K_exp
  have h4 : 2 ^ (n - 2) + 2 ^ (n - 2) ≤ 2 ^ n := by
    have h_pow : 2 ^ (n - 2) + 2 ^ (n - 2) = 2 ^ (n - 2 + 1) := by rw [← mul_two, ← pow_succ]
    rw [h_pow]
    refine Nat.pow_le_pow_right (by decide) (by omega)
  have h_add : 2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k + K ≤ 2 ^ (n - 2) + 2 ^ (n - 2) :=
    Nat.add_le_add h2 h3
  exact h_add.trans h4

/-- Filtering out the entries satisfying a test leaves the length minus the count of
that test. -/
theorem length_filter_not {α} (l : List α) (p : α → Bool) :
    (l.filter (fun x => !p x)).length = l.length - l.countP p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, List.countP_cons, List.length_cons]
    have h_le : xs.countP p ≤ xs.length := List.countP_le_length
    by_cases hp : p x
    · have h_not : (!p x) = false := by rw [hp]; rfl
      rw [h_not, hp]
      dsimp
      rw [ih]
      omega
    · have hp' : p x = false := Bool.eq_false_of_not_eq_true hp
      have h_not : (!p x) = true := by rw [hp']; rfl
      rw [h_not, hp']
      dsimp
      rw [ih]
      omega

/-- When the three auxiliary parameters need no more bits than `n`, the packed input
is at most `|i| + 8 * |n| + 4` bits long. -/
theorem selectorInput5_length_le (n alpha max_k h i : ℕ)
    (ha : (Nat.bits alpha).length ≤ (Nat.bits n).length)
    (hmk : (Nat.bits max_k).length ≤ (Nat.bits n).length)
    (hh : (Nat.bits h).length ≤ (Nat.bits n).length) :
    (selectorInput5 n alpha max_k h i).length
      ≤ (Nat.bits i).length + 8 * (Nat.bits n).length + 4 := by
  unfold selectorInput5 pack5 natBits
  simp only [length_pairCode]
  omega

-- `exercise364_nonstochastic_fraction_weak` (ch14-exercise-364) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

open Classical in
/-- The total a priori probability of the non-`(alpha, beta)`-stochastic strings
of length `n`, computed with the a priori probability `2^{-K(x)}`. -/
noncomputable def nonStochasticMass (U : Map) (n alpha beta : ℕ) : ℝ≥0∞ :=
  ∑' x : BitString,
    if x.length = n ∧ IsNonStochastic U x alpha beta then complexityWeight (KPPlain U x) else 0

/-- **Theorem 251.** Under `2 alpha + beta < n - O(log n)` and
`alpha < beta - O(log n)`, the total a priori probability of the
non-`(alpha, beta)`-stochastic strings of length `n` is `2^{-alpha + O(log n)}`. -/
theorem nonStochasticMass_bounds (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n alpha beta : ℕ),
      2 * alpha + beta + logSlack c n < n →
      alpha + logSlack c n < beta →
      (2 : ℝ≥0∞)⁻¹ ^ (alpha + logSlack c n) ≤ nonStochasticMass U n alpha beta ∧
        nonStochasticMass U n alpha beta ≤ (2 : ℝ≥0∞) ^ (logSlack c n) * (2 : ℝ≥0∞)⁻¹ ^ alpha := by
  classical
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨c_code, hc_code⟩ : ∃ c : Code, IsCodeFor c V := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨C_imp, hC_imp⟩ := prop_nonstochastic_counting_improved V U hV hU c_code hc_code
  obtain ⟨c_1, hc1⟩ := KPPlain_uncovered_string U hU
  obtain ⟨c_2, hc2⟩ := stochastic_mem_levelSet_of_KPPlain_bound U hU
  set c_low := c_1 + c_2 + 4
  refine ⟨c_low + C_imp, fun n alpha beta hgap1 hgap2 => ?_⟩
  set c := c_low + C_imp
  have hc_low : c_low ≤ c := by dsimp [c]; omega
  have hc_imp : C_imp ≤ c := by dsimp [c]; omega
  have hS_imp : logSlack C_imp n ≤ logSlack c n := logSlack_mono_left hc_imp n
  have hS_low : logSlack c_low n ≤ logSlack c n := logSlack_mono_left hc_low n
  constructor
  · -- Lower bound
    have hgap_bridge : 2 * alpha + beta + c_low * (Nat.bits n).length < n := by
      have h1 : c_low * (Nat.bits n).length ≤ logSlack c n := by
        dsimp [c, c_low]; unfold logSlack
        ring_nf; omega
      omega
    set max_k := alpha + beta + c_1 * (Nat.bits n).length + c_2
    have h_size : 2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k < 2 ^ n :=
      nonstochastic_arithmetic_bridge n alpha beta c_1 c_2 c_low (by dsimp [c_low]; omega)
        hgap_bridge
    obtain ⟨x, hx_len, hx_not_mem, hx_KPPlain⟩ := hc1 n alpha max_k h_size
    have hnstoch : IsNonStochastic U x alpha beta := by
      intro hstoch
      set kxBound := alpha + c_1 * (Nat.bits n).length
      have hx_KPPlain_bound : KPPlain U x ≤ (kxBound : ENat) := hx_KPPlain
      have h_threshold : kxBound + beta + c_2 ≤ max_k := by
        dsimp [kxBound, max_k]; omega
      obtain ⟨P, hprob, hcomp, k, hk_max, hk_mem⟩ :=
        hc2 x alpha beta kxBound max_k hstoch hx_KPPlain_bound h_threshold
      exact hx_not_mem P hprob hcomp k hk_max hk_mem
    have h_mem_sum : (if x.length = n ∧ IsNonStochastic U x alpha beta
        then complexityWeight (KPPlain U x) else 0) ≤ nonStochasticMass U n alpha beta :=
      ENNReal.le_tsum (f := fun x => if x.length = n ∧ IsNonStochastic U x alpha beta
        then complexityWeight (KPPlain U x) else 0) x
    rw [ite_eq_left ⟨hx_len, hnstoch⟩] at h_mem_sum
    have h_KPPlain_le_ENat : KPPlain U x ≤ ((alpha + logSlack c n : ℕ) : ENat) := by
      refine hx_KPPlain.trans ?_
      norm_cast
      dsimp [c, c_low]; unfold logSlack
      ring_nf; omega
    have h_weight_le : (2 : ℝ≥0∞)⁻¹ ^ (alpha + logSlack c n) ≤ complexityWeight (KPPlain U x) := by
      have h_cw := complexityWeight_le_of_le h_KPPlain_le_ENat
      rw [complexityWeight_coe] at h_cw
      exact h_cw
    exact h_weight_le.trans h_mem_sum
  · -- Upper bound
    have h_beta_gt : logSlack C_imp n < beta := by
      have h1 : logSlack C_imp n ≤ logSlack c n := hS_imp
      omega
    have h_stoch_imp : ∀ x, IsStochastic U x alpha (logSlack C_imp n) →
        IsStochastic U x alpha beta := fun x h => h.mono_beta (by omega)
    have h_mass_le : nonStochasticMass U n alpha beta ≤
        nonStochasticAprioriMass U n alpha (logSlack C_imp n) := by
      unfold nonStochasticMass nonStochasticAprioriMass
      refine ENNReal.tsum_le_tsum (fun x => ?_)
      by_cases hcond : x.length = n ∧ IsNonStochastic U x alpha beta
      · rw [ite_eq_left hcond]
        have hcond2 : x.length = n ∧ ¬ IsStochastic U x alpha (logSlack C_imp n) := by
          refine ⟨hcond.1, fun hst => hcond.2 (h_stoch_imp x hst)⟩
        rw [ite_eq_left hcond2]
        exact complexityWeight_KP_le_aprioriMeasure U x []
      · rw [ite_eq_right hcond]
        exact zero_le
    have h_apriori_bound := hC_imp n alpha
    have h2_inv_le : (2 : ℝ≥0∞)⁻¹ ^ (logSlack c n) ≤ (2 : ℝ≥0∞)⁻¹ ^ (logSlack C_imp n) :=
      pow_le_pow_right_of_le_one' (by norm_num) hS_imp
    have h_prod_le : (2 : ℝ≥0∞)⁻¹ ^ (logSlack c n) * nonStochasticMass U n alpha beta ≤
        (2 : ℝ≥0∞)⁻¹ ^ alpha := by
      calc (2 : ℝ≥0∞)⁻¹ ^ (logSlack c n) * nonStochasticMass U n alpha beta
          ≤ (2 : ℝ≥0∞)⁻¹ ^ (logSlack C_imp n) *
            nonStochasticAprioriMass U n alpha (logSlack C_imp n) :=
            mul_le_mul' h2_inv_le h_mass_le
        _ ≤ (2 : ℝ≥0∞)⁻¹ ^ alpha := h_apriori_bound
    have h2_cancel : (2 : ℝ≥0∞) ^ (logSlack c n) * (2 : ℝ≥0∞)⁻¹ ^ (logSlack c n) = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    calc nonStochasticMass U n alpha beta
        = 1 * nonStochasticMass U n alpha beta := (one_mul _).symm
      _ = ((2 : ℝ≥0∞) ^ (logSlack c n) * (2 : ℝ≥0∞)⁻¹ ^ (logSlack c n)) *
            nonStochasticMass U n alpha beta := by rw [h2_cancel]
      _ = (2 : ℝ≥0∞) ^ (logSlack c n) *
            ((2 : ℝ≥0∞)⁻¹ ^ (logSlack c n) * nonStochasticMass U n alpha beta) := by ring
      _ ≤ (2 : ℝ≥0∞) ^ (logSlack c n) * (2 : ℝ≥0∞)⁻¹ ^ alpha := by gcongr

end Kolmogorov
