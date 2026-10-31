/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.Cantor
import KolmogorovMathlib.Oracle.PrefixComplexity
import KolmogorovMathlib.PointToSet.ComputableMetric
import KolmogorovMathlib.PointToSet.Conformal.Classical
import Mathlib.Topology.Instances.CantorSet
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorrMass
import KolmogorovMathlib.AlgorithmicRandomness.BlockMap

/-!
# The middle-thirds Cantor set as a computable presentation

This module sets up the running example of the point-to-set principles: the usual ternary
Cantor set `cantorSet ⊆ ℝ`, whose points are `∑ dᵢ / 3ⁱ⁺¹` with digits `dᵢ ∈ {0, 2}`.

* `exists_complex_digit_sequence` (blueprint node `example:digits`): there is an absolute
  constant `c` such that, for every oracle `A`, some binary sequence `ξ` has relative prefix
  complexity `K^A(ξ↾n) ≥ n - c` for all `n`.  It is obtained from Kraft's inequality and the
  fair-coin measure of cylinders, without any randomness detour.
* `middleThirdsPresentation`: the canonical dense presentation of `cantorSet`.  It enumerates
  all finite binary words, reads their digits as ternary digits `0, 2`, and continues with zeros.
  The same presentation is used for every oracle.
* `middleThirds_dimensions_computable`: the ideal-distance table of this presentation is
  computable without an oracle.
* `middleThirds_dimensions` (blueprint node `example:cantor`): both classical dimensions of the
  Cantor set equal `log 2 / log 3`.  The upper bound is the `2ᵐ`-interval cover; the lower bound
  applies the static point-to-set principle to the complex digit sequences above, comparing
  precision complexity at the scales `3⁻ᵐ` with prefix complexity up to `O (log (m + 1))`.

The pointwise and upper-bound refinements of this example live in
`KolmogorovMathlib.PointToSet.Examples.MiddleThirdsPointwise` and
`KolmogorovMathlib.PointToSet.Examples.MiddleThirdsUpper`.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal
open Kolmogorov

/-- The relative prefix-complexity weights `2⁻ᴷᴬ⁽ˣ⁾` over all finite binary strings sum to at
most one (Kraft's inequality). -/
private lemma tsum_inv_two_pow_oracleComplexity_le_one (A : Set ℕ) :
    (∑' x : BitString, (2 : ℝ≥0∞)⁻¹ ^ oracleComplexity A x) ≤ 1 := by
  let U := optimalOraclePrefix A
  have hU_prefix : IsPrefixMachine U := (exists_optimalOraclePrefix_spec A).2.1
  have h_str : (∑' x : BitString, complexityWeight (KP U x [])) ≤ 1 :=
    (ENNReal.tsum_le_tsum fun x ↦ complexityWeight_KP_le_aprioriMeasure U x []).trans
      (tsum_aprioriMeasure_le_one U [] hU_prefix)
  have h_eq : ∀ x, (2 : ℝ≥0∞)⁻¹ ^ oracleComplexity A x = complexityWeight (KP U x []) := by
    intro x
    have h3 : (↑((KP U x []).toNat) : ENat) = KP U x [] :=
      ENat.natCast_toNat (exists_optimalOraclePrefix_finite A x [])
    rw [oracleComplexity, oraclePrefixComplexityNat, oraclePrefixComplexity,
      ← complexityWeight_coe, h3]
  simp_rw [h_eq]
  exact h_str

/-- The sequences having some prefix of relative complexity deficiency more than `c` form a set
of uniform measure at most `2⁻ᶜ`. -/
private lemma uniformMeasure_prefix_deficiency_le (A : Set ℕ) (c : ℕ) :
    uniformMeasure {ξ : CantorSeq | ∃ n : ℕ, oracleComplexity A (cantorPrefix ξ n) + c < n}
      ≤ (2 : ℝ≥0∞)⁻¹ ^ c := by
  let S := {x : BitString | oracleComplexity A x + c < x.length}
  have h_set_eq : {ξ : CantorSeq | ∃ n : ℕ, oracleComplexity A (cantorPrefix ξ n) + c < n} =
      ⋃ x ∈ S, cantorCylinder x := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, S]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨cantorPrefix ξ n, ?_, mem_cantorCylinder_cantorPrefix ξ n⟩
      rwa [cantorPrefix_length]
    · rintro ⟨x, hx, hξ⟩
      refine ⟨x.length, ?_⟩
      rwa [(isCantorPrefix_iff_cantorPrefix_eq x ξ).mp hξ]
  rw [h_set_eq]
  refine (uniformMeasure_iUnion_cantorCylinder_le S).trans ?_
  calc
    ∑' x : ↑(minimalPrefixElements S), (2 : ℝ≥0∞)⁻¹ ^ (x : BitString).length
        ≤ ∑' x : ↑(minimalPrefixElements S),
          (2 : ℝ≥0∞)⁻¹ ^ oracleComplexity A x * (2 : ℝ≥0∞)⁻¹ ^ c := by
      refine ENNReal.tsum_le_tsum fun x ↦ ?_
      rw [← pow_add]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (minimalPrefixElements_subset S x.property).le
    _ = (∑' x : ↑(minimalPrefixElements S), (2 : ℝ≥0∞)⁻¹ ^ oracleComplexity A x) *
          (2 : ℝ≥0∞)⁻¹ ^ c :=
      ENNReal.tsum_mul_right
    _ ≤ 1 * (2 : ℝ≥0∞)⁻¹ ^ c := by
      gcongr
      exact (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
        fun x : BitString ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleComplexity A x).trans
          (tsum_inv_two_pow_oracleComplexity_le_one A)
    _ = (2 : ℝ≥0∞)⁻¹ ^ c := one_mul _

/-- A set of uniform measure less than one omits some Cantor sequence. -/
private lemma exists_notMem_of_uniformMeasure_lt_one
    (S : Set CantorSeq) (hS : uniformMeasure S < 1) :
    ∃ ξ : CantorSeq, ξ ∉ S := by
  by_contra h_all
  push Not at h_all
  rw [Set.eq_univ_of_forall h_all, MeasureTheory.measure_univ] at hS
  exact lt_irrefl _ hS

/-- An absolute constant works for every oracle, with a binary sequence whose every prefix
has relative prefix complexity at least its length minus that constant.
Blueprint node `example:digits`. -/
theorem exists_complex_digit_sequence :
    ∃ c : ℕ, ∀ A : Set ℕ, ∃ ξ : CantorSeq,
      ∀ n : ℕ, n ≤ oracleComplexity A (cantorPrefix ξ n) + c := by
  refine ⟨2, fun A ↦ ?_⟩
  have h_lt : uniformMeasure
      {ξ : CantorSeq | ∃ n : ℕ, oracleComplexity A (cantorPrefix ξ n) + 2 < n} < 1 := by
    refine (uniformMeasure_prefix_deficiency_le A 2).trans_lt ?_
    rw [← ENNReal.inv_pow]
    exact ENNReal.inv_lt_one.mpr (by norm_num)
  obtain ⟨ξ, hξ⟩ := exists_notMem_of_uniformMeasure_lt_one _ h_lt
  refine ⟨ξ, fun n ↦ ?_⟩
  by_contra hn
  exact hξ ⟨n, by omega⟩

/-- The binary sequence of the `i`-th ideal point of the middle-thirds presentation: the word
decoded from `i` (the empty word for invalid codes), followed by zeros. -/
private def idealDigits (i : ℕ) : CantorSeq :=
  prependCantor ((Encodable.decode (α := BitString) i).getD []) fun _ ↦ false

/-- The real number whose ternary digits are `2` where the binary sequence is `true` and `0`
where it is `false`. -/
private noncomputable def ternaryValue (ξ : CantorSeq) : ℝ :=
  Real.ofDigits fun i ↦ cond (ξ i) (2 : Fin 3) 0

/-- A point of the Cantor set is the ternary value of its binary digit sequence. -/
private lemma coe_eq_ternaryValue (x : cantorSet) :
    (x : ℝ) = ternaryValue (cantorSetHomeomorphNatToBool x) :=
  (congrArg Subtype.val (cantorSetHomeomorphNatToBool.symm_apply_apply x)).symm

/-- The canonical Cantor presentation enumerates finite binary words using the existing
decoder, maps their digits to ternary zero and two, and continues with zeros forever.
Invalid codes give the empty word. This one sequence is fixed for every oracle.
Blueprint node `example:cantor`. -/
noncomputable def middleThirdsPresentation : Presentation cantorSet where
  ι i := cantorSetHomeomorphNatToBool.symm (idealDigits i)
  dense := by
    intro x
    let ξ := cantorSetHomeomorphNatToBool x
    have hlim : Tendsto (fun n => prependCantor (cantorPrefix ξ n) (fun _ => false))
        atTop (𝓝 ξ) := by
      apply tendsto_pi_nhds.mpr
      intro j
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop j] with n hn
      simp [prependCantor, hn]
    have hmap := cantorSetHomeomorphNatToBool.symm.continuous.tendsto ξ |>.comp hlim
    rw [cantorSetHomeomorphNatToBool.symm_apply_apply] at hmap
    apply mem_closure_of_tendsto hmap
    exact Eventually.of_forall fun n =>
      ⟨Encodable.encode (cantorPrefix ξ n), by simp [idealDigits]⟩
  complete := isClosed_cantorSet.completeSpace_coe

/-- The ideal points of the presentation are the ternary values of their digit sequences. -/
private lemma coe_ι_eq_ternaryValue (i : ℕ) :
    (middleThirdsPresentation.ι i : ℝ) = ternaryValue (idealDigits i) :=
  rfl

/-- The `k`-th digit of the `i`-th ideal point is computable in `(i, k)`. -/
private lemma computable_idealDigits :
    Computable fun ik : ℕ × ℕ ↦ idealDigits ik.1 ik.2 := by
  have h1 : Computable (fun i : ℕ ↦ (Encodable.decode (α := BitString) i).getD []) :=
    primrecDecodeGetD.to_comp
  have h2 : Computable₂ (fun (l : List Bool) (n : ℕ) ↦ l.getD n false) :=
    (Primrec.list_getD false).to_comp
  refine (h2.comp (h1.comp Computable.fst) Computable.snd).of_eq fun ik ↦ ?_
  simp only [idealDigits, prependCantor]
  split_ifs with h
  · exact List.getD_eq_getElem _ _ h
  · exact List.getD_eq_default _ _ (not_lt.mp h)

/-- The rational truncation, after `p` ternary digits, of the `i`-th ideal point. -/
private def digitTruncation (i p : ℕ) : ℚ :=
  ∑ k ∈ Finset.range p, (cond (idealDigits i k) 2 0 : ℚ) / 3 ^ (k + 1)

/-- The rational ternary truncations of the ideal points are uniformly computable. -/
private lemma computable_digitTruncation :
    Computable fun ip : ℕ × ℕ ↦ digitTruncation ip.1 ip.2 := by
  let term : ℕ × ℕ → ℚ := fun ik ↦ cond (idealDigits ik.1 ik.2) 2 0 / 3 ^ (ik.2 + 1)
  have hterm_num : Computable (fun ik : ℕ × ℕ ↦ (cond (idealDigits ik.1 ik.2) (2 : ℤ) 0)) :=
    Computable.cond computable_idealDigits (Computable.const 2) (Computable.const 0)
  have hterm_den : Computable (fun ik : ℕ × ℕ ↦ (3 ^ (ik.2 + 1) : ℕ)) :=
    ((Kolmogorov.primrec_const_pow 3).to_comp.comp Computable.succ).comp Computable.snd
  have hterm : Computable term := by
    refine Kolmogorov.computable_of_num_den hterm_num hterm_den (fun ik ↦ by positivity) ?_
    intro ik
    simp [term]
  let q : ℕ × ℕ → ℚ := fun ip ↦
    Nat.rec (motive := fun _ ↦ ℚ) 0 (fun k qk ↦ qk + term (ip.1, k)) ip.2
  have h_step : Computable₂ (fun (ip : ℕ × ℕ) (a : ℕ × ℚ) ↦ a.2 + term (ip.1, a.1)) :=
    (Computable₂.comp Kolmogorov.ComputableReals.computable_ratAdd
      (Computable.snd.comp Computable.snd)
      (hterm.comp (Computable.fst.comp Computable.fst |>.pair
        (Computable.fst.comp Computable.snd)))).to₂
  have hq : Computable q :=
    (Computable.nat_rec Computable.snd (Computable.const (0 : ℚ)) h_step).of_eq fun _ ↦ rfl
  refine hq.of_eq fun ⟨i, p⟩ ↦ ?_
  induction p with
  | zero => exact (Finset.sum_range_zero _).symm
  | succ p ih =>
    rw [digitTruncation, Finset.sum_range_succ, ← digitTruncation, ← ih]

/-- The `p`-digit truncation of an ideal point is within `3⁻ᵖ` of it. -/
private lemma abs_sub_digitTruncation_le (i p : ℕ) :
    |(middleThirdsPresentation.ι i : ℝ) - (digitTruncation i p : ℝ)| ≤ (3 : ℝ)⁻¹ ^ p := by
  let a : ℕ → Fin 3 := fun k ↦ cond (idealDigits i k) 2 0
  have hx : (middleThirdsPresentation.ι i : ℝ) = Real.ofDigits a := rfl
  have hq : (digitTruncation i p : ℝ) = ∑ k ∈ Finset.range p, Real.ofDigitsTerm a k := by
    rw [digitTruncation]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    dsimp [Real.ofDigitsTerm, a]
    have h1 : ((cond (idealDigits i k) 2 0 : ℚ) : ℝ) =
        ((cond (idealDigits i k) (2 : Fin 3) 0 : ℕ) : ℝ) := by
      cases idealDigits i k <;> rfl
    have h4 : ((3 : ℚ) ^ (k + 1) : ℝ) = (3 : ℝ) ^ (k + 1) := by push_cast; rfl
    have h7 : ((3 : ℝ) ^ (k + 1))⁻¹ = ((3 : ℝ) ^ k * 3)⁻¹ := by rw [pow_add, pow_one]
    have h8 : ((3 : ℝ) ^ k * 3)⁻¹ = ((3 : ℝ) ^ k)⁻¹ * 3⁻¹ := by rw [mul_inv]
    have h9 : ((3 : ℝ) ^ k)⁻¹ = 3⁻¹ ^ k := by rw [inv_pow]
    change ((cond (idealDigits i k) 2 0 : ℚ) : ℝ) / ((3 : ℚ) ^ (k + 1) : ℝ) = _
    rw [h1, h4, div_eq_mul_inv, h7, h8, h9]
    cases idealDigits i k <;> norm_num
  rw [hx, hq, Real.ofDigits_eq_sum_add_ofDigits a p, add_sub_cancel_left, abs_mul]
  have h3 : |(((3 : ℕ) : ℝ) ^ p)⁻¹| = (3 : ℝ)⁻¹ ^ p := by
    rw [abs_of_pos (by positivity), inv_pow]
    rfl
  rw [h3, abs_of_nonneg (Real.ofDigits_nonneg _)]
  exact mul_le_of_le_one_right (by positivity) (Real.ofDigits_le_one _)

/-- Absolute value on the rationals is computable. -/
private lemma computable_rat_abs : Computable (fun q : ℚ ↦ |q|) := by
  have hle : Computable₂ (fun (a b : ℚ) ↦ decide (a ≤ b)) :=
    ComputableReals.primrec_ratLe.decide.to_comp
  refine (Computable.cond (hle.comp (Computable.const 0) Computable.id) Computable.id
    ComputableReals.computable_ratNeg).of_eq fun x ↦ ?_
  dsimp
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h]
    simp [h]
  · rw [abs_of_neg (lt_of_not_ge h)]
    simp [h]

/-- For a computable rational table `q`, the distance `|q (i, p + 2) - q (j, p + 2)|` is
computable in `((i, j), p)`. -/
private lemma computable_abs_sub_add_two (q : ℕ × ℕ → ℚ) (hq : Computable q) :
    Computable (fun ijp : (ℕ × ℕ) × ℕ ↦ |q (ijp.1.1, ijp.2 + 2) - q (ijp.1.2, ijp.2 + 2)|) := by
  have h_add : Computable (fun ijp : (ℕ × ℕ) × ℕ ↦ ijp.2 + 2) :=
    Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 2)
  have h_q1 : Computable (fun ijp : (ℕ × ℕ) × ℕ ↦ q (ijp.1.1, ijp.2 + 2)) :=
    hq.comp (Computable.pair (Computable.fst.comp Computable.fst) h_add)
  have h_q2 : Computable (fun ijp : (ℕ × ℕ) × ℕ ↦ q (ijp.1.2, ijp.2 + 2)) :=
    hq.comp (Computable.pair (Computable.snd.comp Computable.fst) h_add)
  have h_sub : Computable (fun ijp : (ℕ × ℕ) × ℕ ↦
      q (ijp.1.1, ijp.2 + 2) - q (ijp.1.2, ijp.2 + 2)) :=
    ComputableReals.computable_ratSub.comp h_q1 h_q2
  exact computable_rat_abs.comp h_sub

/-- If two points of the Cantor set are approximated by rationals within `3⁻⁽ᵖ⁺²⁾`, the
distance of the rationals approximates the distance of the points within `2⁻ᵖ`. -/
private lemma abs_abs_sub_sub_dist_lt (x y : cantorSet) (q_x q_y : ℚ) (p : ℕ)
    (hx : |(x : ℝ) - (q_x : ℝ)| ≤ (3 : ℝ)⁻¹ ^ (p + 2))
    (hy : |(y : ℝ) - (q_y : ℝ)| ≤ (3 : ℝ)⁻¹ ^ (p + 2)) :
    |((|q_x - q_y| : ℚ) : ℝ) - dist x y| < (2 : ℝ)⁻¹ ^ p := by
  rw [show dist x y = |(x : ℝ) - (y : ℝ)| from rfl]
  push_cast
  have h1 : |abs ((q_x : ℝ) - (q_y : ℝ)) - abs ((x : ℝ) - (y : ℝ))| ≤
      abs ((x : ℝ) - (q_x : ℝ)) + abs ((y : ℝ) - (q_y : ℝ)) :=
    calc
      _ ≤ abs (((q_x : ℝ) - (q_y : ℝ)) - ((x : ℝ) - (y : ℝ))) :=
        abs_abs_sub_abs_le_abs_sub _ _
      _ = abs (((q_x : ℝ) - (x : ℝ)) + ((y : ℝ) - (q_y : ℝ))) := by
        congr 1
        ring
      _ ≤ abs ((q_x : ℝ) - (x : ℝ)) + abs ((y : ℝ) - (q_y : ℝ)) := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (q_x : ℝ)]
  have h2 : 2 * (3 : ℝ)⁻¹ ^ (p + 2) < (2 : ℝ)⁻¹ ^ p :=
    calc
      2 * (3 : ℝ)⁻¹ ^ (p + 2) = (2 / 9) * (3 : ℝ)⁻¹ ^ p := by ring
      _ < (3 : ℝ)⁻¹ ^ p := by
        have : 0 < (3 : ℝ)⁻¹ ^ p := by positivity
        linarith
      _ ≤ (2 : ℝ)⁻¹ ^ p := by
        gcongr
        norm_num
  linarith [h1.trans (add_le_add hx hy)]

/-- The fixed canonical presentation has a computable ideal-distance table without an oracle.
Blueprint node `example:cantor`. -/
theorem middleThirds_dimensions_computable :
    ComputablePresentationIn middleThirdsPresentation ∅ := by
  refine ⟨fun ijp ↦
    |digitTruncation ijp.1.1 (ijp.2 + 2) - digitTruncation ijp.1.2 (ijp.2 + 2)|, ?_, ?_⟩
  · exact (computable_abs_sub_add_two _ computable_digitTruncation).computableIn
  · intro ij p
    exact abs_abs_sub_sub_dist_lt (middleThirdsPresentation.ι ij.1)
      (middleThirdsPresentation.ι ij.2) (digitTruncation ij.1 (p + 2))
      (digitTruncation ij.2 (p + 2)) p (abs_sub_digitTruncation_le ij.1 (p + 2))
      (abs_sub_digitTruncation_le ij.2 (p + 2))

/-- The binary words of length `m` index a cover of the Cantor set by sets of diameter at most
`3⁻ᵐ`: the ternary cylinders. -/
private lemma exists_cantorSet_cover_ediam_le (m : ℕ) :
    ∃ t : (Fin m → Bool) → Set ℝ,
      cantorSet ⊆ ⋃ w, t w ∧
      ∀ w, Metric.ediam (t w) ≤ (3⁻¹ : ℝ≥0∞) ^ m := by
  let t : (Fin m → Bool) → Set ℝ := fun w =>
    {x | ∃ ξ : ℕ → Bool, (∀ i : Fin m, ξ i = w i) ∧ ternaryValue ξ = x}
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    refine Set.mem_iUnion.mpr
      ⟨fun i ↦ cantorSetHomeomorphNatToBool ⟨x, hx⟩ i, cantorSetHomeomorphNatToBool ⟨x, hx⟩,
        fun _ ↦ rfl, (coe_eq_ternaryValue ⟨x, hx⟩).symm⟩
  · intro w
    have h : Metric.ediam (t w) ≤ ENNReal.ofReal ((3 : ℝ)⁻¹ ^ m) := by
      apply Metric.ediam_le_of_forall_dist_le
      rintro x ⟨ξ, hξ, rfl⟩ y ⟨η, hη, rfl⟩
      rw [Real.dist_eq]
      have hpre : ∀ i < m,
          (cond (ξ i) (2 : Fin 3) 0) = cond (η i) (2 : Fin 3) 0 := by
        intro i hi
        rw [hξ ⟨i, hi⟩, hη ⟨i, hi⟩]
      simpa only [ternaryValue, Nat.cast_ofNat, inv_pow] using
        Real.abs_ofDigits_sub_ofDigits_le hpre
    simpa only [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 3⁻¹),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3), ENNReal.ofReal_ofNat] using h

/-- The Hausdorff dimension of the Cantor set is at most `log 2 / log 3`: the `2ᵐ` ternary
cylinders of diameter `3⁻ᵐ` have Hausdorff cost at most one at this exponent. -/
private lemma dimH_cantorSet_le :
    _root_.dimH cantorSet ≤ ENNReal.ofReal (Real.log 2 / Real.log 3) := by
  classical
  let d : ℝ := Real.log 2 / Real.log 3
  have hd : 0 ≤ d := div_nonneg (Real.log_nonneg (by norm_num))
    (Real.log_nonneg (by norm_num))
  choose t hcover hdiam using exists_cantorSet_cover_ediam_le
  have hr : Tendsto (fun m : ℕ => (3⁻¹ : ℝ≥0∞) ^ m) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hpow : (3⁻¹ : ℝ≥0∞) ^ d = 2⁻¹ := by
    have hreal : (3 : ℝ) ^ d = 2 :=
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
    have hi : (3⁻¹ : ℝ) ^ d = (2 : ℝ)⁻¹ := by
      rw [Real.inv_rpow (by norm_num), hreal]
    have he := congrArg ENNReal.ofReal hi
    simpa only [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 3⁻¹),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat] using he
  have hcost : ∀ m : ℕ, (∑ w, Metric.ediam (t m w) ^ d) ≤ 1 := by
    intro m
    calc
      (∑ w, Metric.ediam (t m w) ^ d) ≤ ∑ _w : Fin m → Bool, ((3⁻¹ : ℝ≥0∞) ^ m) ^ d :=
        Finset.sum_le_sum fun w _ => ENNReal.rpow_le_rpow (hdiam m w) hd
      _ = (2 : ℝ≥0∞) ^ m * ((3⁻¹ : ℝ≥0∞) ^ m) ^ d := by simp
      _ = 1 := by
        rw [← ENNReal.rpow_natCast_mul, mul_comm (m : ℝ), ENNReal.rpow_mul_natCast, hpow,
          ← mul_pow]
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have hmeasure : MeasureTheory.Measure.hausdorffMeasure d cantorSet ≤ 1 := by
    calc
      _ ≤ liminf (fun m => ∑ w, Metric.ediam (t m w) ^ d) atTop :=
        MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum d cantorSet _ hr t
          (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
      _ ≤ 1 := liminf_le_of_frequently_le (Frequently.of_forall hcost)
  have hdim := dimH_le_of_hausdorffMeasure_ne_top
    (d := (⟨d, hd⟩ : NNReal)) (s := cantorSet)
    ((hmeasure.trans_lt ENNReal.one_lt_top).ne)
  change dimH cantorSet ≤ ENNReal.ofReal d
  convert hdim using 1
  exact ENNReal.ofReal_eq_coe_nnreal hd

/-- At the first differing binary digit, the ternary values of two sequences are separated by
at least the next ternary scale. -/
private lemma inv_pow_succ_le_abs_ternaryValue_sub
    (ξ η : CantorSeq) (n : ℕ) (hpre : ∀ i < n, ξ i = η i) (hne : ξ n ≠ η n) :
    (3 : ℝ)⁻¹ ^ (n + 1) ≤ |ternaryValue ξ - ternaryValue η| := by
  have key : ∀ ξ η : CantorSeq, (∀ i < n, ξ i = η i) → ξ n = true → η n = false →
      (3 : ℝ)⁻¹ ^ (n + 1) ≤ ternaryValue ξ - ternaryValue η := by
    intro ξ η hpre hx hy
    let a : ℕ → Fin 3 := fun i => cond (ξ i) 2 0
    let b : ℕ → Fin 3 := fun i => cond (η i) 2 0
    have hs : (∑ i ∈ Finset.range n, Real.ofDigitsTerm a i) =
        ∑ i ∈ Finset.range n, Real.ofDigitsTerm b i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Real.ofDigitsTerm, a, b, hpre i (Finset.mem_range.mp hi)]
    have ha0 := Real.ofDigits_nonneg (fun i => a (i + (n + 1)))
    have ha1 := Real.ofDigits_le_one (fun i => a (i + (n + 1)))
    have hb0 := Real.ofDigits_nonneg (fun i => b (i + (n + 1)))
    have hb1 := Real.ofDigits_le_one (fun i => b (i + (n + 1)))
    have hp : 0 ≤ (3 : ℝ)⁻¹ ^ (n + 1) := by positivity
    change (3 : ℝ)⁻¹ ^ (n + 1) ≤ Real.ofDigits a - Real.ofDigits b
    rw [Real.ofDigits_eq_sum_add_ofDigits a (n + 1),
      Real.ofDigits_eq_sum_add_ofDigits b (n + 1),
      Finset.sum_range_succ, Finset.sum_range_succ, hs]
    simp only [Real.ofDigitsTerm, a, b, hx, hy, Bool.cond_false,
      Bool.cond_true, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
      Nat.cast_ofNat, zero_mul, inv_pow] at *
    nlinarith
  cases hx : ξ n <;> cases hy : η n
  · exact (hne (hx.trans hy.symm)).elim
  · rw [abs_sub_comm]
    exact (key η ξ (fun i hi => (hpre i hi).symm) hy hx).trans (le_abs_self _)
  · exact (key ξ η hpre hx hy).trans (le_abs_self _)
  · exact (hne (hx.trans hy.symm)).elim

/-- Two binary sequences whose ternary values are closer than `3⁻ᵐ` agree on their first
`m` digits. -/
private lemma cantorPrefix_eq_of_abs_ternaryValue_sub_lt
    (ξ η : CantorSeq) (m : ℕ) (h : |ternaryValue ξ - ternaryValue η| < (3 : ℝ)⁻¹ ^ m) :
    cantorPrefix ξ m = cantorPrefix η m := by
  have hagree : ∀ i < m, ξ i = η i := by
    by_contra! hn
    let n := Nat.find hn
    have hn' : n < m ∧ ξ n ≠ η n := Nat.find_spec hn
    have hpre : ∀ i < n, ξ i = η i := by
      intro i hi
      by_contra hne
      exact Nat.find_min hn hi ⟨hi.trans hn'.1, hne⟩
    have hgap := inv_pow_succ_le_abs_ternaryValue_sub ξ η n hpre hn'.2
    have hscale : (3 : ℝ)⁻¹ ^ m ≤ (3 : ℝ)⁻¹ ^ (n + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact (not_lt_of_ge (hscale.trans hgap)) h
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [cantorPrefix_getElem]
    exact hagree i (by simpa using hi)

/-- Extracting a finite prefix of the digit sequence of an ideal point is computable in the
ideal index and the prefix length. -/
private lemma computable_cantorPrefix_idealDigits :
    Computable fun im : ℕ × ℕ ↦ cantorPrefix (idealDigits im.1) im.2 := by
  let f : ℕ × ℕ → BitString := fun im => (List.range im.2).map
    (fun k => ((Encodable.decode (α := BitString) im.1).getD []).getD k false)
  have hd : Primrec (fun im : ℕ × ℕ =>
      (Encodable.decode (α := BitString) im.1).getD []) :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const [])
  have hc : Primrec f :=
    Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      ((Primrec.list_getD false).comp (hd.comp Primrec.fst) Primrec.snd).to₂
  apply hc.to_comp.of_eq
  intro im
  apply List.ext_getElem
  · simp [f]
  · intro i hi hj
    simp only [f, List.getElem_map, List.getElem_range, cantorPrefix_getElem]
    by_cases hl : i < ((Encodable.decode (α := BitString) im.1).getD []).length
    · simp [idealDigits, prependCantor, hl]
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [idealDigits, prependCantor, hl]

/-- Supplying the index and the scale of an ideal point suffices to produce its digit prefix,
so the prefix complexity exceeds the complexity of the index by at most twice the logarithm of
the scale plus a constant, uniformly in the ideal index and scale. -/
private lemma exists_oracleComplexity_cantorPrefix_idealDigits_le (A : Set ℕ) :
    ∃ C : ℕ, ∀ i m : ℕ,
      (oracleComplexity A (cantorPrefix (idealDigits i) m) : ℝ) ≤
        oracleNatComplexity A i + 2 * Real.logb 2 ((m : ℝ) + 1) + C := by
  let g := fun im : ℕ × ℕ => cantorPrefix (idealDigits im.1) im.2
  let F : List BitString →. BitString := fun ws => Part.some
    (g (decodeBits (decodeFirst (ws.headD [])),
      decodeBits (decodeSecond (ws.headD []))))
  have hF : PartrecIn {charOracle A} F := by
    have hd : Computable (fun ws : List BitString => ws.headD []) :=
      (Computable.option_getD Primrec.list_head?.to_comp (Computable.const [])).of_eq
        (fun ws => by cases ws <;> rfl)
    have hi := decodeBits_computable.comp
      (CodedFiniteDistribution.decodeFirst_primrec.to_comp.comp hd)
    have hm := decodeBits_computable.comp
      (CodedFiniteDistribution.decodeSecond_primrec.to_comp.comp hd)
    exact (computable_cantorPrefix_idealDigits.comp (hi.pair hm)).computableIn.partrecIn
  obtain ⟨c₁, hc₁⟩ := oracle_tuple_bounds_composition A 1 F hF
  obtain ⟨c₂, hc₂⟩ := oracle_tuple_bounds_overhead A
  refine ⟨c₁ + c₂, ?_⟩
  intro i m
  have hmem : g (i, m) ∈ F [pairCode (natBits i) (natBits m)] := by
    simp [F, decodeFirst_pairCode, decodeSecond_pairCode, natBits]
  have hc := hc₁ [pairCode (natBits i) (natBits m)] (g (i, m)) rfl hmem
  have hn : oracleComplexity A (g (i, m)) ≤ oraclePairComplexity A i m + c₁ := by
    simpa [oraclePairComplexity] using hc
  have hr : (oracleComplexity A (g (i, m)) : ℝ) ≤
      oraclePairComplexity A i m + c₁ := by exact_mod_cast hn
  have hb := hc₂ i m
  push_cast
  linarith

/-- The complexity of the digit prefix of length `m` of a point of the Cantor set is bounded by
its precision complexity at scale `3⁻ᵐ` plus twice the logarithm of `m + 1` and a constant,
uniformly in the point and `m`. -/
private lemma exists_oracleComplexity_cantorPrefix_le_precisionComplexityNat (A : Set ℕ) :
    ∃ C : ℕ, ∀ (x : cantorSet) (m : ℕ),
      (oracleComplexity A (cantorPrefix (cantorSetHomeomorphNatToBool x) m) : ℝ) ≤
        precisionComplexityNat middleThirdsPresentation A x ((3 : ℝ)⁻¹ ^ m) +
          2 * Real.logb 2 ((m : ℝ) + 1) + C := by
  obtain ⟨C, hC⟩ := exists_oracleComplexity_cantorPrefix_idealDigits_le A
  refine ⟨C, ?_⟩
  intro x m
  obtain ⟨i, hi, heq⟩ := staticPointDimensions_attained middleThirdsPresentation A x
    ((3 : ℝ)⁻¹ ^ m) (by positivity)
  have hclose : |ternaryValue (idealDigits i) -
      ternaryValue (cantorSetHomeomorphNatToBool x)| < (3 : ℝ)⁻¹ ^ m := by
    rw [← coe_eq_ternaryValue x, ← coe_ι_eq_ternaryValue i]
    simpa only [Subtype.dist_eq, Real.dist_eq] using hi
  have hprefix := cantorPrefix_eq_of_abs_ternaryValue_sub_lt _ _ m hclose
  have hnat : precisionComplexityNat middleThirdsPresentation A x ((3 : ℝ)⁻¹ ^ m) =
      oracleNatComplexity A i := by
    simp only [precisionComplexityNat, heq, ENat.toNat_natCast]
  rw [hnat, ← hprefix]
  exact hC i m

/-- If `m` is bounded by `k m` plus twice the logarithm of `m + 1` and a constant, then
`k m` divided by the logarithmic scale `-log₂ 3⁻ᵐ` has lower limit at least `log 2 / log 3`:
the logarithmic overhead is sublinear. -/
private lemma ofReal_log_div_log_le_liminf_of_le_add_log
    (k : ℕ → ℕ) (C : ℝ)
    (hk : ∀ m : ℕ, (m : ℝ) ≤ (k m : ℝ) + 2 * Real.logb 2 ((m : ℝ) + 1) + C) :
    ENNReal.ofReal (Real.log 2 / Real.log 3) ≤
      liminf (fun m => (k m : ℝ≥0∞) /
        ENNReal.ofReal (-Real.logb 2 ((3 : ℝ)⁻¹ ^ m))) atTop := by
  let L : ℝ := Real.logb 2 3
  have hL : 0 < L := by
    dsimp [L, Real.logb]
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  have hlog : Tendsto (fun m : ℕ => Real.logb 2 ((m : ℝ) + 1) / (m : ℝ))
      atTop (𝓝 0) := by
    have H := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using H
  have hc : Tendsto (fun m : ℕ => C / (m : ℝ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop tendsto_natCast_atTop_atTop C
  have hreal : Tendsto (fun m : ℕ =>
      ((m : ℝ) - 2 * Real.logb 2 ((m : ℝ) + 1) - C) / ((m : ℝ) * L))
      atTop (𝓝 (Real.log 2 / Real.log 3)) := by
    have H := (((tendsto_const_nhds (x := (1 : ℝ))).sub (hlog.const_mul 2)).sub hc).div_const L
    have H' : Tendsto (fun m : ℕ =>
        (1 - 2 * (Real.logb 2 ((m : ℝ) + 1) / (m : ℝ)) - C / (m : ℝ)) / L)
        atTop (𝓝 (Real.log 2 / Real.log 3)) := by
      simpa only [mul_zero, sub_zero, L, Real.logb, one_div_div] using H
    apply H'.congr'
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  have he := ENNReal.tendsto_ofReal hreal
  have hnorm : ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (((m : ℝ) - 2 * Real.logb 2 ((m : ℝ) + 1) - C) /
        ((m : ℝ) * L)) ≤
        (k m : ℝ≥0∞) / ENNReal.ofReal (-Real.logb 2 ((3 : ℝ)⁻¹ ^ m)) := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hden : -Real.logb 2 ((3 : ℝ)⁻¹ ^ m) = (m : ℝ) * L := by
      rw [Real.logb_pow, Real.logb_inv]
      dsimp [L]
      ring
    rw [hden, ENNReal.ofReal_div_of_pos (mul_pos hm' hL)]
    apply ENNReal.div_le_div_right
    have hr : (m : ℝ) - 2 * Real.logb 2 ((m : ℝ) + 1) - C ≤ k m := by
      linarith [hk m]
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hr
  calc
    ENNReal.ofReal (Real.log 2 / Real.log 3) =
        liminf (fun m : ℕ => ENNReal.ofReal
          (((m : ℝ) - 2 * Real.logb 2 ((m : ℝ) + 1) - C) / ((m : ℝ) * L))) atTop :=
      he.liminf_eq.symm
    _ ≤ _ := liminf_le_liminf hnorm

/-- The ternary radii `3⁻ᵐ` tend to zero and the ratio of the logarithms of successive radii
tends to one. -/
private lemma tendsto_inv_three_pow_and_log_ratio :
    Tendsto (fun m : ℕ => (3 : ℝ)⁻¹ ^ m) atTop (𝓝 0) ∧
    Tendsto (fun m : ℕ => Real.log ((3 : ℝ)⁻¹ ^ (m + 1)) /
      Real.log ((3 : ℝ)⁻¹ ^ m)) atTop (𝓝 1) := by
  constructor
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · have hL : Real.log ((3 : ℝ)⁻¹) ≠ 0 := by
      rw [Real.log_inv]
      exact neg_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
    have H : Tendsto (fun m : ℕ => (1 : ℝ) + 1 / (m : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add
        (Tendsto.const_div_atTop tendsto_natCast_atTop_atTop (1 : ℝ))
    apply H.congr'
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [Real.log_pow, Nat.cast_add, Nat.cast_one]
    field_simp

/-- For every oracle, some point of the Cantor set has lower static dimension at least
`log 2 / log 3`: the complex digit sequence of `exists_complex_digit_sequence` is such a
point. -/
private lemma exists_point_le_staticPointDimensions_fst (A : Set ℕ) :
    ∃ x : cantorSet, ENNReal.ofReal (Real.log 2 / Real.log 3) ≤
      (staticPointDimensions middleThirdsPresentation A x).1 := by
  obtain ⟨c, hc⟩ := exists_complex_digit_sequence
  obtain ⟨ξ, hξ⟩ := hc A
  let x : cantorSet := cantorSetHomeomorphNatToBool.symm ξ
  refine ⟨x, ?_⟩
  obtain ⟨C, hC⟩ := exists_oracleComplexity_cantorPrefix_le_precisionComplexityNat A
  have hk : ∀ m : ℕ, (m : ℝ) ≤
      (precisionComplexityNat middleThirdsPresentation A x ((3 : ℝ)⁻¹ ^ m) : ℝ) +
        2 * Real.logb 2 ((m : ℝ) + 1) + ((C : ℝ) + c) := by
    intro m
    have hpre := hC x m
    have heq : cantorSetHomeomorphNatToBool x = ξ :=
      cantorSetHomeomorphNatToBool.apply_symm_apply ξ
    rw [heq] at hpre
    have hξ' : (m : ℝ) ≤ oracleComplexity A (cantorPrefix ξ m) + c := by
      exact_mod_cast hξ m
    linarith
  rw [dimension_along_scales middleThirdsPresentation A x (fun m => (3 : ℝ)⁻¹ ^ m)
    (fun _ => by positivity) tendsto_inv_three_pow_and_log_ratio.1
      tendsto_inv_three_pow_and_log_ratio.2]
  exact ofReal_log_div_log_le_liminf_of_le_add_log _ ((C : ℝ) + c) hk

/-- The usual middle-thirds subset of the real line has Hausdorff dimension `log 2 / log 3`.
Blueprint node `example:cantor`. -/
theorem middleThirds_dimensions :
    _root_.dimH cantorSet = ENNReal.ofReal (Real.log 2 / Real.log 3) := by
  apply le_antisymm dimH_cantorSet_le
  have hd := Isometry.dimH_image (f := (Subtype.val : cantorSet → ℝ))
    isometry_subtype_coe Set.univ
  rw [Set.image_univ, Subtype.range_coe] at hd
  obtain ⟨A, hA⟩ := hausdorffAchievingOracle middleThirdsPresentation Set.univ
  obtain ⟨x, hx⟩ := exists_point_le_staticPointDimensions_fst A
  calc
    ENNReal.ofReal (Real.log 2 / Real.log 3) ≤
        ⨆ x ∈ (Set.univ : Set cantorSet),
          (staticPointDimensions middleThirdsPresentation A x).1 :=
      hx.trans (le_iSup₂_of_le x (Set.mem_univ x) le_rfl)
    _ ≤ _root_.dimH (Set.univ : Set cantorSet) := hA
    _ = _root_.dimH cantorSet := hd.symm

end Kolmogorov.PointToSet
