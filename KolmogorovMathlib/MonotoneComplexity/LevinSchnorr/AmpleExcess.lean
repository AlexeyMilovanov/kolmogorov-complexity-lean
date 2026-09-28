/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings

/-!
# The ample excess lemma

SUV Section 5.6, p. 151 states as the second form of Theorem 94(d) that a sequence `ω` is
Martin-Löf random with respect to the uniform measure **iff** the series
`∑ₙ 2^(n − K((ω)ₙ))` converges (SUV Problem 146, p. 150).  The easy half bounds each term of
a convergent series; the hard half — for a random `ω` the whole series converges — is the
*ample excess lemma* of Gács, rediscovered by J. Miller and L. Yu.

This module proves the hard half, in the natural generality in which the argument works: for
*any* lower semicomputable semimeasure `m` on strings and any uniformly random `ω`, the
series `∑ₙ 2ⁿ · m((ω)ₙ)` converges.

## The argument

Write `T_c` for the set of strings `x` with `2^c < ∑_{i ≤ |x|} 2^i · m(x↾i)`
(`prefixExcessPartial`).  Then

* `T_c` is enumerable, uniformly in `c`: the partial sum is a *finite* sum of lower
  semicomputable terms, so its stage-`s` approximations `prefixExcessStage` are computable
  natural numbers and `x ∈ T_c ↔ ∃ s, 2^(c+s) < prefixExcessStage … x s`;
* the set of sequences with a prefix in `T_c` has uniform measure at most `2^(−c)`: it is
  the increasing union over `N` of `{ω : 2^c < ∑_{i ≤ N} 2^i·m((ω)_i)}`, and
  `∫ ∑_{i ≤ N} 2^i·m((ω)_i) dλ = ∑_{i ≤ N} ∑_{|y| = i} m(y) ≤ ∑_y m(y) ≤ 1`,
  so Markov's inequality applies.

Hence `c ↦ prefixHitSet (T_c)` is a Martin-Löf test (`isMartinLofTest_prefixHitSet`), a
random `ω` avoids some level `c`, and all the partial sums of `∑ₙ 2ⁿ·m((ω)ₙ)` are at most
`2^c`.

## Main results

* `tsum_two_pow_mul_ne_top_of_isMartinLofRandom_uniform` — the ample excess lemma for a
  lower semicomputable semimeasure.
* `tsum_two_pow_mul_complexityWeight_KPPlain_ne_top_of_isMartinLofRandom_uniform` — its
  instance for `2^(−K)`, the form used by Theorem 94(d′): the a priori semimeasure of a
  prefix decompressor is lower semicomputable and dominates `2^(−K)`.
-/

namespace Kolmogorov

open MeasureTheory

open scoped ENNReal

/-! ### Partial sums along the prefixes of a string -/

/-- SUV p. 151: the partial sum `∑_{i ≤ |x|} 2^i · m(x↾i)` of the ample-excess series along
the prefixes of `x`. -/
noncomputable def prefixExcessPartial (m : BitString → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (x.length + 1), (2 : ℝ≥0∞) ^ i * m (x.take i)

/-- Along the prefixes of a sequence the partial excess sum is `∑ 2 ^ i * m` over the prefixes of
length at most `n`. -/
lemma prefixExcessPartial_cantorPrefix (m : BitString → ℝ≥0∞) (w : CantorSeq) (n : ℕ) :
    prefixExcessPartial m (cantorPrefix w n)
      = ∑ i ∈ Finset.range (n + 1), (2 : ℝ≥0∞) ^ i * m (cantorPrefix w i) := by
  rw [prefixExcessPartial, cantorPrefix_length]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [_root_.cantorPrefix_take w i n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

/-- The partial excess sum along the prefixes of a sequence is nondecreasing in the prefix length.
-/
lemma prefixExcessPartial_mono_cantorPrefix (m : BitString → ℝ≥0∞) (w : CantorSeq) {n N : ℕ}
    (h : n ≤ N) :
    prefixExcessPartial m (cantorPrefix w n) ≤ prefixExcessPartial m (cantorPrefix w N) := by
  rw [prefixExcessPartial_cantorPrefix, prefixExcessPartial_cantorPrefix]
  refine Finset.sum_le_sum_of_subset ?_
  intro i hi
  simp only [Finset.mem_range] at hi ⊢
  omega

/-! ### The integral bound and Markov's inequality -/

/-- The partial excess sum at level `N` is a measurable function of the sequence. -/
lemma measurable_prefixExcessPartial_cantorPrefix (m : BitString → ℝ≥0∞) (N : ℕ) :
    Measurable fun w : CantorSeq => prefixExcessPartial m (cantorPrefix w N) := by
  have h : (fun w : CantorSeq => prefixExcessPartial m (cantorPrefix w N))
      = fun w => ∑ i ∈ Finset.range (N + 1), (2 : ℝ≥0∞) ^ i * m (cantorPrefix w i) := by
    funext w
    exact prefixExcessPartial_cantorPrefix m w N
  rw [h]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_comp_cantorPrefix i m).const_mul _

/-- Integrating `2 ^ i * m` over the length-`i` prefix against the uniform measure gives the total
mass of `m` on level `i`. -/
lemma lintegral_two_pow_mul_comp_cantorPrefix (m : BitString → ℝ≥0∞) (i : ℕ) :
    ∫⁻ w, (2 : ℝ≥0∞) ^ i * m (cantorPrefix w i) ∂uniformMeasure
      = ∑ y ∈ levelFinset i, m y := by
  rw [lintegral_const_mul _ (measurable_comp_cantorPrefix i m),
    lintegral_comp_cantorPrefix uniformMeasure i m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [mem_levelFinset] at hy
  rw [cantorMass_uniformMeasure, hy, ← mul_assoc, mul_comm ((2 : ℝ≥0∞) ^ i) (m y),
    mul_assoc]
  rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, mul_one]

/-- The level masses of `m` up to level `N` sum to at most the total mass of `m`. -/
lemma sum_sum_levelFinset_le_tsum (m : BitString → ℝ≥0∞) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), ∑ y ∈ levelFinset i, m y ≤ ∑' x : BitString, m x := by
  classical
  have hdisj : ((Finset.range (N + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint levelFinset := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun y hy hy' => ?_
    rw [mem_levelFinset] at hy hy'
    exact hij (hy ▸ hy')
  rw [← Finset.sum_biUnion hdisj]
  exact ENNReal.sum_le_tsum _

/-- For a discrete semimeasure the expected partial excess sum at any level is at most `1`. -/
lemma lintegral_prefixExcessPartial_le {m : BitString → ℝ≥0∞}
    (hm : (∑' x : BitString, m x) ≤ 1) (N : ℕ) :
    ∫⁻ w, prefixExcessPartial m (cantorPrefix w N) ∂uniformMeasure ≤ 1 := by
  have h : (fun w : CantorSeq => prefixExcessPartial m (cantorPrefix w N))
      = fun w => ∑ i ∈ Finset.range (N + 1), (2 : ℝ≥0∞) ^ i * m (cantorPrefix w i) := by
    funext w
    exact prefixExcessPartial_cantorPrefix m w N
  rw [h, lintegral_finset_sum _
    (fun i _ => (measurable_comp_cantorPrefix i m).const_mul _)]
  calc ∑ i ∈ Finset.range (N + 1),
        ∫⁻ w, (2 : ℝ≥0∞) ^ i * m (cantorPrefix w i) ∂uniformMeasure
      = ∑ i ∈ Finset.range (N + 1), ∑ y ∈ levelFinset i, m y :=
        Finset.sum_congr rfl fun i _ => lintegral_two_pow_mul_comp_cantorPrefix m i
    _ ≤ ∑' x : BitString, m x := sum_sum_levelFinset_le_tsum m N
    _ ≤ 1 := hm

/-- By Markov's inequality the sequences whose level-`N` excess sum exceeds `2 ^ c` have uniform
measure at most `2 ^ (-c)`. -/
lemma measure_setOf_lt_prefixExcessPartial_le {m : BitString → ℝ≥0∞}
    (hm : (∑' x : BitString, m x) ≤ 1) (c N : ℕ) :
    uniformMeasure {w : CantorSeq |
        (2 : ℝ≥0∞) ^ c < prefixExcessPartial m (cantorPrefix w N)}
      ≤ (2 : ℝ≥0∞)⁻¹ ^ c := by
  have hmeas := measurable_prefixExcessPartial_cantorPrefix m N
  have hmk := mul_meas_ge_le_lintegral₀ (μ := uniformMeasure) hmeas.aemeasurable
    ((2 : ℝ≥0∞) ^ c)
  have hsub : {w : CantorSeq |
      (2 : ℝ≥0∞) ^ c < prefixExcessPartial m (cantorPrefix w N)}
      ⊆ {w : CantorSeq |
        (2 : ℝ≥0∞) ^ c ≤ prefixExcessPartial m (cantorPrefix w N)} := by
    intro w hw
    rw [Set.mem_setOf_eq] at hw ⊢
    exact le_of_lt hw
  have hkey : (2 : ℝ≥0∞) ^ c * uniformMeasure {w : CantorSeq |
      (2 : ℝ≥0∞) ^ c < prefixExcessPartial m (cantorPrefix w N)} ≤ 1 := by
    refine le_trans (le_trans (mul_le_mul_right (measure_mono hsub) _) hmk) ?_
    exact lintegral_prefixExcessPartial_le hm N
  have hinv : ((2 : ℝ≥0∞)⁻¹) ^ c * (2 : ℝ≥0∞) ^ c = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  calc uniformMeasure {w : CantorSeq |
        (2 : ℝ≥0∞) ^ c < prefixExcessPartial m (cantorPrefix w N)}
      = ((2 : ℝ≥0∞)⁻¹ ^ c * (2 : ℝ≥0∞) ^ c) * uniformMeasure {w : CantorSeq |
          (2 : ℝ≥0∞) ^ c < prefixExcessPartial m (cantorPrefix w N)} := by
        rw [hinv, one_mul]
    _ = (2 : ℝ≥0∞)⁻¹ ^ c * ((2 : ℝ≥0∞) ^ c * uniformMeasure {w : CantorSeq |
          (2 : ℝ≥0∞) ^ c < prefixExcessPartial m (cantorPrefix w N)}) := by
        rw [mul_assoc]
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c * 1 := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ c := mul_one _

/-! ### The enumerable deficiency sets -/

/-- SUV p. 151: the set of strings whose ample-excess partial sum exceeds `2^c`. -/
def prefixExcessSet (m : BitString → ℝ≥0∞) (c : ℕ) : Set BitString :=
  {x | (2 : ℝ≥0∞) ^ c < prefixExcessPartial m x}

/-- The stage-`s` approximation of `2^s · prefixExcessPartial`, a natural number. -/
def prefixExcessStage (A : ℕ → BitString → ℕ) (x : BitString) (s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (x.length + 1), 2 ^ i * A s (x.take i)

/-- The accumulator recursion that adds `f y` at each step computes the partial sum over
`Finset.range n`. -/
lemma natRec_sum_range (f : ℕ → ℕ) (n : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun y IH => IH + f y) n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ← ih]

/-- For a computable stage-wise approximation of `m` the staged excess sum is computable. -/
lemma computable_prefixExcessStage {A : ℕ → BitString → ℕ} (hA : Computable₂ A) :
    Computable₂ (prefixExcessStage A) := by
  have hlen : Computable (fun p : BitString × ℕ => p.1.length + 1) :=
    Primrec.succ.to_comp.comp (Computable.list_length.comp Computable.fst)
  have hstr : Computable (fun r : (BitString × ℕ) × (ℕ × ℕ) => r.1.1.take r.2.1) :=
    (Primrec.list_take.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).to_comp
  have hA' : Computable (fun r : (BitString × ℕ) × (ℕ × ℕ) => A r.1.2 (r.1.1.take r.2.1)) :=
    hA.comp (Computable.snd.comp Computable.fst) hstr
  have hpow : Computable (fun r : (BitString × ℕ) × (ℕ × ℕ) => 2 ^ r.2.1) :=
    primrec_two_pow_aux.to_comp.comp (Computable.fst.comp Computable.snd)
  have hmul : Computable₂ (fun a b : ℕ => a * b) := Primrec.nat_mul.to_comp
  have hadd : Computable₂ (fun a b : ℕ => a + b) := Primrec.nat_add.to_comp
  have hh : Computable₂ (fun (p : BitString × ℕ) (q : ℕ × ℕ) =>
      q.2 + 2 ^ q.1 * A p.2 (p.1.take q.1)) :=
    (hadd.comp (Computable.snd.comp Computable.snd) (hmul.comp hpow hA')).to₂
  refine (Computable.nat_rec (σ := ℕ) hlen (Computable.const 0) hh).of_eq ?_
  rintro ⟨x, s⟩
  exact natRec_sum_range (fun i => 2 ^ i * A s (x.take i)) (x.length + 1)

/-- The staged excess sum has dyadic value `∑ 2 ^ i * A s (x.take i)`, the stage-`s` approximation
of
the excess sum along the prefixes of `x`. -/
lemma dyadicValue_prefixExcessStage (A : ℕ → BitString → ℕ) (x : BitString) (s : ℕ) :
    dyadicValue (prefixExcessStage A x s) s
      = ∑ i ∈ Finset.range (x.length + 1),
          (2 : ℝ≥0∞) ^ i * dyadicValue (A s (x.take i)) s := by
  rw [prefixExcessStage, dyadicValue]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dyadicValue, div_eq_mul_inv, mul_assoc]

/-- The staged excess sums converge upward to the true partial excess sum. -/
lemma iSup_dyadicValue_prefixExcessStage {m : BitString → ℝ≥0∞} {A : ℕ → BitString → ℕ}
    (hmono : ∀ s y, dyadicValue (A s y) s ≤ dyadicValue (A (s + 1) y) (s + 1))
    (hsup : ∀ y, ⨆ s, dyadicValue (A s y) s = m y) (x : BitString) :
    ⨆ s, dyadicValue (prefixExcessStage A x s) s = prefixExcessPartial m x := by
  have hmono' : ∀ i : ℕ, Monotone fun s : ℕ =>
      (2 : ℝ≥0∞) ^ i * dyadicValue (A s (x.take i)) s := by
    intro i
    refine monotone_nat_of_le_succ fun s => ?_
    gcongr
    exact hmono s (x.take i)
  have hstep : (⨆ s, dyadicValue (prefixExcessStage A x s) s)
      = ⨆ s, ∑ i ∈ Finset.range (x.length + 1),
          (2 : ℝ≥0∞) ^ i * dyadicValue (A s (x.take i)) s :=
    iSup_congr fun s => dyadicValue_prefixExcessStage A x s
  rw [hstep, ← ENNReal.finsetSum_iSup_of_monotone hmono', prefixExcessPartial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ENNReal.mul_iSup, hsup (x.take i)]

/-- A string belongs to the level-`c` excess set exactly when some finite stage already certifies
that its excess sum exceeds `2 ^ c`. -/
lemma mem_prefixExcessSet_iff {m : BitString → ℝ≥0∞} {A : ℕ → BitString → ℕ}
    (hmono : ∀ s y, dyadicValue (A s y) s ≤ dyadicValue (A (s + 1) y) (s + 1))
    (hsup : ∀ y, ⨆ s, dyadicValue (A s y) s = m y) (c : ℕ) (x : BitString) :
    x ∈ prefixExcessSet m c ↔ ∃ s : ℕ, 2 ^ (c + s) < prefixExcessStage A x s := by
  rw [prefixExcessSet, Set.mem_setOf_eq, ← iSup_dyadicValue_prefixExcessStage hmono hsup x,
    lt_iSup_iff]
  refine exists_congr fun s => ?_
  rw [dyadicValue, ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num))
    (Or.inl (by norm_num)), ← pow_add]
  constructor
  · intro h
    have hc : ((2 ^ (c + s) : ℕ) : ℝ≥0∞) < ((prefixExcessStage A x s : ℕ) : ℝ≥0∞) := by
      push_cast
      exact h
    exact_mod_cast hc
  · intro h
    have hc : ((2 ^ (c + s) : ℕ) : ℝ≥0∞) < ((prefixExcessStage A x s : ℕ) : ℝ≥0∞) := by
      exact_mod_cast h
    push_cast at hc
    exact hc

/-- For a lower semicomputable `m` the family of level-`c` excess sets is uniformly recursively
enumerable. -/
lemma isRE_prefixExcessSet {m : BitString → ℝ≥0∞}
    (hm : IsLSC fun x (_ : BitString) => m x) :
    IsRE fun q : ℕ × BitString => q.2 ∈ prefixExcessSet m q.1 := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hm
  have hA : Computable₂ (fun (s : ℕ) (y : BitString) => approx s y []) :=
    hcomp.comp (Computable.pair Computable.fst
      (Computable.pair Computable.snd (Computable.const [])))
  have hmono' : ∀ (s : ℕ) (y : BitString),
      dyadicValue (approx s y []) s ≤ dyadicValue (approx (s + 1) y []) (s + 1) :=
    fun s y => hmono s y []
  have hsup' : ∀ y : BitString, ⨆ s, dyadicValue (approx s y []) s = m y :=
    fun y => hsup y []
  have hlt : Computable₂ (fun a b : ℕ => decide (a < b)) := primrec_decide_nat_lt.to_comp
  have hpow : Computable (fun r : (ℕ × BitString) × ℕ => 2 ^ (r.1.1 + r.2)) :=
    primrec_two_pow_aux.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.fst) Computable.snd)
  have hstage : Computable (fun r : (ℕ × BitString) × ℕ =>
      prefixExcessStage (fun s y => approx s y []) r.1.2 r.2) :=
    (computable_prefixExcessStage hA).comp (Computable.snd.comp Computable.fst)
      Computable.snd
  have hbool : IsRE (fun r : (ℕ × BitString) × ℕ =>
      2 ^ (r.1.1 + r.2) < prefixExcessStage (fun s y => approx s y []) r.1.2 r.2) :=
    isRE_of_computable_bool _
      (fun r => decide (2 ^ (r.1.1 + r.2)
        < prefixExcessStage (fun s y => approx s y []) r.1.2 r.2))
      (fun _ => by rw [decide_eq_true_iff]) (hlt.comp hpow hstage)
  refine (IsRE.exists_encodable (R := fun (q : ℕ × BitString) (s : ℕ) =>
    2 ^ (q.1 + s) < prefixExcessStage (fun s y => approx s y []) q.2 s) hbool).of_iff
    fun q => ?_
  exact (mem_prefixExcessSet_iff hmono' hsup' q.1 q.2).symm

/-! ### The ample excess lemma -/

/-- The sequences having a prefix in the level-`c` excess set have uniform measure at most `2 ^
(-c)`,
so the excess sets form a Martin-Löf test. -/
lemma uniformMeasure_prefixHitSet_prefixExcessSet_le {m : BitString → ℝ≥0∞}
    (hm : (∑' x : BitString, m x) ≤ 1) (c : ℕ) :
    uniformMeasure (prefixHitSet (prefixExcessSet m c)) ≤ (2 : ℝ≥0∞)⁻¹ ^ c := by
  classical
  set T : ℕ → Set CantorSeq := fun N => {w : CantorSeq |
    (2 : ℝ≥0∞) ^ c < prefixExcessPartial m (cantorPrefix w N)} with hT
  have hunion : prefixHitSet (prefixExcessSet m c) = ⋃ N, T N := by
    ext w
    simp only [prefixHitSet, Set.mem_setOf_eq, Set.mem_iUnion, hT, prefixExcessSet]
  have hmono : Monotone T := by
    intro N N' hNN' w hw
    exact lt_of_lt_of_le hw (prefixExcessPartial_mono_cantorPrefix m w hNN')
  rw [hunion]
  have htend := tendsto_measure_iUnion_atTop (μ := uniformMeasure) hmono
  refine le_of_tendsto htend (Filter.Eventually.of_forall fun N => ?_)
  exact measure_setOf_lt_prefixExcessPartial_le hm c N

/-- **The ample excess lemma** (SUV Theorem 94(d), second form, p. 151; Problem 146, p. 150;
Gács, rediscovered by J. Miller and L. Yu).  For a Martin-Löf random sequence (uniform
measure) and any lower semicomputable semimeasure `m` on strings the series
`∑ₙ 2ⁿ · m((ω)ₙ)` converges. -/
theorem tsum_two_pow_mul_ne_top_of_isMartinLofRandom_uniform {m : BitString → ℝ≥0∞}
    (hm : IsLowerSemicomputableSemimeasure m) {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) :
    (∑' n : ℕ, (2 : ℝ≥0∞) ^ n * m (cantorPrefix w n)) ≠ ⊤ := by
  have htest : IsMartinLofTest uniformMeasure fun c => prefixHitSet (prefixExcessSet m c) :=
    isMartinLofTest_prefixHitSet (isRE_prefixExcessSet hm.2)
      (fun c => uniformMeasure_prefixHitSet_prefixExcessSet_le hm.1 c)
  have hnot := hw _ htest
  rw [Set.mem_iInter] at hnot
  push_neg at hnot
  obtain ⟨c, hc⟩ := hnot
  have hbound : ∀ N : ℕ, prefixExcessPartial m (cantorPrefix w N) ≤ (2 : ℝ≥0∞) ^ c := by
    intro N
    by_contra hcon
    push_neg at hcon
    exact hc ⟨N, hcon⟩
  have hsum : (∑' n : ℕ, (2 : ℝ≥0∞) ^ n * m (cantorPrefix w n)) ≤ (2 : ℝ≥0∞) ^ c := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    refine le_trans ?_ (hbound N)
    rw [prefixExcessPartial_cantorPrefix]
    refine Finset.sum_le_sum_of_subset ?_
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  exact ne_top_of_le_ne_top (ENNReal.pow_ne_top (by norm_num)) hsum

/-- **The ample excess lemma, prefix-complexity form** (SUV Theorem 94(d), second form,
p. 151; Problem 146, p. 150).  For a Martin-Löf random sequence (uniform measure) the series
`∑ₙ 2^(n − K((ω)ₙ))` converges.

This is the instance of the previous theorem for the a priori semimeasure
`x ↦ aprioriMeasure U x []` of a prefix decompressor: it is a lower semicomputable
semimeasure (`aprioriMeasure_empty_isLowerSemicomputableSemimeasure`) and it dominates
`2^(−K_U)` (`complexityWeight_KP_le_aprioriMeasure`). -/
theorem tsum_two_pow_mul_complexityWeight_KPPlain_ne_top_of_isMartinLofRandom_uniform
    {U : Map} (hU : IsPrefixDecompressor U) {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) :
    (∑' n : ℕ, (2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (cantorPrefix w n))) ≠ ⊤ := by
  refine ne_top_of_le_ne_top
    (tsum_two_pow_mul_ne_top_of_isMartinLofRandom_uniform
      (aprioriMeasure_empty_isLowerSemicomputableSemimeasure U hU) hw)
    (ENNReal.tsum_le_tsum fun n => ?_)
  exact mul_le_mul_right (complexityWeight_KP_le_aprioriMeasure U (cantorPrefix w n) []) _

end Kolmogorov
