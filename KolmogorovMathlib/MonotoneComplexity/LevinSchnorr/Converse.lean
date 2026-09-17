/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore

/-!
# Section 5.6: the Kraft-Chaitin half of the Levin-Schnorr theorem

This module carries out the *second* half of the proof of SUV Theorem 90 (p. 147), which is
also the half that Theorem 92 has to redo (p. 148, "only the second part of the proof needs
to be redone"): from a Martin-Löf test one builds, by Kraft-Chaitin (Theorem 59, p. 96), a
prefix-free decompressor giving `K(xᵢ) ≤ -log μ(Ω_{xᵢ}) - c + O(1)` on the covering
intervals, and the `O(log c)` self-delimiting tag of the source is replaced here by summing
the requests of *all* levels at once with the geometric weights `2^c` on level `2c + 2`.

Concretely, `testRequestWeight μ g` is the request function handed to Kraft-Chaitin:
level `2c + 2` of the test enumerated by `g`, made prefix-free by the Chapter 3
disjointification `disjEnum`, contributes `2^c · μ(Ω_x)` at each of its intervals `Ω_x`.
Its total weight is at most `∑_c 2^c · 2^(-(2c+2)) = 1/2 ≤ 1`
(`tsum_testRequestWeight_le_one`), which is exactly the source's bookkeeping.

The only leaf is the lower semicomputability of that request function.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ### The request function of a Martin-Löf test -/

/-- SUV p. 147: the Kraft-Chaitin request weight attached to a Martin-Löf test enumerated by
`g`.  Level `2c + 2` is disjointified (`disjEnum`, Lemma 2 of Theorem 90) and each of its
intervals `Ω_x` requests weight `2^c · μ(Ω_x)`; the geometric factor is what makes the
deficiency `-log p(x) - K(x)` grow with `c`. -/
noncomputable def testRequestTerm (μ : Measure CantorSeq) (g : ℕ → ℕ → Option BitString)
    (n : ℕ) (x : BitString) : ℝ≥0∞ :=
  if disjEnum (g (2 * (Nat.unpair n).1 + 2)) (Nat.unpair n).2 = some x then cantorMass μ x
  else 0

/-- SUV p. 147: the total Kraft-Chaitin request at `x`.  The pair `(c, i)` -- level and
interval -- is carried by a single natural through `Nat.unpair`, which is the shape the
lower-semicomputability engine `isLSC_tsum_nsmul_of_uniform` consumes. -/
noncomputable def testRequestWeight (μ : Measure CantorSeq) (g : ℕ → ℕ → Option BitString)
    (x : BitString) (_ctx : BitString) : ℝ≥0∞ :=
  ∑' n : ℕ, ((2 ^ (Nat.unpair n).1 : ℕ) : ℝ≥0∞) * testRequestTerm μ g n x

/-- Reindexing a sum over `ℕ` by `Nat.unpair` gives the sum over `ℕ × ℕ`. -/
lemma tsum_unpair (F : ℕ × ℕ → ℝ≥0∞) : ∑' n : ℕ, F (Nat.unpair n) = ∑' p : ℕ × ℕ, F p := by
  have h := Equiv.tsum_eq Nat.pairEquiv.symm F
  exact h

/-- The weight requested by the test is the sum over levels and enumeration indices of `2 ^ level`
times the mass of the requested string. -/
lemma testRequestWeight_eq_tsum_prod (μ : Measure CantorSeq)
    (g : ℕ → ℕ → Option BitString) (x ctx : BitString) :
    testRequestWeight μ g x ctx
      = ∑' p : ℕ × ℕ, ((2 ^ p.1 : ℕ) : ℝ≥0∞) *
          (if disjEnum (g (2 * p.1 + 2)) p.2 = some x then cantorMass μ x else 0) := by
  rw [testRequestWeight]
  exact tsum_unpair (fun p : ℕ × ℕ => ((2 ^ p.1 : ℕ) : ℝ≥0∞) *
    (if disjEnum (g (2 * p.1 + 2)) p.2 = some x then cantorMass μ x else 0))

/-- A single interval of level `2c + 2` already contributes its full request. -/
lemma two_pow_mul_cantorMass_le_testRequestWeight (μ : Measure CantorSeq)
    (g : ℕ → ℕ → Option BitString) {c i : ℕ} {x : BitString}
    (hx : disjEnum (g (2 * c + 2)) i = some x) (ctx : BitString) :
    (2 : ℝ≥0∞) ^ c * cantorMass μ x ≤ testRequestWeight μ g x ctx := by
  rw [testRequestWeight_eq_tsum_prod]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (c, i))
  simp [hx]

/-- Summing an `Option`-indicator over all strings collapses to the `Option.elim`. -/
private lemma tsum_ite_option_eq (q : Option BitString) (f : BitString → ℝ≥0∞) :
    ∑' x : BitString, (if q = some x then f x else 0) = q.elim 0 f := by
  classical
  cases q with
  | none => simp
  | some y =>
      have h0 : ∀ x : BitString, x ≠ y →
          (if (some y : Option BitString) = some x then f x else 0) = 0 := by
        intro x hx
        simp [Ne.symm hx]
      rw [tsum_eq_single y h0]
      simp

/-- The total request weight of a Martin-Löf test is at most `1`: level `2c + 2` has
`μ`-measure at most `2^(-(2c+2))` and is charged `2^c`, so the levels contribute
`∑_c 2^(-(c+2)) = 1/2`. -/
theorem tsum_testRequestWeight_le_one {μ : Measure CantorSeq}
    {g : ℕ → ℕ → Option BitString}
    (hsmall : ∀ n, μ (⋃ i, coverSet (g n) i) ≤ (2 : ℝ≥0∞)⁻¹ ^ n) (ctx : BitString) :
    (∑' x : BitString, testRequestWeight μ g x ctx) ≤ 1 := by
  classical
  have hswap : (∑' x : BitString, testRequestWeight μ g x ctx)
      = ∑' p : ℕ × ℕ, (2 : ℝ≥0∞) ^ p.1
          * (disjEnum (g (2 * p.1 + 2)) p.2).elim 0 (cantorMass μ) := by
    simp only [testRequestWeight_eq_tsum_prod]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun p => ?_
    rw [ENNReal.tsum_mul_left, tsum_ite_option_eq]
    congr 1
    push_cast
    ring
  have hprod : (∑' p : ℕ × ℕ, (2 : ℝ≥0∞) ^ p.1
        * (disjEnum (g (2 * p.1 + 2)) p.2).elim 0 (cantorMass μ))
      = ∑' (c : ℕ) (i : ℕ), (2 : ℝ≥0∞) ^ c
        * (disjEnum (g (2 * c + 2)) i).elim 0 (cantorMass μ) :=
    ENNReal.tsum_prod (f := fun c i => (2 : ℝ≥0∞) ^ c
      * (disjEnum (g (2 * c + 2)) i).elim 0 (cantorMass μ))
  rw [hswap, hprod]
  have hlevel : ∀ c : ℕ,
      (∑' i : ℕ, (2 : ℝ≥0∞) ^ c * (disjEnum (g (2 * c + 2)) i).elim 0 (cantorMass μ))
        ≤ (2 : ℝ≥0∞)⁻¹ ^ (c + 2) := by
    intro c
    rw [ENNReal.tsum_mul_left, tsum_measure_disjEnum]
    refine le_trans (mul_le_mul_right (hsmall (2 * c + 2)) _) (le_of_eq ?_)
    have hcancel : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ c = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    calc (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ (2 * c + 2)
        = (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ c * (2 : ℝ≥0∞)⁻¹ ^ (c + 2)) := by
          rw [← pow_add]
          congr 2
          omega
      _ = (2 : ℝ≥0∞)⁻¹ ^ (c + 2) := by rw [← mul_assoc, hcancel, one_mul]
  refine le_trans (ENNReal.tsum_le_tsum hlevel) ?_
  have hgeo : (∑' c : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (c + 2))
      = (2 : ℝ≥0∞)⁻¹ ^ 2 * ∑' c : ℕ, (2 : ℝ≥0∞)⁻¹ ^ c := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun c => by rw [← pow_add, Nat.add_comm]
  rw [hgeo, ENNReal.tsum_geometric]
  have hone : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.sub_eq_of_eq_add (by norm_num) ?_]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  rw [hone, inv_inv, pow_two, mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  exact ENNReal.inv_le_one.2 one_le_two

/-- **Effectivity of the Kraft-Chaitin request** (SUV p. 147: the requests handed to
Kraft-Chaitin must be enumerable).  `testRequestWeight μ g` is lower semicomputable whenever
`μ` is a computable measure and `g` is a computable enumeration: the cylinder mass is lower
semicomputable (`isLSC_cantorMass`), the level/interval index is decidable, and the weighted
sum is assembled by `isLSC_tsum_nsmul_of_uniform`. -/
theorem isLSC_testRequestWeight {μ : Measure CantorSeq} (hμ : IsComputableMeasure μ)
    {g : ℕ → ℕ → Option BitString} (hg : Computable₂ g) :
    IsLSC (testRequestWeight μ g) := by
  classical
  obtain ⟨M, hMmono, hMsup, hMcomp⟩ := isLSC_cantorMass hμ
  have hcondsel : ∀ (n : ℕ) (x : BitString),
      testRequestTerm μ g n x
        = if disjEnum (g (2 * (Nat.unpair n).1 + 2)) (Nat.unpair n).2 = some x then
            cantorMass μ x else 0 := fun _ _ => rfl
  refine isLSC_tsum_nsmul_of_uniform
    (wt := fun n => 2 ^ (Nat.unpair n).1)
    (b := fun n x => testRequestTerm μ g n x)
    (A := fun n s x =>
      if disjEnum (g (2 * (Nat.unpair n).1 + 2)) (Nat.unpair n).2 = some x then M s x [] else 0)
    (Primrec.to_comp (primrec_two_pow_aux.comp (Primrec.fst.comp Primrec.unpair)))
    ?_ ?_ ?_
  · intro n s x
    by_cases h : disjEnum (g (2 * (Nat.unpair n).1 + 2)) (Nat.unpair n).2 = some x
    · simpa [h] using hMmono s x []
    · simp [h, dyadicValue]
  · intro n x
    by_cases h : disjEnum (g (2 * (Nat.unpair n).1 + 2)) (Nat.unpair n).2 = some x
    · simp only [h, if_pos, testRequestTerm]
      exact hMsup x []
    · simp [h, testRequestTerm, dyadicValue]
  · have hlevel : Computable fun p : ℕ × ℕ × BitString => 2 * (Nat.unpair p.1).1 + 2 :=
      Primrec.to_comp ((Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp (Primrec.unpair.comp
          Primrec.fst)))
        (Primrec.const 2)))
    have hidx : Computable fun p : ℕ × ℕ × BitString => (Nat.unpair p.1).2 :=
      Primrec.to_comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
    have hdisj : Computable fun p : ℕ × ℕ × BitString =>
        disjEnum (g (2 * (Nat.unpair p.1).1 + 2)) (Nat.unpair p.1).2 :=
      (computable_disjEnum hg).comp hlevel hidx
    have heqb : Computable₂ (fun u v : Option BitString => decide (u = v)) :=
      Primrec₂.to_comp (PrimrecPred.decide Primrec.eq)
    have hcond : Computable fun p : ℕ × ℕ × BitString =>
        decide (disjEnum (g (2 * (Nat.unpair p.1).1 + 2)) (Nat.unpair p.1).2
          = some p.2.2) :=
      heqb.comp hdisj (Computable.option_some.comp (Computable.snd.comp Computable.snd))
    have hM : Computable fun p : ℕ × ℕ × BitString => M p.2.1 p.2.2 [] :=
      hMcomp.comp (Computable.pair (Computable.fst.comp Computable.snd)
        (Computable.pair (Computable.snd.comp Computable.snd) (Computable.const [])))
    refine (Computable.cond hcond hM (Computable.const 0)).of_eq fun p => ?_
    by_cases h : disjEnum (g (2 * (Nat.unpair p.1).1 + 2)) (Nat.unpair p.1).2 = some p.2.2
    · simp [h]
    · simp [h]

/-! ### The prefix-complexity bound on the covering intervals -/

/-- SUV p. 147: Kraft-Chaitin turns the request function into a prefix-free decompressor, and
optimality of `U` transfers the bound to `K`: there is one constant `c₀` such that every
interval `Ω_x` of level `2c + 2` of the test satisfies `K(x) ≤ -log μ(Ω_x) - c + c₀`, i.e.
multiplicatively `2^(-c₀) · 2^c · μ(Ω_x) ≤ 2^(-K(x))`. -/
theorem exists_const_two_pow_mul_cantorMass_le_complexityWeight_KPPlain
    {μ : Measure CantorSeq} (hμ : IsComputableMeasure μ) {U : Map}
    (hU : IsOptimalPrefixConditional U) {g : ℕ → ℕ → Option BitString} (hg : Computable₂ g)
    (hsmall : ∀ n, μ (⋃ i, coverSet (g n) i) ≤ (2 : ℝ≥0∞)⁻¹ ^ n) :
    ∃ c₀ : ℕ, ∀ (c i : ℕ) (x : BitString), disjEnum (g (2 * c + 2)) i = some x →
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * ((2 : ℝ≥0∞) ^ c * cantorMass μ x)
        ≤ complexityWeight (KPPlain U x) := by
  obtain ⟨M', hM', c₁, hc₁⟩ := kraftChaitin_realization_bound_unit
    (isLSC_testRequestWeight hμ hg) (fun ctx => tsum_testRequestWeight_le_one hsmall ctx)
  obtain ⟨c₂, hc₂⟩ := hU.invariance hM'
  refine ⟨c₁ + c₂, fun c i x hx => ?_⟩
  have hstep : complexityWeight (KP M' x []) * (2 : ℝ≥0∞)⁻¹ ^ c₂
      ≤ complexityWeight (KPPlain U x) := by
    rw [← complexityWeight_add_nat]
    exact complexityWeight_le_of_le (hc₂ x [])
  calc (2 : ℝ≥0∞)⁻¹ ^ (c₁ + c₂) * ((2 : ℝ≥0∞) ^ c * cantorMass μ x)
      = ((2 : ℝ≥0∞)⁻¹ ^ c₁ * ((2 : ℝ≥0∞) ^ c * cantorMass μ x)) * (2 : ℝ≥0∞)⁻¹ ^ c₂ := by
        rw [pow_add]; ring
    _ ≤ ((2 : ℝ≥0∞)⁻¹ ^ c₁ * testRequestWeight μ g x []) * (2 : ℝ≥0∞)⁻¹ ^ c₂ := by
        gcongr
        exact two_pow_mul_cantorMass_le_testRequestWeight μ g hx []
    _ ≤ complexityWeight (KP M' x []) * (2 : ℝ≥0∞)⁻¹ ^ c₂ := by
        gcongr
        exact hc₁ x []
    _ ≤ complexityWeight (KPPlain U x) := hstep

/-! ### The converse half of Theorems 90 and 92 -/

/-- SUV Theorem 92 (p. 148), converse direction, in contrapositive form: if `w` is *not*
Martin-Löf random for the computable probability measure `μ`, then its prefix-complexity
deficiency is unbounded along the prefixes -- for every `C` some prefix `x` of `w` has
`2^C · p(x) < 2^(-K(x))`.

Source proof (p. 147): apply Kraft-Chaitin to the universal Martin-Löf test, whose level
`2C + c₀ + 3` still contains `w`. -/
theorem exists_prefix_two_pow_mul_cantorMass_lt_complexityWeight_KPPlain
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {U : Map}
    (hU : IsOptimalPrefixConditional U) {w : CantorSeq} (hw : ¬ IsMartinLofRandom μ w)
    (C : ℕ) :
    ∃ n : ℕ, (2 : ℝ≥0∞) ^ C * cantorMass μ (cantorPrefix w n)
      < complexityWeight (KPPlain U (cantorPrefix w n)) := by
  classical
  obtain ⟨V, hV⟩ := exists_universal_martinLof_test hμ
  have hmem : w ∈ ⋂ n, V n := (not_isMartinLofRandom_iff_mem_universal_test hV w).1 hw
  obtain ⟨g, hg, hgV⟩ := hV.1.1
  have hsmall : ∀ n, μ (⋃ i, coverSet (g n) i) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    have hb := hV.1.2 n
    rw [dyadicValue_one_eq_inv_two_pow'] at hb
    rw [show (⋃ i, coverSet (g n) i) = V n from (hgV n).symm]
    exact hb
  obtain ⟨c₀, hc₀⟩ := exists_const_two_pow_mul_cantorMass_le_complexityWeight_KPPlain
    hμ hU hg hsmall
  obtain ⟨cK, hcK⟩ := KPPlain_le_two_mul_length U hU
  set c : ℕ := C + c₀ + 1 with hc
  have hwV : w ∈ V (2 * c + 2) := Set.mem_iInter.1 hmem _
  have hveq : V (2 * c + 2) = ⋃ j, coverSet (g (2 * c + 2)) j := hgV (2 * c + 2)
  have hcover : w ∈ ⋃ i, coverSet (disjEnum (g (2 * c + 2))) i := by
    rw [coverSet_disjEnum_iUnion, ← hveq]
    exact hwV
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hcover
  rcases hx : disjEnum (g (2 * c + 2)) i with _ | x
  · rw [coverSet, hx] at hi
    exact absurd hi (Set.notMem_empty w)
  · rw [coverSet, hx] at hi
    have hpref : cantorPrefix w x.length = x :=
      (isCantorPrefix_iff_cantorPrefix_eq x w).1 hi
    refine ⟨x.length, ?_⟩
    rw [hpref]
    have hlow := hc₀ c i x hx
    -- the mass cannot vanish: `K(x)` is finite, so `2^(-K(x)) > 0`
    rcases eq_or_ne (cantorMass μ x) 0 with hzero | hpos
    · rw [hzero, mul_zero]
      refine (complexityWeight_pos_iff _).2 ?_
      exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hcK x)
    · have hmasstop : cantorMass μ x ≠ ⊤ := measure_ne_top μ _
      by_contra hcon
      rw [not_lt] at hcon
      have hkey : (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞) ^ c * cantorMass μ x
          ≤ (2 : ℝ≥0∞) ^ C * cantorMass μ x := by
        rw [mul_assoc]
        exact le_trans hlow hcon
      have hcancel : (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞) ^ c ≤ (2 : ℝ≥0∞) ^ C :=
        (ENNReal.mul_le_mul_iff_left hpos hmasstop).1 hkey
      have heval : (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞) ^ c = (2 : ℝ≥0∞) ^ (C + 1) := by
        rw [hc, show C + c₀ + 1 = c₀ + (C + 1) by omega, pow_add, ← mul_assoc,
          ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, one_mul]
      rw [heval] at hcancel
      have hscale : (2 : ℝ≥0∞) ^ (C + 1) * (2 : ℝ≥0∞)⁻¹ ^ C
          ≤ (2 : ℝ≥0∞) ^ C * (2 : ℝ≥0∞)⁻¹ ^ C := by gcongr
      have hL : (2 : ℝ≥0∞) ^ (C + 1) * (2 : ℝ≥0∞)⁻¹ ^ C = 2 := by
        rw [pow_succ, mul_comm ((2 : ℝ≥0∞) ^ C) 2, mul_assoc, ← mul_pow,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, mul_one]
      have hR : (2 : ℝ≥0∞) ^ C * (2 : ℝ≥0∞)⁻¹ ^ C = 1 := by
        rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
      rw [hL, hR] at hscale
      exact absurd hscale (by norm_num)

/-- SUV Theorem 92 (Section 5.6, p. 148), converse direction, packaged: bounded prefix
deficiency along the prefixes of `w` implies Martin-Löf randomness.  This is the
contrapositive of
`exists_prefix_two_pow_mul_cantorMass_lt_complexityWeight_KPPlain`. -/
theorem isMartinLofRandom_of_boundedPrefixDeficiency_core {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {U : Map}
    (hU : IsOptimalPrefixConditional U) {w : CantorSeq}
    (hw : BoundedPrefixDeficiency μ U w) : IsMartinLofRandom μ w := by
  by_contra hnr
  obtain ⟨C, hC⟩ := hw
  obtain ⟨n, hn⟩ :=
    exists_prefix_two_pow_mul_cantorMass_lt_complexityWeight_KPPlain hμ hU hnr C
  exact absurd (hC n) (not_le.2 hn)

/-- SUV Theorem 85(d) (`KM ≤ K + O(1)`) read multiplicatively: a bound on the *monotone*
deficiency of the prefixes of `w` gives the same bound, with a larger constant, on the
*prefix* deficiency.  This is why the source only has to redo the second part of the proof
for Theorem 92 (p. 148): the converse half of Theorem 92 implies that of Theorem 90. -/
theorem boundedPrefixDeficiency_of_boundedMonotoneDeficiency {μ : Measure CantorSeq}
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D) {U : Map}
    (hU : IsOptimalPrefixConditional U) {w : CantorSeq}
    (hw : BoundedMonotoneDeficiency μ D w) : BoundedPrefixDeficiency μ U w := by
  obtain ⟨c, hc⟩ := hw
  obtain ⟨c₀, hc₀⟩ := exists_const_KMOf_le_KP hD hU.isPrefixMachine hU.isDecompressor
  have hpow : (2 : ℝ≥0∞) ^ c₀ * (2 : ℝ≥0∞)⁻¹ ^ c₀ = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  refine ⟨c + c₀, fun n => ?_⟩
  have hstep : complexityWeight (KPPlain U (cantorPrefix w n)) * (2 : ℝ≥0∞)⁻¹ ^ c₀
      ≤ (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n) := by
    rw [← complexityWeight_add_nat]
    exact le_trans (complexityWeight_le_of_le (hc₀ (cantorPrefix w n))) (hc n)
  calc complexityWeight (KPPlain U (cantorPrefix w n))
      = (2 : ℝ≥0∞) ^ c₀
          * (complexityWeight (KPPlain U (cantorPrefix w n)) * (2 : ℝ≥0∞)⁻¹ ^ c₀) := by
        rw [← mul_assoc, mul_comm ((2 : ℝ≥0∞) ^ c₀) _, mul_assoc, hpow, mul_one]
    _ ≤ (2 : ℝ≥0∞) ^ c₀ * ((2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n)) := by gcongr
    _ = (2 : ℝ≥0∞) ^ (c + c₀) * cantorMass μ (cantorPrefix w n) := by
        rw [pow_add]; ring

end Kolmogorov
