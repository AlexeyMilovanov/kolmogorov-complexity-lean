/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveOpen
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorrMass
import KolmogorovMathlib.MonotoneComplexity.MonotoneAPriori

/-!
# The a priori complexity deficiency test

The sets `aPrioriExcessSet c` of sequences having a prefix of length `n` on which the
universal continuous semimeasure exceeds `2^c · 2^(-n)` form a Martin-Löf test for the
uniform measure: they are uniformly effectively open (because the universal continuous
semimeasure is lower semicomputable) and, by `uniformMeasure_setOf_exists_prefix_mass_gt_le`,
the `c`-th set has measure at most `2^(-c)`.

Consequently every Martin-Löf random sequence satisfies the complexity lower bound
`KA (w ↾ n) ≥ n - c` for a constant `c` and all `n`, which is one half of the
Levin-Schnorr criterion.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- The `c`-th level of the a priori deficiency test: sequences with a prefix whose
a priori mass exceeds `2^c` times its uniform mass. -/
def aPrioriExcessSet (c : ℕ) : Set CantorSeq :=
  {w | ∃ n, (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ n < universalContinuousSemimeasure (cantorPrefix w n)}

/-- Comparing a scaled uniform mass with a dyadic rational is a statement about natural
numbers. -/
lemma two_pow_mul_inv_two_pow_lt_dyadicValue_iff (c L k s : ℕ) :
    (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ L < dyadicValue k s ↔ 2 ^ c * 2 ^ s < k * 2 ^ L := by
  have h2L : ((2 : ℝ≥0∞) ^ L) ≠ 0 := by positivity
  have h2Lt : ((2 : ℝ≥0∞) ^ L) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have h2s : ((2 : ℝ≥0∞) ^ s) ≠ 0 := by positivity
  have h2st : ((2 : ℝ≥0∞) ^ s) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [dyadicValue, ← ENNReal.inv_pow, ← div_eq_mul_inv,
    ENNReal.div_lt_iff (Or.inl h2L) (Or.inl h2Lt), div_eq_mul_inv, mul_right_comm,
    ← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (Or.inl h2s) (Or.inl h2st),
    show ((2 : ℝ≥0∞) ^ c * 2 ^ s) = ((2 ^ c * 2 ^ s : ℕ) : ℝ≥0∞) by push_cast; ring,
    show ((k : ℝ≥0∞) * 2 ^ L) = ((k * 2 ^ L : ℕ) : ℝ≥0∞) by push_cast; ring]
  exact_mod_cast Iff.rfl

/-- The deficiency test is uniformly effectively open. -/
theorem isUniformlyEffectiveOpen_aPrioriExcessSet :
    IsUniformlyEffectiveOpen aPrioriExcessSet := by
  classical
  obtain ⟨approx, _hmono, hsup, hcomp⟩ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2
  refine ⟨fun c i => (Encodable.decode (α := ℕ × BitString) i).bind (fun p =>
      if 2 ^ c * 2 ^ p.1 < approx p.1 p.2 [] * 2 ^ p.2.length then some p.2 else none), ?_, ?_⟩
  · have hdec : Computable (fun q : ℕ × ℕ => Encodable.decode (α := ℕ × BitString) q.2) :=
      Computable.decode.comp Computable.snd
    refine Computable.option_bind hdec ?_
    have hpost : Computable (fun t : ℕ × ℕ × BitString =>
        if t.1 < t.2.1 * 2 ^ t.2.2.length then some t.2.2 else none) := by
      refine Primrec.to_comp ?_
      have hpow : Primrec (fun t : ℕ × ℕ × BitString => 2 ^ t.2.2.length) :=
        primrec_two_pow_aux.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
      have hlt : PrimrecPred (fun t : ℕ × ℕ × BitString => t.1 < t.2.1 * 2 ^ t.2.2.length) :=
        Primrec.nat_lt.comp Primrec.fst
          (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) hpow)
      exact Primrec.ite hlt (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const none)
    have hk : Computable (fun r : (ℕ × ℕ) × (ℕ × BitString) => approx r.2.1 r.2.2 []) :=
      hcomp.comp (Computable.pair (Computable.fst.comp Computable.snd)
        (Computable.pair (Computable.snd.comp Computable.snd) (Computable.const [])))
    have hlhs : Computable (fun r : (ℕ × ℕ) × (ℕ × BitString) => 2 ^ r.1.1 * 2 ^ r.2.1) :=
      (Primrec.nat_mul.comp (primrec_two_pow_aux.comp (Primrec.fst.comp Primrec.fst))
        (primrec_two_pow_aux.comp (Primrec.fst.comp Primrec.snd))).to_comp
    have hpre : Computable (fun r : (ℕ × ℕ) × (ℕ × BitString) =>
        ((2 ^ r.1.1 * 2 ^ r.2.1 : ℕ), (approx r.2.1 r.2.2 [], r.2.2))) :=
      Computable.pair hlhs (Computable.pair hk (Computable.snd.comp Computable.snd))
    exact (hpost.comp hpre).of_eq (fun _ => rfl)
  · have hsup' : ∀ x : BitString,
        ⨆ s, dyadicValue (approx s x []) s = universalContinuousSemimeasure x :=
      fun x => hsup x []
    intro c
    ext w
    simp only [aPrioriExcessSet, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      set x : BitString := cantorPrefix w n with hx
      have hxlen : x.length = n := cantorPrefix_length w n
      have hmass : universalContinuousSemimeasure x
          = ⨆ s, dyadicValue (approx s x []) s := (hsup' x).symm
      rw [hmass, lt_iSup_iff] at hn
      obtain ⟨s, hs⟩ := hn
      have hcond : 2 ^ c * 2 ^ s < approx s x [] * 2 ^ x.length := by
        rw [hxlen]
        exact (two_pow_mul_inv_two_pow_lt_dyadicValue_iff c n (approx s x []) s).1 hs
      refine ⟨Encodable.encode ((s, x) : ℕ × BitString), ?_⟩
      simp only [Encodable.encodek, Option.bind_some, hcond, if_pos]
      have : w ∈ cantorCylinder x := by
        rw [hx]
        exact (isCantorPrefix_iff_cantorPrefix_eq _ w).2 (by rw [cantorPrefix_length])
      simpa using this
    · rintro ⟨i, hi⟩
      rcases hdecode : Encodable.decode (α := ℕ × BitString) i with _ | p
      · rw [hdecode] at hi; simp at hi
      · rw [hdecode] at hi
        simp only [Option.bind_some] at hi
        by_cases hcond : 2 ^ c * 2 ^ p.1 < approx p.1 p.2 [] * 2 ^ p.2.length
        · rw [if_pos hcond] at hi
          simp only [Option.elim_some] at hi
          have hpref : cantorPrefix w p.2.length = p.2 :=
            (isCantorPrefix_iff_cantorPrefix_eq _ w).1 hi
          refine ⟨p.2.length, ?_⟩
          rw [hpref]
          have hlt : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ p.2.length
              < dyadicValue (approx p.1 p.2 []) p.1 :=
            (two_pow_mul_inv_two_pow_lt_dyadicValue_iff c p.2.length (approx p.1 p.2 []) p.1).2
              hcond
          refine lt_of_lt_of_le hlt ?_
          rw [← hsup' p.2]
          exact le_iSup (fun s => dyadicValue (approx s p.2 []) s) p.1
        · rw [if_neg hcond] at hi; simp at hi

/-- The deficiency sets form a Martin-Löf test for the uniform measure. -/
theorem isMartinLofTest_aPrioriExcessSet :
    IsMartinLofTest uniformMeasure aPrioriExcessSet := by
  refine ⟨isUniformlyEffectiveOpen_aPrioriExcessSet, fun c => ?_⟩
  rw [dyadicValue_one_eq_inv_two_pow']
  exact uniformMeasure_setOf_exists_prefix_mass_gt_le
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1 c

/-- **One half of the Levin-Schnorr criterion.** Every Martin-Löf random sequence has
a priori complexity of its length-`n` prefix at least `n - c`, for a constant `c`
independent of `n`. -/
theorem exists_const_le_KA_cantorPrefix_of_isMartinLofRandom {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) :
    ∃ c : ℕ, ∀ n : ℕ, (n : ℝ) ≤ KA (cantorPrefix w n) + c := by
  by_contra hcon
  push_neg at hcon
  refine hw aPrioriExcessSet isMartinLofTest_aPrioriExcessSet (Set.mem_iInter.2 fun c => ?_)
  obtain ⟨n, hn⟩ := hcon c
  refine ⟨n, ?_⟩
  have h := mass_gt_of_KA_add_lt (x := cantorPrefix w n) (c := c) (by
    rw [cantorPrefix_length]; linarith)
  rwa [cantorPrefix_length] at h

/-- **Levin-Schnorr lower bound in monotone form.** Every Martin-Löf random sequence has
monotone complexity of its length-`n` prefix at least `n - c`, for a constant `c`
independent of `n`. -/
theorem exists_const_le_KMOf_cantorPrefix_of_isMartinLofRandom
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D)
    {w : CantorSeq} (hw : IsMartinLofRandom uniformMeasure w) :
    ∃ c : ℝ, ∀ n : ℕ, (n : ℝ) ≤ ((KMOf D (cantorPrefix w n)).toNat : ℝ) + c := by
  obtain ⟨c₁, hc₁⟩ := exists_const_le_KA_cantorPrefix_of_isMartinLofRandom hw
  obtain ⟨c₂, hc₂⟩ := exists_const_KA_le_KMOf hD
  refine ⟨(c₁ : ℝ) + c₂, fun n => ?_⟩
  have h₁ := hc₁ n
  have h₂ := hc₂ (cantorPrefix w n)
  linarith

end Kolmogorov
