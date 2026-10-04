import KolmogorovMathlib.InformationInequalities.Typization.Uniform

/-!
# Romashchenko's theorem (Theorem 212)

SUV Section 10.6, p. 327, Theorem 212.

An entropy inequality holds for complexities with `O(log N)` precision: take the typization set
of Theorem 211 and a uniformly random point of it, whose entropies are `O(log N)`-close to the
complexities.  Together with the easy direction of Section 10.1 this gives the equivalence
`holdsForEntropies_iff_holdsForComplexitiesCplx` between linear inequalities for Shannon entropies
and for plain Kolmogorov complexities of strings of complexity at most `N`.
-/

namespace Kolmogorov

open Finset
open Kolmogorov.CodedFiniteDistribution

variable {n : ℕ}

private lemma N_lt_two_pow_bits_length (N : ℕ) : N < 2 ^ (Nat.bits N).length := by
  induction N using Nat.binaryRec' with
  | zero => exact Nat.zero_lt_one
  | bit b m hm ih =>
    rw [Nat.bits_append_bit _ _ hm]
    rw [List.length_cons, pow_add, pow_one, mul_comm]
    cases b
    · dsimp [Nat.bit]
      linarith
    · dsimp [Nat.bit]
      linarith

private lemma logb_le_logSlack (c N : ℕ) (hN : 1 < N) : (c : ℝ) * Real.logb 2 N ≤ logSlack c N := by
  have h_le : (N : ℝ) ≤ (2 : ℝ) ^ ((Nat.bits N).length : ℝ) := by
    have h := N_lt_two_pow_bits_length N
    exact_mod_cast h.le
  have hpos : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have htwo : (1 : ℝ) < 2 := one_lt_two
  have hlog := (Real.logb_le_iff_le_rpow htwo hpos).mpr h_le
  have h_mul : (c : ℝ) * Real.logb 2 N ≤ (c : ℝ) * ((Nat.bits N).length : ℝ) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h_slack : (c : ℝ) * ((Nat.bits N).length : ℝ) ≤ logSlack c N := by
    dsimp [logSlack]
    push_cast
    linarith
  exact h_mul.trans h_slack

private lemma logSlack_max_two_le (c N : ℕ) : logSlack c (max N 2) ≤ logSlack (3 * c) N := by
  match N with
  | 0 =>
    change logSlack c 2 ≤ logSlack (3 * c) 0
    dsimp [logSlack]
    have h2 : (Nat.bits 2).length = 2 := rfl
    have h0 : (Nat.bits 0).length = 0 := rfl
    rw [h2, h0]
    omega
  | 1 =>
    change logSlack c 2 ≤ logSlack (3 * c) 1
    dsimp [logSlack]
    have h2 : (Nat.bits 2).length = 2 := rfl
    have h1 : (Nat.bits 1).length = 1 := rfl
    rw [h2, h1]
    omega
  | N + 2 =>
    have hmax : max (N + 2) 2 = N + 2 := by omega
    rw [hmax]
    exact logSlack_mono_left (by omega) (N + 2)

private lemma holdsForComplexitiesCplx_of_holdsForEntropies
    (f : LinearForm n) (D : Map) (hD : isOptimalConditional D)
    (h : HoldsForEntropies f) : HoldsForComplexitiesCplx f D := by
  obtain ⟨d, hd⟩ := exists_cUniform_typization D hD
  let sum_f := Nat.ceil (∑ I ∈ nonemptyParts n, |f I|)
  let c_total := 3 * (2 * sum_f * d)
  refine ⟨c_total, fun N x hN => ?_⟩
  let N' := max N 2
  have hN' : 1 < N' := by omega
  have h_plainK : ∀ i, plainK D (x i) ≤ (N' : ℕ∞) :=
    fun i => (hN i).trans (by exact_mod_cast le_max_left N 2)
  obtain ⟨m, A, hA_nonempty, hA_unif, hA_bound⟩ := hd N' hN' x h_plainK
  have h_evalLogSize := evalLogSize_le_of_isCUniform f h A hA_nonempty hA_unif
  have h_diff : ∀ I ∈ nonemptyParts n,
      |Real.logb 2 (projCard A I) - ((tuplePlainK D x I).toNat : ℝ)| ≤ (logSlack d N' : ℝ) := by
    intro I _
    have h_empty : Disjoint ∅ I := by simp
    have h_bound := hA_bound ∅ I h_empty
    have h_proj : maxSection A I ∅ = projCard A I := maxSection_empty A I
    have h_plain : tupleCondK D x I ∅ = tuplePlainK D x I := by
      rw [tupleCondK, subtupleCode_empty, tuplePlainK]
      rfl
    rw [h_proj, h_plain] at h_bound
    exact h_bound
  have h_eval_diff : |f.evalComplexity D x - f.evalLogSize A| ≤ (sum_f : ℝ) * logSlack d N' := by
    dsimp [LinearForm.evalComplexity, LinearForm.evalLogSize]
    rw [← Finset.sum_sub_distrib]
    calc |∑ I ∈ nonemptyParts n,
        (f I * ((tuplePlainK D x I).toNat : ℝ) - f I * Real.logb 2 (projCard A I))|
      _ ≤ ∑ I ∈ nonemptyParts n,
        |f I * ((tuplePlainK D x I).toNat : ℝ) - f I * Real.logb 2 (projCard A I)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I ∈ nonemptyParts n,
          |f I| * |((tuplePlainK D x I).toNat : ℝ) - Real.logb 2 (projCard A I)| := by
        apply Finset.sum_congr rfl
        intro I _
        rw [← mul_sub, abs_mul]
      _ ≤ ∑ I ∈ nonemptyParts n, |f I| * (logSlack d N' : ℝ) := by
        apply Finset.sum_le_sum
        intro I hI
        have h_abs := h_diff I hI
        have h_eq : |((tuplePlainK D x I).toNat : ℝ) - Real.logb 2 (projCard A I)| =
            |Real.logb 2 (projCard A I) - ((tuplePlainK D x I).toNat : ℝ)| :=
              abs_sub_comm _ _
        rw [h_eq]
        exact mul_le_mul_of_nonneg_left h_abs (abs_nonneg _)
      _ = (∑ I ∈ nonemptyParts n, |f I|) * (logSlack d N' : ℝ) := by rw [← Finset.sum_mul]
      _ ≤ (sum_f : ℝ) * (logSlack d N' : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact Nat.le_ceil _
  have h_eval_le : f.evalComplexity D x ≤
      f.evalLogSize A + (sum_f : ℝ) * logSlack d N' := by
    have h_abs : f.evalComplexity D x - f.evalLogSize A ≤ (sum_f : ℝ) * logSlack d N' :=
    le_trans (le_abs_self _) h_eval_diff
    linarith
  have h_logb_Nd : Real.logb 2 ((N' : ℝ) ^ d) = d * Real.logb 2 (N' : ℝ) := by
    have hN'_pos : (0 : ℝ) < N' := by exact_mod_cast (zero_lt_one.trans hN')
    exact Real.logb_pow 2 N' d
  rw [h_logb_Nd] at h_evalLogSize
  have h_evalLogSize_le2 : f.evalLogSize A ≤
      (sum_f : ℝ) * d * Real.logb 2 (N' : ℝ) := by
    calc f.evalLogSize A ≤
        (∑ I ∈ nonemptyParts n, |f I|) * (d * Real.logb 2 (N' : ℝ)) := h_evalLogSize
      _ = (∑ I ∈ nonemptyParts n, |f I|) * (d * Real.logb 2 (N' : ℝ)) := by ring
      _ ≤ (sum_f : ℝ) * (d * Real.logb 2 (N' : ℝ)) := by
        have hN'_pos : (0 : ℝ) < N' := by exact_mod_cast (zero_lt_one.trans hN')
        have hpos : 0 ≤ (d : ℝ) * Real.logb 2 (N' : ℝ) := by
          refine mul_nonneg (Nat.cast_nonneg _) ?_
          have h1 : (1 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hN'.le
          have hlog := (Real.logb_nonneg_iff one_lt_two hN'_pos).mpr h1
          exact hlog
        have h1 : (∑ I ∈ nonemptyParts n, |f I|) ≤ (sum_f : ℝ) := Nat.le_ceil _
        exact mul_le_mul_of_nonneg_right h1 hpos
      _ = (sum_f : ℝ) * d * Real.logb 2 (N' : ℝ) := by ring
  have h_bound1 : (sum_f : ℝ) * d * Real.logb 2 (N' : ℝ) ≤ (sum_f : ℝ) * logSlack d N' := by
    have h_log_slack := logb_le_logSlack d N' hN'
    calc (sum_f : ℝ) * d * Real.logb 2 (N' : ℝ) =
        (sum_f : ℝ) * (d * Real.logb 2 (N' : ℝ)) := by ring
      _ ≤ (sum_f : ℝ) * logSlack d N' := mul_le_mul_of_nonneg_left h_log_slack (Nat.cast_nonneg _)
  have h_eval_le2 : f.evalComplexity D x ≤
      (2 * sum_f * d : ℕ) * (Nat.bits N').length + (2 * sum_f * d : ℕ) := by
    calc f.evalComplexity D x ≤ f.evalLogSize A + (sum_f : ℝ) * logSlack d N' := h_eval_le
      _ ≤ (sum_f : ℝ) * d * Real.logb 2 (N' : ℝ) + (sum_f : ℝ) * logSlack d N' := by linarith
      _ ≤ (sum_f : ℝ) * logSlack d N' + (sum_f : ℝ) * logSlack d N' := by linarith
      _ = 2 * (sum_f : ℝ) * logSlack d N' := by ring
      _ = 2 * (sum_f : ℝ) * (d * (Nat.bits N').length + d : ℝ) := by
        have hd : (logSlack d N' : ℝ) = d * (Nat.bits N').length + d := by
          dsimp [logSlack]
          push_cast
          ring
        rw [hd]
      _ = (2 * sum_f * d : ℕ) * (Nat.bits N').length + (2 * sum_f * d : ℕ) := by
        push_cast
        ring
  have h_slack_eval : f.evalComplexity D x ≤ logSlack (2 * sum_f * d) N' := by
    calc f.evalComplexity D x ≤
        (2 * sum_f * d : ℕ) * (Nat.bits N').length + (2 * sum_f * d : ℕ) := h_eval_le2
      _ = logSlack (2 * sum_f * d) N' := by
        dsimp [logSlack]
        push_cast
        ring
  have h_slack_max : (logSlack (2 * sum_f * d) N' : ℝ) ≤ logSlack c_total N := by
    have h := logSlack_max_two_le (2 * sum_f * d) N
    exact_mod_cast h
  exact h_slack_eval.trans h_slack_max

private lemma holdsForComplexitiesLen_of_holdsForComplexitiesCplx
    (f : LinearForm n) (D : Map) (hD : isOptimalConditional D)
    (h : HoldsForComplexitiesCplx f D) : HoldsForComplexitiesLen f D := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨cLength, hLength⟩ := plainK_le_length D hD
  obtain ⟨C, hC⟩ := logSlack_linear_bound c 1 cLength
  refine ⟨C, fun N x hx => ?_⟩
  have hcomplexity : ∀ i, plainK D (x i) ≤ ((N + cLength : ℕ) : ℕ∞) := by
    intro i
    calc
      plainK D (x i) ≤ (programLength (x i) : ℕ∞) + cLength := hLength (x i)
      _ ≤ ((N + cLength : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.add_le_add_right ((length_le_tupleMaxLength x i).trans hx) cLength
  exact (hc (N + cLength) x hcomplexity).trans (by
    simpa [Nat.one_mul] using hC N)

/-- **Theorem 212 (A. Romashchenko).**  A linear form is valid for the entropies of all tuples
of random variables if and only if it is valid, with `O(log N)` precision, for the plain
complexities of all tuples of strings of complexity at most `N`.

The forward implication is the book's Theorem 212: take the typization set `A(x)` of
Theorem 211 and a uniformly random point of it; by Theorem 210(d) its entropies are
`O(log N)`-close to the log-sizes of the projections, which are `O(log N)`-close to the
complexities.  The reverse implication is the argument of Section 10.1, which the proof of
Theorem 212 invokes explicitly.  The constant of `O(log N)` (the `c` inside
`HoldsForComplexitiesCplx`) depends on `n` — exponentially, the book says — and on the
coefficients, but not on the strings.  The printed conclusion writes `K(ξ_I)` for the
complexity `C(x_I)` of the string tuples.  SUV Theorem 212, p. 327. -/
theorem holdsForEntropies_iff_holdsForComplexitiesCplx (f : LinearForm n) (D : Map)
    (hD : isOptimalConditional D) :
    HoldsForEntropies f ↔ HoldsForComplexitiesCplx f D := by
  constructor
  · exact holdsForComplexitiesCplx_of_holdsForEntropies f D hD
  · intro h
    exact holdsForEntropies_of_holdsForComplexitiesLen f D hD
      (holdsForComplexitiesLen_of_holdsForComplexitiesCplx f D hD h)

end Kolmogorov
