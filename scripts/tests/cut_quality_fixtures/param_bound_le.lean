-- Calibration fixture for scripts/cut_quality.py: param_bound_le.
-- Lines 157-168, 225-242, 287-290, 355-357 of KolmogorovMathlib/CommonInformation/MaximalSampleFibre.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

/-- Upper bound on the parameter sum in terms of `2 * n * S`. -/
private theorem param_bound_le (m n cProj sum_sizes N S : ℕ)
    (hsum_sizes : sum_sizes ≤ n * Nat.size N)
    (hsizeN : Nat.size N ≤ S) :
    2 * Nat.size m + 2 * Nat.size n + 2 * sum_sizes + m * n + cProj ≤
      2 * n * S + (2 * Nat.size m + 2 * Nat.size n + m * n + cProj) := by
  have h1' : 2 * sum_sizes ≤ 2 * n * S := by
    calc 2 * sum_sizes ≤ 2 * (n * Nat.size N) := by omega
      _ ≤ 2 * n * S := by
          rw [mul_assoc]
          exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left n hsizeN)
  omega

-- ------------------------------------------------------------

theorem maximalSample_projection_typeLog_le
    (V : Map) (hV : isOptimalConditional V)
    {A : Type*} [Fintype A] [DecidableEq A] [FiniteLetterCode A]
    (m : ℕ) (pi : A → Fin m) (proj : List A → BitString) (c₁ c₂ c₃ : ℕ)
    (h₁ : ∀ (W : List A) (z : BitString),
      condK V z (proj W) ≤ condK V z (finiteWordCode (W.map pi)) + (c₁ : ENat))
    (h₂ : ∀ W : List A,
      plainK V (pairCode (proj W) (finiteWordCode W)) ≤
        plainK V (finiteWordCode W) + (c₂ : ENat))
    :
    ∃ C : ℕ, ∀ (N : ℕ) (g : A → ℕ) (W : List A) (kW : ℕ),
      (∀ v, W.count v = g v) → (∑ v, g v = N) →
      HasPlainComplexityValue V (finiteWordCode W) kW →
      (histogramTypeLog g : ENat) ≤ (kW : ENat) + 1 →
      kW ≤ c₃ * N + c₃ * Nat.size (N + 1) + c₃ →
      (histogramTypeLog
          (fun a : Fin m => ∑ v ∈ Finset.univ.filter (fun v => pi v = a), g v) : ENat) ≤
        plainK V (proj W) + (logSlack C (N + 1) : ENat) := by

-- ------------------------------------------------------------

  set SP := Nat.size (∏ a, Nat.multinomial univ (fun b => f (a, b))) with hSP
  set PARAM := 2 * Nat.size m + 2 * Nat.size n +
    2 * (∑ ab, Nat.size (f ab)) + m * n + cProj with hPARAM
  set S := Nat.size (N + 1) with hS

-- ------------------------------------------------------------

  have hsizeN : Nat.size N ≤ S := Nat.size_le_size (Nat.le_succ N)
  have hPARAMb : PARAM ≤ 2 * n * S + (2 * Nat.size m + 2 * Nat.size n + m * n + cProj) :=
    param_bound_le m n cProj (∑ ab, Nat.size (f ab)) N S hsumsize hsizeN

end Kolmogorov
