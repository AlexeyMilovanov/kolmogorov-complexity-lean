-- Calibration fixture for scripts/cut_quality.py: slack_param_bound_le_C_mul_add.
-- Lines 191-207, 225-242, 256-261, 358-364 of KolmogorovMathlib/CommonInformation/MaximalSampleFibre.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

/-- Main constant combination inequality for the logSlack bound. -/
private theorem slack_param_bound_le_C_mul_add
    (m n cChain cProj cOut c₁ cRight gamma C S : ℕ)
    (hC : C = 2 * n + cChain +
      (2 * Nat.size m + 2 * Nat.size n + m * n + cProj + cOut + c₁ + cRight + 2 +
        cChain * Nat.size gamma + cChain)) :
    2 * n * S + (2 * Nat.size m + 2 * Nat.size n + m * n + cProj) +
      cOut + c₁ + (cChain * (Nat.size gamma + S) + cChain) + cRight + 2 ≤ C * S + C := by
  have hA : (2 * n + cChain) * S ≤ C * S :=
    Nat.mul_le_mul_right _ (by rw [hC]; omega)
  have hB : 2 * Nat.size m + 2 * Nat.size n + m * n + cProj + cOut + c₁ +
      cRight + 2 + cChain * Nat.size gamma + cChain ≤ C := by
    rw [hC]; omega
  have hdist : (2 * n + cChain) * S = 2 * n * S + cChain * S := by ring
  have hdist2 : cChain * (Nat.size gamma + S) =
      cChain * Nat.size gamma + cChain * S := by ring
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

  set gamma := 3 * c₃ + c₂ + 1 with hgamma
  set C := 2 * n + cChain +
    (2 * Nat.size m + 2 * Nat.size n + m * n + cProj + cOut + c₁ + cRight + 2 +
      cChain * Nat.size gamma + cChain) with hC
  refine ⟨C, ?_⟩
  intro N g W kW hcounts hsumg hvalue hmaximal hkW_up'

-- ------------------------------------------------------------

  have hgoalNat : Nat.size (Nat.multinomial univ hist) ≤ kx + logSlack C (N + 1) := by
    have hlog : logSlack C (N + 1) = C * S + C := by
      unfold logSlack
      rw [hS, Nat.size_eq_bits_len]
    have hCbig : 2 * n * S + (2 * Nat.size m + 2 * Nat.size n + m * n + cProj) +
        cOut + c₁ + (cChain * (Nat.size gamma + S) + cChain) + cRight + 2 ≤ C * S + C :=
      slack_param_bound_le_C_mul_add m n cChain cProj cOut c₁ cRight gamma C S hC

end Kolmogorov
