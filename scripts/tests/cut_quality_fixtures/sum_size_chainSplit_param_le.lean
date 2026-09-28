-- Calibration fixture for scripts/cut_quality.py: sum_size_chainSplit_param_le.
-- Lines 602-615, 660-669, 707-708, 736-740 of KolmogorovMathlib/CommonInformation/ChainSample/Part01.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

/-- Bounding the sum of split histogram sizes in terms of the sample length size. -/
private theorem sum_size_chainSplit_param_le {k Q N : ℕ} (D : ChainDist k)
    (hQ : D.RationalAtoms Q) (hdiv : Q ∣ N) (j : Fin (2 * k + 2)) (cProj : ℕ) :
    2 * Nat.size 2 + 2 * Nat.size (2 ^ (2 * k + 1)) +
        2 * (∑ ab, Nat.size (chainHistogram D hQ N ((chainSplitEquiv k j).symm ab))) +
        2 * 2 ^ (2 * k + 1) + cProj ≤
      2 * 2 ^ (2 * k + 2) * Nat.size (N + 1) +
        (2 * Nat.size 2 + 2 * Nat.size (2 ^ (2 * k + 1)) + 2 * 2 ^ (2 * k + 1) + cProj) := by
  have h1 : 2 * (∑ ab, Nat.size (chainHistogram D hQ N ((chainSplitEquiv k j).symm ab))) ≤
      2 * 2 ^ (2 * k + 2) * Nat.size (N + 1) :=
    (Nat.mul_le_mul_left 2 (sum_size_chainSplit_le D hQ hdiv j)).trans
      (by rw [mul_assoc]; exact Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left _ (Nat.size_le_size (Nat.le_succ N))))
  omega

-- ------------------------------------------------------------

/-- Fixed-coordinate form of the lower profile: with the coordinate `j` fixed
in advance, maximality of the full chain sample forces the `j`-th projection to
retain its binary type-log, up to a logarithmic loss. -/
theorem chain_single_projection_plainK_lower_at
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) (j : Fin (2 * k + 2)) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
        (histogramTypeLog (fun b => chainHistogram1 D hQ N j b) : ENat) ≤
          plainK V (chainWordAt W j) + (logSlack C (N + 1) : ENat) := by

-- ------------------------------------------------------------

  set PARAM := 2 * Nat.size 2 + 2 * Nat.size (2 ^ (2 * k + 1)) +
      2 * (∑ ab, Nat.size (f ab)) + 2 * 2 ^ (2 * k + 1) + cProj with hPARAM

-- ------------------------------------------------------------

  have hsize_binom : Nat.size binom ≤ kx + C * S + C :=
    chain_sample_lower_bound_arith k cProj binom SP kW PARAM cOut cCond kx kyx kxy cRight
      cChain gamma C S
      (chain_sample_multinomial_split_size_le V D hQ j W kW hsample) hkyx_le hchain hkW_le
      (sum_size_chainSplit_param_le D hQ hdiv j cProj) hlogb hC

end Kolmogorov
