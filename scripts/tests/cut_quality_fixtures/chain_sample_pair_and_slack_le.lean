-- Calibration fixture for scripts/cut_quality.py: chain_sample_pair_and_slack_le.
-- Lines 617-638, 660-669, 682-682, 732-735 of KolmogorovMathlib/CommonInformation/ChainSample/Part01.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

/-- Bounding pair complexity and its logarithmic slack linearly in sample length. -/
private theorem chain_sample_pair_and_slack_le (k N cCode cPair cChain gamma kW kxy : ℕ)
    (hgamma : gamma = (2 * k + 2) + cCode + cCode + cPair + 1)
    (hkW_up : kW ≤ (2 * k + 2) * N + cCode * Nat.size (N + 1) + cCode)
    (hkxy_le : kxy ≤ kW + cPair) :
    kxy + 1 ≤ gamma * (N + 1) ∧
      logSlack cChain (kxy + 1) ≤
        cChain * (Nat.size gamma + Nat.size (N + 1)) + cChain := by
  have hSN : Nat.size (N + 1) ≤ N + 1 := size_le_self (N + 1)
  have hcc : cCode * Nat.size (N + 1) ≤ cCode * (N + 1) := Nat.mul_le_mul_left _ hSN
  have hexp : gamma * (N + 1) =
      (2 * k + 2) * (N + 1) + cCode * (N + 1) + cCode * (N + 1) + cPair * (N + 1) + (N + 1) := by
    rw [hgamma]; ring
  have h1 : (2 * k + 2) * N ≤ (2 * k + 2) * (N + 1) := Nat.mul_le_mul_left _ (Nat.le_succ N)
  have h2 : cCode ≤ cCode * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : cPair ≤ cPair * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hkxy1 : kxy + 1 ≤ gamma * (N + 1) := by omega
  refine ⟨hkxy1, ?_⟩
  unfold logSlack
  rw [Nat.size_eq_bits_len]
  have := Nat.mul_le_mul_left cChain ((Nat.size_le_size hkxy1).trans (size_mul_le _ _))
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

  set gamma := (2 * k + 2) + cCode + cCode + cPair + 1 with hgamma

-- ------------------------------------------------------------

  set S := Nat.size (N + 1) with hS
  set binom := Nat.multinomial univ (fun b : Bool => chainHistogram1 D hQ N j b) with hbinom
  have ⟨hkxy1, hlogb⟩ :=
    chain_sample_pair_and_slack_le k N cCode cPair cChain gamma kW kxy hgamma hkW_up hkxy_le

end Kolmogorov
