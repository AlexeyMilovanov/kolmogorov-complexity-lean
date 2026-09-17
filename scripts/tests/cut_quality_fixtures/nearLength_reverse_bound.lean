-- Calibration fixture for scripts/cut_quality.py: nearLength_reverse_bound.
-- Lines 308-336, 352-363, 365-378, 441-445 of KolmogorovMathlib/CommonInformation/Interfaces.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

/-- Combined chain-rule bound on conditional complexity `krx` in terms of length/complexity
parameters. -/
private lemma nearLength_reverse_bound
    (cLen cSwap cUpperFold cLowerFold cLogs cConst cLinear k d kr kxr krx kPairRX kPairXR : Nat)
    (hcLogs : cLogs = cUpperFold + cLowerFold)
    (hcConst : cLen + cSwap + cUpperFold + cLowerFold ≤ cConst)
    (hcLinear : 2 + cUpperFold + cLowerFold ≤ cLinear)
    (hkxr : kxr ≤ d)
    (hkr : kr ≤ k + d + cLen)
    (hUpper : kPairRX ≤ kr + kxr +
      (logSlack cUpperFold (k + 1) + cUpperFold * d + cUpperFold))
    (hLower : k + krx ≤ kPairXR +
      (logSlack cLowerFold (k + 1) + cLowerFold * d + cLowerFold))
    (hSwap : kPairXR ≤ kPairRX + cSwap) :
    krx ≤ cLinear * d + logSlack cLogs (k + 1) + cConst := by
  generalize hL1 : logSlack cUpperFold (k + 1) = L1
  generalize hL2 : logSlack cLowerFold (k + 1) = L2
  have h1 : k + krx ≤ (k + d + cLen) + d +
      (L1 + cUpperFold * d + cUpperFold) + cSwap +
      (L2 + cLowerFold * d + cLowerFold) := by omega
  have hLog : L1 + L2 = logSlack cLogs (k + 1) := by
    subst hL1 hL2 hcLogs
    exact logSlack_add_const _ _ _
  have hCoeff : (2 + cUpperFold + cLowerFold) * d ≤ cLinear * d :=
    Nat.mul_le_mul_right d hcLinear
  calc
    krx ≤ (2 + cUpperFold + cLowerFold) * d + logSlack cLogs (k + 1) +
        (cLen + cSwap + cUpperFold + cLowerFold) := by linarith [h1, hLog]
    _ ≤ cLinear * d + logSlack cLogs (k + 1) + cConst := by linarith [hCoeff, hcConst]

-- ------------------------------------------------------------

/-- A string of about the right length from which `x` is cheaply decodable is plain equivalent to
`x` and itself incompressible. -/
theorem nearLength_decodable_is_equivalent_incompressible
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ x r k d,
      HasPlainComplexityValue V x k →
      NatCloseWithin r.length k d →
      condK V x r ≤ (d : ENat) →
      PlainEquivalentWithin V x r
          (commonInformationSlack c d (k + 1)) ∧
      PlainIncompressibleWithin V r
          (commonInformationSlack c d (k + 1)) := by

-- ------------------------------------------------------------

  obtain ⟨cLen, hLen⟩ := plainK_le_length V hV
  obtain ⟨cSwap, hSwap⟩ := pairPlainK_swap_le V hV
  obtain ⟨cUpper, hUpper⟩ := pairPlainK_chain_upper_values V hV
  obtain ⟨cLower, hLower⟩ := pairPlainK_chain_lower_values V hV
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le V hV
  let bUpper := 2 * cLen + cCrude
  obtain ⟨cUpperFold, hUpperFold⟩ := logSlack_linear_bound cUpper 3 bUpper
  let bLower := bUpper + cSwap
  obtain ⟨cLowerFold, hLowerFold⟩ := logSlack_linear_bound cLower 3 bLower
  let cLogs := cUpperFold + cLowerFold
  let cConst := cLen + cSwap + cRight + cUpperFold + cLowerFold
  let cLinear := 2 + cUpperFold + cLowerFold
  let C := cLogs + cConst + cLinear
  refine ⟨C, fun x r k d hx hrx hDecode => ?_⟩

-- ------------------------------------------------------------

  have hReverse :
      krx ≤ cLinear * d + logSlack cLogs (k + 1) + cConst :=
    nearLength_reverse_bound cLen cSwap cUpperFold cLowerFold cLogs cConst cLinear
      k d kr kxr krx kPairRX kPairXR rfl (by omega) (by omega) hkxrLe hkrVisible
      hPairUpperVisible hPairLowerVisible hPairSwap

end Kolmogorov
