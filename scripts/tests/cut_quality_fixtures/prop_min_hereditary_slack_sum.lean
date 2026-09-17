-- Calibration fixture for scripts/cut_quality.py: prop_min_hereditary_slack_sum.
-- Lines 30-55, 234-237, 255-257, 310-313 of KolmogorovMathlib/AlgorithmicStatistics/StrongModels/PropMinHereditary.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

/-- Combination of logSlack bounds into the unified kappa slack bound. -/
private theorem prop_min_hereditary_slack_sum
    {cPrefix cBound cBetter cBetterFold cPrefixAbsorb cKappa : ℕ}
    {n delta m : ℕ}
    (hPrefixAbsorb :
      logSlack cPrefix (n + delta + logSlack cBound n) ≤ logSlack cPrefixAbsorb n)
    (hBetterFold : logSlack cBetter (n + logSlack cBetter n) ≤ logSlack cBetterFold n)
    (hcKappa : cPrefixAbsorb + cBetter + cBetterFold ≤ cKappa)
    (hm : m ≤ n + logSlack cBetter n) :
    logSlack cPrefix (n + delta + logSlack cBound n) +
        logSlack cBetter n + logSlack cBetter m ≤
      logSlack cKappa n := by
  have hPrefixSlack :
      logSlack cPrefix (n + delta + logSlack cBound n) ≤ logSlack cPrefixAbsorb n :=
    hPrefixAbsorb
  have hBetterSlack : logSlack cBetter m ≤ logSlack cBetterFold n :=
    (logSlack_mono_right cBetter hm).trans hBetterFold
  calc
    logSlack cPrefix (n + delta + logSlack cBound n) +
        logSlack cBetter n + logSlack cBetter m
      ≤ logSlack cPrefixAbsorb n + logSlack cBetter n + logSlack cBetterFold n := by omega
    _ = logSlack (cPrefixAbsorb + cBetter + cBetterFold) n := by
      unfold logSlack
      ring
    _ ≤ logSlack cKappa n :=
      logSlack_mono_left hcKappa n

-- ------------------------------------------------------------

theorem prop_min_hereditary
    (V : Map) (hV : isOptimalConditional V) :
    PropMinHereditaryStatement V := by
  unfold PropMinHereditaryStatement

-- ------------------------------------------------------------

  obtain ⟨cPrefixAbsorb, hPrefixAbsorb⟩ :=
    logSlack_add_delta_absorb cPrefix cBound
  let cModel := cBetter + cBetterFold + cBound

-- ------------------------------------------------------------

    have hcKappaBound : cPrefixAbsorb + cBetter + cBetterFold ≤ cKappa := by
      dsimp [cKappa]; omega
    have hSlackSum := prop_min_hereditary_slack_sum (hPrefixAbsorb n delta hDelta)
      (hBetterFold n) hcKappaBound hmVisible

end Kolmogorov
