-- Calibration fixture for scripts/cut_quality.py: logSlack_sum_six_add_const_le.
-- Lines 41-55, 74-88, 106-108, 207-212 of KolmogorovMathlib/AlgorithmicStatistics/StrongModels/RemAddNoiseLowBranch.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

/-- Six log-slacks at the same budget and an additive constant combine into a single log-slack
whose constant is the sum. -/
private lemma logSlack_sum_six_add_const_le (c1 c2 c3 c4 c5 c6 cBridge : Nat) (N : Nat) :
    logSlack c1 N + logSlack c2 N + logSlack c3 N + logSlack c4 N +
      logSlack c5 N + logSlack c6 N + cBridge + 2 ≤
      logSlack (c1 + c2 + c3 + c4 + c5 + c6 + cBridge + 2) N := by
  have h1 : logSlack c1 N + logSlack c2 N + logSlack c3 N + logSlack c4 N +
      logSlack c5 N + logSlack c6 N =
      logSlack (c1 + c2 + c3 + c4 + c5 + c6) N := by
    simp only [logSlack_add_const]
  have h2 : logSlack (c1 + c2 + c3 + c4 + c5 + c6) N + (cBridge + 2) ≤
      logSlack (c1 + c2 + c3 + c4 + c5 + c6 + (cBridge + 2)) N :=
    logSlack_add_const_le _ _ _
  rw [h1]
  exact h2

-- ------------------------------------------------------------

/-- **Fibre projection of a pair model.**  An ordinary plain `(i, j)`-model of
`pairCode x y`, together with conditional `epsilon`-randomness of `y` given `x`,
yields an ordinary plain model of `x` of complexity `i + epsilon + O(log N)` and
log-size `j - |y| + O(log N)`, where `N` bounds `|x| + |y|`, `i` and `j`. -/
theorem inPlainDescriptionProfile_fst_of_pair_model
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon i j N : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      x.length + y.length ≤ N →
      i ≤ N →
      j ≤ N →
      InPlainDescriptionProfile V x
        (i + epsilon + logSlack c N) (j - y.length + logSlack c N) := by

-- ------------------------------------------------------------

  refine ⟨cSym + cPre2 + cRank2 + cDrop2 + cFib2 + cShift + cBridge + 2, ?_⟩
  intro x y epsilon i j N hprofile hrandom hlenN hiN hjN
  set c : Nat := cSym + cPre2 + cRank2 + cDrop2 + cFib2 + cShift + cBridge + 2

-- ------------------------------------------------------------

  set s := l - F
  have hchunk := hShift x (i1 - k' + SD + cBridge) (j1 + SD) s hplain
  have hShiftFold : logSlack cShift s ≤ logSlack cShift N := logSlack_mono_right cShift (by omega)
  have hslackSum : logSlack cSym N + logSlack cPre2 N + logSlack cRank2 N + logSlack cDrop2 N +
      logSlack cFib2 N + logSlack cShift N + cBridge + 2 ≤ logSlack c N :=
    logSlack_sum_six_add_const_le cSym cPre2 cRank2 cDrop2 cFib2 cShift cBridge N

end Kolmogorov
