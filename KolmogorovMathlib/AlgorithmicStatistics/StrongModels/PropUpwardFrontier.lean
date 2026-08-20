import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalNoiseTransport

/-!
# The budget-scale witness purity route to `prop:upward`

**Superseded.**  `prop:upward` is now proved unconditionally in
`UpwardOrdinalNoiseBetaRegime.lean` (`prop_upward`), through the unconditional
`strongModelOrdinalNoiseTransport`.  The purity statement below is no longer a
remaining obligation of the section; it is kept as a documented alternative
route and is still never assumed outside the wrapper that consumes it.

`prop:upward` (`PropUpwardStatement U T`) is reduced to a single open question:
whether an arbitrary stochasticity witness for a string can be purified so its
code has conditional complexity bounded by `O(log B)`.

This module records the *composition* of the two, so that the entire remaining
distance to an unconditional `prop:upward` is exhibited as one explicit
hypothesis `hPurity`: the budget-scale witness purity statement.

Nothing here is assumed. `hPurity` is a faithful statement of the open frontier.
It is deliberately **not** the unconditional endpoint: the truth of `hPurity`
is not established, and we pose the question whether the frozen `O(ε + log l(x))`
radius is achievable over arbitrary witnesses of the model code, or whether the
endpoint should target the strong-model-specific ordinal consumer at a weakened radius.
-/

namespace Kolmogorov

/-- **The Budget-Scale Purity Statement.**
The frozen O(ε + log l(x)) radius requires that an arbitrary stochasticity witness for
the model code `z` can be purified: there must exist a stochasticity witness `P` whose
conditional complexity given `z` is bounded by `O(log B)`, where `B` is a budget on the
complexity of `z`. -/
def BudgetedWitnessPurityStatement (V U : Map) : Prop :=
  ∃ c : ℕ, ∀ (z : BitString) (B α β : ℕ), plainK V z ≤ (B : ENat) →
    IsStochastic U z α β →
    ∃ P : CodedFiniteDistribution, P.IsProbability ∧
      P.complexity U ≤ ((α + logSlack c B : ℕ) : ENat) ∧
      DeficiencyLe U P z (β + logSlack c B) ∧
      KP U P.code z ≤ (logSlack c B : ENat)

/-- `prop:upward` from the budget-scale purity statement.
This bridges `StrongModelOrdinalNoiseTransportStatement` by applying the purity
charge on the witness. -/
theorem strongModelOrdinalNoiseTransport_of_budgetedWitnessPurity
    (V U T : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (hPurity : BudgetedWitnessPurityStatement V U) :
    StrongModelOrdinalNoiseTransportStatement U T := by
  obtain ⟨cPure, hPure⟩ := hPurity
  obtain ⟨cCond, hCond⟩ := purified_witness_pair_condition_bound V U hV hU
  obtain ⟨cExt, hExt⟩ := pairUniformExtension_stochasticity_of_condition_bound U hU
  obtain ⟨cModel, hModel⟩ := plainK_strongModelCode_le V T hV hT.1
  obtain ⟨cWidth, hWidth⟩ := finiteSetLogCard_le_length_add_deficiency_log U hU
  obtain ⟨cOrdinal, hOrdinal⟩ :=
    strongModelOrdinalBits_plain_random_given_model V U hV hU
  have hslackAdd : ∀ a b k : ℕ, logSlack a k + logSlack b k = logSlack (a + b) k := by
    intro a b k; unfold logSlack; ring
  set c1 : ℕ := 2 * cPure + 2 * cCond + 2 * cExt + cOrdinal + 1 with hc1
  obtain ⟨C, hAbsorb⟩ := upward_ordinal_noise_radius_absorb c1 cOrdinal cModel cWidth
  refine ⟨C, ?_⟩
  intro x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch
  change IsStochastic U (strongModelOrdinalBitsPair A hA x)
      (alpha + (C * epsilon + logSlack C n))
      (beta + (C * epsilon + logSlack C n))
  set modelCode := (codedUniformOn A hA).code with hmodelCode
  set u := strongModelOrdinalBits A x with hu
  set m := u.length with hm
  set noiseEpsilon := cOrdinal * epsilon + logSlack cOrdinal n with hnoiseEpsilon
  set baseBudget := n + epsilon + logSlack cModel n with hbaseBudget
  have huLen : u.length = finiteSetLogCard A :=
    strongModelOrdinalBits_length A x hx
  have hModelBudget : plainK V modelCode ≤ (baseBudget : ENat) := by
    simpa [hmodelCode, hbaseBudget] using hModel x A hA n epsilon hxn hstrong
  have hWidthBound : finiteSetLogCard A ≤ n + epsilon + logSlack cWidth n :=
    hWidth A hA x n epsilon hxn hx hdef
  have hmBound : m ≤ n + epsilon + logSlack cWidth n := by
    rw [hm, huLen]; exact hWidthBound
  have hRandom :
      (u.length : ENat) ≤ condK V u modelCode + (noiseEpsilon : ENat) := by
    rw [huLen]
    simpa [hu, hmodelCode, hnoiseEpsilon] using
      hOrdinal A hA x n epsilon hxn hx hdef
  -- Purify the stochasticity witness of the model code.
  set s := logSlack cPure baseBudget with hs
  obtain ⟨P, hPprob, hPalpha, hPdef, hPcond⟩ :=
    hPure modelCode baseBudget alpha beta hModelBudget hstoch
  -- The purified witness satisfies the pair-condition bound.
  set delta := noiseEpsilon + s + logSlack cCond baseBudget + logSlack cCond m with hdelta
  have hCondBound :
      KP U modelCode P.code + (m : ENat) ≤
        KP U (pairCode modelCode u) (pairCode P.code (natCode m)) + (delta : ENat) := by
    have h := hCond modelCode u P baseBudget noiseEpsilon s hModelBudget hRandom hPcond
    rw [hdelta]
    calc
      KP U modelCode P.code + (m : ENat)
          ≤ KP U (pairCode modelCode u) (pairCode P.code (natCode m)) +
            ((noiseEpsilon + s + logSlack cCond baseBudget + logSlack cCond u.length : ℕ) :
              ENat) := by
            simpa [hm] using h
      _ = KP U (pairCode modelCode u) (pairCode P.code (natCode m)) +
            ((noiseEpsilon + s + logSlack cCond baseBudget + logSlack cCond m : ℕ) : ENat) := by
            rw [hm]
  have hPair :=
    hExt P modelCode u m (alpha + s) (beta + s) delta hm.symm hPprob hPalpha hPdef hCondBound
  -- Radius bookkeeping.
  have hAbs : c1 * noiseEpsilon + logSlack c1 baseBudget + logSlack c1 m
      ≤ C * epsilon + logSlack C n := hAbsorb n epsilon m hmBound
  have hBudgetSlack :
      s + s + logSlack cCond baseBudget + cExt ≤ logSlack c1 baseBudget := by
    have h1 : s + s + logSlack cCond baseBudget
        = logSlack (cPure + cPure + cCond) baseBudget := by
      rw [hs, hslackAdd, hslackAdd]
    calc
      s + s + logSlack cCond baseBudget + cExt
          = logSlack (cPure + cPure + cCond) baseBudget + cExt := by rw [h1]
        _ ≤ logSlack (cPure + cPure + cCond + cExt) baseBudget :=
            logSlack_add_const_le _ _ _
        _ ≤ logSlack c1 baseBudget := logSlack_mono_left (by omega) _
  have hWidthSlack : logSlack cCond m + logSlack cExt m ≤ logSlack c1 m := by
    rw [hslackAdd]
    exact logSlack_mono_left (by omega) _
  have hNoiseSlack : noiseEpsilon ≤ c1 * noiseEpsilon :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hR2 : s + delta + cExt ≤ C * epsilon + logSlack C n := by
    have : s + delta + cExt
        ≤ c1 * noiseEpsilon + logSlack c1 baseBudget + logSlack c1 m := by
      rw [hdelta]
      have hc : logSlack cCond m ≤ logSlack c1 m := by
        have := hWidthSlack; omega
      omega
    omega
  have hR1 : s + logSlack cExt m ≤ C * epsilon + logSlack C n := by
    have hb : s ≤ logSlack c1 baseBudget := by
      have := hBudgetSlack; omega
    have hw : logSlack cExt m ≤ logSlack c1 m := by
      have := hWidthSlack; omega
    omega
  have hFinal :
      IsStochastic U (pairCode modelCode u)
        (alpha + (C * epsilon + logSlack C n))
        (beta + (C * epsilon + logSlack C n)) := by
    refine isStochastic_mono ?_ ?_ hPair
    · have : s + logSlack cExt m ≤ C * epsilon + logSlack C n := hR1
      omega
    · have : s + delta + cExt ≤ C * epsilon + logSlack C n := hR2
      omega
  simpa [strongModelOrdinalBitsPair, hmodelCode, hu] using hFinal

/-- `prop_upward` reduced to the purity statement.
(Research interface, not a completion obligation.) -/
theorem propUpward_of_budgetedWitnessPurity
    (V U T : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (hPurity : BudgetedWitnessPurityStatement V U) :
    PropUpwardStatement U T :=
  propUpward_of_strongModelOrdinalNoiseTransport U T hU hT
    (strongModelOrdinalNoiseTransport_of_budgetedWitnessPurity V U T hV hU hT hPurity)

end Kolmogorov
