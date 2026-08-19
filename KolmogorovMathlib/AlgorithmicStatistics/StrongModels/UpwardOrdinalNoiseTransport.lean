import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedTransportBetaLe

/-!
# Narrowing the `prop:upward` transport obligation to its consumer instance

`prop:upward` (VS40 Proposition `prop:upward`) is proved conditionally in
`UpwardConditional.lean` (`propUpward_of_budgetedRandomNoiseTransport`) from the
*general* budgeted random-noise transport interface
`BudgetedRandomNoiseTransportStatement V U`, which quantifies over **all**
strings `x`, `y` and budgets.  That interface is strictly stronger than what the
endpoint consumes: `propUpward_of_budgetedRandomNoiseTransport` only ever applies
it at the single instance

* `x := (codedUniformOn A hA).code`  (a strong-model code), and
* `y := strongModelOrdinalBits A x`  (the ordinal index of `x` in `A`),

with `plainK V x ≤ baseBudget` and `l(y) = finiteSetLogCard A`.

This module records that consumer instance as a *narrowed* statement
`StrongModelOrdinalNoiseTransportStatement U T`, whose radius is already in the
final `c * ε + logSlack c n` form (the base-budget and index-width slacks are
absorbed here rather than in the assembly).  Three facts are proved:

* `strongModelOrdinalNoiseTransport_of_budgetedRandomNoiseTransport` — the
  narrowed statement follows from the general interface, certifying that the
  narrowed one is **not stronger** (no new obligation is smuggled in);
* `strongModelOrdinalNoiseTransport_of_beta_le` — the narrowed transport is
  unconditional in the already-discharged regime where `beta` is at most the
  canonical model-code budget;
* `propUpward_of_strongModelOrdinalNoiseTransport` — the narrowed statement is
  already enough to conclude `PropUpwardStatement U T`, reusing the proved
  total-equivalence transport, ordinal randomness, and projection machinery.

None of these theorems manufactures an unconditional `prop_upward`: the narrowed
statement is still an undischarged hypothesis.  Its purpose is to isolate the
exact residual obligation so later iterations can discharge it regime by regime.
-/

namespace Kolmogorov

/-- The consumer instance of the budgeted random-noise transport actually used
by `prop:upward`.  Quantifies over exactly the endpoint data `x A hA n ε α β`:
from a strong set model `A` for `x` with low deficiency and a stochasticity
witness for the model code, the pair `(code, ordinal)` is stochastic up to the
uniform radius `c * ε + logSlack c n`.

The parameter `V` is deliberately absent: the conclusion only mentions `U`, and
the base string is the canonical strong-model code, so no auxiliary optimal plain
machine appears.  This is the narrowed cousin of
`BudgetedRandomNoiseTransportStatement`, exposed at the endpoint's radius scale. -/
def StrongModelOrdinalNoiseTransportStatement (U T : Map) : Prop :=
  ∃ c : ℕ, ∀ x A (hA : A.Nonempty) n ε α β,
    x.length = n →
    x ∈ A →
    IsStrongSetModel T x A hA ε →
    DeficiencyLe U (codedUniformOn A hA) x ε →
    IsStochastic U (codedUniformOn A hA).code α β →
    let r := c * ε + logSlack c n
    IsStochastic U (strongModelOrdinalBitsPair A hA x) (α + r) (β + r)

/-- Radius bookkeeping for the narrowing step: the general transport's
`α`-independent radius `cNoise·noiseEpsilon + logSlack cNoise baseBudget +
logSlack cNoise l(u)` collapses into `C · ε + logSlack C n` once the base budget
is `n + ε + logSlack cModel n`, the noise budget is `cOrdinal·ε + logSlack
cOrdinal n`, and `l(u) ≤ n + ε + logSlack cWidth n`.  This is exactly the noise
sub-term of the already-proved `upward_noise_equivalence_radius_absorb`, so it is
derived from that lemma (with the equivalence/projection constants set to `0`). -/
theorem upward_ordinal_noise_radius_absorb (c1 c2 cModel cWidth : Nat) :
    ∃ C : Nat, ∀ n epsilon l_u,
      l_u ≤ n + epsilon + logSlack cWidth n →
      c1 * (c2 * epsilon + logSlack c2 n) +
        logSlack c1 (n + epsilon + logSlack cModel n) + logSlack c1 l_u
        ≤ C * epsilon + logSlack C n := by
  obtain ⟨C, hC⟩ :=
    upward_noise_equivalence_radius_absorb 0 0 c2 cModel cWidth c1 0
  refine ⟨C, fun n epsilon l_u hlu => ?_⟩
  have h := hC n epsilon l_u hlu
  set A := c1 * (c2 * epsilon + logSlack c2 n)
  set B := logSlack c1 (n + epsilon + logSlack cModel n)
  set D := logSlack c1 l_u
  -- `h : 2 * (epsilon + 0) + 0 + (A + B + D + 0) ≤ C * epsilon + logSlack C n`
  omega

/-- The consumer-shaped transport is unconditional in the discharged
`beta ≤ baseBudget` regime.  The first returned constant is the canonical
model-code budget constant; the second is the final source-scale radius.

This is a proper partial discharge of `StrongModelOrdinalNoiseTransportStatement`:
the remaining case has `beta` strictly above the displayed budget. -/
theorem strongModelOrdinalNoiseTransport_of_beta_le
    (V U T : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ∃ cBudget c : Nat, ∀ x A (hA : A.Nonempty) n epsilon alpha beta,
      x.length = n →
      x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      DeficiencyLe U (codedUniformOn A hA) x epsilon →
      beta ≤ n + epsilon + logSlack cBudget n →
      IsStochastic U (codedUniformOn A hA).code alpha beta →
      IsStochastic U (strongModelOrdinalBitsPair A hA x)
        (alpha + (c * epsilon + logSlack c n))
        (beta + (c * epsilon + logSlack c n)) := by
  obtain ⟨cNoise, hNoise⟩ :=
    budgetedRandomNoiseTransport_of_beta_le V U hV hU
  obtain ⟨cBudget, hBudget⟩ :=
    plainK_strongModelCode_le V T hV hT.1
  obtain ⟨cWidth, hWidth⟩ :=
    finiteSetLogCard_le_length_add_deficiency_log U hU
  obtain ⟨cOrdinal, hOrdinal⟩ :=
    strongModelOrdinalBits_plain_random_given_model V U hV hU
  obtain ⟨C, hAbsorb⟩ :=
    upward_ordinal_noise_radius_absorb cNoise cOrdinal cBudget cWidth
  refine ⟨cBudget, C, ?_⟩
  intro x A hA n epsilon alpha beta hxn hx hstrong hdef hbeta hstoch
  let modelCode := (codedUniformOn A hA).code
  let u := strongModelOrdinalBits A x
  let noiseEpsilon := cOrdinal * epsilon + logSlack cOrdinal n
  let baseBudget := n + epsilon + logSlack cBudget n
  have huLen : u.length = finiteSetLogCard A :=
    strongModelOrdinalBits_length A x hx
  have hModelBudget : plainK V modelCode ≤ (baseBudget : ENat) := by
    simpa [modelCode, baseBudget] using
      hBudget x A hA n epsilon hxn hstrong
  have hWidthBound :
      finiteSetLogCard A ≤ n + epsilon + logSlack cWidth n :=
    hWidth A hA x n epsilon hxn hx hdef
  have hRandom :
      (u.length : ENat) ≤ condK V u modelCode + (noiseEpsilon : ENat) := by
    simpa [u, modelCode, noiseEpsilon, huLen] using
      hOrdinal A hA x n epsilon hxn hx hdef
  have hForward := hNoise modelCode u baseBudget noiseEpsilon alpha beta
    hModelBudget hRandom (by simpa [baseBudget] using hbeta) hstoch
  have hRawLe :
      cNoise * noiseEpsilon + logSlack cNoise baseBudget +
          logSlack cNoise u.length
        ≤ C * epsilon + logSlack C n :=
    hAbsorb n epsilon u.length (by simpa [huLen] using hWidthBound)
  have hForward' :
      IsStochastic U (pairCode modelCode u)
        (alpha + (C * epsilon + logSlack C n))
        (beta + (C * epsilon + logSlack C n)) :=
    isStochastic_mono (Nat.add_le_add_left hRawLe alpha)
      (Nat.add_le_add_left hRawLe beta) hForward
  simpa [strongModelOrdinalBitsPair, modelCode, u] using hForward'

/-- The narrowed statement is weaker than the general budgeted transport: any
witness of `BudgetedRandomNoiseTransportStatement V U` yields a witness of
`StrongModelOrdinalNoiseTransportStatement U T`.  This certifies that the
narrowing introduces no new mathematical content — it only fixes the instance and
absorbs the radius. -/
theorem strongModelOrdinalNoiseTransport_of_budgetedRandomNoiseTransport
    (V U T : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (hNoise : BudgetedRandomNoiseTransportStatement V U) :
    StrongModelOrdinalNoiseTransportStatement U T := by
  obtain ⟨cNoise, hNoise⟩ := hNoise
  obtain ⟨cModel, hModel⟩ := plainK_strongModelCode_le V T hV hT.1
  obtain ⟨cWidth, hWidth⟩ := finiteSetLogCard_le_length_add_deficiency_log U hU
  obtain ⟨cOrdinal, hOrdinal⟩ :=
    strongModelOrdinalBits_plain_random_given_model V U hV hU
  obtain ⟨C, hAbsorb⟩ :=
    upward_ordinal_noise_radius_absorb cNoise cOrdinal cModel cWidth
  refine ⟨C, ?_⟩
  intro x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch
  let modelCode := (codedUniformOn A hA).code
  let u := strongModelOrdinalBits A x
  let noiseEpsilon := cOrdinal * epsilon + logSlack cOrdinal n
  let baseBudget := n + epsilon + logSlack cModel n
  have huLen : u.length = finiteSetLogCard A :=
    strongModelOrdinalBits_length A x hx
  have hModelBudget : plainK V modelCode ≤ (baseBudget : ENat) := by
    simpa [modelCode, baseBudget] using hModel x A hA n epsilon hxn hstrong
  have hWidthBound :
      finiteSetLogCard A ≤ n + epsilon + logSlack cWidth n :=
    hWidth A hA x n epsilon hxn hx hdef
  have hRandom :
      (u.length : ENat) ≤ condK V u modelCode + (noiseEpsilon : ENat) := by
    simpa [u, modelCode, noiseEpsilon, huLen] using
      hOrdinal A hA x n epsilon hxn hx hdef
  have hForward := hNoise modelCode u baseBudget noiseEpsilon alpha beta
    hModelBudget hRandom hstoch
  -- `hForward : IsStochastic U (pairCode modelCode u)
  --    (alpha + rawNoise) (beta + rawNoise)` with the base-budget radius.
  have hulen_bound : u.length ≤ n + epsilon + logSlack cWidth n := by
    rw [huLen]; exact hWidthBound
  have hrawLe :
      cNoise * noiseEpsilon + logSlack cNoise baseBudget + logSlack cNoise u.length
        ≤ C * epsilon + logSlack C n :=
    hAbsorb n epsilon u.length hulen_bound
  have hForward' :
      IsStochastic U (pairCode modelCode u)
        (alpha + (C * epsilon + logSlack C n))
        (beta + (C * epsilon + logSlack C n)) :=
    isStochastic_mono (Nat.add_le_add_left hrawLe alpha)
      (Nat.add_le_add_left hrawLe beta) hForward
  change IsStochastic U (strongModelOrdinalBitsPair A hA x)
      (alpha + (C * epsilon + logSlack C n))
      (beta + (C * epsilon + logSlack C n))
  simpa [strongModelOrdinalBitsPair, modelCode, u] using hForward'

/-- Final radius absorption for the assembly: the equivalence radius
`2·(ε + cEquiv) + cTransport`, the (already-uniform) forward noise radius
`cNoise·ε + logSlack cNoise n`, and the projection constant `cProj` combine into
a single `C · ε + logSlack C n`. -/
theorem upward_ordinal_final_radius_absorb
    (cEquiv cTransport cNoise cProj : Nat) :
    ∃ C : Nat, ∀ n epsilon,
      2 * (epsilon + cEquiv) + cTransport +
          (cNoise * epsilon + logSlack cNoise n + cProj)
        ≤ C * epsilon + logSlack C n := by
  let D := 2 * cEquiv + cTransport + cProj
  let C := cNoise + 2 + D
  refine ⟨C, fun n epsilon => ?_⟩
  have hCoeff : (2 + cNoise) * epsilon ≤ C * epsilon := by
    apply Nat.mul_le_mul_right
    dsimp [C]; omega
  have hLog : logSlack cNoise n + D ≤ logSlack C n := by
    dsimp [C, D]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  calc
    2 * (epsilon + cEquiv) + cTransport +
          (cNoise * epsilon + logSlack cNoise n + cProj)
        = (2 + cNoise) * epsilon + (logSlack cNoise n + D) := by
          dsimp [D]; ring
    _ ≤ C * epsilon + logSlack C n := Nat.add_le_add hCoeff hLog

/-- The narrowed transport statement already discharges `prop:upward`.

The proof reuses the body of `propUpward_of_budgetedRandomNoiseTransport`, but
the forward noise shift now comes directly from the narrowed hypothesis (already
at radius `cNoise·ε + logSlack cNoise n`), the backward shift from the proved
first-coordinate projection `isStochastic_fst_of_pair`, and the equivalence side
from `strong_model_equivalent_fixed_ordinal_pair` +
`totalEquivalentWithin_stochasticityProfiles`.  No auxiliary optimal plain
machine `V` is needed. -/
theorem propUpward_of_strongModelOrdinalNoiseTransport
    (U T : Map)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (hNoise : StrongModelOrdinalNoiseTransportStatement U T) :
    PropUpwardStatement U T := by
  obtain ⟨cNoise, hNoise⟩ := hNoise
  obtain ⟨cEquiv, hEquiv⟩ :=
    strong_model_equivalent_fixed_ordinal_pair T hT
  obtain ⟨cTransport, hTransport⟩ :=
    totalEquivalentWithin_stochasticityProfiles U T hU hT.1
  obtain ⟨cProj, hProj⟩ := isStochastic_fst_of_pair U hU
  obtain ⟨C, hAbsorb⟩ :=
    upward_ordinal_final_radius_absorb cEquiv cTransport cNoise cProj
  refine ⟨C, ?_⟩
  intro x A hA n epsilon hxn hx hstrong hdef
  let modelCode := (codedUniformOn A hA).code
  let u := strongModelOrdinalBits A x
  let noiseRadiusFwd := cNoise * epsilon + logSlack cNoise n
  let noiseRadius := noiseRadiusFwd + cProj
  let equivRadius := 2 * (epsilon + cEquiv) + cTransport
  have hNoiseProfiles :
      ProfileSetsWithinNeighborhood
        (stochasticityProfileSet U modelCode)
        (stochasticityProfileSet U (pairCode modelCode u))
        noiseRadius := by
    apply stochasticityProfileSet_neighborhood_of_uniform_shifts U
      modelCode (pairCode modelCode u) noiseRadius
    · intro alpha beta hstoch
      have hForward :=
        hNoise x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch
      have hForward' :
          IsStochastic U (pairCode modelCode u)
            (alpha + noiseRadiusFwd) (beta + noiseRadiusFwd) := by
        simpa [strongModelOrdinalBitsPair, modelCode, u, noiseRadiusFwd]
          using hForward
      exact isStochastic_mono (by simp [noiseRadius])
        (by simp [noiseRadius]) hForward'
    · intro alpha beta hstoch
      have hProjected := hProj modelCode u alpha beta hstoch
      exact isStochastic_mono (by simp [noiseRadius])
        (by simp [noiseRadius]) hProjected
  have hEquivProfiles :
      ProfileSetsWithinNeighborhood
        (stochasticityProfileSet U x)
        (stochasticityProfileSet U (pairCode modelCode u))
        equivRadius := by
    have hequiv := hEquiv x A hA epsilon hx hstrong
    have hprofiles := hTransport x (strongModelOrdinalBitsPair A hA x)
      (epsilon + cEquiv) hequiv
    simpa [equivRadius, strongModelOrdinalBitsPair, modelCode, u] using hprofiles
  have hCombined :
      ProfileSetsWithinNeighborhood
        (stochasticityProfileSet U x)
        (stochasticityProfileSet U modelCode)
        (equivRadius + noiseRadius) :=
    hEquivProfiles.trans hNoiseProfiles.symm
  have hFinalRadius :
      equivRadius + noiseRadius ≤ C * epsilon + logSlack C n := by
    simpa [equivRadius, noiseRadius, noiseRadiusFwd] using hAbsorb n epsilon
  simpa [modelCode] using hCombined.mono hFinalRadius

end Kolmogorov
