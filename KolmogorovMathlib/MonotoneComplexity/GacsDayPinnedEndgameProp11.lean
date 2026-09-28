import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedFamily
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayTestComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDaySubtreeEmbedding

/-!
# Day's Proposition 11 in the charged family interface

This module proves **Day 2011, Proposition 11** in the form the single-call
endgame (Stage E3′) needs: *if the amplified guaranteed root request exceeds
total mass one, the gray outcome of a charged gray family game spec is
impossible, so the spec's dichotomy collapses to the unserved outcome.*

The load-bearing observation is that the **charged** gray goal
`familyChargedGrayGoal` carries Day's two-sided request window
`alpha / 2 ≤ getFamilyReq c i [] ≤ alpha` at every root `i < n`
(`familyGrayChargeAtB`, third clause), which the *weak* goal
`familyGrayGoal` does not.  Day's outcome (ii)(a) reads
`2 ^ (-r) ≤ a(σ, t₁) < (5/4) · 2 ^ (-r)`; the SUV formalisation uses the
factor-`2` window instead of `5/4`.

Consequently, on the gray branch,

```
totalRootRequest n (cm T) ≥ n * alpha / 2          (`totalRootRequest_ge_of_charge`)
familyGrayMass ≥ kappa * totalRootRequest n (cm T) ≥ kappa * (n * alpha / 2)
familyGrayMass ≤ 1                                  (Kraft, `familyGrayMass_le_one`)
```

so the hypothesis `1 < kappa * (n * alpha / 2)` refutes the gray branch.

Under the *weak* goal the guaranteed mass is only `n * beta = (3/4) * n * alpha`,
which the outer budget `n * alpha ≤ 1 / d` pins below `3/4 < 1`; that is exactly
why the charge is load-bearing at the endgame and not merely an internal device
of the induction.

## Main results

* `totalRootRequest_ge_of_charge` — the window forces the total root request.
* `not_familyChargedGrayGoal_of_one_lt_window` — Proposition 11 proper.
* `familyClientWinsUnservedPositive_of_charged_window` — Proposition 11 against
  a `ChargedGrayFamilyGameSpec`.
* `familyClientWinsUnserved_of_charged_window` — the frozen-interface corollary.
-/

namespace Kolmogorov

/-- **Day 2011, outcome (ii)(a).**  A charge certificate pins every root
request into the window `[alpha / 2, alpha]`, so the total root request is at
least `n * (alpha / 2)`. -/
theorem totalRootRequest_ge_of_charge
    {eta kappa alpha beta : ℚ} {epsDepth deltaDepth n : ℕ}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (h : familyGrayChargeAtB eta kappa alpha beta epsDepth deltaDepth n A c s G = true) :
    (n : ℚ) * (alpha / 2) ≤ totalRootRequest n c := by
  classical
  have hle : ∀ i : Fin n, alpha / 2 ≤ getFamilyReq c i.val [] :=
    fun i => (familyGrayChargeAtB.root h i.isLt).1
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun _ : Fin n => alpha / 2) (g := fun i : Fin n => getFamilyReq c i.val [])
    (fun i _ => hle i)
  simpa [totalRootRequest, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum

/-- **Day 2011, Proposition 11.**  If the amplification applied to the
*guaranteed* root request `n * (alpha / 2)` already exceeds one, the charged
gray goal would need more mass than the whole space has, so it is impossible. -/
theorem not_familyChargedGrayGoal_of_one_lt_window
    {eta kappa alpha beta : ℚ} {epsDepth deltaDepth n : ℕ}
    (hed : epsDepth ≤ deltaDepth) (hk : 0 ≤ kappa)
    {A : Allocation} {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (hone : 1 < kappa * ((n : ℚ) * (alpha / 2))) :
    ¬ familyChargedGrayGoal eta kappa alpha beta epsDepth deltaDepth n A cm sm := by
  rintro ⟨T, hT⟩
  obtain ⟨G, -, hG⟩ := familyChargedGrayGoalAtB.exists_charge hT
  have hwin := totalRootRequest_ge_of_charge hG
  have hweak := familyChargedGrayGoalAtB.to_familyGrayGoalAtB hT
  have hweak2 : familyGrayGoalAtB kappa beta epsDepth deltaDepth n A (cm T)
      (familyAllocatedList n T sm) = true := hweak
  obtain ⟨-, hmass, -⟩ := (familyGrayGoalAtB_eq_true_iff hed n T A cm sm).mp hweak2
  have hle1 := familyGrayMass_le_one epsDepth deltaDepth n T A sm
  have hstep : kappa * ((n : ℚ) * (alpha / 2)) ≤ kappa * totalRootRequest n (cm T) :=
    mul_le_mul_of_nonneg_left hwin hk
  linarith

/-- **Day 2011, Proposition 11, against the pinned charged spec.**  With the
gray branch refuted, `ChargedGrayFamilyGameSpec.wins_charged` delivers the
*positive* unserved outcome. -/
theorem familyClientWinsUnservedPositive_of_charged_window
    {eta kappa alpha beta : ℚ} {epsDepth deltaDepth h b n : ℕ} {A : Allocation}
    {sigma : ClientFamilyStrategy}
    (H : ChargedGrayFamilyGameSpec eta kappa alpha beta epsDepth deltaDepth h b n A sigma)
    (hone : 1 < kappa * ((n : ℚ) * (alpha / 2)))
    (sm : ℕ → FamilyServerMove) (hsm : familyServerPlayLegal n b A sm) :
    familyClientWinsUnservedPositive n h b (playClientFamily A n sigma sm) sm := by
  rcases H.wins_charged sm hsm with hw | hg
  · exact hw
  · exact absurd hg (not_familyChargedGrayGoal_of_one_lt_window H.weak.scales
      (le_trans zero_le_one H.weak.kappa_ge_one) hone)

/-- The frozen-interface corollary of Proposition 11: the unserved win in the
shape `isUniformWinningStrategy_of_familyController` consumes. -/
theorem familyClientWinsUnserved_of_charged_window
    {eta kappa alpha beta : ℚ} {epsDepth deltaDepth h b n : ℕ} {A : Allocation}
    {sigma : ClientFamilyStrategy}
    (H : ChargedGrayFamilyGameSpec eta kappa alpha beta epsDepth deltaDepth h b n A sigma)
    (hone : 1 < kappa * ((n : ℚ) * (alpha / 2)))
    (sm : ℕ → FamilyServerMove) (hsm : familyServerPlayLegal n b A sm) :
    familyClientWinsUnserved n h b (playClientFamily A n sigma sm) sm :=
  familyClientWinsUnserved_of_positive n h b _ _
    (familyClientWinsUnservedPositive_of_charged_window H hone sm hsm)

end Kolmogorov
