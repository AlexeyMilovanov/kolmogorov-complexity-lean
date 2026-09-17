import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame

/-!
# The measure barrier for exact-root family strategies

The source-faithful family invariant does not require root requests to equal
`alpha`: after the final adjustment of SUV p. 143, only the interval recorded
by `familyGrayGoal` is needed. Some explicit low stages happen to keep every
root request equal to `alpha`. This file isolates that stronger property and
the resulting measure barrier; it is deliberately not part of
`GrayFamilyGameSpec` and cannot be used as the general induction step.
-/

namespace Kolmogorov

/-- The gray mass of a family play is at most the mass of the whole space. -/
theorem familyGrayMass_le_one (epsDepth deltaDepth n T : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) :
    familyGrayMass epsDepth deltaDepth n T A sm ≤ 1 := by
  have hsub : newGrayCells epsDepth deltaDepth (familyAllocated n T sm) A.toFinset
      ⊆ stringsOfLength deltaDepth := by
    intro p hp
    exact (mem_stringsOfLength deltaDepth p).mpr (mem_newGrayCells_iff.mp hp).1
  have hcard : (newGrayCells epsDepth deltaDepth (familyAllocated n T sm) A.toFinset).card
      ≤ 2 ^ deltaDepth := by
    calc
      (newGrayCells epsDepth deltaDepth (familyAllocated n T sm) A.toFinset).card
          ≤ (stringsOfLength deltaDepth).card := Finset.card_le_card hsub
      _ = 2 ^ deltaDepth := card_stringsOfLength deltaDepth
  have hq : ((newGrayCells epsDepth deltaDepth
      (familyAllocated n T sm) A.toFinset).card : ℚ) ≤ (2 : ℚ) ^ deltaDepth := by
    exact_mod_cast hcard
  have hpow : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ deltaDepth := by positivity
  have hmul : ((2 : ℚ) ^ deltaDepth) * (1 / 2 : ℚ) ^ deltaDepth = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    familyGrayMass epsDepth deltaDepth n T A sm
        ≤ ((2 : ℚ) ^ deltaDepth) * (1 / 2 : ℚ) ^ deltaDepth :=
      mul_le_mul_of_nonneg_right hq hpow
    _ = 1 := hmul

/-- The optional stronger invariant enjoyed by the explicit base, stage-one,
and stage-two strategies. It is not assumed by the source induction. -/
def FamilyExactRootRequest (alpha : ℚ) (n b : ℕ) (A : Allocation)
    (sigma : ClientFamilyStrategy) : Prop :=
  ∀ sm, familyServerPlayLegal n b A sm → ∀ t i, i < n →
    getFamilyReq (playClientFamily A n sigma sm t) i [] = alpha

/-- In a legal family play in which every client requests exactly `alpha` at the root, the total
root request after any number of rounds is `n * alpha`. -/
theorem totalRootRequest_of_exactRoot
    {alpha : ℚ} {n b : ℕ} {A : Allocation} {sigma : ClientFamilyStrategy}
    (hroot : FamilyExactRootRequest alpha n b A sigma)
    {sm : ℕ → FamilyServerMove} (hsm : familyServerPlayLegal n b A sm) (T : ℕ) :
    totalRootRequest n (playClientFamily A n sigma sm T) = (n : ℚ) * alpha := by
  unfold totalRootRequest
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    hroot sm hsm T i.val i.isLt)]
  simp [mul_comm]

/-- For an explicitly exact-root strategy, a target above total mass forces the
unserved branch. This lemma must not be applied to a general
`GrayFamilyGameSpec`. -/
theorem familyClientWinsUnserved_of_one_lt_exactRootTarget
    {kappa alpha beta : ℚ} {epsDepth deltaDepth h b n : ℕ} {A : Allocation}
    {sigma : ClientFamilyStrategy}
    (hgame : GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n A sigma)
    (hroot : FamilyExactRootRequest alpha n b A sigma)
    (hgt : 1 < kappa * ((n : ℚ) * alpha))
    {sm : ℕ → FamilyServerMove} (hsm : familyServerPlayLegal n b A sm) :
    familyClientWinsUnserved n h b (playClientFamily A n sigma sm) sm := by
  rcases hgame.wins sm hsm with hw | hw
  · exact hw
  · obtain ⟨T, -, hgray, -⟩ := hw
    rw [totalRootRequest_of_exactRoot hroot hsm T] at hgray
    have hle := familyGrayMass_le_one epsDepth deltaDepth n T A sm
    linarith

end Kolmogorov
