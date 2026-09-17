import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustFamily
import KolmogorovMathlib.MonotoneComplexity.GacsDayWitnessForcing
import KolmogorovMathlib.MonotoneComplexity.GacsDaySubtreeEmbedding
import Mathlib.Data.List.Nodup

/-!
# Hereditary certificates from the witness-forcing interface

The explicit witnesses produced by the first two Day strategies are globally
prefix-incomparable and, after strengthening FamilyWitnessForcing, anchored
in their own family component. Restricting them to any sublist therefore
proves Definition 4.3.2(c).
-/

namespace Kolmogorov

open scoped BigOperators

/-- Witness forcing proved on a narrow tree remains valid on a wider tree.
Only the server legality and the hypothesis that every positive request is
eventually served are restricted to the original alphabet. -/
theorem FamilyWitnessForcing.mono_branching
    {kappa : Rat} {h b b' alphaDepth deltaDepth n : Nat} [NeZero n]
    {A : Allocation} {sigma : ClientFamilyStrategy}
    (hbb : b <= b')
    (H : FamilyWitnessForcing kappa h b alphaDepth deltaDepth n A sigma) :
    FamilyWitnessForcing kappa h b' alphaDepth deltaDepth n A sigma := by
  intro sm hsm hserved
  have hsm' : familyServerPlayLegal n b A sm :=
    ⟨fun i hi => serverPlayLegal_mono_branching hbb (hsm.1 i hi),
      hsm.2.1, hsm.2.2⟩
  apply H sm hsm'
  intro i hi t x hx hdig hpos
  exact hserved i hi t x hx
    (fun d hd => lt_of_lt_of_le (hdig d hd) hbb) hpos

private lemma totalRootRequestOnList_eq_const
    {indices : List Nat} {c : FamilyClientMove} {alpha : ℚ}
    (h : ∀ i ∈ indices, getFamilyReq c i [] = alpha) :
    totalRootRequestOnList indices c = (indices.length : ℚ) * alpha := by
  induction indices with
  | nil => simp [totalRootRequestOnList]
  | cons i t ih =>
      have hi := h i (by simp)
      have ht : ∀ j ∈ t, getFamilyReq c j [] = alpha := by
        intro j hj
        exact h j (by simp [hj])
      change getFamilyReq c i [] + totalRootRequestOnList t c =
        ((t.length + 1 : Nat) : ℚ) * alpha
      rw [hi, ih ht]
      push_cast
      ring

private lemma totalRootRequest_eq_const
    {n : Nat} {c : FamilyClientMove} {alpha : ℚ}
    (h : ∀ i, i < n → getFamilyReq c i [] = alpha) :
    totalRootRequest n c = (n : ℚ) * alpha := by
  unfold totalRootRequest
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i.val i.isLt)]
  simp

/-- Restricting a globally incomparable, component-anchored witness family to
any subfamily proves the hereditary Boolean inequality at that same time. -/
theorem familySubfamilyGrayAtB_of_witnesses
    {kappa alpha : ℚ} {epsDepth deltaDepth n m : Nat}
    {A : Allocation} {client : FamilyClientMove} {server : FamilyServerMove}
    (hed : epsDepth ≤ deltaDepth)
    (hk : 0 ≤ kappa) (ha : 0 ≤ alpha)
    (hroot : ∀ i, i < n → getFamilyReq client i [] = alpha)
    (c : Fin n × Fin m → BitString)
    (hc_len : ∀ p, (c p).length ≤ deltaDepth)
    (hc_anc : ∀ p, ∃ y ∈ getFamilyAlloc server p.1.val [], y <+: c p)
    (hc_disj : ∀ p q, p ≠ q →
      ¬ ((c p) <+: (c q) ∨ (c q) <+: (c p)))
    (hc_avoid : ∀ p, ∀ v ∈ A, ¬ ((c p) <+: v ∨ v <+: (c p)))
    (hmass : ∀ i : Fin n, kappa * alpha ≤
      ∑ j : Fin m, (1 / 2 : ℚ) ^ (c (i, j)).length)
    {indices : List Nat} (hindices : indices ∈ (List.range n).sublists) :
    familySubfamilyGrayAtB kappa epsDepth deltaDepth n A client server
      indices = true := by
  classical
  have hsub : List.Sublist indices (List.range n) :=
    List.mem_sublists.mp hindices
  have hnodup : indices.Nodup := List.nodup_range.sublist hsub
  let idx : Fin indices.length → Fin n := fun j =>
    ⟨indices.get j, List.mem_range.mp
      (hsub.subset (List.get_mem indices j))⟩
  let d : Fin indices.length × Fin m → BitString :=
    fun p => c (idx p.1, p.2)
  have hd_len : ∀ p, (d p).length ≤ deltaDepth := by
    intro p
    exact hc_len (idx p.1, p.2)
  have hd_anc : ∀ p, ∃ y ∈ (familyAllocatedOnList indices server).toFinset,
      y <+: d p := by
    intro p
    obtain ⟨y, hy, hyp⟩ := hc_anc (idx p.1, p.2)
    refine ⟨y, List.mem_toFinset.mpr ?_, hyp⟩
    simp only [familyAllocatedOnList, List.mem_flatMap]
    exact ⟨indices.get p.1, List.get_mem indices p.1, hy⟩
  have hidx_inj : Function.Injective idx := by
    intro i j hij
    exact hnodup.injective_get (congrArg Fin.val hij)
  have hd_disj : ∀ p q, p ≠ q →
      ¬ ((d p) <+: (d q) ∨ (d q) <+: (d p)) := by
    intro p q hpq
    apply hc_disj
    intro hp
    apply hpq
    have hp1 : p.1 = q.1 := by
      apply hidx_inj
      exact congrArg (fun z : Fin n × Fin m => z.1) hp
    have hp2 : p.2 = q.2 := by
      exact congrArg (fun z : Fin n × Fin m => z.2) hp
    exact Prod.ext hp1 hp2
  have hd_avoid : ∀ p, ∀ v ∈ A.toFinset,
      ¬ ((d p) <+: v ∨ v <+: (d p)) := by
    intro p v hv
    exact hc_avoid (idx p.1, p.2) v (List.mem_toFinset.mp hv)
  have hgray := grayMass_ge_of_incomparable_witnesses
    epsDepth deltaDepth hed
    (familyAllocatedOnList indices server).toFinset A.toFinset
    d hd_len hd_anc hd_disj hd_avoid
  have hcount :
      ∑ p : Fin indices.length × Fin m, (1 / 2 : ℚ) ^ (d p).length ≤
        grayMassOfCount deltaDepth
          (newGrayCount epsDepth deltaDepth
            (familyAllocatedOnList indices server) A) := by
    rw [grayMassOfCount, ← card_newGrayCells_eq_newGrayCount hed
      (familyAllocatedOnList indices server) A]
    exact hgray
  have hsum :
      (indices.length : ℚ) * (kappa * alpha) ≤
        ∑ p : Fin indices.length × Fin m, (1 / 2 : ℚ) ^ (d p).length := by
    rw [Fintype.sum_prod_type]
    calc
      (indices.length : ℚ) * (kappa * alpha) =
          ∑ _i : Fin indices.length, kappa * alpha := by simp
      _ ≤ ∑ i : Fin indices.length,
          ∑ j : Fin m, (1 / 2 : ℚ) ^ (d (i, j)).length :=
        Finset.sum_le_sum (fun i _ => hmass (idx i))
  have hselected :
      totalRootRequestOnList indices client =
        (indices.length : ℚ) * alpha := by
    apply totalRootRequestOnList_eq_const
    intro i hi
    exact hroot i (List.mem_range.mp (hsub.subset hi))
  have htotal : totalRootRequest n client = (n : ℚ) * alpha :=
    totalRootRequest_eq_const hroot
  have hlenNat : indices.length ≤ n :=
    le_trans hsub.length_le (by simp)
  have hlenQ : (indices.length : ℚ) ≤ (n : ℚ) := by exact_mod_cast hlenNat
  unfold familySubfamilyGrayAtB
  simp only [decide_eq_true_eq]
  rw [hselected, htotal]
  calc
    kappa * (2 * ((indices.length : ℚ) * alpha) - (n : ℚ) * alpha)
        ≤ (indices.length : ℚ) * (kappa * alpha) := by
          nlinarith [mul_nonneg hk ha, mul_nonneg
            (sub_nonneg.mpr hlenQ) ha]
    _ ≤ _ := le_trans hsum hcount

/-- The same witness family also gives the componentwise request window. -/
theorem familyPointwiseGrayAtB_of_witnesses
    {kappa alpha beta : ℚ} {epsDepth deltaDepth n m : Nat}
    {A : Allocation} {client : FamilyClientMove} {server : FamilyServerMove}
    (_hed : epsDepth ≤ deltaDepth)
    (hprogress : beta ≤ kappa * alpha)
    (hcap : alpha ≤ (4 / 3 : ℚ) * beta)
    (hroot : ∀ i, i < n → getFamilyReq client i [] = alpha)
    (c : Fin n × Fin m → BitString)
    (_hc_len : ∀ p, (c p).length ≤ deltaDepth)
    (_hc_anc : ∀ p, ∃ y ∈ getFamilyAlloc server p.1.val [], y <+: c p)
    (_hc_disj : ∀ p q, p ≠ q →
      ¬ ((c p) <+: (c q) ∨ (c q) <+: (c p)))
    (_hc_avoid : ∀ p, ∀ v ∈ A, ¬ ((c p) <+: v ∨ v <+: (c p)))
    (_hmass : ∀ i : Fin n, kappa * alpha ≤
      ∑ j : Fin m, (1 / 2 : ℚ) ^ (c (i, j)).length) :
    familyPointwiseGrayAtB kappa beta epsDepth deltaDepth n A
      client server = true := by
  classical
  unfold familyPointwiseGrayAtB
  rw [List.all_eq_true]
  intro i hi
  have hin : i < n := List.mem_range.mp hi
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rw [hroot i hin]
    exact hprogress
  · rw [hroot i hin]
    exact hcap

/-- Witness forcing yields the hereditary alternative, at one common time for
the aggregate certificate and all subfamilies. -/
theorem robustWins_of_familyWitnessForcing_positive
    (kappa : ℚ) (h b alphaDepth epsDepth deltaDepth n : Nat) [NeZero n]
    (A : Allocation) (sigma : ClientFamilyStrategy)
    (hForcing : FamilyWitnessForcing kappa h b alphaDepth deltaDepth n A sigma)
    (hscales : epsDepth ≤ deltaDepth)
    (hkappa : 1 ≤ kappa)
    (hroot : ∀ sm, familyServerPlayLegal n b A sm → ∀ t i, i < n →
      getFamilyReq (playClientFamily A n sigma sm t) i [] =
        dyadicScale alphaDepth) :
    ∀ sm, familyServerPlayLegal n b A sm →
      familyClientWinsUnservedPositive n h b
          (playClientFamily A n sigma sm) sm ∨
        familyRobustGrayGoal kappa
          ((3 / 4 : ℚ) * dyadicScale alphaDepth)
          epsDepth deltaDepth n A
          (playClientFamily A n sigma sm) sm := by
  classical
  intro sm hsm
  by_cases hwin : familyClientWinsUnservedPositive n h b
      (playClientFamily A n sigma sm) sm
  · exact Or.inl hwin
  · right
    have hserved : ∀ i < n, ∀ t0 (x : GacsDayNode), x.length ≤ h →
        (∀ dg ∈ x, dg < b) →
        0 < getReq
          (familyClientMoveAt (playClientFamily A n sigma sm t0) i) x →
        ∃ t, Serves (getAlloc (familyServerMoveAt (sm t) i) x)
          (getReq
            (familyClientMoveAt (playClientFamily A n sigma sm t0) i) x) := by
      intro i hi t0 x hlen hdig hpos
      by_contra hcon
      push Not at hcon
      exact hwin ⟨i, hi, t0, x, hlen, hdig, hcon, hpos⟩
    obtain ⟨T, m, c, hc_len, hc_anc, hc_disj, hc_avoid,
        hmass_each, _hmass_root⟩ := hForcing sm hsm hserved
    have hc_anc_all : ∀ p, ∃ y ∈ familyAllocated n T sm, y <+: c p := by
      intro p
      obtain ⟨y, hy, hyp⟩ := hc_anc p
      exact ⟨y, Finset.mem_biUnion.mpr
        ⟨p.1, Finset.mem_univ _, List.mem_toFinset.mpr hy⟩, hyp⟩
    have hmass := familyGrayMass_ge_of_incomparable_witnesses
      (epsDepth := epsDepth) (deltaDepth := deltaDepth)
      (n := n) (T := T) (A := A) (sm := sm)
      hscales c hc_len hc_anc_all hc_disj hc_avoid
    have hsum :
        (n : ℚ) * (kappa * dyadicScale alphaDepth) ≤
          ∑ p : Fin n × Fin m, (1 / 2 : ℚ) ^ (c p).length := by
      rw [Fintype.sum_prod_type]
      calc
        (n : ℚ) * (kappa * dyadicScale alphaDepth) =
            ∑ _i : Fin n, kappa * dyadicScale alphaDepth := by simp
        _ ≤ ∑ i : Fin n,
            ∑ j : Fin m, (1 / 2 : ℚ) ^ (c (i, j)).length :=
          Finset.sum_le_sum (fun i _ => hmass_each i)
    have hrootEq :
        totalRootRequest n (playClientFamily A n sigma sm T) =
          (n : ℚ) * dyadicScale alphaDepth := by
      unfold totalRootRequest
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        hroot sm hsm T i.val i.isLt)]
      simp
    have htarget :
        (n : ℚ) * ((3 / 4 : ℚ) * dyadicScale alphaDepth) ≤
          familyGrayMass epsDepth deltaDepth n T A sm := by
      have hk34 : (3 / 4 : ℚ) ≤ kappa := by linarith
      have hdy : 0 ≤ dyadicScale alphaDepth := by
        unfold dyadicScale
        positivity
      calc
        (n : ℚ) * ((3 / 4 : ℚ) * dyadicScale alphaDepth) ≤
            (n : ℚ) * (kappa * dyadicScale alphaDepth) := by
              apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul_of_nonneg_right hk34 hdy
              · positivity
        _ ≤ _ := le_trans hsum hmass
    have hamp :
        kappa * totalRootRequest n
            (playClientFamily A n sigma sm T) ≤
          familyGrayMass epsDepth deltaDepth n T A sm := by
      rw [hrootEq]
      calc
        kappa * ((n : ℚ) * dyadicScale alphaDepth) =
            (n : ℚ) * (kappa * dyadicScale alphaDepth) := by ring
        _ ≤ _ := le_trans hsum hmass
    have hprogress :
        (n : ℚ) * ((3 / 4 : ℚ) * dyadicScale alphaDepth) ≤
          kappa * totalRootRequest n
            (playClientFamily A n sigma sm T) := by
      rw [hrootEq]
      have hk34 : (3 / 4 : ℚ) ≤ kappa := by linarith
      have hdy : 0 ≤ dyadicScale alphaDepth := by
        unfold dyadicScale
        positivity
      have hnonneg : 0 ≤ (n : ℚ) * dyadicScale alphaDepth :=
        mul_nonneg (by positivity) hdy
      calc
        (n : ℚ) * ((3 / 4 : ℚ) * dyadicScale alphaDepth) =
            (3 / 4 : ℚ) *
              ((n : ℚ) * dyadicScale alphaDepth) := by ring
        _ ≤ kappa * ((n : ℚ) * dyadicScale alphaDepth) :=
          mul_le_mul_of_nonneg_right hk34 hnonneg
    refine ⟨T, ?_⟩
    unfold familyRobustGrayGoalAtB
    simp only [Bool.and_eq_true]
    constructor
    · apply (familyGrayGoalAtB_eq_true_iff hscales n T A
        (playClientFamily A n sigma sm) sm).2
      exact ⟨htarget, hamp, hprogress⟩
    · constructor
      · rw [List.all_eq_true]
        intro indices hindices
        apply familySubfamilyGrayAtB_of_witnesses hscales
          (le_trans (by norm_num) hkappa)
          (by simp only [dyadicScale]; positivity)
          (fun i hi => hroot sm hsm T i hi)
          c hc_len hc_anc hc_disj hc_avoid hmass_each hindices
      · apply familyPointwiseGrayAtB_of_witnesses hscales
          (kappa := kappa) (alpha := dyadicScale alphaDepth)
          (beta := (3 / 4 : ℚ) * dyadicScale alphaDepth)
          (by
            have hk34 : (3 / 4 : ℚ) ≤ kappa := by linarith
            have hdy : 0 ≤ dyadicScale alphaDepth := by
              unfold dyadicScale
              positivity
            exact mul_le_mul_of_nonneg_right hk34 hdy)
          (by
            ring_nf
            exact le_rfl)
          (fun i hi => hroot sm hsm T i hi)
          c hc_len hc_anc hc_disj hc_avoid hmass_each

/-- Package witness forcing as the strong family-game interface. -/
theorem robustGrayFamilyGameSpec_of_witnessForcing
    (kappa : ℚ) (h b alphaDepth epsDepth deltaDepth n : Nat) [NeZero n]
    (A : Allocation) (sigma : ClientFamilyStrategy)
    (hForcing : FamilyWitnessForcing kappa h b alphaDepth deltaDepth n A sigma)
    (hweak : GrayFamilyGameSpec kappa (dyadicScale alphaDepth)
      ((3 / 4 : ℚ) * dyadicScale alphaDepth)
      epsDepth deltaDepth h b n A sigma)
    (hkappa : 1 ≤ kappa)
    (hroot : ∀ sm, familyServerPlayLegal n b A sm → ∀ t i, i < n →
      getFamilyReq (playClientFamily A n sigma sm t) i [] =
        dyadicScale alphaDepth)
    (heps : epsDepth ≤ deltaDepth) :
    RobustGrayFamilyGameSpec kappa (dyadicScale alphaDepth)
      ((3 / 4 : ℚ) * dyadicScale alphaDepth)
      epsDepth deltaDepth h b n A sigma := by
  refine ⟨hweak, ?_⟩
  exact robustWins_of_familyWitnessForcing_positive kappa h b alphaDepth
    epsDepth deltaDepth n A sigma hForcing heps hkappa hroot

end Kolmogorov
