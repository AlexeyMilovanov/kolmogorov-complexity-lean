import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1EffectiveRunSemantics
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1RunBounds

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- The number of currently pending `C`- or `D`-marked points. -/
def t1RunPendingCharge (s : T1RunState) : Nat :=
  (s.current.toFinset ∩
    (s.cMarked.toFinset ∪ s.dMarked.toFinset)).card

/-- Pending-charge invariant for an arbitrary positive rebuild quota. -/
def T1RunQuotaChargeInvariant (quota : Nat) (s : T1RunState) : Prop :=
  s.saturation * quota + t1RunPendingCharge s ≤
    s.totalC + s.totalD

/-- Original T1 specialization, whose quota is the whole current model. -/
def T1RunChargeInvariant (k epsilon : Nat) (s : T1RunState) : Prop :=
  T1RunQuotaChargeInvariant (2 ^ (k - epsilon)) s

/-- The state whose pending marks are tested by a transition.  External events
rebuild unconditionally and never increment the saturation counter. -/
noncomputable def t1RunChargePrepared
    (n : Nat) (s : T1RunState) : T1MarkEvent → T1RunState
  | .cPrimeModel w =>
      if w ∈ s.seenCDouble then t1RunCPrimePrepared n s w else s
  | .dString x => t1RunDPrepared n s x
  | _ => s

theorem t1RunStep_cPrime_charge_le
    (cSparse n k epsilon quota : Nat) (s : T1RunState) (w : BitString)
    (hmodel : T1RunModelInvariant cSparse n k epsilon quota s) :
    (t1RunStep cSparse n k epsilon quota s (.cPrimeModel w)).totalC - s.totalC ≤
      cSparse * n + cSparse := by
  by_cases hw : w ∈ s.seenCDouble
  · have hbound :=
      hmodel.2.2.2.2.2 w hw
    have hcurrent : s.current.Nodup := hmodel.1
    have hlength :
        ∀ x ∈ s.current, x.length = n := by
      intro x hx
      exact (memStringsOfLength n x).mp
        (hmodel.2.2.1 (List.mem_toFinset.mpr hx))
    have hfilter :
        (s.current.filter fun x =>
          x ∈ (canonicalPointListOfCode w).filter
            (fun x => x.length = n)).length =
          (s.current.toFinset ∩ t1CodeToSet w).card := by
      rw [← List.toFinset_card_of_nodup
        (hcurrent.filter _)]
      congr 1
      ext x
      by_cases hx : x ∈ s.current
      · simp [hx, hlength x hx, canonicalPointListOfCode,
          t1CodeToSet]
      · simp [hx]
    rw [t1RunStep_cPrime_eq]
    simp only [hw, if_true]
    split <;>
      change s.totalC +
          (s.current.filter fun x =>
            x ∈ (canonicalPointListOfCode w).filter
              (fun x => x.length = n)).length -
            s.totalC ≤ cSparse * n + cSparse <;>
      omega
  · rw [t1RunStep_cPrime_eq]
    simp [hw, t1RunCPrimeSeenPrepared]

theorem t1RunStep_d_charge_le
    (cSparse n k epsilon quota : Nat) (s : T1RunState) (x : BitString) :
    (t1RunStep cSparse n k epsilon quota s (.dString x)).totalD - s.totalD ≤ 1 := by
  rw [t1RunStep_dString_eq]
  simp only
  split <;>
    change s.totalD + (if x ∈ s.current then 1 else 0) -
      s.totalD ≤ 1
  all_goals
    by_cases hx : x ∈ s.current <;> simp [hx]

theorem t1RunStep_saturation_spends_quota
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (event : T1MarkEvent) (hcurrent : s.current.Nodup) :
    let s' := t1RunStep cSparse n k epsilon quota s event
    s'.saturation > s.saturation →
      t1RunPendingCharge (t1RunChargePrepared n s event) ≥ quota := by
  cases event with
  | bSet w =>
      rw [t1RunStep_bSet_eq]
      change s.saturation < s.saturation → _
      simp
  | cDoublePrimeBatch batch =>
      rw [t1RunStep_cDouble_eq]
      change s.saturation < s.saturation → _
      simp
  | cPrimeModel w =>
      by_cases hw : w ∈ s.seenCDouble
      · rw [t1RunStep_cPrime_eq]
        simp only [hw, if_true]
        split
        · rename_i hsat
          intro _
          have hprepared :
              (t1RunCPrimePrepared n s w).current.Nodup := by
            simpa [t1RunCPrimePrepared, t1RunCPrimeSeenPrepared]
              using hcurrent
          simpa [t1RunChargePrepared, hw, t1RunPendingCharge] using
            (t1RunSaturated_iff
              (t1RunCPrimePrepared n s w) quota hprepared).mp hsat
        · change s.saturation < s.saturation → _
          simp
      · rw [t1RunStep_cPrime_eq]
        simp [hw, t1RunChargePrepared,
          t1RunCPrimeSeenPrepared]
  | dString x =>
      rw [t1RunStep_dString_eq]
      simp only
      split
      · rename_i hsat
        intro _
        have hprepared :
            (t1RunDPrepared n s x).current.Nodup := by
          simpa [t1RunDPrepared] using hcurrent
        simpa [t1RunChargePrepared, t1RunPendingCharge] using
          (t1RunSaturated_iff
            (t1RunDPrepared n s x) quota hprepared).mp hsat
      · change s.saturation < s.saturation → _
        simp

/-- A selector rebuild chooses its new current model outside every accumulated
mark, so it has no pending charge. -/
theorem t1RunRebuild_pendingCharge_eq_zero
    (cSparse n k epsilon : Nat) (s : T1RunState) :
    t1RunPendingCharge (t1RunRebuild cSparse n k epsilon s) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.ext
  intro x
  constructor
  · intro hx
    exfalso
    rw [Finset.mem_inter] at hx
    have hsub :=
      (t1RunRebuild_current_spec cSparse n k epsilon s).2 hx.1
    rw [Finset.mem_sdiff] at hsub
    have hnotMarked : x ∉ (t1RunMarked s).toFinset := hsub.2
    apply hnotMarked
    rw [t1RunMarked_toFinset]
    have hdata :=
      t1RunRebuild_markingDataEq cSparse n k epsilon s
    rcases hdata with ⟨_, hc, hd, _, _⟩
    rw [← hc, ← hd] at hx
    simp [hx.2]
  · intro hx
    simp at hx

/-- Activating a `C'` code grows the pending set by at most the number of
current-list hits charged to `totalC`. -/
theorem t1RunCPrimePrepared_pending_le
    (n : Nat) (s : T1RunState) (w : BitString)
    (hcurrent : s.current.Nodup) :
    t1RunPendingCharge (t1RunCPrimePrepared n s w) ≤
      t1RunPendingCharge s +
        ((t1RunCPrimePrepared n s w).totalC - s.totalC) := by
  let points :=
    (canonicalPointListOfCode w).filter
      (fun x => x.length = n)
  have hcharge :
      (t1RunCPrimePrepared n s w).totalC - s.totalC =
        (s.current.toFinset ∩ points.toFinset).card := by
    change s.totalC +
        (s.current.filter fun x => x ∈ points).length -
          s.totalC =
      (s.current.toFinset ∩ points.toFinset).card
    rw [Nat.add_sub_cancel_left,
      ← List.toFinset_card_of_nodup (hcurrent.filter _)]
    congr 1
    ext x
    simp
  have hpending :
      t1RunPendingCharge (t1RunCPrimePrepared n s w) =
        ((s.current.toFinset ∩
            (s.cMarked.toFinset ∪ s.dMarked.toFinset)) ∪
          (s.current.toFinset ∩ points.toFinset)).card := by
    unfold t1RunPendingCharge
    congr 1
    ext x
    simp [t1RunCPrimePrepared,
      t1RunCPrimeSeenPrepared, points]
    tauto
  rw [hpending, hcharge]
  exact Finset.card_union_le _ _

/-- A `D` event grows the pending set by at most its zero-or-one current hit. -/
theorem t1RunDPrepared_pending_le
    (n : Nat) (s : T1RunState) (x : BitString) :
    t1RunPendingCharge (t1RunDPrepared n s x) ≤
      t1RunPendingCharge s +
        ((t1RunDPrepared n s x).totalD - s.totalD) := by
  let points : Finset BitString :=
    if x.length = n then {x} else ∅
  have hcharge :
      (t1RunDPrepared n s x).totalD - s.totalD =
        if x ∈ s.current then 1 else 0 := by
    simp [t1RunDPrepared]
  have hpending :
      t1RunPendingCharge (t1RunDPrepared n s x) =
        ((s.current.toFinset ∩
            (s.cMarked.toFinset ∪ s.dMarked.toFinset)) ∪
          (s.current.toFinset ∩ points)).card := by
    unfold t1RunPendingCharge
    congr 1
    ext y
    by_cases hlen : x.length = n
    · simp [t1RunDPrepared, points, hlen]
      tauto
    · simp [t1RunDPrepared, points, hlen]
  have hextra :
      (s.current.toFinset ∩ points).card ≤
        if x ∈ s.current then 1 else 0 := by
    by_cases hx : x ∈ s.current
    · by_cases hlen : x.length = n
      · simp [points, hlen, hx]
      · simp [points, hlen]
    · have hx' : x ∉ s.current.toFinset := by simpa using hx
      by_cases hlen : x.length = n
      · simp [points, hlen, hx']
      · simp [points, hlen]
  rw [hpending, hcharge]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left hextra _)

theorem t1RunStep_preserves_quota_charge
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent)
    (hcurrent : s.current.Nodup)
    (hcharge : T1RunQuotaChargeInvariant quota s) :
    T1RunQuotaChargeInvariant quota
      (t1RunStep cSparse n k epsilon quota s event) := by
  cases event with
  | bSet w =>
      rw [t1RunStep_bSet_eq]
      change s.saturation * quota +
          t1RunPendingCharge
            (t1RunRebuild cSparse n k epsilon
              (t1RunBSetPrepared n s w)) ≤
        s.totalC + s.totalD
      rw [t1RunRebuild_pendingCharge_eq_zero]
      unfold T1RunQuotaChargeInvariant at hcharge
      omega
  | cDoublePrimeBatch batch =>
      rw [t1RunStep_cDouble_eq]
      change s.saturation * quota +
          t1RunPendingCharge
            (t1RunRebuild cSparse n k epsilon
              (t1RunCDoublePrepared n s batch)) ≤
        s.totalC + s.totalD
      rw [t1RunRebuild_pendingCharge_eq_zero]
      unfold T1RunQuotaChargeInvariant at hcharge
      omega
  | cPrimeModel w =>
      by_cases hw : w ∈ s.seenCDouble
      · let prepared := t1RunCPrimePrepared n s w
        have hpreparedNodup : prepared.current.Nodup := by
          simpa [prepared, t1RunCPrimePrepared,
            t1RunCPrimeSeenPrepared] using hcurrent
        have hpending :=
          t1RunCPrimePrepared_pending_le n s w hcurrent
        have htotal : s.totalC ≤ prepared.totalC := by
          simp [prepared, t1RunCPrimePrepared,
            t1RunCPrimeSeenPrepared]
        have htotalEq :
            s.totalC + (prepared.totalC - s.totalC) =
              prepared.totalC :=
          Nat.add_sub_of_le htotal
        rw [t1RunStep_cPrime_eq]
        simp only [hw, if_true]
        split
        · rename_i hsat
          have hspend :
              quota ≤
                t1RunPendingCharge prepared :=
            (t1RunSaturated_iff prepared
              quota hpreparedNodup).mp hsat
          change (s.saturation + 1) * quota +
              t1RunPendingCharge
                (t1RunRebuild cSparse n k epsilon prepared) ≤
            prepared.totalC + s.totalD
          rw [t1RunRebuild_pendingCharge_eq_zero]
          rw [Nat.add_mul, one_mul]
          unfold T1RunQuotaChargeInvariant at hcharge
          dsimp [prepared] at hpending htotal htotalEq hspend ⊢
          omega
        · change s.saturation * quota +
              t1RunPendingCharge prepared ≤
            prepared.totalC + s.totalD
          unfold T1RunQuotaChargeInvariant at hcharge
          dsimp [prepared] at hpending htotal htotalEq ⊢
          omega
      · rw [t1RunStep_cPrime_eq]
        simp only [hw, if_false]
        simpa [T1RunQuotaChargeInvariant, t1RunPendingCharge,
          t1RunCPrimeSeenPrepared] using hcharge
  | dString x =>
      let prepared := t1RunDPrepared n s x
      have hpreparedNodup : prepared.current.Nodup := by
        simpa [prepared, t1RunDPrepared] using hcurrent
      have hpending := t1RunDPrepared_pending_le n s x
      have htotal : s.totalD ≤ prepared.totalD := by
        simp [prepared, t1RunDPrepared]
      have htotalEq :
          s.totalD + (prepared.totalD - s.totalD) =
            prepared.totalD :=
        Nat.add_sub_of_le htotal
      rw [t1RunStep_dString_eq]
      simp only
      split
      · rename_i hsat
        have hspend :
            quota ≤
              t1RunPendingCharge prepared :=
          (t1RunSaturated_iff prepared
            quota hpreparedNodup).mp hsat
        change (s.saturation + 1) * quota +
            t1RunPendingCharge
              (t1RunRebuild cSparse n k epsilon prepared) ≤
          s.totalC + prepared.totalD
        rw [t1RunRebuild_pendingCharge_eq_zero]
        rw [Nat.add_mul, one_mul]
        unfold T1RunQuotaChargeInvariant at hcharge
        dsimp [prepared] at hpending htotal htotalEq hspend ⊢
        omega
      · change s.saturation * quota +
            t1RunPendingCharge prepared ≤
          s.totalC + prepared.totalD
        unfold T1RunQuotaChargeInvariant at hcharge
        dsimp [prepared] at hpending htotal htotalEq ⊢
        omega

/-- Original whole-model-quota charging theorem. -/
theorem t1RunStep_preserves_charge
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent)
    (hquota : quota = 2 ^ (k - epsilon))
    (hcurrent : s.current.Nodup)
    (hcharge : T1RunChargeInvariant k epsilon s) :
    T1RunChargeInvariant k epsilon
      (t1RunStep cSparse n k epsilon quota s event) := by
  subst quota
  exact t1RunStep_preserves_quota_charge cSparse n k epsilon
    (2 ^ (k - epsilon)) s event hcurrent hcharge

/-- Every transition preserves duplicate-freedom of the current model. -/
theorem t1RunStep_current_nodup
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent)
    (hcurrent : s.current.Nodup) :
    (t1RunStep cSparse n k epsilon quota s event).current.Nodup := by
  cases event with
  | bSet w =>
      rw [t1RunStep_bSet_eq]
      exact (t1RunRebuild_current_spec cSparse n k epsilon
        (t1RunBSetPrepared n s w)).1
  | cDoublePrimeBatch batch =>
      rw [t1RunStep_cDouble_eq]
      exact (t1RunRebuild_current_spec cSparse n k epsilon
        (t1RunCDoublePrepared n s batch)).1
  | cPrimeModel w =>
      rw [t1RunStep_cPrime_eq]
      by_cases hw : w ∈ s.seenCDouble
      · simp only [hw, if_true]
        split
        · exact (t1RunRebuild_current_spec cSparse n k epsilon
            (t1RunCPrimePrepared n s w)).1
        · simpa [t1RunCPrimePrepared, t1RunCPrimeSeenPrepared]
            using hcurrent
      · simpa [hw, t1RunCPrimeSeenPrepared] using hcurrent
  | dString x =>
      rw [t1RunStep_dString_eq]
      simp only
      split
      · exact (t1RunRebuild_current_spec cSparse n k epsilon
          (t1RunDPrepared n s x)).1
      · simpa [t1RunDPrepared] using hcurrent

/-- Duplicate-freedom and the quota-parametric charging invariant propagate
through any finite event fold. -/
theorem t1RunFromEvents_quota_charge_spec
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (events : List T1MarkEvent)
    (hcurrent : s.current.Nodup)
    (hcharge : T1RunQuotaChargeInvariant quota s) :
    let s' :=
      t1RunFromEvents cSparse n k epsilon quota s events
    s'.current.Nodup ∧ T1RunQuotaChargeInvariant quota s' := by
  induction events generalizing s with
  | nil =>
      simpa [t1RunFromEvents] using And.intro hcurrent hcharge
  | cons event events ih =>
      simp only [t1RunFromEvents, List.foldl_cons]
      exact ih (s :=
        t1RunStep cSparse n k epsilon quota s event)
        (t1RunStep_current_nodup cSparse n k epsilon quota
          s event hcurrent)
        (t1RunStep_preserves_quota_charge cSparse n k epsilon quota
          s event hcurrent hcharge)

/-- Original whole-model-quota event-fold charging theorem. -/
theorem t1RunFromEvents_charge_spec
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (events : List T1MarkEvent)
    (hquota : quota = 2 ^ (k - epsilon))
    (hcurrent : s.current.Nodup)
    (hcharge : T1RunChargeInvariant k epsilon s) :
    let s' :=
      t1RunFromEvents cSparse n k epsilon quota s events
    s'.current.Nodup ∧ T1RunChargeInvariant k epsilon s' := by
  subst quota
  exact t1RunFromEvents_quota_charge_spec cSparse n k epsilon
    (2 ^ (k - epsilon)) s events hcurrent hcharge

theorem t1RunAt_charge_spec
    (c : Code) (cDesc cSparse n k epsilon t : Nat) :
    let quota := 2 ^ (k - epsilon)
    let s := t1RunAt c cDesc cSparse n k epsilon quota t
    T1RunChargeInvariant k epsilon s := by
  dsimp only
  exact (t1RunFromEvents_charge_spec cSparse n k epsilon
    (2 ^ (k - epsilon)) (t1InitialRunState n k epsilon)
    (t1MarkingEventStage c n k epsilon
      (epsilon + logSlack cDesc n) t)
    rfl
    (by simpa [t1InitialRunState] using
      t1InitialCurrent_nodup n k epsilon)
    (by simp [T1RunChargeInvariant, T1RunQuotaChargeInvariant,
      t1RunPendingCharge,
      t1InitialRunState])).2

/-- The events that force an external rebuild. -/
def t1RunExternalEvent : T1MarkEvent → Bool
  | .bSet _ | .cDoublePrimeBatch _ => true
  | _ => false

/-- The events that can charge `totalC`. -/
def t1RunCPrimeEvent : T1MarkEvent → Bool
  | .cPrimeModel _ => true
  | _ => false

/-- The events that can charge `totalD`. -/
def t1RunDEvent : T1MarkEvent → Bool
  | .dString _ => true
  | _ => false

private theorem t1_length_le_of_nodup_of_subset
    {α : Type} (xs ys : List α)
    (hxs : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  classical
  rw [← List.toFinset_card_of_nodup hxs]
  exact (Finset.card_le_card (by
    intro x hx
    exact List.mem_toFinset.mpr
      (hsub x (List.mem_toFinset.mp hx)))).trans
        (List.toFinset_card_le ys)

private theorem t1BStage_mono
    (c : Code) (n epsilon : Nat) {u t : Nat} (hut : u ≤ t) :
    t1BStage c n epsilon u <+: t1BStage c n epsilon t := by
  induction t, hut using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
      exact ih.trans (t1BStage_prefix c n epsilon t)

private theorem t1CPrimeStage_mono
    (c : Code) (k : Nat) {u t : Nat} (hut : u ≤ t) :
    t1CPrimeStage c k u <+: t1CPrimeStage c k t := by
  induction t, hut using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
      exact ih.trans (t1CPrimeStage_prefix c k t)

private theorem t1DStage_mono
    (c : Code) (n k : Nat) {u t : Nat} (hut : u ≤ t) :
    t1DStage c n k u <+: t1DStage c n k t := by
  induction t, hut using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
      exact ih.trans (t1DStage_prefix c n k t)

/-- The chronological stream contains no more external events than the final
visible `B` and `C''` streams. -/
theorem t1MarkingEventStage_external_count_le
    (c : Code) (n k epsilon d t : Nat) :
    ((t1MarkingEventStage c n k epsilon d t).filter
      t1RunExternalEvent).length ≤
        (t1BStage c n epsilon t).length +
          (t1CDoublePrimeBatches c n k d t).length := by
  let target :=
    (t1BStage c n epsilon t).map T1MarkEvent.bSet ++
      (t1CDoublePrimeBatches c n k d t).map
        T1MarkEvent.cDoublePrimeBatch
  have hle :
      ((t1MarkingEventStage c n k epsilon d t).filter
        t1RunExternalEvent).length ≤ target.length := by
    apply t1_length_le_of_nodup_of_subset
    · exact (t1MarkingEventStage_nodup c n k epsilon d t).filter _
    · intro event hevent
      obtain ⟨hstage, hkind⟩ := List.mem_filter.mp hevent
      obtain ⟨u, hu, horigin⟩ :=
        t1MarkingEventStage_mem_origin c n k epsilon d t event hstage
      cases event with
      | bSet w =>
          have hw : w ∈ t1BStage c n epsilon u := by
            simpa [t1MarkingEventsUpToTime] using horigin
          apply List.mem_append_left
          exact List.mem_map.mpr
            ⟨w, (t1BStage_mono c n epsilon hu).subset hw, rfl⟩
      | cDoublePrimeBatch batch =>
          have hbatch :
              batch ∈ t1CDoublePrimeBatches c n k d u := by
            simpa [t1MarkingEventsUpToTime] using horigin
          apply List.mem_append_right
          exact List.mem_map.mpr
            ⟨batch,
              (t1CDoublePrimeBatches_mono c n k d hu).subset hbatch,
              rfl⟩
      | cPrimeModel w => simp [t1RunExternalEvent] at hkind
      | dString x => simp [t1RunExternalEvent] at hkind
  simpa [target] using hle

/-- The chronological stream contains no more `C'` events than the final
visible `C'` stream. -/
theorem t1MarkingEventStage_cPrime_count_le
    (c : Code) (n k epsilon d t : Nat) :
    ((t1MarkingEventStage c n k epsilon d t).filter
      t1RunCPrimeEvent).length ≤
        (t1CPrimeStage c k t).length := by
  let target :=
    (t1CPrimeStage c k t).map T1MarkEvent.cPrimeModel
  have hle :
      ((t1MarkingEventStage c n k epsilon d t).filter
        t1RunCPrimeEvent).length ≤ target.length := by
    apply t1_length_le_of_nodup_of_subset
    · exact (t1MarkingEventStage_nodup c n k epsilon d t).filter _
    · intro event hevent
      obtain ⟨hstage, hkind⟩ := List.mem_filter.mp hevent
      obtain ⟨u, hu, horigin⟩ :=
        t1MarkingEventStage_mem_origin c n k epsilon d t event hstage
      cases event with
      | bSet w => simp [t1RunCPrimeEvent] at hkind
      | cDoublePrimeBatch batch => simp [t1RunCPrimeEvent] at hkind
      | cPrimeModel w =>
          have hw : w ∈ t1CPrimeStage c k u := by
            simpa [t1MarkingEventsUpToTime] using horigin
          exact List.mem_map.mpr
            ⟨w, (t1CPrimeStage_mono c k hu).subset hw, rfl⟩
      | dString x => simp [t1RunCPrimeEvent] at hkind
  simpa [target] using hle

/-- The chronological stream contains no more `D` events than the final
visible `D` stream. -/
theorem t1MarkingEventStage_d_count_le
    (c : Code) (n k epsilon d t : Nat) :
    ((t1MarkingEventStage c n k epsilon d t).filter
      t1RunDEvent).length ≤
        (t1DStage c n k t).length := by
  let target :=
    (t1DStage c n k t).map T1MarkEvent.dString
  have hle :
      ((t1MarkingEventStage c n k epsilon d t).filter
        t1RunDEvent).length ≤ target.length := by
    apply t1_length_le_of_nodup_of_subset
    · exact (t1MarkingEventStage_nodup c n k epsilon d t).filter _
    · intro event hevent
      obtain ⟨hstage, hkind⟩ := List.mem_filter.mp hevent
      obtain ⟨u, hu, horigin⟩ :=
        t1MarkingEventStage_mem_origin c n k epsilon d t event hstage
      cases event with
      | bSet w => simp [t1RunDEvent] at hkind
      | cDoublePrimeBatch batch => simp [t1RunDEvent] at hkind
      | cPrimeModel w => simp [t1RunDEvent] at hkind
      | dString x =>
          have hx : x ∈ t1DStage c n k u := by
            simpa [t1MarkingEventsUpToTime] using horigin
          exact List.mem_map.mpr
            ⟨x, (t1DStage_mono c n k hu).subset hx, rfl⟩
  simpa [target] using hle

theorem t1RunStep_external_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent) :
    (t1RunStep cSparse n k epsilon quota s event).external =
      s.external + if t1RunExternalEvent event then 1 else 0 := by
  cases event with
  | bSet w =>
      simp [t1RunStep_bSet_eq, t1RunExternalEvent]
  | cDoublePrimeBatch batch =>
      simp [t1RunStep_cDouble_eq, t1RunExternalEvent]
  | cPrimeModel w =>
      rw [t1RunStep_cPrime_eq]
      by_cases hw : w ∈ s.seenCDouble
      · simp only [hw, if_true]
        split
        · simpa [t1RunExternalEvent, t1RunCPrimePrepared,
            t1RunCPrimeSeenPrepared] using
            (t1RunRebuild_counters cSparse n k epsilon
              (t1RunCPrimePrepared n s w)).1
        · rfl
      · simp [hw, t1RunExternalEvent, t1RunCPrimeSeenPrepared]
  | dString x =>
      rw [t1RunStep_dString_eq]
      simp only
      split
      · simpa [t1RunExternalEvent, t1RunDPrepared] using
          (t1RunRebuild_counters cSparse n k epsilon
            (t1RunDPrepared n s x)).1
      · rfl

theorem t1RunStep_totalD_le
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent) :
    (t1RunStep cSparse n k epsilon quota s event).totalD ≤
      s.totalD + if t1RunDEvent event then 1 else 0 := by
  cases event with
  | bSet w =>
      rw [t1RunStep_bSet_eq]
      simpa [t1RunDEvent, t1RunBSetPrepared] using
        (t1RunRebuild_counters cSparse n k epsilon
          (t1RunBSetPrepared n s w)).2.2.2.le
  | cDoublePrimeBatch batch =>
      rw [t1RunStep_cDouble_eq]
      simpa [t1RunDEvent, t1RunCDoublePrepared] using
        (t1RunRebuild_counters cSparse n k epsilon
          (t1RunCDoublePrepared n s batch)).2.2.2.le
  | cPrimeModel w =>
      rw [t1RunStep_cPrime_eq]
      by_cases hw : w ∈ s.seenCDouble
      · simp only [hw, if_true]
        split
        · simpa [t1RunDEvent, t1RunCPrimePrepared,
            t1RunCPrimeSeenPrepared] using
            (t1RunRebuild_counters cSparse n k epsilon
              (t1RunCPrimePrepared n s w)).2.2.2.le
        · simp [t1RunDEvent, t1RunCPrimePrepared,
            t1RunCPrimeSeenPrepared]
      · simp [hw, t1RunDEvent, t1RunCPrimeSeenPrepared]
  | dString x =>
      rw [t1RunStep_dString_eq]
      have hprepared :
          (t1RunDPrepared n s x).totalD ≤ s.totalD + 1 := by
        by_cases hx : x ∈ s.current <;>
          simp [t1RunDPrepared, hx]
      simp only
      split
      · rw [(t1RunRebuild_counters cSparse n k epsilon
          (t1RunDPrepared n s x)).2.2.2]
        simpa [t1RunDEvent] using hprepared
      · simpa [t1RunDEvent] using hprepared

theorem t1RunFromEvents_external_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (events : List T1MarkEvent) :
    (t1RunFromEvents cSparse n k epsilon quota s events).external =
      s.external +
        (events.filter t1RunExternalEvent).length := by
  induction events using List.reverseRecOn with
  | nil => simp [t1RunFromEvents]
  | append_singleton events event ih =>
      rw [t1RunFromEvents_append, t1RunStep_external_eq, ih]
      cases event <;> simp [t1RunExternalEvent, List.filter_cons, List.filter_nil] <;> omega

theorem t1RunFromEvents_totalD_le
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (events : List T1MarkEvent) :
    (t1RunFromEvents cSparse n k epsilon quota s events).totalD ≤
      s.totalD + (events.filter t1RunDEvent).length := by
  induction events using List.reverseRecOn with
  | nil => simp [t1RunFromEvents]
  | append_singleton events event ih =>
      rw [t1RunFromEvents_append]
      have hstep :=
        t1RunStep_totalD_le cSparse n k epsilon quota
          (t1RunFromEvents cSparse n k epsilon quota s events) event
      simp only [List.filter_append, List.filter_singleton,
        List.length_append] at *
      cases event <;> simp [t1RunDEvent] at hstep ⊢ <;> omega

theorem t1RunStep_totalC_le
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent)
    (hmodel : T1RunModelInvariant cSparse n k epsilon quota s) :
    (t1RunStep cSparse n k epsilon quota s event).totalC ≤
      s.totalC +
        if t1RunCPrimeEvent event then
          cSparse * n + cSparse
        else 0 := by
  cases event with
  | bSet w =>
      rw [t1RunStep_bSet_eq]
      simpa [t1RunCPrimeEvent, t1RunBSetPrepared] using
        (t1RunRebuild_counters cSparse n k epsilon
          (t1RunBSetPrepared n s w)).2.2.1.le
  | cDoublePrimeBatch batch =>
      rw [t1RunStep_cDouble_eq]
      simpa [t1RunCPrimeEvent, t1RunCDoublePrepared] using
        (t1RunRebuild_counters cSparse n k epsilon
          (t1RunCDoublePrepared n s batch)).2.2.1.le
  | cPrimeModel w =>
      have hdiff :=
        t1RunStep_cPrime_charge_le cSparse n k epsilon quota
          s w hmodel
      have hmono :
          s.totalC ≤
            (t1RunStep cSparse n k epsilon quota s
              (.cPrimeModel w)).totalC := by
        rw [t1RunStep_cPrime_eq]
        by_cases hw : w ∈ s.seenCDouble
        · simp only [hw, if_true]
          split
          · have hprepared :
                s.totalC ≤
                  (t1RunCPrimePrepared n s w).totalC := by
              simp [t1RunCPrimePrepared,
                t1RunCPrimeSeenPrepared]
            exact hprepared.trans
              (t1RunRebuild_counters cSparse n k epsilon
                (t1RunCPrimePrepared n s w)).2.2.1.ge
          · simp [t1RunCPrimePrepared,
              t1RunCPrimeSeenPrepared]
        · simp [hw, t1RunCPrimeSeenPrepared]
      change
        (t1RunStep cSparse n k epsilon quota s
          (.cPrimeModel w)).totalC ≤
            s.totalC + (cSparse * n + cSparse)
      omega
  | dString x =>
      rw [t1RunStep_dString_eq]
      simp only
      split
      · simpa [t1RunCPrimeEvent, t1RunDPrepared] using
          (t1RunRebuild_counters cSparse n k epsilon
            (t1RunDPrepared n s x)).2.2.1.le
      · simp [t1RunCPrimeEvent, t1RunDPrepared]

theorem t1RunAt_external_rebuilds_le_of_quota
    (c : Code) (cDesc cSparse n k epsilon quota t : Nat) :
    let s := t1RunAt c cDesc cSparse n k epsilon quota t
    s.external ≤ 2 ^ (epsilon + 1) + 2 ^ (epsilon + logSlack cDesc n + 1) := by
  dsimp only
  let events :=
    t1MarkingEventStage c n k epsilon
      (epsilon + logSlack cDesc n) t
  have hrun :=
    t1RunFromEvents_external_eq cSparse n k epsilon
      quota (t1InitialRunState n k epsilon) events
  have hcount :=
    t1MarkingEventStage_external_count_le c n k epsilon
      (epsilon + logSlack cDesc n) t
  have hB := t1BStage_length_lt c n epsilon t
  have hC :=
    t1CDoublePrimeBatches_length_lt c n k
      (epsilon + logSlack cDesc n) t
  dsimp [t1RunAt, events, t1InitialRunState] at hrun ⊢
  omega

theorem t1RunAt_external_rebuilds_le
    (c : Code) (cDesc cSparse n k epsilon t : Nat) :
    let quota := 2 ^ (k - epsilon)
    let s := t1RunAt c cDesc cSparse n k epsilon quota t
    s.external ≤ 2 ^ (epsilon + 1) + 2 ^ (epsilon + logSlack cDesc n + 1) := by
  exact t1RunAt_external_rebuilds_le_of_quota c cDesc cSparse n k epsilon
    (2 ^ (k - epsilon)) t

theorem t1RunAt_totalC_le
    (V : Map) (c : Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon t,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      let quota := 2 ^ (k - epsilon)
      let s := t1RunAt c cDesc cSparse n k epsilon quota t
      s.totalC ≤
        2 ^ (k + 1) * (cSparse * n + cSparse) := by
  intro cDesc
  obtain ⟨c0, cSparse, hmodel⟩ :=
    t1RunFromEvents_model_spec V c hc cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon t hc0 hepsilon hkn
  let quota := 2 ^ (k - epsilon)
  let full :=
    t1MarkingEventStage c n k epsilon
      (epsilon + logSlack cDesc n) t
  let r := cSparse * n + cSparse
  have hprefix :
      ∀ events : List T1MarkEvent, events <+: full →
        (t1RunFromEvents cSparse n k epsilon quota
          (t1InitialRunState n k epsilon) events).totalC ≤
            (events.filter t1RunCPrimeEvent).length * r := by
    intro events hevents
    induction events using List.reverseRecOn with
    | nil =>
        simp [t1RunFromEvents, t1InitialRunState]
    | append_singleton events event ih =>
        have hold :
            events <+: full :=
          (List.prefix_append events [event]).trans hevents
        have hstate :
            T1RunModelInvariant cSparse n k epsilon quota
              (t1RunFromEvents cSparse n k epsilon quota
                (t1InitialRunState n k epsilon) events) :=
          hmodel n k epsilon quota t events hc0 hepsilon hkn
            rfl (by simpa [full] using hold)
        have hstep :=
          t1RunStep_totalC_le cSparse n k epsilon quota
            (t1RunFromEvents cSparse n k epsilon quota
              (t1InitialRunState n k epsilon) events)
            event hstate
        have ih' := ih hold
        rw [t1RunFromEvents_append]
        cases event with
        | bSet w =>
            simpa [t1RunCPrimeEvent] using hstep.trans ih'
        | cDoublePrimeBatch batch =>
            simpa [t1RunCPrimeEvent] using hstep.trans ih'
        | cPrimeModel w =>
            simp only [List.filter_append, List.filter_singleton,
              t1RunCPrimeEvent, List.length_append]
            calc
              (t1RunStep cSparse n k epsilon quota
                  (t1RunFromEvents cSparse n k epsilon quota
                    (t1InitialRunState n k epsilon) events)
                  (.cPrimeModel w)).totalC
                  ≤ (t1RunFromEvents cSparse n k epsilon quota
                      (t1InitialRunState n k epsilon) events).totalC +
                        r := by simpa [r, t1RunCPrimeEvent] using hstep
              _ ≤ (events.filter t1RunCPrimeEvent).length * r + r :=
                Nat.add_le_add_right ih' r
              _ = ((events.filter t1RunCPrimeEvent).length + 1) * r := by
                ring
        | dString x =>
            simpa [t1RunCPrimeEvent] using hstep.trans ih'
  have hrun := hprefix full (List.prefix_refl _)
  have hcount :=
    t1MarkingEventStage_cPrime_count_le c n k epsilon
      (epsilon + logSlack cDesc n) t
  have hlength := t1CPrimeStage_length_lt c k t
  have hcountPow :
      (full.filter t1RunCPrimeEvent).length ≤ 2 ^ (k + 1) := by
    exact hcount.trans hlength.le
  dsimp only
  change
    (t1RunAt c cDesc cSparse n k epsilon quota t).totalC ≤
      2 ^ (k + 1) * r
  rw [t1RunAt]
  exact hrun.trans (Nat.mul_le_mul_right r hcountPow)

theorem t1RunAt_totalD_le_of_quota
    (c : Code) (cDesc cSparse n k epsilon quota t : Nat) :
    let s := t1RunAt c cDesc cSparse n k epsilon quota t
    s.totalD ≤ 2 ^ k := by
  dsimp only
  let events :=
    t1MarkingEventStage c n k epsilon
      (epsilon + logSlack cDesc n) t
  have hrun :=
    t1RunFromEvents_totalD_le cSparse n k epsilon
      quota (t1InitialRunState n k epsilon) events
  have hcount :=
    t1MarkingEventStage_d_count_le c n k epsilon
      (epsilon + logSlack cDesc n) t
  have hD := t1DStage_length_lt c n k t
  dsimp [t1RunAt, events, t1InitialRunState] at hrun ⊢
  omega

theorem t1RunAt_totalD_le
    (c : Code) (cDesc cSparse n k epsilon t : Nat) :
    let quota := 2 ^ (k - epsilon)
    let s := t1RunAt c cDesc cSparse n k epsilon quota t
    s.totalD ≤ 2 ^ k := by
  exact t1RunAt_totalD_le_of_quota c cDesc cSparse n k epsilon
    (2 ^ (k - epsilon)) t

theorem t1RunAt_saturation_charge
    (c : Code) (cDesc cSparse n k epsilon t : Nat) :
    let quota := 2 ^ (k - epsilon)
    let s := t1RunAt c cDesc cSparse n k epsilon quota t
    s.saturation * 2 ^ (k - epsilon) ≤ s.totalC + s.totalD := by
  dsimp only
  have hcharge :=
    t1RunAt_charge_spec c cDesc cSparse n k epsilon t
  unfold T1RunChargeInvariant T1RunQuotaChargeInvariant at hcharge
  omega

theorem t1RunAt_t1_rebuild_count_lt
    (V : Map) (c : Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse cRun, ∀ n k epsilon t,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      let quota := 2 ^ (k - epsilon)
      let s := t1RunAt c cDesc cSparse n k epsilon quota t
      s.external + s.saturation <
        2 ^ (epsilon + logSlack cRun n) := by
  intro cDesc
  obtain ⟨c0, cSparse, hC⟩ :=
    t1RunAt_totalC_le V c hc cDesc
  obtain ⟨cRun, hcount⟩ :=
    t1_change_count_arith cDesc cSparse
  refine ⟨c0, cSparse, cRun, ?_⟩
  intro n k epsilon t hc0 hepsilon hkn
  let quota := 2 ^ (k - epsilon)
  let s := t1RunAt c cDesc cSparse n k epsilon quota t
  apply hcount n k epsilon s.external s.saturation
    s.totalC s.totalD hepsilon hkn
  · exact t1RunAt_external_rebuilds_le
      c cDesc cSparse n k epsilon t
  · exact hC n k epsilon t hc0 hepsilon hkn
  · exact t1RunAt_totalD_le
      c cDesc cSparse n k epsilon t
  · exact t1RunAt_saturation_charge
      c cDesc cSparse n k epsilon t

/-- Every ordinal already present in the reachable version list fits in the
uniform fixed-width address supplied by the rebuild-count theorem. -/
theorem t1RunAt_version_lt_width
    (V : Map) (c : Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse cRun, ∀ n k epsilon t version,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      version <
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon)) t).versions.length →
      version < 2 ^ (epsilon + logSlack cRun n) := by
  intro cDesc
  obtain ⟨c0, cSparse, cRun, hcount⟩ :=
    t1RunAt_t1_rebuild_count_lt V c hc cDesc
  refine ⟨c0, cSparse, cRun, ?_⟩
  intro n k epsilon t version hc0 hepsilon hkn hversion
  have hlength :=
    t1RunAt_versions_length c cDesc cSparse n k epsilon
      (2 ^ (k - epsilon)) t
  have hcount' := hcount n k epsilon t hc0 hepsilon hkn
  omega

end Kolmogorov
