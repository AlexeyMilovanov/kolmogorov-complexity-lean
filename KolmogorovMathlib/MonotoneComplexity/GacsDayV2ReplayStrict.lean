import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ShapeStrict

/-!
# Strict V2 certificate on `GrayTailStateV2` (blueprint A3/A6)

The wide-block certificate ported onto the blueprint-faithful `GrayTailStateV2`
(`GrayTailRoundV2` rounds).  The harvest chain reads the stored `fineEnd`
(= `blockAnchor + L`), so it needs no `L` parameter.  Content mirrors the
`GrayTailState`-based `GrayChargedBlockTailCertified`.
-/

namespace Kolmogorov

/-- The snapshot `s` of a round `p` frozen after the rounds `earlier` is admissible: the empty
snapshot `none` only when no round precedes, and a time `u` only when it precedes the round's
own exchange and follows the exchange of every earlier round. -/
def GrayTailSnapOKV2 {n b : ℕ} (earlier : List (GrayTailRoundV2 n b))
    (p : GrayTailRoundV2 n b) (s : Option ℕ) : Prop :=
  (s = none → earlier = []) ∧
  ∀ u, s = some u → u < p.serverTime ∧ ∀ r ∈ earlier, r.serverTime ≤ u

/-- The per-round snapshot harvest chain on `GrayTailRoundV2` (uses stored
`fineEnd`): every frozen round's unavailable list is `A` plus the harvest of
its slots at an admissible snapshot. -/
def GrayTailHarvestChainV2 {n b : ℕ} (nn : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (frozen : List (GrayTailRoundV2 n b)) : Prop :=
  ∀ k : ℕ, ∀ hk : k < frozen.length, ∃ s : Option ℕ,
    GrayTailSnapOKV2 (frozen.take k) (frozen[k]'hk) s ∧
    (frozen[k]'hk).unavailable =
      A ++ grayHarvest (n := n) (b := b) (frozen[k]'hk).fineEnd
        (frozen[k]'hk).slots nn (grayHarvestSnapshot sm s)

/-- The empty list of V2 rounds is a harvest chain. -/
lemma grayTailHarvestChainV2_nil {n b : ℕ} (nn : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) :
    GrayTailHarvestChainV2 (n := n) (b := b) nn A sm [] := by
  intro k hk; simp at hk

/-- Appending a round whose snapshot fits the chain and whose unavailable set is the harvest of
that snapshot keeps the V2 harvest chain. -/
lemma grayTailHarvestChainV2_append {n b nn : ℕ} {A : Allocation}
    {sm : ℕ → FamilyServerMove} {frozen : List (GrayTailRoundV2 n b)}
    {p : GrayTailRoundV2 n b} {s : Option ℕ}
    (hchain : GrayTailHarvestChainV2 nn A sm frozen)
    (hs : GrayTailSnapOKV2 frozen p s)
    (hp : p.unavailable =
      A ++ grayHarvest (n := n) (b := b) p.fineEnd p.slots nn
        (grayHarvestSnapshot sm s)) :
    GrayTailHarvestChainV2 nn A sm (frozen ++ [p]) := by
  intro k hk
  have hklen : k < frozen.length + 1 := by simpa using hk
  by_cases hkf : k < frozen.length
  · have hget : (frozen ++ [p])[k]'hk = frozen[k]'hkf :=
      List.getElem_append_left hkf
    have htake : (frozen ++ [p]).take k = frozen.take k :=
      List.take_append_of_le_length (le_of_lt hkf)
    obtain ⟨s', hs', heq⟩ := hchain k hkf
    refine ⟨s', ?_, ?_⟩
    · rw [htake, hget]
      exact hs'
    · rw [hget]
      exact heq
  · have hke : k = frozen.length := by omega
    subst hke
    have hget : (frozen ++ [p])[frozen.length]'hk = p := by
      rw [List.getElem_append_right (Nat.le_refl _)]; simp
    have htake : (frozen ++ [p]).take frozen.length = frozen := List.take_left
    refine ⟨s, ?_, ?_⟩
    · rw [htake, hget]
      exact hs
    · rw [hget]
      exact hp

/-- The predecessor's exchange is an admissible snapshot of a round frozen
later, when the earlier rounds are chronological. -/
lemma grayTailSnapOKV2_pred {n b : ℕ} {frozen : List (GrayTailRoundV2 n b)}
    {p : GrayTailRoundV2 n b}
    (hchrono : ∀ i j, ∀ hi : i < frozen.length, ∀ hj : j < frozen.length,
      i < j → (frozen[i]'hi).serverTime < (frozen[j]'hj).serverTime)
    (hlt : ∀ r ∈ frozen, r.serverTime < p.serverTime) :
    GrayTailSnapOKV2 frozen p
      (Option.map GrayTailRoundV2.serverTime frozen.getLast?) := by
  refine ⟨?_, ?_⟩
  · intro hnone
    cases h : frozen with
    | nil => rfl
    | cons x xs =>
        rw [h] at hnone
        simp at hnone
  · intro u hu
    obtain ⟨l, hl, hlu⟩ := Option.map_eq_some_iff.mp hu
    have hne : frozen ≠ [] := by
      intro h
      rw [h] at hl
      simp at hl
    have hlen : 0 < frozen.length := List.length_pos_of_ne_nil hne
    have hlast : frozen.getLast? = some (frozen[frozen.length - 1]'(by omega)) := by
      rw [List.getLast?_eq_getElem?]
      exact List.getElem?_eq_getElem (by omega)
    rw [hlast] at hl
    have hlEq : l = frozen[frozen.length - 1]'(by omega) := by
      simpa using hl.symm
    have hlmem : l ∈ frozen := by
      rw [hlEq]
      exact List.getElem_mem _
    refine ⟨?_, ?_⟩
    · rw [← hlu]
      exact hlt l hlmem
    · intro r hr
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      rw [← hlu, hlEq]
      rcases Nat.lt_or_ge i (frozen.length - 1) with hlt' | hge
      · exact le_of_lt (hchrono i (frozen.length - 1) hi (by omega) hlt')
      · have hie : i = frozen.length - 1 := by omega
        subst hie
        exact le_refl _

/-- The strict invariant of a V2 block-tail state: its shape, that its clock equals `t`, that
the frozen rounds form a harvest chain, that the unavailable set is exactly the allocation plus
the harvest of the current slots, that the number of frozen rounds respects the advantage bound,
and that every frozen round carries the scheduled depths. -/
structure GrayChargedBlockTailCertifiedV2 {n b : Nat}
    (q L e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (t : Nat) (st : GrayTailStateV2 n b) : Prop where
  shape : GrayBlockTailShapeV2 q L st
  time_eq : st.time = t
  frozen_chain : GrayTailHarvestChainV2 n A sm st.frozen
  unavailable_snap :
    st.unavailable =
      A ++ grayHarvest (grayTailRoundDelta q L e st.frozen.length)
        st.slots n
        (grayHarvestSnapshot sm
          (Option.map GrayTailRoundV2.serverTime st.frozen.getLast?))
  frozen_bound : st.frozen.length <= grayChargedAdvantageRoundCount q ∧
    (st.done = false -> st.frozen.length < grayChargedAdvantageRoundCount q)
  round_valid : forall p, p ∈ st.frozen ->
    p.roundIndex < st.frozen.length ∧
    p.blockAnchor = grayTailRoundEps q L e p.roundIndex ∧
    p.childEps = p.blockAnchor + graySpendSpan q ∧
    p.fineEnd = grayTailRoundDelta q L e p.roundIndex ∧
    p.serverTime < t ∧
    p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove p.fineEnd p.slots (sm p.serverTime)) ∧
    grayChargedBlockGoalAtB q L e p.roundIndex
      p.slots.length p.unavailable p.move
        (grayTailLocalServerMove p.fineEnd p.slots (sm p.serverTime)) = true ∧
    p.slots.Nodup ∧
    forall s, s ∈ p.slots -> grayInAdvBlock q L p.roundIndex s.2.2.val
  frozen_index : forall k, forall hk : k < st.frozen.length,
    (st.frozen[k]'hk).roundIndex = k
  frozen_chrono : forall i j, forall hi : i < st.frozen.length,
    forall hj : j < st.frozen.length, i < j ->
      (st.frozen[i]'hi).serverTime < (st.frozen[j]'hj).serverTime

/-- The initial V2 block tail state is certified at time `0`. -/
lemma grayChargedBlockTailCertifiedV2_initial {n b : Nat}
    (q L a e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove) :
    GrayChargedBlockTailCertifiedV2 q L e A sm 0
      (grayChargedBlockTailInitialStateV2 n b a e q L A) := by
  have hbound : (grayChargedBlockTailInitialStateV2 n b a e q L A).frozen.length
        <= grayChargedAdvantageRoundCount q ∧
      ((grayChargedBlockTailInitialStateV2 n b a e q L A).done = false ->
        (grayChargedBlockTailInitialStateV2 n b a e q L A).frozen.length
          < grayChargedAdvantageRoundCount q) := by
    dsimp [grayChargedBlockTailInitialStateV2]
    exact ⟨Nat.zero_le _, fun _ => grayChargedAdvantageRoundCount_pos q⟩
  refine ⟨grayBlockTailShapeV2_initial n b a e q L A, rfl, ?_, ?_, hbound, ?_, ?_, ?_⟩
  · intro k hk; simp [grayChargedBlockTailInitialStateV2] at hk
  · simp [grayChargedBlockTailInitialStateV2, grayHarvestSnapshot, grayHarvest_nil]
  · intro p hp; simp [grayChargedBlockTailInitialStateV2] at hp
  · intro k hk; simp [grayChargedBlockTailInitialStateV2] at hk
  · intro i j hi hj hij; simp [grayChargedBlockTailInitialStateV2] at hj

/-- Freeze one accepted wide-block round into the strict V2 certificate. -/
lemma grayChargedBlockTailCertifiedV2_freeze {n b q L e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (hst : GrayChargedBlockTailCertifiedV2 q L e A sm t st)
    (hlimit : st.frozen.length < grayChargedAdvantageRoundCount q)
    (done : Bool) (p : GrayTailRoundV2 n b)
    (hpSlots : p.slots = st.slots)
    (hpIndex : p.roundIndex = st.frozen.length)
    (hpBlockAnchor : p.blockAnchor = grayTailRoundEps q L e p.roundIndex)
    (hpChildEps : p.childEps = p.blockAnchor + graySpendSpan q)
    (hpFineEnd : p.fineEnd = grayTailRoundDelta q L e p.roundIndex)
    (hpTime : p.serverTime = t)
    (hpAllocated : p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove p.fineEnd p.slots (sm p.serverTime)))
    (hpUnavailable : p.unavailable = st.unavailable)
    (hpGoal : grayChargedBlockGoalAtB q L e p.roundIndex
      p.slots.length p.unavailable p.move
        (grayTailLocalServerMove p.fineEnd p.slots (sm p.serverTime)) = true)
    (hpNodup : p.slots.Nodup)
    (hpRange : forall s, s ∈ p.slots -> grayInAdvBlock q L p.roundIndex s.2.2.val)
    (next : List (GrayTailSlot n b)) (hnext : next.Nodup)
    (hnextRange : forall s, s ∈ next ->
      grayInAdvBlock q L (st.frozen.length + 1) s.2.2.val)
    (anchoringSlots : List (GrayTailSlot n b))
    (history : FamilyGameHistory)
    (hdone_bound : done = false ->
      (st.frozen ++ [p]).length < grayChargedAdvantageRoundCount q) :
    GrayChargedBlockTailCertifiedV2 q L e A sm (t + 1)
      ({ time := t + 1
         roundStart := t + 1
         done := done
         frozen := st.frozen ++ [p]
         unavailable := A ++
           grayHarvest (grayTailRoundDelta q L e (st.frozen ++ [p]).length)
             next n (sm t)
         slots := next
         anchoringSlots := anchoringSlots
         history := history } : GrayTailStateV2 n b) := by
  have hbound_next : (st.frozen ++ [p]).length <= grayChargedAdvantageRoundCount q ∧
      (done = false -> (st.frozen ++ [p]).length < grayChargedAdvantageRoundCount q) := by
    refine ⟨?_, hdone_bound⟩
    rw [List.length_append, List.length_singleton]; omega
  have hpSnap : p.unavailable =
      A ++ grayHarvest p.fineEnd p.slots n
        (grayHarvestSnapshot sm
          (Option.map GrayTailRoundV2.serverTime st.frozen.getLast?)) := by
    rw [hpUnavailable, hpFineEnd, hpIndex, hpSlots]
    exact hst.unavailable_snap
  have hsOK : GrayTailSnapOKV2 st.frozen p
      (Option.map GrayTailRoundV2.serverTime st.frozen.getLast?) := by
    refine grayTailSnapOKV2_pred hst.frozen_chrono ?_
    intro r hr
    rw [hpTime]
    exact (hst.round_valid r hr).2.2.2.2.1
  refine ⟨grayBlockTailShapeV2_freeze hst.shape (t + 1) (t + 1)
      done p hpSlots next hnext hnextRange anchoringSlots history _,
    rfl, ?_, ?_, hbound_next, ?_, ?_, ?_⟩
  · exact grayTailHarvestChainV2_append hst.frozen_chain hsOK hpSnap
  · simp only [List.getLast?_concat, Option.map_some, grayHarvestSnapshot,
      hpTime]
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hst.round_valid r hr with
        ⟨hidx, hba, hce, hfe, htime, halloc, hgoal, hnodup, hrange⟩
      refine ⟨?_, hba, hce, hfe, ?_, halloc, hgoal, hnodup, hrange⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · omega
    · have hrp : r = p := by simpa using hr
      subst r
      refine ⟨?_, hpBlockAnchor, hpChildEps, hpFineEnd, ?_, hpAllocated,
        hpGoal, hpNodup, hpRange⟩
      · simp only [List.length_append, List.length_singleton, hpIndex]; omega
      · omega
  · intro k hk
    have hklen : k < st.frozen.length + 1 := by simpa using hk
    by_cases hkf : k < st.frozen.length
    · rw [List.getElem_append_left hkf]; exact hst.frozen_index k hkf
    · have hke : k = st.frozen.length := by omega
      subst hke
      have hgetp : (st.frozen ++ [p])[st.frozen.length]'hk = p := by
        rw [List.getElem_append_right (Nat.le_refl _)]; simp
      rw [hgetp, hpIndex]
  · intro i j hi hj hij
    have hjlen : j < st.frozen.length + 1 := by simpa using hj
    by_cases hjf : j < st.frozen.length
    · have hif : i < st.frozen.length := by omega
      rw [List.getElem_append_left hif, List.getElem_append_left hjf]
      exact hst.frozen_chrono i j hif hjf hij
    · have hje : j = st.frozen.length := by omega
      subst hje
      have hif : i < st.frozen.length := by omega
      rw [List.getElem_append_left hif]
      have hgetp : (st.frozen ++ [p])[st.frozen.length]'hj = p := by
        rw [List.getElem_append_right (Nat.le_refl _)]; simp
      rw [hgetp, hpTime]
      have hmem : st.frozen[i]'hif ∈ st.frozen := List.getElem_mem hif
      exact (hst.round_valid _ hmem).2.2.2.2.1

/-- **The strict V2 certificate is preserved by the wide-block step.** -/
lemma grayChargedBlockTailCertifiedV2_step {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b} (sigma : FamilyStrategyScheme)
    (hst : GrayChargedBlockTailCertifiedV2 q L e A sm t st) :
    GrayChargedBlockTailCertifiedV2 q L e A sm (t + 1)
      (grayChargedBlockTailStepV2 q L a e sigma A st (sm t)) := by
  have hrestate (done : Bool) (hdone_eq : done = st.done) (history : FamilyGameHistory) :
      GrayChargedBlockTailCertifiedV2 q L e A sm (t + 1)
        ({ time := st.time + 1
           roundStart := st.roundStart
           done := done
           frozen := st.frozen
           unavailable := st.unavailable
           slots := st.slots
           anchoringSlots := st.anchoringSlots
           history := history } : GrayTailStateV2 n b) := by
    have hbound : st.frozen.length <= grayChargedAdvantageRoundCount q ∧
        (done = false -> st.frozen.length < grayChargedAdvantageRoundCount q) := by
      refine ⟨hst.frozen_bound.1, fun hnotdone => ?_⟩
      subst done; exact hst.frozen_bound.2 hnotdone
    refine ⟨?_, by simp [hst.time_eq], hst.frozen_chain,
      hst.unavailable_snap, hbound, ?_, hst.frozen_index, hst.frozen_chrono⟩
    · exact ⟨hst.shape.frozen_nodup, hst.shape.frozen_round_range,
        hst.shape.slots_nodup, hst.shape.slots_range⟩
    intro p hp
    rcases hst.round_valid p hp with
      ⟨hidx, hba, hce, hfe, htime, halloc, hgoal, hnodup, hrange⟩
    exact ⟨hidx, hba, hce, hfe, by omega, halloc, hgoal, hnodup, hrange⟩
  by_cases hd : st.done = true
  · simpa [grayChargedBlockTailStepV2, hd] using hrestate st.done rfl st.history
  · by_cases hs : st.slots.isEmpty = true
    · simpa [grayChargedBlockTailStepV2, hd, hs] using
        hrestate st.done rfl st.history
    · by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
        st.slots.length st.unavailable
        (grayBlockCurrentMoveV2 q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t)) = true
      · have hlimit : st.frozen.length < grayChargedAdvantageRoundCount q :=
          hst.frozen_bound.2 (Bool.eq_false_of_not_eq_true hd)
        let p : GrayTailRoundV2 n b :=
          { serverTime := t
            roundIndex := List.length st.frozen
            blockAnchor := grayTailRoundEps q L e (List.length st.frozen)
            childEps := grayTailRoundEps q L e (List.length st.frozen) + graySpendSpan q
            fineEnd := grayTailRoundDelta q L e (List.length st.frozen)
            slots := st.slots
            move := grayBlockCurrentMoveV2 q L e sigma st
            allocated :=
              grayTailLocalAllocatedList (grayTailLocalServerMove (grayTailRoundDelta q L e
              (List.length st.frozen)) st.slots (sm t))
            unavailable := st.unavailable }
        let candidates :=
          grayBlockNextSlots q L e (grayChargedSourceCount a e) (st.frozen
          ++ [p]).length (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) A ((st.frozen
          ++ [p]).map GrayTailRoundV2.toV1) (sm t)
        let done :=
          grayTailGlobalQuarterB (grayChargedSourceCount a e) (grayTailNextSlots e
          (grayChargedSourceCount a e) (st.frozen ++ [p]).length (dyadicScale e - dyadicScale e / (6
          * halfAmplification q)) A ((st.frozen ++ [p]).map GrayTailRoundV2.toV1) (sm t))
          || decide (grayChargedAdvantageRoundCount q <= (st.frozen ++ [p]).length)
        have hdone_bound : done = false -> (st.frozen ++ [p]).length
          < grayChargedAdvantageRoundCount q := by
          intro hnd
          have htr := (Bool.or_eq_false_iff.mp hnd).2
          have hge := of_decide_eq_false htr
          omega
        have hstep : grayChargedBlockTailStepV2 q L a e sigma A st (sm t) =
          { time := t + 1
            roundStart := t + 1
            done := done
            frozen := st.frozen ++ [p]
            unavailable := A ++
              grayHarvest (grayTailRoundDelta q L e (st.frozen ++ [p]).length)
                candidates n (sm t)
            slots := candidates
            anchoringSlots := []
            history := ([], []) } := by
          dsimp [grayChargedBlockTailStepV2, p, done, candidates]
          rw [show st.done = false from Bool.eq_false_of_not_eq_true hd]
          rw [show st.slots.isEmpty = false from Bool.eq_false_of_not_eq_true hs]
          rw [hst.time_eq]
          dsimp
          rw [hg]
          dsimp
        rw [hstep]
        exact grayChargedBlockTailCertifiedV2_freeze hst hlimit done p
          rfl rfl (by dsimp [p]) (by dsimp [p]) (by dsimp [p])
          rfl (by dsimp [p])
          rfl (by dsimp [p]; exact hg)
          hst.shape.slots_nodup (fun s hs' => hst.shape.slots_range s hs')
          candidates (grayBlockNextSlots_nodup _ _ _ _ _ _ _ _ _)
          (fun s hs' => by
            have := grayBlockNextSlots_mem_range hs'
            simpa [List.length_append] using this)
          []
          ([], [])
          hdone_bound
      · simpa [grayChargedBlockTailStepV2, hd, hs, hg] using
          hrestate st.done rfl
            (st.history.1 ++ [grayBlockCurrentMoveV2 q L e sigma st],
              st.history.2 ++
                [grayTailLocalServerMove
                  (grayTailRoundDelta q L e st.frozen.length)
                  st.slots (sm t)])

/-- The strict V2 block-tail fold: `grayChargedBlockTailStepV2` folded over a finite server history
from the initial state. -/
def grayChargedBlockTailFoldV2 {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (history : List FamilyServerMove) : GrayTailStateV2 n b :=
  history.foldl (grayChargedBlockTailStepV2 q L a e sigma A)
    (grayChargedBlockTailInitialStateV2 n b a e q L A)

/-- The V2 block tail state after replaying the first `t` moves of the server play `sm`. -/
def grayChargedBlockTailStateAtV2 {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : GrayTailStateV2 n b :=
  grayChargedBlockTailFoldV2 q L a e sigma A (grayTailServerPrefix sm t)

/-- The V2 block tail state at time `t + 1` is one step applied to the state at time `t`. -/
lemma grayChargedBlockTailStateAtV2_succ {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    grayChargedBlockTailStateAtV2 (n := n) (b := b) q L a e sigma A sm (t + 1) =
      grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedBlockTailStateAtV2 q L a e sigma A sm t) (sm t) := by
  simp [grayChargedBlockTailStateAtV2, grayChargedBlockTailFoldV2,
    grayTailServerPrefix_succ]

/-- Every state of a V2 block tail run is certified. -/
theorem grayChargedBlockTailCertifiedV2_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedBlockTailCertifiedV2 q L e A sm t
      (grayChargedBlockTailStateAtV2 (n := n) (b := b) q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayChargedBlockTailCertifiedV2_initial q L a e A sm
  | succ t ih =>
      rw [grayChargedBlockTailStateAtV2_succ]
      exact grayChargedBlockTailCertifiedV2_step sigma ih

/-- The source-son invariant for the strict V2 state. -/
structure GrayTailSourceInvariantV2 {n b : Nat} (used : Nat)
    (st : GrayTailStateV2 n b) : Prop where
  current : forall s, s ∈ st.slots -> s.2.1.val < used
  frozen : forall p, p ∈ st.frozen -> forall s, s ∈ p.slots -> s.2.1.val < used

/-- A V2 block tail step preserves the source invariant. -/
lemma grayChargedBlockSourceInvariantV2_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove)
    (hst : GrayTailSourceInvariantV2 (grayChargedSourceCount a e) st) :
    GrayTailSourceInvariantV2 (grayChargedSourceCount a e)
      (grayChargedBlockTailStepV2 q L a e sigma A st sm) := by
  unfold grayChargedBlockTailStepV2
  by_cases hd : st.done = true
  · simp only [hd, ↓reduceIte]; exact ⟨hst.current, hst.frozen⟩
  · by_cases hs : st.slots.isEmpty = true
    · simp only [hd, hs, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hst.current, hst.frozen⟩
    · by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots sm) = true
      · simp only [hd, hs, hg, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · intro s hs'; exact grayBlockNextSlots_source hs'
        · intro pp hpp s hs'
          rcases List.mem_append.mp hpp with hpp | hpp
          · exact hst.frozen pp hpp s hs'
          · simp only [List.mem_singleton] at hpp
            subst pp
            exact hst.current s (by simpa using hs')
      · simp only [hd, hs, hg, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hst.current, hst.frozen⟩

/-- Every state of a V2 block tail run satisfies the source invariant. -/
theorem grayChargedBlockSourceInvariantV2_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailSourceInvariantV2 (grayChargedSourceCount a e)
      (grayChargedBlockTailStateAtV2 (n := n) (b := b) q L a e sigma A sm t) := by
  induction t with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro s hs
        change s ∈ grayAdvBlockSlots n b (grayChargedSourceCount a e) q L 0 at hs
        exact (grayAdvBlockSlots_mem hs).1
      · intro p hp
        simp [grayChargedBlockTailStateAtV2, grayChargedBlockTailFoldV2,
          grayChargedBlockTailInitialStateV2] at hp
  | succ t ih =>
      rw [grayChargedBlockTailStateAtV2_succ]
      exact grayChargedBlockSourceInvariantV2_step q L a e sigma A _ (sm t) ih

end Kolmogorov
