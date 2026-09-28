import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailResolutionExact
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFresh

/-!
# Pointwise bounds for frozen tail rounds

A controller round contains at most one slot below any fixed outer son.  This
turns the pointwise request window of the recursive family into the upper bound
on the one last call which is discarded in Day's reserve accounting.
-/

namespace Kolmogorov

private def grayTailSonKey {n b : Nat} (s : GrayTailSlot n b) :
    Fin n × Fin b := (s.1, s.2.1)

private lemma grayTailSonKeys_nodup {n b r : Nat}
    {slots : List (GrayTailSlot n b)} (hnodup : slots.Nodup)
    (hround : forall s, s ∈ slots -> s.2.2.val = r) :
    (slots.map grayTailSonKey).Nodup := by
  induction slots with
  | nil => simp
  | cons s rest ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨t, ht, hkey⟩ := List.mem_map.mp hmem
        apply hnodup.1
        have hfirst : t.1 = s.1 :=
          congrArg (fun z : Fin n × Fin b => z.1) hkey
        have hsecond : t.2.1 = s.2.1 :=
          congrArg (fun z : Fin n × Fin b => z.2) hkey
        have hthirdVal : t.2.2.val = s.2.2.val := by
          rw [hround t (by simp [ht]), hround s (by simp)]
        have hthird : t.2.2 = s.2.2 := Fin.ext hthirdVal
        have hts : t = s := Prod.ext hfirst (Prod.ext hsecond hthird)
        simpa [hts] using ht
      · apply ih hnodup.2
        intro t ht
        exact hround t (by simp [ht])

private lemma grayTailSlotEntryKeys_nodup {n b r : Nat}
    {slots : List (GrayTailSlot n b)} {move : FamilyClientMove}
    (hnodup : slots.Nodup)
    (hround : forall s, s ∈ slots -> s.2.2.val = r) :
    ((grayTailSlotEntries slots move).map
      (fun z => grayTailSonKey z.1)).Nodup := by
  have hkeys := grayTailSonKeys_nodup hnodup hround
  rw [← map_fst_grayTailSlotEntries slots move] at hkeys
  simpa only [List.map_map, Function.comp_def] using hkeys

private lemma grayTailSonBase_le_of_keys_nodup {n b : Nat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    {cap : Rat} (hcap0 : 0 <= cap)
    (hkeys : (entries.map (fun z => grayTailSonKey z.1)).Nodup)
    (hnonneg : forall z, z ∈ entries -> 0 <= getReq z.2 [])
    (hcap : forall z, z ∈ entries -> getReq z.2 [] <= cap)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase entries i c <= cap := by
  induction entries with
  | nil =>
      simpa [grayTailSonBase] using hcap0
  | cons z rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hkeys
      unfold grayTailSonBase
      simp only [List.foldr_cons]
      change (if z.1.1 = i ∧ z.1.2.1 = c then
        getReq z.2 [] + grayTailSonBase rest i c
        else grayTailSonBase rest i c) <= cap
      split_ifs with hsame
      · have hrestzero : grayTailSonBase rest i c = 0 := by
          apply grayTailSonBase_eq_zero_of_no_match
          intro w hw
          by_contra hnot
          push_neg at hnot
          apply hkeys.1
          apply List.mem_map.mpr
          refine ⟨w, hw, ?_⟩
          exact Prod.ext (hnot.1.trans hsame.1.symm)
            (hnot.2.trans hsame.2.symm)
        rw [hrestzero, add_zero]
        exact hcap z (by simp)
      · apply ih hkeys.2
        · intro w hw
          exact hnonneg w (by simp [hw])
        · intro w hw
          exact hcap w (by simp [hw])

/-- A round with unique outer-son keys inherits any pointwise request cap.
This is the common combinatorial part of both the robust and charged tail
certificates; the two controllers provide their request bounds differently. -/
theorem grayTailSonBase_le_of_slot_request_bounds {n b r : Nat}
    {slots : List (GrayTailSlot n b)} {move : FamilyClientMove}
    {cap : Rat} (hcap0 : 0 <= cap)
    (hnodup : slots.Nodup)
    (hround : forall s, s ∈ slots -> s.2.2.val = r)
    (hnonneg : forall j : Fin slots.length,
      0 <= getFamilyReq move j.val [])
    (hcap : forall j : Fin slots.length,
      getFamilyReq move j.val [] <= cap)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries slots move) i c <= cap := by
  apply grayTailSonBase_le_of_keys_nodup hcap0
    (grayTailSlotEntryKeys_nodup hnodup hround)
  · intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    have hj := hnonneg j
    unfold getFamilyReq at hj
    exact hj
  · intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    have hj := hcap j
    unfold getFamilyReq at hj
    exact hj

/-- A certified recursive round contributes at most one call-scale request
below a fixed outer son. -/
theorem grayTailRoundSonBase_le_callScale
    {n b q L e t : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {st : GrayTailState n b}
    (hcert : GrayTailCertified q L e A sm t st)
    {p : GrayTailRound n b} (hp : p ∈ st.frozen)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries p.slots p.move) i c <=
      dyadicScale (grayCallDepth q e) := by
  have hvalid := hcert.round_valid p hp
  have hgoal := familyRobustGrayGoalAtB.to_pointwise hvalid.2.2.2.2.1
  apply grayTailSonBase_le_of_keys_nodup
    (cap := dyadicScale (grayCallDepth q e))
    (dyadicScale_pos _).le
    (grayTailSlotEntryKeys_nodup hvalid.2.2.2.2.2.1
      hvalid.2.2.2.2.2.2)
  · apply grayTailSlotEntries_root_nonneg
      (kappa := halfAmplification q)
      (beta := (3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
      (epsDepth := p.epsDepth) (deltaDepth := p.epsDepth + L)
      (A := p.unavailable) (server :=
        grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime))
      (halfAmplification_pos q)
      (mul_nonneg (by norm_num) (dyadicScale_pos _).le)
    exact hgoal
  · intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    have hj := (familyPointwiseGrayAtB.component hgoal j.isLt).2
    unfold getFamilyReq at hj
    calc
      getReq (familyClientMoveAt p.move j.val) [] <=
          (4 / 3 : Rat) * ((3 / 4 : Rat) *
            dyadicScale (grayCallDepth q e)) := hj
      _ = dyadicScale (grayCallDepth q e) := by ring

/-- For a frozen round `p` of a certified gray-tail state, every son base
`grayTailSonBase (grayTailSlotEntries p.slots p.move) i c` is at most
`dyadicScale e / (24 * halfAmplification q)`. -/
theorem grayTailRoundSonBase_le_lastCap
    {n b q L e t : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {st : GrayTailState n b}
    (hcert : GrayTailCertified q L e A sm t st)
    {p : GrayTailRound n b} (hp : p ∈ st.frozen)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries p.slots p.move) i c <=
      dyadicScale e / (24 * halfAmplification q) := by
  exact le_trans (grayTailRoundSonBase_le_callScale hcert hp i c)
    (grayCallDepth_scale_bounds q e).2

end Kolmogorov
