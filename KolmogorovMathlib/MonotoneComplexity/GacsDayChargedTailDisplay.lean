import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailLayout
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.EntryMonotonicity
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.Part02

/-!
# The display layer of the charged tail move

The charged tail controller displays the moves of its live slots two levels
below the owning outer root (`graftTwoLevel`).  This file collects the purely
*layout* facts about that display, i.e. the ones that mention no rung, no charge
budget, no round schedule and no closure leaf:

* requests survive the display (`grayChargedTailFamilyMove_current_req`): the
  request the outer move carries at the grandson node `s.2.1 :: s.2.2 :: x` is
  exactly the request the slot's own move carries at `x`;
* the display never manufactures a request strictly between `0` and the fine
  scale (`grayCharged*_avoidsSmall`): if every displayed entry avoids small
  requests, so do the grafted son and root requests.

Both families are used by the V1 and the V2 round controllers alike, so they
live in the layout layer rather than inside either controller's closure.
-/

namespace Kolmogorov

/-! ### Small-request avoidance through the two-level graft -/

/-- A two-level graft avoids requests below `delta` when its root, its son values and all grafted
moves do. -/
theorem grayCharged_requestAvoidsSmall_graftTwoLevel
    {b : Nat} {root delta : Rat} {son : Nat -> Rat}
    {g : Nat -> Nat -> ClientMove}
    (hroot : root = 0 ∨ delta <= root)
    (hson : ∀ c < b, son c = 0 ∨ delta <= son c)
    (hg : ∀ c < b, ∀ c' < b,
      requestAvoidsSmall delta (g c c')) :
    requestAvoidsSmall delta (graftTwoLevel root b son g) := by
  intro x
  cases x with
  | nil =>
      rw [getReq_graftTwoLevel_root]
      exact hroot
  | cons c x =>
      cases x with
      | nil =>
          by_cases hc : c < b
          · rw [getReq_graftTwoLevel_son hc]
            exact hson c hc
          · simp only [not_lt] at hc
            rw [getReq_graftTwoLevel_of_ge hc]
            exact Or.inl rfl
      | cons c' y =>
          by_cases hc : c < b
          · by_cases hc' : c' < b
            · rw [getReq_graftTwoLevel_grandson hc hc']
              exact hg c hc c' hc' y
            · simp only [not_lt] at hc'
              rw [getReq_graftTwoLevel_of_son_ge hc hc']
              exact Or.inl rfl
          · simp only [not_lt] at hc
            rw [getReq_graftTwoLevel_of_ge hc]
            exact Or.inl rfl

/-- A move assembled for a slot from entries that avoid small requests again avoids them. -/
lemma grayCharged_entryMove_avoidsSmall {n b : Nat} {delta : Rat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hall : ∀ pr ∈ entries, requestAvoidsSmall delta pr.2)
    (slot : GrayTailSlot n b) :
    requestAvoidsSmall delta (grayTailEntryMove entries slot) := by
  unfold grayTailEntryMove
  cases hfind : entries.find? (fun p => decide (p.1 = slot)) with
  | none =>
      intro x
      simp [getReq]
  | some pr =>
      have hmem : pr ∈ entries := List.mem_of_find?_eq_some hfind
      simpa using hall pr hmem

/-- If the frozen moves and the current move avoid requests below `delta`, so does every entry of
the state. -/
lemma grayChargedEntries_all_avoidsSmall {n b : Nat} {delta : Rat}
    {frozen : GrayTailFrozen n b} {slots : List (GrayTailSlot n b)}
    {current : FamilyClientMove}
    (hfrozen : ∀ p ∈ frozen, ∀ j < p.slots.length,
      requestAvoidsSmall delta (familyClientMoveAt p.move j))
    (hcur : ∀ j < slots.length,
      requestAvoidsSmall delta (familyClientMoveAt current j)) :
    ∀ pr ∈ grayTailEntries frozen slots current,
      requestAvoidsSmall delta pr.2 := by
  intro pr hpr
  rw [grayTailEntries, List.mem_append] at hpr
  rcases hpr with hpr | hpr
  · rw [grayTailFrozenEntries, List.mem_flatMap] at hpr
    obtain ⟨p, hp, hpr⟩ := hpr
    rw [grayTailSlotEntries, List.mem_ofFn] at hpr
    obtain ⟨j, hj⟩ := hpr
    subst hj
    exact hfrozen p hp j.val j.isLt
  · rw [grayTailSlotEntries, List.mem_ofFn] at hpr
    obtain ⟨j, hj⟩ := hpr
    subst hj
    exact hcur j.val j.isLt

/-- A son base built from entries that avoid small requests is either `0` or at least `delta`. -/
lemma grayChargedSonBase_avoidsSmall {n b : Nat} {delta : Rat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hpos_delta : 0 < delta)
    (hall : ∀ pr ∈ entries, requestAvoidsSmall delta pr.2)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase entries i c = 0 ∨
      delta <= grayTailSonBase entries i c := by
  induction entries with
  | nil =>
      simp [grayTailSonBase]
  | cons p rest ih =>
      have hhead : requestAvoidsSmall delta p.2 := hall p (by simp)
      have htail : ∀ pr ∈ rest, requestAvoidsSmall delta pr.2 :=
        fun pr hpr => hall pr (by simp [hpr])
      have ih_res := ih htail
      unfold grayTailSonBase
      simp only [List.foldr_cons]
      change
        (if p.1.1 = i ∧ p.1.2.1 = c then
            getReq p.2 [] + grayTailSonBase rest i c
          else grayTailSonBase rest i c) = 0 ∨
        delta <= (if p.1.1 = i ∧ p.1.2.1 = c then
          getReq p.2 [] + grayTailSonBase rest i c
          else grayTailSonBase rest i c)
      split_ifs with hmatch
      · rcases hhead [] with h0 | hge
        · rw [h0, zero_add]
          exact ih_res
        · rcases ih_res with h0' | hge'
          · rw [h0', add_zero]
            exact Or.inr hge
          · have hnonneg : 0 <= grayTailSonBase rest i c := by
              linarith
            exact Or.inr (by linarith)
      · exact ih_res

/-- A son request built from entries that avoid small requests is either `0` or at least `delta`. -/
lemma grayChargedBaseSonRequest_avoidsSmall
    {n b e : Nat} {delta : Rat}
    (hpos_delta : 0 < delta)
    (hdelta_e : delta <= dyadicScale e)
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hall : ∀ pr ∈ entries, requestAvoidsSmall delta pr.2)
    (threshold : Rat) (i : Fin n) (c : Fin b) :
    grayTailSonRequest threshold (dyadicScale e) entries i c = 0 ∨
      delta <= grayTailSonRequest threshold (dyadicScale e) entries i c := by
  unfold grayTailSonRequest
  by_cases htr : threshold < grayTailSonBase entries i c
  · dsimp only
    rw [ite_eq_left htr]
    exact Or.inr hdelta_e
  · dsimp only
    rw [ite_eq_right htr]
    exact grayChargedSonBase_avoidsSmall hpos_delta hall i c

/-- A charged son request built from entries that avoid small requests is either `0` or at least
`delta`. -/
lemma grayChargedSonRequest_avoidsSmall
    {n b e : Nat} {delta : Rat}
    (hpos : 0 < delta) (hdelta_e : delta <= dyadicScale e)
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hall : ∀ pr ∈ entries, requestAvoidsSmall delta pr.2)
    (source : Nat) (threshold : Rat) (i : Fin n) (c : Fin b) :
    grayChargedSonRequest source threshold (dyadicScale e) entries i c = 0 ∨
      delta <= grayChargedSonRequest source threshold
        (dyadicScale e) entries i c := by
  by_cases hc : c.val < source
  · rw [grayChargedSonRequest_source i c hc]
    exact grayChargedBaseSonRequest_avoidsSmall
      hpos hdelta_e hall threshold i c
  · rw [grayChargedSonRequest_spare i c (Nat.le_of_not_gt hc)]
    exact grayChargedSonBase_avoidsSmall hpos hall i c

/-- A charged root request built from entries that avoid small requests is either `0` or at least
`delta`. -/
lemma grayChargedRootRequest_avoidsSmall
    {n b e : Nat} {delta : Rat}
    (hpos : 0 < delta) (hdelta_e : delta <= dyadicScale e)
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hall : ∀ pr ∈ entries, requestAvoidsSmall delta pr.2)
    (source : Nat) (threshold : Rat) (i : Fin n) :
    grayChargedRootRequest source threshold (dyadicScale e) entries i = 0 ∨
      delta <=
        grayChargedRootRequest source threshold (dyadicScale e) entries i := by
  unfold grayChargedRootRequest
  have hson : forall c : Fin b,
      grayChargedSonRequest source threshold
          (dyadicScale e) entries i c = 0 ∨
        delta <= grayChargedSonRequest source threshold
          (dyadicScale e) entries i c :=
    fun c => grayChargedSonRequest_avoidsSmall
      hpos hdelta_e hall source threshold i c
  by_cases hsum : 0 < ∑ c : Fin b,
      grayChargedSonRequest source threshold
        (dyadicScale e) entries i c
  · exact Or.inr
      (sum_ge_of_forall_zero_or_ge
        Finset.univ _ delta hsum (fun c _ => hson c))
  · have hnonneg : forall c : Fin b,
        0 <= grayChargedSonRequest source threshold
          (dyadicScale e) entries i c := by
      intro c
      rcases hson c with hzero | hge
      · rw [hzero]
      · linarith
    have hsumNonneg : 0 <= ∑ c : Fin b,
        grayChargedSonRequest source threshold
          (dyadicScale e) entries i c :=
      Finset.sum_nonneg (fun c _ => hnonneg c)
    exact Or.inl (by linarith)

/-! ### The displayed request of a live slot -/

/-- Below the node of an open slot, the displayed family move reproduces the current move of that
slot. -/
lemma grayChargedTailFamilyMove_current_req
    {n b source : Nat} {threshold eps : Rat}
    {frozen : GrayTailFrozen n b} {slots : List (GrayTailSlot n b)}
    {current : FamilyClientMove}
    (hkeys : (grayTailFrozenSlots frozen ++ slots).Nodup)
    (j : Fin slots.length) (x : GacsDayNode) :
    let s := slots.get j
    getFamilyReq
        (grayChargedTailFamilyMove source threshold eps frozen slots current)
        s.1.val (s.2.1.val :: s.2.2.val :: x) =
      getFamilyReq current j.val x := by
  dsimp only
  let entries := grayTailEntries frozen slots current
  let s := slots.get j
  have hfamily :
      familyClientMoveAt
          (grayChargedTailFamilyMove source threshold eps frozen slots current)
          s.1.val =
        graftTwoLevel
          (grayChargedRootRequest source threshold eps entries s.1)
          b
          (fun c => if hc : c < b then
            grayChargedSonRequest source threshold eps entries s.1 ⟨c, hc⟩
            else 0)
          (fun c c' => if hc : c < b then if hc' : c' < b then
            grayTailEntryMove entries (s.1, ⟨c, hc⟩, ⟨c', hc'⟩)
            else [] else []) := by
    unfold grayChargedTailFamilyMove familyClientMoveAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [s.1.isLt, entries]
  rw [getFamilyReq, hfamily]
  rw [getReq_graftTwoLevel_grandson s.2.1.isLt s.2.2.isLt]
  rw [dite_eq_left s.2.1.isLt, dite_eq_left s.2.2.isLt]
  unfold getFamilyReq
  apply congrArg (fun m => getReq m x)
  apply grayTailEntryMove_eq_of_mem
  · rw [map_fst_grayTailEntries]
    exact hkeys
  · change (slots.get j, familyClientMoveAt current j.val) ∈
      grayTailEntries frozen slots current
    rw [grayTailEntries, List.mem_append]
    right
    exact List.mem_ofFn.mpr ⟨j, rfl⟩

end Kolmogorov
