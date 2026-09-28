import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.TailStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.FinalReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore

/-!
# The charged strategy keeps every client's root request inside its window

The charged client must end with a root request that is neither too small nor too large: between
`dyadicScale a / 2` and `dyadicScale a`. The lower half is the work of the spend passes.
`grayChargedRootIncrement` measures what a list of entries adds at the root of a client, and the
son-base identities (`grayTailSonBase_eq_sum_map_l4`,
`grayChargedRootIncrement_slotEntries_eq_sum`) evaluate it slot by slot;
`mem_grayChargedDeficientRoots_iff` identifies the clients still below half.
`grayChargedSpendWindow_append_round` advances the window by one pass and
`grayChargedDoneWindow_of_eight` shows eight passes suffice. `GrayChargedRequestInvariant`
records the resulting phase-dependent invariant, proved for every state by
`grayChargedRequestInvariant_stateAt`, and `grayCharged_final_request_window` is the final
two-sided bound.
-/

namespace Kolmogorov

open scoped BigOperators

open Classical in
/-- The amount a list of entries adds at the root of client `i`, namely the sum of its son bases
over all children. -/
def grayChargedRootIncrement {n b : Nat}
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n) : Rat :=
  ∑ c : Fin b, grayTailSonBase entries i c

open Classical in
/-- A client is deficient exactly when its frozen root request is below `alpha / 2`. -/
lemma mem_grayChargedDeficientRoots_iff {n b : Nat}
    (source : Nat) (threshold eps alpha : Rat)
    (frozen : GrayTailFrozen n b) (i : Fin n) :
    i ∈ grayChargedDeficientRoots source threshold eps alpha frozen ↔
      grayChargedRootRequest source threshold eps
          (grayTailFrozenEntries frozen) i < alpha / 2 := by
  simp [grayChargedDeficientRoots]

open Classical in
/-- The son base of a child is the sum of the root requests of the entries sitting at that child. -/
lemma grayTailSonBase_eq_sum_map_l4 {n b : Nat}
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n) (c : Fin b) :
    grayTailSonBase entries i c =
      (entries.map fun p =>
        if p.1.1 = i ∧ p.1.2.1 = c then getReq p.2 [] else 0).sum := by
  unfold grayTailSonBase
  induction entries with
  | nil => simp
  | cons p entries ih =>
      by_cases h : p.1.1 = i ∧ p.1.2.1 = c <;> simp [h, ih]

open Classical in
/-- The son base of a child, over slot entries, is the sum of the root requests of the slots
sitting at that child. -/
lemma grayTailSonBase_slotEntries_eq_sum_l4 {n b : Nat}
    (slots : List (GrayTailSlot n b)) (move : FamilyClientMove)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries slots move) i c =
      ∑ j : Fin slots.length,
        if (slots.get j).1 = i ∧ (slots.get j).2.1 = c then
          getFamilyReq move j.val [] else 0 := by
  rw [grayTailSonBase_eq_sum_map_l4]
  unfold grayTailSlotEntries
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

open Classical in
/-- The increment a round adds at the root of a client is the sum of the root requests of that
client's slots. -/
lemma grayChargedRootIncrement_slotEntries_eq_sum {n b : Nat}
    (slots : List (GrayTailSlot n b)) (move : FamilyClientMove) (i : Fin n) :
    grayChargedRootIncrement (grayTailSlotEntries slots move) i =
      ∑ j : Fin slots.length,
        if (slots.get j).1 = i then getFamilyReq move j.val [] else 0 := by
  unfold grayChargedRootIncrement
  simp_rw [grayTailSonBase_slotEntries_eq_sum_l4]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let root := (slots.get j).1
  let son := (slots.get j).2.1
  let req := getFamilyReq move j.val []
  change (∑ c : Fin b, if root = i ∧ son = c then req else 0) =
    if root = i then req else 0
  by_cases hi : root = i <;> simp [hi, eq_comm]

open Classical in
/-- Among the slots built at a fixed root `r`, those belonging to client `i` are all of them if
`r = i` and none otherwise. -/
lemma grayCharged_filter_map_const_root_length {n b : Nat}
    (r i : Fin n) (pairs : List (Fin b × Fin b)) :
    ((pairs.map fun p => (r, p.1, p.2)).filter
        fun s => decide (s.1 = i)).length =
      if r = i then pairs.length else 0 := by
  rw [List.filter_map]
  by_cases hri : r = i
  · simp [Function.comp_def, hri]
  · simp [Function.comp_def, hri]

open Classical in
/-- Among the slots built over a list of distinct roots, client `i` owns one full set of pairs if
it is among the roots and none otherwise. -/
lemma grayCharged_filter_flatMap_root_length {n b : Nat}
    (roots : List (Fin n)) (pairs : List (Fin b × Fin b))
    (hroots : roots.Nodup) (i : Fin n) :
    ((roots.flatMap fun r => pairs.map fun p => (r, p.1, p.2)).filter
        fun s => decide (s.1 = i)).length =
      if i ∈ roots then pairs.length else 0 := by
  induction roots with
  | nil => simp
  | cons r roots ih =>
      rw [List.nodup_cons] at hroots
      rw [List.flatMap_cons, List.filter_append, List.length_append,
        grayCharged_filter_map_const_root_length, ih hroots.2]
      by_cases hri : r = i
      · subst r
        simp [hroots.1]
      · have hir : i ≠ r := Ne.symm hri
        simp [hri, hir]

open Classical in
/-- A deficient client owns exactly one set of spend pairs among the spend slots; other clients
own none. -/
lemma grayChargedSpendSlots_filter_root_length {n b : Nat}
    (source count pass : Nat) (threshold eps alpha : Rat)
    (frozen : GrayTailFrozen n b) (i : Fin n) :
    ((grayChargedSpendSlots source count pass threshold eps alpha frozen).filter
        fun s => decide (s.1 = i)).length =
      if i ∈ grayChargedDeficientRoots source threshold eps alpha frozen then
        (grayChargedSpendPairs b source count pass).length
      else 0 := by
  unfold grayChargedSpendSlots
  exact grayCharged_filter_flatMap_root_length _ _
    (grayChargedDeficientRoots_nodup source threshold eps alpha frozen) i

open Classical in
/-- The indices of the slots belonging to a client are as many as those slots. -/
lemma grayCharged_filter_index_card {n b : Nat}
    (slots : List (GrayTailSlot n b)) (i : Fin n) :
    (Finset.univ.filter
        fun j : Fin slots.length => (slots.get j).1 = i).card =
      (slots.filter fun s => decide (s.1 = i)).length := by
  let roots : List.Vector (Fin n) slots.length :=
    ⟨slots.map Prod.fst, by simp⟩
  have hget (j : Fin slots.length) :
      roots.get j = (slots.get j).1 := by
    simp [List.Vector.get, roots, List.get_eq_getElem]
  have hfilters :
      (Finset.univ.filter
          fun j : Fin slots.length => (slots.get j).1 = i) =
        Finset.univ.filter (fun j : Fin slots.length => roots.get j = i) := by
    ext j
    simp [hget]
  calc
    (Finset.univ.filter
        fun j : Fin slots.length => (slots.get j).1 = i).card =
        (Finset.univ.filter
          fun j : Fin slots.length => roots.get j = i).card := by
            rw [hfilters]
    _ = roots.toList.count i :=
      Fin.card_filter_univ_eq_vector_get_eq_count i roots
    _ = (slots.filter fun s => decide (s.1 = i)).length := by
      dsimp [roots]
      rw [List.count_eq_countP, List.countP_eq_length_filter,
        List.filter_map]
      have hp :
          (fun s : GrayTailSlot n b => s.1 == i) =
            (fun s => decide (s.1 = i)) := by
        funext s
        by_cases hsi : s.1 = i <;> simp [hsi]
      simp only [List.length_map]
      change (slots.filter (fun s => s.1 == i)).length =
        (slots.filter fun s => decide (s.1 = i)).length
      rw [hp]

open Classical in
/-- A successful spend pass raises the root of a deficient client by between `dyadicScale a / 16`
and `dyadicScale a / 8`. -/
lemma grayChargedRootIncrement_spend_bounds
    {q L a e n pass : Nat} {A : Allocation}
    (hae : a <= e) (hpass : pass < 8)
    (frozen : GrayTailFrozen n (grayTailBranch q L a e))
    (move : FamilyClientMove) (server : FamilyServerMove)
    (hgoal : grayChargedSpendGoalAtB q L a e pass
      (grayChargedSlotsForPass q a e pass frozen).length A move server = true)
    (i : Fin n)
    (hi : i ∈ grayChargedDeficientRoots
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (dyadicScale e) (dyadicScale a) frozen) :
    dyadicScale a / 16 <=
        grayChargedRootIncrement
          (grayTailSlotEntries
            (grayChargedSlotsForPass q a e pass frozen) move) i ∧
      grayChargedRootIncrement
          (grayTailSlotEntries
            (grayChargedSlotsForPass q a e pass frozen) move) i <=
        dyadicScale a / 8 := by
  let slots := grayChargedSlotsForPass q a e pass frozen
  change dyadicScale a / 16 <=
      grayChargedRootIncrement (grayTailSlotEntries slots move) i ∧
    grayChargedRootIncrement (grayTailSlotEntries slots move) i <=
      dyadicScale a / 8
  let rootslots := Finset.univ.filter
    fun j : Fin slots.length => (slots.get j).1 = i
  have hcard : rootslots.card = grayChargedSpendCount q a e := by
    calc
      rootslots.card =
          (slots.filter fun s => decide (s.1 = i)).length := by
            simpa [rootslots, List.get_eq_getElem] using
              grayCharged_filter_index_card slots i
      _ = grayChargedSpendCount q a e := by
        dsimp [slots, grayChargedSlotsForPass]
        rw [grayChargedSpendSlots_filter_root_length, if_pos hi,
          grayChargedSpendPairs_length (q := q) (L := L) hae hpass]
  have hsum :
      grayChargedRootIncrement (grayTailSlotEntries slots move) i =
        ∑ j ∈ rootslots, getFamilyReq move j.val [] := by
    rw [grayChargedRootIncrement_slotEntries_eq_sum]
    dsimp [rootslots]
    rw [Finset.sum_filter]
  have hlower :
      (∑ _j ∈ rootslots,
          dyadicScale (grayChargedSpendAlphaDepth a) / 2) <=
        ∑ j ∈ rootslots, getFamilyReq move j.val [] := by
    apply Finset.sum_le_sum
    intro j hj
    exact (grayChargedSpendGoalAtB_root_bounds hgoal j).1
  have hupper :
      (∑ j ∈ rootslots, getFamilyReq move j.val []) <=
        ∑ _j ∈ rootslots, dyadicScale (grayChargedSpendAlphaDepth a) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (grayChargedSpendGoalAtB_root_bounds hgoal j).2
  have hquarter :
      (grayChargedSpendCount q a e : Rat) *
          (dyadicScale (grayChargedSpendAlphaDepth a) / 2) =
        dyadicScale a / 16 := by
    calc
      (grayChargedSpendCount q a e : Rat) *
            (dyadicScale (grayChargedSpendAlphaDepth a) / 2) =
          ((grayChargedSpendCount q a e : Rat) *
            dyadicScale (grayChargedSpendAlphaDepth a)) / 2 := by ring
      _ = (dyadicScale a / 8) / 2 := by
        rw [grayChargedSpendCount_mass hae]
      _ = dyadicScale a / 16 := by ring
  constructor
  · calc
      dyadicScale a / 16 =
          (rootslots.card : Rat) *
            (dyadicScale (grayChargedSpendAlphaDepth a) / 2) := by
              rw [hcard]
              exact hquarter.symm
      _ = ∑ _j ∈ rootslots,
            dyadicScale (grayChargedSpendAlphaDepth a) / 2 := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ <= ∑ j ∈ rootslots, getFamilyReq move j.val [] := hlower
      _ = grayChargedRootIncrement (grayTailSlotEntries slots move) i :=
        hsum.symm
  · rw [hsum]
    calc
      (∑ j ∈ rootslots, getFamilyReq move j.val []) <=
          ∑ _j ∈ rootslots, dyadicScale (grayChargedSpendAlphaDepth a) := hupper
      _ = (rootslots.card : Rat) *
            dyadicScale (grayChargedSpendAlphaDepth a) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ = (grayChargedSpendCount q a e : Rat) *
            dyadicScale (grayChargedSpendAlphaDepth a) := by rw [hcard]
      _ = dyadicScale a / 8 := grayChargedSpendCount_mass hae

open Classical in
/-- A spend pass adds nothing at the root of a client that is not deficient. -/
lemma grayChargedRootIncrement_spend_eq_zero
    {q L a e n pass : Nat}
    (frozen : GrayTailFrozen n (grayTailBranch q L a e))
    (move : FamilyClientMove) (i : Fin n)
    (hi : i ∉ grayChargedDeficientRoots
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (dyadicScale e) (dyadicScale a) frozen) :
    grayChargedRootIncrement
        (grayTailSlotEntries
          (grayChargedSlotsForPass q a e pass frozen) move) i = 0 := by
  let slots := grayChargedSlotsForPass q a e pass frozen
  change grayChargedRootIncrement (grayTailSlotEntries slots move) i = 0
  let rootslots := Finset.univ.filter
    fun j : Fin slots.length => (slots.get j).1 = i
  have hcard : rootslots.card = 0 := by
    calc
      rootslots.card =
          (slots.filter fun s => decide (s.1 = i)).length := by
            simpa [rootslots, List.get_eq_getElem] using
              grayCharged_filter_index_card slots i
      _ = 0 := by
        dsimp [slots, grayChargedSlotsForPass]
        rw [grayChargedSpendSlots_filter_root_length, if_neg hi]
  have hempty : rootslots = ∅ := Finset.card_eq_zero.mp hcard
  rw [grayChargedRootIncrement_slotEntries_eq_sum]
  calc
    (∑ j : Fin slots.length,
        if (slots.get j).1 = i then getFamilyReq move j.val [] else 0) =
        ∑ j ∈ rootslots, getFamilyReq move j.val [] := by
          dsimp [rootslots]
          rw [Finset.sum_filter]
    _ = 0 := by simp [hempty]

open Classical in
/-- Appending entries that only use spare children adds their increment to the root request. -/
lemma grayChargedRootIncrement_append_spare {n b source : Nat}
    (threshold eps : Rat)
    (left right : List (GrayTailSlot n b × ClientMove))
    (hspare : ∀ p ∈ right, source ≤ p.1.2.1.val)
    (i : Fin n) :
    grayChargedRootRequest source threshold eps (left ++ right) i =
      grayChargedRootRequest source threshold eps left i +
        grayChargedRootIncrement right i := by
  unfold grayChargedRootIncrement grayChargedRootRequest
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  unfold grayChargedSonRequest grayTailSonRequest
  rw [grayTailSonBase_append_globalEntries]
  by_cases hc : c.val < source
  · have hzero : grayTailSonBase right i c = 0 := by
      apply grayTailSonBase_eq_zero_of_no_match
      intro p hp
      right
      intro hpc
      have hge := hspare p hp
      have heq : p.1.2.1.val = c.val := congrArg Fin.val hpc
      omega
    simp [hc, hzero]
  · simp [hc]

open Classical in
/-- Freezing a round that only uses spare children adds that round's increment to the frozen root
request. -/
lemma grayChargedRootRequest_append_spend_round
    {n b source : Nat} (threshold eps : Rat)
    (frozen : GrayTailFrozen n b) (p : GrayTailRound n b)
    (hspare : ∀ s ∈ p.slots, source <= s.2.1.val)
    (i : Fin n) :
    grayChargedRootRequest source threshold eps
        (grayTailFrozenEntries (frozen ++ [p])) i =
      grayChargedRootRequest source threshold eps
          (grayTailFrozenEntries frozen) i +
        grayChargedRootIncrement (grayTailSlotEntries p.slots p.move) i := by
  have hentries :
      grayTailFrozenEntries (frozen ++ [p]) =
        grayTailFrozenEntries frozen ++
          grayTailSlotEntries p.slots p.move := by
    simp [grayTailFrozenEntries]
  rw [hentries]
  apply grayChargedRootIncrement_append_spare
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  exact hspare (p.slots.get j) (List.get_mem p.slots j)

open Classical in
/-- Every frozen entry of a charged tail run requests a nonnegative amount at the root. -/
lemma grayChargedTail_frozen_entry_nonneg_stateAt
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {z : GrayTailSlot n (grayTailBranch q L a e) × ClientMove}
    (hz : z ∈ grayTailFrozenEntries
      (grayChargedTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).frozen) :
    0 <= getReq z.2 [] := by
  rw [grayTailFrozenEntries, List.mem_flatMap] at hz
  obtain ⟨p, hp, hzp⟩ := hz
  have hvalid := (grayChargedTailCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t).round_valid p hp
  exact grayChargedTailSlotEntries_root_nonneg hvalid.2.2.2.2.1 z hzp

open Classical in
/-- The frozen root request of every client of a charged tail run lies between `0` and
`dyadicScale a`. -/
lemma grayChargedTail_frozen_root_bounds_stateAt
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hae : a <= e) (i : Fin n) :
    let frozen := (grayChargedTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).frozen
    0 <= grayChargedRootRequest
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (grayTailFrozenEntries frozen) i ∧
      grayChargedRootRequest
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (grayTailFrozenEntries frozen) i <= dyadicScale a := by
  dsimp only
  let frozen := (grayChargedTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t).frozen
  let entries := grayTailFrozenEntries frozen
  have hentryNonneg : ∀ z ∈ entries, 0 <= getReq z.2 [] := by
    intro z hz
    exact grayChargedTail_frozen_entry_nonneg_stateAt
      (q := q) (L := L) (a := a) (e := e)
      (sigma := sigma) (A := A) (sm := sm) (t := t)
      (by simpa [entries, frozen] using hz)
  have hson : ∀ c : Fin (grayTailBranch q L a e),
      0 <= grayChargedSonRequest
          (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) entries i c ∧
        grayChargedSonRequest
          (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) entries i c <=
            if c.val < grayChargedSourceCount a e then dyadicScale e else 0 := by
    intro c
    by_cases hc : c.val < grayChargedSourceCount a e
    · unfold grayChargedSonRequest grayTailSonRequest
      simp only [if_pos hc]
      by_cases hlarge : grayChargedThreshold q e < grayTailSonBase entries i c
      · rw [if_pos hlarge]
        exact ⟨(dyadicScale_pos e).le, le_rfl⟩
      · rw [if_neg hlarge]
        constructor
        · exact grayTailSonBase_nonneg_global hentryNonneg
        · have hbase := grayChargedTail_all_frozen_base_le_stateAt
            q L a e sigma A sm t i c
          simpa [frozen, entries] using hbase
    · have hzero : grayTailSonBase entries i c = 0 := by
        apply grayTailSonBase_eq_zero_of_no_match
        intro z hz
        right
        intro hzc
        have hzlt := grayChargedTailFrozenEntries_used
          (q := q) (L := L) (a := a) (e := e)
          (sigma := sigma) (A := A) (sm := sm) (t := t)
          (by simpa [entries, frozen] using hz)
        have heq : z.1.2.1.val = c.val := congrArg Fin.val hzc
        rw [heq] at hzlt
        exact (Nat.not_lt_of_ge (by
          simpa [grayChargedSourceCount] using Nat.le_of_not_gt hc)) hzlt
      unfold grayChargedSonRequest
      simp only [if_neg hc, hzero]
      norm_num
  unfold grayChargedRootRequest
  constructor
  · apply Finset.sum_nonneg
    intro c hc
    exact (hson c).1
  · calc
      (∑ c : Fin (grayTailBranch q L a e),
          grayChargedSonRequest
            (grayChargedSourceCount a e) (grayChargedThreshold q e)
            (dyadicScale e) entries i c) <=
          ∑ c : Fin (grayTailBranch q L a e),
            if c.val < grayChargedSourceCount a e then dyadicScale e else 0 := by
              apply Finset.sum_le_sum
              intro c hc
              exact (hson c).2
      _ = ∑ c ∈ Finset.univ.filter
            (fun c : Fin (grayTailBranch q L a e) =>
              c.val < grayChargedSourceCount a e), dyadicScale e := by
              rw [Finset.sum_filter]
      _ = ((Finset.univ.filter
            (fun c : Fin (grayTailBranch q L a e) =>
              c.val < grayChargedSourceCount a e)).card : Rat) *
            dyadicScale e := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ <= (grayChargedSourceCount a e : Rat) * dyadicScale e := by
        apply mul_le_mul_of_nonneg_right _ (dyadicScale_pos e).le
        exact_mod_cast grayTail_source_fin_card_le
          (grayTailBranch q L a e) (grayChargedSourceCount a e)
      _ = dyadicScale a := grayChargedSource_mass hae

open Classical in
/-- The request the frozen rounds put at the root of client `i`, with the source count, threshold
and scale of the charged construction. -/
def grayChargedFrozenRootRequest {n b : Nat}
    (q a e : Nat) (frozen : GrayTailFrozen n b) (i : Fin n) : Rat :=
  grayChargedRootRequest
    (grayChargedSourceCount a e) (grayChargedThreshold q e)
    (dyadicScale e) (grayTailFrozenEntries frozen) i

open Classical in
/-- The request window after `pass` spend passes: every client sits between `0` and
`dyadicScale a`, and a client still below `dyadicScale a / 2` has already received
`pass * (dyadicScale a / 16)`. -/
def GrayChargedSpendWindow {n b : Nat}
    (q a e pass : Nat) (frozen : GrayTailFrozen n b) : Prop :=
  ∀ i : Fin n,
    0 <= grayChargedFrozenRootRequest q a e frozen i ∧
      grayChargedFrozenRootRequest q a e frozen i <= dyadicScale a ∧
      (grayChargedFrozenRootRequest q a e frozen i < dyadicScale a / 2 ->
        (pass : Rat) * (dyadicScale a / 16) <=
          grayChargedFrozenRootRequest q a e frozen i)

open Classical in
/-- The request window at the end of the spend phase: every client sits between
`dyadicScale a / 2` and `dyadicScale a`. -/
def GrayChargedDoneWindow {n b : Nat}
    (q a e : Nat) (frozen : GrayTailFrozen n b) : Prop :=
  ∀ i : Fin n,
    dyadicScale a / 2 <= grayChargedFrozenRootRequest q a e frozen i ∧
      grayChargedFrozenRootRequest q a e frozen i <= dyadicScale a

open Classical in
/-- Before the first spend pass, the two-sided bound on the frozen root requests is the whole
window condition. -/
lemma grayChargedSpendWindow_zero_of_bounds {n b q a e : Nat}
    {frozen : GrayTailFrozen n b}
    (hbounds : ∀ i : Fin n,
      0 <= grayChargedFrozenRootRequest q a e frozen i ∧
        grayChargedFrozenRootRequest q a e frozen i <= dyadicScale a) :
    GrayChargedSpendWindow q a e 0 frozen := by
  intro i
  have hi := hbounds i
  refine ⟨hi.1, hi.2, ?_⟩
  intro _hlt
  simpa using hi.1

open Classical in
/-- A spend pass that opens no slot leaves no deficient client, so the done window already holds. -/
lemma grayChargedDoneWindow_of_slots_nil {q L a e n pass : Nat}
    {frozen : GrayTailFrozen n (grayTailBranch q L a e)}
    (hae : a <= e) (hpass : pass < 8)
    (hwindow : GrayChargedSpendWindow q a e pass frozen)
    (hslots : grayChargedSlotsForPass q a e pass frozen = []) :
    GrayChargedDoneWindow q a e frozen := by
  intro i
  have hi := hwindow i
  constructor
  · by_contra hhalf
    have hlt : grayChargedFrozenRootRequest q a e frozen i <
        dyadicScale a / 2 := lt_of_not_ge hhalf
    have hmem : i ∈ grayChargedDeficientRoots
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (dyadicScale a) frozen := by
      exact (mem_grayChargedDeficientRoots_iff
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (dyadicScale a) frozen i).2 hlt
    have hlen := grayChargedSpendSlots_filter_root_length
      (grayChargedSourceCount a e) (grayChargedSpendCount q a e) pass
      (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a) frozen i
    have hslots' : grayChargedSpendSlots
        (grayChargedSourceCount a e) (grayChargedSpendCount q a e) pass
        (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a) frozen = [] := by
      simpa [grayChargedSlotsForPass] using hslots
    rw [hslots', if_pos hmem,
      grayChargedSpendPairs_length (q := q) (L := L) hae hpass] at hlen
    have hcountPos := grayChargedSpendCount_pos q a e
    exact (Nat.ne_of_gt hcountPos) hlen.symm
  · exact hi.2.1

open Classical in
/-- A successful spend pass advances the window from `pass` to `pass + 1`. -/
lemma grayChargedSpendWindow_append_round
    {q L a e n pass : Nat} {U : Allocation}
    {frozen : GrayTailFrozen n (grayTailBranch q L a e)}
    {p : GrayTailRound n (grayTailBranch q L a e)}
    {server : FamilyServerMove}
    (hae : a <= e) (hpass : pass < 8)
    (hwindow : GrayChargedSpendWindow q a e pass frozen)
    (hslots : p.slots = grayChargedSlotsForPass q a e pass frozen)
    (hgoal : grayChargedSpendGoalAtB q L a e pass
      p.slots.length U p.move server = true)
    (hspare : ∀ s ∈ p.slots, grayChargedSourceCount a e <= s.2.1.val) :
    GrayChargedSpendWindow q a e (pass + 1) (frozen ++ [p]) := by
  intro i
  have hreq := grayChargedRootRequest_append_spend_round
    (grayChargedThreshold q e) (dyadicScale e) frozen p hspare i
  change 0 <= grayChargedFrozenRootRequest q a e (frozen ++ [p]) i ∧
    grayChargedFrozenRootRequest q a e (frozen ++ [p]) i <= dyadicScale a ∧
    (grayChargedFrozenRootRequest q a e (frozen ++ [p]) i <
      dyadicScale a / 2 ->
      ((pass + 1 : Nat) : Rat) * (dyadicScale a / 16) <=
        grayChargedFrozenRootRequest q a e (frozen ++ [p]) i)
  symm at hreq
  change grayChargedFrozenRootRequest q a e frozen i +
      grayChargedRootIncrement (grayTailSlotEntries p.slots p.move) i =
    grayChargedFrozenRootRequest q a e (frozen ++ [p]) i at hreq
  have hold := hwindow i
  by_cases hdef : i ∈ grayChargedDeficientRoots
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (dyadicScale e) (dyadicScale a) frozen
  · have hlt : grayChargedFrozenRootRequest q a e frozen i <
        dyadicScale a / 2 :=
      (mem_grayChargedDeficientRoots_iff
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (dyadicScale a) frozen i).1 hdef
    have hinc := grayChargedRootIncrement_spend_bounds
      (q := q) (L := L) (a := a) (e := e) (pass := pass)
      (A := U) hae hpass frozen p.move server (by simpa [hslots] using hgoal) i hdef
    have hinc' : dyadicScale a / 16 <=
          grayChargedRootIncrement (grayTailSlotEntries p.slots p.move) i ∧
        grayChargedRootIncrement (grayTailSlotEntries p.slots p.move) i <=
          dyadicScale a / 8 := by
      simpa [hslots] using hinc
    constructor
    · rw [← hreq]
      linarith [hinc'.1]
    constructor
    · rw [← hreq]
      linarith [hinc'.2]
    · intro _hnew
      have holdLower := hold.2.2 hlt
      rw [← hreq]
      norm_num [Nat.cast_add, Nat.cast_one]
      linarith [hinc'.1]
  · have hinc := grayChargedRootIncrement_spend_eq_zero
      (q := q) (L := L) (a := a) (e := e) (pass := pass)
      frozen p.move i hdef
    have hsame : grayChargedFrozenRootRequest q a e (frozen ++ [p]) i =
        grayChargedFrozenRootRequest q a e frozen i := by
      rw [← hreq, hslots, hinc, add_zero]
    rw [hsame]
    refine ⟨hold.1, hold.2.1, ?_⟩
    intro hlt
    exact False.elim (hdef
      ((mem_grayChargedDeficientRoots_iff
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (dyadicScale a) frozen i).2 hlt))

open Classical in
/-- After eight spend passes the window forces every client above `dyadicScale a / 2`. -/
lemma grayChargedDoneWindow_of_eight
    {n b q a e : Nat} {frozen : GrayTailFrozen n b}
    (hwindow : GrayChargedSpendWindow q a e 8 frozen) :
    GrayChargedDoneWindow q a e frozen := by
  intro i
  have hi := hwindow i
  constructor
  · by_contra hhalf
    have hlt : grayChargedFrozenRootRequest q a e frozen i <
        dyadicScale a / 2 := lt_of_not_ge hhalf
    have hlower := hi.2.2 hlt
    norm_num at hlower
    have hpos := dyadicScale_pos a
    linarith
  · exact hi.2.1

open Classical in
/-- The request invariant of a charged state: no condition in the `advantage` phase, the spend
window of the pass during spending, and the done window once finished. -/
def GrayChargedRequestInvariant {n b : Nat}
    (q a e : Nat) (st : GrayChargedState n b) : Prop :=
  match st.phase with
  | .advantage => True
  | .spend pass => GrayChargedSpendWindow q a e pass st.core.frozen
  | .done => GrayChargedDoneWindow q a e st.core.frozen

open Classical in
/-- Every state of a charged run satisfies the request invariant of its phase. -/
theorem grayChargedRequestInvariant_stateAt
    {q L a e n : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hae : a <= e) (t : Nat) :
    GrayChargedRequestInvariant q a e
      (grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      simp [GrayChargedRequestInvariant, grayChargedStateAt,
        grayChargedFold, grayTailServerPrefix, grayChargedInitialState]
  | succ t ih =>
      rw [grayChargedStateAt_succ]
      have hcert := grayChargedCertified_stateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t
      generalize hst : grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t = st at hcert ih ⊢
      cases hcert with
      | advantage core hcore hsource hactive =>
          have hphase : (grayChargedStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).phase = .advantage := by
            rw [hst]
          have hcoreTail := grayChargedStateAt_core_eq_tailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t hphase
          have hcoreTail' : core = grayChargedTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t := by
            simpa [hst] using hcoreTail
          let next := grayChargedTailStep q L a e sigma A core (sm t)
          by_cases hdone : next.done = true
          · have hnextEq : next = grayChargedTailStateAt
                (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm (t + 1) := by
              rw [grayChargedTailStateAt_succ]
              simp [next, hcoreTail']
            have hbounds : ∀ i : Fin n,
                0 <= grayChargedFrozenRootRequest q a e next.frozen i ∧
                  grayChargedFrozenRootRequest q a e next.frozen i <=
                    dyadicScale a := by
              intro i
              have hi := grayChargedTail_frozen_root_bounds_stateAt
                (q := q) (L := L) (a := a) (e := e)
                (sigma := sigma) (A := A) (sm := sm) (t := t + 1) hae i
              simpa [grayChargedFrozenRootRequest, hnextEq] using hi
            have hwindow0 := grayChargedSpendWindow_zero_of_bounds hbounds
            by_cases hempty :
                (grayChargedSlotsForPass q a e 0 next.frozen).isEmpty = true
            · have hnil : grayChargedSlotsForPass q a e 0 next.frozen = [] :=
                List.isEmpty_iff.mp hempty
              have hdoneWindow := grayChargedDoneWindow_of_slots_nil
                (q := q) (L := L) (a := a) (e := e)
                (pass := 0) hae (by omega) hwindow0 hnil
              simpa [grayChargedStep, next, hdone, grayChargedStartSpend,
                hempty, GrayChargedRequestInvariant] using hdoneWindow
            · have hfalse :
                (grayChargedSlotsForPass q a e 0 next.frozen).isEmpty = false := by
                cases h : (grayChargedSlotsForPass q a e 0 next.frozen).isEmpty <;>
                  simp_all
              simpa [grayChargedStep, next, hdone, grayChargedStartSpend,
                hfalse, GrayChargedRequestInvariant] using hwindow0
          · simp [grayChargedStep, next, hdone,
              GrayChargedRequestInvariant]
      | done core hdone =>
          have hwindow : GrayChargedDoneWindow q a e core.frozen := by
            simpa [GrayChargedRequestInvariant] using ih
          simpa [grayChargedStep, GrayChargedRequestInvariant] using hwindow
      | spend pass core hspend =>
          have hwindow : GrayChargedSpendWindow q a e pass core.frozen := by
            simpa [GrayChargedRequestInvariant] using ih
          have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
          let epsRound := grayChargedSpendEps a L e pass
          let deltaRound := grayChargedSpendDelta a L e pass
          let current := grayChargedSpendMove q L a e pass sigma core
          let localSM := grayTailLocalServerMove deltaRound core.slots (sm t)
          by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
              core.slots.length core.unavailable current localSM = true
          · let p : GrayTailRound n (grayTailBranch q L a e) :=
              { serverTime := core.time
                roundIndex := core.frozen.length
                epsDepth := epsRound
                slots := core.slots
                move := current
                allocated := grayTailLocalAllocatedList localSM
                unavailable := core.unavailable }
            let frozen' := core.frozen ++ [p]
            have hpSlots : p.slots =
                grayChargedSlotsForPass q a e pass core.frozen := by
              simpa [p] using hspend.slots_eq
            have hspare : ∀ s ∈ p.slots,
                grayChargedSourceCount a e <= s.2.1.val := by
              intro s hs
              apply grayChargedSpendSlots_son_ge
              simpa [hpSlots] using hs
            have hwindow' : GrayChargedSpendWindow q a e (pass + 1) frozen' := by
              apply grayChargedSpendWindow_append_round
                (q := q) (L := L) (a := a) (e := e) (pass := pass)
                (U := core.unavailable) (server := localSM)
                hae hspend.pass_lt hwindow hpSlots
              · simpa [p] using hgoal
              · exact hspare
            by_cases hpass : pass + 1 < 8
            · let slots := grayChargedSlotsForPass q a e (pass + 1) frozen'
              by_cases hempty : slots.isEmpty = true
              · have hnil : slots = [] := List.isEmpty_iff.mp hempty
                have hdoneWindow := grayChargedDoneWindow_of_slots_nil
                  (q := q) (L := L) (a := a) (e := e)
                  (pass := pass + 1) hae hpass hwindow'
                  (by simpa [slots] using hnil)
                simpa [grayChargedStep, hslots, hgoal, epsRound, deltaRound,
                  current, localSM, p, frozen', hpass, slots, hempty,
                  GrayChargedRequestInvariant] using hdoneWindow
              · have hfalse : slots.isEmpty = false := by
                  cases h : slots.isEmpty <;> simp_all
                simpa [grayChargedStep, hslots, hgoal, epsRound, deltaRound,
                  current, localSM, p, frozen', hpass, slots, hfalse,
                  GrayChargedRequestInvariant] using hwindow'
            · have hfour : pass + 1 = 8 := by
                have hpassLt : pass < 8 := hspend.pass_lt
                omega
              have hwindow4 : GrayChargedSpendWindow q a e 8 frozen' := by
                simpa [hfour] using hwindow'
              have hdoneWindow := grayChargedDoneWindow_of_eight hwindow4
              simpa [grayChargedStep, hslots, hgoal, epsRound, deltaRound,
                current, localSM, p, frozen', hpass,
                GrayChargedRequestInvariant] using hdoneWindow
          · simpa [grayChargedStep, hslots, hgoal, epsRound, deltaRound,
              current, localSM, GrayChargedRequestInvariant] using hwindow

open Classical in
/-- The displayed family move puts at the root of client `i` exactly the charged root request of
the entries. -/
lemma getFamilyReq_grayChargedTailFamilyMove_root_l4 {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (frozen : GrayTailFrozen n b) (slots : List (GrayTailSlot n b))
    (current : FamilyClientMove) (i : Fin n) :
    getFamilyReq
        (grayChargedTailFamilyMove source threshold eps frozen slots current)
        i.val [] =
      grayChargedRootRequest source threshold eps
        (grayTailEntries frozen slots current) i := by
  unfold grayChargedTailFamilyMove getFamilyReq familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

open Classical in
/-- The charged strategy puts at the root of client `i` the charged root request of the entries
of its controller state. -/
lemma getFamilyReq_grayChargedStrategy_root_l4
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (sm : Nat -> FamilyServerMove) (t : Nat) (i : Fin n) :
    let st := grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
    let current := match st.phase with
      | .done => []
      | .advantage => if st.core.slots.isEmpty then []
        else grayTailCurrentMove q L e sigma st.core
      | .spend pass => if st.core.slots.isEmpty then []
        else grayChargedSpendMove q L a e pass sigma st.core
    getFamilyReq
        (playClientFamily A n (grayChargedStrategy q L a e sigma) sm t)
        i.val [] =
      grayChargedRootRequest
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e)
        (grayTailEntries st.core.frozen st.core.slots current) i := by
  dsimp only
  rw [playClientFamily_grayChargedStrategy]
  exact getFamilyReq_grayChargedTailFamilyMove_root_l4 _ _ _ _ _ _ _

open Classical in
/-- At a final time the charged strategy puts between `dyadicScale a / 2` and `dyadicScale a` at
the root of every client. -/
theorem grayCharged_final_request_window
    {q L B a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (_ha : 1 <= a) (hae : a <= e)
    (_hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (_hRung : ChargedGrayRung 4 q L B sigma)
    (sm : Nat -> FamilyServerMove)
    (_hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hfinal : GrayChargedFinalAt q L a e n sigma A sm T) :
    forall i, i < n ->
      dyadicScale a / 2 <=
          getFamilyReq
            (playClientFamily A n (grayChargedStrategy q L a e sigma) sm T) i [] ∧
        getFamilyReq
            (playClientFamily A n (grayChargedStrategy q L a e sigma) sm T) i []
          <= dyadicScale a := by
  intro i hi
  let fi : Fin n := ⟨i, hi⟩
  let st := grayChargedStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)
  have hdone : st.phase = .done := by
    exact grayChargedFinalAt_successor_done hfinal
  have hinvariant := grayChargedRequestInvariant_stateAt
    (q := q) (L := L) (a := a) (e := e)
    (n := n) (sigma := sigma) (A := A) (sm := sm) hae (T + 1)
  have hwindow : GrayChargedDoneWindow q a e st.core.frozen := by
    simpa [st, GrayChargedRequestInvariant, hdone] using hinvariant
  have hroot := hwindow fi
  have hslots : st.core.slots = [] := by
    exact grayChargedStateAt_slots_eq_nil_of_done
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1) hdone
  have hbridge := getFamilyReq_grayChargedStrategy_root_l4
    (q := q) (L := L) (a := a) (e := e)
    (n := n) (sigma := sigma) (A := A) sm (T + 1) fi
  have hreqEq :
      getFamilyReq
          (playClientFamily A n (grayChargedStrategy q L a e sigma) sm (T + 1))
          i [] =
        grayChargedFrozenRootRequest q a e st.core.frozen fi := by
    simpa [st, grayChargedFrozenRootRequest, hdone, hslots,
      grayTailEntries, grayTailSlotEntries, fi] using hbridge
  have hmove := grayChargedFinalAt_successor_move_eq hfinal
  change playClientFamily A n (grayChargedStrategy q L a e sigma) sm (T + 1) =
    playClientFamily A n (grayChargedStrategy q L a e sigma) sm T at hmove
  rw [← hmove, hreqEq]
  exact hroot

end Kolmogorov
