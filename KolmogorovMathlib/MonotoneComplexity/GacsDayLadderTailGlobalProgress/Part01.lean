import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.Invariants
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.StateAt
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRound

/-!
# Accounting for the total request of a tail run

The sums the global progress argument keeps track of: `grayTailEntryRequestSum` for a list of
entries, `grayTailFrozenRequestSum` for all frozen rounds, and `grayTailSourceBaseSum` for the
son bases over all clients and source children, which coincides with the total root request when
every entry sits at a source child (`grayTailSourceBaseSum_eq_entryRequestSum`). The sums are
additive over concatenation and grow when a round is frozen
(`grayTailEntryRequestSum_append`, `grayTailFrozenSonBase_append_global`), so a per-round gain
accumulates (`grayTailFrozenSonBase_progress_of_each`) — the form in which progress is fed to the
second part.
-/



namespace Kolmogorov

open scoped BigOperators

/-- The sum of the root requests `getReq z.2 []` of the entries `z` of the list, folded from the
right. -/
def grayTailEntryRequestSum {n b : Nat}
    (entries : List (GrayTailSlot n b × ClientMove)) : Rat :=
  entries.foldr (fun z acc => getReq z.2 [] + acc) 0

example {n b : Nat} (slots : List (GrayTailSlot n b))
    (move : FamilyClientMove) :
    totalRootRequest slots.length move =
      grayTailEntryRequestSum (grayTailSlotEntries slots move) := by
  rw [totalRootRequest_eq_foldr]
  unfold grayTailEntryRequestSum grayTailSlotEntries
  rw [List.ofFn_eq_map]
  rw [← List.map_coe_finRange_eq_range]
  rw [List.foldr_map]
  rw [List.foldr_map]
  rfl

/-- The sum of the son bases of the entries over all clients and all source children below
`used`. -/
def grayTailSourceBaseSum {n b : Nat} (used : Nat)
    (entries : List (GrayTailSlot n b × ClientMove)) : Rat :=
  ∑ i : Fin n, ∑ c : Fin b,
    if c.val < used then grayTailSonBase entries i c else 0

/-- Adding an entry at a source child adds its root request to the source base sum. -/
lemma grayTailSourceBaseSum_cons {n b used : Nat}
    (z : GrayTailSlot n b × ClientMove)
    (entries : List (GrayTailSlot n b × ClientMove))
    (hz : z.1.2.1.val < used) :
    grayTailSourceBaseSum used (z :: entries) =
      getReq z.2 [] + grayTailSourceBaseSum used entries := by
  classical
  unfold grayTailSourceBaseSum
  have hpoint : forall (i : Fin n) (c : Fin b),
      (if c.val < used then grayTailSonBase (z :: entries) i c else 0) =
      (if i = z.1.1 ∧ c = z.1.2.1 then getReq z.2 [] else 0) +
        (if c.val < used then grayTailSonBase entries i c else 0) := by
    intro i c
    unfold grayTailSonBase
    simp only [List.foldr_cons]
    by_cases hkey : i = z.1.1 ∧ c = z.1.2.1
    · rcases hkey with ⟨rfl, rfl⟩
      simp [hz]
    · have hkey' : ¬(z.1.1 = i ∧ z.1.2.1 = c) := by
        simpa only [eq_comm] using hkey
      by_cases hc : c.val < used <;> simp [hkey, hkey', hc]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib]
  have hdelta : (∑ i : Fin n, ∑ c : Fin b,
      if i = z.1.1 ∧ c = z.1.2.1 then getReq z.2 [] else 0) =
      getReq z.2 [] := by
    have hinner : forall i : Fin n,
        (∑ c : Fin b,
          if i = z.1.1 ∧ c = z.1.2.1 then getReq z.2 [] else 0) =
        if i = z.1.1 then getReq z.2 [] else 0 := by
      intro i
      by_cases hi : i = z.1.1
      · simp [hi]
      · simp [hi]
    simp_rw [hinner]
    exact Fintype.sum_ite_eq' z.1.1 (fun _ : Fin n => getReq z.2 [])
  rw [hdelta]

/-- When every entry sits at a source child, the source base sum is the total root request. -/
lemma grayTailSourceBaseSum_eq_entryRequestSum {n b used : Nat}
    (entries : List (GrayTailSlot n b × ClientMove))
    (hsource : forall z, z ∈ entries -> z.1.2.1.val < used) :
    grayTailSourceBaseSum used entries = grayTailEntryRequestSum entries := by
  induction entries with
  | nil => simp [grayTailSourceBaseSum, grayTailEntryRequestSum, grayTailSonBase]
  | cons z entries ih =>
      rw [grayTailSourceBaseSum_cons z entries (hsource z (by simp))]
      change getReq z.2 [] + grayTailSourceBaseSum used entries =
        getReq z.2 [] + grayTailEntryRequestSum entries
      rw [ih (fun w hw => hsource w (by simp [hw]))]

/-- The total root request of all frozen rounds. -/
def grayTailFrozenRequestSum {n b : Nat}
    (frozen : GrayTailFrozen n b) : Rat :=
  frozen.foldr
    (fun p acc => totalRootRequest p.slots.length p.move + acc) 0

/-- The total root request is additive over concatenation of entries. -/
lemma grayTailEntryRequestSum_append {n b : Nat}
    (left right : List (GrayTailSlot n b × ClientMove)) :
    grayTailEntryRequestSum (left ++ right) =
      grayTailEntryRequestSum left + grayTailEntryRequestSum right := by
  induction left with
  | nil => simp [grayTailEntryRequestSum]
  | cons z left ih =>
      simp only [List.cons_append]
      unfold grayTailEntryRequestSum at ih ⊢
      simp only [List.foldr_cons]
      rw [ih]
      ring

/-- The total root request of a round is the entry request sum of its slot entries. -/
lemma totalRootRequest_eq_grayTailEntryRequestSum {n b : Nat}
    (slots : List (GrayTailSlot n b)) (move : FamilyClientMove) :
    totalRootRequest slots.length move =
      grayTailEntryRequestSum (grayTailSlotEntries slots move) := by
  rw [totalRootRequest_eq_foldr]
  unfold grayTailEntryRequestSum grayTailSlotEntries
  rw [List.ofFn_eq_map]
  rw [← List.map_coe_finRange_eq_range]
  rw [List.foldr_map]
  rw [List.foldr_map]
  rfl

/-- The frozen request sum is the entry request sum of the frozen entries. -/
lemma grayTailFrozenRequestSum_eq_entries {n b : Nat}
    (frozen : GrayTailFrozen n b) :
    grayTailFrozenRequestSum frozen =
      grayTailEntryRequestSum (grayTailFrozenEntries frozen) := by
  induction frozen with
  | nil => simp [grayTailFrozenRequestSum, grayTailFrozenEntries,
      grayTailEntryRequestSum]
  | cons p frozen ih =>
      unfold grayTailFrozenRequestSum grayTailFrozenEntries
      simp only [List.foldr_cons, List.flatMap_cons]
      rw [grayTailEntryRequestSum_append,
        ← totalRootRequest_eq_grayTailEntryRequestSum]
      change totalRootRequest p.slots.length p.move +
          grayTailFrozenRequestSum frozen =
        totalRootRequest p.slots.length p.move +
          grayTailEntryRequestSum (grayTailFrozenEntries frozen)
      rw [ih]

/-- Every open and every frozen slot sits at a child below `used`. -/
def GrayTailSourceSlots {n b : Nat} (used : Nat)
    (st : GrayTailState n b) : Prop :=
  (forall s, s ∈ st.slots -> s.2.1.val < used) ∧
    forall p, p ∈ st.frozen -> forall s, s ∈ p.slots ->
      s.2.1.val < used

/-- The initial slots of a round sit at children below `used`. -/
lemma grayTailSlots_used {n b used round : Nat}
    {s : GrayTailSlot n b} (hs : s ∈ grayTailSlots n b used round) :
    s.2.1.val < used := by
  unfold grayTailSlots at hs
  split at hs
  · simp only [List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_finRange] at hs
    obtain ⟨i, -, c, hc, rfl⟩ := hs
    exact of_decide_eq_true hc.2
  · simp at hs

/-- The slots carried into the next round sit at children below `used`. -/
lemma grayTailNextSlots_used {n b e used round : Nat}
    {threshold : Rat} {A : Allocation} {frozen : GrayTailFrozen n b}
    {sm : FamilyServerMove} {s : GrayTailSlot n b}
    (hs : s ∈ grayTailNextSlots e used round threshold A frozen sm) :
    s.2.1.val < used := by
  unfold grayTailNextSlots at hs
  split at hs
  · simp only [List.mem_flatMap, List.mem_map] at hs
    obtain ⟨i, -, c, hc, rfl⟩ := hs
    have hp := (List.mem_filter.mp hc).2
    simp only [Bool.and_eq_true] at hp
    exact of_decide_eq_true hp.1.1
  · simp at hs

/-- The initial tail state only uses children below `2 ^ (e - a)`. -/
lemma grayTailSourceSlots_initial (n b a e : Nat) (A : Allocation) :
    GrayTailSourceSlots (2 ^ (e - a))
      (grayTailInitialState n b a e A) := by
  constructor
  · intro s hs
    exact grayTailSlots_used hs
  · simp [grayTailInitialState]

/-- A tail step keeps every slot at a child below `2 ^ (e - a)`. -/
lemma grayTailSourceSlots_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hst : GrayTailSourceSlots (2 ^ (e - a)) st) :
    GrayTailSourceSlots (2 ^ (e - a))
      (grayTailStep q L a e sigma A st sm) := by
  unfold grayTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, if_false]
  split
  · exact hst
  · split
    · exact hst
    · split
      · let p : GrayTailRound n b :=
          { serverTime := st.time
            roundIndex := st.frozen.length
            epsDepth := grayTailRoundEps q L e st.frozen.length
            slots := st.slots
            move := grayTailCurrentMove q L e sigma st
            allocated := grayTailLocalAllocatedList
              (grayTailLocalServerMove
                (grayTailRoundDelta q L e st.frozen.length) st.slots sm)
            unavailable := st.unavailable }
        have hfrozen : forall r, r ∈ st.frozen ++ [p] ->
            forall s, s ∈ r.slots -> s.2.1.val < 2 ^ (e - a) := by
          intro r hr s hs
          rcases List.mem_append.mp hr with hr | hr
          · exact hst.2 r hr s hs
          · have hrp : r = p := by simpa using hr
            subst r
            exact hst.1 s hs
        constructor
        · intro s hs
          exact grayTailNextSlots_used hs
        · exact hfrozen
      · exact hst
/-- Every state of a tail run only uses children below `2 ^ (e - a)`. -/
theorem grayTailSourceSlots_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailSourceSlots (2 ^ (e - a))
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayTailSourceSlots_initial n b a e A
  | succ t ih =>
      rw [grayTailStateAt_succ]
      exact grayTailSourceSlots_step q L a e sigma A _ (sm t) ih

/-- Every frozen entry of a tail run sits at a child below `2 ^ (e - a)`. -/
lemma grayTailFrozenEntries_used {n b q L a e : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {t : Nat}
    {z : GrayTailSlot n b × ClientMove}
    (hz : z ∈ grayTailFrozenEntries
      (grayTailStateAt q L a e sigma A sm t).frozen) :
    z.1.2.1.val < 2 ^ (e - a) := by
  unfold grayTailFrozenEntries at hz
  rw [List.mem_flatMap] at hz
  obtain ⟨p, hp, hz⟩ := hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  exact (grayTailSourceSlots_stateAt q L a e sigma A sm t).2
    p hp (p.slots.get j) (List.get_mem p.slots j)

/-- The sum of the frozen son bases over all clients and all source children below `used`. -/
def grayTailFrozenSourceBaseSum {n b : Nat} (used : Nat)
    (frozen : GrayTailFrozen n b) : Rat :=
  ∑ i : Fin n, ∑ c : Fin b,
    if c.val < used then grayTailFrozenSonBase frozen i c else 0

/-- For a tail run, the frozen source base sum is the total frozen request. -/
lemma grayTailFrozenSourceBaseSum_eq_requestSum
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {t : Nat} :
    grayTailFrozenSourceBaseSum (2 ^ (e - a))
        (grayTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen =
      grayTailFrozenRequestSum
        (grayTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen := by
  rw [grayTailFrozenRequestSum_eq_entries]
  unfold grayTailFrozenSourceBaseSum grayTailFrozenSonBase
  apply grayTailSourceBaseSum_eq_entryRequestSum
  intro z hz
  exact grayTailFrozenEntries_used hz

/-- There is a slot `s ∈ slots` with `s.1 = i` and `s.2.1 = c`: some slot of the list sits at the
son `c` of the outer root `i`. -/
def GrayTailHasKey {n b : Nat}
    (slots : List (GrayTailSlot n b)) (i : Fin n) (c : Fin b) : Prop :=
  exists s, s ∈ slots ∧ s.1 = i ∧ s.2.1 = c

/-- A child no entry sits at has son base zero. -/
lemma grayTailSonBase_eq_zero_of_no_match {n b : Nat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    (i : Fin n) (c : Fin b)
    (h : forall z, z ∈ entries -> z.1.1 ≠ i ∨ z.1.2.1 ≠ c) :
    grayTailSonBase entries i c = 0 := by
  induction entries with
  | nil => rfl
  | cons z rest ih =>
      unfold grayTailSonBase
      simp only [List.foldr_cons]
      have hz := h z (by simp)
      have hrest : forall w, w ∈ rest ->
          w.1.1 ≠ i ∨ w.1.2.1 ≠ c := by
        intro w hw
        exact h w (by simp [hw])
      change (if z.1.1 = i ∧ z.1.2.1 = c then
        getReq z.2 [] + grayTailSonBase rest i c
        else grayTailSonBase rest i c) = 0
      rw [show grayTailSonBase rest i c = 0 from ih hrest]
      split_ifs with hsame
      · rcases hz with hz | hz
        · exact (hz hsame.1).elim
        · exact (hz hsame.2).elim
      · rfl

/-- A child no open slot sits at has son base zero. -/
lemma grayTailSonBase_eq_zero_of_not_hasKey {n b : Nat}
    {slots : List (GrayTailSlot n b)} {move : FamilyClientMove}
    (i : Fin n) (c : Fin b) (h : ¬ GrayTailHasKey slots i c) :
    grayTailSonBase (grayTailSlotEntries slots move) i c = 0 := by
  apply grayTailSonBase_eq_zero_of_no_match
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  by_contra hsame
  push_neg at hsame
  apply h
  exact ⟨slots.get j, List.get_mem slots j, hsame.1, hsame.2⟩

/-- In a round meeting the pointwise gray goal, every slot entry requests a nonnegative amount at
the root. -/
lemma grayTailSlotEntries_root_nonneg_global {n b : Nat}
    {kappa beta : Rat} {epsDepth deltaDepth : Nat}
    {A : Allocation} {slots : List (GrayTailSlot n b)}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hk : 0 < kappa) (hbeta : 0 <= beta)
    (hpoint : familyPointwiseGrayAtB kappa beta epsDepth deltaDepth
      slots.length A move server = true) :
    forall p, p ∈ grayTailSlotEntries slots move -> 0 <= getReq p.2 [] := by
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  have hj := (familyPointwiseGrayAtB.component hpoint j.isLt).1
  unfold getFamilyReq at hj
  nlinarith

/-- A son base built from nonnegative root requests is nonnegative. -/
lemma grayTailSonBase_nonneg_global {n b : Nat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    {i : Fin n} {c : Fin b}
    (hreq : ∀ p ∈ entries, 0 ≤ getReq p.2 []) :
    0 ≤ grayTailSonBase entries i c := by
  induction entries with
  | nil => simp [grayTailSonBase]
  | cons p entries ih =>
      have hp := hreq p (by simp)
      have ht : ∀ q ∈ entries, 0 ≤ getReq q.2 [] := by
        intro q hq
        exact hreq q (by simp [hq])
      unfold grayTailSonBase at ih ⊢
      simp only [List.foldr_cons]
      split_ifs
      · exact add_nonneg hp (ih ht)
      · exact ih ht

/-- Among nonnegative entries, each entry at a child is bounded by that child's son base. -/
lemma getReq_le_grayTailSonBase_of_mem_global {n b : Nat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    {slot : GrayTailSlot n b} {move : ClientMove}
    {i : Fin n} {c : Fin b}
    (hreq : ∀ p ∈ entries, 0 ≤ getReq p.2 [])
    (hmem : (slot, move) ∈ entries)
    (hi : slot.1 = i) (hc : slot.2.1 = c) :
    getReq move [] ≤ grayTailSonBase entries i c := by
  induction entries with
  | nil => simp at hmem
  | cons p entries ih =>
      rcases List.mem_cons.mp hmem with hp | ht
      · subst p
        have htail : 0 ≤ grayTailSonBase entries i c :=
          grayTailSonBase_nonneg_global (fun q hq => hreq q (by simp [hq]))
        unfold grayTailSonBase
        simp only [List.foldr_cons]
        rw [if_pos ⟨hi, hc⟩]
        exact le_add_of_nonneg_right htail
      · have htail : ∀ q ∈ entries, 0 ≤ getReq q.2 [] := by
          intro q hq
          exact hreq q (by simp [hq])
        have hle := ih htail ht
        unfold grayTailSonBase
        simp only [List.foldr_cons]
        split_ifs
        · exact le_trans hle
            (le_add_of_nonneg_left (hreq p (by simp)))
        · exact hle

/-- In a round meeting the pointwise gray goal, every occupied child gains at least `beta` after
amplification by `kappa`. -/
lemma grayTailSlotEntries_selected_progress_global {n b : Nat}
    {kappa beta : Rat} {epsDepth deltaDepth : Nat}
    {A : Allocation} {slots : List (GrayTailSlot n b)}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hk : 0 < kappa) (hbeta : 0 ≤ beta)
    (hpoint : familyPointwiseGrayAtB kappa beta epsDepth deltaDepth
      slots.length A move server = true)
    (j : Fin slots.length) (i : Fin n) (c : Fin b)
    (hi : (slots.get j).1 = i) (hc : (slots.get j).2.1 = c) :
    beta ≤ kappa * grayTailSonBase
      (grayTailSlotEntries slots move) i c := by
  have hcomponent := (familyPointwiseGrayAtB.component hpoint j.isLt).1
  have hselected :
      getFamilyReq move j.val [] ≤ grayTailSonBase
        (grayTailSlotEntries slots move) i c := by
    apply getReq_le_grayTailSonBase_of_mem_global
      (grayTailSlotEntries_root_nonneg_global hk hbeta hpoint)
    · exact List.mem_ofFn.mpr ⟨j, rfl⟩
    · exact hi
    · exact hc
  unfold getFamilyReq at hcomponent hselected
  exact le_trans hcomponent
    (mul_le_mul_of_nonneg_left hselected hk.le)

/-- The son base is additive over concatenation of entries. -/
lemma grayTailSonBase_append_globalEntries {n b : Nat}
    (left right : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (left ++ right) i c =
      grayTailSonBase left i c + grayTailSonBase right i c := by
  induction left with
  | nil => simp [grayTailSonBase]
  | cons p left ih =>
      simp only [List.cons_append]
      unfold grayTailSonBase at ih ⊢
      simp only [List.foldr_cons]
      split_ifs
      · rw [ih]; ring
      · rw [ih]

/-- A child carried into the next round has frozen son base at most the threshold. -/
lemma grayTailNextSlots_base_le_global {n b e used round : Nat}
    {threshold : Rat} {A : Allocation} {frozen : GrayTailFrozen n b}
    {sm : FamilyServerMove} {s : GrayTailSlot n b}
    (hs : s ∈ grayTailNextSlots e used round threshold A frozen sm) :
    grayTailFrozenSonBase frozen s.1 s.2.1 <= threshold := by
  unfold grayTailNextSlots at hs
  split at hs
  · simp only [List.mem_flatMap] at hs
    obtain ⟨i, _hi, hs⟩ := hs
    simp only [List.mem_map] at hs
    obtain ⟨c, hc, rfl⟩ := hs
    have hpred := (List.mem_filter.mp hc).2
    simp only [Bool.and_eq_true] at hpred
    have hnlt : ¬threshold < grayTailFrozenSonBase frozen i c := by
      intro hlt
      have htrue : decide
          (threshold < grayTailFrozenSonBase frozen i c) = true := by
        simp [hlt]
      have hnot := hpred.1.2
      rw [htrue] at hnot
      norm_num at hnot
    exact le_of_not_gt hnlt
  · simp at hs

private def globalGrayTailSonKey {n b : Nat} (s : GrayTailSlot n b) :
    Fin n × Fin b := (s.1, s.2.1)

private lemma globalGrayTailSonKeys_nodup {n b r : Nat}
    {slots : List (GrayTailSlot n b)} (hnodup : slots.Nodup)
    (hround : forall s, s ∈ slots -> s.2.2.val = r) :
    (slots.map globalGrayTailSonKey).Nodup := by
  induction slots with
  | nil => simp
  | cons s rest ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨u, hu, hkey⟩ := List.mem_map.mp hmem
        apply hnodup.1
        have hfirst : u.1 = s.1 :=
          congrArg (fun z : Fin n × Fin b => z.1) hkey
        have hsecond : u.2.1 = s.2.1 :=
          congrArg (fun z : Fin n × Fin b => z.2) hkey
        have hthirdVal : u.2.2.val = s.2.2.val := by
          rw [hround u (by simp [hu]), hround s (by simp)]
        have hthird : u.2.2 = s.2.2 := Fin.ext hthirdVal
        have hus : u = s := Prod.ext hfirst (Prod.ext hsecond hthird)
        simpa [hus] using hu
      · apply ih hnodup.2
        intro u hu
        exact hround u (by simp [hu])

private lemma globalGrayTailEntryKeys_nodup {n b r : Nat}
    {slots : List (GrayTailSlot n b)} {move : FamilyClientMove}
    (hnodup : slots.Nodup)
    (hround : forall s, s ∈ slots -> s.2.2.val = r) :
    ((grayTailSlotEntries slots move).map
      (fun z => globalGrayTailSonKey z.1)).Nodup := by
  have hkeys := globalGrayTailSonKeys_nodup hnodup hround
  rw [← map_fst_grayTailSlotEntries slots move] at hkeys
  simpa only [List.map_map, Function.comp_def] using hkeys

private lemma globalGrayTailSonBase_le_of_keys_nodup {n b : Nat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    {cap : Rat} (hcap0 : 0 <= cap)
    (hkeys : (entries.map (fun z => globalGrayTailSonKey z.1)).Nodup)
    (hnonneg : forall z, z ∈ entries -> 0 <= getReq z.2 [])
    (hcap : forall z, z ∈ entries -> getReq z.2 [] <= cap)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase entries i c <= cap := by
  induction entries with
  | nil => simpa [grayTailSonBase] using hcap0
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

/-- In a round meeting the robust gray goal whose slots share one round index, no son base
exceeds `dyadicScale (grayCallDepth q e)`. -/
lemma grayTailRoundSonBase_le_callScale_of_goal
    {n b q L e r : Nat} {A : Allocation}
    {slots : List (GrayTailSlot n b)} {move : FamilyClientMove}
    {server : FamilyServerMove}
    (hgoal : familyRobustGrayGoalAtB (halfAmplification q)
      ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
      (grayTailRoundEps q L e r) (grayTailRoundDelta q L e r)
      slots.length A move server = true)
    (hnodup : slots.Nodup)
    (hround : forall s, s ∈ slots -> s.2.2.val = r)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries slots move) i c <=
      dyadicScale (grayCallDepth q e) := by
  have hpoint := familyRobustGrayGoalAtB.to_pointwise hgoal
  apply globalGrayTailSonBase_le_of_keys_nodup
    (cap := dyadicScale (grayCallDepth q e))
    (dyadicScale_pos _).le
    (globalGrayTailEntryKeys_nodup hnodup hround)
  · apply grayTailSlotEntries_root_nonneg_global
      (kappa := halfAmplification q)
      (beta := (3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
      (epsDepth := grayTailRoundEps q L e r)
      (deltaDepth := grayTailRoundDelta q L e r)
      (A := A) (server := server)
      (halfAmplification_pos q)
      (mul_nonneg (by norm_num)
        (dyadicScale_pos (grayCallDepth q e)).le)
    exact hpoint
  · intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    have hj := (familyPointwiseGrayAtB.component hpoint j.isLt).2
    unfold getFamilyReq at hj
    calc
      getReq (familyClientMoveAt move j.val) [] <=
          (4 / 3 : Rat) * ((3 / 4 : Rat) *
            dyadicScale (grayCallDepth q e)) := hj
      _ = dyadicScale (grayCallDepth q e) := by ring

/-- Freezing a round adds that round's son base to the frozen son base. -/
lemma grayTailFrozenSonBase_append_global {n b : Nat}
    (frozen : GrayTailFrozen n b) (p : GrayTailRound n b)
    (i : Fin n) (c : Fin b) :
    grayTailFrozenSonBase (frozen ++ [p]) i c =
      grayTailFrozenSonBase frozen i c +
        grayTailSonBase (grayTailSlotEntries p.slots p.move) i c := by
  unfold grayTailFrozenSonBase grayTailFrozenEntries
  rw [List.flatMap_append]
  simp only [List.flatMap_singleton]
  exact grayTailSonBase_append_globalEntries _ _ i c

/-- If every frozen round gains at least `beta` at a child after amplification, the frozen son
base grows linearly in the number of rounds. -/
lemma grayTailFrozenSonBase_progress_of_each {n b : Nat}
    {kappa beta : Rat} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b}
    (hgain : ∀ p ∈ frozen,
      beta ≤ kappa *
        grayTailSonBase (grayTailSlotEntries p.slots p.move) i c) :
    (frozen.length : Rat) * beta ≤
      kappa * grayTailFrozenSonBase frozen i c := by
  induction frozen using List.reverseRecOn with
  | nil =>
      simp [grayTailFrozenSonBase, grayTailFrozenEntries,
        grayTailSonBase]
  | append_singleton frozen p ih =>
      have hprev : ∀ r ∈ frozen,
          beta ≤ kappa *
            grayTailSonBase (grayTailSlotEntries r.slots r.move) i c := by
        intro r hr
        exact hgain r (by simp [hr])
      have hp := hgain p (by simp)
      have hi := ih hprev
      rw [grayTailFrozenSonBase_append_global]
      simp only [List.length_append, List.length_singleton, Nat.cast_add,
        Nat.cast_one]
      nlinarith

/-- The service threshold of the tail is nonnegative. -/
lemma grayTail_threshold_nonneg_global (q e : Nat) :
    (0 : Rat) <= dyadicScale e -
      dyadicScale e / (6 * halfAmplification q) := by
  rw [sub_nonneg, div_le_iff₀
    (mul_pos (by norm_num) (halfAmplification_pos q))]
  have heps := (dyadicScale_pos e).le
  have hk : (1 : Rat) <= halfAmplification q := by
    simp only [halfAmplification]
    have hq : (0 : Rat) <= (q : Rat) := by positivity
    linarith
  have hfac : (1 : Rat) <= 6 * halfAmplification q := by nlinarith
  have hmul := mul_nonneg heps (sub_nonneg.mpr hfac)
  nlinarith

end Kolmogorov
