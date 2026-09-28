import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafBGeom

/-!
# Leaf B of the tail frontier, decomposed

`grayTail_terminal_reserves` (Leaf B) produces, for one terminal snapshot, an
ordinary `IsTailFamilyReserve` for every inactive source son -- each at its own
time, all bounded by one common later horizon `U` -- together with exact
freshness against every frozen gray cell except the owner-charged one.

The decomposition keeps the two exact controller exits apart and isolates the
purely finite "many sons, one horizon" step:

```text
B0a grayTail_ownerIndex_eq_roundIndex_of_split  owner bookkeeping    (proved)
B0b grayTail_sonReserveWitness_of_anchored      witness assembly     (proved)
B1  grayTail_reserveExit_son_witness     reserve exit (open architecture boundary)
B2  grayTail_thresholdExit_son_witness   threshold exit               (proved)
B3  grayTail_exists_common_horizon       finite common horizon        (proved)
```

The geometry both witnesses rest on -- spatial separation of a reserve from a
foreign slot at an arbitrary server time, and freshness against the son's own
earlier calls -- is proved in `GacsDayLadderTailLeafBGeom`.  The reserve-exit
branch remains open: the controller currently uses the unanchored search, which
does not provide the later-time cross-slot information needed by `B1`.  It must
be repaired at the controller/search interface, not by upgrading a reserve.

Nothing here assumes that a reserve persists, that reserves exist at the
terminal time `T`, or the rejected anchored package: `B1` and `B2` each stay at
their own son-dependent time, and `B3` only bounds those times by a common
later `U`.  Freshness comes from the exact exits and their
`prefix_allocations_fresh` certificates, never from persistence.
-/

namespace Kolmogorov

open scoped BigOperators

/-- The per-son datum Leaf B has to produce: an ordinary tail-family reserve at
one son-dependent time, exactly fresh against every frozen recursive call
except the owner-charged component of the son's own owner round. -/
def GrayTailSonReserveWitness (q L a e n : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : ℕ → FamilyServerMove) (T : ℕ)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) (t : ℕ) (R : BitString) :
    Prop :=
  IsTailFamilyReserve e (grayTailBranch q L a e) A n i.val (sm t) [c.val] R ∧
    (∀ p ∈ (grayTailRunState q L a e n sigma A sm T).frozen,
      ∀ j : Fin p.slots.length,
        (p.roundIndex ≠
            grayTailOwnerIndex (grayTailRunState q L a e n sigma A sm T).frozen i c ∨
          (p.slots.get j).1 ≠ i ∨ (p.slots.get j).2.1 ≠ c) →
        ∀ z ∈ getFamilyAlloc
            (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm p.serverTime))
            j.val [],
          ¬ (R <+: z ∨ z <+: R))

/-! ### B0: bookkeeping and assembly, shared by both exits -/

/-- **Child B0a (proved).**  The owner index of an inactive son is the recorded
round index of the round at which the son participates for the last time.

The exact exits hand out such a decomposition; `last_split_unique` identifies
it with the one recorded by `GrayTailTerminalData.owner_split`, and
`GrayTailTerminalData.round_index_eq` converts the position into the recorded
round index. -/
theorem grayTail_ownerIndex_eq_roundIndex_of_split
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hdata : GrayTailTerminalData q L a e n sigma A sm T)
    {i : Fin n} {c : Fin (grayTailBranch q L a e)} (hc : c.val < 2 ^ (e - a))
    (hinactive : ¬ GrayTailHasSon (grayTailRunState q L a e n sigma A sm T).slots i c)
    {pre post : GrayTailFrozen n (grayTailBranch q L a e)}
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hsplit : (grayTailRunState q L a e n sigma A sm T).frozen = pre ++ p :: post)
    (hson : GrayTailRoundHasSon p i c)
    (hpost : ∀ r ∈ post, ¬ GrayTailRoundHasSon r i c) :
    grayTailOwnerIndex (grayTailRunState q L a e n sigma A sm T).frozen i c =
      p.roundIndex := by
  obtain ⟨pre', p', post', hsplit', hlen', hson', hpost'⟩ :=
    hdata.owner_split i c hc hinactive
  obtain ⟨hlen, -⟩ := last_split_unique hsplit hsplit' hson hson' hpost hpost'
  have hlt : pre.length < (grayTailRunState q L a e n sigma A sm T).frozen.length := by
    rw [hsplit]; simp
  have hget : (grayTailRunState q L a e n sigma A sm T).frozen.get ⟨pre.length, hlt⟩ = p := by
    rw [List.get_eq_getElem, List.getElem_of_eq hsplit]
    simp
  have hround := hdata.round_index_eq pre.length hlt
  rw [hget] at hround
  rw [← hlen', ← hlen, hround]

/-- **Child B0b (proved).**  An *anchored* reserve of the son, together with
freshness against the son's own calls outside its owner round, already is a
son reserve witness.

Everything displayed at a slot other than the son's own is separated from the
reserve purely spatially, by `grayTail_anchoredReserve_fresh_of_slot_ne`; the
remaining calls sit at the son's own slot, and the excused ones are exactly
those of the owner round. -/
theorem grayTail_sonReserveWitness_of_anchored
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {i : Fin n} {c : Fin (grayTailBranch q L a e)} {t : ℕ} {R : BitString}
    (hR : IsAnchoredTailFamilyReserve e (grayTailBranch q L a e) A n i.val
      (sm t) [c.val] R)
    (hown : ∀ p ∈ (grayTailRunState q L a e n sigma A sm T).frozen,
      p.roundIndex ≠
          grayTailOwnerIndex (grayTailRunState q L a e n sigma A sm T).frozen i c →
      ∀ j : Fin p.slots.length,
        (p.slots.get j).1 = i → (p.slots.get j).2.1 = c →
        ∀ d ∈ getFamilyAlloc
          (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm p.serverTime))
          j.val [],
          ¬ (R <+: d ∨ d <+: R)) :
    GrayTailSonReserveWitness q L a e n sigma A sm T i c t R := by
  classical
  refine ⟨hR.1, ?_⟩
  intro p hp j hcond z hz
  by_cases hslot : (p.slots.get j).1 = i ∧ (p.slots.get j).2.1 = c
  · have hne : p.roundIndex ≠
        grayTailOwnerIndex (grayTailRunState q L a e n sigma A sm T).frozen i c := by
      rcases hcond with h | h | h
      · exact h
      · exact absurd hslot.1 h
      · exact absurd hslot.2 h
    exact hown p hp hne j hslot.1 hslot.2 z hz
  · have hne : (p.slots.get j).1 ≠ i ∨ (p.slots.get j).2.1 ≠ c := by
      by_cases h1 : (p.slots.get j).1 = i
      · exact Or.inr fun h2 => hslot ⟨h1, h2⟩
      · exact Or.inl h1
    exact grayTail_anchoredReserve_fresh_of_slot_ne hsm hR p j hne hz

/-! ### B1: sons that left through a reserve exit -/

/-- A persistent reserve exit records the last owner
round and a later reserve time dominating every frozen round.  Own-slot calls
before the owner are fresh by its no-reserve checkpoint; the owner call is the
allowed exception; no later own-slot call exists; and foreign calls are transported
forward to the recorded reserve time before spatial reserve separation is applied. -/
theorem grayTail_reserveExit_son_witness
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (_ha : 1 ≤ a) (_hae : a ≤ e)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hdata : GrayTailTerminalData q L a e n sigma A sm T)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) (hc : c.val < 2 ^ (e - a))
    (hinactive : ¬ GrayTailHasSon (grayTailRunState q L a e n sigma A sm T).slots i c)
    (hexit : GrayTailPersistentReserveExit e A sm
      (grayTailRunState q L a e n sigma A sm T).frozen i c) :
    ∃ t R, GrayTailSonReserveWitness q L a e n sigma A sm T i c t R := by
  classical
  obtain ⟨pre, p, post, t, R, hsplit, hson, hR, hmax, hcheck, hpost⟩ := hexit
  have howner :
      grayTailOwnerIndex
          (grayTailRunState q L a e n sigma A sm T).frozen i c =
        p.roundIndex :=
    grayTail_ownerIndex_eq_roundIndex_of_split hdata hc hinactive hsplit hson hpost
  have hpMem : p ∈ (grayTailRunState q L a e n sigma A sm T).frozen := by
    rw [hsplit]
    simp
  have hpTime : p.serverTime ≤ t := hmax p hpMem
  refine ⟨t, R, hR, ?_⟩
  intro r hr j hcond z hz
  by_cases hslot : (r.slots.get j).1 = i ∧ (r.slots.get j).2.1 = c
  · have hne : r.roundIndex ≠
        grayTailOwnerIndex
          (grayTailRunState q L a e n sigma A sm T).frozen i c := by
      rcases hcond with h | h | h
      · exact h
      · exact absurd hslot.1 h
      · exact absurd hslot.2 h
    rw [howner] at hne
    have hmem : r ∈ pre ++ p :: post := by
      rwa [hsplit] at hr
    have hrson : GrayTailRoundHasSon r i c :=
      ⟨r.slots.get j, List.get_mem r.slots j, hslot.1, hslot.2⟩
    rcases List.mem_append.mp hmem with hrpre | hrtail
    · have hcheckLate : pre = [] ∨ ∃ S,
          (∀ w, w ∈ pre → w.serverTime ≤ S) ∧ S ≤ t ∧
          (getTailFamilyReserve e (grayTailBranch q L a e) A n i.val
            (sm S) [c.val]).isNone := by
        rcases hcheck with hempty | ⟨S, hbound, hSp, hnone⟩
        · exact Or.inl hempty
        · exact Or.inr ⟨S, hbound, le_trans hSp hpTime, hnone⟩
      exact grayTail_prefix_alloc_fresh_of_checkpoint (L := L) hsm hR
        hcheckLate r hrpre j hslot.1 hslot.2 z hz
    · rcases List.mem_cons.mp hrtail with rfl | hrpost
      · exact absurd rfl hne
      · exact absurd hrson (hpost r hrpost)
  · have hne : (r.slots.get j).1 ≠ i ∨ (r.slots.get j).2.1 ≠ c := by
      by_cases hroot : (r.slots.get j).1 = i
      · exact Or.inr fun hsonEq => hslot ⟨hroot, hsonEq⟩
      · exact Or.inl hroot
    exact grayTail_reserve_fresh_of_slot_ne_before hsm hR r j (hmax r hr) hne hz
/-! ### B2: sons that left through a threshold exit -/

/-- A son which left the controller because its
accumulated request crossed the source threshold displays exactly `epsilon` at
the terminal move; since the outer play does not lose by a positive unserved
request, that request is served at some later time, and the served cylinder
yields an *anchored* tail-family reserve there.

The serve time is pushed past the owner round with `serves_mono_time`, so the
exit's checkpoint still precedes the reserve: freshness against the son's own
earlier calls is then `grayTail_prefix_alloc_fresh_of_checkpoint`, freshness
against every other slot is `grayTail_anchoredReserve_fresh_of_slot_ne`, and
the son's own owner round is the excused one by
`grayTail_ownerIndex_eq_roundIndex_of_split`.

The bounds `1 ≤ a` and `a ≤ e` turned out not to be needed; they are kept
because they are part of the leaf's prescribed interface. -/
theorem grayTail_thresholdExit_son_witness
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (_ha : 1 ≤ a) (_hae : a ≤ e)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotwin : ¬ familyClientWinsUnservedPositive n (2 * (q + 1))
      (grayTailBranch q L a e)
      (playClientFamily A n (grayTailStrategy q L a e sigma) sm) sm)
    (hdata : GrayTailTerminalData q L a e n sigma A sm T)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) (hc : c.val < 2 ^ (e - a))
    (hinactive : ¬ GrayTailHasSon (grayTailRunState q L a e n sigma A sm T).slots i c)
    (hthreshold : grayTailThreshold q e <
      grayTailFrozenSonBase (grayTailRunState q L a e n sigma A sm T).frozen i c)
    (hexit : GrayTailThresholdExit e A sm
      (grayTailRunState q L a e n sigma A sm T).frozen i c) :
    ∃ t R, GrayTailSonReserveWitness q L a e n sigma A sm T i c t R := by
  classical
  obtain ⟨pre, p, post, hsplit, hson, hcheck, hpost⟩ := hexit
  have howner :
      grayTailOwnerIndex (grayTailRunState q L a e n sigma A sm T).frozen i c =
        p.roundIndex :=
    grayTail_ownerIndex_eq_roundIndex_of_split hdata hc hinactive hsplit hson hpost
  have hnode : ∀ d ∈ ([c.val] : GacsDayNode), d < grayTailBranch q L a e := by
    intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact c.isLt
  -- the son displays exactly `epsilon` at the terminal move
  have hreq :
      getFamilyReq (playClientFamily A n (grayTailStrategy q L a e sigma) sm T)
        i.val [c.val] = dyadicScale e := by
    rw [hdata.play_eq T le_rfl, hdata.son_request_eq i c, if_pos hthreshold]
  -- so the outer play must serve it at some time
  have hserve : ∃ t, Serves (getFamilyAlloc (sm t) i.val [c.val])
      (getFamilyReq (playClientFamily A n (grayTailStrategy q L a e sigma) sm T)
        i.val [c.val]) := by
    by_contra hcon
    push_neg at hcon
    apply hnotwin
    refine ⟨i.val, i.isLt, T, [c.val], ?_, hnode, hcon, ?_⟩
    · simp
      omega
    · change 0 < getFamilyReq
        (playClientFamily A n (grayTailStrategy q L a e sigma) sm T) i.val [c.val]
      rw [hreq]
      exact dyadicScale_pos e
  obtain ⟨t0, ht0⟩ := hserve
  rw [hreq] at ht0
  -- push the serve time past the owner round, so the exit checkpoint precedes it
  have hserveLate : Serves (getFamilyAlloc (sm (max t0 p.serverTime)) i.val [c.val])
      (dyadicScale e) :=
    serves_mono_time (hsm.1 i.val i.isLt) (le_max_left t0 p.serverTime) ht0
  obtain ⟨R, hR⟩ := exists_anchoredTailFamilyReserve_of_serves hsm i.isLt hnode hserveLate
  refine ⟨max t0 p.serverTime, R,
    grayTail_sonReserveWitness_of_anchored (L := L) hsm hR ?_⟩
  intro r hr hne j hji hjc d hd
  rw [howner] at hne
  have hmem : r ∈ pre ++ p :: post := by rwa [hsplit] at hr
  have hrson : GrayTailRoundHasSon r i c :=
    ⟨r.slots.get j, List.get_mem r.slots j, hji, hjc⟩
  rcases List.mem_append.mp hmem with hrpre | hrtail
  · have hcheck' : pre = [] ∨ ∃ S, (∀ w, w ∈ pre → w.serverTime ≤ S) ∧
        S ≤ max t0 p.serverTime ∧
        (getTailFamilyReserve e (grayTailBranch q L a e) A n i.val (sm S) [c.val]).isNone := by
      rcases hcheck with hempty | ⟨S, hmax, hSp, hnone⟩
      · exact Or.inl hempty
      · exact Or.inr ⟨S, hmax, le_trans hSp (le_max_right t0 p.serverTime), hnone⟩
    exact grayTail_prefix_alloc_fresh_of_checkpoint (L := L) hsm hR.1 hcheck' r hrpre j
      hji hjc d hd
  · rcases List.mem_cons.mp hrtail with rfl | hrpost
    · exact absurd rfl hne
    · exact absurd hrson (hpost r hrpost)

/-! ### B3: one common horizon for finitely many son-dependent times -/

/-- Finitely many existential witnesses, each carrying
its own time, can be chosen simultaneously and bounded by one common horizon.

This is the only place where the "common later `U`" of Leaf B is produced; no
persistence of any witness is used. -/
theorem grayTail_exists_common_horizon {ι : Type*} [Finite ι]
    (Q : ι → Prop) (P : ι → ℕ → BitString → Prop)
    (h : ∀ j, Q j → ∃ t R, P j t R) :
    ∃ (U : ℕ) (time : ι → ℕ) (wit : ι → BitString),
      ∀ j, Q j → time j ≤ U ∧ P j (time j) (wit j) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose! time wit hP using h
  exact ⟨Finset.univ.sup time, time, wit,
    fun j hj => ⟨Finset.le_sup (Finset.mem_univ j), hP j hj⟩⟩

/-! ### Leaf B, assembled from its children -/

/-- Every inactive source son has an ordinary
tail-family reserve at a son-dependent time, bounded by one common later
horizon, exactly fresh against the non-owner frozen calls.

The exact exits of Leaf A split the sons into the two cases handled by `B1` and
`B2`; `B3` chooses all witnesses at once and produces the horizon. -/
theorem grayTail_terminal_reserves
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotwin : ¬ familyClientWinsUnservedPositive n (2 * (q + 1))
      (grayTailBranch q L a e)
      (playClientFamily A n (grayTailStrategy q L a e sigma) sm) sm)
    (hdata : GrayTailTerminalData q L a e n sigma A sm T) :
    ∃ U rtime reserve, GrayTailReservePackage q L a e n sigma A sm T U rtime reserve := by
  classical
  set Q : Fin n × Fin (grayTailBranch q L a e) → Prop := fun z =>
    z.2.val < 2 ^ (e - a) ∧
      ¬ GrayTailHasSon (grayTailRunState q L a e n sigma A sm T).slots z.1 z.2
    with hQ
  have hson : ∀ z : Fin n × Fin (grayTailBranch q L a e), Q z →
      ∃ t R, GrayTailSonReserveWitness q L a e n sigma A sm T z.1 z.2 t R := by
    rintro ⟨i, c⟩ ⟨hc, hinactive⟩
    rcases hdata.exits i c hc hinactive with ⟨hthr, hexit⟩ | ⟨hexit, _⟩
    · exact grayTail_thresholdExit_son_witness ha hae hsm hnotwin hdata i c hc
        hinactive hthr hexit
    · exact grayTail_reserveExit_son_witness ha hae hsm hdata i c hc hinactive hexit
  obtain ⟨U, time, wit, hU⟩ := grayTail_exists_common_horizon Q _ hson
  refine ⟨max T U, fun i c => time (i, c), fun i c => wit (i, c),
    le_max_left _ _, ?_⟩
  intro i c hc hinactive
  obtain ⟨hle, hwit⟩ := hU (i, c) ⟨hc, hinactive⟩
  exact ⟨le_trans hle (le_max_right _ _), hwit.1, hwit.2⟩

end Kolmogorov
