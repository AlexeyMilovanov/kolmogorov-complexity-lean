import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Goal
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailController

/-!
# V2 block controller core (Reading C)

Blueprint Stage C, audit verdict Reading C.  The wide-block advantage
controller.  It reuses the committed `GrayTailState` / `GrayTailRound` (the
round's `epsDepth` field already stores the block anchor `ε_r`), and differs
from the flattened `grayChargedTailStep` in exactly three places:

* **wide next-slots** `grayBlockNextSlots`: each surviving `(i, c)` fibre
  spawns the whole grandson block `[offset r, offset r + mult r)` (via
  `grayAdvBlockGrandsons`) instead of the single grandson `r`;
* the **block acceptance goal** `grayChargedBlockGoalAtB` (α-depth
  `dyadicScale ε_r`) instead of `grayChargedTailGoalAtB` (α-depth
  `dyadicScale callDepth`);
* the **scale-aligned child call** `grayBlockCurrentMove` at outer anchor
  `ε_r` (so a child rung's outer scale equals the parent round anchor — the
  fix the export-anchor audit required).

The frozen record, the per-round snapshot harvest, `done'`, and the history
are unchanged from the committed step.
-/

namespace Kolmogorov

/-- The scale-aligned current move: the child rung is invoked at outer anchor
`ε_r` (block anchor), with its own bin one per-round budget deeper. -/
def grayBlockCurrentMove {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) : FamilyClientMove :=
  let r := st.frozen.length
  sigma (grayTailRoundEps q L e r) (grayTailRoundEps q L e r + L)
    st.unavailable st.slots.length st.history

/-- The wide advantage next-slots: like `grayTailNextSlots`, but every
surviving `(i, c)` fibre carries the whole grandson block of round `round`. -/
def grayBlockNextSlots {n b : ℕ}
    (q L e used round : ℕ) (threshold : ℚ) (A : Allocation)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) :
    List (GrayTailSlot n b) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange b).filter fun c =>
      c.val < used &&
      !(decide (threshold < grayTailFrozenSonBase frozen i c)) &&
      !(getTailFamilyReserve e b A n i.val sm [c.val]).isSome).flatMap fun c =>
        (grayAdvBlockGrandsons b q L round).map fun g => (i, c, g)

/-- Every wide next-slot has a grandson in the round's block range. -/
lemma grayBlockNextSlots_mem_range {n b : ℕ}
    {q L e used round : ℕ} {threshold : ℚ} {A : Allocation}
    {frozen : GrayTailFrozen n b} {sm : FamilyServerMove}
    {sl : GrayTailSlot n b}
    (hsl : sl ∈ grayBlockNextSlots q L e used round threshold A frozen sm) :
    grayInAdvBlock q L round sl.2.2.val := by
  rw [grayBlockNextSlots, List.mem_flatMap] at hsl
  obtain ⟨i, -, hsl⟩ := hsl
  rw [List.mem_flatMap] at hsl
  obtain ⟨c, -, hsl⟩ := hsl
  rw [List.mem_map] at hsl
  obtain ⟨g, hg, rfl⟩ := hsl
  exact grayAdvBlockGrandsons_mem_range hg

/-- The wide next-slots are nodup (mirrors `grayAdvBlockSlots_nodup`). -/
lemma grayBlockNextSlots_nodup {n b : ℕ}
    (q L e used round : ℕ) (threshold : ℚ) (A : Allocation)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) :
    (grayBlockNextSlots q L e used round threshold A frozen sm).Nodup := by
  unfold grayBlockNextSlots
  refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
  · intro i _
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro c _
      exact (grayAdvBlockGrandsons_nodup b q L round).map fun g g' h =>
        by exact congrArg (fun p => p.2.2) h
    · refine ((List.nodup_finRange b).filter _).imp ?_
      intro c c' hcc x hxc hxc'
      simp only [List.mem_map] at hxc hxc'
      obtain ⟨gc, _, rfl⟩ := hxc
      obtain ⟨gc', _, h⟩ := hxc'
      exact hcc (congrArg (fun p => p.2.1) h).symm
  · refine (List.nodup_finRange n).imp ?_
    intro i j hij x hxi hxj
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_finRange] at hxi hxj
    obtain ⟨ci, _, gi, _, rfl⟩ := hxi
    obtain ⟨cj, _, gj, _, h⟩ := hxj
    exact hij (congrArg Prod.fst h).symm

/-- The V2 wide-block advantage step: the tail step of `grayChargedTailStep` with the block
acceptance goal, the scale-aligned current move and the wide next-slots; the frozen record and
the per-round harvest are unchanged. -/
def grayChargedBlockTailStep {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove) : GrayTailState n b :=
  if grayTailWaitingB st then
    if grayTailAllAnchoredB e A st.anchoringSlots sm then
      { st with
        time := st.time + 1
        roundStart := st.time + 1
        done := true
        slots := []
        history := ([], []) }
    else
      { st with
        time := st.time + 1
        roundStart := st.time + 1
        history := ([], []) }
  else if st.done then { st with time := st.time + 1 }
  else if st.slots.isEmpty then { st with time := st.time + 1 }
  else
    let r := st.frozen.length
    let epsRound := grayTailRoundEps q L e r
    let deltaRound := grayTailRoundDelta q L e r
    let current := grayBlockCurrentMove q L e sigma st
    let localSM := grayTailLocalServerMove deltaRound st.slots sm
    if grayChargedBlockGoalAtB q L e r st.slots.length
        st.unavailable current localSM then
      let allocated := grayTailLocalAllocatedList localSM
      let frozen' := st.frozen ++
        [{ serverTime := st.time
           roundIndex := r
           epsDepth := epsRound
           slots := st.slots
           move := current
           allocated := allocated
           unavailable := st.unavailable }]
      let threshold := dyadicScale e -
        dyadicScale e / (6 * halfAmplification q)
      let source := grayChargedSourceCount a e
      let candidates := grayBlockNextSlots q L e source frozen'.length threshold A
        frozen' sm
      let unavailable' := A ++
        grayHarvest (grayTailRoundDelta q L e frozen'.length) candidates n sm
      let done' := grayTailGlobalQuarterB source
          (grayTailNextSlots e source frozen'.length threshold A frozen' sm) ||
        decide (grayChargedAdvantageRoundCount q <= frozen'.length)
      { time := st.time + 1
        roundStart := st.time + 1
        done := done'
        frozen := frozen'
        unavailable := unavailable'
        slots := candidates
        anchoringSlots := []
        history := ([], []) }
    else
      { st with
        time := st.time + 1
        history :=
          (st.history.1 ++ [current], st.history.2 ++ [localSM]) }

/-- The V2 wide-block initial state: round 0's whole grandson block for every
`(i, c)` source fibre. -/
def grayChargedBlockTailInitialState (n b a e q L : Nat) (A : Allocation) :
    GrayTailState n b where
  time := 0
  roundStart := 0
  done := false
  frozen := []
  unavailable := A
  slots := grayAdvBlockSlots n b (grayChargedSourceCount a e) q L 0
  anchoringSlots := []
  history := ([], [])

/-- The V2 wide-block advantage fold over a finite server history. -/
def grayChargedBlockTailFold {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (history : List FamilyServerMove) : GrayTailState n b :=
  history.foldl (grayChargedBlockTailStep q L a e sigma A)
    (grayChargedBlockTailInitialState n b a e q L A)

/-- Every wide next-slot uses a source son `< used`. -/
lemma grayBlockNextSlots_source {n b : ℕ}
    {q L e used round : ℕ} {threshold : ℚ} {A : Allocation}
    {frozen : GrayTailFrozen n b} {sm : FamilyServerMove}
    {sl : GrayTailSlot n b}
    (hsl : sl ∈ grayBlockNextSlots q L e used round threshold A frozen sm) :
    sl.2.1.val < used := by
  rw [grayBlockNextSlots, List.mem_flatMap] at hsl
  obtain ⟨i, -, hsl⟩ := hsl
  rw [List.mem_flatMap] at hsl
  obtain ⟨c, hc, hsl⟩ := hsl
  rw [List.mem_map] at hsl
  obtain ⟨g, -, rfl⟩ := hsl
  have := (List.mem_filter.mp hc).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1

/-- Wide next-slots keep only sons below the threshold. -/
lemma grayBlockNextSlots_base_le_global {n b : ℕ}
    {q L e used round : ℕ} {threshold : ℚ} {A : Allocation}
    {frozen : GrayTailFrozen n b} {sm : FamilyServerMove}
    {sl : GrayTailSlot n b}
    (hsl : sl ∈ grayBlockNextSlots q L e used round threshold A frozen sm) :
    grayTailFrozenSonBase frozen sl.1 sl.2.1 ≤ threshold := by
  rw [grayBlockNextSlots, List.mem_flatMap] at hsl
  obtain ⟨i, -, hsl⟩ := hsl
  rw [List.mem_flatMap] at hsl
  obtain ⟨c, hc, hsl⟩ := hsl
  rw [List.mem_map] at hsl
  obtain ⟨g, -, rfl⟩ := hsl
  have := (List.mem_filter.mp hc).2
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
  exact not_lt.mp this.1.2

end Kolmogorov
