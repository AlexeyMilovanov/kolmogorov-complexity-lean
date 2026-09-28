import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReplayStrict
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Progress

/-!
# Strict V2 width invariant (fibre-count, mult-scaled)

The wide-block width invariant on `GrayTailStateV2`: unlike the flattened
`GrayTailWidthInvariant` (`sourceCount < 4·|slots|`), the V2 slots are
`mult`-times inflated, so the invariant is `sourceCount·mult(r) < 4·|slots|`
per round `r`.  This is what recovers the call-depth-scale per-round request
in the frozen-tail contradiction (via the block goal + `grayAdvBlock_fibre_mass`).
-/

namespace Kolmogorov

/-- Every frozen round after the first, and the current one unless the run is finished, keeps
more than a quarter of its block slab open. -/
structure GrayBlockWidthInvariantV2 {n b : Nat} (q L sourceCount : Nat)
    (st : GrayTailStateV2 n b) : Prop where
  current : st.frozen = [] ∨ st.done = true ∨
    sourceCount * grayAdvBlockMult q L st.frozen.length < 4 * st.slots.length
  frozenTail : forall p, p ∈ st.frozen.tail ->
    sourceCount * grayAdvBlockMult q L p.roundIndex < 4 * p.slots.length

/-- The initial V2 block tail state satisfies the block width invariant. -/
lemma grayBlockWidthInvariantV2_initial (n b a e q L : Nat) (A : Allocation) :
    GrayBlockWidthInvariantV2 q L (n * 2 ^ (e - a))
      (grayChargedBlockTailInitialStateV2 n b a e q L A) := by
  refine ⟨Or.inl rfl, ?_⟩
  intro p hp
  simp [grayChargedBlockTailInitialStateV2] at hp

/-- Freeze preserves the mult-scaled width (mirrors `grayTailWidthInvariant_freeze`).
The frozen round `p` records `roundIndex = st.frozen.length` (so its stored mult
matches its slots width from the pre-freeze current clause). -/
lemma grayBlockWidthInvariantV2_freeze {n b q L sourceCount : Nat}
    {st : GrayTailStateV2 n b} (hst : GrayBlockWidthInvariantV2 q L sourceCount st)
    (hactive : ¬(st.done || st.slots.isEmpty) = true)
    (p : GrayTailRoundV2 n b)
    (hpSlots : p.slots = st.slots) (hpIndex : p.roundIndex = st.frozen.length)
    (next : List (GrayTailSlot n b))
    (time roundStart : Nat) (done : Bool)
    (hnext : done = true ∨
      sourceCount * grayAdvBlockMult q L (st.frozen ++ [p]).length < 4 * next.length)
    (unavailable : Allocation)
    (anchoringSlots : List (GrayTailSlot n b)) (history : FamilyGameHistory) :
    GrayBlockWidthInvariantV2 q L sourceCount
      ({ time := time, roundStart := roundStart, done := done,
         frozen := st.frozen ++ [p], unavailable := unavailable,
         slots := next, anchoringSlots := anchoringSlots,
         history := history } : GrayTailStateV2 n b) := by
  constructor
  · right; exact hnext
  · intro r hr
    cases hfrozen : st.frozen with
    | nil => simp [hfrozen] at hr
    | cons first rest =>
        have hr' : r ∈ rest ++ [p] := by simpa [hfrozen] using hr
        rcases List.mem_append.mp hr' with hr' | hr'
        · exact hst.frozenTail r (by simpa [hfrozen] using hr')
        · have hrp : r = p := by simpa using hr'
          subst r
          rw [hpSlots, hpIndex]
          rcases hst.current with hempty | hslots
          · simp [hfrozen] at hempty
          · rcases hslots with hdone | hwide
            · have : (st.done || st.slots.isEmpty) = true := by simp [hdone]
              exact absurd this hactive
            · exact hwide

/-- The width invariant depends only on frozen, done, slots. -/
lemma widthV2_of_eq {n b q L sc : Nat} {st st' : GrayTailStateV2 n b}
    (h : GrayBlockWidthInvariantV2 q L sc st)
    (hf : st'.frozen = st.frozen) (hdn : st'.done = st.done)
    (hsl : st'.slots = st.slots) :
    GrayBlockWidthInvariantV2 q L sc st' := by
  refine ⟨?_, ?_⟩
  · rw [hf, hdn, hsl]; exact h.current
  · rw [hf]; exact h.frozenTail

/-- **The strict V2 step preserves the mult-scaled width invariant**
(at b = grayTailBranch q L a e). -/
lemma grayBlockWidthInvariantV2_step {n q L a e : Nat}
    (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n (grayTailBranch q L a e)) (sm : FamilyServerMove)
    (hst : GrayBlockWidthInvariantV2 q L (n * grayChargedSourceCount a e) st) :
    GrayBlockWidthInvariantV2 q L (n * grayChargedSourceCount a e)
      (grayChargedBlockTailStepV2 q L a e sigma A st sm) := by
  by_cases hd : st.done = true
  · have hstep : grayChargedBlockTailStepV2 q L a e sigma A st sm =
        { st with time := st.time + 1 } := by
      simp [grayChargedBlockTailStepV2, hd]
    rw [hstep]; exact widthV2_of_eq hst rfl rfl rfl
  · by_cases hs : st.slots.isEmpty = true
    · have hstep : grayChargedBlockTailStepV2 q L a e sigma A st sm =
          { st with time := st.time + 1 } := by
        simp [grayChargedBlockTailStepV2, hd, hs]
      rw [hstep]; exact widthV2_of_eq hst rfl rfl rfl
    · by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots sm) = true
      · simp only [grayChargedBlockTailStepV2, hd, hs, hg, Bool.false_eq_true, ↓reduceIte]
        set used := grayChargedSourceCount a e with hused
        set p0 : GrayTailRoundV2 n (grayTailBranch q L a e) :=
          { serverTime := st.time, roundIndex := st.frozen.length,
            blockAnchor := grayTailRoundEps q L e st.frozen.length,
            childEps := grayTailRoundEps q L e st.frozen.length + graySpendSpan q,
            fineEnd := grayTailRoundDelta q L e st.frozen.length,
            slots := st.slots, move := grayBlockCurrentMoveV2 q L e sigma st,
            allocated := grayTailLocalAllocatedList
              (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length) st.slots sm),
            unavailable := st.unavailable } with hp0
        set threshold := dyadicScale e - dyadicScale e / (6 * halfAmplification q) with hthr
        set frozenV1 := (st.frozen ++ [p0]).map GrayTailRoundV2.toV1 with hfv1
        set narrow :=
          grayTailNextSlots e used (st.frozen ++ [p0]).length threshold A frozenV1 sm with hnar
        set candidates :=
          grayBlockNextSlots q L e used (st.frozen
          ++ [p0]).length threshold A frozenV1 sm with hcand
        have hactive : ¬(st.done || st.slots.isEmpty) = true := by
          simp [Bool.eq_false_of_not_eq_true hd, Bool.eq_false_of_not_eq_true hs]
        refine grayBlockWidthInvariantV2_freeze hst hactive p0 rfl rfl candidates
          (st.time + 1) (st.time + 1)
          (grayTailGlobalQuarterB used narrow ||
            decide (grayChargedAdvantageRoundCount q <= (st.frozen ++ [p0]).length)) ?_ _ _ _
        by_cases hdone' : (grayTailGlobalQuarterB used narrow ||
            decide (grayChargedAdvantageRoundCount q <= (st.frozen ++ [p0]).length)) = true
        · exact Or.inl hdone'
        · right
          have hor := Bool.or_eq_false_iff.mp (Bool.eq_false_of_not_eq_true hdone')
          have hnq : grayTailGlobalQuarterB used narrow = false := hor.1
          have hadv : (st.frozen ++ [p0]).length < grayChargedAdvantageRoundCount q := by
            have := of_decide_eq_false hor.2; omega
          have hrb : (st.frozen ++ [p0]).length < grayTailBranch q L a e :=
            round_lt_branch_of_lt_advCount hadv
          have hGlen := grayAdvBlockGrandsons_length_used (q := q) (L := L)
            (a := a) (e := e) hadv
          have hGpos : 0 < (grayAdvBlockGrandsons (grayTailBranch q L a e) q L
              (st.frozen ++ [p0]).length).length := by
            rw [hGlen]; exact grayAdvBlockMult_pos q L _
          have hfw := grayBlockNextSlots_fibre_width q L e used (st.frozen ++ [p0]).length
            threshold A frozenV1 sm hrb hGpos hnq
          rw [hGlen] at hfw
          exact hfw
      · have hstep : grayChargedBlockTailStepV2 q L a e sigma A st sm =
          { st with
            time := st.time + 1
            history :=
              (st.history.1 ++ [grayBlockCurrentMoveV2 q L e sigma st],
                st.history.2 ++ [grayTailLocalServerMove
                  (grayTailRoundDelta q L e st.frozen.length) st.slots sm]) } := by
          simp [grayChargedBlockTailStepV2, hd, hs, hg]
        rw [hstep]; exact widthV2_of_eq hst rfl rfl rfl

/-- The mult-scaled width invariant holds at every stage (at b = grayTailBranch). -/
theorem grayBlockWidthInvariantV2_stateAt {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayBlockWidthInvariantV2 q L (n * grayChargedSourceCount a e)
      (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      have hinit := grayBlockWidthInvariantV2_initial n (grayTailBranch q L a e) a e q L A
      have hsc : n * 2 ^ (e - a) = n * grayChargedSourceCount a e := by
        rw [grayChargedSourceCount]
      rw [hsc] at hinit
      simpa [grayChargedBlockTailStateAtV2, grayChargedBlockTailFoldV2] using hinit
  | succ t ih =>
      rw [grayChargedBlockTailStateAtV2_succ]
      exact grayBlockWidthInvariantV2_step sigma A _ (sm t) ih

/-- **The per-round request lower bound** (the heart of the V2 progress): an
accepted wide-block round supplies `≥ (n·source/4)·(3/4)·dyadicScale(callDepth)`
amplified request — the same call-depth magnitude as the flattened controller,
recovered via the block goal + mult-scaled width + the mass bridge. -/
lemma grayChargedBlockV2_perRound_request_lower {n q L a e : Nat}
    {b' : Nat} {A' : Allocation} {slots : List (GrayTailSlot n b')} {move : FamilyClientMove}
    {server : FamilyServerMove} {r : Nat}
    (hgoal : grayChargedBlockGoalAtB q L e r slots.length A' move server = true)
    (hwidth : n * grayChargedSourceCount a e * grayAdvBlockMult q L r <
      4 * slots.length) :
    ((n * grayChargedSourceCount a e : Nat) : Rat) / 4 *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) <=
      halfAmplification q * totalRootRequest slots.length move := by
  have hgl := grayChargedBlockGoal_totalRequest_lower hgoal
  have hbridge := grayAdvBlock_fibre_mass q L e r
  have hεpos : (0 : Rat) < dyadicScale (grayTailRoundEps q L e r) := dyadicScale_pos _
  have hwidthR : ((n * grayChargedSourceCount a e : Nat) : Rat) *
      (grayAdvBlockMult q L r : Nat) < 4 * (slots.length : Nat) := by
    exact_mod_cast hwidth
  -- (n·source·mult)/4 ≤ slots.length
  have hquarter : ((n * grayChargedSourceCount a e : Nat) : Rat) *
      (grayAdvBlockMult q L r : Nat) / 4 <= (slots.length : Nat) := by
    rw [div_le_iff₀ (by norm_num : (0:Rat) < 4)]
    have : ((n * grayChargedSourceCount a e : Nat) : Rat) *
        (grayAdvBlockMult q L r : Nat) < (slots.length : Nat) * 4 := by
      linarith [hwidthR]
    linarith
  have hstep : ((n * grayChargedSourceCount a e : Nat) : Rat) / 4 *
      ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) <=
      (slots.length : Rat) * ((3 / 4 : Rat) *
        dyadicScale (grayTailRoundEps q L e r)) := by
    have hlhs : ((n * grayChargedSourceCount a e : Nat) : Rat) / 4 *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) =
        (((n * grayChargedSourceCount a e : Nat) : Rat) *
          (grayAdvBlockMult q L r : Nat) / 4) *
          ((3 / 4 : Rat) * dyadicScale (grayTailRoundEps q L e r)) := by
      rw [← hbridge]; ring
    rw [hlhs]
    apply mul_le_mul_of_nonneg_right hquarter
    positivity
  exact le_trans hstep hgl

end Kolmogorov
