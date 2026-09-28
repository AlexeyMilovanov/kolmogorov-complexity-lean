import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Controller
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay

/-!
# V2 block shape invariant (Reading C)

The wide-block analogue of `GrayTailShape`.  A round's slots no longer carry
the grandson coordinate `= roundIndex`; instead every slot's grandson lies in
that round's disjoint block range `[offset r, offset r + mult r)`
(`grayInAdvBlock`).  Cross-round slot distinctness therefore comes from the
disjointness of the block ranges (`grayInAdvBlock_ne_of_round_ne`) rather than
from distinct grandson values.
-/

namespace Kolmogorov

/-- The V2 shape: every frozen round `k`'s slots sit in block range `k`, the
current slots sit in block range `frozen.length`, and both are nodup. -/
structure GrayBlockTailShape {n b : ℕ} (q L : ℕ) (st : GrayTailState n b) : Prop where
  frozen_nodup : (grayTailFrozenSlots st.frozen).Nodup
  frozen_round_range : ∀ k, ∀ hk : k < st.frozen.length,
    ∀ s ∈ (st.frozen[k]'hk).slots, grayInAdvBlock q L k s.2.2.val
  slots_nodup : st.slots.Nodup
  slots_range : ∀ s ∈ st.slots, grayInAdvBlock q L st.frozen.length s.2.2.val

/-- A frozen slot belongs to some round `k < frozen.length` and lies in that
round's block range. -/
lemma mem_grayTailFrozenSlots_range {n b q L : ℕ} {st : GrayTailState n b}
    (hsh : GrayBlockTailShape q L st) {s : GrayTailSlot n b}
    (hs : s ∈ grayTailFrozenSlots st.frozen) :
    ∃ k, ∃ _ : k < st.frozen.length, grayInAdvBlock q L k s.2.2.val := by
  rw [grayTailFrozenSlots, List.mem_flatMap] at hs
  obtain ⟨p, hp, hsp⟩ := hs
  obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
  refine ⟨k, hk, ?_⟩
  exact hsh.frozen_round_range k hk s (hpk ▸ hsp)

/-- **Freeze preserves the V2 shape.**  Appending round `p` (whose slots are
the old current slots, in block range `frozen.length`) and installing new
current slots `next` (in block range `frozen.length + 1`).  The new frozen
nodup follows from the disjointness of block range `frozen.length` from every
earlier range. -/
lemma grayBlockTailShape_freeze {n b q L : ℕ} {st : GrayTailState n b}
    (hsh : GrayBlockTailShape q L st)
    (t' rs' : ℕ) (done : Bool) (p : GrayTailRound n b)
    (hpSlots : p.slots = st.slots)
    (next : List (GrayTailSlot n b)) (hnext : next.Nodup)
    (hnextRange : ∀ s ∈ next, grayInAdvBlock q L (st.frozen.length + 1) s.2.2.val)
    (anchoringSlots : List (GrayTailSlot n b)) (history : FamilyGameHistory)
    (unavailable' : Allocation) :
    GrayBlockTailShape q L
      ({ time := t', roundStart := rs', done := done,
         frozen := st.frozen ++ [p], unavailable := unavailable',
         slots := next, anchoringSlots := anchoringSlots,
         history := history } : GrayTailState n b) := by
  refine ⟨?_, ?_, hnext, ?_⟩
  · -- frozen_nodup
    have hsplit : grayTailFrozenSlots (st.frozen ++ [p]) =
        grayTailFrozenSlots st.frozen ++ p.slots := by
      simp [grayTailFrozenSlots, List.flatMap_append]
    rw [hsplit]
    refine List.Nodup.append hsh.frozen_nodup (hpSlots ▸ hsh.slots_nodup) ?_
    -- disjoint: frozen slot in range k < len, p.slot in range len
    intro s hs hs'
    obtain ⟨k, hk, hrange⟩ := mem_grayTailFrozenSlots_range hsh hs
    rw [hpSlots] at hs'
    have hrange' := hsh.slots_range s hs'
    exact grayInAdvBlock_ne_of_round_ne hrange hrange' (by omega) rfl
  · -- frozen_round_range for the extended list
    intro k hk s hs
    have hk1 : k < st.frozen.length + 1 := by
      rw [List.length_append, List.length_singleton] at hk; exact hk
    by_cases hklt : k < st.frozen.length
    · have hget : (st.frozen ++ [p])[k]'hk = st.frozen[k]'hklt :=
        List.getElem_append_left hklt
      rw [hget] at hs
      exact hsh.frozen_round_range k hklt s hs
    · have hke : k = st.frozen.length := by omega
      subst hke
      have hget : (st.frozen ++ [p])[st.frozen.length]'hk = p := by
        rw [List.getElem_append_right (Nat.le_refl _)]; simp
      rw [hget, hpSlots] at hs
      exact hsh.slots_range s hs
  · -- slots_range for `next`
    intro s hs
    have hlen : (st.frozen ++ [p]).length = st.frozen.length + 1 := by simp
    rw [hlen]
    exact hnextRange s hs

/-- The V2 initial state satisfies the block shape. -/
lemma grayBlockTailShape_initial (n b a e q L : Nat) (A : Allocation) :
    GrayBlockTailShape q L (grayChargedBlockTailInitialState n b a e q L A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [grayChargedBlockTailInitialState, grayTailFrozenSlots]
  · intro k hk
    simp [grayChargedBlockTailInitialState] at hk
  · exact grayAdvBlockSlots_nodup _ _ _ _ _ _
  · intro s hs
    change s ∈ grayAdvBlockSlots n b (grayChargedSourceCount a e) q L 0 at hs
    exact (grayAdvBlockSlots_mem hs).2

/-- **The V2 step preserves the block shape.** -/
lemma grayBlockTailShape_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hsh : GrayBlockTailShape q L st) :
    GrayBlockTailShape q L (grayChargedBlockTailStep q L a e sigma A st sm) := by
  by_cases hd : st.done = true
  · simp only [grayChargedBlockTailStep, grayTailWaitingB, Bool.false_eq_true,
      hd, ↓reduceIte]
    exact ⟨hsh.frozen_nodup, hsh.frozen_round_range, hsh.slots_nodup,
      hsh.slots_range⟩
  · by_cases hs : st.slots.isEmpty = true
    · simp only [grayChargedBlockTailStep, grayTailWaitingB, Bool.false_eq_true,
        hd, hs, ↓reduceIte]
      exact ⟨hsh.frozen_nodup, hsh.frozen_round_range, hsh.slots_nodup,
        hsh.slots_range⟩
    · by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable (grayBlockCurrentMove q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots sm) = true
      · simp only [grayChargedBlockTailStep, grayTailWaitingB,
          Bool.false_eq_true, hd, hs, hg, ↓reduceIte]
        apply grayBlockTailShape_freeze hsh
        · rfl
        · exact grayBlockNextSlots_nodup _ _ _ _ _ _ _ _ _
        · intro s hs'
          simpa [List.length_append] using grayBlockNextSlots_mem_range hs'
      · simp only [grayChargedBlockTailStep, grayTailWaitingB,
          Bool.false_eq_true, hd, hs, hg, ↓reduceIte]
        exact ⟨hsh.frozen_nodup, hsh.frozen_round_range, hsh.slots_nodup,
          hsh.slots_range⟩

end Kolmogorov
