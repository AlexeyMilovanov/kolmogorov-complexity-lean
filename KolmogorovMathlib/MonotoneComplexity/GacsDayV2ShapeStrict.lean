import KolmogorovMathlib.MonotoneComplexity.GacsDayV2StateStrict

/-!
# Strict V2 block shape on `GrayTailStateV2` (blueprint A3)

The wide-block shape invariant, ported onto the blueprint-faithful
`GrayTailStateV2` (frozen rounds are `GrayTailRoundV2`).  Identical in content
to the `GrayTailState`-based `GrayBlockTailShape`; only the record differs.
-/

namespace Kolmogorov

/-- All frozen slots of a V2 state. -/
def grayTailFrozenSlotsV2 {n b : ℕ} (frozen : List (GrayTailRoundV2 n b)) :
    List (GrayTailSlot n b) :=
  frozen.flatMap fun p => p.slots

/-- Shape invariant of a V2 tail state: frozen slots are pairwise distinct and each frozen round
`k` uses only advantage-block indices for `k`, and the live slots are distinct and lie in the
advantage block of the current round. -/
structure GrayBlockTailShapeV2 {n b : ℕ} (q L : ℕ) (st : GrayTailStateV2 n b) : Prop where
  frozen_nodup : (grayTailFrozenSlotsV2 st.frozen).Nodup
  frozen_round_range : ∀ k, ∀ hk : k < st.frozen.length,
    ∀ s ∈ (st.frozen[k]'hk).slots, grayInAdvBlock q L k s.2.2.val
  slots_nodup : st.slots.Nodup
  slots_range : ∀ s ∈ st.slots, grayInAdvBlock q L st.frozen.length s.2.2.val

/-- Under the shape invariant every frozen slot belongs to the advantage block of some earlier
round. -/
lemma mem_grayTailFrozenSlotsV2_range {n b q L : ℕ} {st : GrayTailStateV2 n b}
    (hsh : GrayBlockTailShapeV2 q L st) {s : GrayTailSlot n b}
    (hs : s ∈ grayTailFrozenSlotsV2 st.frozen) :
    ∃ k, ∃ _ : k < st.frozen.length, grayInAdvBlock q L k s.2.2.val := by
  rw [grayTailFrozenSlotsV2, List.mem_flatMap] at hs
  obtain ⟨p, hp, hsp⟩ := hs
  obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
  exact ⟨k, hk, hsh.frozen_round_range k hk s (hpk ▸ hsp)⟩

/-- Freezing the current round and installing a fresh distinct slot list in the next advantage
block preserves the shape invariant. -/
lemma grayBlockTailShapeV2_freeze {n b q L : ℕ} {st : GrayTailStateV2 n b}
    (hsh : GrayBlockTailShapeV2 q L st)
    (t' rs' : ℕ) (done : Bool) (p : GrayTailRoundV2 n b)
    (hpSlots : p.slots = st.slots)
    (next : List (GrayTailSlot n b)) (hnext : next.Nodup)
    (hnextRange : ∀ s ∈ next, grayInAdvBlock q L (st.frozen.length + 1) s.2.2.val)
    (anchoringSlots : List (GrayTailSlot n b)) (history : FamilyGameHistory)
    (unavailable' : Allocation) :
    GrayBlockTailShapeV2 q L
      ({ time := t', roundStart := rs', done := done,
         frozen := st.frozen ++ [p], unavailable := unavailable',
         slots := next, anchoringSlots := anchoringSlots,
         history := history } : GrayTailStateV2 n b) := by
  refine ⟨?_, ?_, hnext, ?_⟩
  · have hsplit : grayTailFrozenSlotsV2 (st.frozen ++ [p]) =
        grayTailFrozenSlotsV2 st.frozen ++ p.slots := by
      simp [grayTailFrozenSlotsV2, List.flatMap_append]
    rw [hsplit]
    refine List.Nodup.append hsh.frozen_nodup (hpSlots ▸ hsh.slots_nodup) ?_
    intro s hs hs'
    obtain ⟨k, hk, hrange⟩ := mem_grayTailFrozenSlotsV2_range hsh hs
    rw [hpSlots] at hs'
    exact grayInAdvBlock_ne_of_round_ne hrange (hsh.slots_range s hs') (by omega) rfl
  · intro k hk s hs
    have hk1 : k < st.frozen.length + 1 := by
      rw [List.length_append, List.length_singleton] at hk; exact hk
    by_cases hkf : k < st.frozen.length
    · rw [List.getElem_append_left hkf] at hs
      exact hsh.frozen_round_range k hkf s hs
    · have hke : k = st.frozen.length := by omega
      subst hke
      have hget : (st.frozen ++ [p])[st.frozen.length]'hk = p := by
        rw [List.getElem_append_right (Nat.le_refl _)]; simp
      rw [hget, hpSlots] at hs
      exact hsh.slots_range s hs
  · intro s hs
    have hlen : (st.frozen ++ [p]).length = st.frozen.length + 1 := by simp
    rw [hlen]
    exact hnextRange s hs

/-- The initial charged block tail state satisfies the shape invariant. -/
lemma grayBlockTailShapeV2_initial (n b a e q L : Nat) (A : Allocation) :
    GrayBlockTailShapeV2 q L (grayChargedBlockTailInitialStateV2 n b a e q L A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [grayChargedBlockTailInitialStateV2, grayTailFrozenSlotsV2]
  · intro k hk
    simp [grayChargedBlockTailInitialStateV2] at hk
  · exact grayAdvBlockSlots_nodup _ _ _ _ _ _
  · intro s hs
    change s ∈ grayAdvBlockSlots n b (grayChargedSourceCount a e) q L 0 at hs
    exact (grayAdvBlockSlots_mem hs).2

/-- **The strict V2 step preserves the block shape.** -/
lemma grayBlockTailShapeV2_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove)
    (hsh : GrayBlockTailShapeV2 q L st) :
    GrayBlockTailShapeV2 q L (grayChargedBlockTailStepV2 q L a e sigma A st sm) := by
  by_cases hd : st.done = true
  · simp only [grayChargedBlockTailStepV2, hd, ↓reduceIte]
    exact ⟨hsh.frozen_nodup, hsh.frozen_round_range, hsh.slots_nodup,
      hsh.slots_range⟩
  · by_cases hs : st.slots.isEmpty = true
    · simp only [grayChargedBlockTailStepV2, hd, hs, Bool.false_eq_true,
        ↓reduceIte]
      exact ⟨hsh.frozen_nodup, hsh.frozen_round_range, hsh.slots_nodup,
        hsh.slots_range⟩
    · by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots sm) = true
      · simp only [grayChargedBlockTailStepV2, hd, hs, hg, Bool.false_eq_true,
          ↓reduceIte]
        apply grayBlockTailShapeV2_freeze hsh
        · rfl
        · exact grayBlockNextSlots_nodup _ _ _ _ _ _ _ _ _
        · intro s hs'
          simpa [List.length_append] using grayBlockNextSlots_mem_range hs'
      · simp only [grayChargedBlockTailStepV2, hd, hs, hg, Bool.false_eq_true,
          ↓reduceIte]
        exact ⟨hsh.frozen_nodup, hsh.frozen_round_range, hsh.slots_nodup,
          hsh.slots_range⟩

end Kolmogorov
