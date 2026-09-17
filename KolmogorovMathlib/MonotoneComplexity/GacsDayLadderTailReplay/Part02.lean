import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.Invariants
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.StateAt

/-!
# What the tail strategy plays

`playClientFamily_grayTailStrategy` identifies the play of the tail strategy: at each time it is
the output of the tail state at that time. The lookup lemmas behind it say that, when the slots
of the entries are distinct, the move assembled for a slot is exactly the move recorded for it
(`grayTailEntryMove_eq_of_mem`), which for a well-shaped state gives an open slot its own row of
the current move (`grayTailEntryMove_current`) and a slot of a frozen round its own row of that
round's move (`grayTailEntryMove_frozen`).
-/

namespace Kolmogorov

/-- When the slots of the entries are distinct, the move assembled for a slot is the move
recorded with it. -/
lemma grayTailEntryMove_eq_of_mem {n b : ℕ}
    (entries : List (GrayTailSlot n b × ClientMove))
    (hkeys : (entries.map Prod.fst).Nodup)
    (slot : GrayTailSlot n b) (move : ClientMove)
    (hmem : (slot, move) ∈ entries) :
    grayTailEntryMove entries slot = move := by
  induction entries with
  | nil => simp at hmem
  | cons p entries ih =>
      simp only [List.map_cons, List.nodup_cons] at hkeys
      rcases hkeys with ⟨hhead, hkeys⟩
      rcases List.mem_cons.mp hmem with hp | hmem
      · subst p
        simp [grayTailEntryMove]
      · have hpne : p.1 ≠ slot := by
          intro hp
          apply hhead
          rw [hp]
          exact List.mem_map.mpr ⟨(slot, move), hmem, rfl⟩
        unfold grayTailEntryMove
        simp only [List.find?_cons, hpne, decide_false,
          ]
        exact ih hkeys hmem

/-- For a well-shaped state, an open slot receives its own row of the current move. -/
lemma grayTailEntryMove_current {n b : ℕ}
    {st : GrayTailState n b} (hst : GrayTailShape st)
    (current : FamilyClientMove) (j : Fin st.slots.length) :
    grayTailEntryMove (grayTailEntries st.frozen st.slots current)
        (st.slots.get j) =
      familyClientMoveAt current j.val := by
  apply grayTailEntryMove_eq_of_mem _ (grayTailEntries_keys_nodup hst current)
  rw [grayTailEntries, List.mem_append]
  right
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- For a well-shaped state, a slot of a frozen round receives its own row of that round's move. -/
lemma grayTailEntryMove_frozen {n b : ℕ}
    {st : GrayTailState n b} (hst : GrayTailShape st)
    {p : GrayTailRound n b} (hp : p ∈ st.frozen)
    (current : FamilyClientMove) (j : Fin p.slots.length) :
    grayTailEntryMove (grayTailEntries st.frozen st.slots current)
        (p.slots.get j) =
      familyClientMoveAt p.move j.val := by
  apply grayTailEntryMove_eq_of_mem _ (grayTailEntries_keys_nodup hst current)
  rw [grayTailEntries, List.mem_append]
  left
  rw [grayTailFrozenEntries, List.mem_flatMap]
  refine ⟨p, hp, ?_⟩
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- The tail strategy plays, at each time, the output of the tail state at that time. -/
lemma playClientFamily_grayTailStrategy
    (q L a e n : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (t : ℕ) :
    let b := ladderBranching (grayTailBaseBranch q L) a e
    playClientFamily A n (grayTailStrategy q L a e sigma) sm t =
      grayTailOutput q L a e sigma
        (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t) := by
  dsimp only
  cases t with
  | zero =>
      rw [playClientFamily]
      rfl
  | succ t =>
      rw [playClientFamily]
      rfl

end Kolmogorov
