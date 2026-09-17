import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailMass

/-!
# Composition with discarded components

A completed tail round makes the neighbourhood of its full allocation
unavailable, while hereditary accounting may retain only a selected
subfamily.  The selected gray cells are still disjoint from all later calls.
-/

namespace Kolmogorov

/-- One recursive call of the composition: its epsilon depth, the allocation it actually charges
and the full allocation it blocks. -/
structure GraySelectedCall where
  epsDepth : Nat
  selected : Finset BitString
  full : Finset BitString

private lemma selectedChain_last_le_head : forall
    (l : List GraySelectedCall)
    (_hchain : l.IsChain (fun p q => q.epsDepth <= p.epsDepth)),
    (l.getLast?.map GraySelectedCall.epsDepth |>.getD 0) <=
      (l.head?.map GraySelectedCall.epsDepth |>.getD 0)
  | [], _ => by simp
  | [_], _ => by rfl
  | x :: y :: tail, hchain => by
      cases hchain
      rename_i rel chainTail
      exact le_trans (selectedChain_last_le_head (y :: tail) chainTail) rel

/-- The cells a chain of selected calls charges in turn, each call blocked by the neighbourhoods
of the full allocations of its predecessors. -/
def graySelectedCallsMass (deltaDepth : Nat) :
    List GraySelectedCall -> Finset BitString -> Nat
  | [], _ => 0
  | p :: rest, unavailable =>
      (newGrayCells p.epsDepth deltaDepth p.selected unavailable).card +
        graySelectedCallsMass deltaDepth rest
          (unavailable ∪ neighborhoodCells p.epsDepth p.full)

private lemma neighborhoodCells_mono_selected
    {depth : Nat} {selected full : Finset BitString}
    (hsub : selected ⊆ full) :
    neighborhoodCells depth selected ⊆ neighborhoodCells depth full := by
  intro p hp
  rw [mem_neighborhoodCells_iff_prefixComparable] at hp ⊢
  obtain ⟨hlen, c, hc, hcomp⟩ := hp
  exact ⟨hlen, c, hsub hc, hcomp⟩

/-- One composition step with a selected allocation inside a blocking full allocation. -/
lemma card_add_le_card_newGrayCells_selectedFull
    {eps1 eps2 delta : Nat}
    {selected1 full1 selected2 unavailable : Finset BitString}
    (hscale : eps2 <= eps1) (hsub : selected1 ⊆ full1) :
    (newGrayCells eps1 delta selected1 unavailable).card +
        (newGrayCells eps2 delta selected2
          (unavailable ∪ neighborhoodCells eps1 full1)).card <=
      (newGrayCells eps2 delta (selected1 ∪ selected2) unavailable).card := by
  have hgraySub :
      newGrayCells eps2 delta selected2
          (unavailable ∪ neighborhoodCells eps1 full1) ⊆
        newGrayCells eps2 delta selected2
          (unavailable ∪ neighborhoodCells eps1 selected1) := by
    intro p hp
    rw [mem_newGrayCells_iff] at hp ⊢
    refine ⟨hp.1, hp.2.1, ?_⟩
    intro hbad
    apply hp.2.2
    have hbad' :
        p ∈ neighborhoodCells delta unavailable ∨
          p ∈ neighborhoodCells delta
            (neighborhoodCells eps1 selected1) := by
      simpa only [neighborhoodCells_union, Finset.mem_union] using hbad
    rw [neighborhoodCells_union, Finset.mem_union]
    rcases hbad' with hU | hsel
    · exact Or.inl hU
    · exact Or.inr (neighborhoodCells_mono_selected
        (neighborhoodCells_mono_selected hsub) hsel)
  have hcard := Finset.card_le_card hgraySub
  calc
    (newGrayCells eps1 delta selected1 unavailable).card +
          (newGrayCells eps2 delta selected2
            (unavailable ∪ neighborhoodCells eps1 full1)).card
        <= (newGrayCells eps1 delta selected1 unavailable).card +
          (newGrayCells eps2 delta selected2
            (unavailable ∪ neighborhoodCells eps1 selected1)).card :=
          Nat.add_le_add_left hcard _
    _ <= (newGrayCells eps2 delta (selected1 ∪ selected2) unavailable).card :=
      card_add_le_card_newGrayCells_grayUnavailable hscale

/-- A chain of calls of decreasing epsilon depth charges at most as many cells as a single call
at the last depth with the union of the selected allocations. -/
lemma graySelectedCallsMass_le_compose
    (calls : List GraySelectedCall) (deltaDepth : Nat)
    (unavailable : Finset BitString)
    (hscale : calls.IsChain (fun p q => q.epsDepth <= p.epsDepth))
    (hsub : forall p, p ∈ calls -> p.selected ⊆ p.full) :
    graySelectedCallsMass deltaDepth calls unavailable <=
      (newGrayCells
        (calls.getLast?.map GraySelectedCall.epsDepth |>.getD 0)
        deltaDepth
        (calls.map GraySelectedCall.selected |>.foldr (· ∪ ·) ∅)
        unavailable).card := by
  induction calls generalizing unavailable with
  | nil =>
      simp [graySelectedCallsMass]
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp [graySelectedCallsMass]
      | cons next rest =>
          have htail : (next :: rest).IsChain
              (fun p q => q.epsDepth <= p.epsDepth) := by
            cases hscale
            assumption
          have hsubTail : forall p, p ∈ next :: rest -> p.selected ⊆ p.full := by
            intro p hp
            exact hsub p (by simp [hp])
          have hih := ih
            (unavailable := unavailable ∪
              neighborhoodCells head.epsDepth head.full)
            htail hsubTail
          rw [graySelectedCallsMass]
          have hadd := Nat.add_le_add_left hih
            (newGrayCells head.epsDepth deltaDepth head.selected unavailable).card
          refine le_trans hadd ?_
          have hlast :
              ((head :: next :: rest).getLast?.map
                  GraySelectedCall.epsDepth |>.getD 0) =
                ((next :: rest).getLast?.map
                  GraySelectedCall.epsDepth |>.getD 0) := rfl
          rw [hlast]
          have heps :
              ((next :: rest).getLast?.map
                  GraySelectedCall.epsDepth |>.getD 0) <= head.epsDepth := by
            have h := selectedChain_last_le_head
              (head :: next :: rest) hscale
            simpa using h
          exact card_add_le_card_newGrayCells_selectedFull
            (delta := deltaDepth)
            (selected1 := head.selected) (full1 := head.full)
            (selected2 :=
              (next :: rest).map GraySelectedCall.selected |>.foldr (· ∪ ·) ∅)
            (unavailable := unavailable) heps
            (hsub head (by simp))

end Kolmogorov
