import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderRelocation

/-!
# Finite composition of gray rounds

The two-round composition theorem is most useful to the Gacs-Day controller
in its iterated form. A completed round contributes its new gray cells and
then makes its whole coarse gray neighbourhood unavailable to all later
rounds. The definitions and theorem below package exactly that fold.
-/

namespace Kolmogorov

/-- Total number of fine gray cells contributed by a finite chronological
list of calls. Later calls see the whole gray neighbourhood of every earlier
allocation as unavailable. -/
def grayCallsNewGrayMassGray (deltaDepth : Nat) :
    List (Nat × Finset BitString) -> Finset BitString -> Nat
  | [], _ => 0
  | (eps, allocated) :: rest, unavailable =>
      (newGrayCells eps deltaDepth allocated unavailable).card +
        grayCallsNewGrayMassGray deltaDepth rest
          (unavailable ∪ neighborhoodCells eps allocated)

/-- The gray cells contributed by a descending finite list of calls fit in
the gray region of the union of their allocations at the coarsest call scale.
No length hypothesis on the allocations is needed because the controller
adds the whole coarse neighbourhood, rather than merely the raw allocation,
to the next unavailable set. -/
lemma grayCallsNewGrayMassGray_le_compose
    (calls : List (Nat × Finset BitString)) (deltaDepth : Nat)
    (unavailable : Finset BitString)
    (hscale : calls.IsChain (fun p q => q.1 <= p.1)) :
    grayCallsNewGrayMassGray deltaDepth calls unavailable <=
      (newGrayCells
        (calls.getLast?.map Prod.fst |>.getD 0)
        deltaDepth
        (calls.map Prod.snd |>.foldr (· ∪ ·) ∅)
        unavailable).card := by
  induction calls generalizing unavailable with
  | nil =>
      simp [grayCallsNewGrayMassGray]
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp [grayCallsNewGrayMassGray]
      | cons next rest =>
          have htail : (next :: rest).IsChain (fun p q => q.1 <= p.1) := by
            cases hscale
            assumption
          have hih := ih
            (unavailable := unavailable ∪ neighborhoodCells head.1 head.2)
            htail
          rw [grayCallsNewGrayMassGray]
          have hadd := Nat.add_le_add_left hih
            (newGrayCells head.1 deltaDepth head.2 unavailable).card
          refine le_trans hadd ?_
          have hlast :
              ((head :: next :: rest).getLast?.map Prod.fst |>.getD 0) =
                ((next :: rest).getLast?.map Prod.fst |>.getD 0) := rfl
          rw [hlast]
          have heps :
              ((next :: rest).getLast?.map Prod.fst |>.getD 0) <= head.1 := by
            have h := chain_last_le_head (head :: next :: rest) hscale
            simpa using h
          exact card_add_le_card_newGrayCells_grayUnavailable
            (delta := deltaDepth)
            (A₁ := head.2)
            (A₂ := (next :: rest).map Prod.snd |>.foldr (· ∪ ·) ∅)
            (U := unavailable) heps

end Kolmogorov
