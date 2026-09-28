import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController

/-!
# Source and spend slots for the charged Gacs-Day controller

The source phase occupies only an initial block of root sons.  The remaining
two-level slots encode the finite version of Gacs's spare sons.  Spend sons
display the honest sum of their recursive requests; only source sons use the
epsilon raise associated with a reserve.
-/

namespace Kolmogorov

/-- Number of source sons.  The source population has total mass exactly
`alpha`: `2^(e-a)` cylinders of mass `epsilon`.  Spend calls use the separate
block provided by `ladderBranching`. -/
def grayChargedSourceCount (a e : Nat) : Nat := 2 ^ (e - a)

/-- The request depth of one spend sub-call: an eighth of the root scale, so
recursive H4/H1 give one pass the increment window `[alpha/16, alpha/8]` and
eight passes close the Day window with overshoot `<= alpha / 8`. -/
def grayChargedSpendAlphaDepth (a : Nat) : Nat := a + 3

/-- The coarse depth of spend pass `pass`: the telescope continues below the
bin scale, one loss step per pass, so the fine depth of pass `pass + 1` is
the coarse depth of pass `pass`.  Every spend cell is therefore at or above
the bin scale, and a serving cell of the sub-root is coarser than every
earlier neighbourhood cell. -/
def grayChargedSpendEps (a L e pass : Nat) : Nat :=
  max (grayChargedSpendAlphaDepth a) (e - (pass + 1) * L)

/-- The fine depth of a spend pass: definitionally one loss step below the
coarse depth of that pass, so the freeze plumbing needs no room hypothesis.
That the fine depth stays at or above the bin scale requires
`(pass + 1) * L <= e` and is assumed only by the ledger, never by the
controller. -/
def grayChargedSpendDelta (a L e pass : Nat) : Nat :=
  grayChargedSpendEps a L e pass + L

/-- Number of recursive roots in one spend batch: a single sub-root per
deficient root per pass, at the spend request scale. -/
def grayChargedSpendCount (_q _a _e : Nat) : Nat := 1

/-- All two-level locations below non-source sons. -/
def grayChargedSparePairs (b source : Nat) : List (Fin b × Fin b) :=
  ((List.finRange b).drop source).flatMap fun c =>
    (List.finRange b).map fun d => (c, d)

/-- The disjoint block of spare locations used by one of the eight spend
passes. -/
def grayChargedSpendPairs (b source count pass : Nat) : List (Fin b × Fin b) :=
  ((grayChargedSparePairs b source).drop (pass * count)).take count

/-- A source-only initial controller state. -/
def grayChargedTailInitialState (n b a e : Nat) (A : Allocation) :
    GrayTailState n b where
  time := 0
  roundStart := 0
  done := false
  frozen := []
  unavailable := A
  slots := grayTailSlots n b (grayChargedSourceCount a e) 0
  anchoringSlots := []
  history := ([], [])

/-- Source sons retain the reserve raise.  Every spare son instead displays
the exact sum of the recursive calls planted below it. -/
def grayChargedSonRequest {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) (c : Fin b) : Rat :=
  if c.val < source then
    grayTailSonRequest threshold eps entries i c
  else
    grayTailSonBase entries i c

/-- The request at the root of client `i`, namely the sum of the charged son requests over all
children. -/
def grayChargedRootRequest {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) : Rat :=
  ∑ c : Fin b, grayChargedSonRequest source threshold eps entries i c

/-- Graft source and spend calls into the same outer family.  No artificial
root floor is used: the spend phase proves the lower request bound. -/
def grayChargedTailFamilyMove {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (frozen : GrayTailFrozen n b) (slots : List (GrayTailSlot n b))
    (current : FamilyClientMove) : FamilyClientMove :=
  let entries := grayTailEntries frozen slots current
  List.ofFn fun i : Fin n =>
    graftTwoLevel (grayChargedRootRequest source threshold eps entries i) b
      (fun c => if hc : c < b then
        grayChargedSonRequest source threshold eps entries i ⟨c, hc⟩
        else 0)
      (fun c c' => if hc : c < b then if hc' : c' < b then
        grayTailEntryMove entries (i, ⟨c, hc⟩, ⟨c', hc'⟩)
        else [] else [])

/-- Roots whose already frozen displayed request is below the Day floor. -/
def grayChargedDeficientRoots {n b : Nat}
    (source : Nat) (threshold eps alpha : Rat)
    (frozen : GrayTailFrozen n b) : List (Fin n) :=
  (List.finRange n).filter fun i =>
    decide (grayChargedRootRequest source threshold eps
      (grayTailFrozenEntries frozen) i < alpha / 2)

/-- Slots for one spend pass.  Every deficient root receives the same-size
fresh block, but root tags keep the recursive family components distinct. -/
def grayChargedSpendSlots {n b : Nat}
    (source count pass : Nat) (threshold eps alpha : Rat)
    (frozen : GrayTailFrozen n b) : List (GrayTailSlot n b) :=
  (grayChargedDeficientRoots source threshold eps alpha frozen).flatMap fun i =>
    (grayChargedSpendPairs b source count pass).map fun p => (i, p.1, p.2)

/-- There is at least one source child. -/
@[simp] lemma grayChargedSourceCount_pos (a e : Nat) :
    0 < grayChargedSourceCount a e := by
  simp [grayChargedSourceCount]

/-- Every spend pass opens at least one pair. -/
@[simp] lemma grayChargedSpendCount_pos (q a e : Nat) :
    0 < grayChargedSpendCount q a e := by
  simp [grayChargedSpendCount]

/-- The source children are among the `2 ^ (e - a)` used children. -/
lemma grayChargedSourceCount_le_used (a e : Nat) :
    grayChargedSourceCount a e <= 2 ^ (e - a) := by
  simp [grayChargedSourceCount]

/-- The source children are exactly the `2 ^ (e - a)` used children. -/
@[simp] lemma grayChargedSourceCount_eq_used (a e : Nat) :
    grayChargedSourceCount a e = 2 ^ (e - a) := by
  rfl

/-- At a source child the charged son request is the plain tail son request. -/
lemma grayChargedSonRequest_source {n b : Nat}
    {source : Nat} {threshold eps : Rat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    (i : Fin n) (c : Fin b) (hc : c.val < source) :
    grayChargedSonRequest source threshold eps entries i c =
      grayTailSonRequest threshold eps entries i c := by
  simp [grayChargedSonRequest, hc]

/-- At a spare child the charged son request is just the son base, with no threshold applied. -/
lemma grayChargedSonRequest_spare {n b : Nat}
    {source : Nat} {threshold eps : Rat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    (i : Fin n) (c : Fin b) (hc : source <= c.val) :
    grayChargedSonRequest source threshold eps entries i c =
      grayTailSonBase entries i c := by
  simp [grayChargedSonRequest, Nat.not_lt.mpr hc]

end Kolmogorov
