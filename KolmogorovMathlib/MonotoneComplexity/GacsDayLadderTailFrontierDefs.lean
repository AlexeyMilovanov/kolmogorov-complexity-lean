import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailSelectedSum
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailOwnerIndex
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailAnchorSearch
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailTerminal
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailStable
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailPointwise
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailAggregate
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailCoupled
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFresh
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailBounds
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRound

/-!
# Interface objects of the explicit leaf frontier of Day's ladder tail

This module carries only the *definitions* of the tail frontier: the
reconstructed run state, the displayed move, the source threshold, the new
depth loss, and the four interface predicates

```text
GrayTailTerminalData            (produced by Leaf A)
GrayTailReservePackage          (produced by Leaf B)
GrayTailSelectedRoundAccounting (produced by Leaf C)
GrayTailHereditaryArithmetic    (produced by Leaf D)
```

Every quantity is read off one real execution of the tail controller
`grayTailStrategy`: the frozen rounds, the owner indices, the exact exits and
the terminal snapshot.  Nothing here is an abstract rational array.

The leaves themselves live in `GacsDayLadderTailLeafA.lean` ...
`GacsDayLadderTailLeafE.lean`, each of which further decomposes its leaf into
strictly narrower children; `GacsDayLadderTailFrontier.lean` collects them.
-/

namespace Kolmogorov

open scoped BigOperators

/-- Abbreviation for `grayTailStateAt q L a e sigma A sm T` with the branching fixed to
`grayTailBranch q L a e`: the controller state reached after the first `T` server moves of `sm`. -/
abbrev grayTailRunState (q L a e n : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : ℕ → FamilyServerMove) (T : ℕ) :
    GrayTailState n (grayTailBranch q L a e) :=
  grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm T

/-- Abbreviation for `grayTailOutput q L a e sigma (grayTailRunState q L a e n sigma A sm T)`: the
outer family move that the controller displays in the state reached after `T` server moves. -/
abbrev grayTailRunMove (q L a e n : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : ℕ → FamilyServerMove) (T : ℕ) : FamilyClientMove :=
  grayTailOutput q L a e sigma (grayTailRunState q L a e n sigma A sm T)

/-- The source threshold `dyadicScale e - dyadicScale e / (6 * halfAmplification q)`, that is `ε - ε
/ (6 * κ)` for `ε = dyadicScale e` and `κ = halfAmplification q`. -/
abbrev grayTailThreshold (q e : ℕ) : ℚ :=
  dyadicScale e - dyadicScale e / (6 * halfAmplification q)

/-- The depth loss produced by one tail half-step: `256 * (q + 1) ^ 2 * L + 256 * (q + 1)`. -/
def grayTailNewLoss (q L : ℕ) : ℕ := 256 * (q + 1) ^ 2 * L + 256 * (q + 1)

/-- The depth the tail loses is `256 * (q + 1) ^ 2 * L + 256 * (q + 1)`. -/
lemma grayTailNewLoss_eq (q L : ℕ) :
    grayTailNewLoss q L = 256 * (q + 1) ^ 2 * L + 256 * (q + 1) := rfl

/-- The new branching bound is literally the controller's own base branching
`max 2 (256 * (q + 1) * 2 ^ newLoss)`. -/
lemma grayTailBaseBranch_eq_newBranch (q L : ℕ) :
    grayTailBaseBranch q L = max 2 (256 * (q + 1) * 2 ^ grayTailNewLoss q L) := rfl

/-- The finite certificate extracted from one terminal tail-controller state.

Every field is a statement about the actual reconstructed state
`grayTailRunState q L a e n sigma A sm T` of the run of
`grayTailStrategy q L a e sigma` against the outer server play `sm`:
the frozen rounds, the exact per-son increments recorded in them, the
participation chronology, the resolved/unresolved status of every source son,
the owner (last participating round) index, the two exact exits, the terminal
at-most-a-quarter bound and the initial all-son participation. -/
structure GrayTailTerminalData (q L a e n : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : ℕ → FamilyServerMove) (T : ℕ) : Prop where
  /-- The controller certificate: frozen chain, exact round depths and times,
  and the hereditary gray certificate of every frozen round. -/
  certified : GrayTailCertified q L e A sm T (grayTailRunState q L a e n sigma A sm T)
  /-- `T` is terminal. -/
  done : (grayTailRunState q L a e n sigma A sm T).done = true
  /-- The recorded round index of a frozen round is its list position, so the
  owner index really selects the owner round. -/
  round_index_eq : ∀ (r : ℕ) (hr : r < (grayTailRunState q L a e n sigma A sm T).frozen.length),
    ((grayTailRunState q L a e n sigma A sm T).frozen.get ⟨r, hr⟩).roundIndex = r
  /-- The outer client play is constant from `T` on, so all later certificates
  can be read at the single time `T`. -/
  play_eq : ∀ U, T ≤ U →
    playClientFamily A n (grayTailStrategy q L a e sigma) sm U =
      grayTailRunMove q L a e n sigma A sm T
  /-- The SUV global stop: at most one quarter of all source sons is still
  unresolved at the terminal recheck. -/
  terminal_width :
    4 * (grayTailRunState q L a e n sigma A sm T).slots.length ≤ n * 2 ^ (e - a)
  /-- Every frozen round carries more than a quarter of the whole source
  family: the first round is the full family, and every later round was
  selected by a failed global stop test. -/
  round_width : ∀ p ∈ (grayTailRunState q L a e n sigma A sm T).frozen,
    n * 2 ^ (e - a) < 4 * p.slots.length
  /-- The first round contains every source son. -/
  first_round : ∀ p ∈ (grayTailRunState q L a e n sigma A sm T).frozen,
    p.roundIndex = 0 →
      ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)), c.val < 2 ^ (e - a) →
        GrayTailRoundHasSon p i c
  /-- Displayed son requests are the accumulated frozen increments, raised to
  `epsilon` exactly above the source threshold. -/
  son_request_eq : ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)),
    getFamilyReq (grayTailRunMove q L a e n sigma A sm T) i.val [c.val] =
      (if grayTailThreshold q e <
          grayTailFrozenSonBase (grayTailRunState q L a e n sigma A sm T).frozen i c
        then dyadicScale e
        else grayTailFrozenSonBase (grayTailRunState q L a e n sigma A sm T).frozen i c)
  /-- Displayed root requests carry the terminal floor adjustment. -/
  root_request_eq : ∀ i : Fin n,
    getFamilyReq (grayTailRunMove q L a e n sigma A sm T) i.val [] =
      max (∑ c : Fin (grayTailBranch q L a e),
            getFamilyReq (grayTailRunMove q L a e n sigma A sm T) i.val [c.val])
        (grayTailTargetFloor q a)
  /-- Sons outside the `2 ^ (e - a)` source sons never carry request. -/
  unused_zero : ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)),
    ¬ c.val < 2 ^ (e - a) →
      grayTailFrozenSonBase (grayTailRunState q L a e n sigma A sm T).frozen i c = 0
  /-- No son accumulates more than `epsilon`. -/
  son_base_le : ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)),
    grayTailFrozenSonBase (grayTailRunState q L a e n sigma A sm T).frozen i c ≤
      dyadicScale e
  /-- Every inactive source son left through one of the two exact exits. -/
  exits : ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)), c.val < 2 ^ (e - a) →
    ¬ GrayTailHasSon (grayTailRunState q L a e n sigma A sm T).slots i c →
      ((grayTailThreshold q e <
            grayTailFrozenSonBase
              (grayTailRunState q L a e n sigma A sm T).frozen i c) ∧
          GrayTailThresholdExit e A sm
            (grayTailRunState q L a e n sigma A sm T).frozen i c) ∨
        (GrayTailPersistentReserveExit e A sm
            (grayTailRunState q L a e n sigma A sm T).frozen i c ∧
          grayTailFrozenSonBase
              (grayTailRunState q L a e n sigma A sm T).frozen i c ≤
            grayTailThreshold q e)
  /-- Each inactive source son has an exact owner (last participating) round. -/
  owner_split : ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)), c.val < 2 ^ (e - a) →
    ¬ GrayTailHasSon (grayTailRunState q L a e n sigma A sm T).slots i c →
      GrayTailOwnerSplitAt (grayTailRunState q L a e n sigma A sm T).frozen i c
        (grayTailOwnerIndex (grayTailRunState q L a e n sigma A sm T).frozen i c)


/-- Reserve witnesses for inactive source sons.  Each witness is taken at its
own time no later than a common horizon `U`; no persistence or anchoring at the
terminal time `T` is assumed.  The final conjunct records exact freshness
against frozen gray cells except the owner-charged contribution. -/
def GrayTailReservePackage (q L a e n : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : ℕ → FamilyServerMove) (T U : ℕ)
    (rtime : Fin n → Fin (grayTailBranch q L a e) → ℕ)
    (reserve : Fin n → Fin (grayTailBranch q L a e) → BitString) : Prop :=
  T ≤ U ∧
    ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)), c.val < 2 ^ (e - a) →
    ¬ GrayTailHasSon (grayTailRunState q L a e n sigma A sm T).slots i c →
      rtime i c ≤ U ∧
      IsTailFamilyReserve e (grayTailBranch q L a e) A n i.val
        (sm (rtime i c)) [c.val] (reserve i c) ∧
      (∀ p ∈ (grayTailRunState q L a e n sigma A sm T).frozen,
        ∀ j : Fin p.slots.length,
          (p.roundIndex ≠
              grayTailOwnerIndex (grayTailRunState q L a e n sigma A sm T).frozen i c ∨
            (p.slots.get j).1 ≠ i ∨ (p.slots.get j).2.1 ≠ c) →
          ∀ z ∈ getFamilyAlloc
              (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm p.serverTime))
              j.val [],
            ¬ (reserve i c <+: z ∨ z <+: reserve i c))


instance instInhabitedGrayTailRound (n b : ℕ) : Inhabited (GrayTailRound n b) :=
  ⟨{ roundIndex := 0, serverTime := 0, epsDepth := 0, slots := [], move := [],
     allocated := [], unavailable := [] }⟩

/-- Slots whose outer root belongs to the selected subfamily. -/
def grayTailSelectKeep {n b : ℕ} (I : List ℕ) : GrayTailSlot n b → Bool :=
  fun s => decide (s.1.val ∈ I)

open scoped Classical in
/-- Selected slots with the owner-charged sons of round `r` removed. -/
noncomputable def grayTailChargedKeep {n b : ℕ} (frozen : GrayTailFrozen n b)
    (slots : List (GrayTailSlot n b)) (used : ℕ) (I : List ℕ) (r : ℕ) :
    GrayTailSlot n b → Bool :=
  fun s => decide (s.1.val ∈ I) &&
    !decide (s.2.1.val < used ∧ ¬ GrayTailHasSon slots s.1 s.2.1 ∧
      grayTailOwnerIndex frozen s.1 s.2.1 = r)

open scoped Classical in
/-- The finite set of pairs `(i, c)` with `i.val ∈ I`, `c.val < used` and `¬ GrayTailHasSon slots i
c`: the source sons of the selected subfamily that carry no active slot. -/
noncomputable def grayTailSelectedInactive {n b : ℕ}
    (slots : List (GrayTailSlot n b)) (used : ℕ) (I : List ℕ) :
    Finset (Fin n × Fin b) :=
  Finset.univ.filter fun z =>
    z.1.val ∈ I ∧ z.2.val < used ∧ ¬ GrayTailHasSon slots z.1 z.2

open scoped Classical in
/-- Doubled owner charge assigned to the frozen round of index `r`: twice the actual
owner-round increments of the selected sons whose last participation is `r`. -/
noncomputable def grayTailOwnerCharge {n b : ℕ} (frozen : GrayTailFrozen n b)
    (slots : List (GrayTailSlot n b)) (used : ℕ) (I : List ℕ) (r : ℕ) : ℚ :=
  2 * ∑ z ∈ (grayTailSelectedInactive slots used I).filter
      fun z => grayTailOwnerIndex frozen z.1 z.2 = r,
    grayTailSonBase
      (grayTailSlotEntries (frozen.getD r default).slots (frozen.getD r default).move)
      z.1 z.2

/-- Twice the root request of the slots of `p` selected by `grayTailSelectKeep I`, minus the total
root request of all slots of `p`. -/
noncomputable def grayTailRoundSigned {n b : ℕ} (I : List ℕ)
    (p : GrayTailRound n b) : ℚ :=
  2 * totalRootRequestOnList (grayTailSelectedIndices (grayTailSelectKeep I) p) p.move -
    totalRootRequest p.slots.length p.move

/-- The sum `∑ c, grayTailFrozenSonBase frozen i c` over all sons `c`: the request accumulated at
the outer root `i` by all frozen rounds. -/
noncomputable def grayTailGamma {n b : ℕ} (frozen : GrayTailFrozen n b)
    (i : Fin n) : ℚ :=
  ∑ c : Fin b, grayTailFrozenSonBase frozen i c

open scoped Classical in
/-- The two accounting facts of Leaf C for one selected subfamily `I`:
the selected-request identity and the round-by-round positive-part credit, with
the owner contribution
removed *before* clamping. -/
noncomputable def GrayTailSelectedRoundAccounting
    (q L a e n : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (T : ℕ) (I : List ℕ) : Prop :=
  let st := grayTailRunState q L a e n sigma A sm T
  ((st.frozen.map (grayTailRoundSigned I)).sum =
      2 * ∑ i ∈ Finset.univ.filter fun i : Fin n => i.val ∈ I,
            grayTailGamma st.frozen i -
        ∑ i : Fin n, grayTailGamma st.frozen i) ∧
    (∀ p ∈ st.frozen,
      max 0 (halfAmplification q *
          (grayTailRoundSigned I p -
            grayTailOwnerCharge st.frozen st.slots (2 ^ (e - a)) I p.roundIndex)) ≤
        grayMassOfCount (p.epsDepth + L)
          (newGrayCount p.epsDepth (p.epsDepth + L)
            (familyAllocatedOnList
              (grayTailSelectedIndices
                (grayTailChargedKeep st.frozen st.slots (2 ^ (e - a)) I p.roundIndex) p)
              (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm p.serverTime)))
            p.unavailable))


open scoped Classical in
/-- The feasible-history hereditary inequality.  It deliberately retains one
positive part per frozen round; collapsing the rounds earlier is not valid. -/
noncomputable def GrayTailHereditaryArithmetic
    (q L a e n : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (T : ℕ) (I : List ℕ) : Prop :=
  let st := grayTailRunState q L a e n sigma A sm T
  let Q : Fin n → ℚ := fun i =>
    getFamilyReq (grayTailRunMove q L a e n sigma A sm T) i.val []
  (halfAmplification q + 1 / 2) *
      (2 * ∑ i ∈ Finset.univ.filter fun i : Fin n => i.val ∈ I, Q i -
        ∑ i : Fin n, Q i) ≤
    (st.frozen.map fun p =>
      max 0 (halfAmplification q *
        (grayTailRoundSigned I p -
          grayTailOwnerCharge st.frozen st.slots
            (2 ^ (e - a)) I p.roundIndex))).sum +
      dyadicScale e *
        ((grayTailSelectedInactive st.slots (2 ^ (e - a)) I).card : ℚ)


end Kolmogorov
