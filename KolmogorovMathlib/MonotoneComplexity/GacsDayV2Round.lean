import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Schedule
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController

/-!
# V2 round metadata

Blueprint v11, Stage A3 (frozen record shape; proof doc v14 §9.0 item 5).

`GrayTailRoundV2` is a NEW record alongside the untouched V1
`GrayTailRound` (versioned-parallel migration; V1 is deleted at Stage E).
It splits the roles the flattened design fused into `epsDepth`: exactly
three scale fields —

* `blockAnchor` — the round's block anchor (the request scale of its
  block roots and the coarse end of its window);
* `childEps` — the ε-parameter of its child calls
  (`= blockAnchor + graySpendSpan (stage − 1)` on the schedule);
* `fineEnd` — the fine end of the round's window, serving as BOTH the
  harvest-truncation scale and the replay truncation depth (one field —
  they are equal by design).

The final child depth is derived (`= fineEnd`), never stored.  The
remaining fields mirror V1's bookkeeping (times, slots, move, allocations,
and the per-round unavailable snapshot of the harvest architecture).
-/

namespace Kolmogorov

/-- One frozen round of the V2 controller: the server time and round index at which it was frozen,
its three scale fields `blockAnchor`, `childEps` and `fineEnd`, the slots it holds, the
recursive family move it stored, and the cylinders it allocated and the unavailable set it ran
against. -/
structure GrayTailRoundV2 (n b : Nat) where
  serverTime : Nat
  roundIndex : Nat
  blockAnchor : Nat
  childEps : Nat
  fineEnd : Nat
  slots : List (GrayTailSlot n b)
  move : FamilyClientMove
  allocated : Allocation
  unavailable : Allocation

namespace GrayTailRoundV2

variable {n b : Nat}

/-- The derived final child depth: exactly the window's fine end. -/
def childDepth (p : GrayTailRoundV2 n b) : Nat := p.fineEnd

/-- The schedule coherence of one V2 round at ladder stage `j`: the child
ε sits one spend span above the anchor, and the window's fine end is one
per-round budget above the anchor (the nesting theorem's shape). -/
def OnSchedule (j : Nat) (p : GrayTailRoundV2 n b) : Prop :=
  p.childEps = p.blockAnchor + graySpendSpan (j - 1) ∧
    p.fineEnd = p.blockAnchor + grayFootprint (j - 1)

/-- On the schedule, the child's window closes exactly at the round's
fine end: `childEps + childLoss = fineEnd` — the record-level face of the
nesting theorem. -/
theorem childEps_add_childLoss {j : Nat} {p : GrayTailRoundV2 n b}
    (hj : 4 ≤ j) (hp : OnSchedule j p) :
    p.childEps + grayChildLoss j = p.fineEnd := by
  obtain ⟨hc, hf⟩ := hp
  have hnest := graySpendSpan_add_childLoss (j := j) hj
  omega

/-- The V1 view of a V2 round: its block anchor plays the role of `epsDepth`
(the frozen son-request accounting and slot geometry are shared with V1). -/
def toV1 (p : GrayTailRoundV2 n b) : GrayTailRound n b where
  roundIndex := p.roundIndex
  serverTime := p.serverTime
  epsDepth := p.blockAnchor
  slots := p.slots
  move := p.move
  allocated := p.allocated
  unavailable := p.unavailable

end GrayTailRoundV2

end Kolmogorov
