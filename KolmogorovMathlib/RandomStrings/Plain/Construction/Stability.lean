/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.Padding
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestReceipts
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestTrace
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestPriority
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestOpponent
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequest
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerFrames
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerLevels
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationSources
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationCandidates
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationClasses
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparation
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.LegalPlay
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferInitialization
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferActions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferCandidates
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.StrategyPostponement
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.StrategyClosure
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameInitial
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameInvariantBase
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameInvariantTick
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameHigherLevels
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGame
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.EventuallyBounded
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.OpponentStream
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.AllocationOccupancy
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CandidateChronology
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationAllocationGrowth
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationDummyFreshness

/-!
# Good padding, true-marker realization, and priority stability

This aggregator imports the `Construction/Stability/` directory. It shows that, for a
suitably padded fighter machine, the phase started by the true marker of a late level really
plays its game to the end and is not disturbed by other levels. This is the "stability" input
of the diagonal argument in `Construction.Diagonal`.

* `Padding`: the constants of the construction and the choice of the padding
  (blueprint node `constr:dchoice`), together with the vocabulary for the true-marker phase.
* `PhaseSeparation*`, `AllocationOccupancy`, `CandidateChronology`, `SettledLower*`: the
  targets and queries of the true-marker phase are separated from the allocations of other
  phases, and lower levels have settled by the time of a late true marker.
* `LegalPlay`, `OpponentStream`, `ClosureBuffer*`, `Strategy*`, `CommonGame*`: the controlled
  player's responses and the opponent's moves are legal, and a common winning game persists
  along the play, both at ticks and inside the finite closure.
* `FundedRequest*`: every funded request of the surviving phase is realized, with priority
  over later requests, and the opponent budget is never exhausted.
* `EventuallyBounded`: the official counter position stabilizes.

The constants below certify the already defined guarded family. They are fixed before
padding is chosen. Phase identity uses the actual marker event, survival refers to the
active records and cancellation archive, and settledness includes the whole local history.
Initial answers come from the saved finite table before the dummy; they are distinct from
the live counter answers. Official play is observed both at ticks and inside finite closure.
-/
