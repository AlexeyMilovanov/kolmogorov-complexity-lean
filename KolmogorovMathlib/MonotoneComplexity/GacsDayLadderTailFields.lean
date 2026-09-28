import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.EntrySupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.FrozenCoherence
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.EntryMonotonicity
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.AvoidsSmall
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafD
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailPointwise

/-!
# The individual fields of the weak tail game specification

`grayTailStrategy_weak_gameSpec` (child `E5` of Leaf E) bundles eleven
independent assertions about the displayed outer play of the tail controller.
This module separates them.

```text
E5a  grayTail_entryMove_supported        support of one grafted recursive move (proved)
E5b  grayTail_fold_entries_supported     support of every entry of a reachable state (proved)
E5c  grayTailStrategy_rangeSupported     `range_supported`                       (proved)
E5d  grayTailStrategy_treeSupported      `tree_supported`                        (proved)
E5e  grayTail_output_coherentCap         `legal`, coherence and the root cap
E5f  grayTail_output_monotone            `legal`, monotonicity in the outer time
E5g  grayTail_output_avoidsSmall         `minimum_request`
```

`E5c` and `E5d` are proved here outright: the displayed move is a two-level
graft, so its support is exactly the support of the recursive moves grafted
below the grandsons, and those are supplied by the preceding rung
(`RobustGrayRung`), whose branching bound `ladderBranching B (grayCallDepth q e)
(grayTailRoundEps q L e r)` is below the outer branching and whose height
`2 * q` is two levels below `2 * (q + 1)`.

The three remaining statements `E5e`, `E5f`, `E5g` are the genuinely numerical
outer-bookkeeping facts and are strictly narrower than the old single leaf: each
one is a *single* field of `GrayFamilyGameSpec` for the concrete displayed move
`grayTailOutput`, with no hereditary, geometric or win content.
-/
