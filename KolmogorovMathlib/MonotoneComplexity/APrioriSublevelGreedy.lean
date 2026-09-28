import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelGreedy.AddressState
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelGreedy.GreedyStages
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelMaxNodes
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.MonotoneComplexity.NestedAllocation
import KolmogorovMathlib.MonotoneComplexity.REClosure

/-!
# An effective address assignment for the a priori sublevel tree

`kaSublevel k` is a recursively enumerable, prefix-closed set of bitstrings all of whose
prefix-antichains have at most `2 ^ k` elements.  This file builds, *computably*, an on-line
greedy assignment of addresses of length exactly `k` to the nodes of that tree:

* the state of the construction is a finite list of pairs `(address, node)`;
* nodes are fed in as they are enumerated, shortest first;
* a new node inherits an address of its immediate predecessor when that predecessor is currently
  a leaf, and otherwise receives a completely fresh address, which is then also recorded for the
  whole branch leading to it.

The bookkeeping invariant is that the number of addresses in use never exceeds the number of
leaves of the current tree, which is a prefix-antichain, hence has at most `2 ^ k` elements; so a
fresh address is always available.

The resulting relation is a stream lower graph for each `k`, is recursively enumerable uniformly
in `k`, and assigns an address of length `k` to every element of `kaSublevel k`.
-/
