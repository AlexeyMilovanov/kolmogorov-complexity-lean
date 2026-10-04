import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator.FreeList
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator.Computability
import KolmogorovMathlib.Prefix.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The online Kraft–Chaitin allocator

This file builds the *online* (causal) prefix-free code allocator behind the
Kraft–Chaitin realization theorem and proves its three defining properties:

* `allocFun_computable` — the allocator is computable uniformly in the context;
* `allocFun_prefixFree` — codes for distinct requests are prefix-incomparable;
* `allocFun_success`    — if the total Kraft weight is `≤ 1`, every request is
  realized by a codeword of exactly the requested length.

The algorithm maintains a *free list* of tree nodes (bitstrings) kept in strictly
descending order of length (hence with pairwise distinct lengths).  A length-`l`
request is serviced by taking the unique free node of largest length `≤ l`,
splitting it into a length-`l` left-most descendant (the allocated codeword) and
its right siblings along the all-`false` path, and re-inserting the siblings in
sorted position.

The proofs are organized around three invariants of the free list:

* `DescLengths` (strictly descending lengths ⇒ distinct lengths);
* prefix-freeness of the node set;
* the mass identity `freeMass free + usedMass req n = 1`.

These are each shown to be preserved step by step.
-/
