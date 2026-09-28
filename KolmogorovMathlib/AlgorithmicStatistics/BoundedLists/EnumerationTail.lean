import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.EnumerationTail.Part01
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.EnumerationTail.Part02
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.BusyBeaver

/-!
# VS40 Section 4, Milestone B3: exact enumeration-tail coordinates

This file fixes the finite object whose asymptotic size is estimated in
`prop:enumeration-tail`.  At time `B'(m-s)` it contains exactly the completed
bound-`m` outputs that have not yet appeared in the bound-`m` enumeration.

The exact `s = 0` theorem is deliberately exposed: the tail after `B'(m)` is
empty.  Consequently a later positive power-of-two lower bound needs a genuine
large-`s` hypothesis, not only `s ≤ m`.
-/
