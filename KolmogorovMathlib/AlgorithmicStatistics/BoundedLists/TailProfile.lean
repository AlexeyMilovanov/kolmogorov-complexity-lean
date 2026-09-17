import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile.Part01
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile.Uniform
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.Position
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization

/-!
# VS40 Section 4: relation to the ordinary profile

This file develops the bridge between the prefix-machine description profile
`InDescriptionProfile U x i j` (Section 3) and the plain-complexity bounded
list `completedBoundedOutput c m` (Section 4, machine `V` with `IsCodeFor c V`).

The public endpoint is `tail_characterization`, with both directions:

* if `x` has an `(i,j)`-description then `x` is at least `2^(j-O(log n))` from
  the end of the `(i+j+O(log n))`-list;
* if at least `2^j` elements follow `x` in the `(i+j)`-list then `x` has an
  `(i+O(log n),j)`-description.

This file proves the **direction-1 membership workhorse**: every member of an
`(i,j)`-description has plain complexity `i+j+O(log j)`, hence appears in the
`(i+j+O(log j))`-list.  The argument is the two-part code
`y = decodeElement (S.code, address of y in S)`, whose plain complexity is
bounded by `setComplexity U S + |address| + O(1) ≤ i + j + O(log j)` using the
plain/prefix pair comparison `plainK_pair_le_KPPlain_add_KPPlain`.

For the forward direction, a uniform partial-recursive selector waits until
every member of the model has appeared, reads the exact number of remaining
outputs, and reconstructs `omegaCount`.  Its complexity bound contradicts
`plainKNat_omegaCount_lower` if the suffix is too short.  For the converse, a
second uniform selector reconstructs the full dyadic block containing `x`.
-/
