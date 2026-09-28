import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock.Part01
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock.Part02
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock.Part03
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock.PrefixEquiv
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock.OmegaCode
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile

/-!
# VS40 Section 4, Milestone B7: standard blocks (standard descriptions)

The completed bound-`m` list has length `omegaCount c m`.  Its standard
decomposition is the binary decomposition of that length: when bit `j` is set,
the corresponding block starts after all blocks belonging to higher bits and
has size `2^j`.  This is distinct from the arbitrary aligned dyadic blocks used
in the reverse direction of `tail_characterization`; those are the chopped
standard blocks.
-/
