import KolmogorovMathlib.CommonInformation.FixedHistogramRank.RankDecoder
import KolmogorovMathlib.CommonInformation.FixedHistogramRank.PlainAndFibreDecoders
import KolmogorovMathlib.CommonInformation.FixedHistogramRank.FibreEnumeration
import KolmogorovMathlib.CommonInformation.FixedFrequency
import KolmogorovMathlib.CommonInformation.FixedHistogram
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaCount
import KolmogorovMathlib.CommonInformation.TypeBounds
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Rank coding of fixed-histogram words: the group

A word over a finite alphabet with a prescribed histogram is described by its rank among the
words of that histogram; relative to a projection, by its rank in the fibre.  `RankDecoder`
sets up the codes and the parameter block, `PlainAndFibreDecoders` proves the plain rank bound
and enumerates the fibre, and `FibreEnumeration` proves the conditional bound and the matching
maximality statement.  These are the estimates the chain-sample arguments of `ChainSample`
use.
-/
