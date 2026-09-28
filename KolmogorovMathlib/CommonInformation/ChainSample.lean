import KolmogorovMathlib.CommonInformation.ChainSample.Part01
import KolmogorovMathlib.CommonInformation.ChainSample.FibreDecompositionOneMaximal
import KolmogorovMathlib.CommonInformation.ChainFibre
import KolmogorovMathlib.CommonInformation.MaximalSampleFibre
import KolmogorovMathlib.CommonInformation.ChainWitness
import KolmogorovMathlib.CommonInformation.FixedHistogramRank
import KolmogorovMathlib.CommonInformation.FixedHistogramProjectionParams
import KolmogorovMathlib.CommonInformation.PlainCoding

/-!
# One maximal sample of a conditional-independence chain

This file develops the "single maximally complex full-chain sample" layer for
SUV Exercise 316.  A `ChainDist` with rational atoms and
`Q ∣ N` has an exact natural-number histogram `chainHistogram`; a sample word
`W : List (Fin (2*k+2) → Bool)` *realises* that histogram when every atom `v`
occurs exactly `chainHistogram D hQ N v` times.

The key discipline (see the strategy risks) is that **every** projection profile
must refer to the *same* maximal sample `W`.  The projection primitives
`chainWordAt`/`chainPairAt`/`chainTripleAt` and the structure
`IsMaximalChainSample` fix that sample once and for all.

The count lemmas below convert the atom-level realisation hypothesis into the
one-, two-, and three-coordinate empirical counts, matching
`chainHistogram1`/`chainHistogram2`/`chainHistogram3`.  They all follow from one
general list identity, `count_map_eq_sum_count`.
-/
