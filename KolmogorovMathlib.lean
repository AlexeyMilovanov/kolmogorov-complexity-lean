import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs
import KolmogorovMathlib.AlgorithmicProbability.ConditionalUniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.HaltingProbabilityApproximation
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part01
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part02
import KolmogorovMathlib.AlgorithmicRandomness
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists
import KolmogorovMathlib.AlgorithmicStatistics.Conservation
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyTest
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyValue
import KolmogorovMathlib.AlgorithmicStatistics.DescriptionProfileInvariance
import KolmogorovMathlib.AlgorithmicStatistics.NonStochasticMassWeak
import KolmogorovMathlib.AlgorithmicStatistics.StochasticityProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongModelImageSet
import KolmogorovMathlib.AlgorithmicStatistics.StructureFunctionDeficiency
import KolmogorovMathlib.CommonInformation
import KolmogorovMathlib.Complexity.AlphabetComplexity
import KolmogorovMathlib.Complexity.BusyBeaver
import KolmogorovMathlib.Complexity.CanonicalObjects
import KolmogorovMathlib.Complexity.ChaitinCorollaries
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.DifferentDecompressors
import KolmogorovMathlib.Complexity.EnumerableFamilies
import KolmogorovMathlib.Complexity.GrowthEnumeration
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.LayeredDecompressors
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SecondIncompletenessCorollaries
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Deprecated.AlgorithmicProbability
import KolmogorovMathlib.Deprecated.AlgorithmicRandomness
import KolmogorovMathlib.Deprecated.AlgorithmicStatistics
import KolmogorovMathlib.Deprecated.CommonInformation
import KolmogorovMathlib.Deprecated.Complexity01
import KolmogorovMathlib.Deprecated.Complexity02
import KolmogorovMathlib.Deprecated.Complexity03
import KolmogorovMathlib.Deprecated.Core
import KolmogorovMathlib.Deprecated.Foundation
import KolmogorovMathlib.Deprecated.Interface
import KolmogorovMathlib.Deprecated.MonotoneComplexity
import KolmogorovMathlib.Deprecated.Prefix
import KolmogorovMathlib.Deprecated.Restricted
import KolmogorovMathlib.Extras
import KolmogorovMathlib.Foundation.Arslanov
import KolmogorovMathlib.Foundation.FixedPointFree
import KolmogorovMathlib.Foundation.RSeparability
import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Interface.StandardMachine
import KolmogorovMathlib.MonotoneComplexity
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse
import KolmogorovMathlib.Prefix.BlockingReadMachines
import KolmogorovMathlib.Prefix.ExtensionTheorem
import KolmogorovMathlib.Prefix.KraftConverse
import KolmogorovMathlib.Prefix.NumericalValues
import KolmogorovMathlib.Prefix.PairComplexity
import KolmogorovMathlib.Prefix.SelfDelimitingMachines
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Restricted.DeficiencyEquiv
import KolmogorovMathlib.Restricted.DescriptionProfileGap
import KolmogorovMathlib.Restricted.DescriptionProfileGap.SlackArithmetic
import KolmogorovMathlib.Restricted.Examples.Cylinders
import KolmogorovMathlib.Restricted.Examples.HammingCurve
import KolmogorovMathlib.Restricted.Examples.Masks
import KolmogorovMathlib.Restricted.MinimalRestrictedDescriptions

/-!
# Algorithmic information theory

Kolmogorov complexity of finite binary strings and the theory built on it: plain and
conditional complexity of bitstrings, prefix complexity, monotone complexity, algorithmic
probability, Martin-Löf randomness, algorithmic statistics, and the profiles of a string
relative to a restricted family of finite-set descriptions.  Decompressors are partial
functions in the sense of Mathlib's computability library, complexities take values in `ℕ∞`,
and statements carry their additive `O(1)` and logarithmic `O(log n)` slack terms explicitly.

The background references are A. Shen, V. A. Uspensky and N. Vereshchagin, *Kolmogorov
Complexity and Algorithmic Randomness* (cited as SUV), and N. Vereshchagin and A. Shen,
*Algorithmic statistics: forty years later* (cited as VS40); `docs/SUV_COVERAGE.md` maps items
of the book to declarations.

This module is the aggregate root: it imports the whole library.  Its parts are

* `Foundation` — search operators, recursively enumerable relations, encodings of naturals and
  bitstrings, fixed-point-free functions, Arslanov's criterion, r-separability;
* `Core` — partial decompressors, plain and conditional complexity, the universal
  decompressor and the invariance theorem;
* `Encoding` — self-delimiting codes for tuples and lists of bitstrings;
* `Complexity` — the elementary bounds, incompressibility, uncomputability, the Chaitin-style
  incompleteness interfaces, enumerable families, canonical objects, pair complexity,
  information and the busy beaver;
* `Interface` — standard machines, dovetailing, computable and lower-semicomputable reals;
* `Prefix` — prefix-free machines, the Kraft inequality and its converse, prefix complexity
  and symmetry of information;
* `MonotoneComplexity` — monotone complexity, effective Hausdorff dimension, the Levin–Schnorr
  theorem, `Ω`, Solovay functions and the Gács–Day theorem;
* `AlgorithmicProbability` — semimeasures, mixtures, domination, universal and conditional
  universal semimeasures, the coding theorem and Kraft–Chaitin coding;
* `AlgorithmicRandomness` — Martin-Löf randomness and its lower-semicomputable
  characterisations;
* `AlgorithmicStatistics` — models, randomness and optimality deficiency, stochasticity,
  non-stochastic strings, and in `TwoPart` the two-part descriptions, gap counting,
  stochasticity profiles and curve realization of VS40 §3;
* `CommonInformation` — common information, the obstructions to extracting it, incidence
  regions;
* `Restricted` — description families and the restricted profiles of VS40 §6, including the
  realization theorem `prop_family_curve` and the concrete families;
* `Deprecated` — the `@[deprecated] alias`es for names that have moved, generated from the
  rename tables.

Refutations of false readings of the sources live in the separate library
`KolmogorovCounterexamples`, which the library deliberately does not import.
-/
