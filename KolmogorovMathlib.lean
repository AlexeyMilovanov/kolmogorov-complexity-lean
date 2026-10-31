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
import KolmogorovMathlib.Combinatorics.EdgeColouring
import KolmogorovMathlib.Combinatorics.LinearNetworkCoding
import KolmogorovMathlib.Combinatorics.OnlineMatching
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
import KolmogorovMathlib.Complexity.Tuples.PrefixOneTerm
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
import KolmogorovMathlib.Entropy.Codes.Huffman
import KolmogorovMathlib.Entropy.Complexity.Expected
import KolmogorovMathlib.Entropy.Complexity.RandomSequences
import KolmogorovMathlib.Entropy.Complexity.ShannonCoding
import KolmogorovMathlib.Extras
import KolmogorovMathlib.Foundation.Arslanov
import KolmogorovMathlib.Foundation.FixedPointFree
import KolmogorovMathlib.Foundation.RSeparability
import KolmogorovMathlib.InformationInequalities.Combinatorial
import KolmogorovMathlib.InformationInequalities.NonShannonTheorems
import KolmogorovMathlib.InformationInequalities.TwoThree
import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Interface.StandardMachine
import KolmogorovMathlib.MonotoneComplexity
import KolmogorovMathlib.MonotoneComplexity.APrioriAtoms.Gap
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse
import KolmogorovMathlib.Multisource.CommonInformationRequest
import KolmogorovMathlib.Multisource.InformationDistance
import KolmogorovMathlib.Multisource.MinimalSufficientStatistics
import KolmogorovMathlib.Multisource.Muchnik
import KolmogorovMathlib.Multisource.MuchnikGame
import KolmogorovMathlib.Multisource.NetworkCoding
import KolmogorovMathlib.Multisource.TwoConditions
import KolmogorovMathlib.Oracle.Basic
import KolmogorovMathlib.Oracle.FinitePrefix
import KolmogorovMathlib.Oracle.Joins
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.Oracle.PrefixComplexity
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic
import KolmogorovMathlib.Oracle.PrefixComplexity.MonotonicityThreshold
import KolmogorovMathlib.Oracle.Universal
import KolmogorovMathlib.Oracle.Universal.Enumeration
import KolmogorovMathlib.Oracle.Universal.Optimal
import KolmogorovMathlib.PointToSet.BSDimension.Defs
import KolmogorovMathlib.PointToSet.BSDimension.Lower
import KolmogorovMathlib.PointToSet.BSDimension.Lower.EffectiveEqSup
import KolmogorovMathlib.PointToSet.BSDimension.Lower.MassDichotomy
import KolmogorovMathlib.PointToSet.BSDimension.Lower.NullCovers
import KolmogorovMathlib.PointToSet.BSDimension.Lower.Realizers
import KolmogorovMathlib.PointToSet.BSDimension.Upper
import KolmogorovMathlib.PointToSet.BSDimension.Upper.OracleAttainment
import KolmogorovMathlib.PointToSet.BSDimension.Upper.PointToSetPrinciple
import KolmogorovMathlib.PointToSet.BSDimension.Upper.ScaleLimits
import KolmogorovMathlib.PointToSet.BSDimension.Upper.UniformNets
import KolmogorovMathlib.PointToSet.BowenEquation
import KolmogorovMathlib.PointToSet.BowenEquation.ConstantExponent
import KolmogorovMathlib.PointToSet.BowenEquation.NonuniformCounterexample
import KolmogorovMathlib.PointToSet.BowenEquation.Pointwise
import KolmogorovMathlib.PointToSet.BowenEquation.PointwiseCriticalValue
import KolmogorovMathlib.PointToSet.BowenEquation.SetCriticalValue
import KolmogorovMathlib.PointToSet.BowenEquation.SetRoot
import KolmogorovMathlib.PointToSet.BowenEquation.SlopeBounds
import KolmogorovMathlib.PointToSet.ComputableMetric
import KolmogorovMathlib.PointToSet.ComputableMetric.DimensionAlongScales
import KolmogorovMathlib.PointToSet.ComputableMetric.Presentation
import KolmogorovMathlib.PointToSet.ComputableMetric.StaticDimensions
import KolmogorovMathlib.PointToSet.Conformal.Classical
import KolmogorovMathlib.PointToSet.Conformal.Classical.HausdorffCovers
import KolmogorovMathlib.PointToSet.Conformal.Classical.HausdorffPointToSet
import KolmogorovMathlib.PointToSet.Conformal.Classical.PackingModifiedBox
import KolmogorovMathlib.PointToSet.Conformal.Classical.PackingPointDimension
import KolmogorovMathlib.PointToSet.Conformal.Classical.PointToSetPrinciple
import KolmogorovMathlib.PointToSet.Conformal.Defs
import KolmogorovMathlib.PointToSet.Conformal.Distortion
import KolmogorovMathlib.PointToSet.Conformal.Distortion.DistortionModuli
import KolmogorovMathlib.PointToSet.Conformal.Distortion.PointwiseDimension
import KolmogorovMathlib.PointToSet.Conformal.TheoremE
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.ActualDiameterBounds
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.ActualDiameterCounterexample
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.BallComparison
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.DimensionTheorem
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.FactorialBoxBounds
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.FactorialPackingGeometry
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.FactorialUltrametric
import KolmogorovMathlib.PointToSet.Dynamics
import KolmogorovMathlib.PointToSet.Dynamics.BirkhoffComputability
import KolmogorovMathlib.PointToSet.Dynamics.BowenBalls
import KolmogorovMathlib.PointToSet.Dynamics.PointwiseQuantities
import KolmogorovMathlib.PointToSet.Dynamics.PresentationChangeBS
import KolmogorovMathlib.PointToSet.Examples
import KolmogorovMathlib.PointToSet.Examples.MiddleThirds
import KolmogorovMathlib.PointToSet.Examples.MiddleThirdsPointwise
import KolmogorovMathlib.PointToSet.Examples.MiddleThirdsUpper
import KolmogorovMathlib.PointToSet.ForMathlib
import KolmogorovMathlib.PointToSet.Geometry.CoverCenters
import KolmogorovMathlib.PointToSet.Geometry.CoverCenters.BSDimensionIndependence
import KolmogorovMathlib.PointToSet.Geometry.CoverCenters.CenterPolicies
import KolmogorovMathlib.PointToSet.Geometry.CoverCenters.PressureIndependence
import KolmogorovMathlib.PointToSet.Geometry.InfiniteEntropy
import KolmogorovMathlib.PointToSet.Geometry.InfiniteEntropy.FiniteAlphabetSubsystems
import KolmogorovMathlib.PointToSet.Geometry.InfiniteEntropy.NoBowenRoot
import KolmogorovMathlib.PointToSet.Order
import KolmogorovMathlib.PointToSet.Order.AchievingOracles
import KolmogorovMathlib.PointToSet.Order.NormalizedSlack
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.CoveringComparison
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.PackingSeparatedDefs
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.RadiusComparison
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.RawThresholdCounterexample
import KolmogorovMathlib.PointToSet.PackingEquivalences.Defs
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.Equivalence
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.ModifiedSeparated
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.PackingSeparatedDefs
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.ScaleDichotomy
import KolmogorovMathlib.PointToSet.Pressure.Defs
import KolmogorovMathlib.PointToSet.Pressure.Lower
import KolmogorovMathlib.PointToSet.Pressure.Lower.BowenGeometry
import KolmogorovMathlib.PointToSet.Pressure.Lower.CenteredContents
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyCharacterization
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyPointToSet
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyZeroPotential
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyZeroPotentialVariants
import KolmogorovMathlib.PointToSet.Pressure.Lower.NullCovers
import KolmogorovMathlib.PointToSet.Pressure.Lower.PointToSetPrinciple
import KolmogorovMathlib.PointToSet.Pressure.Lower.PointwiseTails
import KolmogorovMathlib.PointToSet.Pressure.Lower.SymbolicOrbitComplexity
import KolmogorovMathlib.PointToSet.Pressure.Upper
import KolmogorovMathlib.PointToSet.Pressure.Upper.EffectiveEqSup
import KolmogorovMathlib.PointToSet.Pressure.Upper.PointToSetPrinciple
import KolmogorovMathlib.PointToSet.Pressure.Upper.ScaleComparison
import KolmogorovMathlib.PointToSet.Pressure.Upper.UniformNets
import KolmogorovMathlib.PointToSet.SymbolicSet
import KolmogorovMathlib.Prefix.BlockingReadMachines
import KolmogorovMathlib.Prefix.EntropyFunctions
import KolmogorovMathlib.Prefix.ExtensionTheorem
import KolmogorovMathlib.Prefix.KraftConverse
import KolmogorovMathlib.Prefix.NumericalValues
import KolmogorovMathlib.Prefix.PairComplexity
import KolmogorovMathlib.Prefix.SelfDelimitingMachines
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.RandomStrings.KeyInstances
import KolmogorovMathlib.RandomStrings.PathDataSATree
import KolmogorovMathlib.RandomStrings.Plain.Basic
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.AllocationLengths
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.CapacityFailure
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.DummyHistory
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.DummyIdentities
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.EarlierTargets
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.FuelHistory
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.LevelFrames
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.LevelRanges
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.OutputSet
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.PhaseCountBounds
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.TargetRange
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.UniformRank
import KolmogorovMathlib.RandomStrings.Plain.Construction.Actions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Conditional
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.AllocationGraph
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.AllocationProvenance
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.FundedFrames
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.LiveCounters
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.OracleAgreement
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.PayoffReceipts
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.PolynomialCounting
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.SimulationEvents
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.SimulationState
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.VirtualOutput
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.VirtualStabilization
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.Allocations
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.ConstructionTransitions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.CounterGameOperations
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.EventActions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.GameTransitions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.LiveInvariantSteps
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.LiveInvariants
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.StateMachine
import KolmogorovMathlib.RandomStrings.Plain.Construction.Referees
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.AllocationOccupancy
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ArchiveMonotonicity
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CandidateChronology
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferActions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferCandidates
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferInitialization
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGame
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameHigherLevels
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameInitial
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameInvariantBase
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameInvariantTick
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.EventuallyBounded
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FighterInvariant
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequest
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestOpponent
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestPriority
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestReceipts
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestSaturation
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestTrace
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.HigherLevelServices
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.LegalPlay
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.OpponentStream
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.Padding
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhasePreservation
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparation
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationAllocationGrowth
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationCandidates
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationClasses
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationDummyFreshness
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationDummyRecords
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationDummyTrace
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationSources
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ServiceInvariant
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerFrames
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerLevels
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.StrategyClosure
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.StrategyPostponement
import KolmogorovMathlib.RandomStrings.Plain.Construction.State
import KolmogorovMathlib.RandomStrings.Plain.Encoding
import KolmogorovMathlib.RandomStrings.Plain.Enumeration
import KolmogorovMathlib.RandomStrings.Plain.Enumeration.CanonicalSpec
import KolmogorovMathlib.RandomStrings.Plain.Enumeration.Schedule
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity.Bounds
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity.Density
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity.Relaxed
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice.Decompositions
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice.PastFuture
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice.SquareRoot
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.BoundedSolver
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.LegalMoves
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.RoleExchange
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.Rules
import KolmogorovMathlib.RandomStrings.Plain.HaltingLanguage
import KolmogorovMathlib.RandomStrings.Plain.ListLemmas
import KolmogorovMathlib.RandomStrings.Plain.Main
import KolmogorovMathlib.RandomStrings.Plain.Markers
import KolmogorovMathlib.RandomStrings.Plain.Markers.LastProgram
import KolmogorovMathlib.RandomStrings.Plain.Markers.StagePrefix
import KolmogorovMathlib.RandomStrings.Plain.Native.Adapters
import KolmogorovMathlib.RandomStrings.Plain.Native.Instances
import KolmogorovMathlib.RandomStrings.Plain.Native.Referees
import KolmogorovMathlib.RandomStrings.Plain.Native.Referees.ClockedDecider
import KolmogorovMathlib.RandomStrings.Plain.Native.Referees.EffectiveInterface
import KolmogorovMathlib.RandomStrings.Plain.PrefixInterface
import KolmogorovMathlib.RandomStrings.Plain.StructuralProxy
import KolmogorovMathlib.RandomStrings.Plain.StructuralProxy.Symmetry
import KolmogorovMathlib.RandomStrings.Plain.StructuralProxy.Towers
import KolmogorovMathlib.RandomStrings.Plain.Target
import KolmogorovMathlib.RandomStrings.PrefixForm
import KolmogorovMathlib.RandomStrings.SAExpE
import KolmogorovMathlib.Restricted.DeficiencyEquiv
import KolmogorovMathlib.Restricted.DescriptionProfileGap
import KolmogorovMathlib.Restricted.DescriptionProfileGap.SlackArithmetic
import KolmogorovMathlib.Restricted.Examples.Cylinders
import KolmogorovMathlib.Restricted.Examples.HammingCurve
import KolmogorovMathlib.Restricted.Examples.Masks
import KolmogorovMathlib.Restricted.MinimalRestrictedDescriptions
import KolmogorovMathlib.Solomonoff.Main
import KolmogorovMathlib.Solomonoff.SelectedBits.Statements
import KolmogorovMathlib.Solomonoff.ShenQuestion.Extras
import KolmogorovMathlib.Solomonoff.ShenQuestion.LowerBound
import KolmogorovMathlib.StoppingComplexity.LengthBounds
import KolmogorovMathlib.StoppingComplexity.MainTheorem
import KolmogorovMathlib.StrongMerging.StatementsExtra


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
* `RandomStrings` — resource-bounded reductions to random strings: oracle machines, complexity
  classes, and the Allender–Friedman–Gasarch theorem that decidable sets polynomial-time
  reducible to the random strings of every universal prefix complexity lie in `EXPSPACE`;
* `Restricted` — description families and the restricted profiles of VS40 §6, including the
  realization theorem `prop_family_curve` and the concrete families;
* `Solomonoff` — the universal predictor `M(b | x) = M(xb) / M(x)` of the a priori probability
  on the tree, indices and prefix complexity of computable measures, and Solomonoff's theorem:
  against a computable measure `μ` the total expected squared prediction error is at most
  `(ln 2 / 2) (K(μ) + O(1))` and the predictions converge `μ`-almost surely; in
  `Solomonoff.ShenQuestion` the negative answer to Shen's question: the largest `f(x)` with
  `f(x) · Q(y | x) ≤ M(x y)` is not bounded by a constant times a discrete semimeasure;
* `StoppingComplexity` — randomized stopping machines, the monotone stopping complexity
  `K_stop` and the a priori stopping probability `M_stop`, and the lower bounds on the gap
  `K_stop − (−log M_stop)`, which exceeds `log m + log log log m` by any constant on
  infinitely many strings;
* `Deprecated` — the `@[deprecated] alias`es for names that have moved, generated from the
  rename tables.

Refutations of false readings of the sources live in the separate library
`KolmogorovCounterexamples`, which the library deliberately does not import.
-/
