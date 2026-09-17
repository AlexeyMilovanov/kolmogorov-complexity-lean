import KolmogorovMathlib.Restricted.FamilyCurve.RunChain
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredRun
import KolmogorovMathlib.Restricted.FamilyCurve.BadStream
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredChain.PrefixRuns

/-!
# The vocabulary of an anchored sampled run

The anchored run of a curve grid over inputs of length `n` is always taken with the same
parameters: the ambient length `n + logSlack 8 n`, the sampling slack `sqrtSlack 8 n`, the
target exponents `restrictedAnchoredTarget`, and the bad-code stream sampled against the grid
code.  Written out, these turn every statement about the run into a dozen lines, so they are
named here once and used by the lemmas of `Restricted/FamilyCurve/AnchoredChain` and of
`AlgorithmicStatistics/StrongModels/MixedFamilyVersion`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- The ambient length of the anchored run over inputs of length `n`. -/
abbrev restrictedAnchoredAmbient (n : ℕ) : ℕ := n + logSlack 8 n

/-- The sampling slack of the anchored run over inputs of length `n`. -/
abbrev restrictedAnchoredSlack (n : ℕ) : ℕ := sqrtSlack 8 n

/-- The chronological stream of bad codes sampled by the code `c` against the code of the
grid, for the pre-family of `ℬ`, up to server time `T`. -/
abbrev restrictedAnchoredBadStream (c : Code) (ℬ : DescriptionFamily) {n k N : ℕ}
    {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target) (T : ℕ) : List BitString :=
  restrictedSampledBadCodeStream c (restrictedCurveGridCode grid) ℬ.toPre N
    (restrictedAnchoredSlack n) T

/-- A run chain of `M` steps of the anchored run of `grid` in the family `𝒜`: the states are
the sampled-run states at the ambient length, overhead bound and target exponents of the
anchored run. -/
abbrev RestrictedAnchoredChain (𝒜 : DescriptionFamily) {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target) (M : ℕ) : Type :=
  RestrictedRunChain 𝒜 (N + 1) (restrictedAnchoredAmbient n)
    (2 * 𝒜.overhead (restrictedAnchoredAmbient n))
    (restrictedAnchoredTarget (restrictedAnchoredAmbient n) (restrictedAnchoredSlack n) grid) M

/-- A sampled-run state of the anchored run of `grid` in the family `𝒢`: the ambient length,
overhead bound and target exponents are those of the anchored run. -/
abbrev RestrictedAnchoredState (𝒢 : DescriptionFamily) {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target) : Type :=
  RestrictedSampledRunState 𝒢 (N + 1) (restrictedAnchoredAmbient n)
    (2 * 𝒢.overhead (restrictedAnchoredAmbient n))
    (restrictedAnchoredTarget (restrictedAnchoredAmbient n) (restrictedAnchoredSlack n) grid)

/-- The anchored decoder run after `m` events of `events`: the anchored initial state of
`grid` in the family `𝒢`, replayed through the first `m` events at the ambient length and
slack of the anchored run. -/
noncomputable abbrev restrictedAnchoredEventRun (𝒢 : DescriptionFamily) {n k N : ℕ}
    {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target) (events : List BitString)
    (m : ℕ) : Part BitString :=
  (restrictedEffectiveAnchoredInitialState 𝒢 (restrictedAnchoredAmbient n)
      (restrictedAnchoredSlack n) grid).bind
    (fun st0 => restrictedEventPrefixRun 𝒢 (𝒢.overhead (restrictedAnchoredAmbient n))
      (restrictedEffectiveAnchoredSizes (restrictedAnchoredAmbient n)
        (restrictedAnchoredSlack n) grid) st0 events m)

/-- The bad sets of `chain` are read off the sampled bad-code stream: the bad set of step `m`
is the decoding of the `m`-th entry of the stream. -/
def RestrictedAnchoredChainBads (𝒜 ℬ : DescriptionFamily) (c : Code) {n k N M : ℕ}
    {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target) (T : ℕ)
    (chain : RestrictedAnchoredChain 𝒜 grid M) : Prop :=
  ∀ m, chain.bads m = (decodeCoverCodeList
    ((restrictedAnchoredBadStream c ℬ grid T).getD m [])).toFinset

/-- Every bad set of `chain` is contained in the bad codes already processed by time `T + 1`:
the step-wise form in which the run's live sets are bounded below. -/
def RestrictedAnchoredChainBadsProcessed (𝒜 ℬ : DescriptionFamily) (c : Code) {n k N M : ℕ}
    {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target) (T : ℕ)
    (chain : RestrictedAnchoredChain 𝒜 grid M) : Prop :=
  ∀ m, m < (restrictedAnchoredBadStream c ℬ grid T).length →
    chain.bads m ⊆
      restrictedAnchoredProcessedBadUnion c ℬ (restrictedAnchoredSlack n) grid (T + 1)

end Kolmogorov
