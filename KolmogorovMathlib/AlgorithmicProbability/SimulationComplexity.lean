/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.Simulation
import KolmogorovMathlib.AlgorithmicProbability.OptimalCoding

/-!
# Program Simulation Bridges Complexity and Semimeasure Universality

The repository carries two *separate* notions of one prefix machine "beating"
another:

* `IsOptimalPrefixConditional` (in `Prefix.Optimal`) is the **additive**,
  `KP`-side statement: `U` dominates every prefix decompressor `M` on conditional
  prefix complexity, `KP U ≤ KP M + c`.
* `ProgramSimulation` (in `AlgorithmicProbability.Simulation`) is a **constructive**
  injective, length-bounded, output-preserving translation of `M`'s programs into
  `U`'s, which yields **multiplicative** a priori semimeasure domination,
  `2^{-c} · m_M ≤ m_U`.

These were disconnected. This module supplies the missing bridge: a single
`ProgramSimulation U M c` already implies the additive `KP` bound `KP U ≤ KP M + c`
*with the same constant*. Consequently a machine that simulates every prefix
decompressor (`IsSimulationUniversal`) is simultaneously
`IsOptimalPrefixConditional` **and** semimeasure-dominant — the honest, logarithm-
free core shared by both universality stories.

**Scope.** No existence of a universal machine is claimed: constructing such a `U`
is the deferred computability step. No coding-theorem equality, no real logarithm,
and no lower-semicomputability is asserted here. Everything stays in `ENat`
(additive) / `ℝ≥0∞` (multiplicative `≤×`) with explicit constants.
-/

namespace Kolmogorov

open scoped ENNReal

/-- **Simulation bounds prefix complexity.** A `ProgramSimulation M N c` (every
`N`-program injects into an `M`-program of length `≤ |p| + c` producing the same
output) gives the additive `KP` bound `KP M x y ≤ KP N x y + c`.

When no program of `N` produces `x` from `y`, `KP N = ⊤` and the bound is trivial.
Otherwise the infimum defining `KP N` is achieved (well-ordered `ENat`) by a genuine
program `p`; its translate `translate p` produces the same output on `M` and is no
longer than `|p| + c`, so it bounds `KP M`. This matches the semimeasure constant
`c` from `ProgramSimulation.aprioriMeasure_dominates`. -/
theorem ProgramSimulation.KP_le {M N : Map} {c : ℕ} (h : ProgramSimulation M N c)
    (x y : BitString) : KP M x y ≤ KP N x y + (c : ENat) := by
  rcases Set.eq_empty_or_nonempty (candidateLengths N x y) with he | hne
  · -- No `N`-program produces `x`: `KP N = ⊤`, so the right side is `⊤`.
    have htop : KP N x y = ⊤ := by rw [KP_eq_condK, condK, he, sInf_empty]
    rw [htop]; exact le_top
  · -- The infimum is achieved by a genuine `N`-program `p`.
    have hmem : KP N x y ∈ candidateLengths N x y := by
      rw [KP_eq_condK, condK]; exact csInf_mem hne
    obtain ⟨p, hp, hlen⟩ := hmem
    have h1 : KP M x y ≤ (programLength (h.translate p) : ENat) :=
      KP_le_programLength_of_produces (h.simulates p y x hp)
    have h2 : (programLength (h.translate p) : ENat)
        ≤ (programLength p : ENat) + (c : ENat) := by
      exact_mod_cast h.length_le p
    calc
      KP M x y ≤ (programLength (h.translate p) : ENat) := h1
      _ ≤ (programLength p : ENat) + (c : ENat) := h2
      _ = KP N x y + (c : ENat) := by rw [hlen]

/-- **Consistency of the constant.** The same simulation yields the multiplicative
complexity-weight bound `2^{-c} · 2^{-KP_N} ≤ 2^{-KP_M}`, the `2^{-KP}` shadow of
`ProgramSimulation.KP_le`. The constant `c` is identical to the semimeasure-side
constant of `ProgramSimulation.aprioriMeasure_dominates`, so the two universality
strands share one overhead. -/
theorem ProgramSimulation.complexityWeight_le {M N : Map} {c : ℕ}
    (h : ProgramSimulation M N c) (x y : BitString) :
    (2 : ℝ≥0∞)⁻¹ ^ c * complexityWeight (KP N x y) ≤ complexityWeight (KP M x y) := by
  have hle := complexityWeight_le_of_le (h.KP_le x y)
  rw [complexityWeight_add_nat] at hle
  rwa [mul_comm] at hle

/-! ### Simulation-universal machines -/

/-- A map `U` is **simulation-universal** if it is a prefix decompressor and it
program-simulates every prefix decompressor `M` with some constant overhead. This
is the constructive universality hypothesis: it provides actual translations, not
merely an abstract `KP` bound. Existence of such a `U` is **not** claimed. -/
def IsSimulationUniversal (U : Map) : Prop :=
  IsPrefixDecompressor U ∧
    ∀ M, IsPrefixDecompressor M → ∃ c : ℕ, Nonempty (ProgramSimulation U M c)

/-- **Simulation-universality ⇒ abstract optimality.** A machine that simulates
every prefix decompressor is optimal for conditional prefix complexity: each
simulation's `KP_le` supplies the required additive invariance bound. This is the
headline bridge from the constructive notion to `IsOptimalPrefixConditional`. -/
theorem IsSimulationUniversal.isOptimalPrefixConditional {U : Map}
    (hU : IsSimulationUniversal U) : IsOptimalPrefixConditional U := by
  refine ⟨hU.1, fun M hM => ?_⟩
  obtain ⟨c, ⟨sim⟩⟩ := hU.2 M hM
  exact ⟨c, fun x y => sim.KP_le x y⟩

/-- **Simulation-universality ⇒ semimeasure domination.** The companion to
`isOptimalPrefixConditional` on the a priori semimeasure side: `U`'s semimeasure
multiplicatively dominates that of any prefix decompressor `M`, with the same
overhead constant. -/
theorem IsSimulationUniversal.aprioriMeasure_dominates {U : Map}
    (hU : IsSimulationUniversal U) {M : Map} (hM : IsPrefixDecompressor M) :
    ∃ c : ℕ, Dominates (aprioriMeasure U) (aprioriMeasure M) ((2 : ℝ≥0∞)⁻¹ ^ c) := by
  obtain ⟨c, ⟨sim⟩⟩ := hU.2 M hM
  exact ⟨c, sim.aprioriMeasure_dominates⟩

end Kolmogorov
