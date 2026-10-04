/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod

/-!
# Linear network coding over a two-element field is not enough

The request of SUV Figure 46 sends a two-bit input string to six output nodes through four
intermediate nodes of capacity one, each output node reading a different pair of intermediate
nodes.  A linear coding scheme over `𝔽₂` therefore amounts to four linear functionals
`φ₀, …, φ₃ : 𝔽₂² → 𝔽₂`, one per intermediate node, and an output node reading the nodes `i`
and `j` can decode exactly when `x ↦ (φ i x, φ j x)` is injective.  There are only three
nonzero functionals on `𝔽₂²`, so two of the four coincide and the corresponding output cannot
decode.

The statement below is this combinatorial form of the problem; the graph of Figure 46 enters
only through the six pairs of intermediate nodes, so it does not appear in the formalisation.

SUV Problem 328, pp. 386–387.
-/

namespace Kolmogorov

/-- A function from the four-element space `𝔽₂²` to the two-element field is never injective. -/
private theorem not_injective_toZMod2 (ψ : (Fin 2 → ZMod 2) → ZMod 2) :
    ¬ Function.Injective ψ := by
  intro h
  have := Fintype.card_le_of_injective ψ h
  simp [ZMod.card] at this

/-- A vector of `𝔽₂²` is the combination of the two unit vectors with its coordinates. -/
private theorem eq_smul_single_add_smul_single (x : Fin 2 → ZMod 2) :
    x = x 0 • (Pi.single 0 1 : Fin 2 → ZMod 2) + x 1 • (Pi.single 1 1 : Fin 2 → ZMod 2) := by
  ext k
  fin_cases k <;> simp

/-- Two linear functionals on `𝔽₂²` agreeing on the two unit vectors are equal. -/
private theorem linearMap_ext_of_single {ψ χ : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (h0 : ψ (Pi.single 0 1) = χ (Pi.single 0 1))
    (h1 : ψ (Pi.single 1 1) = χ (Pi.single 1 1)) : ψ = χ := by
  refine LinearMap.ext fun x => ?_
  rw [eq_smul_single_add_smul_single x, map_add, map_add, map_smul, map_smul, map_smul,
    map_smul, h0, h1]

/-- No four `𝔽₂`-linear functionals on `𝔽₂²` have all six of their pairs injective: for some
pair of distinct indices `i, j` the map `x ↦ (φ i x, φ j x)` is not injective, so the output
node of SUV Figure 46 that reads the nodes `i` and `j` cannot restore the input.

The book's hint prints "three non-linear functionals" where it means the three nonzero linear
functionals on a two-dimensional space.

SUV Problem 328, pp. 386–387. -/
theorem exists_pair_not_injective_of_binaryFunctionals
    (φ : Fin 4 → ((Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2)) :
    ∃ i j : Fin 4, i ≠ j ∧ ¬ Function.Injective fun x => (φ i x, φ j x) := by
  set g : Fin 4 → ZMod 2 × ZMod 2 := fun i => (φ i (Pi.single 0 1), φ i (Pi.single 1 1)) with hg
  by_cases hinj : Function.Injective g
  · -- all four value pairs are distinct, so one of them is `(0, 0)` and that functional vanishes
    have hbij : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, by simp [ZMod.card]⟩
    obtain ⟨i, hi⟩ := hbij.2 (0, 0)
    obtain ⟨j, hj⟩ := exists_ne i
    refine ⟨i, j, hj.symm, fun h => not_injective_toZMod2 (φ j) fun x y hxy => h ?_⟩
    have hzero : φ i = 0 :=
      linearMap_ext_of_single (by simpa [hg] using congrArg Prod.fst hi)
        (by simpa [hg] using congrArg Prod.snd hi)
    simp [hzero, hxy]
  · -- two value pairs coincide, so two of the functionals coincide
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    refine ⟨i, j, hne, fun h => not_injective_toZMod2 (φ i) fun x y hxy => h ?_⟩
    have heq : φ i = φ j :=
      linearMap_ext_of_single (by simpa [hg] using congrArg Prod.fst hij)
        (by simpa [hg] using congrArg Prod.snd hij)
    simp [← heq, hxy]

end Kolmogorov
