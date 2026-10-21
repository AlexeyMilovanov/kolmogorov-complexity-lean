/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.General
import KolmogorovMathlib.RandomStrings.TT
import KolmogorovMathlib.RandomStrings.SubAdaptive
import KolmogorovMathlib.RandomStrings.Pspace

/-!
# Instances of the general theorem

* `Family.tt`, `Family.sa`, `Family.strictSA`, `Family.saTree`: the families of non-adaptive,
  sub-adaptive and strictly sub-adaptive clocked machines (membership on an input is decidable).
* `dec_inter_polyTimeTT_RA_subset_PSPACE`: `DEC ∩ ⋂_H P^{R_H}_tt ⊆ PSPACE`
  (the tt-case of the paper).
* `polyTimeTT_subset_polyTimeSA`: tt-reductions are sub-adaptive.
* `dec_inter_expTime_RA_subset`: the general theorem for the exponentially clocked family
  `Family.turingE` (clock `clkE`) and `EXP^{R_K}` (`ExpTimeOracle`): the interface for
  exponential-time reductions.
-/

namespace Kolmogorov.RandomStrings

/-- Non-adaptive clocked machines. -/
@[instance_reducible] def Family.tt : Family :=
  ⟨NonAdaptiveOn, nonAdaptiveB, nonAdaptiveB_iff, nonAdaptiveB_computable, clock, clock_computable⟩

/-- Sub-adaptive clocked machines (two-stage notion of the paper, `SubAdaptiveOn`): for some `k`,
the set of the first `k` strings asked within the clock does not depend on the oracle, and asks
made after at least `k` earlier asks at distinct nodes of the reduction tree (distinct answer
histories, under any oracles) carry distinct strings.  The stage boundary is the `k`-th ask, not
a time. -/
@[instance_reducible] def Family.sa : Family :=
  ⟨SubAdaptiveOn, subAdaptiveB, subAdaptiveB_iff, subAdaptiveB_computable, clock,
    clock_computable⟩

/-- Strictly sub-adaptive clocked machines (`StrictlySubAdaptiveOn`): asks at distinct nodes of the
reduction tree (distinct answer histories) carry distinct strings. -/
@[instance_reducible] def Family.strictSA : Family :=
  ⟨StrictlySubAdaptiveOn, strictlySubAdaptiveB, strictlySubAdaptiveB_iff,
    strictlySubAdaptiveB_computable, clock, clock_computable⟩

/-- Boundary-free two-stage sub-adaptivity (`SubAdaptiveTree`): every query is asked under every
oracle or at a single node of the reduction tree.  Implied by `Family.tt`, `Family.sa` and
`Family.strictSA` (`polyTimeTT_subset_polyTimeSATree`, `polyTimeSA_subset_polyTimeSATree`,
`polyTimeStrictSA_subset_polyTimeSATree`); the family for the planned `EXP` upper bound. -/
@[instance_reducible] def Family.saTree : Family :=
  ⟨SubAdaptiveTreeOn, subAdaptiveTreeB, subAdaptiveTreeB_iff, subAdaptiveTreeB_computable,
    clock, clock_computable⟩

/-- Truth-table reductions are sub-adaptive. -/
theorem polyTimeTT_subset_polyTimeSA (B : Set BitString) : PolyTimeTT B ⊆ PolyTimeSA B :=
  fun _ ⟨M, p, hp, hna, hA⟩ => mem_polyTimeSA_of_nonAdaptive M p hp hna hA

/-- **The tt-case of the paper:** a decidable set polynomial-time truth-table reducible to `R_H`
for every universal entropy function `H` lies in `PSPACE`. -/
theorem dec_inter_polyTimeTT_RA_subset_PSPACE (A : Set BitString)
    (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ PolyTimeTT (RA K)) :
    A ∈ PSPACE := by
  let _ := Family.tt
  exact general PSPACE PSPACE_of_eventually_eq'
    (gameValue_mem_PSPACE_of_family NonAdaptiveOn fun _ _ _ h => card_querySet_le_of_nonAdaptive h)
    A hA fun K hKU => exists_clocked_tt _ _ (hK K hKU)

/-- **The general theorem for exponential-time reductions** (the family `Family.turingE` of all
machines with the exponential clock `clkE e n = 2 ^ (n ^ e + e)`): a decidable set that is in
`EXP^{R_K}` for every universal `K` lies in every class `𝓒` that is closed under finite
modifications and contains the game languages of the `clkE`-clocked machines. -/
theorem dec_inter_expTime_RA_subset (𝓒 : Set (Set BitString))
    (hclosed : ∀ (A B : Set BitString) (Z : Finset BitString), B ∈ 𝓒 →
      (∀ x, x ∉ Z → (x ∈ A ↔ x ∈ B)) → A ∈ 𝓒)
    (hgame : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      {x : BitString | val (gameOfT c (clkE e x.length) x T.fn ((2 : ℝ)⁻¹ ^ m)
        (querySet c.toOTM x (clkE e x.length) \ Y)) = true} ∈ 𝓒)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ ExpTimeOracle (RA K)) :
    A ∈ 𝓒 := by
  let _ := Family.turingE
  refine general 𝓒 hclosed (fun c e _ _ T m Y => hgame c e T m Y) A hA fun K hKU => ?_
  obtain ⟨c, e, hce⟩ := exists_clockedE_of_expTime _ _ (hK K hKU)
  exact ⟨c, e, fun _ => trivial, hce⟩

end Kolmogorov.RandomStrings
