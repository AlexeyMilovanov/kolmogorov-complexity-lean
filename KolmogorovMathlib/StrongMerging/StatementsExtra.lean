/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Computability.Partrec
import Mathlib.Order.Filter.AtTopBot.Defs
import KolmogorovMathlib.StrongMerging.Upper.Profiles
import KolmogorovMathlib.StrongMerging.ExtraDefs
import KolmogorovMathlib.StrongMerging.Upper.Partition
import KolmogorovMathlib.StrongMerging.Upper.Envelope
import KolmogorovMathlib.StrongMerging.Upper.Corollaries

/-!
# Merging strong sufficient statistics: the remaining upper statements

The frozen statements of the non-optional positive results of the strong-merging note
`sublinear-merging.tex` that are not in `StrongMerging.Statements`, over the shared interface of
`StrongMerging.Basic`, the model-level notation `setMutualInfo` (`I(A : B)`) and `overlapMass`
(`t`) of `StrongMerging.Coding.Information`, and the profiles and envelopes of
`StrongMerging.Upper.Profiles` (node M06).

* **Uniform selectors.**  `IsBoundedTotalWitness e p` is the blueprint's class `𝒯_e`: `p` halts
  under the canonical total interpreter `universalDecompressor` on every condition and
  `|p| ≤ e`.  `IsExactPartitionSelector q Q`: the program `q` halts on every input `z` with the
  canonical code of the finite set `Q z ∋ z`, and `q⁻¹(q(z)) = q(z)`.  `IsWitnessedInstance` is
  a qualifying instance: `n ≥ 2`, `e ≤ n`, `|x| = n`, the witnesses output the canonical codes
  of `A` and `B` on `x`, and `A, B ∋ x` are `e`-sufficient.
* **H08** (`cor:partition`): `exists_partition_selector_tradeoff` (a fixed computable rule) and
  `exists_partition_selector_sqrt` (the square-root rule).
* **T06** (`thm:extractability-envelope`): `exists_extractabilityEnvelope_selector`, with the
  envelope `extractabilityEnvelope` (`Φ`) of `StrongMerging.Upper.Profiles`, which is built from
  the ordinary profile `ordinaryCommonProfile` (`𝓔_p`, node M06).
* **T07** (`eq:mutual-information-refinement`): `exists_mutualInfo_selector` and its
  real-tolerance instance form `exists_mutualInfo_merger`, with the scale `mutualInfoEnvelope`
  (`H + √(H max {0, I})`) of `StrongMerging.Upper.Profiles`.
* **Q03** (`UpperTwoSidedMinimality`): `max_setTotalC_le_of_strongRobustMin`.
* **Q04** (`UpperSublinearCorollaries`): `SublinearAbove`, `exists_sublinear_merger_seq`,
  `enlargedWindow_sublinear` and `setTotalC_sublinear_of_strongRobustMin`.

As in `StrongMerging.Statements`, every statement is relative to an arbitrary optimal plain
machine `V` and to `CT` at `universalDecompressor`, and every constant is an explicit
existential quantified after `V` and before all witnesses and instance data.  In
`exists_partition_selector_tradeoff` the tradeoff constant `c` is quantified before the rule `ρ`
and only the program-length constant `c_ρ` after it.

Q03 and Q04 are proved in `StrongMerging.Upper.Corollaries` from the proved
`exists_sqrt_merger` and `setTotalC_le_of_strongRobustMin` of `StrongMerging.Statements`.  The
square-root form of H08 is derived below from its rule form, and both forms of T07 from T06,
with the pointwise transfers of `StrongMerging.Upper.Corollaries`; the rule form of H08 is proved
in `StrongMerging.Upper.Partition` and T06 in `StrongMerging.Upper.Envelope`.
-/

namespace Kolmogorov.StrongMerging

open Filter

/-! ### H08: the uniform partition version -/

/-- **The uniform partition version with a fixed rule.**  For an optimal plain machine `V` there
is a constant `c` such that for every fixed computable rule `ρ(n, e)` there is a constant `c_ρ`
with the following property.  For every integer `e ≥ 0` and all total witnesses `p_A, p_B` of
length at most `e` there is one total program `q` of length at most `c_ρ (e + 1)`, chosen before
every input, which is an exact partition selector (every `q(z)` is a finite set containing `z`
and `q⁻¹(q(z)) = q(z)` for every binary string `z`), and such that at every qualifying instance
(`n ≥ max 2 e`, `x ∈ {0,1}ⁿ`, `A = p_A(x)` and `B = p_B(x)` finite sets containing `x` and
`e`-sufficient) the cell `D = q(x)` satisfies the tradeoff bounds (`TradeoffBounds`) of
`prop:tradeoff` with `H = e + ⌈log₂ (n + 2)⌉` and the clipped exponent
`R = min n (max 1 (ρ n e))`.  Its point strength `CT(D | x) ≤ |q| ≤ c_ρ (e + 1)` follows from
the program.  As in `exists_merger_tradeoff`, only the program-length constant depends on the
rule.

`sublinear-merging.tex`, Corollary `cor:partition` (blueprint target H08,
`UpperHierarchyPartition`). -/
theorem exists_partition_selector_tradeoff (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ ρ : ℕ → ℕ → ℕ, Computable₂ ρ → ∃ cρ : ℕ,
      ∀ (e : ℕ) (pA pB : BitString), IsBoundedTotalWitness e pA → IsBoundedTotalWitness e pB →
        ∃ (q : BitString) (Q : BitString → Finset BitString), IsExactPartitionSelector q Q ∧
          q.length ≤ cρ * (e + 1) ∧
          ∀ (n : ℕ) (x : BitString) (A B : Finset BitString),
            IsWitnessedInstance V n e pA pB x A B →
              TradeoffBounds V n e (min n (max 1 (ρ n e))) c x A B (Q x) :=
  Upper.exists_partition_selector_tradeoff' V hV

/-- **The uniform partition version at the square-root rule.**  For an optimal plain machine `V`
there is a constant `c` such that for every integer `e ≥ 0` and all total witnesses `p_A, p_B` of
length at most `e` there is one total program `q` of length at most `c (e + 1)` which is an exact
partition selector, and such that at every qualifying instance, with `S = √(n H)` and
`H = e + ⌈log₂ (n + 2)⌉` (`rootScale n e`), the cell `D = q(x)` satisfies the square-root bounds
of `thm:main`: `C(D) + log₂ |D| ≤ C(x) + c S`, `CT(D | A), CT(D | B) ≤ c S` and
`log₂ |D| ≥ log₂ |A| + log₂ |B| - log₂ |A ∩ B| - c S`.

`sublinear-merging.tex`, Corollary `cor:partition`, "in particular … the square-root bounds for
the displayed rule for `R`" (blueprint target H08). -/
theorem exists_partition_selector_sqrt (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (e : ℕ) (pA pB : BitString), IsBoundedTotalWitness e pA →
      IsBoundedTotalWitness e pB →
        ∃ (q : BitString) (Q : BitString → Finset BitString), IsExactPartitionSelector q Q ∧
          q.length ≤ c * (e + 1) ∧
          ∀ (n : ℕ) (x : BitString) (A B : Finset BitString),
            IsWitnessedInstance V n e pA pB x A B →
              setC V (Q x) + Real.logb 2 (Q x).card ≤ plainC V x + c * rootScale n e ∧
              setTotalC (Q x) A ≤ c * rootScale n e ∧ setTotalC (Q x) B ≤ c * rootScale n e ∧
              Real.logb 2 A.card + Real.logb 2 B.card - Real.logb 2 (A ∩ B).card -
                c * rootScale n e ≤ Real.logb 2 (Q x).card := by
  obtain ⟨c, h⟩ := exists_partition_selector_tradeoff V hV
  obtain ⟨cρ, h⟩ := h Upper.sqrtRule Upper.sqrtRule_computable
  refine ⟨4 * c + cρ, fun e pA pB hA hB => ?_⟩
  obtain ⟨q, Q, hQ, hlen, hb⟩ := h e pA pB hA hB
  exact ⟨q, Q, hQ, hlen.trans (Nat.mul_le_mul_right _ (Nat.le_add_left cρ (4 * c))),
    fun n x A B hI => Upper.sqrtBounds_of_tradeoffBounds hI.1 hI.2.1 (Nat.le_add_right _ _)
      (hb n x A B hI)⟩

/-! ### T06: the extractability envelope -/

/-- **An envelope over ordinary common factors.**  For an optimal plain machine `V` there are
constants `c, c_pt` such that for every integer `e ≥ 0` and all total witnesses `p_A, p_B` of
length at most `e` there is one total program `q`, depending only on the witnesses and `e`, of
length at most `c_pt (e + 1)`, which is an exact partition selector (outputs contain their
inputs and `q⁻¹(q(z)) = q(z)` for every binary string `z`), such that at every qualifying
instance (`n ≥ 2`, `e ≤ n`, `x ∈ {0,1}ⁿ`, valid containing `e`-sufficient `A = p_A(x)`,
`B = p_B(x)`) the model `D = q(x)` satisfies, with `k = C(x)`,
`t = log₂ |A| + log₂ |B| - log₂ |A ∩ B|` (`overlapMass`) and `Φ = extractabilityEnvelope n e A B`:
`C(D) + log₂ |D| - k ≤ c Φ`, `CT(D | A), CT(D | B) ≤ c Φ` and `t - log₂ |D| ≤ c Φ`.  No common
factor, extraction program, profile value or choice of `r` is supplied to `q`.

`sublinear-merging.tex`, Theorem `thm:extractability-envelope` (blueprint target T06,
`UpperExtractabilityEnvelope`). -/
theorem exists_extractabilityEnvelope_selector (V : Map) (hV : isOptimalConditional V) :
    ∃ c cpt : ℕ, ∀ (e : ℕ) (pA pB : BitString), IsBoundedTotalWitness e pA →
      IsBoundedTotalWitness e pB →
        ∃ (q : BitString) (Q : BitString → Finset BitString), IsExactPartitionSelector q Q ∧
          q.length ≤ cpt * (e + 1) ∧
          ∀ (n : ℕ) (x : BitString) (A B : Finset BitString),
            IsWitnessedInstance V n e pA pB x A B →
              modelScore V (Q x) x ≤ c * extractabilityEnvelope V n e A B ∧
              setTotalC (Q x) A ≤ c * extractabilityEnvelope V n e A B ∧
              setTotalC (Q x) B ≤ c * extractabilityEnvelope V n e A B ∧
              overlapMass A B - Real.logb 2 (Q x).card ≤
                c * extractabilityEnvelope V n e A B :=
  Upper.exists_extractabilityEnvelope_selector' V hV

/-! ### T07: mutual-information merging -/

/-- **Mutual-information merging by the uniform selector.**  For an optimal plain machine `V`
there are constants `c, c_pt` such that for every integer `e ≥ 0` and all total witnesses
`p_A, p_B` of length at most `e` there is one total program `q` of length at most `c_pt (e + 1)`,
an exact partition selector, such that at every qualifying instance the model `D = q(x)`
satisfies `C(D) + log₂ |D| - C(x) ≤ c M`, `CT(D | A), CT(D | B) ≤ c M` and
`t - log₂ |D| ≤ c M`, where `M = H + √(H max {0, I(A : B)})` (`mutualInfoEnvelope n e A B`) and
`t = log₂ |A| + log₂ |B| - log₂ |A ∩ B|`.  No complexity value is supplied to `q`.

`sublinear-merging.tex`, section `sec:extractability-envelope`, the choice `r = 0` in
`thm:extractability-envelope` giving `eq:mutual-information-refinement` (blueprint target T07,
`UpperMutualInformationMerging`). -/
theorem exists_mutualInfo_selector (V : Map) (hV : isOptimalConditional V) :
    ∃ c cpt : ℕ, ∀ (e : ℕ) (pA pB : BitString), IsBoundedTotalWitness e pA →
      IsBoundedTotalWitness e pB →
        ∃ (q : BitString) (Q : BitString → Finset BitString), IsExactPartitionSelector q Q ∧
          q.length ≤ cpt * (e + 1) ∧
          ∀ (n : ℕ) (x : BitString) (A B : Finset BitString),
            IsWitnessedInstance V n e pA pB x A B →
              modelScore V (Q x) x ≤ c * mutualInfoEnvelope V n e A B ∧
              setTotalC (Q x) A ≤ c * mutualInfoEnvelope V n e A B ∧
              setTotalC (Q x) B ≤ c * mutualInfoEnvelope V n e A B ∧
              overlapMass A B - Real.logb 2 (Q x).card ≤ c * mutualInfoEnvelope V n e A B := by
  obtain ⟨c, cpt, h⟩ := exists_extractabilityEnvelope_selector V hV
  refine ⟨c, cpt, fun e pA pB hA hB => ?_⟩
  obtain ⟨q, Q, hQ, hlen, hb⟩ := h e pA pB hA hB
  exact ⟨q, Q, hQ, hlen, fun n x A B hI =>
    Upper.mutualInfoBounds_of_extractabilityBounds (hb n x A B hI)⟩

/-- **Mutual-information merging at a real tolerance.**  For an optimal plain machine `V` there
is a constant `c` with the following property.  Under the hypotheses of `exists_sqrt_merger`
(`n ≥ 2`, `0 ≤ ε ≤ n`, `A, B` `ε`-strong, `ε`-sufficient statistics of `x ∈ {0,1}ⁿ`), with
`e = ⌈ε⌉` and `H = e + ⌈log₂ (n + 2)⌉`, some finite model `D ∋ x` has point strength
`CT(D | x) ≤ c (e + 1)` and score, endpoint and mass errors
`C(D) + log₂ |D| - C(x)`, `CT(D | A)`, `CT(D | B)`, `t - log₂ |D|` all at most
`c (H + √(H max {0, I(A : B)}))` (`mutualInfoEnvelope n e A B`).

`sublinear-merging.tex`, `eq:mutual-information-refinement` under the hypotheses and conventions
of `thm:main` (section `sec:extractability-envelope`, blueprint target T07). -/
theorem exists_mutualInfo_merger (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n : ℕ) (ε : ℝ) (x : BitString) (A B : Finset BitString),
      IsMergingInstance V n ε x A B → ∃ D : Finset BitString, x ∈ D ∧
        pointTotalC D x ≤ c * (⌈ε⌉₊ + 1) ∧
        modelScore V D x ≤ c * mutualInfoEnvelope V n ⌈ε⌉₊ A B ∧
        setTotalC D A ≤ c * mutualInfoEnvelope V n ⌈ε⌉₊ A B ∧
        setTotalC D B ≤ c * mutualInfoEnvelope V n ⌈ε⌉₊ A B ∧
        overlapMass A B - Real.logb 2 D.card ≤ c * mutualInfoEnvelope V n ⌈ε⌉₊ A B := by
  obtain ⟨c, cpt, h⟩ := exists_mutualInfo_selector V hV
  refine ⟨max c cpt, fun n ε x A B hI => ?_⟩
  obtain ⟨pA, pB, hA, hB, hW⟩ := Upper.exists_witnesses_of_isMergingInstance hI
  obtain ⟨q, Q, ⟨hqT, hqP, hqM, -⟩, hqlen, hb⟩ := h ⌈ε⌉₊ pA pB hA hB
  obtain ⟨b1, b2, b3, b4⟩ := hb n x A B hW
  have hM : (0 : ℝ) ≤ mutualInfoEnvelope V n ⌈ε⌉₊ A B := by
    unfold mutualInfoEnvelope; positivity
  have hcM : (c : ℝ) * mutualInfoEnvelope V n ⌈ε⌉₊ A B ≤
      ((max c cpt : ℕ) : ℝ) * mutualInfoEnvelope V n ⌈ε⌉₊ A B :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left c cpt) hM
  have hq : (q.length : ℝ) ≤ ((max c cpt : ℕ) : ℝ) * ((⌈ε⌉₊ : ℝ) + 1) := by
    exact_mod_cast hqlen.trans (Nat.mul_le_mul_right _ (le_max_right c cpt))
  exact ⟨Q x, hqM x, (Upper.pointTotalC_le_length hqT (hqP x)).trans hq, b1.trans hcM,
    b2.trans hcM, b3.trans hcM, b4.trans hcM⟩

/-! ### Q03: two-sided enlarged-window minimality -/

/-- **Two-sided enlarged-window minimality.**  For an optimal plain machine `V` there are
constants `c_win, c_out > 0` with the following property.  Let `n ≥ 2`, let `0 ≤ e ≤ n` be an
integer, let `A, B` be `e`-strong, `e`-sufficient statistics of a string `x` of length `n`, and
put `S = √(n (e + ⌈log₂ (n + 2)⌉))`.  For all reals `δ_A, δ_B ≥ 0`, if `A` is strong-only
robustly minimal at tolerance `e + c_win S` with gap `δ_A` and `B` is so with gap `δ_B`
(`StrongRobustMin`), then `max {CT(A | B), CT(B | A)} ≤ max {δ_A, δ_B} + c_out S`.

`sublinear-merging.tex`, appendix section `bp-upper-sublinear-minimality`, paragraph
`UpperTwoSidedMinimality` (blueprint target Q03). -/
theorem max_setTotalC_le_of_strongRobustMin (V : Map) (hV : isOptimalConditional V) :
    ∃ cwin cout : ℕ, 0 < cwin ∧ 0 < cout ∧
      ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString), IsMergingInstance V n e x A B →
        ∀ δA δB : ℝ, 0 ≤ δA → 0 ≤ δB →
          StrongRobustMin V x A (e + cwin * rootScale n e) δA →
          StrongRobustMin V x B (e + cwin * rootScale n e) δB →
            max (setTotalC A B) (setTotalC B A) ≤ max δA δB + cout * rootScale n e := by
  exact Upper.max_setTotalC_le_of_strongRobustMin' V hV

/-! ### Q04: the sublinear corollaries -/

/-- **Sublinear merging along a sequence.**  For an optimal plain machine `V` there is a constant
`c` with the following property.  Let `(n_j, ε_j, x_j, A_j, B_j)` be a sequence of merging
instances (eventually `IsMergingInstance`) with lengths `n_j → ∞` and tolerances
`ε_j = o(n_j)`.  Then there are finite models `D_j`, eventually containing `x_j` with point
strength `CT(D_j | x_j) ≤ c (⌈ε_j⌉ + 1)`, whose score `C(D_j) + log₂ |D_j| - C(x_j)`, total
reduction costs `CT(D_j | A_j)`, `CT(D_j | B_j)` and mass loss `t_j - log₂ |D_j|` are all at most
`o(n_j)` (`SublinearAbove`).

`sublinear-merging.tex`, appendix section `bp-upper-sublinear-minimality`, paragraph "The
asymptotic consequence and its exact limitation" (blueprint target Q04,
`UpperSublinearCorollaries`, merger part). -/
theorem exists_sublinear_merger_seq (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n : ℕ → ℕ) (ε : ℕ → ℝ) (x : ℕ → BitString) (A B : ℕ → Finset BitString),
      Tendsto n atTop atTop →
      (∀ᶠ j in atTop, IsMergingInstance V (n j) (ε j) (x j) (A j) (B j)) →
      SublinearAbove ε n →
        ∃ D : ℕ → Finset BitString,
          (∀ᶠ j in atTop, x j ∈ D j ∧ pointTotalC (D j) (x j) ≤ c * (⌈ε j⌉₊ + 1)) ∧
          SublinearAbove (fun j => modelScore V (D j) (x j)) n ∧
          SublinearAbove (fun j => setTotalC (D j) (A j)) n ∧
          SublinearAbove (fun j => setTotalC (D j) (B j)) n ∧
          SublinearAbove (fun j => overlapMass (A j) (B j) - Real.logb 2 (D j).card) n := by
  exact Upper.exists_sublinear_merger_seq' V hV

/-- **The enlarged window is sublinear.**  For every real constant `c`, if `n_j → ∞` and
`e_j = o(n_j)`, then `e_j + c √(n_j H_j) = o(n_j)` from above, with
`H_j = e_j + ⌈log₂ (n_j + 2)⌉`; in particular `H_j / n_j → 0` and `S_j / n_j → 0`.

`sublinear-merging.tex`, appendix section `bp-upper-sublinear-minimality`, "The required
minimality window `e_n + c_win S_n` is itself sublinear" (blueprint target Q04). -/
theorem enlargedWindow_sublinear (c : ℝ) (n e : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (he : SublinearAbove (fun j => (e j : ℝ)) n) :
    SublinearAbove (fun j => (e j : ℝ) + c * rootScale (n j) (e j)) n := by
  exact Upper.enlargedWindow_sublinear' c n e hn he

/-- **Sublinear enlarged-window minimality, one- and two-sided.**  For an optimal plain machine
`V` there is a constant `c_win > 0` with the following two properties, for sequences of
merging instances `(n_j, e_j, x_j, A_j, B_j)` (eventually `IsMergingInstance` at the integer
tolerance `e_j`) with `n_j → ∞`, `e_j = o(n_j)` and `S_j = √(n_j (e_j + ⌈log₂ (n_j + 2)⌉))`.
* One-sided: if eventually `δ_j ≥ 0` and `A_j` is strong-only robustly minimal at tolerance
  `e_j + c_win S_j` with gap `δ_j` (`StrongRobustMin`), and `δ_j = o(n_j)`, then
  `CT(A_j | B_j) = o(n_j)`.
* Two-sided: if eventually `δ_{A,j}, δ_{B,j} ≥ 0` and `A_j`, `B_j` are robustly minimal at that
  tolerance with gaps `δ_{A,j}`, `δ_{B,j}`, both `o(n_j)`, then
  `max {CT(A_j | B_j), CT(B_j | A_j)} = o(n_j)`.
Neither claims a bound from minimality only up to `e + c log n`, nor a prescribed sublinear
merging rate.

`sublinear-merging.tex`, appendix section `bp-upper-sublinear-minimality`, paragraph "The
asymptotic consequence and its exact limitation" (blueprint target Q04,
`UpperSublinearCorollaries`, minimality part). -/
theorem setTotalC_sublinear_of_strongRobustMin (V : Map) (hV : isOptimalConditional V) :
    ∃ cwin : ℕ, 0 < cwin ∧
      (∀ (n e : ℕ → ℕ) (x : ℕ → BitString) (A B : ℕ → Finset BitString) (δ : ℕ → ℝ),
        Tendsto n atTop atTop →
        (∀ᶠ j in atTop, IsMergingInstance V (n j) (e j) (x j) (A j) (B j)) →
        SublinearAbove (fun j => (e j : ℝ)) n →
        (∀ᶠ j in atTop, 0 ≤ δ j) → SublinearAbove δ n →
        (∀ᶠ j in atTop,
          StrongRobustMin V (x j) (A j) (e j + cwin * rootScale (n j) (e j)) (δ j)) →
          SublinearAbove (fun j => setTotalC (A j) (B j)) n) ∧
      ∀ (n e : ℕ → ℕ) (x : ℕ → BitString) (A B : ℕ → Finset BitString) (δA δB : ℕ → ℝ),
        Tendsto n atTop atTop →
        (∀ᶠ j in atTop, IsMergingInstance V (n j) (e j) (x j) (A j) (B j)) →
        SublinearAbove (fun j => (e j : ℝ)) n →
        (∀ᶠ j in atTop, 0 ≤ δA j ∧ 0 ≤ δB j) → SublinearAbove δA n → SublinearAbove δB n →
        (∀ᶠ j in atTop,
          StrongRobustMin V (x j) (A j) (e j + cwin * rootScale (n j) (e j)) (δA j) ∧
          StrongRobustMin V (x j) (B j) (e j + cwin * rootScale (n j) (e j)) (δB j)) →
          SublinearAbove (fun j => max (setTotalC (A j) (B j)) (setTotalC (B j) (A j))) n := by
  exact Upper.setTotalC_sublinear_of_strongRobustMin' V hV

end Kolmogorov.StrongMerging
