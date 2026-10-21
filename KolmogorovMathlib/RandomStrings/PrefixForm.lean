/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.General
import KolmogorovMathlib.RandomStrings.Expspace
import KolmogorovMathlib.Prefix.EntropyFunctions

/-!
# Allender–Friedman–Gasarch, prefix-complexity form: `DEC ∩ ⋂_U P^{R_{K_U}} ⊆ EXPSPACE`

`dec_inter_polyTime_RA_subset_EXPSPACE` (below) states Theorem 10 of Allender, Friedman and
Gasarch (deterministic case) with the hypothesis "for every universal a priori complexity `K`"
(every universal entropy function,
`AprioriComplexity` with `K.Universal`).  The paper states it for the prefix complexities `K_U` of
the universal prefix machines `U`.  Every `K_U` is a universal entropy function, so the paper's
hypothesis is weaker (it is required for fewer oracles), and the paper's theorem is stronger.

This module proves the paper's form, using the `KolmogorovMathlib` library:

* `dec_inter_polyTime_RA_subset_EXPSPACE`: the a-priori-complexity form, the special case of
  Theorem `general` for the family of all clocked machines (`Family.turing`) and `EXPSPACE`.
* `prefixApriori U hU`: the prefix complexity `KPPlain U` of an optimal prefix decompressor `U`
  as an `AprioriComplexity` (`Kolmogorov.isEntropyFun_KPPlain_toNat`).
* `prefixRandom U = {x | |x| ≤ K_U(x)}`, the `K_U`-random strings.
* `dec_inter_polyTime_prefixRandom_subset_EXPSPACE`: if `A` is decidable and, for every optimal
  prefix decompressor `U`, `A ∈ P^{prefixRandom U}`, then `A ∈ EXPSPACE`.  The proof runs the
  construction (`Built A K`) with `K = K_{U₀}` for one fixed optimal prefix decompressor `U₀`.
  The construction works for an arbitrary `K : AprioriComplexity` and only needs a machine
  deciding `A` with the oracle `R_H` for `H = Hmin K F = min (K + 5, F + 3)`, where `F` is the
  entropy function it builds.  Claim 1 of the paper (the exact realisation of
  `min (K_U + 5, F + 3)` by a universal prefix machine) is
  `Kolmogorov.exists_isOptimalPrefixConditional_min_toNat`.
-/

namespace Kolmogorov.RandomStrings

open Kolmogorov

/-- **Allender–Friedman–Gasarch, Theorem 10 (deterministic case), a-priori-complexity form.**
The special case of Theorem `general` for the family of all clocked machines (`Family.turing`)
and the class `EXPSPACE`: `EXPSPACE` is closed under finite modifications
(`EXPSPACE_of_eventually_eq`) and contains the game languages (`gameValue_mem_EXPSPACE`); a
polynomial-time oracle machine is a clocked machine (`exists_clocked_of_polyTime`). -/
theorem dec_inter_polyTime_RA_subset_EXPSPACE (A : Set BitString)
    (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ PolyTimeOracle (RA K)) :
    A ∈ EXPSPACE := by
  let _ := Family.turing
  refine general EXPSPACE (fun A B Z hB h => EXPSPACE_of_eventually_eq A B hB Z h)
    (fun c e _ _ T m Y => gameValue_mem_EXPSPACE c e T m Y) A hA fun K hKU => ?_
  obtain ⟨c, e, hce⟩ := exists_clocked_of_polyTime _ _ (hK K hKU)
  exact ⟨c, e, fun _ => trivial, hce⟩

/-- The prefix complexity `K_U = KPPlain U` of an optimal prefix decompressor `U`, as an
a priori complexity function (`ℕ`-valued through `ENat.toNat`; `KPPlain U x ≠ ⊤`). -/
noncomputable def prefixApriori (U : Map) (hU : IsOptimalPrefixConditional U) : AprioriComplexity :=
  ⟨fun x => (KPPlain U x).toNat, KPPlain_toNat_kraft hU, REPred_KPPlain_toNat_le hU⟩

/-- `R_{K_U} = {x | |x| ≤ K_U(x)}`: the strings random for the prefix complexity of `U`. -/
def prefixRandom (U : Map) : Set BitString := {x | (x.length : ℕ∞) ≤ KPPlain U x}

/-- The set of prefix-random strings for an optimal prefix decompressor `U` coincides with the set
of strings that are random for its prefix complexity viewed as an a priori complexity function. -/
theorem prefixRandom_eq_RA (U : Map) (hU : IsOptimalPrefixConditional U) :
    prefixRandom U = RA (prefixApriori U hU) := by
  ext x
  change (x.length : ℕ∞) ≤ KPPlain U x ↔ x.length ≤ (KPPlain U x).toNat
  obtain ⟨k, hk⟩ :=
    ENat.ne_top_iff_exists.1 (KPPlain_ne_top_of_isOptimalPrefixConditional hU x)
  rw [← hk, ENat.toNat_natCast, Nat.cast_le]

/-- **Allender–Friedman–Gasarch, Theorem 10 (deterministic case), prefix form.**  If `A` is
decidable and, for every optimal prefix decompressor `U`, `A` is decided in polynomial time by an
oracle machine with the oracle `R_{K_U} = {x | |x| ≤ K_U(x)}`, then `A ∈ EXPSPACE`. -/
theorem dec_inter_polyTime_prefixRandom_subset_EXPSPACE (A : Set BitString)
    (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ U : Map, IsOptimalPrefixConditional U → A ∈ PolyTimeOracle (prefixRandom U)) :
    A ∈ EXPSPACE := by
  let _ := Family.turing
  by_contra hnot
  obtain ⟨U₀, hU₀⟩ := exists_isOptimalPrefixConditional
  obtain ⟨b⟩ := exists_built A hA
    (witnessesExist_of_class EXPSPACE (fun A B Z hB h => EXPSPACE_of_eventually_eq A B hB Z h)
      (fun c e _ _ T m Y => gameValue_mem_EXPSPACE c e T m Y) A hnot) (prefixApriori U₀ hU₀)
  obtain ⟨U', hU', hmin⟩ := exists_isOptimalPrefixConditional_min_toNat hU₀ b.entropy
  have hRA : prefixRandom U' = RH (Hmin (prefixApriori U₀ hU₀) b.F) := by
    rw [prefixRandom_eq_RA U' hU']
    ext x
    change x.length ≤ (KPPlain U' x).toNat ↔
      x.length ≤ min ((KPPlain U₀ x).toNat + 5) (b.F x + 3)
    rw [hmin]
  obtain ⟨c, e, hce⟩ := exists_clocked_of_polyTime _ _ (hK U' hU')
  rw [hRA] at hce
  exact b.foils c e (fun _ => trivial) hce

end Kolmogorov.RandomStrings
