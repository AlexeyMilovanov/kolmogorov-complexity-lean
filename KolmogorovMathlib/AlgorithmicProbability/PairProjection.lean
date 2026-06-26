/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.PairMarginal
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin
import KolmogorovMathlib.Prefix.Combinators

/-!
# The Pair-Marginal Coding Bound via a Projection Machine

This module proves the **marginal coding bound** at `k = K(x)` by reducing it to
the canonical Kraft–Chaitin coding theorem
`aprioriMeasure_le_complexityWeight_optimal` (`KraftChaitin`).

The key device is the **projection machine** `projMap U`: it runs `U` on its
program (in the empty context) and post-composes the computable first-component
decoder `decodeFirst`, which strips the self-delimiting length prefix of a
`pairCode` and returns the first component. Two facts make this work:

* `projMap U` is a *prefix decompressor* whenever `U` is: its halting domain
  coincides with that of `U` (post-composition by a total function changes no
  domain), so prefix-freeness and partial-recursiveness are inherited.
* The pair marginal is bounded by the projection machine's a priori semimeasure,
  `pairMarginal U x ≤ m_{projMap U}(x | [])`: each pair `⟨x, y⟩` produced by `U`
  decodes to first component `x`, and (because `U` is deterministic) distinct
  second components `y` correspond to distinct programs, so the pair-marginal
  double sum injects into the projection-machine sum.

Applying the coding theorem to `projMap U` gives
`m_{projMap U}(x | []) ≤ 2^{c} · 2^{-K(x)}`, whence
`pairMarginal U x · 2^{K(x)} ≤ 2^{c}`. All algebra here is `ℝ≥0∞`/exponent
manipulation; the only deep input is the Kraft–Chaitin realization isolated in
`KraftChaitin`.
-/

namespace Kolmogorov

open scoped ENNReal
open Classical

/-- **First-component decoder.** Strips the self-delimiting unary length prefix of
a `pairCode` and returns the first component: it reads the leading run of `true`s
(length `m`), drops those `m` bits plus the terminating `false`, and keeps the
next `m` bits. On `pairCode x y` this returns `x`. -/
def decodeFirst (z : BitString) : BitString :=
  (z.drop ((z.takeWhile id).length + 1)).take ((z.takeWhile id).length)

/-- **Second-component decoder.** Strips the self-delimiting unary length prefix
and the first component from a `pairCode`, returning the remaining suffix. -/
def decodeSecond (z : BitString) : BitString :=
  z.drop (((z.takeWhile id).length + 1) + (z.takeWhile id).length)

/-
The decoder recovers the first component of an encoded pair.
-/
theorem decodeFirst_pairCode (x y : BitString) : decodeFirst (pairCode x y) = x := by
  unfold pairCode decodeFirst;
  simp +decide [length_takeWhile_natCode_append]

/-- The second-component decoder recovers the second component of an encoded pair. -/
theorem decodeSecond_pairCode (x y : BitString) : decodeSecond (pairCode x y) = y := by
  unfold pairCode decodeSecond
  simp +decide [length_takeWhile_natCode_append, List.drop_append]

/-- The first-component decoder is computable. It is `take m ∘ drop (m+1)` where
`m = (z.takeWhile id).length`; each piece is primitive recursive, reusing the
list-slicing computability lemmas `primrec_list_drop` / `primrec_list_take`
(`Prefix.TwoStage`, `Core.UniversalDecompressor`) and the `takeWhile`-length
identity `takeWhile_id_length_eq_findIdx`. -/
theorem decodeFirst_computable : Computable decodeFirst := by
  have hlen : Primrec (fun z : BitString => (z.takeWhile id).length) :=
    (Primrec.list_findIdx Primrec.id (Primrec.not.comp Primrec.snd).to₂).of_eq
      (fun z => (takeWhile_id_length_eq_findIdx z).symm)
  have hdrop : Primrec (fun z : BitString => z.drop ((z.takeWhile id).length + 1)) :=
    primrec_list_drop.comp Primrec.id (Primrec.succ.comp hlen)
  exact ((primrec_list_take.comp hdrop hlen).of_eq (fun _ => rfl)).to_comp

/-- The second-component decoder is computable. -/
theorem decodeSecond_computable : Computable decodeSecond := by
  have hlen : Primrec (fun z : BitString => (z.takeWhile id).length) :=
    (Primrec.list_findIdx Primrec.id (Primrec.not.comp Primrec.snd).to₂).of_eq
      (fun z => (takeWhile_id_length_eq_findIdx z).symm)
  have hdrop : Primrec
      (fun z : BitString => z.drop (((z.takeWhile id).length + 1) + (z.takeWhile id).length)) :=
    primrec_list_drop.comp Primrec.id (Primrec.nat_add.comp (Primrec.succ.comp hlen) hlen)
  exact hdrop.to_comp

/-- The **projection machine**: run `U` on the program (empty context) and decode
the first component of its output. -/
def projMap (U : Map) : Map :=
  fun pr => (U (pr.1, [])).map decodeFirst

/-- Membership characterization of the projection machine: it produces `x` from a
program `p` exactly when `U` produces, in the empty context, some `z` whose first
component decodes to `x`. The output context `y` is ignored. -/
theorem produces_projMap_iff (U : Map) (p y x : BitString) :
    produces (projMap U) p y x ↔ ∃ z, produces U p [] z ∧ decodeFirst z = x := by
  change x ∈ Part.map decodeFirst (U (p, [])) ↔ ∃ z, produces U p [] z ∧ decodeFirst z = x
  rw [Part.mem_map_iff]

/-- The halting domain of the projection machine in any context is the halting
domain of `U` in the empty context (post-composition by a total function does not
change the domain). -/
theorem domainAt_projMap (U : Map) (y : BitString) :
    domainAt (projMap U) y = domainAt U [] := rfl

/-- **The projection machine is a prefix decompressor** whenever `U` is: it is
partial recursive (a `Part.map` of a partial-recursive function by the computable
`decodeFirst`), and its halting domain — equal to `U`'s domain in the empty
context — is prefix-free. -/
theorem projMap_isPrefixDecompressor (U : Map) (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (projMap U) := by
  refine ⟨?_, ?_⟩
  · -- Partial recursive: a `Part.map` of a partial-recursive function.
    have hf : Partrec (fun pr : BitString × BitString => U (pr.1, [])) :=
      hU.isDecompressor.comp (Computable.fst.pair (Computable.const []))
    have hg : Computable₂ (fun (_ : BitString × BitString) (z : BitString) => decodeFirst z) :=
      (decodeFirst_computable.comp Computable.snd).to₂
    exact (hf.map hg).of_eq (fun pr => rfl)
  · -- Prefix machine: the domain coincides with `U`'s domain in the empty context.
    intro y
    rw [domainAt_projMap]
    exact hU.isPrefixMachine []

/-- **The pair marginal is bounded by the projection machine's a priori
semimeasure.** Every pair `⟨x, y⟩` that `U` outputs decodes (via `decodeFirst`) to
first component `x`; since `U` is deterministic, distinct `y` arise from distinct
programs, so the pair-marginal double sum over `(y, p)` injects into the
projection-machine sum over `p`. -/
theorem pairMarginal_le_aprioriMeasure_projMap (U : Map) (x : BitString) :
    pairMarginal U x ≤ aprioriMeasure (projMap U) x [] := by
  rw [pairMarginal_def]
  simp only [aprioriMeasure]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum (fun p => ?_)
  by_cases hp : ∃ y, produces U p [] (pairCode x y)
  · -- Determinism of `U` pins a unique second component `y₀`.
    obtain ⟨y₀, hy₀⟩ := hp
    have huniq : ∀ y, produces U p [] (pairCode x y) → y = y₀ := by
      intro y hy
      have hmem : pairCode x y = pairCode x y₀ := Part.mem_unique hy hy₀
      exact (Prod.ext_iff.mp (@pairCode_injective (x, y) (x, y₀) hmem)).2
    have hsum : (∑' y, if produces U p [] (pairCode x y) then progWeight p else 0)
        = progWeight p := by
      rw [tsum_eq_single y₀ (fun y hy => by rw [if_neg (fun h => hy (huniq y h))])]
      rw [if_pos hy₀]
    have hproj : produces (projMap U) p [] x :=
      (produces_projMap_iff U p [] x).mpr ⟨pairCode x y₀, hy₀, decodeFirst_pairCode x y₀⟩
    rw [hsum, if_pos hproj]
  · -- No second component is produced: the inner sum is zero.
    push Not at hp
    rw [ENNReal.tsum_eq_zero.mpr (fun y => if_neg (hp y))]
    exact zero_le

/-- **Marginal coding bound at `k = K(x)`.** The scaled pair-output marginal is
bounded by a uniform constant: `pairMarginal U x · 2^{k} ≤ 2^{c₂}` at `k = K(x)`.

This is the Kraft–Chaitin coding theorem
(`aprioriMeasure_le_complexityWeight_optimal`) applied to the projection machine
`projMap U`, whose a priori semimeasure dominates the pair marginal
(`pairMarginal_le_aprioriMeasure_projMap`). At `k = K(x)` the optimal complexity
weight is `2^{-k}`, giving `pairMarginal U x ≤ 2^{c₂} · 2^{-k}`. -/
theorem pairMarginal_coding_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c₂ : ℕ, ∀ (x : BitString) (k : ℕ), (k : ENat) = KP U x [] →
      pairMarginal U x * (2 : ℝ≥0∞) ^ k ≤ (2 : ℝ≥0∞) ^ c₂ := by
  obtain ⟨c, hc⟩ :=
    aprioriMeasure_le_complexityWeight_optimal hU
      (projMap_isPrefixDecompressor U hU.isPrefixDecompressor)
  refine ⟨c, fun x k hk => ?_⟩
  have h1 : (2 : ℝ≥0∞)⁻¹ ^ c * aprioriMeasure (projMap U) x [] ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
    have := hc x []
    rwa [← hk, complexityWeight_coe] at this
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ c * pairMarginal U x ≤ (2 : ℝ≥0∞)⁻¹ ^ k :=
    le_trans (by gcongr; exact pairMarginal_le_aprioriMeasure_projMap U x) h1
  -- From `2⁻¹^c * a ≤ 2⁻¹^k` conclude `a * 2^k ≤ 2^c`.
  have hcc : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ c = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  have hkk : (2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ k = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc pairMarginal U x * (2 : ℝ≥0∞) ^ k
      = ((2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ c * pairMarginal U x)) * (2 : ℝ≥0∞) ^ k := by
        rw [← mul_assoc, hcc, one_mul]
    _ ≤ ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ k) * (2 : ℝ≥0∞) ^ k := by gcongr
    _ = (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ k) := by ring
    _ = (2 : ℝ≥0∞) ^ c := by rw [hkk, mul_one]

end Kolmogorov
