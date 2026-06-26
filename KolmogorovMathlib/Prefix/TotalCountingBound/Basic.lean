/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.AlgorithmicProbability.OptimalCoding

namespace Kolmogorov

open scoped ENNReal

/-! ### Finite low-complexity sets -/

/-- Any finite family of strings with `KPPlain ≤ n` injects into the concrete
finite list of programs of length at most `n`.

This is the elementary counting part of Theorem 64: choose, for each output in
`A`, one producing program of length at most `n`. Determinism of `Part` makes the
chosen-program map injective on `A`. The sharper SUV estimate below needs the
additional argument that recovers the `K(n)` factor. -/
theorem card_KPPlain_le_boundedPrograms_length (U : Map) (n : ℕ)
    (A : Finset BitString) (hA : ∀ x ∈ A, KPPlain U x ≤ (n : ENat)) :
    A.card ≤ (boundedPrograms n).length := by
  classical
  have h_exists : ∀ x ∈ A, ∃ p, p.length ≤ n ∧ produces U p [] x := by
    intro x hx
    have hxK : condK U x [] ≤ (n : ENat) := by
      simpa [KPPlain, KP, KP_eq_condK] using hA x hx
    exact (condKLeIff U x [] n).mp hxK
  let pOf : BitString → BitString := fun x =>
    if hx : x ∈ A then Classical.choose (h_exists x hx) else []
  have hpOf_mem :
      Set.MapsTo pOf (A : Set BitString) ((boundedPrograms n).toFinset : Set BitString) := by
    intro x hx
    have hxf : x ∈ A := by simpa using hx
    have hspec := Classical.choose_spec (h_exists x hxf)
    change pOf x ∈ (boundedPrograms n).toFinset
    rw [show pOf x = Classical.choose (h_exists x hxf) by simp [pOf, hxf]]
    rw [List.mem_toFinset]
    exact (mem_boundedPrograms_iff (Classical.choose (h_exists x hxf)) n).mpr hspec.1
  have hpOf_inj : (A : Set BitString).InjOn pOf := by
    intro x hx y hy hxy
    have hxf : x ∈ A := by simpa using hx
    have hyf : y ∈ A := by simpa using hy
    have hxspec := Classical.choose_spec (h_exists x hxf)
    have hyspec := Classical.choose_spec (h_exists y hyf)
    have hxprod : produces U (pOf x) [] x := by
      rw [show pOf x = Classical.choose (h_exists x hxf) by simp [pOf, hxf]]
      exact hxspec.2
    have hyprod : produces U (pOf x) [] y := by
      rw [hxy]
      rw [show pOf y = Classical.choose (h_exists y hyf) by simp [pOf, hyf]]
      exact hyspec.2
    exact (Part.mem_unique hxprod hyprod)
  calc
    A.card ≤ ((boundedPrograms n).toFinset).card :=
      Finset.card_le_card_of_injOn pOf hpOf_mem hpOf_inj
    _ = (boundedPrograms n).length := by
      rw [List.toFinset_card_of_nodup (boundedPrograms_nodup n)]

/-! ### The crux of the lower bound: short codes for `n - K(n)` -/

/-- **Crux of the Theorem 64 lower bound.**  The number `n - K(n)` has prefix
complexity at most `K(n) + O(1)`.

A single fixed computable function `f` reads the pair
`(Nat.bits n, natCode kn) = prefixComplexityContext (Nat.bits n) kn` and outputs
`Nat.bits (n - kn)`: it recovers `n = decodeBits (decodeFirst ·)` and
`kn = (decodeSecond ·).length - 1` (since `natCode kn` has length `kn + 1`), then
emits the binary code of their truncated difference.  Computable maps do not raise
prefix complexity (`KPPlain_map_le`), and the pair itself has complexity
`kn + O(1)` by SUV Theorem 61 (`KPPair_self_complexity_le`).  Composing the two
bounds yields the claim.
-/
theorem KPPlain_natBits_sub_self_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn →
      KPPlain U (Nat.bits (n - kn)) ≤ (kn : ENat) + (c : ENat) := by
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℕ, ∀ n kn : ℕ, HasPrefixComplexityValue U (Nat.bits n) kn →
      KPPlain U (Nat.bits (n - kn)) ≤ KPPlain U (prefixComplexityContext (Nat.bits n) kn) + c1 := by
    obtain ⟨c1, hc1⟩ : ∃ c1 : ℕ, ∀ w : BitString,
        KPPlain U (Nat.bits ((decodeBits (decodeFirst w)) - ((decodeSecond w).length - 1))) ≤ KPPlain U w + c1 := by
      have hf_computable : Computable (fun w : BitString => Nat.bits ((decodeBits (decodeFirst w)) - ((decodeSecond w).length - 1))) := by
        refine Computable.comp natBitsComputable ?_
        apply Computable.comp Primrec.nat_sub.to_comp (Computable.pair (decodeBitsComputable.comp decodeFirst_computable) (Computable.comp Primrec.nat_sub.to_comp (Computable.pair (Computable.list_length.comp decodeSecond_computable) (Computable.const 1))))
      convert KPPlain_map_le U hU _ hf_computable using 1
    use c1; intros n kn hkn; specialize hc1 (prefixComplexityContext n.bits kn)
    simp only [prefixComplexityContext_eq_pairCode, decodeFirst_pairCode, decodeSecond_pairCode,
      decodeBits_natBits, length_natCode, add_tsub_cancel_right] at hc1 ⊢
    exact hc1
  obtain ⟨c61, hc61⟩ : ∃ c61 : ℕ, ∀ n kn : ℕ, HasPrefixComplexityValue U (Nat.bits n) kn →
      KPPlain U (prefixComplexityContext (Nat.bits n) kn) ≤ kn + c61 := by
    obtain ⟨c61, hc61⟩ := KPPair_self_complexity_le U hU
    exact ⟨c61, fun n kn h => by
      simpa only [KPPlain_eq_KP, KPPair_eq_KP_pairCode, prefixComplexityContext_eq_pairCode]
        using hc61 _ _ h⟩
  exact ⟨c1 + c61, fun n kn h => le_trans (hc1 n kn h) (by
    rw [add_comm]
    refine le_trans (add_le_add_right (hc61 n kn h) _) ?_
    norm_cast
    omega)⟩

/-- **SUV Theorem 64 (Lower Bound), faithful form.**  In the meaningful regime
`K(n) ≤ n`, there are at least `2^{n - K(n)}` strings whose prefix complexity is
at most `n + O(1)`.

The witnesses are *all* `2^{n-kn}` strings of length `n - kn`.  Each such string
`x` satisfies, by SUV Theorem 63(a) (`KPPlain_le_length_add_KPPlain_length`),
`K(x) ≤ (n - kn) + K(Nat.bits (n - kn)) + O(1)`, and the crux
`KPPlain_natBits_sub_self_le` bounds `K(Nat.bits (n - kn)) ≤ kn + O(1)`, giving
`K(x) ≤ (n - kn) + kn + O(1) = n + O(1)` because `kn ≤ n`.  The cardinality
`2^{n-kn}` equals `2^n · 2^{-kn}` in `ℝ≥0∞` since `kn ≤ n`.

The additive `O(1)` slack on the complexity side is genuine: the original
`card_KPPlain_le_lower_bound` below, which asks for complexity `≤ n` exactly, is
not a theorem for every optimal machine — for a machine all of whose halting
programs have positive length (e.g. the tagged-union universal machine), no
string has complexity `≤ 0`, so the `n = 0` instance forces an empty witness set
while the right-hand side `2^0 · 2^{-(kn+c)}` is positive.
-/
theorem card_KPPlain_le_lower_bound_faithful (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn → kn ≤ n →
    ∃ A : Finset BitString, (∀ x ∈ A, KPPlain U x ≤ (n : ENat) + (c : ENat)) ∧
    (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ kn ≤ (A.card : ℝ≥0∞) := by
  obtain ⟨c63a, hc63a⟩ := KPPlain_le_length_add_KPPlain_length U hU
  obtain ⟨ccrux, hccrux⟩ := KPPlain_natBits_sub_self_le U hU
  use ccrux + c63a
  intro n kn hkn hle
  use stringsOfLength (n - kn)
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxlen : x.length = n - kn := (memStringsOfLength (n - kn) x).mp hx
    refine le_trans (hc63a x) ?_
    rw [hxlen]
    refine le_trans (add_le_add_three le_rfl (hccrux n kn hkn) le_rfl) ?_
    norm_cast
    omega
  · rw [cardStringsOfLength]
    exact two_pow_mul_inv_pow_le_cast_pow_sub n kn


end Kolmogorov
