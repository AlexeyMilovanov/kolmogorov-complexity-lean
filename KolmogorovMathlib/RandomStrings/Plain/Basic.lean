/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Core.Invariance
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.RandomStrings.Clocks
import KolmogorovMathlib.RandomStrings.Effective.Configs
import Mathlib.Data.Nat.Log

/-!+# Plain complexity oracles and fixed interpreter data

The elementary interfaces of the C-random strings blueprint use the repository's
`ENat`-valued complexities. `Base` supplies fixed machines and actual evaluator codes;
there is no global choice of a universal machine. Its literal overhead is fixed before
any construction parameter.

Blueprint node `FoundationOracleClockedMachines`. We reuse `RandomStrings.OTM`, `OTMCode`,
`ClockedAccepts`, `ClockedDecides`, and `PolyTimeOracle` without new wrappers.
-/

namespace Kolmogorov.Milovanov

/-- A plain description of `x` of length at most `k`, including for partial machines.
This is the bounded-output predicate of the blueprint's checked interfaces. -/
def Simple (U : Map) (x : BitString) (k : ℕ) : Prop :=
  plainK U x ≤ (k : ENat)

/-- Bounded plain complexity is equivalent to a bounded program witness. -/
theorem simple_iff_exists_program (U : Map) (x : BitString) (k : ℕ) :
    Simple U x k ↔ ∃ p : BitString, p.length ≤ k ∧ produces U p [] x := by
  simpa only [Simple, plainK, programLength] using condK_le_iff U x [] k

/-- Increasing the description budget preserves simplicity. -/
theorem simple_mono (U : Map) (x : BitString) {k l : ℕ} (h : k ≤ l) :
    Simple U x k → Simple U x l :=
  fun hx => le_trans hx (by exact_mod_cast h)

/-- The number of simple strings, across all output lengths; it is a semantic count. -/
noncomputable def simpleCount (U : Map) (m : ℕ) : ℕ :=
  {x : BitString | Simple U x m}.ncard

/-- All bounded-output fibers are finite and have fewer than `2^(k+1)` elements.
Blueprint node `lem:counting`. No computability or optimality hypothesis is needed. -/
theorem simple_finite_card_lt (U : Map) (k : ℕ) :
    {x : BitString | Simple U x k}.Finite ∧ simpleCount U k < 2 ^ (k + 1) := by
  have hset : {x : BitString | Simple U x k} = (compressibleWords U [] k : Set BitString) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_compressibleWords_iff, Simple, plainK]
  constructor
  · rw [hset]
    exact Finset.finite_toSet _
  · unfold simpleCount
    rw [hset, Set.ncard_coe_finset]
    exact card_compressibleWordsLt U [] k

/-- The cumulative oracle with an explicit encoding of a string and a threshold. -/
def CumulativeOracle (queryEncode : BitString × ℕ → BitString) (U : Map) :
    Set BitString :=
  {w | ∃ x : BitString, ∃ k : ℕ, queryEncode (x, k) = w ∧ Simple U x k}

/-- Plain-random strings for the non-strict threshold `|x| ≤ C_U(x)`. -/
def PlainRandomOracle (U : Map) : Set BitString :=
  {x | (x.length : ENat) ≤ plainK U x}

/-- The empty string belongs to every plain-random oracle. -/
theorem nil_mem_plainRandomOracle (U : Map) :
    ([] : BitString) ∈ PlainRandomOracle U := by
  simp [PlainRandomOracle]

/-- The separation target, parameterized by a halting language and its query encoding. -/
def FormalizationTarget (H : Set BitString)
    (queryEncode : BitString × ℕ → BitString) : Prop :=
  ∃ U : Map, isOptimalConditional U ∧
    H ∉ RandomStrings.PolyTimeOracle (CumulativeOracle queryEncode U)

/-- Fixed interpreters, their numerical realizations, and a prefix literal overhead.
Blueprint node `FoundationConditionalMachine`. The empty section of `V` is the plain
machine. The code equations use `mapToNatFun`, including its rejection of invalid inputs.
The literal bound is the explicit bound of `FoundationPrefixLiteralBound`. -/
structure Base where
  /-- The fixed conditional plain machine. -/
  V : Map
  /-- Optimality in every condition, not only at the empty condition. -/
  optimalV : isOptimalConditional V
  /-- The fixed conditional prefix machine. -/
  D : Map
  /-- Prefix-freeness and optimality in every condition. -/
  optimalD : IsOptimalPrefixConditional D
  /-- A numerical code realizing the whole conditional plain map. -/
  vCode : Nat.Partrec.Code
  /-- Agreement with the repository's encoding of maps on strings. -/
  vCode_eq : vCode.eval = mapToNatFun V
  /-- A numerical code realizing the whole conditional prefix map. -/
  dCode : Nat.Partrec.Code
  /-- Agreement with the same encoding for the prefix interpreter. -/
  dCode_eq : dCode.eval = mapToNatFun D
  /-- A fixed prefix literal overhead, independent of the condition. -/
  cD : ℕ
  /-- Literal descriptions have length plus twice the ceiling logarithm overhead. -/
  literal_bound : ∀ a b : BitString,
    KP D a b ≤ (a.length + 2 * Nat.clog 2 (a.length + 2) + cD : ℕ)

/-- Fixed interpreter packages exist, using optimal-machine existence and code realization.
Blueprint node `FoundationConditionalMachine`. The literal-bound adapter is included. -/
theorem nonempty_base : Nonempty Base := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨D, hD⟩ := exists_isOptimalPrefixConditional
  obtain ⟨v, hv⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨d, hd⟩ := Nat.Partrec.Code.exists_code.mp hD.isDecompressor
  obtain ⟨c₁, hc₁⟩ := KPPlain_le_length_add_log D hD
  obtain ⟨c₂, hc₂⟩ := KP_le_KPPlain D hD
  refine ⟨⟨V, hV, D, hD, v, hv, d, hd, c₁ + c₂, ?_⟩⟩
  intro a b
  have hlen : (Nat.bits a.length).length ≤ Nat.clog 2 (a.length + 2) := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (lt_of_lt_of_le (by omega) (Nat.le_pow_clog (by decide) _))
  calc
    KP D a b ≤ KPPlain D a + (c₂ : ENat) := hc₂ a b
    _ ≤ (a.length : ENat) + 2 * (Nat.bits a.length).length + c₁ + c₂ :=
      add_le_add (hc₁ a) le_rfl
    _ ≤ (a.length + 2 * Nat.clog 2 (a.length + 2) + (c₁ + c₂) : ℕ) := by
      have hn : a.length + 2 * (Nat.bits a.length).length + c₁ + c₂ ≤
          a.length + 2 * Nat.clog 2 (a.length + 2) + (c₁ + c₂) := by omega
      exact_mod_cast hn

end Kolmogorov.Milovanov
