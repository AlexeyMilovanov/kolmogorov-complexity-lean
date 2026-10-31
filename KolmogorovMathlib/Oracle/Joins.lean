/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Oracle.Basic

/-!
# Binary joins and countable data encodings

Turing reducibility is Mathlib's relation applied to total characteristic oracles. This
module defines the binary interleaving `oracleJoin A B` and the paired countable join
`oracleCountableJoin A` of sets of natural numbers, and proves (blueprint node
`oracle:joins`) that the interleaving computes both components and is a least upper bound,
that the countable join computes each component, and that a base oracle, countably many
sets and an integer-valued table can be encoded into a single oracle. Only binary joins are
asserted to be least upper bounds; countable joins need no uniformity assumption on
preexisting component reductions.

The upper-bound statements are used wherever several oracles (for pressure, dimension or
complexity bounds) must be merged into one witnessing oracle, and `oracle_joins_tables`
supplies a single oracle computing a countable family of data in the conformal dimension
theorem.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

/-- Binary interleaving places the first oracle on even queries and the second on odd
queries. Blueprint node `oracle:joins`. -/
def oracleJoin (A B : Set ℕ) : Set ℕ :=
  {n | if n % 2 = 0 then n / 2 ∈ A else n / 2 ∈ B}

/-- The paired countable join uses one fixed natural-number pairing.
Blueprint node `oracle:joins`. -/
def oracleCountableJoin (A : ℕ → Set ℕ) : Set ℕ :=
  {n | (Nat.unpair n).2 ∈ A (Nat.unpair n).1}

/-- Characteristic oracles agree at two queries whose membership statements are equivalent. -/
private theorem charOracle_eq_of_mem_iff {A B : Set ℕ} {m n : ℕ} (h : m ∈ A ↔ n ∈ B) :
    charOracle A m = charOracle B n := by
  classical
  simp only [charOracle, h]

/-- If every query to `A` is a query to `J` at a primitive recursive position, then `A` is
Turing reducible to `J`. -/
private theorem reducible_of_query {A J : Set ℕ} {f : ℕ → ℕ} (hf : Primrec f)
    (h : ∀ n, charOracle A n = charOracle J (f n)) : charOracle A ≤ᵀ charOracle J := by
  have hquery : PartrecIn {charOracle J} (fun n ↦ charOracle J (f n)) :=
    PartrecIn.comp (PartrecIn.oracle _ (Set.mem_singleton _))
      (Computable.computableIn hf.to_comp)
  exact PartrecIn.of_eq hquery fun n ↦ (h n).symm

/-- A binary interleaving computes its first component oracle.
Blueprint node `oracle:joins`. -/
theorem oracle_joins (A B : Set ℕ) :
    charOracle A ≤ᵀ charOracle (oracleJoin A B) := by
  refine reducible_of_query (f := fun n ↦ 2 * n)
    (Primrec₂.comp Primrec.nat_mul (Primrec.const 2) Primrec.id) fun n ↦ ?_
  refine charOracle_eq_of_mem_iff ?_
  have h2 : (2 * n) % 2 = 0 := by omega
  have h3 : (2 * n) / 2 = n := by omega
  simp [oracleJoin, h2, h3]

/-- A binary interleaving computes its second component oracle.
Blueprint node `oracle:joins`. -/
theorem oracle_joins_right (A B : Set ℕ) :
    charOracle B ≤ᵀ charOracle (oracleJoin A B) := by
  have hdouble : Primrec (fun n : ℕ ↦ 2 * n) :=
    Primrec₂.comp Primrec.nat_mul (Primrec.const 2) Primrec.id
  refine reducible_of_query (f := fun n ↦ 2 * n + 1)
    (Primrec₂.comp Primrec.nat_add hdouble (Primrec.const 1)) fun n ↦ ?_
  refine charOracle_eq_of_mem_iff ?_
  have h2 : (2 * n + 1) % 2 = 1 := by omega
  have h3 : (2 * n + 1) / 2 = n := by omega
  simp [oracleJoin, h2, h3]

/-- The parity conditional on component characteristic oracles agrees with the characteristic
oracle of their binary interleaving. -/
private theorem cond_charOracle_eq_charOracle_oracleJoin (A B : Set ℕ) (n : ℕ) :
    cond (n % 2 == 0) (charOracle A (n / 2)) (charOracle B (n / 2)) =
      charOracle (oracleJoin A B) n := by
  by_cases hn : n % 2 = 0
  · simp only [hn, beq_self_eq_true, Bool.cond_true]
    exact charOracle_eq_of_mem_iff (by simp [oracleJoin, hn])
  · have hn' : (n % 2 == 0) = false := by simpa using hn
    simp only [hn', Bool.cond_false]
    exact charOracle_eq_of_mem_iff (by simp [oracleJoin, hn])

/-- If `D ≤ᵀ C`, the characteristic oracle of `D` queried at half the input is computable
from `C`. -/
private theorem partrecIn_charOracle_div_two {C D : Set ℕ}
    (h : charOracle D ≤ᵀ charOracle C) :
    PartrecIn {charOracle C} (fun a : ℕ ↦ charOracle D (a / 2)) := by
  have hdiv : RecursiveIn {charOracle C} (fun a : ℕ ↦ Part.some (a / 2)) :=
    (Primrec.nat_div.comp Primrec.id (Primrec.const 2)).computableIn.recursiveIn
  have hcomp : PartrecIn {charOracle C} (fun a : ℕ ↦ (Part.some (a / 2)).bind (charOracle D)) :=
    relative_closure_comp _ _ _ hdiv h
  exact PartrecIn.of_eq hcomp (fun a ↦ Part.bind_some _ _)

/-- The binary interleaving is a least upper bound for Turing reducibility.
Blueprint node `oracle:joins`. -/
theorem oracle_joins_least (A B C : Set ℕ) (hA : charOracle A ≤ᵀ charOracle C)
    (hB : charOracle B ≤ᵀ charOracle C) :
    charOracle (oracleJoin A B) ≤ᵀ charOracle C := by
  have hcond : PartrecIn {charOracle C}
      (fun n : ℕ ↦ cond (n % 2 == 0) (charOracle A (n / 2)) (charOracle B (n / 2))) := by
    apply relative_closure_cond
    · exact (Primrec.eq.decide.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
        (Primrec.const 0)).computableIn
    · exact partrecIn_charOracle_div_two hA
    · exact partrecIn_charOracle_div_two hB
  exact PartrecIn.of_eq hcond (cond_charOracle_eq_charOracle_oracleJoin A B)

/-- A specified countable join computes each fixed component, without a leastness claim.
Blueprint node `oracle:joins`. -/
theorem oracle_joins_countable (A : ℕ → Set ℕ) (j : ℕ) :
    charOracle (A j) ≤ᵀ charOracle (oracleCountableJoin A) := by
  refine reducible_of_query (f := Nat.pair j)
    (Primrec₂.natPair.comp (Primrec.const j) Primrec.id) fun n ↦ ?_
  refine charOracle_eq_of_mem_iff ?_
  simp [oracleCountableJoin]

/-- The graph of a signed integer table `v`, coded as the set of numbers
`⟨⟨i, j⟩, encode (v i j)⟩`. -/
private def tableGraph (v : ℕ → ℕ → ℤ) : Set ℕ :=
  {n | Encodable.encode
    (v (Nat.unpair (Nat.unpair n).1).1 (Nat.unpair (Nat.unpair n).1).2) =
      (Nat.unpair n).2}

/-- Searching the graph of a signed integer table and decoding the unique matching
code computes the table uniformly in both input coordinates. -/
private theorem computableIn_table_of_graph (v : ℕ → ℕ → ℤ) :
    ComputableIn {charOracle (tableGraph v)}
      (fun p : ℕ × ℕ ↦ v p.1 p.2) := by
  classical
  let G := tableGraph v
  have hquery : PartrecIn {charOracle G}
      (fun q : (ℕ × ℕ) × ℕ ↦ charOracle G (Nat.pair (Nat.pair q.1.1 q.1.2) q.2)) := by
    apply PartrecIn.comp (PartrecIn.oracle _ (Set.mem_singleton _))
    exact (Primrec₂.natPair.comp
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst)) Primrec.snd).computableIn
  have htest : ComputableIn₂ {charOracle G}
      (fun (_ : (ℕ × ℕ) × ℕ) (r : ℕ) ↦ decide (r = 1)) := by
    exact (PrimrecPred.decide
      (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 1))).to₂.to_comp.computableIn₂
  have hsearch := PartrecIn.rfind (hquery.map htest).to₂
  have hdecode : PartrecIn₂ {charOracle G}
      (fun (_ : ℕ × ℕ) (k : ℕ) ↦ Part.ofOption (Encodable.decode (α := ℤ) k)) :=
    (Computable.ofOption (Computable.decode.comp Computable.snd)).partrecIn.to₂
  refine PartrecIn.of_eq_tot (hsearch.bind hdecode) ?_
  intro p
  refine Part.mem_bind_iff.mpr ⟨Encodable.encode (v p.1 p.2), ?_, ?_⟩
  · apply Nat.mem_rfind.mpr
    constructor
    · simp [charOracle, G, tableGraph, Nat.unpair_pair]
    · intro m hm
      have hne : Encodable.encode (v p.1 p.2) ≠ m := Nat.ne_of_gt hm
      simp [charOracle, G, tableGraph, Nat.unpair_pair, hne]
  · rw [Encodable.encodek]
    simp

/-- Countably many sets and integer-valued tables can be encoded with any base oracle;
the resulting oracle computes the tables uniformly in row and entry.
Blueprint node `oracle:joins`. -/
theorem oracle_joins_tables (C : Set ℕ) (A : ℕ → Set ℕ) (v : ℕ → ℕ → ℤ) :
    ∃ B : Set ℕ, charOracle C ≤ᵀ charOracle B ∧
      (∀ j, charOracle (A j) ≤ᵀ charOracle B) ∧
      ComputableIn {charOracle B} (fun p : ℕ × ℕ => v p.1 p.2) := by
  let G := tableGraph v
  let J := oracleJoin (oracleCountableJoin A) G
  let B := oracleJoin C J
  have hJ : charOracle J ≤ᵀ charOracle B := oracle_joins_right C J
  have hG : charOracle G ≤ᵀ charOracle B :=
    (oracle_joins_right (oracleCountableJoin A) G).trans hJ
  refine ⟨B, oracle_joins C J, ?_, ?_⟩
  · intro j
    exact (oracle_joins_countable A j).trans
      ((oracle_joins (oracleCountableJoin A) G).trans hJ)
  · exact RecursiveIn.subst (computableIn_table_of_graph v)
      (by simpa only [Set.mem_singleton_iff, forall_eq] using hG)

end Kolmogorov.PointToSet
