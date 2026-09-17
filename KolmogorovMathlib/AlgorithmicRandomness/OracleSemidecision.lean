import KolmogorovMathlib.AlgorithmicRandomness.OracleComputability

/-!
# Semidecision with the halting oracle `0′`

This file supplies the bridge needed by SUV Theorem 37: *every semidecidable
(`Σ⁰₁`) predicate is decidable with the halting oracle `0′`.*

Concretely, if `g : α → ℕ → Bool` is computable in two arguments, then the
predicate `∃ k, g a k` is computed by a `Bool`-valued function that is
`Kolmogorov.ComputableInJump`, i.e. computable with the oracle
`Kolmogorov.haltingChi`.

The proof goes through the standard route:

* `semiSearch g a` is the unbounded search `Nat.rfind (fun k => g a k)`; its
  domain is exactly `{a | ∃ k, g a k}`;
* by the `s-m-n` theorem (`Nat.Partrec.Code.curry`) one attaches to each `a`
  a code `d a` whose evaluation on *any* input agrees with the search, so
  `d a` is in the halting set iff the search converges;
* the resulting index function is computable, and one oracle query finishes
  the job.

Main results:

* `Kolmogorov.exists_haltingIndex` — the computable many-one reduction of a
  `Σ⁰₁` predicate to the halting set;
* `Kolmogorov.exists_computableInJump_semidecide` — the `0′`-decision
  procedure.
-/

open Encodable

namespace Kolmogorov

variable {α : Type*} [Primcodable α]

/-- The unbounded search attached to a computable `Bool`-valued test.  Its
domain is exactly the set of `a` for which some `k` satisfies `g a k`. -/
def semiSearch (g : α → ℕ → Bool) : α →. ℕ :=
  fun a => Nat.rfind fun k => Part.some (g a k)

/-- Searching for the first witness `k` with `g a k = true` is a partial recursive operation
whenever the test `g` is computable. -/
lemma partrec_semiSearch {g : α → ℕ → Bool} (hg : Computable₂ g) :
    Partrec (semiSearch g) :=
  Partrec.rfind (Computable₂.partrec₂ hg)

omit [Primcodable α] in
/-- The unbounded search for a witness of `g a` halts exactly when some witness exists. -/
lemma semiSearch_dom {g : α → ℕ → Bool} (a : α) :
    (semiSearch g a).Dom ↔ ∃ k, g a k = true := by
  change (Nat.rfind (show ℕ →. Bool from fun k => Part.some (g a k))).Dom ↔ ∃ k, g a k = true
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨k, hk, -⟩
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simp [hk], fun {m} _ => Part.some_dom _⟩

/-- **Many-one reduction of a `Σ⁰₁` predicate to the halting set.**  For a
computable test `g`, the predicate `∃ k, g a k` is computably reducible to
`haltingSet`. -/
theorem exists_haltingIndex {g : α → ℕ → Bool} (hg : Computable₂ g) :
    ∃ idx : α → ℕ, Computable idx ∧ ∀ a, haltingSet (idx a) ↔ ∃ k, g a k = true := by
  classical
  have hf : Partrec (semiSearch g) := partrec_semiSearch hg
  have hFp : Nat.Partrec fun n =>
      Part.bind (decode (α := α) n) fun a => (semiSearch g a).map encode := hf
  have hF2 : Nat.Partrec fun p =>
      Part.bind (decode (α := α) (Nat.unpair p).1) fun a =>
        (semiSearch g a).map encode :=
    (hFp.comp (Nat.Partrec.of_primrec Nat.Primrec.left)).of_eq (fun n => by simp)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hF2
  refine ⟨fun a => encode (Nat.Partrec.Code.curry c (encode a)), ?_, ?_⟩
  · exact Computable.encode.comp
      ((Primrec₂.to_comp Nat.Partrec.Code.primrec₂_curry).comp
        (Computable.const c) Computable.encode)
  · intro a
    have hofNat :
        Denumerable.ofNat Nat.Partrec.Code
            (encode (Nat.Partrec.Code.curry c (encode a)))
          = Nat.Partrec.Code.curry c (encode a) :=
      Denumerable.ofNat_encode _
    rw [haltingSet, hofNat, Nat.Partrec.Code.eval_curry, hc]
    simp only [Nat.unpair_pair, encodek, Part.coe_some, Part.bind_some,
      Part.dom_iff_mem, Part.mem_map_iff]
    constructor
    · rintro ⟨-, k, hk, -⟩
      exact (semiSearch_dom (g := g) a).1 (Part.dom_iff_mem.2 ⟨k, hk⟩)
    · intro h
      obtain ⟨k, hk⟩ := Part.dom_iff_mem.1 ((semiSearch_dom (g := g) a).2 h)
      exact ⟨encode k, k, hk, rfl⟩

/-- **SUV Theorem 37, semidecision bridge.**  Any `Σ⁰₁` predicate is decided by
a `0′`-computable `Bool`-valued function. -/
theorem exists_computableInJump_semidecide {g : α → ℕ → Bool} (hg : Computable₂ g) :
    ∃ h : α → Bool, ComputableInJump h ∧ ∀ a, (h a = true ↔ ∃ k, g a k = true) := by
  classical
  obtain ⟨idx, hidx, hspec⟩ := exists_haltingIndex hg
  refine ⟨fun a => decide (haltingSet (idx a)), ?_, ?_⟩
  · have h1 : PartrecIn ({haltingChi} : Set (ℕ →. ℕ)) fun a : α => haltingChi (idx a) :=
      PartrecIn.comp partrecIn_haltingChi hidx.computableIn
    have hdec : ComputableIn ({haltingChi} : Set (ℕ →. ℕ))
        (fun p : α × ℕ => decide (p.2 = 1)) :=
      Computable.computableIn <| Primrec.to_comp <|
        PrimrecPred.decide (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 1))
    have h2 : PartrecIn ({haltingChi} : Set (ℕ →. ℕ))
        fun a : α => (haltingChi (idx a)).map fun v => decide (v = 1) :=
      h1.map hdec.to₂
    refine PartrecIn.of_eq_tot h2 ?_
    intro a
    by_cases h : haltingSet (idx a) <;> simp [haltingChi, h]
  · intro a
    simpa using hspec a

end Kolmogorov
