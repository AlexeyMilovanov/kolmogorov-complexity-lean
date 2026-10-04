/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.CylinderMass
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelStage
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveNull
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveOpenNormalForm
import KolmogorovMathlib.AlgorithmicRandomness.Disjointify
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Covers by all strings of a fixed length (SUV §5.8, p. 172, remark (3))

> "For `α > 1` any subset `A ⊆ Ω` is an `α`-null set.  Indeed, one can cover `A`
> by `2^n` intervals that correspond to `2^n` strings of length `n`, and the sum
> of their `α`-measures tends to `0` as `n → ∞`." (SUV §5.8, p. 172, remark (3))

This module supplies the *computable* form of that cover, which is what the
effective version of remark (3) needs, together with the exact value of its
`α`-weight.  It is deliberately stated in terms of the raw expression
`uniformMeasure (cantorCylinder x) ^ α` (and not of `intervalAlphaMass`, which is
introduced in `Dimension/Basic.lean`) so that `Dimension/Basic.lean` can import
it.

## Contents

* `levelEnum L` — the enumeration `ℕ → Option BitString` of *all* strings of
  length `L`, each exactly once, indexed by the standard `Encodable` numbering
  of `BitString`; `computable₂_levelEnum` proves it computable jointly in
  `L` and the index, which is what a cover algorithm has to provide.
* `tsum_levelEnum_rpow` — its exact `α`-weight `2^L · (2^{-L})^α`.
* `subset_iUnion_levelEnum` — it covers the whole Cantor space.
-/

namespace Kolmogorov

open MeasureTheory Encodable
open scoped ENNReal

/-! ## The enumeration of all strings of a fixed length -/

/-- All bitstrings of length `L`, enumerated by their code in the standard
numbering of `BitString`: the index `k` yields the string it codes, provided that
string has length `L` and `k` really is its code.  The last clause makes the
support of the enumeration exactly the set of codes of length-`L` strings, so
each such string occurs exactly once. -/
def levelEnum (L k : ℕ) : Option BitString :=
  (Encodable.decode₂ BitString k).bind fun x =>
    bif decide (x.length = L) then some x else none

/-- The level-by-level enumeration of bit strings is computable in the level and the index. -/
lemma computable₂_levelEnum : Computable₂ levelEnum := by
  have hx : Computable (fun q : ℕ × ℕ => Encodable.decode₂ BitString q.2) :=
    (Primrec.decode₂.comp Primrec.snd).to_comp
  have hbranch : Computable₂ (fun (q : ℕ × ℕ) (x : BitString) =>
      bif decide (x.length = q.1) then some x else none) := by
    have htest : Computable (fun r : (ℕ × ℕ) × BitString => decide (r.2.length = r.1.1)) :=
      ((PrimrecRel.comp Primrec.eq (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)).decide).to_comp
    exact (Computable.cond htest (Computable.option_some.comp Computable.snd)
      (Computable.const none)).to₂
  exact (Computable.option_bind hx hbranch).to₂

/-- The level enumeration returns `x` at index `k` exactly when `x` has length `L` and code `k`. -/
lemma levelEnum_eq_some_iff {L k : ℕ} {x : BitString} :
    levelEnum L k = some x ↔ x.length = L ∧ encode x = k := by
  unfold levelEnum
  constructor
  · intro h
    cases hd : Encodable.decode₂ BitString k with
    | none => rw [hd] at h; simp at h
    | some y =>
      rw [hd] at h
      simp only [Option.bind_some] at h
      by_cases hy : y.length = L
      · rw [decide_eq_true hy, Bool.cond_true, Option.some_inj] at h
        subst h
        exact ⟨hy, Encodable.decode₂_eq_some.1 hd⟩
      · rw [decide_eq_false hy, Bool.cond_false] at h
        exact absurd h (by simp)
  · rintro ⟨hlen, hcode⟩
    rw [Encodable.decode₂_eq_some.2 hcode]
    simp only [Option.bind_some]
    rw [decide_eq_true hlen, Bool.cond_true]

/-- The level enumeration returns every string of the right length at its own code. -/
lemma levelEnum_encode {L : ℕ} {x : BitString} (h : x.length = L) :
    levelEnum L (encode x) = some x :=
  levelEnum_eq_some_iff.2 ⟨h, rfl⟩

/-- The cover by all strings of length `L` covers the whole Cantor space, hence
any subset of it. -/
lemma subset_iUnion_levelEnum (L : ℕ) (A : Set CantorSeq) :
    A ⊆ ⋃ k, (levelEnum L k).elim ∅ cantorCylinder := by
  intro w _
  refine Set.mem_iUnion.2 ⟨encode (cantorPrefix w L), ?_⟩
  rw [levelEnum_encode (cantorPrefix_length w L)]
  exact mem_cantorCylinder_cantorPrefix w L

/-! ## The `α`-weight of the fixed-length cover -/

/-- The codes of the strings of length `L`. -/
private def levelCodes (L : ℕ) : Finset ℕ := (levelFinset L).image encode

private lemma card_levelCodes (L : ℕ) : (levelCodes L).card = 2 ^ L := by
  rw [levelCodes, Finset.card_image_of_injective _ encode_injective, card_levelFinset]

private lemma mem_levelCodes_of_levelEnum {L k : ℕ} {x : BitString}
    (h : levelEnum L k = some x) : k ∈ levelCodes L := by
  obtain ⟨hlen, hcode⟩ := levelEnum_eq_some_iff.1 h
  exact Finset.mem_image.2 ⟨x, mem_levelFinset.2 hlen, hcode⟩

/-- **SUV §5.8, p. 172, remark (3).** The `α`-weight of the cover by all `2^L`
strings of length `L` is exactly `2^L · (2^{-L})^α`. -/
theorem tsum_levelEnum_rpow (α : ℝ) (L : ℕ) :
    (∑' k, (levelEnum L k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
      = (2 : ℝ≥0∞) ^ L * ((2 : ℝ≥0∞)⁻¹ ^ L) ^ α := by
  set c : ℝ≥0∞ := ((2 : ℝ≥0∞)⁻¹ ^ L) ^ α with hc
  have hzero : ∀ k ∉ levelCodes L,
      (levelEnum L k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α) = 0 := by
    intro k hk
    cases h : levelEnum L k with
    | none => simp
    | some x => exact absurd (mem_levelCodes_of_levelEnum h) hk
  have hval : ∀ k ∈ levelCodes L,
      (levelEnum L k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α) = c := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
    have hlen : x.length = L := mem_levelFinset.1 hx
    rw [levelEnum_encode hlen]
    simp only [Option.elim_some, hc]
    rw [uniformMeasure_cantorCylinder, hlen]
  rw [tsum_eq_sum hzero, Finset.sum_congr rfl hval, Finset.sum_const, card_levelCodes,
    nsmul_eq_mul]
  norm_cast

end Kolmogorov
