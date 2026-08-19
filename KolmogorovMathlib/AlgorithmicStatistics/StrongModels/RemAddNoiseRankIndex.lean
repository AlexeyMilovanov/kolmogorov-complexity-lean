import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaEquivalence

/-!
# Ordinary conditional complexity of a description from its rank

If `x` has fewer than `2 ^ m` distinct `(i, j)`-descriptions, then any single
`(i, j)`-description of `x` is determined, given `x` itself, by its rank in the
online enumeration of descriptions of `x`.  This is the ordinary (plain)
conditional analogue of `description_count_of_conditional_complexity_gap`; here
the condition is just `x`, so no prefix-complexity context is needed.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- **Rank bound for a description, conditional on the described string.**
If `x` has fewer than `2 ^ m` distinct `(i, j)`-descriptions, then the canonical
code of any `(i, j)`-description `A` of `x` has ordinary conditional complexity
at most `m + O(log (i + j))` given `x`. -/
theorem condK_description_code_le_of_not_many
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (i j m : ℕ),
      x ∈ A →
      setComplexity U A hA = (i : ENat) →
      A.card ≤ 2 ^ j →
      ¬ ManyIJDescriptions U x i j m →
      condK V (codedUniformOn A hA).code x ≤ ((m + logSlack c (i + j) : ℕ) : ENat) := by
  obtain ⟨c_opt, hc_opt⟩ : ∃ c_opt : Code, IsCodeFor c_opt U :=
    Nat.Partrec.Code.exists_code.mp hU.1.1
  have hg : Partrec (fun q : BitString × BitString ↦
      indexSelectorFn c_opt (pairCode q.1 []) q.2) := by
    have hmap : Computable (fun q : BitString × BitString ↦
        (q.2, pairCode q.1 [])) :=
      Computable.pair Computable.snd
        ((pairCode_primrec.comp Primrec.fst (Primrec.const [])).to_comp)
    exact ((partrec_indexSelectorFn c_opt).comp hmap).of_eq (fun q => rfl)
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV
    (fun y p ↦ indexSelectorFn c_opt (pairCode y []) p) hg
  refine ⟨C + 6, ?_⟩
  intro A hA x i j m hxA hcomp hsize hnm
  set code := (codedUniformOn A hA).code with hcode
  obtain ⟨t₀, ht₀⟩ := code_mem_appearanceListCodes hc_opt A hA x i j hxA hcomp hsize
  obtain ⟨r, hr_lt, hr_spec⟩ := indexSelectorFn_eq_code c_opt i j x code t₀ ht₀
  set w := richInput i j 0 r with hw
  have hdec : decodeFirst (pairCode x []) = x := decodeFirst_pairCode x []
  have h_some : indexSelectorFn c_opt (pairCode x []) w = Part.some code :=
    hr_spec (pairCode x []) w hdec (selNat_richInput i j 0 r)
      (selAlpha_richInput i j 0 r) (selH_richInput i j 0 r)
  have h_in : code ∈ indexSelectorFn c_opt (pairCode x []) w :=
    Part.eq_some_iff.mp h_some
  have hbound := hC x w code h_in
  -- The program is the packed tuple `(i, j, 0, r)`.
  have h_w_len : w.length ≤ 2 * (Nat.bits i).length + 2 * (Nat.bits j).length +
      (Nat.bits r).length + 6 := by
    change (richInput i j 0 r).length ≤ _
    unfold richInput selectorInput pack4
    simp [length_pairCode]
    omega
  have hr_lt_2m : r < 2 ^ m :=
    lt_of_lt_of_le hr_lt
      (appearanceListCodes_length_lt_of_not_manyIJ hc_opt hnm t₀).le
  have hr_len : (Nat.bits r).length ≤ m := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hr_lt_2m
  have hi_len : (Nat.bits i).length ≤ (Nat.bits (i + j)).length :=
    length_natBits_mono (by omega)
  have hj_len : (Nat.bits j).length ≤ (Nat.bits (i + j)).length :=
    length_natBits_mono (by omega)
  have hfinal : w.length + C ≤ m + logSlack (C + 6) (i + j) := by
    have hslack : logSlack (C + 6) (i + j) =
        (C + 6) * (Nat.bits (i + j)).length + (C + 6) := rfl
    nlinarith [Nat.zero_le ((Nat.bits (i + j)).length)]
  calc
    condK V code x ≤ ((w.length : ENat)) + (C : ENat) := hbound
    _ = ((w.length + C : ℕ) : ENat) := by push_cast; ring
    _ ≤ ((m + logSlack (C + 6) (i + j) : ℕ) : ENat) := by exact_mod_cast hfinal

end Kolmogorov
