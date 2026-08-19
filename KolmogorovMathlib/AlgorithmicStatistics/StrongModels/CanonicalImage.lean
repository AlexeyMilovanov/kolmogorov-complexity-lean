import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProgramList
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization

/-!
# Canonical finite-set images of total programs

This file finishes the executable finite-set image part of S0.  The varying
program is an input to the transformer: it is not captured by a separately
specialized computable function.  Outputs are deduplicated and sorted before
being encoded, so extensionally equal image sets receive the repository's
canonical uniform-set code.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- Canonical uniform-set code of the finite set underlying an output list.
For the empty list this is merely a syntactic distribution code; all
source-facing correctness theorems below establish nonemptiness first. -/
noncomputable def canonicalImageCodeOfList (ys : List BitString) : BitString :=
  canonicalUniformCodeOfList (canonicalFinsetList ys.toFinset)

/-- Canonical image coding is primitive recursive in the output list. -/
theorem canonicalImageCodeOfList_primrec :
    Primrec canonicalImageCodeOfList :=
  canonicalUniformCodeOfList_primrec.comp
    canonicalFinsetList_toFinset_primrec

theorem canonicalImageCodeOfList_computable :
    Computable canonicalImageCodeOfList :=
  canonicalImageCodeOfList_primrec.to_comp

/-- On a nonempty output list, `canonicalImageCodeOfList` is exactly the
canonical code of the corresponding finite set. -/
theorem canonicalImageCodeOfList_eq_codedUniformOn
    (ys : List BitString) (hys : ys.toFinset.Nonempty) :
    canonicalImageCodeOfList ys = (codedUniformOn ys.toFinset hys).code :=
  canonicalUniformCodeOfList_canonicalFinsetList ys.toFinset hys

/-- Decode the point list of a distribution code and normalize it to the
canonical sorted enumeration of its underlying finite set. -/
noncomputable def canonicalPointListOfCode (w : BitString) : List BitString :=
  canonicalFinsetList
    ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset

/-- Canonical point-list decoding is primitive recursive. -/
theorem canonicalPointListOfCode_primrec :
    Primrec canonicalPointListOfCode := by
  exact canonicalFinsetList_toFinset_primrec.comp
    (Primrec.list_map decodeDistributionData_primrec
      (entry_point_primrec.comp Primrec.snd))

theorem canonicalPointListOfCode_computable :
    Computable canonicalPointListOfCode :=
  canonicalPointListOfCode_primrec.to_comp

/-- A canonical uniform-set code decodes to the canonical enumeration of that
set. -/
@[simp] theorem canonicalPointListOfCode_codedUniformOn
    (S : Finset BitString) (hS : S.Nonempty) :
    canonicalPointListOfCode (codedUniformOn S hS).code =
      canonicalFinsetList S := by
  unfold canonicalPointListOfCode
  rw [dataPoints_codedUniformOn, canonicalFinsetList_toFinset]

/-- Run the varying program over the input list and canonically encode the
finite set of outputs. -/
noncomputable def totalProgramImageCode
    (D : Map) : BitString × List BitString →. BitString :=
  fun input =>
    (totalProgramMapList D input).map canonicalImageCodeOfList

/-- The image-code transformer is partial recursive uniformly in both the
program and the finite input list. -/
theorem totalProgramImageCode_partrec
    (D : Map) (hD : isDecompressor D) :
    Partrec (totalProgramImageCode D) := by
  exact Partrec.map (totalProgramMapList_partrec D hD)
    (canonicalImageCodeOfList_computable.comp Computable.snd)

/-- A program total on every context makes the image-code transformer halt on
every finite input list. -/
theorem totalProgramImageCode_dom_of_total
    {D : Map} {p : BitString}
    (hp : IsTotalProgram D p) (xs : List BitString) :
    (totalProgramImageCode D (p, xs)).Dom := by
  rw [Part.dom_iff_mem]
  obtain ⟨ys, hys⟩ :=
    Part.dom_iff_mem.mp (totalProgramMapList_dom_of_total hp xs)
  exact ⟨canonicalImageCodeOfList ys,
    (Part.mem_map_iff _).2 ⟨ys, hys, rfl⟩⟩

/-- Code-to-code form of the image transformer.  Its first argument is the
varying program; its context is a finite-set code. -/
noncomputable def totalProgramImageCodeFromSetCode (D : Map) : Map :=
  fun input =>
    totalProgramImageCode D
      (input.1, canonicalPointListOfCode input.2)

/-- The code-to-code image transformer is a decompressor whenever `D` is. -/
theorem totalProgramImageCodeFromSetCode_partrec
    (D : Map) (hD : isDecompressor D) :
    isDecompressor (totalProgramImageCodeFromSetCode D) := by
  unfold totalProgramImageCodeFromSetCode
  exact Partrec.comp (totalProgramImageCode_partrec D hD)
    (Computable.pair Computable.fst
      (canonicalPointListOfCode_computable.comp Computable.snd))

/-- A program total for `D` remains total when acting on canonical finite-set
codes through the uniform image transformer. -/
theorem IsTotalProgram.imageSetCode
    {D : Map} {p : BitString} (hp : IsTotalProgram D p) :
    IsTotalProgram (totalProgramImageCodeFromSetCode D) p := by
  intro w
  exact totalProgramImageCode_dom_of_total hp
    (canonicalPointListOfCode w)

private lemma forall₂_exists_right_of_mem
    {R : α → β → Prop} {xs : List α} {ys : List β}
    (hrel : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, R x y := by
  induction hrel with
  | nil => simp at hx
  | @cons x' y' xs' ys' hxy htail ih =>
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨y', List.mem_cons_self, hxy⟩
      · obtain ⟨y, hy, hR⟩ := ih hx
        exact ⟨y, List.mem_cons_of_mem y' hy, hR⟩

private lemma forall₂_exists_left_of_mem
    {R : α → β → Prop} {xs : List α} {ys : List β}
    (hrel : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, R x y := by
  induction hrel with
  | nil => simp at hy
  | @cons x' y' xs' ys' hxy htail ih =>
      rw [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨x', List.mem_cons_self, hxy⟩
      · obtain ⟨x, hx, hR⟩ := ih hy
        exact ⟨x, List.mem_cons_of_mem x' hx, hR⟩

/-- Exact canonical finite-set image construction.

For a nonempty input finite set `S` and a program total on every context, the
executor produces a nonempty finite set `B`.  Its canonical code is produced by
the uniform image transformer, every member of `S` has its program output in
`B`, every member of `B` comes from `S`, and `|B| ≤ |S|`.
-/
theorem exists_totalProgramCanonicalImage
    {D : Map} {p : BitString}
    (hp : IsTotalProgram D p)
    (S : Finset BitString) (hS : S.Nonempty) :
    ∃ (ys : List BitString) (hB : ys.toFinset.Nonempty),
      ys ∈ totalProgramMapList D (p, canonicalFinsetList S) ∧
      (codedUniformOn ys.toFinset hB).code ∈
        totalProgramImageCode D (p, canonicalFinsetList S) ∧
      (∀ x ∈ S, ∃ y ∈ ys.toFinset, produces D p x y) ∧
      (∀ y ∈ ys.toFinset, ∃ x ∈ S, produces D p x y) ∧
      ys.toFinset.card ≤ S.card := by
  obtain ⟨ys, hys⟩ :=
    Part.dom_iff_mem.mp
      (totalProgramMapList_dom_of_total hp (canonicalFinsetList S))
  have hcanonical_ne : canonicalFinsetList S ≠ [] := by
    intro hnil
    have : S = ∅ := by
      rw [← canonicalFinsetList_toFinset S, hnil]
      rfl
    exact hS.ne_empty this
  have hB : ys.toFinset.Nonempty :=
    totalProgramMapList_result_nonempty hcanonical_ne hys
  have hrel :
      List.Forall₂ (fun x y => produces D p x y)
        (canonicalFinsetList S) ys :=
    totalProgramMapList_correct hys
  refine ⟨ys, hB, hys, ?_, ?_, ?_, ?_⟩
  · exact (Part.mem_map_iff _).2
      ⟨ys, hys, canonicalImageCodeOfList_eq_codedUniformOn ys hB⟩
  · intro x hx
    obtain ⟨y, hy, hprod⟩ :=
      forall₂_exists_right_of_mem hrel (mem_canonicalFinsetList.mpr hx)
    exact ⟨y, List.mem_toFinset.mpr hy, hprod⟩
  · intro y hy
    obtain ⟨x, hx, hprod⟩ :=
      forall₂_exists_left_of_mem hrel (List.mem_toFinset.mp hy)
    exact ⟨x, mem_canonicalFinsetList.mp hx, hprod⟩
  · simpa using totalProgramMapList_result_card_le
      (canonicalFinsetList_nodup S) hys

/-- Code-to-code specialization of `exists_totalProgramCanonicalImage`.
The produced output is the canonical code of the exact finite image of `S`. -/
theorem exists_totalProgramCanonicalImage_from_code
    {D : Map} {p : BitString}
    (hp : IsTotalProgram D p)
    (S : Finset BitString) (hS : S.Nonempty) :
    ∃ (ys : List BitString) (hB : ys.toFinset.Nonempty),
      produces (totalProgramImageCodeFromSetCode D) p
        (codedUniformOn S hS).code
        (codedUniformOn ys.toFinset hB).code ∧
      (∀ x ∈ S, ∃ y ∈ ys.toFinset, produces D p x y) ∧
      (∀ y ∈ ys.toFinset, ∃ x ∈ S, produces D p x y) ∧
      ys.toFinset.card ≤ S.card := by
  obtain ⟨ys, hB, _hys, hcode, hforward, hbackward, hcard⟩ :=
    exists_totalProgramCanonicalImage hp S hS
  refine ⟨ys, hB, ?_, hforward, hbackward, hcard⟩
  change (codedUniformOn ys.toFinset hB).code ∈
    totalProgramImageCode D
      (p, canonicalPointListOfCode (codedUniformOn S hS).code)
  rw [canonicalPointListOfCode_codedUniformOn]
  exact hcode

/-- Under an optimal total machine, applying a total program to every member
of a finite set yields a canonical image-set code with the program's length
plus a uniform additive overhead. -/
theorem totalCondK_canonicalImage_le
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ {p : BitString},
      IsTotalProgram T p →
      ∀ (S : Finset BitString) (hS : S.Nonempty),
      ∃ (B : Finset BitString) (hB : B.Nonempty),
        (∀ x ∈ S, ∃ y ∈ B, produces T p x y) ∧
        (∀ y ∈ B, ∃ x ∈ S, produces T p x y) ∧
        B.card ≤ S.card ∧
        totalCondK T (codedUniformOn B hB).code
          (codedUniformOn S hS).code ≤
            (programLength p : ENat) + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    hT.2 (totalProgramImageCodeFromSetCode T)
      (totalProgramImageCodeFromSetCode_partrec T hT.1)
  refine ⟨c, ?_⟩
  intro p hp S hS
  obtain ⟨ys, hB, hprod, hforward, hbackward, hcard⟩ :=
    exists_totalProgramCanonicalImage_from_code hp S hS
  refine ⟨ys.toFinset, hB, hforward, hbackward, hcard, ?_⟩
  calc
    totalCondK T (codedUniformOn ys.toFinset hB).code
        (codedUniformOn S hS).code
        ≤ totalCondK (totalProgramImageCodeFromSetCode T)
            (codedUniformOn ys.toFinset hB).code
            (codedUniformOn S hS).code + (c : ENat) :=
      hc _ _
    _ ≤ (programLength p : ENat) + (c : ENat) := by
      gcongr
      exact totalCondK_le_programLength hp.imageSetCode hprod

end Kolmogorov
