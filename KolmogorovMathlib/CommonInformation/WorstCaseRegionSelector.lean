import KolmogorovMathlib.CommonInformation.WorstCaseRegionSearch
import KolmogorovMathlib.CommonInformation.WorstCaseSelector

/-!
# The selector of the region construction

`muchnikRegionSelector` searches, given `n` and the advice count, for a candidate pair that no
admissible triple serves, and returns the first one found good at the stage at which the
enumerations have produced the advised number of objects.  `muchnikRegionSelector_partrec`
makes it partial recursive and `muchnikRegionSelector_spec` says what it returns: the code of
a survivor pair.

Its test is `muchnikRegionSelectorGoodAtStage`, with
`muchnikRegionSelectorGoodAtStage_eq_true_iff` and `…_primrec`, built on the witness search of
`WorstCaseRegionSearch`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- The test the selector applies to a candidate at a stage: the candidate must not have been
marked bad at that stage. -/
def muchnikRegionSelectorGoodAtStage
    (c : Code) (input : BitString) (t : Nat) (w : BitString) : Bool :=
  !muchnikRegionBadAtStage c (muchnikSelectorN input) t w

/-- The selector's test succeeds exactly when the candidate is not bad at that stage. -/
theorem muchnikRegionSelectorGoodAtStage_eq_true_iff
    (c : Code) (input : BitString) (t : Nat) (w : BitString) :
    muchnikRegionSelectorGoodAtStage c input t w = true ↔
      muchnikRegionBadAtStage c (muchnikSelectorN input) t w = false := by
  unfold muchnikRegionSelectorGoodAtStage
  cases muchnikRegionBadAtStage c (muchnikSelectorN input) t w <;> simp

/-- The selector's test is primitive recursive. -/
theorem muchnikRegionSelectorGoodAtStage_primrec (c : Code) :
    Primrec (fun q : (BitString × Nat) × BitString =>
      muchnikRegionSelectorGoodAtStage c q.1.1 q.1.2 q.2) := by
  let f : ((BitString × Nat) × BitString) →
      ((Nat × Nat) × BitString) :=
    fun q => ((muchnikSelectorN q.1.1, q.1.2), q.2)
  have hf : Primrec f :=
    Primrec.pair
      (Primrec.pair
        (muchnikSelectorN_primrec.comp
          (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  have hbad : Primrec (fun q =>
      muchnikRegionBadAtStage c
        (f q).1.1 (f q).1.2 (f q).2) :=
    (muchnikRegionBadAtStage_primrec c).comp hf
  exact (Primrec.not.comp hbad).of_eq (fun q => by
    simp only [muchnikRegionSelectorGoodAtStage, f])

/-- The partial computable selector that, given `n` and the advice count, searches for a survivor
pair of the region construction. -/
noncomputable def muchnikRegionSelector (c : Code) : BitString → Part BitString := fun input =>
  let n := muchnikSelectorN input
  let total := muchnikSelectorTotal input
  (Nat.rfind (fun t =>
    Part.some (muchnikRegionMergedStageCount c n t == total))).bind fun t =>
      Part.ofOption
        ((muchnikSelectorCandidates input).find?
          (muchnikRegionSelectorGoodAtStage c input t))

/-- The selector returns the first candidate found good at the stage at which the enumeration is
complete. -/
theorem muchnikRegionSelector_eq_some_of_search
    (c : Code) (input : BitString) (t : Nat) (w : BitString)
    (ht : t ∈ Nat.rfind (fun s =>
      Part.some (muchnikRegionMergedStageCount c (muchnikSelectorN input) s ==
        muchnikSelectorTotal input)))
    (hw : (muchnikSelectorCandidates input).find?
      (muchnikRegionSelectorGoodAtStage c input t) = some w) :
    muchnikRegionSelector c input = Part.some w := by
  apply Part.eq_some_iff.mpr
  unfold muchnikRegionSelector
  rw [Part.mem_bind_iff]
  refine ⟨t, ht, ?_⟩
  rw [hw]
  exact Part.mem_some w

/-- The selector is partial recursive. -/
theorem muchnikRegionSelector_partrec (c : Code) : Partrec (muchnikRegionSelector c) := by
  let countInput : BitString × Nat → Nat × Nat :=
    fun st => (muchnikSelectorN st.1, st.2)
  have hCountInput : Computable countInput :=
    (muchnikSelectorN_primrec.to_comp.comp
      Computable.fst).pair Computable.snd
  have hCount : Computable (fun st : BitString × Nat =>
      muchnikRegionMergedStageCount c
        (muchnikSelectorN st.1) st.2) :=
    ((muchnikRegionMergedStageCount_computable c).comp
      hCountInput).of_eq (fun _ => rfl)
  have hCheck : Computable₂
      (fun (input : BitString) (t : Nat) =>
        muchnikRegionMergedStageCount c
          (muchnikSelectorN input) t ==
            muchnikSelectorTotal input) :=
    (Primrec.beq.to_comp.comp
      hCount
      (muchnikSelectorTotal_primrec.to_comp.comp
        Computable.fst)).to₂
  have hSearch : Partrec (fun input : BitString =>
      Nat.rfind (fun t =>
        Part.some (muchnikRegionMergedStageCount c
          (muchnikSelectorN input) t ==
            muchnikSelectorTotal input))) :=
    Partrec.rfind hCheck.partrec₂
  have hFind : Primrec (fun st : BitString × Nat =>
      (muchnikSelectorCandidates st.1).find?
        (muchnikRegionSelectorGoodAtStage c st.1 st.2)) :=
    list_find?_primrec
      (muchnikSelectorCandidates_primrec.comp Primrec.fst)
      (muchnikRegionSelectorGoodAtStage_primrec c).to₂
  have hPost : Partrec₂
      (fun (input : BitString) (t : Nat) =>
        Part.ofOption
          ((muchnikSelectorCandidates input).find?
            (muchnikRegionSelectorGoodAtStage c input t))) :=
    hFind.to_comp.ofOption.to₂
  unfold muchnikRegionSelector
  exact Partrec.bind hSearch hPost

/-- Given `n` and the advice count, the selector returns the code of a survivor pair of the
region construction. -/
theorem muchnikRegionSelector_spec
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n : Nat} (hn : 0 < n) :
    ∃ x y,
      muchnikRegionSelector c
        (pairCode (Nat.bits n)
          (Nat.bits (muchnikRegionAdviceCount V n))) =
        Part.some (pairCode x y) ∧
      IsMuchnikRegionSurvivor V n x y := by
  let input :=
    pairCode (Nat.bits n)
      (Nat.bits (muchnikRegionAdviceCount V n))
  have hInputN : muchnikSelectorN input = n := by
    simp only [muchnikSelectorN, input,
      decodeFirst_pairCode, bitsToNat_bits]
  have hInputTotal :
      muchnikSelectorTotal input =
        muchnikRegionAdviceCount V n := by
    simp only [muchnikSelectorTotal, input,
      decodeSecond_pairCode, bitsToNat_bits]
  let hex : ∃ t,
      muchnikRegionMergedStageCount c n t =
        muchnikRegionAdviceCount V n :=
    exists_muchnikRegionMergedStageCount_eq hc n
  let t₀ := Nat.find hex
  have ht₀Count :
      muchnikRegionMergedStageCount c n t₀ =
        muchnikRegionAdviceCount V n :=
    Nat.find_spec hex
  have ht₀Search :
      t₀ ∈ Nat.rfind (fun t =>
        Part.some (muchnikRegionMergedStageCount c
          (muchnikSelectorN input) t ==
            muchnikSelectorTotal input)) := by
    simp only [hInputN, hInputTotal]
    rw [@Nat.mem_rfind
      ((fun t : ℕ => Part.some
        (muchnikRegionMergedStageCount c n t ==
          muchnikRegionAdviceCount V n)) : ℕ →. Bool)
      t₀]
    refine ⟨?_, ?_⟩
    · simp [ht₀Count]
    · intro m hm
      have hne :
          muchnikRegionMergedStageCount c n m ≠
            muchnikRegionAdviceCount V n :=
        Nat.find_min hex hm
      simp [hne]
  obtain ⟨w, hwFindDirect, hSurvivor⟩ :=
    muchnikRegionFindAtStage_spec hc hn ht₀Count
  have hwFind :
      (muchnikSelectorCandidates input).find?
        (muchnikRegionSelectorGoodAtStage c input t₀) =
          some w := by
    unfold muchnikSelectorCandidates
      muchnikRegionSelectorGoodAtStage
    rw [hInputN]
    exact hwFindDirect
  have hwCandidates :
      w ∈ fixedLengthPairCodes (2 * n + 2) :=
    List.mem_of_find?_eq_some hwFindDirect
  obtain ⟨x, y, _hxLength, _hyLength, hwPair⟩ :=
    (mem_fixedLengthPairCodes_iff
      (2 * n + 2) w).mp hwCandidates
  subst w
  exact ⟨x, y,
    muchnikRegionSelector_eq_some_of_search
      c input t₀ (pairCode x y) ht₀Search hwFind,
    by
      simpa only [decodeFirst_pairCode,
        decodeSecond_pairCode] using hSurvivor⟩

end Kolmogorov
