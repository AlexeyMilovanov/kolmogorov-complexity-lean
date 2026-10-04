import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift

/-!
# Filtered family step

Executable filtered enumeration: intersections of decoded canonical point lists used in
the family step of the strong-models construction.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-! ### Executable filtered enumeration -/

/-- Intersection of the two decoded canonical point lists, kept as a list in
the order of the first code. -/
noncomputable def partitionIntersectionPointList
    (Acode Mcode : BitString) : List BitString :=
  (canonicalPointListOfCode Acode).filter
    (fun x => decide (x ∈ canonicalPointListOfCode Mcode))

/-- Listing the common points of two coded finite sets is primitive recursive. -/
theorem partitionIntersectionPointList_primrec :
    Primrec₂ partitionIntersectionPointList := by
  unfold partitionIntersectionPointList
  refine list_filter_primrec
    (canonicalPointListOfCode_primrec.comp Primrec.fst) ?_
  have hpred : Primrec₂
      (fun (input : BitString × BitString) (x : BitString) =>
        decide (x ∈ canonicalPointListOfCode input.2)) := by
    have hx : Primrec
        (fun q : (BitString × BitString) × BitString => q.2) :=
      Primrec.snd
    have hm : Primrec
        (fun q : (BitString × BitString) × BitString => q.1.2) :=
      Primrec.snd.comp Primrec.fst
    exact (bitString_mem_primrec.comp hx
      (canonicalPointListOfCode_primrec.comp hm)).to₂
  exact hpred

/-- Boolean form of `0 < m ∧ r ≤ Nat.clog 2 m`, expressed without computing
`Nat.clog`. -/
def largeIntersectionBool (m r : Nat) : Bool :=
  decide (0 < m ∧ (r = 0 ∨ 2 ^ (r - 1) < m))

/-- The largeness test succeeds exactly when `m` is positive and `r ≤ clog 2 m`. -/
theorem largeIntersectionBool_iff (m r : Nat) :
    largeIntersectionBool m r = true ↔
      0 < m ∧ r ≤ Nat.clog 2 m := by
  unfold largeIntersectionBool
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hm, hr0 | hpow⟩
    · subst hr0
      exact ⟨hm, Nat.zero_le _⟩
    · exact ⟨hm, by
        have := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hpow
        omega⟩
  · rintro ⟨hm, hr⟩
    by_cases hr0 : r = 0
    · exact ⟨hm, Or.inl hr0⟩
    · refine ⟨hm, Or.inr ?_⟩
      exact (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by omega)

/-- The largeness test is primitive recursive in its two arguments. -/
theorem largeIntersectionBool_primrec :
    Primrec₂ largeIntersectionBool := by
  have h : PrimrecPred (fun p : Nat × Nat =>
      0 < p.1 ∧ (p.2 = 0 ∨ 2 ^ (p.2 - 1) < p.1)) :=
    PrimrecPred.and
      (Primrec.nat_lt.comp (Primrec.const 0) Primrec.fst)
      (PrimrecPred.or
        (Primrec.eq.comp Primrec.snd (Primrec.const 0))
        (Primrec.nat_lt.comp
          (primrec_two_pow_aux.comp
            (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
          Primrec.fst))
  exact h.decide

/-- Canonical member codes of the decoded partition whose decoded sets have a
large nonempty intersection with the decoded context set. -/
noncomputable def partitionIntersectionCandidates
    (input : (BitString × BitString) × Nat) : List BitString :=
  (canonicalPointListOfCode input.1.1).filter fun Mcode =>
    largeIntersectionBool
      (partitionIntersectionPointList input.1.2 Mcode).length input.2

/-- Listing the partition members with a large enough intersection is primitive
recursive. -/
theorem partitionIntersectionCandidates_primrec :
    Primrec partitionIntersectionCandidates := by
  unfold partitionIntersectionCandidates
  refine list_filter_primrec
    (canonicalPointListOfCode_primrec.comp
      (Primrec.fst.comp Primrec.fst)) ?_
  exact largeIntersectionBool_primrec.comp
    (Primrec.list_length.comp
      (partitionIntersectionPointList_primrec.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd))
    (Primrec.snd.comp Primrec.fst)

/-- On canonical codes the point list of the intersection is exactly `A ∩ M`. -/
theorem partitionIntersectionPointList_toFinset
    (A M : Finset BitString) (hA : A.Nonempty) (hM : M.Nonempty) :
    (partitionIntersectionPointList (codedUniformOn A hA).code
      (codedUniformOn M hM).code).toFinset = A ∩ M := by
  ext x
  simp [partitionIntersectionPointList,
    canonicalPointListOfCode_codedUniformOn, mem_canonicalFinsetList]

/-! ### Total selector -/

/-- Post-composition selecting, from a partition code and a model code, the
candidate of the requested index and threshold. -/
noncomputable def partitionIntersectionSelectorPostFn
    (input : BitString × BitString) (Pcode : BitString) : BitString :=
  let params := decodeTotalProgramPairSecond input.1
  let r := decodeBits (decodeTotalProgramPairFirst params)
  let idx := bitsToNat (decodeTotalProgramPairSecond params)
  (partitionIntersectionCandidates ((Pcode, input.2), r)).getD idx
    (canonicalFiniteSetCode ∅)

/-- That selection is computable. -/
theorem partitionIntersectionSelectorPostFn_computable :
    Computable₂ partitionIntersectionSelectorPostFn := by
  unfold partitionIntersectionSelectorPostFn
  have hcand : Computable
      (fun q : (BitString × BitString) × BitString =>
        partitionIntersectionCandidates
          ((q.2, q.1.2), decodeBits
            (decodeTotalProgramPairFirst
              (decodeTotalProgramPairSecond q.1.1)))) :=
    partitionIntersectionCandidates_primrec.to_comp.comp
      ((Computable.snd.pair (Computable.snd.comp Computable.fst)).pair
        (decodeBits_computable.comp
          (decodeTotalProgramPairFirst_computable.comp
            (decodeTotalProgramPairSecond_computable.comp
              (Computable.fst.comp Computable.fst)))))
  have hidx : Computable
      (fun q : (BitString × BitString) × BitString =>
        bitsToNat (decodeTotalProgramPairSecond
          (decodeTotalProgramPairSecond q.1.1))) :=
    bitsToNat_primrec.to_comp.comp
      (decodeTotalProgramPairSecond_computable.comp
        (decodeTotalProgramPairSecond_computable.comp
          (Computable.fst.comp Computable.fst)))
  exact (Primrec.list_getD (canonicalFiniteSetCode ∅)).to_comp.comp
    hcand hidx

/-- Run an ordinary description of a partition at empty context, then select a
large-intersection member by threshold and fixed-width ordinal. -/
noncomputable def partitionIntersectionSelector (V : Map) : Map := fun input =>
  (V (decodeTotalProgramPairFirst input.1, [])).map
    (partitionIntersectionSelectorPostFn input)

/-- The intersection selector is a decompressor. -/
theorem partitionIntersectionSelector_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (partitionIntersectionSelector V) := by
  unfold partitionIntersectionSelector
  exact Partrec.map
    (Partrec.comp hV
      (Computable.pair
        (decodeTotalProgramPairFirst_computable.comp Computable.fst)
        (Computable.const [])))
    partitionIntersectionSelectorPostFn_computable

/-- A program producing a partition code, paired with any parameters, is total in
the intersection selector. -/
theorem partitionIntersectionSelector_total
    {V : Map} {q Pcode params : BitString}
    (hq : produces V q [] Pcode) :
    IsTotalProgram (partitionIntersectionSelector V)
      (totalProgramPairCode q params) := by
  intro Acode
  unfold partitionIntersectionSelector
  rw [decodeTotalProgramPairFirst_pair, Part.dom_iff_mem]
  exact ⟨partitionIntersectionSelectorPostFn
      (totalProgramPairCode q params, Acode) Pcode,
    (Part.mem_map_iff _).2 ⟨Pcode, hq, rfl⟩⟩

/-! ### The filtered family used in the next hereditary step -/

/-- Canonical codes of the partition members whose intersections with `M` are
nonempty and have ceiling log-cardinality at least `r`. -/
noncomputable def hereditaryFamily
    (P : Finset (Finset BitString)) (M : Finset BitString) (r : Nat) :
    Finset BitString :=
  (P.filter fun A => (A ∩ M).Nonempty ∧
    r ≤ finiteSetLogCard (A ∩ M)).image canonicalFiniteSetCode

/-- The distinguished partition member belongs to the filtered family at its
own intersection threshold. -/
theorem hereditaryFamily_mem_code
    (P : Finset (Finset BitString)) (A M : Finset BitString)
    (hA : A.Nonempty) (hAP : A ∈ P) (hinter : (A ∩ M).Nonempty) :
    (codedUniformOn A hA).code ∈
      hereditaryFamily P M (finiteSetLogCard (A ∩ M)) := by
  have hcode : canonicalFiniteSetCode A = (codedUniformOn A hA).code :=
    canonicalUniformCodeOfList_canonicalFinsetList A hA
  rw [← hcode, hereditaryFamily, Finset.mem_image]
  exact ⟨A, by simp [hAP, hinter], rfl⟩

/-- Canonical code of the executable filtered family. -/
noncomputable def hereditaryFamilyCode
    (input : (BitString × BitString) × Nat) : BitString :=
  canonicalImageCodeOfList (partitionIntersectionCandidates input)

/-- The canonical code of the filtered family is computable in its input. -/
theorem hereditaryFamilyCode_computable :
    Computable hereditaryFamilyCode :=
  (canonicalImageCodeOfList_primrec.comp
    partitionIntersectionCandidates_primrec).to_comp

/-! ### Coefficient-one plain-complexity bound -/

/-- The partition program and threshold are framed in a prefix, while the
shortest program for `M` is left as the suffix. -/
noncomputable def hereditaryFamilyPlainDecompressor (V : Map) : Map :=
  fun input =>
    let params := decodeTotalProgramPairSecond input.1
    (V (decodeSecond params, [])).bind fun Mcode =>
      (V (decodeTotalProgramPairFirst input.1, [])).map fun Pcode =>
        hereditaryFamilyCode
          ((Pcode, Mcode), bitsToNat (decodeFirst params))

/-- The plain-complexity decompressor for the filtered family is a decompressor. -/
theorem hereditaryFamilyPlainDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (hereditaryFamilyPlainDecompressor V) := by
  have hrunM : Partrec (fun input : BitString × BitString =>
      V (decodeSecond (decodeTotalProgramPairSecond input.1), [])) :=
    Partrec.comp hV
      (Computable.pair
        (decodeSecond_computable.comp
          (decodeTotalProgramPairSecond_computable.comp Computable.fst))
        (Computable.const []))
  have hrunP : Partrec (fun q : (BitString × BitString) × BitString =>
      V (decodeTotalProgramPairFirst q.1.1, [])) :=
    Partrec.comp hV
      (Computable.pair
        (decodeTotalProgramPairFirst_computable.comp
          (Computable.fst.comp Computable.fst))
        (Computable.const []))
  have hpost : Computable
      (fun q : ((BitString × BitString) × BitString) × BitString =>
        hereditaryFamilyCode
          ((q.2, q.1.2), bitsToNat
            (decodeFirst (decodeTotalProgramPairSecond q.1.1.1)))) :=
    hereditaryFamilyCode_computable.comp
      ((Computable.snd.pair (Computable.snd.comp Computable.fst)).pair
        (bitsToNat_computable.comp
          (decodeFirst_computable.comp
            (decodeTotalProgramPairSecond_computable.comp
              (Computable.fst.comp
                (Computable.fst.comp Computable.fst))))))
  unfold hereditaryFamilyPlainDecompressor
  exact Partrec.bind hrunM (Partrec.map hrunP hpost)

/-- From programs for the partition code and for the model code, the decompressor
produces the code of the filtered family at the threshold `r`. -/
theorem hereditaryFamilyPlainDecompressor_produces
    {V : Map} {q m Pcode Mcode : BitString} {r : Nat}
    (hP : produces V q [] Pcode) (hM : produces V m [] Mcode) :
    produces (hereditaryFamilyPlainDecompressor V)
      (totalProgramPairCode q (pairCode (Nat.bits r) m)) []
      (hereditaryFamilyCode ((Pcode, Mcode), r)) := by
  unfold produces hereditaryFamilyPlainDecompressor
  simp only [decodeTotalProgramPairSecond_pair, decodeSecond_pairCode,
    decodeTotalProgramPairFirst_pair, decodeFirst_pairCode, bitsToNat_bits]
  rw [Part.mem_bind_iff]
  refine ⟨Mcode, hM, ?_⟩
  exact (Part.mem_map_iff _).2 ⟨Pcode, hP, rfl⟩

/-- Generic coefficient-one code bound.  No self-delimiting framing is charged
to the shortest `M` program. -/
theorem plainK_hereditaryFamilyCode_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ q Pcode Mcode r,
      produces V q [] Pcode →
      plainK V (hereditaryFamilyCode ((Pcode, Mcode), r)) ≤
        plainK V Mcode +
          (c * q.length + logSlack c r : ENat) := by
  obtain ⟨cSim, hSim⟩ := hV.2 (hereditaryFamilyPlainDecompressor V)
    (hereditaryFamilyPlainDecompressor_partrec V hV.1)
  let c := cSim + 6
  refine ⟨c, ?_⟩
  intro q Pcode Mcode r hP
  let overhead := q.length + 2 * (Nat.bits q.length).length +
    2 * (Nat.bits r).length + 2
  have hbound : condK (hereditaryFamilyPlainDecompressor V)
      (hereditaryFamilyCode ((Pcode, Mcode), r)) [] ≤
      condK V Mcode [] + (overhead : ENat) := by
    apply sInfLeSInfAdd
    rintro len ⟨m, hm, rfl⟩
    let w := totalProgramPairCode q (pairCode (Nat.bits r) m)
    refine ⟨(w.length : ENat),
      ⟨w, hereditaryFamilyPlainDecompressor_produces hP hm, rfl⟩, ?_⟩
    have hw : w.length = m.length + overhead := by
      dsimp [w, overhead]
      rw [length_totalProgramPairCode, length_pairCode]
      omega
    exact_mod_cast le_of_eq hw
  have hqBits : (Nat.bits q.length).length ≤ q.length :=
    length_natBits_le _
  have hoverhead : overhead + cSim ≤
      c * q.length + logSlack c r := by
    dsimp [overhead, c]
    unfold logSlack
    nlinarith [Nat.zero_le (cSim * q.length),
      Nat.zero_le (cSim * (Nat.bits r).length)]
  calc
    plainK V (hereditaryFamilyCode ((Pcode, Mcode), r)) ≤
        condK (hereditaryFamilyPlainDecompressor V)
          (hereditaryFamilyCode ((Pcode, Mcode), r)) [] +
          (cSim : ENat) := hSim _ _
    _ ≤ (condK V Mcode [] + (overhead : ENat)) +
        (cSim : ENat) := by gcongr
    _ = plainK V Mcode + ((overhead + cSim : Nat) : ENat) := by
      rw [add_assoc]
      norm_cast
    _ ≤ plainK V Mcode +
        ((c * q.length + logSlack c r : Nat) : ENat) := by
      have hcast : ((overhead + cSim : Nat) : ENat) ≤
          ((c * q.length + logSlack c r : Nat) : ENat) := by
        exact_mod_cast hoverhead
      exact add_le_add_right hcast _
    _ = plainK V Mcode +
        (c * q.length + logSlack c r : ENat) := by norm_cast

/-! ### Total strongness transport -/

/-- Executable ceiling-log search.  The range `0, ..., m` contains
`Nat.clog 2 m`, and `clogEqBool` recognizes it uniquely. -/
def clogSearch (m : Nat) : Nat :=
  (List.range (m + 1)).findIdx (fun r => clogEqBool m r)

/-- The executable ceiling binary logarithm is primitive recursive. -/
theorem clogSearch_primrec : Primrec clogSearch := by
  have hrange : Primrec (fun m : Nat => List.range (m + 1)) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
  exact Primrec.list_findIdx hrange clogEqBool_primrec

/-- The executable search computes `Nat.clog 2`. -/
theorem clogSearch_eq (m : Nat) : clogSearch m = Nat.clog 2 m := by
  have hk : Nat.clog 2 m ≤ m :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have hfind : clogSearch m < (List.range (m + 1)).length := by
    unfold clogSearch
    rw [List.findIdx_lt_length]
    exact ⟨Nat.clog 2 m, by simp [hk],
      (clogEqBool_iff m (Nat.clog 2 m)).2 rfl⟩
  have hget := List.findIdx_getElem
    (p := fun r => clogEqBool m r)
    (xs := List.range (m + 1)) (w := hfind)
  have hp : clogEqBool m (clogSearch m) = true := by
    change clogEqBool m ((List.range (m + 1))[clogSearch m]) = true at hget
    rw [List.getElem_range hfind] at hget
    exact hget
  exact ((clogEqBool_iff m (clogSearch m)).1 hp).symm

/-- Ceiling log-cardinality of the intersection decoded from two canonical
finite-set codes. -/
noncomputable def intersectionLogFromCodes
    (Acode Mcode : BitString) : Nat :=
  clogSearch (partitionIntersectionPointList Acode Mcode).length

/-- The log-cardinality of the intersection of two coded sets is primitive recursive
in the two codes. -/
theorem intersectionLogFromCodes_primrec :
    Primrec₂ intersectionLogFromCodes :=
  clogSearch_primrec.comp
    (Primrec.list_length.comp partitionIntersectionPointList_primrec)

end Kolmogorov
