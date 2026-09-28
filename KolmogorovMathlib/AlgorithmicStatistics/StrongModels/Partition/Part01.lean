import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionShift

/-!
# Partitions and description chunks

The apparatus behind Proposition `part`, which relates strong models to partitions.

`IsPartition` is pairwise disjointness; `canonicalFiniteSetCode`, `partitionCode` and
`partitionComplexity` are the canonical codings of a finite set and of a partition.
`partitionMemberCode` looks up the part containing a point — primitive recursive
(`partitionMemberCode_primrec`) and correct on genuine partitions
(`partitionMemberCode_eq_of_mem`) — and `partitionMemberDecompressor` post-composes that
lookup with a decompressor, so a program for the partition code also describes the part.

The second half cuts a model into exact-size chunks: `strongDescriptionChunkCode` computes the
chunk containing `x` from a model code and a fixed-width address, and
`strongDescriptionChunkDecompressor` (with its plain counterpart
`plainDescriptionChunkDecompressor` and the advice framing `plainAdviceCode`) turns a program
for the model into a program for the chunk.  The converse construction is in
`Partition/Converse`.
-/



namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- A family of sets is a partition if its members are pairwise disjoint. -/
def IsPartition (A : Finset (Finset BitString)) : Prop :=
  ∀ B ∈ A, ∀ C ∈ A, B ≠ C → Disjoint B C

/-- Canonical code of a finite set.  For nonempty sets this is definitionally
the repository's canonical uniform-model code; keeping the list encoder here
also gives a deterministic syntactic code for the empty set. -/
noncomputable def canonicalFiniteSetCode (S : Finset BitString) : BitString :=
  canonicalUniformCodeOfList (canonicalFinsetList S)

/-- The canonical code of a partition, obtained by encoding the list of canonical codes
of its member sets. -/
noncomputable def partitionCode (A : Finset (Finset BitString)) : BitString :=
  canonicalFiniteSetCode (A.image canonicalFiniteSetCode)

/-- The complexity of a partition is the ordinary plain complexity of its canonical code. -/
noncomputable def partitionComplexity (U : Map) (A : Finset (Finset BitString)) : ENat :=
  plainK U (partitionCode A)

/-- Canonical finite-set codes decode back to the canonical point list, including
the empty-set syntactic code. -/
@[simp] theorem canonicalPointListOfCode_canonicalFiniteSetCode
    (S : Finset BitString) :
    canonicalPointListOfCode (canonicalFiniteSetCode S) =
      canonicalFinsetList S := by
  unfold canonicalPointListOfCode canonicalFiniteSetCode
    canonicalUniformCodeOfList
  rw [decodeDistributionData_code]
  rw [List.map_map]
  change canonicalFinsetList
      (((canonicalFinsetList S).map id).toFinset) =
    canonicalFinsetList S
  rw [List.map_id, canonicalFinsetList_toFinset]

/-- Given a partition code and a point, return the first coded member containing
the point, or the canonical empty-set code if there is no such member. -/
noncomputable def partitionMemberCode
    (input : BitString × BitString) : BitString :=
  let codes := canonicalPointListOfCode input.1
  let idx := codes.findIdx fun w =>
    decide (input.2 ∈ canonicalPointListOfCode w)
  codes.getD idx (canonicalFiniteSetCode ∅)

/-- Locating the part of a coded partition that contains a given string is primitive
recursive. -/
theorem partitionMemberCode_primrec :
    Primrec partitionMemberCode := by
  let codes : BitString × BitString → List BitString :=
    fun input => canonicalPointListOfCode input.1
  have hcodes : Primrec codes :=
    canonicalPointListOfCode_primrec.comp Primrec.fst
  have hpred : Primrec₂
      (fun (input : BitString × BitString) (w : BitString) =>
        decide (input.2 ∈ canonicalPointListOfCode w)) := by
    exact (bitString_mem_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (canonicalPointListOfCode_primrec.comp Primrec.snd)).to₂
  have hidx : Primrec
      (fun input : BitString × BitString =>
        (codes input).findIdx fun w =>
          decide (input.2 ∈ canonicalPointListOfCode w)) :=
    Primrec.list_findIdx hcodes hpred
  exact (Primrec.list_getD (canonicalFiniteSetCode ∅)).comp
    hcodes hidx

/-- Locating the part containing a given string is computable. -/
theorem partitionMemberCode_computable :
    Computable partitionMemberCode :=
  partitionMemberCode_primrec.to_comp

/-- For a genuine partition, the lookup returns the canonical code of the part
containing the string. -/
theorem partitionMemberCode_eq_of_mem
    (A : Finset (Finset BitString)) (hA : IsPartition A)
    (S : Finset BitString) (hS : S ∈ A)
    (x : BitString) (hx : x ∈ S) :
    partitionMemberCode (partitionCode A, x) =
      canonicalFiniteSetCode S := by
  let codesSet := A.image canonicalFiniteSetCode
  let codes := canonicalFinsetList codesSet
  have hcodesSet : codesSet.Nonempty :=
    ⟨canonicalFiniteSetCode S, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩
  have hdecode :
      canonicalPointListOfCode (partitionCode A) = codes := by
    unfold partitionCode
    change canonicalPointListOfCode (canonicalFiniteSetCode codesSet) = codes
    exact canonicalPointListOfCode_canonicalFiniteSetCode codesSet
  have hScode : canonicalFiniteSetCode S ∈ codes := by
    rw [mem_canonicalFinsetList]
    exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
  let idx := codes.findIdx fun w =>
    decide (x ∈ canonicalPointListOfCode w)
  have hidx : idx < codes.length := by
    rw [List.findIdx_lt_length]
    exact ⟨canonicalFiniteSetCode S, hScode, by
      simp [canonicalPointListOfCode_canonicalFiniteSetCode, hx]⟩
  let selected := codes[idx]
  have hselected_mem : selected ∈ codes :=
    List.getElem_mem hidx
  have hselected_pred :
      decide (x ∈ canonicalPointListOfCode selected) = true := by
    exact List.findIdx_getElem (p := fun w =>
      decide (x ∈ canonicalPointListOfCode w)) (w := hidx)
  obtain ⟨R, hR, hRcode⟩ :
      ∃ R ∈ A, canonicalFiniteSetCode R = selected := by
    have : selected ∈ codesSet :=
      mem_canonicalFinsetList.mp hselected_mem
    simpa [codesSet] using (Finset.mem_image.mp this)
  have hxR : x ∈ R := by
    have : x ∈ canonicalPointListOfCode selected := by
      simpa using hselected_pred
    rw [← hRcode, canonicalPointListOfCode_canonicalFiniteSetCode,
      mem_canonicalFinsetList] at this
    exact this
  have hRS : R = S := by
    by_contra hne
    have hdisjoint := hA R hR S hS hne
    exact (Finset.disjoint_left.mp hdisjoint hxR hx)
  unfold partitionMemberCode
  rw [hdecode]
  change codes.getD idx (canonicalFiniteSetCode ∅) =
    canonicalFiniteSetCode S
  have hget : codes.getD idx (canonicalFiniteSetCode ∅) = selected := by
    simp [selected, List.getD_eq_getElem?_getD, hidx]
  rw [hget, ← hRcode, hRS]

/-- Run an ordinary plain description of a partition code and then select the
unique partition member containing the condition.  The ordinary program is run
at the fixed empty context, so every halting such program becomes total in the
varying point condition. -/
noncomputable def partitionMemberDecompressor (U : Map) : Map :=
  fun input =>
    (U (input.1, [])).map fun Pcode =>
      partitionMemberCode (Pcode, input.2)

/-- Post-composing a decompressor with the part lookup again gives a decompressor. -/
theorem partitionMemberDecompressor_partrec
    (U : Map) (hU : isDecompressor U) :
    isDecompressor (partitionMemberDecompressor U) := by
  exact Partrec.map
    (Partrec.comp hU
      (Computable.pair Computable.fst (Computable.const [])))
    (partitionMemberCode_computable.comp
      (Computable.snd.pair (Computable.snd.comp Computable.fst)))

/-- A program producing a partition code is total in the part-lookup decompressor. -/
theorem partitionMemberDecompressor_total
    {U : Map} {q Pcode : BitString}
    (hq : produces U q [] Pcode) :
    IsTotalProgram (partitionMemberDecompressor U) q := by
  intro x
  unfold partitionMemberDecompressor
  rw [Part.dom_iff_mem]
  exact ⟨partitionMemberCode (Pcode, x),
    (Part.mem_map_iff _).2 ⟨Pcode, hq, rfl⟩⟩

/-- A program producing a partition code produces, on the condition `x`, the code of
the part containing `x`. -/
theorem partitionMemberDecompressor_produces
    {U : Map} {q Pcode x : BitString}
    (hq : produces U q [] Pcode) :
    produces (partitionMemberDecompressor U) q x
      (partitionMemberCode (Pcode, x)) := by
  unfold partitionMemberDecompressor produces
  exact (Part.mem_map_iff _).2 ⟨Pcode, hq, rfl⟩

/-! ### Executable exact-size chunks

The existing `descriptionChunk S x (i + 1)` uses an `(i+1)`-bit address.  Under
`2^i ≤ |S|`, its `|S| / 2^(i+1) + 1` size is at most `|S| / 2^i`.  The extra
address bit is absorbed by the source's logarithmic slack and avoids any
divisibility assumption on `|S|`. -/

/-- Halving `i` times shrinks a description chunk by a factor `2 ^ i`: the chunk at
level `i + 1` has at most `|S| / 2 ^ i` elements. -/
theorem card_descriptionChunk_succ_mul_pow_le
    (S : Finset BitString) (x : BitString) (i : Nat)
    (hi : 2 ^ i ≤ S.card) :
    (descriptionChunk S x (i + 1)).card * 2 ^ i ≤ S.card := by
  have hcard_size :
      (descriptionChunk S x (i + 1)).card ≤
        descriptionChunkSize S (i + 1) := by
    unfold descriptionChunk
    exact (List.toFinset_card_le _).trans (List.length_take_le _ _)
  have hquot_pos : 0 < S.card / 2 ^ i :=
    Nat.div_pos hi (by positivity)
  have hsize :
      descriptionChunkSize S (i + 1) ≤ S.card / 2 ^ i := by
    unfold descriptionChunkSize
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    omega
  have hchunk : (descriptionChunk S x (i + 1)).card ≤
      S.card / 2 ^ i :=
    hcard_size.trans hsize
  exact (Nat.mul_le_mul_right (2 ^ i) hchunk).trans
    (Nat.div_mul_le_self S.card (2 ^ i))

/-- Compute the chunk containing `x` directly from a canonical finite-set code,
the point `x`, and the split parameter `i`. -/
noncomputable def strongDescriptionChunkCode
    (input : (BitString × BitString) × Nat) : BitString :=
  let Scode := input.1.1
  let x := input.1.2
  let s := input.2 + 1
  let L := canonicalPointListOfCode Scode
  let c := L.length / 2 ^ s + 1
  let blockIdx := L.findIdx (· == x) / c
  descriptionChunkUniformCode
    (pairCode Scode (chunkAddress blockIdx s))

/-- The fixed-width chunk address is primitive recursive in the index and the width. -/
theorem chunkAddress_primrec :
    Primrec₂ chunkAddress := by
  unfold chunkAddress
  exact Primrec.list_append.comp
    (primrec_natBits.comp Primrec.fst)
    (Primrec.list_replicate.comp
      (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp
          (primrec_natBits.comp Primrec.fst)))
      (Primrec.const false))

/-- Computing the code of a description chunk from a model code, a string and a
level is computable. -/
theorem strongDescriptionChunkCode_computable :
    Computable strongDescriptionChunkCode := by
  let Scode : (BitString × BitString) × Nat → BitString :=
    fun input => input.1.1
  let point : (BitString × BitString) × Nat → BitString :=
    fun input => input.1.2
  let split : (BitString × BitString) × Nat → Nat :=
    fun input => input.2 + 1
  let points : (BitString × BitString) × Nat → List BitString :=
    fun input => canonicalPointListOfCode (Scode input)
  let chunkSize : (BitString × BitString) × Nat → Nat :=
    fun input => (points input).length / 2 ^ split input + 1
  have hScode : Primrec Scode :=
    Primrec.fst.comp Primrec.fst
  have hpoint : Primrec point :=
    Primrec.snd.comp Primrec.fst
  have hsplit : Primrec split :=
    Primrec.succ.comp Primrec.snd
  have hpoints : Primrec points :=
    canonicalPointListOfCode_primrec.comp hScode
  have hchunkSize : Primrec chunkSize := by
    exact Primrec.succ.comp
      (Primrec.nat_div.comp
        (Primrec.list_length.comp hpoints)
        (primrec_two_pow_aux.comp hsplit))
  have hfind : Primrec
      (fun input : (BitString × BitString) × Nat =>
        (points input).findIdx (· == point input)) := by
    have hpred : Primrec₂
        (fun (input : (BitString × BitString) × Nat) (w : BitString) =>
          w == point input) := by
      have heq : Primrec₂
          (fun (a b : BitString) => decide (a = b)) := by
        convert Primrec.eq
        any_goals exact BitString
        · convert Iff.rfl
          exact primrecRel_iff_primrec_decide
      exact ((heq.comp Primrec.snd
        (hpoint.comp Primrec.fst)).to₂).of_eq
          (fun input => by
            intro w
            apply Bool.eq_iff_iff.mpr
            simp)
    exact Primrec.list_findIdx hpoints hpred
  have hblock : Primrec
      (fun input : (BitString × BitString) × Nat =>
        (points input).findIdx (· == point input) /
          chunkSize input) :=
    Primrec.nat_div.comp hfind hchunkSize
  have haddress : Primrec
      (fun input : (BitString × BitString) × Nat =>
        chunkAddress
          ((points input).findIdx (· == point input) /
            chunkSize input)
          (split input)) :=
    chunkAddress_primrec.comp hblock hsplit
  have hpair : Primrec
      (fun input : (BitString × BitString) × Nat =>
        pairCode (Scode input)
          (chunkAddress
            ((points input).findIdx (· == point input) /
              chunkSize input)
            (split input))) :=
    pairCode_primrec.comp hScode haddress
  exact descriptionChunkUniformCode_computable.comp
    (hpair.to_comp.of_eq fun _ => rfl)

/-- On the canonical code of `S` and a member `x`, the chunk function returns the
canonical code of the level-`i + 1` description chunk of `x` in `S`. -/
theorem strongDescriptionChunkCode_eq
    (S : Finset BitString) (hS : S.Nonempty)
    (x : BitString) (i : Nat) (hx : x ∈ S) :
    strongDescriptionChunkCode
        (((codedUniformOn S hS).code, x), i) =
      (codedUniformOn (descriptionChunk S x (i + 1))
        (descriptionChunk_nonempty S x (i + 1) hx)).code := by
  unfold strongDescriptionChunkCode
  simp only [canonicalPointListOfCode_codedUniformOn,
    length_canonicalFinsetList]
  exact descriptionChunkUniformCode_eq S hS x (i + 1) hx

/-- A short program for the original strong model, paired with the binary
encoding of `i`, computes the exact-size chunk containing every queried
condition. -/
noncomputable def strongDescriptionChunkDecompressor (T : Map) : Map :=
  fun input =>
    (T (decodeSecond input.1, input.2)).map fun Scode =>
      strongDescriptionChunkCode
        ((Scode, input.2), decodeBits (decodeFirst input.1))

/-- Post-composing a decompressor with the chunk function again gives a
decompressor. -/
theorem strongDescriptionChunkDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (strongDescriptionChunkDecompressor T) := by
  have hfirst :
      Partrec (fun input : BitString × BitString =>
        T (decodeSecond input.1, input.2)) :=
    Partrec.comp hT
      (Computable.pair
        (decodeSecond_computable.comp Computable.fst)
        Computable.snd)
  have hpost :
      Computable
        (fun input : (BitString × BitString) × BitString =>
          strongDescriptionChunkCode
            ((input.2, input.1.2),
              decodeBits (decodeFirst input.1.1))) := by
    exact strongDescriptionChunkCode_computable.comp
      ((Computable.snd.pair
        (Computable.snd.comp Computable.fst)).pair
        (decodeBits_computable.comp
          (decodeFirst_computable.comp
            (Computable.fst.comp Computable.fst))))
  exact Partrec.map hfirst hpost

/-- A total program stays total when a level index is prepended to it and the chunk
decompressor is used. -/
theorem strongDescriptionChunkDecompressor_total
    {T : Map} {p : BitString} (hp : IsTotalProgram T p)
    (i : Nat) :
    IsTotalProgram (strongDescriptionChunkDecompressor T)
      (pairCode (Nat.bits i) p) := by
  intro y
  unfold strongDescriptionChunkDecompressor
  rw [decodeSecond_pairCode]
  rw [Part.dom_iff_mem]
  obtain ⟨Scode, hScode⟩ := Part.dom_iff_mem.mp (hp y)
  refine ⟨strongDescriptionChunkCode ((Scode, y), i), ?_⟩
  exact (Part.mem_map_iff _).2 ⟨Scode, hScode, by
    simp [decodeFirst_pairCode, decodeBits_natBits]⟩

/-- A program producing the code of a model containing `x` produces, with the level
`i` prepended, the code of the level-`i + 1` description chunk of `x`. -/
theorem strongDescriptionChunkDecompressor_produces
    {T : Map} {p x : BitString} {S : Finset BitString}
    (hS : S.Nonempty) (i : Nat)
    (hp : produces T p x (codedUniformOn S hS).code)
    (hx : x ∈ S) :
    produces (strongDescriptionChunkDecompressor T)
      (pairCode (Nat.bits i) p) x
      (codedUniformOn (descriptionChunk S x (i + 1))
        (descriptionChunk_nonempty S x (i + 1) hx)).code := by
  change (codedUniformOn (descriptionChunk S x (i + 1))
      (descriptionChunk_nonempty S x (i + 1) hx)).code ∈
    (T (decodeSecond (pairCode (Nat.bits i) p), x)).map
      (fun Scode => strongDescriptionChunkCode
        ((Scode, x), decodeBits (decodeFirst
          (pairCode (Nat.bits i) p))))
  rw [decodeSecond_pairCode, decodeFirst_pairCode, decodeBits_natBits]
  exact (Part.mem_map_iff _).2
    ⟨(codedUniformOn S hS).code, hp,
      strongDescriptionChunkCode_eq S hS x i hx⟩

/-- Self-delimiting framing of an ordinary program `q` followed by a fixed-size
advice string `z`.  Only `|z|` is encoded: the decoder reads `z` from the end of
the body, so the total length is `|q| + |z| + 2|bits |z|| + 1`. -/
def plainAdviceCode (q z : BitString) : BitString :=
  pairCode (Nat.bits z.length) (q ++ z)

/-- The program part of an advice code. -/
def decodePlainAdviceProgram (w : BitString) : BitString :=
  let body := decodeSecond w
  body.take (body.length - decodeBits (decodeFirst w))

/-- The data part of an advice code. -/
def decodePlainAdviceData (w : BitString) : BitString :=
  let body := decodeSecond w
  body.drop (body.length - decodeBits (decodeFirst w))

/-- The program part is read back from an assembled advice code. -/
@[simp] theorem decodePlainAdviceProgram_code
    (q z : BitString) :
    decodePlainAdviceProgram (plainAdviceCode q z) = q := by
  simp [decodePlainAdviceProgram, plainAdviceCode,
    decodeFirst_pairCode, decodeSecond_pairCode,
    decodeBits_natBits]

/-- The data part is read back from an assembled advice code. -/
@[simp] theorem decodePlainAdviceData_code
    (q z : BitString) :
    decodePlainAdviceData (plainAdviceCode q z) = z := by
  simp [decodePlainAdviceData, plainAdviceCode,
    decodeFirst_pairCode, decodeSecond_pairCode,
    decodeBits_natBits]

/-- The length of an advice code: the two parts plus the self-delimiting overhead
`2 * |bits |z|| + 1`. -/
theorem length_plainAdviceCode (q z : BitString) :
    (plainAdviceCode q z).length =
      q.length + z.length + 2 * (Nat.bits z.length).length + 1 := by
  simp [plainAdviceCode, length_pairCode]
  omega

/-- Extracting the program part of an advice code is computable. -/
theorem decodePlainAdviceProgram_computable :
    Computable decodePlainAdviceProgram := by
  unfold decodePlainAdviceProgram
  have hbody : Computable decodeSecond :=
    decodeSecond_computable
  have hcut : Computable
      (fun w : BitString =>
        (decodeSecond w).length - decodeBits (decodeFirst w)) :=
    Primrec.nat_sub.to_comp.comp
      (Computable.list_length.comp hbody)
      (decodeBits_computable.comp decodeFirst_computable)
  exact Primrec.list_take.to_comp.comp hbody hcut

/-- Extracting the data part of an advice code is computable. -/
theorem decodePlainAdviceData_computable :
    Computable decodePlainAdviceData := by
  unfold decodePlainAdviceData
  have hbody : Computable decodeSecond :=
    decodeSecond_computable
  have hcut : Computable
      (fun w : BitString =>
        (decodeSecond w).length - decodeBits (decodeFirst w)) :=
    Primrec.nat_sub.to_comp.comp
      (Computable.list_length.comp hbody)
      (decodeBits_computable.comp decodeFirst_computable)
  exact Primrec.list_drop.to_comp.comp hbody hcut

/-- Ordinary decompressor which first reconstructs a set code using `U`, then
applies the explicit chunk encoder using the fixed-size advice suffix. -/
noncomputable def plainDescriptionChunkDecompressor
    (U : Map) : Map :=
  fun input =>
    (U (decodePlainAdviceProgram input.1, [])).map fun Scode =>
      descriptionChunkUniformCode
        (pairCode Scode (decodePlainAdviceData input.1))

/-- The plain-complexity chunk decompressor is a decompressor. -/
theorem plainDescriptionChunkDecompressor_partrec
    (U : Map) (hU : isDecompressor U) :
    isDecompressor (plainDescriptionChunkDecompressor U) := by
  have hfirst :
      Partrec (fun input : BitString × BitString =>
        U (decodePlainAdviceProgram input.1, [])) :=
    Partrec.comp hU
      (Computable.pair
        (decodePlainAdviceProgram_computable.comp Computable.fst)
        (Computable.const []))
  have hpost :
      Computable
        (fun input : (BitString × BitString) × BitString =>
          descriptionChunkUniformCode
            (pairCode input.2
              (decodePlainAdviceData input.1.1))) := by
    have hz : Computable
        (fun input : (BitString × BitString) × BitString =>
          decodePlainAdviceData input.1.1) :=
      decodePlainAdviceData_computable.comp
        (Computable.fst.comp Computable.fst)
    have hpair : Computable
        (fun input : (BitString × BitString) × BitString =>
          (input.2, decodePlainAdviceData input.1.1)) :=
      Computable.snd.pair hz
    have hencode : Computable
        (fun input : BitString × BitString =>
          pairCode input.1 input.2) :=
      pairCode_primrec.to_comp
    have hcomp :=
      descriptionChunkUniformCode_computable.comp
        (hencode.comp hpair)
    exact hcomp.of_eq (fun _ => rfl)
  exact Partrec.map hfirst hpost

/-- An advice code built from a program for the model code and the chunk data
produces the code of the corresponding description chunk. -/
theorem plainDescriptionChunkDecompressor_produces
    {U : Map} {q z Scode Bcode : BitString}
    (hq : produces U q [] Scode)
    (hcode : descriptionChunkUniformCode
      (pairCode Scode z) = Bcode) :
    produces (plainDescriptionChunkDecompressor U)
      (plainAdviceCode q z) [] Bcode := by
  change Bcode ∈
    (U (decodePlainAdviceProgram (plainAdviceCode q z), [])).map
      (fun Scode => descriptionChunkUniformCode
        (pairCode Scode
          (decodePlainAdviceData (plainAdviceCode q z))))
  rw [decodePlainAdviceProgram_code, decodePlainAdviceData_code]
  exact (Part.mem_map_iff _).2 ⟨Scode, hq, hcode⟩

/-- The level-`i + 1` description chunk of `x` in `S` costs at most the plain set
complexity of `S` plus `i + 1 + 2 * |bits (i + 1)|` and a constant. -/
theorem plainSetComplexity_descriptionChunk_succ
    (U : Map) (hU : isOptimalConditional U) :
    ∃ c : Nat, ∀
      (S : Finset BitString) (hS : S.Nonempty)
      (x : BitString) (i : Nat) (hx : x ∈ S),
      plainSetComplexity U (descriptionChunk S x (i + 1))
          (descriptionChunk_nonempty S x (i + 1) hx) ≤
        plainSetComplexity U S hS +
          ((i + 1 + 2 * (Nat.bits (i + 1)).length + c : Nat) :
            ENat) := by
  obtain ⟨c, hc⟩ :=
    hU.2 (plainDescriptionChunkDecompressor U)
      (plainDescriptionChunkDecompressor_partrec U hU.1)
  refine ⟨c + 1, ?_⟩
  intro S hS x i hx
  obtain ⟨cLiteral, hLiteral⟩ := plainK_le_length U hU
  have hfinite :
      plainK U (codedUniformOn S hS).code ≠ ⊤ := by
    apply ne_top_of_le_ne_top ?_
      (hLiteral (codedUniformOn S hS).code)
    rw [← ENat.coe_add]
    exact ENat.coe_ne_top _
  obtain ⟨q, hq, hqLen⟩ :=
    exists_program_of_KP_ne_top
      (M := U) (x := (codedUniformOn S hS).code) (y := []) (by
        simpa [KP_eq_condK] using hfinite)
  let blockIdx :=
    (canonicalFinsetList S).findIdx (· == x) /
      descriptionChunkSize S (i + 1)
  let z := chunkAddress blockIdx (i + 1)
  have hzLen : z.length = i + 1 := by
    exact chunkAddress_length blockIdx (i + 1)
      (blockIdx_lt S x (i + 1) hx)
  have hprod :
      produces (plainDescriptionChunkDecompressor U)
        (plainAdviceCode q z) []
        (codedUniformOn (descriptionChunk S x (i + 1))
          (descriptionChunk_nonempty S x (i + 1) hx)).code := by
    apply plainDescriptionChunkDecompressor_produces hq
    exact descriptionChunkUniformCode_eq S hS x (i + 1) hx
  calc
    plainSetComplexity U (descriptionChunk S x (i + 1))
        (descriptionChunk_nonempty S x (i + 1) hx)
        ≤ condK (plainDescriptionChunkDecompressor U)
            (codedUniformOn (descriptionChunk S x (i + 1))
              (descriptionChunk_nonempty S x (i + 1) hx)).code [] +
            (c : ENat) :=
      hc _ _
    _ ≤ ((plainAdviceCode q z).length : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨plainAdviceCode q z, hprod, rfl⟩
    _ = plainSetComplexity U S hS +
          ((i + 1 + 2 * (Nat.bits (i + 1)).length + (c + 1) : Nat) :
            ENat) := by
      rw [length_plainAdviceCode, hzLen]
      have hqLen' :
          (programLength q : ENat) =
            plainSetComplexity U S hS := by
        unfold plainSetComplexity plainK
        simpa [KP_eq_condK] using hqLen
      rw [← hqLen']
      push_cast
      ring

/-! ### Proposition `part` -/

/-- If $A$ belongs to a partition of complexity $\varepsilon$, then $A$ is an
$\varepsilon + O(1)$-strong model for any $x \in A$. -/
theorem IsPartition.strong_model_of_mem
    (U : Map) (hU : isOptimalConditional U)
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀
      (A : Finset (Finset BitString)), IsPartition A →
      ∀ (S : Finset BitString), S ∈ A →
      ∀ (x : BitString) (hx : x ∈ S),
      totalCondK T (codedUniformOn S ⟨x, hx⟩).code x ≤
        partitionComplexity U A + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    hT.2 (partitionMemberDecompressor U)
      (partitionMemberDecompressor_partrec U hU.1)
  refine ⟨c, ?_⟩
  intro A hA S hS x hx
  obtain ⟨cLiteral, hLiteral⟩ := plainK_le_length U hU
  have hfinite : plainK U (partitionCode A) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ?_ (hLiteral (partitionCode A))
    rw [← ENat.coe_add]
    exact ENat.coe_ne_top _
  obtain ⟨q, hq, hqLen⟩ :=
    exists_program_of_KP_ne_top
      (M := U) (x := partitionCode A) (y := []) (by
        simpa [KP_eq_condK] using hfinite)
  have htotal : IsTotalProgram (partitionMemberDecompressor U) q :=
    partitionMemberDecompressor_total hq
  have hprod :
      produces (partitionMemberDecompressor U) q x
        (codedUniformOn S ⟨x, hx⟩).code := by
    have hlookup :=
      partitionMemberDecompressor_produces
        (x := x) hq
    rw [partitionMemberCode_eq_of_mem A hA S hS x hx] at hlookup
    have hSne : S.Nonempty := ⟨x, hx⟩
    simpa [canonicalFiniteSetCode,
      canonicalUniformCodeOfList_canonicalFinsetList S hSne] using hlookup
  calc
    totalCondK T (codedUniformOn S ⟨x, hx⟩).code x
        ≤ totalCondK (partitionMemberDecompressor U)
            (codedUniformOn S ⟨x, hx⟩).code x + (c : ENat) :=
      hc _ _
    _ ≤ (programLength q : ENat) + (c : ENat) := by
      gcongr
      exact totalCondK_le_programLength htotal hprod
    _ = partitionComplexity U A + (c : ENat) := by
      unfold partitionComplexity
      simpa [KP_eq_condK] using congrArg (fun z => z + (c : ENat)) hqLen

/-! ### Converse of Proposition `part`: the fibre partition construction

The backward direction runs the strong model's total program over the whole
length-`n` cube, keeps the self-members `x' ∈ p(x')`, and partitions them into
the fibres of `p`. -/

/-- Output value of a total program on a context. -/
noncomputable def totalProgOutput (T : Map) (p : BitString)
    (hp : IsTotalProgram T p) (x' : BitString) : BitString :=
  (T (p, x')).get (hp x')

/-- A total program produces its recorded output on every condition. -/
theorem totalProgOutput_produces (T : Map) (p : BitString)
    (hp : IsTotalProgram T p) (x' : BitString) :
    produces T p x' (totalProgOutput T p hp x') :=
  Part.get_mem (hp x')

/-- An output of a total program is its recorded output, so the output is unique. -/
theorem produces_eq_totalProgOutput {T : Map} {p x' y : BitString}
    (hp : IsTotalProgram T p) (h : produces T p x' y) :
    y = totalProgOutput T p hp x' :=
  Part.mem_unique h (Part.get_mem (hp x'))

/-- The output list of `totalProgramMapList` on a total program is exactly the
pointwise image under `totalProgOutput`. -/
theorem totalProgramMapList_eq_map
    {T : Map} {p : BitString} (hp : IsTotalProgram T p)
    {xs ys : List BitString}
    (hys : ys ∈ totalProgramMapList T (p, xs)) :
    ys = xs.map (totalProgOutput T p hp) := by
  have hrel : List.Forall₂ (fun x y => produces T p x y) xs ys :=
    totalProgramMapList_correct hys
  have hrel' : List.Forall₂ (fun x y => y = totalProgOutput T p hp x) xs ys := by
    refine hrel.imp ?_
    intro a b hab
    exact produces_eq_totalProgOutput hp hab
  clear hrel hys
  induction hrel' with
  | nil => rfl
  | cons hab _ ih => rw [List.map_cons, ← hab, ih]

/-- Aligned pairing of an input list with an output list. -/
def zipStrings (xs ys : List BitString) : List (BitString × BitString) :=
  (List.range ys.length).map (fun k => (xs.getD k [], ys.getD k []))

end Kolmogorov
