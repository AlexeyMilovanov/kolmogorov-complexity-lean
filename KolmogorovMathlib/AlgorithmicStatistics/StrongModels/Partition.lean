import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionShift

/-!
# Strong models characterized by membership in simple finite partitions

This module provides the characterization of strong models using finite partitions.
It shows that a model is strong if and only if it belongs to a simple finite
partition of the space with suitable complexity bounds.
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

theorem partitionMemberCode_computable :
    Computable partitionMemberCode :=
  partitionMemberCode_primrec.to_comp

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

theorem partitionMemberDecompressor_partrec
    (U : Map) (hU : isDecompressor U) :
    isDecompressor (partitionMemberDecompressor U) := by
  exact Partrec.map
    (Partrec.comp hU
      (Computable.pair Computable.fst (Computable.const [])))
    (partitionMemberCode_computable.comp
      (Computable.snd.pair (Computable.snd.comp Computable.fst)))

theorem partitionMemberDecompressor_total
    {U : Map} {q Pcode : BitString}
    (hq : produces U q [] Pcode) :
    IsTotalProgram (partitionMemberDecompressor U) q := by
  intro x
  unfold partitionMemberDecompressor
  rw [Part.dom_iff_mem]
  exact ⟨partitionMemberCode (Pcode, x),
    (Part.mem_map_iff _).2 ⟨Pcode, hq, rfl⟩⟩

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

theorem chunkAddress_primrec :
    Primrec₂ chunkAddress := by
  unfold chunkAddress
  exact Primrec.list_append.comp
    (primrecNatBits.comp Primrec.fst)
    (Primrec.list_replicate.comp
      (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp
          (primrecNatBits.comp Primrec.fst)))
      (Primrec.const false))

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
        (twoPow_primrec.comp hsplit))
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
        (decodeBitsComputable.comp
          (decodeFirst_computable.comp
            (Computable.fst.comp Computable.fst))))
  exact Partrec.map hfirst hpost

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

def decodePlainAdviceProgram (w : BitString) : BitString :=
  let body := decodeSecond w
  body.take (body.length - decodeBits (decodeFirst w))

def decodePlainAdviceData (w : BitString) : BitString :=
  let body := decodeSecond w
  body.drop (body.length - decodeBits (decodeFirst w))

@[simp] theorem decodePlainAdviceProgram_code
    (q z : BitString) :
    decodePlainAdviceProgram (plainAdviceCode q z) = q := by
  simp [decodePlainAdviceProgram, plainAdviceCode,
    decodeFirst_pairCode, decodeSecond_pairCode,
    decodeBits_natBits]

@[simp] theorem decodePlainAdviceData_code
    (q z : BitString) :
    decodePlainAdviceData (plainAdviceCode q z) = z := by
  simp [decodePlainAdviceData, plainAdviceCode,
    decodeFirst_pairCode, decodeSecond_pairCode,
    decodeBits_natBits]

theorem length_plainAdviceCode (q z : BitString) :
    (plainAdviceCode q z).length =
      q.length + z.length + 2 * (Nat.bits z.length).length + 1 := by
  simp [plainAdviceCode, length_pairCode]
  omega

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
      (decodeBitsComputable.comp decodeFirst_computable)
  exact Primrec.list_take.to_comp.comp hcut hbody

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
      (decodeBitsComputable.comp decodeFirst_computable)
  exact Primrec.list_drop.to_comp.comp hcut hbody

/-- Ordinary decompressor which first reconstructs a set code using `U`, then
applies the explicit chunk encoder using the fixed-size advice suffix. -/
noncomputable def plainDescriptionChunkDecompressor
    (U : Map) : Map :=
  fun input =>
    (U (decodePlainAdviceProgram input.1, [])).map fun Scode =>
      descriptionChunkUniformCode
        (pairCode Scode (decodePlainAdviceData input.1))

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
  obtain ⟨cLiteral, hLiteral⟩ := plainKLeLength U hU
  have hfinite :
      plainK U (codedUniformOn S hS).code ≠ ⊤ := by
    apply ne_top_of_le_ne_top ?_
      (hLiteral (codedUniformOn S hS).code)
    rw [← ENat.coe_add]
    exact ENat.coe_ne_top _
  obtain ⟨q, hq, hqLen⟩ :=
    exists_program_of_KP_ne_top
      (M := U) (x := (codedUniformOn S hS).code) (y := []) (by
        simpa [KP_eq_condK, plainK] using hfinite)
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
  obtain ⟨cLiteral, hLiteral⟩ := plainKLeLength U hU
  have hfinite : plainK U (partitionCode A) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ?_ (hLiteral (partitionCode A))
    rw [← ENat.coe_add]
    exact ENat.coe_ne_top _
  obtain ⟨q, hq, hqLen⟩ :=
    exists_program_of_KP_ne_top
      (M := U) (x := partitionCode A) (y := []) (by
        simpa [KP_eq_condK, plainK] using hfinite)
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
      simpa [KP_eq_condK, plainK] using congrArg (fun z => z + (c : ENat)) hqLen

/-! ### Converse of Proposition `part`: the fibre partition construction

The backward direction runs the strong model's total program over the whole
length-`n` cube, keeps the self-members `x' ∈ p(x')`, and partitions them into
the fibres of `p`. -/

/-- Output value of a total program on a context. -/
noncomputable def totalProgOutput (T : Map) (p : BitString)
    (hp : IsTotalProgram T p) (x' : BitString) : BitString :=
  (T (p, x')).get (hp x')

theorem totalProgOutput_produces (T : Map) (p : BitString)
    (hp : IsTotalProgram T p) (x' : BitString) :
    produces T p x' (totalProgOutput T p hp x') :=
  Part.get_mem (hp x')

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

theorem zipStrings_primrec :
    Primrec₂ zipStrings := by
  unfold zipStrings
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) ?_
  exact (Primrec.pair
    ((Primrec.list_getD []).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    ((Primrec.list_getD []).comp (Primrec.snd.comp Primrec.fst) Primrec.snd))

theorem zipStrings_map_self (xs : List BitString)
    (f : BitString → BitString) :
    zipStrings xs (xs.map f) = xs.map (fun x => (x, f x)) := by
  apply List.ext_getElem
  · simp [zipStrings]
  · intro k hk1 hk2
    simp only [zipStrings, List.length_map, List.length_range] at hk1
    have hk : k < xs.length := by
      simpa [List.length_map] using hk1
    rw [List.getElem_map]
    simp only [zipStrings, List.getElem_map, List.getElem_range]
    have h1 : xs.getD k [] = xs[k] := by
      rw [List.getD_eq_getElem xs [] hk]
    have h2 : (xs.map f).getD k [] = f xs[k] := by
      rw [List.getD_eq_getElem (xs.map f) [] (by simpa using hk),
        List.getElem_map]
    rw [h1, h2]

/-! ### Fiber lists over aligned pairs -/

/-- The pairs `(x', out)` where `x'` belongs to the set decoded from its own
output `out`. -/
noncomputable def selfMemberPairs (pairs : List (BitString × BitString)) :
    List (BitString × BitString) :=
  pairs.filter (fun q => decide (q.1 ∈ canonicalPointListOfCode q.2))

/-- The fiber of the value `B`: those self-member strings whose output is `B`. -/
noncomputable def fiberOverCode (pairs : List (BitString × BitString))
    (B : BitString) : List BitString :=
  ((selfMemberPairs pairs).filter (fun q => decide (q.2 = B))).map Prod.fst

/-- Membership in a fiber list, for arbitrary aligned pairs. -/
theorem mem_fiberOverCode (pairs : List (BitString × BitString))
    (B a : BitString) :
    a ∈ fiberOverCode pairs B ↔
      (a, B) ∈ pairs ∧ a ∈ canonicalPointListOfCode B := by
  unfold fiberOverCode selfMemberPairs
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.exists]
  constructor
  · rintro ⟨a', b', ⟨⟨hmem, hself⟩, hb⟩, ha⟩
    subst ha; subst hb
    exact ⟨hmem, hself⟩
  · rintro ⟨hmem, hself⟩
    exact ⟨a, B, ⟨⟨hmem, hself⟩, rfl⟩, rfl⟩

/-- Membership in a fiber list computed from the `f`-paired input list. -/
theorem mem_fiberOverCode_map (xs : List BitString)
    (f : BitString → BitString) (B a : BitString) :
    a ∈ fiberOverCode (xs.map (fun x => (x, f x))) B ↔
      a ∈ xs ∧ f a = B ∧ a ∈ canonicalPointListOfCode B := by
  rw [mem_fiberOverCode]
  constructor
  · rintro ⟨hmem, hself⟩
    rw [List.mem_map] at hmem
    obtain ⟨a', ha'mem, ha'eq⟩ := hmem
    rw [Prod.mk.injEq] at ha'eq
    obtain ⟨rfl, hfe⟩ := ha'eq
    exact ⟨ha'mem, hfe, hself⟩
  · rintro ⟨hmem, hfa, hself⟩
    refine ⟨?_, hself⟩
    rw [List.mem_map]
    exact ⟨a, hmem, by rw [hfa]⟩

/-- Functional property of a fiber: every fiber element maps to the fiber's value. -/
theorem fiberOverCode_map_output {xs : List BitString}
    {f : BitString → BitString} {B a : BitString}
    (h : a ∈ fiberOverCode (xs.map (fun x => (x, f x))) B) :
    f a = B :=
  ((mem_fiberOverCode_map xs f B a).mp h).2.1

/-- The canonical code of a finite set equals the canonical image code of any
list whose `toFinset` is that set. -/
theorem canonicalFiniteSetCode_toFinset (l : List BitString) :
    canonicalFiniteSetCode l.toFinset = canonicalImageCodeOfList l := rfl

theorem selfMemberPairs_primrec :
    Primrec selfMemberPairs := by
  unfold selfMemberPairs
  refine list_filter_primrec Primrec.id ?_
  exact (bitString_mem_primrec.comp (Primrec.fst.comp Primrec.snd)
    (canonicalPointListOfCode_primrec.comp (Primrec.snd.comp Primrec.snd))).to₂

theorem fiberOverCode_primrec :
    Primrec₂ fiberOverCode := by
  unfold fiberOverCode
  have heq : Primrec₂ (fun (a b : BitString) => decide (a = b)) := by
    convert Primrec.eq
    any_goals exact BitString
    · convert Iff.rfl
      exact primrecRel_iff_primrec_decide
  have hfilter : Primrec (fun input : List (BitString × BitString) × BitString =>
      (selfMemberPairs input.1).filter (fun q => decide (q.2 = input.2))) := by
    refine list_filter_primrec (selfMemberPairs_primrec.comp Primrec.fst) ?_
    exact (heq.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  exact (Primrec.list_map hfilter (Primrec.fst.comp Primrec.snd).to₂)

/-- The head of the canonical enumeration of a nonempty finite set is a member. -/
theorem headI_mem_canonicalFinsetList {S : Finset BitString} (hS : S.Nonempty) :
    (canonicalFinsetList S).headI ∈ S := by
  have hne : canonicalFinsetList S ≠ [] := by
    rw [← List.length_pos_iff_ne_nil, length_canonicalFinsetList]
    exact hS.card_pos
  cases h : canonicalFinsetList S with
  | nil => exact absurd h hne
  | cons a t =>
    have ha : a ∈ canonicalFinsetList S := by rw [h]; exact List.mem_cons_self
    change (a :: t).headI ∈ S
    exact mem_canonicalFinsetList.mp ha

/-! ### Decompressor 1: obtain the original model from a fibre model (`CT(A|A')`) -/

/-- On input `(p, B')`, decode the finite set `B'`, take any element (its head),
and run the total program `p` on it.  For the fibre model `A'`, its head lies in
`A'`, so the program's value there is the code of the original model `A`. -/
noncomputable def elementThenProgDecompressor (T : Map) : Map :=
  fun input => T (input.1, (canonicalPointListOfCode input.2).headI)

theorem elementThenProgDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (elementThenProgDecompressor T) := by
  have h : Partrec (fun input : BitString × BitString =>
      T (input.1, (canonicalPointListOfCode input.2).headI)) :=
    Partrec.comp hT
      (Computable.pair Computable.fst
        ((Primrec.list_headI.to_comp).comp
          (canonicalPointListOfCode_computable.comp Computable.snd)))
  exact h

theorem elementThenProgDecompressor_total
    {T : Map} {p : BitString} (hp : IsTotalProgram T p) :
    IsTotalProgram (elementThenProgDecompressor T) p := by
  intro B'
  exact hp _

theorem elementThenProgDecompressor_produces
    {T : Map} {p x₀ B' out : BitString}
    (hhead : (canonicalPointListOfCode B').headI = x₀)
    (hp : produces T p x₀ out) :
    produces (elementThenProgDecompressor T) p B' out := by
  unfold produces elementThenProgDecompressor
  rw [hhead]
  exact hp

/-! ### Decompressor 2: obtain the fibre model from the original model (`CT(A'|A)`) -/

/-- Post-processing: from the aligned outputs and the target set-code `input.2`,
return the canonical code of the fibre over `input.2`. -/
noncomputable def fiberPostFn
    (input : BitString × BitString) (ys : List BitString) : BitString :=
  canonicalImageCodeOfList
    (fiberOverCode
      (zipStrings (allStrings (decodeBits (decodeFirst input.1))) ys)
      input.2)

theorem fiberPostFn_computable : Computable₂ fiberPostFn := by
  have h : Primrec (fun q : (BitString × BitString) × List BitString =>
      canonicalImageCodeOfList
        (fiberOverCode
          (zipStrings (allStrings (decodeBits (decodeFirst q.1.1))) q.2)
          q.1.2)) :=
    canonicalImageCodeOfList_primrec.comp
      (fiberOverCode_primrec.comp
        (zipStrings_primrec.comp
          (allStrings_primrec.comp
            (primrecDecodeBits.comp
              (decodeFirst_primrec.comp (Primrec.fst.comp Primrec.fst))))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  exact h.to_comp

/-- On program `pairCode (bits n) p` and condition set-code `B`, run the total
program `p` over all length-`n` strings and return the canonical code of the
fibre `{x' : x' ∈ p(x'), p(x') = B}`. -/
noncomputable def fiberFromSetCodeDecompressor (T : Map) : Map :=
  fun input =>
    (totalProgramMapList T (decodeSecond input.1,
        allStrings (decodeBits (decodeFirst input.1)))).map (fiberPostFn input)

theorem fiberFromSetCodeDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (fiberFromSetCodeDecompressor T) := by
  have hexec : Partrec (fun input : BitString × BitString =>
      totalProgramMapList T (decodeSecond input.1,
        allStrings (decodeBits (decodeFirst input.1)))) :=
    Partrec.comp (totalProgramMapList_partrec T hT)
      (Computable.pair
        (decodeSecond_computable.comp Computable.fst)
        (allStrings_primrec.to_comp.comp
          (decodeBitsComputable.comp
            (decodeFirst_computable.comp Computable.fst))))
  exact Partrec.map hexec fiberPostFn_computable

/-! ### Decompressor 3: reconstruct the whole partition (partition complexity) -/

/-- The list of member set-codes of the fibre partition determined by aligned
pairs. -/
noncomputable def partitionMemberCodesFromPairs
    (pairs : List (BitString × BitString)) : List BitString :=
  (selfMemberPairs pairs).map
    (fun q => canonicalImageCodeOfList (fiberOverCode pairs q.2))

theorem partitionMemberCodesFromPairs_primrec :
    Primrec partitionMemberCodesFromPairs := by
  unfold partitionMemberCodesFromPairs
  refine Primrec.list_map selfMemberPairs_primrec ?_
  exact (canonicalImageCodeOfList_primrec.comp
    (fiberOverCode_primrec.comp Primrec.fst
      (Primrec.snd.comp Primrec.snd))).to₂

/-- Post-processing: from the aligned outputs, return the canonical code of the
whole fibre partition. -/
noncomputable def partitionPostFn
    (input : BitString × BitString) (ys : List BitString) : BitString :=
  canonicalImageCodeOfList
    (partitionMemberCodesFromPairs
      (zipStrings (allStrings (decodeBits (decodeFirst input.1))) ys))

theorem partitionPostFn_computable : Computable₂ partitionPostFn := by
  have h : Primrec (fun q : (BitString × BitString) × List BitString =>
      canonicalImageCodeOfList
        (partitionMemberCodesFromPairs
          (zipStrings (allStrings (decodeBits (decodeFirst q.1.1))) q.2))) :=
    canonicalImageCodeOfList_primrec.comp
      (partitionMemberCodesFromPairs_primrec.comp
        (zipStrings_primrec.comp
          (allStrings_primrec.comp
            (primrecDecodeBits.comp
              (decodeFirst_primrec.comp (Primrec.fst.comp Primrec.fst))))
          Primrec.snd))
  exact h.to_comp

/-- On program `pairCode (bits n) p`, run `p` over all length-`n` strings and
return the canonical code of the whole fibre partition. -/
noncomputable def partitionFromProgDecompressor (T : Map) : Map :=
  fun input =>
    (totalProgramMapList T (decodeSecond input.1,
        allStrings (decodeBits (decodeFirst input.1)))).map (partitionPostFn input)

theorem partitionFromProgDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (partitionFromProgDecompressor T) := by
  have hexec : Partrec (fun input : BitString × BitString =>
      totalProgramMapList T (decodeSecond input.1,
        allStrings (decodeBits (decodeFirst input.1)))) :=
    Partrec.comp (totalProgramMapList_partrec T hT)
      (Computable.pair
        (decodeSecond_computable.comp Computable.fst)
        (allStrings_primrec.to_comp.comp
          (decodeBitsComputable.comp
            (decodeFirst_computable.comp Computable.fst))))
  exact Partrec.map hexec partitionPostFn_computable

/-! ### Evaluations, totality, and production of the post decompressors -/

theorem fiberPostFn_eval (p : BitString) (n : Nat)
    (f : BitString → BitString) (B : BitString) :
    fiberPostFn (pairCode (Nat.bits n) p, B) ((allStrings n).map f) =
      canonicalImageCodeOfList
        (fiberOverCode ((allStrings n).map (fun x => (x, f x))) B) := by
  unfold fiberPostFn
  simp only [decodeFirst_pairCode, decodeBits_natBits]
  rw [zipStrings_map_self]

theorem partitionPostFn_eval (p : BitString) (n : Nat)
    (f : BitString → BitString) :
    partitionPostFn (pairCode (Nat.bits n) p, []) ((allStrings n).map f) =
      canonicalImageCodeOfList
        (partitionMemberCodesFromPairs
          ((allStrings n).map (fun x => (x, f x)))) := by
  unfold partitionPostFn
  simp only [decodeFirst_pairCode, decodeBits_natBits]
  rw [zipStrings_map_self]

theorem fiberFromSetCodeDecompressor_total
    {T : Map} {p : BitString} (hp : IsTotalProgram T p) (n : Nat) :
    IsTotalProgram (fiberFromSetCodeDecompressor T) (pairCode (Nat.bits n) p) := by
  intro B
  unfold fiberFromSetCodeDecompressor
  simp only [decodeSecond_pairCode, decodeFirst_pairCode, decodeBits_natBits]
  rw [Part.dom_iff_mem]
  obtain ⟨ys, hys⟩ :=
    Part.dom_iff_mem.mp (totalProgramMapList_dom_of_total hp (allStrings n))
  exact ⟨fiberPostFn (pairCode (Nat.bits n) p, B) ys,
    (Part.mem_map_iff _).2 ⟨ys, hys, rfl⟩⟩

theorem fiberFromSetCodeDecompressor_produces
    {T : Map} {p : BitString} (n : Nat)
    {B : BitString} {ys : List BitString}
    (hys : ys ∈ totalProgramMapList T (p, allStrings n)) :
    produces (fiberFromSetCodeDecompressor T) (pairCode (Nat.bits n) p) B
      (fiberPostFn (pairCode (Nat.bits n) p, B) ys) := by
  unfold produces fiberFromSetCodeDecompressor
  simp only [decodeSecond_pairCode, decodeFirst_pairCode, decodeBits_natBits]
  exact (Part.mem_map_iff _).2 ⟨ys, hys, rfl⟩

theorem partitionFromProgDecompressor_produces
    {T : Map} {p : BitString} (n : Nat) {y : BitString}
    {ys : List BitString}
    (hys : ys ∈ totalProgramMapList T (p, allStrings n)) :
    produces (partitionFromProgDecompressor T) (pairCode (Nat.bits n) p) y
      (partitionPostFn (pairCode (Nat.bits n) p, y) ys) := by
  unfold produces partitionFromProgDecompressor
  simp only [decodeSecond_pairCode, decodeFirst_pairCode, decodeBits_natBits]
  exact (Part.mem_map_iff _).2 ⟨ys, hys, rfl⟩

/-! ### The fibre partition and its properties -/

/-- The fibre partition determined by aligned pairs. -/
noncomputable def fiberPartition (pairs : List (BitString × BitString)) :
    Finset (Finset BitString) :=
  ((selfMemberPairs pairs).map
    (fun q => (fiberOverCode pairs q.2).toFinset)).toFinset

/-- The canonical code of the fibre partition is the canonical image code of its
member-code list — connecting the finite-set definition with the computed value. -/
theorem partitionCode_fiberPartition (pairs : List (BitString × BitString)) :
    partitionCode (fiberPartition pairs) =
      canonicalImageCodeOfList (partitionMemberCodesFromPairs pairs) := by
  unfold partitionCode
  rw [← canonicalFiniteSetCode_toFinset]
  congr 1
  unfold fiberPartition partitionMemberCodesFromPairs
  ext w
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨B, ⟨q, hq, hBeq⟩, hwB⟩
    exact ⟨q, hq, by rw [← hwB, ← hBeq, canonicalFiniteSetCode_toFinset]⟩
  · rintro ⟨q, hq, hweq⟩
    exact ⟨(fiberOverCode pairs q.2).toFinset, ⟨q, hq, rfl⟩,
      by rw [← hweq, canonicalFiniteSetCode_toFinset]⟩

/-- Membership in a mapped pair list. -/
theorem mem_map_pair {xs : List BitString} {f : BitString → BitString}
    {z b : BitString} :
    (z, b) ∈ xs.map (fun x => (x, f x)) ↔ z ∈ xs ∧ f z = b := by
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, hae⟩
    rw [Prod.mk.injEq] at hae
    obtain ⟨rfl, rfl⟩ := hae
    exact ⟨ha, rfl⟩
  · rintro ⟨hz, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- The fibre partition of an `f`-paired input list is a genuine partition. -/
theorem isPartition_fiberPartition
    (xs : List BitString) (f : BitString → BitString) :
    IsPartition (fiberPartition (xs.map (fun x => (x, f x)))) := by
  intro B hB C hC hBC
  simp only [fiberPartition, List.mem_toFinset, List.mem_map] at hB hC
  obtain ⟨qB, _, hBeq⟩ := hB
  obtain ⟨qC, _, hCeq⟩ := hC
  rw [Finset.disjoint_left]
  intro z hzB hzC
  rw [← hBeq, List.mem_toFinset] at hzB
  rw [← hCeq, List.mem_toFinset] at hzC
  have hfb : f z = qB.2 := fiberOverCode_map_output hzB
  have hfc : f z = qC.2 := fiberOverCode_map_output hzC
  apply hBC
  rw [← hBeq, ← hCeq, hfb.symm.trans hfc]

/-- Conversely, if $A$ is an $\varepsilon$-strong model for $x$ of length $n$,
there exists a partition of complexity at most $\varepsilon + O(\log n)$
containing a model $A'$ for $x$ such that $\# A' \le \# A$, and both
$\CT(A \mid A')$ and $\CT(A' \mid A)$ are bounded by $\varepsilon + O(\log n)$. -/
theorem IsStrongSetModel.exists_partition
    (U : Map) (hU : isOptimalConditional U)
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀
      (x : BitString) (n : Nat), x.length = n →
      ∀ (S : Finset BitString) (hS : x ∈ S)
        (epsilon : Nat), IsStrongSetModel T x S ⟨x, hS⟩ epsilon →
    ∃ (P : Finset (Finset BitString)) (S' : Finset BitString) (hS' : x ∈ S'),
      IsPartition P ∧
      S' ∈ P ∧
      S'.card ≤ S.card ∧
      partitionComplexity U P ≤
        (epsilon : ENat) + (logSlack c n : ENat) ∧
      totalCondK T (codedUniformOn S ⟨x, hS⟩).code
        (codedUniformOn S' ⟨x, hS'⟩).code ≤
          (epsilon : ENat) + (logSlack c n : ENat) ∧
      totalCondK T (codedUniformOn S' ⟨x, hS'⟩).code
        (codedUniformOn S ⟨x, hS⟩).code ≤
          (epsilon : ENat) + (logSlack c n : ENat) := by
  obtain ⟨c1, hc1⟩ :=
    hT.2 (elementThenProgDecompressor T)
      (elementThenProgDecompressor_partrec T hT.1)
  obtain ⟨c2, hc2⟩ :=
    hT.2 (fiberFromSetCodeDecompressor T)
      (fiberFromSetCodeDecompressor_partrec T hT.1)
  obtain ⟨c3, hc3⟩ :=
    hU.2 (partitionFromProgDecompressor T)
      (partitionFromProgDecompressor_partrec T hT.1)
  refine ⟨c1 + c2 + c3 + 2, ?_⟩
  intro x n hn S hxS epsilon hstrong
  -- Total program witnessing the strong model.
  obtain ⟨p, hpTotal, hpLen, hpProd⟩ :=
    (totalCondK_le_iff T (codedUniformOn S ⟨x, hxS⟩).code x epsilon).mp hstrong
  change p.length ≤ epsilon at hpLen
  set codeS := (codedUniformOn S ⟨x, hxS⟩).code with hcodeS_def
  set f := totalProgOutput T p hpTotal with hf_def
  have hfx : f x = codeS := (produces_eq_totalProgOutput hpTotal hpProd).symm
  set pairs := (allStrings n).map (fun x' => (x', f x')) with hpairs_def
  set S' := (fiberOverCode pairs codeS).toFinset with hS'_def
  have hcode : canonicalPointListOfCode codeS = canonicalFinsetList S :=
    canonicalPointListOfCode_codedUniformOn S ⟨x, hxS⟩
  -- x is in S'.
  have hxS' : x ∈ S' := by
    rw [hS'_def, List.mem_toFinset, mem_fiberOverCode_map]
    refine ⟨(mem_allStrings n x).mpr hn, hfx, ?_⟩
    rw [hcode, mem_canonicalFinsetList]; exact hxS
  set codeS' := (codedUniformOn S' ⟨x, hxS'⟩).code with hcodeS'_def
  -- S' ⊆ S, hence the cardinality bound.
  have hS'subset : S' ⊆ S := by
    intro a ha
    rw [hS'_def, List.mem_toFinset, mem_fiberOverCode_map] at ha
    have := ha.2.2
    rw [hcode, mem_canonicalFinsetList] at this
    exact this
  have hcard : S'.card ≤ S.card := Finset.card_le_card hS'subset
  -- The partition and its properties.
  set P := fiberPartition pairs with hP_def
  have hPart : IsPartition P := isPartition_fiberPartition (allStrings n) f
  have hS'memP : S' ∈ P := by
    rw [hP_def, fiberPartition, List.mem_toFinset, List.mem_map]
    refine ⟨(x, codeS), ?_, ?_⟩
    · rw [selfMemberPairs, List.mem_filter, decide_eq_true_eq]
      refine ⟨(mem_map_pair).mpr ⟨(mem_allStrings n x).mpr hn, hfx⟩, ?_⟩
      rw [hcode, mem_canonicalFinsetList]; exact hxS
    · rfl
  -- The actual output list of the executor.
  obtain ⟨ys, hys⟩ :=
    Part.dom_iff_mem.mp (totalProgramMapList_dom_of_total hpTotal (allStrings n))
  have hys_eq : ys = (allStrings n).map f := totalProgramMapList_eq_map hpTotal hys
  -- The fibre code equals codeS'.
  have hS'ne : S'.Nonempty := ⟨x, hxS'⟩
  have hfiber_code :
      canonicalImageCodeOfList (fiberOverCode pairs codeS) = codeS' := by
    rw [canonicalImageCodeOfList_eq_codedUniformOn (fiberOverCode pairs codeS) hS'ne]
  refine ⟨P, S', hxS', hPart, hS'memP, hcard, ?_, ?_, ?_⟩
  · -- Partition complexity bound.
    have hval : partitionPostFn (pairCode (Nat.bits n) p, []) ys = partitionCode P := by
      rw [hys_eq, partitionPostFn_eval, hP_def, partitionCode_fiberPartition]
    have hprod := partitionFromProgDecompressor_produces (T := T) n (y := ([] : BitString)) hys
    rw [hval] at hprod
    have hlen : (pairCode (Nat.bits n) p).length ≤ 2 * (Nat.bits n).length + 1 + epsilon := by
      rw [length_pairCode]; omega
    calc
      partitionComplexity U P
          = plainK U (partitionCode P) := rfl
      _ = condK U (partitionCode P) [] := rfl
      _ ≤ condK (partitionFromProgDecompressor T) (partitionCode P) [] + (c3 : ENat) :=
          hc3 (partitionCode P) []
      _ ≤ ((pairCode (Nat.bits n) p).length : ENat) + (c3 : ENat) := by
          gcongr
          exact sInf_le ⟨pairCode (Nat.bits n) p, hprod, rfl⟩
      _ ≤ (epsilon : ENat) + (logSlack (c1 + c2 + c3 + 2) n : ENat) := by
          have : (pairCode (Nat.bits n) p).length + c3 ≤
              epsilon + logSlack (c1 + c2 + c3 + 2) n := by
            unfold logSlack
            have h := hlen
            nlinarith [Nat.zero_le ((Nat.bits n).length)]
          exact_mod_cast this
  · -- CT(A | A'): decompressor 1.
    have hheadmem : (canonicalPointListOfCode codeS').headI ∈ S' := by
      rw [hcodeS'_def, canonicalPointListOfCode_codedUniformOn]
      exact headI_mem_canonicalFinsetList hS'ne
    have hfhead : f ((canonicalPointListOfCode codeS').headI) = codeS := by
      rw [hS'_def, List.mem_toFinset] at hheadmem
      exact fiberOverCode_map_output hheadmem
    have hprodhead : produces T p ((canonicalPointListOfCode codeS').headI) codeS := by
      have := totalProgOutput_produces T p hpTotal ((canonicalPointListOfCode codeS').headI)
      rw [← hf_def] at this
      rwa [hfhead] at this
    have hprod : produces (elementThenProgDecompressor T) p codeS' codeS :=
      elementThenProgDecompressor_produces rfl hprodhead
    have htotal : IsTotalProgram (elementThenProgDecompressor T) p :=
      elementThenProgDecompressor_total hpTotal
    calc
      totalCondK T codeS codeS'
          ≤ totalCondK (elementThenProgDecompressor T) codeS codeS' + (c1 : ENat) :=
          hc1 codeS codeS'
      _ ≤ (p.length : ENat) + (c1 : ENat) := by
          gcongr
          exact totalCondK_le_programLength htotal hprod
      _ ≤ (epsilon : ENat) + (logSlack (c1 + c2 + c3 + 2) n : ENat) := by
          have : p.length + c1 ≤ epsilon + logSlack (c1 + c2 + c3 + 2) n := by
            unfold logSlack
            nlinarith [Nat.zero_le ((Nat.bits n).length)]
          exact_mod_cast this
  · -- CT(A' | A): decompressor 2.
    have hval : fiberPostFn (pairCode (Nat.bits n) p, codeS) ys = codeS' := by
      rw [hys_eq, fiberPostFn_eval, ← hpairs_def, hfiber_code]
    have hprod := fiberFromSetCodeDecompressor_produces (T := T) n (B := codeS) hys
    rw [hval] at hprod
    have htotal : IsTotalProgram (fiberFromSetCodeDecompressor T) (pairCode (Nat.bits n) p) :=
      fiberFromSetCodeDecompressor_total hpTotal n
    have hlen : (pairCode (Nat.bits n) p).length ≤ 2 * (Nat.bits n).length + 1 + epsilon := by
      rw [length_pairCode]; omega
    calc
      totalCondK T codeS' codeS
          ≤ totalCondK (fiberFromSetCodeDecompressor T) codeS' codeS + (c2 : ENat) :=
          hc2 codeS' codeS
      _ ≤ ((pairCode (Nat.bits n) p).length : ENat) + (c2 : ENat) := by
          gcongr
          exact totalCondK_le_programLength htotal hprod
      _ ≤ (epsilon : ENat) + (logSlack (c1 + c2 + c3 + 2) n : ENat) := by
          have : (pairCode (Nat.bits n) p).length + c2 ≤
              epsilon + logSlack (c1 + c2 + c3 + 2) n := by
            unfold logSlack
            nlinarith [Nat.zero_le ((Nat.bits n).length)]
          exact_mod_cast this

/-! ### Strong Description Shift -/

/-- Strong models satisfy the description-shift property: if $A$ is an
$\varepsilon$-strong model for $x$, and $i \le \log \# A$, there is an
$\varepsilon + O(\log i)$-strong model $A'$ for $x$ with
$\# A' \le \# A / 2^i$ and $\KS(A') \le \KS(A) + i + O(\log i)$. -/
theorem strong_description_shift
    (U : Map) (hU : isOptimalConditional U)
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀
      (x : BitString) (S : Finset BitString) (hS : x ∈ S)
      (epsilon : Nat), IsStrongSetModel T x S ⟨x, hS⟩ epsilon →
      ∀ (i : Nat), 2^i ≤ S.card →
    ∃ S' : Finset BitString, ∃ (hS' : x ∈ S'),
      IsStrongSetModel T x S' ⟨x, hS'⟩
        (epsilon + logSlack c i) ∧
      S'.card * 2^i ≤ S.card ∧
      plainSetComplexity U S' ⟨x, hS'⟩ ≤
        plainSetComplexity U S ⟨x, hS⟩ +
          (i : ENat) + (logSlack c i : ENat) := by
  obtain ⟨cTotal, hTotal⟩ :=
    hT.2 (strongDescriptionChunkDecompressor T)
      (strongDescriptionChunkDecompressor_partrec T hT.1)
  obtain ⟨cPlain, hPlain⟩ :=
    plainSetComplexity_descriptionChunk_succ U hU
  let c := cTotal + cPlain + 10
  refine ⟨c, ?_⟩
  intro x S hxS epsilon hstrong i hi
  have hS : S.Nonempty := ⟨x, hxS⟩
  obtain ⟨p, hpTotal, hpLen, hpProd⟩ :=
    (totalCondK_le_iff T (codedUniformOn S hS).code x
      epsilon).mp hstrong
  change p.length ≤ epsilon at hpLen
  let S' := descriptionChunk S x (i + 1)
  have hxS' : x ∈ S' :=
    mem_descriptionChunk S x (i + 1) hxS
  refine ⟨S', hxS', ?_, ?_, ?_⟩
  · unfold IsStrongSetModel
    have hencodedTotal :
        IsTotalProgram (strongDescriptionChunkDecompressor T)
          (pairCode (Nat.bits i) p) :=
      strongDescriptionChunkDecompressor_total hpTotal i
    have hencodedProd :
        produces (strongDescriptionChunkDecompressor T)
          (pairCode (Nat.bits i) p) x
          (codedUniformOn S' ⟨x, hxS'⟩).code := by
      exact strongDescriptionChunkDecompressor_produces
        hS i hpProd hxS
    have hslack :
        2 * (Nat.bits i).length + 1 + cTotal ≤
          logSlack c i := by
      unfold logSlack c
      nlinarith [Nat.zero_le (Nat.bits i).length]
    calc
      totalCondK T (codedUniformOn S' ⟨x, hxS'⟩).code x
          ≤ totalCondK (strongDescriptionChunkDecompressor T)
              (codedUniformOn S' ⟨x, hxS'⟩).code x +
              (cTotal : ENat) :=
        hTotal _ _
      _ ≤ ((pairCode (Nat.bits i) p).length : ENat) +
            (cTotal : ENat) := by
        gcongr
        exact totalCondK_le_programLength
          hencodedTotal hencodedProd
      _ ≤ ((epsilon + logSlack c i : Nat) : ENat) := by
        rw [length_pairCode]
        exact_mod_cast (show
          (Nat.bits i).length + 1 + (Nat.bits i).length +
              p.length + cTotal ≤ epsilon + logSlack c i by
            omega)
  · exact card_descriptionChunk_succ_mul_pow_le S x i hi
  · have hbits :
        (Nat.bits (i + 1)).length ≤
          (Nat.bits i).length + 2 := by
      have hadd := length_natBits_add_le i 1
      norm_num at hadd ⊢
      exact hadd
    have hslack :
        1 + 2 * (Nat.bits (i + 1)).length + cPlain ≤
          logSlack c i := by
      unfold logSlack c
      nlinarith [Nat.zero_le (Nat.bits i).length]
    calc
      plainSetComplexity U S' ⟨x, hxS'⟩
          ≤ plainSetComplexity U S hS +
              ((i + 1 + 2 * (Nat.bits (i + 1)).length +
                cPlain : Nat) : ENat) :=
        hPlain S hS x i hxS
      _ ≤ plainSetComplexity U S hS +
            (i : ENat) + (logSlack c i : ENat) := by
        have hnat :
            i + 1 + 2 * (Nat.bits (i + 1)).length + cPlain ≤
              i + logSlack c i := by
          omega
        have henat :
            ((i + 1 + 2 * (Nat.bits (i + 1)).length +
              cPlain : Nat) : ENat) ≤
              ((i + logSlack c i : Nat) : ENat) := by
          exact_mod_cast hnat
        calc
          plainSetComplexity U S hS +
              ((i + 1 + 2 * (Nat.bits (i + 1)).length +
                cPlain : Nat) : ENat)
              ≤ plainSetComplexity U S hS +
                  ((i + logSlack c i : Nat) : ENat) :=
            add_le_add (le_refl _) henat
          _ = plainSetComplexity U S hS +
                (i : ENat) + (logSlack c i : ENat) := by
            push_cast
            rw [add_assoc]

end Kolmogorov
