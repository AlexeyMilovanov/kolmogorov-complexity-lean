import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Support

/-!
# Enumerator-uniform complexity bounds for standard blocks

The bounds `plainK_standardBlock_upper` and `plainKNat_omegaCount_lower` in
`BoundedComplexityLists` are stated with a constant that depends on the
enumerating code `q`.  VS40 Lemma 4 needs both of them *uniformly* in `q`, with
the `q`-dependence paid for by `C(q)` — concretely, by the plain complexity of
the canonical enumerator code `standardEnumeratorCode q`.

This file supplies both uniform versions.  In each case the decoder receives a
shortest plain program for `standardEnumeratorCode q` as a self-delimiting
prefix of its input, decodes `q` from it, and then runs the corresponding
fixed-code decoder; the extra framing costs `2 C(q) + O(1)` bits.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-! ### The completed dyadic block decoder, uniform in the code -/

/-- The completed-dyadic-block decoder, with the machine code as an input. -/
noncomputable def uniformBlockSelector (p : Code × BitString) : Part BitString :=
  completedDyadicBlockSelector p.1 p.2

theorem uniformBlockSelector_partrec : Partrec uniformBlockSelector := by
  have hm : Primrec completedDyadicBlockInputM :=
    bitsToNat_primrec.comp
      (decodeFirst_primrec'.comp decodeFirst_primrec')
  have hj : Primrec completedDyadicBlockInputJ :=
    bitsToNat_primrec.comp
      (decodeSecond_primrec'.comp decodeFirst_primrec')
  have hidx : Primrec completedDyadicBlockInputIndex :=
    decodeFixedWidthNatCode_primrec.comp decodeSecond_primrec'
  have hm' : Primrec (fun w : (Code × BitString) × ℕ =>
      completedDyadicBlockInputM w.1.2) :=
    hm.comp (Primrec.snd.comp Primrec.fst)
  have hj' : Primrec (fun w : (Code × BitString) × ℕ =>
      completedDyadicBlockInputJ w.1.2) :=
    hj.comp (Primrec.snd.comp Primrec.fst)
  have hidx' : Primrec (fun w : (Code × BitString) × ℕ =>
      completedDyadicBlockInputIndex w.1.2) :=
    hidx.comp (Primrec.snd.comp Primrec.fst)
  have hpow : Primrec (fun w : (Code × BitString) × ℕ =>
      2 ^ completedDyadicBlockInputJ w.1.2) :=
    Kolmogorov.CodedFiniteDistribution.twoPow_primrec.comp hj'
  have hend : Primrec (fun w : (Code × BitString) × ℕ =>
      (completedDyadicBlockInputIndex w.1.2 + 1) *
        2 ^ completedDyadicBlockInputJ w.1.2) :=
    Primrec.nat_mul.comp
      (Primrec.nat_add.comp hidx' (Primrec.const 1)) hpow
  have hstage : Primrec (fun w : (Code × BitString) × ℕ =>
      boundedOutputStage w.1.1 (completedDyadicBlockInputM w.1.2) w.2) :=
    boundedOutputStage_primrec_uniform.comp
      (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst) hm')
        Primrec.snd)
  have hcheck : Computable₂ (fun (w : Code × BitString) (t : ℕ) =>
      decide
        ((completedDyadicBlockInputIndex w.2 + 1) *
            2 ^ completedDyadicBlockInputJ w.2 ≤
          (boundedOutputStage w.1
            (completedDyadicBlockInputM w.2) t).length)) :=
    (PrimrecPred.decide
      (Primrec.nat_le.comp hend
        (Primrec.list_length.comp hstage))).to_comp.to₂
  have hsearch : Partrec (fun w : Code × BitString =>
      Nat.rfind (fun t => Part.some (decide
        ((completedDyadicBlockInputIndex w.2 + 1) *
            2 ^ completedDyadicBlockInputJ w.2 ≤
          (boundedOutputStage w.1
            (completedDyadicBlockInputM w.2) t).length)))) :=
    Partrec.rfind hcheck.partrec₂
  have hstart : Primrec (fun w : (Code × BitString) × ℕ =>
      completedDyadicBlockInputIndex w.1.2 *
        2 ^ completedDyadicBlockInputJ w.1.2) :=
    Primrec.nat_mul.comp hidx' hpow
  have hblock : Primrec (fun w : (Code × BitString) × ℕ =>
      (boundedOutputStage w.1.1
        (completedDyadicBlockInputM w.1.2) w.2).drop
          (completedDyadicBlockInputIndex w.1.2 *
            2 ^ completedDyadicBlockInputJ w.1.2) |>.take
              (2 ^ completedDyadicBlockInputJ w.1.2)) :=
    Primrec.list_take.comp hpow
      (Primrec.list_drop.comp hstart hstage)
  have hcode : Computable₂ (fun (w : Code × BitString) (t : ℕ) =>
      canonicalUniformCodeOfList
        (canonicalFinsetList
          (((boundedOutputStage w.1
              (completedDyadicBlockInputM w.2) t).drop
                (completedDyadicBlockInputIndex w.2 *
                  2 ^ completedDyadicBlockInputJ w.2) |>.take
                    (2 ^ completedDyadicBlockInputJ w.2)).toFinset))) :=
    (canonicalUniformCodeOfList_primrec.comp
      (canonicalFinsetList_toFinset_primrec.comp hblock)).to_comp.to₂
  unfold uniformBlockSelector completedDyadicBlockSelector
  exact (Partrec.bind hsearch hcode.partrec₂).of_eq (fun _ => rfl)

/-- Decoder for the enumerator-uniform block bound: the input is
`pairCode pQ w`, where `pQ` is a plain program for `standardEnumeratorCode q`
and `w` is the fixed-code block input `completedDyadicBlockInput`. -/
noncomputable def uniformBlockDecoder (V : Map) : Map := fun input =>
  (V (decodeFirst input.1, [])).bind fun q_enum =>
    (Part.ofOption
      (Encodable.decode (α := Code) (bitsToNat q_enum))).bind fun q =>
      uniformBlockSelector (q, decodeSecond input.1)

theorem uniformBlockDecoder_partrec (V : Map) (hV : isDecompressor V) :
    Partrec (uniformBlockDecoder V) := by
  have hrun : Partrec (fun input : BitString × BitString =>
      V (decodeFirst input.1, [])) :=
    Partrec.comp hV
      (Computable.pair (decodeFirst_computable.comp Computable.fst)
        (Computable.const []))
  have hdecode : Partrec (fun w : (BitString × BitString) × BitString =>
      Part.ofOption (Encodable.decode (α := Code) (bitsToNat w.2))) :=
    Computable.ofOption
      (Computable.decode.comp (bitsToNat_primrec.to_comp.comp Computable.snd))
  have hsel : Partrec
      (fun w : ((BitString × BitString) × BitString) × Code =>
        uniformBlockSelector (w.2, decodeSecond w.1.1.1)) :=
    uniformBlockSelector_partrec.comp
      (Computable.pair Computable.snd
        (decodeSecond_computable.comp
          (Computable.fst.comp (Computable.fst.comp Computable.fst))))
  exact (Partrec.bind hrun (Partrec.bind hdecode hsel.to₂).to₂).of_eq
    (fun _ => rfl)

/-- Enumerator-uniform version of `plainK_standardBlock_upper`: the plain
complexity of a standard block is at most `m - j` plus `O(C(q) + log m)`, with
an absolute constant. -/
theorem plainK_standardBlock_upper_uniform
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ (q : Code) (m j : ℕ) (x : BitString)
      (hx : x ∈ standardBlock q m j x),
      let hA : (standardBlock q m j x).Nonempty := ⟨x, hx⟩
      plainK V (codedUniformOn (standardBlock q m j x) hA).code ≤
        ((m - j : ℕ) : ENat) +
          (C : ENat) * plainK V (standardEnumeratorCode q) +
          (logSlack C m : ENat) := by
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV
      (fun z : BitString => uniformBlockDecoder V (z, []))
      ((uniformBlockDecoder_partrec V hV.1).comp
        (Computable.pair Computable.id (Computable.const [])))
  obtain ⟨Clen, hlen⟩ := plainKLeLength V hV
  refine ⟨Clen + Cmap + 10, ?_⟩
  set C := Clen + Cmap + 10 with hC
  intro q m j x hx hA
  have hQfinite : plainK V (standardEnumeratorCode q) ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top
        ((standardEnumeratorCode q).length + Clen)))
      (hlen (standardEnumeratorCode q))
  obtain ⟨pQ, hpQ, hpQLength⟩ :=
    exists_program_of_KP_ne_top
      (M := V) (x := standardEnumeratorCode q) (y := []) hQfinite
  have hjm : j ≤ m := standardBlock_exponent_le q m j x hx
  have hjlen : (Nat.bits j).length ≤ (Nat.bits m).length :=
    length_natBits_mono hjm
  set blockIdx := completedDyadicBlockIndex q m j x with hblockIdx
  have hidx : blockIdx < 2 ^ (m - j + 1) := by
    have h := completedDyadicBlockIndex_lt_two_pow q (m - j) j x
    rw [Nat.sub_add_cancel hjm] at h
    exact h
  set w := completedDyadicBlockInput m j blockIdx (m - j + 1) with hw
  set input := pairCode pQ w with hinput
  have hwLength :
      w.length = (m - j + 1) + 4 * (Nat.bits m).length +
        2 * (Nat.bits j).length + 3 :=
    completedDyadicBlockInput_length (m := m) (j := j)
      (blockIdx := blockIdx) (blockWidth := m - j + 1) hidx
  have hsel :
      (codedUniformOn (standardBlock q m j x) hA).code ∈
        uniformBlockDecoder V (input, []) := by
    have hrec :
        (codedUniformOn (standardBlock q m j x) hA).code ∈
          completedDyadicBlockSelector q w :=
      completedDyadicBlockSelector_recovers_standardBlock q m j x hx
    unfold uniformBlockDecoder
    simp only [hinput, decodeFirst_pairCode, decodeSecond_pairCode]
    rw [Part.mem_bind_iff]
    refine ⟨standardEnumeratorCode q, hpQ, ?_⟩
    unfold standardEnumeratorCode
    simp only [bitsToNat_bits, Encodable.encodek]
    rw [Part.mem_bind_iff]
    exact ⟨q, by simp, hrec⟩
  have hbudget :
      input.length + Clen + Cmap ≤
        (m - j) + 2 * pQ.length + (C * (Nat.bits m).length + C) := by
    rw [hinput, length_pairCode, hwLength]
    have h6 : 6 ≤ C := by omega
    have hc6 : 6 * (Nat.bits m).length ≤ C * (Nat.bits m).length := by
      exact Nat.mul_le_mul_right _ h6
    omega
  calc
    plainK V (codedUniformOn (standardBlock q m j x) hA).code
        ≤ plainK V input + (Cmap : ENat) := hmap input _ hsel
    _ ≤ ((input.length : ENat) + (Clen : ENat)) + (Cmap : ENat) := by
      gcongr
      exact hlen input
    _ = ((input.length + Clen + Cmap : ℕ) : ENat) := by push_cast; ring
    _ ≤ (((m - j) + 2 * pQ.length + (C * (Nat.bits m).length + C) : ℕ) :
          ENat) := by exact_mod_cast hbudget
    _ = ((m - j : ℕ) : ENat) + 2 * (pQ.length : ENat) +
          (logSlack C m : ENat) := by
      unfold logSlack
      push_cast
      ring
    _ ≤ ((m - j : ℕ) : ENat) +
          (C : ENat) * plainK V (standardEnumeratorCode q) +
          (logSlack C m : ENat) := by
      have hcoef : (2 : ENat) ≤ (C : ENat) := by
        have : (2 : ℕ) ≤ C := by omega
        exact_mod_cast this
      have hpQLengthEq : (pQ.length : ENat) =
          plainK V (standardEnumeratorCode q) := hpQLength
      rw [hpQLengthEq]
      gcongr

/-! ### The diagonal decoder, uniform in the code -/

/- Keep the nested encodings opaque while composing the uniform diagonal
selector with unbounded search. -/
attribute [local irreducible] Primcodable.prod Primcodable.list

open Classical in
/-- Decoder for the enumerator-uniform lower bound on `C(Ω_m)`: the input is
`pairCode pQ (pairCode (Nat.bits e) p)` where `pQ` is a plain program for
`standardEnumeratorCode q`, `p` is a plain program for `Nat.bits (Ω_m)` and
`m = |p| + e`.  It outputs a string of length `m + 1` that the enumeration
never prints, hence a string of complexity greater than `m`. -/
noncomputable def uniformOmegaDiagonalDecoder (V : Map) : Map := fun input =>
  (V (decodeFirst input.1, [])).bind fun q_enum =>
    (Part.ofOption
      (Encodable.decode (α := Code) (bitsToNat q_enum))).bind fun q =>
      omegaDiagonalSelector V q (decodeSecond input.1)

/-- The diagonal selector is partial recursive uniformly in the machine code. -/
theorem omegaDiagonalSelector_partrec_uniform (V : Map) (hV : isDecompressor V) :
    Partrec (fun w : Code × BitString => omegaDiagonalSelector V w.1 w.2) := by
  have hrun : Partrec (fun w : Code × BitString => V (decodeSecond w.2, [])) :=
    Partrec.comp hV
      (Computable.pair (decodeSecond_computable.comp Computable.snd)
        (Computable.const []))
  have hm : Primrec (fun st : ((Code × BitString) × BitString) × ℕ =>
      (decodeSecond st.1.1.2).length + bitsToNat (decodeFirst st.1.1.2)) :=
    Primrec.nat_add.comp
      (Primrec.list_length.comp
        (decodeSecond_primrec.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (bitsToNat_primrec.comp
        (decodeFirst_primrec.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
  have hstage : Primrec (fun st : ((Code × BitString) × BitString) × ℕ =>
      boundedOutputStage st.1.1.1
        ((decodeSecond st.1.1.2).length + bitsToNat (decodeFirst st.1.1.2))
          st.2) :=
    boundedOutputStage_primrec_uniform.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) hm)
        Primrec.snd)
  have hcheck : Computable₂
      (fun (u : (Code × BitString) × BitString) (t : ℕ) =>
      (boundedOutputStage u.1.1
        ((decodeSecond u.1.2).length + bitsToNat (decodeFirst u.1.2)) t).length ==
          bitsToNat u.2) :=
    (Primrec.beq.comp
      (Primrec.list_length.comp hstage)
      (bitsToNat_primrec.comp (Primrec.snd.comp Primrec.fst))).to_comp.to₂
  have hsearch : Partrec (fun u : (Code × BitString) × BitString =>
      Nat.rfind (fun t => Part.some
        ((boundedOutputStage u.1.1
          ((decodeSecond u.1.2).length +
            bitsToNat (decodeFirst u.1.2)) t).length ==
            bitsToNat u.2))) :=
    Partrec.rfind hcheck.partrec₂
  have hstrings : Primrec (fun st : ((Code × BitString) × BitString) × ℕ =>
      canonicalFinsetList (stringsOfLength
        ((decodeSecond st.1.1.2).length +
          bitsToNat (decodeFirst st.1.1.2) + 1))) := by
    have h_pred := canonicalFinsetList_toFinset_primrec.comp
      (allStrings_primrec.comp (Primrec.succ.comp hm))
    have h_eq : (fun (st : ((Code × BitString) × BitString) × ℕ) =>
        canonicalFinsetList (stringsOfLength
          ((decodeSecond st.1.1.2).length + bitsToNat (decodeFirst st.1.1.2) + 1))) =
        (fun (a : ((Code × BitString) × BitString) × ℕ) =>
          canonicalFinsetList (allStrings
            ((decodeSecond a.1.1.2).length + bitsToNat (decodeFirst a.1.1.2)).succ).toFinset) := by
      ext a
      dsimp [stringsOfLength]
      rfl
    rw [h_eq]
    exact h_pred
  have hnotmem : Primrec₂
      (fun (st : ((Code × BitString) × BitString) × ℕ) (s : BitString) =>
        decide (s ∉ boundedOutputStage st.1.1.1
          ((decodeSecond st.1.1.2).length +
            bitsToNat (decodeFirst st.1.1.2)) st.2)) := by
    refine (Primrec.not.comp
      (bitString_mem_primrec.comp Primrec.snd (hstage.comp Primrec.fst))).to₂.of_eq ?_
    intro st s
    simp
  have hfindOpt : Primrec (fun st : ((Code × BitString) × BitString) × ℕ =>
      (canonicalFinsetList (stringsOfLength
        ((decodeSecond st.1.1.2).length +
          bitsToNat (decodeFirst st.1.1.2) + 1))).find?
          (fun s => decide (s ∉ boundedOutputStage st.1.1.1
            ((decodeSecond st.1.1.2).length +
              bitsToNat (decodeFirst st.1.1.2)) st.2))) :=
    list_find?_primrec hstrings hnotmem
  have hfindPart : Partrec (fun st : ((Code × BitString) × BitString) × ℕ =>
      Part.ofOption
        ((canonicalFinsetList (stringsOfLength
          ((decodeSecond st.1.1.2).length +
            bitsToNat (decodeFirst st.1.1.2) + 1))).find?
            (fun s => decide (s ∉ boundedOutputStage st.1.1.1
              ((decodeSecond st.1.1.2).length +
                bitsToNat (decodeFirst st.1.1.2)) st.2)))) :=
    hfindOpt.to_comp.ofOption
  have hpure : Partrec₂
      (fun (_ : ((Code × BitString) × BitString) × ℕ) (x : BitString) =>
        Part.some x) :=
    (Partrec.comp Partrec.some Computable.snd).to₂
  have hfind : Partrec₂
      (fun (u : (Code × BitString) × BitString) (t : ℕ) =>
      (Part.ofOption
        ((canonicalFinsetList (stringsOfLength
          ((decodeSecond u.1.2).length +
            bitsToNat (decodeFirst u.1.2) + 1))).find?
            (fun s => decide (s ∉ boundedOutputStage u.1.1
              ((decodeSecond u.1.2).length +
                bitsToNat (decodeFirst u.1.2)) t)))).bind
        (fun x => Part.some x)) :=
    (Partrec.bind hfindPart hpure).to₂
  have hafter : Partrec₂ (fun (w : Code × BitString) (omegaBits : BitString) =>
      (Nat.rfind (fun t => Part.some
        ((boundedOutputStage w.1
          ((decodeSecond w.2).length + bitsToNat (decodeFirst w.2)) t).length ==
            bitsToNat omegaBits))).bind
        (fun t =>
          (Part.ofOption
            ((canonicalFinsetList (stringsOfLength
              ((decodeSecond w.2).length +
                bitsToNat (decodeFirst w.2) + 1))).find?
                (fun s => decide (s ∉ boundedOutputStage w.1
                  ((decodeSecond w.2).length +
                    bitsToNat (decodeFirst w.2)) t)))).bind
            (fun x => Part.some x))) :=
    (Partrec.bind hsearch hfind).to₂
  unfold omegaDiagonalSelector
  exact (Partrec.bind hrun hafter).of_eq (fun a => rfl)

theorem uniformOmegaDiagonalDecoder_partrec (V : Map) (hV : isDecompressor V) :
    Partrec (uniformOmegaDiagonalDecoder V) := by
  have hrun : Partrec (fun input : BitString × BitString =>
      V (decodeFirst input.1, [])) :=
    Partrec.comp hV
      (Computable.pair (decodeFirst_computable.comp Computable.fst)
        (Computable.const []))
  have hdecode : Partrec (fun w : (BitString × BitString) × BitString =>
      Part.ofOption (Encodable.decode (α := Code) (bitsToNat w.2))) :=
    Computable.ofOption
      (Computable.decode.comp (bitsToNat_primrec.to_comp.comp Computable.snd))
  have hsel : Partrec
      (fun w : ((BitString × BitString) × BitString) × Code =>
        omegaDiagonalSelector V w.2 (decodeSecond w.1.1.1)) :=
    (omegaDiagonalSelector_partrec_uniform V hV).comp
      (Computable.pair Computable.snd
        (decodeSecond_computable.comp
          (Computable.fst.comp (Computable.fst.comp Computable.fst))))
  exact (Partrec.bind hrun (Partrec.bind hdecode hsel.to₂).to₂).of_eq
    (fun _ => rfl)

/-- Enumerator-uniform version of `plainKNat_omegaCount_lower`. -/
theorem plainKNat_omegaCount_lower_uniform
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ (q : Code), IsCodeFor q V → ∀ m : ℕ,
      (m : ENat) ≤
        plainKNat V (omegaCount q m) +
          (C : ENat) * plainK V (standardEnumeratorCode q) +
          (logSlack C m : ENat) := by
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV
      (fun z : BitString => uniformOmegaDiagonalDecoder V (z, []))
      ((uniformOmegaDiagonalDecoder_partrec V hV.1).comp
        (Computable.pair Computable.id (Computable.const [])))
  obtain ⟨Clen, hlen⟩ := plainKLeLength V hV
  refine ⟨Clen + Cmap + 6, ?_⟩
  set C := Clen + Cmap + 6 with hC
  intro q hq m
  have hfinite : plainK V (Nat.bits (omegaCount q m)) ≠ ⊤ := by
    intro htop
    have h := hlen (Nat.bits (omegaCount q m))
    rw [htop, top_le_iff] at h
    exact ENat.coe_ne_top _ h
  have hfinite' : KP V (Nat.bits (omegaCount q m)) [] ≠ ⊤ := hfinite
  obtain ⟨p, hp, hpLength⟩ := exists_program_of_KP_ne_top hfinite'
  have hpLengthEq : (p.length : ENat) = plainKNat V (omegaCount q m) := hpLength
  have hQfinite : plainK V (standardEnumeratorCode q) ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top
        ((standardEnumeratorCode q).length + Clen)))
      (hlen (standardEnumeratorCode q))
  obtain ⟨pQ, hpQ, hpQLength⟩ :=
    exists_program_of_KP_ne_top
      (M := V) (x := standardEnumeratorCode q) (y := []) hQfinite
  have hpQLengthEq : (pQ.length : ENat) =
      plainK V (standardEnumeratorCode q) := hpQLength
  by_cases hpm : m ≤ p.length
  · calc
      (m : ENat) ≤ (p.length : ENat) := by exact_mod_cast hpm
      _ = plainKNat V (omegaCount q m) := hpLengthEq
      _ ≤ plainKNat V (omegaCount q m) +
            (C : ENat) * plainK V (standardEnumeratorCode q) +
            (logSlack C m : ENat) := by
        have h1 : plainKNat V (omegaCount q m) ≤
            plainKNat V (omegaCount q m) +
              (C : ENat) * plainK V (standardEnumeratorCode q) :=
          le_self_add
        exact h1.trans le_self_add
  · have hplt : p.length < m := Nat.lt_of_not_ge hpm
    set e := m - p.length with he
    have hm : m = p.length + e := by omega
    obtain ⟨x, hxSelector, _, hxMissing⟩ :=
      omegaDiagonalSelector_intended_input hV.1 q hm hp
    set input := pairCode pQ (pairCode (Nat.bits e) p) with hinput
    have hxInput : x ∈ uniformOmegaDiagonalDecoder V (input, []) := by
      unfold uniformOmegaDiagonalDecoder
      simp only [hinput, decodeFirst_pairCode, decodeSecond_pairCode]
      rw [Part.mem_bind_iff]
      refine ⟨standardEnumeratorCode q, hpQ, ?_⟩
      unfold standardEnumeratorCode
      simp only [bitsToNat_bits, Encodable.encodek]
      rw [Part.mem_bind_iff]
      exact ⟨q, by simp, hxSelector⟩
    have hxLower : (m : ENat) < plainK V x :=
      plainK_gt_of_not_mem_completed hq hxMissing
    have hxUpper : plainK V x ≤ plainK V input + (Cmap : ENat) :=
      hmap _ _ hxInput
    have hmx : (m : ENat) <
        ((input.length : ENat) + (Clen : ENat)) + (Cmap : ENat) :=
      lt_of_lt_of_le hxLower (hxUpper.trans (by gcongr; exact hlen input))
    have hmxNat : m < input.length + Clen + Cmap := by exact_mod_cast hmx
    have hbits : (Nat.bits e).length ≤ (Nat.bits m).length :=
      length_natBits_mono (by omega)
    have hCm : 6 * (Nat.bits m).length ≤ C * (Nat.bits m).length :=
      Nat.mul_le_mul_right _ (by omega)
    have hfinal : m ≤ p.length + 2 * pQ.length +
        (C * (Nat.bits m).length + C) := by
      rw [hinput, length_pairCode, length_pairCode] at hmxNat
      omega
    calc
      (m : ENat) ≤ ((p.length + 2 * pQ.length +
            (C * (Nat.bits m).length + C) : ℕ) : ENat) := by
        exact_mod_cast hfinal
      _ = (p.length : ENat) + 2 * (pQ.length : ENat) +
            (logSlack C m : ENat) := by
        unfold logSlack
        push_cast
        ring
      _ ≤ plainKNat V (omegaCount q m) +
            (C : ENat) * plainK V (standardEnumeratorCode q) +
            (logSlack C m : ENat) := by
        have hcoef : (2 : ENat) ≤ (C : ENat) := by
          have : (2 : ℕ) ≤ C := by omega
          exact_mod_cast this
        rw [hpLengthEq, hpQLengthEq]
        gcongr

end Kolmogorov
