import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseEnumeration
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaEquivalence

/-!
# Fixed-width rank decoding of the add-noise candidate truncations

If a string `x` has fewer than `2 ^ k` candidate truncations at parameters
`(l, i, j)`, then each candidate is determined, given `x`, by its rank in the
append-only enumeration of `AddNoiseEnumeration.lean`.  Writing that rank in
exactly `k` bits and prefixing the (logarithmically short) parameters `(l,i,j)`
gives a program of length `k + O(log (|x| + l + i + j + k))` for the canonical
uniform code of the candidate, conditioned on `x`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-! ### The packed rank program -/

/-- Program of the rank decoder: the parameters `(l, i, j)` in a self-delimiting
prefix, followed by the `k`-bit address of the rank `r`. -/
def noiseRankProgram (l i j k r : ℕ) : BitString :=
  pairCode (pairCode (Nat.bits l) (pairCode (Nat.bits i) (Nat.bits j)))
    (chunkAddress r k)

/-- The noise length packed into a rank program. -/
def noiseRankL (p : BitString) : ℕ := bitsToNat (decodeFirst (decodeFirst p))
/-- The complexity parameter packed into a rank program. -/
def noiseRankI (p : BitString) : ℕ := bitsToNat (decodeFirst (decodeSecond (decodeFirst p)))
/-- The size parameter packed into a rank program. -/
def noiseRankJ (p : BitString) : ℕ := bitsToNat (decodeSecond (decodeSecond (decodeFirst p)))
/-- The rank packed into a rank program. -/
def noiseRankR (p : BitString) : ℕ := bitsToNat (decodeSecond p)

@[simp] theorem noiseRankL_program (l i j k r : ℕ) :
    noiseRankL (noiseRankProgram l i j k r) = l := by
  simp [noiseRankL, noiseRankProgram, decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem noiseRankI_program (l i j k r : ℕ) :
    noiseRankI (noiseRankProgram l i j k r) = i := by
  simp [noiseRankI, noiseRankProgram, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

@[simp] theorem noiseRankJ_program (l i j k r : ℕ) :
    noiseRankJ (noiseRankProgram l i j k r) = j := by
  simp [noiseRankJ, noiseRankProgram, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

@[simp] theorem noiseRankR_program (l i j k r : ℕ) :
    noiseRankR (noiseRankProgram l i j k r) = r := by
  simp [noiseRankR, noiseRankProgram, decodeSecond_pairCode, bitsToNat_chunkAddress]

theorem noiseRankL_primrec : Primrec noiseRankL :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp decodeFirst_primrec)
theorem noiseRankI_primrec : Primrec noiseRankI :=
  bitsToNat_primrec.comp
    (decodeFirst_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec))
theorem noiseRankJ_primrec : Primrec noiseRankJ :=
  bitsToNat_primrec.comp
    (decodeSecond_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec))
theorem noiseRankR_primrec : Primrec noiseRankR :=
  bitsToNat_primrec.comp decodeSecond_primrec

/-- Length of the packed rank program. -/
theorem length_noiseRankProgram (l i j k r : ℕ) (hr : r < 2 ^ k) :
    (noiseRankProgram l i j k r).length =
      2 * (2 * (Nat.bits l).length + 1 + (2 * (Nat.bits i).length + 1 +
        (Nat.bits j).length)) + 1 + k := by
  rw [noiseRankProgram, length_pairCode, length_pairCode, length_pairCode,
    chunkAddress_length r k hr]
  ring

/-! ### Stability of the enumeration under time -/

theorem noiseCandidateTruncationAppearanceCodes_prefix_of_le
    (c : Code) (x : BitString) (l i j : ℕ) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    noiseCandidateTruncationAppearanceCodes c x l i j t₁ <+:
      noiseCandidateTruncationAppearanceCodes c x l i j t₂ := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    exact ih.trans (noiseCandidateTruncationAppearanceCodes_prefix c x l i j _)

/-- Indexing below the length of a prefix is stable. -/
theorem getD_eq_of_prefix {l₁ l₂ : List BitString} (h : l₁ <+: l₂)
    {n : ℕ} (hn : n < l₁.length) :
    l₁.getD n [] = l₂.getD n [] := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hn]

/-! ### The decoder -/

/-- Given the string `x` as condition and a packed rank program, search for the
first stage at which the enumeration is long enough and return the entry at the
requested rank. -/
noncomputable def noiseRankDecoder (c : Code) : BitString → BitString →. BitString :=
  fun x p =>
    (Nat.rfind (fun t => Part.some (decide (noiseRankR p <
      (noiseCandidateTruncationAppearanceCodes c x (noiseRankL p) (noiseRankI p)
        (noiseRankJ p) t).length)))).bind
      (fun t => Part.some ((noiseCandidateTruncationAppearanceCodes c x (noiseRankL p)
        (noiseRankI p) (noiseRankJ p) t).getD (noiseRankR p) []))

section DecoderPartrec
attribute [local irreducible] noiseCandidateTruncationAppearanceCodes
  noiseRankL noiseRankI noiseRankJ noiseRankR

theorem noiseRankDecoder_partrec (c : Code) :
    Partrec (fun q : BitString × BitString => noiseRankDecoder c q.1 q.2) := by
  have hcodes : Computable (fun st : (BitString × BitString) × ℕ =>
      noiseCandidateTruncationAppearanceCodes c st.1.1 (noiseRankL st.1.2)
        (noiseRankI st.1.2) (noiseRankJ st.1.2) st.2) :=
    (noiseCandidateTruncationAppearanceCodes_computable c).comp
      ((((Computable.fst.comp Computable.fst).pair
        (((noiseRankL_primrec.to_comp).comp (Computable.snd.comp Computable.fst)).pair
          ((noiseRankJ_primrec.to_comp).comp
            (Computable.snd.comp Computable.fst)))).pair
        ((noiseRankI_primrec.to_comp).comp
          (Computable.snd.comp Computable.fst))).pair Computable.snd)
  have hrank : Computable (fun st : (BitString × BitString) × ℕ => noiseRankR st.1.2) :=
    (noiseRankR_primrec.to_comp).comp (Computable.snd.comp Computable.fst)
  have hlt : Computable (fun q : ℕ × ℕ => decide (q.1 < q.2)) := by
    obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel (α := ℕ) (· < ·))
    convert h.to_comp
  have hcheck : Computable (fun st : (BitString × BitString) × ℕ =>
      decide (noiseRankR st.1.2 <
        (noiseCandidateTruncationAppearanceCodes c st.1.1 (noiseRankL st.1.2)
          (noiseRankI st.1.2) (noiseRankJ st.1.2) st.2).length)) :=
    hlt.comp (hrank.pair (Computable.list_length.comp hcodes))
  have hpost : Computable (fun st : (BitString × BitString) × ℕ =>
      (noiseCandidateTruncationAppearanceCodes c st.1.1 (noiseRankL st.1.2)
        (noiseRankI st.1.2) (noiseRankJ st.1.2) st.2).getD (noiseRankR st.1.2) []) :=
    ((Primrec.list_getD ([] : BitString)).to_comp).comp hcodes hrank
  refine (Partrec.bind (Partrec.rfind hcheck.to₂.partrec₂) hpost.to₂.partrec₂).of_eq
    (fun q => ?_)
  unfold noiseRankDecoder
  refine congr_arg₂ Part.bind (congr_arg Nat.rfind ?_) ?_
  · funext t; exact PFun.coe_val _ t
  · funext t; exact PFun.coe_val _ t

theorem mem_noiseRankDecoder_of_rank
    (c : Code) (x : BitString) (l i j k r t : ℕ) {w : BitString}
    (hlt : r < (noiseCandidateTruncationAppearanceCodes c x l i j t).length)
    (hget : (noiseCandidateTruncationAppearanceCodes c x l i j t).getD r [] = w) :
    w ∈ noiseRankDecoder c x (noiseRankProgram l i j k r) := by
  classical
  set P : ℕ → Prop := fun s =>
    r < (noiseCandidateTruncationAppearanceCodes c x l i j s).length with hP
  have hex : ∃ s, P s := ⟨t, hlt⟩
  set t₀ := Nat.find hex with ht₀
  have ht₀P : P t₀ := Nat.find_spec hex
  have ht₀le : t₀ ≤ t := Nat.find_le hlt
  have hstable :
      (noiseCandidateTruncationAppearanceCodes c x l i j t₀).getD r [] = w := by
    rw [getD_eq_of_prefix
      (noiseCandidateTruncationAppearanceCodes_prefix_of_le c x l i j ht₀le) ht₀P]
    exact hget
  unfold noiseRankDecoder
  simp only [noiseRankL_program, noiseRankI_program, noiseRankJ_program,
    noiseRankR_program]
  rw [Part.mem_bind_iff]
  refine ⟨t₀, ?_, ?_⟩
  · refine Nat.mem_rfind.mpr ⟨by simpa using ht₀P, ?_⟩
    intro m hm
    have hm' : ¬ P m := Nat.find_min hex hm
    simpa using Nat.le_of_not_lt hm'
  · simpa using hstable.symm

/-! ### The conditional complexity bound -/

/-- The packed rank program, together with a machine constant, fits in `k` bits
plus logarithmic slack. -/
private theorem noiseRankProgram_length_slack (C : ℕ) (x : BitString) (l i j k r : ℕ)
    (hrk : r < 2 ^ k) :
    (noiseRankProgram l i j k r).length + C ≤
      k + logSlack (15 + C) (x.length + l + i + j + k) := by
  set M := x.length + l + i + j + k with hM
  set W := (Nat.bits M).length with hW
  have hlM : (Nat.bits l).length ≤ W := length_natBits_mono (by omega)
  have hiM : (Nat.bits i).length ≤ W := length_natBits_mono (by omega)
  have hjM : (Nat.bits j).length ≤ W := length_natBits_mono (by omega)
  have hlog : 10 * W + 5 + C ≤ logSlack (15 + C) M := by
    unfold logSlack
    rw [← hW]
    nlinarith [Nat.zero_le W, Nat.zero_le (C * W)]
  rw [length_noiseRankProgram l i j k r hrk]
  omega

/-- **Leaf packet 2.**  When `x` has fewer than `2 ^ k` candidate truncations at
parameters `(l, i, j)`, every candidate has conditional plain complexity at most
`k` plus logarithmic slack, given `x`. -/
theorem condK_noiseCandidate_of_card_lt_pow
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (l i j k : ℕ) (A : Finset BitString) (hA : A.Nonempty),
      A ∈ noiseCandidateTruncations U x l i j →
      (noiseCandidateTruncations U x l i j).card < 2 ^ k →
      condK V (codedUniformOn A hA).code x ≤
        ((k + logSlack c (x.length + l + i + j + k) : ℕ) : ENat) := by
  obtain ⟨cU, hcU⟩ : ∃ cU : Code, IsCodeFor cU U :=
    Nat.Partrec.Code.exists_code.mp hU.1.1
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV (noiseRankDecoder cU)
    (noiseRankDecoder_partrec cU)
  refine ⟨15 + C, ?_⟩
  intro x l i j k A hA hmem hcard
  obtain ⟨_, _, hiff, hlen⟩ := noiseCandidateTruncationAppearanceCodes_spec hcU
  obtain ⟨t, ht⟩ := (hiff x l i j A).mp hmem
  rw [canonicalUniformCodeOfList_canonicalFinsetList A hA] at ht
  obtain ⟨r, hr, hget⟩ : ∃ r, r < (noiseCandidateTruncationAppearanceCodes cU x l i j t).length ∧
      (noiseCandidateTruncationAppearanceCodes cU x l i j t).getD r [] =
        (codedUniformOn A hA).code := by
    rw [List.mem_iff_getElem] at ht
    obtain ⟨r, hr, hget⟩ := ht
    exact ⟨r, hr, by simp [List.getD_eq_getElem?_getD, hr, hget]⟩
  have hrk : r < 2 ^ k :=
    lt_of_lt_of_le hr ((hlen x l i j t).trans_lt hcard).le
  have hmemdec : (codedUniformOn A hA).code ∈
      noiseRankDecoder cU x (noiseRankProgram l i j k r) :=
    mem_noiseRankDecoder_of_rank cU x l i j k r t hr hget
  have hbound := hC x (noiseRankProgram l i j k r) _ hmemdec
  have hslack := noiseRankProgram_length_slack C x l i j k r hrk
  calc condK V (codedUniformOn A hA).code x
      ≤ ((noiseRankProgram l i j k r).length : ENat) + (C : ENat) := hbound
    _ = (((noiseRankProgram l i j k r).length + C : ℕ) : ENat) := by norm_cast
    _ ≤ ((k + logSlack (15 + C) (x.length + l + i + j + k) : ℕ) : ENat) := by
        exact_mod_cast hslack

end DecoderPartrec

end Kolmogorov
