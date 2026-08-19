import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseEnumeration
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseRank

/-!
# Length-free rank decoding of the charged heavy candidates

If a string `x` has fewer than `2 ^ k` charged heavy candidates at noise length
`noiseLen`, budget `baseBudget` and stratum `stratum`, then each candidate is
determined, given `x`, by its rank in the append-only enumeration of
`ChargedHeavyNoiseEnumeration.lean`.

The program that realises this is *length free*: it never mentions `x.length`.
It carries only the noise length, the fibre threshold, and the two budgeted
stratum coordinates — all of which are clamped to `baseBudget` respectively
`noiseLen` — followed by the `k`-bit address of the rank.  Consequently the
overhead is `logSlack c baseBudget + logSlack c noiseLen`, with no dependence on
`|x|`, on the size coordinate, or on the noise deficiency separately.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-! ### The packed rank program -/

/-- Program of the charged rank decoder: the noise-scale parameters
`(noiseLen, thr)` and the budget-scale parameters `(i, j)` in self-delimiting
prefixes, followed by the `k`-bit address of the rank `r`. -/
def chargedHeavyRankProgram (noiseLen thr i j k r : ℕ) : BitString :=
  pairCode (pairCode (Nat.bits noiseLen) (Nat.bits thr))
    (pairCode (pairCode (Nat.bits i) (Nat.bits j)) (chunkAddress r k))

/-- The noise length packed into a charged rank program. -/
def chargedRankNoiseLen (p : BitString) : ℕ := bitsToNat (decodeFirst (decodeFirst p))
/-- The fibre threshold packed into a charged rank program. -/
def chargedRankThr (p : BitString) : ℕ := bitsToNat (decodeSecond (decodeFirst p))
/-- The complexity coordinate packed into a charged rank program. -/
def chargedRankI (p : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeFirst (decodeSecond p)))
/-- The size coordinate packed into a charged rank program. -/
def chargedRankJ (p : BitString) : ℕ :=
  bitsToNat (decodeSecond (decodeFirst (decodeSecond p)))
/-- The rank packed into a charged rank program. -/
def chargedRankR (p : BitString) : ℕ := bitsToNat (decodeSecond (decodeSecond p))

@[simp] theorem chargedRankNoiseLen_program (noiseLen thr i j k r : ℕ) :
    chargedRankNoiseLen (chargedHeavyRankProgram noiseLen thr i j k r) = noiseLen := by
  simp [chargedRankNoiseLen, chargedHeavyRankProgram, decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem chargedRankThr_program (noiseLen thr i j k r : ℕ) :
    chargedRankThr (chargedHeavyRankProgram noiseLen thr i j k r) = thr := by
  simp [chargedRankThr, chargedHeavyRankProgram, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

@[simp] theorem chargedRankI_program (noiseLen thr i j k r : ℕ) :
    chargedRankI (chargedHeavyRankProgram noiseLen thr i j k r) = i := by
  simp [chargedRankI, chargedHeavyRankProgram, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

@[simp] theorem chargedRankJ_program (noiseLen thr i j k r : ℕ) :
    chargedRankJ (chargedHeavyRankProgram noiseLen thr i j k r) = j := by
  simp [chargedRankJ, chargedHeavyRankProgram, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

@[simp] theorem chargedRankR_program (noiseLen thr i j k r : ℕ) :
    chargedRankR (chargedHeavyRankProgram noiseLen thr i j k r) = r := by
  simp [chargedRankR, chargedHeavyRankProgram, decodeSecond_pairCode, bitsToNat_chunkAddress]

theorem chargedRankNoiseLen_primrec : Primrec chargedRankNoiseLen :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp decodeFirst_primrec)
theorem chargedRankThr_primrec : Primrec chargedRankThr :=
  bitsToNat_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec)
theorem chargedRankI_primrec : Primrec chargedRankI :=
  bitsToNat_primrec.comp
    (decodeFirst_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec))
theorem chargedRankJ_primrec : Primrec chargedRankJ :=
  bitsToNat_primrec.comp
    (decodeSecond_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec))
theorem chargedRankR_primrec : Primrec chargedRankR :=
  bitsToNat_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec)

/-- Length of the packed charged rank program. -/
theorem length_chargedHeavyRankProgram (noiseLen thr i j k r : ℕ) (hr : r < 2 ^ k) :
    (chargedHeavyRankProgram noiseLen thr i j k r).length =
      4 * (Nat.bits noiseLen).length + 2 * (Nat.bits thr).length +
        4 * (Nat.bits i).length + 2 * (Nat.bits j).length + 6 + k := by
  rw [chargedHeavyRankProgram, length_pairCode, length_pairCode, length_pairCode,
    length_pairCode, chunkAddress_length r k hr]
  ring

/-! ### Stability of the enumeration under time -/

theorem chargedHeavyAppearanceCodes_prefix_of_le
    (c : Code) (x : BitString) (noiseLen i j thr : ℕ) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    chargedHeavyAppearanceCodes c x noiseLen i j thr t₁ <+:
      chargedHeavyAppearanceCodes c x noiseLen i j thr t₂ := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    exact ih.trans (chargedHeavyAppearanceCodes_prefix c x noiseLen i j thr _)

/-! ### The decoder -/

/-- Given the string `x` as condition and a packed charged rank program, search
for the first stage at which the enumeration is long enough and return the entry
at the requested rank. -/
noncomputable def chargedHeavyRankDecoder (c : Code) : BitString → BitString →. BitString :=
  fun x p =>
    (Nat.rfind (fun t => Part.some (decide (chargedRankR p <
      (chargedHeavyAppearanceCodes c x (chargedRankNoiseLen p) (chargedRankI p)
        (chargedRankJ p) (chargedRankThr p) t).length)))).bind
      (fun t => Part.some ((chargedHeavyAppearanceCodes c x (chargedRankNoiseLen p)
        (chargedRankI p) (chargedRankJ p) (chargedRankThr p) t).getD (chargedRankR p) []))

section DecoderPartrec
attribute [local irreducible] chargedHeavyAppearanceCodes
  chargedRankNoiseLen chargedRankThr chargedRankI chargedRankJ chargedRankR

theorem chargedHeavyRankDecoder_partrec (c : Code) :
    Partrec (fun q : BitString × BitString => chargedHeavyRankDecoder c q.1 q.2) := by
  have hp : Computable (fun st : (BitString × BitString) × ℕ => st.1.2) :=
    Computable.snd.comp Computable.fst
  have hcodes : Computable (fun st : (BitString × BitString) × ℕ =>
      chargedHeavyAppearanceCodes c st.1.1 (chargedRankNoiseLen st.1.2)
        (chargedRankI st.1.2) (chargedRankJ st.1.2) (chargedRankThr st.1.2) st.2) :=
    (chargedHeavyAppearanceCodes_computable c).comp
      ((((Computable.fst.comp Computable.fst).pair
        (((chargedRankNoiseLen_primrec.to_comp).comp hp).pair
          (((chargedRankJ_primrec.to_comp).comp hp).pair
            ((chargedRankThr_primrec.to_comp).comp hp)))).pair
        ((chargedRankI_primrec.to_comp).comp hp)).pair Computable.snd)
  have hrank : Computable (fun st : (BitString × BitString) × ℕ => chargedRankR st.1.2) :=
    (chargedRankR_primrec.to_comp).comp hp
  have hlt : Computable (fun q : ℕ × ℕ => decide (q.1 < q.2)) := by
    obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel (α := ℕ) (· < ·))
    convert h.to_comp
  have hcheck : Computable (fun st : (BitString × BitString) × ℕ =>
      decide (chargedRankR st.1.2 <
        (chargedHeavyAppearanceCodes c st.1.1 (chargedRankNoiseLen st.1.2)
          (chargedRankI st.1.2) (chargedRankJ st.1.2) (chargedRankThr st.1.2) st.2).length)) :=
    hlt.comp (hrank.pair (Computable.list_length.comp hcodes))
  have hpost : Computable (fun st : (BitString × BitString) × ℕ =>
      (chargedHeavyAppearanceCodes c st.1.1 (chargedRankNoiseLen st.1.2)
        (chargedRankI st.1.2) (chargedRankJ st.1.2) (chargedRankThr st.1.2) st.2).getD
          (chargedRankR st.1.2) []) :=
    ((Primrec.list_getD ([] : BitString)).to_comp).comp hcodes hrank
  refine (Partrec.bind (Partrec.rfind hcheck.to₂.partrec₂) hpost.to₂.partrec₂).of_eq
    (fun q => ?_)
  unfold chargedHeavyRankDecoder
  refine congr_arg₂ Part.bind (congr_arg Nat.rfind ?_) ?_
  · funext t; exact PFun.coe_val _ t
  · funext t; exact PFun.coe_val _ t

theorem mem_chargedHeavyRankDecoder_of_rank
    (c : Code) (x : BitString) (noiseLen i j thr k r t : ℕ) {w : BitString}
    (hlt : r < (chargedHeavyAppearanceCodes c x noiseLen i j thr t).length)
    (hget : (chargedHeavyAppearanceCodes c x noiseLen i j thr t).getD r [] = w) :
    w ∈ chargedHeavyRankDecoder c x (chargedHeavyRankProgram noiseLen thr i j k r) := by
  classical
  set P : ℕ → Prop := fun s =>
    r < (chargedHeavyAppearanceCodes c x noiseLen i j thr s).length with hP
  have hex : ∃ s, P s := ⟨t, hlt⟩
  set t₀ := Nat.find hex with ht₀
  have ht₀P : P t₀ := Nat.find_spec hex
  have ht₀le : t₀ ≤ t := Nat.find_le hlt
  have hstable :
      (chargedHeavyAppearanceCodes c x noiseLen i j thr t₀).getD r [] = w := by
    rw [getD_eq_of_prefix
      (chargedHeavyAppearanceCodes_prefix_of_le c x noiseLen i j thr ht₀le) ht₀P]
    exact hget
  unfold chargedHeavyRankDecoder
  simp only [chargedRankNoiseLen_program, chargedRankThr_program, chargedRankI_program,
    chargedRankJ_program, chargedRankR_program]
  rw [Part.mem_bind_iff]
  refine ⟨t₀, ?_, ?_⟩
  · rw [Nat.mem_rfind]
    refine ⟨by simpa using ht₀P, ?_⟩
    intro m hm
    have hm' : ¬ P m := Nat.find_min hex hm
    simpa using Nat.le_of_not_lt hm'
  · simpa using hstable.symm

/-! ### The conditional complexity bound -/

/-- The packed charged rank program, together with a machine constant, fits in
`k` bits plus slack logarithmic in the two ambient budgets — and in particular
does not depend on `x.length`. -/
private theorem chargedHeavyRankProgram_length_slack (C : ℕ)
    (noiseLen baseBudget thr i j k r : ℕ)
    (hthr : thr ≤ noiseLen) (hi : i ≤ baseBudget) (hj : j ≤ baseBudget)
    (hrk : r < 2 ^ k) :
    (chargedHeavyRankProgram noiseLen thr i j k r).length + C ≤
      k + logSlack (6 + C) baseBudget + logSlack (6 + C) noiseLen := by
  have hthrW : (Nat.bits thr).length ≤ (Nat.bits noiseLen).length := length_natBits_mono hthr
  have hiW : (Nat.bits i).length ≤ (Nat.bits baseBudget).length := length_natBits_mono hi
  have hjW : (Nat.bits j).length ≤ (Nat.bits baseBudget).length := length_natBits_mono hj
  have h1 : logSlack (6 + C) baseBudget =
      (6 + C) * (Nat.bits baseBudget).length + (6 + C) := rfl
  have h2 : logSlack (6 + C) noiseLen =
      (6 + C) * (Nat.bits noiseLen).length + (6 + C) := rfl
  have hb : 6 * (Nat.bits baseBudget).length ≤ (6 + C) * (Nat.bits baseBudget).length :=
    Nat.mul_le_mul_right _ (by omega)
  have hn : 6 * (Nat.bits noiseLen).length ≤ (6 + C) * (Nat.bits noiseLen).length :=
    Nat.mul_le_mul_right _ (by omega)
  rw [length_chargedHeavyRankProgram noiseLen thr i j k r hrk, h1, h2]
  omega

/-- **Charged leaf packet 2.**  When `x` has fewer than `2 ^ k` charged heavy
candidates at noise length `noiseLen`, budget `baseBudget` and stratum
`stratum`, every such candidate has conditional plain complexity at most `k`
plus slack logarithmic in `baseBudget` and `noiseLen`, given `x`.

The bound is *length free*: no term depends on `|x|`, and the stratum
coordinates enter only through their clamped values. -/
theorem condK_chargedHeavyCandidate_of_card_lt_pow
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen baseBudget : ℕ) (stratum : BitString) (k : ℕ)
      (H : Finset BitString) (hH : H.Nonempty),
      H ∈ chargedHeavyNoiseCandidates U x noiseLen baseBudget stratum →
      (chargedHeavyNoiseCandidates U x noiseLen baseBudget stratum).card < 2 ^ k →
      condK V (codedUniformOn H hH).code x ≤
        ((k + logSlack c baseBudget + logSlack c noiseLen : ℕ) : ENat) := by
  obtain ⟨cU, hcU⟩ : ∃ cU : Code, IsCodeFor cU U :=
    Nat.Partrec.Code.exists_code.mp hU.1.1
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV (chargedHeavyRankDecoder cU)
    (chargedHeavyRankDecoder_partrec cU)
  refine ⟨6 + C, ?_⟩
  intro x noiseLen baseBudget stratum k H hH hmem hcard
  set i := stratumComplexity baseBudget stratum with hi
  set j := stratumSize baseBudget stratum with hj
  set thr := stratumThreshold noiseLen stratum with hthr
  rw [chargedHeavyNoiseCandidates] at hmem hcard
  obtain ⟨_, _, hiff, hlen⟩ := chargedHeavyAppearanceCodes_spec hcU
  obtain ⟨t, ht⟩ := (hiff x noiseLen i j thr H).mp hmem
  rw [canonicalUniformCodeOfList_canonicalFinsetList H hH] at ht
  obtain ⟨r, hr, hget⟩ : ∃ r, r < (chargedHeavyAppearanceCodes cU x noiseLen i j thr t).length ∧
      (chargedHeavyAppearanceCodes cU x noiseLen i j thr t).getD r [] =
        (codedUniformOn H hH).code := by
    rw [List.mem_iff_getElem] at ht
    obtain ⟨r, hr, hget⟩ := ht
    exact ⟨r, hr, by simp [List.getD_eq_getElem?_getD, hr, hget]⟩
  have hrk : r < 2 ^ k :=
    lt_of_lt_of_le hr ((hlen x noiseLen i j thr t).trans_lt hcard).le
  have hmemdec : (codedUniformOn H hH).code ∈
      chargedHeavyRankDecoder cU x (chargedHeavyRankProgram noiseLen thr i j k r) :=
    mem_chargedHeavyRankDecoder_of_rank cU x noiseLen i j thr k r t hr hget
  have hbound := hC x (chargedHeavyRankProgram noiseLen thr i j k r) _ hmemdec
  have hslack := chargedHeavyRankProgram_length_slack C noiseLen baseBudget thr i j k r
    (stratumThreshold_le noiseLen stratum) (stratumComplexity_le baseBudget stratum)
    (stratumSize_le baseBudget stratum) hrk
  calc condK V (codedUniformOn H hH).code x
      ≤ ((chargedHeavyRankProgram noiseLen thr i j k r).length : ENat) + (C : ENat) := hbound
    _ = (((chargedHeavyRankProgram noiseLen thr i j k r).length + C : ℕ) : ENat) := by norm_cast
    _ ≤ ((k + logSlack (6 + C) baseBudget + logSlack (6 + C) noiseLen : ℕ) : ENat) := by
        exact_mod_cast hslack

/-- Stratum-charged restatement of the previous bound: allotting `s` extra bits
for the stratum is always affordable.  The extra `s` term is in fact not needed,
so no hypothesis on the length of `stratum` is required. -/
theorem condK_chargedHeavyCandidate_stratum_charge
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen baseBudget : ℕ) (stratum : BitString) (s k : ℕ)
      (H : Finset BitString) (hH : H.Nonempty),
      H ∈ chargedHeavyNoiseCandidates U x noiseLen baseBudget stratum →
      (chargedHeavyNoiseCandidates U x noiseLen baseBudget stratum).card < 2 ^ k →
      condK V (codedUniformOn H hH).code x ≤
        ((k + s + logSlack c baseBudget + logSlack c noiseLen : ℕ) : ENat) := by
  obtain ⟨c, hc⟩ := condK_chargedHeavyCandidate_of_card_lt_pow V U hV hU
  refine ⟨c, fun x noiseLen baseBudget stratum s k H hH hmem hcard => ?_⟩
  refine (hc x noiseLen baseBudget stratum k H hH hmem hcard).trans ?_
  exact_mod_cast Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.le_add_right _ s) _) _

end DecoderPartrec

end Kolmogorov
