import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseRawCharge
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseGain

/-!
# Information gain for charged heavy-truncation candidates

This is the budget-scale counterpart of `AddNoiseGain.lean`.  The candidate
family is the raw heavy-truncation family, so its complexity coordinate is
bounded by `baseBudget`, its threshold is bounded by the noise length, and its
unbounded size coordinate is paid for explicitly.  No bound depends on the
length of the base string.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-! ### Packed rank-plus-suffix programs -/

/-- Program of the charged-heavy gain decoder.  The noise length, threshold,
complexity coordinate, and rank width form a self-delimiting left block.  The
size coordinate is the prefix of the right block, followed by the fixed-width
rank and then the program for the noise string.  Putting `j` in the right block
charges only `2 * |bits j|` rather than doubling that cost again. -/
def chargedHeavyGainProgram
    (noiseLen threshold i j m r : ℕ) (q : BitString) : BitString :=
  pairCode
    (pairCode (Nat.bits noiseLen)
      (pairCode (Nat.bits threshold)
        (pairCode (Nat.bits i) (Nat.bits m))))
    (pairCode (Nat.bits j) (chunkAddress r m ++ q))

def chargedHeavyGainParams (p : BitString) : BitString := decodeFirst p
def chargedHeavyGainPayload (p : BitString) : BitString := decodeSecond p

def chargedHeavyGainNoiseLen (p : BitString) : ℕ :=
  bitsToNat (decodeFirst (chargedHeavyGainParams p))

def chargedHeavyGainThreshold (p : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond (chargedHeavyGainParams p)))

def chargedHeavyGainI (p : BitString) : ℕ :=
  bitsToNat
    (decodeFirst (decodeSecond (decodeSecond (chargedHeavyGainParams p))))

def chargedHeavyGainM (p : BitString) : ℕ :=
  bitsToNat
    (decodeSecond (decodeSecond (decodeSecond (chargedHeavyGainParams p))))

def chargedHeavyGainJ (p : BitString) : ℕ :=
  bitsToNat (decodeFirst (chargedHeavyGainPayload p))

def chargedHeavyGainData (p : BitString) : BitString :=
  decodeSecond (chargedHeavyGainPayload p)

def chargedHeavyGainR (p : BitString) : ℕ :=
  bitsToNat (bitPrefix (chargedHeavyGainM p) (chargedHeavyGainData p))

def chargedHeavyGainQ (p : BitString) : BitString :=
  (chargedHeavyGainData p).drop (chargedHeavyGainM p)

@[simp] theorem chargedHeavyGainNoiseLen_program
    (noiseLen threshold i j m r : ℕ) (q : BitString) :
    chargedHeavyGainNoiseLen
        (chargedHeavyGainProgram noiseLen threshold i j m r q) = noiseLen := by
  simp [chargedHeavyGainNoiseLen, chargedHeavyGainParams,
    chargedHeavyGainProgram, decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem chargedHeavyGainThreshold_program
    (noiseLen threshold i j m r : ℕ) (q : BitString) :
    chargedHeavyGainThreshold
        (chargedHeavyGainProgram noiseLen threshold i j m r q) = threshold := by
  simp [chargedHeavyGainThreshold, chargedHeavyGainParams,
    chargedHeavyGainProgram, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

@[simp] theorem chargedHeavyGainI_program
    (noiseLen threshold i j m r : ℕ) (q : BitString) :
    chargedHeavyGainI
        (chargedHeavyGainProgram noiseLen threshold i j m r q) = i := by
  simp [chargedHeavyGainI, chargedHeavyGainParams, chargedHeavyGainProgram,
    decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem chargedHeavyGainM_program
    (noiseLen threshold i j m r : ℕ) (q : BitString) :
    chargedHeavyGainM
        (chargedHeavyGainProgram noiseLen threshold i j m r q) = m := by
  simp [chargedHeavyGainM, chargedHeavyGainParams, chargedHeavyGainProgram,
    decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem chargedHeavyGainJ_program
    (noiseLen threshold i j m r : ℕ) (q : BitString) :
    chargedHeavyGainJ
        (chargedHeavyGainProgram noiseLen threshold i j m r q) = j := by
  simp [chargedHeavyGainJ, chargedHeavyGainPayload, chargedHeavyGainProgram,
    decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

theorem chargedHeavyGainR_program
    (noiseLen threshold i j m r : ℕ) (q : BitString)
    (hr : r < 2 ^ m) :
    chargedHeavyGainR
        (chargedHeavyGainProgram noiseLen threshold i j m r q) = r := by
  have hlen : (chunkAddress r m).length = m := chunkAddress_length r m hr
  have hpre : bitPrefix m (chunkAddress r m ++ q) = chunkAddress r m := by
    have hp := bitPrefix_append (chunkAddress r m) q
    rwa [hlen] at hp
  rw [chargedHeavyGainR, chargedHeavyGainM_program, chargedHeavyGainData,
    chargedHeavyGainPayload, chargedHeavyGainProgram, decodeSecond_pairCode,
    decodeSecond_pairCode,
    hpre, bitsToNat_chunkAddress]

theorem chargedHeavyGainQ_program
    (noiseLen threshold i j m r : ℕ) (q : BitString)
    (hr : r < 2 ^ m) :
    chargedHeavyGainQ
        (chargedHeavyGainProgram noiseLen threshold i j m r q) = q := by
  have hlen : (chunkAddress r m).length = m := chunkAddress_length r m hr
  have hdrop : (chunkAddress r m ++ q).drop m = q := by
    have hd : (chunkAddress r m ++ q).drop (chunkAddress r m).length = q :=
      List.drop_left
    rwa [hlen] at hd
  rw [chargedHeavyGainQ, chargedHeavyGainM_program, chargedHeavyGainData,
    chargedHeavyGainPayload, chargedHeavyGainProgram, decodeSecond_pairCode,
    decodeSecond_pairCode,
    hdrop]

theorem length_chargedHeavyGainProgram
    (noiseLen threshold i j m r : ℕ) (q : BitString)
    (hr : r < 2 ^ m) :
    (chargedHeavyGainProgram noiseLen threshold i j m r q).length =
      2 * (2 * (Nat.bits noiseLen).length + 1 +
        (2 * (Nat.bits threshold).length + 1 +
          (2 * (Nat.bits i).length + (Nat.bits m).length + 1))) + 1 +
        (2 * (Nat.bits j).length + 1 + (m + q.length)) := by
  rw [chargedHeavyGainProgram, length_pairCode, length_pairCode,
    length_pairCode, length_pairCode, length_pairCode, List.length_append,
    chunkAddress_length r m hr]
  ring

theorem chargedHeavyGainNoiseLen_primrec : Primrec chargedHeavyGainNoiseLen :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp decodeFirst_primrec)

theorem chargedHeavyGainThreshold_primrec : Primrec chargedHeavyGainThreshold :=
  bitsToNat_primrec.comp
    (decodeFirst_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec))

theorem chargedHeavyGainI_primrec : Primrec chargedHeavyGainI :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp
    (decodeSecond_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec)))

theorem chargedHeavyGainM_primrec : Primrec chargedHeavyGainM :=
  bitsToNat_primrec.comp (decodeSecond_primrec.comp
    (decodeSecond_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec)))

theorem chargedHeavyGainJ_primrec : Primrec chargedHeavyGainJ :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec)

theorem chargedHeavyGainData_primrec : Primrec chargedHeavyGainData :=
  decodeSecond_primrec.comp decodeSecond_primrec

theorem chargedHeavyGainR_primrec : Primrec chargedHeavyGainR :=
  bitsToNat_primrec.comp
    (bitPrefix_primrec.comp chargedHeavyGainM_primrec chargedHeavyGainData_primrec)

theorem chargedHeavyGainQ_primrec : Primrec chargedHeavyGainQ :=
  list_drop_primrec.comp chargedHeavyGainData_primrec chargedHeavyGainM_primrec

/-! ### The charged-heavy gain decoder -/

/-- Given `x`, decode the ranked heavy truncation, then run the suffix program
with condition `pairCode x H.code`. -/
noncomputable def chargedHeavyGainDecoder (cU : Code) (V : Map) :
    BitString → BitString →. BitString :=
  fun x p =>
    (Nat.rfind (fun t => Part.some (decide (chargedHeavyGainR p <
      (chargedHeavyAppearanceCodes cU x (chargedHeavyGainNoiseLen p)
        (chargedHeavyGainI p) (chargedHeavyGainJ p)
        (chargedHeavyGainThreshold p) t).length)))).bind
      (fun t => V (chargedHeavyGainQ p, pairCode x
        ((chargedHeavyAppearanceCodes cU x (chargedHeavyGainNoiseLen p)
          (chargedHeavyGainI p) (chargedHeavyGainJ p)
          (chargedHeavyGainThreshold p) t).getD (chargedHeavyGainR p) [])))

section GainDecoderPartrec
attribute [local irreducible] chargedHeavyAppearanceCodes
  chargedHeavyGainNoiseLen chargedHeavyGainThreshold chargedHeavyGainI
  chargedHeavyGainJ chargedHeavyGainM chargedHeavyGainR chargedHeavyGainQ

theorem chargedHeavyGainDecoder_partrec
    (cU : Code) (V : Map) (hV : isDecompressor V) :
    Partrec (fun w : BitString × BitString =>
      chargedHeavyGainDecoder cU V w.1 w.2) := by
  have hp : Computable (fun st : (BitString × BitString) × ℕ => st.1.2) :=
    Computable.snd.comp Computable.fst
  have hcodes : Computable (fun st : (BitString × BitString) × ℕ =>
      chargedHeavyAppearanceCodes cU st.1.1 (chargedHeavyGainNoiseLen st.1.2)
        (chargedHeavyGainI st.1.2) (chargedHeavyGainJ st.1.2)
        (chargedHeavyGainThreshold st.1.2) st.2) :=
    (chargedHeavyAppearanceCodes_computable cU).comp
      ((((Computable.fst.comp Computable.fst).pair
        (((chargedHeavyGainNoiseLen_primrec.to_comp).comp hp).pair
          (((chargedHeavyGainJ_primrec.to_comp).comp hp).pair
            ((chargedHeavyGainThreshold_primrec.to_comp).comp hp)))).pair
        ((chargedHeavyGainI_primrec.to_comp).comp hp)).pair Computable.snd)
  have hrank : Computable (fun st : (BitString × BitString) × ℕ =>
      chargedHeavyGainR st.1.2) :=
    (chargedHeavyGainR_primrec.to_comp).comp hp
  have hlt : Computable (fun q : ℕ × ℕ => decide (q.1 < q.2)) := by
    obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel (α := ℕ) (· < ·))
    convert h.to_comp
  have hcheck : Computable (fun st : (BitString × BitString) × ℕ =>
      decide (chargedHeavyGainR st.1.2 <
        (chargedHeavyAppearanceCodes cU st.1.1
          (chargedHeavyGainNoiseLen st.1.2) (chargedHeavyGainI st.1.2)
          (chargedHeavyGainJ st.1.2) (chargedHeavyGainThreshold st.1.2)
          st.2).length)) :=
    hlt.comp (hrank.pair (Computable.list_length.comp hcodes))
  have hentry : Computable (fun st : (BitString × BitString) × ℕ =>
      (chargedHeavyAppearanceCodes cU st.1.1
        (chargedHeavyGainNoiseLen st.1.2) (chargedHeavyGainI st.1.2)
        (chargedHeavyGainJ st.1.2) (chargedHeavyGainThreshold st.1.2)
        st.2).getD (chargedHeavyGainR st.1.2) []) :=
    ((Primrec.list_getD ([] : BitString)).to_comp).comp hcodes hrank
  have hbody : Partrec (fun st : (BitString × BitString) × ℕ =>
      V (chargedHeavyGainQ st.1.2, pairCode st.1.1
        ((chargedHeavyAppearanceCodes cU st.1.1
          (chargedHeavyGainNoiseLen st.1.2) (chargedHeavyGainI st.1.2)
          (chargedHeavyGainJ st.1.2) (chargedHeavyGainThreshold st.1.2)
          st.2).getD (chargedHeavyGainR st.1.2) []))) :=
    hV.comp (((chargedHeavyGainQ_primrec.to_comp).comp hp).pair
      ((pairCode_primrec.to_comp).comp (Computable.fst.comp Computable.fst)
        hentry))
  refine (Partrec.bind (Partrec.rfind hcheck.to₂.partrec₂) hbody.to₂).of_eq
    (fun w => ?_)
  unfold chargedHeavyGainDecoder
  refine congr_arg₂ Part.bind (congr_arg Nat.rfind ?_) rfl
  funext t
  exact PFun.coe_val _ t

theorem mem_chargedHeavyGainDecoder
    (cU : Code) (V : Map) (x : BitString)
    (noiseLen threshold i j m r t : ℕ) (q : BitString)
    (hrm : r < 2 ^ m)
    (hlt : r < (chargedHeavyAppearanceCodes cU x noiseLen i j threshold t).length)
    {y : BitString}
    (hy : y ∈ V (q, pairCode x
      ((chargedHeavyAppearanceCodes cU x noiseLen i j threshold t).getD r []))) :
    y ∈ chargedHeavyGainDecoder cU V x
      (chargedHeavyGainProgram noiseLen threshold i j m r q) := by
  classical
  set P : ℕ → Prop := fun s =>
    r < (chargedHeavyAppearanceCodes cU x noiseLen i j threshold s).length with hP
  have hex : ∃ s, P s := ⟨t, hlt⟩
  set t₀ := Nat.find hex with ht₀
  have ht₀P : P t₀ := Nat.find_spec hex
  have ht₀le : t₀ ≤ t := Nat.find_le hlt
  have hstable :
      (chargedHeavyAppearanceCodes cU x noiseLen i j threshold t₀).getD r [] =
        (chargedHeavyAppearanceCodes cU x noiseLen i j threshold t).getD r [] :=
    getD_eq_of_prefix
      (chargedHeavyAppearanceCodes_prefix_of_le cU x noiseLen i j threshold ht₀le)
      ht₀P
  unfold chargedHeavyGainDecoder
  rw [chargedHeavyGainNoiseLen_program, chargedHeavyGainThreshold_program,
    chargedHeavyGainI_program, chargedHeavyGainJ_program,
    chargedHeavyGainR_program noiseLen threshold i j m r q hrm,
    chargedHeavyGainQ_program noiseLen threshold i j m r q hrm,
    Part.mem_bind_iff]
  refine ⟨t₀, ?_, ?_⟩
  · rw [Nat.mem_rfind]
    refine ⟨by simpa using ht₀P, ?_⟩
    intro s hs
    have hs' : ¬ P s := Nat.find_min hex hs
    simpa using Nat.le_of_not_lt hs'
  · rw [hstable]
    exact hy

end GainDecoderPartrec

/-! ### Length and compression contradiction -/

/-- The packed charged-heavy gain program has no base-string-length term. -/
theorem chargedHeavyGainProgram_length_slack
    (C noiseLen baseBudget threshold i j m r : ℕ) (q : BitString)
    (hthreshold : threshold ≤ noiseLen) (hi : i ≤ baseBudget)
    (hm : m ≤ noiseLen) (hrm : r < 2 ^ m) :
    (chargedHeavyGainProgram noiseLen threshold i j m r q).length + C ≤
      m + q.length + 2 * (Nat.bits j).length +
        logSlack (10 + C) baseBudget + logSlack (10 + C) noiseLen := by
  have hthresholdBits :
      (Nat.bits threshold).length ≤ (Nat.bits noiseLen).length :=
    length_natBits_mono hthreshold
  have hiBits : (Nat.bits i).length ≤ (Nat.bits baseBudget).length :=
    length_natBits_mono hi
  have hmBits : (Nat.bits m).length ≤ (Nat.bits noiseLen).length :=
    length_natBits_mono hm
  rw [length_chargedHeavyGainProgram noiseLen threshold i j m r q hrm]
  unfold logSlack
  nlinarith [Nat.zero_le ((Nat.bits baseBudget).length),
    Nat.zero_le ((Nat.bits noiseLen).length),
    Nat.zero_le (C * (Nat.bits baseBudget).length),
    Nat.zero_le (C * (Nat.bits noiseLen).length)]

private theorem chargedHeavyGain_arith
    (noiseLen gain epsilon m qlen S T : ℕ)
    (hm : m = gain - epsilon - S) (hdeg : epsilon + S < gain)
    (hq : qlen ≤ noiseLen - gain) (hgainLen : gain ≤ noiseLen)
    (hnat : noiseLen ≤ m + qlen + T + epsilon) (hTS : T + 1 ≤ S) :
    False := by
  omega

/-- An exact information gain from the true heavy truncation forces many
distinct raw charged-heavy candidates.  The unbounded size stratum is paid for
by the explicit `2 * |bits j|` charge; all other overhead is logarithmic in the
visible complexity budget and noise length. -/
theorem chargedHeavyNoiseCandidatesRaw_card_lower_of_information_gain
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString) (epsilon baseBudget i j threshold gain : ℕ)
      (B : Finset BitString)
      (_hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
      (hpair : pairCode x y ∈ B),
      i ≤ baseBudget →
      threshold ≤ y.length →
      (hheavy : threshold ≤ finiteSetLogCard (finiteSetFstFiber B x)) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      condK V y
          (pairCode x
            (codedUniformOn (finiteSetFstHeavyTruncation B threshold)
              ⟨x, finiteSetFstHeavyTruncation_mem hpair hheavy⟩).code) +
            (gain : ENat) ≤ (y.length : ENat) →
      2 ^ (gain - epsilon -
          (2 * (Nat.bits j).length + logSlack c baseBudget +
            logSlack c y.length)) ≤
        (chargedHeavyNoiseCandidatesRaw U x y.length i j threshold).card := by
  classical
  obtain ⟨cU, hcU⟩ : ∃ cU : Code, IsCodeFor cU U :=
    Nat.Partrec.Code.exists_code.mp hU.1.1
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV
    (chargedHeavyGainDecoder cU V) (chargedHeavyGainDecoder_partrec cU V hV.1)
  refine ⟨11 + C, ?_⟩
  intro x y epsilon baseBudget i j threshold gain B hB hpair hi hthreshold
    hheavy hincompressible hgain
  set H := finiteSetFstHeavyTruncation B threshold with hH
  have hxH : x ∈ H := finiteSetFstHeavyTruncation_mem hpair hheavy
  have hHne : H.Nonempty := ⟨x, hxH⟩
  have hHmem : H ∈ chargedHeavyNoiseCandidatesRaw U x y.length i j threshold := by
    simpa [H] using
      (mem_chargedHeavyNoiseCandidatesRaw_of_heavy_fibre hB rfl hpair hheavy)
  have hcardpos :
      1 ≤ (chargedHeavyNoiseCandidatesRaw U x y.length i j threshold).card :=
    Finset.card_pos.mpr ⟨H, hHmem⟩
  set S := 2 * (Nat.bits j).length + logSlack (11 + C) baseBudget +
    logSlack (11 + C) y.length with hS
  change 2 ^ (gain - epsilon - S) ≤
    (chargedHeavyNoiseCandidatesRaw U x y.length i j threshold).card
  by_cases hdeg : gain ≤ epsilon + S
  · have hz : gain - epsilon - S = 0 := by omega
    rw [hz, pow_zero]
    exact hcardpos
  push Not at hdeg
  set m := gain - epsilon - S with hm
  by_contra hcon
  push Not at hcon
  obtain ⟨_, _, hiff, hlen⟩ := chargedHeavyAppearanceCodes_spec hcU
  obtain ⟨t, ht⟩ := (hiff x y.length i j threshold H).mp hHmem
  rw [canonicalUniformCodeOfList_canonicalFinsetList H hHne] at ht
  obtain ⟨r, hr, hget⟩ :
      ∃ r, r < (chargedHeavyAppearanceCodes cU x y.length i j threshold t).length ∧
        (chargedHeavyAppearanceCodes cU x y.length i j threshold t).getD r [] =
          (codedUniformOn H hHne).code := by
    rw [List.mem_iff_getElem] at ht
    obtain ⟨r, hr, hget⟩ := ht
    exact ⟨r, hr, by simp [List.getD_eq_getElem?_getD, hr, hget]⟩
  have hrm : r < 2 ^ m :=
    lt_of_lt_of_le hr ((hlen x y.length i j threshold t).trans_lt hcon).le
  have hshort : condK V y (pairCode x (codedUniformOn H hHne).code) ≤
      ((y.length - gain : ℕ) : ENat) := by
    have hfin : condK V y (pairCode x (codedUniformOn H hHne).code) ≠ ⊤ := by
      intro htop
      rw [htop] at hgain
      simp at hgain
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hn] at hgain ⊢
    have hnGain : n + gain ≤ y.length := by exact_mod_cast hgain
    exact_mod_cast Nat.le_sub_of_add_le hnGain
  obtain ⟨q, hqlen, hq⟩ :=
    (condKLeIff V y (pairCode x (codedUniformOn H hHne).code)
      (y.length - gain)).mp hshort
  have hmem : y ∈ chargedHeavyGainDecoder cU V x
      (chargedHeavyGainProgram y.length threshold i j m r q) := by
    refine mem_chargedHeavyGainDecoder cU V x y.length threshold i j m r t q
      hrm hr ?_
    rw [hget]
    exact hq
  have hbound := hC x
    (chargedHeavyGainProgram y.length threshold i j m r q) y hmem
  have hgainLen : gain ≤ y.length := by
    have hg : (gain : ENat) ≤ (y.length : ENat) := le_trans le_add_self hgain
    exact_mod_cast hg
  have hmLen : m ≤ y.length := by omega
  have hslack := chargedHeavyGainProgram_length_slack C y.length baseBudget
    threshold i j m r q hthreshold hi hmLen hrm
  set T := 2 * (Nat.bits j).length + logSlack (10 + C) baseBudget +
    logSlack (10 + C) y.length with hT
  have hfinal : condK V y x ≤ ((m + q.length + T : ℕ) : ENat) := by
    calc
      condK V y x ≤
          ((chargedHeavyGainProgram y.length threshold i j m r q).length : ENat) +
            (C : ENat) := hbound
      _ = (((chargedHeavyGainProgram y.length threshold i j m r q).length + C : ℕ) :
            ENat) := by norm_cast
      _ ≤ ((m + q.length + T : ℕ) : ENat) := by
        exact_mod_cast (show
          (chargedHeavyGainProgram y.length threshold i j m r q).length + C ≤
            m + q.length + T by
          dsimp [T]
          omega)
  have hnat : y.length ≤ m + q.length + T + epsilon := by
    have hstep : (y.length : ENat) ≤
        ((m + q.length + T : ℕ) : ENat) + (epsilon : ENat) :=
      hincompressible.trans (add_le_add hfinal (le_refl (epsilon : ENat)))
    exact_mod_cast hstep
  have hTS : T + 1 ≤ S := by
    have hbase : logSlack (10 + C) baseBudget + 1 ≤
        logSlack (11 + C) baseBudget := by
      simpa [show 11 + C = (10 + C) + 1 by omega] using
        logSlack_add_const_le (10 + C) 1 baseBudget
    have hnoise : logSlack (10 + C) y.length ≤
        logSlack (11 + C) y.length :=
      logSlack_mono_left (by omega) y.length
    omega
  exact chargedHeavyGain_arith y.length gain epsilon m q.length S T
    hm hdeg hqlen hgainLen hnat hTS

/-- **Charged-heavy information gain packaged as many descriptions.**  An exact
information gain from the true heavy truncation of a budgeted pair description
yields `2 ^ k` genuine `(i + logSlack c |y|, j - threshold + 1)`-descriptions of
`x`, where `k` is the gain minus the incompressibility deficiency, the explicit
size-stratum charge `2 * |bits j|`, and slack logarithmic in the complexity
budget and the noise length.  No term depends on `|x|`. -/
theorem manyIJDescriptions_of_chargedHeavy_information_gain
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString)
      (epsilon baseBudget i j threshold gain : ℕ)
      (B : Finset BitString)
      (_hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
      (hpair : pairCode x y ∈ B),
      i ≤ baseBudget →
      threshold ≤ y.length →
      (hheavy : threshold ≤ finiteSetLogCard (finiteSetFstFiber B x)) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      condK V y
          (pairCode x
            (codedUniformOn (finiteSetFstHeavyTruncation B threshold)
              ⟨x, finiteSetFstHeavyTruncation_mem hpair hheavy⟩).code) +
            (gain : ENat) ≤ (y.length : ENat) →
      ManyIJDescriptions U x
        (i + logSlack c y.length)
        (j - threshold + 1)
        (gain - epsilon -
          (2 * (Nat.bits j).length +
            logSlack c baseBudget + logSlack c y.length)) := by
  obtain ⟨c₁, hcard⟩ :=
    chargedHeavyNoiseCandidatesRaw_card_lower_of_information_gain V U hV hU
  obtain ⟨c₂, hmany⟩ := manyIJDescriptions_of_chargedHeavyNoiseCandidatesRaw U hU
  refine ⟨c₁ + c₂, ?_⟩
  intro x y epsilon baseBudget i j threshold gain B hB hpair hi hthreshold
    hheavy hincompressible hgain
  have hlow := hcard x y epsilon baseBudget i j threshold gain B hB hpair hi
    hthreshold hheavy hincompressible hgain
  have hc₁ : ∀ n : ℕ, logSlack c₁ n ≤ logSlack (c₁ + c₂) n :=
    fun n => logSlack_mono_left (by omega) n
  have hc₂ : ∀ n : ℕ, logSlack c₂ n ≤ logSlack (c₁ + c₂) n :=
    fun n => logSlack_mono_left (by omega) n
  set k : ℕ := gain - epsilon -
    (2 * (Nat.bits j).length +
      logSlack (c₁ + c₂) baseBudget + logSlack (c₁ + c₂) y.length)
  have hkle : k ≤ gain - epsilon -
      (2 * (Nat.bits j).length + logSlack c₁ baseBudget +
        logSlack c₁ y.length) := by
    have h1 := hc₁ baseBudget
    have h2 := hc₁ y.length
    omega
  have hpow : 2 ^ k ≤
      (chargedHeavyNoiseCandidatesRaw U x y.length i j threshold).card :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hkle) hlow
  have hres := hmany x y.length i j threshold k hthreshold hpow
  exact hres.mono_i (Nat.add_le_add_left (hc₂ y.length) i)

end Kolmogorov
