import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedChargedHeavyNoiseEnumeration
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseGain

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-! ### Packed rank-plus-suffix programs for the pooled enumeration -/

/-- Program of the all-size charged-heavy gain decoder. The noise length,
base budget, and rank width form a self-delimiting left block. The rank and the
suffix program form the right block.  The pooled enumeration ranges over the
raw size coordinate, so `j` is absent from the program even when
`baseBudget < j`. -/
def budgetedChargedHeavyGainProgram
    (noiseLen baseBudget m r : ℕ) (q : BitString) : BitString :=
  pairCode
    (pairCode (Nat.bits noiseLen)
      (pairCode (Nat.bits baseBudget) (Nat.bits m)))
    (chunkAddress r m ++ q)

def budgetedChargedHeavyGainParams (p : BitString) : BitString := decodeFirst p
def budgetedChargedHeavyGainPayload (p : BitString) : BitString := decodeSecond p

def budgetedChargedHeavyGainNoiseLen (p : BitString) : ℕ :=
  bitsToNat (decodeFirst (budgetedChargedHeavyGainParams p))

def budgetedChargedHeavyGainBaseBudget (p : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond (budgetedChargedHeavyGainParams p)))

def budgetedChargedHeavyGainM (p : BitString) : ℕ :=
  bitsToNat (decodeSecond (decodeSecond (budgetedChargedHeavyGainParams p)))

def budgetedChargedHeavyGainR (p : BitString) : ℕ :=
  bitsToNat (bitPrefix (budgetedChargedHeavyGainM p) (budgetedChargedHeavyGainPayload p))

def budgetedChargedHeavyGainQ (p : BitString) : BitString :=
  (budgetedChargedHeavyGainPayload p).drop (budgetedChargedHeavyGainM p)

@[simp] theorem budgetedChargedHeavyGainNoiseLen_program
    (noiseLen baseBudget m r : ℕ) (q : BitString) :
    budgetedChargedHeavyGainNoiseLen
        (budgetedChargedHeavyGainProgram noiseLen baseBudget m r q) = noiseLen := by
  simp [budgetedChargedHeavyGainNoiseLen, budgetedChargedHeavyGainParams,
    budgetedChargedHeavyGainProgram, decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem budgetedChargedHeavyGainBaseBudget_program
    (noiseLen baseBudget m r : ℕ) (q : BitString) :
    budgetedChargedHeavyGainBaseBudget
        (budgetedChargedHeavyGainProgram noiseLen baseBudget m r q) = baseBudget := by
  simp [budgetedChargedHeavyGainBaseBudget, budgetedChargedHeavyGainParams,
    budgetedChargedHeavyGainProgram, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

@[simp] theorem budgetedChargedHeavyGainM_program
    (noiseLen baseBudget m r : ℕ) (q : BitString) :
    budgetedChargedHeavyGainM
        (budgetedChargedHeavyGainProgram noiseLen baseBudget m r q) = m := by
  simp [budgetedChargedHeavyGainM, budgetedChargedHeavyGainParams,
    budgetedChargedHeavyGainProgram, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

theorem budgetedChargedHeavyGainR_program
    (noiseLen baseBudget m r : ℕ) (q : BitString)
    (hr : r < 2 ^ m) :
    budgetedChargedHeavyGainR
        (budgetedChargedHeavyGainProgram noiseLen baseBudget m r q) = r := by
  have hlen : (chunkAddress r m).length = m := chunkAddress_length r m hr
  have hpre : bitPrefix m (chunkAddress r m ++ q) = chunkAddress r m := by
    have hp := bitPrefix_append (chunkAddress r m) q
    rwa [hlen] at hp
  rw [budgetedChargedHeavyGainR, budgetedChargedHeavyGainM_program,
    budgetedChargedHeavyGainPayload, budgetedChargedHeavyGainProgram,
    decodeSecond_pairCode, hpre, bitsToNat_chunkAddress]

theorem budgetedChargedHeavyGainQ_program
    (noiseLen baseBudget m r : ℕ) (q : BitString)
    (hr : r < 2 ^ m) :
    budgetedChargedHeavyGainQ
        (budgetedChargedHeavyGainProgram noiseLen baseBudget m r q) = q := by
  have hlen : (chunkAddress r m).length = m := chunkAddress_length r m hr
  have hdrop : (chunkAddress r m ++ q).drop m = q := by
    have hd : (chunkAddress r m ++ q).drop (chunkAddress r m).length = q :=
      List.drop_left
    rwa [hlen] at hd
  rw [budgetedChargedHeavyGainQ, budgetedChargedHeavyGainM_program,
    budgetedChargedHeavyGainPayload, budgetedChargedHeavyGainProgram,
    decodeSecond_pairCode, hdrop]

theorem length_budgetedChargedHeavyGainProgram
    (noiseLen baseBudget m r : ℕ) (q : BitString)
    (hr : r < 2 ^ m) :
    (budgetedChargedHeavyGainProgram noiseLen baseBudget m r q).length =
      2 * (2 * (Nat.bits noiseLen).length + 1 +
        (2 * (Nat.bits baseBudget).length + (Nat.bits m).length + 1)) + 1 +
        (m + q.length) := by
  rw [budgetedChargedHeavyGainProgram, length_pairCode, length_pairCode,
    length_pairCode, List.length_append, chunkAddress_length r m hr]
  ring

theorem budgetedChargedHeavyGainNoiseLen_primrec : Primrec budgetedChargedHeavyGainNoiseLen :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp decodeFirst_primrec)

theorem budgetedChargedHeavyGainBaseBudget_primrec : Primrec budgetedChargedHeavyGainBaseBudget :=
  bitsToNat_primrec.comp
    (decodeFirst_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec))

theorem budgetedChargedHeavyGainM_primrec : Primrec budgetedChargedHeavyGainM :=
  bitsToNat_primrec.comp
    (decodeSecond_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec))

theorem budgetedChargedHeavyGainPayload_primrec : Primrec budgetedChargedHeavyGainPayload :=
  decodeSecond_primrec

theorem budgetedChargedHeavyGainR_primrec : Primrec budgetedChargedHeavyGainR :=
  bitsToNat_primrec.comp
    (bitPrefix_primrec.comp budgetedChargedHeavyGainM_primrec
      budgetedChargedHeavyGainPayload_primrec)

theorem budgetedChargedHeavyGainQ_primrec : Primrec budgetedChargedHeavyGainQ :=
  list_drop_primrec.comp budgetedChargedHeavyGainPayload_primrec budgetedChargedHeavyGainM_primrec

/-! ### The budgeted charged-heavy gain decoder -/

noncomputable def budgetedChargedHeavyGainDecoder (cU : Code) (V : Map) :
    BitString → BitString →. BitString :=
  fun x p =>
    (Nat.rfind (fun t => Part.some (decide (budgetedChargedHeavyGainR p <
      (budgetedChargedHeavyAppearanceCodes cU x (budgetedChargedHeavyGainNoiseLen p)
        (budgetedChargedHeavyGainBaseBudget p) t).length)))).bind
      (fun t => V (budgetedChargedHeavyGainQ p, pairCode x
        ((budgetedChargedHeavyAppearanceCodes cU x (budgetedChargedHeavyGainNoiseLen p)
          (budgetedChargedHeavyGainBaseBudget p) t).getD (budgetedChargedHeavyGainR p) [])))

section DecoderPartrec
attribute [local irreducible] budgetedChargedHeavyAppearanceCodes
  budgetedChargedHeavyGainNoiseLen budgetedChargedHeavyGainBaseBudget
  budgetedChargedHeavyGainM budgetedChargedHeavyGainR budgetedChargedHeavyGainQ

theorem budgetedChargedHeavyGainDecoder_partrec
    (cU : Code) (V : Map) (hV : isDecompressor V) :
    Partrec (fun w : BitString × BitString =>
      budgetedChargedHeavyGainDecoder cU V w.1 w.2) := by
  have hp : Computable (fun st : (BitString × BitString) × ℕ => st.1.2) :=
    Computable.snd.comp Computable.fst
  have hcodes : Computable (fun st : (BitString × BitString) × ℕ =>
      budgetedChargedHeavyAppearanceCodes cU st.1.1
        (budgetedChargedHeavyGainNoiseLen st.1.2)
        (budgetedChargedHeavyGainBaseBudget st.1.2) st.2) :=
    (budgetedChargedHeavyAppearanceCodes_computable cU).comp
      ((((Computable.fst.comp Computable.fst).pair
        ((budgetedChargedHeavyGainNoiseLen_primrec.to_comp).comp hp)).pair
        ((budgetedChargedHeavyGainBaseBudget_primrec.to_comp).comp hp)).pair
        Computable.snd)
  have hrank : Computable (fun st : (BitString × BitString) × ℕ =>
      budgetedChargedHeavyGainR st.1.2) :=
    (budgetedChargedHeavyGainR_primrec.to_comp).comp hp
  have hlt : Computable (fun q : ℕ × ℕ => decide (q.1 < q.2)) := by
    obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel (α := ℕ) (· < ·))
    convert h.to_comp
  have hcheck : Computable (fun st : (BitString × BitString) × ℕ =>
      decide (budgetedChargedHeavyGainR st.1.2 <
        (budgetedChargedHeavyAppearanceCodes cU st.1.1
          (budgetedChargedHeavyGainNoiseLen st.1.2)
          (budgetedChargedHeavyGainBaseBudget st.1.2) st.2).length)) :=
    hlt.comp (hrank.pair (Computable.list_length.comp hcodes))
  have hentry : Computable (fun st : (BitString × BitString) × ℕ =>
      (budgetedChargedHeavyAppearanceCodes cU st.1.1
        (budgetedChargedHeavyGainNoiseLen st.1.2)
        (budgetedChargedHeavyGainBaseBudget st.1.2) st.2).getD
          (budgetedChargedHeavyGainR st.1.2) []) :=
    ((Primrec.list_getD ([] : BitString)).to_comp).comp hcodes hrank
  have hbody : Partrec (fun st : (BitString × BitString) × ℕ =>
      V (budgetedChargedHeavyGainQ st.1.2, pairCode st.1.1
        ((budgetedChargedHeavyAppearanceCodes cU st.1.1
          (budgetedChargedHeavyGainNoiseLen st.1.2)
          (budgetedChargedHeavyGainBaseBudget st.1.2) st.2).getD
            (budgetedChargedHeavyGainR st.1.2) []))) :=
    hV.comp (((budgetedChargedHeavyGainQ_primrec.to_comp).comp hp).pair
      ((pairCode_primrec.to_comp).comp (Computable.fst.comp Computable.fst)
        hentry))
  refine (Partrec.bind (Partrec.rfind hcheck.to₂.partrec₂) hbody.to₂).of_eq
    (fun w => ?_)
  unfold budgetedChargedHeavyGainDecoder
  refine congr_arg₂ Part.bind (congr_arg Nat.rfind ?_) rfl
  funext t
  exact PFun.coe_val _ t

theorem mem_budgetedChargedHeavyGainDecoder
    (cU : Code) (V : Map) (x : BitString)
    (noiseLen baseBudget m r t : ℕ) (q : BitString)
    (hrm : r < 2 ^ m)
    (hlt : r < (budgetedChargedHeavyAppearanceCodes cU x noiseLen
      baseBudget t).length)
    {y : BitString}
    (hy : y ∈ V (q, pairCode x
      ((budgetedChargedHeavyAppearanceCodes cU x noiseLen baseBudget t).getD
        r []))) :
    y ∈ budgetedChargedHeavyGainDecoder cU V x
      (budgetedChargedHeavyGainProgram noiseLen baseBudget m r q) := by
  classical
  set P : ℕ → Prop := fun s =>
    r < (budgetedChargedHeavyAppearanceCodes cU x noiseLen
      baseBudget s).length with hP
  have hex : ∃ s, P s := ⟨t, hlt⟩
  set t₀ := Nat.find hex with ht₀
  have ht₀P : P t₀ := Nat.find_spec hex
  have ht₀le : t₀ ≤ t := Nat.find_le hlt
  have hstable :
      (budgetedChargedHeavyAppearanceCodes cU x noiseLen baseBudget t₀).getD
          r [] =
        (budgetedChargedHeavyAppearanceCodes cU x noiseLen baseBudget t).getD
          r [] :=
    getD_eq_of_prefix
      (budgetedChargedHeavyAppearanceCodes_prefix_of_le cU x noiseLen
        baseBudget ht₀le) ht₀P
  unfold budgetedChargedHeavyGainDecoder
  rw [budgetedChargedHeavyGainNoiseLen_program,
    budgetedChargedHeavyGainBaseBudget_program,
    budgetedChargedHeavyGainR_program noiseLen baseBudget m r q hrm,
    budgetedChargedHeavyGainQ_program noiseLen baseBudget m r q hrm,
    Part.mem_bind_iff]
  refine ⟨t₀, ?_, ?_⟩
  · refine Nat.mem_rfind.mpr ⟨by simpa using ht₀P, ?_⟩
    intro s hs
    have hs' : ¬ P s := Nat.find_min hex hs
    simpa using Nat.le_of_not_lt hs'
  · rw [hstable]
    exact hy
end DecoderPartrec

theorem budgetedChargedHeavyGainProgram_length_slack
    (C noiseLen baseBudget m r : ℕ) (q : BitString)
    (hm : m ≤ noiseLen) (hrm : r < 2 ^ m) :
    (budgetedChargedHeavyGainProgram noiseLen baseBudget m r q).length + C ≤
      m + q.length + logSlack (10 + C) baseBudget +
        logSlack (10 + C) noiseLen := by
  have hmBits : (Nat.bits m).length ≤ (Nat.bits noiseLen).length :=
    length_natBits_mono hm
  rw [length_budgetedChargedHeavyGainProgram noiseLen baseBudget m r q hrm]
  unfold logSlack
  nlinarith [Nat.zero_le ((Nat.bits baseBudget).length),
    Nat.zero_le ((Nat.bits noiseLen).length),
    Nat.zero_le (C * (Nat.bits baseBudget).length),
    Nat.zero_le (C * (Nat.bits noiseLen).length)]

/-- In the bounded-size branch, the old explicit size-stratum charge is
absorbed by budget-scale logarithmic slack.  The pooled decoder above is needed
only when the size coordinate is not bounded by `baseBudget`. -/
theorem budgetedChargedHeavyNoiseCandidatesRaw_card_lower_of_information_gain
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString) (epsilon baseBudget i j threshold gain : ℕ)
      (B : Finset BitString)
      (_hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
      (hpair : pairCode x y ∈ B),
      i ≤ baseBudget →
      j ≤ baseBudget →
      threshold ≤ y.length →
      (hheavy : threshold ≤ finiteSetLogCard (finiteSetFstFiber B x)) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      condK V y
          (pairCode x
            (codedUniformOn (finiteSetFstHeavyTruncation B threshold)
              ⟨x, finiteSetFstHeavyTruncation_mem hpair hheavy⟩).code) +
            (gain : ENat) ≤ (y.length : ENat) →
      2 ^ (gain - epsilon -
          (logSlack c baseBudget + logSlack c y.length)) ≤
        (chargedHeavyNoiseCandidatesRaw U x y.length i j threshold).card := by
  obtain ⟨c, hc⟩ :=
    chargedHeavyNoiseCandidatesRaw_card_lower_of_information_gain V U hV hU
  refine ⟨c + 2, ?_⟩
  intro x y epsilon baseBudget i j threshold gain B hB hpair hi hj
    hthreshold hheavy hincompressible hgain
  have hjBits : (Nat.bits j).length ≤ (Nat.bits baseBudget).length :=
    length_natBits_mono hj
  have hcharge :
      2 * (Nat.bits j).length + logSlack c baseBudget + logSlack c y.length ≤
        logSlack (c + 2) baseBudget + logSlack (c + 2) y.length := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits baseBudget).length),
      Nat.zero_le ((Nat.bits y.length).length)]
  have hexponent :
      gain - epsilon -
          (logSlack (c + 2) baseBudget + logSlack (c + 2) y.length) ≤
        gain - epsilon -
          (2 * (Nat.bits j).length + logSlack c baseBudget +
            logSlack c y.length) := by
    omega
  exact (Nat.pow_le_pow_right (by decide) hexponent).trans
    (hc x y epsilon baseBudget i j threshold gain B hB hpair hi
      hthreshold hheavy hincompressible hgain)

private theorem budgetedChargedHeavyGain_arith
    (noiseLen gain epsilon m qlen S T : ℕ)
    (hm : m = gain - epsilon - S) (hdeg : epsilon + S < gain)
    (hq : qlen ≤ noiseLen - gain) (hgainLen : gain ≤ noiseLen)
    (hnat : noiseLen ≤ m + qlen + T + epsilon) (hTS : T + 1 ≤ S) :
    False := by
  omega

private theorem budgetedChargedHeavyAppearanceCodes_length_lower_of_decoder_bound
    (V : Map) (C : ℕ) (cU : Code)
    (hC : ∀ (context p w : BitString),
      w ∈ budgetedChargedHeavyGainDecoder cU V context p →
      condK V w context ≤ (p.length : ENat) + (C : ENat))
    (x y modelCode : BitString) (epsilon baseBudget gain t : ℕ)
    (ht : modelCode ∈
      budgetedChargedHeavyAppearanceCodes cU x y.length baseBudget t)
    (hincompressible :
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat))
    (hgain : condK V y (pairCode x modelCode) + (gain : ENat) ≤
      (y.length : ENat)) :
    2 ^ (gain - epsilon -
        (logSlack (11 + C) baseBudget + logSlack (11 + C) y.length)) ≤
      (budgetedChargedHeavyAppearanceCodes cU x y.length baseBudget t).length := by
  set S := logSlack (11 + C) baseBudget + logSlack (11 + C) y.length with hS
  change 2 ^ (gain - epsilon - S) ≤
    (budgetedChargedHeavyAppearanceCodes cU x y.length baseBudget t).length
  have hlengthPos :
      1 ≤ (budgetedChargedHeavyAppearanceCodes cU x y.length baseBudget t).length :=
    List.length_pos_of_mem ht
  by_cases hdeg : gain ≤ epsilon + S
  · have hz : gain - epsilon - S = 0 := by omega
    rw [hz, pow_zero]
    exact hlengthPos
  push Not at hdeg
  set m := gain - epsilon - S with hm
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hr, hget⟩ :
      ∃ r, r < (budgetedChargedHeavyAppearanceCodes cU x y.length baseBudget t).length ∧
        (budgetedChargedHeavyAppearanceCodes cU x y.length baseBudget t).getD r [] =
          modelCode := by
    rw [List.mem_iff_getElem] at ht
    obtain ⟨r, hr, hget⟩ := ht
    exact ⟨r, hr, by simp [List.getD_eq_getElem?_getD, hr, hget]⟩
  have hrm : r < 2 ^ m := lt_of_lt_of_le hr hcon.le
  have hshort : condK V y (pairCode x modelCode) ≤
      ((y.length - gain : ℕ) : ENat) := by
    have hfin : condK V y (pairCode x modelCode) ≠ ⊤ := by
      intro htop
      rw [htop] at hgain
      simp at hgain
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hn] at hgain ⊢
    have hnGain : n + gain ≤ y.length := by exact_mod_cast hgain
    exact_mod_cast Nat.le_sub_of_add_le hnGain
  obtain ⟨q, hqlen, hq⟩ :=
    (condKLeIff V y (pairCode x modelCode)
      (y.length - gain)).mp hshort
  have hmem : y ∈ budgetedChargedHeavyGainDecoder cU V x
      (budgetedChargedHeavyGainProgram y.length baseBudget m r q) := by
    refine mem_budgetedChargedHeavyGainDecoder cU V x y.length baseBudget m r t q
      hrm hr ?_
    rw [hget]
    exact hq
  have hbound := hC x
    (budgetedChargedHeavyGainProgram y.length baseBudget m r q) y hmem
  have hgainLen : gain ≤ y.length := by
    have hg : (gain : ENat) ≤ (y.length : ENat) := le_trans le_add_self hgain
    exact_mod_cast hg
  have hmLen : m ≤ y.length := by omega
  have hslack := budgetedChargedHeavyGainProgram_length_slack C y.length
    baseBudget m r q hmLen hrm
  set T := logSlack (10 + C) baseBudget + logSlack (10 + C) y.length with hT
  have hfinal : condK V y x ≤ ((m + q.length + T : ℕ) : ENat) := by
    calc
      condK V y x ≤
          ((budgetedChargedHeavyGainProgram y.length baseBudget m r q).length : ENat) +
            (C : ENat) := hbound
      _ = (((budgetedChargedHeavyGainProgram y.length baseBudget m r q).length + C : ℕ) :
            ENat) := by norm_cast
      _ ≤ ((m + q.length + T : ℕ) : ENat) := by
        exact_mod_cast (show
          (budgetedChargedHeavyGainProgram y.length baseBudget m r q).length + C ≤
            m + q.length + T by
          dsimp [T]
          omega)
  have hnat : y.length ≤ m + q.length + T + epsilon := by
    have hstep : (y.length : ENat) ≤
        ((m + q.length + T : ℕ) : ENat) + (epsilon : ENat) :=
      hincompressible.trans (add_le_add hfinal (le_refl (epsilon : ENat)))
    exact_mod_cast hstep
  have hbase : logSlack (10 + C) baseBudget + 1 ≤
      logSlack (11 + C) baseBudget := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits baseBudget).length)]
  have hnoise : logSlack (10 + C) y.length ≤
      logSlack (11 + C) y.length :=
    logSlack_mono_left (by omega) y.length
  have hTS : T + 1 ≤ S := by
    dsimp [T, S]
    omega
  exact budgetedChargedHeavyGain_arith y.length gain epsilon m q.length S T
    hm hdeg hqlen hgainLen hnat hTS

private theorem exists_heavyTruncation_mem_budgetedAppearanceCodes
    (U : Map) (cU : Code) (hcU : IsCodeFor cU U)
    (x y : BitString) (baseBudget i j threshold : ℕ)
    (B : Finset BitString)
    (hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
    (hpair : pairCode x y ∈ B)
    (hi : i ≤ baseBudget) (hthreshold : threshold ≤ y.length)
    (hheavy : threshold ≤ finiteSetLogCard (finiteSetFstFiber B x)) :
    ∃ t : ℕ,
      (codedUniformOn (finiteSetFstHeavyTruncation B threshold)
          ⟨x, finiteSetFstHeavyTruncation_mem hpair hheavy⟩).code ∈
        budgetedChargedHeavyAppearanceCodes cU x y.length baseBudget t := by
  classical
  have hpool : ∃ stratum,
      finiteSetFstHeavyTruncation B threshold ∈
        pooledChargedHeavyNoiseCandidates U x y.length baseBudget stratum := by
    refine ⟨chargedStratumCode i j threshold, ?_⟩
    unfold pooledChargedHeavyNoiseCandidates stratumComplexity stratumThreshold
    simp only [stratumComplexityRaw_code, stratumSizeRaw_code,
      stratumThresholdRaw_code]
    rw [Nat.min_eq_left hi, Nat.min_eq_left hthreshold]
    exact mem_chargedHeavyNoiseCandidatesRaw_of_heavy_fibre
      hB rfl hpair hheavy
  obtain ⟨t, ht⟩ := budgetedChargedHeavyAppearanceCodes_complete hcU
    x y.length baseBudget (finiteSetFstHeavyTruncation B threshold) hpool
  let hHne : (finiteSetFstHeavyTruncation B threshold).Nonempty :=
    ⟨x, finiteSetFstHeavyTruncation_mem hpair hheavy⟩
  rw [canonicalUniformCodeOfList_canonicalFinsetList
    (finiteSetFstHeavyTruncation B threshold) hHne] at ht
  exact ⟨t, ht⟩

/-- **Pooled distinct-truncation compression lemma.**  Exact conditional
information gain from the true heavy truncation forces some finite stage of
the all-size appearance enumeration to contain exponentially many distinct
truncation codes.  The exponent pays only logarithmic slack in the visible
complexity budget and the noise length; in particular it contains no `j` term.

This is the direct compression-contradiction part of the pooled route.  The
remaining step toward `BudgetedPairProjectionManyStatement` is combinatorial:
extract enough descriptions with common complexity and size coordinates from
this pooled collection, using a weight that does not reintroduce `j`. -/
theorem exists_budgetedChargedHeavyAppearanceCodes_many_of_information_gain
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∃ cU : Code, IsCodeFor cU U ∧
      ∀ (x y : BitString) (epsilon baseBudget i j threshold gain : ℕ)
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
        ∃ t : ℕ,
          (codedUniformOn (finiteSetFstHeavyTruncation B threshold)
              ⟨x, finiteSetFstHeavyTruncation_mem hpair hheavy⟩).code ∈
            budgetedChargedHeavyAppearanceCodes cU x y.length baseBudget t ∧
          2 ^ (gain - epsilon -
              (logSlack c baseBudget + logSlack c y.length)) ≤
            (budgetedChargedHeavyAppearanceCodes cU x y.length baseBudget t).length := by
  obtain ⟨cU, hcU⟩ : ∃ cU : Code, IsCodeFor cU U :=
    Nat.Partrec.Code.exists_code.mp hU.1.1
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV
    (budgetedChargedHeavyGainDecoder cU V)
    (budgetedChargedHeavyGainDecoder_partrec cU V hV.1)
  refine ⟨11 + C, cU, hcU, ?_⟩
  intro x y epsilon baseBudget i j threshold gain B hB hpair hi hthreshold
    hheavy hincompressible hgain
  obtain ⟨t, ht⟩ := exists_heavyTruncation_mem_budgetedAppearanceCodes
    U cU hcU x y baseBudget i j threshold B hB hpair hi hthreshold hheavy
  refine ⟨t, ht, ?_⟩
  exact budgetedChargedHeavyAppearanceCodes_length_lower_of_decoder_bound
    V C cU hC x y
      (codedUniformOn (finiteSetFstHeavyTruncation B threshold)
        ⟨x, finiteSetFstHeavyTruncation_mem hpair hheavy⟩).code
      epsilon baseBudget gain t ht hincompressible hgain

end Kolmogorov
