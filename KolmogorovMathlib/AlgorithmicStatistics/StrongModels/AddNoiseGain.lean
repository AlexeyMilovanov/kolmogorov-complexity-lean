import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseRank

/-!
# Multiplicity from an information gain

The direct add-noise route needs the following counting step.  Suppose `x` and a
noise string `y` are such that `y` is incompressible given `x` up to `epsilon`,
while `y` becomes compressible by `k` bits once the canonical first-coordinate
truncation `A` of an `(i,j)`-description `B` containing `⟨x, y⟩` is added to the
condition.  Then `x` must have at least `2 ^ (k - epsilon - O(log))` distinct
candidate truncations at those parameters.

The proof is a direct compression argument: if there were fewer candidates, the
truncation could be addressed by its fixed-width rank in the append-only
enumeration of `AddNoiseEnumeration.lean`, and concatenating that address with
the short program for `y` given `⟨x, A⟩` would compress `y` given `x` below its
assumed incompressibility threshold.

The gain hypothesis is stated as `condK V y ⟨x, A⟩ + k ≤ |y|`, i.e. an exact
`k`-bit gain.  A variant carrying an extra `+ logSlack c (…)` on the same
constant `c` that is subtracted in the conclusion is *not* provable this way:
the two slack terms cancel and the unavoidable decoder overhead then exceeds the
budget.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-! ### A primitive recursive fixed-width prefix -/

/-- The first `n` symbols of a bit string, written through `reverse`/`drop` so
that it is manifestly primitive recursive. -/
def bitPrefix (n : ℕ) (s : BitString) : BitString :=
  (s.reverse.drop (s.length - n)).reverse

@[simp] theorem bitPrefix_append (a b : BitString) :
    bitPrefix a.length (a ++ b) = a := by
  unfold bitPrefix
  rw [List.reverse_append, List.length_append]
  rw [show a.length + b.length - a.length = b.reverse.length by simp]
  rw [List.drop_left, List.reverse_reverse]

theorem list_drop_primrec :
    Primrec₂ (fun (l : BitString) (n : ℕ) => l.drop n) := by
  have h : (fun (l : BitString) (n : ℕ) => l.drop n)
      = fun l n => Nat.rec l (fun _ ih => ih.tail) n := by
    funext l n
    induction n with
    | zero => rfl
    | succ n ih => rw [← List.tail_drop, ih]
  rw [h]
  exact Primrec.nat_rec' Primrec.snd Primrec.fst
    (Primrec.list_tail.comp (Primrec.snd.comp Primrec.snd)).to₂

theorem bitPrefix_primrec : Primrec₂ bitPrefix := by
  have hrev : Primrec (fun q : ℕ × BitString => q.2.reverse) :=
    Primrec.list_reverse.comp Primrec.snd
  have hsub : Primrec (fun q : ℕ × BitString => q.2.length - q.1) :=
    Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst
  exact (Primrec.list_reverse.comp (list_drop_primrec.comp hrev hsub)).to₂

/-! ### The packed gain program -/

/-- Program of the gain decoder: the parameters `(l, i, j, m)` in a
self-delimiting prefix, then the `m`-bit address of the rank, then the program
for `y` given the pair `⟨x, A⟩`. -/
def noiseGainProgram (l i j m r : ℕ) (q : BitString) : BitString :=
  pairCode (pairCode (Nat.bits l)
      (pairCode (Nat.bits i) (pairCode (Nat.bits j) (Nat.bits m))))
    (chunkAddress r m ++ q)

/-- The parameter block of a gain program. -/
def noiseGainParams (p : BitString) : BitString := decodeFirst p
/-- The noise length packed into a gain program. -/
def noiseGainL (p : BitString) : ℕ := bitsToNat (decodeFirst (noiseGainParams p))
/-- The complexity parameter packed into a gain program. -/
def noiseGainI (p : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond (noiseGainParams p)))
/-- The size parameter packed into a gain program. -/
def noiseGainJ (p : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond (decodeSecond (noiseGainParams p))))
/-- The rank width packed into a gain program. -/
def noiseGainM (p : BitString) : ℕ :=
  bitsToNat (decodeSecond (decodeSecond (decodeSecond (noiseGainParams p))))
/-- The rank packed into a gain program. -/
def noiseGainR (p : BitString) : ℕ :=
  bitsToNat (bitPrefix (noiseGainM p) (decodeSecond p))
/-- The suffix program packed into a gain program. -/
def noiseGainQ (p : BitString) : BitString := (decodeSecond p).drop (noiseGainM p)

@[simp] theorem noiseGainL_program (l i j m r : ℕ) (q : BitString) :
    noiseGainL (noiseGainProgram l i j m r q) = l := by
  simp [noiseGainL, noiseGainParams, noiseGainProgram, decodeFirst_pairCode,
    bitsToNat_bits]

@[simp] theorem noiseGainI_program (l i j m r : ℕ) (q : BitString) :
    noiseGainI (noiseGainProgram l i j m r q) = i := by
  simp [noiseGainI, noiseGainParams, noiseGainProgram, decodeFirst_pairCode,
    decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem noiseGainJ_program (l i j m r : ℕ) (q : BitString) :
    noiseGainJ (noiseGainProgram l i j m r q) = j := by
  simp [noiseGainJ, noiseGainParams, noiseGainProgram, decodeFirst_pairCode,
    decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem noiseGainM_program (l i j m r : ℕ) (q : BitString) :
    noiseGainM (noiseGainProgram l i j m r q) = m := by
  simp [noiseGainM, noiseGainParams, noiseGainProgram, decodeFirst_pairCode,
    decodeSecond_pairCode, bitsToNat_bits]

theorem noiseGainR_program (l i j m r : ℕ) (q : BitString) (hr : r < 2 ^ m) :
    noiseGainR (noiseGainProgram l i j m r q) = r := by
  have hlen : (chunkAddress r m).length = m := chunkAddress_length r m hr
  have hpre : bitPrefix m (chunkAddress r m ++ q) = chunkAddress r m := by
    have hp := bitPrefix_append (chunkAddress r m) q
    rwa [hlen] at hp
  rw [noiseGainR, noiseGainM_program, noiseGainProgram, decodeSecond_pairCode,
    hpre, bitsToNat_chunkAddress]

theorem noiseGainQ_program (l i j m r : ℕ) (q : BitString) (hr : r < 2 ^ m) :
    noiseGainQ (noiseGainProgram l i j m r q) = q := by
  have hlen : (chunkAddress r m).length = m := chunkAddress_length r m hr
  have hdrop : (chunkAddress r m ++ q).drop m = q := by
    have hd : (chunkAddress r m ++ q).drop (chunkAddress r m).length = q := List.drop_left
    rwa [hlen] at hd
  rw [noiseGainQ, noiseGainM_program, noiseGainProgram, decodeSecond_pairCode, hdrop]

theorem length_noiseGainProgram (l i j m r : ℕ) (q : BitString) (hr : r < 2 ^ m) :
    (noiseGainProgram l i j m r q).length =
      2 * (2 * (Nat.bits l).length + 1 + (2 * (Nat.bits i).length + 1 +
        (2 * (Nat.bits j).length + 1 + (Nat.bits m).length))) + 1 + (m + q.length) := by
  rw [noiseGainProgram, length_pairCode, length_pairCode, length_pairCode,
    length_pairCode, List.length_append, chunkAddress_length r m hr]
  ring

theorem noiseGainL_primrec : Primrec noiseGainL :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp decodeFirst_primrec)
theorem noiseGainI_primrec : Primrec noiseGainI :=
  bitsToNat_primrec.comp
    (decodeFirst_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec))
theorem noiseGainJ_primrec : Primrec noiseGainJ :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp
    (decodeSecond_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec)))
theorem noiseGainM_primrec : Primrec noiseGainM :=
  bitsToNat_primrec.comp (decodeSecond_primrec.comp
    (decodeSecond_primrec.comp (decodeSecond_primrec.comp decodeFirst_primrec)))
theorem noiseGainR_primrec : Primrec noiseGainR :=
  bitsToNat_primrec.comp
    (bitPrefix_primrec.comp noiseGainM_primrec decodeSecond_primrec)
theorem noiseGainQ_primrec : Primrec noiseGainQ :=
  list_drop_primrec.comp decodeSecond_primrec noiseGainM_primrec

/-! ### The gain decoder -/

/-- Given `x` as condition, decode the rank of a candidate truncation `A`, then
run `V` on the suffix program with condition `⟨x, A⟩`. -/
noncomputable def noiseGainDecoder (cU : Code) (V : Map) :
    BitString → BitString →. BitString :=
  fun x p =>
    (Nat.rfind (fun t => Part.some (decide (noiseGainR p <
      (noiseCandidateTruncationAppearanceCodes cU x (noiseGainL p) (noiseGainI p)
        (noiseGainJ p) t).length)))).bind
      (fun t => V (noiseGainQ p, pairCode x
        ((noiseCandidateTruncationAppearanceCodes cU x (noiseGainL p) (noiseGainI p)
          (noiseGainJ p) t).getD (noiseGainR p) [])))

section GainPartrec
attribute [local irreducible] noiseCandidateTruncationAppearanceCodes
  noiseGainL noiseGainI noiseGainJ noiseGainM noiseGainR noiseGainQ

theorem noiseGainDecoder_partrec (cU : Code) (V : Map) (hV : isDecompressor V) :
    Partrec (fun w : BitString × BitString => noiseGainDecoder cU V w.1 w.2) := by
  have hcodes : Computable (fun st : (BitString × BitString) × ℕ =>
      noiseCandidateTruncationAppearanceCodes cU st.1.1 (noiseGainL st.1.2)
        (noiseGainI st.1.2) (noiseGainJ st.1.2) st.2) :=
    (noiseCandidateTruncationAppearanceCodes_computable cU).comp
      ((((Computable.fst.comp Computable.fst).pair
        (((noiseGainL_primrec.to_comp).comp (Computable.snd.comp Computable.fst)).pair
          ((noiseGainJ_primrec.to_comp).comp
            (Computable.snd.comp Computable.fst)))).pair
        ((noiseGainI_primrec.to_comp).comp
          (Computable.snd.comp Computable.fst))).pair Computable.snd)
  have hrank : Computable (fun st : (BitString × BitString) × ℕ => noiseGainR st.1.2) :=
    (noiseGainR_primrec.to_comp).comp (Computable.snd.comp Computable.fst)
  have hlt : Computable (fun q : ℕ × ℕ => decide (q.1 < q.2)) := by
    obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel (α := ℕ) (· < ·))
    convert h.to_comp
  have hcheck : Computable (fun st : (BitString × BitString) × ℕ =>
      decide (noiseGainR st.1.2 <
        (noiseCandidateTruncationAppearanceCodes cU st.1.1 (noiseGainL st.1.2)
          (noiseGainI st.1.2) (noiseGainJ st.1.2) st.2).length)) :=
    hlt.comp (hrank.pair (Computable.list_length.comp hcodes))
  have hentry : Computable (fun st : (BitString × BitString) × ℕ =>
      (noiseCandidateTruncationAppearanceCodes cU st.1.1 (noiseGainL st.1.2)
        (noiseGainI st.1.2) (noiseGainJ st.1.2) st.2).getD (noiseGainR st.1.2) []) :=
    ((Primrec.list_getD ([] : BitString)).to_comp).comp hcodes hrank
  have hbody : Partrec (fun st : (BitString × BitString) × ℕ =>
      V (noiseGainQ st.1.2, pairCode st.1.1
        ((noiseCandidateTruncationAppearanceCodes cU st.1.1 (noiseGainL st.1.2)
          (noiseGainI st.1.2) (noiseGainJ st.1.2) st.2).getD (noiseGainR st.1.2) []))) :=
    hV.comp (((noiseGainQ_primrec.to_comp).comp
      (Computable.snd.comp Computable.fst)).pair
      ((pairCode_primrec.to_comp).comp (Computable.fst.comp Computable.fst) hentry))
  refine (Partrec.bind (Partrec.rfind hcheck.to₂.partrec₂) hbody.to₂).of_eq
    (fun w => ?_)
  unfold noiseGainDecoder
  refine congr_arg₂ Part.bind (congr_arg Nat.rfind ?_) rfl
  funext t; exact PFun.coe_val _ t

theorem mem_noiseGainDecoder
    (cU : Code) (V : Map) (x : BitString) (l i j m r t : ℕ) (q : BitString)
    (hrm : r < 2 ^ m)
    (hlt : r < (noiseCandidateTruncationAppearanceCodes cU x l i j t).length)
    {y : BitString}
    (hy : y ∈ V (q, pairCode x
      ((noiseCandidateTruncationAppearanceCodes cU x l i j t).getD r []))) :
    y ∈ noiseGainDecoder cU V x (noiseGainProgram l i j m r q) := by
  classical
  set P : ℕ → Prop := fun s =>
    r < (noiseCandidateTruncationAppearanceCodes cU x l i j s).length with hP
  have hex : ∃ s, P s := ⟨t, hlt⟩
  set t₀ := Nat.find hex with ht₀
  have ht₀P : P t₀ := Nat.find_spec hex
  have ht₀le : t₀ ≤ t := Nat.find_le hlt
  have hstable :
      (noiseCandidateTruncationAppearanceCodes cU x l i j t₀).getD r [] =
        (noiseCandidateTruncationAppearanceCodes cU x l i j t).getD r [] :=
    getD_eq_of_prefix
      (noiseCandidateTruncationAppearanceCodes_prefix_of_le cU x l i j ht₀le) ht₀P
  unfold noiseGainDecoder
  rw [noiseGainL_program, noiseGainI_program, noiseGainJ_program,
    noiseGainR_program l i j m r q hrm, noiseGainQ_program l i j m r q hrm,
    Part.mem_bind_iff]
  refine ⟨t₀, ?_, ?_⟩
  · rw [Nat.mem_rfind]
    refine ⟨by simpa using ht₀P, ?_⟩
    intro s hs
    have hs' : ¬ P s := Nat.find_min hex hs
    simpa using Nat.le_of_not_lt hs'
  · rw [hstable]
    exact hy

end GainPartrec

/-! ### The multiplicity bound -/

/-- The packed gain program fits in `m + |q|` bits plus logarithmic slack. -/
private theorem noiseGainProgram_length_slack (C : ℕ) (x y : BitString) (i j k m r : ℕ)
    (q : BitString) (hrm : r < 2 ^ m) (hm : m ≤ k) :
    (noiseGainProgram y.length i j m r q).length + C ≤
      m + q.length + logSlack (20 + C) (x.length + y.length + i + j + k) := by
  set M := x.length + y.length + i + j + k with hM
  set W := (Nat.bits M).length with hW
  have hlM : (Nat.bits y.length).length ≤ W := length_natBits_mono (by omega)
  have hiM : (Nat.bits i).length ≤ W := length_natBits_mono (by omega)
  have hjM : (Nat.bits j).length ≤ W := length_natBits_mono (by omega)
  have hmM : (Nat.bits m).length ≤ W := length_natBits_mono (by omega)
  have hlog : 14 * W + 7 + C ≤ logSlack (20 + C) M := by
    unfold logSlack
    rw [← hW]
    nlinarith [Nat.zero_le W, Nat.zero_le (C * W)]
  rw [length_noiseGainProgram y.length i j m r q hrm]
  omega

/-- The pure arithmetic of the compression contradiction. -/
private theorem gain_arith (yl k epsilon m qlen S T : ℕ)
    (hm : m = k - epsilon - S) (hdeg : epsilon + S < k) (hq : qlen ≤ yl - k)
    (hkle : k ≤ yl) (hnat : yl ≤ m + qlen + T + epsilon) (hST : T + 1 ≤ S) : False := by
  omega

/-- **Leaf packet 3.**  An information gain of `k` bits from the canonical
truncation of an `(i,j)`-description forces at least `2 ^ (k - epsilon - O(log))`
distinct candidate truncations. -/
theorem noiseCandidateTruncations_card_lower_of_information_gain
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString) (epsilon i j k : ℕ) (B : Finset BitString)
      (_ : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
      (hpair : pairCode x y ∈ B),
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      condK V y (pairCode x
          (codedUniformOn (finiteSetFstTruncation B)
            ⟨x, finiteSetFstTruncation_mem hpair⟩).code) + (k : ENat) ≤
        (y.length : ENat) →
      2 ^ (k - epsilon - logSlack c (x.length + y.length + i + j + k)) ≤
        (noiseCandidateTruncations U x y.length i j).card := by
  classical
  obtain ⟨cU, hcU⟩ : ∃ cU : Code, IsCodeFor cU U :=
    Nat.Partrec.Code.exists_code.mp hU.1.1
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV (noiseGainDecoder cU V)
    (noiseGainDecoder_partrec cU V hV.1)
  refine ⟨21 + C, ?_⟩
  intro x y epsilon i j k B hB hpair hincompressible hgain
  set A := finiteSetFstTruncation B with hA
  have hAne : A.Nonempty := ⟨x, finiteSetFstTruncation_mem hpair⟩
  set M := x.length + y.length + i + j + k with hM
  set S := logSlack (21 + C) M with hS
  -- the candidate set is nonempty, which settles the degenerate case
  have hAmem : A ∈ noiseCandidateTruncations U x y.length i j := by
    rw [noiseCandidateTruncations, Finset.mem_image]
    refine ⟨B, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨hB, y, by simp [stringsOfLength], hpair⟩
  have hcardpos : 1 ≤ (noiseCandidateTruncations U x y.length i j).card :=
    Finset.card_pos.mpr ⟨A, hAmem⟩
  by_cases hdeg : k ≤ epsilon + S
  · have : k - epsilon - S = 0 := by omega
    rw [this, pow_zero]
    exact hcardpos
  push_neg at hdeg
  set m := k - epsilon - S with hm
  by_contra hcon
  push_neg at hcon
  -- fewer than `2 ^ m` candidates: address the truncation by its rank
  obtain ⟨_, _, hiff, hlen⟩ := noiseCandidateTruncationAppearanceCodes_spec hcU
  obtain ⟨t, ht⟩ := (hiff x y.length i j A).mp hAmem
  rw [canonicalUniformCodeOfList_canonicalFinsetList A hAne] at ht
  obtain ⟨r, hr, hget⟩ :
      ∃ r, r < (noiseCandidateTruncationAppearanceCodes cU x y.length i j t).length ∧
        (noiseCandidateTruncationAppearanceCodes cU x y.length i j t).getD r [] =
          (codedUniformOn A hAne).code := by
    rw [List.mem_iff_getElem] at ht
    obtain ⟨r, hr, hget⟩ := ht
    exact ⟨r, hr, by simp [List.getD_eq_getElem?_getD, hr, hget]⟩
  have hrm : r < 2 ^ m :=
    lt_of_lt_of_le hr ((hlen x y.length i j t).trans_lt hcon).le
  -- the short program for `y` given the pair
  have hkle : condK V y (pairCode x (codedUniformOn A hAne).code) ≤
      ((y.length - k : ℕ) : ENat) := by
    have hfin : condK V y (pairCode x (codedUniformOn A hAne).code) ≠ ⊤ := by
      intro htop
      rw [htop] at hgain
      simp at hgain
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hn] at hgain ⊢
    have : n + k ≤ y.length := by exact_mod_cast hgain
    exact_mod_cast Nat.le_sub_of_add_le this
  obtain ⟨q, hqlen, hq⟩ :=
    (condKLeIff V y (pairCode x (codedUniformOn A hAne).code) (y.length - k)).mp hkle
  have hqlen' : q.length ≤ y.length - k := hqlen
  -- run the gain decoder
  have hmem : y ∈ noiseGainDecoder cU V x (noiseGainProgram y.length i j m r q) := by
    refine mem_noiseGainDecoder cU V x y.length i j m r t q hrm hr ?_
    rw [hget]
    exact hq
  have hbound := hC x (noiseGainProgram y.length i j m r q) y hmem
  have hslack := noiseGainProgram_length_slack C x y i j k m r q hrm (by omega)
  have hfinal : condK V y x ≤
      ((m + q.length + logSlack (20 + C) M : ℕ) : ENat) := by
    calc condK V y x
        ≤ ((noiseGainProgram y.length i j m r q).length : ENat) + (C : ENat) := hbound
      _ = (((noiseGainProgram y.length i j m r q).length + C : ℕ) : ENat) := by norm_cast
      _ ≤ ((m + q.length + logSlack (20 + C) M : ℕ) : ENat) := by exact_mod_cast hslack
  -- contradiction with incompressibility
  have hklen : k ≤ y.length := by
    have hk : (k : ENat) ≤ (y.length : ENat) := le_trans le_add_self hgain
    exact_mod_cast hk
  have hnat : y.length ≤ (m + q.length + logSlack (20 + C) M) + epsilon := by
    have hstep : (y.length : ENat) ≤
        ((m + q.length + logSlack (20 + C) M : ℕ) : ENat) + (epsilon : ENat) :=
      le_trans hincompressible (add_le_add hfinal (le_refl (epsilon : ENat)))
    exact_mod_cast hstep
  have hSbig : logSlack (20 + C) M + 1 ≤ S := by
    rw [hS, show (21 : ℕ) + C = (20 + C) + 1 by ring]
    exact logSlack_add_const_le (20 + C) 1 M
  exact gain_arith y.length k epsilon m q.length S (logSlack (20 + C) M)
    hm hdeg hqlen' hklen hnat hSbig

end Kolmogorov
