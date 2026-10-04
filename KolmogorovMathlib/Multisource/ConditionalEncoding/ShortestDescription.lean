import KolmogorovMathlib.CommonInformation.Definitions
import KolmogorovMathlib.CommonInformation.OverlapExtraction
import KolmogorovMathlib.CommonInformation.Splitting
import KolmogorovMathlib.Multisource.Requests
import KolmogorovMathlib.Foundation.ListUtil

/-!
# Conditional shortest descriptions are simple given both strings

SUV Problem 317, p. 369.

A shortest description `P` of `A` given `B` has complexity `O(log C(A,B))` given the pair
`(A, B)` (`condK_conditionalShortestDescription_le_log`): there are only `O(1)` shortest
conditional descriptions of the same length, so each is specified by its index among them
together with its length.
-/

namespace Kolmogorov

/-- The triple `(A, B, P)` is computed from the pair `(B, P)` when `D(P, B) = A`, so
`C(A, B, P) ≤ C(B, P) + O(1)`. -/
private theorem pairPlainK_triple_le_pairPlainK_program (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ A B P : BitString, produces D P B A →
      plainK D (pairCode (pairCode A B) P) ≤ pairPlainK D B P + (c : ℕ∞) := by
  let g : BitString × BitString → BitString := fun q =>
    pairCode (pairCode q.2 (decodeFirst q.1)) (decodeSecond q.1)
  let f : BitString →. BitString := fun z =>
    (D (decodeSecond z, decodeFirst z)).map fun A => g (z, A)
  have hRun : Partrec (fun z : BitString => D (decodeSecond z, decodeFirst z)) :=
    Partrec.comp hD.1 (decodeSecond_computable.pair decodeFirst_computable)
  have hMap : Computable g :=
    (pairCode_computable.comp
      ((pairCode_computable.comp
        (Computable.snd.pair (decodeFirst_computable.comp Computable.fst))).pair
        (decodeSecond_computable.comp Computable.fst))).of_eq (fun _ => rfl)
  have hf : Partrec f := Partrec.map hRun hMap
  let E : Map := fun pr => (D (pr.1, [])).bind f
  have hFirst : Partrec (fun pr : BitString × BitString => D (pr.1, [])) :=
    Partrec.comp hD.1 (Computable.pair Computable.fst (Computable.const []))
  have hSecond : Partrec (fun q : (BitString × BitString) × BitString => f q.2) :=
    Partrec.comp hf Computable.snd
  have hE : isDecompressor E := Partrec.bind hFirst hSecond
  obtain ⟨c, hc⟩ := hD.2 E hE
  refine ⟨c, fun A B P hP => ?_⟩
  obtain ⟨kq, hkq⟩ := exists_plainComplexityValue D hD (pairCode B P)
  obtain ⟨q, hq, hqLen⟩ := hkq.exists_program
  have hEprod : produces E q [] (pairCode (pairCode A B) P) := by
    refine Part.mem_bind_iff.mpr ⟨pairCode B P, hq, ?_⟩
    change pairCode (pairCode A B) P ∈
      (D (decodeSecond (pairCode B P), decodeFirst (pairCode B P))).map
        fun A => g (pairCode B P, A)
    have hg : (fun A => g (pairCode B P, A)) = fun A => pairCode (pairCode A B) P := by
      funext A
      simp only [g, decodeFirst_pairCode, decodeSecond_pairCode]
    rw [decodeFirst_pairCode, decodeSecond_pairCode, hg]
    exact Part.mem_map (fun A => pairCode (pairCode A B) P) hP
  have hkq' : plainK D (pairCode B P) = (kq : ℕ∞) := hkq
  calc
    plainK D (pairCode (pairCode A B) P)
        ≤ plainK E (pairCode (pairCode A B) P) + (c : ℕ∞) := hc _ []
    _ ≤ (q.length : ℕ∞) + (c : ℕ∞) := by
      gcongr
      exact sInf_le ⟨q, hEprod, rfl⟩
    _ = pairPlainK D B P + (c : ℕ∞) := by rw [hqLen, pairPlainK, hkq']

/-- For a shortest program `P` of `A` given `B`, the pair `(B, P)` is no more complex than
`(A, B)` up to a logarithmic term: `C(B, P) ≤ C(B) + C(A|B) + O(log) ≤ C(A, B) + O(log C(A, B))`
by the upper and lower Kolmogorov–Levin chain inequalities. -/
private theorem condK_le_length_of_partrec (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ p y, condK D p y ≤ (p.length : ℕ∞) + c := by
  let E : Map := fun pr => some pr.1
  have hFirst : Partrec (fun q : BitString × BitString => some q.1) :=
    (Computable.fst).partrec.of_eq (fun x => rfl)
  have hE : isDecompressor E := hFirst
  obtain ⟨c, hc⟩ := hD.2 E hE
  refine ⟨c, fun p y => (hc p y).trans ?_⟩
  gcongr
  unfold condK candidateLengths
  refine sInf_le ⟨p, ?_, rfl⟩
  change p ∈ E (p, y)
  unfold E
  exact Part.mem_some p

private theorem plainK_pairCode_swap_le (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x y : BitString, plainK D (pairCode y x) ≤ plainK D (pairCode x y) + (c : ℕ∞) := by
  let E : Map := fun pr =>
    (D pr).bind fun z => (some (pairCode (decodeSecond z) (decodeFirst z)) : Part BitString)
  have hFirst : Partrec D := hD.1
  have hSecond_bind : Partrec (fun q : (BitString × BitString) × BitString =>
      (some (pairCode (decodeSecond q.2) (decodeFirst q.2)) : Part BitString)) :=
    (pairCode_computable.comp ((decodeSecond_computable.comp Computable.snd).pair
      (decodeFirst_computable.comp Computable.snd))).partrec.of_eq (fun x => rfl)
  have hE : isDecompressor E := Partrec.bind hFirst hSecond_bind
  obtain ⟨c, hc⟩ := hD.2 E hE
  refine ⟨c, fun x y => ?_⟩
  have h := hc (pairCode y x) []
  calc
    condK D (pairCode y x) [] ≤ condK E (pairCode y x) [] + (c : ℕ∞) := h
    _ ≤ plainK D (pairCode x y) + (c : ℕ∞) := by
      gcongr
      unfold plainK condK candidateLengths
      refine sInf_le_sInf (fun a ha => ?_)
      simp only [Set.mem_ofPred_eq] at ha
      obtain ⟨p, hp, hp_len⟩ := ha
      have heq : pairCode (decodeSecond (pairCode x y))
          (decodeFirst (pairCode x y)) = pairCode y x := by
        simp only [decodeSecond_pairCode, decodeFirst_pairCode]
      refine ⟨p, ?_, hp_len⟩
      change pairCode y x ∈ E (p, [])
      unfold E
      rw [Part.mem_bind_iff]
      refine ⟨pairCode x y, hp, ?_⟩
      rw [heq]
      exact Part.mem_some (pairCode y x)

private theorem exists_pairPlainK_program_le_pair_add_log (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (A B P : BitString) (k kAB : ℕ),
      HasPlainConditionalComplexityValue D A B k → produces D P B A → P.length = k →
      HasPlainComplexityValue D (pairCode A B) kAB →
      ∃ s : ℕ, HasPlainComplexityValue D (pairCode B P) s ∧ s ≤ kAB + logSlack c (kAB + 1) := by
  obtain ⟨cU, hU⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cL, hL⟩ := pairPlainK_chain_lower_values D hD
  obtain ⟨cS, hS⟩ := plainK_pairCode_swap_le D hD
  obtain ⟨cC, hC⟩ := condK_le_length_of_partrec D hD
  let d := cS + cC + logSlack cL cS
  let cBase := cL + d
  obtain ⟨bU, hbU⟩ := logSlack_le_add_const (2 * cU)
  obtain ⟨cFold, hFold⟩ :=
    logSlack_absorb_of_le_linear cU (2 * (cBase + 1)) (2 * cBase + bU + 2)
  let cFinal := cBase + cFold
  refine ⟨cFinal, fun A B P k kAB hk hP hPlen hkAB => ?_⟩
  obtain ⟨s, hs⟩ := exists_plainComplexityValue D hD (pairCode B P)
  refine ⟨s, hs, ?_⟩
  obtain ⟨kB, hkB⟩ := exists_plainComplexityValue D hD B
  obtain ⟨kBA, hkBA⟩ := exists_plainComplexityValue D hD (pairCode B A)
  obtain ⟨kPB, hkPB⟩ := exists_plainConditionalComplexityValue D hD P B
  have hu : s ≤ kB + kPB + logSlack cU (s + 1) :=
    hU B P kB kPB s hkB hkPB hs
  have hl : kB + k ≤ kBA + logSlack cL (kBA + 1) :=
    hL B A kB k kBA hkB hk hkBA
  have hc : condK D P B ≤ (P.length : ℕ∞) + (cC : ℕ∞) := hC P B
  have hsSwap : plainK D (pairCode B A) ≤
      plainK D (pairCode A B) + (cS : ℕ∞) := hS A B
  have hsSwap_nat : kBA ≤ kAB + cS := by
    have h1 : plainK D (pairCode B A) = (kBA : ℕ∞) := hkBA
    have h2 : plainK D (pairCode A B) = (kAB : ℕ∞) := hkAB
    rw [h1, h2] at hsSwap
    exact_mod_cast hsSwap
  have hc_nat : kPB ≤ k + cC := by
    have h1 : condK D P B = (kPB : ℕ∞) := hkPB
    rw [h1, hPlen] at hc
    exact_mod_cast hc
  have hshift : logSlack cL (kAB + cS + 1) ≤
      logSlack cL (kAB + 1) + logSlack cL cS := by
    simpa only [show kAB + cS + 1 = (kAB + 1) + cS by omega] using
      logSlack_add_le cL (kAB + 1) cS
  have hbase : kB + kPB ≤ kAB + logSlack cBase (kAB + 1) := by
    have hadd : logSlack cL (kAB + 1) + d ≤ logSlack cBase (kAB + 1) := by
      dsimp [cBase]
      exact logSlack_add_nat_le cL d (kAB + 1)
    dsimp [d] at hadd
    calc
      kB + kPB ≤ kB + k + cC := by omega
      _ ≤ kBA + logSlack cL (kBA + 1) + cC := by omega
      _ ≤ kAB + cS + logSlack cL (kAB + cS + 1) + cC := by
        have hmono : logSlack cL (kBA + 1) ≤
            logSlack cL (kAB + cS + 1) := logSlack_mono_right cL (by omega)
        omega
      _ ≤ kAB + (logSlack cL (kAB + 1) +
          (cS + cC + logSlack cL cS)) := by omega
      _ ≤ kAB + logSlack cBase (kAB + 1) := by omega
  have hsUpper : s ≤ kAB + logSlack cBase (kAB + 1) + logSlack cU (s + 1) := by
    omega
  have hdouble : 2 * logSlack cU (s + 1) = logSlack (2 * cU) (s + 1) := by
    unfold logSlack
    ring
  have hself : 2 * logSlack cU (s + 1) ≤ s + 1 + bU := by
    rw [hdouble]
    exact hbU (s + 1)
  have hbaseLinear : kAB + logSlack cBase (kAB + 1) ≤
      (cBase + 1) * (kAB + 1) + cBase := by
    have hlin := logSlack_le_self_linear cBase (kAB + 1)
    nlinarith
  have hsLinear : s + 1 ≤
      2 * (cBase + 1) * (kAB + 1) + (2 * cBase + bU + 2) := by
    nlinarith
  have hselfFold : logSlack cU (s + 1) ≤ logSlack cFold (kAB + 1) :=
    hFold (kAB + 1) (s + 1) (by simpa [Nat.mul_assoc] using hsLinear)
  calc
    s ≤ kAB + logSlack cBase (kAB + 1) + logSlack cU (s + 1) := hsUpper
    _ ≤ kAB + logSlack cBase (kAB + 1) + logSlack cFold (kAB + 1) := by
      omega
    _ = kAB + logSlack cFinal (kAB + 1) := by
      dsimp only [cFinal]
      rw [Nat.add_assoc, ← logSlack_add_constants]


/-- The triple `(A, B, P)`, for a shortest program `P` of `A` given `B`, is no more complex
than the pair `(A, B)` up to a logarithmic term: `C(A, B, P) ≤ C(A, B) + O(log C(A, B))`.
Indeed `(A, B, P)` is computed from `(B, P)`, and `C(B, P) ≤ C(B) + C(A|B) + O(log)`, which
is `C(A, B) + O(log)` by the Kolmogorov–Levin chain inequality. -/
private theorem exists_pairPlainK_triple_le_pair_add_log (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (A B P : BitString) (k kAB : ℕ),
      HasPlainConditionalComplexityValue D A B k → produces D P B A → P.length = k →
      HasPlainComplexityValue D (pairCode A B) kAB →
      ∃ r : ℕ, HasPlainComplexityValue D (pairCode (pairCode A B) P) r ∧
        r ≤ kAB + logSlack c (kAB + 1) := by
  obtain ⟨cT, hT⟩ := pairPlainK_triple_le_pairPlainK_program D hD
  obtain ⟨cB, hB⟩ := exists_pairPlainK_program_le_pair_add_log D hD
  refine ⟨cB + cT, fun A B P k kAB hk hP hPlen hkAB => ?_⟩
  obtain ⟨r, hr⟩ := exists_plainComplexityValue D hD (pairCode (pairCode A B) P)
  obtain ⟨s, hs, hsle⟩ := hB A B P k kAB hk hP hPlen hkAB
  refine ⟨r, hr, ?_⟩
  have hr' : plainK D (pairCode (pairCode A B) P) = (r : ℕ∞) := hr
  have hs' : plainK D (pairCode B P) = (s : ℕ∞) := hs
  have hrs : (r : ℕ∞) ≤ ((s + cT : ℕ) : ℕ∞) := by
    rw [← hr']
    refine (hT A B P hP).trans ?_
    rw [pairPlainK, hs']
    push_cast
    exact le_rfl
  have hrsNat : r ≤ s + cT := by exact_mod_cast hrs
  have hslack : logSlack cB (kAB + 1) + cT ≤ logSlack (cB + cT) (kAB + 1) := by
    unfold logSlack
    nlinarith [Nat.zero_le (cT * (Nat.bits (kAB + 1)).length)]
  omega

/-- The Kolmogorov–Levin chain inequality `k + q ≤ r + O(log r)` together with a logarithmic
excess `r ≤ k + O(log k)` bounds `q` by `O(log k)`: the logarithmic version of
`chain_lower_close_conditional`. -/
private theorem chain_lower_close_log (cPair cChain : ℕ) :
    ∃ C : ℕ, ∀ k q r : ℕ,
      r ≤ k + logSlack cPair (k + 1) →
      k + q ≤ r + logSlack cChain (r + 1) →
      q ≤ logSlack C (k + 1) := by
  obtain ⟨cOver, hOver⟩ := polynomialOverhead_bits_le_logSlack (2 * cPair + 1) 1 (by omega)
  refine ⟨cPair + (cChain * cOver + cChain), fun k q r hr hchain => ?_⟩
  have hlin : logSlack cPair (k + 1) ≤ cPair * (k + 1) + cPair :=
    logSlack_le_self_linear cPair (k + 1)
  have hone : cPair ≤ cPair * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hr1 : r + 1 ≤ (2 * cPair + 1) * (k + 1) ^ 1 := by
    rw [pow_one]
    nlinarith
  have hbits : (Nat.bits (r + 1)).length ≤ cOver * (Nat.bits (k + 1)).length + cOver := by
    calc
      (Nat.bits (r + 1)).length = Nat.size (r + 1) := Nat.size_eq_bits_len _
      _ ≤ Nat.size ((2 * cPair + 1) * (k + 1) ^ 1) := Nat.size_le_size hr1
      _ = (Nat.bits ((2 * cPair + 1) * (k + 1) ^ 1)).length := (Nat.size_eq_bits_len _).symm
      _ ≤ logSlack cOver k := hOver k
      _ ≤ logSlack cOver (k + 1) := logSlack_mono_right cOver (by omega)
  have hslack : logSlack cChain (r + 1) ≤ logSlack (cChain * cOver + cChain) (k + 1) := by
    unfold logSlack
    nlinarith [hbits, Nat.zero_le (cChain * (Nat.bits (k + 1)).length)]
  have hadd := logSlack_add_constants cPair (cChain * cOver + cChain) (k + 1)
  omega

/-- Every shortest description of `A` given `B` has logarithmic complexity given `A` and `B`:
if `D(P, B) = A` and `l(P) = C(A|B)`, then `C(P | A, B) = O(log C(A,B))`.  There are only
`O(1)` shortest descriptions (the conditional form of `card_shortestDescriptions_le`,
Exercise 40, which is the book's hint), so each of them is specified by its index among them
together with its length.  The exact values `C(A|B) = k` and `C(A,B) = kAB` are passed as
witnesses, in the form of `condK_shortestDescription_le` (the unconditional statement, which
does not cover conditional descriptions).

SUV Problem 317, p. 369. -/
theorem condK_conditionalShortestDescription_le_log (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (A B P : BitString) (k kAB : ℕ),
      HasPlainConditionalComplexityValue D A B k → produces D P B A → P.length = k →
      HasPlainComplexityValue D (pairCode A B) kAB →
      condK D P (pairCode A B) ≤ (logSlack c (kAB + 1) : ℕ∞) := by
  obtain ⟨cTriple, hTriple⟩ := exists_pairPlainK_triple_le_pair_add_log D hD
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_lower_values D hD
  obtain ⟨cClose, hClose⟩ := chain_lower_close_log cTriple cChain
  refine ⟨cClose, fun A B P k kAB hk hP hPlen hkAB => ?_⟩
  obtain ⟨q, hq⟩ := exists_plainConditionalComplexityValue D hD P (pairCode A B)
  obtain ⟨r, hr, hrle⟩ := hTriple A B P k kAB hk hP hPlen hkAB
  have hchain : kAB + q ≤ r + logSlack cChain (r + 1) :=
    hChain (pairCode A B) P kAB q r hkAB hq hr
  have hqle : q ≤ logSlack cClose (kAB + 1) := hClose kAB q r hrle hchain
  calc
    condK D P (pairCode A B) = (q : ℕ∞) := hq
    _ ≤ (logSlack cClose (kAB + 1) : ℕ∞) := by exact_mod_cast hqle

end Kolmogorov
