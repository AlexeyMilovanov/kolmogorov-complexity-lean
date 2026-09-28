import Mathlib.Data.Nat.Choose.Multinomial
import KolmogorovMathlib.CommonInformation.FixedFrequency
import KolmogorovMathlib.CommonInformation.FixedHistogram
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaCount
import KolmogorovMathlib.CommonInformation.TypeBounds
import KolmogorovMathlib.CommonInformation.FixedHistogramRank.RankDecoder
import KolmogorovMathlib.CommonInformation.FixedHistogramRank.PlainAndFibreDecoders

/-!
# The fibre of a projection, enumerated

`condK_fixedHistogramWord_given_projection_le`: a word of prescribed histogram is described,
given its projection to the first coordinate, by its rank in the fibre — so the conditional
complexity is at most the logarithm of the fibre size, which
`length_fixedHistogramFiberWords` computes exactly (the marginal hypothesis is necessary).

The decoder is `fixedHistogramLiftDecoder`, a fixed-width rank decoder over the numeric
enumeration `numericFixedHistogramFiberWords`; `mem_numericFiber`, `numericGeneral_nodup` and
the `_primrec` lemmas show that enumeration lists exactly the fibre, without repetition and
effectively, and `fixedHistogramLiftDecoder_recovers` is its correctness.

`exists_fixedHistogramWord_condK_gt` is the matching maximality statement: a class of size at
least `2 ^ (k + 1)` contains a word of conditional complexity above `k`.
-/

namespace Kolmogorov
noncomputable section
open Finset Nat

/-- Exact size of a nonempty projection fibre.  The marginal hypothesis is
necessary: without it the fibre can be empty while the displayed product is
positive. -/
theorem length_fixedHistogramFiberWords
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (w_A : List A) (f : A × B → ℕ)
    (hmargin : ∀ a, w_A.count a = ∑ b, f (a, b)) :
    (fixedHistogramFiberWords w_A f).length =
      ∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b)) := by
  have htoFinset :
      (fixedHistogramFiberWords w_A f).toFinset = (fiberLiftWords w_A f).toFinset := by
    ext w
    simp only [List.mem_toFinset, mem_fixedHistogramLiftWords,
      mem_fiberLiftWords w_A f hmargin w]
  rw [← List.toFinset_card_of_nodup (fixedHistogramLiftWords_nodup w_A f), htoFinset,
    List.toFinset_card_of_nodup (fiberLiftWords_nodup w_A f),
    length_fiberLiftWords w_A f hmargin]

/-- Decode a `finiteWordCode` back to its list of natural-number letter codes. -/
def decodeFiniteWordCode (w : BitString) : List ℕ :=
  (Encodable.decode (bitsToNat w)).getD []

/-- Numeric joint words in the histogram whose first-coordinate code word is
the prescribed projection. -/
def numericFixedHistogramFiberWords
    (projection : List ℕ) (table : List (ℕ × ℕ)) : List (List ℕ) :=
  (numericFixedHistogramWords table).filter fun w =>
    decide (w.map (fun code => code.unpair.1) = projection)

/-- Fixed-width rank decoder for a projection fibre.  Product-letter codes use
`Nat.pair`, so `Nat.unpair` exposes the first-coordinate code without knowing
the source alphabet at runtime. -/
def fixedHistogramLiftDecoder : Map := fun pr =>
  let projection := decodeFiniteWordCode (decodeFirst pr.2)
  let table := decodeHistogramTable (decodeSecond pr.2)
  Part.some
    (((numericFixedHistogramFiberWords projection table).map numericWordCode).getD
      (decodeFixedWidthNatCode pr.1) [])

/-- Decoding a coded word over a finite alphabet into the list of letter codes is primitive
recursive. -/
theorem decodeFiniteWordCode_primrec : Primrec decodeFiniteWordCode := by
  unfold decodeFiniteWordCode
  exact Primrec.option_getD.comp (Primrec.decode.comp bitsToNat_primrec)
    (Primrec.const ([] : List ℕ))

/-- The enumeration of the words with a prescribed histogram lying over a given projection is
primitive recursive. -/
theorem numericFixedHistogramFiberWords_primrec :
    Primrec (fun p : List ℕ × List (ℕ × ℕ) =>
      numericFixedHistogramFiberWords p.1 p.2) := by
  unfold numericFixedHistogramFiberWords
  refine list_filter_primrec (numericFixedHistogramWords_primrec.comp Primrec.snd) ?_
  have hmap : Primrec (fun r : (List ℕ × List (ℕ × ℕ)) × List ℕ =>
      r.2.map (fun code => code.unpair.1)) :=
    Primrec.list_map Primrec.snd
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to₂
  have heq : PrimrecPred (fun r : (List ℕ × List (ℕ × ℕ)) × List ℕ =>
      r.2.map (fun code => code.unpair.1) = r.1.1) :=
    Primrec.eq.comp hmap (Primrec.fst.comp Primrec.fst)
  obtain ⟨_, h⟩ := heq
  exact h.to₂.of_eq fun _ _ => decide_eq_decide.mpr Iff.rfl

/-- The decoder that lifts a projected word to a word of the prescribed histogram, reading the
rank inside the fibre, is a decompressor. -/
theorem fixedHistogramLiftDecoder_isDecompressor :
    isDecompressor fixedHistogramLiftDecoder := by
  have hproj : Primrec (fun pr : BitString × BitString =>
      decodeFiniteWordCode (decodeFirst pr.2)) :=
    decodeFiniteWordCode_primrec.comp
      (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.snd)
  have htable : Primrec (fun pr : BitString × BitString =>
      decodeHistogramTable (decodeSecond pr.2)) :=
    decodeHistogramTable_primrec.comp
      (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.snd)
  have hlist : Primrec (fun pr : BitString × BitString =>
      (numericFixedHistogramFiberWords (decodeFiniteWordCode (decodeFirst pr.2))
        (decodeHistogramTable (decodeSecond pr.2))).map numericWordCode) :=
    Primrec.list_map
      (numericFixedHistogramFiberWords_primrec.comp (Primrec.pair hproj htable))
      (numericWordCode_primrec.comp Primrec.snd).to₂
  have hidx : Primrec (fun pr : BitString × BitString =>
      decodeFixedWidthNatCode pr.1) :=
    decodeFixedWidthNatCode_primrec.comp Primrec.fst
  have hg : Computable (fun pr : BitString × BitString =>
      ((numericFixedHistogramFiberWords (decodeFiniteWordCode (decodeFirst pr.2))
        (decodeHistogramTable (decodeSecond pr.2))).map numericWordCode).getD
        (decodeFixedWidthNatCode pr.1) []) :=
    ((Primrec.list_getD ([] : BitString)).comp hlist hidx).to_comp
  exact hg.partrec

/-- The numeric fixed-histogram family is the numeric image of the family over
the original alphabet. -/
theorem mem_numericFixedHistogramWords_general
    {C : Type*} [Fintype C] [BEq C] [LawfulBEq C] [FiniteLetterCode C]
    (f : C → ℕ) (w' : List ℕ) :
    w' ∈ numericFixedHistogramWords
        (Finset.univ.toList.map (fun c => (FiniteLetterCode.encode c, f c))) ↔
      ∃ v : List C, (∀ c, v.count c = f c) ∧ w' = v.map FiniteLetterCode.encode := by
  classical
  have hlen_gen : ∀ u : List C, u.length = ∑ c, u.count c := by
    intro u
    induction u with
    | nil => simp
    | cons c u ih =>
        simp only [List.length_cons, List.count_cons, ih]
        rw [Finset.sum_add_distrib]
        simp
  have hfst : ((Finset.univ.toList.map
        (fun c : C => (FiniteLetterCode.encode c, f c))).map Prod.fst) =
      Finset.univ.toList.map (FiniteLetterCode.encode : C → ℕ) := by
    rw [List.map_map]; rfl
  have hsnd : (((Finset.univ.toList.map
        (fun c : C => (FiniteLetterCode.encode c, f c))).map Prod.snd).sum) = ∑ c, f c := by
    rw [List.map_map]
    exact Finset.sum_map_toList (Finset.univ : Finset C) f
  rw [numericFixedHistogramWords, List.mem_filter, mem_allWordsFrom, hfst, hsnd]
  simp only [decide_eq_true_eq, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hlen, hmem⟩, hcount⟩
    choose g hg using hmem
    have hmapval :
        (w'.attach.map (fun x => g x.1 x.2)).map FiniteLetterCode.encode = w' := by
      rw [List.map_map]
      have hcomp : (fun x : {x // x ∈ w'} => FiniteLetterCode.encode (g x.1 x.2)) =
          fun x : {x // x ∈ w'} => x.1 := by
        funext x; exact hg x.1 x.2
      rw [Function.comp_def, hcomp]
      simp
    refine ⟨w'.attach.map (fun x => g x.1 x.2), ?_, hmapval.symm⟩
    intro c
    have hc := List.count_map_of_injective
      (w'.attach.map (fun x => g x.1 x.2)) FiniteLetterCode.encode
      FiniteLetterCode.injective c
    rw [hmapval] at hc
    rw [← hc]
    exact hcount (FiniteLetterCode.encode c, f c) ⟨c, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.length_map, hlen_gen v]
      exact Finset.sum_congr rfl fun c _ => hv c
    · intro x hx
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨c, rfl⟩
    · rintro e ⟨c, rfl⟩
      rw [List.count_map_of_injective v FiniteLetterCode.encode FiniteLetterCode.injective c]
      exact hv c

/-- The numeric enumeration of the words of a prescribed histogram has no repetitions. -/
theorem numericGeneral_nodup
    {C : Type*} [Fintype C] [FiniteLetterCode C] (f : C → ℕ) :
    (numericFixedHistogramWords
      (Finset.univ.toList.map (fun c => (FiniteLetterCode.encode c, f c)))).Nodup := by
  have hfst : ((Finset.univ.toList.map
        (fun c : C => (FiniteLetterCode.encode c, f c))).map Prod.fst) =
      Finset.univ.toList.map (FiniteLetterCode.encode : C → ℕ) := by
    rw [List.map_map]; rfl
  rw [numericFixedHistogramWords, hfst]
  exact (allWordsFrom_nodup _ ((Finset.nodup_toList _).map FiniteLetterCode.injective) _).filter _

section Lift

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Taking the first component commutes with the pair coding of the letters. -/
theorem map_encode_unpair_fst (v : List (A × B)) :
    (v.map FiniteLetterCode.encode).map (fun code : ℕ => code.unpair.1) =
      (v.map Prod.fst).map (FiniteLetterCode.encode : A → ℕ) := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left ?_
  rintro ⟨a, b⟩ -
  simp [finiteLetterCode_encode_prod]

/-- The numeric fibre enumeration lists exactly the codes of the words of the prescribed
histogram projecting to the given word. -/
theorem mem_numericFiber (f : A × B → ℕ) (w_A : List A) (w' : List ℕ) :
    w' ∈ numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode)
        (Finset.univ.toList.map (fun ab : A × B => (FiniteLetterCode.encode ab, f ab))) ↔
      ∃ v : List (A × B), ((∀ i, v.count i = f i) ∧ v.map Prod.fst = w_A) ∧
        w' = v.map FiniteLetterCode.encode := by
  rw [numericFixedHistogramFiberWords, List.mem_filter,
    mem_numericFixedHistogramWords_general]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hproj⟩
    rw [map_encode_unpair_fst] at hproj
    exact ⟨v, ⟨hv, List.map_injective_iff.mpr FiniteLetterCode.injective hproj⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hmap⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, by rw [map_encode_unpair_fst, hmap]⟩

/-- The numeric fibre enumeration has no repetitions. -/
theorem numericFiber_nodup (f : A × B → ℕ) (w_A : List A) :
    (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode)
      (Finset.univ.toList.map (fun ab : A × B => (FiniteLetterCode.encode ab, f ab)))).Nodup :=
  (numericGeneral_nodup f).filter _

/-- When the projection has the right marginal histogram, the fibre has
`∏ₐ multinomial (f(a, ·))` elements. -/
theorem length_numericFiber (f : A × B → ℕ) (w_A : List A)
    (hmargin : ∀ a, w_A.count a = ∑ b, f (a, b)) :
    (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode)
      (Finset.univ.toList.map (fun ab : A × B => (FiniteLetterCode.encode ab, f ab)))).length =
      ∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b)) := by
  have hmapnodup :
      ((fixedHistogramFiberWords w_A f).map
        (fun v => v.map (FiniteLetterCode.encode : A × B → ℕ))).Nodup :=
    (fixedHistogramLiftWords_nodup w_A f).map (by
      intro u v huv
      exact List.map_injective_iff.mpr FiniteLetterCode.injective huv)
  have htoFinset :
      (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode)
        (Finset.univ.toList.map
          (fun ab : A × B => (FiniteLetterCode.encode ab, f ab)))).toFinset =
        ((fixedHistogramFiberWords w_A f).map
          (fun v => v.map (FiniteLetterCode.encode : A × B → ℕ))).toFinset := by
    ext w'
    simp only [List.mem_toFinset, mem_numericFiber, List.mem_map,
      mem_fixedHistogramLiftWords]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
  rw [← List.toFinset_card_of_nodup (numericFiber_nodup f w_A), htoFinset,
    List.toFinset_card_of_nodup hmapnodup, List.length_map,
    length_fixedHistogramFiberWords w_A f hmargin]

/-- Decoding the code of a word returns the list of its letter codes. -/
theorem decodeFiniteWordCode_finiteWordCode
    {C : Type*} [Fintype C] [DecidableEq C] [FiniteLetterCode C] (v : List C) :
    decodeFiniteWordCode (finiteWordCode v) = v.map FiniteLetterCode.encode := by
  unfold decodeFiniteWordCode finiteWordCode
  rw [bitsToNat_bits, Encodable.encodek]
  rfl

omit [Fintype A] in
/-- The number of occurrences of a letter in the projection is the sum of the counts over the
fibre letters. -/
theorem count_map_fst_eq_sum (v : List (A × B)) (a : A) :
    (v.map Prod.fst).count a = ∑ b, v.count (a, b) := by
  induction v with
  | nil => simp
  | cons ab v ih =>
      obtain ⟨a', b'⟩ := ab
      rw [List.map_cons, List.count_cons, ih]
      have : ∑ b, (List.count (a, b) ((a', b') :: v)) =
          (∑ b, v.count (a, b)) + (if a' = a then 1 else 0) := by
        have hstep : ∀ b : B, List.count (a, b) ((a', b') :: v) =
            v.count (a, b) + (if (a', b') = (a, b) then 1 else 0) := by
          intro b
          rw [List.count_cons]
          congr 1
          by_cases h : (a', b') = (a, b) <;> simp [h]
        rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_add_distrib]
        congr 1
        by_cases h : a' = a
        · subst h
          simp [Prod.ext_iff]
        · rw [Finset.sum_eq_zero, if_neg h]
          intro b _
          rw [if_neg (by simp [Prod.ext_iff, h])]
      rw [this]
      congr 1
      by_cases h : a' = a <;> simp [h]

/-- A word of prescribed histogram is recovered from its projection by a program of length at
most the logarithm of the fibre size. -/
theorem fixedHistogramLiftDecoder_recovers :
  ∀ {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (f : A × B → ℕ) (w : List (A × B)),
    (∀ i, w.count i = f i) →
    ∃ p, p.length ≤
        Nat.size (∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b))) ∧
      produces fixedHistogramLiftDecoder p
        (pairCode (finiteWordCode (w.map Prod.fst)) (histogramContext f))
        (finiteWordCode w) := by
  intro A B _ _ _ _ f w hw
  set w_A := w.map Prod.fst with hw_A
  have hmargin : ∀ a, w_A.count a = ∑ b, f (a, b) := by
    intro a
    rw [hw_A, count_map_fst_eq_sum]
    exact Finset.sum_congr rfl fun b _ => hw (a, b)
  set table := Finset.univ.toList.map (fun ab : A × B => (FiniteLetterCode.encode ab, f ab))
    with htable
  set L := (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode) table).map
    numericWordCode with hL
  have hmem : finiteWordCode w ∈ L := by
    rw [hL, List.mem_map]
    exact ⟨w.map FiniteLetterCode.encode,
      (mem_numericFiber f w_A _).mpr ⟨w, ⟨hw, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hlenL : L.length = ∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b)) := by
    rw [hL, List.length_map, length_numericFiber f w_A hmargin]
  set width := Nat.size (∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b))) with hwidth
  have hi_lt : i < 2 ^ width := by
    have h1 : i < ∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b)) := by
      rw [← hlenL]; exact hi
    exact lt_trans h1 (Nat.lt_size_self _)
  refine ⟨fixedWidthNatCode i width, le_of_eq (fixedWidthNatCode_length hi_lt), ?_⟩
  change finiteWordCode w ∈ fixedHistogramLiftDecoder (fixedWidthNatCode i width,
    pairCode (finiteWordCode w_A) (histogramContext f))
  unfold fixedHistogramLiftDecoder
  rw [Part.mem_some_iff]
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeFiniteWordCode_finiteWordCode,
    decodeHistogramTable_histogramContext, decodeFixedWidthNatCode_encode]
  rw [← htable, ← hL, List.getD_eq_getElem _ _ hi, hget]

end Lift

/-- The fiber complexity bound. -/
theorem condK_fixedHistogramWord_given_projection_le
    (U : Map) (hU : isOptimalConditional U) :
  ∃ c : ℕ, ∀ {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  (f : A × B → ℕ) (w : List (A × B)),
  (∀ i, w.count i = f i) →
  condK U (finiteWordCode w)
    (pairCode (finiteWordCode (w.map Prod.fst)) (histogramContext f)) ≤
    (Nat.size (∏ w_a ∈ univ, Nat.multinomial univ (fun b => f (w_a, b))) : ENat) + c := by
  obtain ⟨c, hc⟩ := hU.2 fixedHistogramLiftDecoder fixedHistogramLiftDecoder_isDecompressor
  refine ⟨c, ?_⟩
  intro A B _ _ _ _ f w hw
  obtain ⟨p, hp, hprod⟩ := fixedHistogramLiftDecoder_recovers f w hw
  let y := pairCode (finiteWordCode (w.map Prod.fst)) (histogramContext f)
  have hD : condK fixedHistogramLiftDecoder (finiteWordCode w) y ≤ (p.length : ENat) :=
    sInf_le ⟨p, hprod, rfl⟩
  calc
    condK U (finiteWordCode w) y ≤
        condK fixedHistogramLiftDecoder (finiteWordCode w) y + (c : ENat) := hc _ _
    _ ≤ (p.length : ENat) + (c : ENat) := by gcongr
    _ ≤
        (Nat.size (∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b))) : ENat) +
          (c : ENat) := by
      exact add_le_add_left (ENat.coe_le_coe.mpr hp) _

/-! ### Maximality -/

/-- A type class of size at least `2^{k+1}` contains a word of conditional complexity greater
than `k`. -/
theorem exists_fixedHistogramWord_condK_gt
    (U : Map) (y : BitString) (m : ℕ) (f : Fin m → ℕ) (k : ℕ)
    (hcard : 2 ^ (k + 1) ≤ Nat.multinomial univ f) :
  ∃ w : List (Fin m), (∀ i, w.count i = f i) ∧
    (k : ENat) < condK U (finiteWordCode w) y := by
  let words := (fixedHistogramWords f).map finiteWordCode
  have hnodup : words.Nodup :=
    (fixedHistogramWords_nodup f).map finiteWordCode_injective
  have hcardS : words.toFinset.card = Nat.multinomial univ f := by
    rw [List.toFinset_card_of_nodup hnodup, List.length_map,
      length_fixedHistogramWords]
  obtain ⟨code, hcode, hK⟩ :=
    exists_mem_condK_gt_of_card_le U y k words.toFinset (by simpa [hcardS])
  rw [List.mem_toFinset, List.mem_map] at hcode
  obtain ⟨w, hw, rfl⟩ := hcode
  exact ⟨w, (mem_fixedHistogramWords f w).mp hw |>.2, hK⟩

end

end Kolmogorov
