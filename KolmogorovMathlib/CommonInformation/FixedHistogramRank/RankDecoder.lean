import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaCount
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.FixedFrequency
import KolmogorovMathlib.CommonInformation.FixedHistogram
import KolmogorovMathlib.CommonInformation.TypeBounds
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionComputable
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Words of a fixed histogram, and their codes

The infrastructure for rank-decoding a word over a finite alphabet.  `FiniteLetterCode` is an
injective numeric code for the letters (a class, so the structure of the alphabet does not
leak into the statements), `finiteWordCode` extends it injectively to words, and
`histogramContext` is the context string carrying a histogram `f : A → ℕ`.

`allWordsFrom` lists the words of a given length over an explicit alphabet, without repetition;
`numericFixedHistogramWords` is the executable numeric counterpart of a fixed-histogram family,
`decodeHistogramTable` reads the histogram back from the context, and `numericWordCode` is the
code format the decoders use.  The self-delimiting parameter block (`natsCode`, `peelStep`,
`peelIter`, `taggedFrom`, with `length_natsCode`) is what a decoder reads before the rank.

The decoders themselves are in `PlainAndFibreDecoders` and `FibreEnumeration`.
-/



namespace Kolmogorov

open Finset Nat

noncomputable section

/-- An injective natural-number code for letters of a finite alphabet.  It is a
typeclass so the structural product instance is selected at each use site,
rather than freezing an opaque finite-type encoding inside a polymorphic
definition. -/
class FiniteLetterCode (A : Type*) where
  encode : A → ℕ
  injective : Function.Injective encode

/-- Every finite type has a (noncanonical) injective letter code. -/
noncomputable instance (priority := 10) finiteLetterCodeOfFintype
    {A : Type*} [Fintype A] [DecidableEq A] : FiniteLetterCode A where
  encode := @Encodable.encode A (Fintype.toEncodable A)
  injective := @Encodable.encode_injective A (Fintype.toEncodable A)

/-- The varying executable alphabet `Fin m` uses its numeric value as code. -/
instance (priority := 100) finiteLetterCodeFin (m : ℕ) : FiniteLetterCode (Fin m) where
  encode i := i.val
  injective := fun _ _ h => Fin.ext h

/-- The binary alphabets used by the conditional-independence chain have an
explicit executable code. -/
instance (priority := 100) finiteLetterCodeBool : FiniteLetterCode Bool where
  encode b := if b then 1 else 0
  injective := by decide

/-- Product letters use `Nat.pair`, exposing their two coordinate codes to the
uniform numeric lift decoder. -/
instance (priority := 100) finiteLetterCodeProd
    {A B : Type*} [FiniteLetterCode A] [FiniteLetterCode B] :
    FiniteLetterCode (A × B) where
  encode ab := Nat.pair (FiniteLetterCode.encode ab.1) (FiniteLetterCode.encode ab.2)
  injective := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    rw [Nat.pair_eq_pair] at h
    exact Prod.ext (FiniteLetterCode.injective h.1) (FiniteLetterCode.injective h.2)

/-- The letter code of a pair is the Cantor pairing of the codes of its components. -/
@[simp]
theorem finiteLetterCode_encode_prod
    {A B : Type*} [FiniteLetterCode A] [FiniteLetterCode B] (a : A) (b : B) :
    FiniteLetterCode.encode (a, b) =
      Nat.pair (FiniteLetterCode.encode a) (FiniteLetterCode.encode b) :=
  rfl

/-! ### Finite alphabet word encoding -/

/-- Encoding a word over a finite type into a `BitString`.

The intermediate list of natural-number letter codes makes the format uniform
across alphabets.  In particular, for a product alphabet the standard product
`Encodable` instance makes each letter code a `Nat.pair`, which is exactly
the structure used by the projection/lift decoder below. -/
def finiteWordCode {A : Type*} [Fintype A] [DecidableEq A] [FiniteLetterCode A]
    (w : List A) : BitString :=
  Nat.bits (Encodable.encode (w.map FiniteLetterCode.encode))

/-- Distinct words over a finite alphabet have distinct codes. -/
theorem finiteWordCode_injective
    {A : Type*} [Fintype A] [DecidableEq A] [FiniteLetterCode A] :
    Function.Injective (@finiteWordCode A _ _ _) := by
  intro w w' h
  have hcodes : w.map FiniteLetterCode.encode = w'.map FiniteLetterCode.encode :=
    Encodable.encode_injective (natBits_injective h)
  exact (List.map_injective_iff.mpr FiniteLetterCode.injective) hcodes

/-- The context string for a fixed histogram `f : A → ℕ`. -/
def histogramContext
    {A : Type*} [Fintype A] [DecidableEq A] [FiniteLetterCode A]
    (f : A → ℕ) : BitString :=
  Nat.bits
    (Encodable.encode (Finset.univ.toList.map fun a => (FiniteLetterCode.encode a, f a)))

/-! ### Rank decoder for fixed-histogram words -/

/-- All words of a fixed length over an explicitly listed alphabet. -/
def allWordsFrom {A : Type*} (symbols : List A) : ℕ → List (List A)
  | 0 => [[]]
  | n + 1 => symbols.flatMap (fun a => (allWordsFrom symbols n).map (a :: ·))

/-- A word occurs in `allWordsFrom symbols n` exactly when it has length `n` and all
its letters come from `symbols`. -/
theorem mem_allWordsFrom {A : Type*} {symbols : List A} {n : ℕ} {w : List A} :
    w ∈ allWordsFrom symbols n ↔ w.length = n ∧ ∀ a ∈ w, a ∈ symbols := by
  induction n generalizing w with
  | zero => cases w <;> simp [allWordsFrom]
  | succ n ih =>
      cases w with
      | nil => simp [allWordsFrom]
      | cons a w =>
          simp [allWordsFrom, ih, _root_.and_left_comm, _root_.and_comm]

/-- If the alphabet list has no repetitions, neither has the list of words of a
given length over it. -/
theorem allWordsFrom_nodup {A : Type*} (symbols : List A) (hs : symbols.Nodup) (n : ℕ) :
    (allWordsFrom symbols n).Nodup := by
  induction n with
  | zero => simp [allWordsFrom]
  | succ n ih =>
      rw [allWordsFrom]
      refine List.nodup_flatMap.mpr ⟨fun a _ => ih.map (fun _ _ h => by injection h), ?_⟩
      refine hs.imp ?_
      intro a b hab w ha hb
      rw [List.mem_map] at ha hb
      obtain ⟨u, -, rfl⟩ := ha
      obtain ⟨v, -, hv⟩ := hb
      exact hab (List.cons.inj hv).1.symm

/-- Decode the numeric histogram table carried by `histogramContext`. -/
def decodeHistogramTable (y : BitString) : List (ℕ × ℕ) :=
  (Encodable.decode (bitsToNat y)).getD []

/-- The executable numeric counterpart of a fixed-histogram family. -/
def numericFixedHistogramWords (table : List (ℕ × ℕ)) : List (List ℕ) :=
  (allWordsFrom (table.map Prod.fst) (table.map Prod.snd).sum).filter fun w =>
    decide (∀ e ∈ table, w.count e.1 = e.2)

/-- The word-code format used by the numeric decoders. -/
def numericWordCode (w : List ℕ) : BitString := Nat.bits (Encodable.encode w)

/-- Fixed-width rank decoder for the numeric histogram table in the context. -/
def fixedHistogramRankDecoder : Map := fun pr =>
  Part.some
    (((numericFixedHistogramWords (decodeHistogramTable pr.2)).map numericWordCode).getD
      (decodeFixedWidthNatCode pr.1) [])

/-- The word enumeration over an explicit numeric alphabet is primitive
recursive in the alphabet and the length. -/
theorem allWordsFromNat_primrec :
    Primrec (fun p : List ℕ × ℕ => allWordsFrom p.1 p.2) := by
  have key : Primrec (fun p : List ℕ × ℕ =>
      Nat.rec (motive := fun _ => List (List ℕ)) [([] : List ℕ)]
        (fun _ IH => (p.1.map (fun a => IH.map (a :: ·))).flatten) p.2) := by
    refine Primrec.nat_rec' (α := List ℕ × ℕ) (β := List (List ℕ))
      (h := fun p q => (p.1.map (fun a => q.2.map (a :: ·))).flatten)
      Primrec.snd (Primrec.const [([] : List ℕ)]) ?_
    have inner : Primrec (fun r : ((List ℕ × ℕ) × (ℕ × List (List ℕ))) × ℕ =>
        (r.1.2.2).map (r.2 :: ·)) :=
      Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
    exact (Primrec.list_flatten.comp
      (Primrec.list_map (Primrec.fst.comp Primrec.fst) inner.to₂)).to₂
  refine key.of_eq ?_
  rintro ⟨symbols, n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [allWordsFrom, List.flatMap] at *
      simp [ih]

/-- Counting occurrences of a natural number in a list of naturals is
primitive recursive in both arguments. -/
theorem natListCount_primrec {α : Type*} [Primcodable α]
    {f : α → List ℕ} {g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).count (g a)) := by
  have := list_countP_primrec (α := α) (β := ℕ) (f := f)
    (p := fun a b => b == g a) hf
    (Primrec.beq.comp Primrec.snd (hg.comp Primrec.fst))
  simpa [List.count] using this

/-- The histogram-matching test used by `numericFixedHistogramWords`. -/
theorem histogramMatch_primrec :
    Primrec (fun p : List (ℕ × ℕ) × List ℕ =>
      decide (∀ e ∈ p.1, p.2.count e.1 = e.2)) := by
  have key : Primrec (fun p : List (ℕ × ℕ) × List ℕ =>
      p.1.foldr (fun e acc => (p.2.count e.1 == e.2) && acc) true) := by
    refine Primrec.list_foldr (α := List (ℕ × ℕ) × List ℕ) (β := ℕ × ℕ) (σ := Bool)
      (h := fun p q => (p.2.count q.1.1 == q.1.2) && q.2)
      Primrec.fst (Primrec.const true) ?_
    have hcount : Primrec (fun r : (List (ℕ × ℕ) × List ℕ) × ((ℕ × ℕ) × Bool) =>
        r.1.2.count r.2.1.1) :=
      natListCount_primrec (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    exact (Primrec.and.comp
      (Primrec.beq.comp hcount (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  refine key.of_eq ?_
  rintro ⟨table, w⟩
  induction table with
  | nil => rfl
  | cons e t ih =>
      have ih' : List.foldr (fun e acc => (List.count e.1 w == e.2) && acc) true t
          = decide (∀ e ∈ t, List.count e.1 w = e.2) := ih
      simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp, ih']
      by_cases h : List.count e.1 w = e.2 <;> simp [h]

/-- Enumerating the numeric words with a prescribed histogram is primitive recursive
in the histogram table. -/
theorem numericFixedHistogramWords_primrec :
    Primrec numericFixedHistogramWords := by
  unfold numericFixedHistogramWords
  refine list_filter_primrec ?_ ?_
  · exact allWordsFromNat_primrec.comp
      (Primrec.pair (Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂)
        (primrec_listSum.comp
          (Primrec.list_map Primrec.id (Primrec.snd.comp Primrec.snd).to₂)))
  · exact histogramMatch_primrec.to₂

/-- Decoding a histogram table from its context string is primitive recursive. -/
theorem decodeHistogramTable_primrec : Primrec decodeHistogramTable := by
  unfold decodeHistogramTable
  exact Primrec.option_getD.comp (Primrec.decode.comp bitsToNat_primrec)
    (Primrec.const ([] : List (ℕ × ℕ)))

/-- The word-code format of the numeric decoders is primitive recursive. -/
theorem numericWordCode_primrec : Primrec numericWordCode := by
  unfold numericWordCode
  exact primrec_natBits.comp Primrec.encode

/-- The rank decoder for fixed-histogram words is a decompressor: it is a computable
partial map of program and context. -/
theorem fixedHistogramRankDecoder_isDecompressor :
    isDecompressor fixedHistogramRankDecoder := by
  have hlist : Primrec (fun pr : BitString × BitString =>
      (numericFixedHistogramWords (decodeHistogramTable pr.2)).map numericWordCode) :=
    Primrec.list_map
      (numericFixedHistogramWords_primrec.comp
        (decodeHistogramTable_primrec.comp Primrec.snd))
      (numericWordCode_primrec.comp Primrec.snd).to₂
  have hidx : Primrec (fun pr : BitString × BitString =>
      decodeFixedWidthNatCode pr.1) :=
    decodeFixedWidthNatCode_primrec.comp Primrec.fst
  have hg : Computable (fun pr : BitString × BitString =>
      ((numericFixedHistogramWords (decodeHistogramTable pr.2)).map
        numericWordCode).getD (decodeFixedWidthNatCode pr.1) []) :=
    ((Primrec.list_getD ([] : BitString)).comp hlist hidx).to_comp
  exact hg.partrec

/-! #### Recovering the histogram table and the rank

The context `histogramContext f` round-trips through `decodeHistogramTable`, so
the decoder rebuilds the numeric table, hence the numeric image of the
fixed-histogram family, whose cardinality is the multinomial coefficient. -/

/-- The histogram context round-trips through the numeric table decoder. -/
theorem decodeHistogramTable_histogramContext
    {A : Type*} [Fintype A] [DecidableEq A] [FiniteLetterCode A] (f : A → ℕ) :
    decodeHistogramTable (histogramContext f) =
      Finset.univ.toList.map (fun a => (FiniteLetterCode.encode a, f a)) := by
  unfold decodeHistogramTable histogramContext
  rw [bitsToNat_bits, Encodable.encodek]
  rfl

section FinAlphabet

variable {m : ℕ}

/-- The first components of the table of an `m`-letter histogram are the letters
`0, …, m - 1`. -/
theorem finTable_fst (f : Fin m → ℕ) :
    ((Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i))).map Prod.fst) =
      Finset.univ.toList.map (Fin.val : Fin m → ℕ) := by
  rw [List.map_map]
  rfl

/-- The second components of the table of an `m`-letter histogram sum to the total
count. -/
theorem finTable_snd_sum (f : Fin m → ℕ) :
    (((Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i))).map Prod.snd).sum) =
      ∑ i, f i := by
  rw [List.map_map]
  exact Finset.sum_map_toList (Finset.univ : Finset (Fin m)) f

/-- The letters of `Fin m`, listed by their values, have no repetitions. -/
theorem finSymbols_nodup :
    ((Finset.univ : Finset (Fin m)).toList.map (Fin.val : Fin m → ℕ)).Nodup :=
  (Finset.nodup_toList _).map Fin.val_injective

/-- The numeric fixed-histogram family is the numeric image of the family over
`Fin m`. -/
theorem mem_numericFin (f : Fin m → ℕ) (w' : List ℕ) :
    w' ∈ numericFixedHistogramWords
        (Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i))) ↔
      ∃ w : List (Fin m), (∀ i, w.count i = f i) ∧ w' = w.map Fin.val := by
  rw [numericFixedHistogramWords, List.mem_filter, mem_allWordsFrom, finTable_fst,
    finTable_snd_sum]
  simp only [decide_eq_true_eq, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hlen, hmem⟩, hcount⟩
    have hlt : ∀ x ∈ w', x < m := by
      intro x hx
      obtain ⟨i, rfl⟩ := hmem x hx
      exact i.isLt
    refine ⟨w'.attach.map (fun x => (⟨x.1, hlt x.1 x.2⟩ : Fin m)), ?_, ?_⟩
    · intro i
      have hmapval : (w'.attach.map (fun x => (⟨x.1, hlt x.1 x.2⟩ : Fin m))).map Fin.val = w' := by
        rw [List.map_map]
        simp
      have hc := List.count_map_of_injective
        (w'.attach.map (fun x => (⟨x.1, hlt x.1 x.2⟩ : Fin m))) Fin.val Fin.val_injective i
      rw [hmapval] at hc
      rw [← hc]
      exact hcount ((i : ℕ), f i) ⟨i, rfl⟩
    · rw [List.map_map]
      simp
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.length_map, length_eq_sum_count w]
      exact Finset.sum_congr rfl fun i _ => hw i
    · intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨i, rfl⟩
    · rintro e ⟨i, rfl⟩
      rw [List.count_map_of_injective w Fin.val Fin.val_injective i]
      exact hw i

/-- The numeric enumeration of the words with a prescribed `Fin m` histogram has no
repetitions. -/
theorem numericFin_nodup (f : Fin m → ℕ) :
    (numericFixedHistogramWords
      (Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i)))).Nodup := by
  rw [numericFixedHistogramWords, finTable_fst]
  exact (allWordsFrom_nodup _ finSymbols_nodup _).filter _

/-- The numeric fixed-histogram family also has exactly `M(f)` entries. -/
theorem length_numericFin (f : Fin m → ℕ) :
    (numericFixedHistogramWords
      (Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i)))).length =
      Nat.multinomial univ f := by
  have hmapnodup : ((fixedHistogramWords f).map (fun w => w.map Fin.val)).Nodup :=
    (fixedHistogramWords_nodup f).map (by
      intro u v huv
      exact List.map_injective_iff.mpr Fin.val_injective huv)
  have htoFinset :
      (numericFixedHistogramWords
        (Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i)))).toFinset =
        ((fixedHistogramWords f).map (fun w => w.map Fin.val)).toFinset := by
    ext w'
    simp only [List.mem_toFinset, mem_numericFin, List.mem_map, mem_fixedHistogramWords]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, ⟨?_, hw⟩, rfl⟩
      rw [length_eq_sum_count w]
      exact Finset.sum_congr rfl fun i _ => hw i
    · rintro ⟨w, ⟨-, hw⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [← List.toFinset_card_of_nodup (numericFin_nodup f), htoFinset,
    List.toFinset_card_of_nodup hmapnodup, List.length_map, length_fixedHistogramWords]

/-- Decoding the context string of an `m`-letter histogram returns its table. -/
theorem decodeHistogramTable_histogramContext_fin (f : Fin m → ℕ) :
    decodeHistogramTable (histogramContext f) =
      Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i)) :=
  decodeHistogramTable_histogramContext f

/-- The code of a word over `Fin m` is the numeric code of the word of its letter
values. -/
theorem finiteWordCode_eq_numericWordCode (w : List (Fin m)) :
    finiteWordCode w = numericWordCode (w.map Fin.val) := rfl

end FinAlphabet

/-- Given the histogram as context, a word with that histogram is recovered from a
program of at most `Nat.size (multinomial f)` bits, its rank in the enumeration. -/
theorem fixedHistogramRankDecoder_recovers :
  ∀ m (f : Fin m → ℕ) w, (∀ i, w.count i = f i) →
  ∃ p, p.length ≤ Nat.size (Nat.multinomial univ f) ∧
    produces fixedHistogramRankDecoder p (histogramContext f) (finiteWordCode w) := by
  intro m f w hw
  set table := Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i)) with htable
  set L := (numericFixedHistogramWords table).map numericWordCode with hL
  have hmem : finiteWordCode w ∈ L := by
    rw [hL, List.mem_map]
    exact ⟨w.map Fin.val, (mem_numericFin f _).mpr ⟨w, hw, rfl⟩,
      (finiteWordCode_eq_numericWordCode w).symm⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hlenL : L.length = Nat.multinomial univ f := by
    rw [hL, List.length_map, length_numericFin]
  set width := Nat.size (Nat.multinomial univ f) with hwidth
  have hi_lt : i < 2 ^ width := by
    have h1 : i < Nat.multinomial univ f := by rw [← hlenL]; exact hi
    exact lt_trans h1 (Nat.lt_size_self _)
  refine ⟨fixedWidthNatCode i width, le_of_eq (fixedWidthNatCode_length hi_lt), ?_⟩
  change finiteWordCode w ∈ fixedHistogramRankDecoder (fixedWidthNatCode i width,
    histogramContext f)
  unfold fixedHistogramRankDecoder
  rw [Part.mem_some_iff]
  simp only [decodeHistogramTable_histogramContext_fin, decodeFixedWidthNatCode_encode]
  rw [← htable, ← hL, List.getD_eq_getElem _ _ hi, hget]

/-- The conditional rank bound: describing a fixed-histogram word given its context. -/
theorem condK_fixedHistogramWord_le_size_multinomial
    (U : Map) (hU : isOptimalConditional U) :
  ∃ c : ℕ, ∀ m (f : Fin m → ℕ) w, (∀ i, w.count i = f i) →
  condK U (finiteWordCode w) (histogramContext f) ≤
    (Nat.size (Nat.multinomial univ f) : ENat) + c := by
  obtain ⟨c, hc⟩ := hU.2 fixedHistogramRankDecoder fixedHistogramRankDecoder_isDecompressor
  refine ⟨c, fun m f w hw => ?_⟩
  obtain ⟨p, hp, hprod⟩ := fixedHistogramRankDecoder_recovers m f w hw
  have hD : condK fixedHistogramRankDecoder (finiteWordCode w) (histogramContext f) ≤
      (p.length : ENat) :=
    sInf_le ⟨p, hprod, rfl⟩
  calc
    condK U (finiteWordCode w) (histogramContext f) ≤
        condK fixedHistogramRankDecoder (finiteWordCode w) (histogramContext f) +
          (c : ENat) := hc _ _
    _ ≤ (p.length : ENat) + (c : ENat) := by gcongr
    _ ≤ (Nat.size (Nat.multinomial univ f) : ENat) + (c : ENat) := by
      exact add_le_add_left (ENat.coe_le_coe.mpr hp) _

/-- The numeric fixed-histogram family built from a duplicate-free complete
listing `L` of the alphabet is the numeric image of the fixed-histogram
family. -/
theorem mem_numericTable
    {C : Type*} [BEq C] [LawfulBEq C] [FiniteLetterCode C]
    (f : C → ℕ) (L : List C) (hnd : L.Nodup) (hcomp : ∀ c, c ∈ L) (w' : List ℕ) :
    w' ∈ numericFixedHistogramWords (L.map (fun c => (FiniteLetterCode.encode c, f c))) ↔
      ∃ v : List C, (∀ c, v.count c = f c) ∧ w' = v.map FiniteLetterCode.encode := by
  classical
  letI : Fintype C := ⟨L.toFinset, fun c => List.mem_toFinset.mpr (hcomp c)⟩
  have hlen_gen : ∀ u : List C, u.length = ∑ c, u.count c := by
    intro u
    induction u with
    | nil => simp
    | cons c u ih =>
        simp only [List.length_cons, List.count_cons, ih]
        rw [Finset.sum_add_distrib]
        simp
  have hfst : ((L.map (fun c : C => (FiniteLetterCode.encode c, f c))).map Prod.fst) =
      L.map (FiniteLetterCode.encode : C → ℕ) := by
    rw [List.map_map]; rfl
  have htoFinset : L.toFinset = (univ : Finset C) :=
    Finset.eq_univ_iff_forall.mpr (fun c => List.mem_toFinset.mpr (hcomp c))
  have hsnd : (((L.map (fun c : C => (FiniteLetterCode.encode c, f c))).map Prod.snd).sum) =
      ∑ c, f c := by
    rw [List.map_map]
    have : (L.map f).sum = ∑ c ∈ L.toFinset, f c := (List.sum_toFinset (fun c => f c) hnd).symm
    rw [show (List.map (Prod.snd ∘ fun c : C => (FiniteLetterCode.encode c, f c)) L)
        = L.map f from rfl, this, htoFinset]
  rw [numericFixedHistogramWords, List.mem_filter, mem_allWordsFrom, hfst, hsnd]
  simp only [decide_eq_true_eq, List.mem_map]
  constructor
  · rintro ⟨⟨hlen, hmem⟩, hcount⟩
    choose g hgL hg using hmem
    have hmapval :
        (w'.attach.map (fun x => g x.1 x.2)).map FiniteLetterCode.encode = w' := by
      rw [List.map_map]
      have hcomp' : (fun x : {x // x ∈ w'} => FiniteLetterCode.encode (g x.1 x.2)) =
          fun x : {x // x ∈ w'} => x.1 := by
        funext x; exact hg x.1 x.2
      rw [Function.comp_def, hcomp']
      simp
    refine ⟨w'.attach.map (fun x => g x.1 x.2), ?_, hmapval.symm⟩
    intro c
    have hc := List.count_map_of_injective
      (w'.attach.map (fun x => g x.1 x.2)) FiniteLetterCode.encode
      FiniteLetterCode.injective c
    rw [hmapval] at hc
    rw [← hc]
    exact hcount (FiniteLetterCode.encode c, f c) ⟨c, hcomp c, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.length_map, hlen_gen v]
      exact Finset.sum_congr rfl fun c _ => hv c
    · intro x hx
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨c, hcomp c, rfl⟩
    · rintro e ⟨c, -, rfl⟩
      rw [List.count_map_of_injective v FiniteLetterCode.encode FiniteLetterCode.injective c]
      exact hv c

/-- The numeric enumeration built from a repetition-free letter list has no
repetitions. -/
theorem numericTable_nodup
    {C : Type*} [FiniteLetterCode C] (f : C → ℕ) (L : List C) (hnd : L.Nodup) :
    (numericFixedHistogramWords
      (L.map (fun c => (FiniteLetterCode.encode c, f c)))).Nodup := by
  have hfst : ((L.map (fun c : C => (FiniteLetterCode.encode c, f c))).map Prod.fst) =
      L.map (FiniteLetterCode.encode : C → ℕ) := by
    rw [List.map_map]; rfl
  rw [numericFixedHistogramWords, hfst]
  exact (allWordsFrom_nodup _ (hnd.map FiniteLetterCode.injective) _).filter _

/-- The numeric enumeration of the words with histogram `f` over a complete
repetition-free letter list has `Nat.multinomial univ f` entries. -/
theorem length_numericTableFin {m : ℕ} (f : Fin m → ℕ) (L : List (Fin m))
    (hnd : L.Nodup) (hcomp : ∀ i, i ∈ L) :
    (numericFixedHistogramWords
      (L.map (fun i : Fin m => (FiniteLetterCode.encode i, f i)))).length =
      Nat.multinomial univ f := by
  have hmapnodup : ((fixedHistogramWords f).map (fun w => w.map Fin.val)).Nodup :=
    (fixedHistogramWords_nodup f).map (by
      intro u v huv
      exact List.map_injective_iff.mpr Fin.val_injective huv)
  have htoFinset :
      (numericFixedHistogramWords
        (L.map (fun i : Fin m => (FiniteLetterCode.encode i, f i)))).toFinset =
        ((fixedHistogramWords f).map (fun w => w.map Fin.val)).toFinset := by
    ext w'
    simp only [List.mem_toFinset, mem_numericTable f L hnd hcomp, List.mem_map,
      mem_fixedHistogramWords]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, ⟨?_, hw⟩, rfl⟩
      rw [length_eq_sum_count w]
      exact Finset.sum_congr rfl fun i _ => hw i
    · rintro ⟨w, ⟨-, hw⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [← List.toFinset_card_of_nodup (numericTable_nodup f L hnd), htoFinset,
    List.toFinset_card_of_nodup hmapnodup, List.length_map, length_fixedHistogramWords]

/-! ### A self-delimiting parameter block for the plain decoder -/

/-- Prepend a self-delimiting binary code of each entry of `xs` to `z`. -/
def natsCode : List ℕ → BitString → BitString
  | [], z => z
  | x :: xs, z => pairCode (Nat.bits x) (natsCode xs z)

/-- The self-delimiting code of a list of numbers has length `∑ (2 * size x + 1)`
plus the length of the trailing string. -/
theorem length_natsCode (xs : List ℕ) (z : BitString) :
    (natsCode xs z).length =
      (xs.map (fun x => 2 * Nat.size x + 1)).sum + z.length := by
  induction xs with
  | nil => simp [natsCode]
  | cons x xs ih =>
      rw [natsCode, length_pairCode, ih, Nat.size_eq_bits_len]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- One step of the parameter-block parser: read the next number and tag it
with the running letter index. -/
def peelStep (st : (List (ℕ × ℕ) × BitString) × ℕ) : (List (ℕ × ℕ) × BitString) × ℕ :=
  ((st.1.1 ++ [(st.2, bitsToNat (decodeFirst st.1.2))], decodeSecond st.1.2), st.2 + 1)

/-- Iterate the parameter-block parser. -/
def peelIter (k : ℕ) (st : (List (ℕ × ℕ) × BitString) × ℕ) :
    (List (ℕ × ℕ) × BitString) × ℕ :=
  Nat.rec st (fun _ s => peelStep s) k

/-- One more iteration of the parameter-block parser is the loop applied after one
parsing step. -/
theorem peelIter_succ (k : ℕ) (st : (List (ℕ × ℕ) × BitString) × ℕ) :
    peelIter (k + 1) st = peelIter k (peelStep st) := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
      change peelStep (peelIter (k + 1) st) = _
      rw [ih]
      rfl

/-- The list of tagged entries produced by parsing, starting from index `i`. -/
def taggedFrom : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | i, x :: xs => (i, x) :: taggedFrom (i + 1) xs

end
end Kolmogorov
