import Mathlib.Data.Nat.Choose.Multinomial
import KolmogorovMathlib.CommonInformation.FixedFrequency
import KolmogorovMathlib.CommonInformation.FixedHistogram
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaCount
import KolmogorovMathlib.CommonInformation.TypeBounds

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
`Encodable` instance makes each letter code a `Nat.pair`, which is exactly the
structure used by the projection/lift decoder below. -/
def finiteWordCode {A : Type*} [Fintype A] [DecidableEq A] [FiniteLetterCode A]
    (w : List A) : BitString :=
  Nat.bits (Encodable.encode (w.map FiniteLetterCode.encode))

theorem finiteWordCode_injective
    {A : Type*} [Fintype A] [DecidableEq A] [FiniteLetterCode A] :
    Function.Injective (@finiteWordCode A _ _ _) := by
  intro w w' h
  have hcodes : w.map FiniteLetterCode.encode = w'.map FiniteLetterCode.encode :=
    Encodable.encode_injective (natBitsInjective h)
  exact (List.map_injective_iff.mpr FiniteLetterCode.injective) hcodes

/-- The context string for a fixed histogram `f : A → ℕ`. -/
def histogramContext
    {A : Type*} [Fintype A] [DecidableEq A] [FiniteLetterCode A]
    (f : A → ℕ) : BitString :=
  Nat.bits
    (Encodable.encode (Finset.univ.toList.map fun a => (FiniteLetterCode.encode a, f a)))

/-! ### Rank decoder for fixed-histogram words -/

/-- All words of a fixed length over an explicitly listed alphabet. -/
def allWordsFrom (symbols : List A) : ℕ → List (List A)
  | 0 => [[]]
  | n + 1 => symbols.flatMap (fun a => (allWordsFrom symbols n).map (a :: ·))

theorem mem_allWordsFrom {symbols : List A} {n : ℕ} {w : List A} :
    w ∈ allWordsFrom symbols n ↔ w.length = n ∧ ∀ a ∈ w, a ∈ symbols := by
  induction n generalizing w with
  | zero => cases w <;> simp [allWordsFrom]
  | succ n ih =>
      cases w with
      | nil => simp [allWordsFrom]
      | cons a w =>
          simp [allWordsFrom, ih, _root_.and_left_comm, _root_.and_comm]

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

/-- Summing a list of naturals is primitive recursive. -/
theorem natListSum_primrec : Primrec (fun l : List ℕ => l.sum) := by
  have key : Primrec (fun l : List ℕ => l.foldr (fun a b => a + b) 0) :=
    Primrec.list_foldr (α := List ℕ) (β := ℕ) (σ := ℕ)
      (h := fun _ q => q.1 + q.2) Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  refine key.of_eq ?_
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem numericFixedHistogramWords_primrec :
    Primrec numericFixedHistogramWords := by
  unfold numericFixedHistogramWords
  refine list_filter_primrec ?_ ?_
  · exact allWordsFromNat_primrec.comp
      (Primrec.pair (Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂)
        (natListSum_primrec.comp
          (Primrec.list_map Primrec.id (Primrec.snd.comp Primrec.snd).to₂)))
  · exact histogramMatch_primrec.to₂

theorem decodeHistogramTable_primrec : Primrec decodeHistogramTable := by
  unfold decodeHistogramTable
  exact Primrec.option_getD.comp (Primrec.decode.comp bitsToNat_primrec)
    (Primrec.const ([] : List (ℕ × ℕ)))

theorem numericWordCode_primrec : Primrec numericWordCode := by
  unfold numericWordCode
  exact primrecNatBits.comp Primrec.encode

theorem decodeFixedWidthNatCode_primrec : Primrec decodeFixedWidthNatCode := by
  unfold decodeFixedWidthNatCode
  exact bitsToNat_primrec.comp Primrec.list_reverse

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

theorem finTable_fst (f : Fin m → ℕ) :
    ((Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i))).map Prod.fst) =
      Finset.univ.toList.map (Fin.val : Fin m → ℕ) := by
  rw [List.map_map]
  rfl

theorem finTable_snd_sum (f : Fin m → ℕ) :
    (((Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i))).map Prod.snd).sum) =
      ∑ i, f i := by
  rw [List.map_map]
  exact Finset.sum_map_toList (Finset.univ : Finset (Fin m)) f

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

theorem decodeHistogramTable_histogramContext_fin (f : Fin m → ℕ) :
    decodeHistogramTable (histogramContext f) =
      Finset.univ.toList.map (fun i : Fin m => ((i : ℕ), f i)) :=
  decodeHistogramTable_histogramContext f

theorem finiteWordCode_eq_numericWordCode (w : List (Fin m)) :
    finiteWordCode w = numericWordCode (w.map Fin.val) := rfl

end FinAlphabet

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

theorem numericTable_nodup
    {C : Type*} [FiniteLetterCode C] (f : C → ℕ) (L : List C) (hnd : L.Nodup) :
    (numericFixedHistogramWords
      (L.map (fun c => (FiniteLetterCode.encode c, f c)))).Nodup := by
  have hfst : ((L.map (fun c : C => (FiniteLetterCode.encode c, f c))).map Prod.fst) =
      L.map (FiniteLetterCode.encode : C → ℕ) := by
    rw [List.map_map]; rfl
  rw [numericFixedHistogramWords, hfst]
  exact (allWordsFrom_nodup _ (hnd.map FiniteLetterCode.injective) _).filter _

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

theorem peelIter_natsCode :
    ∀ (xs : List ℕ) (pre : List (ℕ × ℕ)) (i : ℕ) (z : BitString),
      peelIter xs.length ((pre, natsCode xs z), i) =
        ((pre ++ taggedFrom i xs, z), i + xs.length) := by
  intro xs
  induction xs with
  | nil => intro pre i z; simp [peelIter, natsCode, taggedFrom]
  | cons x xs ih =>
      intro pre i z
      rw [List.length_cons, peelIter_succ]
      have hstep : peelStep ((pre, natsCode (x :: xs) z), i) =
          ((pre ++ [(i, x)], natsCode xs z), i + 1) := by
        rw [peelStep, natsCode]
        simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
      rw [hstep, ih]
      simp only [taggedFrom, List.append_assoc, List.singleton_append]
      congr 1
      omega

theorem length_taggedFrom : ∀ (i : ℕ) (xs : List ℕ), (taggedFrom i xs).length = xs.length := by
  intro i xs
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [taggedFrom, ih]

theorem getElem_taggedFrom : ∀ (i : ℕ) (xs : List ℕ) (j : ℕ) (h : j < (taggedFrom i xs).length),
    (taggedFrom i xs)[j] = (i + j, xs[j]'(by rwa [length_taggedFrom] at h)) := by
  intro i xs
  induction xs generalizing i with
  | nil => intro j h; simp [taggedFrom] at h
  | cons x xs ih =>
      intro j h
      cases j with
      | zero => simp [taggedFrom]
      | succ j =>
          have h' : j < (taggedFrom (i + 1) xs).length := by
            rw [length_taggedFrom] at h ⊢
            simpa using h
          simp only [taggedFrom, List.getElem_cons_succ]
          rw [ih (i + 1) j h']
          congr 1
          omega

theorem taggedFrom_ofFn (m : ℕ) (f : Fin m → ℕ) :
    taggedFrom 0 (List.ofFn f) =
      (List.finRange m).map (fun i : Fin m => (FiniteLetterCode.encode i, f i)) := by
  apply List.ext_getElem
  · simp [length_taggedFrom]
  · intro j h1 h2
    rw [getElem_taggedFrom]
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_ofFn, Prod.mk.injEq,
      Nat.zero_add]
    exact ⟨rfl, rfl⟩

/-- The plain decoder: its program is a self-delimiting binary code of the
alphabet size, then of each histogram entry, then a fixed-width rank. -/
def fixedHistogramPlainDecoder : Map := fun pr =>
  Part.some
    (((numericFixedHistogramWords
        (peelIter (bitsToNat (decodeFirst pr.1))
          ((([] : List (ℕ × ℕ)), decodeSecond pr.1), 0)).1.1).map numericWordCode).getD
      (decodeFixedWidthNatCode
        (peelIter (bitsToNat (decodeFirst pr.1))
          ((([] : List (ℕ × ℕ)), decodeSecond pr.1), 0)).1.2) [])

theorem peelStep_primrec : Primrec peelStep := by
  unfold peelStep
  refine Primrec.pair (Primrec.pair ?_ ?_) ?_
  · exact Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp
        (Primrec.pair Primrec.snd
          (bitsToNat_primrec.comp
            (CodedFiniteDistribution.decodeFirst_primrec.comp
              (Primrec.snd.comp Primrec.fst))))
        (Primrec.const []))
  · exact CodedFiniteDistribution.decodeSecond_primrec.comp (Primrec.snd.comp Primrec.fst)
  · exact Primrec.succ.comp Primrec.snd

theorem fixedHistogramPlainDecoder_isDecompressor :
    isDecompressor fixedHistogramPlainDecoder := by
  have hm : Primrec (fun pr : BitString × BitString => bitsToNat (decodeFirst pr.1)) :=
    bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst)
  have hst : Primrec (fun pr : BitString × BitString =>
      peelIter (bitsToNat (decodeFirst pr.1))
        ((([] : List (ℕ × ℕ)), decodeSecond pr.1), 0)) := by
    refine Primrec.nat_rec' (α := BitString × BitString)
      (β := (List (ℕ × ℕ) × BitString) × ℕ)
      (h := fun _ q => peelStep q.2) hm
      (Primrec.pair (Primrec.pair (Primrec.const ([] : List (ℕ × ℕ)))
        (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst)) (Primrec.const 0))
      ?_
    exact (peelStep_primrec.comp (Primrec.snd.comp Primrec.snd)).to₂
  have hlist : Primrec (fun pr : BitString × BitString =>
      (numericFixedHistogramWords
        (peelIter (bitsToNat (decodeFirst pr.1))
          ((([] : List (ℕ × ℕ)), decodeSecond pr.1), 0)).1.1).map numericWordCode) :=
    Primrec.list_map
      (numericFixedHistogramWords_primrec.comp (Primrec.fst.comp (Primrec.fst.comp hst)))
      (numericWordCode_primrec.comp Primrec.snd).to₂
  have hidx : Primrec (fun pr : BitString × BitString =>
      decodeFixedWidthNatCode
        (peelIter (bitsToNat (decodeFirst pr.1))
          ((([] : List (ℕ × ℕ)), decodeSecond pr.1), 0)).1.2) :=
    decodeFixedWidthNatCode_primrec.comp (Primrec.snd.comp (Primrec.fst.comp hst))
  exact (((Primrec.list_getD ([] : BitString)).comp hlist hidx).to_comp).partrec

theorem fixedHistogramPlainDecoder_recovers :
  ∀ m (f : Fin m → ℕ) w, (∀ i, w.count i = f i) →
  ∃ p, p.length ≤ Nat.size (Nat.multinomial univ f) + 2 * Nat.size m +
      2 * (∑ i, Nat.size (f i)) + m + 1 ∧
    produces fixedHistogramPlainDecoder p [] (finiteWordCode w) := by
  intro m f w hw
  set table := (List.finRange m).map (fun i : Fin m => (FiniteLetterCode.encode i, f i))
    with htable
  set L := (numericFixedHistogramWords table).map numericWordCode with hL
  have hnd : (List.finRange m).Nodup := List.nodup_finRange m
  have hcomp : ∀ i : Fin m, i ∈ List.finRange m := fun i => List.mem_finRange i
  have hmem : finiteWordCode w ∈ L := by
    rw [hL, List.mem_map]
    exact ⟨w.map FiniteLetterCode.encode,
      (mem_numericTable f _ hnd hcomp _).mpr ⟨w, hw, rfl⟩, rfl⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hlenL : L.length = Nat.multinomial univ f := by
    rw [hL, List.length_map, length_numericTableFin f _ hnd hcomp]
  set width := Nat.size (Nat.multinomial univ f) with hwidth
  have hi_lt : i < 2 ^ width := by
    have h1 : i < Nat.multinomial univ f := by rw [← hlenL]; exact hi
    exact lt_trans h1 (Nat.lt_size_self _)
  set p : BitString :=
    pairCode (Nat.bits m) (natsCode (List.ofFn f) (fixedWidthNatCode i width)) with hp
  have hsum : ((List.ofFn f).map (fun x => 2 * Nat.size x + 1)).sum =
      2 * (∑ i, Nat.size (f i)) + m := by
    rw [show (List.ofFn f).map (fun x => 2 * Nat.size x + 1)
        = List.ofFn (fun i => 2 * Nat.size (f i) + 1) from by
      rw [List.map_ofFn]; rfl, List.sum_ofFn]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hplen : p.length =
      Nat.size (Nat.multinomial univ f) + 2 * Nat.size m +
        2 * (∑ i, Nat.size (f i)) + m + 1 := by
    rw [hp, length_pairCode, length_natsCode, hsum, fixedWidthNatCode_length hi_lt,
      Nat.size_eq_bits_len, hwidth]
    omega
  refine ⟨p, le_of_eq hplen, ?_⟩
  have hpeel : peelIter m
      ((([] : List (ℕ × ℕ)), natsCode (List.ofFn f) (fixedWidthNatCode i width)), 0) =
      ((table, fixedWidthNatCode i width), m) := by
    have h := peelIter_natsCode (List.ofFn f) [] 0 (fixedWidthNatCode i width)
    rw [List.length_ofFn] at h
    rw [h, taggedFrom_ofFn, ← htable]
    simp
  change finiteWordCode w ∈ fixedHistogramPlainDecoder (p, [])
  unfold fixedHistogramPlainDecoder
  rw [Part.mem_some_iff]
  simp only [hp, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits, hpeel,
    decodeFixedWidthNatCode_encode]
  rw [← hL, List.getD_eq_getElem _ _ hi, hget]

/-- The plain rank bound: describing a fixed-histogram word from nothing.

The linear `m` term pays for the separators in a self-delimiting list of all
`m` histogram entries.  It cannot in general be replaced by `O(log m)`: even
histograms with three singleton letters range over `Θ(m³)` distinct words. -/
theorem plainK_fixedHistogramWord_le_size_multinomial_add_params
    (U : Map) (hU : isOptimalConditional U) :
  ∃ c : ℕ, ∀ m (f : Fin m → ℕ) w, (∀ i, w.count i = f i) →
  plainK U (finiteWordCode w) ≤
    (Nat.size (Nat.multinomial univ f) : ENat) +
    2 * Nat.size m + 2 * (∑ i, Nat.size (f i)) + m + c := by
  obtain ⟨c, hc⟩ := hU.2 fixedHistogramPlainDecoder fixedHistogramPlainDecoder_isDecompressor
  refine ⟨c + 1, fun m f w hw => ?_⟩
  obtain ⟨p, hplen, hprod⟩ := fixedHistogramPlainDecoder_recovers m f w hw
  have hD : plainK fixedHistogramPlainDecoder (finiteWordCode w) ≤ (p.length : ENat) :=
    sInf_le ⟨p, hprod, rfl⟩
  calc
    plainK U (finiteWordCode w) ≤
        plainK fixedHistogramPlainDecoder (finiteWordCode w) + (c : ENat) :=
      hc (finiteWordCode w) []
    _ ≤ (p.length : ENat) + (c : ENat) := by gcongr
    _ ≤ ((Nat.size (Nat.multinomial univ f) + 2 * Nat.size m +
          2 * (∑ i, Nat.size (f i)) + m + 1 + c : ℕ) : ENat) := by
        exact_mod_cast Nat.add_le_add_right hplen c
    _ = (Nat.size (Nat.multinomial univ f) : ENat) +
          2 * Nat.size m + 2 * (∑ i, Nat.size (f i)) + m + (c + 1 : ℕ) := by
        push_cast
        ring

/-! ### Fiber decoder for projected words -/

theorem length_eq_sum_count_fintype
    {A : Type*} [Fintype A] [DecidableEq A] (w : List A) :
    w.length = ∑ a, w.count a := by
  induction w with
  | nil => simp
  | cons a w ih =>
      simp only [List.length_cons, List.count_cons, ih]
      rw [Finset.sum_add_distrib]
      simp

/-- The words with a prescribed image under a coordinate projection. -/
noncomputable def fixedHistogramFiberWords
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (w_A : List A) (f : A × B → ℕ) : List (List (A × B)) :=
  (allWordsFrom (Finset.univ.toList) (∑ ab, f ab)).filter fun w =>
    decide ((∀ ab, w.count ab = f ab) ∧ w.map Prod.fst = w_A)

theorem fixedHistogramLiftWords_nodup
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (w_A : List A) (f : A × B → ℕ) : (fixedHistogramFiberWords w_A f).Nodup := by
  exact (allWordsFrom_nodup _ (Finset.nodup_toList _) _).filter _

theorem mem_fixedHistogramLiftWords
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (w_A : List A) (f : A × B → ℕ) (w : List (A × B)) :
  w ∈ fixedHistogramFiberWords w_A f ↔
    (∀ i, w.count i = f i) ∧ w.map Prod.fst = w_A := by
  rw [fixedHistogramFiberWords, List.mem_filter, mem_allWordsFrom]
  simp only [decide_eq_true_eq, Finset.mem_toList, Finset.mem_univ, implies_true,
    and_true]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hlen : ∀ u : List (A × B), u.length = ∑ ab, u.count ab := by
    intro u
    induction u with
    | nil => simp
    | cons ab u ih =>
        simp only [List.length_cons, List.count_cons, ih]
        rw [Finset.sum_add_distrib]
        simp
  rw [hlen w]
  exact Finset.sum_congr rfl fun ab _ => h.1 ab

/-! #### The recursive fibre enumeration

The filtered presentation `fixedHistogramFiberWords` is convenient for the
decoder but not for counting.  We introduce the equivalent recursive
enumeration `fiberLiftWords`, which peels off the letters of the projection one
at a time, and count that instead. -/

/-- Decrementing a histogram at one point lowers its total by one. -/
theorem sum_update_pred_univ {B : Type*} [Fintype B] [DecidableEq B]
    (g : B → ℕ) (b : B) (h : 0 < g b) :
    ∑ b', Function.update g b (g b - 1) b' = (∑ b', g b') - 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ b), Finset.sdiff_singleton_eq_erase]
  have := Finset.add_sum_erase (univ : Finset B) g (Finset.mem_univ b)
  omega

/-- Updating a joint histogram at `(a, b)` leaves the other rows untouched. -/
theorem update_prod_row_ne {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A × B → ℕ) (a a' : A) (b : B) (v : ℕ) (h : a' ≠ a) :
    (fun b' => Function.update f (a, b) v (a', b')) = fun b' => f (a', b') := by
  funext b'
  refine Function.update_of_ne ?_ _ _
  simp only [ne_eq, Prod.mk.injEq, not_and]
  intro hc
  exact absurd hc h

/-- Updating a joint histogram at `(a, b)` updates the `a`-row at `b`. -/
theorem update_prod_row_self {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A × B → ℕ) (a : A) (b : B) (v : ℕ) :
    (fun b' => Function.update f (a, b) v (a, b')) =
      Function.update (fun b' => f (a, b')) b v := by
  funext b'
  by_cases hb : b' = b
  · subst hb; simp
  · rw [Function.update_of_ne (by simp only [ne_eq, Prod.mk.injEq, not_and]; intro _; exact hb),
      Function.update_of_ne hb]

/-- A recursive enumeration of the lifts of `w_A` to the joint histogram `f`. -/
def fiberLiftWords {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B] :
    List A → (A × B → ℕ) → List (List (A × B))
  | [], _ => [[]]
  | a :: rest, f =>
      (Finset.univ : Finset B).toList.flatMap (fun b =>
        if f (a, b) = 0 then []
        else (fiberLiftWords rest (Function.update f (a, b) (f (a, b) - 1))).map ((a, b) :: ·))

/-- The marginal hypothesis is preserved by removing one letter. -/
theorem marginal_update {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    {a : A} {rest : List A} {f : A × B → ℕ} {b : B}
    (hmargin : ∀ a', (a :: rest).count a' = ∑ b', f (a', b'))
    (hpos : 0 < f (a, b)) :
    ∀ a', rest.count a' = ∑ b', Function.update f (a, b) (f (a, b) - 1) (a', b') := by
  intro a'
  by_cases ha : a' = a
  · subst ha
    rw [update_prod_row_self, sum_update_pred_univ (fun b' => f (a', b')) b hpos]
    have h := hmargin a'
    rw [List.count_cons_self] at h
    omega
  · rw [update_prod_row_ne f a a' b _ ha]
    have h := hmargin a'
    rw [List.count_cons_of_ne (Ne.symm ha)] at h
    omega

theorem mem_fiberLiftWords {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B] :
    ∀ (w_A : List A) (f : A × B → ℕ), (∀ a, w_A.count a = ∑ b, f (a, b)) →
      ∀ w : List (A × B),
        w ∈ fiberLiftWords w_A f ↔ ((∀ i, w.count i = f i) ∧ w.map Prod.fst = w_A) := by
  intro w_A
  induction w_A with
  | nil =>
      intro f hmargin w
      have hf0 : ∀ i : A × B, f i = 0 := by
        rintro ⟨a, b⟩
        have h := (hmargin a).symm
        simp only [List.count_nil] at h
        exact Finset.sum_eq_zero_iff.mp h b (Finset.mem_univ b)
      simp only [fiberLiftWords, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨fun i => by simp [hf0 i], by simp⟩
      · rintro ⟨-, hmap⟩
        exact List.eq_nil_of_length_eq_zero (by simpa using congrArg List.length hmap)
  | cons a rest ih =>
      intro f hmargin w
      rw [fiberLiftWords]
      simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨b, hb⟩
        by_cases h0 : f (a, b) = 0
        · simp [h0] at hb
        rw [if_neg h0, List.mem_map] at hb
        obtain ⟨w', hw', rfl⟩ := hb
        have hpos : 0 < f (a, b) := Nat.pos_of_ne_zero h0
        obtain ⟨hc', hm'⟩ := (ih _ (marginal_update hmargin hpos) w').mp hw'
        refine ⟨fun i => ?_, by simp [hm']⟩
        by_cases hi : i = (a, b)
        · subst hi
          rw [List.count_cons_self, hc' (a, b), Function.update_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm hi), hc' i, Function.update_of_ne hi]
      · rintro ⟨hc, hm⟩
        obtain ⟨ab, w', rfl⟩ : ∃ ab w', w = ab :: w' := by
          cases w with
          | nil => simp at hm
          | cons ab w' => exact ⟨ab, w', rfl⟩
        obtain ⟨a', b⟩ := ab
        rw [List.map_cons] at hm
        obtain ⟨ha', hm'⟩ := List.cons.inj hm
        simp only at ha'
        subst ha'
        have hpos : 0 < f (a', b) := by
          have h := hc (a', b)
          rw [List.count_cons_self] at h
          omega
        refine ⟨b, ?_⟩
        rw [if_neg (by omega), List.mem_map]
        refine ⟨w', ?_, rfl⟩
        refine (ih _ (marginal_update hmargin hpos) w').mpr ⟨fun i => ?_, hm'⟩
        by_cases hii : i = (a', b)
        · subst hii
          have h := hc (a', b)
          rw [List.count_cons_self] at h
          rw [Function.update_self]
          omega
        · have h := hc i
          rw [List.count_cons_of_ne (Ne.symm hii)] at h
          rw [Function.update_of_ne hii]
          exact h

theorem fiberLiftWords_nodup {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B] :
    ∀ (w_A : List A) (f : A × B → ℕ), (fiberLiftWords w_A f).Nodup := by
  intro w_A
  induction w_A with
  | nil => intro f; simp [fiberLiftWords]
  | cons a rest ih =>
      intro f
      rw [fiberLiftWords]
      refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
      · intro b _
        by_cases h0 : f (a, b) = 0
        · simp [h0]
        · rw [if_neg h0]
          exact (ih _).map (fun x y h => by cases h; rfl)
      · refine (Finset.nodup_toList _).imp ?_
        intro b b' hbb' w hw hw'
        simp only at hw hw'
        by_cases h0 : f (a, b) = 0
        · simp [h0] at hw
        by_cases h1 : f (a, b') = 0
        · simp [h1] at hw'
        rw [if_neg h0, List.mem_map] at hw
        rw [if_neg h1, List.mem_map] at hw'
        obtain ⟨u, -, rfl⟩ := hw
        obtain ⟨v, -, hv⟩ := hw'
        have hab : (a, b') = (a, b) := (List.cons.inj hv).1
        exact hbb' (by simpa [Prod.ext_iff] using hab.symm)

/-- The recursive fibre enumeration has exactly `∏_a M(f(a, ·))` entries. -/
theorem length_fiberLiftWords {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    ∀ (w_A : List A) (f : A × B → ℕ), (∀ a, w_A.count a = ∑ b, f (a, b)) →
      (fiberLiftWords w_A f).length =
        ∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b)) := by
  intro w_A
  induction w_A with
  | nil =>
      intro f hmargin
      have hf0 : ∀ i : A × B, f i = 0 := by
        rintro ⟨a, b⟩
        have h := (hmargin a).symm
        simp only [List.count_nil] at h
        exact Finset.sum_eq_zero_iff.mp h b (Finset.mem_univ b)
      simp [fiberLiftWords, Nat.multinomial, hf0]
  | cons a rest ih =>
      intro f hmargin
      have hposrow : 0 < ∑ b, f (a, b) := by
        have h := hmargin a
        rw [List.count_cons_self] at h
        omega
      have hstep : ∀ b : B,
          (if f (a, b) = 0 then []
            else (fiberLiftWords rest
              (Function.update f (a, b) (f (a, b) - 1))).map ((a, b) :: ·)).length =
            (∏ a' ∈ univ.erase a, Nat.multinomial univ (fun b' => f (a', b'))) *
              (if f (a, b) = 0 then 0
                else Nat.multinomial univ
                  (Function.update (fun b' => f (a, b')) b (f (a, b) - 1))) := by
        intro b
        by_cases h0 : f (a, b) = 0
        · simp [h0]
        · have hpos : 0 < f (a, b) := Nat.pos_of_ne_zero h0
          rw [if_neg h0, if_neg h0]
          simp only [List.length_map]
          rw [ih _ (marginal_update hmargin hpos)]
          rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ a)]
          rw [mul_comm]
          congr 1
          · refine Finset.prod_congr rfl fun a' ha' => ?_
            rw [update_prod_row_ne f a a' b _ (Finset.ne_of_mem_erase ha')]
          · rw [update_prod_row_self]
      rw [fiberLiftWords, List.length_flatMap, Finset.sum_map_toList,
        Finset.sum_congr rfl (fun b _ => hstep b), ← Finset.mul_sum,
        ← multinomial_eq_sum_update_pred univ (fun b' => f (a, b')) hposrow,
        mul_comm,
        Finset.mul_prod_erase univ (fun a' => Nat.multinomial univ (fun b' => f (a', b')))
          (Finset.mem_univ a)]

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

theorem decodeFiniteWordCode_primrec : Primrec decodeFiniteWordCode := by
  unfold decodeFiniteWordCode
  exact Primrec.option_getD.comp (Primrec.decode.comp bitsToNat_primrec)
    (Primrec.const ([] : List ℕ))

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

theorem map_encode_unpair_fst (v : List (A × B)) :
    (v.map FiniteLetterCode.encode).map (fun code : ℕ => code.unpair.1) =
      (v.map Prod.fst).map (FiniteLetterCode.encode : A → ℕ) := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left ?_
  rintro ⟨a, b⟩ -
  simp [finiteLetterCode_encode_prod]

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

theorem numericFiber_nodup (f : A × B → ℕ) (w_A : List A) :
    (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode)
      (Finset.univ.toList.map (fun ab : A × B => (FiniteLetterCode.encode ab, f ab)))).Nodup :=
  (numericGeneral_nodup f).filter _

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

theorem decodeFiniteWordCode_finiteWordCode
    {C : Type*} [Fintype C] [DecidableEq C] [FiniteLetterCode C] (v : List C) :
    decodeFiniteWordCode (finiteWordCode v) = v.map FiniteLetterCode.encode := by
  unfold decodeFiniteWordCode finiteWordCode
  rw [bitsToNat_bits, Encodable.encodek]
  rfl

omit [Fintype A] in
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
