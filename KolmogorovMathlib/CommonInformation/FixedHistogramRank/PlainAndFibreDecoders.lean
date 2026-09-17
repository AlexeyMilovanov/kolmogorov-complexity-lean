import Mathlib.Data.Nat.Choose.Multinomial
import KolmogorovMathlib.CommonInformation.FixedHistogram
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaCount
import KolmogorovMathlib.CommonInformation.FixedFrequency
import KolmogorovMathlib.CommonInformation.TypeBounds
import KolmogorovMathlib.CommonInformation.FixedHistogramRank.RankDecoder

/-!
# Describing a word by its histogram and its rank

`plainK_fixedHistogramWord_le_size_multinomial_add_params`: a word with histogram `f` is
described from nothing by the logarithm of the multinomial coefficient plus the bits of the
parameters.  The witness is `fixedHistogramPlainDecoder`, whose program is a self-delimiting
code of the alphabet size and of the histogram entries followed by the rank; `peelStep`,
`peelIter` and `taggedFrom` parse that parameter block, and
`fixedHistogramPlainDecoder_isDecompressor` and `…_recovers` are its correctness.

The second half prepares the relative version: `fixedHistogramFiberWords` is the set of words
with a prescribed projection and `fiberLiftWords` its recursive enumeration, shown to list it
exactly, without repetition, with `∏_a M(f(a, ·))` entries.  The complexity statement drawn
from it is in `FibreEnumeration`.
-/

namespace Kolmogorov
noncomputable section
open Finset

/-- Parsing as many blocks as there are entries recovers the list of numbers, tagged
with consecutive letters, and leaves the trailing string. -/
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

/-- Tagging a list with consecutive letters preserves its length. -/
theorem length_taggedFrom : ∀ (i : ℕ) (xs : List ℕ), (taggedFrom i xs).length = xs.length := by
  intro i xs
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [taggedFrom, ih]

/-- The `j`-th entry of a list tagged from `i` is the pair of `i + j` and the `j`-th
entry. -/
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

/-- Tagging the value list of an `m`-letter histogram from `0` gives the histogram
table over `Fin m`. -/
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

/-- One step of the parameter-block parser is primitive recursive. -/
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

/-- The self-contained fixed-histogram decoder, which reads the histogram off its
own program, is a decompressor. -/
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

/-- Without context, a word with histogram `f` is recovered from a program of at
most `size (multinomial f) + 2 size m + 2 ∑ size (f i) + m + 1` bits: the
histogram, self-delimited, followed by the rank. -/
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

/-- The length of a word is the sum of the counts of its letters. -/
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

/-- The enumeration of the words over `A × B` with histogram `f` lying over a fixed
first-coordinate word has no repetitions. -/
theorem fixedHistogramLiftWords_nodup
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (w_A : List A) (f : A × B → ℕ) : (fixedHistogramFiberWords w_A f).Nodup := by
  exact (allWordsFrom_nodup _ (Finset.nodup_toList _) _).filter _

/-- A word occurs in that fibre enumeration exactly when it has histogram `f` and
projects to the given first-coordinate word. -/
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

/-- When the histogram is compatible with the first-coordinate word, the recursive
fibre enumeration lists exactly the words with histogram `f` projecting to it. -/
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

/-- The recursive fibre enumeration has no repetitions. -/
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

end
end Kolmogorov
