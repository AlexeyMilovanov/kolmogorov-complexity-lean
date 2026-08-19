import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.List.Count
import Mathlib.Data.List.FinRange

/-!
# Fixed-histogram words over a finite alphabet

Chapter 11 of SUV uses fixed-frequency families over alphabets larger than
`Bool` (Exercise 316 needs the four-letter alphabet obtained from a *pair* of
bit strings).  `KolmogorovMathlib.CommonInformation.FixedFrequency` supplies the
binary case; this file supplies the exact finite combinatorics of the
multi-letter case.

* `allWords m n` enumerates every word of length `n` over the alphabet
  `Fin m`; it is duplicate free and its membership predicate is exact.
* `fixedHistogramWords f` (for `f : Fin m → ℕ`) enumerates the words whose
  letter histogram is exactly `f`.  It is presented as a filter of `allWords`,
  and `mem_fixedHistogramWords`, `fixedHistogramWords_nodup` and
  `length_fixedHistogramWords` give its membership predicate, duplicate
  freeness, and cardinality `Nat.multinomial Finset.univ f`.
* `multinomial_univ_four_choose` expresses the four-letter multinomial
  coefficient as the product of three binomial coefficients.

The counting statement `length_fixedHistogramWords` is the multinomial
generalization of `length_fixedWeightFiltered`; the auxiliary
`Nat.multinomial` recurrences `sum_mul_multinomial_update_pred` and
`multinomial_eq_sum_update_pred` are proved here as well.
-/

namespace Kolmogorov

open Finset Nat

/-! ### Two recurrences for multinomial coefficients -/

/-- Decrementing `f` at a single point `i` scales the multinomial coefficient by
`f i / (∑ j, f j)`; in division-free form. -/
theorem sum_mul_multinomial_update_pred {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ℕ) {i : α} (hi : i ∈ s) (hpos : 0 < f i) :
    (∑ j ∈ s, f j) * Nat.multinomial s (Function.update f i (f i - 1)) =
      f i * Nat.multinomial s f := by
  set g := Function.update f i (f i - 1) with hg
  have hgi : g i = f i - 1 := by rw [hg, Function.update_self]
  have hgj : ∀ j ∈ s.erase i, g j = f j := by
    intro j hj
    rw [hg, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hfsum : f i + ∑ x ∈ s.erase i, f x = ∑ j ∈ s, f j := Finset.add_sum_erase s f hi
  have hfprod : (f i)! * ∏ x ∈ s.erase i, (f x)! = ∏ j ∈ s, (f j)! :=
    Finset.mul_prod_erase s (fun j => (f j)!) hi
  have hgsum0 : g i + ∑ x ∈ s.erase i, g x = ∑ j ∈ s, g j := Finset.add_sum_erase s g hi
  have hgprod0 : (g i)! * ∏ x ∈ s.erase i, (g x)! = ∏ j ∈ s, (g j)! :=
    Finset.mul_prod_erase s (fun j => (g j)!) hi
  rw [Finset.sum_congr rfl hgj, hgi] at hgsum0
  rw [Finset.prod_congr rfl (fun j hj => by rw [hgj j hj])] at hgprod0
  have hgsum0' : f i - 1 + ∑ x ∈ s.erase i, f x = ∑ j ∈ s, g j := hgsum0
  have hgsum : ∑ j ∈ s, g j + 1 = ∑ j ∈ s, f j := by omega
  have hgprod : f i * ∏ j ∈ s, (g j)! = ∏ j ∈ s, (f j)! := by
    rw [← hgprod0, hgi, ← hfprod, ← mul_assoc]
    congr 1
    conv_rhs => rw [show f i = (f i - 1) + 1 by omega]
    rw [Nat.factorial_succ]
    congr 1
    omega
  have hposP : 0 < f i * ∏ j ∈ s, (g j)! :=
    Nat.mul_pos hpos (Finset.prod_pos fun j _ => Nat.factorial_pos _)
  refine Nat.eq_of_mul_eq_mul_right hposP ?_
  have hspecg := Nat.multinomial_spec s g
  have hspecf := Nat.multinomial_spec s f
  calc (∑ j ∈ s, f j) * Nat.multinomial s g * (f i * ∏ j ∈ s, (g j)!)
      = f i * ((∑ j ∈ s, f j) * ((∏ j ∈ s, (g j)!) * Nat.multinomial s g)) := by ring
    _ = f i * ((∑ j ∈ s, g j + 1) * (∑ j ∈ s, g j)!) := by rw [hspecg, hgsum]
    _ = f i * (∑ j ∈ s, f j)! := by rw [← Nat.factorial_succ, hgsum]
    _ = f i * ((∏ j ∈ s, (f j)!) * Nat.multinomial s f) := by rw [hspecf]
    _ = f i * Nat.multinomial s f * (f i * ∏ j ∈ s, (g j)!) := by rw [← hgprod]; ring

/-- Pascal's rule for multinomial coefficients: a nonempty histogram splits
according to its last letter. -/
theorem multinomial_eq_sum_update_pred {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ℕ) (h : 0 < ∑ j ∈ s, f j) :
    Nat.multinomial s f =
      ∑ i ∈ s, (if f i = 0 then 0 else Nat.multinomial s (Function.update f i (f i - 1))) := by
  refine Nat.eq_of_mul_eq_mul_left h ?_
  rw [Finset.mul_sum]
  calc (∑ j ∈ s, f j) * Nat.multinomial s f
      = ∑ i ∈ s, f i * Nat.multinomial s f := by rw [← Finset.sum_mul]
    _ = ∑ i ∈ s, (∑ j ∈ s, f j) *
          (if f i = 0 then 0 else Nat.multinomial s (Function.update f i (f i - 1))) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        by_cases h0 : f i = 0
        · simp [h0]
        · rw [if_neg h0, sum_mul_multinomial_update_pred s f hi (Nat.pos_of_ne_zero h0)]

/-- The four-letter multinomial coefficient as a product of binomial
coefficients. -/
theorem multinomial_univ_four_choose (a b c d : ℕ) :
    Nat.multinomial (Finset.univ : Finset (Fin 4)) ![a, b, c, d] =
      (a + b + c + d).choose a *
        (b + c + d).choose b *
        (c + d).choose c := by
  have huniv : (Finset.univ : Finset (Fin 4)) =
      insert 0 (insert 1 (insert 2 ({3} : Finset (Fin 4)))) := by decide
  rw [huniv]
  rw [Nat.multinomial_insert (by decide), Nat.multinomial_insert (by decide),
    Nat.multinomial_insert (by decide), Nat.multinomial_singleton]
  simp only [Finset.sum_insert (by decide : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
    Finset.sum_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))),
    Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring_nf

/-! ### Enumeration of all words of a given length -/

/-- `allWords m n` lists every word of length `n` over the alphabet `Fin m`. -/
def allWords (m : ℕ) : ℕ → List (List (Fin m))
  | 0 => [[]]
  | n + 1 => (List.finRange m).flatMap (fun i => (allWords m n).map (i :: ·))

/-- Membership in `allWords m n` is exactly "length `n`". -/
theorem mem_allWords (m n : ℕ) (w : List (Fin m)) : w ∈ allWords m n ↔ w.length = n := by
  induction n generalizing w with
  | zero => cases w <;> simp [allWords]
  | succ n ih =>
    cases w with
    | nil => simp [allWords]
    | cons a w => simp [allWords, ih]

/-- `allWords m n` is duplicate free. -/
theorem allWords_nodup (m n : ℕ) : (allWords m n).Nodup := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
    rw [allWords]
    refine List.nodup_flatMap.mpr ⟨fun i _ => ih.map (fun a b h => by injection h), ?_⟩
    refine (List.nodup_finRange m).imp ?_
    intro i j hij w hw hw'
    rw [List.mem_map] at hw hw'
    obtain ⟨a, -, rfl⟩ := hw
    obtain ⟨b, -, hb⟩ := hw'
    have : j = i := by injection hb
    exact hij this.symm

/-! ### Words with a prescribed letter histogram -/

/-- The length of a word is the total of its letter counts. -/
theorem length_eq_sum_count {m : ℕ} (w : List (Fin m)) : w.length = ∑ i, w.count i := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.length_cons, List.count_cons, ih]
    rw [Finset.sum_add_distrib]
    simp

theorem count_cons_fin {m : ℕ} (j i : Fin m) (w : List (Fin m)) :
    List.count j (i :: w) = List.count j w + (if i = j then 1 else 0) := by
  simp [List.count_cons]

theorem sum_update_pred {m : ℕ} (f : Fin m → ℕ) (i : Fin m) (h : 0 < f i) :
    ∑ j, Function.update f i (f i - 1) j = (∑ j, f j) - 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have := Finset.add_sum_erase (univ : Finset (Fin m)) f (Finset.mem_univ i)
  omega

/-- A recursive enumeration of the words with letter histogram `f`, where the
first argument is the (necessarily equal) total length `∑ i, f i`. -/
def histWords {m : ℕ} : ℕ → (Fin m → ℕ) → List (List (Fin m))
  | 0, _ => [[]]
  | n + 1, f => (List.finRange m).flatMap (fun i =>
      if f i = 0 then [] else (histWords n (Function.update f i (f i - 1))).map (i :: ·))

theorem mem_histWords {m : ℕ} : ∀ (n : ℕ) (f : Fin m → ℕ), (∑ i, f i) = n →
    ∀ w : List (Fin m), w ∈ histWords n f ↔ ∀ i, w.count i = f i := by
  intro n
  induction n with
  | zero =>
    intro f hf w
    have hf0 : ∀ i, f i = 0 := fun i => Finset.sum_eq_zero_iff.mp hf i (Finset.mem_univ i)
    simp only [histWords, List.mem_singleton]
    constructor
    · rintro rfl i; simp [hf0 i]
    · intro h
      have hlen : w.length = 0 := by
        rw [length_eq_sum_count]
        simp [h, hf0]
      exact List.eq_nil_of_length_eq_zero hlen
  | succ n ih =>
    intro f hf w
    rw [histWords]
    simp only [List.mem_flatMap, List.mem_finRange, true_and]
    constructor
    · rintro ⟨i, hi⟩
      by_cases h0 : f i = 0
      · simp [h0] at hi
      · rw [if_neg h0, List.mem_map] at hi
        obtain ⟨w', hw', rfl⟩ := hi
        have hpos : 0 < f i := Nat.pos_of_ne_zero h0
        have hsum : (∑ j, Function.update f i (f i - 1) j) = n := by
          rw [sum_update_pred f i hpos, hf]
          omega
        have hc := (ih _ hsum w').mp hw'
        intro j
        rw [count_cons_fin, hc j]
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self, if_pos rfl]
          omega
        · rw [Function.update_of_ne hji, if_neg (Ne.symm hji)]
          omega
    · intro hcount
      have hlen : w.length = n + 1 := by
        rw [length_eq_sum_count]
        simp only [hcount]
        exact hf
      obtain ⟨i, w', rfl⟩ : ∃ i w', w = i :: w' := by
        cases w with
        | nil => simp at hlen
        | cons a w' => exact ⟨a, w', rfl⟩
      have h0 : f i ≠ 0 := by
        have hci := hcount i
        rw [count_cons_fin, if_pos rfl] at hci
        omega
      have hpos : 0 < f i := Nat.pos_of_ne_zero h0
      refine ⟨i, ?_⟩
      rw [if_neg h0, List.mem_map]
      refine ⟨w', ?_, rfl⟩
      have hsum : (∑ j, Function.update f i (f i - 1) j) = n := by
        rw [sum_update_pred f i hpos, hf]
        omega
      refine (ih _ hsum w').mpr ?_
      intro j
      have hj := hcount j
      rw [count_cons_fin] at hj
      by_cases hji : j = i
      · subst hji
        rw [Function.update_self, if_pos rfl] at *
        omega
      · rw [Function.update_of_ne hji, if_neg (Ne.symm hji)] at *
        omega

theorem histWords_nodup {m : ℕ} : ∀ (n : ℕ) (f : Fin m → ℕ), (histWords n f).Nodup := by
  intro n
  induction n with
  | zero => intro f; simp [histWords]
  | succ n ih =>
    intro f
    rw [histWords]
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro i _
      by_cases h0 : f i = 0
      · simp [h0]
      · rw [if_neg h0]
        exact (ih _).map (fun a b h => by cases h; rfl)
    · refine (List.nodup_finRange m).imp ?_
      intro i j hij w hw hw'
      simp only at hw hw'
      by_cases h0 : f i = 0
      · simp [h0] at hw
      by_cases h1 : f j = 0
      · simp [h1] at hw'
      rw [if_neg h0, List.mem_map] at hw
      rw [if_neg h1, List.mem_map] at hw'
      obtain ⟨a, -, rfl⟩ := hw
      obtain ⟨b, -, hb⟩ := hw'
      have : j = i := by injection hb
      exact hij this.symm

theorem length_histWords_succ {m : ℕ} (n : ℕ) (f : Fin m → ℕ) :
    (histWords (n + 1) f).length =
      ∑ i, (if f i = 0 then 0 else (histWords n (Function.update f i (f i - 1))).length) := by
  rw [histWords, List.length_flatMap, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left ?_
  intro i _
  by_cases h0 : f i = 0 <;> simp [h0]

/-- The recursive enumeration has exactly `Nat.multinomial univ f` entries. -/
theorem length_histWords {m : ℕ} : ∀ (n : ℕ) (f : Fin m → ℕ), (∑ i, f i) = n →
    (histWords n f).length = Nat.multinomial univ f := by
  intro n
  induction n with
  | zero =>
    intro f hf
    have hf0 : ∀ i, f i = 0 := fun i => Finset.sum_eq_zero_iff.mp hf i (Finset.mem_univ i)
    simp [histWords, Nat.multinomial, hf0]
  | succ n ih =>
    intro f hf
    rw [length_histWords_succ,
      multinomial_eq_sum_update_pred (univ : Finset (Fin m)) f (by rw [hf]; omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : f i = 0
    · simp [h0]
    · have hpos : 0 < f i := Nat.pos_of_ne_zero h0
      rw [if_neg h0, if_neg h0]
      exact ih _ (by rw [sum_update_pred f i hpos, hf]; omega)

/-! ### The fixed-histogram family -/

/-- `fixedHistogramWords f` lists the words over `Fin m` whose letter histogram
is exactly `f`.  It is presented as a filter of the enumeration `allWords` of
all words of the appropriate length. -/
def fixedHistogramWords {m : ℕ} (f : Fin m → ℕ) : List (List (Fin m)) :=
  (allWords m (∑ i, f i)).filter (fun w => decide (∀ i, w.count i = f i))

/-- Membership in `fixedHistogramWords f` is exactly "the histogram is `f`"
(equivalently, the length is `∑ i, f i` and every letter count matches). -/
theorem mem_fixedHistogramWords {m : ℕ} (f : Fin m → ℕ) (w : List (Fin m)) :
    w ∈ fixedHistogramWords f ↔
      w.length = ∑ i, f i ∧ ∀ i, w.count i = f i := by
  unfold fixedHistogramWords
  rw [List.mem_filter, mem_allWords]
  simp

theorem fixedHistogramWords_nodup {m : ℕ} (f : Fin m → ℕ) :
    (fixedHistogramWords f).Nodup :=
  (allWords_nodup m (∑ i, f i)).filter _

/-- **Multinomial enumeration.** There are exactly `Nat.multinomial univ f`
words with letter histogram `f`. -/
theorem length_fixedHistogramWords {m : ℕ} (f : Fin m → ℕ) :
    (fixedHistogramWords f).length = Nat.multinomial Finset.univ f := by
  have hmem : ∀ w : List (Fin m),
      w ∈ fixedHistogramWords f ↔ w ∈ histWords (∑ i, f i) f := by
    intro w
    rw [mem_fixedHistogramWords, mem_histWords (∑ i, f i) f rfl]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [length_eq_sum_count]
    exact Finset.sum_congr rfl fun i _ => h i
  have htoFinset : (fixedHistogramWords f).toFinset = (histWords (∑ i, f i) f).toFinset := by
    ext w
    simpa using hmem w
  rw [← List.toFinset_card_of_nodup (fixedHistogramWords_nodup f), htoFinset,
    List.toFinset_card_of_nodup (histWords_nodup _ f), length_histWords _ f rfl]

/-- The four-letter case, in binomial form: the number of words over a
four-letter alphabet with letter counts `a, b, c, d`. -/
theorem length_fixedHistogramWords_four (a b c d : ℕ) :
    (fixedHistogramWords ![a, b, c, d]).length =
      (a + b + c + d).choose a *
        (b + c + d).choose b *
        (c + d).choose c := by
  rw [length_fixedHistogramWords, multinomial_univ_four_choose]

end Kolmogorov
