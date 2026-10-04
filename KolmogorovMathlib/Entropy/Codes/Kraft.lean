/-
Copyright (c) 2024 The KolmogorovMathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The KolmogorovMathlib Contributors
-/
import KolmogorovMathlib.Entropy.Codes.Alphabet
import KolmogorovMathlib.AlgorithmicRandomness.Cantor
import KolmogorovMathlib.Complexity.Incompressibility
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation

/-!
# Prefix codes, the Kraft inequality and the McMillan inequality

SUV Sections 7.1.1 and 7.1.4, pp. 213–217.

A code for a `k`-letter alphabet assigns a binary codeword to each letter and encodes a word by
concatenating the codewords of its letters, with no separators.  This file collects the purely
combinatorial part of Section 7.1: prefix codes are uniquely decodable (Theorem 137), a length
vector is realised by a prefix code exactly when it satisfies the Kraft inequality (the Lemma on
p. 214), and the same inequality already holds for the length vector of a uniquely decodable code
(Theorem 140, the McMillan inequality), so that uniquely decodable codes are no shorter than
prefix codes.

The book's "prefix code" is `Code.IsPrefixFree`: no codeword is a prefix of the codeword of
another letter (which in particular forces distinct letters to get distinct codewords), and no
codeword is empty.  The non-emptiness is a repair adopted by this library and not a condition of
the book, which puts none on the codewords of a code (p. 213) and states the Kraft lemma for
non-negative lengths (p. 214); without it Theorem 137 is false for a one-letter alphabet, and
for two or more letters it is automatic.  Its one visible consequence is in the Kraft lemma
below, whose right-hand side gains the conjunct `0 < n a` that the printed lemma does not have:
for a one-letter alphabet the length vector `n = 0` satisfies `∑ 2^{-n_i} ≤ 1` but is realised
only by the empty codeword.  "Uniquely decodable" is `Code.IsUniquelyDecodable`, the
injectivity of `Code.encodeWord`.
-/

namespace Kolmogorov

open Finset

namespace Code

variable {α β : Type*}

/-! ### Prefix codes are uniquely decodable -/

/-- **Every prefix code is uniquely decodable**: if no codeword is empty and no codeword is a
prefix of another codeword, then distinct words over the alphabet have distinct encodings.  The
non-emptiness of the codewords is part of `Code.IsPrefixFree` — a repair of this library, not a
condition printed in the book — and it is needed: for a one-letter alphabet the code `a ↦ ε` has
no codeword that is a prefix of a *different* codeword, yet all words have the same encoding.
SUV Theorem 137, p. 213. -/
theorem isUniquelyDecodable_of_isPrefixFree {c : Code α} (h : c.IsPrefixFree) :
    c.IsUniquelyDecodable := by
  intro w₁
  induction w₁ with
  | nil =>
    intro w₂ hw
    cases w₂ with
    | nil => rfl
    | cons b w₂ =>
      rw [encodeWord_nil, encodeWord_cons] at hw
      exact absurd (List.append_eq_nil_iff.1 hw.symm).1 (h.ne_nil b)
  | cons a w₁ ih =>
    intro w₂ hw
    cases w₂ with
    | nil =>
      rw [encodeWord_nil, encodeWord_cons] at hw
      exact absurd (List.append_eq_nil_iff.1 hw).1 (h.ne_nil a)
    | cons b w₂ =>
      rw [encodeWord_cons, encodeWord_cons] at hw
      have hab : a = b := by
        by_contra hne
        rcases List.append_eq_append_iff.1 hw with ⟨t, ht, -⟩ | ⟨t, ht, -⟩
        · exact h.2 a b hne ⟨t, ht.symm⟩
        · exact h.2 b a (Ne.symm hne) ⟨t, ht.symm⟩
      subst hab
      rw [ih (List.append_cancel_left hw)]

/-- Reading an encoding backwards: the reverse of the encoding of a word is the encoding of the
reversed word by the code whose codewords are the reversed codewords.  This turns a suffix code
into a prefix code.  SUV Problem 214, p. 213. -/
theorem reverse_encodeWord (c : Code α) (w : List α) :
    (c.encodeWord w).reverse = Code.encodeWord (fun a => (c a).reverse) w.reverse := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [encodeWord_cons, List.reverse_append, ih]
    unfold encodeWord
    simp

/-- There is a uniquely decodable code that is not a prefix code; a suffix code such as
`{0, 01}` over a two-letter alphabet is one.  SUV Problem 214, p. 213. -/
theorem exists_isUniquelyDecodable_not_isPrefixFree :
    ∃ c : Code Bool, c.IsUniquelyDecodable ∧ ¬ c.IsPrefixFree := by
  refine ⟨fun b => if b then [false, true] else [false], ?_, ?_⟩
  · have hpf : Code.IsPrefixFree
        (fun a => ((fun b : Bool => if b then [false, true] else [false]) a).reverse) := by
      refine ⟨by decide, ?_⟩
      intro a b hab
      cases a <;> cases b <;> simp at hab ⊢
    intro w₁ w₂ hw
    have hrev := congrArg List.reverse hw
    rw [reverse_encodeWord, reverse_encodeWord] at hrev
    exact List.reverse_injective (isUniquelyDecodable_of_isPrefixFree hpf hrev)
  · intro hc
    exact hc.2 false true (by decide) ⟨[true], rfl⟩

/-! ### Two constructions on codes -/

/-- The concatenation of a code for `α` and a code for `β`: the codeword of the pair `(a, b)` is
the codeword of `a` followed by the codeword of `b`.  SUV Problem 216, p. 213. -/
def concat (c : Code α) (d : Code β) : Code (α × β) := fun q => c q.1 ++ d q.2

/-- The codeword of a pair is the concatenation of the two codewords. -/
@[simp] theorem concat_apply (c : Code α) (d : Code β) (q : α × β) :
    concat c d q = c q.1 ++ d q.2 := rfl

/-- **The concatenation of two prefix codes is a prefix code** for the product alphabet: if
`c₁, …, c_k` is a prefix code for a `k`-letter alphabet and `d₁, …, d_l` is a prefix code for an
`l`-letter alphabet, the `kl` strings `c_i d_j` form a prefix code.
SUV Problem 216, p. 213. -/
theorem isPrefixFree_concat {c : Code α} {d : Code β} (hc : c.IsPrefixFree)
    (hd : d.IsPrefixFree) : (concat c d).IsPrefixFree := by
  refine ⟨fun q hq => hc.ne_nil q.1 (List.append_eq_nil_iff.1 hq).1, ?_⟩
  rintro ⟨a, b⟩ ⟨a', b'⟩ hne hpre
  simp only [concat_apply] at hpre
  have haa : a = a' := by
    by_contra h
    have h1 : c a <+: c a' ++ d b' := (List.prefix_append _ _).trans hpre
    rcases List.prefix_or_prefix_of_prefix h1 (List.prefix_append _ _) with h2 | h2
    · exact hc.2 a a' h h2
    · exact hc.2 a' a (Ne.symm h) h2
  subst haa
  rw [List.prefix_append_right_inj] at hpre
  have hbb : b = b' := by
    by_contra h
    exact hd.2 b b' h hpre
  exact hne (by rw [hbb])

/-- The complete prefix code of the hint of SUV Problem 215: `0 ↦ 00`, `1 ↦ 01`, `2 ↦ 1`.
SUV Problem 215, p. 213. -/
def ternaryCode : Code (Fin 3) := ![[false, false], [false, true], [true]]

/-- The code `0 ↦ 00`, `1 ↦ 01`, `2 ↦ 1` is a prefix code.  SUV Problem 215, p. 213. -/
private theorem ternaryCode_isPrefixFree : ternaryCode.IsPrefixFree := by
  refine ⟨by decide, by decide⟩

private theorem length_le_length_encodeWord {c : Code α} (hc : ∀ a, c a ≠ []) (w : List α) :
    w.length ≤ (c.encodeWord w).length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [encodeWord_cons, List.length_append, List.length_cons]
    have := List.length_pos_iff.2 (hc a)
    omega

private theorem encodeWord_prefix_of_prefix (c : Code α) {u v : List α} (h : u <+: v) :
    c.encodeWord u <+: c.encodeWord v := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨c.encodeWord t, by simp [encodeWord]⟩

private theorem eq_of_encodeWord_prefix {c : Code α} (hc : c.IsPrefixFree) :
    ∀ {u v : List α}, c.encodeWord u <+: c.encodeWord v → u.length = v.length → u = v := by
  intro u
  induction u with
  | nil =>
    intro v _ hlen
    exact (List.eq_nil_of_length_eq_zero hlen.symm).symm
  | cons a u ih =>
    intro v hpre hlen
    cases v with
    | nil => simp at hlen
    | cons b v =>
      rw [encodeWord_cons, encodeWord_cons] at hpre
      have hab : a = b := by
        by_contra hne
        have h1 : c a <+: c b ++ c.encodeWord v := (List.prefix_append _ _).trans hpre
        rcases List.prefix_or_prefix_of_prefix h1 (List.prefix_append _ _) with h2 | h2
        · exact hc.2 a b hne h2
        · exact hc.2 b a (Ne.symm hne) h2
      subst hab
      rw [List.prefix_append_right_inj] at hpre
      rw [ih hpre (by simpa using hlen)]

private theorem ofFn_prefix_ofFn (x : ℕ → Fin 3) {m n : ℕ} (h : m ≤ n) :
    (List.ofFn fun j : Fin m => x j.val) <+: List.ofFn fun j : Fin n => x j.val := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨_, (List.ofFn_add (f := fun j : Fin (m + k) => x j.val)).symm⟩

/-- The infinite binary sequence that reads off the codewords of `ternaryCode` along a ternary
sequence: its `n`-th bit is the `n`-th bit of the encoding of the first `n + 1` digits, which
has at least `n + 1` bits.  SUV Problem 215, p. 213. -/
private def ternaryStream (x : ℕ → Fin 3) : CantorSeq := fun n =>
  (ternaryCode.encodeWord (List.ofFn fun j : Fin (n + 1) => x j.val)).getD n false

private theorem isCantorPrefix_ternaryStream (x : ℕ → Fin 3) (n : ℕ) :
    IsCantorPrefix (ternaryCode.encodeWord (List.ofFn fun j : Fin n => x j.val))
      (ternaryStream x) := by
  intro i hi
  have h1 := encodeWord_prefix_of_prefix ternaryCode (ofFn_prefix_ofFn x (le_max_left n (i + 1)))
  have h2 :=
    encodeWord_prefix_of_prefix ternaryCode (ofFn_prefix_ofFn x (le_max_right n (i + 1)))
  have hi2 : i < (ternaryCode.encodeWord (List.ofFn fun j : Fin (i + 1) => x j.val)).length := by
    have := length_le_length_encodeWord ternaryCode_isPrefixFree.ne_nil
      (List.ofFn fun j : Fin (i + 1) => x j.val)
    rw [List.length_ofFn] at this
    omega
  change (ternaryCode.encodeWord (List.ofFn fun j : Fin (i + 1) => x j.val)).getD i false = _
  rw [List.getD_eq_getElem _ _ hi2, h1.getElem hi, h2.getElem hi2]

private theorem ternaryStream_injective : Function.Injective ternaryStream := by
  intro x y hxy
  funext j
  have hx := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 (isCantorPrefix_ternaryStream x (j + 1))
  have hy := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 (isCantorPrefix_ternaryStream y (j + 1))
  rw [hxy] at hx
  have key : (List.ofFn fun i : Fin (j + 1) => x i.val) =
      List.ofFn fun i : Fin (j + 1) => y i.val := by
    rcases le_total (ternaryCode.encodeWord (List.ofFn fun i : Fin (j + 1) => x i.val)).length
        (ternaryCode.encodeWord (List.ofFn fun i : Fin (j + 1) => y i.val)).length with h | h
    · refine eq_of_encodeWord_prefix ternaryCode_isPrefixFree ?_ (by simp)
      rw [← hx, ← hy]
      exact cantorPrefix_mono _ h
    · refine (eq_of_encodeWord_prefix ternaryCode_isPrefixFree ?_ (by simp)).symm
      rw [← hx, ← hy]
      exact cantorPrefix_mono _ h
  exact congrFun (List.ofFn_inj.1 key) ⟨j, Nat.lt_succ_self j⟩

/-- One step of parsing a binary sequence into codewords of `ternaryCode` from position `p`:
the digit read and the position after it. -/
private def ternaryStep (y : CantorSeq) (p : ℕ) : Fin 3 × ℕ :=
  if y p then (2, p + 1) else if y (p + 1) then (1, p + 2) else (0, p + 2)

/-- The position reached after parsing `k` digits. -/
private def ternaryPos (y : CantorSeq) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (ternaryStep y (ternaryPos y k)).2

/-- The `k`-th digit parsed from a binary sequence. -/
private def ternaryDigit (y : CantorSeq) (k : ℕ) : Fin 3 := (ternaryStep y (ternaryPos y k)).1

private theorem cantorPrefix_succ (y : CantorSeq) (p : ℕ) :
    cantorPrefix y (p + 1) = cantorPrefix y p ++ [y p] := by
  simp only [cantorPrefix, List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

private theorem cantorPrefix_ternaryStep (y : CantorSeq) (p : ℕ) :
    cantorPrefix y (ternaryStep y p).2 =
      cantorPrefix y p ++ ternaryCode (ternaryStep y p).1 := by
  unfold ternaryStep
  by_cases h0 : y p
  · simp [h0, cantorPrefix_succ, ternaryCode]
  · by_cases h1 : y (p + 1)
    · simp [h0, h1, cantorPrefix_succ, ternaryCode]
    · simp [h0, h1, cantorPrefix_succ, ternaryCode]

private theorem encodeWord_append (c : Code α) (u v : List α) :
    c.encodeWord (u ++ v) = c.encodeWord u ++ c.encodeWord v := by
  simp [encodeWord]

private theorem encodeWord_ternaryDigit (y : CantorSeq) (n : ℕ) :
    ternaryCode.encodeWord (List.ofFn fun j : Fin n => ternaryDigit y j.val) =
      cantorPrefix y (ternaryPos y n) := by
  induction n with
  | zero => simp [cantorPrefix, ternaryPos]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, encodeWord_append]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    change _ = cantorPrefix y (ternaryStep y (ternaryPos y n)).2
    rw [cantorPrefix_ternaryStep]
    simp [encodeWord, ternaryDigit]

private theorem le_ternaryPos (y : CantorSeq) (n : ℕ) : n ≤ ternaryPos y n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    change n + 1 ≤ (ternaryStep y (ternaryPos y n)).2
    unfold ternaryStep
    split_ifs <;> simp <;> omega

/-- Every binary sequence is read off some ternary sequence: the code `0 ↦ 00`, `1 ↦ 01`,
`2 ↦ 1` is complete, so a binary sequence can be parsed into codewords from left to right
without ever getting stuck.  SUV Problem 215, p. 213. -/
private theorem ternaryStream_surjective : Function.Surjective ternaryStream := by
  intro y
  refine ⟨ternaryDigit y, funext fun i => ?_⟩
  change (ternaryCode.encodeWord (List.ofFn fun j : Fin (i + 1) => ternaryDigit y j.val)).getD
    i false = y i
  rw [encodeWord_ternaryDigit]
  have hi : i < (cantorPrefix y (ternaryPos y (i + 1))).length := by
    rw [cantorPrefix_length]
    exact lt_of_lt_of_le (Nat.lt_succ_self i) (le_ternaryPos y (i + 1))
  rw [List.getD_eq_getElem _ _ hi, cantorPrefix_getElem]


/-- **A bijection between ternary and binary sequences.**  There is a bijection from the infinite
sequences of digits `0, 1, 2` to the infinite binary sequences that reads off the codewords of the
complete prefix code `0 ↦ 00`, `1 ↦ 01`, `2 ↦ 1`: the image of a ternary sequence extends the
encoding of each of its finite prefixes.  SUV Problem 215, p. 213. -/
theorem exists_bijective_ternaryCode_stream :
    ∃ f : (ℕ → Fin 3) → CantorSeq, Function.Bijective f ∧
      ∀ (x : ℕ → Fin 3) (n : ℕ),
        IsCantorPrefix (ternaryCode.encodeWord (List.ofFn fun j : Fin n => x j.val)) (f x) :=
  ⟨ternaryStream, ⟨ternaryStream_injective, ternaryStream_surjective⟩,
    isCantorPrefix_ternaryStream⟩

/-! ### Injective codes of minimal average length -/

/-- The strings of length at most `j`, as a finset. -/
private def stringsLe (j : ℕ) : Finset BitString :=
  (Finset.range (j + 1)).biUnion stringsOfLength

private theorem mem_stringsLe {j : ℕ} {s : BitString} : s ∈ stringsLe j ↔ s.length ≤ j := by
  simp only [stringsLe, Finset.mem_biUnion, Finset.mem_range, mem_stringsOfLength]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨s.length, by omega, rfl⟩

/-- The average length as a sum over bit positions: position `j` is paid for by every letter
whose codeword is longer than `j`.  SUV Problem 217, p. 214. -/
private theorem avgLength_eq_sum_range [Fintype α] (c : Code α) (p : α → ℝ) {M : ℕ}
    (hM : ∀ a, (c a).length ≤ M) :
    c.avgLength p =
      ∑ j ∈ Finset.range M, ∑ a ∈ Finset.univ.filter (fun a => ¬ (c a).length ≤ j), p a := by
  have key : ∀ a, ((c a).length : ℝ) =
      ∑ j ∈ Finset.range M, if ¬ (c a).length ≤ j then (1 : ℝ) else 0 := by
    intro a
    rw [Finset.sum_boole]
    have : (Finset.range M).filter (fun j => ¬ (c a).length ≤ j) =
        Finset.range (c a).length := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      have := hM a
      omega
    rw [this, Finset.card_range]
  unfold avgLength
  simp_rw [key, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (Finset.sum_filter _ _).symm

/-- A set of letters that carries the largest frequencies has the largest total frequency among
the sets of at most its size.  SUV Problem 217, p. 214. -/
private theorem sum_le_sum_of_card_le {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    {s t : Finset α} (hcard : s.card ≤ t.card) (htop : ∀ a ∈ t, ∀ b ∉ t, p b ≤ p a) :
    ∑ a ∈ s, p a ≤ ∑ a ∈ t, p a := by
  classical
  rw [← Finset.sum_inter_add_sum_sdiff s t, ← Finset.sum_inter_add_sum_sdiff t s,
    Finset.inter_comm t s]
  refine add_le_add le_rfl ?_
  have hst : (s \ t).card ≤ (t \ s).card := by
    have h1 := Finset.card_sdiff_add_card_inter s t
    have h2 := Finset.card_sdiff_add_card_inter t s
    rw [Finset.inter_comm] at h2
    omega
  rcases (s \ t).eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty]
    exact Finset.sum_nonneg fun a _ => hp a
  obtain ⟨b₀, hb₀, hmax⟩ := (s \ t).exists_max_image p h
  obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq hst
  calc ∑ a ∈ s \ t, p a ≤ (s \ t).card • p b₀ := Finset.sum_le_card_nsmul _ _ _ hmax
    _ = u.card • p b₀ := by rw [hucard]
    _ ≤ ∑ a ∈ u, p a := by
        refine Finset.card_nsmul_le_sum _ _ _ fun a ha => ?_
        exact htop a (Finset.mem_sdiff.1 (hu ha)).1 b₀ (Finset.mem_sdiff.1 hb₀).2
    _ ≤ ∑ a ∈ t \ s, p a := Finset.sum_le_sum_of_subset_of_nonneg hu fun a _ _ => hp a

/-- The counting step: for every `j`, the matching code has at least as many codewords of
length at most `j` as any injective code, because it uses every string of length at most `j`
before any longer one.  SUV Problem 217, p. 214. -/
private theorem card_filter_length_le [Fintype α] {c : Code α}
    (hshort : ∀ (a : α) (s : BitString), s.length < (c a).length → ∃ b, c b = s)
    {d : Code α} (hd : Function.Injective d) (j : ℕ) :
    (Finset.univ.filter fun a => (d a).length ≤ j).card ≤
      (Finset.univ.filter fun a => (c a).length ≤ j).card := by
  by_cases h : ∀ a, (c a).length ≤ j
  · rw [Finset.filter_true_of_mem fun a _ => h a]
    exact Finset.card_le_card (Finset.subset_univ _)
  push Not at h
  obtain ⟨a, ha⟩ := h
  calc (Finset.univ.filter fun a => (d a).length ≤ j).card ≤ (stringsLe j).card := by
        refine Finset.card_le_card_of_injOn d (fun b hb => ?_) hd.injOn
        exact Finset.mem_coe.2
          (mem_stringsLe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2)
    _ ≤ (Finset.univ.filter fun a => (c a).length ≤ j).card := by
        refine Finset.card_le_card_of_surjOn c fun s hs => ?_
        have hs' := mem_stringsLe.1 (Finset.mem_coe.1 hs)
        obtain ⟨b, rfl⟩ := hshort a s (hs'.trans_lt ha)
        exact ⟨b, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ b, hs'⟩), rfl⟩

/-- **The matching code is optimal.**  The supporting implication behind
`Code.exists_injective_avgLength_le`: an injective code in which every string shorter than a
codeword is itself a codeword (`hshort`) and in which a more frequent letter gets a codeword that
is no longer (`hmono`) has the smallest average length among injective codes.
SUV Problem 217, p. 214. -/
theorem avgLength_le_of_injective_of_optimal_matching [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) {c : Code α} (_hinj : Function.Injective c)
    (hshort : ∀ (a : α) (s : BitString), s.length < (c a).length → ∃ b, c b = s)
    (hmono : ∀ a b : α, p a < p b → (c b).length ≤ (c a).length)
    {d : Code α} (hd : Function.Injective d) :
    c.avgLength p ≤ d.avgLength p := by
  classical
  obtain ⟨M, hMc, hMd⟩ : ∃ M : ℕ, (∀ a, (c a).length ≤ M) ∧ ∀ a, (d a).length ≤ M :=
    ⟨(Finset.univ.sup fun a => (c a).length) ⊔ (Finset.univ.sup fun a => (d a).length),
      fun a => (Finset.le_sup (f := fun a => (c a).length) (Finset.mem_univ a)).trans le_sup_left,
      fun a => (Finset.le_sup (f := fun a => (d a).length) (Finset.mem_univ a)).trans le_sup_right⟩
  rw [avgLength_eq_sum_range c p hMc, avgLength_eq_sum_range d p hMd]
  refine Finset.sum_le_sum fun j _ => ?_
  have hc := Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => (c a).length ≤ j) p
  have hd' := Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => (d a).length ≤ j) p
  have hle : ∑ a ∈ Finset.univ.filter (fun a => (d a).length ≤ j), p a ≤
      ∑ a ∈ Finset.univ.filter (fun a => (c a).length ≤ j), p a := by
    refine sum_le_sum_of_card_le hp (card_filter_length_le hshort hd j) ?_
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hlt
    push Not at hlt
    exact hb ⟨Finset.mem_univ b, (hmono a b hlt).trans ha.2⟩
  linarith

/-- The first `k` binary strings in order of increasing length: an injective family of strings
whose lengths are monotone in the index and in which every string shorter than a member is
itself a member.  SUV Problem 217, p. 214. -/
private theorem exists_strings_sorted (k : ℕ) :
    ∃ str : Fin k → BitString, Function.Injective str ∧ Monotone (fun i => (str i).length) ∧
      ∀ (i : Fin k) (s : BitString), s.length < (str i).length → ∃ j, str j = s := by
  classical
  have hk : k ≤ Fintype.card (stringsLe k) := by
    rw [Fintype.card_coe]
    have hsub : (Finset.range k).image (fun i => List.replicate i true) ⊆ stringsLe k := by
      intro s hs
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hs
      rw [mem_stringsLe, List.length_replicate]
      exact (Finset.mem_range.1 hi).le
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ (List.replicate_left_injective true),
      Finset.card_range] at this
  set e := Fintype.equivFin (stringsLe k) with he
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin (Fintype.card (stringsLe k))),
      Monotone fun i => ((e.symm (σ i) : stringsLe k) : BitString).length :=
    ⟨_, Tuple.monotone_sort fun i => ((e.symm i : stringsLe k) : BitString).length⟩
  refine ⟨fun i => ((e.symm (σ (Fin.castLE hk i)) : stringsLe k) : BitString), ?_, ?_, ?_⟩
  · intro i i' h
    exact Fin.castLE_injective hk (σ.injective (e.symm.injective (Subtype.val_injective h)))
  · intro i i' h
    exact hmono (show Fin.castLE hk i ≤ Fin.castLE hk i' from h)
  · intro i s hs
    have hsT : s ∈ stringsLe k :=
      mem_stringsLe.2 (hs.le.trans (mem_stringsLe.1 (e.symm (σ (Fin.castLE hk i))).2))
    obtain ⟨j, hj⟩ : ∃ j, ((e.symm (σ j) : stringsLe k) : BitString) = s :=
      ⟨σ.symm (e ⟨s, hsT⟩), by rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]⟩
    have hlt : j < Fin.castLE hk i := hmono.reflect_lt
      (show ((e.symm (σ j) : stringsLe k) : BitString).length <
        ((e.symm (σ (Fin.castLE hk i)) : stringsLe k) : BitString).length by
        rw [hj]; exact hs)
    refine ⟨⟨j.val, lt_trans hlt i.isLt⟩, ?_⟩
    have hcast : Fin.castLE hk ⟨j.val, lt_trans hlt i.isLt⟩ = j := Fin.ext rfl
    change ((e.symm (σ (Fin.castLE hk ⟨j.val, lt_trans hlt i.isLt⟩)) : stringsLe k) : BitString)
      = s
    rw [hcast, hj]

/-- The matching of the hint: the letters in order of decreasing frequency, the binary strings
in order of increasing length, matched in order.  SUV Problem 217, p. 214. -/
private theorem exists_injective_matching [Finite α] (p : α → ℝ) :
    ∃ c : Code α, Function.Injective c ∧
      (∀ (a : α) (s : BitString), s.length < (c a).length → ∃ b, c b = s) ∧
      ∀ a b : α, p a < p b → (c b).length ≤ (c a).length := by
  have := Fintype.ofFinite α
  obtain ⟨str, hinj, hmono, hshort⟩ := exists_strings_sorted (Fintype.card α)
  set e := Fintype.equivFin α with he
  obtain ⟨σ, hsort⟩ : ∃ σ : Equiv.Perm (Fin (Fintype.card α)),
      Monotone fun i => -p (e.symm (σ i)) := ⟨_, Tuple.monotone_sort fun i => -p (e.symm i)⟩
  refine ⟨fun a => str (σ.symm (e a)), ?_, ?_, ?_⟩
  · intro a b h
    exact e.injective (σ.symm.injective (hinj h))
  · intro a s hs
    obtain ⟨j, hj⟩ := hshort _ s hs
    refine ⟨e.symm (σ j), ?_⟩
    change str (σ.symm (e (e.symm (σ j)))) = s
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply, hj]
  · intro a b hab
    have hlt : σ.symm (e b) < σ.symm (e a) := by
      by_contra h
      push Not at h
      have := hsort h
      simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, neg_le_neg_iff] at this
      exact absurd hab (not_lt.2 this)
    exact hmono hlt.le

/-- **An injective code of minimal average length exists**, and the matching described by the
hint of the problem produces one: putting the letters in order of decreasing frequency and the
binary strings in order of increasing length and matching them gives an injective code `c` in
which every string shorter than a codeword is itself a codeword, in which a more frequent letter
gets a codeword that is no longer, and whose average length is minimal among *injective* codes
(no constraint beyond injectivity, so the empty string may be a codeword).  This is the answer to
the question of the problem, which is printed only as a hint.  SUV Problem 217, p. 214. -/
theorem exists_injective_avgLength_le [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) :
    ∃ c : Code α, Function.Injective c ∧
      (∀ (a : α) (s : BitString), s.length < (c a).length → ∃ b, c b = s) ∧
      (∀ a b : α, p a < p b → (c b).length ≤ (c a).length) ∧
      ∀ d : Code α, Function.Injective d → c.avgLength p ≤ d.avgLength p := by
  obtain ⟨c, hinj, hshort, hmono⟩ := exists_injective_matching p
  exact ⟨c, hinj, hshort, hmono, fun d hd =>
    avgLength_le_of_injective_of_optimal_matching hp hinj hshort hmono hd⟩

/-- No codeword of a uniquely decodable code is empty: the empty codeword would encode the
one-letter word and the empty word alike.  SUV Section 7.1.1, p. 213. -/
theorem ne_nil_of_isUniquelyDecodable {c : Code α} (h : c.IsUniquelyDecodable) (a : α) :
    c a ≠ [] := by
  intro hnil
  have : c.encodeWord [a] = c.encodeWord [] := by simp [hnil]
  exact List.cons_ne_nil a [] (h this)

/-! ### The McMillan inequality -/

/-- The encoding of a word given as a tuple has length the sum of the codeword lengths. -/
private theorem length_encodeWord_ofFn (c : Code α) {N : ℕ} (p : Fin N → α) :
    (c.encodeWord (List.ofFn p)).length = ∑ i, (c (p i)).length := by
  simp [encodeWord, List.length_flatten, List.map_ofFn, List.sum_ofFn]

/-- The `N`-th power of the Kraft sum is the sum of `2^{-|enc w|}` over the words `w` of length
`N`.  SUV Theorem 140, p. 217. -/
private theorem kraftSum_pow_eq [Fintype α] (c : Code α) (N : ℕ) :
    c.kraftSum ^ N = ∑ p : Fin N → α, (2 : ℝ)⁻¹ ^ (c.encodeWord (List.ofFn p)).length := by
  rw [kraftSum, Fintype.sum_pow]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [length_encodeWord_ofFn, Finset.prod_pow_eq_pow_sum]

/-- Summing `2^{-|s|}` over all strings of length at most `M` gives `M + 1`: each length
contributes exactly one.  SUV Theorem 140, p. 217. -/
private theorem sum_stringsOfLength_le (M : ℕ) :
    ∑ s ∈ (Finset.range (M + 1)).biUnion stringsOfLength, (2 : ℝ)⁻¹ ^ s.length = M + 1 := by
  rw [Finset.sum_biUnion]
  · have : ∀ m ∈ Finset.range (M + 1),
        ∑ s ∈ stringsOfLength m, (2 : ℝ)⁻¹ ^ s.length = 1 := by
      intro m _
      rw [Finset.sum_congr rfl fun s hs => by rw [(mem_stringsOfLength m s).1 hs]]
      rw [Finset.sum_const, card_stringsOfLength, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
        inv_pow, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast; ring
  · intro m _ m' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs hs'
    rw [mem_stringsOfLength] at hs hs'
    exact hne (hs.symm.trans hs')

/-- The counting step of the McMillan inequality: for a uniquely decodable code with maximal
codeword length `L`, the words of length `N` have distinct encodings of length at most `N L`,
so the `N`-th power of the Kraft sum is at most `N L + 1`.  SUV Theorem 140, p. 217. -/
private theorem kraftSum_pow_le_of_isUniquelyDecodable [Fintype α] {c : Code α}
    (h : c.IsUniquelyDecodable) (N : ℕ) :
    c.kraftSum ^ N ≤ N * (Finset.univ.sup fun a => (c a).length) + 1 := by
  classical
  set L := Finset.univ.sup fun a => (c a).length with hL
  rw [kraftSum_pow_eq]
  have hinj : Function.Injective fun p : Fin N → α => c.encodeWord (List.ofFn p) :=
    fun p q hpq => List.ofFn_injective (h hpq)
  rw [← Finset.sum_image (f := fun s : BitString => (2 : ℝ)⁻¹ ^ s.length) hinj.injOn]
  calc ∑ s ∈ Finset.univ.image (fun p : Fin N → α => c.encodeWord (List.ofFn p)),
        (2 : ℝ)⁻¹ ^ s.length
      ≤ ∑ s ∈ (Finset.range (N * L + 1)).biUnion stringsOfLength, (2 : ℝ)⁻¹ ^ s.length := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro s hs
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hs
        rw [Finset.mem_biUnion]
        refine ⟨_, Finset.mem_range.2 (Nat.lt_succ_of_le ?_), (mem_stringsOfLength _ _).2 rfl⟩
        rw [length_encodeWord_ofFn]
        calc ∑ i, (c (p i)).length ≤ ∑ _i : Fin N, L :=
              Finset.sum_le_sum fun i _ => Finset.le_sup (f := fun a => (c a).length)
                (Finset.mem_univ (p i))
          _ = N * L := by simp
    _ = N * L + 1 := by rw [sum_stringsOfLength_le]; push_cast; ring

/-- A real number whose powers grow at most linearly is at most one.
SUV Theorem 140, p. 217. -/
private theorem le_one_of_pow_le_linear {S : ℝ} {L : ℕ}
    (h : ∀ N : ℕ, S ^ N ≤ N * L + 1) : S ≤ 1 := by
  by_contra hS
  push Not at hS
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hS
  have hev := ht.eventually_lt_const (u := 1 / ((L : ℝ) + 1)) (by positivity)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  have hN := hN₀ (max N₀ 1) (le_max_left _ _)
  set N := max N₀ 1 with hNdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_max_right N₀ 1
  have hpos : 0 < S ^ N := pow_pos (by linarith) _
  rw [pow_one, div_lt_iff₀ hpos, div_mul_eq_mul_div, one_mul, lt_div_iff₀ (by positivity)] at hN
  have := h N
  nlinarith

/-- **The McMillan inequality.**  The codeword lengths `n_i` of a *uniquely decodable* code
already satisfy the Kraft inequality `∑_i 2^{-n_i} ≤ 1`.

The book gives a second proof of this inequality on p. 222, through the entropy lower bound
`Kolmogorov.entropyDist_le_avgLength_of_isUniquelyDecodable`.  SUV Theorem 140, p. 217. -/
theorem kraftSum_le_one_of_isUniquelyDecodable [Fintype α] {c : Code α}
    (h : c.IsUniquelyDecodable) : c.kraftSum ≤ 1 :=
  le_one_of_pow_le_linear (kraftSum_pow_le_of_isUniquelyDecodable h)

/-! ### The Kraft inequality -/

/-- The strings of length `m` that extend the string `s`. -/
private def extensions (s : BitString) (m : ℕ) : Finset BitString :=
  (stringsOfLength (m - s.length)).image (s ++ ·)

private theorem card_extensions {s : BitString} (m : ℕ) :
    (extensions s m).card = 2 ^ (m - s.length) := by
  rw [extensions, Finset.card_image_of_injective _ fun u v huv => List.append_cancel_left huv,
    card_stringsOfLength]

private theorem mem_extensions {s x : BitString} {m : ℕ} (h : s.length ≤ m) :
    x ∈ extensions s m ↔ x.length = m ∧ s <+: x := by
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    rw [mem_stringsOfLength] at hu
    refine ⟨?_, List.prefix_append _ _⟩
    rw [List.length_append, hu]
    omega
  · rintro ⟨hx, ⟨u, rfl⟩⟩
    refine Finset.mem_image.2 ⟨u, (mem_stringsOfLength _ _).2 ?_, rfl⟩
    rw [List.length_append] at hx
    omega

/-- The counting step of Kraft's lemma: a prefix-free family of codewords of lengths at most `m`
whose Kraft sum is at most `1 - 2^{-m}` leaves some string of length `m` free, i.e. extending
none of the codewords.  SUV Lemma (Kraft inequality), p. 214. -/
private theorem exists_free_string {t : Finset α} {c : Code α} {m : ℕ}
    (hle : ∀ b ∈ t, (c b).length ≤ m)
    (hpf : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ c a <+: c b)
    (hsum : ∑ b ∈ t, (2 : ℝ)⁻¹ ^ (c b).length ≤ 1 - (2 : ℝ)⁻¹ ^ m) :
    ∃ x : BitString, x.length = m ∧ ∀ b ∈ t, ¬ c b <+: x := by
  set E := t.biUnion fun b => extensions (c b) m with hE
  have hcard : E.card = ∑ b ∈ t, 2 ^ (m - (c b).length) := by
    rw [hE, Finset.card_biUnion]
    · exact Finset.sum_congr rfl fun b _ => card_extensions m
    · intro a ha b hb hab
      rw [Function.onFun, Finset.disjoint_left]
      intro x hxa hxb
      rw [mem_extensions (hle a ha)] at hxa
      rw [mem_extensions (hle b hb)] at hxb
      rcases List.prefix_or_prefix_of_prefix hxa.2 hxb.2 with h | h
      · exact hpf a ha b hb hab h
      · exact hpf b hb a ha (Ne.symm hab) h
  have hreal : ((∑ b ∈ t, 2 ^ (m - (c b).length) : ℕ) : ℝ) + 1 ≤ 2 ^ m := by
    push_cast
    have h2 : (∑ b ∈ t, (2 : ℝ) ^ (m - (c b).length)) =
        2 ^ m * ∑ b ∈ t, (2 : ℝ)⁻¹ ^ (c b).length := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [inv_pow, pow_sub₀ (2 : ℝ) two_ne_zero (hle b hb)]
    have h3 : (2 : ℝ) ^ m * ∑ b ∈ t, (2 : ℝ)⁻¹ ^ (c b).length ≤ 2 ^ m * (1 - (2 : ℝ)⁻¹ ^ m) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    rw [mul_sub, mul_one, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)] at h3
    linarith
  have hlt : E.card < (stringsOfLength m).card := by
    rw [hcard, card_stringsOfLength]
    have : (∑ b ∈ t, 2 ^ (m - (c b).length)) + 1 ≤ 2 ^ m := by exact_mod_cast hreal
    omega
  obtain ⟨x, hx, hxE⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [mem_stringsOfLength] at hx
  refine ⟨x, hx, fun b hb hpre => hxE ?_⟩
  exact Finset.mem_biUnion.2 ⟨b, hb, (mem_extensions (hle b hb)).2 ⟨hx, hpre⟩⟩

/-- The inductive construction of Kraft's lemma: codewords are assigned to the letters of a
finite set in order of increasing length, each time choosing a free string of the required
length, which the counting step provides.  SUV Lemma (Kraft inequality), p. 214. -/
private theorem exists_isPrefixFree_on_of_kraft (n : α → ℕ) (t : Finset α)
    (hsum : ∑ a ∈ t, (2 : ℝ)⁻¹ ^ n a ≤ 1) :
    ∃ c : Code α, (∀ a ∈ t, (c a).length = n a) ∧
      ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ c a <+: c b := by
  classical
  induction t using Finset.strongInduction with
  | H t ih =>
  rcases t.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => [], by simp, by simp⟩
  obtain ⟨a, ha, hmax⟩ := t.exists_max_image n hne
  have hsum' : ∑ b ∈ t.erase a, (2 : ℝ)⁻¹ ^ n b ≤ 1 - (2 : ℝ)⁻¹ ^ n a := by
    have := Finset.sum_erase_add t (fun b => (2 : ℝ)⁻¹ ^ n b) ha
    linarith
  obtain ⟨c, hlen, hpf⟩ := ih (t.erase a) (Finset.erase_ssubset ha)
    (hsum'.trans (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) (n a)]))
  obtain ⟨x, hx, hxfree⟩ := exists_free_string (t := t.erase a) (c := c) (m := n a)
    (fun b hb => (hlen b hb).symm ▸ hmax b (Finset.mem_of_mem_erase hb)) hpf
    (by rw [Finset.sum_congr rfl fun b hb => by rw [hlen b hb]]; exact hsum')
  refine ⟨Function.update c a x, fun b hb => ?_, fun b hb b' hb' hbb hpre => ?_⟩
  · rcases eq_or_ne b a with rfl | hba
    · rw [Function.update_self, hx]
    · rw [Function.update_of_ne hba]
      exact hlen b (Finset.mem_erase.2 ⟨hba, hb⟩)
  · rcases eq_or_ne b a with rfl | hba
    · have hb'a : b' ∈ t.erase b := Finset.mem_erase.2 ⟨Ne.symm hbb, hb'⟩
      rw [Function.update_self, Function.update_of_ne (Ne.symm hbb)] at hpre
      have heq : x = c b' := hpre.eq_of_length_le (by rw [hlen b' hb'a, hx]; exact hmax b' hb')
      exact hxfree b' hb'a (heq ▸ List.prefix_refl x)
    · rw [Function.update_of_ne hba] at hpre
      rcases eq_or_ne b' a with rfl | hb'a
      · rw [Function.update_self] at hpre
        exact hxfree b (Finset.mem_erase.2 ⟨hba, hb⟩) hpre
      · rw [Function.update_of_ne hb'a] at hpre
        exact hpf b (Finset.mem_erase.2 ⟨hba, hb⟩) b' (Finset.mem_erase.2 ⟨hb'a, hb'⟩) hbb hpre

/-- The constructive half of Kraft's lemma: positive lengths `n` with `∑_a 2^{-n_a} ≤ 1` are the
codeword lengths of some prefix code.  SUV Lemma (Kraft inequality), p. 214. -/
private theorem exists_isPrefixFree_of_kraft [Fintype α] (n : α → ℕ) (hpos : ∀ a, 0 < n a)
    (hsum : ∑ a, (2 : ℝ)⁻¹ ^ n a ≤ 1) :
    ∃ c : Code α, (∀ a, (c a).length = n a) ∧ c.IsPrefixFree := by
  classical
  obtain ⟨c, hlen, hpf⟩ := exists_isPrefixFree_on_of_kraft n Finset.univ hsum
  refine ⟨c, fun a => hlen a (Finset.mem_univ a), fun a hnil => ?_,
    fun a b hab => hpf a (Finset.mem_univ a) b (Finset.mem_univ b) hab⟩
  have h := hlen a (Finset.mem_univ a)
  rw [hnil, List.length_nil] at h
  exact absurd h.symm (hpos a).ne'

/-- **Kraft's inequality.**  A vector of lengths `n_1, …, n_k` is the vector of codeword lengths
of a prefix code if and only if every `n_i` is positive and `∑_i 2^{-n_i} ≤ 1`.

The book states the lemma for *non-negative* integers `n_1, …, n_k`, with `∑_i 2^{-n_i} ≤ 1`
alone on the right-hand side (p. 214).  The conjunct `0 < n a` is therefore not the book's: it is
forced by the non-empty-codeword repair of `Code.IsPrefixFree` (see its docstring) and is the one
place in the chapter where that repair is visible.  It is harmless for `k ≥ 2` letters, where
`∑_i 2^{-n_i} ≤ 1` already forbids `n_i = 0`, the other terms being positive.  For a one-letter
alphabet, though, `n = 0` satisfies the printed Kraft inequality and is realised only by the
empty codeword, which the repaired definition rejects.
SUV Lemma (Kraft inequality), p. 214. -/
theorem exists_isPrefixFree_lengths_iff_kraft [Fintype α] (n : α → ℕ) :
    (∃ c : Code α, (∀ a, (c a).length = n a) ∧ c.IsPrefixFree) ↔
      ((∀ a, 0 < n a) ∧ ∑ a, (2 : ℝ)⁻¹ ^ n a ≤ 1) := by
  constructor
  · rintro ⟨c, hlen, hc⟩
    refine ⟨fun a => ?_, ?_⟩
    · rw [← hlen a]
      exact List.length_pos_iff.2 (hc.ne_nil a)
    · have h := kraftSum_le_one_of_isUniquelyDecodable (isUniquelyDecodable_of_isPrefixFree hc)
      rw [kraftSum] at h
      simpa only [hlen] using h
  · rintro ⟨hpos, hsum⟩
    exact exists_isPrefixFree_of_kraft n hpos hsum

/-- **Uniquely decodable codes are no shorter than prefix codes.**  For every uniquely decodable
code there is a prefix code with the same codeword lengths; this is the McMillan inequality
combined with Kraft's lemma.  SUV Theorem 140, p. 217. -/
theorem exists_isPrefixFree_lengths_eq_of_isUniquelyDecodable [Finite α] {c : Code α}
    (h : c.IsUniquelyDecodable) :
    ∃ d : Code α, d.IsPrefixFree ∧ ∀ a, (d a).length = (c a).length := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨d, hlen, hd⟩ := (exists_isPrefixFree_lengths_iff_kraft fun a => (c a).length).2
    ⟨fun a => List.length_pos_iff.2 (ne_nil_of_isUniquelyDecodable h a),
      kraftSum_le_one_of_isUniquelyDecodable h⟩
  exact ⟨d, hd, hlen⟩

end Code

end Kolmogorov
