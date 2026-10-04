/-
Copyright (c) 2024 The KolmogorovMathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The KolmogorovMathlib Contributors
-/
import KolmogorovMathlib.Entropy.Codes.Kraft
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.FinCases

/-!
# The Huffman code

SUV Section 7.1.3, pp. 216–217.

Theorem 138 locates the average length of an optimal prefix code between `H` and `H + 1`; the
Huffman algorithm computes such a code.  The algorithm merges the two rarest letters into one,
builds an optimal prefix code for the `k − 1` resulting probabilities recursively, and replaces
the codeword `x` of the merged letter by `x0` and `x1`.

This module states the claim that this produces an optimal code:

* `IsOptimalPrefixCode p c` — `c` is a prefix code of minimal average length for `p`;
* `exists_isOptimalPrefixCode` — an optimal prefix code exists, so the phrase "the lengths of the
  codewords for an optimal code" of p. 216 refers to something;
* `IsHuffmanCode p c` — the codes produced by the recursive algorithm of p. 217, as an inductive
  relation: the base cases of one and of two letters, the rearrangement of the letters in order of
  increasing probability, and the merge/split step;
* `exists_isHuffmanCode` — the algorithm always produces a code, so that the relation is
  non-empty on every non-empty alphabet;
* `isOptimalPrefixCode_of_isHuffmanCode` — the theorem of p. 217: every Huffman code is an optimal
  prefix code, and `exists_isHuffmanCode_isOptimalPrefixCode` for the two together, which is the
  printed claim that the algorithm *finds* the optimal code.

The three lemmas of the book's argument are stated separately, as the supporting statements they
are: `length_le_length_of_prob_lt` (the exchange argument), the equality
`length_zero_eq_length_one_of_isOptimalPrefixCode` of the two largest lengths, and
`isOptimalPrefixCode_huffmanSplit`, the induction step itself.

The alphabet of the recursion step is `Fin (k + 2)` with the probabilities in increasing order, as
on p. 216 (`p₁ ≤ p₂ ≤ … ≤ p_k`), so that the two letters to be merged are `0` and `1`.

Prefix codes here have non-empty codewords (`Code.IsPrefixFree`), which is a repair adopted by
this library and not a condition of the book (see the docstring of `Code.IsPrefixFree`).  It is
why the recursion stops at two letters instead of one: an optimal code for a one-letter alphabet
is a single *bit* here, not the empty string of the book's recursion, and splitting it would give
two codewords of length two instead of the optimal `0` and `1`.  For `k ≥ 2` letters this changes
nothing, because the codes produced for two letters and the codes obtained from the one-letter
code by the printed recursion agree.
-/

namespace Kolmogorov

open Finset

variable {α : Type*}

/-! ### Codes under permutations and pointwise length bounds -/

/-- Precomposing a prefix code with an injective map of alphabets gives a prefix code.
SUV Section 7.1.1, p. 213. -/
theorem Code.IsPrefixFree.comp {β : Type*} {c : Code α} (hc : c.IsPrefixFree) {f : β → α}
    (hf : Function.Injective f) : Code.IsPrefixFree (fun b => c (f b)) :=
  ⟨fun b => hc.ne_nil (f b), fun a b hab => hc.2 (f a) (f b) (hf.ne hab)⟩

/-- Every codeword of a prefix code has positive length.  SUV Section 7.1.1, p. 213. -/
theorem Code.IsPrefixFree.one_le_length {c : Code α} (hc : c.IsPrefixFree) (a : α) :
    1 ≤ (c a).length :=
  List.length_pos_of_ne_nil (hc.ne_nil a)

/-- The average length is non-negative for non-negative weights.  SUV Section 7.1, p. 214. -/
theorem Code.avgLength_nonneg [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (c : Code α) :
    0 ≤ c.avgLength p :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hp a) (Nat.cast_nonneg _)

/-- For non-negative weights the average length is monotone in the codeword lengths.
SUV Section 7.1, p. 214. -/
theorem Code.avgLength_le_avgLength_of_length_le [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    {c d : Code α} (h : ∀ a, (c a).length ≤ (d a).length) : c.avgLength p ≤ d.avgLength p :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (by exact_mod_cast h a) (hp a)

/-- Two codes with the same codeword lengths have the same average length.
SUV Section 7.1, p. 214. -/
theorem Code.avgLength_congr [Fintype α] (p : α → ℝ) {c d : Code α}
    (h : ∀ a, (c a).length = (d a).length) : c.avgLength p = d.avgLength p :=
  Finset.sum_congr rfl fun a _ => by rw [h a]

/-- Reindexing the code and the distribution by the same bijection leaves the average length
unchanged.  SUV Section 7.1.3, p. 216. -/
theorem Code.avgLength_comp_equiv [Fintype α] {β : Type*} [Fintype β] (σ : β ≃ α) (c : Code α)
    (p : α → ℝ) : Code.avgLength (fun b => c (σ b)) (fun b => p (σ b)) = c.avgLength p :=
  Equiv.sum_comp σ fun a => p a * (c a).length

/-- The average length after exchanging the codewords of the letters `a` and `b`: it changes by
`(p a − p b)(|c b| − |c a|)`, the quantity of the exchange argument.
SUV Section 7.1.3, p. 216. -/
theorem Code.avgLength_comp_swap [Fintype α] [DecidableEq α] (c : Code α) (p : α → ℝ)
    (a b : α) : Code.avgLength (fun x => c (Equiv.swap a b x)) p =
      c.avgLength p + (p a - p b) * (((c b).length : ℝ) - (c a).length) := by
  by_cases hab : a = b
  · subst hab
    simp
  · have key : ∑ x, (p x * ((c (Equiv.swap a b x)).length : ℝ) - p x * ((c x).length : ℝ)) =
        (p a * ((c b).length : ℝ) - p a * ((c a).length : ℝ)) +
          (p b * ((c a).length : ℝ) - p b * ((c b).length : ℝ)) := by
      rw [Finset.sum_eq_add_of_mem a b (mem_univ a) (mem_univ b) hab]
      · rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
      · intro x _ hx
        rw [Equiv.swap_apply_of_ne_of_ne hx.1 hx.2, sub_self]
    rw [Finset.sum_sub_distrib] at key
    unfold Code.avgLength
    linarith

/-- The average length after replacing the codeword of the letter `a` by `x`.
SUV Section 7.1.3, p. 216. -/
theorem Code.avgLength_update [Fintype α] [DecidableEq α] (c : Code α) (p : α → ℝ) (a : α)
    (x : BitString) : Code.avgLength (Function.update c a x) p =
      c.avgLength p + p a * ((x.length : ℝ) - (c a).length) := by
  have key : ∑ i, (p i * ((Function.update c a x i).length : ℝ) - p i * ((c i).length : ℝ)) =
      p a * ((x.length : ℝ) - (c a).length) := by
    rw [Finset.sum_eq_single a]
    · simp only [Function.update_self]
      ring
    · intro j _ hj
      rw [Function.update_of_ne hj, sub_self]
    · intro h
      exact absurd (mem_univ a) h
  rw [Finset.sum_sub_distrib] at key
  unfold Code.avgLength
  linarith

/-! ### Optimal prefix codes -/

/-- A prefix code of minimal average length for the distribution `p`: the "optimal code" of
SUV Section 7.1.3, p. 216. -/
def IsOptimalPrefixCode [Fintype α] (p : α → ℝ) (c : Code α) : Prop :=
  c.IsPrefixFree ∧ ∀ d : Code α, d.IsPrefixFree → c.avgLength p ≤ d.avgLength p

/-- Optimality is invariant under a simultaneous bijective renaming of the letters and of their
codewords.  SUV Section 7.1.3, p. 216. -/
theorem isOptimalPrefixCode_comp_equiv [Fintype α] {β : Type*} [Fintype β] (σ : β ≃ α)
    {p : α → ℝ} {c : Code α} (hc : IsOptimalPrefixCode p c) :
    IsOptimalPrefixCode (fun b => p (σ b)) (fun b => c (σ b)) := by
  refine ⟨hc.1.comp σ.injective, fun d hd => ?_⟩
  have h := hc.2 (fun a => d (σ.symm a)) (hd.comp σ.symm.injective)
  rw [Code.avgLength_comp_equiv]
  calc c.avgLength p ≤ Code.avgLength (fun a => d (σ.symm a)) p := h
    _ = Code.avgLength (fun b => d (σ.symm (σ b))) (fun b => p (σ b)) :=
      (Code.avgLength_comp_equiv σ _ p).symm
    _ = d.avgLength (fun b => p (σ b)) := by simp

/-- An optimal prefix code exists for every non-negative weight function; the normalisation
`∑ a, p a = 1` of `exists_isOptimalPrefixCode` is not needed for the existence of the minimum.
SUV Section 7.1.3, p. 216. -/
theorem exists_isOptimalPrefixCode_of_nonneg [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) :
    ∃ c : Code α, IsOptimalPrefixCode p c := by
  classical
  let : Encodable α := Fintype.toEncodable α
  have hc₀ : (alphabetCode α).IsPrefixFree := alphabetCode_isPrefixFree
  set M : ℝ := (alphabetCode α).avgLength p with hM
  have hM0 : 0 ≤ M := Code.avgLength_nonneg hp _
  obtain ⟨B, hB⟩ := exists_nat_ge (∑ a, M / p a)
  have hbound : ∀ d : Code α, d.avgLength p ≤ M → ∀ a, 0 < p a → (d a).length ≤ B := by
    intro d hdM a hpa
    have h1 : p a * ((d a).length : ℝ) ≤ d.avgLength p :=
      Finset.single_le_sum (f := fun a => p a * ((d a).length : ℝ))
        (fun a _ => mul_nonneg (hp a) (Nat.cast_nonneg _)) (mem_univ a)
    have h2 : ((d a).length : ℝ) ≤ M / p a := by
      rw [le_div_iff₀ hpa]
      linarith [mul_comm (p a) ((d a).length : ℝ)]
    have h3 : M / p a ≤ ∑ a, M / p a :=
      Finset.single_le_sum (f := fun a => M / p a) (fun a _ => div_nonneg hM0 (hp a)) (mem_univ a)
    exact_mod_cast h2.trans (h3.trans hB)
  let V : Set ℝ := {x | ∃ d : Code α, d.IsPrefixFree ∧ d.avgLength p = x ∧ x ≤ M}
  have hVfin : V.Finite := by
    refine ((Finset.univ : Finset (α → Fin (B + 1))).image
      fun m => ∑ a, p a * ((m a : ℕ) : ℝ)).finite_toSet.subset ?_
    rintro x ⟨d, _, rfl, hdM⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨fun a =>
      if h : 0 < p a then ⟨(d a).length, Nat.lt_succ_of_le (hbound d hdM a h)⟩ else 0,
      mem_univ _, ?_⟩)
    unfold Code.avgLength
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hpa : 0 < p a
    · simp [hpa]
    · have : p a = 0 := le_antisymm (not_lt.1 hpa) (hp a)
      simp [this]
  have hVne : V.Nonempty := ⟨M, alphabetCode α, hc₀, rfl, le_rfl⟩
  obtain ⟨x, ⟨c, hc, rfl, hcM⟩, hmin⟩ := Set.exists_min_image V id hVfin hVne
  refine ⟨c, hc, fun d hd => ?_⟩
  by_cases hdM : d.avgLength p ≤ M
  · exact hmin _ ⟨d, hd, rfl, hdM⟩
  · exact hcM.trans (not_le.1 hdM).le

/-- **An optimal prefix code exists** for every distribution.

The minimum is attained even though infinitely many prefix codes compete: fix the prefix code
whose codewords all have length `n = card α` (its Kraft sum `n·2^{-n}` is at most one), and let
`M` be its average length.  A prefix code that is at least as good gives every letter `a` with
`p a > 0` a codeword of length at most `M / p a`, so only finitely many length vectors have to be
compared on those letters, while the letters of probability zero do not contribute to the average
length at all.

The hypotheses `hp` and `hpsum` say that `p` is a probability distribution, as on p. 216.  They
are not decoration: for a weight function with a negative value the statement is false — for
`α = Unit` and `p = −1`, replacing a codeword by a longer one always decreases the average
length, so no minimum exists.  SUV Section 7.1.3, p. 216. -/
theorem exists_isOptimalPrefixCode [Fintype α] [Nonempty α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) :
    ∃ c : Code α, IsOptimalPrefixCode p c := by
  have _h := hpsum
  exact exists_isOptimalPrefixCode_of_nonneg hp

/-- **The exchange argument.**  In an optimal prefix code a strictly more frequent letter never
gets a strictly longer codeword: otherwise exchanging the two codewords decreases the average
length.  SUV Section 7.1.3, p. 216. -/
theorem length_le_length_of_prob_lt [Fintype α] {p : α → ℝ} {c : Code α}
    (hc : IsOptimalPrefixCode p c) {a b : α} (hab : p a < p b) :
    (c b).length ≤ (c a).length := by
  classical
  by_contra hlt
  push Not at hlt
  have h := hc.2 (fun x => c (Equiv.swap a b x)) (hc.1.comp (Equiv.swap a b).injective)
  rw [Code.avgLength_comp_swap] at h
  have h1 : (p a - p b) * (((c b).length : ℝ) - (c a).length) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (sub_pos.2 (by exact_mod_cast hlt))
  linarith

/-- **Dropping the last bit of a longest codeword.**  If the codeword of `a₀` is `x ++ [b]` with
`x` non-empty, no other codeword is longer than it, and the sibling `x ++ [!b]` is not the
codeword of another letter, then replacing the codeword of `a₀` by `x` keeps the code prefix-free.
This is the shortening step of the two lemmas of p. 216: a longest codeword whose sibling is
unused can be shortened.  SUV Section 7.1.3, p. 216. -/
theorem Code.IsPrefixFree.update_of_sibling_not_mem [DecidableEq α] {c : Code α}
    (hc : c.IsPrefixFree) {a₀ : α} {x : BitString} {b : Bool} (hx : x ≠ [])
    (hc0 : c a₀ = x ++ [b]) (hlen : ∀ a, a ≠ a₀ → (c a).length ≤ x.length + 1)
    (hsib : ∀ a, a ≠ a₀ → c a ≠ x ++ [!b]) : Code.IsPrefixFree (Function.update c a₀ x) := by
  refine ⟨fun a => ?_, fun a a' haa' => ?_⟩
  · by_cases h : a = a₀
    · subst h
      simpa using hx
    · rw [Function.update_of_ne h]
      exact hc.ne_nil a
  · by_cases h : a = a₀
    · subst h
      rw [Function.update_self, Function.update_of_ne (Ne.symm haa')]
      intro hpre
      rcases (hlen a' (Ne.symm haa')).lt_or_eq with hl | hl
      · have hxa : x = c a' := hpre.eq_of_length_le (by omega)
        exact hc.2 a' a (Ne.symm haa') (by rw [← hxa, hc0]; exact List.prefix_append x [b])
      · rcases List.eq_nil_or_concat (c a') with hnil | ⟨y, e, hy⟩
        · exact hc.ne_nil a' hnil
        rw [List.concat_eq_append] at hy
        rw [hy] at hpre hl
        simp only [List.length_append, List.length_singleton] at hl
        have hxy : x = y := by
          rcases List.prefix_concat_iff.1 hpre with h1 | h1
          · have := congrArg List.length h1
            simp at this
            omega
          · exact h1.eq_of_length (by omega)
        subst hxy
        rcases Bool.eq_or_eq_not e b with he | he
        · subst he
          exact Ne.symm haa' (hc.injective (hy.trans hc0.symm))
        · subst he
          exact hsib a' (Ne.symm haa') hy
    · rw [Function.update_of_ne h]
      by_cases h' : a' = a₀
      · subst h'
        rw [Function.update_self]
        intro hpre
        exact hc.2 a a' h (by rw [hc0]; exact hpre.trans (List.prefix_append x [b]))
      · rw [Function.update_of_ne h']
        exact hc.2 a a' haa'

/-- **The two rarest letters have codewords of the same length.**  The letters are numbered in
order of increasing probability (`hmono`, the normalisation `p₁ ≤ … ≤ p_k` of p. 216) and the
codeword lengths of an optimal prefix code are arranged in decreasing order (`hlen`, the
normalisation `n₁ ≥ … ≥ n_k` that the exchange argument makes possible).  If the rarest letter has
positive probability, then `n₁ = n₂`: were `n₁` larger than all the other lengths, the Kraft sum
would leave room to shorten the first codeword.

`hmono` is what makes this the printed statement — the claim is about the two *least frequent*
letters — although the argument just sketched uses only `hlen` and `0 < p 0`.
SUV Section 7.1.3, p. 216. -/
theorem length_zero_eq_length_one_of_isOptimalPrefixCode {k : ℕ} {p : Fin (k + 2) → ℝ}
    (hmono : Monotone p) (hp : 0 < p 0) {c : Code (Fin (k + 2))} (hc : IsOptimalPrefixCode p c)
    (hlen : ∀ i j : Fin (k + 2), i ≤ j → (c j).length ≤ (c i).length) :
    (c 0).length = (c 1).length := by
  have _h := hmono
  by_contra hne
  have hlt : (c 1).length < (c 0).length :=
    lt_of_le_of_ne (hlen 0 1 (Fin.zero_le _)) (Ne.symm hne)
  rcases List.eq_nil_or_concat (c 0) with h0 | ⟨x, b, hx⟩
  · exact hc.1.ne_nil 0 h0
  rw [List.concat_eq_append] at hx
  have hxlen : (c 0).length = x.length + 1 := by
    rw [hx]
    simp
  have hj : ∀ j, j ≠ 0 → (c j).length < (c 0).length := fun j hj =>
    lt_of_le_of_lt (hlen 1 j (Fin.one_le_of_ne_zero hj)) hlt
  have hxne : x ≠ [] := by
    intro hxnil
    have := hc.1.one_le_length 1
    rw [hxnil] at hxlen
    simp at hxlen
    omega
  have hd := hc.1.update_of_sibling_not_mem hxne hx (fun j hj0 => by have := hj j hj0; omega)
    (fun j hj0 heq => by
      have := hj j hj0
      rw [heq] at this
      simp at this
      omega)
  have hle := hc.2 _ hd
  rw [Code.avgLength_update, hxlen] at hle
  push_cast at hle
  nlinarith

/-! ### The Huffman recursion -/

/-- The distribution obtained by merging the two rarest letters `0` and `1` of `p` into a single
letter of probability `p 0 + p 1`, which becomes the letter `0` of the smaller alphabet.
SUV Section 7.1.3, p. 216. -/
def mergeDist {k : ℕ} (p : Fin (k + 2) → ℝ) : Fin (k + 1) → ℝ :=
  Fin.cases (motive := fun _ => ℝ) (p 0 + p 1) fun i : Fin k => p i.succ.succ

/-- The merged letter carries the two smallest probabilities.  SUV Section 7.1.3, p. 216. -/
@[simp] theorem mergeDist_zero {k : ℕ} (p : Fin (k + 2) → ℝ) : mergeDist p 0 = p 0 + p 1 := rfl

/-- The other letters keep their probabilities.  SUV Section 7.1.3, p. 216. -/
@[simp] theorem mergeDist_succ {k : ℕ} (p : Fin (k + 2) → ℝ) (i : Fin k) :
    mergeDist p i.succ = p i.succ.succ := rfl

/-- The merged distribution is non-negative when `p` is.  SUV Section 7.1.3, p. 216. -/
theorem mergeDist_nonneg {k : ℕ} {p : Fin (k + 2) → ℝ} (hp : ∀ i, 0 ≤ p i) (i : Fin (k + 1)) :
    0 ≤ mergeDist p i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact add_nonneg (hp 0) (hp 1)
  · exact hp _

/-- Merging two letters preserves the total weight.  SUV Section 7.1.3, p. 216. -/
theorem sum_mergeDist {k : ℕ} (p : Fin (k + 2) → ℝ) : ∑ i, mergeDist p i = ∑ i, p i := by
  simp only [Fin.sum_univ_succ, mergeDist_zero, mergeDist_succ, Fin.succ_zero_eq_one]
  ring

/-- The code obtained from a code for the merged alphabet by replacing the codeword `x` of the
merged letter with the two codewords `x0` and `x1`: this is the step of Huffman's algorithm.
SUV Section 7.1.3, p. 217. -/
def huffmanSplit {k : ℕ} (c : Code (Fin (k + 1))) : Code (Fin (k + 2)) :=
  Fin.cases (motive := fun _ => BitString) (c 0 ++ [false])
    (Fin.cases (motive := fun _ => BitString) (c 0 ++ [true]) fun i : Fin k => c i.succ)

/-- The first letter of the split gets `x0`.  SUV Section 7.1.3, p. 217. -/
@[simp] theorem huffmanSplit_zero {k : ℕ} (c : Code (Fin (k + 1))) :
    huffmanSplit c 0 = c 0 ++ [false] := rfl

/-- The second letter of the split gets `x1`.  SUV Section 7.1.3, p. 217. -/
@[simp] theorem huffmanSplit_one {k : ℕ} (c : Code (Fin (k + 1))) :
    huffmanSplit c 1 = c 0 ++ [true] := by
  rw [← Fin.succ_zero_eq_one]
  rfl

/-- The other letters keep their codewords.  SUV Section 7.1.3, p. 217. -/
@[simp] theorem huffmanSplit_succ_succ {k : ℕ} (c : Code (Fin (k + 1))) (i : Fin k) :
    huffmanSplit c i.succ.succ = c i.succ := rfl

/-- The average length of the split code is that of the merged code plus the merged probability
`p 0 + p 1`, since the codewords of the letters `0` and `1` are one bit longer than the codeword
of the merged letter.  SUV Section 7.1.3, p. 217. -/
theorem avgLength_huffmanSplit {k : ℕ} (c : Code (Fin (k + 1))) (p : Fin (k + 2) → ℝ) :
    (huffmanSplit c).avgLength p = c.avgLength (mergeDist p) + (p 0 + p 1) := by
  simp only [Code.avgLength, Fin.sum_univ_succ, Fin.succ_zero_eq_one, huffmanSplit_zero,
    huffmanSplit_one, huffmanSplit_succ_succ, mergeDist_zero, mergeDist_succ, List.length_append,
    List.length_singleton]
  push_cast
  ring

/-- Splitting a codeword of a prefix code into its two extensions gives a prefix code.
SUV Section 7.1.3, p. 217. -/
theorem Code.IsPrefixFree.huffmanSplit {k : ℕ} {c : Code (Fin (k + 1))} (hc : c.IsPrefixFree) :
    (huffmanSplit c).IsPrefixFree := by
  have hne : ∀ (u : BitString) (b : Bool), u ++ [b] ≠ [] := fun u b => by simp
  have h01 : ∀ (u : BitString) (b b' : Bool), b ≠ b' → ¬ (u ++ [b] <+: u ++ [b']) := by
    intro u b b' hbb' h
    rcases List.prefix_concat_iff.1 h with h | h
    · exact hbb' (by simpa using List.append_cancel_left h)
    · have := h.length_le
      simp at this
  have hsucc : ∀ (u : BitString) (b : Bool) (i : Fin k), ¬ (c 0 ++ [b] <+: c i.succ) ∧
      ¬ (c i.succ <+: c 0 ++ [b]) := by
    intro u b i
    have h0 := hc.2 0 i.succ (Fin.succ_ne_zero i).symm
    have h1 := hc.2 i.succ 0 (Fin.succ_ne_zero i)
    refine ⟨fun h => h0 ((List.prefix_append _ _).trans h), fun h => ?_⟩
    rcases List.prefix_concat_iff.1 h with h | h
    · exact h0 (by rw [h]; exact List.prefix_append _ _)
    · exact h1 h
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact hne _ _
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact hne _ _
      · exact hc.ne_nil _
  · refine Fin.cases ?_ (fun i => ?_) i hij
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact absurd rfl h
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          simp only [huffmanSplit_zero, Fin.succ_zero_eq_one, huffmanSplit_one]
          exact h01 _ _ _ (by decide)
        · intro _
          simp only [huffmanSplit_zero, huffmanSplit_succ_succ]
          exact (hsucc [] false j).1
    · refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          simp only [huffmanSplit_zero, Fin.succ_zero_eq_one, huffmanSplit_one]
          exact h01 _ _ _ (by decide)
        · refine Fin.cases ?_ (fun j => ?_) j
          · intro h
            exact absurd rfl h
          · intro _
            simp only [Fin.succ_zero_eq_one, huffmanSplit_one, huffmanSplit_succ_succ]
            exact (hsucc [] true j).1
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          simp only [huffmanSplit_zero, huffmanSplit_succ_succ]
          exact (hsucc [] false i).2
        · refine Fin.cases ?_ (fun j => ?_) j
          · intro _
            simp only [Fin.succ_zero_eq_one, huffmanSplit_one, huffmanSplit_succ_succ]
            exact (hsucc [] true i).2
          · intro h
            simp only [huffmanSplit_succ_succ]
            exact hc.2 _ _ fun e => h (by rw [e])

/-- **No codeword extends the common stem of two sibling codewords.**  If `x ++ [0]` and
`x ++ [1]` are codewords of the letters `a₀` and `a₁` of a prefix code, then `x` is not a prefix
of the codeword of any third letter: such a codeword would extend `x` by a bit and thereby have
`x0` or `x1` as a prefix, or be `x` itself and be a prefix of them.  SUV Section 7.1.3, p. 217. -/
theorem Code.IsPrefixFree.not_prefix_of_sibling {c : Code α} (hc : c.IsPrefixFree) {a₀ a₁ : α}
    {x : BitString} (hsib : ∀ e : Bool, x ++ [e] = c a₀ ∨ x ++ [e] = c a₁) {j : α} (hj0 : j ≠ a₀)
    (hj1 : j ≠ a₁) : ¬ x <+: c j := by
  rintro ⟨rest, hrest⟩
  cases rest with
  | nil =>
    rw [List.append_nil] at hrest
    rcases hsib true with h | h
    · exact hc.2 j a₀ hj0 (by rw [← hrest, ← h]; exact List.prefix_append _ _)
    · exact hc.2 j a₁ hj1 (by rw [← hrest, ← h]; exact List.prefix_append _ _)
  | cons e rest' =>
    have hpre : x ++ [e] <+: c j := ⟨rest', by rw [← hrest]; simp⟩
    rcases hsib e with h | h
    · exact hc.2 a₀ j (Ne.symm hj0) (h ▸ hpre)
    · exact hc.2 a₁ j (Ne.symm hj1) (h ▸ hpre)

/-- Exchanging the codewords of a rarer letter `i` and a more frequent letter `j` whose codeword
is at least as long keeps an optimal prefix code optimal: the exchange argument in its
non-strict form.  SUV Section 7.1.3, p. 216. -/
theorem isOptimalPrefixCode_comp_swap [Fintype α] [DecidableEq α] [Preorder α] {p : α → ℝ}
    (hmono : Monotone p) {d : Code α} (hd : IsOptimalPrefixCode p d) {i j : α} (hij : i ≤ j)
    (hlen : (d i).length ≤ (d j).length) :
    IsOptimalPrefixCode p (fun x => d (Equiv.swap i j x)) := by
  refine ⟨hd.1.comp (Equiv.swap i j).injective, fun e he => ?_⟩
  rw [Code.avgLength_comp_swap]
  have h1 : (p i - p j) * (((d j).length : ℝ) - (d i).length) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hmono hij])
      (sub_nonneg.2 (by exact_mod_cast hlen))
  linarith [hd.2 e he]

/-- The code obtained from a code on `k + 3` letters whose letters `0` and `1` carry the sibling
codewords `x0` and `x1` by merging the two letters into one with the codeword `x`: the inverse of
`huffmanSplit`, used to compare an optimal code for `p` with the codes for the merged
distribution.  SUV Section 7.1.3, p. 217. -/
def mergeCode {k : ℕ} (d : Code (Fin (k + 3))) (x : BitString) : Code (Fin (k + 2)) :=
  Fin.cases (motive := fun _ => BitString) x fun i : Fin (k + 1) => d i.succ.succ

/-- The merged letter gets the common stem `x`.  SUV Section 7.1.3, p. 217. -/
@[simp] theorem mergeCode_zero {k : ℕ} (d : Code (Fin (k + 3))) (x : BitString) :
    mergeCode d x 0 = x := rfl

/-- The other letters keep their codewords.  SUV Section 7.1.3, p. 217. -/
@[simp] theorem mergeCode_succ {k : ℕ} (d : Code (Fin (k + 3))) (x : BitString)
    (i : Fin (k + 1)) : mergeCode d x i.succ = d i.succ.succ := rfl

/-- Splitting the merged code recovers the codeword lengths of the original code.
SUV Section 7.1.3, p. 217. -/
theorem length_huffmanSplit_mergeCode {k : ℕ} {d : Code (Fin (k + 3))} {x : BitString} {b : Bool}
    (h0 : d 0 = x ++ [b]) (h1 : d 1 = x ++ [!b]) (i : Fin (k + 3)) :
    (huffmanSplit (mergeCode d x) i).length = (d i).length := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [h0]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp [Fin.succ_zero_eq_one, h1]
    · rfl

/-- Merging two sibling codewords of a prefix code gives a prefix code.
SUV Section 7.1.3, p. 217. -/
theorem Code.IsPrefixFree.mergeCode {k : ℕ} {d : Code (Fin (k + 3))} (hd : d.IsPrefixFree)
    {x : BitString} {b : Bool} (h0 : d 0 = x ++ [b]) (h1 : d 1 = x ++ [!b]) :
    (mergeCode d x).IsPrefixFree := by
  have hsib : ∀ e : Bool, x ++ [e] = d 0 ∨ x ++ [e] = d 1 := by
    intro e
    rcases Bool.eq_or_eq_not e b with h | h
    · exact Or.inl (by rw [h, h0])
    · exact Or.inr (by rw [h, h1])
  have hnp : ∀ i : Fin (k + 1), ¬ x <+: d i.succ.succ := fun i =>
    hd.not_prefix_of_sibling hsib (Fin.succ_ne_zero _)
      (by rw [← Fin.succ_zero_eq_one]; exact fun h => Fin.succ_ne_zero _ (Fin.succ_inj.1 h))
  have hxne : x ≠ [] := fun h => hnp 0 (h ▸ List.nil_prefix)
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact hxne
    · exact hd.ne_nil _
  · refine Fin.cases ?_ (fun i => ?_) i hij
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact absurd rfl h
      · intro _
        exact hnp j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _ h
        exact hd.2 _ _ (Fin.succ_ne_zero _) (by rw [h0]; exact h.trans (List.prefix_append _ _))
      · intro h
        exact hd.2 _ _ fun e => h (Fin.succ_inj.1 e)

/-- **The split of an optimal code for the merged alphabet is at least as good as every prefix
code**, once the argument of pp. 216–217 has produced, from some optimal prefix code for `p`, one
whose two rarest letters `0` and `1` carry sibling codewords `x0`, `x1`.  Among the optimal codes
one of minimal total codeword length is chosen; two exchanges give the letters `0` and `1` the
two longest codewords, and if the sibling of the codeword of `0` is unused, dropping the last bit
would give an optimal code of smaller total length.  SUV Section 7.1.3, pp. 216–217. -/
theorem exists_isPrefixFree_avgLength_huffmanSplit_le {k : ℕ} {p : Fin (k + 3) → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hmono : Monotone p) :
    ∃ e : Code (Fin (k + 2)), e.IsPrefixFree ∧
      ∀ d : Code (Fin (k + 3)), d.IsPrefixFree → (huffmanSplit e).avgLength p ≤ d.avgLength p := by
  classical
  obtain ⟨d₀, hd₀⟩ := exists_isOptimalPrefixCode_of_nonneg hp
  have hex : ∃ n : ℕ, ∃ d : Code (Fin (k + 3)), IsOptimalPrefixCode p d ∧
      ∑ i, (d i).length = n := ⟨_, d₀, hd₀, rfl⟩
  obtain ⟨d, hd, hdn⟩ := Nat.find_spec hex
  have hmin : ∀ d' : Code (Fin (k + 3)), IsOptimalPrefixCode p d' →
      ∑ i, (d i).length ≤ ∑ i, (d' i).length :=
    fun d' hd' => hdn ▸ Nat.find_min' hex ⟨d', hd', rfl⟩
  -- the letter `0` gets a longest codeword
  obtain ⟨a, ha⟩ := Finite.exists_max fun i => (d i).length
  set d₁ : Code (Fin (k + 3)) := fun y => d (Equiv.swap 0 a y) with hd₁
  have hd₁opt : IsOptimalPrefixCode p d₁ :=
    isOptimalPrefixCode_comp_swap hmono hd (Fin.zero_le a) (ha 0)
  have hd₁tot : ∑ i, (d₁ i).length = ∑ i, (d i).length :=
    Equiv.sum_comp (Equiv.swap 0 a) fun i => (d i).length
  have hd₁max : ∀ j, (d₁ j).length ≤ (d₁ 0).length := by
    intro j
    simp only [hd₁, Equiv.swap_apply_left]
    exact ha _
  -- the letter `1` gets a longest codeword among the remaining ones
  obtain ⟨b, hb⟩ := Finite.exists_max fun i : Fin (k + 2) => (d₁ i.succ).length
  set d₂ : Code (Fin (k + 3)) := fun y => d₁ (Equiv.swap 1 b.succ y) with hd₂
  have hd₂opt : IsOptimalPrefixCode p d₂ :=
    isOptimalPrefixCode_comp_swap hmono hd₁opt (Fin.one_le_of_ne_zero (Fin.succ_ne_zero b))
      (by rw [← Fin.succ_zero_eq_one]; exact hb 0)
  have hd₂tot : ∑ i, (d₂ i).length = ∑ i, (d i).length :=
    (Equiv.sum_comp (Equiv.swap 1 b.succ) fun i => (d₁ i).length).trans hd₁tot
  have hd₂0 : d₂ 0 = d₁ 0 := by
    simp only [hd₂]
    rw [Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one (Fin.succ_ne_zero b).symm]
  have hd₂max : ∀ j, (d₂ j).length ≤ (d₂ 0).length := by
    intro j
    rw [hd₂0]
    exact hd₁max _
  have hd₂max1 : ∀ i : Fin (k + 2), (d₂ i.succ).length ≤ (d₂ 1).length := by
    intro i
    simp only [hd₂, Equiv.swap_apply_left]
    by_cases hi1 : i.succ = 1
    · rw [hi1, Equiv.swap_apply_left]
    by_cases hib : i.succ = b.succ
    · rw [hib, Equiv.swap_apply_right, ← Fin.succ_zero_eq_one]
      exact hb 0
    · rw [Equiv.swap_apply_of_ne_of_ne hi1 hib]
      exact hb i
  -- the codeword of `0` is `x ++ [bit]`
  rcases List.eq_nil_or_concat (d₂ 0) with h0 | ⟨x, bit, hx⟩
  · exact absurd h0 (hd₂opt.1.ne_nil 0)
  rw [List.concat_eq_append] at hx
  have hxlen : (d₂ 0).length = x.length + 1 := by
    rw [hx]
    simp
  by_cases hsib : ∃ j, d₂ j = x ++ [!bit]
  · -- the sibling `x ++ [!bit]` is a codeword: bring it to the letter `1` and merge
    obtain ⟨j, hj⟩ := hsib
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [hx] at hj
      simpa using List.append_cancel_left hj
    obtain ⟨i, rfl⟩ : ∃ i : Fin (k + 2), j = i.succ := ⟨j.pred hj0, (Fin.succ_pred j hj0).symm⟩
    have hjlen : (d₂ i.succ).length = x.length + 1 := by
      rw [hj]
      simp
    have hlenj : (d₂ i.succ).length = (d₂ 1).length :=
      le_antisymm (hd₂max1 i) (by rw [hjlen, ← hxlen]; exact hd₂max 1)
    set d₃ : Code (Fin (k + 3)) := fun y => d₂ (Equiv.swap 1 i.succ y) with hd₃
    have hd₃opt : IsOptimalPrefixCode p d₃ :=
      isOptimalPrefixCode_comp_swap hmono hd₂opt (Fin.one_le_of_ne_zero (Fin.succ_ne_zero i))
        hlenj.ge
    have hd₃0 : d₃ 0 = x ++ [bit] := by
      simp only [hd₃]
      rw [Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one (Fin.succ_ne_zero i).symm, hx]
    have hd₃1 : d₃ 1 = x ++ [!bit] := by
      simp only [hd₃]
      rw [Equiv.swap_apply_left, hj]
    refine ⟨mergeCode d₃ x, hd₃opt.1.mergeCode hd₃0 hd₃1, fun d' hd' => ?_⟩
    rw [Code.avgLength_congr p (length_huffmanSplit_mergeCode hd₃0 hd₃1)]
    exact hd₃opt.2 d' hd'
  · -- the sibling is unused: dropping the last bit contradicts the minimal total length
    push Not at hsib
    exfalso
    have hxne : x ≠ [] := by
      intro hxnil
      subst hxnil
      have h1 : (d₂ 1).length ≤ 1 := by
        have := hd₂max 1
        rw [hxlen] at this
        simpa using this
      obtain ⟨e, he⟩ := List.length_eq_one_iff.1 (le_antisymm h1 (hd₂opt.1.one_le_length 1))
      rcases Bool.eq_or_eq_not e bit with h | h
      · subst h
        exact Fin.zero_ne_one (hd₂opt.1.injective (hx.trans he.symm))
      · subst h
        exact hsib 1 (by rw [he]; rfl)
    have hd'' := hd₂opt.1.update_of_sibling_not_mem hxne hx
      (fun j _ => by have := hd₂max j; omega) (fun j _ => hsib j)
    have hopt : IsOptimalPrefixCode p (Function.update d₂ 0 x) := by
      refine ⟨hd'', fun d' hd' => ?_⟩
      have h1 := hd₂opt.2 d' hd'
      have h2 : p 0 * ((x.length : ℝ) - ((x.length : ℝ) + 1)) = -p 0 := by ring
      rw [Code.avgLength_update, hxlen]
      push_cast
      linarith [hp 0]
    have htot := hmin _ hopt
    have hsum : ∑ i, (Function.update d₂ 0 x i).length + 1 = ∑ i, (d₂ i).length := by
      simp only [Fin.sum_univ_succ, Function.update_self,
        Function.update_of_ne (Fin.succ_ne_zero _), hxlen]
      omega
    omega

/-- **The induction step of Huffman's algorithm.**  If the two rarest letters of `p` (the letters
`0` and `1`, since `p` is in increasing order) are merged and `c` is an optimal prefix code for the
merged distribution, then splitting the codeword of the merged letter into `x0` and `x1` gives an
optimal prefix code for `p`.

The alphabet has at least three letters and the merged alphabet at least two, which is where the
step is used by `isOptimalPrefixCode_of_isHuffmanCode`; with the non-empty-codeword repair of
`Code.IsPrefixFree` the step is *false* for the smallest case of two letters merged into one,
where the optimal code for the single letter is one bit long and splitting it gives two codewords
of length two rather than the optimal `0`, `1`.  SUV Section 7.1.3, pp. 216–217. -/
theorem isOptimalPrefixCode_huffmanSplit {k : ℕ} {p : Fin (k + 3) → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hmono : Monotone p) {c : Code (Fin (k + 2))} (hc : IsOptimalPrefixCode (mergeDist p) c) :
    IsOptimalPrefixCode p (huffmanSplit c) := by
  obtain ⟨e, he, hle⟩ := exists_isPrefixFree_avgLength_huffmanSplit_le hp hmono
  refine ⟨hc.1.huffmanSplit, fun d hd => ?_⟩
  calc (huffmanSplit c).avgLength p = c.avgLength (mergeDist p) + (p 0 + p 1) :=
        avgLength_huffmanSplit c p
    _ ≤ e.avgLength (mergeDist p) + (p 0 + p 1) := by linarith [hc.2 e he]
    _ = (huffmanSplit e).avgLength p := (avgLength_huffmanSplit e p).symm
    _ ≤ d.avgLength p := hle d hd

/-! ### The Huffman code -/

/-- **The Huffman codes** of a distribution `p` on `Fin k`: the codes produced by the recursive
algorithm of p. 217, written as an inductive relation.

* `one`, `two` — the base of the recursion: for one letter the codeword is a single bit, and for
  two letters the codewords are the two strings of length one.  The book's recursion goes down to
  one letter and uses the empty codeword there; with the non-empty-codeword repair of
  `Code.IsPrefixFree` the two-letter base case takes over, and for `k ≥ 2` the codes obtained are
  the same.
* `reorder` — "rearranging the letters, we may assume that `p₁ ≤ p₂ ≤ … ≤ p_k`" (p. 216): the
  relation is invariant under a simultaneous permutation of the letters and of their codewords.
* `merge` — the three steps of p. 217: combine the two rarest letters `0` and `1` of an increasing
  `p` into one (`mergeDist`), find a Huffman code for the resulting `k − 1` probabilities, and
  replace the codeword `x` of the merged letter by `x0` and `x1` (`huffmanSplit`).

SUV Section 7.1.3, pp. 216–217. -/
inductive IsHuffmanCode : {k : ℕ} → (Fin k → ℝ) → Code (Fin k) → Prop
  /-- One letter: its codeword is a single bit. -/
  | one (p : Fin 1 → ℝ) (c : Code (Fin 1)) (h : (c 0).length = 1) : IsHuffmanCode p c
  /-- Two letters: the two codewords are the two distinct strings of length one. -/
  | two (p : Fin 2 → ℝ) (c : Code (Fin 2)) (h0 : (c 0).length = 1) (h1 : (c 1).length = 1)
      (hne : c 0 ≠ c 1) : IsHuffmanCode p c
  /-- Rearranging the letters (and their codewords along with them). -/
  | reorder {k : ℕ} (σ : Equiv.Perm (Fin k)) (p : Fin k → ℝ) (c : Code (Fin k))
      (h : IsHuffmanCode (fun i => p (σ i)) (fun i => c (σ i))) : IsHuffmanCode p c
  /-- Merge the two rarest letters, recurse, and split the codeword of the merged letter. -/
  | merge {k : ℕ} (p : Fin (k + 3) → ℝ) (hmono : Monotone p) (c : Code (Fin (k + 2)))
      (h : IsHuffmanCode (mergeDist p) c) : IsHuffmanCode p (huffmanSplit c)

/-- A code whose codewords all have length one and are pairwise distinct is an optimal prefix
code for every non-negative weight function: no prefix code has a codeword shorter than one bit.
This covers the two base cases of Huffman's recursion.  SUV Section 7.1.3, p. 217. -/
theorem isOptimalPrefixCode_of_length_eq_one [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    {c : Code α} (hinj : Function.Injective c) (hlen : ∀ a, (c a).length = 1) :
    IsOptimalPrefixCode p c := by
  refine ⟨⟨fun a h => by simpa [h] using hlen a, fun a b hab hpre => hab (hinj ?_)⟩,
    fun d hd => ?_⟩
  · exact hpre.eq_of_length (by rw [hlen, hlen])
  · exact Code.avgLength_le_avgLength_of_length_le hp fun a =>
      (hlen a).symm ▸ hd.one_le_length a

/-- **Huffman's algorithm produces an optimal prefix code**: every Huffman code for a probability
distribution `p` has minimal average length among all prefix codes for `p`.  This is the claim of
p. 217 that "the optimal code constructed by this algorithm is called the Huffman code".
SUV Section 7.1.3, pp. 216–217. -/
theorem isOptimalPrefixCode_of_isHuffmanCode {k : ℕ} {p : Fin k → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) {c : Code (Fin k)} (h : IsHuffmanCode p c) :
    IsOptimalPrefixCode p c := by
  have _h := hpsum
  clear hpsum _h
  induction h with
  | one p c h =>
    exact isOptimalPrefixCode_of_length_eq_one hp (fun a b _ => Subsingleton.elim a b)
      fun a => by rw [Subsingleton.elim a 0, h]
  | two p c h0 h1 hne =>
    refine isOptimalPrefixCode_of_length_eq_one hp ?_ ?_
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab hne
      · exact absurd hab.symm hne
      · rfl
    · rw [Fin.forall_fin_two]
      exact ⟨h0, h1⟩
  | reorder σ p c _ ih =>
    have := isOptimalPrefixCode_comp_equiv σ.symm (ih fun i => hp (σ i))
    simpa using this
  | merge p hmono c _ ih =>
    exact isOptimalPrefixCode_huffmanSplit hp hmono (ih (mergeDist_nonneg hp))

/-- **Huffman's algorithm produces a code.**  For every weight vector on a non-empty alphabet
`Fin (k + 1)` there is a Huffman code: "the recursive algorithm that finds the optimal prefix
code" of p. 217 always terminates.  Without this statement
`isOptimalPrefixCode_of_isHuffmanCode` would be a claim about a possibly empty relation.

The constructors of `IsHuffmanCode` cover the non-empty alphabets and only those: `one` gives a
code for `Fin 1` and `two` one for `Fin 2`, while for `k + 3` letters `reorder` sorts the letters
(some permutation makes any `p` monotone) and `merge` then reduces to `k + 2` letters, so the
recursion ends at the two base cases.  For the empty alphabet the relation is empty — the only
constructor whose alphabet can be `Fin 0` is `reorder`, which again asks for a code on `Fin 0`,
so no derivation grounds out — and nothing is lost by it, because an empty alphabet carries no
distribution (`∑ i : Fin 0, p i = 0 ≠ 1`).  No hypothesis on `p` is needed: the algorithm runs on
arbitrary weights, and only its optimality needs a distribution.
SUV Section 7.1.3, pp. 216–217. -/
theorem exists_isHuffmanCode {k : ℕ} (p : Fin (k + 1) → ℝ) :
    ∃ c : Code (Fin (k + 1)), IsHuffmanCode p c := by
  induction k with
  | zero => exact ⟨fun _ => [false], .one p _ rfl⟩
  | succ k ih =>
    cases k with
    | zero => exact ⟨![[false], [true]], .two p _ rfl rfl (by simp)⟩
    | succ k =>
      obtain ⟨c, hc⟩ := ih (mergeDist (p ∘ Tuple.sort p))
      refine ⟨fun i => huffmanSplit c ((Tuple.sort p).symm i), .reorder (Tuple.sort p) p _ ?_⟩
      have : (fun i => huffmanSplit c ((Tuple.sort p).symm (Tuple.sort p i))) = huffmanSplit c :=
        funext fun i => by simp
      rw [this]
      exact .merge _ (Tuple.monotone_sort p) c hc

/-- **Huffman's algorithm finds an optimal prefix code.**  The claim of p. 217 in full: for every
distribution on a non-empty alphabet the algorithm produces a code, and the code it produces has
minimal average length among all prefix codes.  This is `exists_isHuffmanCode` together with
`isOptimalPrefixCode_of_isHuffmanCode`.  SUV Section 7.1.3, pp. 216–217. -/
theorem exists_isHuffmanCode_isOptimalPrefixCode {k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    ∃ c : Code (Fin (k + 1)), IsHuffmanCode p c ∧ IsOptimalPrefixCode p c :=
  let ⟨c, hc⟩ := exists_isHuffmanCode p
  ⟨c, hc, isOptimalPrefixCode_of_isHuffmanCode hp hpsum hc⟩

end Kolmogorov
