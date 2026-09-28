import KolmogorovMathlib.MonotoneComplexity.GacsDayGame

/-!
# Fixed-width block encoding of Gács–Day tree nodes

The Gács–Day game (Theorem 88) is played on a tree of depth `O(d)` with branching
factor `2 ^ ((C * d) ^ (C * d))`.  Embedding that game into the *binary* tree
replaces every branch index by a block of `m` bits, so a node
`x : GacsDayNode = List ℕ` becomes the bit string `fixedWidthBlocks m x`.

This file supplies the elementary scaffolding for that embedding:

* `branch_le_two_pow_ceilLog` : a branching factor `b` fits in `Nat.log2 b + 1` bits;
* `natBlock` / `fixedWidthBlocks` : the fixed-width block code and its length;
* `fixedWidthBlocks_inj`, `blockEncode_append_inj` : injectivity of the code;
* `fixedWidthBlocks_prefix_iff` : the code is prefix-faithful, i.e. it maps the
  tree order to the prefix order (and hence incomparable nodes to incomparable,
  therefore disjoint, cylinders).

Note on hypotheses: a fixed-width block code is *not* self-delimiting, so the
naive statement `fixedWidthBlocks m a ++ p = fixedWidthBlocks m b ++ q → a = b`
is false (for `m = 1`, `a = [0]`, `p = [true]`, `b = [0, 1]`, `q = []` both sides
are `[false, true]`).  The correct hypotheses are either that the two nodes sit
at the same tree depth (`a.length = b.length`), which is how the embedding uses
it, or that the encoded strings have equal length; both variants are provided.
-/

namespace Kolmogorov

/-- A branching factor `b` can be encoded in `Nat.log2 b + 1` bits. -/
lemma branch_le_two_pow_ceilLog (b : ℕ) : b ≤ 2 ^ (Nat.log2 b + 1) := by
  rcases Nat.eq_zero_or_pos b with rfl | _
  · simp
  · rw [Nat.log2_eq_log_two]
    exact le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) b)

/-- The `m`-bit block (least significant bit first) of the natural number `n`. -/
def natBlock (m n : ℕ) : BitString := (List.range m).map (fun i => n.testBit i)

/-- `natBlock m n` is a block of exactly `m` bits. -/
@[simp] lemma natBlock_length (m n : ℕ) : (natBlock m n).length = m := by
  simp [natBlock]

/-- Numbers below `2 ^ m` are determined by their `m`-bit block. -/
lemma natBlock_inj {m n1 n2 : ℕ} (h1 : n1 < 2 ^ m) (h2 : n2 < 2 ^ m)
    (h : natBlock m n1 = natBlock m n2) : n1 = n2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · have hgi := congrArg (fun l => l[i]?) h
    simpa [natBlock, List.getElem?_map, List.getElem?_range, hi] using hgi
  · push_neg at hi
    have hp : (2 : ℕ) ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h1 hp),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h2 hp)]

/-- The binary encoding of a Gács–Day node: each branch index becomes an
`m`-bit block, and the blocks are concatenated. -/
def fixedWidthBlocks (m : ℕ) (x : GacsDayNode) : BitString := (x.map (natBlock m)).flatten

/-- The fixed-width encoding of the empty node is empty. -/
@[simp] lemma fixedWidthBlocks_nil (m : ℕ) : fixedWidthBlocks m [] = [] := rfl

/-- The fixed-width encoding of a node emits the `m`-bit block of its first entry, followed by
the encoding of the rest. -/
lemma fixedWidthBlocks_cons (m : ℕ) (a : ℕ) (x : GacsDayNode) :
    fixedWidthBlocks m (a :: x) = natBlock m a ++ fixedWidthBlocks m x := by
  simp [fixedWidthBlocks]

/-- The fixed-width encoding turns concatenation of nodes into concatenation of bit strings. -/
lemma fixedWidthBlocks_append (m : ℕ) (x y : GacsDayNode) :
    fixedWidthBlocks m (x ++ y) = fixedWidthBlocks m x ++ fixedWidthBlocks m y := by
  simp [fixedWidthBlocks]

/-- The fixed-width encoding of a node of length `n` has exactly `m * n` bits. -/
@[simp] lemma fixedWidthBlocks_length (m : ℕ) (x : GacsDayNode) :
    (fixedWidthBlocks m x).length = m * x.length := by
  induction x with
  | nil => simp
  | cons a t ih =>
      simp only [fixedWidthBlocks_cons, List.length_append, natBlock_length, ih,
        List.length_cons, Nat.mul_succ]
      omega

/-- Nodes of the same depth with branch indices below `2 ^ m` are determined by
their block encodings. -/
lemma fixedWidthBlocks_inj {m : ℕ} {a b : GacsDayNode}
    (ha : ∀ i ∈ a, i < 2 ^ m) (hb : ∀ i ∈ b, i < 2 ^ m) (hlen : a.length = b.length)
    (h : fixedWidthBlocks m a = fixedWidthBlocks m b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons y t => simp at hlen
  | cons x s ih =>
      cases b with
      | nil => simp at hlen
      | cons y t =>
          rw [fixedWidthBlocks_cons, fixedWidthBlocks_cons] at h
          obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
          have hxy : x = y := natBlock_inj (ha x (by simp)) (hb y (by simp)) h1
          subst hxy
          have hst : s = t :=
            ih (fun i hi => ha i (by simp [hi])) (fun i hi => hb i (by simp [hi]))
              (by simpa using hlen) h2
          simp [hst]

/-- With a positive block width the depth of a node is recoverable from its
encoding, so injectivity needs no depth hypothesis. -/
lemma fixedWidthBlocks_inj_of_pos {m : ℕ} (hm : 0 < m) {a b : GacsDayNode}
    (ha : ∀ i ∈ a, i < 2 ^ m) (hb : ∀ i ∈ b, i < 2 ^ m)
    (h : fixedWidthBlocks m a = fixedWidthBlocks m b) : a = b := by
  have hlen : a.length = b.length := by
    have := congrArg List.length h
    simp only [fixedWidthBlocks_length] at this
    exact Nat.eq_of_mul_eq_mul_left hm this
  exact fixedWidthBlocks_inj ha hb hlen h

/-- Prefix/injectivity form used when parsing a block-encoded node off the front
of a bit string: at a fixed depth the encoding of the node and the remaining
suffix are both determined. -/
lemma blockEncode_append_inj {m : ℕ} {a b : GacsDayNode} {p q : BitString}
    (ha : ∀ i ∈ a, i < 2 ^ m) (hb : ∀ i ∈ b, i < 2 ^ m) (hlen : a.length = b.length)
    (h : fixedWidthBlocks m a ++ p = fixedWidthBlocks m b ++ q) : a = b ∧ p = q := by
  have hlen' : (fixedWidthBlocks m a).length = (fixedWidthBlocks m b).length := by
    simp [hlen]
  obtain ⟨h1, h2⟩ := List.append_inj h hlen'
  exact ⟨fixedWidthBlocks_inj ha hb hlen h1, h2⟩

/-- The block encoding is monotone for the prefix (tree) order. -/
lemma fixedWidthBlocks_prefix_of_prefix {m : ℕ} {a b : GacsDayNode} (h : a <+: b) :
    fixedWidthBlocks m a <+: fixedWidthBlocks m b := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨fixedWidthBlocks m z, (fixedWidthBlocks_append m a z).symm⟩

/-- With a positive block width the encoding is prefix-*faithful*: one node is an
ancestor of another exactly when its code is a prefix of the other's code. -/
lemma fixedWidthBlocks_prefix_iff {m : ℕ} (hm : 0 < m) {a b : GacsDayNode}
    (ha : ∀ i ∈ a, i < 2 ^ m) (hb : ∀ i ∈ b, i < 2 ^ m) :
    fixedWidthBlocks m a <+: fixedWidthBlocks m b ↔ a <+: b := by
  refine ⟨?_, fixedWidthBlocks_prefix_of_prefix⟩
  intro h
  have hle : a.length ≤ b.length := by
    have := h.length_le
    simp only [fixedWidthBlocks_length] at this
    exact Nat.le_of_mul_le_mul_left this hm
  have hsplit : b.take a.length ++ b.drop a.length = b := List.take_append_drop _ _
  have hbtake : (b.take a.length).length = a.length := by
    simp [hle]
  have hcode : fixedWidthBlocks m a = fixedWidthBlocks m (b.take a.length) := by
    have hpre : fixedWidthBlocks m (b.take a.length) <+: fixedWidthBlocks m b :=
      fixedWidthBlocks_prefix_of_prefix ⟨b.drop a.length, hsplit⟩
    have hlen : (fixedWidthBlocks m a).length
        = (fixedWidthBlocks m (b.take a.length)).length := by
      simp [hbtake]
    exact (List.prefix_iff_eq_take.mp h).trans
      (by rw [hlen, ← List.prefix_iff_eq_take.mp hpre])
  have hbound : ∀ i ∈ b.take a.length, i < 2 ^ m := fun i hi =>
    hb i (List.mem_of_mem_take hi)
  have hab := fixedWidthBlocks_inj ha hbound hbtake.symm hcode
  refine ⟨b.drop a.length, ?_⟩
  nth_rewrite 1 [hab]
  exact hsplit

/-- Incomparable nodes get prefix-incomparable codes, which is exactly the
`disjointAllocations` condition for the singleton allocations they generate. -/
lemma fixedWidthBlocks_disjoint_of_incomparable {m : ℕ} (hm : 0 < m) {a b : GacsDayNode}
    (ha : ∀ i ∈ a, i < 2 ^ m) (hb : ∀ i ∈ b, i < 2 ^ m)
    (hab : ¬ (a <+: b ∨ b <+: a)) :
    disjointAllocations [fixedWidthBlocks m a] [fixedWidthBlocks m b] := by
  rw [not_or] at hab
  intro x hx y hy
  simp only [List.mem_singleton] at hx hy
  subst hx; subst hy
  rw [not_or]
  exact ⟨fun h => hab.1 ((fixedWidthBlocks_prefix_iff hm ha hb).mp h),
    fun h => hab.2 ((fixedWidthBlocks_prefix_iff hm hb ha).mp h)⟩

end Kolmogorov
