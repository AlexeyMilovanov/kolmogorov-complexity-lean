import KolmogorovMathlib.MonotoneComplexity.GacsDayGame

/-!
# Block codes and the server side of the Gács–Day binary embedding

The Gács–Day game is played on a tree of branching factor `b ≤ 2 ^ m`.  Replacing
each branch index by a block of `m` bits embeds that tree into the binary tree.
This file develops the block code as an operation on `GacsDayNode = List ℕ`
(rather than on `BitString`, which is what `GacsDayBinaryEncoding` does), because
the game is phrased in terms of nodes:

* `bitsToNatLocal`, `bitsOfNat`, `chunkNat`, `blockCode`: the code and its inverse;
* `chunkNat_blockCode`, `blockCode_chunkNat`: the two round trips;
* `baseServerMove`: the `b`-ary server move induced by a binary server move,
  together with `getAlloc_baseServerMove` (it computes the allocation of the
  encoded node) and `serverPlayLegal_baseServerMove` (a legal binary server play
  induces a legal `b`-ary server play).

The client side of the embedding lives in `GacsDayEmbedding`.
-/

namespace Kolmogorov

/-! ### The block code -/

/-- The value of a list of bits, least significant bit first. -/
def bitsToNatLocal : List ℕ → ℕ
  | [] => 0
  | (b :: bs) => b + 2 * bitsToNatLocal bs

/-- The empty bit list has value `0`. -/
@[simp] lemma bitsToNatLocal_nil : bitsToNatLocal [] = 0 := rfl

/-- `bitsToNatLocal` reads its list least significant digit first. -/
lemma bitsToNatLocal_cons (b : ℕ) (bs : List ℕ) :
    bitsToNatLocal (b :: bs) = b + 2 * bitsToNatLocal bs := rfl

/-- Every entry of a list is at most the value `bitsToNatLocal` gives to the list. -/
lemma le_bitsToNatLocal_of_mem :
    ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ bitsToNatLocal l := by
  intro l
  induction l with
  | nil => intro a ha; cases ha
  | cons b bs ih =>
      intro a ha
      rw [bitsToNatLocal_cons]
      rcases List.mem_cons.mp ha with rfl | ha'
      · omega
      · have := ih ha'
        omega

/-- A word of `k` bits decodes to a value below `2 ^ k`. -/
lemma bitsToNatLocal_lt : ∀ (l : List ℕ), (∀ a ∈ l, a < 2) → bitsToNatLocal l < 2 ^ l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons b bs ih =>
      intro h
      have hb : b < 2 := h b List.mem_cons_self
      have hbs := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      have hpow : (2 : ℕ) ^ (b :: bs).length = 2 * 2 ^ bs.length := by
        simp [List.length_cons, pow_succ]; ring
      rw [bitsToNatLocal_cons, hpow]
      omega

/-- Split a word into consecutive blocks of width `m`, decoding each block. -/
def chunkNat (m : ℕ) : List ℕ → List ℕ
  | [] => []
  | l => if hm : m > 0 ∧ m ≤ l.length then
           have : (l.drop m).length < l.length := by
             rw [List.length_drop]; omega
           bitsToNatLocal (l.take m) :: chunkNat m (l.drop m)
         else []
termination_by l => l.length

/-- Chunking the empty list produces no chunks. -/
lemma chunkNat_nil (m : ℕ) : chunkNat m [] = [] := by rw [chunkNat]

/-- While at least `m` entries remain, chunking peels off the value of the first `m` entries and
continues on the rest. -/
lemma chunkNat_eq (m : ℕ) (hm : 0 < m) (l : List ℕ) (hl : m ≤ l.length) :
    chunkNat m l = bitsToNatLocal (l.take m) :: chunkNat m (l.drop m) := by
  cases l with
  | nil => simp at hl; omega
  | cons a t =>
      rw [chunkNat, dif_pos ⟨hm, hl⟩]
      simp

/-- A list of length exactly `m` chunks into the single value of that list. -/
lemma chunkNat_of_length (m : ℕ) (hm : 0 < m) (l : List ℕ) (hl : l.length = m) :
    chunkNat m l = [bitsToNatLocal l] := by
  rw [chunkNat_eq m hm l (by omega)]
  simp [hl, chunkNat_nil, List.take_of_length_le, List.drop_eq_nil_of_le]

private lemma chunkNat_append_aux (m : ℕ) (hm : 0 < m) (z : List ℕ) :
    ∀ (n : ℕ) (y : List ℕ), y.length = n → m ∣ y.length →
      chunkNat m (y ++ z) = chunkNat m y ++ chunkNat m z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy hdvd
    rcases Nat.eq_zero_or_pos y.length with h0 | hpos
    · have hnil : y = [] := List.eq_nil_of_length_eq_zero h0
      subst hnil
      simp [chunkNat_nil]
    · have hml : m ≤ y.length := Nat.le_of_dvd hpos hdvd
      rw [chunkNat_eq m hm (y ++ z) (by simp; omega), chunkNat_eq m hm y hml,
        List.take_append_of_le_length hml, List.drop_append_of_le_length hml,
        ih (y.drop m).length (by simp; omega) (y.drop m) rfl (by simp; omega)]
      simp

/-- Chunking distributes over concatenation as soon as the first part has length divisible by the
block width `m`. -/
lemma chunkNat_append (m : ℕ) (hm : 0 < m) (y z : List ℕ) (hdvd : m ∣ y.length) :
    chunkNat m (y ++ z) = chunkNat m y ++ chunkNat m z :=
  chunkNat_append_aux m hm z y.length y rfl hdvd

/-- A list of length `m * q` chunks into exactly `q` values. -/
lemma chunkNat_length_eq (m : ℕ) (hm : 0 < m) :
    ∀ (q : ℕ) (w : List ℕ), w.length = m * q → (chunkNat m w).length = q := by
  intro q
  induction q with
  | zero =>
      intro w hw
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp [chunkNat_nil]
  | succ q ih =>
      intro w hw
      have hlen : w.length = m * q + m := by rw [hw]; ring
      have hml : m ≤ w.length := by omega
      rw [chunkNat_eq m hm w hml]
      have hdrop : (w.drop m).length = m * q := by
        rw [List.length_drop]; omega
      simp [ih _ hdrop]

/-- In a list of length `m * q`, every entry is bounded by the value of one of its chunks. -/
lemma exists_ge_mem_chunkNat (m : ℕ) (hm : 0 < m) :
    ∀ (q : ℕ) (w : List ℕ), w.length = m * q → ∀ a ∈ w, ∃ v ∈ chunkNat m w, a ≤ v := by
  intro q
  induction q with
  | zero =>
      intro w hw a ha
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      cases ha
  | succ q ih =>
      intro w hw a ha
      have hlen : w.length = m * q + m := by rw [hw]; ring
      have hml : m ≤ w.length := by omega
      rw [chunkNat_eq m hm w hml]
      have hsplit : a ∈ w.take m ∨ a ∈ w.drop m := by
        have hmem : a ∈ w.take m ++ w.drop m := by rwa [List.take_append_drop]
        exact List.mem_append.mp hmem
      rcases hsplit with h | h
      · exact ⟨bitsToNatLocal (w.take m), List.mem_cons_self, le_bitsToNatLocal_of_mem h⟩
      · obtain ⟨v, hv, hav⟩ := ih (w.drop m) (by rw [List.length_drop]; omega) a h
        exact ⟨v, List.mem_cons_of_mem _ hv, hav⟩

/-- Every block value of a binary word of length `m * q` is below `2 ^ m`. -/
lemma chunkNat_lt_two_pow (m : ℕ) (hm : 0 < m) :
    ∀ (q : ℕ) (w : List ℕ), w.length = m * q → (∀ a ∈ w, a < 2) →
      ∀ v ∈ chunkNat m w, v < 2 ^ m := by
  intro q
  induction q with
  | zero =>
      intro w hw _ v hv
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      rw [chunkNat_nil] at hv
      cases hv
  | succ q ih =>
      intro w hw hbin v hv
      have hlen : w.length = m * q + m := by rw [hw]; ring
      have hml : m ≤ w.length := by omega
      rw [chunkNat_eq m hm w hml] at hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · have htake : (w.take m).length = m := by rw [List.length_take]; omega
        have := bitsToNatLocal_lt (w.take m)
          (fun a ha => hbin a (List.mem_of_mem_take ha))
        rwa [htake] at this
      · exact ih (w.drop m) (by rw [List.length_drop]; omega)
          (fun a ha => hbin a (List.mem_of_mem_drop ha)) v hv'

/-- The `k`-bit block (least significant bit first) of `n`, as a list of `0`s and `1`s. -/
def bitsOfNat (k n : ℕ) : List ℕ := (List.range k).map (fun i => (n >>> i) % 2)

/-- `bitsOfNat k n` consists of exactly `k` digits. -/
@[simp] lemma bitsOfNat_length (k n : ℕ) : (bitsOfNat k n).length = k := by simp [bitsOfNat]

/-- Every digit of `bitsOfNat k n` is a bit, that is, smaller than `2`. -/
lemma bitsOfNat_lt_two (k n : ℕ) : ∀ a ∈ bitsOfNat k n, a < 2 := by
  intro a ha
  simp only [bitsOfNat, List.mem_map] at ha
  obtain ⟨i, _, rfl⟩ := ha
  omega

/-- `bitsOfNat` emits the least significant bit of `n` first and encodes `n / 2` after it. -/
lemma bitsOfNat_succ (k n : ℕ) :
    bitsOfNat (k + 1) n = (n % 2) :: bitsOfNat k (n / 2) := by
  simp [bitsOfNat, List.range_succ_eq_map, Function.comp, Nat.shiftRight_eq_div_pow,
    Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- On numbers below `2 ^ k`, reading back a `k`-bit encoding recovers the number. -/
lemma bitsToNatLocal_bitsOfNat :
    ∀ (k n : ℕ), n < 2 ^ k → bitsToNatLocal (bitsOfNat k n) = n := by
  intro k
  induction k with
  | zero => intro n hn; interval_cases n; simp [bitsOfNat]
  | succ k ih =>
    intro n hn
    rw [bitsOfNat_succ, bitsToNatLocal_cons]
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [ih (n / 2) (by omega)]
    omega

/-- Decoding a binary word of length `k` and re-encoding returns the word. -/
lemma bitsOfNat_bitsToNatLocal :
    ∀ (l : List ℕ), (∀ a ∈ l, a < 2) → bitsOfNat l.length (bitsToNatLocal l) = l := by
  intro l
  induction l with
  | nil => intro _; simp [bitsOfNat]
  | cons b bs ih =>
      intro h
      have hb : b < 2 := h b List.mem_cons_self
      have hbs := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      rw [List.length_cons, bitsOfNat_succ, bitsToNatLocal_cons]
      have h1 : (b + 2 * bitsToNatLocal bs) % 2 = b := by omega
      have h2 : (b + 2 * bitsToNatLocal bs) / 2 = bitsToNatLocal bs := by omega
      rw [h1, h2, hbs]

/-- The block encoding of a Gács–Day node as a node of the binary tree. -/
def blockCode (m : ℕ) (x : GacsDayNode) : GacsDayNode := (x.map (bitsOfNat m)).flatten

/-- The block code of the empty node is empty. -/
@[simp] lemma blockCode_nil (m : ℕ) : blockCode m [] = [] := rfl

/-- The block code of a node emits the `m`-bit encoding of its first entry, followed by the code
of the rest. -/
lemma blockCode_cons (m a : ℕ) (x : GacsDayNode) :
    blockCode m (a :: x) = bitsOfNat m a ++ blockCode m x := by
  simp [blockCode]

/-- The block code turns concatenation of nodes into concatenation of bit strings. -/
lemma blockCode_append (m : ℕ) (x y : GacsDayNode) :
    blockCode m (x ++ y) = blockCode m x ++ blockCode m y := by
  simp [blockCode]

/-- The block code of a node of length `n` has exactly `m * n` bits. -/
@[simp] lemma blockCode_length (m : ℕ) (x : GacsDayNode) :
    (blockCode m x).length = m * x.length := by
  induction x with
  | nil => simp
  | cons a t ih =>
      rw [blockCode_cons, List.length_append, bitsOfNat_length, ih, List.length_cons]
      ring

/-- Every entry of a block code is a bit. -/
lemma blockCode_lt_two (m : ℕ) (x : GacsDayNode) : ∀ a ∈ blockCode m x, a < 2 := by
  induction x with
  | nil => intro a ha; cases ha
  | cons c t ih =>
      intro a ha
      rw [blockCode_cons] at ha
      rcases List.mem_append.mp ha with h | h
      · exact bitsOfNat_lt_two m c a h
      · exact ih a h

/-- The length of a block code is a multiple of the block width `m`. -/
lemma blockCode_dvd_length (m : ℕ) (x : GacsDayNode) : m ∣ (blockCode m x).length :=
  ⟨x.length, by simp⟩

/-- Encoding a node and chunking the result returns the node. -/
lemma chunkNat_blockCode (m : ℕ) (hm : 0 < m) :
    ∀ (x : GacsDayNode), (∀ a ∈ x, a < 2 ^ m) → chunkNat m (blockCode m x) = x := by
  intro x
  induction x with
  | nil => intro _; simp [chunkNat_nil]
  | cons c t ih =>
      intro h
      have hc : c < 2 ^ m := h c List.mem_cons_self
      have hlen : (bitsOfNat m c).length = m := bitsOfNat_length m c
      rw [blockCode_cons,
        chunkNat_append m hm _ _ (by rw [hlen]),
        chunkNat_of_length m hm _ hlen,
        bitsToNatLocal_bitsOfNat m c hc,
        ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
      simp

/-- Chunking a binary word whose length is a multiple of `m` and re-encoding
returns the word. -/
lemma blockCode_chunkNat (m : ℕ) (hm : 0 < m) :
    ∀ (q : ℕ) (w : List ℕ), w.length = m * q → (∀ a ∈ w, a < 2) →
      blockCode m (chunkNat m w) = w := by
  intro q
  induction q with
  | zero =>
      intro w hw _
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp [chunkNat_nil]
  | succ q ih =>
      intro w hw hbin
      have hlen : w.length = m * q + m := by rw [hw]; ring
      have hml : m ≤ w.length := by omega
      have htake : (w.take m).length = m := by rw [List.length_take]; omega
      rw [chunkNat_eq m hm w hml, blockCode_cons,
        ih (w.drop m) (by rw [List.length_drop]; omega)
          (fun a ha => hbin a (List.mem_of_mem_drop ha))]
      have hbits : bitsOfNat m (bitsToNatLocal (w.take m)) = w.take m := by
        have := bitsOfNat_bitsToNatLocal (w.take m)
          (fun a ha => hbin a (List.mem_of_mem_take ha))
        rwa [htake] at this
      rw [hbits, List.take_append_drop]

/-- On nodes whose entries are below `2 ^ m`, the block code determines the node. -/
lemma blockCode_injective (m : ℕ) (hm : 0 < m) {x y : GacsDayNode}
    (hx : ∀ a ∈ x, a < 2 ^ m) (hy : ∀ a ∈ y, a < 2 ^ m)
    (h : blockCode m x = blockCode m y) : x = y := by
  have := congrArg (chunkNat m) h
  rwa [chunkNat_blockCode m hm x hx, chunkNat_blockCode m hm y hy] at this

/-! ### Elementary facts about allocations -/


/-- The empty allocation is contained in every allocation. -/
lemma allocationSubset_nil (a : Allocation) : allocationSubset [] a := by
  intro x hx; cases hx

/-- The empty allocation is disjoint from every allocation. -/
lemma disjointAllocations_nil_left (a : Allocation) : disjointAllocations [] a := by
  intro x hx; cases hx

/-- Disjointness of allocations passes to sub-allocations. -/
lemma disjointAllocations_of_subset {a1 a2 a1' a2' : Allocation}
    (h : disjointAllocations a1 a2) (h1 : allocationSubset a1' a1)
    (h2 : allocationSubset a2' a2) : disjointAllocations a1' a2' := by
  intro x hx y hy
  obtain ⟨u, hu, hux⟩ := h1 x hx
  obtain ⟨v, hv, hvy⟩ := h2 y hy
  have huv := h u hu v hv
  rw [not_or] at huv ⊢
  refine ⟨fun hxy => ?_, fun hyx => ?_⟩
  · rcases List.prefix_or_prefix_of_prefix (hux.trans hxy) hvy with h' | h'
    · exact huv.1 h'
    · exact huv.2 h'
  · rcases List.prefix_or_prefix_of_prefix (hvy.trans hyx) hux with h' | h'
    · exact huv.2 h'
    · exact huv.1 h'

/-! ### Descending in a coherent binary server move -/

/-- For a coherent binary server move, the allocation at a node is contained in the allocation at
each of its ancestors. -/
lemma getAlloc_descend {S : ServerMove} (hS : serverMoveCoherent 2 S) :
    ∀ (z : GacsDayNode), (∀ a ∈ z, a < 2) → ∀ (y : GacsDayNode),
      allocationSubset (getAlloc S (y ++ z)) (getAlloc S y) := by
  intro z
  induction z with
  | nil => intro _ y; simpa using allocationSubset_refl (getAlloc S y)
  | cons c t ih =>
      intro hz y
      have hc : c < 2 := hz c List.mem_cons_self
      have h1 : allocationSubset (getAlloc S ((y ++ [c]) ++ t)) (getAlloc S (y ++ [c])) :=
        ih (fun a ha => hz a (List.mem_cons_of_mem _ ha)) _
      have h2 : allocationSubset (getAlloc S (y ++ [c])) (getAlloc S y) := by
        simpa using hS.1 y ⟨c, hc⟩
      rw [List.append_assoc, List.cons_append, List.nil_append] at h1
      exact allocationSubset_trans h1 h2

/-- Two prefix-incomparable lists split at their first difference. -/
lemma exists_firstDiff : ∀ (y1 y2 : List ℕ), ¬ (y1 <+: y2 ∨ y2 <+: y1) →
    ∃ p c1 c2 u v, c1 ≠ c2 ∧ y1 = p ++ c1 :: u ∧ y2 = p ++ c2 :: v := by
  intro y1
  induction y1 with
  | nil => intro y2 h; exact absurd (Or.inl List.nil_prefix) h
  | cons a t ih =>
      intro y2 h
      cases y2 with
      | nil => exact absurd (Or.inr List.nil_prefix) h
      | cons b s =>
          by_cases hab : a = b
          · subst hab
            have h' : ¬ (t <+: s ∨ s <+: t) := by
              intro hor
              apply h
              rcases hor with h1 | h1
              · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h1⟩)
              · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h1⟩)
            obtain ⟨p, c1, c2, u, v, hne, e1, e2⟩ := ih s h'
            exact ⟨a :: p, c1, c2, u, v, hne, by rw [e1]; simp, by rw [e2]; simp⟩
          · exact ⟨[], a, b, t, s, hab, rfl, rfl⟩

/-- Two distinct lists of the same length are prefix-incomparable. -/
lemma incomparable_of_length_eq_of_ne {u v : List ℕ} (hlen : u.length = v.length)
    (hne : u ≠ v) : ¬ (u <+: v ∨ v <+: u) := by
  rw [not_or]
  exact ⟨fun h => hne (h.eq_of_length hlen), fun h => hne (h.eq_of_length hlen.symm).symm⟩

/-- In a coherent binary server move, prefix-incomparable binary nodes carry
disjoint allocations. -/
lemma getAlloc_disjoint_of_incomparable {S : ServerMove} (hS : serverMoveCoherent 2 S)
    {y1 y2 : GacsDayNode} (h1 : ∀ a ∈ y1, a < 2) (h2 : ∀ a ∈ y2, a < 2)
    (hinc : ¬ (y1 <+: y2 ∨ y2 <+: y1)) :
    disjointAllocations (getAlloc S y1) (getAlloc S y2) := by
  obtain ⟨p, c1, c2, u, v, hne, e1, e2⟩ := exists_firstDiff y1 y2 hinc
  have hc1 : c1 < 2 := h1 c1 (by rw [e1]; simp)
  have hc2 : c2 < 2 := h2 c2 (by rw [e2]; simp)
  have hu : ∀ a ∈ u, a < 2 := fun a ha => h1 a (by rw [e1]; simp [ha])
  have hv : ∀ a ∈ v, a < 2 := fun a ha => h2 a (by rw [e2]; simp [ha])
  have hy1 : y1 = (p ++ [c1]) ++ u := by rw [e1]; simp
  have hy2 : y2 = (p ++ [c2]) ++ v := by rw [e2]; simp
  have hsub1 : allocationSubset (getAlloc S y1) (getAlloc S (p ++ [c1])) := by
    rw [hy1]; exact getAlloc_descend hS u hu _
  have hsub2 : allocationSubset (getAlloc S y2) (getAlloc S (p ++ [c2])) := by
    rw [hy2]; exact getAlloc_descend hS v hv _
  have hne' : (⟨c1, hc1⟩ : Fin 2) ≠ ⟨c2, hc2⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    exact hne
  have hdisj := hS.2 p ⟨c1, hc1⟩ ⟨c2, hc2⟩ hne'
  simp only at hdisj
  exact disjointAllocations_of_subset hdisj hsub1 hsub2

/-! ### The induced `b`-ary server move -/

/-- The `b`-ary server move induced by a binary server move: every binary node
whose depth is a multiple of the block width `m` is read as an encoded `b`-ary
node. -/
def baseServerMove (m : ℕ) (S : ServerMove) : ServerMove :=
  S.filterMap (fun p =>
    if (∀ a ∈ p.1, a < 2) ∧ m ∣ p.1.length then some (chunkNat m p.1, p.2) else none)

/-- On nodes whose entries are below `2 ^ m`, the base server move looks the node up under its
block code in `S`. -/
lemma lookup_baseServerMove (m : ℕ) (hm : 0 < m) (S : ServerMove) (x : GacsDayNode)
    (hx : ∀ a ∈ x, a < 2 ^ m) :
    (baseServerMove m S).lookup x = S.lookup (blockCode m x) := by
  induction S with
  | nil => simp [baseServerMove]
  | cons p ps ih =>
      by_cases hp : (∀ a ∈ p.1, a < 2) ∧ m ∣ p.1.length
      · have hfp : (fun p : GacsDayNode × Allocation =>
            if (∀ a ∈ p.1, a < 2) ∧ m ∣ p.1.length then some (chunkNat m p.1, p.2) else none) p
            = some (chunkNat m p.1, p.2) := if_pos hp
        have hcons : baseServerMove m (p :: ps)
            = (chunkNat m p.1, p.2) :: baseServerMove m ps := by
          simp only [baseServerMove, List.filterMap_cons, hfp]
        obtain ⟨q, hq⟩ := hp.2
        have hkey : (x = chunkNat m p.1) ↔ (blockCode m x = p.1) := by
          constructor
          · intro h
            rw [h, blockCode_chunkNat m hm q p.1 (by omega) hp.1]
          · intro h
            rw [← h, chunkNat_blockCode m hm x hx]
        rw [hcons]
        by_cases hxk : x = chunkNat m p.1
        · have hbc : blockCode m x = p.1 := hkey.mp hxk
          have e1 : (x == chunkNat m p.1) = true := beq_iff_eq.mpr hxk
          have e2 : (blockCode m x == p.1) = true := beq_iff_eq.mpr hbc
          rw [List.lookup_cons, List.lookup_cons, e1, e2]
        · have hbc : blockCode m x ≠ p.1 := fun h => hxk (hkey.mpr h)
          rw [List.lookup_cons, List.lookup_cons,
            beq_eq_false_iff_ne.mpr hxk, beq_eq_false_iff_ne.mpr hbc]
          simpa using ih
      · have hfp : (fun p : GacsDayNode × Allocation =>
            if (∀ a ∈ p.1, a < 2) ∧ m ∣ p.1.length then some (chunkNat m p.1, p.2) else none) p
            = none := if_neg hp
        have hcons : baseServerMove m (p :: ps) = baseServerMove m ps := by
          simp only [baseServerMove, List.filterMap_cons, hfp]
        have hbc : blockCode m x ≠ p.1 := by
          intro h
          exact hp ⟨by rw [← h]; exact blockCode_lt_two m x, by rw [← h]; exact ⟨x.length, by simp⟩⟩
        rw [hcons, List.lookup_cons, beq_eq_false_iff_ne.mpr hbc]
        simpa using ih

/-- On nodes whose entries are below `2 ^ m`, the base server move hands out the allocation that
`S` gives to the block code of the node. -/
lemma getAlloc_baseServerMove (m : ℕ) (hm : 0 < m) (S : ServerMove) (x : GacsDayNode)
    (hx : ∀ a ∈ x, a < 2 ^ m) :
    getAlloc (baseServerMove m S) x = getAlloc S (blockCode m x) := by
  unfold getAlloc
  rw [lookup_baseServerMove m hm S x hx]

/-- Nodes with an out-of-range branch index carry no allocation in the induced
`b`-ary server move. -/
lemma getAlloc_baseServerMove_of_not_lt (m : ℕ) (hm : 0 < m) (S : ServerMove)
    (x : GacsDayNode) (hx : ¬ ∀ a ∈ x, a < 2 ^ m) :
    getAlloc (baseServerMove m S) x = [] := by
  unfold getAlloc
  have hnone : (baseServerMove m S).lookup x = none := by
    induction S with
    | nil => simp [baseServerMove]
    | cons p ps ih =>
        by_cases hp : (∀ a ∈ p.1, a < 2) ∧ m ∣ p.1.length
        · have hfp : (fun p : GacsDayNode × Allocation =>
              if (∀ a ∈ p.1, a < 2) ∧ m ∣ p.1.length then some (chunkNat m p.1, p.2) else none) p
              = some (chunkNat m p.1, p.2) := if_pos hp
          have hcons : baseServerMove m (p :: ps)
              = (chunkNat m p.1, p.2) :: baseServerMove m ps := by
            simp only [baseServerMove, List.filterMap_cons, hfp]
          obtain ⟨q, hq⟩ := hp.2
          have hxk : x ≠ chunkNat m p.1 := by
            intro h
            exact hx (fun v hv => chunkNat_lt_two_pow m hm q p.1 (by omega) hp.1 v (h ▸ hv))
          rw [hcons, List.lookup_cons, beq_eq_false_iff_ne.mpr hxk]
          simpa using ih
        · have hfp : (fun p : GacsDayNode × Allocation =>
              if (∀ a ∈ p.1, a < 2) ∧ m ∣ p.1.length then some (chunkNat m p.1, p.2) else none) p
              = none := if_neg hp
          have hcons : baseServerMove m (p :: ps) = baseServerMove m ps := by
            simp only [baseServerMove, List.filterMap_cons, hfp]
          rw [hcons]
          exact ih
  rw [hnone]

/-- A legal binary server play induces a legal `b`-ary server play, for any
branching factor `b ≤ 2 ^ m`. -/
lemma serverMoveCoherent_baseServerMove (m b : ℕ) (hm : 0 < m) (hb : b ≤ 2 ^ m)
    (S : ServerMove) (hS : serverMoveCoherent 2 S) :
    serverMoveCoherent b (baseServerMove m S) := by
  constructor
  · intro x c
    by_cases hx : ∀ a ∈ x, a < 2 ^ m
    · have hxc : ∀ a ∈ x ++ [c.val], a < 2 ^ m := by
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact hx a h
        · have : a = c.val := by simpa using h
          omega
      rw [getAlloc_baseServerMove m hm S _ hxc, getAlloc_baseServerMove m hm S x hx,
        blockCode_append]
      exact getAlloc_descend hS _ (blockCode_lt_two m [c.val]) _
    · have hxc : ¬ ∀ a ∈ x ++ [c.val], a < 2 ^ m := by
        intro hall
        exact hx (fun a ha => hall a (List.mem_append_left _ ha))
      rw [getAlloc_baseServerMove_of_not_lt m hm S _ hxc]
      exact allocationSubset_nil _
  · intro x c1 c2 hne
    by_cases hx : ∀ a ∈ x, a < 2 ^ m
    · have hbound : ∀ (c : Fin b), ∀ a ∈ x ++ [c.val], a < 2 ^ m := by
        intro c a ha
        rcases List.mem_append.mp ha with h | h
        · exact hx a h
        · have : a = c.val := by simpa using h
          omega
      rw [getAlloc_baseServerMove m hm S _ (hbound c1),
        getAlloc_baseServerMove m hm S _ (hbound c2)]
      have hc1 : c1.val < 2 ^ m := lt_of_lt_of_le c1.isLt hb
      have hc2 : c2.val < 2 ^ m := lt_of_lt_of_le c2.isLt hb
      have hvne : c1.val ≠ c2.val := fun h => hne (Fin.ext h)
      have hbne : bitsOfNat m c1.val ≠ bitsOfNat m c2.val := by
        intro h
        apply hvne
        rw [← bitsToNatLocal_bitsOfNat m c1.val hc1, ← bitsToNatLocal_bitsOfNat m c2.val hc2, h]
      have hcodene : blockCode m (x ++ [c1.val]) ≠ blockCode m (x ++ [c2.val]) := by
        rw [blockCode_append, blockCode_append]
        intro h
        apply hbne
        have := List.append_cancel_left h
        simpa [blockCode_cons] using this
      refine getAlloc_disjoint_of_incomparable hS (blockCode_lt_two _ _)
        (blockCode_lt_two _ _) (incomparable_of_length_eq_of_ne ?_ hcodene)
      simp
    · have hxc : ∀ (c : Fin b), ¬ ∀ a ∈ x ++ [c.val], a < 2 ^ m := by
        intro c hall
        exact hx (fun a ha => hall a (List.mem_append_left _ ha))
      rw [getAlloc_baseServerMove_of_not_lt m hm S _ (hxc c1)]
      exact disjointAllocations_nil_left _

/-- A legal binary server play induces a legal `b`-ary server play. -/
lemma serverPlayLegal_baseServerMove (m b : ℕ) (hm : 0 < m) (hb : b ≤ 2 ^ m)
    (sms : ℕ → ServerMove) (h : serverPlayLegal 2 sms) :
    serverPlayLegal b (fun t => baseServerMove m (sms t)) := by
  refine ⟨fun t => serverMoveCoherent_baseServerMove m b hm hb (sms t) (h.1 t), ?_⟩
  intro t x
  by_cases hx : ∀ a ∈ x, a < 2 ^ m
  · rw [getAlloc_baseServerMove m hm _ x hx, getAlloc_baseServerMove m hm _ x hx]
    exact h.2 t (blockCode m x)
  · rw [getAlloc_baseServerMove_of_not_lt m hm _ x hx]
    exact allocationSubset_nil _

end Kolmogorov
