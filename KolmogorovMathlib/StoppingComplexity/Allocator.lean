import KolmogorovMathlib.StoppingComplexity.TimeSemimeasure
import KolmogorovMathlib.StoppingComplexity.Words
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# Effective seed allocation on a finite grid

Blueprint 03 §4.2 and Lemmas A1–A3: the finite-grid allocator that turns a budgeted stream of dyadic
requests `(z, k, L)` (mass `k / 2 ^ L` at the input string `z`) into a table of seed atoms.

A state `AllocState` fixes a common precision `prec` and, for every occupied input string, a list of
atom indices `i < 2 ^ prec`; the atom `i` labels the seed cylinder of the word `bitsOfNatBE prec i`.
The three invariants of the blueprint (allocation mass, comparable disjointness, initial-segment
property of `Q_v` inside the complement of `P_v`) are the structure `AllocState.Invariant`.
`refineState` passes to a finer grid, `allocStep` performs one allocation (refine, then add the `k`
least free atoms to `z`), and `allocRun` iterates it along a request stream.  Lemma A1 identifies
the occupancy of `P_v ∪ Q_v` with the maximal chain load, Lemma A2 is the preservation of the
invariants under one step, Lemma A3 is the uniform computability of the construction.

All masses are counted in units of `2 ^ (-prec)`; the rational path load `gridLoad` converts back.
-/

namespace Kolmogorov

open scoped ENNReal

/-- Finite grid state: the seed precision `prec` and, per occupied input string, the list of its
atom indices `< 2 ^ prec`.  The atom `i` labels the cylinder of the word `bitsOfNatBE prec i`.
Blueprint 03 §4.2 (finite-grid state). -/
structure AllocState where
  /-- The common seed precision `L`. -/
  prec : ℕ
  /-- The occupied input strings with their atom lists. -/
  table : List (BitString × List ℕ)

/-- An allocation state is a pair of its precision and its table (for `Primcodable`).
Blueprint 03 §4.2. -/
def AllocState.equivProd : AllocState ≃ ℕ × List (BitString × List ℕ) where
  toFun st := (st.prec, st.table)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro st; cases st; rfl
  right_inv := by intro p; rfl

instance : Primcodable AllocState := Primcodable.ofEquiv _ AllocState.equivProd

/-- `A_z`: the atoms allocated to the input string `z` (empty for unoccupied strings).
Blueprint 03 §4.2. -/
def AllocState.atoms (st : AllocState) (z : BitString) : List ℕ := (st.table.lookup z).getD []

/-- `P_v`: the atoms of the strict prefixes of `v`. Blueprint 03 §4.2. -/
def AllocState.ancestorAtoms (st : AllocState) (v : BitString) : List ℕ :=
  ((List.range v.length).map fun k => st.atoms (v.take k)).flatten

/-- `Q_v`: the atoms of `v` and of its (occupied) extensions. Blueprint 03 §4.2. -/
def AllocState.descendantAtoms (st : AllocState) (v : BitString) : List ℕ :=
  (st.table.filter fun e => decide (v <+: e.1)).flatMap Prod.snd

/-- The invariants of the finite-grid state, with the masses `mass z` in units of `2 ^ (-prec)`:
the table is a finite map (no string occurs in two rows), every atom lies on the grid, atom lists
have no repetition, `|A_z| = mass z`, `A_z` and `A_w` are disjoint for distinct comparable `z, w`,
and `Q_v` is an initial segment of the grid minus `P_v`
(if `i ∈ Q_v`, `j < i` and `j ∉ P_v` then `j ∈ Q_v`). Blueprint 03 §4.2 (allocation mass,
comparable disjointness, initial-segment invariant). -/
structure AllocState.Invariant (st : AllocState) (mass : BitString → ℕ) : Prop where
  /-- The table is a finite map: no input string occurs in two rows (so the row lookup of
  `atoms` and the row scan of `descendantAtoms` read the same atom sets). -/
  keys_nodup : (st.table.map Prod.fst).Nodup
  /-- Every atom is an index of the grid `[0, 2 ^ prec)`. -/
  atoms_lt : ∀ z i, i ∈ st.atoms z → i < 2 ^ st.prec
  /-- No atom is listed twice at one string. -/
  nodup : ∀ z, (st.atoms z).Nodup
  /-- Allocation mass: `|A_z| · 2 ^ (-prec)` is the requested weight at `z`. -/
  card : ∀ z, (st.atoms z).length = mass z
  /-- Comparable disjointness. -/
  disjoint : ∀ z w, IsComparable z w → z ≠ w → ∀ i, i ∈ st.atoms z → i ∉ st.atoms w
  /-- Initial-segment property of `Q_v` in the ordered complement of `P_v`. -/
  initial : ∀ v i j, i ∈ st.descendantAtoms v → j < i → j ∉ st.ancestorAtoms v →
    j ∈ st.descendantAtoms v

/-- The rational path load of a grid mass table in units `2 ^ (-prec)`: the sum of
`mass u / 2 ^ prec` over all prefixes `u` of `v` (`[]` and `v` included). Blueprint 03 §4.2. -/
def gridLoad (prec : ℕ) (mass : BitString → ℕ) (v : BitString) : ℚ :=
  ∑ k ∈ Finset.range (v.length + 1), (mass (v.take k) : ℚ) / 2 ^ prec

/-! ### Reading the table: row lookup and the two atom unions -/

/-- In a table whose keys are pairwise distinct, looking up the key of a row returns the atom list
of that row. -/
private theorem lookup_eq_some_of_mem {t : List (BitString × List ℕ)}
    (hnd : (t.map Prod.fst).Nodup) {e : BitString × List ℕ} (he : e ∈ t) :
    t.lookup e.1 = some e.2 := by
  induction t with
  | nil => simp at he
  | cons a t ih =>
    obtain ⟨k, b⟩ := a
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · have hne : (e.1 == k) = false :=
        beq_eq_false_iff_ne.mpr fun h => hnd.1 (List.mem_map.mpr ⟨e, he, h⟩)
      rw [List.lookup_cons, hne]
      exact ih hnd.2 he

/-- A string with an atom is occupied: its row `(y, A_y)` belongs to the table. -/
private theorem mem_table_of_mem_atoms {st : AllocState} {y : BitString} {i : ℕ}
    (hi : i ∈ st.atoms y) : (y, st.atoms y) ∈ st.table := by
  unfold AllocState.atoms at hi ⊢
  cases h : st.table.lookup y with
  | none => simp [h] at hi
  | some l =>
    obtain ⟨l₁, l₂, heq, -⟩ := List.lookup_eq_some_iff.mp h
    simp [heq]

/-- Under distinct keys the row scan defining `Q_v` agrees with the row lookup defining `A_y`:
an atom lies in `Q_v` iff it is an atom of some extension `y` of `v`. -/
private theorem mem_descendantAtoms_iff {st : AllocState} (hnd : (st.table.map Prod.fst).Nodup)
    {v : BitString} {i : ℕ} : i ∈ st.descendantAtoms v ↔ ∃ y, v <+: y ∧ i ∈ st.atoms y := by
  simp only [AllocState.descendantAtoms, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨he, hv⟩, hi⟩
    exact ⟨e.1, hv, by simpa [AllocState.atoms, lookup_eq_some_of_mem hnd he] using hi⟩
  · rintro ⟨y, hv, hi⟩
    exact ⟨(y, st.atoms y), ⟨mem_table_of_mem_atoms hi, hv⟩, hi⟩

/-- `P_v` is the union of the atom lists of the strict prefixes `v.take k`, `k < |v|`. -/
private theorem mem_ancestorAtoms_iff {st : AllocState} {v : BitString} {i : ℕ} :
    i ∈ st.ancestorAtoms v ↔ ∃ k < v.length, i ∈ st.atoms (v.take k) := by
  simp [AllocState.ancestorAtoms]

/-- Comparable disjointness along a chain: an atom of `u` is not an atom of a strictly longer
extension `y` of `u`. -/
private theorem not_mem_atoms_of_prefix {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) {u y : BitString} (hu : u <+: y) (hlt : u.length < y.length)
    {i : ℕ} (hi : i ∈ st.atoms u) : i ∉ st.atoms y :=
  hinv.disjoint u y (Or.inl hu) (fun h => (lt_irrefl _ (h ▸ hlt))) i hi

/-- Refinement to the precision `L'`: the atom `i` is replaced by the block
`[i · 2 ^ (L' - L), (i + 1) · 2 ^ (L' - L))` of its length-`L'` descendants (meaningful for
`L ≤ L'`). Blueprint 03 §4.2 (refinement). -/
def refineState (st : AllocState) (L' : ℕ) : AllocState :=
  ⟨L', st.table.map fun e =>
    (e.1, e.2.flatMap fun i =>
      (List.range (2 ^ (L' - st.prec))).map fun r => i * 2 ^ (L' - st.prec) + r)⟩

/-- Looking up a key after mapping every atom list by `g` is mapping the looked-up list. -/
private theorem lookup_map_snd (t : List (BitString × List ℕ)) (g : List ℕ → List ℕ)
    (z : BitString) : (t.map fun e => (e.1, g e.2)).lookup z = (t.lookup z).map g := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨k, b⟩ := a
    simp only [List.map_cons, List.lookup_cons]
    cases z == k <;> simp [ih]

/-- The atoms of `z` after refinement are the length-`L'` descendants of its old atoms.
Blueprint 03 §4.2 (refinement). -/
theorem refineState_atoms (st : AllocState) (L' : ℕ) (z : BitString) :
    (refineState st L').atoms z =
      (st.atoms z).flatMap fun i =>
        (List.range (2 ^ (L' - st.prec))).map fun r => i * 2 ^ (L' - st.prec) + r := by
  simp only [AllocState.atoms, refineState, lookup_map_snd]
  cases st.table.lookup z <;> simp

/-- The block of the atom `a` at relative depth `d` consists exactly of the indices whose
quotient by `2 ^ d` is `a`. Blueprint 03 §4.2 (quotient and remainder by `2 ^ (L' - L)`). -/
private theorem mem_refineBlock_iff {a d j : ℕ} :
    j ∈ (List.range (2 ^ d)).map (fun r => a * 2 ^ d + r) ↔ j / 2 ^ d = a := by
  have hpos : 0 < 2 ^ d := by positivity
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rintro rfl
    exact ⟨j % 2 ^ d, Nat.mod_lt _ hpos, Nat.div_add_mod' j (2 ^ d)⟩

/-- An index lies in the refinement of an atom list iff its quotient by `2 ^ d` is an atom.
Blueprint 03 §4.2 (refinement). -/
private theorem mem_refineBlocks_iff {l : List ℕ} {d j : ℕ} :
    j ∈ l.flatMap (fun i => (List.range (2 ^ d)).map fun r => i * 2 ^ d + r) ↔ j / 2 ^ d ∈ l := by
  simp only [List.mem_flatMap, mem_refineBlock_iff, exists_eq_right']

/-- Membership in `A_z` after refinement to `L'`: the quotient by `2 ^ (L' - L)` is an old atom. -/
private theorem mem_refineState_atoms_iff {st : AllocState} {L' : ℕ} {z : BitString} {i : ℕ} :
    i ∈ (refineState st L').atoms z ↔ i / 2 ^ (L' - st.prec) ∈ st.atoms z := by
  rw [refineState_atoms, mem_refineBlocks_iff]

/-- Membership in `Q_v` after refinement: the quotient by `2 ^ (L' - L)` lies in the old `Q_v`. -/
private theorem mem_refineState_descendantAtoms_iff {st : AllocState} {L' : ℕ} {v : BitString}
    {i : ℕ} : i ∈ (refineState st L').descendantAtoms v ↔
      i / 2 ^ (L' - st.prec) ∈ st.descendantAtoms v := by
  simp only [AllocState.descendantAtoms, refineState, List.filter_map, List.flatMap_map,
    List.mem_flatMap, List.mem_filter, Function.comp_def, mem_refineBlock_iff, exists_eq_right']

/-- Membership in `P_v` after refinement: the quotient by `2 ^ (L' - L)` lies in the old `P_v`. -/
private theorem mem_refineState_ancestorAtoms_iff {st : AllocState} {L' : ℕ} {v : BitString}
    {i : ℕ} : i ∈ (refineState st L').ancestorAtoms v ↔
      i / 2 ^ (L' - st.prec) ∈ st.ancestorAtoms v := by
  simp only [mem_ancestorAtoms_iff, mem_refineState_atoms_iff]

/-- Refinement from `L` to `L' ≥ L` preserves the invariants; the masses scale by `2 ^ (L' - L)`.
Blueprint 03 §4.2 (refinement preserves masses, disjointness and the initial-segment invariant). -/
theorem refineState_invariant {st : AllocState} {mass : BitString → ℕ} (hinv : st.Invariant mass)
    {L' : ℕ} (hL : st.prec ≤ L') :
    (refineState st L').Invariant fun z => mass z * 2 ^ (L' - st.prec) := by
  have hpos : 0 < 2 ^ (L' - st.prec) := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [refineState, List.map_map, Function.comp_def] using hinv.keys_nodup
  · intro z i hi
    have h := (Nat.div_lt_iff_lt_mul hpos).mp (hinv.atoms_lt z _ (mem_refineState_atoms_iff.mp hi))
    rw [← pow_add, Nat.add_sub_cancel' hL] at h
    exact h
  · intro z
    rw [refineState_atoms]
    refine List.nodup_flatMap.mpr ⟨fun a _ => List.nodup_range.map fun r₁ r₂ h => ?_, ?_⟩
    · exact Nat.add_left_cancel h
    · refine (hinv.nodup z).imp fun hab => ?_
      simp only [Function.onFun]
      intro x hxa hxb
      rw [mem_refineBlock_iff] at hxa hxb
      exact hab (hxa.symm.trans hxb)
  · intro z
    rw [refineState_atoms, List.length_flatMap]
    simp [hinv.card z]
  · intro z w hzw hne i hiz hiw
    rw [mem_refineState_atoms_iff] at hiz hiw
    exact hinv.disjoint z w hzw hne _ hiz hiw
  · intro v i j hi hji hj
    rw [mem_refineState_descendantAtoms_iff] at hi ⊢
    rw [mem_refineState_ancestorAtoms_iff] at hj
    rcases (Nat.div_le_div_right (c := 2 ^ (L' - st.prec)) hji.le).lt_or_eq with h | h
    · exact hinv.initial v _ _ hi h hj
    · exact h ▸ hi

/-! ### Lemma A1: the chain recursion -/

/-- A proper extension of `v` extends `v ++ [false]` or `v ++ [true]`. -/
private theorem prefix_split {v y : BitString} (h : v <+: y) :
    y = v ∨ v ++ [false] <+: y ∨ v ++ [true] <+: y := by
  obtain ⟨t, rfl⟩ := h
  rcases t with _ | ⟨b, t⟩
  · simp
  · cases b
    · exact Or.inr (Or.inl ⟨t, by simp⟩)
    · exact Or.inr (Or.inr ⟨t, by simp⟩)

/-- Under the invariants `|P_v| = Σ_{k < |v|} |A_{v.take k}|`: the atom lists of the strict
prefixes of `v` are pairwise disjoint and have no repetitions. -/
private theorem card_ancestorAtoms {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) (v : BitString) :
    (st.ancestorAtoms v).toFinset.card =
      ∑ k ∈ Finset.range v.length, (st.atoms (v.take k)).length := by
  have hset : (st.ancestorAtoms v).toFinset =
      (Finset.range v.length).biUnion fun k => (st.atoms (v.take k)).toFinset := by
    ext i
    simp [mem_ancestorAtoms_iff]
  rw [hset, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun k _ => List.toFinset_card_of_nodup (hinv.nodup _)
  · intro k hk k' hk' hne
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    simp only [Function.onFun, Finset.disjoint_left, List.mem_toFinset]
    intro i hi hi'
    rcases lt_or_gt_of_ne hne with h | h
    · exact not_mem_atoms_of_prefix hinv (List.take_prefix_take_left h.le)
        (by simp only [List.length_take]; omega) hi hi'
    · exact not_mem_atoms_of_prefix hinv (List.take_prefix_take_left h.le)
        (by simp only [List.length_take]; omega) hi' hi

/-- `P_v` and `Q_v` are disjoint: an atom of a strict prefix of `v` is not an atom of an
extension of `v` (comparable disjointness). -/
private theorem disjoint_ancestor_descendant {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) (v : BitString) :
    Disjoint (st.ancestorAtoms v).toFinset (st.descendantAtoms v).toFinset := by
  rw [Finset.disjoint_left]
  intro i hP hQ
  rw [List.mem_toFinset, mem_ancestorAtoms_iff] at hP
  rw [List.mem_toFinset, mem_descendantAtoms_iff hinv.keys_nodup] at hQ
  obtain ⟨k, hk, hik⟩ := hP
  obtain ⟨y, hvy, hiy⟩ := hQ
  exact not_mem_atoms_of_prefix hinv ((List.take_prefix k v).trans hvy)
    (by have := hvy.length_le; simp only [List.length_take]; omega) hik hiy

/-- An atom of `Q_{v b}` is not an ancestor atom of `v b'`: the strict prefixes of `v b'` are the
prefixes of `v`, strictly shorter than every extension of `v b`. -/
private theorem not_mem_ancestorAtoms_child {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) {v : BitString} (b b' : Bool) {i : ℕ}
    (hi : i ∈ st.descendantAtoms (v ++ [b])) : i ∉ st.ancestorAtoms (v ++ [b']) := by
  rw [mem_descendantAtoms_iff hinv.keys_nodup] at hi
  rw [mem_ancestorAtoms_iff]
  rintro ⟨k, hk, hik⟩
  obtain ⟨y, hy, hiy⟩ := hi
  have hk' : k ≤ v.length := by
    simp only [List.length_append, List.length_singleton] at hk; omega
  rw [List.take_append_of_le_length hk'] at hik
  refine not_mem_atoms_of_prefix hinv
    ((List.take_prefix k v).trans ((List.prefix_append v [b]).trans hy)) ?_ hik hiy
  have := hy.length_le
  simp only [List.length_take, List.length_append, List.length_singleton] at this ⊢
  omega

/-- Lemma A1's key step: the descendant atoms of the two children of `v` are nested, being
initial segments of the same ordered complement of `P_v ∪ A_v`. Blueprint 03 Lemma A1. -/
private theorem descendantAtoms_children_nested {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) (v : BitString) :
    (st.descendantAtoms (v ++ [false])).toFinset ⊆ (st.descendantAtoms (v ++ [true])).toFinset ∨
      (st.descendantAtoms (v ++ [true])).toFinset ⊆
        (st.descendantAtoms (v ++ [false])).toFinset := by
  by_contra h
  rw [not_or, Finset.not_subset, Finset.not_subset] at h
  obtain ⟨⟨i, hi, hi'⟩, ⟨j, hj, hj'⟩⟩ := h
  rw [List.mem_toFinset] at hi hi' hj hj'
  rcases lt_trichotomy i j with h | rfl | h
  · exact hi' (hinv.initial _ j i hj h (not_mem_ancestorAtoms_child hinv false true hi))
  · exact hj' hi
  · exact hj' (hinv.initial _ i j hi h (not_mem_ancestorAtoms_child hinv true false hj))

/-- The recursion of Lemma A1: `|Q_v| = |A_v| + max(|Q_{v0}|, |Q_{v1}|)`, since `A_v` is
disjoint from the two nested child sets. Blueprint 03 Lemma A1 (displayed recursion). -/
private theorem card_descendantAtoms_eq {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) (v : BitString) :
    (st.descendantAtoms v).toFinset.card = (st.atoms v).length +
      max (st.descendantAtoms (v ++ [false])).toFinset.card
        (st.descendantAtoms (v ++ [true])).toFinset.card := by
  have hset : (st.descendantAtoms v).toFinset = (st.atoms v).toFinset ∪
      ((st.descendantAtoms (v ++ [false])).toFinset ∪
        (st.descendantAtoms (v ++ [true])).toFinset) := by
    ext i
    simp only [Finset.mem_union, List.mem_toFinset, mem_descendantAtoms_iff hinv.keys_nodup]
    constructor
    · rintro ⟨y, hvy, hi⟩
      rcases prefix_split hvy with rfl | h | h
      · exact Or.inl hi
      · exact Or.inr (Or.inl ⟨y, h, hi⟩)
      · exact Or.inr (Or.inr ⟨y, h, hi⟩)
    · rintro (hi | ⟨y, hy, hi⟩ | ⟨y, hy, hi⟩)
      · exact ⟨v, List.prefix_refl v, hi⟩
      · exact ⟨y, (List.prefix_append v [false]).trans hy, hi⟩
      · exact ⟨y, (List.prefix_append v [true]).trans hy, hi⟩
  have hdisj : Disjoint (st.atoms v).toFinset ((st.descendantAtoms (v ++ [false])).toFinset ∪
      (st.descendantAtoms (v ++ [true])).toFinset) := by
    rw [Finset.disjoint_left]
    intro i hi hQ
    simp only [Finset.mem_union, List.mem_toFinset,
      mem_descendantAtoms_iff hinv.keys_nodup] at hi hQ
    rcases hQ with ⟨y, hy, hiy⟩ | ⟨y, hy, hiy⟩ <;>
    · refine not_mem_atoms_of_prefix hinv ((List.prefix_append v _).trans hy) ?_ hi hiy
      have := hy.length_le
      simp only [List.length_append, List.length_singleton] at this
      omega
  rw [hset, Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup (hinv.nodup v)]
  rcases descendantAtoms_children_nested hinv v with h | h
  · rw [Finset.union_eq_right.mpr h, max_eq_right (Finset.card_le_card h)]
  · rw [Finset.union_eq_left.mpr h, max_eq_left (Finset.card_le_card h)]

/-- At the greatest occupied depth the only occupied extension of `v` is `v`: `Q_v = A_v` when
every occupied string has length at most `|v|`. -/
private theorem descendantAtoms_toFinset_of_length {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) {v : BitString} (hD : ∀ e ∈ st.table, e.1.length ≤ v.length) :
    (st.descendantAtoms v).toFinset = (st.atoms v).toFinset := by
  ext i
  simp only [List.mem_toFinset, mem_descendantAtoms_iff hinv.keys_nodup]
  constructor
  · rintro ⟨y, hvy, hi⟩
    rwa [← hvy.eq_of_length (le_antisymm hvy.length_le (hD _ (mem_table_of_mem_atoms hi)))] at hi
  · exact fun hi => ⟨v, List.prefix_refl v, hi⟩

/-- For `|v| < D` the length-`D` extensions of `v` are those of `v0` together with those of
`v1`. -/
private theorem extensions_eq_union {D : ℕ} {v : BitString} (hv : v.length < D) :
    ((exactLengthPrograms D).filter fun w => decide (v <+: w)).toFinset =
      ((exactLengthPrograms D).filter fun w => decide (v ++ [false] <+: w)).toFinset ∪
        ((exactLengthPrograms D).filter fun w => decide (v ++ [true] <+: w)).toFinset := by
  ext w
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, hvw⟩
    rcases prefix_split hvw with rfl | h | h
    · exact absurd (exactLengthPrograms_length_eq D w hw) hv.ne
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, h⟩
  · rintro (⟨hw, h⟩ | ⟨hw, h⟩)
    · exact ⟨hw, (List.prefix_append _ _).trans h⟩
    · exact ⟨hw, (List.prefix_append _ _).trans h⟩

/-- The only length-`|v|` extension of `v` is `v` itself. -/
private theorem extensions_self (v : BitString) :
    ((exactLengthPrograms v.length).filter fun w => decide (v <+: w)).toFinset = {v} := by
  ext w
  simp only [Finset.mem_singleton, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, hvw⟩
    exact (hvw.eq_of_length (exactLengthPrograms_length_eq _ w hw).symm).symm
  · rintro rfl
    exact ⟨mem_exactLengthPrograms_self w, List.prefix_refl w⟩

/-- Lemma A1 along the chain: for `|v| ≤ D`, the strict-prefix load of `v` plus `|Q_v|` is the
maximal chain load `Σ_{k ≤ D} |A_{w.take k}|` over the length-`D` extensions `w` of `v`
(induction on `D - |v|`). Blueprint 03 Lemma A1. -/
private theorem prefixLoad_add_card_descendantAtoms {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) {D : ℕ} (hD : ∀ e ∈ st.table, e.1.length ≤ D) {v : BitString}
    (hv : v.length ≤ D) :
    ∑ k ∈ Finset.range v.length, (st.atoms (v.take k)).length +
        (st.descendantAtoms v).toFinset.card =
      ((exactLengthPrograms D).filter fun w => decide (v <+: w)).toFinset.sup
        fun w => ∑ k ∈ Finset.range (D + 1), (st.atoms (w.take k)).length := by
  obtain ⟨n, hn⟩ : ∃ n, v.length + n = D := ⟨D - v.length, by omega⟩
  induction n generalizing v with
  | zero =>
    have hDv : D = v.length := by omega
    subst hDv
    rw [descendantAtoms_toFinset_of_length hinv hD, List.toFinset_card_of_nodup (hinv.nodup v),
      extensions_self, Finset.sup_singleton, Finset.sum_range_succ, List.take_length]
  | succ n ih =>
    have hstep : ∀ b : Bool, ∑ k ∈ Finset.range (v ++ [b]).length,
        (st.atoms ((v ++ [b]).take k)).length =
        ∑ k ∈ Finset.range v.length, (st.atoms (v.take k)).length + (st.atoms v).length := by
      intro b
      rw [List.length_append, List.length_singleton, Finset.sum_range_succ,
        List.take_append_of_le_length le_rfl, List.take_length]
      congr 1
      exact Finset.sum_congr rfl fun k hk => by
        rw [List.take_append_of_le_length (Finset.mem_range.mp hk).le]
    have h0 := ih (v := v ++ [false]) (by simp; omega) (by simp; omega)
    have h1 := ih (v := v ++ [true]) (by simp; omega) (by simp; omega)
    rw [hstep] at h0 h1
    rw [card_descendantAtoms_eq hinv v, extensions_eq_union (by omega), Finset.sup_union, ← h0,
      ← h1]
    omega

/-- The right fold of `max` from `0` over a list is the supremum over its set of elements. -/
private theorem foldr_max_eq_sup {α : Type*} [DecidableEq α] (f : α → ℕ) (l : List α) :
    l.foldr (fun w m => max m (f w)) 0 = l.toFinset.sup f := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, ih, List.toFinset_cons, Finset.sup_insert, max_comm]

/-- Lemma A1 (subtree occupancy equals maximal chain load): at a state satisfying the invariants,
with every occupied string and `v` of length at most `D`, the number of distinct atoms in
`P_v ∪ Q_v` is the maximum, over the strings `w` of length `D` extending `v`, of the chain load
`Σ_{k ≤ D} |A_{w.take k}|`. Blueprint 03 Lemma A1. -/
theorem card_ancestor_union_descendant_eq_sup {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) {v : BitString} {D : ℕ} (hD : ∀ e ∈ st.table, e.1.length ≤ D)
    (hv : v.length ≤ D) :
    ((st.ancestorAtoms v ++ st.descendantAtoms v).dedup).length =
      ((exactLengthPrograms D).filter fun w => decide (v <+: w)).foldr
        (fun w m => max m (∑ k ∈ Finset.range (D + 1), (st.atoms (w.take k)).length)) 0 := by
  rw [foldr_max_eq_sup, ← List.card_toFinset, List.toFinset_append,
    Finset.card_union_of_disjoint (disjoint_ancestor_descendant hinv v), card_ancestorAtoms hinv v]
  exact prefixLoad_add_card_descendantAtoms hinv hD hv

/-- `F_z`: the grid atoms outside `P_z ∪ Q_z`, in increasing order. Blueprint 03 Lemma A2. -/
def AllocState.freeAtoms (st : AllocState) (z : BitString) : List ℕ :=
  (List.range (2 ^ st.prec)).filter fun i =>
    decide (i ∉ st.ancestorAtoms z ∧ i ∉ st.descendantAtoms z)

/-- Replace the atom list of `z` by `l` (the other entries are kept). Blueprint 03 Lemma A3. -/
def AllocState.setAtoms (st : AllocState) (z : BitString) (l : List ℕ) : AllocState :=
  ⟨st.prec, (z, l) :: st.table.filter fun e => decide (e.1 ≠ z)⟩

/-- Precision after serving the request `(z, k, L)` from precision `prec`: `max prec L`.
Blueprint 03 Lemma A2. -/
def requestPrec (prec : ℕ) (r : DyadicRequest) : ℕ := max prec r.2.2

/-- Number of atoms of precision `max prec L` requested by `(z, k, L)`: `k · 2 ^ (max prec L - L)`.
Blueprint 03 Lemma A2 (`delta = k · 2 ^ (-L)` on the refined grid). -/
def requestAtomCount (prec : ℕ) (r : DyadicRequest) : ℕ := r.2.1 * 2 ^ (requestPrec prec r - r.2.2)

/-- The requested masses after the request `r = (z, k, L)`, in units of `2 ^ (-max prec L)`: the
old masses scaled to the new precision, plus `k · 2 ^ (max prec L - L)` at `z`.
Blueprint 03 Lemma A2 (updated requested weights). -/
def updatedMass (prec : ℕ) (mass : BitString → ℕ) (r : DyadicRequest) : BitString → ℕ :=
  fun w => mass w * 2 ^ (requestPrec prec r - prec) + if w = r.1 then requestAtomCount prec r else 0

/-- One allocation step for the request `(z, k, L)`: refine to the precision `max prec L`, take the
`k · 2 ^ (max prec L - L)` least atoms outside `P_z ∪ Q_z` and add them to `A_z`.  Total: with too
few free atoms the step saturates (Lemma A2 shows this never happens under the path budget).
Blueprint 03 Lemma A2 (allocation step) and Lemma A3 (default failure output). -/
def allocStep (st : AllocState) (r : DyadicRequest) : AllocState :=
  let st' := refineState st (requestPrec st.prec r)
  st'.setAtoms r.1 (st'.atoms r.1 ++ (st'.freeAtoms r.1).take (requestAtomCount st.prec r))

/-! ### Lemma A2: one allocation step -/

/-- Dropping the rows of `z` does not change the lookup of any other key. -/
private theorem lookup_filter_ne (t : List (BitString × List ℕ)) {z w : BitString} (hw : w ≠ z) :
    (t.filter fun e => decide (e.1 ≠ z)).lookup w = t.lookup w := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨k, b⟩ := a
    by_cases hk : k = z
    · subst hk
      have hwk : (w == k) = false := beq_eq_false_iff_ne.mpr hw
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, List.lookup_cons, hwk, ih]
    · simp only [List.filter_cons, ne_eq, hk, not_false_eq_true, decide_true, if_true,
        List.lookup_cons, ih]

/-- The atoms after `setAtoms z l`: `l` at `z`, the old atoms elsewhere. Blueprint 03 Lemma A3
(finite-map update). -/
private theorem setAtoms_atoms (st : AllocState) (z : BitString) (l : List ℕ) (w : BitString) :
    (st.setAtoms z l).atoms w = if w = z then l else st.atoms w := by
  simp only [AllocState.setAtoms, AllocState.atoms]
  split_ifs with hw
  · subst hw
    simp
  · rw [List.lookup_cons, beq_eq_false_iff_ne.mpr hw]
    exact congrArg (Option.getD · []) (lookup_filter_ne _ hw)

/-- `setAtoms` keeps the keys of the table pairwise distinct. -/
private theorem setAtoms_keys_nodup {st : AllocState} (hnd : (st.table.map Prod.fst).Nodup)
    (z : BitString) (l : List ℕ) : ((st.setAtoms z l).table.map Prod.fst).Nodup := by
  simp only [AllocState.setAtoms, List.map_cons, List.nodup_cons]
  exact ⟨by simp, hnd.sublist (List.filter_sublist.map _)⟩

/-- In a strictly increasing list the first `n` entries form an initial segment: an entry below
a member of `l.take n` lies in `l.take n`. -/
private theorem mem_take_of_lt {l : List ℕ} (hl : l.Pairwise (· < ·)) {n i j : ℕ}
    (hi : i ∈ l.take n) (hj : j ∈ l) (hji : j < i) : j ∈ l.take n := by
  rw [← List.take_append_drop n l] at hl hj
  rcases List.mem_append.mp hj with hj | hj
  · exact hj
  · exact absurd ((List.pairwise_append.mp hl).2.2 i hi j hj) (not_lt.mpr hji.le)

/-- Membership in the free atoms `F_z`: grid atoms outside `P_z ∪ Q_z`. -/
private theorem mem_freeAtoms_iff {st : AllocState} {z : BitString} {i : ℕ} :
    i ∈ st.freeAtoms z ↔ i < 2 ^ st.prec ∧ i ∉ st.ancestorAtoms z ∧ i ∉ st.descendantAtoms z := by
  simp [AllocState.freeAtoms]

/-- Counting the free atoms: `|F_z| + |P_z ∪ Q_z| = 2 ^ prec`, all atoms lying on the grid. -/
private theorem length_freeAtoms_add {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) (z : BitString) :
    (st.freeAtoms z).length + ((st.ancestorAtoms z ++ st.descendantAtoms z).dedup).length =
      2 ^ st.prec := by
  have hnd : (st.freeAtoms z).Nodup := List.nodup_range.filter _
  have hU : (st.ancestorAtoms z ++ st.descendantAtoms z).toFinset ⊆
      Finset.range (2 ^ st.prec) := by
    intro i hi
    simp only [List.mem_toFinset, List.mem_append, mem_ancestorAtoms_iff,
      mem_descendantAtoms_iff hinv.keys_nodup] at hi
    rw [Finset.mem_range]
    rcases hi with ⟨m, -, hm⟩ | ⟨y, -, hy⟩
    · exact hinv.atoms_lt _ i hm
    · exact hinv.atoms_lt _ i hy
  have hset : (st.freeAtoms z).toFinset =
      Finset.range (2 ^ st.prec) \ (st.ancestorAtoms z ++ st.descendantAtoms z).toFinset := by
    ext i
    simp [AllocState.freeAtoms]
  rw [← List.toFinset_card_of_nodup hnd, ← List.card_toFinset, hset,
    Finset.card_sdiff_add_card_eq_card hU, Finset.card_range]

/-- For `v ⊑ z` the atoms of `P_z ∪ Q_z` lie in `P_v ∪ Q_v`: a string comparable with `z` is
comparable with `v`. Blueprint 03 Lemma A2 (case 3). -/
private theorem mem_ancestor_or_descendant_of_prefix {st : AllocState}
    (hnd : (st.table.map Prod.fst).Nodup) {v z : BitString} (hvz : v <+: z) {i : ℕ}
    (hi : i ∈ st.ancestorAtoms z ∨ i ∈ st.descendantAtoms z) :
    i ∈ st.ancestorAtoms v ∨ i ∈ st.descendantAtoms v := by
  simp only [mem_ancestorAtoms_iff, mem_descendantAtoms_iff hnd] at hi ⊢
  rcases hi with ⟨m, hm, him⟩ | ⟨y, hzy, hiy⟩
  · by_cases hmv : m < v.length
    · refine Or.inl ⟨m, hmv, ?_⟩
      rwa [List.prefix_iff_eq_take.mp hvz, List.take_take, min_eq_left hmv.le]
    · refine Or.inr ⟨z.take m, ?_, him⟩
      rw [List.prefix_iff_eq_take.mp hvz]
      exact List.take_prefix_take_left (not_lt.mp hmv)
  · exact Or.inr ⟨y, hvz.trans hzy, hiy⟩

/-- Lemma A2 on a fixed grid: when `F_z` has at least `k` atoms, adding its `k` least atoms to
`A_z` preserves the invariants, the mass at `z` growing by `k`. Blueprint 03 Lemma A2 (mass,
disjointness, and the four cases of the initial-segment invariant). -/
private theorem setAtoms_take_freeAtoms_invariant {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) (z : BitString) {k : ℕ} (hk : k ≤ (st.freeAtoms z).length) :
    (st.setAtoms z (st.atoms z ++ (st.freeAtoms z).take k)).Invariant
      fun w => mass w + if w = z then k else 0 := by
  have hB : ∀ i ∈ (st.freeAtoms z).take k,
      i < 2 ^ st.prec ∧ i ∉ st.ancestorAtoms z ∧ i ∉ st.descendantAtoms z :=
    fun i hi => mem_freeAtoms_iff.mp (List.mem_of_mem_take hi)
  have hatoms := setAtoms_atoms st z (st.atoms z ++ (st.freeAtoms z).take k)
  have hkeys := setAtoms_keys_nodup hinv.keys_nodup z (st.atoms z ++ (st.freeAtoms z).take k)
  have hmono : ∀ w i, i ∈ st.atoms w →
      i ∈ (st.setAtoms z (st.atoms z ++ (st.freeAtoms z).take k)).atoms w := by
    intro w i hi
    rw [hatoms]
    split_ifs with hwz
    · exact List.mem_append_left _ (hwz ▸ hi)
    · exact hi
  -- the new atoms avoid every string comparable with `z` (including `z`)
  have hBavoid : ∀ w, IsComparable w z → ∀ i ∈ (st.freeAtoms z).take k, i ∉ st.atoms w := by
    intro w hwz i hi hiw
    obtain ⟨-, hP, hQ⟩ := hB i hi
    rcases hwz with hwz | hzw
    · by_cases hw : w.length < z.length
      · exact hP (mem_ancestorAtoms_iff.mpr
          ⟨w.length, hw, by rwa [← List.prefix_iff_eq_take.mp hwz]⟩)
      · obtain rfl := hwz.eq_of_length (le_antisymm hwz.length_le (not_lt.mp hw))
        exact hQ ((mem_descendantAtoms_iff hinv.keys_nodup).mpr ⟨_, List.prefix_refl _, hiw⟩)
    · exact hQ ((mem_descendantAtoms_iff hinv.keys_nodup).mpr ⟨w, hzw, hiw⟩)
  -- `Q_v` after the step: the old `Q_v`, plus the new atoms when `v ⊑ z`
  have hQ2 : ∀ v i, i ∈ (st.setAtoms z (st.atoms z ++ (st.freeAtoms z).take k)).descendantAtoms v
      ↔ i ∈ st.descendantAtoms v ∨ (v <+: z ∧ i ∈ (st.freeAtoms z).take k) := by
    intro v i
    rw [mem_descendantAtoms_iff hkeys, mem_descendantAtoms_iff hinv.keys_nodup]
    constructor
    · rintro ⟨y, hvy, hi⟩
      rw [hatoms] at hi
      split_ifs at hi with hyz
      · rcases List.mem_append.mp hi with hi | hi
        · exact Or.inl ⟨z, hyz ▸ hvy, hi⟩
        · exact Or.inr ⟨hyz ▸ hvy, hi⟩
      · exact Or.inl ⟨y, hvy, hi⟩
    · rintro (⟨y, hvy, hi⟩ | ⟨hvz, hi⟩)
      · exact ⟨y, hvy, hmono y i hi⟩
      · refine ⟨z, hvz, ?_⟩
        rw [hatoms, if_pos rfl]
        exact List.mem_append_right _ hi
  refine ⟨hkeys, ?_, ?_, ?_, ?_, ?_⟩
  · intro w i hi
    rw [hatoms] at hi
    split_ifs at hi with hwz
    · rcases List.mem_append.mp hi with hi | hi
      · exact hinv.atoms_lt z i hi
      · exact (hB i hi).1
    · exact hinv.atoms_lt w i hi
  · intro w
    rw [hatoms]
    split_ifs with hwz
    · refine List.nodup_append.mpr ⟨hinv.nodup z, ?_, ?_⟩
      · exact (List.nodup_range.filter _).sublist (List.take_sublist _ _)
      · intro a ha b hb hab
        exact hBavoid z (Or.inl (List.prefix_refl z)) b hb (hab ▸ ha)
    · exact hinv.nodup w
  · intro w
    rw [hatoms]
    split_ifs with hwz
    · rw [List.length_append, List.length_take, min_eq_left hk, hinv.card z, hwz]
    · rw [hinv.card w, Nat.add_zero]
  · intro w w' hww' hne i hi hi'
    rw [hatoms] at hi hi'
    by_cases hw : w = z
    · subst hw
      rw [if_pos rfl] at hi
      rw [if_neg (Ne.symm hne)] at hi'
      rcases List.mem_append.mp hi with hi | hi
      · exact hinv.disjoint _ _ hww' hne i hi hi'
      · exact hBavoid w' (Or.symm hww') i hi hi'
    · rw [if_neg hw] at hi
      by_cases hw' : w' = z
      · subst hw'
        rw [if_pos rfl] at hi'
        rcases List.mem_append.mp hi' with hi' | hi'
        · exact hinv.disjoint _ _ hww' hne i hi hi'
        · exact hBavoid w hww' i hi' hi
      · rw [if_neg hw'] at hi'
        exact hinv.disjoint _ _ hww' hne i hi hi'
  · intro v i j hi hji hj
    rw [hQ2] at hi ⊢
    have hj' : j ∉ st.ancestorAtoms v := fun h => hj (by
      obtain ⟨m, hm, hjm⟩ := mem_ancestorAtoms_iff.mp h
      exact mem_ancestorAtoms_iff.mpr ⟨m, hm, hmono _ j hjm⟩)
    rcases hi with hi | ⟨hvz, hi⟩
    · exact Or.inl (hinv.initial v i j hi hji hj')
    · by_cases hjQ : j ∈ st.descendantAtoms v
      · exact Or.inl hjQ
      · have hsorted : (st.freeAtoms z).Pairwise (· < ·) := List.pairwise_lt_range.filter _
        refine Or.inr ⟨hvz, mem_take_of_lt hsorted hi ?_ hji⟩
        refine mem_freeAtoms_iff.mpr ⟨hji.trans (hB i hi).1, fun hjP => ?_, fun hjQz => ?_⟩
        · rcases mem_ancestor_or_descendant_of_prefix hinv.keys_nodup hvz (Or.inl hjP)
            with h | h
          · exact hj' h
          · exact hjQ h
        · rcases mem_ancestor_or_descendant_of_prefix hinv.keys_nodup hvz (Or.inr hjQz)
            with h | h
          · exact hj' h
          · exact hjQ h

/-- Capacity in Lemma A2: under the updated path budget the refined grid has at least `k'` atoms
outside `P_z ∪ Q_z`. Every length-`D` chain through `z` carries its old load plus `k'` within
`2 ^ L'`, so Lemma A1 bounds `|P_z ∪ Q_z|` by `2 ^ L' - k'`. Blueprint 03 Lemma A2 (capacity
proof). -/
private theorem requestAtomCount_le_length_freeAtoms {st : AllocState} {mass : BitString → ℕ}
    (hinv : st.Invariant mass) {r : DyadicRequest}
    (hbud : ∀ v, gridLoad (requestPrec st.prec r) (updatedMass st.prec mass r) v ≤ 1) :
    requestAtomCount st.prec r ≤
      ((refineState st (requestPrec st.prec r)).freeAtoms r.1).length := by
  have hinv' := refineState_invariant hinv (L' := requestPrec st.prec r) (le_max_left _ _)
  obtain ⟨D, hDtab, hzD⟩ : ∃ D, (∀ e ∈ (refineState st (requestPrec st.prec r)).table,
      e.1.length ≤ D) ∧ r.1.length ≤ D := by
    refine ⟨r.1.length + (st.table.map fun e => e.1.length).sum, fun e he => ?_,
      Nat.le_add_right _ _⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact (List.le_sum_of_mem (List.mem_map_of_mem (f := fun e => e.1.length) ha)).trans
      (Nat.le_add_left _ _)
  have hchain : ∀ w ∈ ((exactLengthPrograms D).filter fun w => decide (r.1 <+: w)).toFinset,
      ∑ m ∈ Finset.range (D + 1),
          ((refineState st (requestPrec st.prec r)).atoms (w.take m)).length +
        requestAtomCount st.prec r ≤ 2 ^ requestPrec st.prec r := by
    intro w hw
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw
    obtain ⟨hwD, hzw⟩ := hw
    have hlen := exactLengthPrograms_length_eq D w hwD
    have hb := hbud w
    rw [gridLoad, ← Finset.sum_div, div_le_one (by positivity), hlen] at hb
    have hb' : ∑ m ∈ Finset.range (D + 1), updatedMass st.prec mass r (w.take m) ≤
        2 ^ requestPrec st.prec r := by
      exact_mod_cast hb
    have hind : ∑ m ∈ Finset.range (D + 1),
        (if w.take m = r.1 then requestAtomCount st.prec r else 0) =
          requestAtomCount st.prec r := by
      rw [Finset.sum_eq_single_of_mem r.1.length (Finset.mem_range.mpr (by omega)),
        if_pos (List.prefix_iff_eq_take.mp hzw).symm]
      intro m hm hne
      rw [if_neg]
      intro h
      have hl := congrArg List.length h
      rw [List.length_take, hlen] at hl
      have := Finset.mem_range.mp hm
      omega
    calc ∑ m ∈ Finset.range (D + 1),
            ((refineState st (requestPrec st.prec r)).atoms (w.take m)).length +
          requestAtomCount st.prec r
        = ∑ m ∈ Finset.range (D + 1), updatedMass st.prec mass r (w.take m) := by
          simp only [updatedMass, Finset.sum_add_distrib, hinv'.card, hind]
      _ ≤ 2 ^ requestPrec st.prec r := hb'
  have hk : requestAtomCount st.prec r ≤ 2 ^ requestPrec st.prec r := by
    have hw0 := hchain (r.1 ++ List.replicate (D - r.1.length) false) (by
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      refine ⟨?_, List.prefix_append _ _⟩
      have h := mem_exactLengthPrograms_self (r.1 ++ List.replicate (D - r.1.length) false)
      rwa [List.length_append, List.length_replicate, Nat.add_sub_cancel' hzD] at h)
    omega
  have hsup := Finset.sup_le fun w hw => Nat.le_sub_of_add_le (hchain w hw)
  have hA1 := card_ancestor_union_descendant_eq_sup hinv' hDtab hzD
  rw [foldr_max_eq_sup] at hA1
  have hfree := length_freeAtoms_add hinv' r.1
  have hprec : (refineState st (requestPrec st.prec r)).prec = requestPrec st.prec r := rfl
  rw [hprec] at hfree
  omega

/-- Lemma A2 (allocation step preserves the invariants): if the state satisfies the invariants for
`mass` and the updated requested weights satisfy the path budget `≤ 1` at every string (saturation
allowed), then the state after the step satisfies the invariants for the updated masses.
Blueprint 03 Lemma A2. -/
theorem allocStep_invariant {st : AllocState} {mass : BitString → ℕ} (hinv : st.Invariant mass)
    {r : DyadicRequest}
    (hbud : ∀ v, gridLoad (requestPrec st.prec r) (updatedMass st.prec mass r) v ≤ 1) :
    (allocStep st r).Invariant (updatedMass st.prec mass r) :=
  setAtoms_take_freeAtoms_invariant (refineState_invariant hinv (le_max_left st.prec r.2.2)) r.1
    (requestAtomCount_le_length_freeAtoms hinv hbud)

/-- At every string other than the requested one, the atoms after the step are the refined old
atoms. Blueprint 03 Lemma A2 (the added atoms go to `A_z` only). -/
theorem allocStep_atoms_of_ne (st : AllocState) (r : DyadicRequest) {w : BitString} (hw : w ≠ r.1) :
    (allocStep st r).atoms w = (refineState st (requestPrec st.prec r)).atoms w := by
  simp only [allocStep, setAtoms_atoms, if_neg hw]

/-- Under the invariants and the updated path budget, the step adds exactly the requested number of
atoms at `z`: the mass at `z` increases by precisely `delta`. Blueprint 03 Lemma A2 (capacity and
mass). -/
theorem allocStep_mass {st : AllocState} {mass : BitString → ℕ} (hinv : st.Invariant mass)
    {r : DyadicRequest}
    (hbud : ∀ v, gridLoad (requestPrec st.prec r) (updatedMass st.prec mass r) v ≤ 1) :
    ((allocStep st r).atoms r.1).length = updatedMass st.prec mass r r.1 :=
  (allocStep_invariant hinv hbud).card r.1

/-! ### Lemma A3: the step is primitive recursive -/

/-- The precision of a state is primitive recursive. -/
private theorem primrec_prec : Primrec AllocState.prec :=
  (Primrec.fst.comp (Primrec.of_equiv (e := AllocState.equivProd))).of_eq fun _ => rfl

/-- The table of a state is primitive recursive. -/
private theorem primrec_table : Primrec AllocState.table :=
  (Primrec.snd.comp (Primrec.of_equiv (e := AllocState.equivProd))).of_eq fun _ => rfl

/-- Building a state from a precision and a table is primitive recursive. -/
private theorem primrec_mk : Primrec₂ AllocState.mk :=
  (Primrec.of_equiv_symm (e := AllocState.equivProd)).of_eq fun _ => rfl

/-- The row lookup of `BitString` keys through its `BEq` instance is the lookup through the
decidable equality (the two lawful instances coincide). -/
private theorem lookup_eq_lookup_decEq (z : BitString) (t : List (BitString × List ℕ)) :
    @List.lookup _ _ instBEqOfDecidableEq z t = t.lookup z := by
  congr
  exact lawful_beq_subsingleton _ _

/-- `A_z` is primitive recursive in the state and the string. -/
private theorem primrec_atoms : Primrec₂ AllocState.atoms := by
  have h : Primrec fun p : AllocState × BitString =>
      (@List.lookup _ _ instBEqOfDecidableEq p.2 p.1.table).getD [] :=
    Primrec.option_getD.comp (Primrec.listLookup.comp Primrec.snd (primrec_table.comp Primrec.fst))
      (Primrec.const [])
  exact h.of_eq fun p => by rw [lookup_eq_lookup_decEq]; rfl

/-- The prefix test on bit strings is primitive recursive (`v <+: w` iff `w.take |v| = v`). -/
private theorem primrec_decide_prefix : Primrec₂ fun v w : BitString => decide (v <+: w) := by
  have h : Primrec fun p : BitString × BitString => decide (p.2.take p.1.length = p.1) :=
    (PrimrecRel.comp Primrec.eq (Primrec.list_take.comp Primrec.snd
      (Primrec.list_length.comp Primrec.fst)) Primrec.fst).decide
  exact h.of_eq fun p => decide_eq_decide.mpr (eq_comm.trans List.prefix_iff_eq_take.symm)

/-- `P_v` is primitive recursive in the state and the string. -/
private theorem primrec_ancestorAtoms : Primrec₂ AllocState.ancestorAtoms := by
  have h : Primrec fun p : AllocState × BitString =>
      ((List.range p.2.length).map fun k => p.1.atoms (p.2.take k)).flatten :=
    Primrec.list_flatten.comp (Primrec.list_map
      (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd))
      (primrec_atoms.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_take.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)
  exact h.of_eq fun _ => rfl

/-- `Q_v` is primitive recursive in the state and the string. -/
private theorem primrec_descendantAtoms : Primrec₂ AllocState.descendantAtoms := by
  have h : Primrec fun p : AllocState × BitString =>
      (p.1.table.filter fun e => decide (p.2 <+: e.1)).flatMap Prod.snd :=
    Primrec.list_flatMap (Primrec.list_filter (primrec_table.comp Primrec.fst)
      (primrec_decide_prefix.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)).to₂)
      (Primrec.snd.comp Primrec.snd).to₂
  exact h.of_eq fun _ => rfl

/-- `F_z` is primitive recursive in the state and the string. -/
private theorem primrec_freeAtoms : Primrec₂ AllocState.freeAtoms := by
  have hmem : ∀ {l : (AllocState × BitString) × ℕ → List ℕ}, Primrec l →
      Primrec fun q : (AllocState × BitString) × ℕ => (l q).any fun j => decide (j = q.2) :=
    fun hl => list_any_primrec hl
      (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.snd.comp Primrec.fst)).decide.to₂
  have hP := hmem (primrec_ancestorAtoms.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst))
  have hQ := hmem (primrec_descendantAtoms.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst))
  have h : Primrec fun p : AllocState × BitString => (List.range (2 ^ p.1.prec)).filter fun i =>
      !((p.1.ancestorAtoms p.2).any fun j => decide (j = i)) &&
        !((p.1.descendantAtoms p.2).any fun j => decide (j = i)) :=
    Primrec.list_filter (Primrec.list_range.comp
      (nat_pow_primrec₂.comp (Primrec.const 2) (primrec_prec.comp Primrec.fst)))
      (Primrec.and.comp (Primrec.not.comp hP) (Primrec.not.comp hQ)).to₂
  refine h.of_eq fun p => ?_
  unfold AllocState.freeAtoms
  congr 1
  funext i
  have key : ∀ l : List ℕ, (l.any fun j => decide (j = i)) = decide (i ∈ l) := fun l => by
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    simp
  simp only [key, Bool.decide_and, decide_not]

/-- Refinement is primitive recursive in the state and the target precision. -/
private theorem primrec_refineState : Primrec₂ refineState := by
  have hd : Primrec fun p : AllocState × ℕ => 2 ^ (p.2 - p.1.prec) :=
    nat_pow_primrec₂.comp (Primrec.const 2)
      (Primrec.nat_sub.comp Primrec.snd (primrec_prec.comp Primrec.fst))
  have hblk : Primrec fun q : (AllocState × ℕ) × ℕ =>
      (List.range (2 ^ (q.1.2 - q.1.1.prec))).map fun r => q.2 * 2 ^ (q.1.2 - q.1.1.prec) + r :=
    Primrec.list_map (Primrec.list_range.comp (hd.comp Primrec.fst))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst)
        (hd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd).to₂
  have hrow : Primrec fun q : (AllocState × ℕ) × (BitString × List ℕ) =>
      (q.2.1, q.2.2.flatMap fun i =>
        (List.range (2 ^ (q.1.2 - q.1.1.prec))).map fun r => i * 2 ^ (q.1.2 - q.1.1.prec) + r) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.list_flatMap
      (Primrec.snd.comp Primrec.snd)
      (hblk.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂)
  exact (primrec_mk.comp Primrec.snd
    (Primrec.list_map (primrec_table.comp Primrec.fst) hrow.to₂)).of_eq fun _ => rfl

/-- `setAtoms` is primitive recursive. -/
private theorem primrec_setAtoms :
    Primrec fun p : AllocState × BitString × List ℕ => p.1.setAtoms p.2.1 p.2.2 := by
  have hne : Primrec fun q : (AllocState × BitString × List ℕ) × (BitString × List ℕ) =>
      decide (q.2.1 ≠ q.1.2.1) :=
    (PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).not.decide
  exact (primrec_mk.comp (primrec_prec.comp Primrec.fst)
    (Primrec.list_cons.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))
      (Primrec.list_filter (primrec_table.comp Primrec.fst) hne.to₂))).of_eq fun _ => rfl

/-- Lemma A3 (uniform effective allocation): the allocation step is computable in the pair
(state, request). Blueprint 03 Lemma A3. -/
theorem allocStep_computable :
    Computable fun a : AllocState × DyadicRequest => allocStep a.1 a.2 := by
  have hL : Primrec fun a : AllocState × DyadicRequest => max a.1.prec a.2.2.2 :=
    Primrec.nat_max.comp (primrec_prec.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hst : Primrec fun a : AllocState × DyadicRequest => refineState a.1 (max a.1.prec a.2.2.2) :=
    primrec_refineState.comp Primrec.fst hL
  have hz : Primrec fun a : AllocState × DyadicRequest => a.2.1 := Primrec.fst.comp Primrec.snd
  have hk : Primrec fun a : AllocState × DyadicRequest =>
      a.2.2.1 * 2 ^ (max a.1.prec a.2.2.2 - a.2.2.2) :=
    Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (nat_pow_primrec₂.comp (Primrec.const 2)
        (Primrec.nat_sub.comp hL (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hl := Primrec.list_append.comp (primrec_atoms.comp hst hz)
    (Primrec.list_take.comp (primrec_freeAtoms.comp hst hz) hk)
  exact (primrec_setAtoms.comp (Primrec.pair hst (Primrec.pair hz hl))).to_comp.of_eq
    fun _ => rfl

/-- The stage table of the allocator along a request stream: the empty state at stage `0`, one
`allocStep` per emitted request. Blueprint 03 Lemma A3 / §4 (stage table). -/
def allocRun (ρ : RequestStream) : ℕ → AllocState
  | 0 => ⟨0, []⟩
  | s + 1 =>
    match ρ s with
    | some r => allocStep (allocRun ρ s) r
    | none => allocRun ρ s

/-- Lemma A3: the stage table is computable from a computable request stream (compositionally, not
by assumption). Blueprint 03 Lemma A3. -/
theorem allocRun_computable {ρ : RequestStream} (hρ : Computable ρ) : Computable (allocRun ρ) := by
  have hstep : Computable₂ fun (_ : ℕ) (p : ℕ × AllocState) =>
      Option.casesOn (motive := fun _ => AllocState) (ρ p.1) p.2 fun r => allocStep p.2 r :=
    (Computable.option_casesOn (hρ.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
      (allocStep_computable.comp (Computable.pair
        (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd)).to₂).to₂
  refine (Computable.nat_rec Computable.id (Computable.const (⟨0, []⟩ : AllocState))
    hstep).of_eq fun s => ?_
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [id] at ih ⊢
    rw [ih]
    simp only [allocRun]
    cases ρ s <;> rfl

/-- The stage-`(s + 1)` table adds the request of stage `s` (if any) to the stage-`s` table.
Blueprint 01 F3 (F3-STREAM). -/
private theorem streamStageMass_succ (ρ : RequestStream) (s : ℕ) (z : BitString) :
    streamStageMass ρ (s + 1) z = streamStageMass ρ s z +
      (((ρ s).toList.filter fun r => decide (r.1 = z)).map DyadicRequest.weight).sum := by
  simp only [streamStageMass, List.range_succ, List.filterMap_append, List.filter_append,
    List.map_append, List.sum_append]
  cases h : ρ s <;> simp [h]

/-- One step in rational units: the updated masses at precision `max prec L`, divided by
`2 ^ max prec L`, are the old rational masses plus the request weight `k / 2 ^ L` at `z`.
Blueprint 03 Lemma A2 (updated requested weights). -/
private theorem updatedMass_div (prec : ℕ) (mass : BitString → ℕ) (r : DyadicRequest)
    (w : BitString) :
    (updatedMass prec mass r w : ℚ) / 2 ^ requestPrec prec r =
      (mass w : ℚ) / 2 ^ prec + if w = r.1 then r.weight else 0 := by
  obtain ⟨a, ha⟩ : ∃ a, requestPrec prec r = prec + a :=
    ⟨_, (Nat.add_sub_cancel' (le_max_left prec r.2.2)).symm⟩
  obtain ⟨b, hb⟩ : ∃ b, requestPrec prec r = r.2.2 + b :=
    ⟨_, (Nat.add_sub_cancel' (le_max_right prec r.2.2)).symm⟩
  simp only [updatedMass, requestAtomCount, DyadicRequest.weight]
  push_cast
  rw [add_div]
  congr 1
  · rw [ha, Nat.add_sub_cancel_left, pow_add, mul_div_mul_right _ _ (by positivity)]
  · split_ifs
    · rw [hb, Nat.add_sub_cancel_left, pow_add, mul_div_mul_right _ _ (by positivity)]
    · exact zero_div _

/-- Lemma A3 with A2: along a budgeted request stream every stage state satisfies the invariants for
the stage masses, and those masses in units of `2 ^ (-prec)` are exactly the rational masses
`streamStageMass ρ s z` requested so far. Blueprint 03 Lemma A3 (correctness for legal requests). -/
theorem allocRun_invariant {ρ : RequestStream} (hb : IsBudgetedRequestStream ρ) (s : ℕ) :
    ∃ mass : BitString → ℕ, (allocRun ρ s).Invariant mass ∧
      ∀ z, (mass z : ℚ) / 2 ^ (allocRun ρ s).prec = streamStageMass ρ s z := by
  induction s with
  | zero =>
    refine ⟨fun _ => 0, ⟨by simp [allocRun], ?_, ?_, ?_, ?_, ?_⟩, fun z => ?_⟩
    · intro z i hi
      simp [allocRun, AllocState.atoms] at hi
    · intro z
      simp [allocRun, AllocState.atoms]
    · intro z
      simp [allocRun, AllocState.atoms]
    · intro z w _ _ i hi
      simp [allocRun, AllocState.atoms] at hi
    · intro v i j hi
      simp [allocRun, AllocState.descendantAtoms] at hi
    · simp [streamStageMass]
  | succ s ih =>
    obtain ⟨mass, hinv, hmass⟩ := ih
    rcases hρ : ρ s with _ | r
    · refine ⟨mass, ?_, fun z => ?_⟩
      · simpa only [allocRun, hρ] using hinv
      · simp only [allocRun, hρ, streamStageMass_succ, hmass, Option.toList_none,
          List.filter_nil, List.map_nil, List.sum_nil, add_zero]
    · have hstep : ∀ z, (updatedMass (allocRun ρ s).prec mass r z : ℚ) /
          2 ^ requestPrec (allocRun ρ s).prec r = streamStageMass ρ (s + 1) z := by
        intro z
        rw [updatedMass_div, hmass, streamStageMass_succ, hρ]
        by_cases hz : z = r.1
        · simp [hz]
        · simp [hz, Ne.symm hz]
      have hbud : ∀ v, gridLoad (requestPrec (allocRun ρ s).prec r)
          (updatedMass (allocRun ρ s).prec mass r) v ≤ 1 := by
        intro v
        rw [gridLoad]
        simp only [hstep]
        exact hb (s + 1) v
      refine ⟨updatedMass (allocRun ρ s).prec mass r, ?_, fun z => ?_⟩
      · simpa only [allocRun, hρ] using allocStep_invariant hinv hbud
      · simpa only [allocRun, hρ] using hstep z

end Kolmogorov
