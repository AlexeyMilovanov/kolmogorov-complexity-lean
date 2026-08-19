import KolmogorovMathlib.Prefix.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The online Kraft–Chaitin allocator

This file builds the *online* (causal) prefix-free code allocator behind the
Kraft–Chaitin realization theorem and proves its three defining properties:

* `allocFun_computable` — the allocator is computable uniformly in the context;
* `allocFun_prefixFree` — codes for distinct requests are prefix-incomparable;
* `allocFun_success`    — if the total Kraft weight is `≤ 1`, every request is
  realized by a codeword of exactly the requested length.

The algorithm maintains a *free list* of tree nodes (bitstrings) kept in strictly
descending order of length (hence with pairwise distinct lengths).  A length-`l`
request is serviced by taking the unique free node of largest length `≤ l`,
splitting it into a length-`l` left-most descendant (the allocated codeword) and
its right siblings along the all-`false` path, and re-inserting the siblings in
sorted position.

The proofs are organized around three invariants of the free list:

* `DescLengths` (strictly descending lengths ⇒ distinct lengths);
* prefix-freeness of the node set;
* the mass identity `freeMass free + usedMass req n = 1`.

These are each shown to be preserved step by step.
-/

namespace Kolmogorov
namespace KraftChaitin

open scoped ENNReal

/-! ## Core definitions -/

/-- Split a node `v` of length `≤ l` into a length-`l` left-most descendant (all
`false` continuation) and the list of its right siblings along that path. -/
def splitNode (v : BitString) (l : ℕ) : BitString × List BitString :=
  let diff := l - v.length
  let allocated := v ++ List.replicate diff false
  let newNodes := (List.range diff).map (fun i => v ++ List.replicate i false ++ [true])
  (allocated, newNodes)

/-- Allocate one prefix-free codeword of length `l` from the free list.

Finds the free node of largest length `≤ l` (the *first* such node when the list
is sorted in descending order of length), allocates a length-`l` descendant, and
re-inserts the unallocated right siblings — in descending length order — into the
position the chosen node occupied.  This keeps the free list sorted. -/
def allocateOne (free : List BitString) (l : ℕ) : Option (BitString × List BitString) :=
  match free.findIdx? (fun v => v.length ≤ l) with
  | none => none
  | some idx =>
    let v := free[idx]!
    let (allocated, newNodes) := splitNode v l
    some (allocated, free.take idx ++ newNodes.reverse ++ free.drop (idx + 1))

/-- The state of the online allocator (its free list) after processing the first
`n` requests. -/
def allocatorState (req : ℕ → Option (BitString × ℕ)) (n : ℕ) : Option (List BitString) :=
  match n with
  | 0 => some [[]]
  | n' + 1 =>
    match allocatorState req n' with
    | none => none
    | some free =>
      match req n' with
      | none => some free
      | some (_, l) =>
        match allocateOne free l with
        | none => none
        | some (_, free') => some free'

/-- The allocation function giving the `n`-th codeword. -/
def allocFun (req : ℕ → Option (BitString × ℕ)) (n : ℕ) : Option BitString :=
  match allocatorState req n with
  | none => none
  | some free =>
    match req n with
    | none => none
    | some (_, l) =>
      match allocateOne free l with
      | none => none
      | some (allocated, _) => some allocated

/-- The dyadic mass `2^{-|v|}` of a single node. -/
noncomputable def nodeMass (v : BitString) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ v.length

/-- The total Kraft mass of a free list. -/
noncomputable def freeMass (free : List BitString) : ℝ≥0∞ := (free.map nodeMass).sum

/-- The Kraft mass requested by request `i`. -/
noncomputable def reqMass (req : ℕ → Option (BitString × ℕ)) (i : ℕ) : ℝ≥0∞ :=
  match req i with
  | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
  | none => 0

/-- The total Kraft mass used by the first `n` requests. -/
noncomputable def usedMass (req : ℕ → Option (BitString × ℕ)) (n : ℕ) : ℝ≥0∞ :=
  (Finset.range n).sum (reqMass req)

/-- The free list has strictly descending node lengths (hence distinct lengths). -/
def DescLengths (free : List BitString) : Prop :=
  free.IsChain (fun a b => b.length < a.length)

private lemma isChain_get_fin {α} {R : α → α → Prop} {l : List α}
    (h : List.IsChain R l) (i : Fin l.length.pred) :
    R (l.get (Fin.cast (by
        have hi : i.1 + 1 < l.length := Nat.succ_lt_of_lt_pred i.2
        exact Nat.succ_pred_eq_of_pos (by omega)) i.castSucc))
      (l.get (Fin.cast (by
        have hi : i.1 + 1 < l.length := Nat.succ_lt_of_lt_pred i.2
        exact Nat.succ_pred_eq_of_pos (by omega)) i.succ)) := by
  have hi : i.1 + 1 < l.length := Nat.succ_lt_of_lt_pred i.2
  simpa using (List.isChain_iff_getElem.mp h i.1 hi)

private lemma isChain_iff_get_fin {α} {R : α → α → Prop} {l : List α} :
    List.IsChain R l ↔ ∀ i : Fin l.length.pred,
      R (l.get (Fin.cast (by
          have hi : i.1 + 1 < l.length := Nat.succ_lt_of_lt_pred i.2
          exact Nat.succ_pred_eq_of_pos (by omega)) i.castSucc))
        (l.get (Fin.cast (by
          have hi : i.1 + 1 < l.length := Nat.succ_lt_of_lt_pred i.2
          exact Nat.succ_pred_eq_of_pos (by omega)) i.succ)) := by
  constructor
  · intro h i
    exact isChain_get_fin h i
  · intro h
    rw [List.isChain_iff_getElem]
    intro i hi
    have hfin := h ⟨i, Nat.lt_pred_iff.mpr hi⟩
    simpa using hfin

private lemma descLengths_getElem_length_lt {free : List BitString} (hd : DescLengths free)
    {i j : ℕ} (hij : i < j) (hj : j < free.length) :
    (free[j]'hj).length < (free[i]'(lt_trans hij hj)).length := by
  haveI : Trans (fun a b : BitString => b.length < a.length)
      (fun a b : BitString => b.length < a.length)
      (fun a b : BitString => b.length < a.length) :=
    ⟨fun {a b c : BitString} (hab : b.length < a.length) (hbc : c.length < b.length) =>
      lt_trans hbc hab⟩
  have hp : List.Pairwise (fun a b : BitString => b.length < a.length) free :=
    List.isChain_iff_pairwise.mp hd
  rw [List.pairwise_iff_get] at hp
  simpa using hp ⟨i, lt_trans hij hj⟩ ⟨j, hj⟩ (by simpa using hij)

/-! ## Elementary `splitNode` facts -/

/-- The allocated descendant has exactly the requested length. -/
lemma splitNode_length (v : BitString) (l : ℕ) (hl : v.length ≤ l) :
    (splitNode v l).1.length = l := by
  simp only [splitNode, List.append_assoc, List.length_append, List.length_replicate,
    Nat.add_sub_of_le hl]

/-- The original node `v` is a prefix of the allocated descendant. -/
lemma splitNode_allocated_prefix (v : BitString) (l : ℕ) :
    v <+: (splitNode v l).1 := by
  simp only [splitNode]
  exact ⟨List.replicate (l - v.length) false, rfl⟩

/-- Every right sibling produced by the split is a descendant of `v`. -/
lemma splitNode_newNodes_prefix (v : BitString) (l : ℕ) :
    ∀ x ∈ (splitNode v l).2, v <+: x := by
  intro x hx
  simp only [splitNode, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact ⟨List.replicate i false ++ [true], by simp only [List.append_assoc]⟩

/-- The right siblings produced by the split all have length in `(|v|, l]`. -/
lemma splitNode_newNodes_length (v : BitString) (l : ℕ) :
    ∀ x ∈ (splitNode v l).2, v.length < x.length ∧ x.length ≤ l := by
  intro x hx
  simp only [splitNode, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  refine ⟨?_, ?_⟩ <;>
    simp only [List.length_append, List.length_replicate, List.length_singleton] <;> omega

/-
**Mass conservation for a single split.**  When `|v| ≤ l`, the mass of `v`
equals the mass of the allocated descendant plus the masses of all the right
siblings.
-/
lemma splitNode_mass (v : BitString) (l : ℕ) (_hl : v.length ≤ l) :
    nodeMass v
      = nodeMass (splitNode v l).1 + (((splitNode v l).2).map nodeMass).sum := by
  -- A finite geometric identity in `ℝ≥0∞`: `2⁻¹ ^ a` splits into the mass of the
  -- length-`(a + n)` descendant plus the masses `2⁻¹ ^ (a + i + 1)` of the siblings.
  have geomSplit : ∀ a n : ℕ,
      (2⁻¹ : ℝ≥0∞) ^ a = 2⁻¹ ^ (a + n) + ∑ i ∈ Finset.range n, 2⁻¹ ^ (a + i + 1) := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hcollapse :
          (2⁻¹ : ℝ≥0∞) ^ (a + (n + 1)) + 2⁻¹ ^ (a + n + 1) = 2⁻¹ ^ (a + n) := by
        have h1 : (2⁻¹ : ℝ≥0∞) ^ (a + (n + 1)) = 2⁻¹ ^ (a + n) * 2⁻¹ := by
          rw [show a + (n + 1) = (a + n) + 1 from by ring, pow_succ]
        have h2 : (2⁻¹ : ℝ≥0∞) ^ (a + n + 1) = 2⁻¹ ^ (a + n) * 2⁻¹ := by rw [pow_succ]
        rw [h1, h2, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
      calc (2⁻¹ : ℝ≥0∞) ^ a
          = 2⁻¹ ^ (a + n) + ∑ i ∈ Finset.range n, 2⁻¹ ^ (a + i + 1) := ih
        _ = (2⁻¹ ^ (a + (n + 1)) + 2⁻¹ ^ (a + n + 1))
              + ∑ i ∈ Finset.range n, 2⁻¹ ^ (a + i + 1) := by rw [hcollapse]
        _ = 2⁻¹ ^ (a + (n + 1))
              + (∑ i ∈ Finset.range n, 2⁻¹ ^ (a + i + 1) + 2⁻¹ ^ (a + n + 1)) := by ring
  -- The sibling masses, summed over `List.range`, agree with the `Finset.range` sum.
  have listRange_map_sum : ∀ (f : ℕ → ℝ≥0∞) (n : ℕ),
      ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
    intro f n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
      simp
  simp only [nodeMass, splitNode, List.length_append, List.length_replicate, List.map_map]
  rw [geomSplit v.length (l - v.length), listRange_map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, nodeMass, List.length_append, List.length_replicate,
    List.length_singleton]

/-
The two children families produced by a split are pairwise prefix-incomparable:
the allocated leaf and all right siblings form an antichain.
-/
lemma splitNode_antichain (v : BitString) (l : ℕ) :
    IsPrefixFree ↑(((splitNode v l).1 :: (splitNode v l).2).toFinset) := by
  intro p hp q hq hpq
  unfold splitNode at *
  simp +zetaDelta only [List.append_assoc, List.toFinset_cons, Finset.coe_insert,
    List.coe_toFinset, List.mem_map, List.mem_range, Set.mem_insert_iff,
    Set.mem_setOf_eq] at *
  rcases hp with (rfl | ⟨a, ha, rfl⟩) <;>
    rcases hq with (rfl | ⟨b, hb, rfl⟩) <;>
      simp_all +decide only [List.prefix_append_right_inj, List.append_cancel_left_eq]
  · have hle : l - v.length ≤ b + 1 := by
      simpa only [List.length_replicate, List.length_append, List.length_singleton] using
        hpq.length_le
    apply hpq.eq_of_length
    simp only [List.length_replicate, List.length_append, List.length_singleton]
    omega
  · have hpq_eq : List.replicate a false ++ [true] =
        List.take (a + 1) (List.replicate (l - v.length) false) := by
      simpa only [List.prefix_iff_eq_take, List.length_append, List.length_replicate,
        List.length_singleton] using hpq
    replace hpq_eq := congr_arg (fun x => x[a]!) hpq_eq
    simp_all +decide
  · have := hpq.length_le
    have hab : a ≤ b := by
      simpa only [List.length_append, List.length_replicate, List.length_singleton,
        Nat.add_le_add_iff_right] using this
    rcases hab.eq_or_lt with hab | hab
    · subst b
      rfl
    · have hpq_eq : List.replicate a false ++ [true] =
          List.take (a + 1) (List.replicate b false ++ [true]) := by
        simpa only [List.prefix_iff_eq_take, List.length_append, List.length_replicate,
          List.length_singleton] using hpq
      replace hpq_eq := congr_arg (fun x => x[a]!) hpq_eq
      simp_all +decide

/-! ## Descendant monotonicity of the free list

These facts are independent of the ordering of the free list and only use that
`allocateOne` replaces one node by descendants of it. -/

/-
Anything prefix-incomparable to `v` is prefix-incomparable to every descendant
of `v`.
-/
lemma not_prefix_of_descendant {c v d : BitString} (hvd : v <+: d)
    (hcv : ¬ c <+: v) (hvc : ¬ v <+: c) : ¬ c <+: d := by
  intro hcd
  exact (List.prefix_or_prefix_of_prefix hcd hvd).elim hcv hvc

/-
Every node remaining after one allocation step has a prefix among the nodes
present before the step.
-/
lemma allocateOne_free_descendant (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free')) :
    ∀ w ∈ free', ∃ u ∈ free, u <+: w := by
  unfold allocateOne at h
  rcases hidx : free.findIdx? (fun v => v.length ≤ l) with _ | idx
  · rw [hidx] at h; simp at h
  · rw [hidx] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hfree'⟩ := h
    have hlt : idx < free.length := (List.findIdx?_eq_some_iff_getElem.mp hidx).1
    have hmem : free[idx]! ∈ free := by
      rw [getElem!_pos free idx hlt]; exact List.getElem_mem hlt
    intro w hw
    rw [← hfree'] at hw
    simp only [List.mem_append, List.mem_reverse] at hw
    rcases hw with (hw | hw) | hw
    · exact ⟨w, List.mem_of_mem_take hw, List.prefix_refl _⟩
    · exact ⟨free[idx]!, hmem, splitNode_newNodes_prefix free[idx]! l w hw⟩
    · exact ⟨w, List.mem_of_mem_drop hw, List.prefix_refl _⟩

/-
The allocated codeword is a descendant of some node present before the step.
-/
lemma allocateOne_allocated_descendant (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free')) :
    ∃ u ∈ free, u <+: a := by
  unfold allocateOne at h
  rcases hidx : free.findIdx? (fun v => v.length ≤ l) with _ | idx
  · rw [hidx] at h; simp at h
  · rw [hidx] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨ha, -⟩ := h
    have hlt : idx < free.length := (List.findIdx?_eq_some_iff_getElem.mp hidx).1
    refine ⟨free[idx]!, ?_, ?_⟩
    · rw [getElem!_pos free idx hlt]
      exact List.getElem_mem hlt
    · rw [← ha]
      exact splitNode_allocated_prefix free[idx]! l

/-
After an allocation step the allocated codeword is prefix-incomparable to every
remaining free node, provided the free list was prefix-free.
-/
lemma allocateOne_alloc_incomp_free' (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free'))
    (hpf : IsPrefixFree ↑free.toFinset) (hd : DescLengths free) :
    ∀ w ∈ free', ¬ a <+: w ∧ ¬ w <+: a := by
  unfold allocateOne at h
  cases hfind : List.findIdx? (fun v => decide (v.length ≤ l)) free with
  | none => simp only [hfind, reduceCtorEq] at h
  | some idx =>
      simp only [hfind, List.getElem!_eq_getElem?_getD, List.append_assoc,
        Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨ha, hfree'⟩
      subst a
      subst free'
      have hidx : idx < free.length := by
        have := List.findIdx?_eq_some_iff_getElem.mp hfind
        grind
      have hselected_mem : free[idx]! ∈ free := by
        rw [getElem!_pos free idx hidx]
        exact List.getElem_mem hidx
      have hnodup : List.Nodup free := by
        have hlen_nodup : List.Nodup (List.map List.length free) := by
          have hchain : List.IsChain (fun a b => b < a) (List.map List.length free) := by
            rw [List.isChain_iff_getElem]
            intro i hi
            simpa using (List.isChain_iff_getElem.mp hd i (by simpa using hi))
          exact (List.isChain_iff_pairwise.mp hchain).nodup
        exact List.Nodup.of_map (fun x => x.length) hlen_nodup
      have old_incomp (w : BitString)
          (hw : w ∈ free.take idx ++ free.drop (idx + 1)) :
          ¬ (splitNode free[idx]! l).1 <+: w ∧ ¬ w <+: (splitNode free[idx]! l).1 := by
        have hw_free : w ∈ free := by
          rcases List.mem_append.mp hw with hw | hw
          · exact List.mem_of_mem_take hw
          · exact List.mem_of_mem_drop hw
        have hne : free[idx]! ≠ w := by
          rw [← List.eraseIdx_eq_take_drop_succ] at hw
          obtain ⟨i, hi, hine, hiw⟩ := List.mem_eraseIdx_iff_getElem.mp hw
          intro heq
          rw [getElem!_pos free idx hidx] at heq
          have hfin : (⟨i, hi⟩ : Fin free.length) = ⟨idx, hidx⟩ :=
            (List.nodup_iff_injective_get.mp hnodup) (by simpa using hiw.trans heq.symm)
          exact hine (congr_arg Fin.val hfin)
        have hselected_set : free[idx]! ∈ ↑free.toFinset := by simpa using hselected_mem
        have hw_set : w ∈ ↑free.toFinset := by simpa using hw_free
        have hselected_not_prefix : ¬ free[idx]! <+: w := fun hp =>
          hne (hpf hselected_set hw_set hp)
        have hw_not_prefix : ¬ w <+: free[idx]! := fun hp =>
          hne (hpf hw_set hselected_set hp).symm
        have hprefix := splitNode_allocated_prefix free[idx]! l
        exact ⟨fun hp => hselected_not_prefix (hprefix.trans hp),
          not_prefix_of_descendant hprefix hw_not_prefix hselected_not_prefix⟩
      have new_incomp (w : BitString) (hw : w ∈ (splitNode free[idx]! l).2) :
          ¬ (splitNode free[idx]! l).1 <+: w ∧ ¬ w <+: (splitNode free[idx]! l).1 := by
        have hne : (splitNode free[idx]! l).1 ≠ w := by
          unfold splitNode at hw ⊢
          simp only [List.mem_map, List.mem_range] at hw
          obtain ⟨i, _, rfl⟩ := hw
          intro heq
          rw [List.append_assoc] at heq
          have heq := List.append_cancel_left heq
          have htrue : true ∈ List.replicate (l - free[idx]!.length) false := by
            rw [heq]
            simp
          simp at htrue
        have hanti := splitNode_antichain free[idx]! l
        have hallocated : (splitNode free[idx]! l).1 ∈
            ↑(((splitNode free[idx]! l).1 :: (splitNode free[idx]! l).2).toFinset) := by simp
        have hw_set : w ∈
            ↑(((splitNode free[idx]! l).1 :: (splitNode free[idx]! l).2).toFinset) := by
          rw [List.mem_toFinset]
          exact List.mem_cons.mpr (Or.inr hw)
        exact ⟨fun hp => hne (hanti hallocated hw_set hp),
          fun hp => hne (hanti hw_set hallocated hp).symm⟩
      intro w hw
      simp only [List.mem_append, List.mem_reverse] at hw
      rcases hw with hw | hw | hw
      · simpa only [List.getElem!_eq_getElem?_getD] using
          old_incomp w (List.mem_append_left _ hw)
      · have hw' : w ∈ (splitNode free[idx]! l).2 := by
          simpa only [List.getElem!_eq_getElem?_getD] using hw
        simpa only [List.getElem!_eq_getElem?_getD] using new_incomp w hw'
      · simpa only [List.getElem!_eq_getElem?_getD] using
          old_incomp w (List.mem_append_right _ hw)

/-
Prefix-freeness of the free list is preserved by one allocation step.
-/
lemma allocateOne_prefixFree (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free'))
    (hpf : IsPrefixFree ↑free.toFinset) (hd : DescLengths free) :
    IsPrefixFree ↑free'.toFinset := by
  obtain ⟨idx, hidx, -, -⟩ : ∃ idx, free.findIdx? (fun v => v.length ≤ l) = some idx ∧ free[idx]! ∈
      free ∧ free[idx]!.length ≤ l := by
    unfold allocateOne at h
    cases h_idx : free.findIdx? (fun v => v.length ≤ l) with
    | none =>
      simp only [h_idx] at h
      contradiction
    | some idx =>
      obtain ⟨h_len, h_pred, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h_idx
      refine ⟨idx, rfl, ?_, ?_⟩
      · rw [getElem!_pos free idx h_len]
        exact List.getElem_mem h_len
      · rw [getElem!_pos free idx h_len]
        exact of_decide_eq_true h_pred
  have h_idx_lt : idx < free.length := (List.findIdx?_eq_some_iff_getElem.mp hidx).1
  have h_new_nodes_antichain' : IsPrefixFree (↑((splitNode free[idx]! l).2.toFinset)) := by
    intro p hp q hq hpq
    apply splitNode_antichain free[idx]! l
    · change p ∈ ((splitNode free[idx]! l).1 :: (splitNode free[idx]! l).2).toFinset
      rw [List.mem_toFinset]
      exact List.mem_cons.mpr (Or.inr (by simpa using hp))
    · change q ∈ ((splitNode free[idx]! l).1 :: (splitNode free[idx]! l).2).toFinset
      rw [List.mem_toFinset]
      exact List.mem_cons.mpr (Or.inr (by simpa using hq))
    · exact hpq
  have h_disjoint : ∀ p ∈ free.take idx ++ free.drop (idx + 1), p ≠ free[idx]! ∧ ¬ free[idx]! <+: p
      ∧ ¬ p <+: free[idx]! := by
    intro p hp
    have h_distinct : p ≠ free[idx]! := by
      have h_distinct : List.Nodup free := by
        have h_distinct : List.Nodup free := by
          have h_chain : List.IsChain (fun a b => b.length < a.length) free := hd
          have h_distinct : List.Pairwise (fun a b => a.length ≠ b.length) free := by
            rw [ List.pairwise_iff_get ];
            intro i j hij
            exact ne_of_gt (descLengths_getElem_length_lt h_chain hij j.2)
          exact List.Pairwise.imp_of_mem ( by aesop ) h_distinct;
        exact h_distinct;
      intro h_eq
      have h_contradiction : List.Nodup
          (List.take idx free ++ free[idx]! :: List.drop (idx + 1) free) := by
        convert h_distinct using 1;
        simp +zetaDelta only [List.coe_toFinset, List.getElem!_eq_getElem?_getD,
          List.mem_append] at *;
        rw [ List.getElem?_eq_getElem h_idx_lt ];
        simp +zetaDelta only [Option.getD_some, List.getElem_cons_drop,
            List.take_append_drop] at *;
      grind
    have h_incomparable : ¬ free[idx]! <+: p ∧ ¬ p <+: free[idx]! := by
      have h_incomparable : ∀ p ∈ free, p ≠ free[idx]! →
          ¬ free[idx]! <+: p ∧ ¬ p <+: free[idx]! := by
        intros p hp hp_ne; exact ⟨by
        exact fun h => hp_ne <| hpf ( by aesop ) ( by aesop ) h ▸ rfl, by
          exact fun h => hp_ne <| hpf ( by aesop ) ( by aesop ) h⟩;
      apply h_incomparable p (by
      rw [ List.mem_append ] at hp;
      exact hp.elim (fun hp => List.mem_of_mem_take hp)
        (fun hp => List.mem_of_mem_drop hp)) h_distinct
    exact ⟨h_distinct, h_incomparable⟩;
  have h_disjoint : ∀ p ∈ free.take idx ++ free.drop (idx + 1),
      ∀ q ∈ (splitNode free[idx]! l).2, ¬ p <+: q ∧ ¬ q <+: p := by
    intro p hp q hq
    have h_not_prefix_p := h_disjoint p hp
    have h_q_desc := splitNode_newNodes_prefix free[idx]! l q hq
    exact ⟨not_prefix_of_descendant h_q_desc h_not_prefix_p.2.2 h_not_prefix_p.2.1,
      fun h_q_p => h_not_prefix_p.2.1 (h_q_desc.trans h_q_p)⟩
  have hfree' : free' = free.take idx ++
      ((splitNode free[idx]! l).2.reverse ++ free.drop (idx + 1)) := by
    unfold allocateOne at h
    simp only [hidx, List.getElem!_eq_getElem?_getD, List.append_assoc,
      Option.some.injEq, Prod.mk.injEq] at h
    simpa only [List.getElem!_eq_getElem?_getD] using h.2.symm
  have mem_old_or_new {x : BitString} (hx : x ∈ ↑free'.toFinset) :
      x ∈ free.take idx ++ free.drop (idx + 1) ∨ x ∈ (splitNode free[idx]! l).2 := by
    have hx : x ∈ free' := by simpa using hx
    rw [hfree'] at hx
    simp only [List.mem_append, List.mem_reverse] at hx ⊢
    tauto
  have old_mem_free {x : BitString}
      (hx : x ∈ free.take idx ++ free.drop (idx + 1)) : x ∈ free := by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_of_mem_take hx
    · exact List.mem_of_mem_drop hx
  intro p hp q hq hpq
  rcases mem_old_or_new hp with hp_old | hp_new
  · rcases mem_old_or_new hq with hq_old | hq_new
    · exact hpf (by simpa using old_mem_free hp_old) (by simpa using old_mem_free hq_old) hpq
    · exact False.elim ((h_disjoint p hp_old q hq_new).1 hpq)
  · rcases mem_old_or_new hq with hq_old | hq_new
    · exact False.elim ((h_disjoint q hq_old p hp_new).2 hpq)
    · exact h_new_nodes_antichain' (by simpa using hp_new) (by simpa using hq_new) hpq

/-! ## Length and mass behaviour of one allocation step -/

/-
`allocateOne` fails exactly when no free node has length `≤ l`.
-/
lemma allocateOne_eq_none_iff (free : List BitString) (l : ℕ) :
    allocateOne free l = none ↔ ∀ v ∈ free, l < v.length := by
  calc
    allocateOne free l = none ↔
        List.findIdx? (fun v => decide (v.length ≤ l)) free = none := by
      unfold allocateOne
      cases List.findIdx? (fun v => decide (v.length ≤ l)) free <;> simp
    _ ↔ ∀ v ∈ free, decide (v.length ≤ l) = false :=
      List.findIdx?_eq_none_iff
    _ ↔ ∀ v ∈ free, l < v.length := by simp

/-
If some free node has length `≤ l`, `allocateOne` succeeds.
-/
lemma allocateOne_isSome_of_exists (free : List BitString) (l : ℕ)
    (h : ∃ v ∈ free, v.length ≤ l) : (allocateOne free l).isSome := by
  contrapose! h;
  simp_all +decide [ allocateOne_eq_none_iff ]

/-
The codeword produced by a successful allocation has exactly length `l`.
-/
lemma allocateOne_length (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free')) :
    a.length = l := by
  unfold allocateOne at h
  rcases hidx : free.findIdx? (fun v => v.length ≤ l) with _ | idx
  · rw [hidx] at h; simp at h
  · rw [hidx] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨ha, -⟩ := h
    have hv : (free[idx]!).length ≤ l := by
      obtain ⟨hlt, hpred, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt] using hpred
    rw [← ha]
    exact splitNode_length _ _ hv

/-
**Mass conservation for one allocation step.**
-/
lemma allocateOne_mass (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free')) :
    freeMass free' + nodeMass a = freeMass free := by
  unfold allocateOne at h;
  rcases h' : List.findIdx? (fun v => decide (List.length v ≤ l)) free with (_ | idx)
  · simp_all +decide
  simp_all +decide only [List.getElem!_eq_getElem?_getD, List.append_assoc,
    Option.some.injEq, Prod.mk.injEq];
  have hv : (free[idx]!).length ≤ l := by
    obtain ⟨hlt, hpred, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h'
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt] using hpred
  have ha : a = (splitNode free[idx]! l).1 := by
    simpa only [List.getElem!_eq_getElem?_getD] using h.1.symm
  have h_split : nodeMass (free[idx]!) = nodeMass a +
      (List.map nodeMass (splitNode (free[idx]!) l).2).sum := by
    rw [ha]; exact splitNode_mass free[idx]! l hv
  have h_freeMass_split : freeMass free = freeMass (free.take idx) + nodeMass (free[idx]!) +
      freeMass (free.drop (idx + 1)) := by
    have h_freeMass_split : free = free.take idx ++ [free[idx]!] ++ free.drop (idx + 1) := by
      have h_free : idx < free.length := (List.findIdx?_eq_some_iff_getElem.mp h').1
      simp +decide only [h_free, getElem!_pos, List.take_append_getElem, List.take_append_drop];
    conv_lhs => rw [ h_freeMass_split ];
    unfold freeMass; simp +decide [ List.sum_append ] ;
    ring;
  simp_all +decide only [List.getElem!_eq_getElem?_getD, freeMass, List.map_take, List.map_drop];
  rw [ ← h.2 ] ; simp +decide [ List.map_append, List.sum_append ] ; ring;

/-
One allocation step preserves descending lengths.
-/
lemma allocateOne_descLengths (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free'))
    (hd : DescLengths free) : DescLengths free' := by
  unfold allocateOne at h;
  rcases h' : List.findIdx? (fun v => decide (List.length v ≤ l)) free with (_ | idx)
  · simp_all +decide
  simp_all +decide only [List.getElem!_eq_getElem?_getD, List.append_assoc,
    Option.some.injEq, Prod.mk.injEq];
  have h_desc : List.IsChain (fun a b => b.length < a.length)
      (List.take idx free ++ List.reverse (splitNode (free[idx]!) l).2 ++
        List.drop (idx + 1) free) := by
    apply List.isChain_append.mpr;
    refine ⟨ ?_, ?_, ?_ ⟩;
    · refine List.isChain_append.mpr ⟨ ?_, ?_, ?_ ⟩;
      · apply List.IsChain.take;
        exact hd;
      · unfold splitNode
        simp +decide only [List.getElem!_eq_getElem?_getD, List.append_assoc,
          List.isChain_reverse]
        rw [ isChain_iff_get_fin ];
        simp +decide ;
      · have h_last_take : ∀ x ∈ List.take idx free, x.length > l := by
          intro x hx
          have := List.mem_iff_getElem.mp hx
          simp_all +decide only [List.getElem_take, List.length_take, lt_inf_iff,
            gt_iff_lt]
          obtain ⟨i, hi, rfl⟩ := this
          have := List.findIdx?_eq_some_iff_getElem.mp h'
          simp_all +decide only [decide_eq_true_eq, not_le, gt_iff_lt];
          exact this.choose_spec.2 i hi.1;
        have h_last_take : ∀ y ∈ (splitNode (free[idx]!) l).2, y.length ≤ l := by
          intros y hy; exact (splitNode_newNodes_length (free[idx]!) l y hy).right;
        grind;
    · exact List.IsChain.drop hd (idx + 1)
    · have h_after : ∀ y ∈ List.drop (idx + 1) free, y.length < (free[idx]!).length := by
        intro y hy
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
        have hidx : idx < free.length := (List.findIdx?_eq_some_iff_getElem.mp h').1
        have hj : idx + 1 + i < free.length := by
          have hle : idx + 1 ≤ free.length := by omega
          have hlt : i < free.length - (idx + 1) := by
            simpa [List.length_drop, Nat.add_sub_assoc hle] using hi
          omega
        rw [getElem!_pos free idx hidx]
        simpa [List.getElem_drop, add_assoc] using
          descLengths_getElem_length_lt hd (i := idx) (j := idx + 1 + i) (by omega) hj
      have h_split : ∀ x ∈ List.reverse (splitNode (free[idx]!) l).2, x.length ≥
          (free[idx]!).length
          + 1 := by
        simp [splitNode];
      have h_before : ∀ x ∈ List.take idx free, (free[idx]!).length < x.length := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hidx : idx < free.length := (List.findIdx?_eq_some_iff_getElem.mp h').1
        have hi_idx : i < idx := by
          simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)] using hi
        rw [getElem!_pos free idx hidx]
        simpa [List.getElem_take] using
          descLengths_getElem_length_lt hd (i := i) (j := idx) hi_idx hidx
      intro x hx y hy
      have hy_after := h_after y (List.mem_of_mem_head? hy)
      rcases List.mem_append.mp (List.mem_of_mem_getLast? hx) with hx_before | hx_split
      · exact lt_trans hy_after (h_before x hx_before)
      · have hx_bound := h_split x hx_split
        omega
  rw [← h.2]
  simpa only [DescLengths, List.getElem!_eq_getElem?_getD, List.append_assoc] using h_desc

/-! ## Serviceability from distinct lengths -/

/-
A free list with strictly descending lengths all `> l` has mass `< 2^{-l}`.
-/
lemma freeMass_lt_of_all_gt (free : List BitString) (l : ℕ)
    (hd : DescLengths free) (hgt : ∀ v ∈ free, l < v.length) :
    freeMass free < (2 : ℝ≥0∞)⁻¹ ^ l := by
  -- Since the lengths are strictly decreasing, we can order the elements in the free list by their
  --   lengths.
  have h_order : ∃ (f : ℕ → BitString), (∀ i < free.length, f i ∈ free) ∧
      (∀ i j, i < j → i < free.length → j < free.length → f i ≠ f j) ∧
      (∀ i < free.length, List.length (f i) > l) ∧
      (∀ i j, i < j → i < free.length → j < free.length →
        List.length (f i) > List.length (f j)) := by
    use fun i => if hi : i < free.length then free[i]! else [];
    refine ⟨ ?_, ?_, ?_, ?_ ⟩;
    · grind;
    · intro i j hij hi hj
      simp only [hi, hj, dite_true, getElem!_pos]
      intro heq
      have hlen := descLengths_getElem_length_lt hd hij hj
      exact (ne_of_gt hlen) (congr_arg List.length heq)
    · aesop;
    · intro i j hij hi hj
      simp only [hi, hj, dite_true, getElem!_pos]
      exact descLengths_getElem_length_lt hd hij hj
  obtain ⟨f, hf_mem, hf_distinct, hf_length, hf_order⟩ := h_order;
  have h_sum : freeMass free ≤
      ∑ i ∈ Finset.range free.length, (2⁻¹ : ℝ≥0∞) ^ List.length (f i) := by
    have h_sum : freeMass free ≤
        ∑ i ∈ Finset.image f (Finset.range free.length), (2⁻¹ : ℝ≥0∞) ^ List.length i := by
      have h_sum : freeMass free =
          ∑ i ∈ free.toFinset, (2⁻¹ : ℝ≥0∞) ^ List.length i := by
        have h_sum : List.Nodup free := by
          have h_distinct : ∀ i j, i < j → i < free.length → j < free.length →
              free[i]! ≠ free[j]! := by
            intro i j hij hi hj heq
            rw [getElem!_pos free i hi, getElem!_pos free j hj] at heq
            have hlen := descLengths_getElem_length_lt hd hij hj
            exact (ne_of_gt hlen) (congr_arg List.length heq)
          rw [ List.nodup_iff_injective_get ];
          intros i j hij;
          exact le_antisymm
            (le_of_not_gt fun hi => h_distinct _ _ hi (by simp) (by simp) <| by
              simpa [Fin.cast_val_eq_self] using hij.symm)
            (le_of_not_gt fun hj => h_distinct _ _ hj (by simp) (by simp) <| by
              simpa [Fin.cast_val_eq_self] using hij);
        rw [ List.sum_toFinset ];
        · rfl;
        · assumption;
      rw [h_sum];
      rw [Finset.eq_of_subset_of_card_le
        (show Finset.image f (Finset.range free.length) ⊆ free.toFinset from
          Finset.image_subset_iff.mpr fun i hi => by aesop)];
      rw [Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm
        (le_of_not_gt fun hi' =>
          hf_distinct _ _ hi' (Finset.mem_range.mp hj) (Finset.mem_range.mp hi) hij.symm)
        (le_of_not_gt fun hj' =>
          hf_distinct _ _ hj' (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij),
        Finset.card_range];
      exact List.toFinset_card_le _;
    rwa [Finset.sum_image <| by
      intros i hi j hj hij
      exact le_antisymm
        (le_of_not_gt fun hi' =>
          hf_distinct _ _ hi' (Finset.mem_range.mp hj) (Finset.mem_range.mp hi) hij.symm)
        (le_of_not_gt fun hj' =>
          hf_distinct _ _ hj' (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij)] at h_sum;
  -- Since the lengths are strictly decreasing, we can bound each term in the sum.
  have h_bound : ∀ i < free.length, (2⁻¹ : ℝ≥0∞) ^ (List.length (f i)) ≤ (2⁻¹ : ℝ≥0∞) ^
      (l + 1 + (free.length - 1 - i)) := by
    intros i hi
    have h_length : List.length (f i) ≥ l + 1 + (free.length - 1 - i) := by
      induction hdist : free.length - 1 - i generalizing i with
      | zero =>
          have := hf_length i hi
          omega
      | succ d ih =>
          have hi_succ : i + 1 < free.length := by omega
          have hnext : free.length - 1 - (i + 1) = d := by omega
          have hih := ih (i + 1) hi_succ hnext
          have hstep := hf_order i (i + 1) (Nat.lt_succ_self i) hi hi_succ
          omega
    exact pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) h_length;
  refine lt_of_le_of_lt h_sum <| lt_of_le_of_lt
    (Finset.sum_le_sum fun i hi => h_bound i <| Finset.mem_range.mp hi) ?_;
  norm_num [ pow_add, Finset.mul_sum _ _ _, Finset.sum_mul ];
  rw [ ← Finset.mul_sum _ _ _, ← Finset.sum_range_reflect ];
  rw [Finset.sum_congr rfl fun i hi => by
    rw [tsub_tsub_cancel_of_le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))]];
  ring_nf;
  rw [ ← ENNReal.toReal_lt_toReal ] <;> norm_num;
  · rw [ENNReal.toReal_sum]
    · norm_num [geom_sum_eq]
      ring_nf
      norm_num
    · exact fun _ _ => ENNReal.pow_ne_top <| by norm_num;
  · norm_num [ ENNReal.mul_eq_top ]

/-- **Serviceability.**  A free list of descending lengths with mass `≥ 2^{-l}`
contains a node of length `≤ l`. -/
lemma exists_fit_of_mass_ge (free : List BitString) (l : ℕ)
    (hd : DescLengths free) (hmass : (2 : ℝ≥0∞)⁻¹ ^ l ≤ freeMass free) :
    ∃ v ∈ free, v.length ≤ l := by
  by_contra hcon
  push Not at hcon
  exact absurd hmass (not_le.mpr (freeMass_lt_of_all_gt free l hd hcon))

/-! ## Unconditional invariants of the free list

Prefix-freeness, descending lengths, and the mass identity hold whenever the
state exists, with no hypothesis on the total Kraft weight. -/

/-
The free list is always prefix-free.
-/
lemma allocatorState_prefixFree (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (free : List BitString)
    (h : allocatorState req n = some free) : IsPrefixFree ↑free.toFinset := by
  have hgood : ∀ k free, allocatorState req k = some free →
      IsPrefixFree ↑free.toFinset ∧ DescLengths free := by
    intro k
    induction k with
    | zero =>
        intro free hfree
        simp only [allocatorState, Option.some.injEq] at hfree
        subst free
        constructor <;> simp [IsPrefixFree, DescLengths]
    | succ k ih =>
        intro free hfree
        rw [allocatorState] at hfree
        cases hstate : allocatorState req k with
        | none => simp only [hstate, reduceCtorEq] at hfree
        | some previous =>
            have hprevious := ih previous hstate
            cases hreq : req k with
            | none =>
                simp only [hstate, hreq, Option.some.injEq] at hfree
                subst free
                exact hprevious
            | some request =>
                rcases request with ⟨out, length⟩
                cases halloc : allocateOne previous length with
                | none => simp only [hstate, hreq, halloc, reduceCtorEq] at hfree
                | some result =>
                    rcases result with ⟨allocated, next⟩
                    simp only [hstate, hreq, halloc, Option.some.injEq] at hfree
                    subst free
                    exact ⟨allocateOne_prefixFree previous length allocated next halloc
                        hprevious.1 hprevious.2,
                      allocateOne_descLengths previous length allocated next halloc hprevious.2⟩
  exact (hgood n free h).1

/-
The free list always has strictly descending lengths.
-/
lemma allocatorState_descLengths (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (free : List BitString)
    (h : allocatorState req n = some free) : DescLengths free := by
  induction n generalizing free with
  | zero => cases h ; tauto
  | succ n ih =>
    obtain ⟨free₀, h₀⟩ : ∃ free₀, allocatorState req n = some free₀ := by
      cases h' : allocatorState req n
      · simp_all +decide only [allocatorState, reduceCtorEq]
      simp_all +decide only [Option.some.injEq, forall_eq', exists_eq', allocatorState]
    cases h' : req n
    · simp_all +decide only [allocatorState]
    simp_all +decide only [Option.some.injEq, forall_eq', allocatorState]
    cases h'' : allocateOne free₀ ‹BitString × ℕ›.2
    · simp_all +decide only [reduceCtorEq]
    simp_all +decide only [Option.some.injEq]
    exact h ▸ allocateOne_descLengths _ _ _ _ h'' ih

/-
The free mass plus the used mass is always exactly `1`.
-/
lemma allocatorState_mass (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (free : List BitString)
    (h : allocatorState req n = some free) : freeMass free + usedMass req n = 1 := by
  induction n generalizing free with
  | zero =>
    cases h ; norm_num [ freeMass, usedMass ];
    unfold nodeMass; norm_num;
  | succ n ih =>
    by_cases h1 : allocatorState req n = none;
    · unfold allocatorState at h; aesop;
    · obtain ⟨free₀, hfree₀⟩ : ∃ free₀, allocatorState req n = some free₀ := by
        exact Option.ne_none_iff_exists'.mp h1;
      by_cases h2 : req n = none <;>
        simp_all +decide only [Option.some.injEq, forall_eq', allocatorState,
          reduceCtorEq, not_false_eq_true];
      · unfold usedMass; simp_all +decide only [Finset.sum_range_succ] ;
        unfold reqMass; aesop;
      · obtain ⟨fst, l, hl⟩ : ∃ fst l, req n = some (fst, l) := by
          cases h : req n <;> tauto;
        obtain ⟨a, free', hallocate⟩ : ∃ a free', allocateOne free₀ l = some (a, free') ∧ free =
            free' := by
          cases h' : allocateOne free₀ l <;> aesop;
        have h_mass : freeMass free' + nodeMass a = freeMass free₀ := by
          apply allocateOne_mass; exact hallocate.left;
        have h_mass : nodeMass a = (2 : ℝ≥0∞)⁻¹ ^ l := by
          have h_mass : a.length = l := by
            exact allocateOne_length free₀ l a free' hallocate.1;
          exact h_mass ▸ rfl;
        simp_all +decide only [usedMass, reduceCtorEq, not_false_eq_true, Finset.sum_range_succ];
        simp_all +decide only [reqMass, ← add_assoc];
        rw [ add_right_comm, ← ih, ← ‹freeMass free' + 2⁻¹ ^ l = freeMass free₀› ]

/-
Each partial Kraft sum is bounded by the total.
-/
lemma usedMass_le_tsum (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    usedMass req n ≤ ∑' i, reqMass req i := by
  exact ENNReal.sum_le_tsum (Finset.range n)

/-
Given the global Kraft bound `≤ 1`, the allocator never fails.
-/
lemma allocatorState_isSome (req : ℕ → Option (BitString × ℕ)) (n : ℕ)
    (hweight : (∑' i, reqMass req i) ≤ 1) : (allocatorState req n).isSome := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h : allocatorState req n with ( _ | ⟨ free₀ ⟩ ) <;>
      simp_all +decide only [Option.isSome_some];
    by_cases hreq : req n = none;
    · simp +decide only [allocatorState, h, hreq, Option.isSome_some];
    · obtain ⟨o, l⟩ : ∃ o l, req n = some (o, l) := by
        cases h : req n <;> tauto;
      obtain ⟨l, hl⟩ : ∃ l, req n = some (o, l) := l
      have h_mass : freeMass free₀ + usedMass req n = 1 := by
        convert allocatorState_mass req n free₀ h using 1
      have h_usedMass : usedMass req (n + 1) = usedMass req n + reqMass req n := by
        exact Finset.sum_range_succ _ _
      have h_reqMass : reqMass req n = (2 : ℝ≥0∞)⁻¹ ^ l := by
        unfold reqMass; aesop;
      have h_freeMass : (2 : ℝ≥0∞)⁻¹ ^ l ≤ freeMass free₀ := by
        have h_freeMass : usedMass req (n + 1) ≤ 1 := by
          exact le_trans ( usedMass_le_tsum req ( n + 1 ) ) hweight;
        contrapose! h_freeMass;
        rw [ ← h_mass, h_usedMass, h_reqMass ];
        rw [ add_comm ] ; gcongr;
        exact ne_of_lt (lt_of_le_of_lt (usedMass_le_tsum req n)
          (lt_of_le_of_lt hweight (by norm_num)))
      have h_exists_fit : ∃ v ∈ free₀, v.length ≤ l := by
        apply exists_fit_of_mass_ge free₀ l (allocatorState_descLengths req n free₀ h) h_freeMass
      have h_allocateOne : (allocateOne free₀ l).isSome :=
        allocateOne_isSome_of_exists free₀ l h_exists_fit
      simp only [allocatorState, h, hl]
      cases h' : allocateOne free₀ l with
      | none =>
        rw [h'] at h_allocateOne
        contradiction
      | some res => exact Option.isSome_some

/-! ## Computability building blocks -/

/-- `drop n` is iterated `tail`, hence primitive recursive. -/
theorem drop_eq_iterate {α} (n : ℕ) (l : List α) : l.drop n = (List.tail)^[n] l := by
  induction n generalizing l with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ', Function.comp_apply, ← ih, List.tail_drop]

/-- `take n` expressed via `reverse` and `drop`. -/
theorem take_eq_rev {α} (n : ℕ) (l : List α) :
    l.take n = (l.reverse.drop (l.length - n)).reverse := by
  rw [← List.reverse_take, List.reverse_reverse]

/-- `findIdx?` expressed via `findIdx` and a length comparison. -/
theorem findIdx?_eq_ite {α} (p : α → Bool) (l : List α) :
    l.findIdx? p = if l.findIdx p < l.length then some (l.findIdx p) else none := by
  by_cases h : l.findIdx p < l.length
  · simp only [h, if_true]
    rw [List.findIdx?_eq_some_iff_findIdx_eq]; exact ⟨h, rfl⟩
  · simp only [h, if_false]
    rw [List.findIdx?_eq_none_iff]
    have hlen : l.findIdx p = l.length := le_antisymm List.findIdx_le_length (not_lt.mp h)
    rw [List.findIdx_eq_length] at hlen
    exact hlen

/-- `List.drop` (as a binary function) is primitive recursive. -/
theorem drop_primrec {α} [Primcodable α] : Primrec₂ (fun (l : List α) (n : ℕ) => l.drop n) := by
  have h : Primrec (fun p : List α × ℕ => (List.tail)^[p.2] p.1) :=
    Primrec.nat_iterate Primrec.snd Primrec.fst (Primrec.list_tail.comp Primrec.snd).to₂
  exact h.of_eq (fun p => (drop_eq_iterate p.2 p.1).symm)

/-- `List.take` (as a binary function) is primitive recursive. -/
theorem take_primrec {α} [Primcodable α] : Primrec₂ (fun (l : List α) (n : ℕ) => l.take n) := by
  have hdrop : Primrec₂ (fun (l : List α) (n : ℕ) => l.drop n) := drop_primrec
  have h : Primrec (fun p : List α × ℕ => ((p.1.reverse).drop (p.1.length - p.2)).reverse) := by
    apply Primrec.list_reverse.comp
    apply hdrop.comp (Primrec.list_reverse.comp Primrec.fst)
    exact Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd
  exact h.of_eq (fun p => (take_eq_rev p.2 p.1).symm)

/-- `List.replicate _ false` is primitive recursive. -/
theorem replicate_false_primrec : Primrec (fun n : ℕ => List.replicate n false) := by
  have : (fun n : ℕ => List.replicate n false) =
      (fun n => (List.range n).map (fun _ => false)) := by
    funext n; rw [List.map_const']; simp
  rw [this]
  exact Primrec.list_range.list_map (Primrec.const false).to₂

/-
`splitNode` is computable.
-/
/-- `splitNode` (as a binary function) is primitive recursive. -/
lemma splitNode_primrec : Primrec (fun p : BitString × ℕ => splitNode p.1 p.2) := by
  refine Primrec.pair ?_ ?_
  · exact Primrec.list_append.comp Primrec.fst
      (replicate_false_primrec.comp (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst)))
  · refine Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst))) ?_
    exact (Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
        (replicate_false_primrec.comp Primrec.snd))
      (Primrec.const [true])).to₂

lemma splitNode_computable :
    Computable (fun p : BitString × ℕ => splitNode p.1 p.2) :=
  splitNode_primrec.to_comp

/-- `getElem!` on a free list is primitive recursive. -/
lemma getElem!_primrec : Primrec₂ (fun (l : List BitString) (i : ℕ) => l[i]!) :=
  (Primrec.option_getD.comp Primrec.list_getElem? (Primrec.const default)).of_eq
    (fun _ => (List.getElem!_eq_getElem?_getD ..).symm)

/-- The length-fit search used by `allocateOne` is primitive recursive. -/
lemma findIdx?_pred_primrec :
    Primrec (fun p : List BitString × ℕ =>
      p.1.findIdx? (fun v => decide (v.length ≤ p.2))) := by
  have hR : PrimrecRel (fun (p : List BitString × ℕ) (v : BitString) => v.length ≤ p.2) :=
    Primrec.nat_le.comp₂ (Primrec.list_length.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  have hj : Primrec (fun p : List BitString × ℕ =>
      p.1.findIdx (fun v => decide (v.length ≤ p.2))) :=
    Primrec.list_findIdx Primrec.fst hR.decide
  exact (Primrec.ite (Primrec.nat_lt.comp hj (Primrec.list_length.comp Primrec.fst))
      (Primrec.option_some.comp hj) (Primrec.const none)).of_eq
    (fun _ => (findIdx?_eq_ite _ _).symm)

/-- `allocateOne` written as an `Option.map` over the fit search. -/
lemma allocateOne_eq_map (free : List BitString) (l : ℕ) :
    allocateOne free l = (free.findIdx? (fun v => decide (v.length ≤ l))).map
      (fun idx => ((splitNode free[idx]! l).1,
        free.take idx ++ (splitNode free[idx]! l).2.reverse ++ free.drop (idx + 1))) := by
  unfold allocateOne
  cases free.findIdx? (fun v => decide (v.length ≤ l)) <;> rfl

-- Treat the data functions opaquely from here on: their definitions have already
-- been characterized by the equational lemmas above, and keeping them reducible
-- makes the `Computable`/`Primrec` combinator unifications whnf-unfold these large
-- definitions, which is prohibitively slow.
attribute [local irreducible] splitNode allocateOne

/-- `allocateOne` is computable. -/
lemma allocateOne_computable :
    Computable (fun p : List BitString × ℕ => allocateOne p.1 p.2) := by
  apply Primrec.to_comp
  have hv : Primrec (fun a : (List BitString × ℕ) × ℕ => a.1.1[a.2]!) :=
    getElem!_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hnode : Primrec (fun a : (List BitString × ℕ) × ℕ => splitNode a.1.1[a.2]! a.1.2) :=
    splitNode_primrec.comp (Primrec.pair hv (Primrec.snd.comp Primrec.fst))
  have hg : Primrec₂ (fun (p : List BitString × ℕ) (idx : ℕ) =>
      ((splitNode p.1[idx]! p.2).1,
        p.1.take idx ++ (splitNode p.1[idx]! p.2).2.reverse ++ p.1.drop (idx + 1))) := by
    refine Primrec.pair (Primrec.fst.comp hnode) ?_
    exact Primrec.list_append.comp
      (Primrec.list_append.comp
        (take_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.list_reverse.comp (Primrec.snd.comp hnode)))
      (drop_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp Primrec.snd))
  exact (Primrec.option_map findIdx?_pred_primrec hg).of_eq
    (fun p => (allocateOne_eq_map p.1 p.2).symm)

/-- `allocatorState` rewritten as an explicit `Nat.rec` with a combinator-friendly step. -/
lemma allocatorState_eq_rec (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    allocatorState req n = Nat.rec (some [[]])
      (fun y IH => IH.bind (fun free =>
        ((req y).map (fun pr => (allocateOne free pr.2).map Prod.snd)).getD (some free))) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have step_eq : ∀ X : Option (List BitString),
        (match X with
          | none => none
          | some free => match req k with
            | none => some free
            | some (_, l) => match allocateOne free l with
              | none => none
              | some (_, free') => some free')
        = X.bind (fun free =>
            ((req k).map (fun pr => (allocateOne free pr.2).map Prod.snd)).getD (some free)) := by
      intro X
      cases X with
      | none => rfl
      | some free =>
        simp only [Option.bind_some]
        rcases hr : req k with _ | ⟨o, l⟩
        · rfl
        · simp only [Option.map_some]
          rcases allocateOne free l with _ | ⟨a, free'⟩ <;> rfl
    calc allocatorState req (k + 1)
        = (match allocatorState req k with
            | none => none
            | some free => match req k with
              | none => some free
              | some (_, l) => match allocateOne free l with
                | none => none
                | some (_, free') => some free') := by rw [allocatorState]
      _ = (allocatorState req k).bind (fun free =>
            ((req k).map (fun pr => (allocateOne free pr.2).map Prod.snd)).getD (some free)) :=
            step_eq _
      _ = _ := by rw [ih]

attribute [local irreducible] allocatorState

lemma allocatorState_hinner_free_comp :
    Computable (fun (p : (((BitString × ℕ) × (ℕ × Option (List BitString))) ×
      List BitString) × (BitString × ℕ)) => p.1.2) :=
  Computable.snd.comp Computable.fst

lemma allocatorState_hinner_length_comp :
    Computable (fun (p : (((BitString × ℕ) × (ℕ × Option (List BitString))) ×
      List BitString) × (BitString × ℕ)) => p.2.2) :=
  Computable.snd.comp Computable.snd

-- Extracted as a helper to isolate the slow `Primcodable` elaboration.
/-- Helper for allocatorState_hinner_computable: computability of allocateOne inner step. -/
lemma allocatorState_hinner_computable :
    Computable₂
      (fun (d : ((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString)
        (pr : BitString × ℕ) => (allocateOne d.2 pr.2).map Prod.snd) := by
  refine Computable.option_map ?_ (Computable.snd.comp Computable.snd).to₂
  exact @Computable.comp
    ((((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString) × (BitString × ℕ))
    (List BitString × ℕ)
    (Option (BitString × List BitString))
    inferInstance inferInstance inferInstance
    (fun (p : List BitString × ℕ) => allocateOne p.1 p.2)
    (fun p => (p.1.2, p.2.2))
    allocateOne_computable
    (allocatorState_hinner_free_comp.pair allocatorState_hinner_length_comp)

/-- Helper for allocatorState_computable: computability of the bind step. -/
lemma allocatorState_hstep_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable₂ (fun (p : BitString × ℕ) (q : ℕ × Option (List BitString)) =>
      q.2.bind (fun free =>
        ((req p.1 q.1).map (fun pr => (allocateOne free pr.2).map Prod.snd)).getD
          (some free))) := by
  have hreq : Computable
      (fun d : ((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString =>
        req d.1.1.1 d.1.2.1) :=
    @Computable.comp (((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString)
      (BitString × ℕ) (Option (BitString × ℕ))
      inferInstance inferInstance inferInstance
      (fun p => req p.1 p.2)
      (fun d => (d.1.1.1, d.1.2.1))
      hcomp
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.fst.comp (Computable.snd.comp Computable.fst)))
  have hg : Computable
      (fun d : ((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString =>
        ((req d.1.1.1 d.1.2.1).map
          (fun pr => (allocateOne d.2 pr.2).map Prod.snd)).getD (some d.2)) :=
    Computable.option_getD (Computable.option_map hreq allocatorState_hinner_computable)
      (Computable.option_some.comp Computable.snd)
  exact Computable.option_bind (Computable.snd.comp Computable.snd) hg

/-- The allocator state is computable uniformly in the context.

The `Nat.rec` step function is built by `Computable` combinators over a deeply
nested product of list types, whose `Primcodable` encoders make elaboration
unusually slow. -/
lemma allocatorState_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable (fun p : BitString × ℕ => allocatorState (req p.1) p.2) := by
  have hstep := allocatorState_hstep_computable req hcomp
  refine (Computable.nat_rec Computable.snd (Computable.const (some [[]])) hstep).of_eq ?_
  intro p
  exact (allocatorState_eq_rec (req p.1) p.2).symm

/-! ## The three top-level obligations -/

/-- `allocFun` rewritten as a bind over the allocator state. -/
lemma allocFun_eq_bind (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    allocFun req n = (allocatorState req n).bind (fun free =>
      ((req n).map (fun pr => (allocateOne free pr.2).map Prod.fst)).getD none) := by
  unfold allocFun
  rcases allocatorState req n with _ | free
  · rfl
  · simp only [Option.bind_some]
    rcases req n with _ | ⟨o, l⟩
    · rfl
    · simp only [Option.map_some]
      rcases allocateOne free l with _ | ⟨a, free'⟩ <;> rfl

lemma allocFun_hinner_free_comp :
    Computable (fun p : ((BitString × ℕ) × List BitString) × (BitString × ℕ) => p.1.2) :=
  Computable.snd.comp Computable.fst

lemma allocFun_hinner_length_comp :
    Computable (fun p : ((BitString × ℕ) × List BitString) × (BitString × ℕ) => p.2.2) :=
  Computable.snd.comp Computable.snd

/-- Helper for allocFun_computable: computability of the allocateOne step. -/
lemma allocFun_hinner_computable :
    Computable₂ (fun (e : (BitString × ℕ) × List BitString) (pr : BitString × ℕ) =>
        (allocateOne e.2 pr.2).map Prod.fst) := by
  refine Computable.option_map ?_ (Computable.fst.comp Computable.snd).to₂
  exact @Computable.comp
    (((BitString × ℕ) × List BitString) × (BitString × ℕ))
    (List BitString × ℕ)
    (Option (BitString × List BitString))
    inferInstance inferInstance inferInstance
    (fun p : List BitString × ℕ => allocateOne p.1 p.2)
    (fun p => (p.1.2, p.2.2))
    allocateOne_computable
    (allocFun_hinner_free_comp.pair allocFun_hinner_length_comp)

/-- Helper for allocFun_computable: computability of the map and getD step. -/
lemma allocFun_hg_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable₂ (fun (p : BitString × ℕ) (free : List BitString) =>
      ((req p.1 p.2).map (fun pr => (allocateOne free pr.2).map Prod.fst)).getD none) := by
  have hreq : Computable (fun e : (BitString × ℕ) × List BitString => req e.1.1 e.1.2) :=
    hcomp.comp Computable.fst
  exact Computable.option_getD
    (Computable.option_map hreq allocFun_hinner_computable) (Computable.const none)

/-- The allocation function is computable uniformly in the context. -/
lemma allocFun_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable (fun p : BitString × ℕ => allocFun (req p.1) p.2) := by
  have hg := allocFun_hg_computable req hcomp
  refine (Computable.option_bind (allocatorState_computable req hcomp) hg).of_eq ?_
  intro p
  exact (allocFun_eq_bind (req p.1) p.2).symm

/-
If step `n` produces a codeword, the state after step `n` exists.
-/
lemma allocFun_state_succ (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (cn : BitString)
    (hn : allocFun req n = some cn) : ∃ free', allocatorState req (n + 1) = some free' := by
  unfold allocFun at hn;
  unfold allocatorState; aesop;

/-
The codeword allocated at step `n` is prefix-incomparable to every node still
free after step `n`.
-/
lemma alloc_incomp_freeNext (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (cn : BitString)
    (hn : allocFun req n = some cn) (free' : List BitString)
    (hfree' : allocatorState req (n + 1) = some free') :
    ∀ w ∈ free', ¬ cn <+: w ∧ ¬ w <+: cn := by
  obtain ⟨free, hfree⟩ : ∃ free, allocatorState req n = some free := by
    cases h : allocatorState req n
    · simp_all +decide only [allocFun, reduceCtorEq]
    simp_all +decide only [allocFun, Option.some.injEq, exists_eq']
  unfold allocFun at hn;
  rcases h : req n with ( _ | ⟨ fst, l ⟩ )
  · simp_all +decide only [reduceCtorEq]
  simp_all +decide only
  rcases h' : allocateOne free l with ( _ | ⟨ allocated, snd ⟩ )
  · simp_all +decide only [reduceCtorEq]
  simp_all +decide only [Option.some.injEq]
  have h_succ : allocatorState req (n + 1) = some snd := by
    simp only [allocatorState, hfree, h, h']
  have h_eq : free' = snd := Option.some.inj (hfree'.symm.trans h_succ)
  rw [h_eq]
  apply allocateOne_alloc_incomp_free' free l cn snd h'
    (allocatorState_prefixFree req n free hfree)
    (allocatorState_descLengths req n free hfree)

/-
Descendant monotonicity of the free list: a node free at a later step has a
prefix among the nodes free at an earlier step.
-/
lemma allocatorState_descendant_mono (req : ℕ → Option (BitString × ℕ)) (k k' : ℕ) (hk : k ≤ k')
    (F F' : List BitString) (h : allocatorState req k = some F)
    (h' : allocatorState req k' = some F') :
    ∀ w ∈ F', ∃ u ∈ F, u <+: w := by
  induction hk generalizing F F' with
  | refl =>
      intro w hw
      have hFF' : F = F' := by
        simpa [h] using h'
      subst F'
      exact ⟨w, hw, List.prefix_refl w⟩
  | step hkm ih =>
      rename_i m
      unfold allocatorState at h'
      cases hG : allocatorState req m with
      | none =>
          rw [hG] at h'
          cases h'
      | some G =>
          cases hreq : req m with
          | none =>
              have hGF' : G = F' := by
                simpa [hG, hreq] using h'
              subst F'
              exact ih F G h hG
          | some pr =>
              rcases pr with ⟨a, l⟩
              cases halloc : allocateOne G l with
              | none =>
                  simp only [hG, hreq, halloc, reduceCtorEq] at h'
              | some out =>
                  rcases out with ⟨a', free'⟩
                  have hfree' : free' = F' := by
                    simpa [hG, hreq, halloc] using h'
                  subst F'
                  intro w hw
                  obtain ⟨u, hu, huw⟩ := allocateOne_free_descendant G l a' free' halloc w hw
                  obtain ⟨v, hv, hvu⟩ := ih F G h hG u hu
                  exact ⟨v, hv, List.IsPrefix.trans hvu huw⟩

/-
The codeword allocated at step `m` is a descendant of some node free at step `m`.
-/
lemma allocFun_descendant_state (req : ℕ → Option (BitString × ℕ)) (m : ℕ) (cm : BitString)
    (hm : allocFun req m = some cm) :
    ∃ Fm, allocatorState req m = some Fm ∧ ∃ u ∈ Fm, u <+: cm := by
  unfold allocFun at hm;
  rcases h : allocatorState req m with (_ | Fm)
  · simp_all +decide only [reduceCtorEq]
  rcases h' : req m with (_ | ⟨fst, l⟩)
  · simp_all +decide only [reduceCtorEq]
  simp_all +decide only [Option.some.injEq, exists_eq_left']
  rcases h'' : allocateOne Fm l with ( _ | ⟨ allocated, snd ⟩ )
  · simp_all +decide only [reduceCtorEq]
  simp_all +decide only [Option.some.injEq]
  exact allocateOne_allocated_descendant Fm l cm snd h''

/-- For `m > n`, the codeword allocated at step `m` has a prefix among the nodes
free after step `n`. -/
lemma alloc_descendant_freeNext (req : ℕ → Option (BitString × ℕ)) (n m : ℕ) (cm : BitString)
    (hnm : n < m) (hm : allocFun req m = some cm) (free' : List BitString)
    (hfree' : allocatorState req (n + 1) = some free') :
    ∃ w ∈ free', w <+: cm := by
  obtain ⟨Fm, hFm, u, hu, hupre⟩ := allocFun_descendant_state req m cm hm
  obtain ⟨w, hw, hwpre⟩ := allocatorState_descendant_mono req (n + 1) m hnm free' Fm hfree' hFm u hu
  exact ⟨w, hw, hwpre.trans hupre⟩

lemma allocFun_prefixFree (req : ℕ → Option (BitString × ℕ)) (n m : ℕ) (cn cm : BitString)
    (hn : allocFun req n = some cn) (hm : allocFun req m = some cm) (hneq : n ≠ m) :
    ¬ List.IsPrefix cn cm := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · obtain ⟨free', hfree'⟩ := allocFun_state_succ req n cn hn
    obtain ⟨w, hw, hwpre⟩ := alloc_descendant_freeNext req n m cm hlt hm free' hfree'
    obtain ⟨h1, h2⟩ := alloc_incomp_freeNext req n cn hn free' hfree' w hw
    exact not_prefix_of_descendant hwpre h1 h2
  · exact absurd heq hneq
  · obtain ⟨free', hfree'⟩ := allocFun_state_succ req m cm hm
    obtain ⟨w, hw, hwpre⟩ := alloc_descendant_freeNext req m n cn hgt hn free' hfree'
    obtain ⟨_, h2⟩ := alloc_incomp_freeNext req m cm hm free' hfree' w hw
    exact fun hcontra => h2 (hwpre.trans hcontra)

lemma allocFun_success (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (o : BitString) (l : ℕ)
    (hreq : req n = some (o, l))
    (hweight : (∑' i, match req i with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1) :
    ∃ c, allocFun req n = some c ∧ c.length = l := by
  -- Reduce the inline Kraft sum to `reqMass`.
  have hw : (∑' i, reqMass req i) ≤ 1 := by
    refine le_trans (le_of_eq ?_) hweight
    exact tsum_congr (fun i => by simp only [reqMass])
  -- The state exists at step `n`.
  obtain ⟨free, hstate⟩ : ∃ free, allocatorState req n = some free := by
    have := allocatorState_isSome req n hw
    exact Option.isSome_iff_exists.mp this
  have hd : DescLengths free := allocatorState_descLengths req n free hstate
  have hmass : freeMass free + usedMass req n = 1 := allocatorState_mass req n free hstate
  -- Serviceability: the free mass is at least `2^{-l}`.
  have hreqn : reqMass req n = (2 : ℝ≥0∞)⁻¹ ^ l := by simp only [reqMass, hreq]
  have hpartial : usedMass req n + (2 : ℝ≥0∞)⁻¹ ^ l ≤ 1 := by
    have hsucc : usedMass req (n + 1) ≤ ∑' i, reqMass req i := usedMass_le_tsum req (n + 1)
    have hstep : usedMass req (n + 1) = usedMass req n + reqMass req n := by
      simp only [usedMass, Finset.sum_range_succ]
    rw [hstep, hreqn] at hsucc
    exact le_trans hsucc hw
  have hmassge : (2 : ℝ≥0∞)⁻¹ ^ l ≤ freeMass free := by
    by_contra hlt
    push Not at hlt
    have : freeMass free + usedMass req n < (2 : ℝ≥0∞)⁻¹ ^ l + usedMass req n :=
      ENNReal.add_lt_add_right (by
        have : usedMass req n ≤ 1 := le_trans (usedMass_le_tsum req n) hw
        exact ne_top_of_le_ne_top (by norm_num) this) hlt
    rw [hmass, add_comm ((2 : ℝ≥0∞)⁻¹ ^ l)] at this
    exact absurd hpartial (not_le.mpr this)
  obtain ⟨v, hv, hvl⟩ := exists_fit_of_mass_ge free l hd hmassge
  -- Allocation succeeds, with the requested length.
  obtain ⟨a, free', halloc⟩ : ∃ a free', allocateOne free l = some (a, free') := by
    have := allocateOne_isSome_of_exists free l ⟨v, hv, hvl⟩
    obtain ⟨⟨a, free'⟩, h⟩ := Option.isSome_iff_exists.mp this
    exact ⟨a, free', h⟩
  refine ⟨a, ?_, allocateOne_length free l a free' halloc⟩
  simp only [allocFun, hstate, hreq, halloc]

end KraftChaitin
end Kolmogorov
