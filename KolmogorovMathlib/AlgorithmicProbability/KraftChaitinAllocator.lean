/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.Prefix.Basic
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple

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

These are bundled in `AllocGood` and shown to be preserved step by step.
-/

namespace Kolmogorov
namespace KraftChaitin

open scoped ENNReal
open Computability

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
  simp [splitNode, List.length_append, Nat.add_sub_of_le hl]

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
  exact ⟨List.replicate i false ++ [true], by simp [List.append_assoc]⟩

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
  intro p hp q hq;
  simp +zetaDelta at *;
  rcases hp with ( rfl | hp ) <;> rcases hq with ( rfl | hq );
  · exact fun _ => rfl;
  · unfold splitNode at *;
    simp +zetaDelta at *;
    rcases hq with ⟨ a, ha, rfl ⟩ ; simp_all +decide [ List.prefix_iff_eq_take ] ;
  · unfold splitNode at *;
    simp +zetaDelta at *;
    rcases hp with ⟨ a, ha, rfl ⟩;
    intro h;
    have := h.getElem ( show a + v.length < List.length ( v ++ ( List.replicate a false ++ [ true ] ) ) from by simp +arith +decide ) ; simp_all +decide [ List.getElem_append_right ] ;
  · intro h;
    unfold splitNode at hp hq;
    simp +zetaDelta at *;
    rcases hp with ⟨ a, ha, rfl ⟩ ; rcases hq with ⟨ b, hb, rfl ⟩ ; simp_all +decide [ List.IsPrefix ];
    rcases h with ⟨ t, ht ⟩ ; replace ht := congr_arg ( fun x => x.takeWhile ( fun y => y = false ) ) ht ; simp_all +decide  ;

/-! ## Descendant monotonicity of the free list

These facts are independent of the ordering of the free list and only use that
`allocateOne` replaces one node by descendants of it. -/

/-
Anything prefix-incomparable to `v` is prefix-incomparable to every descendant
of `v`.
-/
lemma not_prefix_of_descendant {c v d : BitString} (hvd : v <+: d)
    (hcv : ¬ c <+: v) (hvc : ¬ v <+: c) : ¬ c <+: d := by
  grind +suggestions

/-
Every node remaining after one allocation step has a prefix among the nodes
present before the step.
-/
lemma allocateOne_free_descendant (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free')) :
    ∀ w ∈ free', ∃ u ∈ free, u <+: w := by
  unfold allocateOne at h;
  cases h' : List.findIdx? ( fun v => decide ( List.length v ≤ l ) ) free <;> simp_all +decide;
  rw [ ← h.2 ];
  simp +zetaDelta at *;
  rintro w ( hw | hw | hw );
  · exact ⟨ w, List.mem_of_mem_take hw, List.prefix_refl _ ⟩;
  · use free[‹ℕ›]!;
    grind +suggestions;
  · exact ⟨ w, List.mem_of_mem_drop hw, List.prefix_refl _ ⟩

/-
The allocated codeword is a descendant of some node present before the step.
-/
lemma allocateOne_allocated_descendant (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free')) :
    ∃ u ∈ free, u <+: a := by
  unfold allocateOne at h;
  rcases h' : List.findIdx? ( fun v => decide ( List.length v ≤ l ) ) free with ( _ | idx ) <;> simp_all +decide;
  use free[idx]!;
  grind +suggestions

/-
After an allocation step the allocated codeword is prefix-incomparable to every
remaining free node, provided the free list was prefix-free.
-/
lemma allocateOne_alloc_incomp_free' (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free'))
    (hpf : IsPrefixFree ↑free.toFinset) (hd : DescLengths free) :
    ∀ w ∈ free', ¬ a <+: w ∧ ¬ w <+: a := by
  intro w hw;
  by_cases h_cases : w ∈ (splitNode (free[(free.findIdx? (fun v => v.length ≤ l)).get!]!) l).2.reverse;
  · have h_antichain : IsPrefixFree ↑(((splitNode (free[(free.findIdx? (fun v => v.length ≤ l)).get!]!) l).1 :: (splitNode (free[(free.findIdx? (fun v => v.length ≤ l)).get!]!) l).2).toFinset) := by
      convert splitNode_antichain _ _ using 1;
    have h_a : a = (splitNode (free[(free.findIdx? (fun v => v.length ≤ l)).get!]!) l).1 := by
      unfold allocateOne at h
      cases hidx : List.findIdx? (fun v => decide (v.length ≤ l)) free <;> simp_all
    have h_a_ne_w : a ≠ w := by
      unfold splitNode at *; simp_all +decide [ List.mem_reverse ] ;
      rcases h_cases with ⟨ a, ha, rfl ⟩ ; simp +decide  ;
      intro H; have := congr_arg List.reverse H; norm_num at this;
      cases h : l - List.length ( free[(List.findIdx? ( fun v => decide ( List.length v ≤ l ) ) free).get!]?.getD default ) <;> simp_all +decide [ List.replicate ];
    simp_all +decide [ IsPrefixFree ];
    grind;
  · -- Since $w$ is not in the reversed list of new nodes, it must be in the take or drop part of the original free list.
    have h_take_drop : w ∈ free.take (free.findIdx? (fun v => v.length ≤ l)).get! ∨ w ∈ free.drop ((free.findIdx? (fun v => v.length ≤ l)).get! + 1) := by
      grind +locals;
    have h_neq : w ≠ free[(free.findIdx? (fun v => v.length ≤ l)).get!]! := by
      have h_neq : List.Nodup free := by
        have h_nodup : List.Nodup (List.map List.length free) := by
          have h_nodup : List.IsChain (fun a b => b < a) (List.map List.length free) := by
            rw [List.isChain_iff_getElem]
            intro i hi
            simpa using (List.isChain_iff_getElem.mp hd i (by simpa using hi))
          exact List.isChain_iff_pairwise.mp h_nodup |> fun h => h.nodup;
        exact List.Nodup.of_map ( fun x => x.length ) h_nodup;
      cases h_take_drop <;> simp_all +decide [ List.mem_iff_get ];
      · cases h : List.findIdx? ( fun v => decide ( List.length v ≤ l ) ) free <;> simp_all +decide ;
        · unfold allocateOne at * ; aesop;
        · grind +suggestions;
      · obtain ⟨ n, hn ⟩ := ‹_›; simp_all +decide [ add_assoc ] ;
        rw [ ← hn ];
        rw [ List.getElem?_eq_getElem ];
        exact fun h => by have := List.nodup_iff_injective_get.mp h_neq h; exact absurd this ( by simp +decide [ Fin.ext_iff ] ) ;
        grind +qlia;
    have h_not_prefix : ¬(free[(free.findIdx? (fun v => v.length ≤ l)).get!]! <+: w) ∧ ¬(w <+: free[(free.findIdx? (fun v => v.length ≤ l)).get!]!) := by
      have h_not_prefix : free[(free.findIdx? (fun v => v.length ≤ l)).get!]! ∈ free.toFinset ∧ w ∈ free.toFinset := by
        cases h : List.findIdx? ( fun v => decide ( List.length v ≤ l ) ) free <;> simp_all +decide ;
        · cases free <;> aesop;
        · have h_mem : free[‹ℕ›]?.getD default ∈ free := by
            grind +suggestions;
          exact ⟨ h_mem, by cases h_take_drop <;> [ exact List.mem_of_mem_take ‹_›; exact List.mem_of_mem_drop ‹_› ] ⟩;
      exact ⟨ fun h => h_neq <| by have := hpf h_not_prefix.1 h_not_prefix.2 h; tauto, fun h => h_neq <| by have := hpf h_not_prefix.2 h_not_prefix.1 h; tauto ⟩;
    have h_not_prefix_a : free[(free.findIdx? (fun v => v.length ≤ l)).get!]! <+: a := by
      grind +locals;
    grind +suggestions

/-
Prefix-freeness of the free list is preserved by one allocation step.
-/
lemma allocateOne_prefixFree (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free'))
    (hpf : IsPrefixFree ↑free.toFinset) (hd : DescLengths free) :
    IsPrefixFree ↑free'.toFinset := by
  -- Let's unfold the definition of `allocateOne` to understand how `free'` is constructed.
  obtain ⟨idx, hidx, hv⟩ : ∃ idx, free.findIdx? (fun v => v.length ≤ l) = some idx ∧ free[idx]! ∈ free ∧ free[idx]!.length ≤ l := by
    unfold allocateOne at h;
    grind +suggestions;
  have h_new_nodes_antichain' : IsPrefixFree (↑((splitNode free[idx]! l).2.toFinset)) := by
    have := splitNode_antichain free[idx]! l; simp_all +decide [ IsPrefixFree ] ;
    exact fun p hp q hq hpq => this.2 p hp |>.2 q hq hpq;
  have h_disjoint : ∀ p ∈ free.take idx ++ free.drop (idx + 1), p ≠ free[idx]! ∧ ¬ free[idx]! <+: p ∧ ¬ p <+: free[idx]! := by
    intro p hp
    have h_distinct : p ≠ free[idx]! := by
      have h_distinct : List.Nodup free := by
        have h_distinct : List.Nodup free := by
          have h_chain : List.IsChain (fun a b => b.length < a.length) free := hd
          have h_distinct : List.Pairwise (fun a b => a.length ≠ b.length) free := by
            rw [ List.pairwise_iff_get ];
              intro i j hij; have := isChain_iff_get_fin.mp h_chain; simp_all +decide  ;
            have h_distinct : ∀ i j : Fin free.length, i < j → List.length free[i] > List.length free[j] := by
              intro i j hij; obtain ⟨j, hj⟩ := j; obtain ⟨i, hi⟩ := i; simp_all +decide  ;
              induction hij <;> simp_all +decide ;
              · exact this ⟨ i, Nat.lt_pred_iff.mpr hj ⟩;
              · exact lt_trans ( this ⟨ _, Nat.lt_pred_iff.mpr hj ⟩ ) ( by solve_by_elim [ Nat.lt_of_succ_lt ] );
            exact ne_of_gt ( h_distinct _ _ hij );
          exact List.Pairwise.imp_of_mem ( by aesop ) h_distinct;
        exact h_distinct;
      intro h_eq
      have h_contradiction : List.Nodup (List.take idx free ++ free[idx]! :: List.drop (idx + 1) free) := by
        convert h_distinct using 1;
        simp +zetaDelta at *;
        rw [ List.getElem?_eq_getElem ];
        swap;
        grind +suggestions;
        simp +zetaDelta at *;
      grind
    have h_incomparable : ¬ free[idx]! <+: p ∧ ¬ p <+: free[idx]! := by
      have h_incomparable : ∀ p ∈ free, p ≠ free[idx]! → ¬ free[idx]! <+: p ∧ ¬ p <+: free[idx]! := by
        intros p hp hp_ne; exact ⟨by
        exact fun h => hp_ne <| hpf ( by aesop ) ( by aesop ) h ▸ rfl, by
          exact fun h => hp_ne <| hpf ( by aesop ) ( by aesop ) h⟩;
      apply h_incomparable p (by
      rw [ List.mem_append ] at hp;
      exact hp.elim ( fun hp => List.mem_of_mem_take hp ) fun hp => List.mem_of_mem_drop hp) h_distinct
    exact ⟨h_distinct, h_incomparable⟩;
  have h_disjoint : ∀ p ∈ free.take idx ++ free.drop (idx + 1), ∀ q ∈ (splitNode free[idx]! l).2, ¬ p <+: q ∧ ¬ q <+: p := by
    grind +suggestions;
  intro p hp q hq hpq;
  by_cases hp_take : p ∈ free.take idx ++ free.drop (idx + 1) <;> by_cases hq_take : q ∈ free.take idx ++ free.drop (idx + 1) <;> simp_all +decide [ allocateOne ];
  · exact hpf ( show p ∈ free from by
                  exact hp_take.elim ( fun hp_take => List.mem_of_mem_take hp_take ) fun hp_take => List.mem_of_mem_drop hp_take |> fun h => by simpa using h; ) ( show q ∈ free from by
                                                  exact List.mem_append.mp ( show q ∈ List.take idx free ++ List.drop ( idx + 1 ) free from by aesop ) |> Or.rec ( fun h => List.mem_of_mem_take h ) fun h => List.mem_of_mem_drop h ) hpq;
  · grind;
  · grind +splitImp;
  · simp_all +decide [ ← h.2 ];
    exact h_new_nodes_antichain' hp hq hpq

/-! ## Length and mass behaviour of one allocation step -/

/-
`allocateOne` fails exactly when no free node has length `≤ l`.
-/
lemma allocateOne_eq_none_iff (free : List BitString) (l : ℕ) :
    allocateOne free l = none ↔ ∀ v ∈ free, l < v.length := by
  simp [allocateOne];
  cases h' : List.findIdx? ( fun v => decide ( List.length v ≤ l ) ) free <;> simp_all +decide;
  grind +suggestions

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
  unfold allocateOne at h;
  grind +suggestions

/-
**Mass conservation for one allocation step.**
-/
lemma allocateOne_mass (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free')) :
    freeMass free' + nodeMass a = freeMass free := by
  unfold allocateOne at h;
  rcases h' : List.findIdx? ( fun v => decide ( List.length v ≤ l ) ) free with ( _ | idx ) <;> simp_all +decide;
  -- By definition of `splitNode`, we know that `nodeMass (free[idx]!) = nodeMass a + (List.map nodeMass (splitNode (free[idx]!) l).2).sum`.
  have h_split : nodeMass (free[idx]!) = nodeMass a + (List.map nodeMass (splitNode (free[idx]!) l).2).sum := by
    grind +suggestions;
  have h_freeMass_split : freeMass free = freeMass (free.take idx) + nodeMass (free[idx]!) + freeMass (free.drop (idx + 1)) := by
    have h_freeMass_split : free = free.take idx ++ [free[idx]!] ++ free.drop (idx + 1) := by
      have h_free : idx < free.length := by
        grind +suggestions;
      simp +decide [ List.take_append_drop, h_free ];
    conv_lhs => rw [ h_freeMass_split ];
    unfold freeMass; simp +decide [ List.sum_append ] ;
    ring;
  simp_all +decide [ freeMass ];
  rw [ ← h.2 ] ; simp +decide [ List.map_append, List.sum_append ] ; ring;

/-
One allocation step preserves descending lengths.
-/
lemma allocateOne_descLengths (free : List BitString) (l : ℕ)
    (a : BitString) (free' : List BitString) (h : allocateOne free l = some (a, free'))
    (hd : DescLengths free) : DescLengths free' := by
  unfold allocateOne at h;
  rcases h' : List.findIdx? ( fun v => decide ( List.length v ≤ l ) ) free with ( _ | idx ) <;> simp_all +decide;
  -- By definition of `DescLengths`, we need to show that the lengths of the elements in `free'` are strictly decreasing.
  have h_desc : List.IsChain (fun a b => b.length < a.length) (List.take idx free ++ List.reverse (splitNode (free[idx]!) l).2 ++ List.drop (idx + 1) free) := by
    apply List.isChain_append.mpr;
    refine ⟨ ?_, ?_, ?_ ⟩;
    · refine List.isChain_append.mpr ⟨ ?_, ?_, ?_ ⟩;
      · apply List.IsChain.take;
        exact hd;
      · unfold splitNode; simp +decide [ List.isChain_reverse ] ;
        rw [ isChain_iff_get_fin ];
        simp +decide ;
      · have h_last_take : ∀ x ∈ List.take idx free, x.length > l := by
          intro x hx; have := List.mem_iff_getElem.mp hx; simp_all +decide  ;
          obtain ⟨ i, hi, rfl ⟩ := this; have := List.findIdx?_eq_some_iff_getElem.mp h'; simp_all +decide  ;
          exact this.choose_spec.2 i hi.1;
        have h_last_take : ∀ y ∈ (splitNode (free[idx]!) l).2, y.length ≤ l := by
          intros y hy; exact (splitNode_newNodes_length (free[idx]!) l y hy).right;
        grind;
    · exact List.IsChain.drop hd (idx + 1)
    · have h_last : ∀ y ∈ List.drop (idx + 1) free, y.length < (free[idx]!).length := by
        intro y hy
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
        have hidx : idx < free.length := by
          grind +suggestions
        have hj : idx + 1 + i < free.length := by
          have hle : idx + 1 ≤ free.length := by omega
          have hlt : i < free.length - (idx + 1) := by
            simpa [List.length_drop, Nat.add_sub_assoc hle] using hi
          omega
        rw [getElem!_pos free idx hidx]
        simpa [List.getElem_drop, add_assoc] using
          descLengths_getElem_length_lt hd (i := idx) (j := idx + 1 + i) (by omega) hj
      have h_last : ∀ x ∈ List.reverse (splitNode (free[idx]!) l).2, x.length ≥ (free[idx]!).length + 1 := by
        simp [splitNode];
      grind +suggestions;
  grind +locals

/-! ## Serviceability from distinct lengths -/

/-
A free list with strictly descending lengths all `> l` has mass `< 2^{-l}`.
-/
lemma freeMass_lt_of_all_gt (free : List BitString) (l : ℕ)
    (hd : DescLengths free) (hgt : ∀ v ∈ free, l < v.length) :
    freeMass free < (2 : ℝ≥0∞)⁻¹ ^ l := by
  -- Since the lengths are strictly decreasing, we can order the elements in the free list by their lengths.
  have h_order : ∃ (f : ℕ → BitString), (∀ i < free.length, f i ∈ free) ∧ (∀ i j, i < j → i < free.length → j < free.length → f i ≠ f j) ∧ (∀ i < free.length, List.length (f i) > l) ∧ (∀ i j, i < j → i < free.length → j < free.length → List.length (f i) > List.length (f j)) := by
    use fun i => if hi : i < free.length then free[i]! else [];
    refine ⟨ ?_, ?_, ?_, ?_ ⟩;
    · grind;
    · intro i j hij hi hj; have := isChain_iff_get_fin.mp hd; simp_all +decide  ;
      -- By induction on $j - i$, we can show that the lengths of the elements at positions $i$ and $j$ are strictly decreasing.
      have h_ind : ∀ i j : ℕ, i < j → i < free.length → j < free.length → List.length free[i]! > List.length free[j]! := by
        intros i j hij hi hj; induction hij <;> simp_all +decide  ;
        · exact this ⟨ i, Nat.lt_pred_iff.mpr hj ⟩;
        · exact lt_trans ( this ⟨ _, Nat.lt_pred_iff.mpr hj ⟩ ) ( by solve_by_elim [ Nat.lt_of_succ_lt ] );
      grind;
    · aesop;
    · intro i j hij hi hj; have := isChain_iff_get_fin.mp hd; simp_all +decide  ;
      induction hij <;> simp_all +decide [ Nat.succ_eq_add_one ];
      · exact this ⟨ i, Nat.lt_pred_iff.mpr hj ⟩;
      · exact lt_trans ( this ⟨ _, Nat.lt_pred_iff.mpr hj ⟩ ) ( by solve_by_elim [ Nat.lt_of_succ_lt ] );
  obtain ⟨f, hf_mem, hf_distinct, hf_length, hf_order⟩ := h_order;
  have h_sum : (freeMass free) ≤ ∑ i ∈ Finset.range free.length, (2⁻¹ : ℝ≥0∞) ^ (List.length (f i)) := by
    have h_sum : (freeMass free) ≤ ∑ i ∈ Finset.image f (Finset.range free.length), (2⁻¹ : ℝ≥0∞) ^ (List.length i) := by
      have h_sum : (freeMass free) = ∑ i ∈ free.toFinset, (2⁻¹ : ℝ≥0∞) ^ (List.length i) := by
        have h_sum : List.Nodup free := by
          have h_distinct : ∀ i j, i < j → i < free.length → j < free.length → free[i]! ≠ free[j]! := by
            have := isChain_iff_get_fin.mp hd;
            have h_distinct : ∀ i j, i < j → i < free.length → j < free.length → List.length (free[i]!) > List.length (free[j]!) := by
              intros i j hij hi hj;
              induction hij <;> simp_all +decide ;
              · exact this ⟨ i, Nat.lt_pred_iff.mpr hj ⟩;
              · exact lt_trans ( this ⟨ _, Nat.lt_pred_iff.mpr hj ⟩ ) ( by solve_by_elim [ Nat.lt_of_succ_lt ] );
            grind;
          rw [ List.nodup_iff_injective_get ];
          intros i j hij;
          exact le_antisymm ( le_of_not_gt fun hi => h_distinct _ _ hi ( by simp ) ( by simp ) <| by simpa [ Fin.cast_val_eq_self ] using hij.symm ) ( le_of_not_gt fun hj => h_distinct _ _ hj ( by simp ) ( by simp ) <| by simpa [ Fin.cast_val_eq_self ] using hij );
        rw [ List.sum_toFinset ];
        · rfl;
        · assumption;
      rw [h_sum];
      rw [ Finset.eq_of_subset_of_card_le ( show Finset.image f ( Finset.range free.length ) ⊆ free.toFinset from Finset.image_subset_iff.mpr fun i hi => by aesop ) ];
      rw [ Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm ( le_of_not_gt fun hi' => hf_distinct _ _ hi' ( Finset.mem_range.mp hj ) ( Finset.mem_range.mp hi ) hij.symm ) ( le_of_not_gt fun hj' => hf_distinct _ _ hj' ( Finset.mem_range.mp hi ) ( Finset.mem_range.mp hj ) hij ), Finset.card_range ];
      exact List.toFinset_card_le _;
    rwa [ Finset.sum_image <| by intros i hi j hj hij; exact le_antisymm ( le_of_not_gt fun hi' => hf_distinct _ _ hi' ( Finset.mem_range.mp hj ) ( Finset.mem_range.mp hi ) hij.symm ) ( le_of_not_gt fun hj' => hf_distinct _ _ hj' ( Finset.mem_range.mp hi ) ( Finset.mem_range.mp hj ) hij ) ] at h_sum;
  -- Since the lengths are strictly decreasing, we can bound each term in the sum.
  have h_bound : ∀ i < free.length, (2⁻¹ : ℝ≥0∞) ^ (List.length (f i)) ≤ (2⁻¹ : ℝ≥0∞) ^ (l + 1 + (free.length - 1 - i)) := by
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
  refine lt_of_le_of_lt h_sum <| lt_of_le_of_lt ( Finset.sum_le_sum fun i hi => h_bound i <| Finset.mem_range.mp hi ) ?_;
  norm_num [ pow_add, Finset.mul_sum _ _ _, Finset.sum_mul ];
  rw [ ← Finset.mul_sum _ _ _, ← Finset.sum_range_reflect ];
  rw [ Finset.sum_congr rfl fun i hi => by rw [ tsub_tsub_cancel_of_le ( Nat.le_sub_one_of_lt ( Finset.mem_range.mp hi ) ) ] ] ; ring_nf;
  rw [ ← ENNReal.toReal_lt_toReal ] <;> norm_num;
  · rw [ ENNReal.toReal_sum ] ; norm_num [ geom_sum_eq ] ; ring_nf ; norm_num;
    exact fun _ _ => ENNReal.pow_ne_top <| by norm_num;
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
  induction n generalizing free with
  | zero =>
    cases h;
    exact fun p hp q hq hpq => by aesop;
  | succ n ih =>
    obtain ⟨free₀, h₀⟩ : ∃ free₀, allocatorState req n = some free₀ ∧ (req n = none → free = free₀) ∧ (req n ≠ none → ∃ a free', allocateOne free₀ (req n).get!.2 = some (a, free') ∧ free = free') := by
      unfold allocatorState at h; aesop;
    by_cases h₁ : req n = none <;> simp_all +decide;
    have h₂ :DescLengths free₀ := by
      have h₂ : ∀ n, ∀ free, allocatorState req n = some free → DescLengths free := by
        intros n free hfree
        induction n generalizing free with
        | zero => cases hfree ; tauto
        | succ n ih =>
          obtain ⟨free₀, h₀⟩ : ∃ free₀, allocatorState req n = some free₀ ∧ (req n = none → free = free₀) ∧ (req n ≠ none → ∃ a free', allocateOne free₀ (req n).get!.2 = some (a, free') ∧ free = free') := by
            unfold allocatorState at hfree; aesop;
          by_cases h₁ : req n = none <;> simp_all +decide;
          exact allocateOne_descLengths _ _ _ _ h₀.2.choose_spec ih;
      exact h₂ _ _ h₀.1;
    obtain ⟨ a, ha ⟩ := h₀.2; have := allocateOne_prefixFree free₀ ( req n |>.get!.2 ) a free ha; aesop;

/-
The free list always has strictly descending lengths.
-/
lemma allocatorState_descLengths (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (free : List BitString)
    (h : allocatorState req n = some free) : DescLengths free := by
  induction n generalizing free with
  | zero => cases h ; tauto
  | succ n ih =>
    -- By definition of `allocatorState`, if `allocatorState req (n + 1) = some free`, then `allocatorState req n = some free₀` for some `free₀`, and `req n = some (_, l)` for some `l`.
    obtain ⟨free₀, h₀⟩ : ∃ free₀, allocatorState req n = some free₀ := by
      cases h' : allocatorState req n <;> simp_all +decide [ allocatorState ];
    cases h' : req n <;> simp_all +decide [ allocatorState ];
    cases h'' : allocateOne free₀ ‹BitString × ℕ›.2 <;> simp_all +decide;
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
      by_cases h2 : req n = none <;> simp_all +decide [ allocatorState ];
      · unfold usedMass; simp_all +decide [ Finset.sum_range_succ ] ;
        unfold reqMass; aesop;
      · obtain ⟨fst, l, hl⟩ : ∃ fst l, req n = some (fst, l) := by
          cases h : req n <;> tauto;
        obtain ⟨a, free', hallocate⟩ : ∃ a free', allocateOne free₀ l = some (a, free') ∧ free = free' := by
          cases h' : allocateOne free₀ l <;> aesop;
        have h_mass : freeMass free' + nodeMass a = freeMass free₀ := by
          apply allocateOne_mass; exact hallocate.left;
        have h_mass : nodeMass a = (2 : ℝ≥0∞)⁻¹ ^ l := by
          have h_mass : a.length = l := by
            exact allocateOne_length free₀ l a free' hallocate.1;
          exact h_mass ▸ rfl;
        simp_all +decide [ usedMass, Finset.sum_range_succ ];
        simp_all +decide [ ← add_assoc, reqMass ];
        rw [ add_right_comm, ← ih, ← ‹freeMass free' + 2⁻¹ ^ l = freeMass free₀› ]

/-
Each partial Kraft sum is bounded by the total.
-/
lemma usedMass_le_tsum (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    usedMass req n ≤ ∑' i, reqMass req i := by
  unfold usedMass
  exact ENNReal.sum_le_tsum (Finset.range n)

/-
Given the global Kraft bound `≤ 1`, the allocator never fails.
-/
lemma allocatorState_isSome (req : ℕ → Option (BitString × ℕ)) (n : ℕ)
    (hweight : (∑' i, reqMass req i) ≤ 1) : (allocatorState req n).isSome := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h : allocatorState req n with ( _ | ⟨ free₀ ⟩ ) <;> simp_all +decide;
    by_cases hreq : req n = none;
    · simp +decide [ allocatorState, h, hreq ];
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
        exact ne_of_lt ( lt_of_le_of_lt ( usedMass_le_tsum req n ) ( lt_of_le_of_lt hweight ( by norm_num ) ) )
      have h_exists_fit : ∃ v ∈ free₀, v.length ≤ l := by
        apply exists_fit_of_mass_ge free₀ l (allocatorState_descLengths req n free₀ h) h_freeMass
      have h_allocateOne : (allocateOne free₀ l).isSome := by
        grind +locals
      simp [allocatorState, h, hl];
      cases h : allocateOne free₀ l <;> aesop

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
  have : (fun n : ℕ => List.replicate n false) = (fun n => (List.range n).map (fun _ => false)) := by
    funext n; rw [List.map_const']; simp
  rw [this]
  exact Primrec.list_range.list_map (Primrec.const false).to₂

/-
`splitNode` is computable.
-/
lemma splitNode_computable :
    Computable (fun p : BitString × ℕ => splitNode p.1 p.2) := by
  unfold splitNode
  refine (Primrec.pair ?_ ?_).to_comp
  · exact Primrec.list_append.comp Primrec.fst
      (replicate_false_primrec.comp (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst)))
  · refine Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst))) ?_
    exact (show Primrec₂ (fun (p : BitString × ℕ) (i : ℕ) =>
        p.1 ++ List.replicate i false ++ [true]) from
      (Primrec.list_append.comp
        (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
          (replicate_false_primrec.comp Primrec.snd))
        (Primrec.const [true])).to₂)

/-- `splitNode` (as a binary function) is primitive recursive. -/
lemma splitNode_primrec : Primrec (fun p : BitString × ℕ => splitNode p.1 p.2) := by
  refine Primrec.pair ?_ ?_
  · exact Primrec.list_append.comp Primrec.fst
      (replicate_false_primrec.comp (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst)))
  · refine Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst))) ?_
    exact (show Primrec₂ (fun (p : BitString × ℕ) (i : ℕ) =>
        p.1 ++ List.replicate i false ++ [true]) from
      (Primrec.list_append.comp
        (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
          (replicate_false_primrec.comp Primrec.snd))
        (Primrec.const [true])).to₂)

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

/-- A single step of the allocator state transition. -/
def allocStep (r : Option (BitString × ℕ)) (st : Option (List BitString)) : Option (List BitString) :=
  st.bind (fun free =>
    (r.map (fun pr => (allocateOne free pr.2).map Prod.snd)).getD (some free))

set_option maxHeartbeats 2000000 in
-- The branch witness composes `allocateOne_computable` under nested
-- `Option.map`/`Option.bind` over encoded product inputs; keeping it as a named
-- helper localizes the remaining normalization cost.
/-- `allocStep` is computable. -/
lemma allocStep_computable :
    Computable₂ (fun (r : Option (BitString × ℕ)) (st : Option (List BitString)) => allocStep r st) := by
  have hinner : Computable₂
      (fun (d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString)
        (pr : BitString × ℕ) => (allocateOne d.2 pr.2).map Prod.snd) := by
    refine comp_option_map ?_ (comp_snd_snd Computable.id)
    exact allocateOne_computable.comp
      ((Computable.snd.comp Computable.fst).pair (Computable.snd.comp Computable.snd))
  have hg : Computable
      (fun d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString =>
        (d.1.1.map (fun pr => (allocateOne d.2 pr.2).map Prod.snd)).getD (some d.2)) := by
    exact comp_option_getD (comp_option_map (comp_fst_fst Computable.id) hinner)
      (Computable.option_some.comp (comp_snd Computable.id))
  exact (comp_option_bind Computable.snd hg.to₂).of_eq (fun _ => rfl)

/-- `allocatorState` rewritten as an explicit `Nat.rec` with a combinator-friendly step. -/
lemma allocatorState_eq_rec (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    allocatorState req n = Nat.rec (some [[]]) (fun y IH => allocStep (req y) IH) n := by
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
        = allocStep (req k) X := by
      intro X
      cases X with
      | none => rfl
      | some free =>
        dsimp [allocStep]
        cases hr : req k with
        | none =>
          simp only [Option.map_none, Option.getD_none]
        | some o =>
          simp only [Option.map_some]
          cases h_alloc : allocateOne free o.2 with
          | none =>
            simp only [Option.map_none, Option.getD_some]
          | some a =>
            simp only [Option.map_some, Option.getD_some]
    calc allocatorState req (k + 1)
        = (match allocatorState req k with
            | none => none
            | some free => match req k with
              | none => some free
              | some (_, l) => match allocateOne free l with
                | none => none
                | some (_, free') => some free') := by rfl
      _ = allocStep (req k) (allocatorState req k) := step_eq _
      _ = allocStep (req k) (Nat.rec (some [[]]) (fun y IH => allocStep (req y) IH) k) := by rw [ih]

attribute [local irreducible] allocatorState

/-- The allocator state is computable uniformly in the context. -/
lemma allocatorState_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable (fun p : BitString × ℕ => allocatorState (req p.1) p.2) := by
  have hstep : Computable₂ (fun (p : BitString × ℕ) (q : ℕ × Option (List BitString)) =>
      allocStep (req p.1 q.1) q.2) := by
    have hreq : Computable (fun pq : (BitString × ℕ) × ℕ × Option (List BitString) => req pq.1.1 pq.2.1) :=
      hcomp.comp (Computable.pair (comp_fst_fst Computable.id) (comp_snd_fst Computable.id))
    exact Computable.comp allocStep_computable (Computable.pair hreq (comp_snd_snd Computable.id))
  refine (Computable.nat_rec (comp_snd Computable.id) (Computable.const (some [[]])) hstep).of_eq ?_
  intro p
  exact (allocatorState_eq_rec (req p.1) p.2).symm

/-! ## The three top-level obligations -/

/-- Extracting the payload of allocation at a given step. -/
def allocOut (r : Option (BitString × ℕ)) (st : Option (List BitString)) : Option BitString :=
  st.bind (fun free =>
    (r.map (fun pr => (allocateOne free pr.2).map Prod.fst)).getD none)

set_option maxHeartbeats 2000000 in
-- This is the output analogue of `allocStep_computable`; it has the same nested
-- product and `Option.map` composition cost, isolated from `allocFun_computable`.
/-- `allocOut` is computable. -/
lemma allocOut_computable :
    Computable₂ (fun (r : Option (BitString × ℕ)) (st : Option (List BitString)) => allocOut r st) := by
  have hinner : Computable₂
      (fun (d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString)
        (pr : BitString × ℕ) => (allocateOne d.2 pr.2).map Prod.fst) := by
    refine comp_option_map ?_ (comp_snd_fst Computable.id)
    exact allocateOne_computable.comp
      ((Computable.snd.comp Computable.fst).pair (Computable.snd.comp Computable.snd))
  have hg : Computable
      (fun d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString =>
        (d.1.1.map (fun pr => (allocateOne d.2 pr.2).map Prod.fst)).getD none) := by
    exact comp_option_getD (comp_option_map (comp_fst_fst Computable.id) hinner) (Computable.const none)
  exact (comp_option_bind Computable.snd hg.to₂).of_eq (fun _ => rfl)

/-- `allocFun` rewritten as a bind over the allocator state. -/
lemma allocFun_eq_bind (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    allocFun req n = allocOut (req n) (allocatorState req n) := by
  dsimp [allocFun, allocOut]
  cases h_st : allocatorState req n with
  | none =>
    rfl
  | some free =>
    simp only [Option.bind_some]
    cases hr : req n with
    | none =>
      simp only [Option.map_none, Option.getD_none]
    | some o =>
      simp only [Option.map_some]
      cases h_alloc : allocateOne free o.2 with
      | none =>
        simp only [Option.map_none, Option.getD_some]
      | some a =>
        simp only [Option.map_some, Option.getD_some]

/-- The allocation function is computable uniformly in the context. -/
lemma allocFun_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable (fun p : BitString × ℕ => allocFun (req p.1) p.2) := by
  have hreq : Computable (fun p : BitString × ℕ => req p.1 p.2) := hcomp
  have hst : Computable (fun p : BitString × ℕ => allocatorState (req p.1) p.2) := allocatorState_computable req hcomp
  refine (Computable.comp allocOut_computable (Computable.pair hreq hst)).of_eq ?_
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
  -- By definition of `allocatorState`, we know that `allocatorState req n = some free` for some `free`.
  obtain ⟨free, hfree⟩ : ∃ free, allocatorState req n = some free := by
    cases h : allocatorState req n <;> simp_all +decide [ allocFun ];
  unfold allocFun at hn;
  rcases h : req n with ( _ | ⟨ fst, l ⟩ ) <;> simp_all +decide;
  rcases h' : allocateOne free l with ( _ | ⟨ allocated, snd ⟩ ) <;> simp_all +decide;
  rw [ show free' = snd from by { rw [ show allocatorState req ( n + 1 ) = some snd from by { rw [ show allocatorState req ( n + 1 ) = match allocatorState req n with | none => none | some free => match req n with | none => some free | some ( fst, l ) => match allocateOne free l with | none => none | some ( allocated, free' ) => some free' from by rw [allocatorState] ] ; aesop } ] at hfree'; aesop } ];
  apply allocateOne_alloc_incomp_free' free l cn snd h' (allocatorState_prefixFree req n free hfree) (allocatorState_descLengths req n free hfree)

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
                  simp [hG, hreq, halloc] at h'
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
  rcases h : allocatorState req m with ( _ | Fm ) <;> rcases h' : req m with ( _ | ⟨ fst, l ⟩ ) <;> simp_all +decide;
  rcases h'' : allocateOne Fm l with ( _ | ⟨ allocated, snd ⟩ ) <;> simp_all +decide;
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
