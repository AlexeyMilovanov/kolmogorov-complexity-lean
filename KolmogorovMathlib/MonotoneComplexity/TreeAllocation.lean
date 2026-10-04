import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.LSCApproximation
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.UniformNumerators
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.MonotoneComplexity.CopyGenerator

/-!
# Allocating disjoint sets of atoms to the nodes of the tree

A `TreeAllocation` gives each node `x` of the binary tree a duplicate-free list of `q x` atoms —
strings of a common length `s` — with a child's atoms taken from its parent's and siblings kept
apart (`extendAtoms_child`, `extendAtoms_disjoint`). Passing to the next stage doubles the
precision: `refineAtoms` replaces each atom by its two one-bit extensions
(`refineAtoms_length`, `refineAtoms_mem`, `refineAtoms_nodup`) and `TreeAllocation.extend`
distributes the refined atoms according to the new numerators, which the dyadic estimate
`two_mul_le_of_dyadicValue_le` shows to be large enough. `TreeAllocation.extend_refines` records
that the stages are nested, so an allocation can be grown indefinitely.
-/

open ENNReal

namespace Kolmogorov

/-- A dyadic inequality across one precision step doubles the numerator. -/
theorem two_mul_le_of_dyadicValue_le {n m s : ℕ}
    (h : dyadicValue n s ≤ dyadicValue m (s + 1)) : 2 * n ≤ m := by
  unfold dyadicValue at h
  have h1 : (n : ENNReal) / (2 : ENNReal)^s * (2 : ENNReal)^(s+1)
      ≤ (m : ENNReal) / (2 : ENNReal)^(s+1) * (2 : ENNReal)^(s+1) := by gcongr
  rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)] at h1
  have h2 : (n : ENNReal) / (2 : ENNReal)^s * (2 : ENNReal)^(s+1) = (n : ENNReal) * 2 := by
    rw [pow_succ, ← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  rw [h2] at h1
  rw [mul_comm, ← Nat.cast_two, ← Nat.cast_mul] at h1
  norm_cast at h1

/-- An allocation of atoms of length `s` to the nodes of the tree: each node gets `q x` distinct
atoms, the root gets all of them, children inherit from their parent, and siblings are
disjoint. -/
structure TreeAllocation (q : BitString → ℕ) (s : ℕ) where
  atoms : BitString → List BitString
  atoms_length   : ∀ x p, p ∈ atoms x → p.length = s
  atoms_nodup    : ∀ x, (atoms x).Nodup
  atoms_card     : ∀ x, (atoms x).length = q x
  atoms_root     : ∀ p, p.length = s → p ∈ atoms []
  atoms_child    : ∀ x b p, p ∈ atoms (x ++ [b]) → p ∈ atoms x
  atoms_disjoint : ∀ x p, p ∈ atoms (x ++ [false]) → p ∉ atoms (x ++ [true])

/-- Refining atoms by one bit: each atom is replaced by its two one-bit extensions. -/
def refineAtoms (L : List BitString) : List BitString :=
  L.flatMap (fun p => [p ++ [false], p ++ [true]])

/-- Refining doubles the number of atoms. -/
theorem refineAtoms_length (L : List BitString) :
    (refineAtoms L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons head tail ih =>
    simp [refineAtoms, List.flatMap] at *
    omega

/-- The refined atoms are exactly the one-bit extensions of the original ones. -/
theorem refineAtoms_mem (L : List BitString) (p : BitString) :
    p ∈ refineAtoms L ↔ ∃ q ∈ L, ∃ b : Bool, p = q ++ [b] := by
  simp [refineAtoms, List.mem_flatMap]

/-- Refining a duplicate-free list gives a duplicate-free list. -/
theorem refineAtoms_nodup (L : List BitString) (hL : L.Nodup) :
    (refineAtoms L).Nodup := by
  rw [refineAtoms]
  apply List.nodup_flatMap.mpr
  constructor
  · intro x hx
    simp
  · refine List.Pairwise.imp ?_ hL
    intro x y hxy
    dsimp [Function.onFun]
    rw [List.disjoint_iff_ne]
    intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · simp [hxy]
    · intro h; simp at h
    · intro h; simp at h
    · simp [hxy]

/-- Refining atoms of length `s` gives atoms of length `s + 1`. -/
theorem refineAtoms_mem_length (L : List BitString) (s : ℕ)
    (h_len : ∀ p ∈ L, p.length = s) (p : BitString) (hp : p ∈ refineAtoms L) :
    p.length = s + 1 := by
  rw [refineAtoms_mem] at hp
  rcases hp with ⟨q, hq, b, rfl⟩
  simp [h_len q hq]

/-- Taking `k` entries of a filtered list with at least `k` entries gives exactly `k`. -/
theorem take_filter_length {α : Type _} (L : List α) (P : α → Bool) (k : ℕ)
    (h : k ≤ (L.filter P).length) : ((L.filter P).take k).length = k := by
  rw [List.length_take, Nat.min_eq_left h]

/-- Taking entries of a filtered duplicate-free list keeps it duplicate-free. -/
theorem take_filter_nodup {α : Type _} (L : List α) (P : α → Bool) (k : ℕ)
    (hL : L.Nodup) : ((L.filter P).take k).Nodup := by
  exact List.Nodup.sublist (List.take_sublist k (L.filter P)) (List.Nodup.filter P hL)

/-- Entries taken from a filtered list belong to the original list. -/
theorem take_filter_subset {α : Type _} (L : List α) (P : α → Bool) (k : ℕ) :
    ((L.filter P).take k) ⊆ L := by
  intro x hx
  exact List.mem_filter.mp (List.mem_of_mem_take hx) |>.left

/-- Entries taken from a filtered list satisfy the filter. -/
theorem take_filter_disjoint {α : Type _} (L : List α) (P : α → Bool) (k : ℕ)
    (x : α) (hx : x ∈ (L.filter P).take k) : P x = true := by
  exact List.mem_filter.mp (List.mem_of_mem_take hx) |>.right

/-- Refining a subset gives a subset. -/
theorem refineAtoms_subset {L L' : List BitString} (h : L ⊆ L') :
    refineAtoms L ⊆ refineAtoms L' := by
  intro p hp
  rw [refineAtoms_mem] at hp ⊢
  obtain ⟨y, hy, b, rfl⟩ := hp
  exact ⟨y, h hy, b, rfl⟩

/-- If every element of a nodup list `L` failing the predicate `P` lies in `S`, then `L` is no
longer than `L.filter P` together with `S`. -/
theorem length_le_length_filter_add {α : Type _} (P : α → Bool) (L S : List α)
    (hL : L.Nodup) (hsub : ∀ x ∈ L, P x = false → x ∈ S) :
    L.length ≤ (L.filter P).length + S.length := by
  have h1 : L.length = (L.filter P).length + (L.filter (fun a => decide ¬ P a = true)).length := by
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.length_eq_countP_add_countP P
  have h2 : (L.filter (fun a => decide ¬ P a = true)).length ≤ S.length := by
    refine List.Subperm.length_le (List.subperm_of_subset (hL.filter _) ?_)
    intro x hx
    rw [List.mem_filter] at hx
    exact hsub x hx.1 (by simpa using hx.2)
  omega

/-- Every bitstring of length `n` is enumerated by `exactLengthPrograms n`. -/
theorem mem_exactLengthPrograms_of_length (p : BitString) (n : ℕ) (h : p.length = n) :
    p ∈ exactLengthPrograms n := by
  subst h
  induction p with
  | nil => simp [exactLengthPrograms]
  | cons b tail ih =>
    simp only [exactLengthPrograms, List.length_cons, List.mem_flatMap]
    exact ⟨tail, ih, by cases b <;> simp⟩

/-- The atoms allocated to `x` at the next stage: the refined atoms of the path, completed from
the parent's spare pool. -/
def TreeAllocation.extendAtoms (q r : BitString → ℕ) (s : ℕ) (A : TreeAllocation q s)
    (x : BitString) : List BitString :=
  let rec go (current_path remaining : BitString) (parent_alloc : List BitString) :
      List BitString :=
    match remaining with
    | [] => if s + 1 < current_path.length then [] else parent_alloc
    | b :: bs =>
        let M_false := refineAtoms (A.atoms (current_path ++ [false]))
        let M_true := refineAtoms (A.atoms (current_path ++ [true]))
        let pool := parent_alloc.filter (fun p => p ∉ M_false ∧ p ∉ M_true)
        let need_false := r (current_path ++ [false]) - M_false.length
        let child_alloc := if b = false then
          M_false ++ pool.take need_false
        else
          let need_true := r (current_path ++ [true]) - M_true.length
          M_true ++ (pool.drop need_false).take need_true
        go (current_path ++ [b]) bs child_alloc
  go [] x (exactLengthPrograms (s + 1))

namespace TreeAllocation

variable {q : BitString → ℕ} {s : ℕ}

/-- The allocation handed to the child `cp ++ [b]` by a parent holding `alloc`. -/
def stepAlloc (r : BitString → ℕ) (A : TreeAllocation q s)
    (cp : BitString) (b : Bool) (alloc : List BitString) : List BitString :=
  let M_false := refineAtoms (A.atoms (cp ++ [false]))
  let M_true := refineAtoms (A.atoms (cp ++ [true]))
  let pool := alloc.filter (fun p => decide (p ∉ M_false ∧ p ∉ M_true))
  let need_false := r (cp ++ [false]) - M_false.length
  if b = false then M_false ++ pool.take need_false
  else M_true ++ ((pool.drop need_false).take (r (cp ++ [true]) - M_true.length))

/-- Iterated `stepAlloc`: this is `extendAtoms.go` without the final length truncation. -/
def runAlloc (r : BitString → ℕ) (A : TreeAllocation q s) :
    BitString → BitString → List BitString → List BitString
  | _, [], alloc => alloc
  | cp, b :: bs, alloc => runAlloc r A (cp ++ [b]) bs (stepAlloc r A cp b alloc)

/-- The recursion of the extension is the allocation run, and is empty below the new frontier. -/
theorem go_eq (r : BitString → ℕ) (A : TreeAllocation q s) (u cp : BitString)
    (alloc : List BitString) :
    extendAtoms.go q r s A cp u alloc =
      if s + 1 < (cp ++ u).length then [] else runAlloc r A cp u alloc := by
  induction u generalizing cp alloc with
  | nil => simp [extendAtoms.go, runAlloc]
  | cons b bs ih =>
    rw [show extendAtoms.go q r s A cp (b :: bs) alloc
        = extendAtoms.go q r s A (cp ++ [b]) bs (stepAlloc r A cp b alloc) from rfl]
    rw [ih, runAlloc]
    simp

/-- Running the allocation along an extended path is one further step of the run. -/
theorem runAlloc_append (r : BitString → ℕ) (A : TreeAllocation q s) (u : BitString)
    (b : Bool) (cp : BitString) (alloc : List BitString) :
    runAlloc r A cp (u ++ [b]) alloc = stepAlloc r A (cp ++ u) b (runAlloc r A cp u alloc) := by
  induction u generalizing cp alloc with
  | nil => simp [runAlloc]
  | cons c cs ih => simp [runAlloc, ih]

/-- The invariant maintained along the recursion defining `extendAtoms`. -/
structure AllocInv (r : BitString → ℕ) (A : TreeAllocation q s) (cp : BitString)
    (alloc : List BitString) : Prop where
  len : ∀ p ∈ alloc, p.length = s + 1
  nodup : alloc.Nodup
  card : alloc.length = r cp
  sub : refineAtoms (A.atoms cp) ⊆ alloc

/-- Refined atoms of an allocation at stage `s` have length `s + 1`. -/
theorem refine_atoms_mem_length (A : TreeAllocation q s) (x : BitString) (p : BitString)
    (hp : p ∈ refineAtoms (A.atoms x)) : p.length = s + 1 :=
  refineAtoms_mem_length _ s (fun y hy => A.atoms_length x y hy) p hp

/-- The refined atoms of a child are refined atoms of the parent. -/
theorem refine_child_subset (A : TreeAllocation q s) (cp : BitString) (b : Bool) :
    refineAtoms (A.atoms (cp ++ [b])) ⊆ refineAtoms (A.atoms cp) :=
  refineAtoms_subset (fun y hy => A.atoms_child cp b y hy)

/-- The refined atoms of the two children are disjoint. -/
theorem refine_children_disjoint (A : TreeAllocation q s) (cp : BitString) (p : BitString)
    (hf : p ∈ refineAtoms (A.atoms (cp ++ [false])))
    (ht : p ∈ refineAtoms (A.atoms (cp ++ [true]))) : False := by
  rw [refineAtoms_mem] at hf ht
  obtain ⟨y, hy, b, rfl⟩ := hf
  obtain ⟨y', hy', b', hEq⟩ := ht
  have hyy : y = y' := (List.append_inj' hEq.symm (by simp)).1.symm
  subst hyy
  exact A.atoms_disjoint cp y hy hy'

/-- The pool of unallocated programs is large enough to serve both children. -/
theorem stepAlloc_pool_card {r : BitString → ℕ} (A : TreeAllocation q s)
    (hcoh : ∀ x, r (x ++ [false]) + r (x ++ [true]) ≤ r x)
    (hmono : ∀ x, 2 * q x ≤ r x) (cp : BitString) (alloc : List BitString)
    (h : AllocInv r A cp alloc) :
    (r (cp ++ [false]) - (refineAtoms (A.atoms (cp ++ [false]))).length)
      + (r (cp ++ [true]) - (refineAtoms (A.atoms (cp ++ [true]))).length)
      ≤ (alloc.filter (fun p => decide (p ∉ refineAtoms (A.atoms (cp ++ [false]))
          ∧ p ∉ refineAtoms (A.atoms (cp ++ [true]))))).length := by
  set Mf := refineAtoms (A.atoms (cp ++ [false])) with hMf
  set Mt := refineAtoms (A.atoms (cp ++ [true])) with hMt
  have hMfr : Mf.length ≤ r (cp ++ [false]) := by
    rw [hMf, refineAtoms_length, A.atoms_card]; exact hmono _
  have hMtr : Mt.length ≤ r (cp ++ [true]) := by
    rw [hMt, refineAtoms_length, A.atoms_card]; exact hmono _
  have key := length_le_length_filter_add
    (fun p => decide (p ∉ Mf ∧ p ∉ Mt)) alloc (Mf ++ Mt) h.nodup (by
      intro x _ hx
      simp only [decide_eq_false_iff_not, not_and, not_not] at hx
      simp only [List.mem_append]
      by_cases hxf : x ∈ Mf
      · exact Or.inl hxf
      · exact Or.inr (hx hxf))
  rw [h.card, List.length_append] at key
  have := hcoh cp
  omega

/-- Assembling a child allocation out of the refinement of the child's atoms together with a
fresh `part` of the parent's pool preserves the invariant. -/
theorem alloc_inv_of_part {r : BitString → ℕ} (A : TreeAllocation q s)
    (hmono : ∀ x, 2 * q x ≤ r x) (cp : BitString) (b : Bool) (alloc part : List BitString)
    (h : AllocInv r A cp alloc)
    (hsub : ∀ p ∈ part, p ∈ alloc)
    (hnot : ∀ p ∈ part, p ∉ refineAtoms (A.atoms (cp ++ [b])))
    (hnodup : part.Nodup)
    (hlen : part.length = r (cp ++ [b]) - (refineAtoms (A.atoms (cp ++ [b]))).length) :
    AllocInv r A (cp ++ [b]) (refineAtoms (A.atoms (cp ++ [b])) ++ part) := by
  set M := refineAtoms (A.atoms (cp ++ [b])) with hM
  have hMr : M.length ≤ r (cp ++ [b]) := by
    rw [hM, refineAtoms_length, A.atoms_card]; exact hmono _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact refine_atoms_mem_length A _ p hp
    · exact h.len p (hsub p hp)
  · refine List.nodup_append.mpr ⟨refineAtoms_nodup _ (A.atoms_nodup _), hnodup, ?_⟩
    rintro a ha c hc rfl
    exact hnot a hc ha
  · rw [List.length_append, hlen]; omega
  · exact List.subset_append_left _ _

/-- One step of the recursion preserves the invariant. -/
theorem stepAlloc_inv {r : BitString → ℕ} (A : TreeAllocation q s)
    (hcoh : ∀ x, r (x ++ [false]) + r (x ++ [true]) ≤ r x)
    (hmono : ∀ x, 2 * q x ≤ r x) (cp : BitString) (b : Bool) (alloc : List BitString)
    (h : AllocInv r A cp alloc) :
    AllocInv r A (cp ++ [b]) (stepAlloc r A cp b alloc) := by
  have hpool := stepAlloc_pool_card A hcoh hmono cp alloc h
  set Mf := refineAtoms (A.atoms (cp ++ [false])) with hMf
  set Mt := refineAtoms (A.atoms (cp ++ [true])) with hMt
  set pool := alloc.filter (fun p => decide (p ∉ Mf ∧ p ∉ Mt)) with hpooldef
  set nf := r (cp ++ [false]) - Mf.length with hnf
  set nt := r (cp ++ [true]) - Mt.length with hnt
  have hpool_sub : ∀ p ∈ pool, p ∈ alloc := fun p hp => (List.mem_filter.mp hp).1
  have hpool_prop : ∀ p ∈ pool, p ∉ Mf ∧ p ∉ Mt := by
    intro p hp
    simpa using (List.mem_filter.mp hp).2
  have hpool_nodup : pool.Nodup := h.nodup.filter _
  cases b with
  | false =>
    have hstep : stepAlloc r A cp false alloc = Mf ++ pool.take nf := rfl
    rw [hstep]
    refine alloc_inv_of_part A hmono cp false alloc _ h ?_ ?_ ?_ ?_
    · exact fun p hp => hpool_sub p (List.mem_of_mem_take hp)
    · exact fun p hp => (hpool_prop p (List.mem_of_mem_take hp)).1
    · exact hpool_nodup.sublist (List.take_sublist _ _)
    · rw [List.length_take, ← hnf]
      omega
  | true =>
    have hstep : stepAlloc r A cp true alloc = Mt ++ (pool.drop nf).take nt := rfl
    rw [hstep]
    refine alloc_inv_of_part A hmono cp true alloc _ h ?_ ?_ ?_ ?_
    · exact fun p hp => hpool_sub p (List.mem_of_mem_drop (List.mem_of_mem_take hp))
    · exact fun p hp => (hpool_prop p (List.mem_of_mem_drop (List.mem_of_mem_take hp))).2
    · exact (hpool_nodup.sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _)
    · rw [List.length_take, List.length_drop, ← hnt]
      omega

/-- The full recursion preserves the invariant. -/
theorem runAlloc_inv {r : BitString → ℕ} (A : TreeAllocation q s)
    (hcoh : ∀ x, r (x ++ [false]) + r (x ++ [true]) ≤ r x)
    (hmono : ∀ x, 2 * q x ≤ r x) (u cp : BitString) (alloc : List BitString)
    (h : AllocInv r A cp alloc) :
    AllocInv r A (cp ++ u) (runAlloc r A cp u alloc) := by
  induction u generalizing cp alloc with
  | nil => simpa [runAlloc] using h
  | cons b bs ih =>
    have := ih (cp ++ [b]) (stepAlloc r A cp b alloc) (stepAlloc_inv A hcoh hmono cp b alloc h)
    simpa [runAlloc] using this

/-- A child's allocation is contained in its parent's allocation. -/
theorem stepAlloc_subset {r : BitString → ℕ} (A : TreeAllocation q s)
    (cp : BitString) (b : Bool) (alloc : List BitString)
    (h : AllocInv r A cp alloc) : stepAlloc r A cp b alloc ⊆ alloc := by
  have hM : ∀ c : Bool, refineAtoms (A.atoms (cp ++ [c])) ⊆ alloc := fun c =>
    fun p hp => h.sub (refine_child_subset A cp c hp)
  intro p hp
  cases b with
  | false =>
    rcases List.mem_append.mp hp with hp | hp
    · exact hM false hp
    · exact (List.mem_filter.mp (List.mem_of_mem_take hp)).1
  | true =>
    rcases List.mem_append.mp hp with hp | hp
    · exact hM true hp
    · exact (List.mem_filter.mp (List.mem_of_mem_drop (List.mem_of_mem_take hp))).1

/-- The two children of a node receive disjoint allocations. -/
theorem stepAlloc_disjoint {r : BitString → ℕ} (A : TreeAllocation q s)
    (cp : BitString) (alloc : List BitString) (h : AllocInv r A cp alloc) (p : BitString)
    (hf : p ∈ stepAlloc r A cp false alloc) (ht : p ∈ stepAlloc r A cp true alloc) : False := by
  set Mf := refineAtoms (A.atoms (cp ++ [false])) with hMf
  set Mt := refineAtoms (A.atoms (cp ++ [true])) with hMt
  set pool := alloc.filter (fun p => decide (p ∉ Mf ∧ p ∉ Mt)) with hpooldef
  set nf := r (cp ++ [false]) - Mf.length with hnf
  set nt := r (cp ++ [true]) - Mt.length with hnt
  have hfe : stepAlloc r A cp false alloc = Mf ++ pool.take nf := rfl
  have hte : stepAlloc r A cp true alloc = Mt ++ (pool.drop nf).take nt := rfl
  rw [hfe] at hf
  rw [hte] at ht
  have hpool_prop : ∀ y ∈ pool, y ∉ Mf ∧ y ∉ Mt := by
    intro y hy
    simpa using (List.mem_filter.mp hy).2
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp ht with ht | ht
    · exact refine_children_disjoint A cp p hf ht
    · exact (hpool_prop p (List.mem_of_mem_drop (List.mem_of_mem_take ht))).1 hf
  · rcases List.mem_append.mp ht with ht | ht
    · exact (hpool_prop p (List.mem_of_mem_take hf)).2 ht
    · exact List.disjoint_take_drop (h.nodup.filter _) (Nat.le_refl nf) hf
        (List.mem_of_mem_take ht)

/-- The invariant holds at the root, where every program of length `s + 1` is available. -/
theorem root_inv {r : BitString → ℕ} (A : TreeAllocation q s) (hroot : r [] = 2 ^ (s + 1)) :
    AllocInv r A [] (exactLengthPrograms (s + 1)) where
  len := fun p hp => exactLengthPrograms_length_eq _ p hp
  nodup := exactLengthPrograms_nodup _
  card := by rw [length_exactLengthPrograms, hroot]
  sub := fun p hp =>
    mem_exactLengthPrograms_of_length p (s + 1) (refine_atoms_mem_length A [] p hp)

/-- Two-branch unfolding of the extension: `A.extendAtoms q r s x` is the empty allocation at
every node `x` deeper than `s + 1`, and otherwise the run `runAlloc r A [] x` from the root
over all programs of length `s + 1`.  Beyond the depth guard nothing is allocated. -/
theorem extendAtoms_eq (r : BitString → ℕ) (A : TreeAllocation q s) (x : BitString) :
    A.extendAtoms q r s x =
      if s + 1 < x.length then [] else runAlloc r A [] x (exactLengthPrograms (s + 1)) := by
  rw [show A.extendAtoms q r s x = extendAtoms.go q r s A [] x (exactLengthPrograms (s + 1)) from
    rfl, go_eq]
  simp

/-- Beyond the frontier, all allocations are empty. -/
theorem refineAtoms_atoms_eq_nil {r : BitString → ℕ} (A : TreeAllocation q s)
    (hmono : ∀ x, 2 * q x ≤ r x) (x : BitString) (hx : r x = 0) :
    refineAtoms (A.atoms x) = [] := by
  have h : (refineAtoms (A.atoms x)).length = 0 := by
    rw [refineAtoms_length, A.atoms_card]
    have := hmono x
    omega
  exact List.eq_nil_of_length_eq_zero h

/-- The allocation produced by `extendAtoms` satisfies the invariant everywhere. -/
theorem extendAtoms_inv {r : BitString → ℕ} (A : TreeAllocation q s)
    (hroot : r [] = 2 ^ (s + 1))
    (hcoh : ∀ x, r (x ++ [false]) + r (x ++ [true]) ≤ r x)
    (hfront : ∀ x, s + 1 < x.length → r x = 0)
    (hmono : ∀ x, 2 * q x ≤ r x) (x : BitString) :
    AllocInv r A x (A.extendAtoms q r s x) := by
  rw [extendAtoms_eq]
  by_cases hx : s + 1 < x.length
  · have hr : r x = 0 := hfront x hx
    rw [ite_eq_left hx]
    exact ⟨by simp, List.nodup_nil, by simp [hr],
      by rw [refineAtoms_atoms_eq_nil A hmono x hr]⟩
  · rw [ite_eq_right hx]
    have := runAlloc_inv A hcoh hmono x [] (exactLengthPrograms (s + 1)) (root_inv A hroot)
    simpa using this

/-- At the root the extension allocates every atom of the new length. -/
theorem extendAtoms_nil (r : BitString → ℕ) (A : TreeAllocation q s) :
    A.extendAtoms q r s [] = exactLengthPrograms (s + 1) := by
  rw [extendAtoms_eq]
  simp [runAlloc]

/-- A child's atoms are among its parent's atoms. -/
theorem extendAtoms_child {r : BitString → ℕ} (A : TreeAllocation q s)
    (hroot : r [] = 2 ^ (s + 1))
    (hcoh : ∀ x, r (x ++ [false]) + r (x ++ [true]) ≤ r x)
    (hmono : ∀ x, 2 * q x ≤ r x) (x : BitString) (b : Bool) :
    A.extendAtoms q r s (x ++ [b]) ⊆ A.extendAtoms q r s x := by
  by_cases hx : s + 1 < (x ++ [b]).length
  · rw [extendAtoms_eq, ite_eq_left hx]
    exact List.nil_subset _
  · have hlen : (x ++ [b]).length = x.length + 1 := by simp
    have hx' : ¬ s + 1 < x.length := by omega
    rw [extendAtoms_eq, ite_eq_right hx, extendAtoms_eq r A x, ite_eq_right hx', runAlloc_append,
      List.nil_append]
    refine stepAlloc_subset A x b _ ?_
    simpa using runAlloc_inv A hcoh hmono x [] (exactLengthPrograms (s + 1)) (root_inv A hroot)

/-- Sibling subtrees get disjoint atoms. -/
theorem extendAtoms_disjoint {r : BitString → ℕ} (A : TreeAllocation q s)
    (hroot : r [] = 2 ^ (s + 1))
    (hcoh : ∀ x, r (x ++ [false]) + r (x ++ [true]) ≤ r x)
    (hmono : ∀ x, 2 * q x ≤ r x) (x : BitString) (p : BitString)
    (hp : p ∈ A.extendAtoms q r s (x ++ [false])) : p ∉ A.extendAtoms q r s (x ++ [true]) := by
  intro hp'
  by_cases hx : s + 1 < (x ++ [false]).length
  · rw [extendAtoms_eq, ite_eq_left hx] at hp
    exact List.not_mem_nil hp
  · have hlen : (x ++ [false]).length = x.length + 1 := by simp
    have hlen' : (x ++ [true]).length = x.length + 1 := by simp
    have hx' : ¬ s + 1 < (x ++ [true]).length := by omega
    rw [extendAtoms_eq, ite_eq_right hx, runAlloc_append, List.nil_append] at hp
    rw [extendAtoms_eq, ite_eq_right hx', runAlloc_append, List.nil_append] at hp'
    refine stepAlloc_disjoint A x _ ?_ p hp hp'
    simpa using runAlloc_inv A hcoh hmono x [] (exactLengthPrograms (s + 1)) (root_inv A hroot)

end TreeAllocation

/-- The next stage of an allocation, for numerators that are exact at the root, coherent, vanish
below the frontier and at least double the previous ones. -/
def TreeAllocation.extend {q r : BitString → ℕ} {s : ℕ} (A : TreeAllocation q s)
    (hroot : r [] = 2 ^ (s + 1))
    (hcoh : ∀ x, r (x ++ [false]) + r (x ++ [true]) ≤ r x)
    (hfront : ∀ x, s + 1 < x.length → r x = 0)
    (hmono : ∀ x, 2 * q x ≤ r x) : TreeAllocation r (s + 1) where
  atoms := A.extendAtoms q r s
  atoms_length := fun x p hp =>
    (TreeAllocation.extendAtoms_inv A hroot hcoh hfront hmono x).len p hp
  atoms_nodup := fun x => (TreeAllocation.extendAtoms_inv A hroot hcoh hfront hmono x).nodup
  atoms_card := fun x => (TreeAllocation.extendAtoms_inv A hroot hcoh hfront hmono x).card
  atoms_root := fun p hp => by
    rw [TreeAllocation.extendAtoms_nil]
    exact mem_exactLengthPrograms_of_length p (s + 1) hp
  atoms_child := fun x b p hp => TreeAllocation.extendAtoms_child A hroot hcoh hmono x b hp
  atoms_disjoint := fun x p hp => TreeAllocation.extendAtoms_disjoint A hroot hcoh hmono x p hp

/-- The extension keeps the refined atoms of the previous stage, so the stages are nested. -/
theorem TreeAllocation.extend_refines {q r : BitString → ℕ} {s : ℕ} (A : TreeAllocation q s)
    (hroot : r [] = 2 ^ (s + 1))
    (hcoh : ∀ x, r (x ++ [false]) + r (x ++ [true]) ≤ r x)
    (hfront : ∀ x, s + 1 < x.length → r x = 0)
    (hmono : ∀ x, 2 * q x ≤ r x) (x : BitString) :
    ∀ p ∈ refineAtoms (A.atoms x), p ∈ (A.extend hroot hcoh hfront hmono).atoms x := fun _ hp =>
  (TreeAllocation.extendAtoms_inv A hroot hcoh hfront hmono x).sub hp

end Kolmogorov
