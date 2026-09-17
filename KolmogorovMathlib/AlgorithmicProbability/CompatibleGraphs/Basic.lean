import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.Prefix.SelfDelimitingMachines

/-!
# Compatible graphs, and the geometry of the free list

Two subjects that the a priori probability of a continuous map needs.

### Compatible graphs

A *compatible graph* is a set of pairs (finite input, output) closed under the conditions that
make it the graph of a continuous map on `Σ ∪ Ω`.  `continuous_F_of_A` and `contGraph_F_of_A`
show that reading a map off a graph and taking the graph of a map are mutually inverse;
`existsUnique_continuousMap_of_compatibleGraph` and `continuousMap_graph_bijection` package
this as SUV Theorem 54: `F ↦ Γ_F` is a bijection between continuous maps `Σ ∪ Ω → ℕ⊥` and
compatible graph sets.

### The binary tree seen through `leftValue`

`leftValue` reads a bitstring as a big-endian numeral, so that padding two strings to a common
length compares the dyadic intervals they name.  Its arithmetic (`leftValue_append`,
`leftValue_cons_true`, `leftValue_lt_pow`, `leftValue_le_of_prefix`) supports the analysis of
the Kraft–Chaitin allocator: `splitNodeBlock` is the block of free nodes that replaces a node
when a codeword is cut out of it, `exists_alloc_overlap_or_free_prefix` says the allocator
leaves no gap in the tree, and `allocatorState_getElem_incomparable` says distinct entries of
the free list are prefix-incomparable.  The remaining order lemma is in `APrioriMarginals`.
-/



namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-- The partial function read off a compatible graph is continuous for the topology of the
extension order on finite and infinite sequences. -/
lemma continuous_F_of_A (A : Set (BitString × ℕ)) (hA : IsCompatibleGraph A) :
    @Continuous SeqE (Option ℕ) eTopology natBotTopology (F_of_A A) := by
  rw [continuous_natBotTopology_iff]
  intro m
  have h_eq : (F_of_A A) ⁻¹' {some m} = ⋃ (x : BitString) (_ : (x, m) ∈ A), sequenceCylinder x := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, sequenceCylinder,
      Set.mem_ofPred_eq]
    rw [F_of_A_eq_some A hA z m]
    constructor
    · rintro ⟨x, h1, h2⟩; exact ⟨x, h1, h2⟩
    · rintro ⟨x, h1, h2⟩; exact ⟨x, h1, h2⟩
  rw [h_eq]
  let instSeqE : TopologicalSpace SeqE := eTopology
  refine isOpen_biUnion fun x _ => ?_
  exact TopologicalSpace.GenerateOpen.basic _ ⟨x, rfl⟩

/-- Reading a continuous function off a compatible graph and taking its graph again returns the
graph one started from. -/
lemma contGraph_F_of_A (A : Set (BitString × ℕ)) (hA : IsCompatibleGraph A) :
    contGraph (F_of_A A) = A := by
  ext ⟨x, m⟩
  simp [contGraph, F_of_A_inl_eq_some A hA]

/-- **Theorem 54, uniqueness clause.** Every compatible graph set is the graph of
exactly one continuous map. -/
theorem existsUnique_continuousMap_of_compatibleGraph (A : Set (BitString × ℕ))
    (hA : IsCompatibleGraph A) :
    ∃! F : SeqE → Option ℕ,
      @Continuous SeqE (Option ℕ) eTopology natBotTopology F ∧ contGraph F = A := by
  refine ⟨F_of_A A, ⟨continuous_F_of_A A hA, contGraph_F_of_A A hA⟩, ?_⟩
  intro F ⟨hF_cont, hF_graph⟩
  ext z
  cases z with
  | inl x =>
    cases hF : F (Sum.inl x) with
    | none =>
      have hF_A : F_of_A A (Sum.inl x) = none := by
        by_contra h_some
        cases h_ex : F_of_A A (Sum.inl x) with
        | none => contradiction
        | some m =>
          rw [F_of_A_inl_eq_some A hA] at h_ex
          rw [← hF_graph] at h_ex
          dsimp [contGraph] at h_ex
          rw [hF] at h_ex
          contradiction
      rw [hF_A]
    | some m =>
      have hx : (x, m) ∈ contGraph F := hF
      rw [hF_graph] at hx
      have hF_A : F_of_A A (Sum.inl x) = some m := (F_of_A_inl_eq_some A hA x m).mpr hx
      rw [hF_A]
  | inr w =>
    cases hF : F (Sum.inr w) with
    | none =>
      have hF_A : F_of_A A (Sum.inr w) = none := by
        by_contra h_some
        cases h_ex : F_of_A A (Sum.inr w) with
        | none => contradiction
        | some m =>
          rw [F_of_A_inr_eq_some A hA] at h_ex
          rcases h_ex with ⟨n, hA_n⟩
          have h_graph : F (Sum.inl (streamTake w n)) = some m := by
            rw [← hF_graph] at hA_n
            exact hA_n
          have h_open : @IsOpen SeqE eTopology (F ⁻¹' {some m}) :=
            (continuous_natBotTopology_iff F).mp hF_cont m
          have h_ext : Sum.inr w ∈ F ⁻¹' {some m} :=
            isOpen_eTopology_extends h_open (EExtends_streamTake w n) h_graph
          change F (Sum.inr w) = some m at h_ext
          rw [hF] at h_ext
          contradiction
      rw [hF_A]
    | some m =>
      have h_open : @IsOpen SeqE eTopology (F ⁻¹' {some m}) :=
        (continuous_natBotTopology_iff F).mp hF_cont m
      have h_inr : Sum.inr w ∈ F ⁻¹' {some m} := hF
      rcases isOpen_eTopology_stream h_open h_inr with ⟨n, hn⟩
      change F (Sum.inl (streamTake w n)) = some m at hn
      have hA_n : (streamTake w n, m) ∈ A := by
        rw [← hF_graph]
        exact hn
      have hF_A : F_of_A A (Sum.inr w) = some m := (F_of_A_inr_eq_some A hA w m).mpr ⟨n, hA_n⟩
      rw [hF_A]

/-- **Theorem 54.** `F ↦ Γ_F` is a bijection between the continuous maps
`Σ ∪ Ω → ℕ⊥` and the compatible graph sets. -/
theorem continuousMap_graph_bijection :
    Set.BijOn contGraph {F | @Continuous SeqE (Option ℕ) eTopology natBotTopology F}
      {A | IsCompatibleGraph A} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro F (hF : @Continuous SeqE (Option ℕ) eTopology natBotTopology F)
    refine ⟨?_, ?_⟩
    · intro x y n hxn hxy
      dsimp [contGraph] at hxn ⊢
      have h_open : @IsOpen SeqE eTopology (F ⁻¹' {some n}) :=
        (continuous_natBotTopology_iff F).mp hF n
      exact isOpen_eTopology_extends h_open hxy hxn
    · intro x n m hxn hxm
      dsimp [contGraph] at hxn hxm
      rw [hxn] at hxm
      injection hxm
  · intro F1 hF1 F2 hF2 hEq
    have hA : IsCompatibleGraph (contGraph F1) := by
      refine ⟨?_, ?_⟩
      · intro x y n hxn hxy
        dsimp [contGraph] at hxn ⊢
        have h_open : @IsOpen SeqE eTopology (F1 ⁻¹' {some n}) :=
          (continuous_natBotTopology_iff F1).mp hF1 n
        exact isOpen_eTopology_extends h_open hxy hxn
      · intro x n m hxn hxm
        dsimp [contGraph] at hxn hxm; rw [hxn] at hxm; injection hxm
    have hUniq := existsUnique_continuousMap_of_compatibleGraph (contGraph F1) hA
    have h1 : F1 = F_of_A (contGraph F1) := by
      exact hUniq.unique ⟨hF1, rfl⟩ ⟨continuous_F_of_A _ hA, contGraph_F_of_A _ hA⟩
    have h2 : F2 = F_of_A (contGraph F1) := by
      exact hUniq.unique ⟨hF2, hEq.symm⟩ ⟨continuous_F_of_A _ hA, contGraph_F_of_A _ hA⟩
    rw [h1, h2]
  · intro A hA
    refine ⟨F_of_A A, continuous_F_of_A A hA, contGraph_F_of_A A hA⟩

/-! ### A priori probability: grouping and marginals -/

/-- The value of a bit string read as a big-endian binary numeral; it orders the
strings of a fixed length from left to right, i.e. by the position of the
corresponding dyadic interval. -/
def leftValue (w : BitString) : ℕ := w.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0

/-- The left fold computing the value of a bitstring, started from an accumulator, shifts that
accumulator by the length of the string and adds the value of the string. -/
lemma foldl_leftValue_aux (v : BitString) (acc : ℕ) :
    v.foldl (fun a b => 2 * a + (if b then 1 else 0)) acc = acc * 2 ^ v.length + leftValue v := by
  induction v generalizing acc with
  | nil => simp [leftValue]
  | cons x xs ih =>
    have h1 : (2 * acc + if x then 1 else 0) * 2 ^ xs.length + leftValue xs =
        acc * 2 ^ (xs.length + 1) + ((if x then 1 else 0) * 2 ^ xs.length + leftValue xs) := by
      rw [pow_succ]; ring
    have hzero : (if x then 1 else 0) = 0 + if x then 1 else 0 := (zero_add _).symm
    dsimp [leftValue, List.foldl_cons, List.length_cons]
    rw [ih (2 * acc + if x then 1 else 0), h1, ← ih (if x then 1 else 0)]
    nth_rw 1 [hzero]

/-- The value of a concatenation shifts the value of the first factor by the length of the
second one. -/
lemma leftValue_append (w v : BitString) :
    leftValue (w ++ v) = leftValue w * 2 ^ v.length + leftValue v := by
  simp only [leftValue, List.foldl_append]
  exact foldl_leftValue_aux v (leftValue w)

/-- Prefixing a one adds the corresponding power of two. -/
lemma leftValue_cons_true (xs : BitString) :
    leftValue (true :: xs) = 2 ^ xs.length + leftValue xs := by
  change List.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0 (true :: xs) = _
  rw [List.foldl_cons]
  have h1 : 2 * 0 + (if true then 1 else 0) = 1 := rfl
  rw [h1, foldl_leftValue_aux, one_mul]

/-- Prefixing a zero leaves the value unchanged. -/
lemma leftValue_cons_false (xs : BitString) :
    leftValue (false :: xs) = leftValue xs := by
  change List.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0 (false :: xs) = _
  rw [List.foldl_cons]
  have h1 : 2 * 0 + (if false then 1 else 0) = 0 := rfl
  rw [h1, foldl_leftValue_aux, zero_mul, zero_add]

/-- A string of zeros has value zero. -/
lemma leftValue_replicate_false (k : ℕ) :
    leftValue (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change List.foldl (fun a b => 2 * a + if b then 1 else 0) 0 (List.replicate (k + 1) false) = 0
    rw [List.replicate_succ, List.foldl_cons]
    have hzero : (2 * 0 + if false then 1 else 0) = 0 := rfl
    rw [hzero]
    exact ih

/-- Padding a prefix with zeros to the length of the extending string does not raise its value:
`leftValue` is monotone along the prefix order once both strings are padded to one length. -/
lemma leftValue_le_of_prefix (v u : BitString) (l : ℕ) (h : v <+: u) (hu : u.length = l) :
    leftValue (v ++ List.replicate (l - v.length) false) ≤ leftValue u := by
  obtain ⟨s, rfl⟩ := h
  have hs : s.length = l - v.length := by
    have hlen : (v ++ s).length = l := hu
    rw [List.length_append] at hlen
    omega
  rw [leftValue_append, leftValue_append, leftValue_replicate_false, add_zero,
    List.length_replicate, hs]
  exact Nat.le_add_right _ _

/-- Against a block of `diff` zeros a string is either a prefix of it, or extends it, or first
differs from it at a one in a position below `diff`. -/
lemma replicate_false_trichotomy (s : BitString) (diff : ℕ) :
    (s <+: List.replicate diff false) ∨
    (List.replicate diff false <+: s) ∨
    (∃ m < diff, List.replicate m false ++ [true] <+: s) := by
  induction diff generalizing s with
  | zero =>
    right; left
    exact List.nil_prefix
  | succ diff ih =>
    cases s with
    | nil =>
      left
      exact List.nil_prefix
    | cons b s =>
      cases b with
      | false =>
        rcases ih s with h1 | h2 | ⟨m, hm, ⟨t, ht⟩⟩
        · left
          rw [List.replicate_succ]
          obtain ⟨t, ht⟩ := h1
          exact ⟨t, by simp [ht]⟩
        · right; left
          rw [List.replicate_succ]
          obtain ⟨t, ht⟩ := h2
          exact ⟨t, by simp [ht]⟩
        · right; right
          use m + 1
          refine ⟨Nat.add_lt_add_right hm 1, t, ?_⟩
          rw [List.replicate_succ]
          simp [ht]
      | true =>
        right; right
        use 0
        refine ⟨Nat.succ_pos _, s, ?_⟩
        rw [List.replicate_zero, List.nil_append]
        rfl

/-- The value of a string of length `n` is below `2^n`. -/
lemma leftValue_lt_pow (w : BitString) : leftValue w < 2 ^ w.length := by
  induction w with
  | nil => decide
  | cons b w ih =>
    cases b
    · rw [leftValue_cons_false, List.length_cons, pow_succ]
      omega
    · rw [leftValue_cons_true, List.length_cons, pow_succ]
      omega

/-- In a free list with strictly descending description lengths, a later entry is strictly shorter
than an earlier one. -/
lemma descLengths_getElem_length_lt {free : List BitString} (hd : KraftChaitin.DescLengths free)
    {i j : ℕ} (hij : i < j) (hj : j < free.length) :
    (free[j]'hj).length < (free[i]'(lt_trans hij hj)).length := by
  have : Trans (fun a b : BitString => b.length < a.length)
      (fun a b : BitString => b.length < a.length)
      (fun a b : BitString => b.length < a.length) :=
    ⟨fun {a b c : BitString} (hab : b.length < a.length) (hbc : c.length < b.length) =>
      lt_trans hbc hab⟩
  have hp : List.Pairwise (fun a b : BitString => b.length < a.length) free :=
    List.isChain_iff_pairwise.mp hd
  rw [List.pairwise_iff_get] at hp
  simpa using hp ⟨i, lt_trans hij hj⟩ ⟨j, hj⟩ (by simpa using hij)

/-- Two incomparable strings padded to a common length keep their order strictly: if the padded
value of `v` is at most that of `u`, the whole block of `v` lies below `u`. -/
lemma leftValue_ge_of_prefixFree_and_le (v u : BitString) (L : ℕ)
    (hv : v.length ≤ L) (hu : u.length ≤ L) (hpf : ¬ v <+: u) (hpu : ¬ u <+: v)
    (h_le : leftValue (v ++ List.replicate (L - v.length) false) ≤
            leftValue (u ++ List.replicate (L - u.length) false)) :
    (leftValue v + 1) * 2 ^ (L - v.length) ≤
    leftValue (u ++ List.replicate (L - u.length) false) := by
  induction v generalizing u L with
  | nil => exfalso; exact hpf List.nil_prefix
  | cons b1 v1 ih =>
    cases u with
    | nil => exfalso; exact hpu List.nil_prefix
    | cons b2 u1 =>
      cases L with
      | zero => simp only [List.length_cons] at hv; omega
      | succ L' =>
        have hv1 : v1.length ≤ L' := by simp only [List.length_cons] at hv; omega
        have hu1 : u1.length ≤ L' := by simp only [List.length_cons] at hu; omega
        have h_v_len : L' + 1 - (v1.length + 1) = L' - v1.length := by omega
        have h_u_len : L' + 1 - (u1.length + 1) = L' - u1.length := by omega
        have h_le' : leftValue ((b1 :: v1) ++ List.replicate (L' - v1.length) false) ≤
            leftValue ((b2 :: u1) ++ List.replicate (L' - u1.length) false) := by
          simpa [h_v_len, h_u_len] using h_le
        cases b1 <;> cases b2
        · have hpf1 : ¬ v1 <+: u1 := fun h => hpf (by simp [h])
          have hpu1 : ¬ u1 <+: v1 := fun h => hpu (by simp [h])
          have h_v_app : leftValue ((false :: v1) ++ List.replicate (L' - v1.length) false) =
              leftValue (v1 ++ List.replicate (L' - v1.length) false) := by
            rw [List.cons_append, leftValue_cons_false]
          have h_u_app : leftValue ((false :: u1) ++ List.replicate (L' - u1.length) false) =
              leftValue (u1 ++ List.replicate (L' - u1.length) false) := by
            rw [List.cons_append, leftValue_cons_false]
          rw [h_v_app, h_u_app] at h_le'
          have h_ih := ih u1 L' hv1 hu1 hpf1 hpu1 h_le'
          have h_val : (leftValue (false :: v1) + 1) * 2 ^ (L' + 1 - (false :: v1).length) =
              (leftValue v1 + 1) * 2 ^ (L' - v1.length) := by
            rw [leftValue_cons_false]
            have h1 : L' + 1 - (false :: v1).length = L' - v1.length := by
              simp only [List.length_cons]; omega
            rw [h1]
          have h_u_app' : leftValue ((false :: u1) ++
              List.replicate (L' + 1 - (false :: u1).length) false) =
              leftValue (u1 ++ List.replicate (L' - u1.length) false) := by
            have h1 : L' + 1 - (false :: u1).length = L' - u1.length := by
              simp only [List.length_cons]; omega
            rw [List.cons_append, h1, leftValue_cons_false]
          rw [h_val, h_u_app']
          exact h_ih
        · have h_v_app : leftValue ((false :: v1) ++ List.replicate (L' - v1.length) false) =
              leftValue (v1 ++ List.replicate (L' - v1.length) false) := by
            rw [List.cons_append, leftValue_cons_false]
          have h_u_app : leftValue ((true :: u1) ++ List.replicate (L' - u1.length) false) =
              2 ^ L' + leftValue (u1 ++ List.replicate (L' - u1.length) false) := by
            rw [List.cons_append, leftValue_cons_true, List.length_append,
              List.length_replicate, Nat.add_sub_of_le hu1]
          rw [h_v_app, h_u_app] at h_le'
          have h_val : (leftValue (false :: v1) + 1) * 2 ^ (L' + 1 - (false :: v1).length) =
              (leftValue v1 + 1) * 2 ^ (L' - v1.length) := by
            rw [leftValue_cons_false]
            have h1 : L' + 1 - (false :: v1).length = L' - v1.length := by
              simp only [List.length_cons]; omega
            rw [h1]
          have h_u_app' : leftValue ((true :: u1) ++
              List.replicate (L' + 1 - (true :: u1).length) false) =
              2 ^ L' + leftValue (u1 ++ List.replicate (L' - u1.length) false) := by
            have h1 : L' + 1 - (true :: u1).length = L' - u1.length := by
              simp only [List.length_cons]; omega
            rw [List.cons_append, h1, leftValue_cons_true, List.length_append,
              List.length_replicate, Nat.add_sub_of_le hu1]
          rw [h_val, h_u_app']
          have h_bound : (leftValue v1 + 1) * 2 ^ (L' - v1.length) ≤ 2 ^ L' := by
            have h2 : leftValue v1 + 1 ≤ 2 ^ v1.length := leftValue_lt_pow v1
            have h3 : (leftValue v1 + 1) * 2 ^ (L' - v1.length) ≤
                2 ^ v1.length * 2 ^ (L' - v1.length) := by gcongr
            rw [← pow_add, Nat.add_sub_of_le hv1] at h3
            exact h3
          omega
        · have h_v_app : leftValue ((true :: v1) ++ List.replicate (L' - v1.length) false) =
              2 ^ L' + leftValue (v1 ++ List.replicate (L' - v1.length) false) := by
            rw [List.cons_append, leftValue_cons_true, List.length_append,
              List.length_replicate, Nat.add_sub_of_le hv1]
          have h_u_app : leftValue ((false :: u1) ++ List.replicate (L' - u1.length) false) =
              leftValue (u1 ++ List.replicate (L' - u1.length) false) := by
            rw [List.cons_append, leftValue_cons_false]
          have h_u_lt : leftValue (u1 ++ List.replicate (L' - u1.length) false) < 2 ^ L' := by
            rw [leftValue_append, leftValue_replicate_false, add_zero, List.length_replicate]
            have : leftValue u1 < 2 ^ u1.length := leftValue_lt_pow u1
            have : leftValue u1 * 2 ^ (L' - u1.length) < 2 ^ u1.length * 2 ^ (L' - u1.length) := by
              gcongr
            rw [← pow_add, Nat.add_sub_of_le hu1] at this
            exact this
          have h_val : (leftValue (true :: v1) + 1) * 2 ^ (L' + 1 - (true :: v1).length) =
              2 ^ L' + (leftValue v1 + 1) * 2 ^ (L' - v1.length) := by
            rw [leftValue_cons_true]
            have h1 : L' + 1 - (true :: v1).length = L' - v1.length := by
              simp only [List.length_cons]; omega
            rw [h1, add_assoc, add_mul]
            congr 1
            rw [← pow_add, Nat.add_sub_of_le hv1]
          have h_u_app' : leftValue ((false :: u1) ++
              List.replicate (L' + 1 - (false :: u1).length) false) =
              leftValue (u1 ++ List.replicate (L' - u1.length) false) := by
            have h1 : L' + 1 - (false :: u1).length = L' - u1.length := by
              simp only [List.length_cons]; omega
            rw [List.cons_append, h1, leftValue_cons_false]
          rw [h_v_app, h_u_app] at h_le'
          rw [h_val, h_u_app']
          omega
        · have hpf1 : ¬ v1 <+: u1 := fun h => hpf (by simp [h])
          have hpu1 : ¬ u1 <+: v1 := fun h => hpu (by simp [h])
          have h_v_app : leftValue ((true :: v1) ++ List.replicate (L' - v1.length) false) =
              2 ^ L' + leftValue (v1 ++ List.replicate (L' - v1.length) false) := by
            rw [List.cons_append, leftValue_cons_true, List.length_append,
              List.length_replicate, Nat.add_sub_of_le hv1]
          have h_u_app : leftValue ((true :: u1) ++ List.replicate (L' - u1.length) false) =
              2 ^ L' + leftValue (u1 ++ List.replicate (L' - u1.length) false) := by
            rw [List.cons_append, leftValue_cons_true, List.length_append,
              List.length_replicate, Nat.add_sub_of_le hu1]
          rw [h_v_app, h_u_app] at h_le'
          have h_le'' : leftValue (v1 ++ List.replicate (L' - v1.length) false) ≤
              leftValue (u1 ++ List.replicate (L' - u1.length) false) := by omega
          have h_ih := ih u1 L' hv1 hu1 hpf1 hpu1 h_le''
          have h_val : (leftValue (true :: v1) + 1) * 2 ^ (L' + 1 - (true :: v1).length) =
              2 ^ L' + (leftValue v1 + 1) * 2 ^ (L' - v1.length) := by
            rw [leftValue_cons_true]
            have h1 : L' + 1 - (true :: v1).length = L' - v1.length := by
              simp only [List.length_cons]; omega
            rw [h1, add_assoc, add_mul]
            congr 1
            rw [← pow_add, Nat.add_sub_of_le hv1]
          have h_u_app' : leftValue ((true :: u1) ++
              List.replicate (L' + 1 - (true :: u1).length) false) =
              2 ^ L' + leftValue (u1 ++ List.replicate (L' - u1.length) false) := by
            have h1 : L' + 1 - (true :: u1).length = L' - u1.length := by
              simp only [List.length_cons]; omega
            rw [List.cons_append, h1, leftValue_cons_true, List.length_append,
              List.length_replicate, Nat.add_sub_of_le hu1]
          rw [h_val, h_u_app']
          omega

/-- The value of the node the allocator splits off, padded to length `L`. -/
lemma leftValue_newNode_pad (v : BitString) (l m L : ℕ) (hv : v.length ≤ l) (hl : l - m ≤ L)
    (hm : m < l - v.length) :
    leftValue (v ++ List.replicate (l - v.length - 1 - m) false ++ [true] ++
        List.replicate (L - (l - m)) false) =
      leftValue v * 2 ^ (L - v.length) + 2 ^ (L - (l - m)) := by
  have h_len : (v ++ List.replicate (l - v.length - 1 - m) false ++ [true]).length = l - m := by
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    omega
  rw [leftValue_append, leftValue_append, leftValue_append, leftValue_replicate_false, add_zero,
    leftValue_replicate_false, add_zero]
  have h_true : leftValue [true] = 1 := rfl
  rw [h_true]
  simp only [List.length_singleton, List.length_replicate]
  have h_exp : (l - v.length - 1 - m + 1) + (L - (l - m)) = L - v.length := by omega
  have h_p : 2 ^ (l - v.length - 1 - m + 1) * 2 ^ (L - (l - m)) = 2 ^ (L - v.length) := by
    rw [← pow_add, h_exp]
  have h_pow : leftValue v * 2 ^ (l - v.length - 1 - m + 1) * 2 ^ (L - (l - m)) =
      leftValue v * 2 ^ (L - v.length) := by
    rw [mul_assoc, h_p]
  have h_pow2 : 1 * 2 ^ (L - (l - m)) = 2 ^ (L - (l - m)) := by
    rw [one_mul]
  have h_assoc_pow : 2 ^ (l - v.length - 1 - m) * 2 ^ 1 = 2 ^ (l - v.length - 1 - m + 1) := by
    rw [← pow_add]
  rw [add_mul, mul_assoc (leftValue v), h_assoc_pow, h_pow, h_pow2]

/-- Every string is either comparable with a code already allocated before stage `n`, or extends a
string still free at stage `n`: the allocator leaves no gap in the binary tree. -/
lemma exists_alloc_overlap_or_free_prefix (req : ℕ → Option (BitString × ℕ)) (n : ℕ)
    (free : List BitString) (hfree : KraftChaitin.allocatorState req n = some free)
    (u : BitString) :
    (∃ i < n, ∃ v, KraftChaitin.allocFun req i = some v ∧ (u <+: v ∨ v <+: u)) ∨
    (∃ w ∈ free, w <+: u) := by
  induction n generalizing free with
  | zero =>
    unfold KraftChaitin.allocatorState at hfree
    have h1 : free = [[]] := Option.some.inj hfree.symm
    subst h1
    right
    refine ⟨[], by simp, List.nil_prefix⟩
  | succ n ih =>
    unfold KraftChaitin.allocatorState at hfree
    rcases hF : KraftChaitin.allocatorState req n with _ | F
    · rw [hF] at hfree; contradiction
    rw [hF] at hfree
    dsimp only at hfree
    rcases hreq : req n with _ | ⟨o, l⟩
    · rw [hreq] at hfree
      injection hfree with h1; subst h1
      rcases ih F hF with ⟨i, hi_lt, v, hv, hov⟩ | ⟨w, hw_mem, hw_pre⟩
      · left; exact ⟨i, Nat.lt_succ_of_lt hi_lt, v, hv, hov⟩
      · right; exact ⟨w, hw_mem, hw_pre⟩
    · rw [hreq] at hfree
      dsimp only at hfree
      rcases halloc : KraftChaitin.allocateOne F l with _ | ⟨w_n, free'⟩
      · rw [halloc] at hfree; contradiction
      rw [halloc] at hfree
      injection hfree with h1; subst h1
      rcases ih F hF with ⟨i, hi_lt, v, hv, hov⟩ | ⟨w, hw_mem, hw_pre⟩
      · left; exact ⟨i, Nat.lt_succ_of_lt hi_lt, v, hv, hov⟩
      · have h_allocFun_n : KraftChaitin.allocFun req n = some w_n := by
          have h1 : KraftChaitin.allocFun req n = (match KraftChaitin.allocatorState req n with
            | none => none
            | some free =>
              match req n with
              | none => none
              | some (_, l) =>
                match KraftChaitin.allocateOne free l with
                | none => none
                | some (allocated, _) => some allocated) := rfl
          rw [h1, hF, hreq]
          dsimp only
          rw [halloc]
        unfold KraftChaitin.allocateOne at halloc
        rcases hfind : F.findIdx? (fun v => v.length ≤ l) with _ | idx
        · rw [hfind] at halloc; contradiction
        rw [hfind] at halloc
        injection halloc with hw_n_eq
        have h_wn_def : w_n = F[idx]! ++ List.replicate (l - F[idx]!.length) false := by
          have h2 := congr_arg Prod.fst hw_n_eq
          exact h2.symm
        have h_free'_def : free' = F.take idx ++
            ((List.range (l - F[idx]!.length)).map
              (fun m => F[idx]! ++ List.replicate m false ++ [true])).reverse ++
            F.drop (idx + 1) := by
          have h2 := congr_arg Prod.snd hw_n_eq
          exact h2.symm
        rcases List.mem_iff_getElem.mp hw_mem with ⟨k, hk_lt, rfl⟩
        rcases lt_trichotomy k idx with hk_lt_idx | rfl | hk_gt_idx
        · right
          refine ⟨F[k], ?_, hw_pre⟩
          rw [h_free'_def]
          simp only [List.mem_append]
          left; left
          rw [List.mem_iff_getElem]
          have h_len_k : k < (F.take idx).length := by
            rw [List.length_take]
            exact Nat.lt_min.mpr ⟨hk_lt_idx, hk_lt⟩
          have h_get : (F.take idx)[k] = F[k] := by rw [List.getElem_take]
          exact ⟨k, h_len_k, h_get⟩
        · obtain ⟨s, hs⟩ := hw_pre
          have h_wn_u : u = F[k]! ++ s := by
            have : F[k] = F[k]! := (getElem!_pos F k hk_lt).symm
            rw [← this, hs]
          let diff := l - F[k]!.length
          rcases replicate_false_trichotomy s diff with h_s1 | h_s2 | ⟨m, hm_lt, hm_pre⟩
          · left
            refine ⟨n, Nat.lt_succ_self n, w_n, h_allocFun_n, Or.inl ?_⟩
            rw [h_wn_def, h_wn_u]
            obtain ⟨t, ht⟩ := h_s1
            refine ⟨t, ?_⟩
            rw [List.append_assoc, ht]
          · left
            refine ⟨n, Nat.lt_succ_self n, w_n, h_allocFun_n, Or.inr ?_⟩
            rw [h_wn_def, h_wn_u]
            obtain ⟨t, ht⟩ := h_s2
            refine ⟨t, ?_⟩
            rw [List.append_assoc, ht]
          · right
            refine ⟨F[k]! ++ List.replicate m false ++ [true], ?_, ?_⟩
            · rw [h_free'_def]
              simp only [List.mem_append, List.mem_reverse, List.mem_map, List.mem_range]
              left; right
              exact ⟨m, hm_lt, rfl⟩
            · rw [h_wn_u]
              obtain ⟨t, ht⟩ := hm_pre
              refine ⟨t, ?_⟩
              have h_app : F[k]! ++ List.replicate m false ++ [true] ++ t =
                  F[k]! ++ (List.replicate m false ++ [true] ++ t) := by simp
              rw [h_app, ht]
        · right
          refine ⟨F[k], ?_, hw_pre⟩
          rw [h_free'_def]
          simp only [List.mem_append]
          right
          have hk_drop : k - (idx + 1) < (F.drop (idx + 1)).length := by
            rw [List.length_drop]
            omega
          have h_get_drop : (F.drop (idx + 1))[k - (idx + 1)] = F[k] := by
            rw [List.getElem_drop]
            congr 1; omega
          rw [← h_get_drop]
          exact List.getElem_mem hk_drop

/-- Entries of the rebuilt free list before the replaced position are the old ones. -/
lemma getElem_free'_part1 {F : List BitString} {idx : ℕ} {B : List BitString}
    (hA : idx ≤ F.length) (k : ℕ) (hk : k < idx)
    (hk' : k < (F.take idx ++ B ++ F.drop (idx + 1)).length) :
    (F.take idx ++ B ++ F.drop (idx + 1))[k] = F[k]'(by omega) := by
  have h1 : k < (F.take idx ++ B).length := by
    rw [List.length_append, List.length_take, Nat.min_eq_left hA]; omega
  have h2 : (F.take idx ++ B ++ F.drop (idx + 1))[k] = (F.take idx ++ B)[k] :=
    List.getElem_append_left h1
  have h3 : k < (F.take idx).length := by
    rw [List.length_take, Nat.min_eq_left hA]; exact hk
  have h4 : (F.take idx ++ B)[k] = (F.take idx)[k] := List.getElem_append_left h3
  have h5 : (F.take idx)[k] = F[k] := List.getElem_take
  exact h2.trans (h4.trans h5)

/-- Entries of the rebuilt free list inside the replaced block are the new ones. -/
lemma getElem_free'_part2 {F : List BitString} {idx diff : ℕ} {B : List BitString}
    (hA : idx ≤ F.length) (hB : B.length = diff) (k : ℕ) (hk1 : idx ≤ k) (hk2 : k < idx + diff)
    (hk' : k < (F.take idx ++ B ++ F.drop (idx + 1)).length) :
    (F.take idx ++ B ++ F.drop (idx + 1))[k] = B[k - idx]'(by omega) := by
  have h1 : k < (F.take idx ++ B).length := by
    rw [List.length_append, List.length_take, Nat.min_eq_left hA, hB]; omega
  have h2 : (F.take idx ++ B ++ F.drop (idx + 1))[k] = (F.take idx ++ B)[k] :=
    List.getElem_append_left h1
  have h3 : (F.take idx).length ≤ k := by
    rw [List.length_take, Nat.min_eq_left hA]; exact hk1
  rw [h2, List.getElem_append_right h3]
  congr 1
  rw [List.length_take, Nat.min_eq_left hA]

/-- The block of new free nodes that replaces a node `v` when a codeword of length `l` is
allocated from it: the right siblings along the leftmost path out of `v`, listed by decreasing
length. -/
def splitNodeBlock (v : BitString) (l : ℕ) : List BitString :=
  ((List.range (l - v.length)).map (fun m => v ++ List.replicate m false ++ [true])).reverse

/-- The replacement block of a node `v` for a request of length `l` has `l - v.length`
entries. -/
lemma splitNodeBlock_length (v : BitString) (l : ℕ) :
    (splitNodeBlock v l).length = l - v.length := by
  simp [splitNodeBlock]

/-- The `m`-th node of the replacement block is `v` followed by `l - v.length - 1 - m` zeros
and a closing one. -/
lemma splitNodeBlock_getElem (v : BitString) (l m : ℕ)
    (hm : m < (splitNodeBlock v l).length) :
    (splitNodeBlock v l)[m] =
      v ++ List.replicate (l - v.length - 1 - m) false ++ [true] := by
  simp only [splitNodeBlock, List.getElem_reverse, List.getElem_map, List.getElem_range,
    List.length_map, List.length_range]

/-- The `m`-th node of the replacement block of a node of length at most `l` has length
`l - m`. -/
lemma splitNodeBlock_getElem_length (v : BitString) (l m : ℕ) (hv : v.length ≤ l)
    (hm : m < (splitNodeBlock v l).length) :
    ((splitNodeBlock v l)[m]).length = l - m := by
  rw [splitNodeBlock_getElem v l m hm]
  rw [splitNodeBlock_length] at hm
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  omega

/-- Padded to length `L`, the `m`-th node of the replacement block has the value of `v` plus a
single bit of weight `2 ^ (L - (l - m))`. -/
lemma leftValue_splitNodeBlock_pad (v : BitString) (l m L : ℕ) (hv : v.length ≤ l)
    (hL : l - m ≤ L) (hm : m < (splitNodeBlock v l).length) :
    leftValue ((splitNodeBlock v l)[m] ++
        List.replicate (L - ((splitNodeBlock v l)[m]).length) false) =
      leftValue v * 2 ^ (L - v.length) + 2 ^ (L - (l - m)) := by
  have hlen := splitNodeBlock_getElem_length v l m hv hm
  have hget := splitNodeBlock_getElem v l m hm
  rw [splitNodeBlock_length] at hm
  rw [hlen, hget]
  exact leftValue_newNode_pad v l m L hv hL hm

/-- Inside the replacement block the padded values increase with the index. -/
lemma leftValue_splitNodeBlock_pad_mono (v : BitString) (l m m' L : ℕ) (hv : v.length ≤ l)
    (hm : m < (splitNodeBlock v l).length) (hm' : m' < (splitNodeBlock v l).length)
    (hmm : m ≤ m') (hL : l - m ≤ L) :
    leftValue ((splitNodeBlock v l)[m] ++
        List.replicate (L - ((splitNodeBlock v l)[m]).length) false) ≤
      leftValue ((splitNodeBlock v l)[m'] ++
        List.replicate (L - ((splitNodeBlock v l)[m']).length) false) := by
  rw [leftValue_splitNodeBlock_pad v l m L hv hL hm,
    leftValue_splitNodeBlock_pad v l m' L hv (by omega) hm']
  exact Nat.add_le_add_left (Nat.pow_le_pow_right (by omega) (by omega)) _

/-- The node that is split lies below every node of its replacement block, after padding to a
common length. -/
lemma leftValue_pad_le_splitNodeBlock_pad (v : BitString) (l m L : ℕ) (hv : v.length ≤ l)
    (hL : l - m ≤ L) (hm : m < (splitNodeBlock v l).length) :
    leftValue (v ++ List.replicate (L - v.length) false) ≤
      leftValue ((splitNodeBlock v l)[m] ++
        List.replicate (L - ((splitNodeBlock v l)[m]).length) false) := by
  rw [leftValue_splitNodeBlock_pad v l m L hv hL hm, leftValue_append,
    leftValue_replicate_false, add_zero, List.length_replicate]
  exact Nat.le_add_right _ _

/-- Every node of the replacement block of `v` stays below a string `u` that is incomparable
with `v` and already lies above `v` after padding. -/
lemma leftValue_splitNodeBlock_pad_le_of_prefixFree (v u : BitString) (l m L : ℕ)
    (hv : v.length ≤ l) (hu : u.length ≤ L) (hpf : ¬ v <+: u) (hpu : ¬ u <+: v)
    (hm : m < (splitNodeBlock v l).length) (hL : l - m ≤ L)
    (h_le : leftValue (v ++ List.replicate (L - v.length) false) ≤
      leftValue (u ++ List.replicate (L - u.length) false)) :
    leftValue ((splitNodeBlock v l)[m] ++
        List.replicate (L - ((splitNodeBlock v l)[m]).length) false) ≤
      leftValue (u ++ List.replicate (L - u.length) false) := by
  have hmlt : m < l - v.length := by rwa [splitNodeBlock_length] at hm
  have hvL : v.length ≤ L := by omega
  have h2 := leftValue_ge_of_prefixFree_and_le v u L hvL hu hpf hpu h_le
  rw [leftValue_splitNodeBlock_pad v l m L hv hL hm]
  calc leftValue v * 2 ^ (L - v.length) + 2 ^ (L - (l - m))
      ≤ leftValue v * 2 ^ (L - v.length) + 2 ^ (L - v.length) :=
        Nat.add_le_add_left (Nat.pow_le_pow_right (by omega) (by omega)) _
    _ = (leftValue v + 1) * 2 ^ (L - v.length) := by ring
    _ ≤ leftValue (u ++ List.replicate (L - u.length) false) := h2

/-- Two distinct entries of the allocator's free list are incomparable: neither is a prefix of
the other. -/
lemma allocatorState_getElem_incomparable (req : ℕ → Option (BitString × ℕ)) (n : ℕ)
    (F : List BitString) (hF : KraftChaitin.allocatorState req n = some F)
    (a b : ℕ) (hab : a < b) (hb : b < F.length) :
    ¬ (F[a]'(by omega)) <+: F[b] ∧ ¬ F[b] <+: (F[a]'(by omega)) := by
  have ha : a < F.length := by omega
  have hpf := KraftChaitin.allocatorState_prefixFree req n F hF
  have ha_mem : F[a] ∈ F.toFinset := List.mem_toFinset.mpr (List.getElem_mem ha)
  have hb_mem : F[b] ∈ F.toFinset := List.mem_toFinset.mpr (List.getElem_mem hb)
  have h_ne : F[a] ≠ F[b] := by
    intro h_eq
    have h_desc : KraftChaitin.DescLengths F :=
      KraftChaitin.allocatorState_descLengths req n F hF
    have h_lt := descLengths_getElem_length_lt h_desc hab hb
    rw [h_eq] at h_lt
    exact lt_irrefl _ h_lt
  exact ⟨fun h => h_ne (hpf ha_mem hb_mem h), fun h => h_ne (hpf hb_mem ha_mem h).symm⟩

end Kolmogorov
