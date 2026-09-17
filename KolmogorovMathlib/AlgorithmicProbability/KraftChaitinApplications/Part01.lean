/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
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
import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs
import KolmogorovMathlib.MonotoneComplexity.SimpleTreeApproximation

/-!
# Applications of the Kraft-Chaitin theorem, part 1

The leftmost-allocation form of the Kraft-Chaitin theorem
(`kraftChaitin_leftmost_allocation`), and its use to compute the a priori probability of a
pair from the a priori probabilities of its components: the sum and the maximum of two
a priori measures are again a priori measures up to a constant factor
(`aprioriMeasure_pair_sum_eq`, `aprioriMeasure_pair_max_eq`).

SUV Theorem 43 and Exercises 96-97, pp. 105-110.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-- **Exercise 100.** The Kraft–Chaitin allocator always uses the leftmost
properly aligned interval of the requested length that does not overlap with the
previously allocated ones. -/
theorem kraftChaitin_leftmost_allocation
    (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (w : BitString)
    (hw : KraftChaitin.allocFun req n = some w) :
    (∀ u : BitString, u.length = w.length →
        (∀ i < n, ∀ v : BitString, KraftChaitin.allocFun req i = some v →
          ¬ (u <+: v ∨ v <+: u)) →
        leftValue w ≤ leftValue u) := by
  intro u hu_len hu_disj
  have h_state : ∃ free, KraftChaitin.allocatorState req n = some free := by
    dsimp [KraftChaitin.allocFun] at hw
    rcases hF : KraftChaitin.allocatorState req n with _ | free
    · rw [hF] at hw; contradiction
    · exact ⟨free, rfl⟩
  obtain ⟨free, hfree⟩ := h_state
  rcases exists_alloc_overlap_or_free_prefix req n free hfree u with
      ⟨i, hi_lt, v, hv, hov⟩ | ⟨fk, hfk_mem, hfk_pre⟩
  · exfalso
    exact hu_disj i hi_lt v hv hov
  · rcases List.mem_iff_getElem.mp hfk_mem with ⟨k, hk_lt, rfl⟩
    have hw_copy := hw
    dsimp [KraftChaitin.allocFun] at hw
    rw [hfree] at hw
    dsimp only at hw
    rcases hreq : req n with _ | ⟨o, l⟩
    · rw [hreq] at hw; contradiction
    rw [hreq] at hw
    dsimp only at hw
    rcases halloc : KraftChaitin.allocateOne free l with _ | ⟨allocated, free'⟩
    · rw [halloc] at hw; contradiction
    rw [halloc] at hw
    injection hw with hw_eq; subst hw_eq
    have h_fk_len : free[k].length ≤ allocated.length := by
      have h1 : free[k].length ≤ u.length := List.IsPrefix.length_le hfk_pre
      omega
    have h_left1 : leftValue (free[k] ++
        List.replicate (allocated.length - free[k].length) false) ≤ leftValue u :=
      leftValue_le_of_prefix free[k] u allocated.length hfk_pre hu_len
    unfold KraftChaitin.allocateOne at halloc
    rcases hfind : free.findIdx? (fun v => v.length ≤ l) with _ | idx
    · rw [hfind] at halloc; contradiction
    rw [hfind] at halloc
    injection halloc with hw_def
    have hw_val : allocated = free[idx]! ++ List.replicate (l - free[idx]!.length) false := by
      have h1 := congr_arg Prod.fst hw_def
      exact h1.symm
    have h_idx_spec := List.findIdx?_eq_some_iff_getElem.mp hfind
    obtain ⟨h_idx_lt, h_idx_len_dec, h_idx_min⟩ := h_idx_spec
    have h_idx_len : free[idx].length ≤ l := of_decide_eq_true h_idx_len_dec
    have h_l_eq : l = allocated.length := by
      rw [hw_val, List.length_append, List.length_replicate]
      have : free[idx]! = free[idx] := getElem!_pos free idx h_idx_lt
      rw [this]
      omega
    have h_idx_le_k : idx ≤ k := by
      by_contra h_lt
      push Not at h_lt
      have h_k_not_len := h_idx_min k h_lt
      have h_fk_len' : free[k].length ≤ l := by omega
      have h_dec : decide (free[k].length ≤ l) = true := decide_eq_true h_fk_len'
      exact h_k_not_len h_dec
    have h_left2 : leftValue (free[idx] ++ List.replicate (l - free[idx].length) false) ≤
        leftValue (free[k] ++ List.replicate (l - free[k].length) false) := by
      exact leftValue_le_of_state req n free hfree idx k h_idx_lt hk_lt h_idx_le_k l h_idx_len
        (by omega)
    have h_idx_eq : free[idx]! = free[idx] := getElem!_pos free idx h_idx_lt
    rw [hw_val, h_idx_eq]
    have h_left1' : leftValue (free[k] ++ List.replicate (l - free[k].length) false) ≤
        leftValue u := by
      rw [h_l_eq]
      exact h_left1
    exact h_left2.trans h_left1'

namespace SemimeasureEmbedding

/-- The semimeasure `m` transported to pair codes: the mass of `pairCode x []` is `m x`, and every
other string has mass `0`. -/
def embedFirst (m : BitString → ℝ≥0∞) (z : BitString) : ℝ≥0∞ :=
  if z = pairCode (decodeFirst z) [] then m (decodeFirst z) else 0

/-- The transported semimeasure gives `pairCode x []` exactly the mass `m x`. -/
lemma embedFirst_pairCode (m : BitString → ℝ≥0∞) (x : BitString) :
    embedFirst m (pairCode x []) = m x := by
  unfold embedFirst
  rw [decodeFirst_pairCode]
  simp

/-- Transporting a semimeasure to pair codes leaves a semimeasure. -/
lemma isSemimeasure_embedFirst {m : BitString → ℝ≥0∞} (hm : IsSemimeasure m) :
    IsSemimeasure (embedFirst m) := by
  change (∑' z : BitString, embedFirst m z) ≤ 1
  have h_support : Function.support (embedFirst m) ⊆ Set.range (fun x => pairCode x []) := by
    intro z hz
    by_contra hc
    have h_if : z ≠ pairCode (decodeFirst z) [] := by
      intro h_eq
      apply hc
      exact ⟨decodeFirst z, h_eq.symm⟩
    unfold embedFirst at hz
    exact hz (if_neg h_if)
  have h_inj : Function.Injective (fun x : BitString => pairCode x []) := by
    intro x1 x2 h
    have h_pair : pairCode x1 [] = pairCode x2 [] := h
    have h_prod := @pairCode_injective (x1, []) (x2, []) h_pair
    exact (Prod.ext_iff.mp h_prod).1
  have h_sum : (∑' z : BitString, embedFirst m z) = ∑' x : BitString, m x := by
    rw [← tsum_subtype_eq_of_support_subset h_support]
    have h_eq : (fun (z : {z : BitString // z ∈ Set.range (fun x => pairCode x [])}) =>
          embedFirst m z.1)
        = (fun z => m (decodeFirst z.1)) := by
      ext ⟨z, x, hx⟩
      unfold embedFirst
      have h_eq : z = pairCode (decodeFirst z) [] := by
        subst hx
        rw [decodeFirst_pairCode]
      rw [if_pos h_eq]
    rw [h_eq]
    have h_equiv := (Equiv.ofInjective (fun x => pairCode x []) h_inj).tsum_eq
      (fun z => m (decodeFirst z))
    rw [← h_equiv]
    congr 1
    ext x
    have h_val : ((Equiv.ofInjective (fun x => pairCode x []) h_inj) x : BitString)
        = pairCode x [] := rfl
    rw [h_val, decodeFirst_pairCode]
  rw [h_sum]
  exact hm

/-- Transporting a lower semicomputable function to pair codes leaves it lower semicomputable. -/
lemma isLSC_embedFirst {m : BitString → ℝ≥0∞} (hm : IsLSC (fun x _ => m x)) :
    IsLSC (fun z _ => embedFirst m z) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hm
  set approx_embed : ℕ → BitString → BitString → ℕ := fun s z ctx =>
    if z = pairCode (decodeFirst z) [] then approx s (decodeFirst z) ctx else 0
  refine ⟨approx_embed, ?_, ?_, ?_⟩
  · intro s z ctx
    unfold approx_embed
    split_ifs with h
    · exact hmono s (decodeFirst z) ctx
    · simp [dyadicValue]
  · intro z ctx
    unfold approx_embed
    split_ifs with h
    · change ⨆ s, dyadicValue (approx s (decodeFirst z) ctx) s = embedFirst m z
      rw [hsup (decodeFirst z) ctx]
      unfold embedFirst
      rw [if_pos h]
    · simp [dyadicValue, embedFirst, h]
  · unfold approx_embed
    have h_dec : Computable decodeFirst := decodeFirst_computable
    have h_pair : Computable (fun p : BitString × BitString => pairCode p.1 p.2) :=
      pairCode_computable
    have h_eq : Computable (fun p : BitString × BitString => decide (p.1 = p.2)) :=
      bitstring_eq_decide_computable
    have h_check : Computable (fun z : BitString => decide (z = pairCode (decodeFirst z) [])) :=
      h_eq.comp (Computable.id.pair (h_pair.comp (h_dec.pair (Computable.const []))))
    have h_cond : Computable (fun p : ℕ × BitString × BitString =>
        decide (p.2.1 = pairCode (decodeFirst p.2.1) [])) :=
      h_check.comp (Computable.fst.comp Computable.snd)
    have h_val : Computable (fun p : ℕ × BitString × BitString =>
        approx p.1 (decodeFirst p.2.1) p.2.2) :=
      hcomp.comp (Computable.fst.pair
        ((h_dec.comp (Computable.fst.comp Computable.snd)).pair
          (Computable.snd.comp Computable.snd)))
    exact (Computable.cond h_cond h_val (Computable.const 0)).of_eq (fun p => by
      dsimp [cond]
      split_ifs with h
      · rw [decide_eq_true h]
      · rw [decide_eq_false h])

/-- Transporting a lower semicomputable semimeasure to pair codes leaves one. -/
lemma isLowerSemicomputableSemimeasure_embedFirst {m : BitString → ℝ≥0∞}
    (hm : IsLowerSemicomputableSemimeasure m) :
    IsLowerSemicomputableSemimeasure (embedFirst m) :=
  ⟨isSemimeasure_embedFirst hm.1, isLSC_embedFirst hm.2⟩

/-- A universal semimeasure gives `pairCode x []` at least a fixed fraction of the mass of `x`. -/
lemma lower_bound_pair_code {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m) :
    ∃ c₁ : ℝ≥0∞, 0 < c₁ ∧ ∀ x : BitString, c₁ * m x ≤ m (pairCode x []) := by
  obtain ⟨c₁, hc₁_pos, hc₁_dom⟩ :=
    hm.2 (embedFirst m) (isLowerSemicomputableSemimeasure_embedFirst hm.1)
  refine ⟨c₁, hc₁_pos, fun x => ?_⟩
  have h := hc₁_dom (pairCode x [])
  rw [embedFirst_pairCode] at h
  exact h

/-- The list of all bitstrings of length at most `s`. -/
def boundedList (s : ℕ) : List BitString :=
  (List.range (s + 1)).flatMap allStrings

/-- The strings of length at most `s + 1` are those of length at most `s` followed by those of
length exactly `s + 1`. -/
lemma boundedList_succ (s : ℕ) :
    boundedList (s + 1) = boundedList s ++ allStrings (s + 1) := by
  unfold boundedList
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Each of these lists is a prefix of the next one. -/
lemma boundedList_prefix (s : ℕ) :
    boundedList s <+: boundedList (s + 1) := by
  rw [boundedList_succ]
  exact List.prefix_append _ _

/-- The first marginal of `m` along pair codes: the total mass of `pairCode x y` over all `y`. -/
noncomputable def sumPair (m : BitString → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  ∑' y : BitString, m (pairCode x y)

/-- The first marginal of a semimeasure is a semimeasure. -/
lemma isSemimeasure_sumPair {m : BitString → ℝ≥0∞} (hm : IsSemimeasure m) :
    IsSemimeasure (sumPair m) := by
  change (∑' x : BitString, ∑' y : BitString, m (pairCode x y)) ≤ 1
  have h_prod : (∑' x : BitString, ∑' y : BitString, m (pairCode x y))
      = ∑' p : BitString × BitString, m (pairCode p.1 p.2) := ENNReal.tsum_prod.symm
  rw [h_prod]
  refine le_trans ?_ hm
  exact ENNReal.tsum_comp_le_tsum_of_injective pairCode_injective m

/-- A string belongs to `boundedList s` exactly when its length is at most `s`. -/
lemma mem_boundedList (s : ℕ) (y : BitString) :
    y ∈ boundedList s ↔ y.length ≤ s := by
  unfold boundedList
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨l, hl, hyl⟩
    rw [List.mem_range] at hl
    rw [mem_allStrings] at hyl
    omega
  · intro hy
    refine ⟨y.length, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · rw [mem_allStrings]

/-- `boundedList s` lists each string once. -/
lemma boundedList_nodup (s : ℕ) : (boundedList s).Nodup := by
  induction s with
  | zero =>
    unfold boundedList
    simp [allStrings]
  | succ s ih =>
    rw [boundedList_succ]
    refine List.Nodup.append ih (allStrings_nodup (s + 1)) ?_
    intro y hy1 hy2
    rw [mem_boundedList] at hy1
    rw [mem_allStrings] at hy2
    omega

/-- The sum of `f` over a duplicate-free list is its sum over the corresponding finite set. -/
lemma list_sum_eq_finset_sum {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup)
    (f : α → ℝ≥0∞) :
    ((l.map f).sum : ℝ≥0∞) = ∑ y ∈ l.toFinset, f y := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    have ha : a ∉ l.toFinset := by
      intro h
      exact hl.1 (List.mem_toFinset.mp h)
    rw [Finset.sum_insert ha, ih hl.2]

/-- The sum of a list of naturals, in the fold form the computability proofs use. -/
def natListSum (l : List ℕ) : ℕ := l.foldr (· + ·) 0

/-- The fold form agrees with `List.sum`. -/
lemma natListSum_eq_sum (l : List ℕ) : natListSum l = l.sum := by
  unfold natListSum
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.foldr, ih]

/-- Listing the strings of length at most `s` is primitive recursive in `s`. -/
lemma boundedList_primrec : Primrec boundedList := by
  have h_range : Primrec (fun s : ℕ => List.range (s + 1)) :=
    Primrec.list_range.comp Primrec.succ
  have h_flatMap : Primrec (fun s : ℕ => (List.range (s + 1)).flatMap allStrings) :=
    Primrec.list_flatMap h_range
      ((CodedFiniteDistribution.allStrings_primrec.comp Primrec.snd).to₂)
  exact h_flatMap

/-- Listing the strings of length at most `s` is computable in `s`. -/
lemma boundedList_computable : Computable boundedList := boundedList_primrec.to_comp

/-- The stage-`s` numerator of the marginal: the sum of the stage numerators of `pairCode x y`
over the strings `y` of length at most `s`. -/
def approxSum (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x ctx : BitString) : ℕ :=
  natListSum ((boundedList s).map (fun y => approx s (pairCode x y) ctx))

/-- The marginal numerator written as the sum over `boundedList s`. -/
lemma approx_sum_eq (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x ctx : BitString) :
    approxSum approx s x ctx = ((boundedList s).map (fun y => approx s (pairCode x y) ctx)).sum :=
  natListSum_eq_sum _

/-- The dyadic value of the marginal numerator is the sum of the dyadic values of its terms. -/
lemma dyadicValue_boundedList_sum (approx : ℕ → BitString → BitString → ℕ)
    (s : ℕ) (x ctx : BitString) :
    dyadicValue (approxSum approx s x ctx) s =
      ∑ y ∈ (boundedList s).toFinset, dyadicValue (approx s (pairCode x y) ctx) s := by
  unfold dyadicValue
  rw [approx_sum_eq, Nat.cast_list_sum]
  have h_map : (((boundedList s).map (fun y => approx s (pairCode x y) ctx)).map
        (Nat.cast : ℕ → ℝ≥0∞)) =
      (boundedList s).map (fun y => (approx s (pairCode x y) ctx : ℝ≥0∞)) := by
    rw [List.map_map]
    rfl
  rw [h_map]
  rw [list_sum_eq_finset_sum (boundedList s) (boundedList_nodup s)
    (fun y => (approx s (pairCode x y) ctx : ℝ≥0∞))]
  rw [div_eq_mul_inv, Finset.sum_mul]
  rfl

/-- A finite sum of suprema of monotone sequences is the supremum of the sums. -/
lemma finset_sum_iSup_monotone {α : Type*} (F : Finset α) (f : α → ℕ → ℝ≥0∞)
    (hf : ∀ a ∈ F, Monotone (f a)) :
    (∑ a ∈ F, ⨆ s, f a s) = ⨆ s, ∑ a ∈ F, f a s := by
  have h_lim : Filter.Tendsto (fun s => ∑ a ∈ F, f a s) Filter.atTop
      (nhds (∑ a ∈ F, ⨆ s, f a s)) :=
    tendsto_finsetSum _ (fun a ha => tendsto_atTop_iSup (hf a ha))
  have h_mon : Monotone (fun s => ∑ a ∈ F, f a s) := fun s1 s2 hle =>
    Finset.sum_le_sum (fun a ha => hf a ha hle)
  exact (tendsto_nhds_unique (tendsto_atTop_iSup h_mon) h_lim).symm

/-- A sum over a list rewritten as a sum over the range of its indices. -/
lemma list_sum_eq_range_getElem? (l : List BitString) (f : BitString → ℕ) :
    (l.map f).sum = ∑ i ∈ Finset.range l.length, match l[i]? with
      | some y => f y
      | none => 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons]
    have h := @Finset.sum_range_succ' ℕ _
      (fun i => match (a :: l)[i]? with | some y => f y | none => 0) l.length
    have h0 : (match (a :: l)[0]? with | some y => f y | none => 0) = f a := rfl
    have hsucc : (fun i => match (a :: l)[i + 1]? with | some y => f y | none => 0) =
        (fun i => match l[i]? with | some y => f y | none => 0) :=
      funext (fun i => by rw [List.getElem?_cons_succ])
    rw [h0, hsucc] at h
    rw [h, add_comm]

/-- The `i`-th term of the marginal numerator, indexed by position in `boundedList s`. -/
def approxSumRangeTerm (approx : ℕ → BitString → BitString → ℕ)
    (p : ℕ × BitString × BitString) (i : ℕ) : ℕ :=
  ((boundedList p.1)[i]?.map (fun y => approx p.1 (pairCode p.2.1 y) p.2.2)).getD 0

/-- The indexed term is the stage numerator of the `i`-th string of `boundedList s`, and `0`
beyond the end of that list. -/
lemma approx_sum_range_term_eq (approx : ℕ → BitString → BitString → ℕ)
    (p : ℕ × BitString × BitString) (i : ℕ) :
    approxSumRangeTerm approx p i =
      match (boundedList p.1)[i]? with
      | some y => approx p.1 (pairCode p.2.1 y) p.2.2
      | none => 0 := by
  unfold approxSumRangeTerm
  cases (boundedList p.1)[i]? <;> rfl

/-- The marginal numerator is the sum of its indexed terms over a range. -/
lemma approx_sum_eq_range_sum (approx : ℕ → BitString → BitString → ℕ)
    (p : ℕ × BitString × BitString) :
    approxSum approx p.1 p.2.1 p.2.2 =
      ∑ i ∈ Finset.range (boundedList p.1).length, approxSumRangeTerm approx p i := by
  dsimp [approxSum]
  rw [natListSum_eq_sum]
  have h := list_sum_eq_range_getElem? (boundedList p.1)
    (fun y => approx p.1 (pairCode p.2.1 y) p.2.2)
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (approx_sum_range_term_eq approx p i).symm

/-- The indexed term is computable when the underlying stage approximation is. -/
lemma approx_sum_range_term_computable {approx : ℕ → BitString → BitString → ℕ}
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable₂ (approxSumRangeTerm approx) := by
  have h1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => (boundedList q.1.1)[q.2]?) :=
    Computable.list_getElem?.comp
      (boundedList_computable.comp (Computable.fst.comp Computable.fst))
      Computable.snd
  have h2 : Computable₂ (fun (q : (ℕ × BitString × BitString) × ℕ) (y : BitString) =>
      approx q.1.1 (pairCode q.1.2.1 y) q.1.2.2) := by
    have h_s : Computable (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString => r.1.1.1) :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have h_x : Computable (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString => r.1.1.2.1) :=
      (Computable.fst.comp Computable.snd).comp (Computable.fst.comp Computable.fst)
    have h_ctx : Computable (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString => r.1.1.2.2) :=
      (Computable.snd.comp Computable.snd).comp (Computable.fst.comp Computable.fst)
    have h_pair : Computable (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString =>
        pairCode r.1.1.2.1 r.2) :=
      (show Computable₂ (fun x y : BitString => pairCode x y) from pairCode_computable).comp
        h_x Computable.snd
    have h_arg : Computable (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString =>
        (r.1.1.1, pairCode r.1.1.2.1 r.2, r.1.1.2.2)) :=
      h_s.pair (h_pair.pair h_ctx)
    exact (hcomp.comp h_arg).to₂
  have h3 : Computable (fun q : (ℕ × BitString × BitString) × ℕ =>
      ((boundedList q.1.1)[q.2]?.map (fun y => approx q.1.1 (pairCode q.1.2.1 y) q.1.2.2))) :=
    Computable.option_map h1 h2
  have h4 : Computable (fun q : (ℕ × BitString × BitString) × ℕ =>
      ((boundedList q.1.1)[q.2]?.map
        (fun y => approx q.1.1 (pairCode q.1.2.1 y) q.1.2.2)).getD 0) :=
    Computable.option_getD h3 (Computable.const 0)
  exact h4.to₂

/-- The marginal numerator is computable when the underlying stage approximation is. -/
lemma approx_sum_computable {approx : ℕ → BitString → BitString → ℕ}
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString × BitString => approxSum approx p.1 p.2.1 p.2.2) := by
  have h_bound : Computable (fun p : ℕ × BitString × BitString => (boundedList p.1).length) :=
    Computable.list_length.comp (boundedList_computable.comp Computable.fst)
  have h_sum := computable_range_sum (approxSumRangeTerm approx)
    (approx_sum_range_term_computable hcomp) (fun p => (boundedList p.1).length) h_bound
  exact h_sum.of_eq (fun p => (approx_sum_eq_range_sum approx p).symm)

/-- The first marginal of a lower semicomputable function is lower semicomputable. -/
lemma isLSC_sumPair {m : BitString → ℝ≥0∞} (hm : IsLSC (fun x _ => m x)) :
    IsLSC (fun x _ => sumPair m x) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hm
  refine ⟨approxSum approx, ?_, ?_, approx_sum_computable hcomp⟩
  · intro s x ctx
    rw [dyadicValue_boundedList_sum, dyadicValue_boundedList_sum]
    have h1 : (∑ y ∈ (boundedList s).toFinset, dyadicValue (approx s (pairCode x y) ctx) s) ≤
        ∑ y ∈ (boundedList s).toFinset,
          dyadicValue (approx (s + 1) (pairCode x y) ctx) (s + 1) := by
      refine Finset.sum_le_sum (fun y _ => hmono s (pairCode x y) ctx)
    have h2 : (∑ y ∈ (boundedList s).toFinset,
          dyadicValue (approx (s + 1) (pairCode x y) ctx) (s + 1))
        ≤ ∑ y ∈ (boundedList (s + 1)).toFinset,
          dyadicValue (approx (s + 1) (pairCode x y) ctx) (s + 1) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => zero_le)
      intro y hy
      rw [List.mem_toFinset, mem_boundedList] at hy ⊢
      omega
    exact le_trans h1 h2
  · intro x ctx
    have h_dyadic_sum : ∀ s, dyadicValue (approxSum approx s x ctx) s
        = ∑ y ∈ (boundedList s).toFinset, dyadicValue (approx s (pairCode x y) ctx) s :=
      fun s => dyadicValue_boundedList_sum approx s x ctx
    simp_rw [h_dyadic_sum]
    apply le_antisymm
    · apply iSup_le
      intro s
      calc ∑ y ∈ (boundedList s).toFinset, dyadicValue (approx s (pairCode x y) ctx) s
          ≤ ∑ y ∈ (boundedList s).toFinset, m (pairCode x y) := by
            refine Finset.sum_le_sum (fun y _ => ?_)
            have := le_iSup (fun s => dyadicValue (approx s (pairCode x y) ctx) s) s
            rwa [hsup (pairCode x y) ctx] at this
        _ ≤ ∑' y : BitString, m (pairCode x y) := ENNReal.sum_le_tsum _
    · rw [sumPair, ENNReal.tsum_eq_iSup_sum]
      apply iSup_le
      intro F
      set S := F.sup List.length
      have hFS : ∀ y ∈ F, y.length ≤ S := fun y hy => Finset.le_sup hy
      have hF_sub : F ⊆ (boundedList S).toFinset := by
        intro y hy
        rw [List.mem_toFinset, mem_boundedList]
        exact hFS y hy
      calc ∑ y ∈ F, m (pairCode x y)
          = ∑ y ∈ F, ⨆ s, dyadicValue (approx s (pairCode x y) ctx) s := by
            congr 1; ext y; exact (hsup (pairCode x y) ctx).symm
        _ = ⨆ s, ∑ y ∈ F, dyadicValue (approx s (pairCode x y) ctx) s := by
            refine finset_sum_iSup_monotone F _ (fun y _ => ?_)
            exact monotone_nat_of_le_succ (fun k => hmono k (pairCode x y) ctx)
        _ ≤ ⨆ s, ∑ y ∈ (boundedList (max s S)).toFinset,
              dyadicValue (approx (max s S) (pairCode x y) ctx) (max s S) := by
            refine iSup_mono (fun s => ?_)
            have hF_sub' : F ⊆ (boundedList (max s S)).toFinset := by
              refine hF_sub.trans ?_
              intro y hy
              rw [List.mem_toFinset, mem_boundedList] at hy ⊢
              omega
            calc ∑ y ∈ F, dyadicValue (approx s (pairCode x y) ctx) s
                ≤ ∑ y ∈ F, dyadicValue (approx (max s S) (pairCode x y) ctx) (max s S) := by
                  refine Finset.sum_le_sum (fun y _ => monotone_nat_of_le_succ
                    (fun k => hmono k (pairCode x y) ctx) (le_max_left s S))
              _ ≤ ∑ y ∈ (boundedList (max s S)).toFinset,
                    dyadicValue (approx (max s S) (pairCode x y) ctx) (max s S) := by
                  refine Finset.sum_le_sum_of_subset_of_nonneg hF_sub' (fun _ _ _ => zero_le)
        _ ≤ ⨆ s, ∑ y ∈ (boundedList s).toFinset,
              dyadicValue (approx s (pairCode x y) ctx) s := by
            refine iSup_le (fun s => ?_)
            exact le_iSup (fun k => ∑ y ∈ (boundedList k).toFinset,
              dyadicValue (approx k (pairCode x y) ctx) k) (max s S)

/-- The first marginal of a lower semicomputable semimeasure is one. -/
lemma isLowerSemicomputableSemimeasure_sumPair {m : BitString → ℝ≥0∞}
    (hm : IsLowerSemicomputableSemimeasure m) :
    IsLowerSemicomputableSemimeasure (sumPair m) :=
  ⟨isSemimeasure_sumPair hm.1, isLSC_sumPair hm.2⟩

/-- For a universal semimeasure the first marginal is bounded by a constant multiple of the
semimeasure itself. -/
lemma upper_bound_sum_pair {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m) :
    ∃ c₂ : ℝ≥0∞, c₂ ≠ ⊤ ∧ ∀ x : BitString, sumPair m x ≤ c₂ * m x := by
  obtain ⟨c, hc_pos, hc_dom⟩ := hm.2 (sumPair m) (isLowerSemicomputableSemimeasure_sumPair hm.1)
  set c' := min c 1
  have hc'_pos : 0 < c' := lt_min hc_pos (by norm_num)
  have hc'_le1 : c' ≤ 1 := min_le_right c 1
  have hc'_dom : DominatesUnary m (sumPair m) c' :=
    hc_dom.mono_const (min_le_left c 1)
  refine ⟨c'⁻¹, ?_, fun x => ?_⟩
  · intro h_top
    rw [ENNReal.inv_eq_top] at h_top
    exact hc'_pos.ne' h_top
  · have h1 := hc'_dom x
    have h_inv_top : c'⁻¹ ≠ ⊤ := by
      intro h_top
      rw [ENNReal.inv_eq_top] at h_top
      exact hc'_pos.ne' h_top
    have h_inv_zero : c'⁻¹ ≠ 0 := by
      intro h_zero
      rw [ENNReal.inv_eq_zero] at h_zero
      have : c' ≤ 1 := hc'_le1
      rw [h_zero] at this
      contradiction
    have h_mul_inv : c'⁻¹ * c' = 1 := ENNReal.inv_mul_cancel hc'_pos.ne' (by
      intro h_top
      rw [h_top] at hc'_le1
      contradiction)
    calc sumPair m x
        = 1 * sumPair m x := (one_mul _).symm
      _ = (c'⁻¹ * c') * sumPair m x := by rw [h_mul_inv]
      _ = c'⁻¹ * (c' * sumPair m x) := by rw [mul_assoc]
      _ ≤ c'⁻¹ * m x := by gcongr

end SemimeasureEmbedding

/-- **Exercise 101, sum version.** `∑_y m([x, y])` differs from `m(x)` by at most
a constant factor in both directions. -/
theorem aprioriMeasure_pair_sum_eq (m : BitString → ℝ≥0∞) (hm : IsUniversalSemimeasure m) :
    ∃ c₁ c₂ : ℝ≥0∞, 0 < c₁ ∧ c₂ ≠ ⊤ ∧ ∀ x : BitString,
      c₁ * m x ≤ ∑' y : BitString, m (pairCode x y) ∧
        (∑' y : BitString, m (pairCode x y)) ≤ c₂ * m x := by
  obtain ⟨c₁, hc₁_pos, hc₁_bound⟩ := SemimeasureEmbedding.lower_bound_pair_code hm
  obtain ⟨c₂, hc₂_top, hc₂_bound⟩ := SemimeasureEmbedding.upper_bound_sum_pair hm
  refine ⟨c₁, c₂, hc₁_pos, hc₂_top, fun x => ⟨?_, hc₂_bound x⟩⟩
  calc c₁ * m x ≤ m (pairCode x []) := hc₁_bound x
    _ ≤ ∑' y : BitString, m (pairCode x y) := ENNReal.le_tsum []

/-- **Exercise 101, maximum version.** `max_y m([x, y])` differs from `m(x)` by at
most a constant factor in both directions. -/
theorem aprioriMeasure_pair_max_eq (m : BitString → ℝ≥0∞) (hm : IsUniversalSemimeasure m) :
    ∃ c₁ c₂ : ℝ≥0∞, 0 < c₁ ∧ c₂ ≠ ⊤ ∧ ∀ x : BitString,
      c₁ * m x ≤ ⨆ y : BitString, m (pairCode x y) ∧
        (⨆ y : BitString, m (pairCode x y)) ≤ c₂ * m x := by
  obtain ⟨c₁, hc₁_pos, hc₁_bound⟩ := SemimeasureEmbedding.lower_bound_pair_code hm
  obtain ⟨c₂, hc₂_top, hc₂_bound⟩ := SemimeasureEmbedding.upper_bound_sum_pair hm
  refine ⟨c₁, c₂, hc₁_pos, hc₂_top, fun x => ⟨?_, ?_⟩⟩
  · calc c₁ * m x ≤ m (pairCode x []) := hc₁_bound x
      _ ≤ ⨆ y : BitString, m (pairCode x y) := le_iSup (fun y => m (pairCode x y)) []
  · calc (⨆ y : BitString, m (pairCode x y))
        ≤ ∑' y : BitString, m (pairCode x y) := iSup_le (fun y => ENNReal.le_tsum y)
      _ ≤ c₂ * m x := hc₂_bound x

end Kolmogorov
