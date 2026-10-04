/-
Copyright (c) 2025 The Kolmogorov Project Developers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Kolmogorov Project Developers
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bipartite graphs, neighbourhoods and the expansion property

A finite bipartite graph is a `Finset (L × R)`: the set of its edges, with the left part `L`
and the right part `R` given as types.  This file fixes the vocabulary used by the
combinatorial arguments of SUV Chapter 12 (Muchnik's theorem and on-line matching): the
neighbourhood of a left vertex, the degrees on both sides, the neighbourhood `E(T)` of a set
of left vertices, and the expansion property "`E(T)` is strictly larger than `T`" for all
small enough `T`.

The expander-like graph whose existence is proved by a counting argument on
SUV pp. 371–372 is stated here as `exists_expanding_bipartiteGraph`.

SUV Section 12.3, pp. 370–372.
-/

namespace Kolmogorov

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-- Boolean strings of length `n` as a finite type: the set `𝔹ⁿ` of the book, used as the
vertex set of the bipartite graphs of Chapter 12.

SUV Section 12.3, p. 371. -/
abbrev BoolVec (n : ℕ) := Fin n → Bool

/-- The right neighbours of a left vertex `l` in the bipartite graph `g`.

SUV Section 12.3, p. 371. -/
def neighbors (g : Finset (L × R)) (l : L) : Finset R :=
  (g.filter fun e => e.1 = l).image Prod.snd

/-- The degree of a left vertex: the number of its right neighbours.

SUV Section 12.3, p. 371. -/
def leftDegree (g : Finset (L × R)) (l : L) : ℕ := (neighbors g l).card

/-- The left neighbours of a right vertex `r` in the bipartite graph `g`.

SUV Section 12.3, p. 371. -/
def rightNeighbors (g : Finset (L × R)) (r : R) : Finset L :=
  (g.filter fun e => e.2 = r).image Prod.fst

/-- The degree of a right vertex: the number of its left neighbours.

SUV Section 12.3, p. 371. -/
def rightDegree (g : Finset (L × R)) (r : R) : ℕ := (rightNeighbors g r).card

/-- `E(T)`: all right neighbours of all left vertices of `T`.

SUV Section 12.3, p. 371. -/
def neighborSet (g : Finset (L × R)) (T : Finset L) : Finset R := T.biUnion (neighbors g)

/-- The expansion property of SUV p. 371: for every nonempty set `T` of at most `k` left
vertices, `E(T)` has strictly more elements than `T`.

The nonemptiness hypothesis is ours: the book writes "for every set `T` with at most `2^{m-1}`
elements", which is false as printed for `T = ∅` (where `|E(T)| = 0 = |T|`); the proof of the
lemma quantifies over nonempty `T`.

SUV Section 12.3, p. 371. -/
def IsExpanding (g : Finset (L × R)) (k : ℕ) : Prop :=
  ∀ T : Finset L, T.Nonempty → T.card ≤ k → T.card < (neighborSet g T).card

private abbrev ChoiceTable (a m : ℕ) :=
  BoolVec a → Fin (a + m + 2) → BoolVec m

private def BadChoiceTable (a m : ℕ) (f : ChoiceTable a m) : Prop :=
  ∃ T : Finset (BoolVec a), T.Nonempty ∧ T.card ≤ 2 ^ (m - 1) ∧
    (T.biUnion fun l ↦ Finset.univ.image (f l)).card ≤ T.card

private noncomputable def badChoiceTables (a m : ℕ) : Finset (ChoiceTable a m) := by
  classical
  exact Finset.univ.filter (BadChoiceTable a m)

private lemma card_boolVec (n : ℕ) : Fintype.card (BoolVec n) = 2 ^ n := by
  simp [BoolVec]

private lemma card_choiceTable (a m : ℕ) :
    Fintype.card (ChoiceTable a m) = (2 ^ m) ^ (2 ^ a * (a + m + 2)) := by
  change Fintype.card (BoolVec a → Fin (a + m + 2) → BoolVec m) = _
  rw [Fintype.card_fun, Fintype.card_fun, card_boolVec, card_boolVec,
    Fintype.card_fin, ← pow_mul, mul_comm]

/-- The choice tables sending every trial of every vertex of `T` into `U`: the event
"all neighbours of `T` lie in `U`" of the book's random-graph argument. -/
private def tablesInto (a m : ℕ) (T : Finset (BoolVec a)) (U : Finset (BoolVec m)) :
    Finset (ChoiceTable a m) :=
  Fintype.piFinset fun l ↦ Fintype.piFinset fun _ : Fin (a + m + 2) ↦
    if l ∈ T then U else Finset.univ

private lemma card_tablesInto (a m : ℕ) (T : Finset (BoolVec a)) (U : Finset (BoolVec m)) :
    (tablesInto a m T U).card =
      (U.card ^ T.card * (2 ^ m) ^ (2 ^ a - T.card)) ^ (a + m + 2) := by
  classical
  rw [tablesInto, Fintype.card_piFinset]
  simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    apply_ite Finset.card]
  rw [Finset.prod_pow, Finset.prod_ite, Finset.prod_const, Finset.prod_const,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_not,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ_sdiff, card_boolVec,
    card_boolVec]

/-- The key estimate of SUV p. 372: for `|U| = |T| = t ≤ 2^{m-1}` the event "all neighbours
of `T` lie in `U`" has probability at most `2^{-t(a+m+2)}`, stated multiplicatively. -/
private lemma card_tablesInto_mul_le (a m : ℕ) (hm : 0 < m) (T : Finset (BoolVec a))
    (U : Finset (BoolVec m)) (hU : U.card = T.card) (hT : T.card ≤ 2 ^ (m - 1)) :
    (tablesInto a m T U).card * 2 ^ (T.card * (a + m + 2)) ≤
      Fintype.card (ChoiceTable a m) := by
  rw [card_tablesInto, card_choiceTable, hU]
  have hTa : T.card ≤ 2 ^ a := by simpa [card_boolVec] using Finset.card_le_univ T
  have h1 : T.card ^ T.card * 2 ^ T.card ≤ (2 ^ m) ^ T.card := by
    rw [← mul_pow]
    apply Nat.pow_le_pow_left
    calc T.card * 2 ≤ 2 ^ (m - 1) * 2 := Nat.mul_le_mul_right 2 hT
      _ = 2 ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm]
  calc (T.card ^ T.card * (2 ^ m) ^ (2 ^ a - T.card)) ^ (a + m + 2) *
        2 ^ (T.card * (a + m + 2))
      = (T.card ^ T.card * 2 ^ T.card * (2 ^ m) ^ (2 ^ a - T.card)) ^ (a + m + 2) := by
        rw [pow_mul, ← mul_pow]; ring
    _ ≤ ((2 ^ m) ^ T.card * (2 ^ m) ^ (2 ^ a - T.card)) ^ (a + m + 2) :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ h1) _
    _ = (2 ^ m) ^ (2 ^ a * (a + m + 2)) := by
        rw [← pow_add, Nat.add_sub_cancel' hTa, ← pow_mul]

/-- The index set of the union bound: a size `t ∈ [1, 2^{m-1}]` together with a set `T` of
`t` left vertices and a set `U` of `t` right vertices. -/
private def badWitnesses (a m : ℕ) :
    Finset (Σ _t : ℕ, Finset (BoolVec a) × Finset (BoolVec m)) :=
  (Finset.Icc 1 (2 ^ (m - 1))).sigma fun t ↦
    Finset.powersetCard t Finset.univ ×ˢ Finset.powersetCard t Finset.univ

private lemma badChoiceTables_subset (a m : ℕ) :
    badChoiceTables a m ⊆
      (badWitnesses a m).biUnion fun w ↦ tablesInto a m w.2.1 w.2.2 := by
  classical
  intro f hf
  simp only [badChoiceTables, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  obtain ⟨T, hT, hTk, hcard⟩ := hf
  have hTm : T.card ≤ (Finset.univ : Finset (BoolVec m)).card := by
    rw [Finset.card_univ, card_boolVec]
    exact hTk.trans (Nat.pow_le_pow_right two_pos (Nat.sub_le m 1))
  obtain ⟨U, hUsub, -, hUcard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ _) hcard hTm
  rw [Finset.mem_biUnion]
  refine ⟨⟨T.card, T, U⟩, ?_, ?_⟩
  · simp only [badWitnesses, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_product,
      Finset.mem_powersetCard]
    exact ⟨⟨hT.card_pos, hTk⟩, ⟨Finset.subset_univ _, trivial⟩, ⟨Finset.subset_univ _, hUcard⟩⟩
  · simp only [tablesInto, Fintype.mem_piFinset]
    intro l i
    split_ifs with hl
    · exact hUsub (Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    · exact Finset.mem_univ _

/-- The geometric tail of SUV p. 372: if `g t ≤ N / 4^t` for `1 ≤ t ≤ K`, then
`∑_{t=1}^{K} g t ≤ N/3 < N`. -/
private lemma sum_lt_of_mul_four_pow_le {N K : ℕ} (hN : 0 < N) (g : ℕ → ℕ)
    (hg : ∀ t ∈ Finset.Icc 1 K, g t * 4 ^ t ≤ N) : ∑ t ∈ Finset.Icc 1 K, g t < N := by
  have hq : ∀ t ∈ Finset.Icc 1 K, (g t : ℚ) ≤ N * (1 / 4 : ℚ) ^ t := by
    intro t ht
    have h4 : (0 : ℚ) < 4 ^ t := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ h4]
    exact_mod_cast hg t ht
  have hgeom : ∑ t ∈ Finset.Icc 1 K, (1 / 4 : ℚ) ^ t < 1 := by
    rw [show Finset.Icc 1 K = Finset.Ico 1 (K + 1) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    refine (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans_lt ?_
    norm_num
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have : ((∑ t ∈ Finset.Icc 1 K, g t : ℕ) : ℚ) < N := by
    push_cast
    calc ∑ t ∈ Finset.Icc 1 K, (g t : ℚ) ≤ ∑ t ∈ Finset.Icc 1 K, (N : ℚ) * (1 / 4 : ℚ) ^ t :=
          Finset.sum_le_sum hq
      _ = N * ∑ t ∈ Finset.Icc 1 K, (1 / 4 : ℚ) ^ t := by rw [Finset.mul_sum]
      _ < N * 1 := by gcongr
      _ = N := mul_one _
  exact_mod_cast this

/-- The union bound of SUV p. 372 for one size `t`: summed over all pairs `(T, U)` of size
`t`, the bad events have total measure at most `2^{at} 2^{mt} 2^{-t(a+m+2)} = 4^{-t}`. -/
private lemma sum_card_tablesInto_mul_le (a m : ℕ) (hm : 0 < m) (t : ℕ)
    (ht : t ≤ 2 ^ (m - 1)) :
    (∑ p ∈ Finset.powersetCard t (Finset.univ : Finset (BoolVec a)) ×ˢ
        Finset.powersetCard t (Finset.univ : Finset (BoolVec m)),
        (tablesInto a m p.1 p.2).card) * 4 ^ t ≤ Fintype.card (ChoiceTable a m) := by
  classical
  set N := Fintype.card (ChoiceTable a m)
  set P := Finset.powersetCard t (Finset.univ : Finset (BoolVec a)) ×ˢ
    Finset.powersetCard t (Finset.univ : Finset (BoolVec m)) with hP
  have hbound : ∀ p ∈ P, (tablesInto a m p.1 p.2).card * 2 ^ (t * (a + m + 2)) ≤ N := by
    intro p hp
    rw [hP, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
    have := card_tablesInto_mul_le a m hm p.1 p.2 (hp.2.2.trans hp.1.2.symm) (hp.1.2 ▸ ht)
    rwa [hp.1.2] at this
  have hsum : (∑ p ∈ P, (tablesInto a m p.1 p.2).card) * 2 ^ (t * (a + m + 2)) ≤
      P.card * N := by
    rw [Finset.sum_mul]
    refine (Finset.sum_le_sum hbound).trans ?_
    rw [Finset.sum_const_nat fun _ _ ↦ rfl]
  have hpairs : P.card ≤ 2 ^ (t * (a + m)) := by
    rw [hP, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_univ, Finset.card_univ, card_boolVec, card_boolVec]
    calc (2 ^ a).choose t * (2 ^ m).choose t ≤ (2 ^ a) ^ t * (2 ^ m) ^ t :=
          Nat.mul_le_mul (Nat.choose_le_pow _ _) (Nat.choose_le_pow _ _)
      _ = 2 ^ (t * (a + m)) := by
          rw [← pow_mul, ← pow_mul, ← pow_add, mul_comm a t, mul_comm m t, mul_add]
  have hk : 2 ^ (t * (a + m + 2)) = 4 ^ t * 2 ^ (t * (a + m)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hmain : (∑ p ∈ P, (tablesInto a m p.1 p.2).card) * 4 ^ t * 2 ^ (t * (a + m)) ≤
      N * 2 ^ (t * (a + m)) := by
    calc (∑ p ∈ P, (tablesInto a m p.1 p.2).card) * 4 ^ t * 2 ^ (t * (a + m))
        = (∑ p ∈ P, (tablesInto a m p.1 p.2).card) * 2 ^ (t * (a + m + 2)) := by
          rw [hk]; ring
      _ ≤ P.card * N := hsum
      _ ≤ 2 ^ (t * (a + m)) * N := Nat.mul_le_mul_right _ hpairs
      _ = N * 2 ^ (t * (a + m)) := mul_comm _ _
  exact Nat.le_of_mul_le_mul_right hmain (by positivity)

private lemma badChoiceTable_count_lt (a m : ℕ) :
    0 < m → m ≤ a → (badChoiceTables a m).card < Fintype.card (ChoiceTable a m) := by
  intro hm _
  classical
  refine (Finset.card_le_card (badChoiceTables_subset a m)).trans_lt ?_
  refine lt_of_le_of_lt Finset.card_biUnion_le ?_
  rw [badWitnesses, Finset.sum_sigma]
  refine sum_lt_of_mul_four_pow_le Fintype.card_pos _ fun t ht ↦ ?_
  exact sum_card_tablesInto_mul_le a m hm t (Finset.mem_Icc.1 ht).2

private lemma exists_expanding_choiceTable (a m : ℕ) (hm : 0 < m) (hma : m ≤ a) :
    ∃ f : ChoiceTable a m, ∀ T : Finset (BoolVec a), T.Nonempty →
      T.card ≤ 2 ^ (m - 1) → T.card <
        (T.biUnion fun l ↦ Finset.univ.image (f l)).card := by
  classical
  have hex : ∃ f : ChoiceTable a m, ¬ BadChoiceTable a m f := by
    by_contra h
    push Not at h
    have hall : badChoiceTables a m = Finset.univ := by
      ext f
      simp [badChoiceTables, h f]
    have hcount := badChoiceTable_count_lt a m hm hma
    rw [hall, Finset.card_univ] at hcount
    exact (Nat.lt_irrefl _ hcount)
  obtain ⟨f, hf⟩ := hex
  refine ⟨f, ?_⟩
  intro T hT hcard
  by_contra h
  exact hf ⟨T, hT, hcard, Nat.le_of_not_gt h⟩

private def graphOfChoices {L R I : Type*} [Fintype L] [Fintype I]
    [DecidableEq L] [DecidableEq R] (f : L → I → R) : Finset (L × R) :=
  Finset.univ.biUnion fun l ↦ Finset.univ.image fun i ↦ (l, f l i)

/-- The expander-like graph of SUV Section 12.3: for positive `m ≤ a` there is a bipartite
graph `E ⊆ 𝔹ᵃ × 𝔹ᵐ` of left degree at most `a + m + 2` in which every nonempty set `T` of at
most `2^{m-1}` left vertices satisfies `|E(T)| > |T|`.

SUV Lemma of Section 12.3, pp. 371–372. -/
theorem exists_expanding_bipartiteGraph (a m : ℕ) (hm : 0 < m) (hma : m ≤ a) :
    ∃ g : Finset (BoolVec a × BoolVec m),
      (∀ l : BoolVec a, leftDegree g l ≤ a + m + 2) ∧ IsExpanding g (2 ^ (m - 1)) := by
  classical
  obtain ⟨f, hf⟩ := exists_expanding_choiceTable a m hm hma
  refine ⟨graphOfChoices f, ?_, ?_⟩
  · intro l
    rw [leftDegree]
    have hneighbors :
        neighbors (graphOfChoices f) l = Finset.univ.image (f l) := by
      ext r
      simp [neighbors, graphOfChoices]
    rw [hneighbors]
    simpa using (Finset.card_image_le (s := Finset.univ) (f := f l))
  · intro T hT hcard
    rw [show neighborSet (graphOfChoices f) T =
        T.biUnion (fun l ↦ Finset.univ.image (f l)) by
      ext r
      simp [neighborSet, neighbors, graphOfChoices]]
    exact hf T hT hcard

end Kolmogorov
