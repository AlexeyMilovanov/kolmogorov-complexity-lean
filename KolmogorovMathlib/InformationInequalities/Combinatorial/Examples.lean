import KolmogorovMathlib.InformationInequalities.AlmostUniform

/-!
# Combinatorial interpretations: two examples

SUV Section 10.7, pp. 328–330.

Two inequalities between complexities translated into statements about covers of finite sets:
the pair formula `C(x, y) ≥ C(x) + C(y | x)` (Problem 288) and the basic inequality, whose
translation covers a set of triples by two sets, one with a short first projection and one of
small volume.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}
/-! ### Section 10.7: examples -/

/-- **Problem 288.**  The combinatorial counterpart of `C(x, y) ≥ C(x) + C(y | x)`: for all
`u, v` and every set `A` of pairs with at most `2^{u+v}` elements there are a set `B` of at most
`2^u` first components and a set `C` of pairs with at most `2^v` pairs over any given first
component, such that every pair of `A` has its first component in `B` or belongs to `C`.  The
problem asks to prove it by translating the proof of the formula for the complexity of a pair.
SUV Problem 288, p. 329. -/
theorem exists_cover_of_card_le_two_pow {α β : Type} [DecidableEq α]
    (u v : ℕ) (A : Finset (α × β)) (hA : A.card ≤ 2 ^ (u + v)) :
    ∃ (B : Finset α) (C : Finset (α × β)),
      B.card ≤ 2 ^ u ∧ (∀ a : α, (C.filter fun p => p.1 = a).card ≤ 2 ^ v) ∧
        ∀ p ∈ A, p.1 ∈ B ∨ p ∈ C := by
  classical
  -- the fibre of `A` over a first component `a`
  set fib : α → Finset (α × β) := fun a => A.filter fun p => p.1 = a with hfib
  -- heavy first components: more than `2^v` pairs above them
  let B : Finset α := (A.image Prod.fst).filter fun a => 2 ^ v < (fib a).card
  -- the pairs of `A` above a light first component
  let C : Finset (α × β) := A.filter fun p => (fib p.1).card ≤ 2 ^ v
  refine ⟨B, C, ?_, ?_, ?_⟩
  · -- the heavy fibres are disjoint subsets of `A`, so `|B| · (2^v + 1) ≤ |A| ≤ 2^u · 2^v`
    have hdisj : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → Disjoint (fib a) (fib b) := by
      intro a _ b _ hab
      refine Finset.disjoint_left.2 fun p hpa hpb => hab ?_
      simp only [hfib, Finset.mem_filter] at hpa hpb
      exact hpa.2.symm.trans hpb.2
    have hsub : B.biUnion fib ⊆ A := by
      intro p hp
      obtain ⟨a, _, hpa⟩ := Finset.mem_biUnion.1 hp
      exact (Finset.mem_filter.1 hpa).1
    have hsum : B.card • (2 ^ v + 1) ≤ ∑ a ∈ B, (fib a).card :=
      Finset.card_nsmul_le_sum B _ _ fun a ha => (Finset.mem_filter.1 ha).2
    have hcard : ∑ a ∈ B, (fib a).card ≤ A.card := by
      rw [← Finset.card_biUnion hdisj]
      exact Finset.card_le_card hsub
    rw [smul_eq_mul] at hsum
    rw [pow_add] at hA
    by_contra hB
    push Not at hB
    have h1 : (2 ^ u + 1) * (2 ^ v + 1) ≤ B.card * (2 ^ v + 1) := Nat.mul_le_mul_right _ hB
    have h2 : 2 ^ u * 2 ^ v < (2 ^ u + 1) * (2 ^ v + 1) := by
      calc 2 ^ u * 2 ^ v < 2 ^ u * 2 ^ v + 1 := Nat.lt_succ_self _
        _ ≤ (2 ^ u + 1) * (2 ^ v + 1) := by
          rw [add_mul, mul_add, mul_add]
          simp only [mul_one, one_mul]
          exact Nat.add_le_add (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    exact absurd (h2.trans_le (h1.trans (hsum.trans (hcard.trans hA)))) (lt_irrefl _)
  · intro a
    by_cases ha : (fib a).card ≤ 2 ^ v
    · refine le_trans (Finset.card_le_card ?_) ha
      intro p hp
      simp only [Finset.mem_filter, C] at hp
      exact Finset.mem_filter.2 ⟨hp.1.1, hp.2⟩
    · have hempty : (C.filter fun p => p.1 = a) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun p hp hpa => ha ?_
        simp only [Finset.mem_filter, C] at hp
        rw [← hpa]
        exact hp.2
      rw [hempty]
      simp
  · intro p hp
    by_cases h : (fib p.1).card ≤ 2 ^ v
    · exact Or.inr (Finset.mem_filter.2 ⟨hp, h⟩)
    · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hp, not_le.1 h⟩)
/-- The combinatorial counterpart of the basic inequality
`C(x₁) + C(x₁, x₂, x₃) ≤ C(x₁, x₂) + C(x₁, x₃) + O(log N)`: if `A ⊆ X₁ × X₂ × X₃` and
`m_A(1,2) · m_A(1,3) = l · V` for some positive reals `l, V`, then `A` is covered by two sets
`B` and `C` with `m_B(1) ≤ l` and `m_C(1,2,3) = |C| ≤ V`.
The page prints the basic inequality as `C(x₁) + C(x₁,x₂,x₃) ≤ C(x₁,x₂) + C(x₂,x₃)`, a
misprint for `C(x₁,x₃)`: the restatement right below it, and the combinatorial statement,
use the projection onto the coordinates `1, 3`.  SUV Section 10.7, pp. 329–330 (unnumbered). -/
theorem exists_cover_of_projCard_mul_eq {X : Fin 3 → Type} [∀ i, DecidableEq (X i)]
    (A : Finset (∀ i, X i)) {l V : ℝ} (hl : 0 < l) (hV : 0 < V)
    (h : (projCard A {0, 1} : ℝ) * projCard A {0, 2} = l * V) :
    ∃ B C : Finset (∀ i, X i), A ⊆ B ∪ C ∧ (projCard B {0} : ℝ) ≤ l ∧
      (projCard C Finset.univ : ℝ) ≤ V := by
  classical
  have h01 : (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := by decide
  have h02 : (0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) := by decide
  have h00 : (0 : Fin 3) ∈ ({0} : Finset (Fin 3)) := by decide
  -- the first coordinates of the points of `A`
  set S : Finset (X 0) := A.image fun x => x 0 with hS
  -- `p a` and `q a`: the points of the projections onto `(1, 2)` and `(1, 3)` over `a`
  set p : X 0 → ℕ := fun a => ((proj A {0, 1}).filter fun r => r ⟨0, h01⟩ = a).card with hp
  set q : X 0 → ℕ := fun a => ((proj A {0, 2}).filter fun r => r ⟨0, h02⟩ = a).card with hq
  -- the section of `A` over `a` injects into the product of the two projection fibres
  have hsec : ∀ a, (A.filter fun x => x 0 = a).card ≤ p a * q a := by
    intro a
    have key := Finset.card_le_card_of_injOn (s := A.filter fun x => x 0 = a)
      (t := ((proj A {0, 1}).filter fun r => r ⟨0, h01⟩ = a) ×ˢ
        ((proj A {0, 2}).filter fun r => r ⟨0, h02⟩ = a))
      (fun x => (restrictTo {0, 1} x, restrictTo {0, 2} x)) ?_ ?_
    · rw [Finset.card_product] at key
      exact key
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨?_, ?_⟩)
      · exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hx.1, hx.2⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hx.1, hx.2⟩
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      funext i
      fin_cases i
      · exact congrFun hxy.1 ⟨0, h01⟩
      · exact congrFun hxy.1 ⟨1, by decide⟩
      · exact congrFun hxy.2 ⟨2, by decide⟩
  -- the projections and `A` itself are counted fibrewise over the first coordinate
  have hPsum : projCard A {0, 1} = ∑ a ∈ S, p a := by
    unfold projCard
    refine Finset.card_eq_sum_card_fiberwise (s := proj A {0, 1}) (t := S)
      (f := fun r : (i : ({0, 1} : Finset (Fin 3))) → X i.val => r ⟨0, h01⟩) fun r hr => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hr)
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx)
  have hQsum : projCard A {0, 2} = ∑ a ∈ S, q a := by
    unfold projCard
    refine Finset.card_eq_sum_card_fiberwise (s := proj A {0, 2}) (t := S)
      (f := fun r : (i : ({0, 2} : Finset (Fin 3))) → X i.val => r ⟨0, h02⟩) fun r hr => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hr)
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx)
  have hQsum' : (projCard A {0, 2} : ℝ) = ∑ a ∈ S, (q a : ℝ) := by
    rw [hQsum, Nat.cast_sum]
  -- `m_A(1,2) · m_A(1,3) = l · V > 0`, so `A` is non-empty and `m_A(1,3) > 0`
  have hQpos : (0 : ℝ) < projCard A {0, 2} :=
    pos_of_mul_pos_right (by rw [h]; exact mul_pos hl hV) (Nat.cast_nonneg _)
  -- heavy first coordinates: `q a · l > m_A(1, 3)`; there are fewer than `l` of them
  let B : Finset (∀ i, X i) := A.filter fun x => (projCard A {0, 2} : ℝ) < (q (x 0) : ℝ) * l
  let C : Finset (∀ i, X i) := A.filter fun x => (q (x 0) : ℝ) * l ≤ (projCard A {0, 2} : ℝ)
  let H : Finset (X 0) := S.filter fun a => (projCard A {0, 2} : ℝ) < (q a : ℝ) * l
  refine ⟨B, C, ?_, ?_, ?_⟩
  · intro x hx
    rcases lt_or_ge (projCard A {0, 2} : ℝ) ((q (x 0) : ℝ) * l) with hx' | hx'
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx, hx'⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hx, hx'⟩)
  · have hBH : projCard B {0} ≤ H.card := by
      refine Finset.card_le_card_of_injOn (fun r => r ⟨0, h00⟩) ?_ ?_
      · intro r hr
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hr)
        have hx' := Finset.mem_filter.1 hx
        exact Finset.mem_coe.2
          (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hx'.1, hx'.2⟩)
      · intro r _ r' _ hrr
        funext i
        obtain ⟨i, hi⟩ := i
        obtain rfl := Finset.mem_singleton.1 hi
        exact hrr
    have hHl : (H.card : ℝ) ≤ l := by
      rcases H.eq_empty_or_nonempty with hH | hH
      · rw [hH, Finset.card_empty, Nat.cast_zero]
        exact hl.le
      · have h1 : ∑ _a ∈ H, (projCard A {0, 2} : ℝ) < ∑ a ∈ H, (q a : ℝ) * l :=
          Finset.sum_lt_sum_of_nonempty hH fun a ha => (Finset.mem_filter.1 ha).2
        have h2 : ∑ a ∈ H, (q a : ℝ) * l ≤ (projCard A {0, 2} : ℝ) * l := by
          rw [hQsum', Finset.sum_mul]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun a _ _ => by positivity
        rw [Finset.sum_const, nsmul_eq_mul] at h1
        have h3 : (H.card : ℝ) * (projCard A {0, 2} : ℝ) < l * (projCard A {0, 2} : ℝ) := by
          linarith
        exact (lt_of_mul_lt_mul_right h3 hQpos.le).le
    exact le_trans (by exact_mod_cast hBH) hHl
  · rw [projCard_univ]
    have hCsum : C.card = ∑ a ∈ S, (C.filter fun x => x 0 = a).card := by
      refine Finset.card_eq_sum_card_fiberwise (s := C) (t := S)
        (f := fun x : (i : Fin 3) → X i => x 0) fun x hx => ?_
      exact Finset.mem_coe.2
        (Finset.mem_image_of_mem _ (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).1)
    -- over a light `a` the fibre of `C` has at most `p a · q a ≤ p a · m_A(1,3) / l` points
    have hfib : ∀ a ∈ S,
        ((C.filter fun x => x 0 = a).card : ℝ) * l ≤ (p a : ℝ) * (projCard A {0, 2} : ℝ) := by
      intro a _
      rcases lt_or_ge (projCard A {0, 2} : ℝ) ((q a : ℝ) * l) with ha | ha
      · have hempty : (C.filter fun x => x 0 = a) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun x hx hxa => ?_
          have hxC := (Finset.mem_filter.1 hx).2
          rw [hxa] at hxC
          exact absurd ha (not_lt.2 hxC)
        rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]
        positivity
      · have hle : (C.filter fun x => x 0 = a).card ≤ p a * q a :=
          le_trans (Finset.card_le_card fun x hx => Finset.mem_filter.2
            ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).1, (Finset.mem_filter.1 hx).2⟩)
            (hsec a)
        have hle' : ((C.filter fun x => x 0 = a).card : ℝ) ≤ (p a : ℝ) * q a := by
          exact_mod_cast hle
        calc ((C.filter fun x => x 0 = a).card : ℝ) * l ≤ (p a : ℝ) * q a * l :=
              mul_le_mul_of_nonneg_right hle' hl.le
          _ = (p a : ℝ) * ((q a : ℝ) * l) := by ring
          _ ≤ (p a : ℝ) * (projCard A {0, 2} : ℝ) :=
              mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)
    have hCl : (C.card : ℝ) * l ≤ V * l := by
      rw [mul_comm V l, ← h, hCsum, Nat.cast_sum, Finset.sum_mul, hPsum, Nat.cast_sum,
        Finset.sum_mul]
      exact Finset.sum_le_sum hfib
    exact le_of_mul_le_mul_right hCl hl

end Kolmogorov
