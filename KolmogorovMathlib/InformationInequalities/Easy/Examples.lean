import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaCount
import KolmogorovMathlib.Entropy.Coding
import KolmogorovMathlib.Entropy.Complexity.Frequencies
import KolmogorovMathlib.Entropy.Inequalities
import KolmogorovMathlib.InformationInequalities.UniformSets

/-!
# First combinatorial translations: an example and two failures

SUV Section 10.1, pp. 315–318, Problems 281 and 282.

The set inequality `|A|² ≤ m(1,2) m(1,3) m(2,3)` (`card_sq_le_prod_projCard_pairs`), deduced
from the entropy inequality `2H(ξ₁, ξ₂, ξ₃) ≤ H(ξ₁, ξ₂) + H(ξ₁, ξ₃) + H(ξ₂, ξ₃)` for a triple
uniformly distributed on `A`, and the two naive translations that fail
(`exists_projCard_naive_basic_false`, `exists_maxSection_naive_pair_false`), which is what
motivates uniform sets in Section 10.2.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-! ### The set inequality `|A|² ≤ m(1,2) m(1,3) m(2,3)` -/

private lemma nat_sq_le_mul_three_of_logb {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : 2 * Real.logb 2 a ≤ Real.logb 2 b + Real.logb 2 c + Real.logb 2 d) :
    a ^ 2 ≤ b * c * d := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.logb 2 ((a : ℝ) ^ 2) ≤ Real.logb 2 ((b : ℝ) * c * d) := by
    rw [Real.logb_pow, Real.logb_mul (mul_ne_zero hbR.ne' hcR.ne') hdR.ne',
      Real.logb_mul hbR.ne' hcR.ne']
    norm_num
    exact h
  have hreal : (a : ℝ) ^ 2 ≤ (b : ℝ) * c * d :=
    (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mp hlog
  exact_mod_cast hreal

private lemma entropy_le_logb_card_range {Ω : Type*} [Fintype Ω]
    {α : Type*} [DecidableEq α] (μ : FiniteProbSpace Ω) (Y : Ω → α) :
    entropy μ Y ≤ Real.logb 2 (rangeFinset Y).card := by
  let Y' : Ω → {a // a ∈ rangeFinset Y} :=
    fun ω => ⟨Y ω, mem_rangeFinset.2 ⟨ω, rfl⟩⟩
  have heq : entropy μ Y = entropy μ Y' := by
    have h := entropy_comp_of_injective μ Y' Subtype.val_injective
    simpa [Y', Function.comp_def] using h
  rw [heq, entropy_eq_entropyDist]
  have hsum : ∑ a, μ.dist Y' a = 1 := by
    rw [← μ.sum_dist_eq_one Y']
    exact (Finset.sum_subset (Finset.subset_univ _) fun a _ ha =>
      μ.dist_eq_zero_of_not_mem_range ha).symm
  simpa using entropyDist_le_logb_card (μ.dist_nonneg Y') hsum

private lemma entropy_uniformProbOn_id {α : Type*} [DecidableEq α]
    (A : Finset α) (hA : A.Nonempty) :
    entropy (uniformProbOn A hA) (fun ω : {a // a ∈ A} => ω) =
      Real.logb 2 A.card := by
  have hrange : rangeFinset (fun ω : {a // a ∈ A} => ω) = Finset.univ := by
    ext ω
    simp
  have hdist : ∀ ω : {a // a ∈ A},
      (uniformProbOn A hA).dist (fun x : {a // a ∈ A} => x) ω =
        (A.card : ℝ)⁻¹ := by
    intro ω
    rw [FiniteProbSpace.dist,
      show (Finset.univ.filter fun x : {a // a ∈ A} => x = ω) = {ω} by ext; simp]
    simp [FiniteProbSpace.probOf, uniformProbOn]
  have hcard : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 hA).ne'
  have hlog2 : Real.log 2 ≠ 0 := by positivity
  rw [entropy, hrange, Finset.sum_congr rfl fun a _ => by rw [hdist a],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [negMulLog2, Real.negMulLog, Real.log_inv, Real.logb]
  rw [Fintype.card_coe]
  field_simp

private lemma exists_uniform_point_code {X : Fin 3 → Type}
    [∀ i, DecidableEq (X i)] (A : Finset (∀ i, X i)) (hA : A.Nonempty) :
    ∃ Z : Fin 3 → {a // a ∈ A} → ℕ,
      Function.Injective (subtuple Z Finset.univ) ∧
        ∀ I : Finset (Fin 3),
          (rangeFinset (subtuple Z I)).card = projCard A I := by
  have _ := hA
  have f_i (i : Fin 3) : ∃ f : X i → ℕ,
      ∀ x y, (∃ a ∈ A, a i = x) → (∃ a ∈ A, a i = y) → f x = f y → x = y := by
    let A_i := image (fun a : ∀ i, X i => a i) A
    let eq_f := Fintype.equivFin A_i
    let f : X i → ℕ := fun x => if h : x ∈ A_i then eq_f ⟨x, h⟩ else 0
    refine ⟨f, fun x y hx hy heq => ?_⟩
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    have haA : a i ∈ A_i := mem_image.mpr ⟨a, ha, rfl⟩
    have hbA : b i ∈ A_i := mem_image.mpr ⟨b, hb, rfl⟩
    simp only [f, haA, hbA, dite_eq_left] at heq
    have h_eq2 : eq_f ⟨a i, haA⟩ = eq_f ⟨b i, hbA⟩ := Fin.ext heq
    exact congrArg Subtype.val (eq_f.injective h_eq2)
  choose f hf using f_i
  let Z : Fin 3 → {a // a ∈ A} → ℕ := fun i a => f i (a.val i)
  refine ⟨Z, ?_, fun I => ?_⟩
  · intro a b hab
    ext i
    have heq : Z i a = Z i b := congrFun hab ⟨i, mem_univ i⟩
    exact hf i (a.val i) (b.val i) ⟨a.val, a.prop, rfl⟩ ⟨b.val, b.prop, rfl⟩ heq
  · rw [projCard]
    have h_eq_card : (rangeFinset (subtuple Z I)).card = (image (restrictTo I) A).card := by
      let F : ((i : I) → X i.val) → (i : I) → ℕ := fun x i => f i.val (x i)
      have hF_inj : Set.InjOn F (image (restrictTo I) A) := by
        intro x hx y hy heq
        rcases mem_image.mp hx with ⟨a, ha, rfl⟩
        rcases mem_image.mp hy with ⟨b, hb, rfl⟩
        ext i
        have h_feq : f i.val (a i.val) = f i.val (b i.val) := congrFun heq i
        exact hf i.val (a i.val) (b i.val) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ h_feq
      have H : rangeFinset (subtuple Z I) = image F (image (restrictTo I) A) := by
        ext g
        simp only [mem_rangeFinset, mem_image]
        constructor
        · rintro ⟨a, rfl⟩
          refine ⟨fun i => a.val i.val, ⟨a.val, a.prop, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
          refine ⟨⟨a, ha⟩, rfl⟩
      rw [H, card_image_of_injOn hF_inj]
    exact h_eq_card

private lemma entropySub_uniform_point_eq_logb_card {X : Fin 3 → Type}
    (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (Z : Fin 3 → {a // a ∈ A} → ℕ)
    (hZ : Function.Injective (subtuple Z Finset.univ)) :
    entropySub (uniformProbOn A hA) Z Finset.univ = Real.logb 2 A.card := by
  classical
  rw [entropySub, ← entropy_uniformProbOn_id A hA]
  simpa [Function.comp_def] using
    entropy_comp_of_injective (uniformProbOn A hA)
      (fun a : {a // a ∈ A} => a) hZ

private lemma entropySub_uniform_point_le_logb_projCard {X : Fin 3 → Type}
    [∀ i, DecidableEq (X i)] (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (Z : Fin 3 → {a // a ∈ A} → ℕ) (I : Finset (Fin 3))
    (hZ : (rangeFinset (subtuple Z I)).card = projCard A I) :
    entropySub (uniformProbOn A hA) Z I ≤ Real.logb 2 (projCard A I) := by
  rw [entropySub, ← hZ]
  exact entropy_le_logb_card_range (uniformProbOn A hA) (subtuple Z I)

private lemma two_mul_logb_card_le_sum_logb_projCard_pairs {X : Fin 3 → Type}
    [∀ i, DecidableEq (X i)] (A : Finset (∀ i, X i)) (hA : A.Nonempty) :
    2 * Real.logb 2 A.card ≤
      Real.logb 2 (projCard A {0, 1}) + Real.logb 2 (projCard A {0, 2}) +
        Real.logb 2 (projCard A {1, 2}) := by
  obtain ⟨Z, hZinj, hZrange⟩ := exists_uniform_point_code A hA
  have hfull := entropySub_uniform_point_eq_logb_card A hA Z hZinj
  have hpair (I : Finset (Fin 3)) :=
    entropySub_uniform_point_le_logb_projCard A hA Z I (hZrange I)
  have h := sub_one_mul_entropySub_univ_le_sum (n := 3) (uniformProbOn A hA) Z
  have h0 : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
  have h1 : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
  have h2 : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  rw [Fin.sum_univ_three, h0, h1, h2] at h
  norm_num at h
  rw [hfull] at h
  linarith [hpair {0, 1}, hpair {0, 2}, hpair {1, 2}]

/-- For every finite subset `A` of a product of three sets, `|A|² ≤ m(1,2) m(1,3) m(2,3)`,
where `m(i,j)` is the size of the projection of `A` onto the `i`-th and `j`-th coordinates.
The book deduces it from the complexity inequality `2C(x₁,x₂,x₃) ≤ C(x₁,x₂) + C(x₁,x₃) +
C(x₂,x₃) + O(log N)` of Theorem 26 applied to the rows of an element of `A^N` of maximal
complexity.  Problem 281 asks for the same conclusion from the entropy inequality
(`two_mul_entropySub_le_sum_pairs` below), and Problem 282 for a proof that mentions neither
complexity nor entropy; the statement proved is this one in all three cases.
SUV Section 10.1, pp. 315–316 (unnumbered), Problems 281 and 282, p. 316. -/
theorem card_sq_le_prod_projCard_pairs {X : Fin 3 → Type} [∀ i, DecidableEq (X i)]
    (A : Finset (∀ i, X i)) :
    A.card ^ 2 ≤ projCard A {0, 1} * projCard A {0, 2} * projCard A {1, 2} := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [projCard, proj]
  · have hproj (I : Finset (Fin 3)) : 0 < projCard A I := by
      exact Finset.card_pos.mpr (Finset.image_nonempty.mpr hA)
    exact nat_sq_le_mul_three_of_logb (Finset.card_pos.mpr hA)
      (hproj {0, 1}) (hproj {0, 2}) (hproj {1, 2})
      (two_mul_logb_card_le_sum_logb_projCard_pairs A hA)

/-- The entropy inequality that Problem 281 starts from:
`2H(ξ₁, ξ₂, ξ₃) ≤ H(ξ₁, ξ₂) + H(ξ₁, ξ₃) + H(ξ₂, ξ₃)`.  Applying it to a triple uniformly
distributed on `A` and bounding the entropy of each pair by the log-size of its range gives
`card_sq_le_prod_projCard_pairs`.  SUV Problem 281, p. 316. -/
theorem two_mul_entropySub_le_sum_pairs {Ω : Type} [Fintype Ω] {α : Type} [DecidableEq α]
    (μ : FiniteProbSpace Ω) (X : Fin 3 → Ω → α) :
    2 * entropySub μ X Finset.univ
      ≤ entropySub μ X {0, 1} + entropySub μ X {0, 2} + entropySub μ X {1, 2} := by
  have h := sub_one_mul_entropySub_univ_le_sum (n := 3) μ X
  have h0 : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
  have h1 : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
  have h2 : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  rw [Fin.sum_univ_three, h0, h1, h2] at h
  norm_num at h
  linarith

/-! ### The naive translations fail -/

/-- The naive combinatorial translation of the basic inequality,
`m(1) · m(1,2,3) ≤ m(1,2) · m(1,3)`, is false for some sets.  The witness is a
parallelepiped `a × b × c` together with a much longer one `a' × 1 × 1`: the projections onto
the planes `(1,2)` and `(1,3)` grow slowly while `m(1)` grows with `a'`.
SUV Section 10.1, p. 318 (unnumbered). -/
theorem exists_projCard_naive_basic_false :
    ∃ A : Finset (Fin 3 → Fin 4), A.Nonempty ∧
      projCard (X := fun _ => Fin 4) A {0, 1} * projCard (X := fun _ => Fin 4) A {0, 2}
        < projCard (X := fun _ => Fin 4) A {0} * projCard (X := fun _ => Fin 4) A Finset.univ := by
  let A : Finset (Fin 3 → Fin 4) :=
    {![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1],
      ![1, 2, 2], ![2, 2, 2], ![3, 2, 2]}
  refine ⟨A, ?_, ?_⟩
  · simp [A]
  · change 5 * 5 < 4 * 7
    decide

/-- The naive combinatorial translation of `C(x₁) + C(x₂ | x₁) ≤ C(x₁, x₂)`, namely
`m(1) · m(2 | 1) ≤ m(1,2)`, is false for some sets: `m(1,2) / m(1)` is the *average* size of a
non-empty section, which can be smaller than the maximal size `m(2 | 1)`.
SUV Section 10.1, p. 318 (unnumbered). -/
theorem exists_maxSection_naive_pair_false :
    ∃ A : Finset (Fin 2 → Fin 2), A.Nonempty ∧
      projCard (X := fun _ => Fin 2) A Finset.univ
        < projCard (X := fun _ => Fin 2) A {0} * maxSection (X := fun _ => Fin 2) A {1} {0} := by
  let A : Finset (Fin 2 → Fin 2) := {![0, 0], ![1, 0], ![1, 1]}
  refine ⟨A, ?_, ?_⟩
  · simp [A]
  · change 3 < 2 * 2
    decide

end Kolmogorov
