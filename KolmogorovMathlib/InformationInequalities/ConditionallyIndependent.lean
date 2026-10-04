import KolmogorovMathlib.InformationInequalities.Ingleton
import KolmogorovMathlib.InformationInequalities.ArtificialIndependence
import KolmogorovMathlib.Entropy.Inequalities
import KolmogorovMathlib.InformationInequalities.NonShannon

/-!
# Conditionally independent random variables

SUV Section 10.12, pp. 342–343.

`α` and `β` are independent given `γ` when `I(α : β | γ) = 0`, equivalently when for every
value of `γ` of positive probability the conditional distributions of `α` and `β` are
independent (Problem 301).  Abusing the terminology, the book calls `α` and `β`
*conditionally independent* when, on the same space or a refinement of it, there are `γ` and
`δ` with `γ, δ` independent and `α, β` independent both given `γ` and given `δ`.  Three terms
of the right-hand side of Ingleton's inequality then vanish, and Romashchenko's example
(Theorem 217) has a positive left-hand side: Ingleton's inequality is false for random
variables.

As the book notes, conditional independence of `α` and `β` depends only on their joint
distribution.  `IsConditionallyIndependent` therefore asks for *some* finite space carrying a
pair with the same joint distribution together with the auxiliary `γ, δ`; this covers the
book's "the same probability space or its more fine-grained version".
-/

namespace Kolmogorov

open Finset

section

variable {Ω : Type} [Fintype Ω] {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The event `{Z = c}` as a finite set of outcomes: the condition of the conditional
distributions of Problem 301.  SUV Problem 301, p. 342. -/
def valueEvent (Z : Ω → γ) (c : γ) : Finset Ω := Finset.univ.filter fun ω => Z ω = c

private noncomputable def condMutualInfoGiven (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (E : Finset Ω) : ℝ :=
  condEntropyGiven μ X E + condEntropyGiven μ Y E - condEntropyGiven μ (pairRV X Y) E

private lemma condMutualInfo_eq_sum_given (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) :
    condMutualInfo μ X Y Z =
      ∑ c ∈ rangeFinset Z, μ.dist Z c * condMutualInfoGiven μ X Y (valueEvent Z c) := by
  simp only [condMutualInfo, condEntropy, condMutualInfoGiven, valueEvent, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

private lemma condMutualInfoGiven_nonneg (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (E : Finset Ω) :
    0 ≤ condMutualInfoGiven μ X Y E := by
  by_cases hE : 0 < μ.probOf E
  · rw [condMutualInfoGiven, ← μ.entropy_condSpace hE,
      ← μ.entropy_condSpace hE, ← μ.entropy_condSpace hE]
    linarith [entropy_pairRV_le_add (μ.condSpace E hE) X Y]
  · have hE0 : μ.probOf E = 0 := le_antisymm (not_lt.mp hE) (μ.probOf_nonneg E)
    simp [condMutualInfoGiven, condEntropyGiven, FiniteProbSpace.condDist, hE0,
      negMulLog2_zero]

private lemma condMutualInfoGiven_eq_zero_iff (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (E : Finset Ω) (hE : 0 < μ.probOf E) :
    condMutualInfoGiven μ X Y E = 0 ↔
      ∀ a b, μ.condDist (pairRV X Y) E (a, b) = μ.condDist X E a * μ.condDist Y E b := by
  rw [condMutualInfoGiven, ← μ.entropy_condSpace hE, ← μ.entropy_condSpace hE,
    ← μ.entropy_condSpace hE]
  have hcrit := independent_iff_entropy_pairRV_eq_add (μ.condSpace E hE) X Y
  constructor
  · intro hzero a b
    have hind : Independent (μ.condSpace E hE) X Y := hcrit.mpr (by linarith)
    simpa only [μ.dist_condSpace hE] using hind a b
  · intro hind
    have hind' : Independent (μ.condSpace E hE) X Y := by
      intro a b
      simpa only [μ.dist_condSpace hE] using hind a b
    linarith [hcrit.mp hind']

/-- **Problem 301.**  `I(α : β | γ) = 0` if and only if for every value `c` of `γ` that has
non-zero probability, the conditional distributions of `α` and `β` given `γ = c` are
independent: the conditional distribution of the pair is the product of the conditional
distributions.  SUV Problem 301, p. 342. -/
theorem condMutualInfo_eq_zero_iff (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) :
    condMutualInfo μ X Y Z = 0 ↔
      ∀ c, 0 < μ.dist Z c → ∀ a b,
        μ.condDist (pairRV X Y) (valueEvent Z c) (a, b)
          = μ.condDist X (valueEvent Z c) a * μ.condDist Y (valueEvent Z c) b := by
  rw [condMutualInfo_eq_sum_given]
  constructor
  · intro hsum c hc a b
    have hc_mem : c ∈ rangeFinset Z := by
      by_contra hc_not_mem
      rw [μ.dist_eq_zero_of_not_mem_range hc_not_mem] at hc
      exact (lt_irrefl 0) hc
    have hnonneg : ∀ d ∈ rangeFinset Z,
        0 ≤ μ.dist Z d * condMutualInfoGiven μ X Y (valueEvent Z d) := by
      intro d _
      exact mul_nonneg (μ.dist_nonneg Z d)
        (condMutualInfoGiven_nonneg μ X Y _)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum c hc_mem
    have hlocal : condMutualInfoGiven μ X Y (valueEvent Z c) = 0 :=
      (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hc)
    exact (condMutualInfoGiven_eq_zero_iff μ X Y _
      (by simpa [valueEvent, FiniteProbSpace.dist] using hc)).mp hlocal a b
  · intro hlocal
    have hnonneg : ∀ c ∈ rangeFinset Z,
        0 ≤ μ.dist Z c * condMutualInfoGiven μ X Y (valueEvent Z c) := by
      intro c _
      exact mul_nonneg (μ.dist_nonneg Z c)
        (condMutualInfoGiven_nonneg μ X Y _)
    apply (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mpr
    intro c hc_mem
    by_cases hc : 0 < μ.dist Z c
    · rw [(condMutualInfoGiven_eq_zero_iff μ X Y _
        (by simpa [valueEvent, FiniteProbSpace.dist] using hc)).mpr (hlocal c hc), mul_zero]
    · have hzero : μ.dist Z c = 0 := le_antisymm (not_lt.mp hc) (μ.dist_nonneg Z c)
      rw [hzero, zero_mul]

/-- Two random variables are **conditionally independent** (in the book's sense) when some
finite probability space carries a pair with the same joint distribution together with two
random variables `γ, δ` such that `γ` and `δ` are independent, and the pair is independent
given `γ` and given `δ`.  SUV Section 10.12, p. 342. -/
def IsConditionallyIndependent (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) : Prop :=
  ∃ (m : ℕ) (ν : FiniteProbSpace (Fin m)) (X' : Fin m → α) (Y' : Fin m → β)
    (G D : Fin m → ℕ),
    (∀ a b, ν.dist (pairRV X' Y') (a, b) = μ.dist (pairRV X Y) (a, b)) ∧
      Independent ν G D ∧ condMutualInfo ν X' Y' G = 0 ∧ condMutualInfo ν X' Y' D = 0

end

private def romashchenkoG (i : Fin 16) : ℕ := i.val / 8

private def romashchenkoD (i : Fin 16) : ℕ := i.val / 4 % 2

private def romashchenkoX (i : Fin 16) : ℕ := i.val / 2 % 2

private def romashchenkoY (i : Fin 16) : ℕ := i.val % 2

private noncomputable def romashchenkoSpace : FiniteProbSpace (Fin 16) where
  prob i :=
    if romashchenkoG i = romashchenkoD i then
      if romashchenkoX i = romashchenkoG i ∧ romashchenkoY i = romashchenkoG i
        then 1 / 4 else 0
    else if romashchenkoX i = romashchenkoY i then 1 / 32 else 3 / 32
  prob_nonneg i := by
    split_ifs <;> norm_num
  sum_prob := by
    norm_num [Fin.sum_univ_succ, romashchenkoG, romashchenkoD, romashchenkoX,
      romashchenkoY]

private lemma romashchenko_auxiliaries_independent :
    Independent romashchenkoSpace romashchenkoG romashchenkoD := by
  have hG : rangeFinset romashchenkoG = {0, 1} := by
    decide
  have hD : rangeFinset romashchenkoD = {0, 1} := by
    decide
  intro a b
  by_cases ha : a ∈ rangeFinset romashchenkoG
  · by_cases hb : b ∈ rangeFinset romashchenkoD
    · rw [hG] at ha
      rw [hD] at hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp only [FiniteProbSpace.dist, FiniteProbSpace.probOf, pairRV,
          Finset.sum_filter] <;>
        norm_num [romashchenkoSpace, romashchenkoG, romashchenkoD,
          romashchenkoX, romashchenkoY, Finset.sum_filter, Fin.sum_univ_succ]
    · rw [romashchenkoSpace.dist_eq_zero_of_not_mem_range hb, mul_zero]
      apply romashchenkoSpace.dist_eq_zero_of_not_mem_range
      intro hab
      obtain ⟨ω, hω⟩ := mem_rangeFinset.mp hab
      exact hb (mem_rangeFinset.mpr ⟨ω, congrArg Prod.snd hω⟩)
  · rw [romashchenkoSpace.dist_eq_zero_of_not_mem_range ha, zero_mul]
    apply romashchenkoSpace.dist_eq_zero_of_not_mem_range
    intro hab
    obtain ⟨ω, hω⟩ := mem_rangeFinset.mp hab
    exact ha (mem_rangeFinset.mpr ⟨ω, congrArg Prod.fst hω⟩)
/-- Romashchenko's weights multiplied by `32`, as natural numbers. -/
private def romashchenkoCount (i : Fin 16) : ℕ :=
  if romashchenkoG i = romashchenkoD i then
    if romashchenkoX i = romashchenkoG i ∧ romashchenkoY i = romashchenkoG i then 8 else 0
  else if romashchenkoX i = romashchenkoY i then 1 else 3

private lemma romashchenkoSpace_probOf (E : Finset (Fin 16)) :
    romashchenkoSpace.probOf E = ((∑ i ∈ E, romashchenkoCount i : ℕ) : ℝ) / 32 := by
  rw [FiniteProbSpace.probOf, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [romashchenkoSpace, romashchenkoCount]
  split_ifs <;> norm_num

/-- On Romashchenko's space, a product identity between conditional distributions follows from
the corresponding identity between integer weight counts. -/
private lemma romashchenko_condDist_mul_of_counts {α β : Type} [DecidableEq α] [DecidableEq β]
    (X : Fin 16 → α) (Y : Fin 16 → β) (E : Finset (Fin 16)) (a : α) (b : β)
    (h : (∑ i ∈ E.filter (fun ω => pairRV X Y ω = (a, b)), romashchenkoCount i) *
        ∑ i ∈ E, romashchenkoCount i =
      (∑ i ∈ E.filter (fun ω => X ω = a), romashchenkoCount i) *
        ∑ i ∈ E.filter (fun ω => Y ω = b), romashchenkoCount i) :
    romashchenkoSpace.condDist (pairRV X Y) E (a, b) =
      romashchenkoSpace.condDist X E a * romashchenkoSpace.condDist Y E b := by
  simp only [FiniteProbSpace.condDist, romashchenkoSpace_probOf]
  generalize ∑ i ∈ E.filter (fun ω => pairRV X Y ω = (a, b)), romashchenkoCount i = p at h ⊢
  generalize ∑ i ∈ E.filter (fun ω => X ω = a), romashchenkoCount i = x at h ⊢
  generalize ∑ i ∈ E.filter (fun ω => Y ω = b), romashchenkoCount i = y at h ⊢
  generalize ∑ i ∈ E, romashchenkoCount i = e at h ⊢
  have hR : (p : ℝ) * e = x * y := by exact_mod_cast h
  by_cases he : (e : ℝ) = 0
  · simp [he]
  · field_simp
    linear_combination hR

/-- The weight-count identities behind the conditional independence of `X` and `Y` given `Z`:
for every value `c` of `Z` and all bits `a`, `b`. -/
private def RomashchenkoCountsFactor (Z : Fin 16 → ℕ) : Prop :=
  ∀ c a b : Fin 2,
    (∑ i ∈ (valueEvent Z (c : ℕ)).filter
        (fun ω => pairRV romashchenkoX romashchenkoY ω = ((a : ℕ), (b : ℕ))),
        romashchenkoCount i) * ∑ i ∈ valueEvent Z (c : ℕ), romashchenkoCount i =
      (∑ i ∈ (valueEvent Z (c : ℕ)).filter (fun ω => romashchenkoX ω = a),
          romashchenkoCount i) *
        ∑ i ∈ (valueEvent Z (c : ℕ)).filter (fun ω => romashchenkoY ω = b),
          romashchenkoCount i

private instance (Z : Fin 16 → ℕ) : Decidable (RomashchenkoCountsFactor Z) := by
  unfold RomashchenkoCountsFactor
  infer_instance

/-- A bit-valued `Z` whose weight counts factor makes `X` and `Y` independent given `Z`. -/
private lemma romashchenko_condMutualInfo_eq_zero {Z : Fin 16 → ℕ} (hZ : ∀ i, Z i < 2)
    (hcounts : RomashchenkoCountsFactor Z) :
    condMutualInfo romashchenkoSpace romashchenkoX romashchenkoY Z = 0 := by
  apply (condMutualInfo_eq_zero_iff _ _ _ _).mpr
  intro c hc a b
  have hc_lt : c < 2 := by
    by_contra hc_ge
    have hc_zero : romashchenkoSpace.dist Z c = 0 := by
      apply romashchenkoSpace.dist_eq_zero_of_not_mem_range
      rw [mem_rangeFinset]
      rintro ⟨i, rfl⟩
      exact hc_ge (hZ i)
    rw [hc_zero] at hc
    exact (lt_irrefl 0) hc
  by_cases ha : a < 2
  · by_cases hb : b < 2
    · exact romashchenko_condDist_mul_of_counts _ _ _ _ _
        (hcounts ⟨c, hc_lt⟩ ⟨a, ha⟩ ⟨b, hb⟩)
    · have hYb : b ∉ rangeFinset romashchenkoY := by
        rw [mem_rangeFinset]
        push Not
        intro i
        simp only [romashchenkoY]
        omega
      have hpair : (a, b) ∉ rangeFinset (pairRV romashchenkoX romashchenkoY) := by
        rw [mem_rangeFinset]
        push Not
        intro i hi
        exact hYb (mem_rangeFinset.mpr ⟨i, congrArg Prod.snd hi⟩)
      rw [romashchenkoSpace.condDist_eq_zero_of_not_mem_range _ hpair,
        romashchenkoSpace.condDist_eq_zero_of_not_mem_range _ hYb, mul_zero]
  · have hXa : a ∉ rangeFinset romashchenkoX := by
      rw [mem_rangeFinset]
      push Not
      intro i
      simp only [romashchenkoX]
      omega
    have hpair : (a, b) ∉ rangeFinset (pairRV romashchenkoX romashchenkoY) := by
      rw [mem_rangeFinset]
      push Not
      intro i hi
      exact hXa (mem_rangeFinset.mpr ⟨i, congrArg Prod.fst hi⟩)
    rw [romashchenkoSpace.condDist_eq_zero_of_not_mem_range _ hpair,
      romashchenkoSpace.condDist_eq_zero_of_not_mem_range _ hXa, zero_mul]

private lemma romashchenko_conditionally_independent_given_g :
    condMutualInfo romashchenkoSpace romashchenkoX romashchenkoY romashchenkoG = 0 :=
  romashchenko_condMutualInfo_eq_zero (fun i => by simp only [romashchenkoG]; omega)
    (by decide)

private lemma romashchenko_conditionally_independent_given_d :
    condMutualInfo romashchenkoSpace romashchenkoX romashchenkoY romashchenkoD = 0 :=
  romashchenko_condMutualInfo_eq_zero (fun i => by simp only [romashchenkoD]; omega)
    (by decide)

private lemma romashchenko_main_variables_not_independent :
    ¬ Independent romashchenkoSpace romashchenkoX romashchenkoY := by
  intro h
  have h00 := h 0 0
  simp only [FiniteProbSpace.dist, FiniteProbSpace.probOf, Finset.sum_filter] at h00
  norm_num [pairRV, romashchenkoSpace, romashchenkoG, romashchenkoD, romashchenkoX,
    romashchenkoY, Fin.sum_univ_succ] at h00

/-- **Theorem 217.**  There exist conditionally independent random variables that are not
independent.  Romashchenko's example: `γ, δ` independent uniform bits; if `γ = δ` then
`α = β = γ`; if `γ ≠ δ` the pair `(α, β)` has the joint distribution
`[[1/8, 3/8], [3/8, 1/8]]`.  Given any fixed value of `γ` (or of `δ`) the pair has the product
distribution `[[9/16, 3/16], [3/16, 1/16]]`, while unconditionally it is
`[[5/16, 3/16], [3/16, 5/16]]`, which is not a product.  SUV Theorem 217, p. 342. -/
theorem exists_isConditionallyIndependent_not_independent :
    ∃ (m : ℕ) (μ : FiniteProbSpace (Fin m)) (X Y : Fin m → ℕ),
      IsConditionallyIndependent μ X Y ∧ ¬ Independent μ X Y := by
  refine ⟨16, romashchenkoSpace, romashchenkoX, romashchenkoY, ?_,
    romashchenko_main_variables_not_independent⟩
  refine ⟨16, romashchenkoSpace, romashchenkoX, romashchenkoY, romashchenkoG,
    romashchenkoD, ?_⟩
  exact ⟨fun _ _ => rfl, romashchenko_auxiliaries_independent,
    romashchenko_conditionally_independent_given_g,
    romashchenko_conditionally_independent_given_d⟩

/-- Ingleton's inequality is not true for random variables: the example of Theorem 217 makes
its right-hand side `0` and its left-hand side positive.  Hence the cone generated by the
non-special extreme rays for `n = 4` (equivalently, by the book's cited computation, the cone
of the basic inequalities together with Ingleton's) is not an exact description of the
entropy region.  SUV Section 10.12, pp. 342–343 (consequence of Theorem 217). -/
private theorem eval_singleton_injective_helper {α : Type} {n : ℕ} (i : Fin n) :
    Function.Injective fun h : ↥({i} : Finset (Fin n)) → α =>
      h ⟨i, Finset.mem_singleton_self i⟩ := by
  intro h₁ h₂ hh
  funext ⟨k, hk⟩
  obtain rfl := Finset.mem_singleton.1 hk
  exact hh

private theorem entropySub_singleton_helper {Ω : Type} [Fintype Ω]
    {α : Type} [DecidableEq α] {n : ℕ} (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) (i : Fin n) :
    entropySub μ X {i} = entropy μ (X i) :=
  (entropy_eq_of_comp μ (subtuple X {i}) (X i) _
    (eval_singleton_injective_helper i) fun _ => rfl).symm

private theorem entropySub_pair_helper {Ω : Type} [Fintype Ω] {α : Type} [DecidableEq α] {n : ℕ}
    (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) (i j : Fin n) :
    entropySub μ X {i, j} = entropy μ (pairRV (X i) (X j)) := by
  rw [Finset.insert_eq, entropySub_union]
  symm
  exact entropy_eq_of_comp μ (pairRV (subtuple X {i}) (subtuple X {j})) (pairRV (X i) (X j)) _
    ((eval_singleton_injective_helper i).prodMap
      (eval_singleton_injective_helper j)) fun _ => rfl

private theorem entropySub_union_union_helper {Ω : Type} [Fintype Ω]
    {α : Type} [DecidableEq α] {n : ℕ}
    (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) (I J K : Finset (Fin n)) :
    entropySub μ X (I ∪ J ∪ K)
      = entropy μ (pairRV (pairRV (subtuple X I) (subtuple X J)) (subtuple X K)) := by
  rw [entropySub_union]
  set g : (↥(I ∪ J) → α) → (↥I → α) × (↥J → α) :=
    fun h => (fun i : ↥I => h ⟨i.1, Finset.mem_union_left J i.2⟩,
      fun j : ↥J => h ⟨j.1, Finset.mem_union_right I j.2⟩) with hg_def
  have hg : Function.Injective g := by
    intro h₁ h₂ hh
    funext i
    rcases Finset.mem_union.1 i.2 with hi | hi
    · exact congrFun (congrArg Prod.fst hh) ⟨i.1, hi⟩
    · exact congrFun (congrArg Prod.snd hh) ⟨i.1, hi⟩
  symm
  exact entropy_eq_of_comp μ (pairRV (subtuple X (I ∪ J)) (subtuple X K))
    (pairRV (pairRV (subtuple X I) (subtuple X J)) (subtuple X K)) (Prod.map g id)
    (hg.prodMap Function.injective_id) fun _ => rfl

private theorem entropySub_triple_helper {Ω : Type} [Fintype Ω] {α : Type} [DecidableEq α] {n : ℕ}
    (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) (i j k : Fin n) :
    entropySub μ X {i, j, k} = entropy μ (pairRV (pairRV (X i) (X j)) (X k)) := by
  rw [Finset.insert_eq, Finset.insert_eq, ← Finset.union_assoc, entropySub_union_union_helper]
  symm
  exact entropy_eq_of_comp μ
    (pairRV (pairRV (subtuple X {i}) (subtuple X {j})) (subtuple X {k}))
    (pairRV (pairRV (X i) (X j)) (X k)) _
    (((eval_singleton_injective_helper i).prodMap (eval_singleton_injective_helper j)).prodMap
      (eval_singleton_injective_helper k)) fun _ => rfl

private def table_ingletonForm : List (Finset (Fin 4) × ℝ) :=
  [({0, 1}, 1), ({2}, 1), ({3}, 1), ({0, 2, 3}, 1), ({1, 2, 3}, 1),
    ({0, 2}, -1), ({1, 2}, -1), ({0, 3}, -1), ({1, 3}, -1), ({2, 3}, -1)]

private lemma evalEntropy_ingletonForm_eq {Ω : Type} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (X Y G D : Ω → ℕ) :
    LinearForm.evalEntropy ingletonForm μ ![G, D, X, Y] =
      mutualInfo μ X Y - condMutualInfo μ X Y G - condMutualInfo μ X Y D - mutualInfo μ G D
      := by
  have ht : ∀ e ∈ table_ingletonForm, (e : Finset (Fin 4) × ℝ).1.Nonempty := by decide
  have heq : ingletonForm = LinearForm.ofTable table_ingletonForm := rfl
  rw [heq, LinearForm.evalEntropy, LinearForm.sum_ofTable_mul _ _ ht]
  simp only [table_ingletonForm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [entropySub_singleton_helper, entropySub_pair_helper, entropySub_triple_helper]
  simp only [condMutualInfo_eq, mutualInfo]
  have h0 : (![G, D, X, Y] 0) = G := rfl
  have h1 : (![G, D, X, Y] 1) = D := rfl
  have h2 : (![G, D, X, Y] 2) = X := rfl
  have h3 : (![G, D, X, Y] 3) = Y := rfl
  rw [h0, h1, h2, h3]
  have e0 : entropy μ (pairRV (pairRV G X) Y) = entropy μ (pairRV (pairRV X Y) G) := by
    calc
      entropy μ (pairRV (pairRV G X) Y) = entropy μ (pairRV G (pairRV X Y)) :=
        entropy_pairRV_assoc _ _ _ _
      _ = entropy μ (pairRV (pairRV X Y) G) := entropy_pairRV_comm _ _ _
  have e1 : entropy μ (pairRV (pairRV D X) Y) = entropy μ (pairRV (pairRV X Y) D) := by
    calc
      entropy μ (pairRV (pairRV D X) Y) = entropy μ (pairRV D (pairRV X Y)) :=
        entropy_pairRV_assoc _ _ _ _
      _ = entropy μ (pairRV (pairRV X Y) D) := entropy_pairRV_comm _ _ _
  have e2 : entropy μ (pairRV G X) = entropy μ (pairRV X G) := entropy_pairRV_comm _ _ _
  have e3 : entropy μ (pairRV D X) = entropy μ (pairRV X D) := entropy_pairRV_comm _ _ _
  have e4 : entropy μ (pairRV G Y) = entropy μ (pairRV Y G) := entropy_pairRV_comm _ _ _
  have e5 : entropy μ (pairRV D Y) = entropy μ (pairRV Y D) := entropy_pairRV_comm _ _ _
  rw [e0, e1, e2, e3, e4, e5]
  ring

private lemma mutualInfo_nonneg_helper {Ω α β : Type} [Fintype Ω] [DecidableEq α] [DecidableEq β]
    (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    0 ≤ mutualInfo μ X Y := by
  rw [mutualInfo]
  linarith [entropy_pairRV_le_add μ X Y]

/-- Ingleton's inequality is not true for random variables: the example of Theorem 217 makes
its right-hand side `0` and its left-hand side positive.  Hence the cone generated by the
non-special extreme rays for `n = 4` (equivalently, by the book's cited computation, the cone
of the basic inequalities together with Ingleton's) is not an exact description of the
entropy region.  SUV Section 10.12, pp. 342–343 (consequence of Theorem 217). -/
theorem not_holdsForEntropies_ingletonForm : ¬ HoldsForEntropies ingletonForm := by
  intro h
  have h_le := h (Fin 16) romashchenkoSpace
    ![romashchenkoG, romashchenkoD, romashchenkoX, romashchenkoY]
  rw [evalEntropy_ingletonForm_eq] at h_le
  have h_mut_GD : mutualInfo romashchenkoSpace romashchenkoG romashchenkoD = 0 := by
    rw [mutualInfo, (independent_iff_entropy_pairRV_eq_add _ _ _).mp
      romashchenko_auxiliaries_independent]
    ring
  have h_cond_G := romashchenko_conditionally_independent_given_g
  have h_cond_D := romashchenko_conditionally_independent_given_d
  rw [h_mut_GD, h_cond_G, h_cond_D, sub_zero, sub_zero, sub_zero] at h_le
  have h_mut_XY_pos : 0 < mutualInfo romashchenkoSpace romashchenkoX romashchenkoY := by
    by_contra h_contra
    have h_mut_XY_zero : mutualInfo romashchenkoSpace romashchenkoX romashchenkoY = 0 := by
      linarith [mutualInfo_nonneg_helper romashchenkoSpace romashchenkoX romashchenkoY,
        not_lt.mp h_contra]
    have h_indep_XY : Independent romashchenkoSpace romashchenkoX romashchenkoY := by
      apply (independent_iff_entropy_pairRV_eq_add _ _ _).mpr
      have h_unfold : mutualInfo romashchenkoSpace romashchenkoX romashchenkoY =
        entropy romashchenkoSpace romashchenkoX + entropy romashchenkoSpace romashchenkoY -
        entropy romashchenkoSpace (pairRV romashchenkoX romashchenkoY) := rfl
      rw [h_unfold] at h_mut_XY_zero
      linarith
    exact romashchenko_main_variables_not_independent h_indep_XY
  linarith

end Kolmogorov
