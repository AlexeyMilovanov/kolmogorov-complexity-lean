import KolmogorovMathlib.Entropy.Inequalities
import KolmogorovMathlib.InformationInequalities.ChanYeung
import KolmogorovMathlib.InformationInequalities.Groups
import KolmogorovMathlib.InformationInequalities.NonShannon
import KolmogorovMathlib.InformationInequalities.Subspaces
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Dimensions and Ingleton's inequality

SUV Section 10.11, pp. 337–342.

The basic inequalities `H(ξ_I) ≥ 0`, `H(ξ_I) ≤ H(ξ_J)` for `I ⊆ J`, and
`H(ξ_{I∩J}) + H(ξ_{I∪J}) ≤ H(ξ_I) + H(ξ_J)` cut out a polyhedral cone that contains the entropy
region `E`.  For `n = 2` the two coincide, for `n = 3` the region is dense in the cone
(`TwoThree.lean`), and for `n = 4` it is not even dense: the cone has "special" extreme rays,
one of which is `specialRay` below, that lie outside the closure of `E` (Theorem 218 and its
consequences, `NonShannonTheorems.lean`).

Dimensions of subspaces behave like entropies: for a subspace `Y` of a finite-dimensional
space over a finite field `F`, the restriction to `Y` of a uniformly random linear functional
has entropy `dim Y · log |F|`, and the pair of restrictions to `Y` and `Z` carries the same
information as the restriction to `Y + Z`.  So every entropy inequality is an inequality for
dimensions of sums of subspaces over a finite field (Theorem 216).  The converse fails:
Ingleton's inequality (Theorem 215) holds for subspaces but not for random variables
(Theorem 217).

Problems 294–295 (Theorem 216 over `ℝ`, `ℂ` and arbitrary fields) and Problems 299–300 (the
four-variable inequalities valid for subspaces, or for subgroups of abelian groups, are those
of Ingleton type) need machinery outside the book's scope and are archived, with their
statements, in `docs/ARCHIVED_TARGETS.md`.

Sign convention of `LinearForm`: `∑_I λ_I · (quantity of I) ≤ 0`, so the printed Ingleton
inequality `12 + 3 + 4 + 134 + 234 ≤ 13 + 23 + 14 + 24 + 34` is `ingletonForm`, the left side
minus the right side.  The book's `ξ_1, …, ξ_4` (or `H_1, …, H_4`) are the indices `0, …, 3`.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-! ### The basic inequalities for arbitrary index sets -/

section Basic

variable {Ω : Type} [Fintype Ω] {α : Type} [DecidableEq α]

/-- Monotonicity of subtuple entropy: `H(ξ_I) ≤ H(ξ_J)` for `I ⊆ J`, one of the three kinds of
basic inequality.  SUV Section 10.11, p. 338. -/
theorem entropySub_le_entropySub_of_subset (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    {I J : Finset (Fin n)} (h : I ⊆ J) : entropySub μ X I ≤ entropySub μ X J :=
  entropy_comp_le μ (subtuple X J) fun v : (↥J → α) => fun i : ↥I => v ⟨i.1, h i.2⟩

/-- `H(ξ_A, ξ_B, ξ_C) = H(ξ_{A ∪ B ∪ C})`: the triple of subtuples and the subtuple over the
union determine each other. -/
private lemma entropy_pairRV_pairRV_subtuple (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (A B C : Finset (Fin n)) :
    entropy μ (pairRV (pairRV (subtuple X A) (subtuple X B)) (subtuple X C))
      = entropySub μ X (A ∪ B ∪ C) := by
  rw [entropySub_union]
  set g : (↥(A ∪ B) → α) → (↥A → α) × (↥B → α) :=
    fun h => (fun i : ↥A => h ⟨i.1, Finset.mem_union_left B i.2⟩,
      fun j : ↥B => h ⟨j.1, Finset.mem_union_right A j.2⟩) with hg_def
  have hg : Function.Injective g := by
    intro h₁ h₂ hh
    funext i
    rcases Finset.mem_union.1 i.2 with hi | hi
    · exact congrFun (congrArg Prod.fst hh) ⟨i.1, hi⟩
    · exact congrFun (congrArg Prod.snd hh) ⟨i.1, hi⟩
  have hcomp : pairRV (pairRV (subtuple X A) (subtuple X B)) (subtuple X C)
      = Prod.map g id ∘ pairRV (subtuple X (A ∪ B)) (subtuple X C) := rfl
  rw [hcomp, entropy_comp_of_injective μ _ (hg.prodMap Function.injective_id)]

/-- Submodularity of subtuple entropy for arbitrary index sets:
`H(ξ_{I∩J}) + H(ξ_{I∪J}) ≤ H(ξ_I) + H(ξ_J)`.  The printed basic inequality
`H(ξ₁) + H(ξ₁, ξ₂, ξ₃) ≤ H(ξ₁, ξ₂) + H(ξ₁, ξ₃)` is the case `I = {1, 2}`, `J = {1, 3}`, and the
general case reduces to it by grouping variables.  SUV Section 10.11, p. 338. -/
theorem entropySub_inter_add_entropySub_union_le (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (I J : Finset (Fin n)) :
    entropySub μ X (I ∩ J) + entropySub μ X (I ∪ J) ≤ entropySub μ X I + entropySub μ X J := by
  have h := entropy_triple_add_entropy_le_add_entropy_pair μ (subtuple X I) (subtuple X J)
    (subtuple X (I ∩ J))
  rw [entropy_pairRV_pairRV_subtuple, ← entropySub_union μ X I (I ∩ J),
    ← entropySub_union μ X J (I ∩ J), Finset.union_eq_left.2 Finset.inter_subset_left,
    Finset.union_eq_left.2 Finset.inter_subset_right,
    Finset.union_eq_left.2 Finset.inter_subset_union] at h
  have e : entropySub μ X (I ∩ J) = entropy μ (subtuple X (I ∩ J)) := rfl
  linarith

/-- The indicator coefficient at `T` picks out `H(ξ_T)` from the sum over non-empty sets; for
`T = ∅` both sides vanish. -/
private lemma sum_ite_mul_entropySub (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (T : Finset (Fin n)) :
    ∑ S ∈ nonemptyParts n, (if S = T then (1 : ℝ) else 0) * entropySub μ X S
      = entropySub μ X T := by
  by_cases hT : T.Nonempty
  · simp [ite_mul, Finset.sum_ite_eq', hT]
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.1 hT
    simp [ite_mul, Finset.sum_ite_eq', hT]

/-- A basic inequality holds for entropies: submodularity for the sets `I ∪ K` and `J ∪ K`,
together with monotonicity from `K` to their intersection. -/
private lemma evalEntropy_basicInequality_nonpos (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (I J K : Finset (Fin n)) : (basicInequality n I J K).evalEntropy μ X ≤ 0 := by
  have hsub := entropySub_inter_add_entropySub_union_le μ X (I ∪ K) (J ∪ K)
  have hmono := entropySub_le_entropySub_of_subset μ X
    (Finset.subset_inter (Finset.subset_union_right : K ⊆ I ∪ K)
      (Finset.subset_union_right : K ⊆ J ∪ K))
  have hU : I ∪ K ∪ (J ∪ K) = I ∪ J ∪ K := by
    ext x; simp only [Finset.mem_union]; tauto
  rw [hU] at hsub
  simp only [LinearForm.evalEntropy, basicInequality, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_ite_mul_entropySub]
  linarith

/-- A monotonicity form holds for entropies. -/
private lemma evalEntropy_monotonicityForm_nonpos (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (I J : Finset (Fin n)) : (monotonicityForm n I J).evalEntropy μ X ≤ 0 := by
  have hmono := entropySub_le_entropySub_of_subset μ X (Finset.subset_union_left : I ⊆ I ∪ J)
  simp only [LinearForm.evalEntropy, monotonicityForm, sub_mul, Finset.sum_sub_distrib,
    sum_ite_mul_entropySub]
  linarith

end Basic

/-- The entropy region is contained in the cone cut out by the basic inequalities.
SUV Section 10.11, p. 338. -/
theorem entropyRegion_subset_basicCone (n : ℕ) : entropyRegion n ⊆ basicCone n := by
  rintro v ⟨m, μ, X, rfl⟩
  exact ⟨entropySub_empty μ X, fun I => entropySub_nonneg μ X I,
    fun I J h => entropySub_le_entropySub_of_subset μ X h,
    fun I J => entropySub_inter_add_entropySub_union_le μ X I J⟩

/-- Every Shannon-type form — a non-negative combination of basic inequalities — is valid for
entropies.  SUV Section 10.11, p. 338. -/
theorem holdsForEntropies_of_isShannonType (f : LinearForm n) (h : IsShannonType f) :
    HoldsForEntropies f := by
  obtain ⟨m, g, c, hc, hg, hf⟩ := h
  intro Ω _ μ X
  have hgen : ∀ k, (g k).evalEntropy μ X ≤ 0 := by
    intro k
    rcases hg k with ⟨I, J, K, hk⟩ | ⟨I, J, hk⟩
    · rw [hk]; exact evalEntropy_basicInequality_nonpos μ X I J K
    · rw [hk]; exact evalEntropy_monotonicityForm_nonpos μ X I J
  have hsplit : f.evalEntropy μ X = ∑ k, c k * (g k).evalEntropy μ X := by
    simp only [LinearForm.evalEntropy, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [hf I (mem_nonemptyParts.1 hI), Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit]
  exact Finset.sum_nonpos fun k _ => mul_nonpos_iff.2 (Or.inl ⟨hc k, hgen k⟩)

/-! ### The special extreme ray for four variables -/

/-- The "special" extreme ray of the cone of basic inequalities for four variables, at
parameter `1`: `H(ξ_i) = 2` for every `i`, `H(ξ₁, ξ₂) = 4`, the other five pairs `3`, and all
triples and the quadruple `4`.  All special rays are this one up to renaming the variables.
The book writes the ray with a scale parameter it calls `n`.  SUV Section 10.11, p. 338. -/
def specialRay : Finset (Fin 4) → ℝ :=
  LinearForm.ofTable
    [({0}, 2), ({1}, 2), ({2}, 2), ({3}, 2), ({0, 1}, 4),
      ({0, 2}, 3), ({0, 3}, 3), ({1, 2}, 3), ({1, 3}, 3), ({2, 3}, 3),
      ({0, 1, 2}, 4), ({0, 1, 3}, 4), ({0, 2, 3}, 4), ({1, 2, 3}, 4), ({0, 1, 2, 3}, 4)]

/-- Every subset of `Fin 4` is one of the sixteen listed ones; this is how a statement about
all coordinates of a four-variable form is reduced to sixteen computations. -/
private lemma finset_fin4_cases (S : Finset (Fin 4)) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {3} ∨ S = {0, 1} ∨ S = {0, 2} ∨ S = {0, 3} ∨
      S = {1, 2} ∨ S = {1, 3} ∨ S = {2, 3} ∨ S = {0, 1, 2} ∨ S = {0, 1, 3} ∨ S = {0, 2, 3} ∨
      S = {1, 2, 3} ∨ S = {0, 1, 2, 3} := by
  revert S; decide

/-- The special ray as a `ℕ`-valued function given by a closed formula, so that the basic
inequalities for it can be checked by `decide`. -/
private def specialRayNat (S : Finset (Fin 4)) : ℕ :=
  if S = ∅ then 0 else if S = {0, 1} then 4 else min 4 (S.card + 1)

/-- The table `specialRay` and the formula `specialRayNat` agree. -/
private lemma specialRay_apply (S : Finset (Fin 4)) : specialRay S = specialRayNat S := by
  rcases finset_fin4_cases S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide [specialRay, LinearForm.ofTable, specialRayNat]

/-- The special ray satisfies all basic inequalities.  SUV Section 10.11, p. 338; used in
Section 10.13, p. 344. -/
theorem specialRay_mem_basicCone : specialRay ∈ basicCone 4 := by
  have hmono : ∀ I J : Finset (Fin 4), I ⊆ J → specialRayNat I ≤ specialRayNat J := by decide
  have hsub : ∀ I J : Finset (Fin 4),
      specialRayNat (I ∩ J) + specialRayNat (I ∪ J) ≤ specialRayNat I + specialRayNat J := by
    decide
  refine ⟨?_, fun I => ?_, fun I J h => ?_, fun I J => ?_⟩
  · simp [specialRay_apply, specialRayNat]
  · rw [specialRay_apply]; exact Nat.cast_nonneg _
  · rw [specialRay_apply, specialRay_apply]; exact_mod_cast hmono I J h
  · simp only [specialRay_apply]; exact_mod_cast hsub I J

/-- The special ray is an extreme ray of the cone of basic inequalities for four variables: if
it is the sum of two points of the cone, both are non-negative multiples of it.  The book
cites the enumeration of the extreme rays from its reference [64] without proof.
SUV Section 10.11, p. 338 (cited). -/
theorem specialRay_isExtreme {v w : Finset (Fin 4) → ℝ} (hv : v ∈ basicCone 4)
    (hw : w ∈ basicCone 4) (hsum : v + w = specialRay) :
    ∃ t : ℝ, 0 ≤ t ∧ v = t • specialRay := by
  obtain ⟨hvE, hv0, hvm, hvs⟩ := hv
  obtain ⟨-, -, hwm, hws⟩ := hw
  have hs : ∀ I, v I + w I = (specialRayNat I : ℝ) := fun I => by
    rw [← specialRay_apply]; exact congrFun hsum I
  -- a monotonicity inequality that is tight on the special ray is tight on `v`
  have tm : ∀ I J : Finset (Fin 4), I ⊆ J → specialRayNat I = specialRayNat J → v I = v J := by
    intro I J hIJ hIJ'
    have h1 := hvm I J hIJ
    have h2 := hwm I J hIJ
    have h3 := hs I
    have h4 := hs J
    rw [hIJ'] at h3
    linarith
  -- a submodularity inequality that is tight on the special ray is tight on `v`
  have ts : ∀ I J K L : Finset (Fin 4), I ∩ J = K → I ∪ J = L →
      specialRayNat K + specialRayNat L = specialRayNat I + specialRayNat J →
      v K + v L = v I + v J := by
    intro I J K L hK hL hIJ
    subst hK hL
    have h1 := hvs I J
    have h2 := hws I J
    have h3 := hs (I ∩ J)
    have h4 := hs (I ∪ J)
    have h5 := hs I
    have h6 := hs J
    have h7 : (specialRayNat (I ∩ J) : ℝ) + specialRayNat (I ∪ J)
        = specialRayNat I + specialRayNat J := by exact_mod_cast hIJ
    linarith
  have e012 := tm {0, 1, 2} {0, 1, 2, 3} (by decide) (by decide)
  have e013 := tm {0, 1, 3} {0, 1, 2, 3} (by decide) (by decide)
  have e023 := tm {0, 2, 3} {0, 1, 2, 3} (by decide) (by decide)
  have e123 := tm {1, 2, 3} {0, 1, 2, 3} (by decide) (by decide)
  have e01 := tm {0, 1} {0, 1, 2} (by decide) (by decide)
  have s01 := ts {0} {1} (∅) {0, 1} (by decide) (by decide) (by decide)
  have s02 := ts {0, 2} {1, 2} {2} {0, 1, 2} (by decide) (by decide) (by decide)
  have s03 := ts {0, 2} {2, 3} {2} {0, 2, 3} (by decide) (by decide) (by decide)
  have s04 := ts {1, 2} {2, 3} {2} {1, 2, 3} (by decide) (by decide) (by decide)
  have s05 := ts {0, 3} {1, 3} {3} {0, 1, 3} (by decide) (by decide) (by decide)
  have s06 := ts {0, 3} {2, 3} {3} {0, 2, 3} (by decide) (by decide) (by decide)
  have s07 := ts {1, 3} {2, 3} {3} {1, 2, 3} (by decide) (by decide) (by decide)
  have s08 := ts {0, 2} {0, 3} {0} {0, 2, 3} (by decide) (by decide) (by decide)
  have s09 := ts {1, 2} {1, 3} {1} {1, 2, 3} (by decide) (by decide) (by decide)
  refine ⟨v {0, 1, 2, 3} / 4, by linarith [hv0 {0, 1, 2, 3}], ?_⟩
  funext I
  rw [Pi.smul_apply, smul_eq_mul, specialRay_apply]
  rcases finset_fin4_cases I with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide [specialRayNat] <;>
  linarith

/-! ### Ingleton's inequality and dimensions -/

/-- **Theorem 215 (Ingleton's inequality).**  For finite-dimensional subspaces `H₁, H₂, H₃, H₄`
of a vector space over any field,
`dim(H₁+H₂) + dim H₃ + dim H₄ + dim(H₁+H₃+H₄) + dim(H₂+H₃+H₄)`
`≤ dim(H₁+H₃) + dim(H₂+H₃) + dim(H₁+H₄) + dim(H₂+H₄) + dim(H₃+H₄)`.
Equivalently `ingletonForm.evalDim ![H₁, H₂, H₃, H₄] ≤ 0`.  The book's proof works over a finite
field and reduces other fields to it; Problem 297 asks for a proof over an arbitrary field, which
is the statement here.  SUV Theorem 215, p. 339; Problem 297, p. 341. -/
theorem ingleton_finrank {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (H₁ H₂ H₃ H₄ : Submodule F V) [FiniteDimensional F H₁] [FiniteDimensional F H₂]
    [FiniteDimensional F H₃] [FiniteDimensional F H₄] :
    Module.finrank F ↥(H₁ ⊔ H₂) + Module.finrank F H₃ + Module.finrank F H₄
        + Module.finrank F ↥(H₁ ⊔ H₃ ⊔ H₄) + Module.finrank F ↥(H₂ ⊔ H₃ ⊔ H₄)
      ≤ Module.finrank F ↥(H₁ ⊔ H₃) + Module.finrank F ↥(H₂ ⊔ H₃)
        + Module.finrank F ↥(H₁ ⊔ H₄) + Module.finrank F ↥(H₂ ⊔ H₄)
        + Module.finrank F ↥(H₃ ⊔ H₄) := by
  -- `W = H₃ ⊓ H₄` plays the part of the common information of `ξ₃` and `ξ₄`
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq H₃ H₄
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq (H₃ ⊓ H₄ ⊔ H₁) (H₃ ⊓ H₄ ⊔ H₂)
  have e3 := Submodule.finrank_sup_add_finrank_inf_eq (H₁ ⊔ H₃) (H₁ ⊔ H₄)
  have e4 := Submodule.finrank_sup_add_finrank_inf_eq (H₂ ⊔ H₃) (H₂ ⊔ H₄)
  -- the dimension form of `H(ξ) ≤ H(ξ|γ) + H(ξ|δ) + I(γ:δ)` for `ξ = W`
  have m2a : Module.finrank F ↥(H₁ ⊔ H₂)
      ≤ Module.finrank F ↥(H₃ ⊓ H₄ ⊔ H₁ ⊔ (H₃ ⊓ H₄ ⊔ H₂)) :=
    Submodule.finrank_mono
      (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right))
  have m2b : Module.finrank F ↥(H₃ ⊓ H₄)
      ≤ Module.finrank F ↥((H₃ ⊓ H₄ ⊔ H₁) ⊓ (H₃ ⊓ H₄ ⊔ H₂)) :=
    Submodule.finrank_mono (le_inf le_sup_left le_sup_left)
  -- `dim X/C ≤ I(A:B|C)`: the image of `W` lies in the intersection of the images
  have m3a : Module.finrank F ↥(H₁ ⊔ H₃ ⊔ H₄)
      ≤ Module.finrank F ↥(H₁ ⊔ H₃ ⊔ (H₁ ⊔ H₄)) :=
    Submodule.finrank_mono (sup_le le_sup_left (le_sup_right.trans le_sup_right))
  have m3b : Module.finrank F ↥(H₃ ⊓ H₄ ⊔ H₁)
      ≤ Module.finrank F ↥((H₁ ⊔ H₃) ⊓ (H₁ ⊔ H₄)) :=
    Submodule.finrank_mono (sup_le
      (le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans le_sup_right))
      (le_inf le_sup_left le_sup_left))
  have m4a : Module.finrank F ↥(H₂ ⊔ H₃ ⊔ H₄)
      ≤ Module.finrank F ↥(H₂ ⊔ H₃ ⊔ (H₂ ⊔ H₄)) :=
    Submodule.finrank_mono (sup_le le_sup_left (le_sup_right.trans le_sup_right))
  have m4b : Module.finrank F ↥(H₃ ⊓ H₄ ⊔ H₂)
      ≤ Module.finrank F ↥((H₂ ⊔ H₃) ⊓ (H₂ ⊔ H₄)) :=
    Submodule.finrank_mono (sup_le
      (le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans le_sup_right))
      (le_inf le_sup_left le_sup_left))
  omega

section Dimensions

variable {F U : Type} [Field F] [Finite F] [AddCommGroup U] [Module F U] [FiniteDimensional F U]

/-- The annihilator of a subspace `S` of `U`: the functionals vanishing on `S`, as a subgroup
of the dual space of `U` written multiplicatively.  The restriction to `S` of a functional is
determined by its coset modulo this subgroup, which is the dictionary of p. 339. -/
private def annihilatorSubgroup (S : Submodule F U) :
    Subgroup (Multiplicative (Module.Dual F U)) :=
  AddSubgroup.toSubgroup S.dualAnnihilator.toAddSubgroup

omit [Finite F] [FiniteDimensional F U] in
/-- Membership in the annihilator subgroup is membership in the annihilator. -/
private lemma mem_annihilatorSubgroup (S : Submodule F U)
    (φ : Multiplicative (Module.Dual F U)) :
    φ ∈ annihilatorSubgroup S ↔ Multiplicative.toAdd φ ∈ S.dualAnnihilator := Iff.rfl

omit [Finite F] [FiniteDimensional F U] in
/-- The intersection of the annihilators of the `W i`, `i ∈ I`, annihilates their sum. -/
private lemma subgroupMeet_annihilatorSubgroup (W : Fin n → Submodule F U)
    (I : Finset (Fin n)) :
    subgroupMeet (fun i => annihilatorSubgroup (W i)) I
      = annihilatorSubgroup (subspaceSum W I) := by
  ext φ
  simp only [subgroupMeet, Subgroup.mem_iInf, mem_annihilatorSubgroup, subspaceSum,
    Submodule.dualAnnihilator_iSup_eq, Submodule.mem_iInf]

/-- `|F|^{dim U} / |ann S| = |F|^{dim S}`: the index of the annihilator of `S` counts the
restrictions to `S` of the functionals on `U`. -/
private lemma card_div_card_annihilatorSubgroup (S : Submodule F U) :
    (Nat.card (Multiplicative (Module.Dual F U)) : ℝ) / Nat.card (annihilatorSubgroup S)
      = (Nat.card F : ℝ) ^ Module.finrank F S := by
  have hcard : Nat.card (annihilatorSubgroup S) = Nat.card S.dualAnnihilator := rfl
  have hdual : Nat.card (Multiplicative (Module.Dual F U)) = Nat.card (Module.Dual F U) := rfl
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  rw [hcard, hdual, Module.natCard_eq_pow_finrank (K := F) (V := Module.Dual F U),
    Module.natCard_eq_pow_finrank (K := F) (V := S.dualAnnihilator), Subspace.dual_finrank_eq,
    div_eq_iff (by exact_mod_cast (pow_pos Nat.card_pos _).ne')]
  push_cast
  rw [← pow_add, h1]

/-- Theorem 216 for subspaces of a finite-dimensional space, through the group dictionary:
the dual space with the annihilator subgroups realises the dimension dictionary, every index
being `|F|^{dim}`, so the value of the form on the indices is `log₂ |F|` times its value on the
dimensions.  The dual space is abelian, so validity for finite abelian groups suffices.
SUV Theorem 216, p. 340. -/
private lemma evalDim_nonpos_of_forall_evalGroupIndex_abelian_nonpos (f : LinearForm n)
    (h : ∀ (G : Type) [CommGroup G] [Finite G] (H : Fin n → Subgroup G), f.evalGroupIndex H ≤ 0)
    (W : Fin n → Submodule F U) : f.evalDim W ≤ 0 := by
  have : Finite (Module.Dual F U) := Module.finite_of_finite F
  have hG := h (Multiplicative (Module.Dual F U)) fun i => annihilatorSubgroup (W i)
  have hq : (1 : ℝ) < Nat.card F := by
    exact_mod_cast Finite.one_lt_card_iff_nontrivial.2 inferInstance
  have hL : 0 < Real.logb 2 (Nat.card F) := Real.logb_pos (by norm_num) hq
  have key : f.evalGroupIndex (fun i => annihilatorSubgroup (W i))
      = Real.logb 2 (Nat.card F) * f.evalDim W := by
    unfold LinearForm.evalGroupIndex LinearForm.evalDim
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [subgroupMeet_annihilatorSubgroup, card_div_card_annihilatorSubgroup, Real.logb_pow]
    ring
  rw [key] at hG
  have h0 : Real.logb 2 (Nat.card F) * f.evalDim W ≤ Real.logb 2 (Nat.card F) * 0 := by
    simpa using hG
  exact le_of_mul_le_mul_left h0 hL

end Dimensions

/-- A form valid for the indices of subgroups of every finite abelian group is valid for
dimensions of finite-dimensional subspaces over every finite field: the sum of the subspaces is
finite-dimensional and its dual space is a finite abelian group. -/
private lemma holdsForSubspaces_of_forall_evalGroupIndex_abelian_nonpos (f : LinearForm n)
    (hG : ∀ (G : Type) [CommGroup G] [Finite G] (H : Fin n → Subgroup G),
      f.evalGroupIndex H ≤ 0) : HoldsForSubspaces f := by
  intro F _ _ V _ _ W _
  -- `U`, the sum of all the `W i`, is finite-dimensional; the `W i` are subspaces of it
  set U : Submodule F V := ⨆ i, W i with hU
  have hle : ∀ i, W i ≤ U := fun i => le_iSup W i
  have hmap : ∀ I, (subspaceSum (fun i => (W i).comap U.subtype) I).map U.subtype
      = subspaceSum W I := by
    intro I
    simp only [subspaceSum, Submodule.map_iSup, Submodule.map_comap_subtype,
      inf_eq_right.2 (hle _)]
  have hrank : ∀ I, Module.finrank F (subspaceSum (fun i => (W i).comap U.subtype) I)
      = Module.finrank F (subspaceSum W I) := by
    intro I; rw [← hmap I, Submodule.finrank_map_subtype_eq]
  have := evalDim_nonpos_of_forall_evalGroupIndex_abelian_nonpos f hG
    fun i => (W i).comap U.subtype
  unfold LinearForm.evalDim at this ⊢
  simpa only [hrank] using this

/-- **Theorem 216.**  Every linear inequality that is true for entropies of random variables
and their tuples is true for dimensions of finite-dimensional subspaces of a vector space over
a finite field, when the entropy of a tuple is replaced by the dimension of the sum of the
corresponding subspaces.  SUV Theorem 216, p. 340. -/
theorem holdsForSubspaces_of_holdsForEntropies (f : LinearForm n) (h : HoldsForEntropies f) :
    HoldsForSubspaces f :=
  holdsForSubspaces_of_forall_evalGroupIndex_abelian_nonpos f fun G _ _ H =>
    (holdsForEntropies_iff_holdsForGroups f).1 h G H

/-! ### Problems 296–298 -/

/-- **Problem 296.**  For all random variables `ξ, γ, δ`:
`H(ξ) ≤ H(ξ | γ) + H(ξ | δ) + I(γ : δ)`.  It is a sum of basic inequalities, via the identity
`H(ξ) + H(ξ | γ, δ) + I(γ : δ | ξ) = H(ξ | γ) + H(ξ | δ) + I(γ : δ)`.
SUV Problem 296, p. 341. -/
theorem entropy_le_condEntropy_add_condEntropy_add_mutualInfo {Ω : Type} [Fintype Ω]
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (μ : FiniteProbSpace Ω) (X : Ω → α) (G : Ω → β) (D : Ω → γ) :
    entropy μ X ≤ condEntropy μ X G + condEntropy μ X D + mutualInfo μ G D := by
  have h145 := entropy_triple_add_entropy_le_add_entropy_pair μ G D X
  have hmono : entropy μ (pairRV G D) ≤ entropy μ (pairRV (pairRV G D) X) :=
    entropy_comp_le μ (pairRV (pairRV G D) X) Prod.fst
  have hXG := entropy_pairRV_eq_add_condEntropy μ X G
  have hXD := entropy_pairRV_eq_add_condEntropy μ X D
  have hswapG := entropy_comp_of_injective μ (pairRV X G) Prod.swap_injective
  have hswapD := entropy_comp_of_injective μ (pairRV X D) Prod.swap_injective
  have eG : Prod.swap ∘ pairRV X G = pairRV G X := by funext ω; rfl
  have eD : Prod.swap ∘ pairRV X D = pairRV D X := by funext ω; rfl
  rw [eG] at hswapG
  rw [eD] at hswapD
  unfold mutualInfo
  linarith

/-- Evaluating a table form against a quantity `q` sums the table's entries weighted by `q` at
their sets, provided every listed set is non-empty: `∑_{I ≠ ∅} (ofTable t) I · q I = ∑_{(I, c) ∈ t}
c · q I`.  This is how a concrete inequality of Chapter 10 is unfolded into its terms. -/
theorem LinearForm.sum_ofTable_mul (t : List (Finset (Fin n) × ℝ)) (q : Finset (Fin n) → ℝ)
    (ht : ∀ e ∈ t, e.1.Nonempty) :
    ∑ I ∈ nonemptyParts n, LinearForm.ofTable t I * q I = (t.map fun e => e.2 * q e.1).sum := by
  induction t with
  | nil => simp [LinearForm.ofTable]
  | cons e t ih =>
    have ht' : ∀ e ∈ t, e.1.Nonempty := fun e he => ht e (List.mem_cons_of_mem _ he)
    have hsplit : ∀ I, LinearForm.ofTable (e :: t) I
        = (if e.1 = I then e.2 else 0) + LinearForm.ofTable t I := by
      intro I
      simp only [LinearForm.ofTable, List.filter_cons]
      split_ifs with h <;> simp_all
    have he : e.1 ∈ nonemptyParts n := mem_nonemptyParts.2 (ht e (List.mem_cons_self ..))
    simp only [hsplit, add_mul, Finset.sum_add_distrib, ih ht', List.map_cons, List.sum_cons,
      ite_mul, zero_mul, Finset.sum_ite_eq, ite_eq_left he]

section Groups

variable {G : Type} [Group G] [Finite G]

/-- In the group dictionary `|G| / |K|` is the index of `K`. -/
private lemma card_div_card_eq_index (K : Subgroup G) :
    (Nat.card G : ℝ) / Nat.card K = K.index := by
  have h := K.card_mul_index
  have hpos : (0 : ℝ) < Nat.card K := by exact_mod_cast Nat.card_pos
  rw [div_eq_iff hpos.ne', mul_comm]
  exact_mod_cast h.symm

/-- The index of a subgroup of a finite group is positive. -/
private lemma index_pos_real (K : Subgroup G) : (0 : ℝ) < K.index := by
  exact_mod_cast Nat.pos_of_ne_zero K.index_ne_zero_of_finite

/-- The log-index is antitone: a larger subgroup has a smaller index. -/
private lemma logb_index_le_of_le {K L : Subgroup G} (h : K ≤ L) :
    Real.logb 2 L.index ≤ Real.logb 2 K.index := by
  have hle : L.index ≤ K.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero K.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le h)
  exact Real.logb_le_logb_of_le (by norm_num) (index_pos_real L) (by exact_mod_cast hle)

/-- The modular law for indices of subgroups of a finite abelian group:
`[G : K ⊔ L] · [G : K ⊓ L] = [G : K] · [G : L]`.  This is the group form of
`dim (Y + Z) + dim (Y ∩ Z) = dim Y + dim Z`; it uses that `K ⊔ L` is the product `K L`, i.e.
that every subgroup is normal.  SUV Problem 298 (hint), p. 341. -/
private lemma index_sup_mul_index_inf {G : Type} [CommGroup G] [Finite G] (K L : Subgroup G) :
    (K ⊔ L).index * (K ⊓ L).index = K.index * L.index := by
  have h1 := Subgroup.relIndex_mul_index (le_sup_right : L ≤ K ⊔ L)
  have h2 := Subgroup.relIndex_mul_index (inf_le_left : K ⊓ L ≤ K)
  rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_sup_right] at h2
  rw [← h1, ← h2]
  ring

/-- The modular law for log-indices in a finite abelian group. -/
private lemma logb_index_sup_add_logb_index_inf {G : Type} [CommGroup G] [Finite G]
    (K L : Subgroup G) :
    Real.logb 2 (K ⊔ L).index + Real.logb 2 (K ⊓ L).index
      = Real.logb 2 K.index + Real.logb 2 L.index := by
  rw [← Real.logb_mul (index_pos_real _).ne' (index_pos_real _).ne',
    ← Real.logb_mul (index_pos_real _).ne' (index_pos_real _).ne']
  congr 1
  exact_mod_cast index_sup_mul_index_inf K L

end Groups

/-- **Problem 298.**  Under the translation `H(ξ_I) ↦ log₂ (|G| / |G_I|)`, `G_I` the
intersection of the `G_i` with `i ∈ I`, Ingleton's inequality is true for subgroups of a
finite abelian group.  SUV Problem 298, p. 341. -/
theorem ingletonForm_evalGroupIndex_nonpos {G : Type} [CommGroup G] [Finite G]
    (H : Fin 4 → Subgroup G) : ingletonForm.evalGroupIndex H ≤ 0 := by
  simp only [LinearForm.evalGroupIndex, card_div_card_eq_index]
  rw [ingletonForm, LinearForm.sum_ofTable_mul _ _ (by decide)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, subgroupMeet,
    Finset.iInf_insert, Finset.iInf_singleton]
  set a := H 0
  set b := H 1
  set c := H 2
  set d := H 3
  -- `W = c ⊔ d` is the sum of the two subgroups, the common information of `ξ₃` and `ξ₄`
  have e1 := logb_index_sup_add_logb_index_inf c d
  have e2 := logb_index_sup_add_logb_index_inf ((c ⊔ d) ⊓ a) ((c ⊔ d) ⊓ b)
  have e3 := logb_index_sup_add_logb_index_inf (a ⊓ c) (a ⊓ d)
  have e4 := logb_index_sup_add_logb_index_inf (b ⊓ c) (b ⊓ d)
  have m2a := logb_index_le_of_le (G := G)
    (sup_le inf_le_left inf_le_left : ((c ⊔ d) ⊓ a) ⊔ ((c ⊔ d) ⊓ b) ≤ c ⊔ d)
  have m2b := logb_index_le_of_le (G := G)
    (inf_le_inf inf_le_right inf_le_right : ((c ⊔ d) ⊓ a) ⊓ ((c ⊔ d) ⊓ b) ≤ a ⊓ b)
  have m3a := logb_index_le_of_le (G := G)
    (sup_le (le_inf (inf_le_right.trans le_sup_left) inf_le_left)
      (le_inf (inf_le_right.trans le_sup_right) inf_le_left) : (a ⊓ c) ⊔ (a ⊓ d) ≤ (c ⊔ d) ⊓ a)
  have m3b := logb_index_le_of_le (G := G)
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_inf inf_le_right inf_le_right) :
      (a ⊓ c) ⊓ (a ⊓ d) ≤ a ⊓ (c ⊓ d))
  have m4a := logb_index_le_of_le (G := G)
    (sup_le (le_inf (inf_le_right.trans le_sup_left) inf_le_left)
      (le_inf (inf_le_right.trans le_sup_right) inf_le_left) : (b ⊓ c) ⊔ (b ⊓ d) ≤ (c ⊔ d) ⊓ b)
  have m4b := logb_index_le_of_le (G := G)
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_inf inf_le_right inf_le_right) :
      (b ⊓ c) ⊓ (b ⊓ d) ≤ b ⊓ (c ⊓ d))
  linarith

end Kolmogorov
