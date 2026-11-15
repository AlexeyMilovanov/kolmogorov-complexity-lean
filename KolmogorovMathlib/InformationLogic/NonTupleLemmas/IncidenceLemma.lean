import KolmogorovMathlib.InformationLogic.NonTupleComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry
import KolmogorovMathlib.Complexity.Information.MutualInformation
import KolmogorovMathlib.Complexity.EnumerableFamilies.CountingBounds
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Incidence Lemma

The incidence lemma used in the construction of non-tuple complexity profiles: for a finite
field `F` with `2ⁿ` elements, lines `a` of the affine space `F³` with a chosen point `f a ∈ a`
and a chosen plane `g a ⊇ a`, the number of pairs `(a, b)` with `f a ∈ b` and `a ⊆ g b` is
`O(2^{5.5n})`.

The main declarations are `AffLine` and `AffPlane` (lines and planes of `F³`) and
`incidence_pairs_card_sq_le`, which states the bound as `|S|² ≤ C · 2^{11n}`.  The proof is a
double counting argument with the Cauchy–Schwarz inequality, as in the book by Shen, Uspensky
and Vereshchagin ("Kolmogorov complexity and algorithmic randomness"), in the part on
non-tuple (information-logic) inequalities.
-/

namespace Kolmogorov
namespace InformationLogic

open ProblemCalculus

/-- Lines of the affine space `F³`: affine subspaces with one-dimensional direction. -/
def AffLine (F : Type*) [Field F] : Type _ :=
  {L : AffineSubspace F (Fin 3 → F) // Module.finrank F L.direction = 1}

/-- Planes of the affine space `F³`: affine subspaces with two-dimensional direction. -/
def AffPlane (F : Type*) [Field F] : Type _ :=
  {L : AffineSubspace F (Fin 3 → F) // Module.finrank F L.direction = 2}

/-- Auxiliary for `incidence_pairs_card_sq_le`: pointwise `x_i² ≤ A y_i²` gives
`(Σ x_i)² ≤ A (Σ y_i)²`. -/
private lemma incidence_pairs_card_sq_le_agg {ι : Type} [Fintype ι] (x y : ι → ℕ) (A : ℕ)
    (h : ∀ i, x i ^ 2 ≤ A * y i ^ 2) : (∑ i, x i) ^ 2 ≤ A * (∑ i, y i) ^ 2 := by
  have hp : ∀ i j, x i * x j ≤ A * (y i * y j) := by
    intro i j
    have h1 : (x i * x j) ^ 2 ≤ (A * (y i * y j)) ^ 2 := by
      calc (x i * x j) ^ 2 = x i ^ 2 * x j ^ 2 := by ring
        _ ≤ (A * y i ^ 2) * (A * y j ^ 2) := Nat.mul_le_mul (h i) (h j)
        _ = (A * (y i * y j)) ^ 2 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h1
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => hp i j

/-- Auxiliary for `incidence_pairs_card_sq_le`: `ncard` of a set-builder set in a fintype. -/
private lemma incidence_pairs_card_sq_le_ncard_eq_card {α : Type} [Fintype α] (P : α → Prop)
    [DecidablePred P] : {x | P x}.ncard = (Finset.univ.filter P).card := by
  rw [Set.ncard_eq_toFinset_card']
  simp

/-- Step 1 of the proof of `incidence_pairs_card_sq_le`: the abstract combinatorial core
(Cauchy–Schwarz slice argument).  In an abstract incidence structure of lines `Ln`, planes `Pl`
and points `Pt` (all finite), with at most `q` points on a line, at most `K q` lines of a plane
through a point, at most `K q²` lines in a plane, two distinct lines sharing at most one point, at
most `K q⁴` lines and `K q³` planes, the set of pairs `(a, b)` with `f a ∈ b` and `a ⊆ g b` (for
`f a ∈ a`) satisfies `|S|² ≤ 4 K⁴ q^{11}`.  Proof: slice by `d = g b`; with
`A_c = {a ⊆ d | f a = c}`, `B_c = {b | g b = d, c ∈ b}`, `|slice| = Σ_c |A_c||B_c|`, so
`|slice|² ≤ (Σ|A_c|²)(Σ|B_c|²)`; `Σ|A_c|² ≤ K q · K q²`, `Σ|B_c|² ≤ q m + m² ≤ (m + q)²` with
`m = |{b | g b = d}|`; then `|slice| ≤ K q^{3/2} (m + q)` (pairwise, via `x_d x_d' ≤ A y_d y_d'`
from squares), summing over `d`: `Σ (m_d + q) = |Ln| + q |Pl| ≤ 2 K q⁴`. -/
private theorem incidence_pairs_card_sq_le_core {Ln Pl Pt : Type} [Finite Ln] [Finite Pl]
    [Finite Pt] (q K : ℕ) (mem : Pt → Ln → Prop) (sub : Ln → Pl → Prop) (f : Ln → Pt)
    (g : Ln → Pl) (hf : ∀ a, mem (f a) a)
    (H1 : ∀ d c, {a : Ln | sub a d ∧ mem c a}.ncard ≤ K * q)
    (H2 : ∀ d, {a : Ln | sub a d}.ncard ≤ K * q ^ 2)
    (H3 : ∀ a, {c : Pt | mem c a}.ncard ≤ q)
    (H4 : ∀ a b : Ln, a ≠ b → {c : Pt | mem c a ∧ mem c b}.ncard ≤ 1)
    (H5 : Nat.card Ln ≤ K * q ^ 4) (H6 : Nat.card Pl ≤ K * q ^ 3) :
    ({p : Ln × Ln | mem (f p.1) p.2 ∧ sub p.1 (g p.2)}.ncard) ^ 2 ≤ 4 * K ^ 4 * q ^ 11 := by
  classical
  have := Fintype.ofFinite Ln
  have := Fintype.ofFinite Pl
  have := Fintype.ofFinite Pt
  simp only [incidence_pairs_card_sq_le_ncard_eq_card] at H1 H2 H3 H4
  rw [Nat.card_eq_fintype_card] at H5 H6
  rw [incidence_pairs_card_sq_le_ncard_eq_card]
  set M : Pl → Finset Ln := fun d => Finset.univ.filter (fun b => g b = d) with hM
  set α : Pl → Pt → ℕ := fun d c => (Finset.univ.filter fun a => sub a d ∧ f a = c).card with hα
  set β : Pl → Pt → ℕ := fun d c => (Finset.univ.filter fun b => g b = d ∧ mem c b).card with hβ
  set slice : Pl → ℕ := fun d =>
    ((Finset.univ.filter fun p : Ln × Ln => mem (f p.1) p.2 ∧ sub p.1 (g p.2)).filter
      fun p => g p.2 = d).card with hslice
  have hS : (Finset.univ.filter fun p : Ln × Ln => mem (f p.1) p.2 ∧ sub p.1 (g p.2)).card
      = ∑ d, slice d := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Ln × Ln => g p.2) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  have hsl : ∀ d, slice d = ∑ c, α d c * β d c := by
    intro d
    have e1 : slice d = ∑ a, if sub a d then β d (f a) else 0 := by
      simp only [hslice, Finset.filter_filter, Finset.card_filter]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : sub a d
      · simp only [ha, ite_true, hβ, Finset.card_filter]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb : g b = d
        · subst hb; simp [ha]
        · simp [hb]
      · simp only [ha, ite_false]
        refine Finset.sum_eq_zero fun b _ => ?_
        by_cases hb : g b = d
        · subst hb; simp [ha]
        · simp [hb]
    rw [e1, ← Finset.sum_fiberwise Finset.univ f]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.1 ha).2])]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Finset.filter_filter]
    simp only [hα]
    congr 2
    ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have hA : ∀ d c, α d c ≤ K * q := by
    intro d c
    refine le_trans (Finset.card_le_card ?_) (H1 d c)
    intro a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h, rfl⟩; exact ⟨h, hf a⟩
  have hAsum : ∀ d, ∑ c, α d c ≤ K * q ^ 2 := by
    intro d
    have : (Finset.univ.filter fun a => sub a d).card = ∑ c, α d c := by
      rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      simp only [hα, Finset.filter_filter]
    rw [← this]; exact H2 d
  have hAsq : ∀ d, ∑ c, α d c ^ 2 ≤ K ^ 2 * q ^ 3 := by
    intro d
    calc ∑ c, α d c ^ 2 ≤ ∑ c, (K * q) * α d c := Finset.sum_le_sum fun c _ => by
          rw [sq]; exact Nat.mul_le_mul_right _ (hA d c)
      _ = (K * q) * ∑ c, α d c := by rw [Finset.mul_sum]
      _ ≤ (K * q) * (K * q ^ 2) := Nat.mul_le_mul_left _ (hAsum d)
      _ = K ^ 2 * q ^ 3 := by ring
  have hB : ∀ d, ∑ c, β d c ^ 2 ≤ (M d).card * q + (M d).card ^ 2 := by
    intro d
    have e : ∀ c, β d c = ∑ b ∈ M d, if mem c b then 1 else 0 := by
      intro c
      simp only [hβ, hM]
      rw [Finset.card_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases h1 : g b = d <;> by_cases h2 : mem c b <;> simp [h1, h2]
    calc ∑ c, β d c ^ 2
        = ∑ c, ∑ b ∈ M d, ∑ b' ∈ M d,
            (if mem c b then 1 else 0) * (if mem c b' then 1 else 0) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [sq, e c, Finset.sum_mul_sum]
      _ = ∑ b ∈ M d, ∑ b' ∈ M d, ∑ c,
            (if mem c b then 1 else 0) * (if mem c b' then 1 else 0) := by
          refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ => ?_)
          exact Finset.sum_comm
      _ ≤ ∑ b ∈ M d, ∑ b' ∈ M d, ((if b = b' then q else 0) + 1) := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => ?_
          have : ∑ c, (if mem c b then 1 else 0) * (if mem c b' then 1 else 0)
              = (Finset.univ.filter fun c => mem c b ∧ mem c b').card := by
            rw [Finset.card_filter]
            refine Finset.sum_congr rfl fun c _ => ?_
            by_cases h1 : mem c b <;> by_cases h2 : mem c b' <;> simp [h1, h2]
          rw [this]
          by_cases h : b = b'
          · subst h
            simp only [ite_true, and_self]
            have := H3 b
            omega
          · simp only [h, ite_false, zero_add]
            exact H4 b b' h
      _ = (M d).card * q + (M d).card ^ 2 := by
          have : ∀ b ∈ M d, ∑ b' ∈ M d, ((if b = b' then q else 0) + 1) = q + (M d).card := by
            intro b hb
            simp [Finset.sum_add_distrib, Finset.sum_ite_eq, hb]
          rw [Finset.sum_congr rfl this]
          simp only [Finset.sum_const, smul_eq_mul]
          ring
  have hx : ∀ d, slice d ^ 2 ≤ (K ^ 2 * q ^ 3) * ((M d).card + q) ^ 2 := by
    intro d
    rw [hsl d]
    calc (∑ c, α d c * β d c) ^ 2 ≤ (∑ c, α d c ^ 2) * (∑ c, β d c ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (K ^ 2 * q ^ 3) * ((M d).card * q + (M d).card ^ 2) :=
          Nat.mul_le_mul (hAsq d) (hB d)
      _ ≤ (K ^ 2 * q ^ 3) * ((M d).card + q) ^ 2 := by
          refine Nat.mul_le_mul_left _ ?_
          generalize (M d).card = m
          nlinarith [Nat.zero_le (q * q), Nat.zero_le (m * q)]
  have hMsum : ∑ d, (M d).card = Fintype.card Ln := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  have hag := incidence_pairs_card_sq_le_agg slice (fun d => (M d).card + q) (K ^ 2 * q ^ 3) hx
  rw [← hS] at hag
  have hY : ∑ d, ((M d).card + q) ≤ 2 * K * q ^ 4 := by
    rw [Finset.sum_add_distrib, hMsum]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have : Fintype.card Pl * q ≤ K * q ^ 4 := by
      calc Fintype.card Pl * q ≤ (K * q ^ 3) * q := Nat.mul_le_mul_right _ H6
        _ = K * q ^ 4 := by ring
    linarith
  calc _ ≤ _ := hag
    _ ≤ (K ^ 2 * q ^ 3) * (2 * K * q ^ 4) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hY 2)
    _ = 4 * K ^ 4 * q ^ 11 := by ring

/-- Step 2 of the proof of `incidence_pairs_card_sq_le`: a line of `F³` has at most `|F|`
points (in fact exactly `|F|`: it is `p + F v`). -/
private theorem incidence_pairs_card_sq_le_line_points (F : Type) [Field F] [Fintype F]
    (a : AffLine F) : {c : Fin 3 → F | c ∈ a.1}.ncard ≤ Fintype.card F := by
  by_cases h : ∃ p, p ∈ a.1
  · obtain ⟨p, hp⟩ := h
    have hcard : Nat.card (a.1.direction : Set (Fin 3 → F)) = Fintype.card F := by
      have := Module.natCard_eq_pow_finrank (K := F) (V := a.1.direction)
      rw [a.2, pow_one] at this
      simpa [Nat.card_eq_fintype_card] using this
    calc {c : Fin 3 → F | c ∈ a.1}.ncard
        ≤ (a.1.direction : Set (Fin 3 → F)).ncard := by
          refine Set.ncard_le_ncard_of_injOn (fun c => c - p) ?_ ?_ (Set.toFinite _)
          · intro c hc
            exact AffineSubspace.vsub_mem_direction hc hp
          · intro x _ y _ hxy
            simpa using hxy
      _ = Fintype.card F := by rw [← Nat.card_coe_set_eq]; exact hcard
  · have : {c : Fin 3 → F | c ∈ a.1} = ∅ := by
      ext c; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hc => h ⟨c, hc⟩
    rw [this]; simp

/-- Step 3 of the proof of `incidence_pairs_card_sq_le`: two distinct lines of `F³`
have at most one common point. -/
private theorem incidence_pairs_card_sq_le_lines_meet (F : Type) [Field F] [Finite F]
    (a b : AffLine F) (hab : a ≠ b) :
    {c : Fin 3 → F | c ∈ a.1 ∧ c ∈ b.1}.ncard ≤ 1 := by
  have : Finite {c : Fin 3 → F | c ∈ a.1 ∧ c ∈ b.1} := Set.toFinite _
  rw [Set.ncard_le_one_iff_subsingleton]
  intro x hx y hy
  by_contra hne
  apply hab
  have hv : y -ᵥ x ≠ 0 := by
    intro h
    rw [vsub_eq_sub, sub_eq_zero] at h
    exact hne h.symm
  have hva : y -ᵥ x ∈ a.1.direction := AffineSubspace.vsub_mem_direction hy.1 hx.1
  have hvb : y -ᵥ x ∈ b.1.direction := AffineSubspace.vsub_mem_direction hy.2 hx.2
  have h1 : Module.finrank F (F ∙ (y -ᵥ x)) = 1 := finrank_span_singleton hv
  have hda : F ∙ (y -ᵥ x) = a.1.direction :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hva)
      (by rw [h1, a.2])
  have hdb : F ∙ (y -ᵥ x) = b.1.direction :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hvb)
      (by rw [h1, b.2])
  exact Subtype.ext (AffineSubspace.ext_of_direction_eq (hda.symm.trans hdb)
    ⟨x, hx.1, hx.2⟩)

/-- Step 4 of the proof of `incidence_pairs_card_sq_le`: through a point `c` of `F³`
pass at most `|F| + 1` lines contained in a given plane `d` (exactly `|F| + 1` if `c ∈ d`, none
otherwise). -/
private theorem incidence_pairs_card_sq_le_plane_point_lines (F : Type) [Field F]
    [Fintype F] (d : AffPlane F) (c : Fin 3 → F) :
    {a : AffLine F | a.1 ≤ d.1 ∧ c ∈ a.1}.ncard ≤ Fintype.card F + 1 := by
  set V : Submodule F (Fin 3 → F) := d.1.direction with hV
  have hle : ∀ a : AffLine F, a.1 ≤ d.1 → a.1.direction ≤ V :=
    fun a h => AffineSubspace.direction_le h
  let t : Set (Submodule F V) := {H | Module.finrank F H = 1}
  have hcard : t.ncard = Fintype.card F + 1 := by
    have h1 := Projectivization.card_of_finrank_two F V d.2
    rw [Nat.card_congr (Projectivization.equivSubmodule F V)] at h1
    rw [Nat.card_eq_fintype_card (α := F)] at h1
    rw [← h1, ← Nat.card_coe_set_eq]
    rfl
  rw [← hcard]
  refine Set.ncard_le_ncard_of_injOn (fun a => a.1.direction.comap V.subtype) ?_ ?_
    (Set.toFinite _)
  · rintro a ⟨ha, -⟩
    change Module.finrank F (a.1.direction.comap V.subtype) = 1
    exact (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (hle a ha))).trans a.2
  · rintro a ⟨ha, hca⟩ b ⟨hb, hcb⟩ hab
    refine Subtype.ext (AffineSubspace.ext_of_direction_eq ?_ ⟨c, hca, hcb⟩)
    have h1 := hle a ha
    have h2 := hle b hb
    have := congrArg (Submodule.map V.subtype) hab
    simp only [Submodule.map_comap_subtype, inf_of_le_right h1, inf_of_le_right h2] at this
    exact this

/-- Auxiliary for step 5: an affine subspace of `F³` with `k`-dimensional direction and a point has
exactly `|F|ᵏ` points. -/
private lemma incidence_pairs_card_sq_le_plane_lines_aux_ncard (F : Type) [Field F]
    [Fintype F] (s : AffineSubspace F (Fin 3 → F)) (k : ℕ) (hk : Module.finrank F s.direction = k)
    (p : Fin 3 → F) (hp : p ∈ s) : {c : Fin 3 → F | c ∈ s}.ncard = Fintype.card F ^ k := by
  have hcard : Nat.card (s.direction : Set (Fin 3 → F)) = Fintype.card F ^ k := by
    have := Module.natCard_eq_pow_finrank (K := F) (V := s.direction)
    rw [hk] at this
    simpa [Nat.card_eq_fintype_card] using this
  rw [← hcard, Nat.card_coe_set_eq]
  apply le_antisymm
  · refine Set.ncard_le_ncard_of_injOn (fun c => c - p) ?_ ?_ (Set.toFinite _)
    · intro c hc
      exact AffineSubspace.vsub_mem_direction hc hp
    · intro x _ y _ hxy
      simpa using hxy
  · refine Set.ncard_le_ncard_of_injOn (fun v => v + p) ?_ ?_ (Set.toFinite _)
    · intro v hv
      exact AffineSubspace.vadd_mem_of_mem_direction hv hp
    · intro x _ y _ hxy
      simpa using hxy

/-- Auxiliary for step 5: a subspace whose direction has positive finrank is nonempty. -/
private lemma incidence_pairs_card_sq_le_plane_lines_aux_nonempty (F : Type) [Field F]
    (s : AffineSubspace F (Fin 3 → F)) (k : ℕ) (hk : Module.finrank F s.direction = k + 1) :
    ∃ p, p ∈ s := by
  by_contra h
  have : s = ⊥ := by
    rw [← AffineSubspace.coe_eq_bot_iff, Set.eq_empty_iff_forall_notMem]
    exact fun p hp => h ⟨p, hp⟩
  subst this
  rw [AffineSubspace.direction_bot] at hk
  simp at hk

/-- Step 5 of the proof of `incidence_pairs_card_sq_le`: a plane `d` of `F³` contains at
most `|F|² + |F| + 1` lines (exactly that many). -/
private theorem incidence_pairs_card_sq_le_plane_lines (F : Type) [Field F] [Fintype F]
    (d : AffPlane F) :
    {a : AffLine F | a.1 ≤ d.1}.ncard ≤ Fintype.card F ^ 2 + Fintype.card F + 1 := by
  classical
  have : Finite (AffLine F) :=
    Finite.of_injective (fun L : AffLine F => (L.1 : Set (Fin 3 → F)))
      (fun L L' h => Subtype.ext (SetLike.coe_injective h))
  have := Fintype.ofFinite (AffLine F)
  have hq : 0 < Fintype.card F := Fintype.card_pos
  obtain ⟨p, hp⟩ := incidence_pairs_card_sq_le_plane_lines_aux_nonempty F d.1 1 d.2
  have hd := incidence_pairs_card_sq_le_plane_lines_aux_ncard F d.1 2 d.2 p hp
  set s : Finset (AffLine F) := Finset.univ.filter (fun a => a.1 ≤ d.1) with hs
  set t : Finset (Fin 3 → F) := Finset.univ.filter (fun c => c ∈ d.1) with ht
  have hdc : t.card = Fintype.card F ^ 2 := by
    rw [← hd, incidence_pairs_card_sq_le_ncard_eq_card]
  have hS : {a : AffLine F | a.1 ≤ d.1}.ncard = s.card :=
    incidence_pairs_card_sq_le_ncard_eq_card _
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := s) (t := t) (fun (a : AffLine F) (c : Fin 3 → F) => c ∈ a.1)
  have hlow : ∀ a ∈ s, (t.bipartiteAbove (fun (a : AffLine F) (c : Fin 3 → F) => c ∈ a.1) a).card
      = Fintype.card F := by
    intro a ha
    obtain ⟨p', hp'⟩ := incidence_pairs_card_sq_le_plane_lines_aux_nonempty F a.1 0 a.2
    have := incidence_pairs_card_sq_le_plane_lines_aux_ncard F a.1 1 a.2 p' hp'
    rw [pow_one, incidence_pairs_card_sq_le_ncard_eq_card] at this
    rw [← this]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.bipartiteAbove, ht]
    have ha' : a.1 ≤ d.1 := by simpa [hs] using ha
    exact ⟨fun h => h.2, fun h => ⟨ha' h, h⟩⟩
  have hup : ∀ c ∈ t, (s.bipartiteBelow (fun (a : AffLine F) (c : Fin 3 → F) => c ∈ a.1) c).card
      ≤ Fintype.card F + 1 := by
    intro c _
    have := incidence_pairs_card_sq_le_plane_point_lines F d c
    rw [incidence_pairs_card_sq_le_ncard_eq_card] at this
    refine le_trans (le_of_eq ?_) this
    congr 1
    ext a
    simp [Finset.bipartiteBelow, hs]
  have h1 : ∑ a ∈ s, (t.bipartiteAbove (fun (a : AffLine F) (c : Fin 3 → F) => c ∈ a.1) a).card
      = s.card * Fintype.card F := by
    rw [Finset.sum_congr rfl hlow]; simp
  have h2 : ∑ c ∈ t, (s.bipartiteBelow (fun (a : AffLine F) (c : Fin 3 → F) => c ∈ a.1) c).card
      ≤ Fintype.card F ^ 2 * (Fintype.card F + 1) := by
    calc _ ≤ ∑ c ∈ t, (Fintype.card F + 1) := Finset.sum_le_sum hup
      _ = _ := by rw [Finset.sum_const, hdc, smul_eq_mul]
  rw [h1] at key
  rw [hS]
  have h3 : s.card * Fintype.card F ≤ (Fintype.card F * (Fintype.card F + 1)) * Fintype.card F := by
    calc _ ≤ _ := key ▸ h2
      _ = _ := by ring
  have := Nat.le_of_mul_le_mul_right h3 hq
  nlinarith

/-- Auxiliary for step 6: a line of `F³` has exactly `|F|` points. -/
private theorem incidence_pairs_card_sq_le_card_lines_aux_pts (F : Type) [Field F]
    [Fintype F] (L : AffLine F) : Nat.card {c : Fin 3 → F // c ∈ L.1} = Fintype.card F := by
  have hne : (L.1 : Set (Fin 3 → F)).Nonempty := by
    rcases AffineSubspace.eq_bot_or_nonempty L.1 with h | h
    · have := L.2
      rw [h, AffineSubspace.direction_bot] at this
      simp at this
    · exact h
  obtain ⟨p, hp⟩ := hne
  have hcard : Nat.card L.1.direction = Fintype.card F := by
    have := Module.natCard_eq_pow_finrank (K := F) (V := L.1.direction)
    rw [L.2, pow_one] at this
    simpa [Nat.card_eq_fintype_card] using this
  rw [← hcard]
  refine Nat.card_congr
    { toFun := fun c => ⟨c.1 - p, AffineSubspace.vsub_mem_direction c.2 hp⟩
      invFun := fun v => ⟨v.1 + p, AffineSubspace.vadd_mem_of_mem_direction v.2 hp⟩
      left_inv := fun c => by ext; simp
      right_inv := fun v => by ext; simp }

/-- Auxiliary for step 6: a line of `F³` has exactly `|F| - 1` nonzero direction vectors. -/
private theorem incidence_pairs_card_sq_le_card_lines_aux_dir (F : Type) [Field F]
    [Fintype F] (L : AffLine F) :
    Nat.card {v : L.1.direction // v ≠ 0} = Fintype.card F - 1 := by
  classical
  have hcard : Nat.card L.1.direction = Fintype.card F := by
    have := Module.natCard_eq_pow_finrank (K := F) (V := L.1.direction)
    rw [L.2, pow_one] at this
    simpa [Nat.card_eq_fintype_card] using this
  have : Finite L.1.direction :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Fintype.card_ne_zero)
  have := Fintype.ofFinite L.1.direction
  rw [Nat.card_eq_fintype_card] at hcard ⊢
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard]

/-- Step 6 of the proof of `incidence_pairs_card_sq_le`: `F³` has at most
`|F|² (|F|² + |F| + 1)` lines (exactly that many: `|F|² + |F| + 1` directions, `|F|²` parallel
lines for each). -/
private theorem incidence_pairs_card_sq_le_card_lines (F : Type) [Field F] [Fintype F] :
    Nat.card (AffLine F) ≤ Fintype.card F ^ 2 * (Fintype.card F ^ 2 + Fintype.card F + 1) := by
  classical
  have : Finite (AffLine F) :=
    Finite.of_injective (fun L : AffLine F => (L.1 : Set (Fin 3 → F)))
      (fun L L' h => Subtype.ext (SetLike.coe_injective h))
  have := Fintype.ofFinite (AffLine F)
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  let T := Σ L : AffLine F, {c : Fin 3 → F // c ∈ L.1} × {v : L.1.direction // v ≠ 0}
  have hinj : Function.Injective (fun t : T =>
      ((t.2.1.1, ⟨t.2.2.1.1, fun h => t.2.2.2 (Subtype.ext h)⟩) :
        (Fin 3 → F) × {v : Fin 3 → F // v ≠ 0})) := by
    rintro ⟨L, ⟨p, hp⟩, ⟨v, hv⟩⟩ ⟨L', ⟨p', hp'⟩, ⟨v', hv'⟩⟩ h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨rfl, hvv⟩ := h
    have hvv' : (v : Fin 3 → F) = v' := hvv
    have hdir : ∀ (M M' : AffLine F) (w : M.1.direction) (w' : M'.1.direction),
        (w : Fin 3 → F) = w' → w ≠ 0 → M.1.direction ≤ M'.1.direction := by
      intro M M' w w' hww hw0 x hx
      have h1 := (finrank_eq_one_iff_of_nonzero' w hw0).1 M.2 ⟨x, hx⟩
      obtain ⟨c, hc⟩ := h1
      have hx' : x = c • (w : Fin 3 → F) := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      rw [hx', hww]
      exact M'.1.direction.smul_mem c w'.2
    have hd1 := hdir L L' v v' hvv' hv
    have hd2 := hdir L' L v' v hvv'.symm
        (fun h => hv (Subtype.ext (by simpa [hvv'] using congrArg Subtype.val h)))
    have hd : L.1.direction = L'.1.direction := le_antisymm hd1 hd2
    have hL : L = L' := by
      apply Subtype.ext
      rw [← AffineSubspace.mk'_eq hp, ← AffineSubspace.mk'_eq hp', hd]
    subst hL
    have : v = v' := Subtype.ext hvv'
    subst this
    rfl
  have hle := Nat.card_le_card_of_injective _ hinj
  have hT : Nat.card T = Nat.card (AffLine F) *
      (Fintype.card F * (Fintype.card F - 1)) := by
    rw [Nat.card_sigma]
    simp only [Nat.card_prod,
      incidence_pairs_card_sq_le_card_lines_aux_pts,
      incidence_pairs_card_sq_le_card_lines_aux_dir]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  have hR : Nat.card ((Fin 3 → F) × {v : Fin 3 → F // v ≠ 0}) =
      Fintype.card F ^ 3 * (Fintype.card F ^ 3 - 1) := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    simp
  rw [hT, hR] at hle
  generalize Fintype.card F = q at hq2 hle ⊢
  generalize Nat.card (AffLine F) = N at hle ⊢
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 2 := ⟨q - 2, by omega⟩
  have hpos : 0 < (s + 2) * (s + 2 - 1) := by
    have : s + 2 - 1 = s + 1 := by omega
    rw [this]; positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  have e : (s + 2) ^ 3 * ((s + 2) ^ 3 - 1) =
      (s + 2) ^ 2 * ((s + 2) ^ 2 + (s + 2) + 1) * ((s + 2) * (s + 2 - 1)) := by
    have h1 : s + 2 - 1 = s + 1 := by omega
    have h2 : (s + 2) ^ 3 - 1 = (s + 1) * ((s + 2) ^ 2 + (s + 2) + 1) := by
      have : (s + 2) ^ 3 = (s + 1) * ((s + 2) ^ 2 + (s + 2) + 1) + 1 := by ring
      omega
    rw [h1, h2]; ring
  rw [← e]
  exact hle

/-- Auxiliary for `incidence_pairs_card_sq_le_card_planes`: every plane of `F³` is the
solution set of a nonzero linear equation `a x₀ + b x₁ + c x₂ = d`. -/
private lemma incidence_pairs_card_sq_le_card_planes_exists_eq (F : Type) [Field F]
    (P : AffPlane F) :
    ∃ a b c d : F, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      ∀ x : Fin 3 → F, x ∈ P.1 ↔ a * x 0 + b * x 1 + c * x 2 = d := by
  obtain ⟨P, hP⟩ := P
  have hne : (P : Set (Fin 3 → F)).Nonempty := by
    rw [AffineSubspace.nonempty_iff_ne_bot]
    rintro rfl
    rw [AffineSubspace.direction_bot, finrank_bot] at hP
    omega
  obtain ⟨p, hp⟩ := hne
  have hlt : P.direction < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h, finrank_top] at hP
    simp at hP
  obtain ⟨φ, hφ0, hle⟩ := P.direction.exists_le_ker_of_lt_top hlt
  have hker : P.direction = LinearMap.ker φ := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have h1 := φ.finrank_range_add_finrank_ker
    have h2 : 0 < Module.finrank F (LinearMap.range φ) := by
      obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
        by_contra h
        push Not at h
        exact hφ0 (LinearMap.ext h)
      apply Module.finrank_pos_iff_exists_ne_zero.2
      exact ⟨⟨φ v, v, rfl⟩, fun h => hv (congrArg Subtype.val h)⟩
    simp at h1
    omega
  have hφx : ∀ x : Fin 3 → F, φ x = φ (fun j => if (0 : Fin 3) = j then 1 else 0) * x 0 +
      φ (fun j => if (1 : Fin 3) = j then 1 else 0) * x 1 +
      φ (fun j => if (2 : Fin 3) = j then 1 else 0) * x 2 := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ φ x, Fin.sum_univ_three]
    simp only [smul_eq_mul]
    ring
  refine ⟨φ (fun j => if (0 : Fin 3) = j then 1 else 0),
    φ (fun j => if (1 : Fin 3) = j then 1 else 0),
    φ (fun j => if (2 : Fin 3) = j then 1 else 0), φ p, ?_, ?_⟩
  · by_contra h
    simp only [not_or, not_not] at h
    apply hφ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply, hφx x, h.1, h.2.1, h.2.2]
    simp
  · intro x
    change x ∈ P ↔ _
    rw [← hφx x]
    have : x ∈ P ↔ x -ᵥ p ∈ P.direction := by
      constructor
      · exact fun hx => AffineSubspace.vsub_mem_direction hx hp
      · intro h
        simpa using AffineSubspace.vadd_mem_of_mem_direction h hp
    rw [this, hker, LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero]

/-- Auxiliary for `incidence_pairs_card_sq_le_card_planes`: a nonzero linear equation can
be rescaled so that its first nonzero coefficient is `1`. -/
private lemma incidence_pairs_card_sq_le_card_planes_normalize (F : Type) [Field F]
    (a b c d : F) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∃ a' b' c' d' : F, (a' = 1 ∨ (a' = 0 ∧ b' = 1) ∨ (a' = 0 ∧ b' = 0 ∧ c' = 1)) ∧
      ∀ x : Fin 3 → F, a * x 0 + b * x 1 + c * x 2 = d ↔ a' * x 0 + b' * x 1 + c' * x 2 = d' := by
  by_cases ha : a ≠ 0
  · refine ⟨1, b / a, c / a, d / a, Or.inl rfl, fun x => ?_⟩
    constructor
    · intro hx
      field_simp
      linear_combination hx
    · intro hx
      field_simp at hx
      linear_combination hx
  by_cases hb : b ≠ 0
  · have ha' : a = 0 := not_not.1 ha
    refine ⟨0, 1, c / b, d / b, Or.inr (Or.inl ⟨rfl, rfl⟩), fun x => ?_⟩
    subst ha'
    constructor
    · intro hx
      field_simp
      linear_combination hx
    · intro hx
      field_simp at hx
      linear_combination hx
  · have ha' : a = 0 := not_not.1 ha
    have hb' : b = 0 := not_not.1 hb
    have hc : c ≠ 0 := by tauto
    refine ⟨0, 0, 1, d / c, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), fun x => ?_⟩
    subst ha' hb'
    constructor
    · intro hx
      field_simp
      linear_combination hx
    · intro hx
      field_simp at hx
      linear_combination hx

/-- Step 7 of the proof of `incidence_pairs_card_sq_le`: `F³` has at most
`|F| (|F|² + |F| + 1)` planes (exactly that many: `|F|² + |F| + 1` directions, `|F|` parallel
planes for each). -/
private theorem incidence_pairs_card_sq_le_card_planes (F : Type) [Field F] [Fintype F] :
    Nat.card (AffPlane F) ≤ Fintype.card F * (Fintype.card F ^ 2 + Fintype.card F + 1) := by
  classical
  let N : Finset (F × F × F × F) :=
    (Finset.univ : Finset (F × F × F)).image (fun t => (1, t.1, t.2.1, t.2.2)) ∪
    (Finset.univ : Finset (F × F)).image (fun t => (0, 1, t.1, t.2)) ∪
    (Finset.univ : Finset F).image (fun d => (0, 0, 1, d))
  have hN : N.card ≤ Fintype.card F * (Fintype.card F ^ 2 + Fintype.card F + 1) := by
    calc N.card ≤ _ := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ Fintype.card (F × F × F) + Fintype.card (F × F) + Fintype.card F := by
          refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_ <;>
            exact Finset.card_image_le.trans (by simp)
      _ = _ := by simp only [Fintype.card_prod]; ring
  have h : ∀ P : AffPlane F, ∃ t : F × F × F × F, t ∈ N ∧
      ∀ x : Fin 3 → F, x ∈ P.1 ↔ t.1 * x 0 + t.2.1 * x 1 + t.2.2.1 * x 2 = t.2.2.2 := by
    intro P
    obtain ⟨a, b, c, d, hnz, hx⟩ := incidence_pairs_card_sq_le_card_planes_exists_eq F P
    obtain ⟨a', b', c', d', hn, hx'⟩ :=
      incidence_pairs_card_sq_le_card_planes_normalize F a b c d hnz
    refine ⟨(a', b', c', d'), ?_, fun x => (hx x).trans (hx' x)⟩
    simp only [N, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    rcases hn with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl (Or.inl ⟨(b', c', d'), rfl⟩)
    · exact Or.inl (Or.inr ⟨(c', d'), rfl⟩)
    · exact Or.inr ⟨d', rfl⟩
  choose ψ hψN hψ using h
  have hinj : Function.Injective (fun P : AffPlane F => (⟨ψ P, hψN P⟩ : N)) := by
    intro P Q hPQ
    have : ψ P = ψ Q := congrArg Subtype.val hPQ
    apply Subtype.ext
    apply SetLike.ext
    intro x
    rw [hψ P x, hψ Q x, this]
  calc Nat.card (AffPlane F) ≤ Nat.card N := Nat.card_le_card_of_injective _ hinj
    _ = N.card := by simp
    _ ≤ _ := hN

/-- SUV Theorem 247, Lemma of the geometric proof (Section 13.6, printed p. 418).  In the affine
3-space over the field with `2ⁿ` elements, let `f` map every line to a point of it and `g` map
every line to a plane containing it; then the set `S` of pairs of lines `(a, b)` with `f(a) ∈ b`
and `a ⊆ g(b)` has `O(2^{5.5n})` elements, written `|S|² ≤ C · 2^{11n}` with `C` independent
of `n`, `f`, `g`.  Pairs `a = b` are allowed, as in the book's lemma (there are only
`≈ 2^{4n}` of them).
Book's proof: split `S` into slices by the plane `d = g(b)`; in a slice,
`|slice| ≤ Σ_c |A_c| |B_c| ≤ (Σ_c |A_c|²)^{1/2} (Σ_c |B_c|²)^{1/2}` (Cauchy–Schwarz) with
`Σ_c |A_c|² = O(2^{3n})` (two random lines of `d` have the same `f`-point with probability
`O(2^{-n})`) and `Σ_c |B_c|² ≤ (|M_d| + 2ⁿ)²`; sum over the `≈ 2^{3n}` planes, `Σ_d |M_d| ≈ 2^{4n}`.
(The argument works for every finite field; the book uses cardinality `2ⁿ`.) -/
theorem incidence_pairs_card_sq_le : ∃ C : ℕ, ∀ (F : Type) [Field F] [Fintype F] (n : ℕ),
    Fintype.card F = 2 ^ n →
    ∀ (f : AffLine F → (Fin 3 → F)) (g : AffLine F → AffPlane F),
      (∀ a, f a ∈ a.1) → (∀ a, a.1 ≤ (g a).1) →
      ({p : AffLine F × AffLine F | f p.1 ∈ p.2.1 ∧ p.1.1 ≤ (g p.2).1}.ncard) ^ 2 ≤
        C * 2 ^ (11 * n) := by
  refine ⟨4 * 3 ^ 4, ?_⟩
  intro F _ _ n hcard f g hf hg
  have : Finite (AffLine F) :=
    Finite.of_injective (fun L : AffLine F => (L.1 : Set (Fin 3 → F)))
      (fun L L' h => Subtype.ext (SetLike.coe_injective h))
  have : Finite (AffPlane F) :=
    Finite.of_injective (fun L : AffPlane F => (L.1 : Set (Fin 3 → F)))
      (fun L L' h => Subtype.ext (SetLike.coe_injective h))
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have key := incidence_pairs_card_sq_le_core (Pt := Fin 3 → F) (Fintype.card F) 3
    (fun c a => c ∈ a.1) (fun a d => a.1 ≤ d.1) f g hf
    (fun d c => by
      have := incidence_pairs_card_sq_le_plane_point_lines F d c
      omega)
    (fun d => by
      have := incidence_pairs_card_sq_le_plane_lines F d
      nlinarith)
    (incidence_pairs_card_sq_le_line_points F)
    (incidence_pairs_card_sq_le_lines_meet F)
    (by
      have := incidence_pairs_card_sq_le_card_lines F
      nlinarith [pow_pos hq 3, pow_pos hq 2])
    (by
      have := incidence_pairs_card_sq_le_card_planes F
      nlinarith [pow_pos hq 2])
  rw [hcard] at key
  calc _ ≤ _ := key
    _ = 4 * 3 ^ 4 * 2 ^ (11 * n) := by rw [← pow_mul]; ring_nf

end InformationLogic
end Kolmogorov
