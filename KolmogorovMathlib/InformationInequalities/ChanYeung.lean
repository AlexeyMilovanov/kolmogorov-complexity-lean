/-
Copyright (c) 2024 Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
import KolmogorovMathlib.InformationInequalities.UniformSetsTheorems
import KolmogorovMathlib.InformationInequalities.Groups
import KolmogorovMathlib.CommonInformation.TypeBounds
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Topology.Algebra.Order.Field

/-!
# The Chan–Yeung theorems: uniform sets, orbits and subgroups

SUV Sections 10.3 and 10.4, pp. 321–324.

Theorem 206 sent entropy inequalities to inequalities for the log-sizes of the projections of
uniform sets.  Theorem 207 is the converse, and it is the harder half: given a tuple of random
variables with rational probabilities and common denominator `N`, write an `n × N` matrix
whose columns realise those probabilities and let `U` be the set of all column permutations of
it.  `U` is uniform, and by Stirling's formula `log m_U(I) = N · H(η_I) + O(log N)`; multiply
`N` by integers, divide by `N` and pass to the limit.  Arbitrary distributions follow because
rational ones are dense and entropy is continuous.

Section 10.4 identifies the source of that uniformity: the set `U` is an orbit of the
symmetric group acting on the columns, and *every* orbit of a finite group acting
coordinatewise is uniform (Theorem 208).  Since the projection of the orbit of `x` onto `I` has
size `|G| / |G_I|` with `G_I` the intersection of the stabilisers of the `x_i`, and since every
subgroup is a stabiliser, entropy inequalities and inequalities for indices of subgroups are
the same thing (Theorem 209).

The printed statement of Theorem 209 reads "every linear *equality* for the entropies …"; that
is a misprint for "inequality", as the two examples on the same page show.  The theorem is
also stated informally ("translates … and vice versa"); the precise form used here is the
equivalence `HoldsForEntropies f ↔ HoldsForGroups f` of the dictionary
`H(ξ_I) ↦ log₂ (|G| / |G_I|)`, which is what `LinearForm.evalGroupIndex` implements.

Entropies are base two throughout.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-! ### Theorem 207 -/

/-- The entropy of a distribution on a finite set depends continuously on the distribution.
This is the step that carries Theorem 207 from distributions with rational probabilities to
arbitrary ones.  SUV Section 10.3, p. 322 (unnumbered). -/
theorem continuous_entropyDist {α : Type} [Fintype α] :
    Continuous (entropyDist (α := α)) := by
  unfold entropyDist negMulLog2
  fun_prop

/-! ### Theorem 208: orbits are uniform -/

/-- The first `m` coordinates in the ordering `σ`, indexed by a natural number. -/
private def earlierNat (σ : Equiv.Perm (Fin n)) (m : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin n => j.val < m).image σ

/-- `earlierIndices` in terms of `earlierNat`. -/
private theorem earlierIndices_eq_earlierNat (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    earlierIndices σ k = earlierNat σ k.val := by
  simp only [earlierIndices, earlierNat, Fin.lt_def]

/-- Adding the next coordinate of the ordering. -/
private theorem earlierNat_succ (σ : Equiv.Perm (Fin n)) {m : ℕ} (h : m < n) :
    earlierNat σ (m + 1) = earlierNat σ m ∪ {σ ⟨m, h⟩} := by
  rw [earlierNat, earlierNat, ← Finset.image_singleton, ← Finset.image_union]
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton, Fin.ext_iff,
    Nat.lt_succ_iff_lt_or_eq]

/-- No coordinate precedes the first one. -/
private theorem earlierNat_zero (σ : Equiv.Perm (Fin n)) : earlierNat σ 0 = ∅ := by
  simp [earlierNat]

/-- All coordinates precede position `n`. -/
private theorem earlierNat_self (σ : Equiv.Perm (Fin n)) : earlierNat σ n = Finset.univ := by
  ext j
  simp only [earlierNat, mem_image, mem_filter, mem_univ, true_and, iff_true]
  exact ⟨σ.symm j, (σ.symm j).isLt, σ.apply_symm_apply j⟩

section Orbits

variable {G : Type} [Group G] [Fintype G]
variable {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
variable [∀ i, MulAction G (X i)]

omit [Fintype G] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] in
/-- The stabiliser of the restriction of `x` to `I`, for the coordinatewise action on the
partial product, is the intersection of the stabilisers of the coordinates `x_i`, `i ∈ I`. -/
private theorem stabilizer_restrictTo (x : ∀ i, X i) (I : Finset (Fin n)) :
    MulAction.stabilizer G (restrictTo I x)
      = subgroupMeet (fun i => MulAction.stabilizer G (x i)) I := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, subgroupMeet, Subgroup.mem_iInf, funext_iff,
    Pi.smul_apply, restrictTo, Subtype.forall]

omit [∀ i, Fintype (X i)] in
/-- The projection of the orbit of `x` onto `I` is the orbit of the restriction of `x`. -/
private theorem proj_orbit (x : ∀ i, X i) (I : Finset (Fin n)) :
    proj ((Finset.univ : Finset G).image fun g => fun i => g • x i) I
      = (Finset.univ : Finset G).image fun g => g • restrictTo I x := by
  rw [proj, Finset.image_image]
  rfl

omit [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] [∀ i, MulAction G (X i)] in
/-- The orbit of a point, as a set, is the image of the group. -/
private theorem orbit_eq_coe_image {Y : Type} [MulAction G Y] [DecidableEq Y] (y : Y) :
    MulAction.orbit G y = ↑((Finset.univ : Finset G).image fun g => g • y) := by
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rfl

omit [∀ i, Fintype (X i)] in
/-- The size of the projection of an orbit: `m_U(I) = |G| / |G_I|`, where `G_I` is the
intersection of the stabilisers of the coordinates `x_i` with `i ∈ I`.  Stated without
division.  Every subgroup of `G` is such a stabiliser (act on its cosets), so this dictionary
turns every inequality for projections of uniform sets into one for subgroup indices.
SUV Section 10.4, pp. 323–324 (unnumbered). -/
theorem projCard_orbit_mul_card_subgroupMeet (x : ∀ i, X i) (I : Finset (Fin n)) :
    projCard ((Finset.univ : Finset G).image fun g => fun i => g • x i) I
        * Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) I)
      = Nat.card G := by
  rw [← stabilizer_restrictTo, projCard, proj_orbit]
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G (restrictTo I x))
  rw [Nat.card_prod, orbit_eq_coe_image, Nat.card_coe_set_eq, Set.ncard_coe_finset] at h
  exact h

omit [∀ i, Fintype (X i)] in
/-- The orbit is invariant under the diagonal action. -/
private theorem smul_mem_orbit_image (x : ∀ i, X i) (g : G) {a : ∀ i, X i}
    (ha : a ∈ (Finset.univ : Finset G).image fun g => fun i => g • x i) :
    g • a ∈ (Finset.univ : Finset G).image fun g => fun i => g • x i := by
  simp only [mem_image, mem_univ, true_and] at ha ⊢
  obtain ⟨h, rfl⟩ := ha
  exact ⟨g * h, funext fun i => mul_smul g h (x i)⟩

omit [∀ i, Fintype (X i)] in
/-- Translating the base point of a section by `g₀` translates the section by `g₀`. -/
private theorem sectionOver_orbit_smul (x : ∀ i, X i) (J I : Finset (Fin n)) (g₀ : G)
    (p : (i : I) → X i.val) :
    sectionOver ((Finset.univ : Finset G).image fun g => fun i => g • x i) J I (g₀ • p)
      = (sectionOver ((Finset.univ : Finset G).image fun g => fun i => g • x i) J I p).image
          (g₀ • ·) := by
  set A := (Finset.univ : Finset G).image fun g => fun i => g • x i with hA
  have hfilt : (A.filter fun a => restrictTo I a = g₀ • p)
      = (A.filter fun a => restrictTo I a = p).image (g₀ • ·) := by
    ext a
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨ha, hp⟩
      refine ⟨g₀⁻¹ • a, ⟨smul_mem_orbit_image x g₀⁻¹ ha, ?_⟩, smul_inv_smul g₀ a⟩
      change g₀⁻¹ • restrictTo I a = p
      rw [hp, inv_smul_smul]
    · rintro ⟨b, ⟨hb, hpb⟩, rfl⟩
      refine ⟨smul_mem_orbit_image x g₀ hb, ?_⟩
      change g₀ • restrictTo I b = g₀ • p
      rw [hpb]
  rw [sectionOver, sectionOver, hfilt, Finset.image_image, Finset.image_image]
  rfl

omit [∀ i, Fintype (X i)] in
/-- The section of the orbit over the restriction of `x` itself is the orbit of the
restriction of `x` to `J` under the stabiliser subgroup `G_I`. -/
private theorem sectionOver_orbit_base (x : ∀ i, X i) (J I : Finset (Fin n))
    [Fintype (subgroupMeet (fun i => MulAction.stabilizer G (x i)) I)] :
    sectionOver ((Finset.univ : Finset G).image fun g => fun i => g • x i) J I (restrictTo I x)
      = (Finset.univ : Finset (subgroupMeet (fun i => MulAction.stabilizer G (x i)) I)).image
          fun k : subgroupMeet (fun i => MulAction.stabilizer G (x i)) I =>
            (k : G) • restrictTo J x := by
  ext q
  simp only [sectionOver, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨a, ⟨⟨g, rfl⟩, hI⟩, rfl⟩
    refine ⟨⟨g, ?_⟩, rfl⟩
    rw [← stabilizer_restrictTo]
    exact hI
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨fun i => g • x i, ⟨⟨g, rfl⟩, ?_⟩, rfl⟩
    rw [← stabilizer_restrictTo] at hg
    exact hg

omit [∀ i, Fintype (X i)] in
/-- The size of the base section: `|section| · |G_{I ∪ J}| = |G_I|`. -/
private theorem card_sectionOver_orbit_base (x : ∀ i, X i) (J I : Finset (Fin n)) :
    (sectionOver ((Finset.univ : Finset G).image fun g => fun i => g • x i) J I
        (restrictTo I x)).card
      * Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) (I ∪ J))
      = Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) I) := by
  classical
  set K := subgroupMeet (fun i => MulAction.stabilizer G (x i)) I with hK
  have : Fintype K := Fintype.ofFinite K
  rw [sectionOver_orbit_base]
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K (restrictTo J x))
  rw [Nat.card_prod, orbit_eq_coe_image, Nat.card_coe_set_eq, Set.ncard_coe_finset] at h
  have hstab : MulAction.stabilizer K (restrictTo J x)
      = (MulAction.stabilizer G (restrictTo J x)).subgroupOf K := by
    ext ⟨g, hg⟩
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]
  have hcard : Nat.card (MulAction.stabilizer K (restrictTo J x))
      = Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) (I ∪ J)) := by
    rw [hstab, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, stabilizer_restrictTo,
      hK, subgroupMeet, subgroupMeet, subgroupMeet, Finset.iInf_union, inf_comm]
  rw [hcard] at h
  exact h

/-- The maximal section of an orbit: `m_U(J | I) · |G_{I ∪ J}| = |G_I|`. -/
private theorem maxSection_orbit_mul_card (x : ∀ i, X i) (J I : Finset (Fin n)) :
    maxSection ((Finset.univ : Finset G).image fun g => fun i => g • x i) J I
      * Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) (I ∪ J))
      = Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) I) := by
  rw [maxSection_eq_sup_proj, proj_orbit]
  have hconst : ∀ p ∈ (Finset.univ : Finset G).image (fun g => g • restrictTo I x),
      (sectionOver ((Finset.univ : Finset G).image fun g => fun i => g • x i) J I p).card
        = (sectionOver ((Finset.univ : Finset G).image fun g => fun i => g • x i) J I
            (restrictTo I x)).card := by
    intro p hp
    obtain ⟨g, -, rfl⟩ := mem_image.1 hp
    rw [sectionOver_orbit_smul, card_image_of_injective _ (MulAction.injective g)]
  rw [Finset.sup_congr rfl hconst, Finset.sup_const ⟨_, mem_image_of_mem _ (mem_univ 1)⟩]
  exact card_sectionOver_orbit_base x J I

/-- The telescoping product along the first `m` factors of the chain bound. -/
private theorem prod_maxSection_orbit_mul_card (x : ∀ i, X i) (σ : Equiv.Perm (Fin n))
    (m : ℕ) (hm : m ≤ n) :
    (∏ i ∈ Finset.range m, if h : i < n then
        maxSection ((Finset.univ : Finset G).image fun g => fun i => g • x i) {σ ⟨i, h⟩}
          (earlierNat σ i) else 1)
      * Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) (earlierNat σ m))
      = Nat.card G := by
  induction m with
  | zero =>
    rw [Finset.prod_range_zero, one_mul, earlierNat_zero, subgroupMeet_empty, Subgroup.card_top]
  | succ m ih =>
    have hmn : m < n := hm
    rw [Finset.prod_range_succ, dite_eq_left hmn, earlierNat_succ σ hmn, mul_assoc,
      maxSection_orbit_mul_card]
    exact ih hmn.le

/-- **Theorem 208.**  Let a finite group `G` act on finite sets `X_1, …, X_n`, hence
diagonally on their product.  The orbit of any point is a uniform subset of the product.  For
a uniformly random `g ∈ G` the image `g · x` is uniformly distributed on the orbit — the
elements carrying `x` to a given point form a coset of the stabiliser — and the same holds for
every projection, so Theorem 205 applies.  SUV Theorem 208, p. 323. -/
theorem isUniform_orbit (x : ∀ i, X i) :
    IsUniform ((Finset.univ : Finset G).image fun g => fun i => g • x i) := by
  intro σ
  have hT := prod_maxSection_orbit_mul_card (G := G) x σ n le_rfl
  rw [earlierNat_self] at hT
  have hA : ((Finset.univ : Finset G).image fun g => fun i => g • x i).card
      * Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) Finset.univ)
      = Nat.card G := by
    rw [← projCard_univ]
    exact projCard_orbit_mul_card_subgroupMeet x Finset.univ
  have hpos : 0 < Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) Finset.univ) :=
    Nat.card_pos
  have hprod : chainBound ((Finset.univ : Finset G).image fun g => fun i => g • x i) σ
      = ∏ i ∈ Finset.range n, if h : i < n then
        maxSection ((Finset.univ : Finset G).image fun g => fun i => g • x i) {σ ⟨i, h⟩}
          (earlierNat σ i) else 1 := by
    rw [chainBound, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [dite_eq_left k.isLt, earlierIndices_eq_earlierNat]
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hprod, hT, hA]

end Orbits

/-! ### The dictionary between orbits and groups, and Theorem 207 -/

/-- The form holds for orbits: `∑_{I ≠ ∅} λ_I · log₂ m_U(I) ≤ 0` for every orbit `U` of a
finite group acting coordinatewise on a product of finite sets.  This is the class of uniform
sets that Sections 10.3 and 10.4 actually use: the set of column permutations of a matrix
(Theorem 207) is the orbit of a symmetric group.  SUV Section 10.4, pp. 323–324. -/
private def HoldsForOrbits (f : LinearForm n) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (X : Fin n → Type) [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)] [∀ i, MulAction G (X i)] (x : ∀ i, X i),
    f.evalLogSize ((Finset.univ : Finset G).image fun g => fun i => g • x i) ≤ 0

/-- The dictionary of p. 323: the value of a form on the log-sizes of the projections of an
orbit is its value on the indices of the stabilisers, `log₂ m_U(I) = log₂ (|G| / |G_I|)`. -/
private theorem evalLogSize_orbit_eq_evalGroupIndex {G : Type} [Group G] [Fintype G]
    {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, MulAction G (X i)]
    (f : LinearForm n) (x : ∀ i, X i) :
    f.evalLogSize ((Finset.univ : Finset G).image fun g => fun i => g • x i)
      = f.evalGroupIndex fun i => MulAction.stabilizer G (x i) := by
  unfold LinearForm.evalLogSize LinearForm.evalGroupIndex
  refine Finset.sum_congr rfl fun I _ => ?_
  have hpos : (0 : ℝ) < Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) I) := by
    exact_mod_cast (Nat.card_pos (α := subgroupMeet (fun i => MulAction.stabilizer G (x i)) I))
  have h : (projCard ((Finset.univ : Finset G).image fun g => fun i => g • x i) I : ℝ)
      = (Nat.card G : ℝ) / Nat.card (subgroupMeet (fun i => MulAction.stabilizer G (x i)) I) := by
    rw [eq_div_iff hpos.ne']
    exact_mod_cast projCard_orbit_mul_card_subgroupMeet x I
  rw [h]

/-- The forms valid for orbits are exactly the forms valid for groups: every subgroup is the
stabiliser of the coset `H` under the action of `G` on `G / H`, and every stabiliser is a
subgroup.  SUV Section 10.4, pp. 323–324. -/
private theorem holdsForOrbits_iff_holdsForGroups (f : LinearForm n) :
    HoldsForOrbits f ↔ HoldsForGroups f := by
  constructor
  · intro hf G _ _ H
    have : Fintype G := Fintype.ofFinite G
    have : ∀ i, Finite (G ⧸ H i) := fun i =>
      Finite.of_surjective _ (QuotientGroup.mk_surjective (s := H i))
    have : ∀ i, Fintype (G ⧸ H i) := fun i => Fintype.ofFinite _
    have : ∀ i, DecidableEq (G ⧸ H i) := fun i => Classical.decEq _
    have h := hf G (fun i => G ⧸ H i) fun i => ((1 : G) : G ⧸ H i)
    rw [evalLogSize_orbit_eq_evalGroupIndex] at h
    simpa only [MulAction.stabilizer_quotient] using h
  · intro hf G _ _ X _ _ _ x
    rw [evalLogSize_orbit_eq_evalGroupIndex]
    exact hf G _

/-- Every form valid for uniform sets is valid for orbits, since orbits are uniform
(Theorem 208).  SUV Theorem 208, p. 323. -/
private theorem holdsForOrbits_of_holdsForUniformSets (f : LinearForm n)
    (h : HoldsForUniformSets f) : HoldsForOrbits f := by
  intro G _ _ X _ _ _ x
  exact h X _ ⟨_, mem_image_of_mem _ (mem_univ 1)⟩ (isUniform_orbit x)

/-! ### Theorem 207: the orbit of a matrix under column permutations -/

/-- The slack `(C · log₂ t + D) / t` tends to zero, so a real number bounded by it for every
`t ≥ 1` is non-positive.  This is the passage to the limit `t → ∞` of the proof of
Theorem 207.  SUV Section 10.3, p. 323. -/
private theorem nonpos_of_forall_le_logb_div {s C D : ℝ}
    (h : ∀ t : ℕ, 1 ≤ t → s ≤ (C * Real.logb 2 t + D) / t) : s ≤ 0 := by
  have hlog : Filter.Tendsto (fun t : ℕ => Real.log t / t) Filter.atTop (nhds 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine this.congr fun t => ?_
    simp [Function.comp]
  have hC : Filter.Tendsto (fun t : ℕ => C * Real.logb 2 t / t) Filter.atTop (nhds 0) := by
    have := hlog.const_mul (C / Real.log 2)
    rw [mul_zero] at this
    refine this.congr fun t => ?_
    rw [Real.logb]
    ring
  have hD : Filter.Tendsto (fun t : ℕ => D / t) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat D
  have hsum := hC.add hD
  rw [add_zero] at hsum
  refine ge_of_tendsto hsum (Filter.eventually_atTop.2 ⟨1, fun t ht => ?_⟩)
  change s ≤ C * Real.logb 2 t / t + D / t
  rw [← add_div]
  exact h t ht

/-- `2^{N h(c/N)} · ∏_b c_b^{c_b} = N^N` for a count vector `c` summing to `N ≥ 1`: the
entropy of the frequencies against the product of the powers.  SUV Section 7.3.1, p. 226. -/
private theorem two_rpow_mul_entropyDist_mul_prod_pow {B : Type} [Fintype B] (N : ℕ)
    (c : B → ℕ) (hc : ∑ b, c b = N) (hN : 0 < N) :
    (2 : ℝ) ^ ((N : ℝ) * entropyDist fun b => (c b : ℝ) / N) * ∏ b, (c b : ℝ) ^ c b
      = (N : ℝ) ^ N := by
  have hcoord : ∀ k : ℕ, (2 : ℝ) ^ ((N : ℝ) * negMulLog2 ((k : ℝ) / N)) * (k : ℝ) ^ k
      = (N : ℝ) ^ k := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hkr : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [negMulLog2, Real.negMulLog_eq_neg]
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hdiv : (k : ℝ) / N > 0 := div_pos hkr hNr
    rw [show Real.log 2 * ((N : ℝ) *
        (-((k : ℝ) / N * Real.log ((k : ℝ) / N)) / Real.log 2)) =
        -(k : ℝ) * Real.log ((k : ℝ) / N) by field_simp]
    rw [show -(k : ℝ) * Real.log ((k : ℝ) / N) =
        -(Real.log ((k : ℝ) / N) * (k : ℝ)) by ring]
    rw [Real.exp_neg, Real.exp_mul, Real.exp_log hdiv, Real.rpow_natCast]
    rw [div_pow]
    field_simp
  rw [entropyDist, Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num),
    ← Finset.prod_mul_distrib]
  simp_rw [hcoord]
  rw [Finset.prod_pow_eq_pow_sum, hc]

/-- The product of the powers `c_b^{c_b}` is positive. -/
private theorem prod_pow_self_pos {B : Type} [Fintype B] (c : B → ℕ) :
    0 < ∏ b, (c b : ℝ) ^ c b :=
  Finset.prod_pos fun b _ => by
    by_cases hcb : c b = 0
    · simp [hcb]
    · positivity

/-- `log₂ M(c) ≤ N · h(c/N)`: the multinomial coefficient of a count vector summing to `N` is
at most `2^{N h(c/N)}`.  This is the upper half of `log m_U(I) = N · H + O(log N)` in the
proof of Theorem 207.  SUV Section 10.3, p. 322. -/
private theorem logb_multinomial_le {B : Type} [Fintype B] (N : ℕ) (c : B → ℕ)
    (hc : ∑ b, c b = N) (hN : 0 < N) :
    Real.logb 2 (Nat.multinomial Finset.univ c)
      ≤ (N : ℝ) * entropyDist fun b => (c b : ℝ) / N := by
  classical
  have hmem : c ∈ Finset.piAntidiag (Finset.univ : Finset B) N := by
    simp [Finset.mem_piAntidiag, hc]
  have h1 : (Nat.multinomial Finset.univ c : ℝ) * ∏ b, (c b : ℝ) ^ c b ≤ (N : ℝ) ^ N := by
    exact_mod_cast multinomial_mul_typeProb_le_one Finset.univ c N hmem
  rw [← two_rpow_mul_entropyDist_mul_prod_pow N c hc hN] at h1
  have hmpos : (0 : ℝ) < Nat.multinomial Finset.univ c := by
    exact_mod_cast Nat.multinomial_pos _ _
  rw [Real.logb_le_iff_le_rpow (by norm_num) hmpos]
  exact le_of_mul_le_mul_right h1 (prod_pow_self_pos c)

/-- `N · h(c/N) ≤ log₂ M(c) + |B| · log₂ (N + 1)`: the lower half of
`log m_U(I) = N · H + O(log N)`, with the explicit `O(log N)` term `|B| log₂ (N + 1)` coming
from the number of types.  SUV Section 10.3, p. 322. -/
private theorem le_logb_multinomial_add {B : Type} [Fintype B] (N : ℕ)
    (c : B → ℕ) (hc : ∑ b, c b = N) (hN : 0 < N) :
    (N : ℝ) * entropyDist (fun b => (c b : ℝ) / N)
      ≤ Real.logb 2 (Nat.multinomial Finset.univ c)
        + Fintype.card B * Real.logb 2 (N + 1) := by
  classical
  have hmem : c ∈ Finset.piAntidiag (Finset.univ : Finset B) N := by
    simp [Finset.mem_piAntidiag, hc]
  have h1 : (N : ℝ) ^ N ≤ ((N : ℝ) + 1) ^ Fintype.card B
      * ((Nat.multinomial Finset.univ c : ℝ) * ∏ b, (c b : ℝ) ^ c b) := by
    have := one_le_pow_mul_multinomial_mul_typeProb Finset.univ c N hmem
    rw [Finset.card_univ] at this
    exact_mod_cast this
  rw [← two_rpow_mul_entropyDist_mul_prod_pow N c hc hN] at h1
  have hmpos : (0 : ℝ) < Nat.multinomial Finset.univ c := by
    exact_mod_cast Nat.multinomial_pos _ _
  have h2 : (2 : ℝ) ^ ((N : ℝ) * entropyDist fun b => (c b : ℝ) / N)
      ≤ ((N : ℝ) + 1) ^ Fintype.card B * Nat.multinomial Finset.univ c := by
    refine le_of_mul_le_mul_right ?_ (prod_pow_self_pos c)
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hpos : (0 : ℝ) < ((N : ℝ) + 1) ^ Fintype.card B * Nat.multinomial Finset.univ c := by
    positivity
  have := (Real.le_logb_iff_rpow_le (by norm_num) hpos).2 h2
  rwa [Real.logb_mul (by positivity) hmpos.ne', Real.logb_pow, add_comm] at this

section Matrices

variable {A : Type} [Fintype A] [DecidableEq A]

attribute [local instance] arrowAction

/-- The `I`-marginal of a distribution `p` on `n`-tuples: `p_I(v) = ∑_{a : a|_I = v} p(a)`,
the distribution of the subtuple `ξ_I` when `p` is the joint distribution of `ξ`. -/
private def marginal (I : Finset (Fin n)) (p : (Fin n → A) → ℝ) : ((i : I) → A) → ℝ :=
  fun v => ∑ a ∈ Finset.univ.filter (fun a : Fin n → A => restrictTo I a = v), p a

/-- The marginal depends continuously on the distribution. -/
private theorem continuous_marginal (I : Finset (Fin n)) :
    Continuous fun p : (Fin n → A) → ℝ => marginal I p :=
  continuous_pi fun _ => continuous_finsetSum _ fun a _ => continuous_apply a

/-- The entropy of a subtuple of `ℕ`-valued random variables that factor through a finite
alphabet `A` is the entropy of the corresponding marginal of the joint distribution:
`H(ξ_I) = H(p_I)`.  SUV Section 10.3, p. 322. -/
private theorem entropySub_eq_entropyDist_marginal {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (Y : Ω → (Fin n → A)) (e : A → ℕ) (he : Function.Injective e)
    (I : Finset (Fin n)) :
    entropySub μ (fun i ω => e (Y ω i)) I = entropyDist (marginal I (μ.dist Y)) := by
  have hinj : Function.Injective fun v : (i : I) → A => fun i => e (v i) :=
    fun v₁ v₂ h => funext fun i => he (congrFun h i)
  have hcomp : subtuple (fun i ω => e (Y ω i)) I
      = (fun v : (i : I) → A => fun i => e (v i)) ∘ fun ω => restrictTo I (Y ω) := rfl
  rw [entropySub, hcomp, entropy_comp_of_injective μ _ hinj, entropy_eq_entropyDist]
  congr 1
  funext v
  simp only [marginal, FiniteProbSpace.dist, FiniteProbSpace.probOf]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  refine Finset.sum_congr (Finset.filter_congr fun ω _ => ?_) fun _ _ => rfl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The rows of the `n × N` matrix whose columns are the tuples `w j`. -/
private def rows {N : ℕ} (w : Fin N → (Fin n → A)) : Fin n → (Fin N → A) := fun i j => w j i

/-- The frequencies of the word of `I`-columns are the `I`-marginals of the frequencies of the
columns. -/
private theorem freq_restrictTo {N : ℕ} (w : Fin N → (Fin n → A)) (I : Finset (Fin n))
    (v : (i : I) → A) :
    freq (fun j => restrictTo I (w j)) v
      = ∑ a ∈ Finset.univ.filter (fun a : Fin n → A => restrictTo I a = v), freq w a := by
  simp only [freq]
  rw [Finset.card_eq_sum_card_fiberwise (f := w)
    (t := Finset.univ.filter fun a : Fin n → A => restrictTo I a = v)]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr fun j _ => ?_)
    have hav := (Finset.mem_filter.1 ha).2
    exact ⟨fun h => h.2, fun h => ⟨by rw [h, hav], h⟩⟩
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, hj.2⟩

/-- The empirical distribution of the `I`-columns is the `I`-marginal of the empirical
distribution of the columns. -/
private theorem marginal_freq_div {N : ℕ} (w : Fin N → (Fin n → A)) (I : Finset (Fin n)) :
    marginal I (fun a => (freq w a : ℝ) / N)
      = fun v => (freq (fun j => restrictTo I (w j)) v : ℝ) / N := by
  funext v
  rw [marginal, freq_restrictTo, Nat.cast_sum, Finset.sum_div]

/-- The stabiliser of a word under the action of `S_N` on positions is the product of the
symmetric groups of its fibres: `|Stab(u)| = ∏_b (freq u b)!`.  SUV Section 10.3, p. 322. -/
private theorem card_stabilizer_word {N : ℕ} {B : Type} [Fintype B] [DecidableEq B]
    (u : Fin N → B) :
    Nat.card (MulAction.stabilizer (Equiv.Perm (Fin N)) u) = ∏ b, (freq u b).factorial := by
  have hiff : ∀ σ : Equiv.Perm (Fin N),
      σ ∈ MulAction.stabilizer (Equiv.Perm (Fin N)) u ↔ u ∘ σ = u := by
    intro σ
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      funext a
      have ha := congrFun h (σ a)
      change u (σ.symm (σ a)) = u (σ a) at ha
      rw [Equiv.symm_apply_apply] at ha
      exact ha.symm
    · intro h
      funext a
      change u (σ.symm a) = u a
      have ha := congrFun h (σ.symm a)
      rw [Function.comp_apply, Equiv.apply_symm_apply] at ha
      exact ha.symm
  have hstab : Nat.card (MulAction.stabilizer (Equiv.Perm (Fin N)) u)
      = Fintype.card {σ : Equiv.Perm (Fin N) // u ∘ σ = u} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [hstab, DomMulAct.stabilizer_card u]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Fintype.card_subtype]
  rfl

omit [Fintype A] [DecidableEq A] in
/-- The stabiliser of the `I`-rows of the matrix is the stabiliser of the word of
`I`-columns. -/
private theorem stabilizer_restrictTo_rows {N : ℕ} (w : Fin N → (Fin n → A))
    (I : Finset (Fin n)) :
    MulAction.stabilizer (Equiv.Perm (Fin N)) (restrictTo I (rows w))
      = MulAction.stabilizer (Equiv.Perm (Fin N)) (fun j => restrictTo I (w j)) := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff, funext_iff, Pi.smul_apply, restrictTo, rows]
  exact forall_comm

/-- The projection of the orbit of the matrix onto `I` has size `N! / ∏_v (freq u_I v)!`,
where `u_I` is the word of `I`-columns: `m_U(I)` is a multinomial coefficient.  Stated without
division.  SUV Section 10.3, p. 322. -/
private theorem projCard_orbit_rows_mul_prod_factorial {N : ℕ} (w : Fin N → (Fin n → A))
    (I : Finset (Fin n)) :
    projCard ((Finset.univ : Finset (Equiv.Perm (Fin N))).image fun g => fun i => g • rows w i) I
        * ∏ v, (freq (fun j => restrictTo I (w j)) v).factorial
      = N.factorial := by
  have h := projCard_orbit_mul_card_subgroupMeet (G := Equiv.Perm (Fin N)) (rows w) I
  rw [← stabilizer_restrictTo, stabilizer_restrictTo_rows, card_stabilizer_word,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
  exact h

/-- `m_U(I)` is the multinomial coefficient of the frequencies of the `I`-columns. -/
private theorem projCard_orbit_rows_eq_multinomial {N : ℕ} (w : Fin N → (Fin n → A))
    (I : Finset (Fin n)) :
    projCard ((Finset.univ : Finset (Equiv.Perm (Fin N))).image fun g => fun i => g • rows w i) I
      = Nat.multinomial Finset.univ (freq fun j => restrictTo I (w j)) := by
  have h := projCard_orbit_rows_mul_prod_factorial w I
  have hspec := Nat.multinomial_spec Finset.univ (freq fun j => restrictTo I (w j))
  rw [sum_freq] at hspec
  have hpos : 0 < ∏ v, (freq (fun j => restrictTo I (w j)) v).factorial :=
    Finset.prod_pos fun _ _ => Nat.factorial_pos _
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [mul_comm, h, ← hspec]

omit [DecidableEq A] in
/-- The alphabet of the `I`-columns has at most `(|A| + 1)^n` letters. -/
private theorem card_pi_le (I : Finset (Fin n)) :
    Fintype.card ((i : I) → A) ≤ (Fintype.card A + 1) ^ n := by
  rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  calc Fintype.card A ^ I.card ≤ (Fintype.card A + 1) ^ I.card :=
        Nat.pow_le_pow_left (Nat.le_succ _) _
    _ ≤ (Fintype.card A + 1) ^ n :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by simpa using Finset.card_le_univ I)

/-- One summand of the orbit inequality: with `K = (|A| + 1)^n`,
`λ_I · N · H(p_I) ≤ λ_I · log₂ m_U(I) + |λ_I| · K · log₂ (N + 1)` for the empirical
distribution `p` of the columns.  SUV Section 10.3, pp. 322–323. -/
private theorem mul_entropyDist_marginal_le (f : LinearForm n) {N : ℕ} (hN : 0 < N)
    (w : Fin N → (Fin n → A)) (I : Finset (Fin n)) :
    f I * ((N : ℝ) * entropyDist (marginal I fun a => (freq w a : ℝ) / N))
      ≤ f I * Real.logb 2 (projCard ((Finset.univ : Finset (Equiv.Perm (Fin N))).image
            fun g => fun i => g • rows w i) I)
        + |f I| * (Fintype.card A + 1) ^ n * Real.logb 2 (N + 1) := by
  rw [marginal_freq_div, projCard_orbit_rows_eq_multinomial]
  have hc : ∑ v, freq (fun j => restrictTo I (w j)) v = N := sum_freq _
  have hup := logb_multinomial_le N _ hc hN
  have hlow := le_logb_multinomial_add N _ hc hN
  have hL : 0 ≤ Real.logb 2 (N + 1) := Real.logb_nonneg (by norm_num) (by simp)
  have hK : (Fintype.card ((i : I) → A) : ℝ) ≤ (Fintype.card A + 1) ^ n := by
    exact_mod_cast card_pi_le (A := A) I
  rcases le_or_gt 0 (f I) with hf | hf
  · rw [abs_of_nonneg hf]
    calc f I * ((N : ℝ) * entropyDist fun v => (freq (fun j => restrictTo I (w j)) v : ℝ) / N)
        ≤ f I * (Real.logb 2 (Nat.multinomial Finset.univ
              fun v => freq (fun j => restrictTo I (w j)) v)
            + Fintype.card ((i : I) → A) * Real.logb 2 (N + 1)) :=
          mul_le_mul_of_nonneg_left hlow hf
      _ ≤ _ := by
          rw [mul_add, mul_assoc]
          gcongr
  · rw [abs_of_neg hf]
    have h1 := mul_le_mul_of_nonpos_left hup hf.le
    have h2 : 0 ≤ -f I * (Fintype.card A + 1) ^ n * Real.logb 2 (N + 1) := by
      have : 0 ≤ -f I := by linarith
      positivity
    linarith

end Matrices

/-- The existence of a word with prescribed letter counts. -/
private theorem exists_word_freq {B : Type} [Fintype B] [DecidableEq B] (N : ℕ) (c : B → ℕ)
    (hc : ∑ b, c b = N) : ∃ w : Fin N → B, ∀ b, freq w b = c b := by
  have hcard : Fintype.card (Σ b, Fin (c b)) = N := by
    rw [Fintype.card_sigma]
    simpa using hc
  let e : Fin N ≃ Σ b, Fin (c b) := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun j => (e j).1, fun b => ?_⟩
  have hfib : {s : Σ b', Fin (c b') // s.1 = b} ≃ Fin (c b) :=
    { toFun := fun s => Fin.cast (congrArg c s.2) s.1.2
      invFun := fun k => ⟨⟨b, k⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨b', k⟩, h⟩
        dsimp only at h
        subst h
        rfl
      right_inv := fun k => rfl }
  calc freq (fun j => (e j).1) b = Fintype.card {j : Fin N // (e j).1 = b} :=
        (Fintype.card_subtype _).symm
    _ = c b := by
        rw [Fintype.card_congr ((e.subtypeEquiv fun j => Iff.rfl).trans hfib), Fintype.card_fin]

/-- Rational approximation of a distribution: for every `δ > 0` there are counts `c` with
total `N ≥ 1` whose frequencies `c/N` are within `δ` of `p` at every point.  This is the
density step of the proof of Theorem 207.  SUV Section 10.3, p. 323. -/
private theorem exists_counts_near {B : Type} [Fintype B] (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b)
    (hp1 : ∑ b, p b = 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (c : B → ℕ), 0 < N ∧ ∑ b, c b = N ∧ ∀ b, |(c b : ℝ) / N - p b| < δ := by
  classical
  rcases isEmpty_or_nonempty B with hB | ⟨⟨b₀⟩⟩
  · simp at hp1
  obtain ⟨N, hN⟩ := exists_nat_gt ((Fintype.card B : ℝ) / δ)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg _) hδ.le) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hcard : (Fintype.card B : ℝ) < δ * N := by
    rwa [div_lt_iff₀ hδ, mul_comm] at hN
  have h1 : (1 : ℝ) ≤ Fintype.card B := Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨b₀⟩)
  set d : B → ℕ := fun b => ⌊p b * N⌋₊ with hd
  have hdle : ∀ b, (d b : ℝ) ≤ p b * N := fun b => Nat.floor_le (mul_nonneg (hp0 b) hNpos.le)
  have hdlt : ∀ b, p b * N < d b + 1 := fun b => Nat.lt_floor_add_one _
  have hsumN : ∑ b, p b * N = N := by rw [← Finset.sum_mul, hp1, one_mul]
  have hsum_le : ∑ b, d b ≤ N := by
    have : (∑ b, (d b : ℝ)) ≤ N := by
      rw [← hsumN]
      exact Finset.sum_le_sum fun b _ => hdle b
    exact_mod_cast this
  have hexcess : ((N - ∑ b', d b' : ℕ) : ℝ) < Fintype.card B := by
    rw [Nat.cast_sub hsum_le, Nat.cast_sum]
    have : (N : ℝ) < ∑ b', ((d b' : ℝ) + 1) := by
      rw [← hsumN]
      exact Finset.sum_lt_sum_of_nonempty ⟨b₀, Finset.mem_univ _⟩ fun b' _ => hdlt b'
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    linarith
  set c : B → ℕ := fun b => d b + if b = b₀ then N - ∑ b', d b' else 0 with hc
  refine ⟨N, c, hN0, ?_, fun b => ?_⟩
  · simp only [hc, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Nat.add_sub_of_le hsum_le
  · have hlow : p b * N - 1 < (c b : ℝ) := by
      have h : (d b : ℝ) ≤ c b := by exact_mod_cast (Nat.le_add_right _ _ : d b ≤ c b)
      linarith [hdlt b]
    have hup : (c b : ℝ) < p b * N + Fintype.card B := by
      have h : (c b : ℝ) ≤ d b + ((N - ∑ b', d b' : ℕ) : ℝ) := by
        have : c b ≤ d b + (N - ∑ b', d b') := by
          simp only [hc]
          split_ifs <;> omega
        exact_mod_cast this
      linarith [hdle b]
    have hmain : |(c b : ℝ) - p b * N| < δ * N := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    have heq : (c b : ℝ) / N - p b = ((c b : ℝ) - p b * N) / N := by
      rw [sub_div, mul_div_assoc, div_self hNpos.ne', mul_one]
    rw [heq, abs_div, abs_of_pos hNpos, div_lt_iff₀ hNpos]
    exact hmain

section Distributions

variable {A : Type} [Fintype A] [DecidableEq A]

attribute [local instance] arrowAction

/-- The orbit inequality for the matrix of a word `w` of `N ≥ 1` columns: with
`C = ∑_I |λ_I| · (|A| + 1)^n`, `N · ∑_I λ_I H(p_I) ≤ C · log₂ (N + 1)` for the empirical
distribution `p` of the columns.  SUV Section 10.3, pp. 322–323. -/
private theorem mul_sum_entropyDist_marginal_le (f : LinearForm n) (h : HoldsForOrbits f)
    {N : ℕ} (hN : 0 < N) (w : Fin N → (Fin n → A)) :
    (N : ℝ) * ∑ I ∈ nonemptyParts n, f I * entropyDist (marginal I fun a => (freq w a : ℝ) / N)
      ≤ (∑ I ∈ nonemptyParts n, |f I|) * (Fintype.card A + 1) ^ n * Real.logb 2 (N + 1) := by
  have hU := h (Equiv.Perm (Fin N)) (fun _ => Fin N → A) (rows w)
  rw [Finset.mul_sum]
  calc ∑ I ∈ nonemptyParts n, (N : ℝ) * (f I * entropyDist (marginal I fun a => (freq w a : ℝ) / N))
      ≤ ∑ I ∈ nonemptyParts n, (f I * Real.logb 2 (projCard
            ((Finset.univ : Finset (Equiv.Perm (Fin N))).image fun g => fun i => g • rows w i) I)
          + |f I| * (Fintype.card A + 1) ^ n * Real.logb 2 (N + 1)) := by
        refine Finset.sum_le_sum fun I _ => ?_
        rw [mul_left_comm]
        exact mul_entropyDist_marginal_le f hN w I
    _ = f.evalLogSize ((Finset.univ : Finset (Equiv.Perm (Fin N))).image
            fun g => fun i => g • rows w i)
          + (∑ I ∈ nonemptyParts n, |f I|) * (Fintype.card A + 1) ^ n * Real.logb 2 (N + 1) := by
        rw [Finset.sum_add_distrib, LinearForm.evalLogSize, Finset.sum_mul, Finset.sum_mul]
    _ ≤ _ := by linarith

/-- A form valid for orbits is valid for the entropies of every distribution with rational
probabilities: the bound of the matrix with `t · N` columns divided by `t · N` tends to zero.
SUV Section 10.3, p. 323. -/
private theorem sum_entropyDist_marginal_counts_nonpos (f : LinearForm n) (h : HoldsForOrbits f)
    {N : ℕ} (hN : 0 < N) (c : (Fin n → A) → ℕ) (hc : ∑ a, c a = N) :
    ∑ I ∈ nonemptyParts n, f I * entropyDist (marginal I fun a => (c a : ℝ) / N) ≤ 0 := by
  set S : ℝ := (∑ I ∈ nonemptyParts n, |f I|) * (Fintype.card A + 1) ^ n with hS
  have hS0 : 0 ≤ S := by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine nonpos_of_forall_le_logb_div (C := S / N) (D := S * (1 + Real.logb 2 N) / N)
    fun t ht => ?_
  obtain ⟨w, hw⟩ := exists_word_freq (t * N) (fun a => t * c a) (by rw [← Finset.mul_sum, hc])
  have htN : 0 < t * N := Nat.mul_pos (by omega) hN
  have hbound := mul_sum_entropyDist_marginal_le f h htN w
  have htr : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hfreq : (fun a => (freq w a : ℝ) / ((t * N : ℕ) : ℝ)) = fun a => (c a : ℝ) / N := by
    funext a
    rw [hw a]
    push_cast
    field_simp
  rw [hfreq] at hbound
  have hlog : Real.logb 2 (((t * N : ℕ) : ℝ) + 1) ≤ 1 + Real.logb 2 t + Real.logb 2 N := by
    have h2 : ((t * N : ℕ) : ℝ) + 1 ≤ 2 * (t * N) := by
      push_cast
      have : (1 : ℝ) ≤ t * N := by
        have := mul_pos htr hNr
        exact_mod_cast htN
      linarith
    calc Real.logb 2 (((t * N : ℕ) : ℝ) + 1) ≤ Real.logb 2 (2 * (t * N)) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) h2
      _ = 1 + Real.logb 2 t + Real.logb 2 N := by
          rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_mul htr.ne' hNr.ne',
            Real.logb_self_eq_one (by norm_num)]
          ring
  have hmain : ((t * N : ℕ) : ℝ) * ∑ I ∈ nonemptyParts n, f I *
      entropyDist (marginal I fun a => (c a : ℝ) / N) ≤ S * (1 + Real.logb 2 t + Real.logb 2 N) :=
    hbound.trans (mul_le_mul_of_nonneg_left hlog hS0)
  push_cast at hmain
  rw [show (S / N * Real.logb 2 t + S * (1 + Real.logb 2 N) / N) / t
      = S * (1 + Real.logb 2 t + Real.logb 2 N) / (t * N) by field_simp; ring]
  rw [le_div_iff₀ (mul_pos htr hNr)]
  linarith

/-- A form valid for orbits is valid for the entropies of every distribution on `A^n`:
rational distributions are dense and the two sides depend continuously on the distribution.
SUV Section 10.3, p. 323. -/
private theorem sum_entropyDist_marginal_nonpos (f : LinearForm n) (h : HoldsForOrbits f)
    (p : (Fin n → A) → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ∑ I ∈ nonemptyParts n, f I * entropyDist (marginal I p) ≤ 0 := by
  set F : ((Fin n → A) → ℝ) → ℝ :=
    fun q => ∑ I ∈ nonemptyParts n, f I * entropyDist (marginal I q) with hF
  have hcont : Continuous F :=
    continuous_finsetSum _ fun I _ =>
      continuous_const.mul (continuous_entropyDist.comp (continuous_marginal I))
  change F p ≤ 0
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuous_iff.1 hcont p ε hε
  obtain ⟨N, c, hN, hc, hnear⟩ := exists_counts_near p hp0 hp1 hδ
  have hq : dist (fun a => (c a : ℝ) / N) p < δ := by
    rw [dist_pi_lt_iff hδ]
    intro a
    rw [Real.dist_eq]
    exact hnear a
  have hclose := hδF _ hq
  rw [Real.dist_eq, abs_sub_lt_iff] at hclose
  have hrat : F (fun a => (c a : ℝ) / N) ≤ 0 :=
    sum_entropyDist_marginal_counts_nonpos f h hN c hc
  linarith [hclose.2]

end Distributions

/-- The core of Theorem 207: a form valid for all orbits is valid for all entropies.  Given
random variables with rational probabilities with common denominator `N`, the set of column
permutations of an `n × N` matrix realising them is the orbit of the symmetric group `S_N`;
`log m_U(I) = N · H(ξ_I) + O(log N)` by Stirling's formula; multiply `N` by `t`, divide by
`tN` and let `t → ∞`; arbitrary distributions follow by density and `continuous_entropyDist`.
SUV Theorem 207, pp. 322–323. -/
private theorem holdsForEntropies_of_holdsForOrbits (f : LinearForm n)
    (h : HoldsForOrbits f) : HoldsForEntropies f := by
  intro Ω _ μ X
  set M : ℕ := (Finset.univ.sup fun q : Ω × Fin n => X q.2 q.1) + 1 with hM
  have hlt : ∀ i ω, X i ω < M := fun i ω =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun q : Ω × Fin n => X q.2 q.1) (Finset.mem_univ (ω, i)))
  let Y : Ω → (Fin n → Fin M) := fun ω i => ⟨X i ω, hlt i ω⟩
  have hX : X = fun i ω => ((Y ω i : Fin M) : ℕ) := rfl
  have hev : f.evalEntropy μ X
      = ∑ I ∈ nonemptyParts n, f I * entropyDist (marginal I (μ.dist Y)) := by
    unfold LinearForm.evalEntropy
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hX, entropySub_eq_entropyDist_marginal μ Y (fun a : Fin M => a.val) Fin.val_injective I]
  have hsum : ∑ a, μ.dist Y a = 1 := by
    rw [← μ.sum_dist_eq_one Y]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
    exact μ.dist_eq_zero_of_not_mem_range ha
  rw [hev]
  exact sum_entropyDist_marginal_nonpos f h (μ.dist Y) (μ.dist_nonneg Y) hsum

/-- **Theorem 207 (Chan and Yeung).**  Every linear inequality that is true for the log-sizes
of the projections of all uniform sets is true for the entropies of arbitrary tuples of random
variables.  SUV Theorem 207, p. 323. -/
theorem holdsForEntropies_of_holdsForUniformSets (f : LinearForm n)
    (h : HoldsForUniformSets f) : HoldsForEntropies f :=
  holdsForEntropies_of_holdsForOrbits f (holdsForOrbits_of_holdsForUniformSets f h)

/-- The inequality `m(1,2) ≤ m(1) · m(2)` read through the subgroup dictionary:
`|H₁ ∩ H₂| ≥ |H₁| · |H₂| / |G|` for arbitrary subgroups of a finite group.  Stated without
division.  SUV Section 10.4, p. 324 (unnumbered). -/
theorem card_mul_card_le_card_inf_mul_card {G : Type} [Group G] [Finite G]
    (H₁ H₂ : Subgroup G) :
    Nat.card H₁ * Nat.card H₂ ≤ Nat.card (H₁ ⊓ H₂ : Subgroup G) * Nat.card G := by
  have : Nonempty G := ⟨1⟩
  have h₁ := Subgroup.card_mul_index H₁
  have h₂ := Subgroup.card_mul_index H₂
  have h₃ := Subgroup.card_mul_index (H₁ ⊓ H₂)
  have hle := Subgroup.index_inf_le (H := H₁) (K := H₂)
  have hpos : 0 < (H₁ ⊓ H₂).index := by
    rcases Nat.eq_zero_or_pos (H₁ ⊓ H₂).index with h | h
    · rw [h, mul_zero] at h₃
      exact absurd h₃.symm Nat.card_pos.ne'
    · exact h
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card H₁ * Nat.card H₂ * (H₁ ⊓ H₂).index
      ≤ Nat.card H₁ * Nat.card H₂ * (H₁.index * H₂.index) := Nat.mul_le_mul_left _ hle
    _ = (Nat.card H₁ * H₁.index) * (Nat.card H₂ * H₂.index) := by ring
    _ = Nat.card G * Nat.card G := by rw [h₁, h₂]
    _ = Nat.card (H₁ ⊓ H₂ : Subgroup G) * Nat.card G * (H₁ ⊓ H₂).index := by
      rw [← h₃]; ring

/-- The two-subgroup inequality inside a subgroup `L`: `|H| · |K| ≤ |H ∩ K| · |L|` whenever
`H, K ≤ L`. -/
private theorem card_mul_card_le_card_inf_mul_card_of_le {G : Type} [Group G] [Finite G]
    {H K L : Subgroup G} (hH : H ≤ L) (hK : K ≤ L) :
    Nat.card H * Nat.card K ≤ Nat.card (H ⊓ K : Subgroup G) * Nat.card L := by
  have h := card_mul_card_le_card_inf_mul_card (H.subgroupOf L) (K.subgroupOf L)
  have hHK : (H ⊓ K).subgroupOf L = H.subgroupOf L ⊓ K.subgroupOf L :=
    Subgroup.comap_inf _ _ _
  rwa [← hHK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hH)).toEquiv] at h


/-- The inequality `m(1,2,3)² ≤ m(1,2) m(1,3) m(2,3)` read through the subgroup dictionary:
`|H₁ ∩ H₂ ∩ H₃|² ≥ |H₁ ∩ H₂| · |H₁ ∩ H₃| · |H₂ ∩ H₃| / |G|`.  Stated without division.
SUV Section 10.4, p. 324 (unnumbered). -/
theorem card_inf_pairs_le_card_inf_triple_sq_mul_card {G : Type} [Group G] [Finite G]
    (H₁ H₂ H₃ : Subgroup G) :
    Nat.card (H₁ ⊓ H₂ : Subgroup G) * Nat.card (H₁ ⊓ H₃ : Subgroup G)
        * Nat.card (H₂ ⊓ H₃ : Subgroup G)
      ≤ Nat.card (H₁ ⊓ H₂ ⊓ H₃ : Subgroup G) ^ 2 * Nat.card G := by
  have h₁ := card_mul_card_le_card_inf_mul_card_of_le (G := G) (H := H₁ ⊓ H₂) (K := H₁ ⊓ H₃)
    (L := H₁) inf_le_left inf_le_left
  have h₂ := card_mul_card_le_card_inf_mul_card H₁ (H₂ ⊓ H₃)
  have e₁ : (H₁ ⊓ H₂ ⊓ (H₁ ⊓ H₃) : Subgroup G) = H₁ ⊓ H₂ ⊓ H₃ := by
    ext g; simp only [Subgroup.mem_inf]; tauto
  have e₂ : (H₁ ⊓ (H₂ ⊓ H₃) : Subgroup G) = H₁ ⊓ H₂ ⊓ H₃ := (inf_assoc _ _ _).symm
  rw [e₁] at h₁
  rw [e₂] at h₂
  calc Nat.card (H₁ ⊓ H₂ : Subgroup G) * Nat.card (H₁ ⊓ H₃ : Subgroup G)
        * Nat.card (H₂ ⊓ H₃ : Subgroup G)
      ≤ Nat.card (H₁ ⊓ H₂ ⊓ H₃ : Subgroup G) * Nat.card H₁
          * Nat.card (H₂ ⊓ H₃ : Subgroup G) := Nat.mul_le_mul_right _ h₁
    _ = Nat.card (H₁ ⊓ H₂ ⊓ H₃ : Subgroup G) * (Nat.card H₁ * Nat.card (H₂ ⊓ H₃ : Subgroup G)) :=
        by ring
    _ ≤ Nat.card (H₁ ⊓ H₂ ⊓ H₃ : Subgroup G)
          * (Nat.card (H₁ ⊓ H₂ ⊓ H₃ : Subgroup G) * Nat.card G) := Nat.mul_le_mul_left _ h₂
    _ = Nat.card (H₁ ⊓ H₂ ⊓ H₃ : Subgroup G) ^ 2 * Nat.card G := by ring


/-- **Theorem 209 (Chan and Yeung).**  A linear form is valid for the entropies of all tuples
of random variables if and only if it is valid for the indices of subgroups of every finite
group, under the dictionary `H(ξ_I) ↦ log₂ (|G| / |G_I|)` with `G_I = ⋂_{i ∈ I} G_i`.  The
forward direction goes through orbits (Theorem 208) and Theorem 206; the converse uses the
uniform set of Theorem 207, which is an orbit of a symmetric group.  The book prints "linear
equality" for "linear inequality" and states the equivalence informally; this is the precise
form, read off the two examples on the same page.  SUV Theorem 209, p. 324. -/
theorem holdsForEntropies_iff_holdsForGroups (f : LinearForm n) :
    HoldsForEntropies f ↔ HoldsForGroups f :=
  ⟨fun h => (holdsForOrbits_iff_holdsForGroups f).1 (holdsForOrbits_of_holdsForUniformSets f
      (holdsForUniformSets_of_holdsForEntropies f h)),
    fun h => holdsForEntropies_of_holdsForOrbits f ((holdsForOrbits_iff_holdsForGroups f).2 h)⟩

end Kolmogorov
