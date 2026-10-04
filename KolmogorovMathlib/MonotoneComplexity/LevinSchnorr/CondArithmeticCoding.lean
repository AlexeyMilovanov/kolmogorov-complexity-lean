/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic

/-!
# Conditional arithmetic coding: the relativised Theorem 89

SUV Section 5.6, p. 149 (inside the proof of Theorem 93) uses "the relativized version of
Theorem 89: `KM(y | x) ⩽ −log p_x(Ω_y)` for any computable family of measures that
(computably) depends on the parameter `x`", where `p_x(Ω_y) = μ(Ω_{xy}) / μ(Ω_x)`.

This module proves that statement by relativising the arithmetic coding of
`MonotoneComplexity/ArithmeticCoding.lean`.

## The construction

The unconditional arithmetic coding allocates to each string `z` the interval
`π_z = treeIco (cantorMass μ) z ⊆ [0, 1)`, and lets a program `p` produce `z` as soon as the
closed binary interval `I_p ⊆ [0,1]` is contained in the interior of `π_z`.

For the conditional measure `μ_x` the tree of intervals is exactly the *subtree* of the `μ`
tree hanging below `x`, rescaled affinely so that `π_x` becomes `[0, 1)`.  Rather than
dividing by `μ(Ω_x)` — which is not a computable operation, since the divisor may be `0` or
arbitrarily small — we push the affine map the other way and let `p` produce `y` as soon as

`condScale μ x '' I_p ⊆ interior (treeIco (cantorMass μ) (x ++ y))`,

where `condScale μ x t = treeLeftEnd (cantorMass μ) x + μ(Ω_x) · t` maps `[0,1]` onto `π_x`.
This is *literally* the arithmetic coding of `μ_x`, but every quantity occurring in it is a
difference of numbers that the computability of `μ` approximates from both sides, so the
relation is enumerable jointly in `(x, p, y)` with no division anywhere.  This is what makes
the family "computably dependent on the parameter `x`" in the source's sense, and it is why
no `Measure`-valued conditional measure is needed.

At a null condition (`μ(Ω_x) = 0`) the map `condScale μ x` is constant and the relation
degenerates to `y = []`; that is harmless — it is still a stream lower graph — and the
conclusion of the relativised Theorem 89 carries the hypothesis `cantorMass μ x ≠ 0` anyway
(there `μ_x` is not a probability measure, see `condCantorMass_of_cantorMass_eq_zero`).

## Main results

* `condArithmeticCodingLowerGraph_isStreamLowerGraph` — the relation is a stream lower graph
  for every condition `x`;
* `condArithmeticCodingLowerGraph_isRE` — it is r.e. jointly in `(x, p, y)`;
* `exists_const_condCantorMass_mul_le_complexityWeight_condKMOf` — the relativised
  Theorem 89, `2^(-c) · μ_x(Ω_y) ≤ 2^(-KM(y | x))`.
-/

namespace Kolmogorov

open MeasureTheory Set

open scoped ENNReal

/-! ### The affine rescaling onto the interval allocated to the condition -/

/-- The affine map of `[0, 1]` onto the closed interval `π_x` that the arithmetic coding of
`μ` allocates to the condition `x` (SUV p. 149).  For `μ(Ω_x) > 0` this is the inverse of the
rescaling that turns `μ` restricted to `Ω_x` into the conditional measure `μ_x`. -/
noncomputable def condScale (μ : Measure CantorSeq) (x : BitString) (t : ℝ) : ℝ :=
  treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal * t

/-- The conditional scaling factor at `x` is monotone in its argument. -/
lemma condScale_mono (μ : Measure CantorSeq) (x : BitString) : Monotone (condScale μ x) := by
  intro s t hst
  have hM : (0 : ℝ) ≤ (cantorMass μ x).toReal := ENNReal.toReal_nonneg
  simp only [condScale]
  have hmul := mul_le_mul_of_nonneg_left hst hM
  linarith

/-- SUV p. 149: the lower graph of the arithmetic coding of the conditional measure `μ_x`,
written without any division (see the module docstring). -/
def condArithmeticCodingLowerGraph (μ : Measure CantorSeq) (x p y : BitString) : Prop :=
  y = [] ∨
    condScale μ x '' binaryClosedInterval p ⊆ interior (treeIco (cantorMass μ) (x ++ y))

/-! ### Elementary list lemmas -/

/-- Appending a common prefix preserves the prefix relation. -/
lemma append_prefix_append_of_prefix (x : BitString) {y y' : BitString} (h : y' <+: y) :
    x ++ y' <+: x ++ y := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t, by rw [List.append_assoc]⟩

/-- A common prefix may be cancelled from both sides of a prefix relation. -/
lemma prefix_of_append_prefix_append {x y y' : BitString} (h : x ++ y <+: x ++ y') :
    y <+: y' := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  rw [List.append_assoc] at ht
  exact List.append_cancel_left ht

/-- The closed dyadic interval attached to a bit string is nonempty. -/
lemma binaryClosedInterval_nonempty (p : BitString) : (binaryClosedInterval p).Nonempty := by
  rw [binaryClosedInterval]
  refine nonempty_Icc.mpr ?_
  rw [le_add_iff_nonneg_right, lengthMeasure_toReal]
  exact le_of_lt (pow_pos (by norm_num) _)

/-! ### The relation is a stream lower graph -/

/-- The conditional arithmetic coding relation is a stream lower graph: it is monotone in the
program
and prefix-closed in the output. -/
lemma condArithmeticCodingLowerGraph_isStreamLowerGraph (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (x : BitString) :
    IsStreamLowerGraph (condArithmeticCodingLowerGraph μ x) := by
  have ha := isContinuousTreeSemimeasure_cantorMass μ
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_⟩
  · intro p y y' h hy
    rcases h with rfl | h
    · exact Or.inl (List.eq_nil_of_prefix_nil hy)
    · by_cases hy' : y' = []
      · exact Or.inl hy'
      · refine Or.inr (h.trans (interior_mono ?_))
        exact treeIco_prefix_subset ha (append_prefix_append_of_prefix x hy)
  · intro p p' y h hp
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Subset.trans
        (Set.image_mono (binaryClosedInterval_subset_of_prefix hp)) h)
  · intro p y y' hy hy'
    rcases hy with rfl | hy
    · exact Or.inl List.nil_prefix
    · rcases hy' with rfl | hy'
      · exact Or.inr List.nil_prefix
      · obtain ⟨r, hr⟩ := (binaryClosedInterval_nonempty p).image (condScale μ x)
        have h1 := interior_subset (hy hr)
        have h2 := interior_subset (hy' hr)
        rcases prefix_or_prefix_of_mem_treeIco ha h1 h2 with h | h
        · exact Or.inl (prefix_of_append_prefix_append h)
        · exact Or.inr (prefix_of_append_prefix_append h)

/-- For a non-empty output the conditional lower graph is the strict containment of the two
endpoints of `condScale μ x '' I_p` in the open interval allocated to `x ++ y`. -/
lemma condArithmeticCodingLowerGraph_iff_endpoints (μ : Measure CantorSeq) (x p y : BitString)
    (hy : y ≠ []) :
    condArithmeticCodingLowerGraph μ x p y ↔
      treeLeftEnd (cantorMass μ) (x ++ y)
          < condScale μ x ((devBitsToNat p : ℝ) / 2 ^ p.length) ∧
        condScale μ x (((devBitsToNat p : ℝ) + 1) / 2 ^ p.length)
          < treeLeftEnd (cantorMass μ) (x ++ y) + (cantorMass μ (x ++ y)).toReal := by
  rw [condArithmeticCodingLowerGraph, or_iff_right hy, binaryClosedInterval_eq_Icc, treeIco,
    interior_Ico]
  have hle : (devBitsToNat p : ℝ) / 2 ^ p.length
      ≤ ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length := by
    gcongr
    linarith
  constructor
  · intro h
    exact ⟨(h ⟨_, Set.left_mem_Icc.mpr hle, rfl⟩).1, (h ⟨_, Set.right_mem_Icc.mpr hle, rfl⟩).2⟩
  · rintro ⟨h1, h2⟩ r ⟨t, ht, rfl⟩
    rw [Set.mem_Icc] at ht
    exact ⟨lt_of_lt_of_le h1 (condScale_mono μ x ht.1),
      lt_of_le_of_lt (condScale_mono μ x ht.2) h2⟩

/-! ### The arithmetic core

The strict containment of a rescaled dyadic interval in `(L_z, L_z + M_z)` is witnessed at
some finite stage of any two-sided approximation of the four quantities involved.  Everything
is multiplied by `2^n` (`n = |p|`) so that no truncated subtraction and no division occurs;
the resulting stage conditions are inequalities between natural numbers.
-/

/-- The strict nesting of a dyadic subinterval inside the conditional interval is equivalent to a
finite-stage inequality between the integer approximations of the endpoints. -/
lemma cond_endpoints_iff_exists_stage_core (Nx Nz k n : ℕ) (Lx Mx Lz Mz : ℝ)
    (LAx Ax LAz Az : ℕ → ℕ)
    (hLAx : ∀ s, |(LAx s : ℝ) - 2 ^ s * Lx| ≤ (Nx : ℝ))
    (hAx : ∀ s, |(Ax s : ℝ) - 2 ^ s * Mx| ≤ 1)
    (hLAz : ∀ s, |(LAz s : ℝ) - 2 ^ s * Lz| ≤ (Nz : ℝ))
    (hAz : ∀ s, |(Az s : ℝ) - 2 ^ s * Mz| ≤ 1) :
    (Lz < Lx + Mx * ((k : ℝ) / 2 ^ n) ∧ Lx + Mx * (((k : ℝ) + 1) / 2 ^ n) < Lz + Mz) ↔
      ∃ s : ℕ,
        2 ^ n * LAz s + (2 ^ n * Nz + 2 ^ n * Nx + k) < 2 ^ n * LAx s + Ax s * k ∧
          2 ^ n * LAx s + Ax s * (k + 1) + (2 ^ n * Nx + (k + 1) + 2 ^ n * Nz + 2 ^ n)
            < 2 ^ n * LAz s + 2 ^ n * Az s := by
  have hP0 : (0 : ℝ) < 2 ^ n := by positivity
  have hne : ((2 : ℝ) ^ n) ≠ 0 := ne_of_gt hP0
  have hdiv : ∀ c : ℝ, (2 : ℝ) ^ n * (Mx * (c / 2 ^ n)) = Mx * c := by
    intro c
    field_simp
  have hcast1 : ∀ s : ℕ,
      (2 ^ n * LAz s + (2 ^ n * Nz + 2 ^ n * Nx + k) < 2 ^ n * LAx s + Ax s * k) ↔
        ((2 : ℝ) ^ n * (LAz s : ℝ)
            + ((2 : ℝ) ^ n * (Nz : ℝ) + (2 : ℝ) ^ n * (Nx : ℝ) + (k : ℝ))
          < (2 : ℝ) ^ n * (LAx s : ℝ) + (Ax s : ℝ) * (k : ℝ)) := by
    intro s
    rw [← Nat.cast_lt (α := ℝ)]
    push_cast
    constructor <;> intro h <;> linarith
  have hcast2 : ∀ s : ℕ,
      (2 ^ n * LAx s + Ax s * (k + 1) + (2 ^ n * Nx + (k + 1) + 2 ^ n * Nz + 2 ^ n)
          < 2 ^ n * LAz s + 2 ^ n * Az s) ↔
        ((2 : ℝ) ^ n * (LAx s : ℝ) + (Ax s : ℝ) * ((k : ℝ) + 1)
            + ((2 : ℝ) ^ n * (Nx : ℝ) + ((k : ℝ) + 1) + (2 : ℝ) ^ n * (Nz : ℝ) + (2 : ℝ) ^ n)
          < (2 : ℝ) ^ n * (LAz s : ℝ) + (2 : ℝ) ^ n * (Az s : ℝ)) := by
    intro s
    rw [← Nat.cast_lt (α := ℝ)]
    push_cast
    constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨d1, hd1def⟩ : ∃ v : ℝ, v = Lx + Mx * ((k : ℝ) / 2 ^ n) - Lz := ⟨_, rfl⟩
    obtain ⟨d2, hd2def⟩ : ∃ v : ℝ, v = Lz + Mz - (Lx + Mx * (((k : ℝ) + 1) / 2 ^ n)) :=
      ⟨_, rfl⟩
    obtain ⟨E1, hE1def⟩ : ∃ v : ℝ,
        v = (2 : ℝ) ^ n * (Nz : ℝ) + (2 : ℝ) ^ n * (Nx : ℝ) + (k : ℝ) := ⟨_, rfl⟩
    obtain ⟨E2, hE2def⟩ : ∃ v : ℝ, v = (2 : ℝ) ^ n * (Nx : ℝ) + ((k : ℝ) + 1)
        + (2 : ℝ) ^ n * (Nz : ℝ) + (2 : ℝ) ^ n := ⟨_, rfl⟩
    have hd1 : 0 < d1 := by rw [hd1def]; linarith
    have hd2 : 0 < d2 := by rw [hd2def]; linarith
    have hPd1 : (2 : ℝ) ^ n * d1 = 2 ^ n * Lx + Mx * (k : ℝ) - 2 ^ n * Lz := by
      rw [hd1def, ← hdiv (k : ℝ)]; ring
    have hPd2 : (2 : ℝ) ^ n * d2
        = 2 ^ n * Lz + 2 ^ n * Mz - 2 ^ n * Lx - Mx * ((k : ℝ) + 1) := by
      rw [hd2def, ← hdiv ((k : ℝ) + 1)]; ring
    obtain ⟨s1, hs1⟩ := pow_unbounded_of_one_lt (2 * E1 / (2 ^ n * d1))
      (by norm_num : (1 : ℝ) < 2)
    obtain ⟨s2, hs2⟩ := pow_unbounded_of_one_lt (2 * E2 / (2 ^ n * d2))
      (by norm_num : (1 : ℝ) < 2)
    refine ⟨max s1 s2, (hcast1 _).mpr ?_, (hcast2 _).mpr ?_⟩
    · have hmono : (2 : ℝ) ^ s1 ≤ 2 ^ (max s1 s2) :=
        pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
      have hb1 : 2 * E1 < (2 ^ n * Lx + Mx * (k : ℝ) - 2 ^ n * Lz) * 2 ^ (max s1 s2) := by
        have h := lt_of_lt_of_le hs1 hmono
        rw [div_lt_iff₀ (by positivity)] at h
        rw [← hPd1]
        linarith
      have e1 : (2 : ℝ) ^ n * (LAz (max s1 s2) : ℝ)
          ≤ 2 ^ n * (2 ^ (max s1 s2) * Lz + (Nz : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hLAz (max s1 s2))).2]) hP0.le
      have e2 : (2 : ℝ) ^ n * (2 ^ (max s1 s2) * Lx - (Nx : ℝ))
          ≤ 2 ^ n * (LAx (max s1 s2) : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hLAx (max s1 s2))).1]) hP0.le
      have e3 : (2 ^ (max s1 s2) * Mx - 1) * (k : ℝ) ≤ (Ax (max s1 s2) : ℝ) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp (hAx (max s1 s2))).1])
          (Nat.cast_nonneg k)
      rw [hE1def] at hb1
      linarith
    · have hmono : (2 : ℝ) ^ s2 ≤ 2 ^ (max s1 s2) :=
        pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
      have hb2 : 2 * E2
          < (2 ^ n * Lz + 2 ^ n * Mz - 2 ^ n * Lx - Mx * ((k : ℝ) + 1)) * 2 ^ (max s1 s2) := by
        have h := lt_of_lt_of_le hs2 hmono
        rw [div_lt_iff₀ (by positivity)] at h
        rw [← hPd2]
        linarith
      have e1 : (2 : ℝ) ^ n * (LAx (max s1 s2) : ℝ)
          ≤ 2 ^ n * (2 ^ (max s1 s2) * Lx + (Nx : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hLAx (max s1 s2))).2]) hP0.le
      have e2 : (Ax (max s1 s2) : ℝ) * ((k : ℝ) + 1)
          ≤ (2 ^ (max s1 s2) * Mx + 1) * ((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp (hAx (max s1 s2))).2])
          (by positivity)
      have e3 : (2 : ℝ) ^ n * (2 ^ (max s1 s2) * Lz - (Nz : ℝ))
          ≤ 2 ^ n * (LAz (max s1 s2) : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hLAz (max s1 s2))).1]) hP0.le
      have e4 : (2 : ℝ) ^ n * (2 ^ (max s1 s2) * Mz - 1)
          ≤ 2 ^ n * (Az (max s1 s2) : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hAz (max s1 s2))).1]) hP0.le
      rw [hE2def] at hb2
      linarith
  · rintro ⟨s, C1, C2⟩
    have C1R := (hcast1 s).mp C1
    have C2R := (hcast2 s).mp C2
    have f1 : (2 : ℝ) ^ n * (2 ^ s * Lz - (Nz : ℝ)) ≤ 2 ^ n * (LAz s : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hLAz s)).1]) hP0.le
    have f2 : (2 : ℝ) ^ n * (LAx s : ℝ) ≤ 2 ^ n * (2 ^ s * Lx + (Nx : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hLAx s)).2]) hP0.le
    have f3 : (Ax s : ℝ) * (k : ℝ) ≤ (2 ^ s * Mx + 1) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp (hAx s)).2]) (Nat.cast_nonneg k)
    have f4 : (2 : ℝ) ^ n * (2 ^ s * Lx - (Nx : ℝ)) ≤ 2 ^ n * (LAx s : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hLAx s)).1]) hP0.le
    have f5 : (2 ^ s * Mx - 1) * ((k : ℝ) + 1) ≤ (Ax s : ℝ) * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp (hAx s)).1]) (by positivity)
    have f6 : (2 : ℝ) ^ n * (LAz s : ℝ) ≤ 2 ^ n * (2 ^ s * Lz + (Nz : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hLAz s)).2]) hP0.le
    have f7 : (2 : ℝ) ^ n * (Az s : ℝ) ≤ 2 ^ n * (2 ^ s * Mz + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hAz s)).2]) hP0.le
    have hQ0 : (0 : ℝ) < 2 ^ s := by positivity
    constructor
    · have hrw : ((2 : ℝ) ^ n * 2 ^ s) * (Lx + Mx * ((k : ℝ) / 2 ^ n))
          = 2 ^ n * 2 ^ s * Lx + 2 ^ s * (Mx * (k : ℝ)) := by
        rw [← hdiv (k : ℝ)]; ring
      have key : ((2 : ℝ) ^ n * 2 ^ s) * Lz
          < ((2 : ℝ) ^ n * 2 ^ s) * (Lx + Mx * ((k : ℝ) / 2 ^ n)) := by
        rw [hrw]
        nlinarith [C1R, f1, f2, f3, hQ0]
      exact lt_of_mul_lt_mul_left key (by positivity)
    · have hrw : ((2 : ℝ) ^ n * 2 ^ s) * (Lx + Mx * (((k : ℝ) + 1) / 2 ^ n))
          = 2 ^ n * 2 ^ s * Lx + 2 ^ s * (Mx * ((k : ℝ) + 1)) := by
        rw [← hdiv ((k : ℝ) + 1)]; ring
      have key : ((2 : ℝ) ^ n * 2 ^ s) * (Lx + Mx * (((k : ℝ) + 1) / 2 ^ n))
          < ((2 : ℝ) ^ n * 2 ^ s) * (Lz + Mz) := by
        rw [hrw]
        nlinarith [C2R, f4, f5, f6, f7, hQ0]
      exact lt_of_mul_lt_mul_left key (by positivity)

/-! ### The stage predicate and its enumerability -/

/-- The stage-`s` approximation of the conditional lower graph.  All four quantities of the
core lemma are replaced by their stage-`s` approximants and the error budget is paid
explicitly; see `cond_endpoints_iff_exists_stage_core`. -/
def condArithmeticCodingStage (a : BitString → ℕ → ℕ) (s : ℕ) (x p y : BitString) : Bool :=
  if y.isEmpty then true else
    decide (2 ^ p.length * treeLeftEndApprox a (x ++ y) s
        + (2 ^ p.length * (x ++ y).length + 2 ^ p.length * x.length + devBitsToNat p)
      < 2 ^ p.length * treeLeftEndApprox a x s + a x s * devBitsToNat p) &&
    decide (2 ^ p.length * treeLeftEndApprox a x s + a x s * (devBitsToNat p + 1)
        + (2 ^ p.length * x.length + (devBitsToNat p + 1)
          + 2 ^ p.length * (x ++ y).length + 2 ^ p.length)
      < 2 ^ p.length * treeLeftEndApprox a (x ++ y) s + 2 ^ p.length * a (x ++ y) s)

/-- For a nonempty output the stage test unfolds to the pair of integer inequalities comparing the
approximated endpoints of the intervals of `x` and `x ++ y`. -/
lemma condArithmeticCodingStage_of_ne_nil (a : BitString → ℕ → ℕ) (s : ℕ) (x p y : BitString)
    (hy : ¬ y.isEmpty = true) :
    condArithmeticCodingStage a s x p y = true ↔
      (2 ^ p.length * treeLeftEndApprox a (x ++ y) s
          + (2 ^ p.length * (x ++ y).length + 2 ^ p.length * x.length + devBitsToNat p)
        < 2 ^ p.length * treeLeftEndApprox a x s + a x s * devBitsToNat p) ∧
      (2 ^ p.length * treeLeftEndApprox a x s + a x s * (devBitsToNat p + 1)
          + (2 ^ p.length * x.length + (devBitsToNat p + 1)
            + 2 ^ p.length * (x ++ y).length + 2 ^ p.length)
        < 2 ^ p.length * treeLeftEndApprox a (x ++ y) s + 2 ^ p.length * a (x ++ y) s) := by
  unfold condArithmeticCodingStage
  rw [ite_eq_right hy]
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- For a computable dyadic approximation of the mass function the stage test of conditional
arithmetic coding is computable. -/
lemma computable_condArithmeticCodingStage {a : BitString → ℕ → ℕ} (ha : Computable₂ a) :
    Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      condArithmeticCodingStage a r.2 r.1.1 r.1.2.1 r.1.2.2) := by
  have hx : Computable (fun r : (BitString × BitString × BitString) × ℕ => r.1.1) :=
    Computable.fst.comp Computable.fst
  have hp : Computable (fun r : (BitString × BitString × BitString) × ℕ => r.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hy : Computable (fun r : (BitString × BitString × BitString) × ℕ => r.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun r : (BitString × BitString × BitString) × ℕ => r.2) :=
    Computable.snd
  have hadd : Computable₂ (fun m n : ℕ => m + n) := Primrec.nat_add.to_comp
  have hmul : Computable₂ (fun m n : ℕ => m * n) := Primrec.nat_mul.to_comp
  have hlt : Computable₂ (fun m n : ℕ => decide (m < n)) := primrec_decide_nat_lt.to_comp
  have happ : Computable₂ (fun u v : BitString => u ++ v) := Primrec.list_append.to_comp
  have hz : Computable (fun r : (BitString × BitString × BitString) × ℕ => r.1.1 ++ r.1.2.2) :=
    happ.comp hx hy
  have hP : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      2 ^ r.1.2.1.length) :=
    primrec_two_pow_aux.to_comp.comp (Computable.list_length.comp hp)
  have hk : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      devBitsToNat r.1.2.1) := primrec_devBitsToNat.to_comp.comp hp
  have hk1 : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      devBitsToNat r.1.2.1 + 1) := Primrec.succ.to_comp.comp hk
  have hxlen : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      r.1.1.length) := Computable.list_length.comp hx
  have hzlen : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      (r.1.1 ++ r.1.2.2).length) := Computable.list_length.comp hz
  have hlax : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      treeLeftEndApprox a r.1.1 r.2) := (computable_treeLeftEndApprox ha).comp hx hs
  have hlaz : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      treeLeftEndApprox a (r.1.1 ++ r.1.2.2) r.2) :=
    (computable_treeLeftEndApprox ha).comp hz hs
  have hax : Computable (fun r : (BitString × BitString × BitString) × ℕ => a r.1.1 r.2) :=
    ha.comp hx hs
  have haz : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      a (r.1.1 ++ r.1.2.2) r.2) := ha.comp hz hs
  have hempty : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      r.1.2.2.isEmpty) := primrec_decide_list_isEmpty.to_comp.comp hy
  have hbudget1 : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      2 ^ r.1.2.1.length * (r.1.1 ++ r.1.2.2).length
        + 2 ^ r.1.2.1.length * r.1.1.length + devBitsToNat r.1.2.1) :=
    hadd.comp (hadd.comp (hmul.comp hP hzlen) (hmul.comp hP hxlen)) hk
  have hbudget2 : Computable (fun r : (BitString × BitString × BitString) × ℕ =>
      2 ^ r.1.2.1.length * r.1.1.length + (devBitsToNat r.1.2.1 + 1)
        + 2 ^ r.1.2.1.length * (r.1.1 ++ r.1.2.2).length + 2 ^ r.1.2.1.length) :=
    hadd.comp (hadd.comp (hadd.comp (hmul.comp hP hxlen) hk1) (hmul.comp hP hzlen)) hP
  have hc1 := hlt.comp (hadd.comp (hmul.comp hP hlaz) hbudget1)
    (hadd.comp (hmul.comp hP hlax) (hmul.comp hax hk))
  have hc2 := hlt.comp
    (hadd.comp (hadd.comp (hmul.comp hP hlax) (hmul.comp hax hk1)) hbudget2)
    (hadd.comp (hmul.comp hP hlaz) (hmul.comp hP haz))
  refine (Computable.cond hempty (Computable.const true)
    (Primrec.and.to_comp.comp hc1 hc2)).of_eq ?_
  rintro ⟨⟨x, p, y⟩, s⟩
  simp only [condArithmeticCodingStage]
  by_cases h1 : y.isEmpty = true
  · simp [h1]
  · simp [h1]

/-- The conditional arithmetic coding relation holds exactly when some finite stage of the integer
test already certifies it. -/
lemma condArithmeticCodingLowerGraph_iff_exists_stage (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (a : BitString → ℕ → ℕ)
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (x p y : BitString) :
    condArithmeticCodingLowerGraph μ x p y ↔
      ∃ s : ℕ, condArithmeticCodingStage a s x p y = true := by
  by_cases hynil : y = []
  · subst hynil
    refine ⟨fun _ => ⟨0, ?_⟩, fun _ => Or.inl rfl⟩
    simp [condArithmeticCodingStage]
  have hye : ¬ y.isEmpty = true := by simpa using hynil
  rw [condArithmeticCodingLowerGraph_iff_endpoints μ x p y hynil]
  have hcore := cond_endpoints_iff_exists_stage_core x.length (x ++ y).length
    (devBitsToNat p) p.length (treeLeftEnd (cantorMass μ) x) ((cantorMass μ x).toReal)
    (treeLeftEnd (cantorMass μ) (x ++ y)) ((cantorMass μ (x ++ y)).toReal)
    (fun s => treeLeftEndApprox a x s) (fun s => a x s)
    (fun s => treeLeftEndApprox a (x ++ y) s) (fun s => a (x ++ y) s)
    (fun s => abs_treeLeftEndApprox_sub_le μ ha x s) (fun s => abs_approx_sub_le_one μ ha x s)
    (fun s => abs_treeLeftEndApprox_sub_le μ ha (x ++ y) s)
    (fun s => abs_approx_sub_le_one μ ha (x ++ y) s)
  simp only [condScale]
  rw [hcore]
  exact exists_congr fun s => (condArithmeticCodingStage_of_ne_nil a s x p y hye).symm

/-- For a computable measure the conditional arithmetic coding relation is recursively enumerable.
-/
lemma condArithmeticCodingLowerGraph_isRE (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) :
    IsRE (fun t : BitString × BitString × BitString =>
      condArithmeticCodingLowerGraph μ t.1 t.2.1 t.2.2) := by
  obtain ⟨a, ha_comp, ha⟩ := hμ
  have hstage : IsRE (fun r : (BitString × BitString × BitString) × ℕ =>
      condArithmeticCodingStage a r.2 r.1.1 r.1.2.1 r.1.2.2 = true) :=
    isRE_of_computable_bool _ (fun r => condArithmeticCodingStage a r.2 r.1.1 r.1.2.1 r.1.2.2)
      (fun _ => Iff.rfl) (computable_condArithmeticCodingStage ha_comp)
  have hex : IsRE (fun t : BitString × BitString × BitString => ∃ s : ℕ,
      condArithmeticCodingStage a s t.1 t.2.1 t.2.2 = true) :=
    IsRE.exists_encodable (R := fun (t : BitString × BitString × BitString) (s : ℕ) =>
      condArithmeticCodingStage a s t.1 t.2.1 t.2.2 = true) hstage
  exact hex.of_iff (fun t =>
    (condArithmeticCodingLowerGraph_iff_exists_stage μ a ha t.1 t.2.1 t.2.2).symm)

/-! ### The length bound -/

/-- Real core of the length bound: a closed binary interval whose affine image lands strictly
inside `(L_z, L_z + M_z)` and whose length is at least a quarter of `M_z / M_x`. -/
lemma exists_binaryClosedInterval_affine_image_subset {Lx Mx Lz Mz : ℝ} (hMx : 0 < Mx)
    (hMz : 0 < Mz) (h1 : Lx ≤ Lz) (h2 : Lz + Mz ≤ Lx + Mx) :
    ∃ p : BitString,
      (fun t => Lx + Mx * t) '' binaryClosedInterval p ⊆ Set.Ioo Lz (Lz + Mz) ∧
        Mz / Mx / 4 ≤ (2 : ℝ)⁻¹ ^ p.length := by
  have hne : Mx ≠ 0 := ne_of_gt hMx
  have hA : Mx * ((Lz - Lx) / Mx) = Lz - Lx := by field_simp
  have hB : Mx * ((Lz + Mz - Lx) / Mx) = Lz + Mz - Lx := by field_simp
  have hl0 : 0 ≤ (Lz - Lx) / Mx := div_nonneg (by linarith) hMx.le
  have hdiff : (Lz + Mz - Lx) / Mx - (Lz - Lx) / Mx = Mz / Mx := by
    rw [div_sub_div_same]
    congr 1
    ring
  have hlr : (Lz - Lx) / Mx < (Lz + Mz - Lx) / Mx := by
    have hpos : 0 < Mz / Mx := div_pos hMz hMx
    linarith
  have hr1 : (Lz + Mz - Lx) / Mx ≤ 1 := by
    rw [div_le_one hMx]
    linarith
  obtain ⟨p, hsub, hlen⟩ := exists_binaryClosedInterval_subset_Ioo_pow hl0 hlr hr1
  rw [hdiff] at hlen
  refine ⟨p, ?_, hlen⟩
  rintro w ⟨t, ht, rfl⟩
  have hm := hsub ht
  rw [Set.mem_Ioo] at hm
  rw [Set.mem_Ioo]
  constructor
  · have hmul := mul_lt_mul_of_pos_left hm.1 hMx
    rw [hA] at hmul
    linarith
  · have hmul := mul_lt_mul_of_pos_left hm.2 hMx
    rw [hB] at hmul
    linarith

/-- Every conditional cylinder of nonzero mass has a code whose length is at most
`-log₂ μ(y | x) + 2`. -/
lemma exists_condProgram_length_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {x : BitString} (hx : cantorMass μ x ≠ 0) {y : BitString}
    (hy : cantorMass μ (x ++ y) ≠ 0) :
    ∃ p : BitString, condArithmeticCodingLowerGraph μ x p y ∧
      (2 : ℝ≥0∞)⁻¹ ^ 2 * condCantorMass μ x y ≤ (2 : ℝ≥0∞)⁻¹ ^ p.length := by
  have hcts := isContinuousTreeSemimeasure_cantorMass μ
  have hMxpos : 0 < (cantorMass μ x).toReal := ENNReal.toReal_pos hx (measure_ne_top μ _)
  have hMzpos : 0 < (cantorMass μ (x ++ y)).toReal :=
    ENNReal.toReal_pos hy (measure_ne_top μ _)
  have hsub : treeIco (cantorMass μ) (x ++ y) ⊆ treeIco (cantorMass μ) x :=
    treeIco_prefix_subset hcts (⟨y, rfl⟩ : x <+: x ++ y)
  obtain ⟨hle1, hle2⟩ := (Set.Ico_subset_Ico_iff (by linarith :
    treeLeftEnd (cantorMass μ) (x ++ y)
      < treeLeftEnd (cantorMass μ) (x ++ y) + (cantorMass μ (x ++ y)).toReal)).mp hsub
  obtain ⟨p, hsubp, hlen⟩ := exists_binaryClosedInterval_affine_image_subset hMxpos hMzpos
    hle1 hle2
  refine ⟨p, Or.inr ?_, ?_⟩
  · rw [treeIco, interior_Ico]
    exact hsubp
  · have hne : condCantorMass μ x y ≠ ⊤ := ENNReal.div_ne_top (measure_ne_top μ _) hx
    rw [← ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hne)
      (ENNReal.pow_ne_top (by simp))]
    have h1 : ((2 : ℝ≥0∞)⁻¹ ^ 2 * condCantorMass μ x y).toReal
        = (cantorMass μ (x ++ y)).toReal / (cantorMass μ x).toReal / 4 := by
      rw [ENNReal.toReal_mul, condCantorMass, ENNReal.toReal_div]
      norm_num
      ring
    have h2 : ((2 : ℝ≥0∞)⁻¹ ^ p.length).toReal = (2 : ℝ)⁻¹ ^ p.length := by simp
    rw [h1, h2]
    exact hlen

/-! ### The relativised Theorem 89 -/

/-- **SUV Theorem 89, relativised version** (Section 5.6, p. 149, used in the proof of
Theorem 93): `KM(y | x) ≤ -log μ_x(Ω_y) + c` with one constant `c` uniform in both `x` and
`y`, where `μ_x(Ω_y) = μ(Ω_{xy}) / μ(Ω_x)`.

Multiplicatively, `2^(-c) · μ_x(Ω_y) ≤ 2^(-KM(y | x))`.  The proof is the conditional
arithmetic coding of this module: the family `x ↦ μ_x` is realised as the affine rescaling
`condScale μ x` of the arithmetic-coding tree of `μ`, so no division ever has to be
performed, and the resulting conditional stream map is compared with the optimal one. -/
theorem exists_const_condCantorMass_mul_le_complexityWeight_condKMOf (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ)
    {D : BitString → BitStream → BitStream}
    (hD : IsOptimalConditionalMonotoneDecompressor D) :
    ∃ c : ℕ, ∀ x : BitString, cantorMass μ x ≠ 0 → ∀ y : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c * condCantorMass μ x y ≤ complexityWeight (condKMOf D y x) := by
  have hLG : ∀ x : BitString, IsStreamLowerGraph (condArithmeticCodingLowerGraph μ x) :=
    fun x => condArithmeticCodingLowerGraph_isStreamLowerGraph μ x
  have hfc : IsComputableConditionalStreamMap
      (fun x => streamMapOfLowerGraph (condArithmeticCodingLowerGraph μ x) (hLG x)) := by
    refine ⟨fun x => streamMapOfLowerGraph_isContinuousStreamMap _, ?_⟩
    refine (condArithmeticCodingLowerGraph_isRE μ hμ).of_iff (fun t => ?_)
    exact (streamMapOfLowerGraph_finite_spec (hLG t.1) t.2.1 t.2.2).symm
  obtain ⟨c₀, hc₀⟩ := hD.2 _ hfc
  refine ⟨c₀ + 2, fun x hx y => ?_⟩
  by_cases hz : cantorMass μ (x ++ y) = 0
  · have hzero : condCantorMass μ x y = 0 := by simp [condCantorMass, hz]
    simp [hzero]
  · obtain ⟨p, hp, hplen⟩ := exists_condProgram_length_le μ hx hz
    have hprod : monotoneProduces
        (streamMapOfLowerGraph (condArithmeticCodingLowerGraph μ x) (hLG x)) p y :=
      (streamMapOfLowerGraph_finite_spec (hLG x) p y).mpr hp
    have h1 : condKMOf
        (fun x => streamMapOfLowerGraph (condArithmeticCodingLowerGraph μ x) (hLG x)) y x
        ≤ (p.length : ℕ∞) := KMOf_le_length_of_monotoneProduces hprod
    have h2 : condKMOf D y x ≤ (p.length : ℕ∞) + (c₀ : ℕ∞) :=
      le_trans (hc₀ y x) (add_le_add h1 le_rfl)
    calc (2 : ℝ≥0∞)⁻¹ ^ (c₀ + 2) * condCantorMass μ x y
        = (2 : ℝ≥0∞)⁻¹ ^ c₀ * ((2 : ℝ≥0∞)⁻¹ ^ 2 * condCantorMass μ x y) := by
          rw [pow_add, mul_assoc]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞)⁻¹ ^ p.length := by gcongr
      _ = complexityWeight ((p.length : ℕ∞) + (c₀ : ℕ∞)) := by
          rw [complexityWeight_add_nat, complexityWeight_coe, mul_comm]
      _ ≤ complexityWeight (condKMOf D y x) := complexityWeight_le_of_le h2

end Kolmogorov
