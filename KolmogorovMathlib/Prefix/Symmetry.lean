/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.Encoding
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.AlgorithmicProbability.ConditionalCoding

/-!
# Prefix Complexity of Pairs and Symmetry of Information

This module adds a small interface for the prefix complexity of a pair of
bitstrings. The pair itself is encoded as a single bitstring by writing a
self-delimiting unary code for the length of the first component, followed by the
first component and then the second component. The concrete pair code and the
two-stage builder infrastructure live in `KolmogorovMathlib.Prefix.TwoStage`.

The staged symmetry-of-information statement uses the faithful prefix-complexity
form

`K(x,y) = K(x) + K(y | x, K(x)) + O(1)`.

Since `KP U x []` has type `ENat`, the context contains a natural witness `kx`
with `(kx : ENat) = KP U x []`. This avoids silently turning `top` into `0`, and
keeps the theorem statement close to the standard mathematical formulation.
-/

namespace Kolmogorov

/-- Plain prefix complexity, written as a prefix-specific abbreviation. -/
noncomputable def KPPlain (U : Map) (x : BitString) : ENat :=
  KP U x []

/-- Prefix complexity of the pair `(x, y)`, using `pairCode` as the output code. -/
noncomputable def KPPair (U : Map) (x y : BitString) : ENat :=
  KP U (pairCode x y) []

/-- `KPPlain` is definitionally the conditional prefix complexity with empty context. -/
@[simp] theorem KPPlain_eq_KP (U : Map) (x : BitString) :
    KPPlain U x = KP U x [] :=
  rfl

/-- `KPPair` is definitionally `KP` of the encoded pair with empty context. -/
@[simp] theorem KPPair_eq_KP_pairCode (U : Map) (x y : BitString) :
    KPPair U x y = KP U (pairCode x y) [] :=
  rfl

/-- A context containing `x` together with a natural value for `K(x)`. -/
def prefixComplexityContext (x : BitString) (kx : Nat) : BitString :=
  pairCode x (natCode kx)

/-- `kx` is a natural-number witness for the finite prefix complexity of `x`. -/
def HasPrefixComplexityValue (U : Map) (x : BitString) (kx : Nat) : Prop :=
  (kx : ENat) = KPPlain U x

/-- The context encoder unfolds to the concrete pair code. -/
@[simp] theorem prefixComplexityContext_eq_pairCode (x : BitString) (kx : Nat) :
    prefixComplexityContext x kx = pairCode x (natCode kx) :=
  rfl

/-! ### Computability of the context encoders -/

/-- The `(x, K(x))` context map is computable. -/
theorem prefixComplexityContext_computable :
    Computable (fun p : BitString × ℕ => prefixComplexityContext p.1 p.2) := by
  have h : (fun p : BitString × ℕ => prefixComplexityContext p.1 p.2)
      = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
          (fun p : BitString × ℕ => (p.1, natCode p.2)) := by
    funext p; rfl
  rw [h]
  exact pairCode_computable.comp (Computable.fst.pair (natCode_computable.comp Computable.snd))

/-! ### Staged interfaces for the prefix SoI infrastructure -/

/-- A prefix decompressor with a direct coding bound for the faithful two-stage
pair construction proves the upper direction for any optimal prefix decompressor. -/
theorem KPPair_chain_upper_of_prefix_decompressor (U M : Map)
    (hU : IsOptimalPrefixConditional U) (hM : IsPrefixDecompressor M) (c0 : Nat)
    (hbound : ∀ x y : BitString, ∀ kx : Nat,
      HasPrefixComplexityValue U x kx →
        KP M (pairCode x y) [] ≤
          KPPlain U x + KP U y (prefixComplexityContext x kx) + (c0 : ENat)) :
    Exists fun c : Nat => forall x y : BitString, forall kx : Nat,
      HasPrefixComplexityValue U x kx ->
        KPPair U x y <= KPPlain U x + KP U y (prefixComplexityContext x kx) + (c : ENat) := by
  obtain ⟨c1, h1⟩ := hU.invariance hM
  refine ⟨c0 + c1, ?_⟩
  intro x y kx hkx
  calc
    KPPair U x y = KP U (pairCode x y) [] := rfl
    _ ≤ KP M (pairCode x y) [] + (c1 : ENat) := h1 (pairCode x y) []
    _ ≤ (KPPlain U x + KP U y (prefixComplexityContext x kx) + (c0 : ENat))
        + (c1 : ENat) := add_le_add_left (hbound x y kx hkx) _
    _ = KPPlain U x + KP U y (prefixComplexityContext x kx) + ((c0 + c1 : Nat) : ENat) := by
      rw [Nat.cast_add]
      ac_rfl

/-- The same staged upper-direction interface for the deliberately weaker bound
where the second-stage conditional program sees only `x` as context. -/
theorem KPPair_chain_upper_weak_of_prefix_decompressor (U M : Map)
    (hU : IsOptimalPrefixConditional U) (hM : IsPrefixDecompressor M) (c0 : Nat)
    (hbound : ∀ x y : BitString,
        KP M (pairCode x y) [] ≤ KPPlain U x + KP U y x + (c0 : ENat)) :
    Exists fun c : Nat => forall x y : BitString,
      KPPair U x y <= KPPlain U x + KP U y x + (c : ENat) := by
  obtain ⟨c1, h1⟩ := hU.invariance hM
  refine ⟨c0 + c1, ?_⟩
  intro x y
  calc
    KPPair U x y = KP U (pairCode x y) [] := rfl
    _ ≤ KP M (pairCode x y) [] + (c1 : ENat) := h1 (pairCode x y) []
    _ ≤ (KPPlain U x + KP U y x + (c0 : ENat)) + (c1 : ENat) :=
      add_le_add_left (hbound x y) _
    _ = KPPlain U x + KP U y x + ((c0 + c1 : Nat) : ENat) := by
      rw [Nat.cast_add]
      ac_rfl

/-- The upper, coding direction of prefix symmetry of information:
`K(x,y) ≤ K(x) + K(y | x, K(x)) + O(1)`.

The proof instantiates the staged interface with the explicit, dovetailing
two-stage prefix decompressor `twoStagePairBuilder` (whose computability is
proved in `KolmogorovMathlib.Prefix.TwoStage`). -/
theorem KPPair_chain_upper (U : Map) (hU : IsOptimalPrefixConditional U) :
    Exists fun c : Nat => forall x y : BitString, forall kx : Nat,
      HasPrefixComplexityValue U x kx ->
        KPPair U x y <= KPPlain U x + KP U y (prefixComplexityContext x kx) + (c : ENat) := by
  have hM : IsPrefixDecompressor (twoStagePairBuilder U prefixComplexityContext) :=
    twoStagePairBuilder_isPrefixDecompressor hU.isDecompressor hU.isPrefixMachine
      prefixComplexityContext_computable
  refine KPPair_chain_upper_of_prefix_decompressor U
    (twoStagePairBuilder U prefixComplexityContext) hU hM 0 ?_
  intro x y kx hkx
  -- `K(x)` is finite (its natural witness is `kx`).
  have hKx : KPPlain U x ≠ ⊤ := by
    rw [← hkx]; exact ENat.coe_ne_top kx
  obtain ⟨p, hp, hplen⟩ := exists_program_of_KP_ne_top (M := U) (x := x) (y := []) hKx
  -- `p.length = kx`.
  have hpl_eq : (p.length : ENat) = KPPlain U x := hplen
  have hp_kx : p.length = kx := by
    have : (p.length : ENat) = (kx : ENat) := by rw [hpl_eq, ← hkx]
    exact_mod_cast this
  -- Split on whether `K(y | x, K(x))` is finite.
  by_cases hKy : KP U y (prefixComplexityContext x kx) = ⊤
  · -- The right-hand side is `⊤`.
    rw [hKy]
    simp
  · obtain ⟨q, hq, hqlen⟩ :=
      exists_program_of_KP_ne_top (M := U) (x := y)
        (y := prefixComplexityContext x kx) hKy
    -- `q` produces `y` from `ctx x p.length` since `p.length = kx`.
    have hq' : produces U q (prefixComplexityContext x p.length) y := by
      rw [hp_kx]; exact hq
    have hbound := KP_twoStagePairBuilder_le_of_produces
      (U := U) (ctx := prefixComplexityContext) hU.isPrefixMachine hp hq'
    calc
      KP (twoStagePairBuilder U prefixComplexityContext) (pairCode x y) []
          ≤ ((p.length + q.length : Nat) : ENat) := hbound
      _ = KPPlain U x + KP U y (prefixComplexityContext x kx) := by
            rw [Nat.cast_add, hpl_eq, hqlen]
      _ = KPPlain U x + KP U y (prefixComplexityContext x kx) + (0 : ENat) := by
            rw [add_zero]

open scoped ENNReal in
/-- **Reduction of the lower direction to a single conditional coding bound.**

The Levin–Gács lower direction, transcribed into the project's multiplicative
`ℝ≥0∞` setting, collapses to one analytic hypothesis `hcode`: in the context
`(x, k)` *with `k = K(x)`*, the conditional prefix complexity weight
`2^{-K(y | x, k)}` dominates the *scaled section mass*
`2^{-c₁} · m_U(⟨x,y⟩) · 2^{k}`, where `m_U(⟨x,y⟩)` is the a priori probability of
the encoded pair. This is exactly the conditional coding theorem applied to the
section semimeasure `y ↦ m_U(⟨x,y⟩) · 2^{k}` (which is a genuine conditional
semimeasure once the marginal coding bound `∑_y m_U(⟨x,y⟩) ≤ 2^{-k}` holds at
`k = K(x)`).

**Important correction.** The bound is only requested at `k = K(x)`, expressed by
the guard `HasPrefixComplexityValue U x k`. An *unguarded* `∀ k` version of
`hcode` is in fact **false**: for fixed `x, y` with `m_U(⟨x,y⟩) > 0`, the left
side `2^{-c₁} · m_U(⟨x,y⟩) · 2^{k}` grows without bound in `k`, while the right
side `2^{-K(y | x, k)} ≤ 1` stays bounded. The proof of the reduction only ever
instantiates the bound at the natural witness `k = kx` of `K(x)`, so the guard
loses nothing and makes `hcode` a satisfiable (true) statement.

Given `hcode`, the additive lower bound follows by pure `ENat`/`ENNReal`
arithmetic: the easy coding bound `2^{-K(x,y)} ≤ m_U(⟨x,y⟩)`, the cancellation
`2^{k} · 2^{-k} = 1`, and the multiplicative-to-additive bridge
`le_add_nat_of_complexityWeight_le`. No counting infrastructure leaks into this
proof — it is entirely isolated inside `hcode`. -/
theorem KPPair_chain_lower_of_conditional_coding (U : Map)
    (_hU : IsOptimalPrefixConditional U)
    (hcode : ∃ c₁ : ℕ, ∀ x y : BitString, ∀ k : ℕ,
        HasPrefixComplexityValue U x k →
        (2 : ℝ≥0∞)⁻¹ ^ c₁ * (aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
          ≤ complexityWeight (KP U y (prefixComplexityContext x k))) :
    Exists fun c : Nat => forall x y : BitString, forall kx : Nat,
      HasPrefixComplexityValue U x kx ->
        KPPlain U x + KP U y (prefixComplexityContext x kx) <= KPPair U x y + (c : ENat) := by
  obtain ⟨c₁, hc₁⟩ := hcode
  refine ⟨c₁, ?_⟩
  intro x y kx hkx
  -- Replace `K(x)` by its natural witness `kx`.
  rw [← hkx]
  by_cases hP : KPPair U x y = ⊤
  · rw [hP]; simp
  · -- Easy coding bound for the pair: `2^{-K(x,y)} ≤ m_U(⟨x,y⟩)`.
    have heasy : complexityWeight (KPPair U x y)
        ≤ aprioriMeasure U (pairCode x y) [] := by
      rw [KPPair_eq_KP_pairCode]
      exact complexityWeight_KP_le_aprioriMeasure U (pairCode x y) []
    -- `2^{kx} · 2^{-kx} = 1`.
    have hcancel : (2 : ℝ≥0∞) ^ kx * (2 : ℝ≥0∞)⁻¹ ^ kx = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    -- `2^{-(kx + K(y | x,kx))} = 2^{-K(y | x,kx)} · 2^{-kx}`.
    have hcw : complexityWeight ((kx : ENat) + KP U y (prefixComplexityContext x kx))
        = complexityWeight (KP U y (prefixComplexityContext x kx)) * (2 : ℝ≥0∞)⁻¹ ^ kx := by
      rw [add_comm, complexityWeight_add_nat]
    -- The multiplicative coding chain.
    have key : (2 : ℝ≥0∞)⁻¹ ^ c₁ * complexityWeight (KPPair U x y)
        ≤ complexityWeight ((kx : ENat) + KP U y (prefixComplexityContext x kx)) := by
      rw [hcw]
      calc
        (2 : ℝ≥0∞)⁻¹ ^ c₁ * complexityWeight (KPPair U x y)
            ≤ (2 : ℝ≥0∞)⁻¹ ^ c₁ * aprioriMeasure U (pairCode x y) [] :=
          mul_le_mul_right heasy _
        _ = ((2 : ℝ≥0∞)⁻¹ ^ c₁ *
              (aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ kx)) * (2 : ℝ≥0∞)⁻¹ ^ kx := by
              rw [mul_assoc, mul_assoc, hcancel, mul_one]
        _ ≤ complexityWeight (KP U y (prefixComplexityContext x kx)) * (2 : ℝ≥0∞)⁻¹ ^ kx :=
          mul_le_mul_left (hc₁ x y kx hkx) _
    -- Read the multiplicative bound back as the additive lower bound.
    exact le_add_nat_of_complexityWeight_le hP key

/-- The lower, counting direction of prefix symmetry of information.

Mathematically this is
`K(x) + K(y | x, K(x)) <= K(x,y) + O(1)`.
This is the hard Levin-Gacs direction and is expected to need substantially more
counting and enumeration infrastructure. -/
theorem KPPair_chain_lower (U : Map) (hU : IsOptimalPrefixConditional U) :
    Exists fun c : Nat => forall x y : BitString, forall kx : Nat,
      HasPrefixComplexityValue U x kx ->
        KPPlain U x + KP U y (prefixComplexityContext x kx) <= KPPair U x y + (c : ENat) := by
  -- By `KPPair_chain_lower_of_conditional_coding`, the entire counting content of
  -- the Levin–Gács direction has been isolated into the single conditional coding
  -- bound `hcode` below, now correctly *guarded* at `k = K(x)` (the unguarded
  -- `∀ k` form is false; see the reduction lemma's docstring). What remains
  -- genuinely hard is exactly this bound: it is the conditional coding theorem
  -- (SUV §4.5, Kraft–Chaitin) applied to the section semimeasure
  -- `y ↦ m_U(⟨x,y⟩) · 2^{k}`, whose validity rests on
  --   * lower-semicomputability of `m_U`, and
  --   * the marginal coding bound `∑_y m_U(⟨x,y⟩) ≤ 2^{-K(x)}` at `k = K(x)`.
  -- Both are isolated, named Chapter-4 facts; the surrounding arithmetic is fully
  -- discharged by the reduction theorem above. The conditional coding bound at
  -- `k = K(x)` is assembled in `ConditionalCoding.section_coding_bound` from two
  -- precise, guarded obligations (`pairMarginal_coding_bound`,
  -- `conditional_coding_section_realization`); the guard `(k : ENat) = KP U x []`
  -- is definitionally `HasPrefixComplexityValue`, and `pairCode x (natCode k)` is
  -- definitionally `prefixComplexityContext x k`.
  apply KPPair_chain_lower_of_conditional_coding U hU
  exact section_coding_bound U hU

/-- Staged prefix symmetry of information.

This packages the faithful prefix-complexity shape
`K(x,y) = K(x) + K(y | x, K(x)) + O(1)` as the two additive inequalities above,
with possibly different constants. -/
theorem KPPair_symmetryOfInformation_staged (U : Map) (hU : IsOptimalPrefixConditional U) :
    Exists fun cUpper : Nat => Exists fun cLower : Nat =>
      forall x y : BitString, forall kx : Nat,
        HasPrefixComplexityValue U x kx ->
          KPPair U x y
              <= KPPlain U x + KP U y (prefixComplexityContext x kx) + (cUpper : ENat) /\
          KPPlain U x + KP U y (prefixComplexityContext x kx)
              <= KPPair U x y + (cLower : ENat) := by
  cases KPPair_chain_upper U hU with
  | intro cUpper hUpper =>
    cases KPPair_chain_lower U hU with
    | intro cLower hLower =>
      exact Exists.intro cUpper
        (Exists.intro cLower
          (fun x y kx hkx => And.intro (hUpper x y kx hkx) (hLower x y kx hkx)))

/-- Weak upper bound with only `x` as condition.

This is deliberately only an upper bound. The corresponding lower bound with
condition `x` alone is not the standard prefix symmetry theorem; the faithful
statement above conditions on both `x` and `K(x)`. -/
theorem KPPair_chain_upper_weak (U : Map) (hU : IsOptimalPrefixConditional U) :
    Exists fun c : Nat => forall x y : BitString,
      KPPair U x y <= KPPlain U x + KP U y x + (c : ENat) := by
  have hctx : Computable (fun p : BitString × ℕ => (fun (x : BitString) (_ : Nat) => x) p.1 p.2) :=
    Computable.fst
  have hM : IsPrefixDecompressor (twoStagePairBuilder U (fun x _ => x)) :=
    twoStagePairBuilder_isPrefixDecompressor hU.isDecompressor hU.isPrefixMachine hctx
  refine KPPair_chain_upper_weak_of_prefix_decompressor U
    (twoStagePairBuilder U (fun x _ => x)) hU hM 0 ?_
  intro x y
  by_cases hKx : KPPlain U x = ⊤
  · rw [hKx]; simp
  · obtain ⟨p, hp, hplen⟩ := exists_program_of_KP_ne_top (M := U) (x := x) (y := []) hKx
    by_cases hKy : KP U y x = ⊤
    · rw [hKy]; simp
    · obtain ⟨q, hq, hqlen⟩ := exists_program_of_KP_ne_top (M := U) (x := y) (y := x) hKy
      have hq' : produces U q ((fun (x : BitString) (_ : Nat) => x) x p.length) y := hq
      have hbound := KP_twoStagePairBuilder_le_of_produces
        (U := U) (ctx := fun x _ => x) hU.isPrefixMachine hp hq'
      calc
        KP (twoStagePairBuilder U (fun x _ => x)) (pairCode x y) []
            ≤ ((p.length + q.length : Nat) : ENat) := hbound
        _ = KPPlain U x + KP U y x := by rw [Nat.cast_add, hplen, hqlen]; rfl
        _ = KPPlain U x + KP U y x + (0 : ENat) := by rw [add_zero]

end Kolmogorov
