import KolmogorovMathlib.CommonInformation.ConditionalIndependenceChains
import KolmogorovMathlib.CommonInformation.TypeBounds
import Mathlib.Data.Nat.Size

/-!
# Exact histograms for conditional-independence chains

This file converts a rational-atom `ChainDist` into an exact natural-number
histogram whenever the sample size is divisible by a common denominator.  It
then transfers conditional independence to product identities and derives the
multinomial type-log defects needed by the fixed-frequency proof of SUV
Exercise 316.
-/

namespace Kolmogorov
open Finset

private lemma size_mul_le (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  apply Nat.size_le.mpr
  calc a * b < 2 ^ Nat.size a * 2 ^ Nat.size b :=
        Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self a)
          (Nat.le_of_lt (Nat.lt_size_self b)) (by positivity)
    _ = 2 ^ (Nat.size a + Nat.size b) := (pow_add 2 _ _).symm

private lemma size_add_size_le_size_mul_add_one {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Nat.size a + Nat.size b ≤ Nat.size (a * b) + 1 := by
  have h1 : 2 ^ (Nat.size a - 1) ≤ a := by
    by_contra h
    have h_lt : a < 2 ^ (Nat.size a - 1) := not_le.mp h
    have h_size : Nat.size a ≤ Nat.size a - 1 := Nat.size_le.mpr h_lt
    have h_pos : 0 < Nat.size a := Nat.size_pos.mpr ha
    omega
  have h2 : 2 ^ (Nat.size b - 1) ≤ b := by
    by_contra h
    have h_lt : b < 2 ^ (Nat.size b - 1) := not_le.mp h
    have h_size : Nat.size b ≤ Nat.size b - 1 := Nat.size_le.mpr h_lt
    have h_pos : 0 < Nat.size b := Nat.size_pos.mpr hb
    omega
  have h3 : 2 ^ (Nat.size a - 1 + (Nat.size b - 1)) ≤ a * b := by
    rw [pow_add]
    exact Nat.mul_le_mul h1 h2
  have h4 : Nat.size a - 1 + (Nat.size b - 1) < Nat.size (a * b) := by
    have h_lt : a * b < 2 ^ Nat.size (a * b) := Nat.lt_size_self (a * b)
    have := lt_of_le_of_lt h3 h_lt
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  omega

private lemma sum_bool {α : Type*} [AddCommMonoid α] (f : Bool → α) :
    ∑ b : Bool, f b = f true + f false := by
  have : (univ : Finset Bool) = {true, false} := rfl
  rw [this, sum_insert (by decide), sum_singleton]

private lemma prod_bool {α : Type*} [CommMonoid α] (f : Bool → α) :
    ∏ b : Bool, f b = f true * f false := by
  have : (univ : Finset Bool) = {true, false} := rfl
  rw [this, prod_insert (by decide), prod_singleton]

/-- `Q` is a positive common denominator for all atoms of the chain law. -/
def ChainDist.RationalAtoms {k : ℕ} (D : ChainDist k) (Q : ℕ) : Prop :=
  0 < Q ∧ ∀ v, ∃ n : ℕ, (Q : ℝ) * D.w v = (n : ℝ)

/-- Flipping the bottom `α` coordinate preserves the same atom denominator. -/
theorem ChainDist.RationalAtoms.invertChainDist {k Q : ℕ} {D : ChainDist k}
    (hQ : D.RationalAtoms Q) : (invertChainDist D).RationalAtoms Q := by
  refine ⟨hQ.1, fun v => ?_⟩
  obtain ⟨n, hn⟩ := hQ.2 (flip0 v)
  exact ⟨n, by simpa [invertChainDist] using hn⟩

/-- Each transition weight of the chain step kernel has denominator `4 * R`
whenever `c` has denominator `R`. -/
theorem chainStepKernel_rationalAtom {R p : ℕ} {c : ℝ} (hR : 0 < R)
    (hcRat : (R : ℝ) * c = (p : ℝ)) (hc1 : c ≤ 1) (a b g d : Bool) :
    ∃ m : ℕ, (4 * R : ℝ) * chainStepKernel c a b g d = (m : ℝ) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hpR : p ≤ R := by
    have : (p : ℝ) ≤ (R : ℝ) := by
      rw [← hcRat]
      nlinarith
    exact_mod_cast this
  have hsub : ((R - p : ℕ) : ℝ) = (R : ℝ) - (p : ℝ) := Nat.cast_sub hpR
  by_cases hgd : g = d
  · subst hgd
    by_cases hab : a = g ∧ b = g
    · exact ⟨4 * R, by push_cast; simp [chainStepKernel, hab]⟩
    · exact ⟨0, by simp [chainStepKernel, hab]⟩
  · by_cases hab : a = b
    · refine ⟨R - p, ?_⟩
      rw [hsub]
      simp only [chainStepKernel, hgd, hab, if_false, if_true]
      field_simp
      linarith [hcRat]
    · refine ⟨R + p, ?_⟩
      push_cast
      simp only [chainStepKernel, hgd, hab, if_false]
      field_simp
      linarith [hcRat]

/-- One chain extension multiplies the atom denominator by at most `4 * R`,
where `R` is a denominator for the correlation parameter `c`. -/
theorem ChainDist.RationalAtoms.extendChainDist
    {k Q R p : ℕ} {D : ChainDist k} {c : ℝ}
    (hD : D.RationalAtoms Q) (hR : 0 < R)
    (hcRat : (R : ℝ) * c = (p : ℝ))
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (extendChainDist D c hc0 hc1).RationalAtoms (4 * Q * R) := by
  have hQpos : 0 < Q := hD.1
  refine ⟨Nat.mul_pos (Nat.mul_pos (by norm_num) hQpos) hR, fun v => ?_⟩
  obtain ⟨n, hn⟩ := hD.2 (extensionEquiv k v).1
  obtain ⟨m, hm⟩ := chainStepKernel_rationalAtom (c := c) hR hcRat hc1
    (extensionEquiv k v).2.1 (extensionEquiv k v).2.2
    ((extensionEquiv k v).1 (chainAlphaIdx 0)) ((extensionEquiv k v).1 (chainBetaIdx 0))
  refine ⟨n * m, ?_⟩
  change ((4 * Q * R : ℕ) : ℝ) *
      (D.w (extensionEquiv k v).1 *
        chainStepKernel c (extensionEquiv k v).2.1 (extensionEquiv k v).2.2
          ((extensionEquiv k v).1 (chainAlphaIdx 0))
          ((extensionEquiv k v).1 (chainBetaIdx 0))) = ((n * m : ℕ) : ℝ)
  push_cast
  calc (4 : ℝ) * (Q : ℝ) * (R : ℝ) *
        (D.w (extensionEquiv k v).1 *
          chainStepKernel c (extensionEquiv k v).2.1 (extensionEquiv k v).2.2
            ((extensionEquiv k v).1 (chainAlphaIdx 0))
            ((extensionEquiv k v).1 (chainBetaIdx 0)))
      = ((Q : ℝ) * D.w (extensionEquiv k v).1) *
        ((4 * (R : ℝ)) *
          chainStepKernel c (extensionEquiv k v).2.1 (extensionEquiv k v).2.2
            ((extensionEquiv k v).1 (chainAlphaIdx 0))
            ((extensionEquiv k v).1 (chainBetaIdx 0))) := by ring
    _ = (n : ℝ) * (m : ℝ) := by rw [hn, hm]

/-- The exact `N`-sample histogram obtained by scaling rational atom counts. -/
noncomputable def chainHistogram {k : ℕ} (D : ChainDist k) {Q : ℕ}
    (hQ : D.RationalAtoms Q) (N : ℕ) :
    (Fin (2 * k + 2) → Bool) → ℕ :=
  fun v => (N / Q) * (Classical.choose (hQ.2 v) : ℕ)

/-- An exact chain histogram has total mass `N` when `Q ∣ N`. -/
theorem chainHistogram_total {k : ℕ} (D : ChainDist k) {Q : ℕ}
    (hQ : D.RationalAtoms Q) (N : ℕ) (hdiv : Q ∣ N) :
    ∑ v, chainHistogram D hQ N v = N := by
  have H : (Q : ℝ) * ∑ v, D.w v = ((∑ v, (Classical.choose (hQ.2 v) : ℕ)) : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    exact Classical.choose_spec (hQ.2 v)
  rw [D.total, mul_one] at H
  have H2 : Q = ∑ v, (Classical.choose (hQ.2 v) : ℕ) := by exact_mod_cast H
  unfold chainHistogram
  rw [← mul_sum]
  obtain ⟨m, hm⟩ := hdiv
  subst hm
  rw [Nat.mul_div_cancel_left _ hQ.1]
  rw [← H2]
  ring

/-- Binary size of the multinomial cardinality of a fixed-histogram class. -/
def histogramTypeLog {α} [Fintype α] [DecidableEq α] (f : α → ℕ) : ℕ :=
  Nat.size (Nat.multinomial Finset.univ f)

noncomputable def chainMarginal {k : ℕ} (D : ChainDist k) {Q : ℕ}
    (hQ : D.RationalAtoms Q) (N : ℕ)
    (S : (Fin (2 * k + 2) → Bool) → Bool) : ℕ :=
  ∑ v, if S v then chainHistogram D hQ N v else 0

noncomputable def chainHistogram3 {k : ℕ} (D : ChainDist k) {Q : ℕ}
    (hQ : D.RationalAtoms Q) (N : ℕ)
    (j1 j2 j3 : Fin (2 * k + 2)) (v1 v2 v3 : Bool) : ℕ :=
  chainMarginal D hQ N (fun w => (w j1 == v1) && (w j2 == v2) && (w j3 == v3))

noncomputable def chainHistogram2 {k : ℕ} (D : ChainDist k) {Q : ℕ}
    (hQ : D.RationalAtoms Q) (N : ℕ)
    (j1 j2 : Fin (2 * k + 2)) (v1 v2 : Bool) : ℕ :=
  chainMarginal D hQ N (fun w => (w j1 == v1) && (w j2 == v2))

noncomputable def chainHistogram1 {k : ℕ} (D : ChainDist k) {Q : ℕ}
    (hQ : D.RationalAtoms Q) (N : ℕ)
    (j1 : Fin (2 * k + 2)) (v1 : Bool) : ℕ :=
  chainMarginal D hQ N (fun w => w j1 == v1)

theorem chainMarginal_eq_pr {k : ℕ} (D : ChainDist k) {Q : ℕ}
    (hQ : D.RationalAtoms Q) (N : ℕ) (hdiv : Q ∣ N)
    (S : (Fin (2 * k + 2) → Bool) → Bool) :
    (chainMarginal D hQ N S : ℝ) = N * D.pr S := by
  unfold chainMarginal ChainDist.pr
  push_cast
  rw [mul_sum]
  have hNQ : ((N / Q : ℕ) : ℝ) * Q = N := by
    obtain ⟨m, hm⟩ := hdiv
    subst hm
    have eq : (Q * m) / Q = m := Nat.mul_div_cancel_left m hQ.1
    rw [eq]
    push_cast
    ring
  apply sum_congr rfl
  intro v _
  split_ifs with h
  · unfold chainHistogram
    have spec := Classical.choose_spec (hQ.2 v)
    calc (((N / Q) * (Classical.choose (hQ.2 v) : ℕ) : ℕ) : ℝ)
      _ = ((N / Q : ℕ) : ℝ) * (Classical.choose (hQ.2 v) : ℕ) := by push_cast; rfl
      _ = ((N / Q : ℕ) : ℝ) * (Q * D.w v) := by rw [← spec]
      _ = (((N / Q : ℕ) : ℝ) * Q) * D.w v := by ring
      _ = N * D.w v := by rw [hNQ]
  · simp

theorem chainMarginal_eq_nat_of_pr {k Q q m N : ℕ} (D : ChainDist k)
    (hQ : D.RationalAtoms Q) (S : (Fin (2 * k + 2) → Bool) → Bool)
    (hq : 0 < q) (hdiv : Q ∣ N) (hqN : q ∣ N)
    (hpr : (q : ℝ) * D.pr S = (m : ℝ)) :
    chainMarginal D hQ N S = (N / q) * m := by
  have H := chainMarginal_eq_pr D hQ N hdiv S
  have hq_real : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hpr' : D.pr S = (m : ℝ) / (q : ℝ) := by
    calc D.pr S = ((q : ℝ) * D.pr S) / (q : ℝ) := by rw [mul_div_cancel_left₀ _ hq_real]
      _ = (m : ℝ) / (q : ℝ) := by rw [hpr]
  rw [hpr'] at H
  have h_eq : (N : ℝ) * ((m : ℝ) / (q : ℝ)) = (((N / q) * m : ℕ) : ℝ) := by
    have hN_eq : (N : ℝ) = ((N / q : ℕ) : ℝ) * (q : ℝ) := by
      obtain ⟨c, hc⟩ := hqN
      subst hc
      rw [Nat.mul_div_cancel_left _ hq]
      push_cast
      ring
    rw [hN_eq]
    calc ((N / q : ℕ) : ℝ) * (q : ℝ) * ((m : ℝ) / (q : ℝ))
      _ = ((N / q : ℕ) : ℝ) * ((q : ℝ) * ((m : ℝ) / (q : ℝ))) := by rw [mul_assoc]
      _ = ((N / q : ℕ) : ℝ) * (((m : ℝ) / (q : ℝ)) * (q : ℝ)) := by rw [mul_comm (q : ℝ) _]
      _ = ((N / q : ℕ) : ℝ) * (m : ℝ) := by rw [div_mul_cancel₀ _ hq_real]
      _ = (((N / q) * m : ℕ) : ℝ) := by push_cast; rfl
  rw [h_eq] at H
  exact_mod_cast H

/-- Conditional independence transfers exactly to the scaled histogram. -/
theorem chainHistogram_condIndep_product_form {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (hdiv : Q ∣ N)
    (j1 j2 j3 : Fin (2 * k + 2)) (h_cond : D.CondIndepCoords j1 j2 j3) :
    ∀ v1 v2 v3 : Bool,
      chainHistogram1 D hQ N j3 v3 * chainHistogram3 D hQ N j1 j2 j3 v1 v2 v3 =
        chainHistogram2 D hQ N j1 j3 v1 v3 * chainHistogram2 D hQ N j2 j3 v2 v3 := by
  intro v1 v2 v3
  have h_pr := h_cond v1 v2 v3
  unfold ChainDist.prAt3 ChainDist.prAt2 ChainDist.prAt at h_pr
  have h_cast :
      ((chainHistogram1 D hQ N j3 v3 *
          chainHistogram3 D hQ N j1 j2 j3 v1 v2 v3 : ℕ) : ℝ) =
        ((chainHistogram2 D hQ N j1 j3 v1 v3 *
          chainHistogram2 D hQ N j2 j3 v2 v3 : ℕ) : ℝ) := by
    push_cast
    unfold chainHistogram1 chainHistogram2 chainHistogram3
    rw [chainMarginal_eq_pr D hQ N hdiv, chainMarginal_eq_pr D hQ N hdiv,
      chainMarginal_eq_pr D hQ N hdiv, chainMarginal_eq_pr D hQ N hdiv]
    calc (N : ℝ) * D.pr (fun w => w j3 == v3) *
          ((N : ℝ) * D.pr (fun w => (w j1 == v1) && (w j2 == v2) && (w j3 == v3)))
      _ = (N : ℝ)^2 *
          (D.pr (fun w => (w j1 == v1) && (w j2 == v2) && (w j3 == v3)) *
            D.pr (fun w => w j3 == v3)) := by ring
      _ = (N : ℝ)^2 *
          (D.pr (fun w => (w j1 == v1) && (w j3 == v3)) *
            D.pr (fun w => (w j2 == v2) && (w j3 == v3))) := by rw [h_pr]
      _ = (N : ℝ) * D.pr (fun w => (w j1 == v1) && (w j3 == v3)) *
            ((N : ℝ) * D.pr (fun w => (w j2 == v2) && (w j3 == v3))) := by ring
  exact_mod_cast h_cast

/-- Unconditional independence transfers exactly to the scaled histogram. -/
theorem chainHistogram_indep_product_form {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (hdiv : Q ∣ N)
    (j1 j2 : Fin (2 * k + 2)) (h_cond : D.IndepCoords j1 j2) :
    ∀ v1 v2 : Bool,
      N * chainHistogram2 D hQ N j1 j2 v1 v2 =
        chainHistogram1 D hQ N j1 v1 * chainHistogram1 D hQ N j2 v2 := by
  intro v1 v2
  have h_pr := h_cond v1 v2
  unfold ChainDist.prAt2 ChainDist.prAt at h_pr
  have h_cast : ((N * chainHistogram2 D hQ N j1 j2 v1 v2 : ℕ) : ℝ) =
    ((chainHistogram1 D hQ N j1 v1 * chainHistogram1 D hQ N j2 v2 : ℕ) : ℝ) := by
    push_cast
    unfold chainHistogram1 chainHistogram2
    rw [chainMarginal_eq_pr D hQ N hdiv, chainMarginal_eq_pr D hQ N hdiv,
      chainMarginal_eq_pr D hQ N hdiv]
    calc (N : ℝ) * ((N : ℝ) * D.pr (fun w => (w j1 == v1) && (w j2 == v2)))
      _ = (N : ℝ)^2 * D.pr (fun w => (w j1 == v1) && (w j2 == v2)) := by ring
      _ = (N : ℝ)^2 * (D.pr (fun w => w j1 == v1) * D.pr (fun w => w j2 == v2)) := by rw [h_pr]
      _ = (N : ℝ) * D.pr (fun w => w j1 == v1) * ((N : ℝ) * D.pr (fun w => w j2 == v2)) := by ring
  exact_mod_cast h_cast

theorem chainHistogram_marginal_3_2_A {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (A B W : Fin (2 * k + 2)) :
    ∀ a w : Bool, chainHistogram2 D hQ N A W a w =
      ∑ b : Bool, chainHistogram3 D hQ N A B W a b w := by
  intro a w
  unfold chainHistogram2 chainHistogram3 chainMarginal
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [sum_bool]
  cases h1 : (v A == a) <;> cases h2 : (v B) <;> cases h3 : (v W == w) <;> simp_all

theorem chainHistogram_marginal_3_2_B {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (A B W : Fin (2 * k + 2)) :
    ∀ b w : Bool, chainHistogram2 D hQ N B W b w =
      ∑ a : Bool, chainHistogram3 D hQ N A B W a b w := by
  intro b w
  unfold chainHistogram2 chainHistogram3 chainMarginal
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [sum_bool]
  cases h1 : (v B == b) <;> cases h2 : (v A) <;> cases h3 : (v W == w) <;> simp_all

theorem chainHistogram_marginal_2_1_W {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (A W : Fin (2 * k + 2)) :
    ∀ w : Bool, chainHistogram1 D hQ N W w = ∑ a : Bool, chainHistogram2 D hQ N A W a w := by
  intro w
  unfold chainHistogram1 chainHistogram2 chainMarginal
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [sum_bool]
  cases h1 : (v W == w) <;> cases h2 : (v A) <;> simp_all

theorem chainHistogram_marginal_3_1_W {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (A B W : Fin (2 * k + 2)) :
    ∀ w : Bool, chainHistogram1 D hQ N W w =
      ∑ ab : Bool × Bool, chainHistogram3 D hQ N A B W ab.1 ab.2 w := by
  intro w
  have H :
      ∑ ab : Bool × Bool, chainHistogram3 D hQ N A B W ab.1 ab.2 w =
        ∑ a : Bool, ∑ b : Bool, chainHistogram3 D hQ N A B W a b w := by
    rw [Fintype.sum_prod_type]
  rw [H]
  have H2 :
      ∑ a : Bool, ∑ b : Bool, chainHistogram3 D hQ N A B W a b w =
        ∑ a : Bool, chainHistogram2 D hQ N A W a w := by
    apply sum_congr rfl
    intro a _
    exact (chainHistogram_marginal_3_2_A D hQ N A B W a w).symm
  rw [H2]
  exact chainHistogram_marginal_2_1_W D hQ N A W w

theorem chainHistogram_marginal_1_2_left {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (j1 j2 : Fin (2 * k + 2)) :
    ∀ v1 : Bool, chainHistogram1 D hQ N j1 v1 =
      ∑ v2 : Bool, chainHistogram2 D hQ N j1 j2 v1 v2 := by
  intro v1
  unfold chainHistogram1 chainHistogram2 chainMarginal
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  rw [sum_bool]
  cases h1 : (w j1 == v1) <;> cases h2 : (w j2) <;> simp_all

theorem chainHistogram_marginal_1_2_right {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (j1 j2 : Fin (2 * k + 2)) :
    ∀ v2 : Bool, chainHistogram1 D hQ N j2 v2 =
      ∑ v1 : Bool, chainHistogram2 D hQ N j1 j2 v1 v2 := by
  intro v2
  unfold chainHistogram1 chainHistogram2 chainMarginal
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  rw [sum_bool]
  cases h1 : (w j2 == v2) <;> cases h2 : (w j1) <;> simp_all

theorem chainHistogram_condIndep_product_form_cond {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (hdiv : Q ∣ N)
    (A B W : Fin (2 * k + 2)) (h_cond : D.CondIndepCoords A B W) :
    ∀ w : Bool, ∀ a b : Bool,
      chainHistogram1 D hQ N W w * chainHistogram3 D hQ N A B W a b w =
        chainHistogram2 D hQ N A W a w * chainHistogram2 D hQ N B W b w := by
  intro w a b
  exact chainHistogram_condIndep_product_form D hQ N hdiv A B W h_cond a b w

private lemma multinomial_pos {α} (s : Finset α) (f : α → ℕ) :
    0 < Nat.multinomial s f := by
  have h_mul := Nat.multinomial_spec s f
  cases Nat.eq_zero_or_pos (Nat.multinomial s f) with
  | inl h =>
    rw [h, mul_zero] at h_mul
    have h_fac_pos : 0 < (∑ i ∈ s, f i).factorial := Nat.factorial_pos _
    linarith
  | inr h => exact h

private lemma multinomial_zero {α} [Fintype α]
    (f : α → ℕ) (h : ∀ a, f a = 0) :
    Nat.multinomial univ f = 1 := by
  have h1 : ∑ a : α, f a = 0 := sum_eq_zero (fun i _ => h i)
  have h2 : ∏ a : α, (f a).factorial = 1 := by
    apply prod_eq_one
    intro i _
    rw [h i, Nat.factorial_zero]
  have h3 := Nat.multinomial_spec univ f
  rw [h1, h2, Nat.factorial_zero, one_mul] at h3
  exact h3

private lemma size_pow_four (n : ℕ) : Nat.size (n ^ 4) ≤ 4 * Nat.size n := by
  have h2 : Nat.size (n ^ 2) ≤ 2 * Nat.size n := by
    have h_sq : n ^ 2 = n * n := by ring
    calc Nat.size (n ^ 2) = Nat.size (n * n) := by rw [h_sq]
      _ ≤ Nat.size n + Nat.size n := size_mul_le n n
      _ = 2 * Nat.size n := by ring
  have h_four : n ^ 4 = n ^ 2 * n ^ 2 := by ring
  calc Nat.size (n ^ 4) = Nat.size (n ^ 2 * n ^ 2) := by rw [h_four]
    _ ≤ Nat.size (n ^ 2) + Nat.size (n ^ 2) := size_mul_le _ _
    _ ≤ 2 * Nat.size n + 2 * Nat.size n := Nat.add_le_add h2 h2
    _ = 4 * Nat.size n := by ring

private lemma size_pow_eight (n : ℕ) : Nat.size (n ^ 8) ≤ 8 * Nat.size n := by
  have h4 := size_pow_four n
  have h_eight : n ^ 8 = n ^ 4 * n ^ 4 := by ring
  calc Nat.size (n ^ 8) = Nat.size (n ^ 4 * n ^ 4) := by rw [h_eight]
    _ ≤ Nat.size (n ^ 4) + Nat.size (n ^ 4) := size_mul_le _ _
    _ ≤ 4 * Nat.size n + 4 * Nat.size n := Nat.add_le_add h4 h4
    _ = 8 * Nat.size n := by ring

lemma sum_chainHistogram1 {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (hdiv : Q ∣ N)
    (W : Fin (2 * k + 2)) :
    ∑ w : Bool, chainHistogram1 D hQ N W w = N := by
  unfold chainHistogram1 chainMarginal
  rw [sum_comm]
  have H :
      ∑ v, ∑ w : Bool, (if v W == w then chainHistogram D hQ N v else 0) =
        ∑ v, chainHistogram D hQ N v := by
    apply sum_congr rfl
    intro v _
    rw [sum_bool]
    cases h : (v W) <;> simp_all
  rw [H]
  exact chainHistogram_total D hQ N hdiv

lemma chainHistogram1_le_N {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (hdiv : Q ∣ N)
    (W : Fin (2 * k + 2)) (w : Bool) : chainHistogram1 D hQ N W w ≤ N := by
  have H := sum_chainHistogram1 D hQ N hdiv W
  have h_le : chainHistogram1 D hQ N W w ≤ ∑ w : Bool, chainHistogram1 D hQ N W w := by
    apply single_le_sum (fun i _ => Nat.zero_le _) (mem_univ w)
  omega

lemma chainHistogram_marg_W {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (hdiv : Q ∣ N)
    (A B W : Fin (2 * k + 2)) (h_cond : D.CondIndepCoords A B W) (w : Bool) :
    (Nat.multinomial univ (fun a => chainHistogram2 D hQ N A W a w) *
      Nat.multinomial univ (fun b => chainHistogram2 D hQ N B W b w)) ≤
      (N + 1) ^ 4 * Nat.multinomial univ
        (fun ab : Bool × Bool => chainHistogram3 D hQ N A B W ab.1 ab.2 w) := by
  rcases Nat.eq_zero_or_pos (chainHistogram1 D hQ N W w) with hT_zero | hT_pos
  · have h_sumA : ∑ a, chainHistogram2 D hQ N A W a w = 0 := by
      rw [← chainHistogram_marginal_2_1_W D hQ N A W w, hT_zero]
    have h_sumB : ∑ b, chainHistogram2 D hQ N B W b w = 0 := by
      rw [← chainHistogram_marginal_2_1_W D hQ N B W w, hT_zero]
    have hA_zero : ∀ a, chainHistogram2 D hQ N A W a w = 0 := fun a => by
      have h_mem : a ∈ (univ : Finset Bool) := mem_univ a
      exact sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp h_sumA a h_mem
    have hB_zero : ∀ b, chainHistogram2 D hQ N B W b w = 0 := fun b => by
      have h_mem : b ∈ (univ : Finset Bool) := mem_univ b
      exact sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp h_sumB b h_mem
    rw [multinomial_zero _ hA_zero, multinomial_zero _ hB_zero]
    have H_pos := multinomial_pos univ
      (fun ab : Bool × Bool => chainHistogram3 D hQ N A B W ab.1 ab.2 w)
    have h_N1 : 1 ≤ (N + 1) ^ 4 := by
      have h1 : 1 ≤ N + 1 := by omega
      exact Nat.pow_le_pow_left h1 4
    have H_le :
        1 * 1 ≤ (N + 1) ^ 4 * Nat.multinomial univ
          (fun ab : Bool × Bool => chainHistogram3 D hQ N A B W ab.1 ab.2 w) := by
      apply Nat.mul_le_mul h_N1 H_pos
    exact H_le
  · have H_marg := multinomial_marginals_le_of_product_form
      (fun (a, b) => chainHistogram3 D hQ N A B W a b w)
      (fun a => chainHistogram2 D hQ N A W a w)
      (fun b => chainHistogram2 D hQ N B W b w)
      (chainHistogram1 D hQ N W w) hT_pos
      (fun a => chainHistogram_marginal_3_2_A D hQ N A B W a w)
      (fun b => chainHistogram_marginal_3_2_B D hQ N A B W b w)
      (fun a b => chainHistogram_condIndep_product_form_cond D hQ N hdiv A B W h_cond w a b)
    have H_le_N := chainHistogram1_le_N D hQ N hdiv W w
    have H_pow : (chainHistogram1 D hQ N W w + 1) ^ 4 ≤ (N + 1) ^ 4 := by
      have h_le : chainHistogram1 D hQ N W w + 1 ≤ N + 1 := by omega
      exact Nat.pow_le_pow_left h_le 4
    calc
      Nat.multinomial univ (fun a => chainHistogram2 D hQ N A W a w) *
          Nat.multinomial univ (fun b => chainHistogram2 D hQ N B W b w)
        ≤ (chainHistogram1 D hQ N W w + 1) ^
            (Fintype.card Bool * Fintype.card Bool) *
          Nat.multinomial univ
            (fun x : Bool × Bool => chainHistogram3 D hQ N A B W x.1 x.2 w) := H_marg
      _ = (chainHistogram1 D hQ N W w + 1) ^ 4 *
          Nat.multinomial univ
            (fun x : Bool × Bool => chainHistogram3 D hQ N A B W x.1 x.2 w) := by
        have H_card : Fintype.card Bool * Fintype.card Bool = 4 := rfl
        rw [H_card]
      _ ≤ (N + 1) ^ 4 * Nat.multinomial univ
          (fun x : Bool × Bool => chainHistogram3 D hQ N A B W x.1 x.2 w) :=
        Nat.mul_le_mul_right _ H_pow

/-- A conditionally independent link has only logarithmic multinomial type-log defect. -/
theorem chain_link_mutualInformation_defect {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (hdiv : Q ∣ N)
    (A B W : Fin (2 * k + 2)) (h_cond : D.CondIndepCoords A B W) :
    histogramTypeLog (fun (a, w) => chainHistogram2 D hQ N A W a w) +
    histogramTypeLog (fun (b, w) => chainHistogram2 D hQ N B W b w)
    ≤ histogramTypeLog (fun w => chainHistogram1 D hQ N W w) +
      histogramTypeLog (fun x : (Bool × Bool) × Bool =>
        match x with
        | (ab, w) => chainHistogram3 D hQ N A B W ab.1 ab.2 w) +
      8 * Nat.size (N + 1) + 1 := by
  unfold histogramTypeLog
  have hAW_pos := multinomial_pos univ (fun (a, w) => chainHistogram2 D hQ N A W a w)
  have hBW_pos := multinomial_pos univ (fun (b, w) => chainHistogram2 D hQ N B W b w)
  have H1 := size_add_size_le_size_mul_add_one hAW_pos hBW_pos
  rcases Nat.eq_zero_or_pos N with rfl | hN_pos
  · have h_zeroAW :
        ∀ aw : Bool × Bool, chainHistogram2 D hQ 0 A W aw.1 aw.2 = 0 := fun _ => by
      unfold chainHistogram2 chainMarginal chainHistogram
      simp
    have h_zeroBW :
        ∀ bw : Bool × Bool, chainHistogram2 D hQ 0 B W bw.1 bw.2 = 0 := fun _ => by
      unfold chainHistogram2 chainMarginal chainHistogram
      simp
    have h_zeroW : ∀ w, chainHistogram1 D hQ 0 W w = 0 := fun _ => by
      unfold chainHistogram1 chainMarginal chainHistogram
      simp
    have h_zeroABW : ∀ abw : (Bool × Bool) × Bool,
        chainHistogram3 D hQ 0 A B W abw.1.1 abw.1.2 abw.2 = 0 := fun _ => by
      unfold chainHistogram3 chainMarginal chainHistogram
      simp
    rw [multinomial_zero _ h_zeroAW, multinomial_zero _ h_zeroBW,
      multinomial_zero _ h_zeroW, multinomial_zero _ h_zeroABW]
    simp
  · have H2_AW := multinomial_fiber_factorization (fun (a, w) => chainHistogram2 D hQ N A W a w)
    have H2_BW := multinomial_fiber_factorization (fun (b, w) => chainHistogram2 D hQ N B W b w)
    have H2_ABW := multinomial_fiber_factorization
      (fun x : (Bool × Bool) × Bool =>
        match x with
        | (ab, w) => chainHistogram3 D hQ N A B W ab.1 ab.2 w)
    have h_sumA :
        (fun w => ∑ a, chainHistogram2 D hQ N A W a w) =
          (fun w => chainHistogram1 D hQ N W w) := by
      ext w
      exact (chainHistogram_marginal_2_1_W D hQ N A W w).symm
    have h_sumB :
        (fun w => ∑ b, chainHistogram2 D hQ N B W b w) =
          (fun w => chainHistogram1 D hQ N W w) := by
      ext w
      exact (chainHistogram_marginal_2_1_W D hQ N B W w).symm
    have h_sumAB :
        (fun w => ∑ ab : Bool × Bool,
          chainHistogram3 D hQ N A B W ab.1 ab.2 w) =
            (fun w => chainHistogram1 D hQ N W w) := by
      ext w
      exact (chainHistogram_marginal_3_1_W D hQ N A B W w).symm
    rw [h_sumA] at H2_AW
    rw [h_sumB] at H2_BW
    
    have h_sumAB2 :
        (fun w => ∑ a : Bool × Bool,
          match (a, w) with
          | (ab, w_1) => chainHistogram3 D hQ N A B W ab.1 ab.2 w_1) =
            (fun w => chainHistogram1 D hQ N W w) := by
      ext w
      have H_eq :
          (∑ a : Bool × Bool,
            match (a, w) with
            | (ab, w_1) => chainHistogram3 D hQ N A B W ab.1 ab.2 w_1) =
              ∑ ab : Bool × Bool,
                chainHistogram3 D hQ N A B W ab.1 ab.2 w := by
        apply sum_congr rfl
        intro a _
        rfl
      have H_val := congrFun h_sumAB w
      rw [H_eq]
      exact H_val
    rw [h_sumAB2] at H2_ABW
    have h_prod_AW :
        ∏ w ∈ univ, Nat.multinomial univ
          (fun a => chainHistogram2 D hQ N A W a w) =
            Nat.multinomial univ (fun a => chainHistogram2 D hQ N A W a true) *
              Nat.multinomial univ
                (fun a => chainHistogram2 D hQ N A W a false) := prod_bool _
    have h_prod_BW :
        ∏ w ∈ univ, Nat.multinomial univ
          (fun b => chainHistogram2 D hQ N B W b w) =
            Nat.multinomial univ (fun b => chainHistogram2 D hQ N B W b true) *
              Nat.multinomial univ
                (fun b => chainHistogram2 D hQ N B W b false) := prod_bool _
    have h_prod_ABW :
        ∏ w ∈ univ, Nat.multinomial univ (fun a : Bool × Bool =>
          match (a, w) with
          | (ab, w_1) => chainHistogram3 D hQ N A B W ab.1 ab.2 w_1) =
            Nat.multinomial univ (fun ab : Bool × Bool =>
              chainHistogram3 D hQ N A B W ab.1 ab.2 true) *
            Nat.multinomial univ (fun ab : Bool × Bool =>
              chainHistogram3 D hQ N A B W ab.1 ab.2 false) := by
      have H_eq :
          ∏ w ∈ univ, Nat.multinomial univ (fun a : Bool × Bool =>
            match (a, w) with
            | (ab, w_1) => chainHistogram3 D hQ N A B W ab.1 ab.2 w_1) =
              ∏ w ∈ univ, Nat.multinomial univ (fun ab : Bool × Bool =>
                chainHistogram3 D hQ N A B W ab.1 ab.2 w) := by
        apply prod_congr rfl
        intro w _
        rfl
      rw [H_eq]
      exact prod_bool _
    rw [h_prod_AW] at H2_AW
    rw [h_prod_BW] at H2_BW
    rw [h_prod_ABW] at H2_ABW
    
    let mA (w : Bool) := Nat.multinomial univ
      (fun a => chainHistogram2 D hQ N A W a w)
    let mB (w : Bool) := Nat.multinomial univ
      (fun b => chainHistogram2 D hQ N B W b w)
    let mAB (w : Bool) := Nat.multinomial univ
      (fun ab : Bool × Bool => chainHistogram3 D hQ N A B W ab.1 ab.2 w)
    let mW := Nat.multinomial univ (fun w => chainHistogram1 D hQ N W w)
    let mAW := Nat.multinomial univ
      (fun (a, w) => chainHistogram2 D hQ N A W a w)
    let mBW := Nat.multinomial univ
      (fun (b, w) => chainHistogram2 D hQ N B W b w)
    let mABW := Nat.multinomial univ (fun x : (Bool × Bool) × Bool =>
      match x with
      | (ab, w) => chainHistogram3 D hQ N A B W ab.1 ab.2 w)
    have hAW_factor : mAW = mW * (mA true * mA false) := by
      simpa [mAW, mW, mA] using H2_AW
    have hBW_factor : mBW = mW * (mB true * mB false) := by
      simpa [mBW, mW, mB] using H2_BW
    have hABW_factor : mABW = mW * (mAB true * mAB false) := by
      simpa [mABW, mW, mAB] using H2_ABW
    have h_marg_T : mA true * mB true ≤ (N + 1) ^ 4 * mAB true := by
      simpa [mA, mB, mAB] using
        chainHistogram_marg_W D hQ N hdiv A B W h_cond true
    have h_marg_F : mA false * mB false ≤ (N + 1) ^ 4 * mAB false := by
      simpa [mA, mB, mAB] using
        chainHistogram_marg_W D hQ N hdiv A B W h_cond false
    have H_mul_T_F :
        (mA true * mA false) * (mB true * mB false) ≤
          ((N + 1) ^ 4 * mAB true) * ((N + 1) ^ 4 * mAB false) := by
      calc
        (mA true * mA false) * (mB true * mB false) =
            (mA true * mB true) * (mA false * mB false) := by ring
        _ ≤ _ := Nat.mul_le_mul h_marg_T h_marg_F
    have H_bound : mAW * mBW ≤ (N + 1) ^ 8 * (mW * mABW) := by
      calc
        mAW * mBW =
            (mW * (mA true * mA false)) * (mW * (mB true * mB false)) := by
          rw [hAW_factor, hBW_factor]
        _ = mW * (mW * ((mA true * mA false) * (mB true * mB false))) := by
          ring
        _ ≤ mW * (mW *
            (((N + 1) ^ 4 * mAB true) * ((N + 1) ^ 4 * mAB false))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ H_mul_T_F)
        _ = (N + 1) ^ 8 * (mW * (mW * (mAB true * mAB false))) := by
          ring
        _ = (N + 1) ^ 8 * (mW * mABW) := by rw [hABW_factor]
    have H_size := Nat.size_le_size H_bound
    have H_size2 := size_mul_le ((N + 1) ^ 8) (mW * mABW)
    have H_size3 := size_mul_le mW mABW
    have H_size4 := size_pow_eight (N + 1)
    change Nat.size mAW + Nat.size mBW ≤ Nat.size (mAW * mBW) + 1 at H1
    change Nat.size mAW + Nat.size mBW ≤
      Nat.size mW + Nat.size mABW + 8 * Nat.size (N + 1) + 1
    omega

/-- An independent top pair has only logarithmic multinomial type-log defect. -/
theorem chain_top_mutualInformation_defect {k : ℕ} (D : ChainDist k)
    {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (hdiv : Q ∣ N)
    (A B : Fin (2 * k + 2)) (h_cond : D.IndepCoords A B) :
    histogramTypeLog (fun a => chainHistogram1 D hQ N A a) +
    histogramTypeLog (fun b => chainHistogram1 D hQ N B b)
    ≤ histogramTypeLog (fun (a, b) => chainHistogram2 D hQ N A B a b) +
      4 * Nat.size (N + 1) + 1 := by
  unfold histogramTypeLog
  have hA_pos := multinomial_pos univ (fun a => chainHistogram1 D hQ N A a)
  have hB_pos := multinomial_pos univ (fun b => chainHistogram1 D hQ N B b)
  have H1 := size_add_size_le_size_mul_add_one hA_pos hB_pos
  rcases Nat.eq_zero_or_pos N with rfl | hN_pos
  · have h_zeroA : ∀ a, chainHistogram1 D hQ 0 A a = 0 := fun _ => by
      unfold chainHistogram1 chainMarginal chainHistogram
      simp
    have h_zeroB : ∀ b, chainHistogram1 D hQ 0 B b = 0 := fun _ => by
      unfold chainHistogram1 chainMarginal chainHistogram
      simp
    have h_zeroAB :
        ∀ ab : Bool × Bool, chainHistogram2 D hQ 0 A B ab.1 ab.2 = 0 := fun _ => by
      unfold chainHistogram2 chainMarginal chainHistogram
      simp
    rw [multinomial_zero _ h_zeroA, multinomial_zero _ h_zeroB, multinomial_zero _ h_zeroAB]
    simp
  · have H2 : Nat.multinomial univ (fun a => chainHistogram1 D hQ N A a) *
              Nat.multinomial univ (fun b => chainHistogram1 D hQ N B b) ≤
                (N + 1) ^ (Fintype.card Bool * Fintype.card Bool) *
                Nat.multinomial univ (fun (a, b) => chainHistogram2 D hQ N A B a b) := by
      apply multinomial_marginals_le_of_product_form
      · exact hN_pos
      · intro a; exact chainHistogram_marginal_1_2_left D hQ N A B a
      · intro b; exact chainHistogram_marginal_1_2_right D hQ N A B b
      · intro a b; exact chainHistogram_indep_product_form D hQ N hdiv A B h_cond a b
    have H3 := Nat.size_le_size H2
    have H4 := size_mul_le
      ((N + 1) ^ (Fintype.card Bool * Fintype.card Bool))
      (Nat.multinomial univ (fun (a, b) => chainHistogram2 D hQ N A B a b))
    have H5 : Fintype.card Bool * Fintype.card Bool = 4 := rfl
    rw [H5] at H3 H4
    have H6 := size_pow_four (N + 1)
    omega

end Kolmogorov
