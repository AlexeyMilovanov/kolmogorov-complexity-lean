/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.Restricted.FamilyCurve.SampledRun
import KolmogorovMathlib.Restricted.FamilyCurve.Selector
import KolmogorovMathlib.Encoding.Tuples

/-!
# Restricted family-curve foundations

This file defines the target curve, its restricted-profile approximation, and the balanced
finite grids used by the sampled construction.
-/

namespace Kolmogorov
open scoped ENNReal

/-- Target up-set for the restricted curve theorem: below budget `k`, the
boundary is prescribed by the decreasing sequence `t`. -/
def FamilyCurveTarget (k : ℕ) (t : ℕ → ℕ) (i j : ℕ) : Prop :=
  i ≤ k → t i ≤ j

/-- A concrete two-sided `L∞`-style approximation of the target curve by the
restricted profile.  The upper clause puts shifted target boundary points in
`P_x^𝒜`; the lower clause says the restricted profile does not cross more than
`Δ` below the target while the target height is above `Δ`. -/
def RestrictedProfileWithinCurve (𝒜 : DescriptionFamily) (U : Map)
    (x : BitString) (k : ℕ) (t : ℕ → ℕ) (Δ : ℕ) : Prop :=
  (∀ i : ℕ, i ≤ k →
    InDescriptionProfileIn 𝒜 U x (i + Δ) (t i + Δ)) ∧
  (∀ i : ℕ, i ≤ k →
    ¬ InDescriptionProfileIn 𝒜 U x i (t i - (Δ + 1)) ∨ t i ≤ Δ)

/-- A discretization of the boundary curve into `N` steps along the `j` axis. -/
structure RestrictedCurveGrid (n k N : ℕ) (t : ℕ → ℕ) where
  i : ℕ → ℕ
  j : ℕ → ℕ
  steps_pos : 0 < N
  i_start : i 0 = 0
  i_end : i N = k
  i_mono : ∀ s < N, i s ≤ i (s + 1)
  j_start : j 0 = n
  j_end : j N = 0
  j_mono : ∀ s < N, j (s + 1) ≤ j s
  j_step_le : ∀ s < N, j s - j (s + 1) ≤ n / N + 1
  i_le_k : ∀ s ≤ N, i s ≤ k
  j_le_n : ∀ s ≤ N, j s ≤ n
  cross_below : ∀ s ≤ N, t (i s) ≤ j s
  cross_above : ∀ s ≤ N, 0 < i s → j s < t (i s - 1)

/-- For any height `h`, there is a least index `i` where the curve crosses `h`. -/
lemma curve_crossing_index_spec {k : ℕ} {t : ℕ → ℕ} (htk : t k = 0)
    (_hstrict : ∀ idx < k, t (idx + 1) < t idx) (h : ℕ) :
    ∃ i ≤ k, t i ≤ h ∧ ∀ i' < i, h < t i' := by
  let P : ℕ → Prop := fun i => i ≤ k ∧ t i ≤ h
  have hex : ∃ i, P i := ⟨k, le_rfl, by simp [htk]⟩
  let i := Nat.find hex
  have hi : P i := Nat.find_spec hex
  refine ⟨i, hi.1, hi.2, ?_⟩
  intro i' hi'i
  have hi'k : i' ≤ k := (Nat.le_of_lt hi'i).trans hi.1
  have hnot : ¬ P i' := Nat.find_min hex hi'i
  exact Nat.lt_of_not_ge (fun hle => hnot ⟨hi'k, hle⟩)

/--
Lemma M7.1: The target boundary curve `t` can be discretized into `N` steps
such that the vertical distance between consecutive steps is small.
-/
lemma exists_restricted_curve_grid (n k N : ℕ) (t : ℕ → ℕ)
    (hN : 0 < N) (h_start : t 0 ≤ n) (h_end : t k = 0)
    (h_strict : ∀ idx < k, t (idx + 1) < t idx) :
    Nonempty (RestrictedCurveGrid n k N t) := by
  classical
  let q := n / N
  let r := n % N
  let j : ℕ → ℕ := fun s => n - (s * q + min s r)
  let i : ℕ → ℕ := fun s =>
    Classical.choose (curve_crossing_index_spec h_end h_strict (j s))
  have hrN : r < N := by
    dsimp [r]
    exact Nat.mod_lt n hN
  have hdecomp : N * q + r = n := by
    simpa [q, r] using Nat.div_add_mod n N
  have hi_spec (s : ℕ) :
      i s ≤ k ∧ t (i s) ≤ j s ∧ ∀ i' < i s, j s < t i' := by
    dsimp [i]
    exact Classical.choose_spec
      (curve_crossing_index_spec h_end h_strict (j s))
  have hj0 : j 0 = n := by simp [j]
  have hjN : j N = 0 := by
    dsimp [j]
    rw [Nat.min_eq_right (Nat.le_of_lt hrN)]
    omega
  have hj_mono (s : ℕ) (_hs : s < N) : j (s + 1) ≤ j s := by
    have hmul : s * q ≤ (s + 1) * q :=
      Nat.mul_le_mul_right q (Nat.le_succ s)
    have hmin : min s r ≤ min (s + 1) r :=
      min_le_min (Nat.le_succ s) le_rfl
    dsimp [j]
    omega
  have hj_step (s : ℕ) (hs : s < N) :
      j s - j (s + 1) ≤ q + 1 := by
    have hsN : s ≤ N := Nat.le_of_lt hs
    have hsuccN : s + 1 ≤ N := hs
    have hmul_s : s * q ≤ N * q := Nat.mul_le_mul_right q hsN
    have hmul_succ : (s + 1) * q ≤ N * q :=
      Nat.mul_le_mul_right q hsuccN
    have hmul_mono : s * q ≤ (s + 1) * q :=
      Nat.mul_le_mul_right q (Nat.le_succ s)
    have hmin_s : min s r ≤ r := min_le_right _ _
    have hmin_succ : min (s + 1) r ≤ r := min_le_right _ _
    have hmin_mono : min s r ≤ min (s + 1) r :=
      min_le_min (Nat.le_succ s) le_rfl
    have hmin_step : min (s + 1) r ≤ min s r + 1 := by
      by_cases hsr : s < r
      · rw [Nat.min_eq_left (Nat.le_of_lt hsr)]
        exact min_le_left _ _
      · have hrs : r ≤ s := Nat.le_of_not_gt hsr
        rw [Nat.min_eq_right hrs,
          Nat.min_eq_right (hrs.trans (Nat.le_succ s))]
        omega
    have hmul_step : (s + 1) * q = s * q + q := by ring
    let A := s * q + min s r
    let B := (s + 1) * q + min (s + 1) r
    have hAn : A ≤ n := by
      dsimp [A]
      exact (Nat.add_le_add hmul_s hmin_s).trans_eq hdecomp
    have hBn : B ≤ n := by
      dsimp [B]
      exact (Nat.add_le_add hmul_succ hmin_succ).trans_eq hdecomp
    have hAB : A ≤ B := by
      dsimp [A, B]
      exact Nat.add_le_add hmul_mono hmin_mono
    have hBA : B ≤ A + (q + 1) := by
      calc
        B = s * q + q + min (s + 1) r := by dsimp [B]; omega
        _ ≤ s * q + q + (min s r + 1) := Nat.add_le_add_left hmin_step _
        _ = A + (q + 1) := by dsimp [A]; omega
    change (n - A) - (n - B) ≤ q + 1
    omega
  have hi0 : i 0 = 0 := by
    by_contra hne
    have hpos : 0 < i 0 := Nat.pos_of_ne_zero hne
    have habove := (hi_spec 0).2.2 0 hpos
    rw [hj0] at habove
    omega
  have hiN : i N = k := by
    have hispec := hi_spec N
    have htzero : t (i N) = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hjN] using hispec.2.1
    by_contra hne
    have hlt : i N < k := Nat.lt_of_le_of_ne hispec.1 hne
    have hdrop := h_strict (i N) hlt
    rw [htzero] at hdrop
    omega
  refine ⟨{
    i := i
    j := j
    steps_pos := hN
    i_start := hi0
    i_end := hiN
    i_mono := ?_
    j_start := hj0
    j_end := hjN
    j_mono := hj_mono
    j_step_le := ?_
    i_le_k := ?_
    j_le_n := ?_
    cross_below := ?_
    cross_above := ?_ }⟩
  · intro s hs
    by_contra hnot
    have hlt : i (s + 1) < i s := Nat.lt_of_not_ge hnot
    have habove := (hi_spec s).2.2 (i (s + 1)) hlt
    have hbelow := (hi_spec (s + 1)).2.1
    have hj := hj_mono s hs
    omega
  · intro s hs
    simpa [q] using hj_step s hs
  · intro s _hs
    exact (hi_spec s).1
  · intro s _hs
    exact Nat.sub_le n _
  · intro s _hs
    exact (hi_spec s).2.1
  · intro s _hs hpos
    exact (hi_spec s).2.2 (i s - 1) (by omega)

/-- The restricted curve grid covers all target indices `i ≤ k`. -/
lemma restrictedCurveGrid_covers (n k N : ℕ) (t : ℕ → ℕ)
    (grid : RestrictedCurveGrid n k N t) (idx : ℕ) (hidx : idx ≤ k) :
    ∃ s < N, grid.i s ≤ idx ∧ idx ≤ grid.i (s + 1) := by
  let P : ℕ → Prop := fun r => r ≤ N ∧ idx ≤ grid.i r
  have hex : ∃ r, P r := ⟨N, le_rfl, by simpa [P, grid.i_end] using hidx⟩
  let r := Nat.find hex
  have hr : P r := Nat.find_spec hex
  by_cases hr0 : r = 0
  · refine ⟨0, grid.steps_pos, ?_, ?_⟩
    · simp [grid.i_start]
    · have hr2 : idx ≤ grid.i 0 := by simpa [hr0] using hr.2
      exact hr2.trans (grid.i_mono 0 grid.steps_pos)
  · obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hr0
    have hsN : s < N := by omega
    have hnot : ¬ P s := by
      apply Nat.find_min hex
      simpa [r] using (show s < r by omega)
    have his : grid.i s < idx := by
      apply Nat.lt_of_not_ge
      intro hidxs
      exact hnot ⟨Nat.le_of_lt hsN, hidxs⟩
    have hr2 : idx ≤ grid.i (s + 1) := by simpa [hs] using hr.2
    exact ⟨s, hsN, Nat.le_of_lt his, hr2⟩

/-
A strictly decreasing natural-valued restricted curve loses at least one
unit at every step.  This arithmetic fact is used both by grid interpolation
and by the geometric counting part of the scale-template construction.
-/
lemma restricted_curve_drop_bound {k : ℕ} {t : ℕ → ℕ}
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i)
    {i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    t j + (j - i) ≤ t i := by
  induction hij <;> simp_all +arith +decide
  grind

/-
Binary logarithmic length is bounded by the explicit binary-list length,
with one extra unit covering zero.
-/
private lemma log2_succ_le_bits_length_add_one (a : ℕ) :
    Nat.log2 a + 1 ≤ (Nat.bits a).length + 1 := by
  rcases a with (_ | _ | a) <;> simp +arith +decide only [add_le_add_iff_right]
  convert Nat.le_of_lt_succ _ using 1
  rw [Nat.log2_lt] <;> norm_num [Nat.size_eq_bits_len]
  exact Nat.lt_of_lt_of_le (Nat.lt_size_self _)
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))

/-
Elementary square-root balancing estimate used by the grid budget.
-/
private lemma grid_sqrt_balance (c n : ℕ) (hn : 0 < n) :
    (Nat.sqrt (n / (Nat.log2 n + 1)) + 1) *
        (c * (Nat.bits n).length + c + 1) ≤
      sqrtSlack (4 * (c + 1)) n := by
  have h_bits_length : n.bits.length = Nat.log2 n + 1 := by
    rw [Nat.size_eq_bits_len, Nat.le_antisymm_iff]
    constructor
    · rw [Nat.size_le]
      exact Nat.lt_log2_self
    · rw [Nat.add_one_le_iff, Nat.log2_lt]
      · exact Nat.lt_size_self n
      · positivity
  set q := Nat.sqrt (n / (Nat.log2 n + 1))
  set r := Nat.sqrt (n * (Nat.log2 n + 1))
  have h_qb_le_r : q * (Nat.log2 n + 1) ≤ r := by
    refine Nat.le_sqrt.mpr ?_
    nlinarith [Nat.sqrt_le (n / (n.log2 + 1)),
      Nat.div_mul_le_self n (n.log2 + 1), pow_two (n.log2 + 1)]
  have h_b_le_r : Nat.log2 n + 1 ≤ r := by
    refine Nat.le_sqrt.mpr ?_
    rw [mul_comm]
    gcongr
    rw [Nat.succ_le_iff]
    rw [Nat.log2_lt] <;> try linarith
    exact Nat.lt_two_pow_self
  unfold sqrtSlack
  rw [h_bits_length]
  nlinarith [Nat.zero_le (q * c), Nat.zero_le (q * 1), Nat.zero_le (c * 1)]

/-- The vertical mesh of the balanced grid is bounded by one fixed
`sqrtSlack` budget.  This numeric fact is independent of the description
family and of the target curve. -/
lemma restrictedCurveGrid_mesh_le_sqrtSlack (n : ℕ) :
    n / (Nat.sqrt (n / (Nat.log2 n + 1)) + 1) + 1 ≤ sqrtSlack 8 n := by
  by_cases hn : n = 0
  · subst n
    norm_num [sqrtSlack, Nat.bits]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have h_bits_length : n.bits.length = Nat.log2 n + 1 := by
    rw [Nat.size_eq_bits_len, Nat.le_antisymm_iff]
    constructor
    · rw [Nat.size_le]
      exact Nat.lt_log2_self
    · rw [Nat.add_one_le_iff, Nat.log2_lt]
      · exact Nat.lt_size_self n
      · positivity
  set b := Nat.log2 n + 1
  set q := Nat.sqrt (n / b)
  have hb_pos : 0 < b := by simp [b]
  have hq : n / b ≤ q * q + q + q := by
    simpa [q] using Nat.sqrt_le_add (n / b)
  have hquot_mul : (n / b) * b ≤ (q * q + q + q) * b :=
    Nat.mul_le_mul_right b hq
  have hdiv := Nat.div_add_mod n b
  have hmod : n % b ≤ b := Nat.le_of_lt (Nat.mod_lt n hb_pos)
  have hn_bound : n ≤ (q + 1) * (q + 1) * b := by
    nlinarith
  have hquot : n / (q + 1) ≤ (q + 1) * b := by
    apply Nat.div_le_of_le_mul
    calc
      n ≤ (q + 1) * (q + 1) * b := hn_bound
      _ = (q + 1) * ((q + 1) * b) := by ring
  have hbalance := grid_sqrt_balance 1 n hn_pos
  calc
    n / (Nat.sqrt (n / (Nat.log2 n + 1)) + 1) + 1
        = n / (q + 1) + 1 := by simp [q, b]
    _ ≤ (q + 1) * b + 1 := Nat.add_le_add_right hquot 1
    _ ≤ (q + 1) * (b + 2) := by nlinarith
    _ ≤ sqrtSlack 8 n := by
      simpa [q, b, h_bits_length] using hbalance

/-
The total cost of the grid scales is bounded by a `sqrtSlack` budget whose
constant depends only on the fixed polynomial overhead bound.
-/
lemma restrictedCurveGrid_scale_budget (C d : ℕ) (hC : 0 < C) :
    ∃ c_budget : ℕ, ∀ (n : ℕ) (overhead : ℕ → ℕ) (N : ℕ),
      (∀ m, overhead m ≤ C * (m + 1) ^ d) →
      N ≤ Nat.sqrt (n / (Nat.log2 n + 1)) + 1 →
      N * (Nat.log2 (overhead n) + 1) ≤ sqrtSlack c_budget n := by
        obtain ⟨c,
                 hc⟩ : ∃ c : ℕ, ∀ n : ℕ, Nat.log2 (C * (n + 1) ^ d) + 1 ≤ (c : ℕ) * (Nat.bits
                                                                                      n).length +
                                                                                          (c : ℕ) +
                                                                                              1 :=
                                                                                                  by
          -- Apply the lemma `polynomialOverhead_bits_le_logSlack` to obtain the constant $c$.
          obtain ⟨c, hc⟩ := polynomialOverhead_bits_le_logSlack C d hC;
          use c;
          intro n;
          exact Nat.le_trans (log2_succ_le_bits_length_add_one _)
            (Nat.add_le_add_right (hc n) 1)
        use 4 * ( c + 1 );
        intro n overhead N h_overhead hN
        have h_log2 : Nat.log2 (overhead n) + 1 ≤ c * (Nat.bits n).length + c + 1 := by
          refine le_trans ?_ ( hc n );
          by_cases h : overhead n = 0 <;>
            simp_all +decide only [Nat.log2, Nat.succ_eq_add_one, add_le_add_iff_right,
              Nat.rec_zero, zero_add, le_add_iff_nonneg_left, zero_le]
          have h_log2_mono : ∀ {a b : ℕ}, 0 < a → a ≤ b → Nat.log2 a ≤ Nat.log2 b := by
            intros a b ha hb; exact (by
            rw [ Nat.le_log2 ] <;> try linarith;
            refine le_trans ?_ hb;
            rw [ ← Nat.le_log2 ] ; linarith);
          exact h_log2_mono ( Nat.pos_of_ne_zero h ) ( h_overhead n );
        by_cases hn : n = 0;
        · simp_all +decide [ sqrtSlack ];
          nlinarith;
        · exact le_trans ( Nat.mul_le_mul hN h_log2 )
            ( grid_sqrt_balance c n ( Nat.pos_of_ne_zero hn ) )

/-- The code of the sampled grid is the list code of its crossing pairs. -/
def restrictedCurveGridCode {n k N : ℕ} {t : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N t) : BitString :=
  listCode ((List.range (N + 1)).map
    (fun s => pairCode (Nat.bits (grid.i s)) (Nat.bits (grid.j s))))

/--
The grid approximates the original curve: for every index `idx ≤ k`, there
is a sampled grid step that bounds it within one vertical mesh unit `n / N + 1`.
-/
lemma restrictedCurveGrid_interpolates {n k N : ℕ} {t : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N t) (idx : ℕ) (hidx : idx ≤ k) :
    ∃ s < N, grid.i s ≤ idx ∧ idx ≤ grid.i (s + 1) ∧
      grid.j s - grid.j (s + 1) ≤ n / N + 1 := by
  obtain ⟨s, hs, his, his'⟩ :=
    restrictedCurveGrid_covers n k N t grid idx hidx
  exact ⟨s, hs, his, his', grid.j_step_le s hs⟩

/-- Actual sampled-height interpolation.  Some sampled crossing immediately
above `t idx` has horizontal coordinate at most `idx`, its successor has
horizontal coordinate at least `idx`, and its height exceeds `t idx` by at
most one vertical mesh step. -/
lemma restrictedCurveGrid_height_le_target_add_mesh
    {n k N : ℕ} {t : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N t)
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i)
    (idx : ℕ) (hidx : idx ≤ k) :
    ∃ s < N, grid.i s ≤ idx ∧ idx ≤ grid.i (s + 1) ∧
      grid.j s ≤ t idx + (n / N + 1) := by
  let P : ℕ → Prop := fun r => r ≤ N ∧ grid.j r ≤ t idx
  have hex : ∃ r, P r := ⟨N, le_rfl, by simp [grid.j_end]⟩
  let r := Nat.find hex
  have hr : P r := Nat.find_spec hex
  by_cases hr0 : r = 0
  · have htidx_le_t0 : t idx ≤ t 0 := by
      have hdrop := restricted_curve_drop_bound hstrict (Nat.zero_le idx) hidx
      omega
    have ht0_le_j0 : t 0 ≤ grid.j 0 := by
      simpa [grid.i_start] using grid.cross_below 0 (Nat.zero_le N)
    have hj0_le : grid.j 0 ≤ t idx := by simpa [hr0] using hr.2
    have hidx0 : idx = 0 := by
      have hdrop := restricted_curve_drop_bound hstrict (Nat.zero_le idx) hidx
      omega
    refine ⟨0, grid.steps_pos, by simp [grid.i_start], ?_, ?_⟩
    · simp [hidx0]
    · exact hj0_le.trans (Nat.le_add_right _ _)
  · obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hr0
    have hsN : s < N := by omega
    have hr_eq : r = s + 1 := hs
    have hnot : ¬ P s := Nat.find_min hex (by omega)
    have hj_gt : t idx < grid.j s := by
      have hs_le : s ≤ N := Nat.le_of_lt hsN
      exact Nat.lt_of_not_ge (fun h => hnot ⟨hs_le, h⟩)
    have hjnext_le : grid.j (s + 1) ≤ t idx := by
      simpa [hr_eq] using hr.2
    have his : grid.i s ≤ idx := by
      by_contra hnot_le
      have hidx_lt : idx < grid.i s := Nat.lt_of_not_ge hnot_le
      have hi_pos : 0 < grid.i s := lt_of_le_of_lt (Nat.zero_le idx) hidx_lt
      have habove := grid.cross_above s (Nat.le_of_lt hsN) hi_pos
      have hi_pred_le_k : grid.i s - 1 ≤ k :=
        (Nat.sub_le _ _).trans (grid.i_le_k s (Nat.le_of_lt hsN))
      have hdrop := restricted_curve_drop_bound hstrict
        (show idx ≤ grid.i s - 1 by omega) hi_pred_le_k
      omega
    have hisnext : idx ≤ grid.i (s + 1) := by
      by_contra hnot_le
      have hi_lt : grid.i (s + 1) < idx := Nat.lt_of_not_ge hnot_le
      have hnext_le_N : s + 1 ≤ N := hsN
      have hbelow := grid.cross_below (s + 1) hnext_le_N
      have hdrop := restricted_curve_drop_bound hstrict
        (Nat.le_of_lt hi_lt) hidx
      omega
    refine ⟨s, hsN, his, hisnext, ?_⟩
    have hjmono := grid.j_mono s hsN
    have hjstep := grid.j_step_le s hsN
    omega

/-- A list code has the expected linear length bound when every component has
length at most `b`. -/
private lemma length_listCode_le_of_forall_le (l : List BitString) (b : ℕ)
    (h : ∀ x ∈ l, x.length ≤ b) :
    (listCode l).length ≤ l.length * (2 * b + 1) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [length_listCode_cons]
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, y.length ≤ b := by
        intro y hy
        exact h y (by simp [hy])
      have hi := ih hxs
      simp only [List.length_cons]
      calc
        2 * x.length + 1 + (listCode xs).length
            ≤ (2 * b + 1) + xs.length * (2 * b + 1) :=
              Nat.add_le_add (by omega) hi
        _ = (xs.length + 1) * (2 * b + 1) := by ring

/-- The length of every sampled-grid code is bounded by one uniform
`O(N log n)` constant.  The constant precedes the grid parameters; `k ≤ n`
is necessary to bound both coordinates by the visible parameter `n`. -/
lemma restrictedCurveGrid_code_length_le_sqrt {n k N : ℕ} {t : ℕ → ℕ}
    (hk : k ≤ n) (grid : RestrictedCurveGrid n k N t) :
    (restrictedCurveGridCode grid).length ≤
      12 * N * ((Nat.bits n).length + 1) := by
  let L : List BitString := (List.range (N + 1)).map
    (fun s => pairCode (Nat.bits (grid.i s)) (Nat.bits (grid.j s)))
  have hcomponent : ∀ w ∈ L, w.length ≤ 3 * (Nat.bits n).length + 1 := by
    intro w hw
    rw [List.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    have hsN : s ≤ N := by
      rw [List.mem_range] at hs
      omega
    have hi : grid.i s ≤ n := (grid.i_le_k s hsN).trans hk
    have hj : grid.j s ≤ n := grid.j_le_n s hsN
    have hbi := length_natBits_mono hi
    have hbj := length_natBits_mono hj
    simp only [length_pairCode]
    omega
  have hraw : (restrictedCurveGridCode grid).length ≤
      (N + 1) * (2 * (3 * (Nat.bits n).length + 1) + 1) := by
    change (listCode L).length ≤ _
    simpa [L] using
      (length_listCode_le_of_forall_le L (3 * (Nat.bits n).length + 1) hcomponent)
  have hN : 1 ≤ N := grid.steps_pos
  calc
    (restrictedCurveGridCode grid).length
        ≤ (N + 1) * (2 * (3 * (Nat.bits n).length + 1) + 1) := hraw
    _ ≤ 12 * N * ((Nat.bits n).length + 1) := by
      nlinarith [Nat.zero_le (N * (Nat.bits n).length)]

/-- The plain complexity of the grid code satisfies the `sqrtSlack` budget. -/
lemma KPPlain_restrictedCurveGridCode_le (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ {n k N : ℕ} {t : ℕ → ℕ},
      k ≤ n → ∀ grid : RestrictedCurveGrid n k N t,
      N ≤ Nat.sqrt (n / (Nat.log2 n + 1)) + 1 →
      KPPlain U (restrictedCurveGridCode grid) ≤
        (sqrtSlack c n : ENat) := by
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  refine ⟨156 + c_len, ?_⟩
  intro n k N t hk grid hN
  let code := restrictedCurveGridCode grid
  have hcode_len : code.length ≤
      12 * N * ((Nat.bits n).length + 1) :=
    restrictedCurveGrid_code_length_le_sqrt hk grid
  have hcode_sqrt : code.length ≤ sqrtSlack 52 n := by
    by_cases hn : n = 0
    · subst n
      have hNle : N ≤ 1 := by simpa using hN
      have hlen : code.length ≤ 12 := by
        have := hcode_len
        simp [Nat.bits] at this
        nlinarith
      exact hlen.trans (by norm_num [sqrtSlack, Nat.bits])
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hbalance := grid_sqrt_balance 12 n hn_pos
      calc
        code.length ≤ 12 * N * ((Nat.bits n).length + 1) := hcode_len
        _ = N * (12 * (Nat.bits n).length + 12) := by ring
        _ ≤ (Nat.sqrt (n / (Nat.log2 n + 1)) + 1) *
              (12 * (Nat.bits n).length + 12) := by
            exact Nat.mul_le_mul_right _ hN
        _ ≤ (Nat.sqrt (n / (Nat.log2 n + 1)) + 1) *
              (12 * (Nat.bits n).length + 12 + 1) := by
            exact Nat.mul_le_mul_left _ (by omega)
        _ ≤ sqrtSlack 52 n := by
            simpa using hbalance
  have hbits_code : (Nat.bits code.length).length ≤ code.length :=
    length_natBits_le_self code.length
  have hkp := hc_len code
  have hnat : code.length + 2 * (Nat.bits code.length).length + c_len ≤
      sqrtSlack (156 + c_len) n := by
    unfold sqrtSlack at hcode_sqrt ⊢
    nlinarith
  calc
    KPPlain U code
        ≤ code.length + 2 * (Nat.bits code.length).length + (c_len : ENat) := hkp
    _ ≤ (sqrtSlack (156 + c_len) n : ENat) := by exact_mod_cast hnat

/-- A packaged existence lemma for the encoded restricted curve grid. -/
lemma exists_encoded_restricted_curve_grid (U : Map) (hU : IsOptimalPrefixConditional U)
    : ∃ c_grid : ℕ, ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n → t 0 ≤ n → t k = 0 →
      (∀ idx < k, t (idx + 1) < t idx) →
      ∃ N : ℕ, ∃ grid : RestrictedCurveGrid n k N t,
        N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1 ∧
        KPPlain U (restrictedCurveGridCode grid) ≤
          (sqrtSlack c_grid n : ENat) := by
  obtain ⟨c_grid, hcode⟩ := KPPlain_restrictedCurveGridCode_le U hU
  refine ⟨c_grid, ?_⟩
  intro n k t hk h_start h_end h_strict
  let N := Nat.sqrt (n / (Nat.log2 n + 1)) + 1
  have hN : 0 < N := by simp [N]
  obtain ⟨grid⟩ :=
    exists_restricted_curve_grid n k N t hN h_start h_end h_strict
  exact ⟨N, grid, rfl, hcode hk grid (by simp [N])⟩

/-- Select the member of the family cover that contains a specified
length-`n` point.  This is the pointwise descent step used by the restricted
multi-scale construction.
-/
lemma exists_family_cover_member (𝒜 : DescriptionFamily) {A : Finset BitString}
    (hA : 𝒜.mem A) {x : BitString} (hxA : x ∈ A) (n j d : ℕ)
    (hxn : x.length = n) (hcard : A.card ≤ 2 ^ j) (hd : d ≤ j) :
    ∃ B : Finset BitString,
      𝒜.mem B ∧ x ∈ B ∧ B.card ≤ 2 ^ (j - d) := by
  obtain ⟨𝒞, hsmall, hcover, _⟩ :=
    exists_family_cover 𝒜 hA n j d hcard hd
  obtain ⟨B, hB𝒞, hxB⟩ := hcover x hxA hxn
  obtain ⟨hBmem, hBcard⟩ := hsmall B hB𝒞
  exact ⟨B, hBmem, hxB, hBcard⟩

/-- State of the VV scale construction for the restricted profile.
This packages the target string `x`, its ambient length `ambientLength`, and the
nested sequence of "good sets" from the description family `𝒜` that witness the
upper bounds of the profile curve.  The ambient length is allowed the same
`O(log n)` padding as the paper-facing theorem. -/
structure RestrictedScaleState (𝒜 : DescriptionFamily) (U : Map) (n k c : ℕ) (t : ℕ → ℕ) where
  x : BitString
  ambientLength : ℕ
  x_len : x.length = ambientLength
  n_le_ambient : n ≤ ambientLength
  ambient_le : ambientLength ≤ n + logSlack c n
  goodSets : ℕ → Finset BitString
  mem_family : ∀ s (_hs : s ≤ k), 𝒜.mem (goodSets s)
  x_mem : ∀ s (_hs : s ≤ k), x ∈ goodSets s
  size_bound : ∀ s (_hs : s ≤ k), (goodSets s).card ≤ 2 ^ (t s + sqrtSlack c n)
  complexity_bound : ∀ s (hs : s ≤ k), setComplexity U (goodSets s) ⟨x,
                                                                      x_mem s hs⟩ ≤ (s + sqrtSlack
                                                                                      c n : ENat)

/-- Intermediate data for the VV restricted curve construction.  It separates
the hard counting construction (the template below) from the final selection
and packaging into `RestrictedScaleState`.

`badSet` is the finite set of candidate strings that already have a forbidden
restricted profile point.  The template carries the actual common survivor
maintained by the coupled process, together with its nonmembership in `badSet`. -/
structure RestrictedScaleTemplate (𝒜 : DescriptionFamily) (U : Map)
    (n k c : ℕ) (t : ℕ → ℕ) where
  ambientLength : ℕ
  n_le_ambient : n ≤ ambientLength
  ambient_le : ambientLength ≤ n + logSlack c n
  goodSets : ℕ → Finset BitString
  mem_family : ∀ s (_hs : s ≤ k), 𝒜.mem (goodSets s)
  size_bound : ∀ s (_hs : s ≤ k), (goodSets s).card ≤ 2 ^ (t s + sqrtSlack c n)
  complexity_bound : ∀ s (_hs : s ≤ k) (hS : (goodSets s).Nonempty),
    setComplexity U (goodSets s) hS ≤ (s + sqrtSlack c n : ENat)
  candidates : Finset BitString
  candidates_nonempty : candidates.Nonempty
  candidate_len : ∀ x ∈ candidates, x.length = ambientLength
  candidate_mem : ∀ x ∈ candidates, ∀ s (_hs : s ≤ k), x ∈ goodSets s
  candidate_complexity : ∀ x ∈ candidates,
    KPPlain U x ≤ (k + sqrtSlack c n : ENat)
  badSet : Finset BitString
  badSet_subset_candidates : badSet ⊆ candidates
  badSet_exact : ∀ x ∈ candidates,
    x ∈ badSet ↔ ∃ i : ℕ, i ≤ k ∧ t i > sqrtSlack c n ∧
      InDescriptionProfileIn 𝒜 U x i (t i - (sqrtSlack c n + 1))
  survivor : BitString
  survivor_mem : survivor ∈ candidates
  survivor_not_bad : survivor ∉ badSet

/-- Every point of a strictly decreasing restricted curve lies below its
left endpoint after accounting for the horizontal displacement. -/
lemma restricted_curve_index_add_le_start {k : ℕ} {t : ℕ → ℕ}
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i)
    {i : ℕ} (hik : i ≤ k) :
    i + t i ≤ t 0 := by
  simpa [Nat.add_comm] using
    (restricted_curve_drop_bound hstrict (Nat.zero_le i) hik)

/-- If a restricted curve reaches zero at `k`, its height at an earlier index
is at least the number of remaining strict drops.  This is the sufficiency-line
inequality needed when the restricted curve is viewed as an ordinary profile
curve. -/
lemma restricted_curve_remaining_le {k : ℕ} {t : ℕ → ℕ}
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i)
    (htk : t k = 0) {i : ℕ} (hik : i ≤ k) :
    k - i ≤ t i := by
  simpa [htk] using
    (restricted_curve_drop_bound hstrict hik (le_refl k))

/--
The pointwise descent step: cover a previous family member at the next target
size, and pick the cover member that maximizes its intersection with the
currently surviving candidates `C`.
-/
lemma exists_cover_member_large_intersection (𝒜 : DescriptionFamily)
    {A : Finset BitString} (hA : 𝒜.mem A)
    (C : Finset BitString) (hC : C ⊆ A)
    (n c : ℕ) (hC_n : ∀ x ∈ C, x.length = n)
    (hc_pos : 0 < c) (hc_le : c ≤ A.card) :
    ∃ B : Finset BitString,
      𝒜.mem B ∧
      B.card ≤ c ∧
      c * C.card ≤ (𝒜.overhead n * A.card) * (B ∩ C).card := by
  classical
  by_cases hC_empty : C = ∅
  · refine ⟨{[]}, 𝒜.singleton_mem [], hc_pos, ?_⟩
    simp [hC_empty]
  · have hC_nonempty : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hC_empty
    obtain ⟨cover, hsmall, hcover, hcover_card⟩ :=
      𝒜.cover hA n c hc_pos hc_le
    let coverSet : Finset (Finset BitString) := cover.toFinset
    have hcoverSet_nonempty : coverSet.Nonempty := by
      obtain ⟨x, hxC⟩ := hC_nonempty
      obtain ⟨B, hBcover, _hxB⟩ := hcover x (hC hxC) (hC_n x hxC)
      exact ⟨B, List.mem_toFinset.mpr hBcover⟩
    obtain ⟨B, hBset, hBmax⟩ := Finset.exists_max_image coverSet
      (fun B => (B ∩ C).card) hcoverSet_nonempty
    have hBcover : B ∈ cover := List.mem_toFinset.mp hBset
    obtain ⟨hBmem, hBcard⟩ := hsmall B hBcover
    refine ⟨B, hBmem, hBcard, ?_⟩
    have hCsub : C ⊆ coverSet.biUnion (fun B => B ∩ C) := by
      intro x hxC
      obtain ⟨B', hB'cover, hxB'⟩ := hcover x (hC hxC) (hC_n x hxC)
      rw [Finset.mem_biUnion]
      exact ⟨B', List.mem_toFinset.mpr hB'cover, Finset.mem_inter.mpr ⟨hxB', hxC⟩⟩
    have hCcard : C.card ≤ cover.length * (B ∩ C).card := by
      calc
        C.card ≤ (coverSet.biUnion (fun B' => B' ∩ C)).card :=
          Finset.card_le_card hCsub
        _ ≤ ∑ B' ∈ coverSet, (B' ∩ C).card := Finset.card_biUnion_le
        _ ≤ coverSet.card * (B ∩ C).card :=
          Finset.sum_le_card_nsmul coverSet (fun B' => (B' ∩ C).card)
            (B ∩ C).card hBmax
        _ ≤ cover.length * (B ∩ C).card :=
          Nat.mul_le_mul_right _ (List.toFinset_card_le cover)
    calc
      c * C.card ≤ c * (cover.length * (B ∩ C).card) :=
        Nat.mul_le_mul_left c hCcard
      _ = (cover.length * c) * (B ∩ C).card := by ring
      _ ≤ (𝒜.overhead n * A.card) * (B ∩ C).card :=
        Nat.mul_le_mul_right _ hcover_card

/-- Rebuilding one step: given a surviving candidate set `C ⊆ A`, we can find a new
member `B` of size `≤ c` such that its intersection with `C` has density bounded
relative to the overhead and the previous size bound. -/
lemma restricted_rebuild_step_density (𝒜 : DescriptionFamily)
    {A : Finset BitString} (hA : 𝒜.mem A)
    (C : Finset BitString) (hC : C ⊆ A)
    (n c A_bound : ℕ) (hC_n : ∀ x ∈ C, x.length = n)
    (hc_pos : 0 < c) (hc_bound : c ≤ A_bound)
    (hA_bound : A.card ≤ A_bound) :
    ∃ B : Finset BitString,
      𝒜.mem B ∧
      B.card ≤ c ∧
      c * C.card ≤ (𝒜.overhead n * A_bound) * (B ∩ C).card := by
  classical
  by_cases hcA : c ≤ A.card
  · obtain ⟨B, hBmem, hBcard, hdensity⟩ :=
      exists_cover_member_large_intersection 𝒜 hA C hC n c hC_n hc_pos hcA
    refine ⟨B, hBmem, hBcard, hdensity.trans ?_⟩
    exact Nat.mul_le_mul_right (B ∩ C).card
      (Nat.mul_le_mul_left (𝒜.overhead n) hA_bound)
  · have hAcard : A.card ≤ c := Nat.le_of_lt (Nat.lt_of_not_ge hcA)
    have hinter : A ∩ C = C := Finset.inter_eq_right.mpr hC
    refine ⟨A, hA, hAcard, ?_⟩
    rw [hinter]
    have hc_overhead : c ≤ 𝒜.overhead n * A_bound := by
      calc
        c ≤ A_bound := hc_bound
        _ = 1 * A_bound := by simp
        _ ≤ 𝒜.overhead n * A_bound :=
          Nat.mul_le_mul_right A_bound (𝒜.overhead_pos n)
    exact Nat.mul_le_mul_right C.card hc_overhead

/-- The end-to-end density bound for a rebuilt suffix, resolving the step recurrence. -/
lemma restricted_rebuild_suffix_density
    (s k : ℕ) (t : ℕ → ℕ) (overhead_bound : ℕ)
    (C_seq : ℕ → Finset BitString)
    (hs_le_k : s ≤ k)
    (hstep : ∀ i, s ≤ i → i < k →
        (2 ^ t (i + 1)) * (C_seq i).card ≤ (overhead_bound * 2 ^ t i) * (C_seq (i + 1)).card) :
    (2 ^ t k) * (C_seq s).card ≤ (overhead_bound ^ (k - s) * 2 ^ t s) * (C_seq k).card := by
  have aux : ∀ i, s ≤ i → i ≤ k →
      (2 ^ t i) * (C_seq s).card ≤
        (overhead_bound ^ (i - s) * 2 ^ t s) * (C_seq i).card := by
    intro i hsi
    induction hsi with
    | refl =>
        intro _hsk
        simp
    | @step i hsi ih =>
        intro hi_succ_k
        have hi_k : i < k := by omega
        have hprev := ih (Nat.le_of_lt hi_k)
        have hnext := hstep i hsi hi_k
        have hsub : i + 1 - s = (i - s) + 1 := by
          simpa [Nat.succ_eq_add_one] using Nat.succ_sub hsi
        have hmul :
            (2 ^ t i) * ((2 ^ t (i + 1)) * (C_seq s).card) ≤
              (2 ^ t i) *
                ((overhead_bound ^ (i + 1 - s) * 2 ^ t s) *
                  (C_seq (i + 1)).card) := by
          calc
            (2 ^ t i) * ((2 ^ t (i + 1)) * (C_seq s).card)
                = (2 ^ t (i + 1)) * ((2 ^ t i) * (C_seq s).card) := by ring
            _ ≤ (2 ^ t (i + 1)) *
                ((overhead_bound ^ (i - s) * 2 ^ t s) * (C_seq i).card) :=
              Nat.mul_le_mul_left _ hprev
            _ = (overhead_bound ^ (i - s) * 2 ^ t s) *
                ((2 ^ t (i + 1)) * (C_seq i).card) := by ring
            _ ≤ (overhead_bound ^ (i - s) * 2 ^ t s) *
                ((overhead_bound * 2 ^ t i) * (C_seq (i + 1)).card) :=
              Nat.mul_le_mul_left _ hnext
            _ = (2 ^ t i) *
                ((overhead_bound ^ (i + 1 - s) * 2 ^ t s) *
                  (C_seq (i + 1)).card) := by
              rw [hsub, pow_succ]
              ring
        exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  exact aux k hs_le_k le_rfl

lemma restricted_rebuild_suffix_pointwise_core (𝒜 : DescriptionFamily)
    (n s k : ℕ) (t : ℕ → ℕ) (overhead_bound : ℕ)
    (hover : 𝒜.overhead n ≤ overhead_bound)
    (A_s : Finset BitString) (hA_s : 𝒜.mem A_s)
    (C : Finset BitString) (D : Finset BitString) (hC : C ⊆ A_s)
    (hC_n : ∀ x ∈ C, x.length = n)
    (hA_s_card : A_s.card ≤ 2 ^ t s)
    (ht_strict : ∀ i, s ≤ i → i < k → t (i + 1) < t i) :
    ∃ (B : ℕ → Finset BitString) (C_seq : ℕ → Finset BitString),
      B s = A_s ∧
      C_seq s = C \ D ∧
      (∀ i, s < i → i ≤ k → 𝒜.mem (B i)) ∧
      (∀ i, s < i → i ≤ k → (B i).card ≤ 2 ^ t i) ∧
      (∀ i, s ≤ i → i < k → C_seq (i + 1) = C_seq i ∩ B (i + 1)) ∧
      (∀ i, s ≤ i → i < k →
        (2 ^ t (i + 1)) * (C_seq i).card ≤ (overhead_bound * 2 ^ t i) * (C_seq (i + 1)).card) := by
  classical
  let nextOK : ℕ → Finset BitString → Finset BitString → Finset BitString → Prop :=
    fun i _A C' B' =>
      𝒜.mem B' ∧
      B'.card ≤ 2 ^ t (i + 1) ∧
      (2 ^ t (i + 1)) * C'.card ≤
        (overhead_bound * 2 ^ t i) * (C' ∩ B').card
  let nextB : ℕ → Finset BitString → Finset BitString → Finset BitString :=
    fun i A' C' =>
      if hc_le : (2 ^ t (i + 1)) ≤ A'.card ∧ 0 < (2 ^ t (i + 1)) ∧ 𝒜.mem A' ∧ C' ⊆ A' ∧
          (∀ x ∈ C', x.length = n) then
        let hA_nonempty : A'.Nonempty := Finset.card_pos.mp (by omega)
        let Acode := (codedUniformOn A' hA_nonempty).code
        let Ccode : BitString := if hC_ne : C'.Nonempty then (codedUniformOn C' hC_ne).code else []
        have h_spec :=
            restrictedMaxIntersectionCoverSelector_spec 𝒜 Acode Ccode n (2 ^ t (i + 1))
                (𝒜.overhead n) A' C' (decodeCoverCodeList_code A' hA_nonempty)
                    (by
                      dsimp only [Ccode]
                      split_ifs with h
                      · exact decodeCoverCodeList_code C' h
                      · have heq : C' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
                        subst heq
                        unfold canonicalFinsetList; rw [Finset.sort_empty]
                        rfl) (by rfl) hc_le.2.2.1 hc_le.2.2.2.1 hc_le.2.2.2.2 hc_le.2.1 hc_le.1
        have h_dom :
            (restrictedMaxIntersectionCoverSelector 𝒜
              (restrictedCoverSelectorInput Acode Ccode
                (2 ^ t (i + 1)) (𝒜.overhead n))).Dom := by
          obtain ⟨ Bcode, B, h_eq, _ ⟩ := h_spec
          rw [h_eq]
          trivial
        let Bcode :=
            (restrictedMaxIntersectionCoverSelector 𝒜
              (restrictedCoverSelectorInput Acode Ccode
                (2 ^ t (i + 1)) (𝒜.overhead n))).get h_dom
        (decodeCoverCodeList Bcode).toFinset
      else
        if hex2 : ∃ B', nextOK i A' C' B' then Classical.choose hex2 else A_s
  have nextB_spec (i : ℕ) (A' C' : Finset BitString)
      (hA_card : A'.card ≤ 2 ^ t i)
      (hex : ∃ B', nextOK i A' C' B') : nextOK i A' C' (nextB i A' C') := by
    dsimp only [nextB]
    by_cases hc_le :
        ((2 ^ t (i + 1)) ≤ A'.card ∧ 0 < (2 ^ t (i + 1)) ∧ 𝒜.mem A' ∧ C' ⊆ A' ∧ (∀ x ∈ C',
                                                                                  List.length x =
                                                                                      n))
    · simp only [dif_pos hc_le]
      let hA_nonempty : A'.Nonempty := Finset.card_pos.mp (by omega)
      let Acode := (codedUniformOn A' hA_nonempty).code
      let Ccode : BitString := if hC_ne : C'.Nonempty then (codedUniformOn C' hC_ne).code else []
      have h_spec :=
          restrictedMaxIntersectionCoverSelector_spec 𝒜 Acode Ccode n (2 ^ t (i + 1))
              (𝒜.overhead n) A' C' (decodeCoverCodeList_code A' hA_nonempty)
                  (by
                    dsimp only [Ccode]
                    split_ifs with h
                    · exact decodeCoverCodeList_code C' h
                    · have heq : C' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
                      subst heq
                      unfold canonicalFinsetList; rw [Finset.sort_empty]
                      rfl) (by rfl) hc_le.2.2.1 hc_le.2.2.2.1 hc_le.2.2.2.2 hc_le.2.1 hc_le.1
      have h_dom :
          (restrictedMaxIntersectionCoverSelector 𝒜
            (restrictedCoverSelectorInput Acode Ccode
              (2 ^ t (i + 1)) (𝒜.overhead n))).Dom := by
        obtain ⟨ Bcode, B, h_eq, _ ⟩ := h_spec
        rw [h_eq]
        trivial
      generalize hget :
          (restrictedMaxIntersectionCoverSelector 𝒜
            (restrictedCoverSelectorInput Acode Ccode
              (2 ^ t (i + 1)) (𝒜.overhead n))).get h_dom =
            Bcode_ex
      obtain ⟨ Bcode, B, h_eq, hB_eq, hB_mem, hB_card, hB_dens ⟩ := h_spec
      have hget_eq : Bcode_ex = Bcode := by
        rw [← hget, Part.get_eq_iff_eq_some, h_eq]
      rw [hget_eq]
      have hB_toFinset : (decodeCoverCodeList Bcode).toFinset = B := by
        rw [hB_eq, canonicalFinsetList_toFinset]
      rw [hB_toFinset]
      refine ⟨ hB_mem, hB_card, ?_ ⟩
      calc (2 ^ t (i + 1)) * C'.card
        _ ≤ 𝒜.overhead n * A'.card * (B ∩ C').card := hB_dens
        _ ≤ overhead_bound * 2 ^ t i * (C' ∩ B).card := by
          rw [Finset.inter_comm]
          exact Nat.mul_le_mul (Nat.mul_le_mul hover hA_card) (le_refl _)
    · rw [dif_neg hc_le]
      rw [dif_pos hex]
      exact Classical.choose_spec hex
  have next_exists (i : ℕ) (A' C' : Finset BitString)
      (hsi : s ≤ i) (hik : i < k)
      (hA'mem : 𝒜.mem A') (hA'card : A'.card ≤ 2 ^ t i)
      (hC'sub : C' ⊆ A') (hC'len : ∀ x ∈ C', x.length = n) :
      ∃ B', nextOK i A' C' B' := by
    have hpow : 2 ^ t (i + 1) ≤ 2 ^ t i :=
      Nat.pow_le_pow_right (by decide) (Nat.le_of_lt (ht_strict i hsi hik))
    obtain ⟨B', hB'mem, hB'card, hdensity⟩ :=
      restricted_rebuild_step_density 𝒜 hA'mem C' hC'sub n
        (2 ^ t (i + 1)) (2 ^ t i) hC'len (by positivity) hpow hA'card
    refine ⟨B', ?_⟩
    refine ⟨hB'mem, hB'card, ?_⟩
    calc
      (2 ^ t (i + 1)) * C'.card
          ≤ (𝒜.overhead n * 2 ^ t i) * (B' ∩ C').card := hdensity
      _ ≤ (overhead_bound * 2 ^ t i) * (B' ∩ C').card := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right (2 ^ t i) hover)
      _ = (overhead_bound * 2 ^ t i) * (C' ∩ B').card := by
        rw [Finset.inter_comm]
  let step : ℕ → (Finset BitString × Finset BitString) →
      (Finset BitString × Finset BitString) :=
    fun m state =>
      let B' := nextB (s + m) state.1 state.2
      (B', state.2 ∩ B')
  let states : ℕ → (Finset BitString × Finset BitString) :=
    fun m => Nat.rec (A_s, C \ D) (fun m state => step m state) m
  have states_zero : states 0 = (A_s, C \ D) := by rfl
  have states_succ (m : ℕ) : states (m + 1) = step m (states m) := by rfl
  have states_invariant : ∀ m : ℕ, s + m ≤ k →
      𝒜.mem (states m).1 ∧
      (states m).1.card ≤ 2 ^ t (s + m) ∧
      (states m).2 ⊆ (states m).1 ∧
      (∀ x ∈ (states m).2, x.length = n) := by
    intro m
    induction m with
    | zero =>
        intro _hsk
        rw [states_zero]
        refine ⟨hA_s, hA_s_card, ?_, ?_⟩
        · exact Finset.sdiff_subset.trans hC
        · intro x hx
          exact hC_n x (Finset.sdiff_subset hx)
    | succ m ih =>
        intro hm_succ_k
        have hm_k : s + m < k := by omega
        obtain ⟨hmem, hcard, hsub, hlen⟩ := ih (Nat.le_of_lt hm_k)
        have hex := next_exists (s + m) (states m).1 (states m).2
          (by omega) hm_k hmem hcard hsub hlen
        have hnext := nextB_spec (s + m) (states m).1 (states m).2 hcard hex
        rw [states_succ]
        simp only [step]
        refine ⟨hnext.1, ?_, Finset.inter_subset_right, ?_⟩
        · simpa [Nat.add_assoc] using hnext.2.1
        · intro x hx
          exact hlen x (Finset.inter_subset_left hx)
  let B : ℕ → Finset BitString := fun i =>
    if hsi : s ≤ i then (states (i - s)).1 else A_s
  let C_seq : ℕ → Finset BitString := fun i =>
    if hsi : s ≤ i then (states (i - s)).2 else C \ D
  have hB_s : B s = A_s := by
    simp [B, states_zero]
  have hC_s : C_seq s = C \ D := by
    simp [C_seq, states_zero]
  have hmem_B : ∀ i, s < i → i ≤ k → 𝒜.mem (B i) := by
    intro i hsi hik
    have hle : s ≤ i := Nat.le_of_lt hsi
    have hi_eq : s + (i - s) = i := Nat.add_sub_of_le hle
    have hinv := states_invariant (i - s) (by simpa [hi_eq] using hik)
    simpa [B, hle] using hinv.1
  have hcard_B : ∀ i, s < i → i ≤ k → (B i).card ≤ 2 ^ t i := by
    intro i hsi hik
    have hle : s ≤ i := Nat.le_of_lt hsi
    have hi_eq : s + (i - s) = i := Nat.add_sub_of_le hle
    have hinv := states_invariant (i - s) (by simpa [hi_eq] using hik)
    simpa [B, hle, hi_eq] using hinv.2.1
  have hC_step : ∀ i, s ≤ i → i < k →
      C_seq (i + 1) = C_seq i ∩ B (i + 1) := by
    intro i hsi _hik
    have hsi_succ : s ≤ i + 1 := hsi.trans (Nat.le_succ i)
    have hsub_succ : i + 1 - s = (i - s) + 1 := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_sub hsi
    have hi_eq : s + (i - s) = i := Nat.add_sub_of_le hsi
    simp only [C_seq, B, dif_pos hsi, dif_pos hsi_succ]
    rw [hsub_succ, states_succ]
  have hdensity_step : ∀ i, s ≤ i → i < k →
      (2 ^ t (i + 1)) * (C_seq i).card ≤
        (overhead_bound * 2 ^ t i) * (C_seq (i + 1)).card := by
    intro i hsi hik
    have hi_eq : s + (i - s) = i := Nat.add_sub_of_le hsi
    have hinv := states_invariant (i - s) (by rw [hi_eq]; exact Nat.le_of_lt hik)
    have hex := next_exists i (states (i - s)).1 (states (i - s)).2
      hsi hik hinv.1 (by simpa [hi_eq] using hinv.2.1) hinv.2.2.1 hinv.2.2.2
    have hnext :=
        nextB_spec i (states (i - s)).1 (states (i - s)).2 (by simpa [hi_eq] using hinv.2.1) hex
    have hsi_succ : s ≤ i + 1 := hsi.trans (Nat.le_succ i)
    have hsub_succ : i + 1 - s = (i - s) + 1 := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_sub hsi
    simp only [C_seq, dif_pos hsi, dif_pos hsi_succ]
    rw [hsub_succ, states_succ]
    simp only [step, hi_eq]
    exact hnext.2.2
  exact ⟨B, C_seq, hB_s, hC_s, hmem_B, hcard_B, hC_step, hdensity_step⟩

lemma restricted_rebuild_suffix (𝒜 : DescriptionFamily)
    (n s k : ℕ) (t : ℕ → ℕ) (overhead_bound : ℕ)
    (hover : ∀ m, 𝒜.overhead m ≤ overhead_bound)
    (A_s : Finset BitString) (hA_s : 𝒜.mem A_s)
    (C : Finset BitString) (D : Finset BitString) (hC : C ⊆ A_s)
    (hC_n : ∀ x ∈ C, x.length = n)
    (hA_s_card : A_s.card ≤ 2 ^ t s)
    (ht_strict : ∀ i, s ≤ i → i < k → t (i + 1) < t i) :
    ∃ (B : ℕ → Finset BitString) (C_seq : ℕ → Finset BitString),
      B s = A_s ∧
      C_seq s = C \ D ∧
      (∀ i, s < i → i ≤ k → 𝒜.mem (B i)) ∧
      (∀ i, s < i → i ≤ k → (B i).card ≤ 2 ^ t i) ∧
      (∀ i, s ≤ i → i < k → C_seq (i + 1) = C_seq i ∩ B (i + 1)) ∧
      (∀ i, s ≤ i → i < k →
        (2 ^ t (i + 1)) * (C_seq i).card ≤ (overhead_bound * 2 ^ t i) * (C_seq (i + 1)).card) := by
  exact restricted_rebuild_suffix_pointwise_core 𝒜 n s k t overhead_bound
    (hover n) A_s hA_s C D hC hC_n hA_s_card ht_strict

/-! ### Finite bad-description counting

The coupled process must charge rebuilds to actual bad descriptions and to
actual deleted survivors.  The following definitions and lemmas expose the
finite objects being counted; in particular, none of the witnesses below is an
unconstrained natural number.
-/

/-- Restricted family members whose canonical uniform codes have complexity at
most `i` and whose cardinality is at most `2^j`. -/
noncomputable def restrictedBadDescriptions (𝒜 : DescriptionFamily) (U : Map)
    (i j : ℕ) : Finset (Finset BitString) := by
  classical
  exact (descriptionsWithComplexityLeAndSizeLe U i j).filter 𝒜.mem

/-- There are at most `2^(i+1)` distinct restricted bad descriptions of
complexity at most `i`.  This is the honest large-description appearance
bound: appearances are counted by canonical finite sets, not by an arbitrary
existential counter. -/
lemma restricted_large_bad_appearances_le (𝒜 : DescriptionFamily) (U : Map)
    (i j : ℕ) :
    (restrictedBadDescriptions 𝒜 U i j).card ≤ 2 ^ (i + 1) := by
  classical
  calc
    (restrictedBadDescriptions 𝒜 U i j).card
        ≤ (descriptionsWithComplexityLeAndSizeLe U i j).card := by
          unfold restrictedBadDescriptions
          exact Finset.card_filter_le _ _
    _ ≤ 2 ^ (i + 1) := card_descriptionsWithComplexityLeAndSizeLe U i j

/-- The union of all restricted bad descriptions at parameters `(i,j)` has
volume at most `2^(i+1) * 2^j`. -/
lemma restricted_small_bad_deleted_volume_le (𝒜 : DescriptionFamily) (U : Map)
    (i j : ℕ) :
    ((restrictedBadDescriptions 𝒜 U i j).biUnion id).card ≤
      2 ^ (i + 1) * 2 ^ j := by
  classical
  have hsize : ∀ A ∈ restrictedBadDescriptions 𝒜 U i j, A.card ≤ 2 ^ j := by
    intro A hA
    unfold restrictedBadDescriptions at hA
    rw [Finset.mem_filter] at hA
    exact (Finset.mem_filter.mp hA.1).2
  calc
    ((restrictedBadDescriptions 𝒜 U i j).biUnion id).card
        ≤ ∑ A ∈ restrictedBadDescriptions 𝒜 U i j, A.card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ restrictedBadDescriptions 𝒜 U i j, 2 ^ j :=
          Finset.sum_le_sum hsize
    _ = (restrictedBadDescriptions 𝒜 U i j).card * 2 ^ j := by simp
    _ ≤ 2 ^ (i + 1) * 2 ^ j :=
          Nat.mul_le_mul_right (2 ^ j)
            (restricted_large_bad_appearances_le 𝒜 U i j)

/-- If every rebuild charged to small bad descriptions deletes at least `ν`
fresh survivors, and the charged deletion blocks are pairwise disjoint, then
the number of such rebuilds times `ν` is bounded by the total small-bad volume.
This is the exact finite combinatorial charging step used by the coupled
process. -/
lemma restricted_rebuilds_charged_to_deleted_volume
    {ι α : Type*}
    (rebuilds : Finset ι) (deleted : ι → Finset α)
    (smallBad : Finset α) (ν : ℕ)
    (hdisjoint : (↑rebuilds : Set ι).PairwiseDisjoint deleted)
    (hsubset : ∀ r ∈ rebuilds, deleted r ⊆ smallBad)
    (hthreshold : ∀ r ∈ rebuilds, ν ≤ (deleted r).card) :
    rebuilds.card * ν ≤ smallBad.card := by
  classical
  have hUnion : rebuilds.biUnion deleted ⊆ smallBad := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨r, hr, hxr⟩ := hx
    exact hsubset r hr hxr
  calc
    rebuilds.card * ν = ∑ _r ∈ rebuilds, ν := by simp
    _ ≤ ∑ r ∈ rebuilds, (deleted r).card := Finset.sum_le_sum hthreshold
    _ = (rebuilds.biUnion deleted).card := (Finset.card_biUnion hdisjoint).symm
    _ ≤ smallBad.card := Finset.card_le_card hUnion

/-- A decreasing chronological survivor sequence makes its fresh deletion
blocks pairwise disjoint, so the general finite deleted-volume charge applies
without requiring disjointness as a separate process invariant. -/
lemma restricted_self_rebuilds_charged_to_deleted_volume
    (rebuilds : Finset ℕ)
    (survivors deleted : ℕ → Finset BitString)
    (smallBad : Finset BitString) (threshold : ℕ)
    (h_mono : ∀ i j, i ≤ j → survivors j ⊆ survivors i)
    (h_deleted_sub : ∀ i, deleted i ⊆ survivors i)
    (h_fresh : ∀ i, Disjoint (deleted i) (survivors (i + 1)))
    (h_smallBad : ∀ r ∈ rebuilds, deleted r ⊆ smallBad)
    (h_threshold : ∀ r ∈ rebuilds, threshold ≤ (deleted r).card) :
    rebuilds.card * threshold ≤ smallBad.card := by
  have h_all := restricted_self_rebuild_deletedBlocks_pairwiseDisjoint
    survivors deleted h_mono h_deleted_sub h_fresh
  apply restricted_rebuilds_charged_to_deleted_volume
    rebuilds deleted smallBad threshold
  · intro i _hi j _hj hij
    exact h_all (Set.mem_univ i) (Set.mem_univ j) hij
  · exact h_smallBad
  · exact h_threshold

/-- The candidates already carrying a forbidden restricted-profile witness.
This concrete filter is the bad set packaged by `RestrictedScaleTemplate`. -/
noncomputable def restrictedProfileBadSet (𝒜 : DescriptionFamily) (U : Map)
    (candidates : Finset BitString) (k Δ : ℕ) (t : ℕ → ℕ) :
    Finset BitString := by
  classical
  exact candidates.filter fun x => ∃ i : ℕ, i ≤ k ∧ t i > Δ ∧
    InDescriptionProfileIn 𝒜 U x i (t i - (Δ + 1))

/-
Filtering candidates by the forbidden-profile predicate simultaneously gives
the subset and exact-membership fields required by the scale template.
-/
lemma restrictedProfileBadSet_spec (𝒜 : DescriptionFamily) (U : Map)
    (candidates : Finset BitString) (k Δ : ℕ) (t : ℕ → ℕ) :
    restrictedProfileBadSet 𝒜 U candidates k Δ t ⊆ candidates ∧
      ∀ x ∈ candidates,
        x ∈ restrictedProfileBadSet 𝒜 U candidates k Δ t ↔
          ∃ i : ℕ, i ≤ k ∧ t i > Δ ∧
            InDescriptionProfileIn 𝒜 U x i (t i - (Δ + 1)) := by
  unfold restrictedProfileBadSet
  aesop

/-- The concrete forbidden-profile filter is bounded by the sum of the
per-boundary-point bad-description volumes.  This reduces the lower-profile
side of the scale construction to finite cardinal arithmetic; overlap between
bad descriptions only improves the estimate. -/
lemma restrictedProfileBadSet_card_le_bad_volume
    (𝒜 : DescriptionFamily) (U : Map)
    (candidates : Finset BitString) (k Δ : ℕ) (t : ℕ → ℕ) :
    (restrictedProfileBadSet 𝒜 U candidates k Δ t).card ≤
      ∑ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
        2 ^ (i + 1) * 2 ^ (t i - (Δ + 1)) := by
  classical
  let allBad : Finset BitString :=
    ((Finset.range (k + 1)).filter fun i => Δ < t i).biUnion fun i =>
      (restrictedBadDescriptions 𝒜 U i (t i - (Δ + 1))).biUnion id
  have hsub : restrictedProfileBadSet 𝒜 U candidates k Δ t ⊆ allBad := by
    intro x hx
    rw [restrictedProfileBadSet, Finset.mem_filter] at hx
    obtain ⟨i, hi, ht, hprof⟩ := hx.2
    obtain ⟨S, hS, hmem, hdesc⟩ := hprof
    obtain ⟨hxS, hcomp, hcard⟩ := hdesc
    dsimp [allBad]
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi), ht⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨S, ?_, hxS⟩
    unfold restrictedBadDescriptions
    rw [Finset.mem_filter, descriptionsWithComplexityLeAndSizeLe,
      Finset.mem_filter]
    exact ⟨⟨mem_descriptionsWithComplexityLe_of_complexity hS hcomp, hcard⟩,
      hmem⟩
  calc
    (restrictedProfileBadSet 𝒜 U candidates k Δ t).card
        ≤ allBad.card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
          ((restrictedBadDescriptions 𝒜 U i
            (t i - (Δ + 1))).biUnion id).card := by
          dsimp [allBad]
          exact Finset.card_biUnion_le
    _ ≤ ∑ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
          2 ^ (i + 1) * 2 ^ (t i - (Δ + 1)) := by
          exact Finset.sum_le_sum fun i _hi =>
            restricted_small_bad_deleted_volume_le 𝒜 U i
              (t i - (Δ + 1))

/-- Along a strictly decreasing boundary, the total bad-description volume is
at most `(k+1) * 2^(t 0 - Δ)`.  The filter to levels with `Δ < t i` is essential:
at lower levels the forbidden-profile predicate is inactive. -/
lemma restricted_bad_volume_sum_le
    {k Δ : ℕ} {t : ℕ → ℕ}
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i) :
    (∑ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
        2 ^ (i + 1) * 2 ^ (t i - (Δ + 1))) ≤
      (k + 1) * 2 ^ (t 0 - Δ) := by
  have hterm : ∀ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
      2 ^ (i + 1) * 2 ^ (t i - (Δ + 1)) ≤ 2 ^ (t 0 - Δ) := by
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp
      (Finset.mem_filter.mp hi).1)
    have hΔ : Δ < t i := (Finset.mem_filter.mp hi).2
    have hcurve : i + t i ≤ t 0 :=
      restricted_curve_index_add_le_start hstrict hik
    have hexp : i + 1 + (t i - (Δ + 1)) ≤ t 0 - Δ := by
      omega
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) hexp
  calc
    (∑ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
        2 ^ (i + 1) * 2 ^ (t i - (Δ + 1)))
        ≤ ∑ _i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
            2 ^ (t 0 - Δ) := Finset.sum_le_sum hterm
    _ = ((Finset.range (k + 1)).filter (fun i => Δ < t i)).card *
          2 ^ (t 0 - Δ) := by simp
    _ ≤ (k + 1) * 2 ^ (t 0 - Δ) := by
      exact Nat.mul_le_mul_right _
        ((Finset.card_filter_le _ _).trans_eq (Finset.card_range (k + 1)))

/-- Final bad-candidate cardinality estimate obtained by combining the finite
description count with strict decrease of the target boundary. -/
lemma restrictedProfileBadSet_card_le
    (𝒜 : DescriptionFamily) (U : Map)
    (candidates : Finset BitString) (k Δ : ℕ) (t : ℕ → ℕ)
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i) :
    (restrictedProfileBadSet 𝒜 U candidates k Δ t).card ≤
      (k + 1) * 2 ^ (t 0 - Δ) := by
  exact (restrictedProfileBadSet_card_le_bad_volume 𝒜 U candidates k Δ t).trans
    (restricted_bad_volume_sum_le hstrict)

/-- Output data of the computably generated coupled rebuild process, before
filtering out candidates with a forbidden restricted-profile witness.

The explicit `survivor` is the dynamic invariant replacing the false global
comparison between bad-set volume and the terminal common candidate pool. -/
structure RestrictedCoupledScaleProcess (𝒜 : DescriptionFamily) (U : Map)
    (n k c : ℕ) (t : ℕ → ℕ) where
  gridSteps : ℕ
  grid : RestrictedCurveGrid n k gridSteps t
  gridSteps_eq : gridSteps = Nat.sqrt (n / (Nat.log2 n + 1)) + 1
  grid_code_complexity :
    KPPlain U (restrictedCurveGridCode grid) ≤ (sqrtSlack c n : ENat)
  ambientLength : ℕ
  n_le_ambient : n ≤ ambientLength
  ambient_le : ambientLength ≤ n + logSlack c n
  goodSets : ℕ → Finset BitString
  mem_family : ∀ s (_hs : s ≤ k), 𝒜.mem (goodSets s)
  size_bound : ∀ s (_hs : s ≤ k),
    (goodSets s).card ≤ 2 ^ (t s + sqrtSlack c n)
  complexity_bound : ∀ s (_hs : s ≤ k) (hS : (goodSets s).Nonempty),
    setComplexity U (goodSets s) hS ≤ (s + sqrtSlack c n : ENat)
  candidates : Finset BitString
  candidates_nonempty : candidates.Nonempty
  candidate_len : ∀ x ∈ candidates, x.length = ambientLength
  candidate_mem : ∀ x ∈ candidates, ∀ s (_hs : s ≤ k), x ∈ goodSets s
  candidate_complexity : ∀ x ∈ candidates,
    KPPlain U x ≤ (k + sqrtSlack c n : ENat)
  survivor : BitString
  survivor_mem : survivor ∈ candidates
  survivor_not_bad :
    survivor ∉ restrictedProfileBadSet 𝒜 U candidates k (sqrtSlack c n) t

/-- The dynamic output of the sampled run, separated from the already-proved
encoded-grid construction.  This is the part that stabilization and fixed-length
version coding must produce. -/
structure RestrictedCoupledOutput (𝒜 : DescriptionFamily) (U : Map)
    (n k c : ℕ) (t : ℕ → ℕ) where
  ambientLength : ℕ
  n_le_ambient : n ≤ ambientLength
  ambient_le : ambientLength ≤ n + logSlack c n
  goodSets : ℕ → Finset BitString
  mem_family : ∀ s (_hs : s ≤ k), 𝒜.mem (goodSets s)
  size_bound : ∀ s (_hs : s ≤ k),
    (goodSets s).card ≤ 2 ^ (t s + sqrtSlack c n)
  complexity_bound : ∀ s (_hs : s ≤ k) (hS : (goodSets s).Nonempty),
    setComplexity U (goodSets s) hS ≤ (s + sqrtSlack c n : ENat)
  candidates : Finset BitString
  candidates_nonempty : candidates.Nonempty
  candidate_len : ∀ x ∈ candidates, x.length = ambientLength
  candidate_mem : ∀ x ∈ candidates, ∀ s (_hs : s ≤ k), x ∈ goodSets s
  candidate_complexity : ∀ x ∈ candidates,
    KPPlain U x ≤ (k + sqrtSlack c n : ENat)
  survivor : BitString
  survivor_mem : survivor ∈ candidates
  survivor_not_bad :
    survivor ∉ restrictedProfileBadSet 𝒜 U candidates k (sqrtSlack c n) t

/-- The genuine dynamic and coding output at the `N + 1` sampled boundary
scales.  It deliberately omits the elementary mesh inequality, which is added
by `RestrictedSampledOutputCore.toSampledOutput`. -/
structure RestrictedSampledOutputCore (𝒜 : DescriptionFamily) (U : Map)
    (n k N c : ℕ) (t : ℕ → ℕ) (grid : RestrictedCurveGrid n k N t) where
  ambientLength : ℕ
  n_le_ambient : n ≤ ambientLength
  ambient_le : ambientLength ≤ n + logSlack c n
  sampledSets : ℕ → Finset BitString
  mem_family : ∀ s (_hs : s ≤ N), 𝒜.mem (sampledSets s)
  size_bound : ∀ s (_hs : s ≤ N), (sampledSets s).card ≤ 2 ^ grid.j s
  complexity_bound : ∀ s (_hs : s ≤ N) (hS : (sampledSets s).Nonempty),
    setComplexity U (sampledSets s) hS ≤ (grid.i s + sqrtSlack c n : ENat)
  candidates : Finset BitString
  candidates_nonempty : candidates.Nonempty
  candidate_len : ∀ x ∈ candidates, x.length = ambientLength
  candidate_mem : ∀ x ∈ candidates, ∀ s (_hs : s ≤ N), x ∈ sampledSets s
  candidate_complexity : ∀ x ∈ candidates,
    KPPlain U x ≤ (k + sqrtSlack c n : ENat)
  survivor : BitString
  survivor_mem : survivor ∈ candidates
  survivor_not_bad :
    survivor ∉ restrictedProfileBadSet 𝒜 U candidates k (sqrtSlack c n) t

/-- Output at the `N + 1` sampled boundary scales maintained by the coupled
rebuild construction.  The all-index `RestrictedCoupledOutput` is obtained by
interpolating with the predecessor sample supplied by `grid`.

Keeping this intermediate object explicit prevents the dynamic run from being
artificially indexed by all `k + 1` boundary coordinates. -/
structure RestrictedSampledOutput (𝒜 : DescriptionFamily) (U : Map)
    (n k N c : ℕ) (t : ℕ → ℕ) (grid : RestrictedCurveGrid n k N t)
    extends RestrictedSampledOutputCore 𝒜 U n k N c t grid where
  mesh_le_slack : n / N + 1 ≤ sqrtSlack c n

/-- Add the separately proved numeric mesh estimate to the dynamic sampled
output. -/
def RestrictedSampledOutputCore.toSampledOutput
    {𝒜 : DescriptionFamily} {U : Map} {n k N c : ℕ} {t : ℕ → ℕ}
    {grid : RestrictedCurveGrid n k N t}
    (output : RestrictedSampledOutputCore 𝒜 U n k N c t grid)
    (hmesh : n / N + 1 ≤ sqrtSlack c n) :
    RestrictedSampledOutput 𝒜 U n k N c t grid :=
  { toRestrictedSampledOutputCore := output
    mesh_le_slack := hmesh }

/-- The predecessor sample used to interpolate a sampled family-curve output
at an arbitrary horizontal coordinate `idx ≤ k`. -/
noncomputable def restrictedCurveGridPredecessor
    {n k N : ℕ} {t : ℕ → ℕ} (grid : RestrictedCurveGrid n k N t)
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i) (idx : ℕ) : ℕ :=
  if hidx : idx ≤ k then
    Classical.choose (restrictedCurveGrid_height_le_target_add_mesh grid hstrict idx hidx)
  else 0

/-- The predecessor sample lies below `idx` horizontally and at most one mesh
above `t idx` vertically. -/
lemma restrictedCurveGridPredecessor_spec
    {n k N : ℕ} {t : ℕ → ℕ} (grid : RestrictedCurveGrid n k N t)
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i) (idx : ℕ) (hidx : idx ≤ k) :
    restrictedCurveGridPredecessor grid hstrict idx < N ∧
      grid.i (restrictedCurveGridPredecessor grid hstrict idx) ≤ idx ∧
      grid.j (restrictedCurveGridPredecessor grid hstrict idx) ≤
        t idx + (n / N + 1) := by
  unfold restrictedCurveGridPredecessor
  rw [dif_pos hidx]
  have hs := Classical.choose_spec
    (restrictedCurveGrid_height_le_target_add_mesh grid hstrict idx hidx)
  exact ⟨hs.1, hs.2.1, hs.2.2.2⟩

/-- Interpolate sampled good sets to every `idx ≤ k`.  This is the purely
static final assembly step applied after the dynamic construction produces the
`N + 1` sampled versions and their common surviving candidate. -/
lemma RestrictedSampledOutput.toCoupledOutput
    {𝒜 : DescriptionFamily} {U : Map} {n k N c : ℕ} {t : ℕ → ℕ}
    {grid : RestrictedCurveGrid n k N t}
    (output : RestrictedSampledOutput 𝒜 U n k N c t grid)
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i) :
    Nonempty (RestrictedCoupledOutput 𝒜 U n k c t) := by
  let pred : ℕ → ℕ := restrictedCurveGridPredecessor grid hstrict
  refine ⟨{
    ambientLength := output.ambientLength
    n_le_ambient := output.n_le_ambient
    ambient_le := output.ambient_le
    goodSets := fun idx => output.sampledSets (pred idx)
    mem_family := ?_
    size_bound := ?_
    complexity_bound := ?_
    candidates := output.candidates
    candidates_nonempty := output.candidates_nonempty
    candidate_len := output.candidate_len
    candidate_mem := ?_
    candidate_complexity := output.candidate_complexity
    survivor := output.survivor
    survivor_mem := output.survivor_mem
    survivor_not_bad := output.survivor_not_bad }⟩
  · intro idx hidx
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    exact output.mem_family (pred idx) (Nat.le_of_lt hp.1)
  · intro idx hidx
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    calc
      (output.sampledSets (pred idx)).card ≤ 2 ^ grid.j (pred idx) :=
        output.size_bound (pred idx) (Nat.le_of_lt hp.1)
      _ ≤ 2 ^ (t idx + sqrtSlack c n) := by
        apply Nat.pow_le_pow_right (by decide)
        exact hp.2.2.trans (Nat.add_le_add_left output.mesh_le_slack (t idx))
  · intro idx hidx hS
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    calc
      setComplexity U (output.sampledSets (pred idx)) hS ≤
          (grid.i (pred idx) + sqrtSlack c n : ENat) :=
        output.complexity_bound (pred idx) (Nat.le_of_lt hp.1) hS
      _ ≤ (idx + sqrtSlack c n : ENat) := by
        exact_mod_cast Nat.add_le_add_right hp.2.1 (sqrtSlack c n)
  · intro x hx idx hidx
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    exact output.candidate_mem x hx (pred idx) (Nat.le_of_lt hp.1)

/-
Package the output of the coupled construction once its survivor and
forbidden-profile cardinality estimates have been established.
-/
lemma RestrictedScaleTemplate.ofCandidates
    {𝒜 : DescriptionFamily} {U : Map} {n k c : ℕ} {t : ℕ → ℕ}
    (ambientLength : ℕ)
    (h_n_le : n ≤ ambientLength)
    (h_ambient_le : ambientLength ≤ n + logSlack c n)
    (goodSets : ℕ → Finset BitString)
    (h_mem : ∀ s (_hs : s ≤ k), 𝒜.mem (goodSets s))
    (h_size : ∀ s (_hs : s ≤ k), (goodSets s).card ≤ 2 ^ (t s + sqrtSlack c n))
    (h_complexity : ∀ s (_hs : s ≤ k) (hS : (goodSets s).Nonempty),
      setComplexity U (goodSets s) hS ≤ (s + sqrtSlack c n : ENat))
    (candidates : Finset BitString)
    (h_candidates_nonempty : candidates.Nonempty)
    (h_candidate_len : ∀ x ∈ candidates, x.length = ambientLength)
    (h_candidate_mem : ∀ x ∈ candidates, ∀ s (_hs : s ≤ k), x ∈ goodSets s)
    (h_candidate_complexity : ∀ x ∈ candidates,
      KPPlain U x ≤ (k + sqrtSlack c n : ENat))
    (survivor : BitString)
    (h_survivor_mem : survivor ∈ candidates)
    (h_survivor_not_bad :
      survivor ∉ restrictedProfileBadSet 𝒜 U candidates k (sqrtSlack c n) t) :
    Nonempty (RestrictedScaleTemplate 𝒜 U n k c t) := by
  obtain ⟨h_bad_subset, h_bad_exact⟩ :=
    restrictedProfileBadSet_spec 𝒜 U candidates k (sqrtSlack c n) t
  exact ⟨{
    ambientLength := ambientLength
    n_le_ambient := h_n_le
    ambient_le := h_ambient_le
    goodSets := goodSets
    mem_family := h_mem
    size_bound := h_size
    complexity_bound := h_complexity
    candidates := candidates
    candidates_nonempty := h_candidates_nonempty
    candidate_len := h_candidate_len
    candidate_mem := h_candidate_mem
    candidate_complexity := h_candidate_complexity
    badSet := restrictedProfileBadSet 𝒜 U candidates k (sqrtSlack c n) t
    badSet_subset_candidates := h_bad_subset
    badSet_exact := h_bad_exact
    survivor := survivor
    survivor_mem := h_survivor_mem
    survivor_not_bad := h_survivor_not_bad }⟩

/-- Filtering the output of a coupled process by the concrete forbidden-profile
set produces a scale template. -/
lemma RestrictedCoupledScaleProcess.toTemplate
    {𝒜 : DescriptionFamily} {U : Map} {n k c : ℕ} {t : ℕ → ℕ}
    (process : RestrictedCoupledScaleProcess 𝒜 U n k c t) :
    Nonempty (RestrictedScaleTemplate 𝒜 U n k c t) := by
  apply RestrictedScaleTemplate.ofCandidates
    process.ambientLength process.n_le_ambient process.ambient_le
    process.goodSets process.mem_family process.size_bound
    process.complexity_bound process.candidates process.candidates_nonempty
    process.candidate_len process.candidate_mem process.candidate_complexity
    process.survivor process.survivor_mem process.survivor_not_bad

/-
Polynomial covering overhead supplies a uniform square-root budget for
all sampled-scale covering costs.  This specializes
`restrictedCurveGrid_scale_budget` to the overhead function carried by the
family.
-/
lemma DescriptionFamily.sampled_cover_cost_le_sqrtSlack
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_budget : ℕ, ∀ (n N : ℕ),
      N ≤ Nat.sqrt (n / (Nat.log2 n + 1)) + 1 →
      N * (Nat.log2 (𝒜.overhead n) + 1) ≤ sqrtSlack c_budget n := by
  obtain ⟨C, d, hC, hbound⟩ := hPoly
  obtain ⟨c_budget, hc⟩ := restrictedCurveGrid_scale_budget C d hC
  exact ⟨c_budget, fun n N hN => hc n _ _ hbound hN⟩

/-
The pointwise suffix-density recurrence preserves a nonempty terminal
survivor pool.  This isolates the final positivity argument from the
chronological version-counting construction.
-/
lemma restricted_rebuild_suffix_preserves_terminal_nonempty
    (s k overheadBound : ℕ) (t : ℕ → ℕ)
    (live : ℕ → Finset BitString)
    (hsk : s ≤ k) (hLive : (live s).Nonempty)
    (hstep : ∀ i, s ≤ i → i < k →
      (2 ^ t (i + 1)) * (live i).card ≤
        (overheadBound * 2 ^ t i) * (live (i + 1)).card) :
    (live k).Nonempty := by
  have h_density :
      (2 ^ t k) * (live s).card ≤
        (overheadBound ^ (k - s) * 2 ^ t s) * (live k).card := by
    exact restricted_rebuild_suffix_density s k t overheadBound live hsk hstep
  exact restricted_rebuild_suffix_terminal_nonempty
    s k overheadBound t live hLive h_density

/-
A pointwise-overhead adapter for rebuilding a suffix at a fixed string length.
Unlike `restricted_rebuild_suffix`, this only assumes the overhead estimate at
that one length, which is all the construction uses.
-/
lemma restricted_rebuild_suffix_at_length
    (𝒜 : DescriptionFamily)
    (n s k : ℕ) (t : ℕ → ℕ) (overheadBound : ℕ)
    (hover : 𝒜.overhead n ≤ overheadBound)
    (A_s : Finset BitString) (hA_s : 𝒜.mem A_s)
    (C D : Finset BitString) (hC : C ⊆ A_s)
    (hC_n : ∀ x ∈ C, x.length = n)
    (hA_s_card : A_s.card ≤ 2 ^ t s)
    (ht_strict : ∀ i, s ≤ i → i < k → t (i + 1) < t i) :
    ∃ (B C_seq : ℕ → Finset BitString),
      B s = A_s ∧
      C_seq s = C \ D ∧
      (∀ i, s < i → i ≤ k → 𝒜.mem (B i)) ∧
      (∀ i, s < i → i ≤ k → (B i).card ≤ 2 ^ t i) ∧
      (∀ i, s ≤ i → i < k →
        C_seq (i + 1) = C_seq i ∩ B (i + 1)) ∧
      (∀ i, s ≤ i → i < k →
        (2 ^ t (i + 1)) * (C_seq i).card ≤
          (overheadBound * 2 ^ t i) * (C_seq (i + 1)).card) := by
  exact restricted_rebuild_suffix_pointwise_core 𝒜 n s k t overheadBound
    hover A_s hA_s C D hC hC_n hA_s_card ht_strict

/-
A strict cardinality gap between a candidate pool and its bad subset
produces a concrete surviving candidate.
-/
lemma restricted_exists_survivor_outside_bad
    (candidates bad : Finset BitString)
    (hbad : bad ⊆ candidates) (hcard : bad.card < candidates.card) :
    ∃ x ∈ candidates, x ∉ bad := by
  exact Finset.exists_of_ssubset
    (hbad.ssubset_of_ne (by
      intro heq
      subst bad
      simp at hcard))

/-
Filtering a stabilized coupled output by the concrete forbidden-profile
set produces the corresponding scale template.
-/
lemma RestrictedCoupledOutput.toTemplate
    {𝒜 : DescriptionFamily} {U : Map} {n k c : ℕ} {t : ℕ → ℕ}
    (output : RestrictedCoupledOutput 𝒜 U n k c t) :
    Nonempty (RestrictedScaleTemplate 𝒜 U n k c t) := by
  apply RestrictedScaleTemplate.ofCandidates
    output.ambientLength output.n_le_ambient output.ambient_le
    output.goodSets output.mem_family output.size_bound
    output.complexity_bound output.candidates output.candidates_nonempty
    output.candidate_len output.candidate_mem output.candidate_complexity
    output.survivor output.survivor_mem output.survivor_not_bad

/-
A coupled output remains valid when its uniform slack constant is enlarged.
-/
lemma RestrictedCoupledOutput.mono_slack
    {𝒜 : DescriptionFamily} {U : Map} {n k c c' : ℕ} {t : ℕ → ℕ}
    (output : RestrictedCoupledOutput 𝒜 U n k c t) (hcc' : c ≤ c') :
    Nonempty (RestrictedCoupledOutput 𝒜 U n k c' t) := by
  obtain ⟨ ambientLength, n_le_ambient, ambient_le, goodSets, mem_family, size_bound,
           complexity_bound, candidates, candidates_nonempty, candidate_len, candidate_mem,
               candidate_complexity, survivor, survivor_mem, survivor_not_bad ⟩ := output;
  refine ⟨ ⟨ ambientLength, n_le_ambient, ?_, goodSets, mem_family, ?_, ?_, candidates,
              candidates_nonempty, candidate_len, candidate_mem, ?_, survivor, survivor_mem, ?_
                  ⟩ ⟩ <;> try linarith [ logSlack_mono_left hcc' n ];
  · exact fun s hs =>
      le_trans ( size_bound s hs )
          ( pow_le_pow_right₀ ( by decide ) ( Nat.add_le_add_left ( sqrtSlack_mono_left hcc' n ) _
                                              ) );
  · intro s hs hS; specialize complexity_bound s hs hS; exact le_trans complexity_bound (by
    exact_mod_cast Nat.add_le_add_left ( sqrtSlack_mono_left hcc' n ) s);
  · exact fun x hx =>
      le_trans ( candidate_complexity x hx ) ( by gcongr ; exact sqrtSlack_mono_left hcc' n );
  · intro h
    contrapose! survivor_not_bad
    simp_all +decide only [KPPlain_eq_KP, restrictedProfileBadSet, gt_iff_lt,
      Finset.mem_filter, true_and]
    obtain ⟨ i, hi, hi', hi'' ⟩ := h; use i, hi; refine ⟨ lt_of_le_of_lt ?_ hi', ?_ ⟩;
    · exact sqrtSlack_mono_left hcc' n;
    · exact InDescriptionProfileIn.mono_j
        (Nat.sub_le_sub_left (Nat.succ_le_succ (sqrtSlack_mono_left hcc' n)) _) hi''

/-
It suffices to construct the dynamic output with a base slack constant:
the separate grid-coding allowance can then be absorbed monotonically.
-/
lemma restricted_coupled_output_uniform_of_base
    (𝒜 : DescriptionFamily) (U : Map) (c_run : ℕ)
    (hbase : ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      Nonempty (RestrictedCoupledOutput 𝒜 U n k c_run t)) :
    ∀ (c_grid n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      Nonempty (RestrictedCoupledOutput 𝒜 U n k (c_grid + c_run) t) := by
  intros c_grid n k t hk h0 hk0 ht;
  exact RestrictedCoupledOutput.mono_slack ( hbase n k t hk h0 hk0 ht |> Classical.choice )
      ( by linarith )

end Kolmogorov
