/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.BoundedBetStrategy

/-!
# Muchnik Witnesses

A finite family of computable monotone selection rules witnessing a bias.  The main declaration
is `not_isMisesKLRandom_of_plainK_lt_finite_selection`: for `0 < β < 1` there are a number `M` of
rules and a rational `ε > 0`, depending only on `β`, such that, uniformly computably in a finite
Kraft-bounded list `D` of words, every word of `D` has one of the `M` rules selecting a
subsequence whose discrepancy between zeros and ones is at least `ε` times the word's length.
The supporting lemmas are an arithmetic-geometric mean estimate for products of bet gains, the
discretization of the gains, the computability of the weights defining the rules, and the fact
that the rules select the classes of the bias.  This is the finite martingale/selection argument
used for the non-monotone selection rules of Merkle, Miller, Nies, Reimann and Stephan
(Proposition 35 and Remark 37), discussed in Chapter 13 of the book by Shen, Uspensky and
Vereshchagin.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-- Step 7 (analysis) of the proof of `not_isMisesKLRandom_of_plainK_lt`:
if the product of `n` numbers `u i ∈ (0, 1]` is at least `2 ^ (-(β n) - 1)`, then their
"bet gains" `2 u i - 1` sum to at least `((1 - β) / 2) n - 3 / 2`.  Tangent line of `exp`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_amgm (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (n : ℕ) (u : Fin n → ℝ) (hu0 : ∀ i, 0 < u i)
    (hprod : (2 : ℝ) ^ (-(β * n) - 1) ≤ ∏ i, u i) :
    ((1 - β) / 2) * n - 3 / 2 ≤ ∑ i, (2 * u i - 1) := by
  have hl_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h2exp : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  set ℓ := Real.log 2 with hℓ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hβ' : 0 ≤ 1 - β := by linarith
  set E := Real.exp (-(β * ℓ)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have h2E : 2 * E = Real.exp ((1 - β) * ℓ) := by
    calc 2 * E = Real.exp ℓ * Real.exp (-(β * ℓ)) := by rw [← h2exp]
      _ = Real.exp (ℓ + -(β * ℓ)) := (Real.exp_add _ _).symm
      _ = Real.exp ((1 - β) * ℓ) := by ring_nf
  have hexp_ge : 1 + (1 - β) * ℓ ≤ 2 * E := by
    rw [h2E]
    linarith [Real.add_one_le_exp ((1 - β) * ℓ)]
  -- tangent line bound `u i ≥ E (1 + log (u i) + β ℓ)`
  have htan : ∀ i, E * (1 + Real.log (u i) + β * ℓ) ≤ u i := by
    intro i
    have h1 : u i = E * Real.exp (Real.log (u i) + β * ℓ) := by
      rw [hE, ← Real.exp_add]
      have : -(β * ℓ) + (Real.log (u i) + β * ℓ) = Real.log (u i) := by ring
      rw [this, Real.exp_log (hu0 i)]
    have h2 := Real.add_one_le_exp (Real.log (u i) + β * ℓ)
    calc E * (1 + Real.log (u i) + β * ℓ) = E * ((Real.log (u i) + β * ℓ) + 1) := by ring
      _ ≤ E * Real.exp (Real.log (u i) + β * ℓ) := by gcongr
      _ = u i := h1.symm
  have hsum_tan : E * ((n : ℝ) + ∑ i, Real.log (u i) + n * (β * ℓ)) ≤ ∑ i, u i := by
    calc E * ((n : ℝ) + ∑ i, Real.log (u i) + n * (β * ℓ))
        = ∑ i, E * (1 + Real.log (u i) + β * ℓ) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp
      _ ≤ ∑ i, u i := Finset.sum_le_sum (fun i _ => htan i)
  have hlogprod : Real.log (∏ i, u i) = ∑ i, Real.log (u i) :=
    Real.log_prod (fun i _ => (hu0 i).ne')
  have hlog_ge : (-(β * n) - 1) * ℓ ≤ ∑ i, Real.log (u i) := by
    rw [← hlogprod]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(β * n) - 1) := by positivity
    have := Real.log_le_log hpos hprod
    rwa [Real.log_rpow (by norm_num)] at this
  have hsumu : E * ((n : ℝ) - ℓ) ≤ ∑ i, u i := by
    refine le_trans ?_ hsum_tan
    have : (n : ℝ) - ℓ ≤ (n : ℝ) + ∑ i, Real.log (u i) + n * (β * ℓ) := by
      nlinarith [hlog_ge]
    exact mul_le_mul_of_nonneg_left this hEpos.le
  have hrhs : ∑ i, (2 * u i - 1) = 2 * ∑ i, u i - n := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  rw [hrhs]
  have hEl : E * ℓ ≤ ℓ := mul_le_of_le_one_left hl_pos.le hE1
  have hprod1 : 0 ≤ (n : ℝ) * (2 * E - 1 - (1 - β) * ℓ) := by
    apply mul_nonneg hn0
    linarith
  have hprod2 : 0 ≤ (n : ℝ) * (1 - β) * (ℓ - 1 / 2) := by
    apply mul_nonneg (mul_nonneg hn0 hβ')
    linarith
  nlinarith [hsumu, hEl, hprod1, hprod2, hl_lt]

/-- `betGainOnOne` as a sum over the positions `0, …, |x| - 1`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_gain_eq_range (s : BitString → ℝ)
    (x : BitString) :
    betGainOnOne s x = ∑ i ∈ Finset.range x.length,
      s (x.take i) * (if x.getD i false then 1 else -1) := by
  unfold betGainOnOne
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => s (x.take i) * (if x.getD i false then 1 else -1)) x.length]
  apply Finset.sum_congr rfl
  intro i _
  rw [List.getD_eq_getElem _ _ i.2]
  rfl

/-- Appending one bit adds the bet on that bit to `betGainOnOne`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_gain_append (s : BitString → ℝ)
    (x : BitString) (b : Bool) :
    betGainOnOne s (x ++ [b]) = betGainOnOne s x + s x * (if b then 1 else -1) := by
  rw [not_isMisesKLRandom_of_plainK_lt_gain_eq_range,
    not_isMisesKLRandom_of_plainK_lt_gain_eq_range, List.length_append,
    List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < x.length := Finset.mem_range.mp hi
    rw [List.take_append_of_le_length hi'.le, List.getD_append _ _ _ _ hi']
  · rw [List.take_left, List.getD_append_right _ _ _ _ le_rfl]
    simp

/-- The number of `true` bits selected from `x` by the class `⌊L s⌋ = c`. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_cntT (s : BitString → ℝ)
    (L : ℕ) (c : ℤ) (x : BitString) : ℝ :=
  ((selectedBits {y | ⌊(L : ℝ) * s y⌋ = c} x).count true : ℝ)

/-- The number of `false` bits selected from `x` by the class `⌊L s⌋ = c`. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_cntF (s : BitString → ℝ)
    (L : ℕ) (c : ℤ) (x : BitString) : ℝ :=
  ((selectedBits {y | ⌊(L : ℝ) * s y⌋ = c} x).count false : ℝ)

private lemma not_isMisesKLRandom_of_plainK_lt_cntT_append (s : BitString → ℝ) (L : ℕ)
    (c : ℤ) (x : BitString) (b : Bool) :
    not_isMisesKLRandom_of_plainK_lt_cntT s L c (x ++ [b]) =
      not_isMisesKLRandom_of_plainK_lt_cntT s L c x +
        (if ⌊(L : ℝ) * s x⌋ = c ∧ b = true then 1 else 0) := by
  unfold not_isMisesKLRandom_of_plainK_lt_cntT
  rw [selectedBits_append_singleton]
  by_cases h : ⌊(L : ℝ) * s x⌋ = c
  · have hx : x ∈ {y : BitString | ⌊(L : ℝ) * s y⌋ = c} := h
    rw [ite_eq_left hx]
    cases b <;> simp [h, List.count_append]
  · have hx : x ∉ {y : BitString | ⌊(L : ℝ) * s y⌋ = c} := h
    rw [ite_eq_right hx]
    simp [h]

private lemma not_isMisesKLRandom_of_plainK_lt_cntF_append (s : BitString → ℝ) (L : ℕ)
    (c : ℤ) (x : BitString) (b : Bool) :
    not_isMisesKLRandom_of_plainK_lt_cntF s L c (x ++ [b]) =
      not_isMisesKLRandom_of_plainK_lt_cntF s L c x +
        (if ⌊(L : ℝ) * s x⌋ = c ∧ b = false then 1 else 0) := by
  unfold not_isMisesKLRandom_of_plainK_lt_cntF
  rw [selectedBits_append_singleton]
  by_cases h : ⌊(L : ℝ) * s x⌋ = c
  · have hx : x ∈ {y : BitString | ⌊(L : ℝ) * s y⌋ = c} := h
    rw [ite_eq_left hx]
    cases b <;> simp [h, List.count_append]
  · have hx : x ∉ {y : BitString | ⌊(L : ℝ) * s y⌋ = c} := h
    rw [ite_eq_right hx]
    simp [h]

/-- Key inequality for the discretization, by induction on the string: the gain of the bet `s`
is bounded by a sum over the `2 L + 1` classes `⌊L s⌋ = c`, and the classes partition the
positions. -/
private lemma not_isMisesKLRandom_of_plainK_lt_disc_key (s : BitString → ℝ)
    (hs : ∀ y, |s y| ≤ 1) (L : ℕ) (hL : 0 < L) (x : BitString) :
    betGainOnOne s x ≤ ∑ c ∈ Finset.Icc (-(L : ℤ)) L,
        ((c : ℝ) / L * (not_isMisesKLRandom_of_plainK_lt_cntT s L c x -
            not_isMisesKLRandom_of_plainK_lt_cntF s L c x) +
          not_isMisesKLRandom_of_plainK_lt_cntT s L c x / L) ∧
    ∑ c ∈ Finset.Icc (-(L : ℤ)) L,
        (not_isMisesKLRandom_of_plainK_lt_cntT s L c x +
          not_isMisesKLRandom_of_plainK_lt_cntF s L c x) = x.length := by
  induction x using List.reverseRecOn with
  | nil =>
    simp [betGainOnOne, not_isMisesKLRandom_of_plainK_lt_cntT,
      not_isMisesKLRandom_of_plainK_lt_cntF, selectedBits, selectedAux]
  | append_singleton x b ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hb := abs_le.mp (hs x)
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℤ, ⌊(L : ℝ) * s x⌋ = c₀ := ⟨_, rfl⟩
    have hc₀1 : (c₀ : ℝ) ≤ (L : ℝ) * s x := by rw [← hc₀]; exact Int.floor_le _
    have hc₀2 : (L : ℝ) * s x < c₀ + 1 := by rw [← hc₀]; exact Int.lt_floor_add_one _
    have hc₀mem : c₀ ∈ Finset.Icc (-(L : ℤ)) L := by
      rw [Finset.mem_Icc]
      constructor
      · rw [← hc₀]
        apply Int.le_floor.mpr
        push_cast
        nlinarith [hb.1]
      · have : (c₀ : ℝ) ≤ (L : ℝ) := hc₀1.trans (by nlinarith [hb.2])
        exact_mod_cast this
    have hstep : ∀ c : ℤ,
        (c : ℝ) / L * (not_isMisesKLRandom_of_plainK_lt_cntT s L c (x ++ [b]) -
            not_isMisesKLRandom_of_plainK_lt_cntF s L c (x ++ [b])) +
          not_isMisesKLRandom_of_plainK_lt_cntT s L c (x ++ [b]) / L =
        ((c : ℝ) / L * (not_isMisesKLRandom_of_plainK_lt_cntT s L c x -
            not_isMisesKLRandom_of_plainK_lt_cntF s L c x) +
          not_isMisesKLRandom_of_plainK_lt_cntT s L c x / L) +
        (if c₀ = c then (if b = true then (c : ℝ) / L + 1 / L else -((c : ℝ) / L)) else 0) := by
      intro c
      rw [not_isMisesKLRandom_of_plainK_lt_cntT_append,
        not_isMisesKLRandom_of_plainK_lt_cntF_append, hc₀]
      by_cases hc : c₀ = c
      · subst hc
        cases b <;> simp <;> ring
      · cases b <;> simp [hc]
    have hcount : ∀ c : ℤ,
        not_isMisesKLRandom_of_plainK_lt_cntT s L c (x ++ [b]) +
            not_isMisesKLRandom_of_plainK_lt_cntF s L c (x ++ [b]) =
          (not_isMisesKLRandom_of_plainK_lt_cntT s L c x +
            not_isMisesKLRandom_of_plainK_lt_cntF s L c x) + (if c₀ = c then 1 else 0) := by
      intro c
      rw [not_isMisesKLRandom_of_plainK_lt_cntT_append,
        not_isMisesKLRandom_of_plainK_lt_cntF_append, hc₀]
      by_cases hc : c₀ = c
      · subst hc
        cases b <;> simp <;> ring
      · cases b <;> simp [hc]
    constructor
    · rw [not_isMisesKLRandom_of_plainK_lt_gain_append,
        Finset.sum_congr rfl (fun c _ => hstep c), Finset.sum_add_distrib, Finset.sum_ite_eq,
        ite_eq_left hc₀mem]
      have hbet : s x * (if b = true then 1 else -1) ≤
          (if b = true then (c₀ : ℝ) / L + 1 / L else -((c₀ : ℝ) / L)) := by
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have : (c₀ : ℝ) / L ≤ s x := by
            rw [div_le_iff₀ hLpos]; linarith
          linarith
        · simp only [↓reduceIte]
          have : s x ≤ ((c₀ : ℝ) + 1) / L := by
            rw [le_div_iff₀ hLpos]; linarith
          rw [add_div] at this
          linarith
      linarith
    · rw [Finset.sum_congr rfl (fun c _ => hcount c), Finset.sum_add_distrib, Finset.sum_ite_eq,
        ite_eq_left hc₀mem, ih2, List.length_append, List.length_singleton]
      push_cast
      ring

/-- Step 7 (discretization) of the proof of `not_isMisesKLRandom_of_plainK_lt`:
a bet `s` with values in `[-1, 1]` is cut into the `2 L + 1` selection classes `⌊L s⌋ = c`
(`-L ≤ c ≤ L`); one of the classes has a discrepancy proportional to the gain of `s`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_discretize
    (s : BitString → ℝ) (hs : ∀ y, |s y| ≤ 1) (L : ℕ) (hL : 0 < L) (x : BitString) :
    ∃ c : ℤ, -(L : ℤ) ≤ c ∧ c ≤ L ∧
      (betGainOnOne s x - (x.length : ℝ) / L) / (2 * L + 1) ≤
        |((selectedBits {y | ⌊(L : ℝ) * s y⌋ = c} x).count true : ℝ) -
          (selectedBits {y | ⌊(L : ℝ) * s y⌋ = c} x).count false| := by
  obtain ⟨h1, h2⟩ := not_isMisesKLRandom_of_plainK_lt_disc_key s hs L hL x
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hne : (Finset.Icc (-(L : ℤ)) L).Nonempty := ⟨0, by simp⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image (Finset.Icc (-(L : ℤ)) L)
    (fun c => |not_isMisesKLRandom_of_plainK_lt_cntT s L c x -
      not_isMisesKLRandom_of_plainK_lt_cntF s L c x|) hne
  refine ⟨c, (Finset.mem_Icc.mp hc).1, (Finset.mem_Icc.mp hc).2, ?_⟩
  -- per-class bound
  have hcls : ∀ c' ∈ Finset.Icc (-(L : ℤ)) L,
      (c' : ℝ) / L * (not_isMisesKLRandom_of_plainK_lt_cntT s L c' x -
          not_isMisesKLRandom_of_plainK_lt_cntF s L c' x) +
        not_isMisesKLRandom_of_plainK_lt_cntT s L c' x / L ≤
      |not_isMisesKLRandom_of_plainK_lt_cntT s L c' x -
          not_isMisesKLRandom_of_plainK_lt_cntF s L c' x| +
        not_isMisesKLRandom_of_plainK_lt_cntT s L c' x / L := by
    intro c' hc'
    have hcL := Finset.mem_Icc.mp hc'
    have hcabs : |(c' : ℝ) / L| ≤ 1 := by
      rw [abs_div, abs_of_pos hLpos, div_le_one hLpos]
      have h3 : |c'| ≤ (L : ℤ) := abs_le.mpr ⟨hcL.1, hcL.2⟩
      have h4 : ((|c'| : ℤ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast h3
      rwa [Int.cast_abs] at h4
    have h5 : (c' : ℝ) / L * (not_isMisesKLRandom_of_plainK_lt_cntT s L c' x -
          not_isMisesKLRandom_of_plainK_lt_cntF s L c' x) ≤
        |not_isMisesKLRandom_of_plainK_lt_cntT s L c' x -
          not_isMisesKLRandom_of_plainK_lt_cntF s L c' x| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hcabs
    linarith
  have hcard : (Finset.Icc (-(L : ℤ)) L).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  have hsumabs : ∑ c' ∈ Finset.Icc (-(L : ℤ)) L,
      |not_isMisesKLRandom_of_plainK_lt_cntT s L c' x -
        not_isMisesKLRandom_of_plainK_lt_cntF s L c' x| ≤
      (2 * L + 1 : ℝ) * |not_isMisesKLRandom_of_plainK_lt_cntT s L c x -
        not_isMisesKLRandom_of_plainK_lt_cntF s L c x| := by
    have h6 := Finset.sum_le_card_nsmul (Finset.Icc (-(L : ℤ)) L)
      (fun c' => |not_isMisesKLRandom_of_plainK_lt_cntT s L c' x -
        not_isMisesKLRandom_of_plainK_lt_cntF s L c' x|)
      |not_isMisesKLRandom_of_plainK_lt_cntT s L c x -
        not_isMisesKLRandom_of_plainK_lt_cntF s L c x| (fun c' hc' => hmax c' hc')
    rw [hcard, nsmul_eq_mul] at h6
    push_cast at h6
    exact h6
  have hsumT : ∑ c' ∈ Finset.Icc (-(L : ℤ)) L,
      not_isMisesKLRandom_of_plainK_lt_cntT s L c' x ≤ x.length := by
    rw [← h2]
    apply Finset.sum_le_sum
    intro c' _
    have : (0 : ℝ) ≤ not_isMisesKLRandom_of_plainK_lt_cntF s L c' x :=
      Nat.cast_nonneg _
    linarith
  have hgain : betGainOnOne s x ≤
      (2 * L + 1 : ℝ) * |not_isMisesKLRandom_of_plainK_lt_cntT s L c x -
        not_isMisesKLRandom_of_plainK_lt_cntF s L c x| + (x.length : ℝ) / L := by
    refine h1.trans ?_
    calc _ ≤ ∑ c' ∈ Finset.Icc (-(L : ℤ)) L,
          (|not_isMisesKLRandom_of_plainK_lt_cntT s L c' x -
            not_isMisesKLRandom_of_plainK_lt_cntF s L c' x| +
            not_isMisesKLRandom_of_plainK_lt_cntT s L c' x / L) :=
          Finset.sum_le_sum hcls
      _ = ∑ c' ∈ Finset.Icc (-(L : ℤ)) L,
          |not_isMisesKLRandom_of_plainK_lt_cntT s L c' x -
            not_isMisesKLRandom_of_plainK_lt_cntF s L c' x| +
          (∑ c' ∈ Finset.Icc (-(L : ℤ)) L,
            not_isMisesKLRandom_of_plainK_lt_cntT s L c' x) / L := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div]
      _ ≤ _ := by
          have : (∑ c' ∈ Finset.Icc (-(L : ℤ)) L,
            not_isMisesKLRandom_of_plainK_lt_cntT s L c' x) / L ≤ (x.length : ℝ) / L :=
            div_le_div_of_nonneg_right hsumT hLpos.le
          linarith
  rw [div_le_iff₀ (by positivity)]
  have : betGainOnOne s x - (x.length : ℝ) / L ≤
      (2 * L + 1 : ℝ) * |not_isMisesKLRandom_of_plainK_lt_cntT s L c x -
        not_isMisesKLRandom_of_plainK_lt_cntF s L c x| := by linarith
  calc betGainOnOne s x - (x.length : ℝ) / L ≤ _ := this
    _ = _ := by rw [mul_comm]; rfl

/-- The largest length of a word of `D`. -/
private def not_isMisesKLRandom_of_plainK_lt_scale (D : List BitString) : ℕ :=
  (D.map List.length).foldr max 0

/-- Natural-number weight `2 ^ (S - ⌈β |x|⌉)` of the word `x`. -/
private def not_isMisesKLRandom_of_plainK_lt_wt (β : ℚ) (S : ℕ) (x : BitString) : ℕ :=
  2 ^ (S - ⌈β * (x.length : ℚ)⌉₊)

/-- Total weight of the distinct words of `D` that extend `y`. -/
private def not_isMisesKLRandom_of_plainK_lt_W (β : ℚ) (D : List BitString) (y : BitString) :
    ℕ :=
  ((D.dedup.filter (fun x => decide (y <+: x))).map
    (fun x => not_isMisesKLRandom_of_plainK_lt_wt β
                (not_isMisesKLRandom_of_plainK_lt_scale D) x)).sum

/-- The bias of the weight of the `1`-child over the `0`-child of `y`, in `[-1, 1]`. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_bias (β : ℚ) (D : List BitString)
    (y : BitString) : ℝ :=
  if not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) +
      not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) = 0 then 0
  else ((not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) : ℝ) -
      (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) : ℝ)) /
    ((not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) : ℝ) +
      (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) : ℝ))

/-- Every word of `D` is at most as long as the scale of `D`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_le_scale (D : List BitString) (x : BitString)
    (hx : x ∈ D) : x.length ≤ not_isMisesKLRandom_of_plainK_lt_scale D := by
  induction D with
  | nil => simp at hx
  | cons a t ih =>
    unfold not_isMisesKLRandom_of_plainK_lt_scale at ih ⊢
    rcases List.mem_cons.mp hx with rfl | h
    · simp
    · have := ih h
      simp only [List.map_cons, List.foldr_cons]
      exact le_trans this (le_max_right _ _)

/-- The total weight is a finite sum over the distinct words of `D`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_W_eq (β : ℚ) (D : List BitString)
    (y : BitString) :
    not_isMisesKLRandom_of_plainK_lt_W β D y =
      ∑ x ∈ D.toFinset, if y <+: x then
        not_isMisesKLRandom_of_plainK_lt_wt β
          (not_isMisesKLRandom_of_plainK_lt_scale D) x else 0 := by
  unfold not_isMisesKLRandom_of_plainK_lt_W
  have h1 : ∀ l : List BitString,
      ((l.filter (fun x => decide (y <+: x))).map
        (fun x => not_isMisesKLRandom_of_plainK_lt_wt β
          (not_isMisesKLRandom_of_plainK_lt_scale D) x)).sum =
      (l.map (fun x => if y <+: x then
        not_isMisesKLRandom_of_plainK_lt_wt β
          (not_isMisesKLRandom_of_plainK_lt_scale D) x else 0)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      by_cases h : y <+: a
      · simp [h, ih]
      · simp [h, ih]
  rw [h1, ← List.sum_toFinset _ (List.nodup_dedup D), List.toFinset_dedup]

/-- The weights of the two children of `y` add up to at most the weight of `y`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_W_children_le (β : ℚ) (D : List BitString)
    (y : BitString) :
    not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) +
      not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) ≤
        not_isMisesKLRandom_of_plainK_lt_W β D y := by
  rw [not_isMisesKLRandom_of_plainK_lt_W_eq, not_isMisesKLRandom_of_plainK_lt_W_eq,
    not_isMisesKLRandom_of_plainK_lt_W_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases h0 : y ++ [false] <+: x
  · have hy : y <+: x := (List.prefix_append y [false]).trans h0
    have h1 : ¬ (y ++ [true] <+: x) := by
      intro h1
      have hle := List.prefix_of_prefix_length_le h0 h1 (by simp)
      have heq := hle.eq_of_length (by simp)
      simp at heq
    simp [h0, hy, h1]
  · by_cases h1 : y ++ [true] <+: x
    · have hy : y <+: x := (List.prefix_append y [true]).trans h1
      simp [h0, h1, hy]
    · simp [h0, h1]

/-- A word of `D` extending `y` contributes its weight to `W y`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_wt_le_W (β : ℚ) (D : List BitString)
    (y x : BitString) (hx : x ∈ D) (hy : y <+: x) :
    not_isMisesKLRandom_of_plainK_lt_wt β (not_isMisesKLRandom_of_plainK_lt_scale D) x ≤
      not_isMisesKLRandom_of_plainK_lt_W β D y := by
  rw [not_isMisesKLRandom_of_plainK_lt_W_eq]
  calc not_isMisesKLRandom_of_plainK_lt_wt β
        (not_isMisesKLRandom_of_plainK_lt_scale D) x
      = (if y <+: x then not_isMisesKLRandom_of_plainK_lt_wt β
        (not_isMisesKLRandom_of_plainK_lt_scale D) x else 0) := by simp [hy]
    _ ≤ ∑ z ∈ D.toFinset, if y <+: z then not_isMisesKLRandom_of_plainK_lt_wt β
        (not_isMisesKLRandom_of_plainK_lt_scale D) z else 0 :=
      Finset.single_le_sum (f := fun z => if y <+: z then
        not_isMisesKLRandom_of_plainK_lt_wt β
          (not_isMisesKLRandom_of_plainK_lt_scale D) z else 0)
        (fun z _ => Nat.zero_le _) (List.mem_toFinset.mpr hx)

/-- The bias is a number in `[-1, 1]`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_bias_abs_le (β : ℚ) (D : List BitString)
    (y : BitString) : |not_isMisesKLRandom_of_plainK_lt_bias β D y| ≤ 1 := by
  unfold not_isMisesKLRandom_of_plainK_lt_bias
  split_ifs with h
  · simp
  · have h0 : (0 : ℝ) ≤ (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) : ℝ) :=
      Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) : ℝ) :=
      Nat.cast_nonneg _
    have hpos : (0 : ℝ) < (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) : ℝ) +
        (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) : ℝ) := by
      have hnat : 0 < not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) +
          not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) := Nat.pos_of_ne_zero h
      have hR : (0 : ℝ) < (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) : ℝ) +
          (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) : ℝ) := by
        exact_mod_cast hnat
      linarith
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Real bounds on the natural weights: `2^S 2^(-βn-1) ≤ wt ≤ 2^S 2^(-βn)`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_wt_bounds (β : ℚ) (hβ : 0 < β)
    (hβ1 : β < 1) (D : List BitString) (x : BitString) (hx : x ∈ D) :
    (2 : ℝ) ^ (not_isMisesKLRandom_of_plainK_lt_scale D) *
        (2 : ℝ) ^ (-((β : ℝ) * x.length) - 1) ≤
      (not_isMisesKLRandom_of_plainK_lt_wt β
        (not_isMisesKLRandom_of_plainK_lt_scale D) x : ℝ) ∧
    (not_isMisesKLRandom_of_plainK_lt_wt β
        (not_isMisesKLRandom_of_plainK_lt_scale D) x : ℝ) ≤
      (2 : ℝ) ^ (not_isMisesKLRandom_of_plainK_lt_scale D) *
        (2 : ℝ) ^ (-(β : ℝ) * x.length) := by
  have hlen := not_isMisesKLRandom_of_plainK_lt_le_scale D x hx
  have hcle : ⌈β * (x.length : ℚ)⌉₊ ≤ x.length := by
    apply Nat.ceil_le.mpr
    have : β * (x.length : ℚ) ≤ 1 * (x.length : ℚ) :=
      mul_le_mul_of_nonneg_right hβ1.le (Nat.cast_nonneg _)
    simpa using this
  have h1 : (β : ℝ) * x.length ≤ (⌈β * (x.length : ℚ)⌉₊ : ℝ) := by
    have := Nat.le_ceil (β * (x.length : ℚ))
    exact_mod_cast this
  have h2 : (⌈β * (x.length : ℚ)⌉₊ : ℝ) < (β : ℝ) * x.length + 1 := by
    have := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ β * (x.length : ℚ) by positivity)
    exact_mod_cast this
  unfold not_isMisesKLRandom_of_plainK_lt_wt
  generalize not_isMisesKLRandom_of_plainK_lt_scale D = S at hlen ⊢
  generalize ⌈β * (x.length : ℚ)⌉₊ = c at hcle h1 h2 ⊢
  have hcS : c ≤ S := hcle.trans hlen
  have hwt : (((2 ^ (S - c) : ℕ)) : ℝ) * 2 ^ c = 2 ^ S := by
    push_cast
    rw [← pow_add, Nat.sub_add_cancel hcS]
  have hwt0 : (0 : ℝ) ≤ (((2 ^ (S - c) : ℕ)) : ℝ) := Nat.cast_nonneg _
  generalize hT : (β : ℝ) * x.length = t at h1 h2 ⊢
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hneg : (-(β : ℝ) * x.length) = -t := by rw [← hT]; ring
  have hexp1 : (2 : ℝ) ^ (-t - 1) = ((2 : ℝ) ^ t * 2)⁻¹ := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_one]
    field_simp
  have hexp0 : (2 : ℝ) ^ (-t) = ((2 : ℝ) ^ t)⁻¹ := Real.rpow_neg (by norm_num) t
  have hc_le : (2 : ℝ) ^ t ≤ 2 ^ c := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have hc_lt : (2 : ℝ) ^ c < (2 : ℝ) ^ t * 2 := by
    have h3 : (2 : ℝ) ^ (c : ℝ) < 2 ^ (t + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2
    rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_natCast] at h3
    exact h3
  constructor
  · rw [hexp1, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    calc (2 : ℝ) ^ S = (((2 ^ (S - c) : ℕ)) : ℝ) * 2 ^ c := hwt.symm
      _ ≤ (((2 ^ (S - c) : ℕ)) : ℝ) * ((2 : ℝ) ^ t * 2) :=
        mul_le_mul_of_nonneg_left hc_lt.le hwt0
  · rw [hneg, hexp0, ← div_eq_mul_inv, le_div_iff₀ h2t]
    calc (((2 ^ (S - c) : ℕ)) : ℝ) * (2 : ℝ) ^ t ≤ (((2 ^ (S - c) : ℕ)) : ℝ) * 2 ^ c :=
        mul_le_mul_of_nonneg_left hc_le hwt0
      _ = 2 ^ S := hwt

/-- The total weight is at most `2 ^ S`, by the Kraft-type hypothesis. -/
private lemma not_isMisesKLRandom_of_plainK_lt_W_nil_le (β : ℚ) (hβ : 0 < β)
    (hβ1 : β < 1) (D : List BitString)
    (hD : ∑ x ∈ D.toFinset, (2 : ℝ) ^ (-(β : ℝ) * x.length) ≤ 1) :
    (not_isMisesKLRandom_of_plainK_lt_W β D [] : ℝ) ≤
      (2 : ℝ) ^ (not_isMisesKLRandom_of_plainK_lt_scale D) := by
  rw [not_isMisesKLRandom_of_plainK_lt_W_eq, Nat.cast_sum]
  calc ∑ x ∈ D.toFinset, ((if ([] : BitString) <+: x then
          not_isMisesKLRandom_of_plainK_lt_wt β
            (not_isMisesKLRandom_of_plainK_lt_scale D) x else 0 : ℕ) : ℝ)
      ≤ ∑ x ∈ D.toFinset, (2 : ℝ) ^ (not_isMisesKLRandom_of_plainK_lt_scale D) *
          (2 : ℝ) ^ (-(β : ℝ) * x.length) := by
        apply Finset.sum_le_sum
        intro x hx
        have hnil : ([] : BitString) <+: x := List.nil_prefix
        simp only [hnil, ite_true]
        exact (not_isMisesKLRandom_of_plainK_lt_wt_bounds β hβ hβ1 D x
          (List.mem_toFinset.mp hx)).2
    _ = (2 : ℝ) ^ (not_isMisesKLRandom_of_plainK_lt_scale D) *
          ∑ x ∈ D.toFinset, (2 : ℝ) ^ (-(β : ℝ) * x.length) := by rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (not_isMisesKLRandom_of_plainK_lt_scale D) * 1 := by
        apply mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (2 : ℝ) ^ (not_isMisesKLRandom_of_plainK_lt_scale D) := mul_one _

/-- Numerical identities for one position. -/
private lemma not_isMisesKLRandom_of_plainK_lt_num_aux (a0 a1 : ℝ) (b : Bool)
    (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (hb : 0 < (if b then a1 else a0)) :
    0 < a0 + a1 ∧ 0 < (if b then a1 else a0) / (a0 + a1) ∧
      (if b then a1 else a0) / (a0 + a1) ≤ 1 ∧
      (a1 - a0) / (a1 + a0) * (if b then (1 : ℝ) else -1) =
        2 * ((if b then a1 else a0) / (a0 + a1)) - 1 := by
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hb ⊢
    have hs : 0 < a0 + a1 := by linarith
    have hs' : 0 < a1 + a0 := by linarith
    refine ⟨hs, div_pos hb hs, (div_le_one hs).mpr (by linarith), ?_⟩
    field_simp
    ring
  · simp only [ite_true] at hb ⊢
    have hs : 0 < a0 + a1 := by linarith
    have hs' : 0 < a1 + a0 := by linarith
    refine ⟨hs, div_pos hb hs, (div_le_one hs).mpr (by linarith), ?_⟩
    field_simp
    ring

/-- **Potential lemma** (step 7): the bias strategy of the weight tree of `D` gains a positive
proportion of the length on every word of `D`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_potential_aux (β : ℚ) (hβ : 0 < β)
    (hβ1 : β < 1) (D : List BitString)
    (hD : ∑ x ∈ D.toFinset, (2 : ℝ) ^ (-(β : ℝ) * x.length) ≤ 1)
    (x : BitString) (hx : x ∈ D)
    (amgm : ∀ (β : ℝ), 0 < β → β < 1 →
      ∀ (n : ℕ) (u : Fin n → ℝ), (∀ i, 0 < u i) →
        (2 : ℝ) ^ (-(β * n) - 1) ≤ ∏ i, u i →
        ((1 - β) / 2) * n - 3 / 2 ≤ ∑ i, (2 * u i - 1)) :
    ((1 - (β : ℝ)) / 2) * x.length - 3 / 2 ≤
      betGainOnOne (not_isMisesKLRandom_of_plainK_lt_bias β D) x := by
  classical
  have hxpos : 0 < not_isMisesKLRandom_of_plainK_lt_wt β
      (not_isMisesKLRandom_of_plainK_lt_scale D) x := by
    unfold not_isMisesKLRandom_of_plainK_lt_wt
    positivity
  have hWb_eq : ∀ (y : BitString) (b : Bool),
      (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [b]) : ℝ) =
        if b then (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) : ℝ)
        else (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) : ℝ) := by
    intro y b
    cases b <;> simp
  obtain ⟨u', hu'⟩ : ∃ u' : ℕ → ℝ, ∀ (i : ℕ) (h : i < x.length), u' i =
      (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [x[i]]) : ℝ) /
        ((not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [false]) : ℝ) +
          (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [true]) : ℝ)) :=
    ⟨fun i => if h : i < x.length then
      (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [x[i]]) : ℝ) /
        ((not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [false]) : ℝ) +
          (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [true]) : ℝ)) else 1,
      fun i h => by simp [h]⟩
  have hstep : ∀ (i : ℕ) (h : i < x.length),
      0 < u' i ∧ u' i ≤ 1 ∧
      (not_isMisesKLRandom_of_plainK_lt_W β D (x.take (i + 1)) : ℝ) ≤
        u' i * (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i) : ℝ) ∧
      not_isMisesKLRandom_of_plainK_lt_bias β D (x.take i) *
          (if x[i] then (1 : ℝ) else -1) = 2 * u' i - 1 := by
    intro i h
    have hxt : x.take (i + 1) = x.take i ++ [x[i]] := List.take_succ_eq_append_getElem h
    have hpre : x.take i ++ [x[i]] <+: x := by
      rw [← hxt]
      exact List.take_prefix _ _
    have hWbpos : 0 < not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [x[i]]) :=
      lt_of_lt_of_le hxpos
        (not_isMisesKLRandom_of_plainK_lt_wt_le_W β D _ x hx hpre)
    have hWbpos' : (0 : ℝ) < (not_isMisesKLRandom_of_plainK_lt_W β D
        (x.take i ++ [x[i]]) : ℝ) := by exact_mod_cast hWbpos
    have hnum := not_isMisesKLRandom_of_plainK_lt_num_aux
      (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [false]) : ℝ)
      (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [true]) : ℝ) x[i]
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by rw [← hWb_eq]; exact hWbpos')
    obtain ⟨hs, hup, hu1, hbias⟩ := hnum
    have hu'i : u' i = (if x[i] then
        (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [true]) : ℝ)
        else (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [false]) : ℝ)) /
        ((not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [false]) : ℝ) +
          (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [true]) : ℝ)) := by
      rw [hu' i h, hWb_eq]
    rw [← hu'i] at hup hu1 hbias
    have hW_children : (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [false]) : ℝ) +
        (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [true]) : ℝ) ≤
        (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i) : ℝ) := by
      exact_mod_cast not_isMisesKLRandom_of_plainK_lt_W_children_le β D (x.take i)
    have hWb_real : (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [x[i]]) : ℝ) =
        u' i * ((not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [false]) : ℝ) +
          (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [true]) : ℝ)) := by
      rw [hu' i h]
      field_simp
    refine ⟨hup, hu1, ?_, ?_⟩
    · rw [hxt, hWb_real]
      exact mul_le_mul_of_nonneg_left hW_children hup.le
    · have hne : ¬ (not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [false]) +
          not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [true]) = 0) := by
        intro hzero
        have : ((not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [false]) +
          not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [true]) : ℕ) : ℝ) = 0 := by
          rw [hzero]; simp
        push_cast at this
        linarith
      unfold not_isMisesKLRandom_of_plainK_lt_bias
      simp only [hne, ite_false]
      exact hbias
  have hchain : ∀ k : ℕ, k ≤ x.length →
      (not_isMisesKLRandom_of_plainK_lt_W β D (x.take k) : ℝ) ≤
        (not_isMisesKLRandom_of_plainK_lt_W β D [] : ℝ) *
          ∏ i ∈ Finset.range k, u' i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k < x.length := hk
      obtain ⟨hup, _, hle, _⟩ := hstep k hk'
      calc (not_isMisesKLRandom_of_plainK_lt_W β D (x.take (k + 1)) : ℝ)
          ≤ u' k * (not_isMisesKLRandom_of_plainK_lt_W β D (x.take k) : ℝ) := hle
        _ ≤ u' k * ((not_isMisesKLRandom_of_plainK_lt_W β D [] : ℝ) *
              ∏ i ∈ Finset.range k, u' i) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hup.le
        _ = (not_isMisesKLRandom_of_plainK_lt_W β D [] : ℝ) *
              ∏ i ∈ Finset.range (k + 1), u' i := by
            rw [Finset.prod_range_succ]
            ring
  have hprodnonneg : 0 ≤ ∏ i ∈ Finset.range x.length, u' i :=
    Finset.prod_nonneg (fun i hi => (hstep i (Finset.mem_range.mp hi)).1.le)
  have hWx : (not_isMisesKLRandom_of_plainK_lt_wt β
      (not_isMisesKLRandom_of_plainK_lt_scale D) x : ℝ) ≤
      (not_isMisesKLRandom_of_plainK_lt_W β D [] : ℝ) *
        ∏ i ∈ Finset.range x.length, u' i := by
    have h1 := hchain x.length le_rfl
    rw [List.take_length] at h1
    have h2 : (not_isMisesKLRandom_of_plainK_lt_wt β
        (not_isMisesKLRandom_of_plainK_lt_scale D) x : ℝ) ≤
        (not_isMisesKLRandom_of_plainK_lt_W β D x : ℝ) := by
      exact_mod_cast not_isMisesKLRandom_of_plainK_lt_wt_le_W β D x x hx List.prefix_rfl
    exact h2.trans h1
  have hbounds := not_isMisesKLRandom_of_plainK_lt_wt_bounds β hβ hβ1 D x hx
  have hWnil := not_isMisesKLRandom_of_plainK_lt_W_nil_le β hβ hβ1 D hD
  have hprod : (2 : ℝ) ^ (-((β : ℝ) * x.length) - 1) ≤ ∏ i ∈ Finset.range x.length, u' i := by
    have h2S : (0 : ℝ) < 2 ^ (not_isMisesKLRandom_of_plainK_lt_scale D) := by positivity
    have hmul : (2 : ℝ) ^ (not_isMisesKLRandom_of_plainK_lt_scale D) *
        (2 : ℝ) ^ (-((β : ℝ) * x.length) - 1) ≤
        (2 : ℝ) ^ (not_isMisesKLRandom_of_plainK_lt_scale D) *
          ∏ i ∈ Finset.range x.length, u' i := by
      calc _ ≤ (not_isMisesKLRandom_of_plainK_lt_wt β
            (not_isMisesKLRandom_of_plainK_lt_scale D) x : ℝ) := hbounds.1
        _ ≤ (not_isMisesKLRandom_of_plainK_lt_W β D [] : ℝ) *
              ∏ i ∈ Finset.range x.length, u' i := hWx
        _ ≤ (2 : ℝ) ^ (not_isMisesKLRandom_of_plainK_lt_scale D) *
              ∏ i ∈ Finset.range x.length, u' i :=
            mul_le_mul_of_nonneg_right hWnil hprodnonneg
    exact le_of_mul_le_mul_left hmul h2S
  have hu0 : ∀ i : Fin x.length, 0 < u' i := fun i => (hstep i i.2).1
  have hprodFin : (2 : ℝ) ^ (-((β : ℝ) * x.length) - 1) ≤ ∏ i : Fin x.length, u' i := by
    rw [Fin.prod_univ_eq_prod_range (fun i => u' i) x.length]
    exact hprod
  have hamgm := amgm (β : ℝ) (by exact_mod_cast hβ) (by exact_mod_cast hβ1) x.length
    (fun i : Fin x.length => u' i) hu0 hprodFin
  calc ((1 - (β : ℝ)) / 2) * x.length - 3 / 2 ≤ ∑ i : Fin x.length, (2 * u' i - 1) := hamgm
    _ = betGainOnOne (not_isMisesKLRandom_of_plainK_lt_bias β D) x := by
      unfold betGainOnOne
      apply Finset.sum_congr rfl
      intro i _
      exact ((hstep i i.2).2.2.2).symm



/-- **Potential lemma** (step 7).  For every word `x` of a list `D` with Kraft sum at most one,
the bias strategy of the weight tree of `D` gains at least `((1 - β)/2) |x| - 3/2` on `x`
(in the bounded-bet game of `betGainOnOne`).  It combines the potential argument
(`..._potential_aux`) with the AM-GM step `..._amgm`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_potential (β : ℚ) (hβ : 0 < β) (hβ1 : β < 1)
    (D : List BitString) (hD : ∑ x ∈ D.toFinset, (2 : ℝ) ^ (-(β : ℝ) * x.length) ≤ 1)
    (x : BitString) (hx : x ∈ D) :
    ((1 - (β : ℝ)) / 2) * x.length - 3 / 2 ≤
      betGainOnOne (not_isMisesKLRandom_of_plainK_lt_bias β D) x :=
  not_isMisesKLRandom_of_plainK_lt_potential_aux β hβ hβ1 D hD x hx
    (fun β hβ0 hβ1 n u hu0 hprod =>
      not_isMisesKLRandom_of_plainK_lt_amgm β hβ0 hβ1 n u hu0 hprod)


/-! ### Computability of the weights -/

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_scale :
    Primrec not_isMisesKLRandom_of_plainK_lt_scale := by
  have h : Primrec (fun D : List BitString => D.foldr (fun x s => max x.length s) 0) :=
    Primrec.list_foldr (f := fun D : List BitString => D) (g := fun _ => (0 : ℕ))
      (h := fun (_ : List BitString) (p : BitString × ℕ) => max p.1.length p.2)
      Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  refine h.of_eq fun D => ?_
  unfold not_isMisesKLRandom_of_plainK_lt_scale
  rw [List.foldr_map]

/-- Closed form of the ceiling of a rational multiple. -/
private lemma not_isMisesKLRandom_of_plainK_lt_ceil_eq (a b n : ℕ) (hb : 0 < b) :
    ⌈((a : ℚ) / b) * (n : ℚ)⌉₊ = (a * n + b - 1) / b := by
  have hq : ((a : ℚ) / b) * (n : ℚ) = ((a * n : ℕ) : ℚ) / (b : ℚ) := by push_cast; ring
  rw [hq]
  generalize a * n = m
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hbq]
    have h1 := Nat.div_add_mod (m + b - 1) b
    have h2 := Nat.mod_lt (m + b - 1) hb
    rw [Nat.mul_comm] at h1
    have h3 : m ≤ (m + b - 1) / b * b := by omega
    exact_mod_cast h3
  · have hc : (m : ℚ) / b ≤ (⌈(m : ℚ) / b⌉₊ : ℚ) := Nat.le_ceil _
    rw [div_le_iff₀ hbq] at hc
    have hc' : m ≤ ⌈(m : ℚ) / b⌉₊ * b := by exact_mod_cast hc
    have : (m + b - 1) / b < ⌈(m : ℚ) / b⌉₊ + 1 := by
      rw [Nat.div_lt_iff_lt_mul hb, Nat.add_mul, Nat.one_mul]
      omega
    omega

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_ceil (β : ℚ) (hβ : 0 ≤ β) :
    Primrec (fun n : ℕ => ⌈β * (n : ℚ)⌉₊) := by
  have hden : 0 < β.den := β.den_pos
  have hnum : (β.num.toNat : ℤ) = β.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hβ)
  have hβ' : β = ((β.num.toNat : ℕ) : ℚ) / (β.den : ℚ) := by
    have h1 : ((β.num.toNat : ℕ) : ℚ) = (β.num : ℚ) := by
      exact_mod_cast hnum
    rw [h1]
    exact (Rat.num_div_den β).symm
  have h : Primrec (fun n : ℕ => (β.num.toNat * n + β.den - 1) / β.den) :=
    Primrec.nat_div.comp
      (Primrec.nat_sub.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const _) Primrec.id)
          (Primrec.const _)) (Primrec.const 1))
      (Primrec.const _)
  refine h.of_eq fun n => ?_
  have := not_isMisesKLRandom_of_plainK_lt_ceil_eq β.num.toNat β.den n hden
  rw [← this]
  congr 1
  rw [← hβ']

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_wt (β : ℚ) (hβ : 0 ≤ β) :
    Primrec₂ (fun (S : ℕ) (x : BitString) =>
      not_isMisesKLRandom_of_plainK_lt_wt β S x) := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  unfold not_isMisesKLRandom_of_plainK_lt_wt
  exact hpow.comp (Primrec.const 2)
    (Primrec.nat_sub.comp Primrec.fst
      ((not_isMisesKLRandom_of_plainK_lt_primrec_ceil β hβ).comp
        (Primrec.list_length.comp Primrec.snd)))

private lemma not_isMisesKLRandom_of_plainK_lt_dedup_eq (l : List BitString) :
    l.dedup = l.foldr (fun x IH => if x ∈ IH then IH else x :: IH) [] := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.foldr_cons, ← ih]
    by_cases hx : x ∈ l
    · rw [List.dedup_cons_of_mem hx, ite_eq_left (List.mem_dedup.mpr hx)]
    · rw [List.dedup_cons_of_notMem hx, ite_eq_right (fun h => hx (List.mem_dedup.mp h))]

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_mem :
    Primrec (fun p : BitString × List BitString => decide (p.1 ∈ p.2)) := by
  have h : Primrec (fun p : BitString × List BitString =>
      decide (@List.idxOf BitString instBEqOfDecidableEq p.1 p.2 < p.2.length)) :=
    (Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.fst Primrec.snd)
      (Primrec.list_length.comp Primrec.snd)).decide
  refine h.of_eq fun p => ?_
  exact decide_eq_decide.mpr
    (@List.idxOf_lt_length_iff BitString instBEqOfDecidableEq inferInstance _ _)

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_dedup :
    Primrec (fun l : List BitString => l.dedup) := by
  have h : Primrec (fun l : List BitString =>
      l.foldr (fun x IH => if x ∈ IH then IH else x :: IH) []) :=
    Primrec.list_foldr (f := fun l : List BitString => l) (g := fun _ => ([] : List BitString))
      (h := fun (_ : List BitString) (p : BitString × List BitString) =>
        if p.1 ∈ p.2 then p.2 else p.1 :: p.2)
      Primrec.id (Primrec.const [])
      (Primrec.cond (not_isMisesKLRandom_of_plainK_lt_primrec_mem.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
        |>.of_eq fun p => by simp)
  exact h.of_eq fun l => (not_isMisesKLRandom_of_plainK_lt_dedup_eq l).symm

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_prefix :
    Primrec (fun p : BitString × BitString => decide (p.1 <+: p.2)) := by
  have h : Primrec (fun p : BitString × BitString =>
      decide (p.1 = p.2.take p.1.length)) :=
    (Primrec.eq.comp Primrec.fst
      (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)).decide
  refine h.of_eq fun p => ?_
  exact decide_eq_decide.mpr List.prefix_iff_eq_take.symm

private lemma not_isMisesKLRandom_of_plainK_lt_W_eq_foldr (β : ℚ) (D : List BitString)
    (y : BitString) :
    not_isMisesKLRandom_of_plainK_lt_W β D y =
      D.dedup.foldr (fun x acc => cond (decide (y <+: x))
        (not_isMisesKLRandom_of_plainK_lt_wt β
          (not_isMisesKLRandom_of_plainK_lt_scale D) x + acc) acc) 0 := by
  unfold not_isMisesKLRandom_of_plainK_lt_W
  generalize D.dedup = l
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.filter_cons, List.foldr_cons, ← ih]
    by_cases h : y <+: x
    · simp [h]
    · simp [h]

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_W (β : ℚ) (hβ : 0 ≤ β) :
    Primrec (fun q : List BitString × BitString =>
      not_isMisesKLRandom_of_plainK_lt_W β q.1 q.2) := by
  have hwt := not_isMisesKLRandom_of_plainK_lt_primrec_wt β hβ
  have hsc := not_isMisesKLRandom_of_plainK_lt_primrec_scale
  have hpre := not_isMisesKLRandom_of_plainK_lt_primrec_prefix
  have hdd := not_isMisesKLRandom_of_plainK_lt_primrec_dedup
  have h : Primrec (fun q : List BitString × BitString =>
      q.1.dedup.foldr (fun x acc => cond (decide (q.2 <+: x))
        (not_isMisesKLRandom_of_plainK_lt_wt β
          (not_isMisesKLRandom_of_plainK_lt_scale q.1) x + acc) acc) 0) :=
    Primrec.list_foldr (f := fun q : List BitString × BitString => q.1.dedup)
      (g := fun _ => (0 : ℕ))
      (h := fun (q : List BitString × BitString) (p : BitString × ℕ) =>
        cond (decide (q.2 <+: p.1))
          (not_isMisesKLRandom_of_plainK_lt_wt β
            (not_isMisesKLRandom_of_plainK_lt_scale q.1) p.1 + p.2) p.2)
      (hdd.comp Primrec.fst) (Primrec.const 0)
      (Primrec.cond
        (hpre.comp (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
        (Primrec.nat_add.comp
          (hwt.comp (hsc.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  exact h.of_eq fun q => (not_isMisesKLRandom_of_plainK_lt_W_eq_foldr β q.1 q.2).symm

/-- The selection rule number `j`: for `j ≤ 2L` it selects the strings `y` whose extension
weights `W₀ = W(y0)`, `W₁ = W(y1)` satisfy `⌊2 L W₁ / (W₀ + W₁)⌋ = j`; the last rule
(`j = 2L + 1`) selects only the empty string, i.e. the first bit. -/
private def not_isMisesKLRandom_of_plainK_lt_rule (β : ℚ) (L : ℕ) (D : List BitString)
    (j : ℕ) (y : BitString) : Bool :=
  if j ≤ 2 * L then
    (!decide (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) +
        not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) = 0)) &&
      decide (2 * L * not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) /
        (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) +
          not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true])) = j)
  else decide (y = [])

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_rule (β : ℚ) (hβ : 0 ≤ β)
    (L : ℕ) :
    Primrec (fun p : (List BitString × ℕ) × BitString =>
      not_isMisesKLRandom_of_plainK_lt_rule β L p.1.1 p.1.2 p.2) := by
  have hW := not_isMisesKLRandom_of_plainK_lt_primrec_W β hβ
  have hW0 : Primrec (fun p : (List BitString × ℕ) × BitString =>
      not_isMisesKLRandom_of_plainK_lt_W β p.1.1 (p.2 ++ [false])) :=
    hW.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.list_concat.comp Primrec.snd (Primrec.const false)))
  have hW1 : Primrec (fun p : (List BitString × ℕ) × BitString =>
      not_isMisesKLRandom_of_plainK_lt_W β p.1.1 (p.2 ++ [true])) :=
    hW.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.list_concat.comp Primrec.snd (Primrec.const true)))
  have hS := Primrec.nat_add.comp hW0 hW1
  have hcls : Primrec (fun p : (List BitString × ℕ) × BitString =>
      (!decide (not_isMisesKLRandom_of_plainK_lt_W β p.1.1 (p.2 ++ [false]) +
        not_isMisesKLRandom_of_plainK_lt_W β p.1.1 (p.2 ++ [true]) = 0)) &&
      decide (2 * L * not_isMisesKLRandom_of_plainK_lt_W β p.1.1 (p.2 ++ [true]) /
        (not_isMisesKLRandom_of_plainK_lt_W β p.1.1 (p.2 ++ [false]) +
          not_isMisesKLRandom_of_plainK_lt_W β p.1.1 (p.2 ++ [true])) = p.1.2)) :=
    Primrec.and.comp
      (Primrec.not.comp (Primrec.eq.comp hS (Primrec.const 0)).decide)
      (Primrec.eq.comp
        (Primrec.nat_div.comp
          (Primrec.nat_mul.comp (Primrec.const (2 * L)) hW1) hS)
        (Primrec.snd.comp Primrec.fst)).decide
  have hlast : Primrec (fun p : (List BitString × ℕ) × BitString => decide (p.2 = [])) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const [])).decide
  have hle : Primrec (fun p : (List BitString × ℕ) × BitString => decide (p.1.2 ≤ 2 * L)) :=
    (Primrec.nat_le.comp (Primrec.snd.comp Primrec.fst) (Primrec.const (2 * L))).decide
  have h := Primrec.cond hle hcls hlast
  refine h.of_eq fun p => ?_
  simp [not_isMisesKLRandom_of_plainK_lt_rule]

private lemma not_isMisesKLRandom_of_plainK_lt_computable_rule (β : ℚ) (hβ : 0 ≤ β)
    (L M : ℕ) :
    Computable (fun p : (List BitString × Fin M) × BitString =>
      not_isMisesKLRandom_of_plainK_lt_rule β L p.1.1 p.1.2.val p.2) := by
  have h := not_isMisesKLRandom_of_plainK_lt_primrec_rule β hβ L
  exact (h.comp (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
    (Primrec.fin_val.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)).to_comp

/-! ### The rule selects the classes of the bias -/

private lemma not_isMisesKLRandom_of_plainK_lt_le_sum_of_mem {l : List ℕ} {a : ℕ}
    (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h
      simp
      omega

private lemma not_isMisesKLRandom_of_plainK_lt_W_pos (β : ℚ) (D : List BitString)
    (x : BitString) (hx : x ∈ D) (z : BitString) (hz : z <+: x) :
    0 < not_isMisesKLRandom_of_plainK_lt_W β D z := by
  unfold not_isMisesKLRandom_of_plainK_lt_W
  have hmem : x ∈ D.dedup.filter (fun x => decide (z <+: x)) := by
    rw [List.mem_filter]
    exact ⟨List.mem_dedup.mpr hx, by simpa using hz⟩
  have hmem2 := List.mem_map_of_mem
    (f := fun x => not_isMisesKLRandom_of_plainK_lt_wt β
      (not_isMisesKLRandom_of_plainK_lt_scale D) x) hmem
  have hpos : 0 < not_isMisesKLRandom_of_plainK_lt_wt β
      (not_isMisesKLRandom_of_plainK_lt_scale D) x := by
    unfold not_isMisesKLRandom_of_plainK_lt_wt
    positivity
  exact lt_of_lt_of_le hpos (not_isMisesKLRandom_of_plainK_lt_le_sum_of_mem hmem2)

/-- Every proper prefix of a word of `D` has a child with positive weight. -/
private lemma not_isMisesKLRandom_of_plainK_lt_sum_ne_zero (β : ℚ) (D : List BitString)
    (x : BitString) (hx : x ∈ D) (i : ℕ) (hi : i < x.length) :
    not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [false]) +
      not_isMisesKLRandom_of_plainK_lt_W β D (x.take i ++ [true]) ≠ 0 := by
  have hpre : x.take i ++ [x[i]] <+: x := by
    rw [← List.take_succ_eq_append_getElem hi]
    exact List.take_prefix _ _
  have hpos := not_isMisesKLRandom_of_plainK_lt_W_pos β D x hx _ hpre
  by_cases hb : x[i] = true
  · rw [hb] at hpos
    omega
  · have hb' : x[i] = false := by simpa using hb
    rw [hb'] at hpos
    omega

/-- The floor of `L` times the bias is the class `⌊2 L W₁ / (W₀ + W₁)⌋ - L`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_floor_bias (β : ℚ) (L : ℕ)
    (D : List BitString) (y : BitString)
    (hS : not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) +
        not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) ≠ 0) :
    ⌊(L : ℝ) * not_isMisesKLRandom_of_plainK_lt_bias β D y⌋ =
      ((2 * L * not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) /
        (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) +
          not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true])) : ℕ) : ℤ) - L := by
  have hb : not_isMisesKLRandom_of_plainK_lt_bias β D y =
      ((not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) : ℝ) -
        (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) : ℝ)) /
      ((not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) : ℝ) +
        (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) : ℝ)) := by
    unfold not_isMisesKLRandom_of_plainK_lt_bias
    rw [ite_eq_right hS]
  rw [hb]
  generalize not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) = W0 at hS ⊢
  generalize not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) = W1 at hS ⊢
  have hSN : 0 < W0 + W1 := Nat.pos_of_ne_zero hS
  have hSpos : (0 : ℝ) < (W1 : ℝ) + W0 := by
    have : (0 : ℝ) < ((W0 + W1 : ℕ) : ℝ) := by exact_mod_cast hSN
    push_cast at this
    linarith
  have h1 : (L : ℝ) * (((W1 : ℝ) - W0) / ((W1 : ℝ) + W0)) =
      ((2 * L * W1 : ℕ) : ℝ) / ((W0 + W1 : ℕ) : ℝ) - (L : ℝ) := by
    have hne1 : (W1 : ℝ) + W0 ≠ 0 := hSpos.ne'
    have hne2 : (W0 : ℝ) + W1 ≠ 0 := by linarith
    push_cast
    field_simp
    ring
  rw [h1, Int.floor_sub_natCast]
  congr 1
  rw [Int.floor_eq_iff]
  have hq1 : 2 * L * W1 / (W0 + W1) * (W0 + W1) ≤ 2 * L * W1 := Nat.div_mul_le_self _ _
  have hq2 : 2 * L * W1 < 2 * L * W1 / (W0 + W1) * (W0 + W1) + (W0 + W1) :=
    Nat.lt_div_mul_add hSN
  constructor
  · rw [le_div_iff₀ (by exact_mod_cast hSN)]
    exact_mod_cast hq1
  · rw [div_lt_iff₀ (by exact_mod_cast hSN)]
    have : ((2 * L * W1 : ℕ) : ℝ) <
        (((2 * L * W1 / (W0 + W1) : ℕ) : ℝ) + 1) * ((W0 + W1 : ℕ) : ℝ) := by
      have h3 : 2 * L * W1 < (2 * L * W1 / (W0 + W1) + 1) * (W0 + W1) := by
        rw [Nat.add_mul, Nat.one_mul]
        exact hq2
      exact_mod_cast h3
    exact_mod_cast this

private lemma not_isMisesKLRandom_of_plainK_lt_rule_iff (β : ℚ) (L : ℕ)
    (D : List BitString) (j : ℕ) (hj : j ≤ 2 * L) (y : BitString)
    (hS : not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) +
        not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) ≠ 0) :
    not_isMisesKLRandom_of_plainK_lt_rule β L D j y = true ↔
      ⌊(L : ℝ) * not_isMisesKLRandom_of_plainK_lt_bias β D y⌋ = (j : ℤ) - L := by
  rw [not_isMisesKLRandom_of_plainK_lt_floor_bias β L D y hS]
  unfold not_isMisesKLRandom_of_plainK_lt_rule
  rw [ite_eq_left hj]
  generalize 2 * L * not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true]) /
    (not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [false]) +
      not_isMisesKLRandom_of_plainK_lt_W β D (y ++ [true])) = q
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h⟩
    rw [h]
  · intro h
    refine ⟨hS, ?_⟩
    omega

private lemma not_isMisesKLRandom_of_plainK_lt_selectedAux_congr (R R' : Set BitString) :
    ∀ (x pre : BitString), (∀ i < x.length, (pre ++ x.take i ∈ R ↔ pre ++ x.take i ∈ R')) →
      selectedAux R pre x = selectedAux R' pre x := by
  intro x
  induction x with
  | nil => intro pre _; rfl
  | cons b rest ih =>
    intro pre h
    have h0 : pre ∈ R ↔ pre ∈ R' := by simpa using h 0 (by simp)
    have h1 : selectedAux R (pre ++ [b]) rest = selectedAux R' (pre ++ [b]) rest := by
      apply ih
      intro i hi
      have := h (i + 1) (by simpa using hi)
      simpa [List.append_assoc] using this
    simp only [selectedAux]
    rw [h1]
    by_cases hp : pre ∈ R
    · rw [ite_eq_left hp, ite_eq_left (h0.mp hp)]
    · rw [ite_eq_right hp, ite_eq_right (fun hp' => hp (h0.mpr hp'))]

private lemma not_isMisesKLRandom_of_plainK_lt_selectedBits_congr (R R' : Set BitString)
    (x : BitString) (h : ∀ i < x.length, (x.take i ∈ R ↔ x.take i ∈ R')) :
    selectedBits R x = selectedBits R' x := by
  unfold selectedBits
  exact not_isMisesKLRandom_of_plainK_lt_selectedAux_congr R R' x [] (by simpa using h)

private lemma not_isMisesKLRandom_of_plainK_lt_selectedAux_empty (pre : BitString)
    (hpre : pre ≠ []) (rest : BitString) :
    selectedAux {y : BitString | y = []} pre rest = [] := by
  induction rest generalizing pre with
  | nil => rfl
  | cons c rest ih =>
    simp only [selectedAux]
    rw [ite_eq_right (by simpa using hpre)]
    simp only [List.nil_append]
    exact ih (pre ++ [c]) (by simp)

private lemma not_isMisesKLRandom_of_plainK_lt_selectedBits_first (b : Bool)
    (rest : BitString) :
    selectedBits {y : BitString | y = []} (b :: rest) = [b] := by
  unfold selectedBits
  have h := not_isMisesKLRandom_of_plainK_lt_selectedAux_empty [b] (by simp) rest
  simp only [selectedAux, List.nil_append]
  rw [ite_eq_left (show ([] : BitString) ∈ {y : BitString | y = []} from rfl), h]
  rfl

/-- Step 7 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
a finite Kraft-bounded list admits a uniformly computable fixed finite family of
monotone selection rules. On each listed word one of them has a discrepancy
proportional to that word's length. Both the number of rules and the positive
rational proportionality constant depend only on `β`, not on the list or its
maximum length. This is the finite martingale/selection argument of Proposition 35
and Remark 37 of Merkle--Miller--Nies--Reimann--Stephan. -/
lemma not_isMisesKLRandom_of_plainK_lt_finite_selection
    (β : ℚ) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ (M : ℕ) (ε : ℚ) (F : List BitString → Fin M → BitString → Bool),
      0 < M ∧ 0 < ε ∧ ε ≤ 1 ∧
      Computable (fun p : (List BitString × Fin M) × BitString => F p.1.1 p.1.2 p.2) ∧
      ∀ D : List BitString,
        (∑ x ∈ D.toFinset, (2 : ℝ) ^ (-(β : ℝ) * x.length)) ≤ 1 →
        ∀ x ∈ D, ∃ j : Fin M,
          (ε : ℝ) * x.length ≤
            |((selectedBits {y | F D j y = true} x).count true : ℝ) -
              (selectedBits {y | F D j y = true} x).count false| := by
  have hγ : (0 : ℚ) < 1 - β := by linarith
  have hγR : (0 : ℝ) < 1 - (β : ℝ) := by
    have : (β : ℝ) < 1 := by exact_mod_cast hβ1
    linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌈8 / (1 - β)⌉₊ := ⟨_, rfl⟩
  have hL8 : 8 / (1 - β) ≤ (L : ℚ) := by rw [hLdef]; exact Nat.le_ceil _
  have hL1 : (8 : ℚ) ≤ L := by
    have h8 : (8 : ℚ) ≤ 8 / (1 - β) := by
      rw [le_div_iff₀ hγ]; nlinarith
    linarith
  have hLpos : 0 < L := by
    have : (0 : ℚ) < L := by linarith
    exact_mod_cast this
  have hL8R : 8 / (1 - (β : ℝ)) ≤ (L : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hL8
    push_cast at this
    exact this
  have hLR : (8 : ℝ) ≤ L := by exact_mod_cast hL1
  refine ⟨2 * L + 2, (1 - β) / (8 * (2 * (L : ℚ) + 1)),
    fun D j y => not_isMisesKLRandom_of_plainK_lt_rule β L D j.val y,
    by omega, div_pos hγ (by positivity), ?_,
    not_isMisesKLRandom_of_plainK_lt_computable_rule β hβ.le L (2 * L + 2), ?_⟩
  · rw [div_le_one (by positivity)]
    have : (0 : ℚ) ≤ L := by positivity
    nlinarith
  · intro D hD x hx
    have hε : (((1 - β) / (8 * (2 * (L : ℚ) + 1)) : ℚ) : ℝ) =
        (1 - (β : ℝ)) / (8 * (2 * (L : ℝ) + 1)) := by push_cast; ring
    rw [hε]
    by_cases hn0 : x.length = 0
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [hn0]
      simp
    by_cases hbig : (6 : ℝ) / (1 - (β : ℝ)) ≤ x.length
    · -- the case of a long word: the potential bound and the discretization
      have hpot := not_isMisesKLRandom_of_plainK_lt_potential β hβ hβ1 D hD x hx
      obtain ⟨c, hcL, hcL', hdisc⟩ := not_isMisesKLRandom_of_plainK_lt_discretize
        (not_isMisesKLRandom_of_plainK_lt_bias β D)
        (not_isMisesKLRandom_of_plainK_lt_bias_abs_le β D) L hLpos x
      have hjc : (((c + L).toNat : ℕ) : ℤ) = c + L := Int.toNat_of_nonneg (by omega)
      have hjle : (c + L).toNat ≤ 2 * L := by omega
      refine ⟨⟨(c + L).toNat, by omega⟩, ?_⟩
      have hsel : selectedBits {y | not_isMisesKLRandom_of_plainK_lt_rule β L D
            (c + L).toNat y = true} x =
          selectedBits {y | ⌊(L : ℝ) * not_isMisesKLRandom_of_plainK_lt_bias β D y⌋ = c}
            x := by
        apply not_isMisesKLRandom_of_plainK_lt_selectedBits_congr
        intro i hi
        have hS := not_isMisesKLRandom_of_plainK_lt_sum_ne_zero β D x hx i hi
        simp only [Set.mem_ofPred_eq]
        rw [not_isMisesKLRandom_of_plainK_lt_rule_iff β L D _ hjle _ hS, hjc]
        constructor <;> intro h <;> omega
      change _ ≤ |((selectedBits {y | not_isMisesKLRandom_of_plainK_lt_rule β L D
            (c + L).toNat y = true} x).count true : ℝ) - _|
      rw [hsel]
      refine le_trans ?_ hdisc
      -- the arithmetic
      have hn6 : 6 ≤ (1 - (β : ℝ)) * x.length := by
        rwa [div_le_iff₀ hγR, mul_comm] at hbig
      have hnL : (x.length : ℝ) / L ≤ (1 - (β : ℝ)) * x.length / 8 := by
        have hLpos' : (0 : ℝ) < L := by exact_mod_cast hLpos
        have h8 : 8 ≤ (1 - (β : ℝ)) * L := by
          rwa [div_le_iff₀ hγR, mul_comm] at hL8R
        rw [div_le_div_iff₀ hLpos' (by norm_num)]
        have hn0' : (0 : ℝ) ≤ x.length := by positivity
        nlinarith
      have hG : (1 - (β : ℝ)) * x.length / 4 ≤
          betGainOnOne (not_isMisesKLRandom_of_plainK_lt_bias β D) x := by
        nlinarith
      have hnum : (1 - (β : ℝ)) * x.length / 8 ≤
          betGainOnOne (not_isMisesKLRandom_of_plainK_lt_bias β D) x -
            (x.length : ℝ) / L := by linarith
      have hden : (0 : ℝ) < 2 * (L : ℝ) + 1 := by positivity
      calc (1 - (β : ℝ)) / (8 * (2 * (L : ℝ) + 1)) * x.length
          = ((1 - (β : ℝ)) * x.length / 8) / (2 * (L : ℝ) + 1) := by
            field_simp
        _ ≤ _ := by
            apply div_le_div_of_nonneg_right hnum hden.le
    · -- the case of a short word: only the first bit is selected
      have hbig := not_le.mp hbig
      obtain ⟨b, rest, rfl⟩ : ∃ b rest, x = b :: rest := by
        cases x with
        | nil => simp at hn0
        | cons b rest => exact ⟨b, rest, rfl⟩
      refine ⟨⟨2 * L + 1, by omega⟩, ?_⟩
      have hnot : ¬ (2 * L + 1 ≤ 2 * L) := by omega
      have hset : {y : BitString | not_isMisesKLRandom_of_plainK_lt_rule β L D
          (2 * L + 1) y = true} = {y : BitString | y = []} := by
        ext y
        simp [not_isMisesKLRandom_of_plainK_lt_rule, hnot]
      change _ ≤ |((selectedBits {y | not_isMisesKLRandom_of_plainK_lt_rule β L D
            (2 * L + 1) y = true} (b :: rest)).count true : ℝ) - _|
      rw [hset, not_isMisesKLRandom_of_plainK_lt_selectedBits_first]
      have hε1 : (1 - (β : ℝ)) / (8 * (2 * (L : ℝ) + 1)) * ((b :: rest).length : ℝ) ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one (by positivity)]
        have hlt : (1 - (β : ℝ)) * ((b :: rest).length : ℝ) < 6 := by
          rwa [lt_div_iff₀ hγR, mul_comm] at hbig
        nlinarith
      cases b <;> simpa using hε1

end Kolmogorov.FrequencyGames
