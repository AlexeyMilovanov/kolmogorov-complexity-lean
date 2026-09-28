import Mathlib.Analysis.SpecialFunctions.Pow.Real
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveSLLN
import KolmogorovMathlib.MonotoneComplexity.MeasureRepresentation
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity

/-!
# Dyadic cells of the unit interval

The closed dyadic interval `binaryClosedInterval p = [0.p, 0.p + 2 ^ (-|p|)]` attached to a bit
string, together with what is needed to place such cells inside prescribed open intervals. The
endpoint `0.p` is identified with the left endpoint of the uniform tree measure
(`treeLeftEnd_lengthMeasure_eq_div`), cells are nested along the prefix order and contained in
`[0, 1]`, and the main results `exists_binaryClosedInterval_subset_Ioo` and its power form
`exists_binaryClosedInterval_subset_Ioo_pow` produce a cell of controlled length inside any open
subinterval of `[0, 1]`. Used by the arithmetic-coding and measure-representation arguments.
-/

open Kolmogorov Set

/-- The mass that `lengthMeasure` assigns to `p`, as a real number, is `2^{-|p|}`. -/
lemma lengthMeasure_toReal (p : BitString) :
    (lengthMeasure p).toReal = (2 : ℝ)⁻¹ ^ p.length := by
  unfold lengthMeasure
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv]
  rfl


/-- Every `d` in `(0, 1]` admits a power of two lying in `[d/4, d/2)`. -/
lemma exists_inv_two_pow_mem_Ico_quarter_half {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ n : ℕ, d / 4 ≤ (2 : ℝ)⁻¹ ^ n ∧ (2 : ℝ)⁻¹ ^ n < d / 2 := by
  have H : ∃ n : ℕ, (2 : ℝ)⁻¹ ^ n < d / 2 := exists_pow_lt_of_lt_one (half_pos hd) (by norm_num)
  let n := Nat.find H
  have hn : (2 : ℝ)⁻¹ ^ n < d / 2 := Nat.find_spec H
  have hn0 : n ≠ 0 := by
    intro h0
    have : (2 : ℝ)⁻¹ ^ 0 = 1 := by norm_num
    have : 1 < d / 2 := by
      calc 1 = (2 : ℝ)⁻¹ ^ 0 := by norm_num
           _ < d / 2 := by rw [h0] at hn; exact hn
    linarith
  have hn_min := Nat.find_min H (Nat.pred_lt hn0)
  use n
  refine ⟨?_, hn⟩
  push_neg at hn_min
  have Hpow : (2 : ℝ)⁻¹ ^ (n - 1) = 2 * (2 : ℝ)⁻¹ ^ n := by
    have : n = n - 1 + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)).symm
    nth_rw 2 [this]
    rw [pow_add, pow_one]
    ring
  have hn_min' : d / 2 ≤ (2 : ℝ)⁻¹ ^ (n - 1) := hn_min
  rw [Hpow] at hn_min'
  linarith

/-- An interval of length more than `2 ^ (1 - n)` inside `[0, 1]` contains a dyadic cell of
resolution `n`. -/
lemma exists_nat_dyadic_cell_subset_Ioo {l r : ℝ} {n : ℕ}
    (hl : 0 ≤ l) (hr : r ≤ 1)
    (hn : (2 : ℝ)⁻¹ ^ n < (r - l) / 2) :
    ∃ k : ℕ, k + 1 ≤ 2 ^ n ∧
      l < (k : ℝ) * (2 : ℝ)⁻¹ ^ n ∧ ((k : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n < r := by
  let x := l * 2 ^ n
  have Hx_nonneg : 0 ≤ x := mul_nonneg hl (by positivity)
  let k := ⌊ x ⌋₊ + 1
  use k
  have h_floor2 : x < (⌊ x ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have h_k1 : x < (k : ℝ) := by
    calc x < (⌊ x ⌋₊ : ℝ) + 1 := h_floor2
         _ = (k : ℝ) := by simp [k]
  have Hpow : (2 : ℝ)⁻¹ ^ n = ((2 : ℝ) ^ n)⁻¹ := by exact inv_pow 2 n
  have h_k2 : (k : ℝ) ≤ x + 1 := by
    calc (k : ℝ) = (⌊ x ⌋₊ : ℝ) + 1 := by simp [k]
         _ ≤ x + 1 := by
           have : (⌊ x ⌋₊ : ℝ) ≤ x := Nat.floor_le Hx_nonneg
           linarith
  have H_l : l < (k : ℝ) * (2 : ℝ)⁻¹ ^ n := by
    rw [Hpow, ← div_eq_mul_inv]
    exact (lt_div_iff₀ (by positivity)).mpr h_k1
  have H_r : ((k : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n < r := by
    rw [Hpow, ← div_eq_mul_inv]
    have h_strict : (x + 2) / 2 ^ n < r := by
      have : (x + 2) / 2 ^ n = l + 2 * ((2 : ℝ) ^ n)⁻¹ := by
        calc (x + 2) / 2 ^ n = x * ((2 : ℝ) ^ n)⁻¹ + 2 * ((2 : ℝ) ^ n)⁻¹ := by
               rw [div_eq_mul_inv]; ring
             _ = (l * 2 ^ n) * ((2 : ℝ) ^ n)⁻¹ + 2 * ((2 : ℝ) ^ n)⁻¹ := rfl
             _ = l + 2 * ((2 : ℝ) ^ n)⁻¹ := by
               have hpos : (2 : ℝ) ^ n ≠ 0 := by positivity
               rw [mul_assoc, mul_inv_cancel₀ hpos, mul_one]
      rw [this, ← Hpow]
      linarith
    have : ((k : ℝ) + 1) / 2 ^ n ≤ (x + 2) / 2 ^ n := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      linarith
    linarith
  have H_b : k + 1 ≤ 2 ^ n := by
    have h_bound : ((k : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n < 1 := by linarith
    rw [Hpow, ← div_eq_mul_inv] at h_bound
    have : (k : ℝ) + 1 < 2 ^ n := (div_lt_one (by positivity)).mp h_bound
    exact_mod_cast this.le
  exact ⟨H_b, H_l, H_r⟩

private lemma devBitsToNat_append (x : BitString) (b : Bool) :
  devBitsToNat (x ++ [b]) = devBitsToNat x * 2 + (if b then 1 else 0) := by
  induction x with
  | nil =>
    cases b <;> rfl
  | cons h t ih =>
    rw [devBitsToNat, List.cons_append, devBitsToNat, ih, List.length_append, List.length_singleton]
    have : 2 ^ (t.length + 1) = 2 ^ t.length * 2 := by ring
    rw [this]
    ring

/-- Under the uniform measure the left endpoint attached to `p` is `p` read as a binary fraction. -/
lemma treeLeftEnd_lengthMeasure_eq_div (p : BitString) :
    treeLeftEnd lengthMeasure p = (devBitsToNat p : ℝ) / 2 ^ p.length := by
  induction p using List.reverseRecOn with
  | nil =>
    simp [treeLeftEnd, devBitsToNat]
  | append_singleton x b ih =>
    rw [List.length_append, List.length_singleton]
    rw [devBitsToNat_append x b]
    push_cast
    have Hpow : (2 : ℝ) ^ (x.length + 1) = 2 ^ x.length * 2 := by ring
    rw [Hpow]
    cases b
    · rw [treeLeftEnd_append_false]
      rw [ih]
      simp
      ring
    · rw [treeLeftEnd_append_true]
      rw [ih]
      have Hlm : (lengthMeasure (x ++ [false])).toReal = (2 : ℝ)⁻¹ ^ (x.length + 1) := by
        rw [lengthMeasure_toReal, List.length_append, List.length_singleton]
      rw [Hlm]
      simp
      ring

/-- Writing `k < 2 ^ n` in `n` binary digits and reading it back returns `k`. -/
lemma devBitsToNat_natToBits {n k : ℕ} (hk : k < 2 ^ n) : devBitsToNat (natToBits n k) = k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this
    rfl
  | succ n ih =>
    rw [natToBits_succ, devBitsToNat]
    rw [natToBits_length, bitsAux_fst]
    have Hmod : k % 2^n < 2^n := Nat.mod_lt _ (pow_pos (by omega) _)
    have ih' := ih Hmod
    have Hbits : natToBits n k = natToBits n (k % 2^n) := by
      have h1 : k = k % 2^n + (k / 2^n) * 2^n := by
        have := Nat.mod_add_div k (2^n)
        rw [mul_comm] at this
        exact this.symm
      nth_rw 1 [h1]
      rw [natToBits_add_mul]
    rw [Hbits, ih']
    have Hdiv : k / 2^n < 2 := by
      have h_pow : 2 ^ (n + 1) = 2 ^ n * 2 := by ring
      rw [h_pow] at hk
      exact Nat.div_lt_of_lt_mul hk
    cases h_div : (k / 2^n) with
    | zero =>
      simp
      have := Nat.mod_add_div k (2^n)
      rw [h_div] at this
      omega
    | succ x =>
      cases x with
      | zero =>
        simp
        have := Nat.mod_add_div k (2^n)
        rw [h_div] at this
        omega
      | succ y =>
        exfalso
        omega

/-- The closed dyadic interval `[0.p, 0.p + 2 ^ (-|p|)]` attached to a bit string. -/
noncomputable def binaryClosedInterval (p : BitString) : Set ℝ :=
  Set.Icc (treeLeftEnd lengthMeasure p)
          (treeLeftEnd lengthMeasure p + (lengthMeasure p).toReal)

/-- Every open subinterval of `[0, 1]` contains a closed dyadic interval of length at least a
quarter
of its own. -/
theorem exists_binaryClosedInterval_subset_Ioo
    {l r : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ 1) :
    ∃ p : BitString,
      binaryClosedInterval p ⊆ Set.Ioo l r ∧
      (r - l) / 4 ≤ (lengthMeasure p).toReal := by
  let d := r - l
  have hd : 0 < d := sub_pos.mpr hlr
  have hd1 : d ≤ 1 := by linarith
  rcases exists_inv_two_pow_mem_Ico_quarter_half hd hd1 with ⟨n, hn1, hn2⟩
  rcases exists_nat_dyadic_cell_subset_Ioo hl hr hn2 with ⟨k, hk1, hk2, hk3⟩
  use natToBits n k
  have hk_lt : k < 2^n := by omega
  have h_len : (natToBits n k).length = n := natToBits_length n k
  have h_dev : devBitsToNat (natToBits n k) = k := devBitsToNat_natToBits hk_lt
  have h_left : treeLeftEnd lengthMeasure (natToBits n k) = (k : ℝ) * (2 : ℝ)⁻¹ ^ n := by
    rw [treeLeftEnd_lengthMeasure_eq_div]
    rw [h_len, h_dev]
    rw [inv_pow]
    exact div_eq_mul_inv (k:ℝ) (2^n:ℝ)
  have h_len_meas : (lengthMeasure (natToBits n k)).toReal = (2 : ℝ)⁻¹ ^ n := by
    rw [lengthMeasure_toReal, h_len]
  constructor
  · rw [binaryClosedInterval]
    rw [h_left, h_len_meas]
    intro x hx
    simp only [Set.mem_Icc, Set.mem_Ioo] at hx ⊢
    constructor
    · linarith
    · linarith
  · rw [h_len_meas]
    exact hn1

/-- Explicit description of the closed binary interval `I_p` as `[k/2^n, (k+1)/2^n]`,
where `n = |p|` and `k` is the natural number with binary expansion `p`. -/
lemma binaryClosedInterval_eq_Icc (p : BitString) :
    binaryClosedInterval p =
      Set.Icc ((devBitsToNat p : ℝ) / 2 ^ p.length)
              (((devBitsToNat p : ℝ) + 1) / 2 ^ p.length) := by
  rw [binaryClosedInterval, treeLeftEnd_lengthMeasure_eq_div, lengthMeasure_toReal]
  congr 1
  rw [inv_pow]
  field_simp

/-- Dyadic intervals start at a nonnegative point. -/
lemma treeLeftEnd_lengthMeasure_nonneg (p : BitString) :
    0 ≤ treeLeftEnd lengthMeasure p := by
  rw [treeLeftEnd_lengthMeasure_eq_div]
  positivity

/-- Dyadic intervals end at a point of `[0, 1]`. -/
lemma treeLeftEnd_lengthMeasure_add_lengthMeasure_le_one (p : BitString) :
    treeLeftEnd lengthMeasure p + (lengthMeasure p).toReal ≤ 1 := by
  rw [treeLeftEnd_lengthMeasure_eq_div, lengthMeasure_toReal, inv_pow,
    show ((2 : ℝ) ^ p.length)⁻¹ = 1 / 2 ^ p.length from (one_div _).symm,
    ← add_div, div_le_one (by positivity)]
  have h : devBitsToNat p + 1 ≤ 2 ^ p.length := bitsToNat_lt p
  exact_mod_cast h

/-- Every closed binary interval is contained in the unit interval. -/
lemma binaryClosedInterval_subset_Icc_zero_one (p : BitString) :
    binaryClosedInterval p ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  rw [binaryClosedInterval, Set.mem_Icc] at hx
  exact ⟨le_trans (treeLeftEnd_lengthMeasure_nonneg p) hx.1,
    le_trans hx.2 (treeLeftEnd_lengthMeasure_add_lengthMeasure_le_one p)⟩

/-- Restatement of `exists_binaryClosedInterval_subset_Ioo` with the length of the binary
interval given explicitly as `2^{-|p|}`. -/
theorem exists_binaryClosedInterval_subset_Ioo_pow
    {l r : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ 1) :
    ∃ p : BitString,
      binaryClosedInterval p ⊆ Set.Ioo l r ∧ (r - l) / 4 ≤ (2 : ℝ)⁻¹ ^ p.length := by
  obtain ⟨p, hsub, hlen⟩ := exists_binaryClosedInterval_subset_Ioo hl hlr hr
  exact ⟨p, hsub, by rwa [lengthMeasure_toReal] at hlen⟩

/-- The left endpoint `0.p` belongs to the closed binary interval `I_p`. -/
lemma treeLeftEnd_mem_binaryClosedInterval (p : BitString) :
    treeLeftEnd lengthMeasure p ∈ binaryClosedInterval p := by
  rw [binaryClosedInterval, Set.mem_Icc]
  refine ⟨le_rfl, ?_⟩
  have : (0 : ℝ) ≤ (lengthMeasure p).toReal := ENNReal.toReal_nonneg
  linarith
