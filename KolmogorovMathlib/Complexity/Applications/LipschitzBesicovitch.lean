/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.LibraryAPI
import KolmogorovMathlib.Complexity.Applications.BesicovitchDistance
import KolmogorovMathlib.CommonInformation.FixedFrequency
import KolmogorovMathlib.Complexity.PairComplexity.Basic
import KolmogorovMathlib.PointToSet.Order.NormalizedSlack
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic
import KolmogorovMathlib.PointToSet.Examples.MiddleThirds

/-!
# Lipschitz transformations are not transitive (SUV Section 8.7, pp. 258-260)

Theorem 165 is purely about Cantor and Besicovitch distance, but the proof goes through the
effective Hausdorff dimension of a sequence, the library's `effectiveHausdorffDim {ω}`, equal to
`liminf C(ω_0 … ω_{n-1}) / n` by Theorem 120 (`effectiveHausdorffDim_singleton_eq_liminf`).

**Relativization.**  The proof ends with "all our arguments are relativizable and every Lipschitz
mapping is computable relative to some oracle".  No matching Cantor-space oracle-effective cover
dimension is available in the library, so we use `oraclePrefixDim`, the lower density of the prefix
complexity relative to the oracle set `A`, using the library's `PointToSet.optimalOraclePrefix`.
Plain and prefix complexity differ by `O(log n)`, which does not change this limit.  This is a
complexity presentation of the book's relativized dimension; its equality with a relativized
cover definition is not formalized here.  The library's
`exists_optimalOraclePrefix_finite` ensures that the complexities used below are finite.

**Lemma 2 needs `ε ≤ 1/2`.**  The book's Lemma 2 says that if `ρ(ω₁, ω₂) < ε`, the dimensions differ
by at most `H(ε)`.  This fails for large `ε`, since `H` is not monotone there: a random `ω₁` and
`ω₂ = 0^∞` have `ρ = 1/2 < 0.9` and dimensions differing by `1 > H(0.9)`.  The book only applies the
lemma to small `ε`, and the hypothesis `ε ≤ 1/2` is added here.
-/

namespace Kolmogorov.Applications

open Filter

/-- **SUV p. 259.**  `f` is a *computable Lipschitz mapping*: the first `n` bits of `f(ω)` are
effectively determined by the first `n + c` bits of `ω`, for some `c`. -/
def IsComputableLipschitz (f : CantorSeq → CantorSeq) : Prop :=
  ∃ (c : ℕ) (g : BitString → BitString), Computable g ∧
    ∀ w n, g (cantorPrefix w (n + c)) = cantorPrefix (f w) n


/-- Step 1 of the proof of `effectiveHausdorffDim_singleton_apply_le`: extract complexity
bound. -/
private lemma effectiveHausdorffDim_singleton_apply_le_step1
    {f : CantorSeq → CantorSeq} (c : ℕ) (g : BitString → BitString) (hg : Computable g)
    (h_g_prefix : ∀ w n, g (cantorPrefix w (n + c)) = cantorPrefix (f w) n)
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c_K : ℕ, ∀ w n,
      plainK V (cantorPrefix (f w) n) ≤ plainK V (cantorPrefix w (n + c)) + (c_K : ℕ∞) := by
  obtain ⟨c_K, hc_K⟩ := plainK_map_le V hV g hg
  use c_K
  intro w n
  have h := hc_K (cantorPrefix w (n + c))
  rw [h_g_prefix] at h
  exact h

/-- Step 2 of the proof of `effectiveHausdorffDim_singleton_apply_le`: the liminf of
shifted complexity ratio is equal to the unshifted liminf. -/
private lemma effectiveHausdorffDim_singleton_apply_le_step2
    (w : CantorSeq) (c : ℕ) (V : Map) :
    Filter.liminf (fun n : ℕ =>
      ((plainK V (cantorPrefix w (n + c))).toNat : ℝ) / (n + c : ℝ)) Filter.atTop =
    Filter.liminf (fun n : ℕ =>
      ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ)) Filter.atTop := by
  have h : (fun n : ℕ => ((plainK V (cantorPrefix w (n + c))).toNat : ℝ) / (n + c : ℝ)) =
           (fun n : ℕ => (fun m : ℕ => ((plainK V (cantorPrefix w m)).toNat : ℝ) / (m : ℝ)) (n + c))
               := by
    funext n
    dsimp only
    rw [Nat.cast_add]
  rw [h]
  exact Filter.liminf_nat_add (fun m : ℕ => ((plainK V (cantorPrefix w m)).toNat : ℝ) / (m : ℝ)) c

/-- Step 3 of the proof of `effectiveHausdorffDim_singleton_apply_le`: bound the liminf of
the target complexity ratio. -/
private lemma effectiveHausdorffDim_singleton_apply_le_step3
    {f : CantorSeq → CantorSeq} (w : CantorSeq) (c : ℕ) (c_K : ℕ) (V : Map)
        (hV : isOptimalConditional V)
    (h_le : ∀ n, plainK V (cantorPrefix (f w) n) ≤ plainK V (cantorPrefix w (n + c)) + (c_K : ℕ∞)) :
    Filter.liminf (fun n : ℕ =>
      ((plainK V (cantorPrefix (f w) n)).toNat : ℝ) / (n : ℝ)) Filter.atTop ≤
    Filter.liminf (fun n : ℕ =>
      ((plainK V (cantorPrefix w (n + c))).toNat : ℝ) / (n + c : ℝ)) Filter.atTop := by
  obtain ⟨C, hC⟩ := plainK_le_length V hV
  set u : ℕ → ℝ := fun n => ((plainK V (cantorPrefix (f w) n)).toNat : ℝ) / (n : ℝ)
  set v : ℕ → ℝ := fun n => ((plainK V (cantorPrefix w (n + c))).toNat : ℝ) / ((n + c : ℕ) : ℝ)
  set M : ℝ := (1 + (C : ℝ)) * (c : ℝ) + (c_K : ℝ)
  suffices hlim : Filter.liminf u Filter.atTop ≤ Filter.liminf v Filter.atTop by
    simpa only [u, v, Nat.cast_add] using hlim
  have hB : ∀ n : ℕ, (plainK V (cantorPrefix w (n + c))).toNat ≤ (n + c : ℕ) + C := by
    intro n
    have h1 := hC (cantorPrefix w (n + c))
    have hlen : (programLength (cantorPrefix w (n + c)) : ℕ∞) = ((n + c : ℕ) : ℕ∞) := by
      exact_mod_cast cantorPrefix_length w (n + c)
    rw [hlen] at h1
    have hrhs : (((n + c : ℕ) : ℕ∞) + (C : ℕ∞)) ≠ ⊤ :=
      WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ENat.natCast_ne_top C⟩
    have h2 := ENat.toNat_le_toNat h1 hrhs
    rwa [ENat.toNat_add (ENat.natCast_ne_top _) (ENat.natCast_ne_top C), ENat.toNat_natCast,
      ENat.toNat_natCast] at h2
  have hA : ∀ n : ℕ, (plainK V (cantorPrefix (f w) n)).toNat ≤
      (plainK V (cantorPrefix w (n + c))).toNat + c_K := by
    intro n
    have h1 := h_le n
    have hrhs : (plainK V (cantorPrefix w (n + c)) + (c_K : ℕ∞)) ≠ ⊤ := by
      have hbdd : plainK V (cantorPrefix w (n + c)) ≤ ((n + c : ℕ) : ℕ∞) + (C : ℕ∞) := by
        have h := hC (cantorPrefix w (n + c))
        have hlen : (programLength (cantorPrefix w (n + c)) : ℕ∞) = ((n + c : ℕ) : ℕ∞) := by
          exact_mod_cast cantorPrefix_length w (n + c)
        rwa [hlen] at h
      have hbdd2 : plainK V (cantorPrefix w (n + c)) ≠ ⊤ := by
        have hne : (((n + c : ℕ) : ℕ∞) + (C : ℕ∞)) ≠ ⊤ :=
            WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ENat.natCast_ne_top C⟩
        exact ne_top_of_le_ne_top hne hbdd
      exact WithTop.add_ne_top.mpr ⟨hbdd2, ENat.natCast_ne_top c_K⟩
    have h2 := ENat.toNat_le_toNat h1 hrhs
    rwa [ENat.toNat_add (ne_top_of_le_ne_top hrhs (le_add_right le_rfl)) (ENat.natCast_ne_top c_K),
        ENat.toNat_natCast] at h2
  
  have hv_le : ∀ n, v n ≤ 1 + (C : ℝ) := by
    intro n
    by_cases hn : n + c = 0
    · have hn_nat : n = 0 ∧ c = 0 := by omega
      have hnc_real : ((n + c : ℕ) : ℝ) = 0 := by exact_mod_cast hn
      have hz1 : v n = ((plainK V (cantorPrefix w (n + c))).toNat : ℝ) / ((n + c : ℕ) : ℝ) := rfl
      rw [hz1, hnc_real, div_zero]
      positivity
    · have hn_pos : (0 : ℝ) < ((n + c : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hn_ge_1 : (1 : ℝ) ≤ ((n + c : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + c by omega)
      calc v n = ((plainK V (cantorPrefix w (n + c))).toNat : ℝ) / ((n + c : ℕ) : ℝ) := rfl
        _ ≤ (((n + c : ℕ) + C : ℕ) : ℝ) / ((n + c : ℕ) : ℝ) := div_le_div_of_nonneg_right
            (by exact_mod_cast (hB n)) (by positivity)
        _ = (((n + c : ℕ) : ℝ) + (C : ℝ)) / ((n + c : ℕ) : ℝ) := by push_cast; rfl
        _ = ((n + c : ℕ) : ℝ) / ((n + c : ℕ) : ℝ) + (C : ℝ) / ((n + c : ℕ) : ℝ) := by rw [add_div]
        _ = 1 + (C : ℝ) / ((n + c : ℕ) : ℝ) := by rw [div_self hn_pos.ne']
        _ ≤ 1 + (C : ℝ) / 1 := by gcongr
        _ = 1 + (C : ℝ) := by rw [div_one]
  have hu_le_v_add : ∀ n ≥ 1, u n ≤ v n + M / (n : ℝ) := by
    intro n hn
    have hn_nat : 0 < n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_nat
    have hn_pos_add : (0 : ℝ) < ((n + c : ℕ) : ℝ) := by exact_mod_cast (show 0 < n + c by omega)
    calc u n = ((plainK V (cantorPrefix (f w) n)).toNat : ℝ) / n := rfl
      _ ≤ (((plainK V (cantorPrefix w (n + c))).toNat : ℝ) + c_K) / n := div_le_div_of_nonneg_right
          (by exact_mod_cast (hA n)) (by positivity)
      _ = ((plainK V (cantorPrefix w (n + c))).toNat : ℝ) / n + (c_K : ℝ) / n := by rw [add_div]
      _ = (((plainK V (cantorPrefix w (n + c))).toNat : ℝ) / ((n + c : ℕ) : ℝ)) * ((n + c : ℕ) : ℝ)
          / n + (c_K : ℝ) / n := by
        have h1 : (((plainK V (cantorPrefix w (n + c))).toNat : ℝ) / ((n + c : ℕ) : ℝ)) *
            ((n + c : ℕ) : ℝ) = ((plainK V (cantorPrefix w (n + c))).toNat : ℝ) :=
            div_mul_cancel₀ _ hn_pos_add.ne'
        rw [h1]
      _ = (v n * ((n + c : ℕ) : ℝ)) / n + (c_K : ℝ) / n := rfl
      _ = v n * (((n + c : ℕ) : ℝ) / n) + (c_K : ℝ) / n := by rw [mul_div_assoc]
      _ = v n * (((n : ℝ) + (c : ℝ)) / n) + (c_K : ℝ) / n := by
        have h_cast : ((n + c : ℕ) : ℝ) = (n : ℝ) + (c : ℝ) := by exact Nat.cast_add n c
        rw [h_cast]
      _ = v n * ((n : ℝ) / (n : ℝ) + (c : ℝ) / (n : ℝ)) + (c_K : ℝ) / n := by rw [add_div]
      _ = v n * (1 + (c : ℝ) / (n : ℝ)) + (c_K : ℝ) / n := by rw [div_self hn_pos.ne']
      _ = v n + v n * ((c : ℝ) / (n : ℝ)) + (c_K : ℝ) / n := by rw [mul_add, mul_one]
      _ ≤ v n + (1 + (C : ℝ)) * ((c : ℝ) / (n : ℝ)) + (c_K : ℝ) / n := by
        gcongr
        exact hv_le n
      _ = v n + M / (n : ℝ) := by
        dsimp [M]
        ring
  have hcompare : ∀ᶠ n in Filter.atTop, u n ≤ v n + M / (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact hu_le_v_add n hn
  
  have hvCob : IsCoboundedUnder (· ≥ ·) Filter.atTop v := Filter.isCoboundedUnder_ge_of_le
      Filter.atTop hv_le
  have huBdd : IsBoundedUnder (· ≥ ·) Filter.atTop u := Filter.isBoundedUnder_of ⟨(0 : ℝ),
      fun n => (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) : 0 ≤ u n)⟩
  
  have he : Tendsto (fun n : ℕ => M / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat M
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlt : Filter.liminf v Filter.atTop < Filter.liminf v Filter.atTop + ε / 2 := by linarith
  have hfreq : ∃ᶠ n in Filter.atTop, v n < Filter.liminf v Filter.atTop + ε / 2 :=
      Filter.frequently_lt_of_liminf_lt hvCob hlt
  have hev : ∀ᶠ n : ℕ in Filter.atTop, M / (n : ℝ) < ε / 2 := Filter.Tendsto.eventually_lt he
      tendsto_const_nhds (by linarith)
  have hfreq2 : ∃ᶠ n in Filter.atTop, u n ≤ Filter.liminf v Filter.atTop + ε := by
    refine (hfreq.and_eventually (hev.and hcompare)).mono ?_
    rintro n ⟨hv, he', hu⟩
    linarith
  exact Filter.liminf_le_of_frequently_le hfreq2 huBdd

/-- **SUV Lemma 1 of Section 8.7, p. 259.**  A computable Lipschitz mapping does not increase the
effective Hausdorff dimension of a sequence. -/
theorem effectiveHausdorffDim_singleton_apply_le {f : CantorSeq → CantorSeq}
    (hf : IsComputableLipschitz f) (w : CantorSeq) :
    effectiveHausdorffDim {f w} ≤ effectiveHausdorffDim {w} := by
  obtain ⟨c, g, hg, h_g_prefix⟩ := hf
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  rw [effectiveHausdorffDim_singleton_eq_liminf V hV (f w)]
  rw [effectiveHausdorffDim_singleton_eq_liminf V hV w]
  obtain ⟨c_K, hc_K⟩ := effectiveHausdorffDim_singleton_apply_le_step1 c g hg h_g_prefix V hV
  have h1 := effectiveHausdorffDim_singleton_apply_le_step3 w c c_K V hV (hc_K w)
  have h2 := effectiveHausdorffDim_singleton_apply_le_step2 w c V
  rwa [h2] at h1


/-! ### Lemma 2 (SUV Section 8.7, p. 259)

The proof follows the book.  If the first `n` terms of `ω₁` and `ω₂` differ in `k` places, the
complexity of the `n`-prefix of `ω₁` exceeds the one of `ω₂` by at most the complexity of the
bitwise xor of the two prefixes (a string of length `n` with `k` ones, of complexity at most
`log₂ (n choose k) + O(log n)`), plus the `O(log n)` price of the pair.  For `k < ε n` with
`ε ≤ 1/2`, `log₂ (n choose k) ≤ n H(ε)`.  Dividing by `n` and taking the lower limit gives the
claim, by Theorem 120 (`effectiveHausdorffDim_singleton_eq_liminf`). -/

/-- The number of discrepancies is symmetric. -/
private lemma abs_effectiveHausdorffDim_sub_le_discrepancies_comm (a b : CantorSeq) (n : ℕ) :
    discrepancies a b n = discrepancies b a n := by
  classical
  unfold discrepancies
  congr 1
  ext i
  simp [ne_comm]

/-- The Besicovitch distance is symmetric. -/
private lemma abs_effectiveHausdorffDim_sub_le_besicovitchDist_comm (a b : CantorSeq) :
    besicovitchDist a b = besicovitchDist b a := by
  unfold besicovitchDist
  simp only [abs_effectiveHausdorffDim_sub_le_discrepancies_comm a b]

/-- If `ρ(a, b) < ε`, then eventually the number of discrepancies is less than `ε n`. -/
private lemma abs_effectiveHausdorffDim_sub_le_eventually_discrepancies_lt {a b : CantorSeq}
    {ε : ℝ} (hρ : besicovitchDist a b < ε) :
    ∀ᶠ n : ℕ in atTop, (discrepancies a b n : ℝ) < ε * n := by
  unfold besicovitchDist at hρ
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (discrepancies a b n : ℝ) / n) := by
    refine Filter.isBoundedUnder_of ⟨1, fun n => ?_⟩
    have hle : (discrepancies a b n : ℝ) ≤ n := by
      classical
      unfold discrepancies
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · exact (div_le_one (by exact_mod_cast hpos)).2 hle
  have h := Filter.eventually_lt_of_limsup_lt hρ hbdd
  filter_upwards [h, eventually_gt_atTop 0] with n hn hn0
  rwa [div_lt_iff₀ (by exact_mod_cast hn0)] at hn

/-- An additive error `e n → 0` does not change the comparison of lower limits, up to the
constant `H`: if `u n ≤ v n + H + e n` eventually, then `liminf u ≤ liminf v + H`. -/
private lemma abs_effectiveHausdorffDim_sub_le_liminf_le_liminf_add (u v e : ℕ → ℝ) (H : ℝ)
    (hu0 : ∀ n, 0 ≤ u n) (hvM : ∃ M, ∀ n, v n ≤ M) (he : Tendsto e atTop (nhds 0))
    (h : ∀ᶠ n in atTop, u n ≤ v n + H + e n) :
    liminf u atTop ≤ liminf v atTop + H := by
  obtain ⟨M, hM⟩ := hvM
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hlt : liminf v atTop < liminf v atTop + δ / 2 := by linarith
  have hfreq : ∃ᶠ n in atTop, v n < liminf v atTop + δ / 2 :=
    Filter.frequently_lt_of_liminf_lt (isCoboundedUnder_ge_of_le atTop hM) hlt
  have hev : ∀ᶠ n in atTop, e n < δ / 2 := he.eventually_lt_const (by linarith)
  have hfreq2 : ∃ᶠ n in atTop, u n ≤ liminf v atTop + H + δ := by
    refine (hfreq.and_eventually (hev.and h)).mono ?_
    rintro n ⟨h1, h2, h3⟩
    linarith
  exact Filter.liminf_le_of_frequently_le hfreq2 (isBoundedUnder_of ⟨0, hu0⟩)

/-- The binomial bound in logarithmic form: for `0 < ε ≤ 1/2` and `k ≤ ε n`,
`ln (n choose k) ≤ n (-ε ln ε - (1 - ε) ln (1 - ε))`.  It comes from the single term
`ε^k (1 - ε)^(n - k) (n choose k)` of the binomial expansion of `(ε + (1 - ε))^n = 1`. -/
private lemma abs_effectiveHausdorffDim_sub_le_log_choose_le {n k : ℕ} {ε : ℝ} (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 2) (hk : (k : ℝ) ≤ ε * n) :
    Real.log (n.choose k : ℝ) ≤ n * (Real.negMulLog ε + Real.negMulLog (1 - ε)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have h1ε : 0 < 1 - ε := by linarith
  have hsum : ∑ m ∈ Finset.range (n + 1), ε ^ m * (1 - ε) ^ (n - m) * (n.choose m : ℝ) = 1 := by
    have := add_pow ε (1 - ε) n
    simpa using this.symm
  have hterm : ε ^ k * (1 - ε) ^ (n - k) * (n.choose k : ℝ) ≤ 1 := by
    refine le_of_le_of_eq ?_ hsum
    exact Finset.single_le_sum (f := fun m => ε ^ m * (1 - ε) ^ (n - m) * (n.choose m : ℝ))
      (fun m _ => mul_nonneg (mul_nonneg (pow_nonneg hε0.le _) (pow_nonneg h1ε.le _))
        (Nat.cast_nonneg _)) (show k ∈ Finset.range (n + 1) from Finset.mem_range.2 (by omega))
  have hchoose : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hlog := Real.log_le_log (by positivity) hterm
  rw [Real.log_one, Real.log_mul (by positivity) hchoose.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Nat.cast_sub hkn] at hlog
  have hlogle : Real.log ε ≤ Real.log (1 - ε) := Real.log_le_log hε0 (by linarith)
  simp only [Real.negMulLog_def] at *
  nlinarith [mul_nonneg (sub_nonneg.2 hk) (sub_nonneg.2 hlogle)]

/-- The binary length of a natural number is at most `log₂` plus one. -/
private lemma abs_effectiveHausdorffDim_sub_le_nat_size_real_le (n : ℕ) :
    (Nat.size n : ℝ) ≤ Real.logb 2 n + 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hpow_nat : 2 ^ (n.size - 1) ≤ n :=
    Nat.lt_size.mp (by have : 0 < n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn); omega)
  have hpow_real : (2 : ℝ) ^ (n.size - 1) ≤ (n : ℝ) := by exact_mod_cast hpow_nat
  have hlog : Real.logb 2 ((2 : ℝ) ^ (n.size - 1)) ≤ Real.logb 2 n :=
    (Real.logb_le_logb (by norm_num) (by positivity)
      (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr hpow_real
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one] at hlog
  have h1n : 1 ≤ n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
  push_cast [Nat.cast_sub h1n] at hlog
  linarith

/-- For `0 < ε ≤ 1/2` and `k ≤ ε n`, the binary length of `n choose k` is at most
`n H(ε) + 1`. -/
private lemma abs_effectiveHausdorffDim_sub_le_size_choose_le {n k : ℕ} {ε : ℝ} (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 2) (hk : (k : ℝ) ≤ ε * n) :
    (Nat.size (n.choose k) : ℝ) ≤ n * binaryEntropy ε + 1 := by
  have h := abs_effectiveHausdorffDim_sub_le_log_choose_le hε0 hε hk
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact_mod_cast this
  have hchoose : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : Real.logb 2 (n.choose k : ℝ) ≤ n * binaryEntropy ε := by
    rw [Real.logb, div_le_iff₀ hl2]
    have : (n : ℝ) * binaryEntropy ε * Real.log 2 =
        n * (Real.negMulLog ε + Real.negMulLog (1 - ε)) := by
      unfold binaryEntropy negMulLog2
      field_simp
    rw [this]
    exact h
  have := abs_effectiveHausdorffDim_sub_le_nat_size_real_le (n.choose k)
  linarith

/-- The bitwise xor of the two components of a pair code.  Applied to the pair code of
`(y, x)` with `x = y ⊕ z` it returns `z`, so a string is computable from the pair code of
a second string and of the xor of the two. -/
private def abs_effectiveHausdorffDim_sub_le_xorDecode (s : BitString) : BitString :=
  (List.range (decodeFirst s).length).map fun i =>
    xor ((decodeFirst s).getD i false) ((decodeSecond s).getD i false)

/-- The xor decoder is computable (indeed primitive recursive). -/
private lemma abs_effectiveHausdorffDim_sub_le_xorDecode_computable :
    Computable abs_effectiveHausdorffDim_sub_le_xorDecode := by
  have hf : Primrec (fun s : BitString => decodeFirst s) :=
    CodedFiniteDistribution.decodeFirst_primrec
  have hs : Primrec (fun s : BitString => decodeSecond s) :=
    CodedFiniteDistribution.decodeSecond_primrec
  have h1 : Primrec (fun s : BitString => List.range (decodeFirst s).length) :=
    Primrec.list_range.comp (Primrec.list_length.comp hf)
  have h2 : Primrec₂ (fun (s : BitString) (i : ℕ) =>
      xor ((decodeFirst s).getD i false) ((decodeSecond s).getD i false)) := by
    have hg1 : Primrec₂ (fun (s : BitString) (i : ℕ) => (decodeFirst s).getD i false) :=
      (Primrec.list_getD false).comp (hf.comp Primrec.fst) Primrec.snd
    have hg2 : Primrec₂ (fun (s : BitString) (i : ℕ) => (decodeSecond s).getD i false) :=
      (Primrec.list_getD false).comp (hs.comp Primrec.fst) Primrec.snd
    exact (Primrec.dom_bool₂ xor).comp hg1 hg2
  exact (Primrec.list_map h1 h2).to_comp

/-- The `n`-prefix of `a` is recovered from the `n`-prefix of `b` and the `n`-prefix of the xor
sequence `a ⊕ b`. -/
private lemma abs_effectiveHausdorffDim_sub_le_xorDecode_pairCode (a b : CantorSeq) (n : ℕ) :
    abs_effectiveHausdorffDim_sub_le_xorDecode
        (pairCode (cantorPrefix b n) (cantorPrefix (fun i => xor (a i) (b i)) n)) =
      cantorPrefix a n := by
  unfold abs_effectiveHausdorffDim_sub_le_xorDecode
  rw [decodeFirst_pairCode, decodeSecond_pairCode, cantorPrefix_length]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    have hl : i < (cantorPrefix b n).length := by simpa using hi
    have hl' : i < (cantorPrefix (fun i => xor (a i) (b i)) n).length := by simpa using hi
    have e1 : (cantorPrefix b n).getD i false = b i := by
      rw [List.getD_eq_getElem _ _ hl, cantorPrefix_getElem]
    have e2 : (cantorPrefix (fun i => xor (a i) (b i)) n).getD i false = xor (a i) (b i) := by
      rw [List.getD_eq_getElem _ _ hl', cantorPrefix_getElem]
    simp only [List.getElem_map, List.getElem_range, e1, e2, cantorPrefix_getElem]
    cases a i <;> cases b i <;> rfl

/-- The number of ones in the `n`-prefix of the xor sequence is the number of discrepancies. -/
private lemma abs_effectiveHausdorffDim_sub_le_count_xor (a b : CantorSeq) (n : ℕ) :
    (cantorPrefix (fun i => xor (a i) (b i)) n).count true = discrepancies a b n := by
  classical
  induction n with
  | zero => simp [cantorPrefix, discrepancies]
  | succ n ih =>
    rw [cantorPrefix_succ, List.count_append, ih]
    unfold discrepancies
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : a n = b n
    · simp [h]
    · have hx : xor (a n) (b n) = true := by
        cases ha : a n <;> cases hb : b n <;> simp_all
      have hne : a n ≠ b n := h
      simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      simp [hx]

/-- `⌊log₂ m⌋` is at most the binary length of `m`. -/
private lemma abs_effectiveHausdorffDim_sub_le_log_le_size (m : ℕ) :
    Nat.log 2 m ≤ Nat.size m := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · simp [h0]
  · have h1 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
    have h2 : m < 2 ^ Nat.size m := Nat.lt_size_self m
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h1 h2) |>.le

/-- The pointwise form of the book's argument: the complexity of the `n`-prefix of `a` exceeds
the one of `b` by at most the binary length of `n choose d_n(a, b)` plus `O(log n)`, with a
constant independent of `a`, `b` and `n`. -/
private lemma abs_effectiveHausdorffDim_sub_le_plainK_prefix_le (V : Map)
    (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (a b : CantorSeq) (n : ℕ),
      ((plainK V (cantorPrefix a n)).toNat : ℝ) ≤
        ((plainK V (cantorPrefix b n)).toNat : ℝ) +
          (Nat.size (n.choose (discrepancies a b n)) : ℝ) + (logSlack C n : ℝ) := by
  obtain ⟨c_map, hc_map⟩ := plainK_map_le V hV abs_effectiveHausdorffDim_sub_le_xorDecode
    abs_effectiveHausdorffDim_sub_le_xorDecode_computable
  obtain ⟨k₀, hk₀⟩ := plainK_pair_le_add_two_log V hV
  obtain ⟨c_fw, hc_fw⟩ := plainK_fixedWeight_le_size_choose_add_length V hV
  obtain ⟨c_len, hc_len⟩ := plainK_le_length V hV
  obtain ⟨C₁, hC₁⟩ := logSlack_linear_bound 2 1 c_len
  refine ⟨C₁ + 4 + (c_fw + k₀ + c_map), fun a b n => ?_⟩
  set z : BitString := cantorPrefix b n with hz
  set x : BitString := cantorPrefix (fun i => xor (a i) (b i)) n with hx
  set k : ℕ := discrepancies a b n with hk
  have hxlen : x.length = n := by simp [hx]
  have hxcount : x.count true = k := abs_effectiveHausdorffDim_sub_le_count_xor a b n
  have h1 : plainK V (cantorPrefix a n) ≤ plainK V (pairCode z x) + (c_map : ℕ∞) := by
    have := hc_map (pairCode z x)
    rwa [hz, hx, abs_effectiveHausdorffDim_sub_le_xorDecode_pairCode] at this
  have h2 : plainK V (pairCode z x) ≤
      plainK V z + plainK V x + ((2 * Nat.log 2 (cVal V z) + k₀ : ℕ) : ℕ∞) := hk₀ z x
  have h3 : plainK V x ≤ ((Nat.size (n.choose k) + 4 * Nat.size n + c_fw : ℕ) : ℕ∞) :=
    hc_fw n k x hxlen hxcount
  have hz_le : plainK V z ≤ ((n + c_len : ℕ) : ℕ∞) := by
    have := hc_len z
    simpa [programLength, hz] using this
  have hfin : plainK V z ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hz_le
  have hcVal : cVal V z ≤ n + c_len := by
    have := ENat.toNat_le_toNat hz_le (ENat.natCast_ne_top _)
    rwa [ENat.toNat_natCast] at this
  have hlog : Nat.log 2 (cVal V z) ≤ Nat.size (n + c_len) :=
    (Nat.log_mono_right hcVal).trans (abs_effectiveHausdorffDim_sub_le_log_le_size _)
  have hslack : 4 * Nat.size n + 2 * Nat.log 2 (cVal V z) + c_fw + k₀ + c_map ≤
      logSlack (C₁ + 4 + (c_fw + k₀ + c_map)) n := by
    rw [logSlack_add_constants, logSlack_add_constants]
    have e1 : 2 * Nat.log 2 (cVal V z) ≤ logSlack C₁ n := by
      calc 2 * Nat.log 2 (cVal V z) ≤ 2 * Nat.size (n + c_len) := by omega
        _ ≤ logSlack 2 (1 * n + c_len) := by
          unfold logSlack
          rw [one_mul, ← Nat.size_eq_bits_len]
          omega
        _ ≤ logSlack C₁ n := hC₁ n
    have e2 : 4 * Nat.size n ≤ logSlack 4 n := by
      unfold logSlack
      rw [← Nat.size_eq_bits_len]
      omega
    have e3 : c_fw + k₀ + c_map ≤ logSlack (c_fw + k₀ + c_map) n := by
      unfold logSlack
      omega
    omega
  set S : ℕ :=
    Nat.size (n.choose k) + 4 * Nat.size n + c_fw + 2 * Nat.log 2 (cVal V z) + k₀ + c_map
    with hS
  have hmain : plainK V (cantorPrefix a n) ≤ plainK V z + ((S : ℕ) : ℕ∞) := by
    calc plainK V (cantorPrefix a n) ≤ plainK V (pairCode z x) + (c_map : ℕ∞) := h1
      _ ≤ (plainK V z + plainK V x + ((2 * Nat.log 2 (cVal V z) + k₀ : ℕ) : ℕ∞)) +
            (c_map : ℕ∞) := by gcongr
      _ ≤ (plainK V z + ((Nat.size (n.choose k) + 4 * Nat.size n + c_fw : ℕ) : ℕ∞) +
            ((2 * Nat.log 2 (cVal V z) + k₀ : ℕ) : ℕ∞)) + (c_map : ℕ∞) := by gcongr
      _ = plainK V z + ((S : ℕ) : ℕ∞) := by
          rw [hS]
          push_cast
          ring
  have hne : plainK V z + ((S : ℕ) : ℕ∞) ≠ ⊤ :=
    WithTop.add_ne_top.mpr ⟨hfin, ENat.natCast_ne_top _⟩
  have hnat := ENat.toNat_le_toNat hmain hne
  rw [ENat.toNat_add hfin (ENat.natCast_ne_top _), ENat.toNat_natCast] at hnat
  have hreal : ((plainK V (cantorPrefix a n)).toNat : ℝ) ≤
      ((plainK V z).toNat : ℝ) + ((Nat.size (n.choose k) +
        logSlack (C₁ + 4 + (c_fw + k₀ + c_map)) n : ℕ) : ℝ) := by
    have : (plainK V (cantorPrefix a n)).toNat ≤
        (plainK V z).toNat + (Nat.size (n.choose k) +
          logSlack (C₁ + 4 + (c_fw + k₀ + c_map)) n) := hnat.trans (by omega)
    exact_mod_cast this
  push_cast at hreal
  linarith

/-- The one-sided form of Lemma 2: if `ρ(a, b) < ε` and `ε ≤ 1/2`, then
`dim a ≤ dim b + H(ε)`. -/
private lemma abs_effectiveHausdorffDim_sub_le_dim_le_add (V : Map) (hV : isOptimalConditional V)
    {a b : CantorSeq} {ε : ℝ} (hε : ε ≤ 1 / 2) (hρ : besicovitchDist a b < ε) :
    effectiveHausdorffDim {a} ≤ effectiveHausdorffDim {b} + binaryEntropy ε := by
  rw [effectiveHausdorffDim_singleton_eq_liminf V hV a,
    effectiveHausdorffDim_singleton_eq_liminf V hV b]
  obtain ⟨C, hC⟩ := abs_effectiveHausdorffDim_sub_le_plainK_prefix_le V hV
  obtain ⟨c_len, hc_len⟩ := plainK_le_length V hV
  have hdens := abs_effectiveHausdorffDim_sub_le_eventually_discrepancies_lt hρ
  have hε0 : 0 < ε := by
    obtain ⟨n, hn, hn1⟩ := (hdens.and (eventually_gt_atTop 0)).exists
    have h0 : (0 : ℝ) ≤ discrepancies a b n := Nat.cast_nonneg _
    have hn1' : (0 : ℝ) < n := by exact_mod_cast hn1
    by_contra hneg
    have hneg' : ε ≤ 0 := not_lt.1 hneg
    nlinarith
  have hbound : ∀ n : ℕ, (plainK V (cantorPrefix b n)).toNat ≤ n + c_len := by
    intro n
    have h := hc_len (cantorPrefix b n)
    simp only [programLength, cantorPrefix_length] at h
    have := ENat.toNat_le_toNat (h.trans_eq (by push_cast; rfl)) (ENat.natCast_ne_top (n + c_len))
    rwa [ENat.toNat_natCast] at this
  refine abs_effectiveHausdorffDim_sub_le_liminf_le_liminf_add
    (fun n => ((plainK V (cantorPrefix a n)).toNat : ℝ) / n)
    (fun n => ((plainK V (cantorPrefix b n)).toNat : ℝ) / n)
    (fun n => (1 + (logSlack C n : ℝ)) / n) (binaryEntropy ε) ?_ ?_ ?_ ?_
  · intro n
    positivity
  · refine ⟨1 + c_len, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [CharP.cast_eq_zero, div_zero]
      positivity
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos
      have h1 : ((plainK V (cantorPrefix b n)).toNat : ℝ) ≤ n + c_len := by
        exact_mod_cast hbound n
      have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      have h3 : (0 : ℝ) ≤ c_len := Nat.cast_nonneg _
      change ((plainK V (cantorPrefix b n)).toNat : ℝ) / n ≤ 1 + c_len
      rw [div_le_iff₀ hnpos]
      nlinarith
  · have h := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add
      (PointToSet.normalized_additive_slack_logSlack C)
    rw [add_zero] at h
    exact h.congr fun n => (add_div _ _ _).symm
  · filter_upwards [hdens, eventually_gt_atTop 0] with n hn hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 := hC a b n
    have h2 := abs_effectiveHausdorffDim_sub_le_size_choose_le hε0 hε hn.le
    have hkey : ((plainK V (cantorPrefix a n)).toNat : ℝ) ≤
        ((plainK V (cantorPrefix b n)).toNat : ℝ) + n * binaryEntropy ε +
          (1 + (logSlack C n : ℝ)) := by linarith
    change ((plainK V (cantorPrefix a n)).toNat : ℝ) / n ≤
      ((plainK V (cantorPrefix b n)).toNat : ℝ) / n + binaryEntropy ε +
        (1 + (logSlack C n : ℝ)) / n
    calc ((plainK V (cantorPrefix a n)).toNat : ℝ) / n
        ≤ (((plainK V (cantorPrefix b n)).toNat : ℝ) + n * binaryEntropy ε +
            (1 + (logSlack C n : ℝ))) / n := div_le_div_of_nonneg_right hkey hnpos.le
      _ = ((plainK V (cantorPrefix b n)).toNat : ℝ) / n + binaryEntropy ε +
            (1 + (logSlack C n : ℝ)) / n := by
          field_simp

/-- **SUV Lemma 2 of Section 8.7, p. 259.**  If `ρ(ω₁, ω₂) < ε`, with `ε ≤ 1/2`, the effective
Hausdorff dimensions of `ω₁` and `ω₂` differ at most by `H(ε)`. -/
theorem abs_effectiveHausdorffDim_sub_le {a b : CantorSeq} {ε : ℝ} (hε : ε ≤ 1 / 2)
    (hρ : besicovitchDist a b < ε) :
    |effectiveHausdorffDim {a} - effectiveHausdorffDim {b}| ≤ binaryEntropy ε := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  have h1 := abs_effectiveHausdorffDim_sub_le_dim_le_add V hV hε hρ
  have hρ' : besicovitchDist b a < ε := by
    rwa [abs_effectiveHausdorffDim_sub_le_besicovitchDist_comm] at hρ
  have h2 := abs_effectiveHausdorffDim_sub_le_dim_le_add V hV hε hρ'
  rw [abs_le]
  constructor <;> linarith

/-! ### The relativized form -/

/-- The dimension of a sequence relative to the oracle `A`: the lower density of the prefix
complexity of its prefixes relative to `A`.  This uses the complexity presentation of dimension,
not a new definition by oracle-effective covers; the bridge to such covers remains unstated.
The chosen oracle prefix decompressor has finite complexity on every finite string, so `toNat`
does not silently turn an infinite complexity into zero. -/
noncomputable def oraclePrefixDim (A : Set ℕ) (w : CantorSeq) : ℝ :=
  liminf (fun n : ℕ =>
    ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w n)).toNat : ℝ) / n) atTop

/-- The relativized computable Lipschitz mappings: the function on strings is computable in `A`. -/
def IsComputableLipschitzIn (A : Set ℕ) (f : CantorSeq → CantorSeq) : Prop :=
  ∃ (c : ℕ) (g : BitString → BitString), PartrecIn {charOracle A} (fun x => Part.some (g x)) ∧
    ∀ w n, g (cantorPrefix w (n + c)) = cantorPrefix (f w) n

/-- Step 1 of the proof of `exists_isComputableLipschitzIn_of_isCantorLipschitz`: extract
the lookahead constant from the Lipschitz property. -/
private lemma exists_isComputableLipschitzIn_of_isCantorLipschitz_delay {f : CantorSeq →
    CantorSeq}
    (hf : IsCantorLipschitz f) :
    ∃ k : ℕ, ∀ (a b : CantorSeq) (n : ℕ), cantorPrefix a (n + k) = cantorPrefix b (n + k) →
      cantorPrefix (f a) n = cantorPrefix (f b) n := by
  obtain ⟨c, hc⟩ := hf
  have hk_exists : ∃ k : ℕ, c ≤ 2^k := by
    obtain ⟨k, hk⟩ := exists_nat_gt c
    use k
    exact hk.le.trans (by exact_mod_cast (Nat.lt_pow_self (by decide : 1 < 2)).le)
  obtain ⟨k, hk⟩ := hk_exists
  use k
  intro a b n h
  have hd_ab : cantorDist b a ≤ (1 / 2) ^ (n + k) := by
    change @Dist.dist (ℕ → Bool) (PiNat.dist (E := fun _ => Bool)) b a ≤ (1 / 2) ^ (n + k)
    rw [← PiNat.mem_cylinder_iff_dist_le, PiNat.mem_cylinder_iff]
    intro i hi
    unfold cantorPrefix at h
    have h1 := congrArg (fun L => L[i]?) h
    have hia : i < (List.ofFn fun j : Fin (n + k) => a j).length := by
      rw [List.length_ofFn]
      exact hi
    have hib : i < (List.ofFn fun j : Fin (n + k) => b j).length := by
      rw [List.length_ofFn]
      exact hi
    rw [List.getElem?_eq_getElem hia, List.getElem?_eq_getElem hib] at h1
    have h2 := Option.some.inj h1
    rw [List.getElem_ofFn, List.getElem_ofFn] at h2
    exact h2.symm
  have hd_f : cantorDist (f b) (f a) ≤ c * cantorDist b a := hc b a
  by_cases h_c_neg : c ≤ 0
  · have h_dist_le_0 : cantorDist (f b) (f a) ≤ 0 := by
      calc cantorDist (f b) (f a) ≤ c * cantorDist b a := hd_f
        _ ≤ 0 * cantorDist b a := by
          have h_dist_nonneg : 0 ≤ cantorDist b a := by
            change 0 ≤ @Dist.dist (ℕ → Bool) (PiNat.dist (E := fun _ => Bool)) b a
            exact PiNat.dist_nonneg b a
          gcongr
        _ = 0 := zero_mul _
    have hd_fa_fb_zero : cantorDist (f b) (f a) = 0 :=
        le_antisymm h_dist_le_0 (by exact PiNat.dist_nonneg _ _)
    have h_fa_eq_fb : f b = f a := by
      change @Dist.dist (ℕ → Bool) (PiNat.dist (E := fun _ => Bool)) (f b) (f a) =
          0 at hd_fa_fb_zero
      exact PiNat.eq_of_dist_eq_zero _ _ hd_fa_fb_zero
    rw [h_fa_eq_fb]
  · push Not at h_c_neg
    have hd_f_le : cantorDist (f b) (f a) ≤ (1 / 2) ^ n := by
      calc cantorDist (f b) (f a) ≤ c * cantorDist b a := hd_f
        _ ≤ 2^k * cantorDist b a := by
          have h_dist_nonneg : 0 ≤ cantorDist b a := PiNat.dist_nonneg b a
          gcongr
        _ ≤ 2^k * (1 / 2) ^ (n + k) := by
          gcongr
        _ = (2:ℝ)^k * (2:ℝ)⁻¹ ^ (n + k) := by norm_num
        _ = (2:ℝ)^k * ((2:ℝ)⁻¹ ^ n * (2:ℝ)⁻¹ ^ k) := by
          rw [pow_add]
        _ = (2:ℝ)^k * (2:ℝ)⁻¹ ^ k * (2:ℝ)⁻¹ ^ n := by ring
        _ = (2 * (2:ℝ)⁻¹) ^ k * (2:ℝ)⁻¹ ^ n := by
          rw [mul_pow]
        _ = (1:ℝ) ^ k * (2:ℝ)⁻¹ ^ n := by
          have h_inv : (2:ℝ) * (2:ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by norm_num)
          rw [h_inv]
        _ = (1 / 2) ^ n := by norm_num
    have h_f_cyl : f b ∈ PiNat.cylinder (f a) n := by
      have hd_f_le2 : @Dist.dist (ℕ → Bool) (PiNat.dist (E := fun _ => Bool)) (f b) (f a) ≤ (1 / 2)
          ^ n := hd_f_le
      exact PiNat.mem_cylinder_iff_dist_le.mpr hd_f_le2
    rw [PiNat.mem_cylinder_iff] at h_f_cyl
    unfold cantorPrefix
    apply List.ext_getElem
    · rw [List.length_ofFn, List.length_ofFn]
    · intro i hi1 hi2
      rw [List.length_ofFn] at hi1
      rw [List.getElem_ofFn, List.getElem_ofFn]
      exact (h_f_cyl i hi1).symm

/-- Step 2 of the proof of `exists_isComputableLipschitzIn_of_isCantorLipschitz`: there
exists a string function representing the Cantor mapping. -/
private lemma exists_isComputableLipschitzIn_of_isCantorLipschitz_g {f : CantorSeq →
    CantorSeq}
    (k : ℕ) (h_delay : ∀ (a b : CantorSeq) (n : ℕ), cantorPrefix a (n + k) = cantorPrefix b (n + k)
        →
      cantorPrefix (f a) n = cantorPrefix (f b) n) :
    ∃ g : BitString → BitString, ∀ w n, g (cantorPrefix w (n + k)) = cantorPrefix (f w) n := by
  use fun s => cantorPrefix (f (prependCantor s (fun _ => false))) (s.length - k)
  intro w n
  dsimp only
  have hs_len : (cantorPrefix w (n + k)).length = n + k := cantorPrefix_length w (n + k)
  have hn : (cantorPrefix w (n + k)).length - k = n := by rw [hs_len, Nat.add_sub_cancel]
  rw [hn]
  apply h_delay
  have h1 : cantorPrefix (prependCantor (cantorPrefix w (n + k)) (fun _ => false)) (n + k) =
      cantorPrefix w (n + k) := by
    have h2 := cantorPrefix_prepend (cantorPrefix w (n + k)) (fun _ => false)
    rw [hs_len] at h2
    exact h2
  rw [h1]

private def exists_isComputableLipschitzIn_of_isCantorLipschitz_oracle_tableGraph
    (g : BitString → BitString) : Set ℕ :=
  Set.range (fun x : BitString => Nat.pair (Encodable.encode x) (Encodable.encode (g x)))

/-- Step 3 of the proof of `exists_isComputableLipschitzIn_of_isCantorLipschitz`: any
string function is computable relative to some oracle. -/
private lemma exists_isComputableLipschitzIn_of_isCantorLipschitz_oracle
    (g : BitString → BitString) :
    ∃ A : Set ℕ, PartrecIn {charOracle A} (fun x => Part.some (g x)) := by
  let G := exists_isComputableLipschitzIn_of_isCantorLipschitz_oracle_tableGraph g
  have hquery : PartrecIn {charOracle G}
      (fun q : BitString × ℕ ↦ charOracle G (Nat.pair (Encodable.encode q.1) q.2)) := by
    apply PartrecIn.comp (PartrecIn.oracle _ (Set.mem_singleton _))
    exact (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd).computableIn
  have htest : ComputableIn₂ {charOracle G}
      (fun (_ : BitString × ℕ) (r : ℕ) ↦ decide (r = 1)) := by
    exact (PrimrecPred.decide
      (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 1))).to₂.to_comp.computableIn₂
  have hsearch := PartrecIn.rfind (hquery.map htest).to₂
  have hdecode : PartrecIn₂ {charOracle G}
      (fun (_ : BitString) (k : ℕ) ↦ Part.ofOption (Encodable.decode (α := BitString) k)) :=
    (Computable.ofOption (Computable.decode.comp Computable.snd)).partrecIn.to₂
  use G
  refine PartrecIn.of_eq_tot (hsearch.bind hdecode) ?_
  intro x
  refine Part.mem_bind_iff.mpr ⟨Encodable.encode (g x), ?_, ?_⟩
  · apply Nat.mem_rfind.mpr
    constructor
    · simp [charOracle, G,
        exists_isComputableLipschitzIn_of_isCantorLipschitz_oracle_tableGraph]
    · intro m hm
      have hne : Encodable.encode (g x) ≠ m := Nat.ne_of_gt hm
      have h_not_mem : Nat.pair (Encodable.encode x) m ∉ G := by
        intro hmem
        obtain ⟨y, hy⟩ := hmem
        have h_enc_x_eq : Encodable.encode y = Encodable.encode x := (Nat.pair_eq_pair.mp hy).1
        have h_eq : y = x := Encodable.encode_injective h_enc_x_eq
        subst h_eq
        exact hne (Nat.pair_eq_pair.mp hy).2
      simp [charOracle, h_not_mem]
  · rw [Encodable.encodek]
    simp

/-- **SUV p. 260.**  Every Lipschitz mapping is computable relative to some oracle. -/
theorem exists_isComputableLipschitzIn_of_isCantorLipschitz {f : CantorSeq → CantorSeq}
    (hf : IsCantorLipschitz f) : ∃ A, IsComputableLipschitzIn A f := by
  obtain ⟨k, hk⟩ := exists_isComputableLipschitzIn_of_isCantorLipschitz_delay hf
  obtain ⟨g, hg⟩ := exists_isComputableLipschitzIn_of_isCantorLipschitz_g k hk
  obtain ⟨A, hA⟩ := exists_isComputableLipschitzIn_of_isCantorLipschitz_oracle g
  use A
  unfold IsComputableLipschitzIn
  use k, g


/-- Step 1 of the proof of `oraclePrefixDim_apply_le`: extract complexity bound. -/
private lemma oraclePrefixDim_apply_le_step1
    {A : Set ℕ} {f : CantorSeq → CantorSeq} (c : ℕ) (g : BitString → BitString)
    (hg : PartrecIn {charOracle A} (fun x => Part.some (g x)))
    (h_g_prefix : ∀ w n, g (cantorPrefix w (n + c)) = cantorPrefix (f w) n) :
    ∃ c_K : ℕ, ∀ w n,
      KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix (f w) n) ≤
      KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w (n + c)) + (c_K : ℕ∞) := by
  let F : List BitString →. BitString := fun xs => Part.some (g xs.headI)
  have hF : PartrecIn {charOracle A} F := by
    exact PartrecIn.comp (f := fun x => Part.some (g x)) (g := fun xs : List BitString => xs.headI)
        hg Primrec.list_headI.to_comp.computableIn
  obtain ⟨c_K, hc_K⟩ := PointToSet.oracle_tuple_bounds_composition A 1 F hF
  use c_K
  intro w n
  have h := hc_K [cantorPrefix w (n + c)] (cantorPrefix (f w) n) rfl (by
    simp only [F, List.headI_cons, h_g_prefix, Part.mem_some_iff]
  )
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  have eq1 : KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix (f w) n) =
      PointToSet.oracleComplexity A (cantorPrefix (f w) n) :=
      (PointToSet.oraclePrefixComplexity_coe A (cantorPrefix (f w) n) []).symm
  have eq2 : KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w (n + c)) =
      PointToSet.oracleComplexity A (cantorPrefix w (n + c)) :=
      (PointToSet.oraclePrefixComplexity_coe A (cantorPrefix w (n + c)) []).symm
  rw [eq1, eq2]
  exact ENat.natCast_le_natCast.mpr h

/-- Step 2 of the proof of `oraclePrefixDim_apply_le`: the liminf of shifted complexity
ratio is equal to the unshifted liminf. -/
private lemma oraclePrefixDim_apply_le_step2
    (A : Set ℕ) (w : CantorSeq) (c : ℕ) :
    Filter.liminf (fun n : ℕ =>
      ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w (n + c))).toNat : ℝ) /
          (n + c : ℝ)) Filter.atTop =
    Filter.liminf (fun n : ℕ =>
      ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w n)).toNat : ℝ) / (n : ℝ))
          Filter.atTop := by
  have h := Filter.liminf_nat_add (fun n : ℕ =>
    ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w n)).toNat : ℝ) / (n : ℝ)) c
  rw [← h]
  simp only [Nat.cast_add]


private lemma oraclePrefixDim_apply_le_linear_bound (A : Set ℕ) :
    ∃ C : ℕ, ∀ x : BitString,
      (KPPlain (PointToSet.optimalOraclePrefix A) x).toNat ≤ 2 * x.length + C := by
  obtain ⟨U₀, hU₀⟩ := exists_isOptimalPrefixConditional
  have hU₀_in : IsDecompressorIn (charOracle A) U₀ := by
    unfold IsDecompressorIn
    have hd : Computable (fun n => Encodable.decode (α := BitString × BitString) n) :=
      Computable.decode
    have hopt : Partrec (fun n =>
        Part.ofOption (Encodable.decode (α := BitString × BitString) n)) :=
      Computable.ofOption hd
    have hmap : Partrec₂ (fun (n : ℕ) (a : BitString × BitString) =>
        (U₀ a).map Encodable.encode) := by
      have ht1 : Partrec (fun (pr : ℕ × (BitString × BitString)) => U₀ pr.2) :=
        hU₀.1.1.comp Computable.snd
      have ht2 : Computable (fun (pr : (ℕ × (BitString × BitString)) × BitString) =>
          Encodable.encode pr.2) :=
        Computable.encode.comp Computable.snd
      exact Partrec.map ht1 ht2
    have h_partrec : Partrec (mapToNatFun U₀) := by
      unfold mapToNatFun
      exact Partrec.bind hopt hmap
    have ht1 : PartrecIn {charOracle A} (mapToNatFun U₀) := Partrec.partrecIn h_partrec
    exact RecursiveIn.iff_nat.mpr (PartrecIn.iff_nat.mp ht1)
  obtain ⟨c₁, hc₁⟩ := (PointToSet.exists_optimalOraclePrefix_spec A).2.2 U₀ hU₀_in hU₀.1.2
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_two_mul_length U₀ hU₀
  refine ⟨c₂ + c₁, fun x => ?_⟩
  have h : KPPlain (PointToSet.optimalOraclePrefix A) x ≤
      ((2 * x.length + (c₂ + c₁) : ℕ) : ℕ∞) := by
    calc KPPlain (PointToSet.optimalOraclePrefix A) x ≤ KPPlain U₀ x + (c₁ : ℕ∞) := hc₁ x []
      _ ≤ (2 * (x.length : ℕ∞) + (c₂ : ℕ∞)) + (c₁ : ℕ∞) := by gcongr; exact hc₂ x
      _ = (((2 * x.length + c₂ : ℕ) : ℕ∞) + (c₁ : ℕ∞)) := by exact_mod_cast rfl
      _ = ((2 * x.length + (c₂ + c₁) : ℕ) : ℕ∞) := by exact_mod_cast Nat.add_assoc _ _ _
  have h_nat := ENat.toNat_le_toNat h (ENat.natCast_ne_top _)
  rwa [ENat.toNat_natCast] at h_nat

private lemma oraclePrefixDim_apply_le_analysis (a b : ℕ → ℝ) (c c_K C : ℕ)
    (ha0 : ∀ n, 0 ≤ a n)
    (h_le : ∀ n, a n ≤ b n + c_K)
    (hb_le : ∀ n, b n ≤ 2 * (n + c : ℝ) + C) :
    liminf (fun n => a n / n) atTop ≤ liminf (fun n => b n / (n + c)) atTop := by
  set u := fun n : ℕ => a n / n
  set v := fun n : ℕ => b n / (n + c)
  set M : ℝ := 2 + C
  have hv_M : ∀ n, 1 ≤ n → v n ≤ M := by
    intro n hn
    have hn_pos : (0 : ℝ) < n + c := by positivity
    have h1 : b n / (n + c) ≤ (2 * (n + c : ℝ) + C) / (n + c) := div_le_div_of_nonneg_right
        (hb_le n) hn_pos.le
    have h2 : (2 * (n + c : ℝ) + C) / (n + c) = 2 + C / (n + c) := by
      rw [add_div, mul_div_cancel_right₀ _ hn_pos.ne']
    have h3 : 2 + (C : ℝ) / (n + c) ≤ 2 + C := by
      gcongr
      have h4 : (C : ℝ) / (n + c) ≤ C / 1 := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) < 1)
        have h5 : 1 ≤ n + c := by omega
        exact_mod_cast h5
      simpa using h4
    exact h1.trans (h2.trans_le h3)
  have hu_le : ∀ᶠ n in atTop, u n ≤ v n + (M * c + c_K) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn_c_pos : (0 : ℝ) < n + c := by positivity
    have h1 : u n ≤ (b n + c_K) / n := div_le_div_of_nonneg_right (h_le n) hn_pos.le
    have h2 : (b n + c_K) / n = b n / n + c_K / n := add_div _ _ _
    have h3 : b n / n = b n / (n + c) + b n * c / ((n + c) * n) := by
      have hd1 : (n : ℝ) ≠ 0 := hn_pos.ne'
      have hd2 : (n + c : ℝ) ≠ 0 := hn_c_pos.ne'
      calc b n / n = (b n * (n + c)) / (n * (n + c)) := by 
            have h_eq1 : b n / n = (b n / n) * 1 := by rw [mul_one]
            have h_eq2 : 1 = (n + c : ℝ) / (n + c) := by rw [div_self hd2]
            rw [h_eq1, h_eq2, div_mul_div_comm, mul_comm (n : ℝ) (n + c)]
        _ = (b n * n + b n * c) / (n * (n + c)) := by rw [mul_add]
        _ = b n * n / (n * (n + c)) + b n * c / (n * (n + c)) := by rw [add_div]
        _ = b n / (n + c) + b n * c / (n * (n + c)) := by 
          congr 1
          calc b n * n / (n * (n + c)) = b n * n / ((n + c) * n) := by rw [mul_comm (n : ℝ) (n+c)]
            _ = (b n / (n + c)) * (n / n) := by rw [div_mul_div_comm]
            _ = (b n / (n + c)) * 1 := by rw [div_self hd1]
            _ = b n / (n + c) := mul_one _
        _ = b n / (n + c) + b n * c / ((n + c) * n) := by
          congr 2
          rw [mul_comm (n : ℝ) (n+c)]
    have h4 : b n * c / ((n + c) * n) = (b n / (n + c)) * (c / n) := by
      rw [div_mul_div_comm]
    have h5 : u n ≤ v n + v n * (c / n) + c_K / n := by
      calc u n ≤ b n / n + c_K / n := by linarith
        _ = v n + v n * (c / n) + c_K / n := by rw [h3, h4]
    have h6 : v n * (c / n) ≤ M * (c / n) := by
      have h_c_div_n_pos : 0 ≤ (c : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn_pos.le
      have h_bound : v n ≤ M := hv_M n hn
      exact mul_le_mul_of_nonneg_right h_bound h_c_div_n_pos
    calc u n ≤ v n + v n * (c / n) + c_K / n := h5
      _ ≤ v n + M * (c / n) + c_K / n := by linarith
      _ = v n + (M * c + c_K) / n := by
        have h_tmp : M * (c / n) = M * c / n := by rw [mul_div_assoc]
        rw [h_tmp]
        have h_tmp2 : M * c / n + c_K / n = (M * c + c_K) / n := by rw [add_div]
        linarith
  have hvM' : ∀ (n : ℕ), v n ≤ M := fun n => by
    by_cases hn : 1 ≤ n
    · exact hv_M n hn
    · have h0 : n = 0 := by omega
      subst h0
      have hc_pos_or : c = 0 ∨ 0 < c := by omega
      rcases hc_pos_or with hc0 | hcp
      · subst hc0
        have h_v0 : v 0 = 0 := by
          dsimp [v]
          norm_num
        rw [h_v0]
        have hM_pos : 0 ≤ M := by
          have hC : (0:ℝ) ≤ C := Nat.cast_nonneg _
          linarith
        exact hM_pos
      · have hn_pos : (0 : ℝ) < c := by exact_mod_cast hcp
        have hb_le_0 := hb_le 0
        have h_ineq : b 0 ≤ 2 * (c : ℝ) + C := by 
          calc b 0 ≤ 2 * ((0 : ℝ) + c) + C := by simpa using hb_le_0
            _ = 2 * (c : ℝ) + C := by ring_nf
        have h1 : b 0 / c ≤ (2 * (c : ℝ) + C) / c := div_le_div_of_nonneg_right h_ineq hn_pos.le
        have h2 : (2 * (c : ℝ) + C) / c = 2 + C / c := by
          rw [add_div, mul_div_cancel_right₀ _ hn_pos.ne']
        have h3 : 2 + (C : ℝ) / c ≤ 2 + C := by
          gcongr
          have h4 : (C : ℝ) / c ≤ C / 1 := by
            apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) < 1)
            exact_mod_cast hcp
          simpa using h4
        have h_trans : b 0 / c ≤ 2 + C := h1.trans (h2.trans_le h3)
        have h_v0 : v 0 = b 0 / c := by
          dsimp [v]
          have h_tmp : ((0 : ℕ) : ℝ) + (c : ℝ) = (c : ℝ) := by norm_num
          rw [h_tmp]
        have h_M_def : M = 2 + C := rfl
        rw [h_M_def, h_v0]
        exact h_trans
  have h_bound_v : ∃ M, ∀ n, v n ≤ M := ⟨M, hvM'⟩
  have he : Tendsto (fun n : ℕ => (M * c + c_K) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
  have hu0 : ∀ n, 0 ≤ u n := fun n => div_nonneg (ha0 n) (Nat.cast_nonneg _)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hlt : liminf v atTop < liminf v atTop + δ / 2 := by linarith
  have hfreq : ∃ᶠ n in atTop, v n < liminf v atTop + δ / 2 := by
    apply Filter.frequently_lt_of_liminf_lt (isCoboundedUnder_ge_of_le atTop hvM') hlt
  have hev : ∀ᶠ (n : ℕ) in atTop, (M * c + c_K) / (n : ℝ) < δ / 2 := by
    have h_half : 0 < δ / 2 := by linarith
    exact he.eventually (gt_mem_nhds h_half)
  have hfreq2 : ∃ᶠ n in atTop, u n ≤ liminf v atTop + δ := by
    refine (hfreq.and_eventually (hev.and hu_le)).mono ?_
    rintro n ⟨h1, h2, h3⟩
    linarith
  exact Filter.liminf_le_of_frequently_le hfreq2 (isBoundedUnder_of ⟨0, hu0⟩)
/-- Step 3 of the proof of `oraclePrefixDim_apply_le`: bound the liminf of the target
complexity ratio. -/
private lemma oraclePrefixDim_apply_le_step3
    {A : Set ℕ} {f : CantorSeq → CantorSeq} (w : CantorSeq) (c : ℕ) (c_K : ℕ)
    (h_le : ∀ n, KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix (f w) n) ≤
                 KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w (n + c)) + (c_K : ℕ∞)) :
    Filter.liminf (fun n : ℕ =>
      ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix (f w) n)).toNat : ℝ) / (n : ℝ))
          Filter.atTop ≤
    Filter.liminf (fun n : ℕ =>
      ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w (n + c))).toNat : ℝ) /
          (n + c : ℝ)) Filter.atTop := by
  have h_fin : ∀ x, KPPlain (PointToSet.optimalOraclePrefix A) x ≠ ⊤ :=
      fun x => PointToSet.exists_optimalOraclePrefix_finite A x []
  let a : ℕ → ℝ := fun n : ℕ => ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix (f w)
                                  n)).toNat : ℝ)
  let b : ℕ → ℝ := fun n : ℕ => ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w (n +
                                  c))).toNat : ℝ)
  have ha0 : ∀ n, 0 ≤ a n := fun n => by
    have h_nat : (0 : ℝ) ≤ ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix (f w)
        n)).toNat : ℝ) := Nat.cast_nonneg _
    exact h_nat
  have h_le_nat : ∀ n, a n ≤ b n + c_K := by
    intro n
    have h1 := ENat.toNat_le_toNat (h_le n) (WithTop.add_ne_top.mpr ⟨h_fin _, ENat.natCast_ne_top
        c_K⟩)
    rw [ENat.toNat_add (h_fin _) (ENat.natCast_ne_top c_K), ENat.toNat_natCast] at h1
    change ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix (f w) n)).toNat : ℝ) ≤
        ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w (n + c))).toNat : ℝ) + c_K
    exact_mod_cast h1
  obtain ⟨C, hc_bound⟩ := oraclePrefixDim_apply_le_linear_bound A
  have hb_le_nat : ∀ n, b n ≤ 2 * (n + c : ℝ) + C := by
    intro n
    have h := hc_bound (cantorPrefix w (n + c))
    rw [cantorPrefix_length] at h
    have h_cast : ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix w (n + c))).toNat : ℝ)
        ≤ ((2 * (n + c) + C : ℕ) : ℝ) := by exact_mod_cast h
    have ht_cast : ((2 * (n + c) + C : ℕ) : ℝ) = 2 * (n + c : ℝ) + C := by push_cast; ring
    rw [ht_cast] at h_cast
    exact h_cast
  exact oraclePrefixDim_apply_le_analysis a b c c_K C ha0 h_le_nat hb_le_nat

/-- Lemma 1 relativized. -/
theorem oraclePrefixDim_apply_le {A : Set ℕ} {f : CantorSeq → CantorSeq}
    (hf : IsComputableLipschitzIn A f) (w : CantorSeq) :
    oraclePrefixDim A (f w) ≤ oraclePrefixDim A w := by
  obtain ⟨c, g, hg, h_g_prefix⟩ := hf
  unfold oraclePrefixDim
  obtain ⟨c_K, hc_K⟩ := oraclePrefixDim_apply_le_step1 c g hg h_g_prefix
  have h1 := oraclePrefixDim_apply_le_step3 w c c_K (hc_K w)
  have h2 := oraclePrefixDim_apply_le_step2 A w c
  rwa [h2] at h1

/-- A computable decompressor is computable relative to every oracle. -/
private lemma abs_oraclePrefixDim_sub_le_isDecompressorIn (A : Set ℕ) (D : Map)
    (hD : isDecompressor D) : IsDecompressorIn (charOracle A) D := by
  unfold IsDecompressorIn
  have hd : Computable (fun n => Encodable.decode (α := BitString × BitString) n) :=
    Computable.decode
  have hopt : Partrec (fun n =>
      Part.ofOption (Encodable.decode (α := BitString × BitString) n)) :=
    Computable.ofOption hd
  have hmap : Partrec₂ (fun (n : ℕ) (a : BitString × BitString) =>
      (D a).map Encodable.encode) := by
    have h1 : Partrec (fun (pr : ℕ × (BitString × BitString)) => D pr.2) :=
      hD.comp Computable.snd
    have h2 : Computable (fun (pr : (ℕ × (BitString × BitString)) × BitString) =>
        Encodable.encode pr.2) :=
      Computable.encode.comp Computable.snd
    exact Partrec.map h1 h2
  have h_partrec : Partrec (mapToNatFun D) := by
    unfold mapToNatFun
    exact Partrec.bind hopt hmap
  have h1 : PartrecIn {charOracle A} (mapToNatFun D) := Partrec.partrecIn h_partrec
  exact RecursiveIn.iff_nat.mpr (PartrecIn.iff_nat.mp h1)

/-- The optimal oracle prefix machine is optimal among the computable prefix decompressors,
up to an additive constant. -/
private lemma abs_oraclePrefixDim_sub_le_transfer (A : Set ℕ) {U₀ : Map}
    (hU₀ : IsOptimalPrefixConditional U₀) :
    ∃ c : ℕ, ∀ x, KPPlain (PointToSet.optimalOraclePrefix A) x ≤ KPPlain U₀ x + (c : ℕ∞) := by
  obtain ⟨c, hc⟩ := (PointToSet.exists_optimalOraclePrefix_spec A).2.2 U₀
    (abs_oraclePrefixDim_sub_le_isDecompressorIn A U₀ hU₀.1.1) hU₀.1.2
  exact ⟨c, fun x => hc x []⟩

/-- A linear upper bound for the prefix complexity relative to `A`. -/
private lemma abs_oraclePrefixDim_sub_le_linear_bound (A : Set ℕ) :
    ∃ c : ℕ, ∀ x : BitString,
      (KPPlain (PointToSet.optimalOraclePrefix A) x).toNat ≤ 2 * x.length + c := by
  obtain ⟨U₀, hU₀⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := abs_oraclePrefixDim_sub_le_transfer A hU₀
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_two_mul_length U₀ hU₀
  refine ⟨c₂ + c₁, fun x => ?_⟩
  have h : KPPlain (PointToSet.optimalOraclePrefix A) x ≤
      ((2 * x.length + (c₂ + c₁) : ℕ) : ℕ∞) := by
    calc KPPlain (PointToSet.optimalOraclePrefix A) x ≤ KPPlain U₀ x + (c₁ : ℕ∞) := hc₁ x
      _ ≤ (2 * (x.length : ℕ∞) + (c₂ : ℕ∞)) + (c₁ : ℕ∞) := by
          gcongr
          exact hc₂ x
      _ = ((2 * x.length + (c₂ + c₁) : ℕ) : ℕ∞) := by
          push_cast
          ring
  have := ENat.toNat_le_toNat h (ENat.natCast_ne_top _)
  rwa [ENat.toNat_natCast] at this

/-- The prefix complexity relative to `A` of a word of length `n` with `k` ones is at most the
binary length of `n choose k` plus `O(log n)`. -/
private lemma abs_oraclePrefixDim_sub_le_sparse (A : Set ℕ) :
    ∃ C : ℕ, ∀ (n k : ℕ) (s : BitString), s.length = n → s.count true = k →
      (KPPlain (PointToSet.optimalOraclePrefix A) s).toNat ≤
        Nat.size (n.choose k) + logSlack C n := by
  obtain ⟨U₀, hU₀⟩ := exists_isOptimalPrefixConditional
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨c₁, hc₁⟩ := abs_oraclePrefixDim_sub_le_transfer A hU₀
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_plainK_add_KPPlain_plainK U₀ V hU₀ hV
  obtain ⟨c₃, hc₃⟩ := KPPlain_le_two_mul_length U₀ hU₀
  obtain ⟨c_fw, hc_fw⟩ := plainK_fixedWeight_le_size_choose_add_length V hV
  obtain ⟨c_len, hc_len⟩ := plainK_le_length V hV
  obtain ⟨C₁, hC₁⟩ := logSlack_linear_bound 2 1 c_len
  refine ⟨C₁ + 4 + (c₁ + c₂ + c₃ + c_fw), fun n k s hsn hsk => ?_⟩
  have hs_le : plainK V s ≤ ((n + c_len : ℕ) : ℕ∞) := by
    have := hc_len s
    simpa [programLength, hsn] using this
  have hfin : plainK V s ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hs_le
  obtain ⟨kC, hkC⟩ : ∃ kC : ℕ, plainK V s = (kC : ℕ∞) :=
    ⟨(plainK V s).toNat, (ENat.natCast_toNat hfin).symm⟩
  have hkC_le : kC ≤ n + c_len := by
    rw [hkC] at hs_le
    exact_mod_cast hs_le
  have hkC_fw : kC ≤ Nat.size (n.choose k) + 4 * Nat.size n + c_fw := by
    have := hc_fw n k s hsn hsk
    rw [hkC] at this
    exact_mod_cast this
  have h1 := hc₂ s kC hkC
  have h2 := hc₃ (Nat.bits kC)
  have h3 := hc₁ s
  have hmain : KPPlain (PointToSet.optimalOraclePrefix A) s ≤
      ((kC + (2 * Nat.size kC + c₃) + c₂ + c₁ : ℕ) : ℕ∞) := by
    calc KPPlain (PointToSet.optimalOraclePrefix A) s ≤ KPPlain U₀ s + (c₁ : ℕ∞) := h3
      _ ≤ ((kC : ℕ∞) + KPPlain U₀ (Nat.bits kC) + (c₂ : ℕ∞)) + (c₁ : ℕ∞) := by gcongr
      _ ≤ ((kC : ℕ∞) + (2 * ((Nat.bits kC).length : ℕ∞) + (c₃ : ℕ∞)) + (c₂ : ℕ∞)) +
            (c₁ : ℕ∞) := by gcongr
      _ = ((kC + (2 * Nat.size kC + c₃) + c₂ + c₁ : ℕ) : ℕ∞) := by
          rw [Nat.size_eq_bits_len]
          push_cast
          ring
  have hnat := ENat.toNat_le_toNat hmain (ENat.natCast_ne_top _)
  rw [ENat.toNat_natCast] at hnat
  have hsz : Nat.size kC ≤ Nat.size (n + c_len) := Nat.size_le_size hkC_le
  have hslack : 4 * Nat.size n + 2 * Nat.size (n + c_len) + (c₁ + c₂ + c₃ + c_fw) ≤
      logSlack (C₁ + 4 + (c₁ + c₂ + c₃ + c_fw)) n := by
    rw [logSlack_add_constants, logSlack_add_constants]
    have e1 : 2 * Nat.size (n + c_len) ≤ logSlack C₁ n := by
      calc 2 * Nat.size (n + c_len) ≤ logSlack 2 (1 * n + c_len) := by
            unfold logSlack
            rw [one_mul, ← Nat.size_eq_bits_len]
            omega
        _ ≤ logSlack C₁ n := hC₁ n
    have e2 : 4 * Nat.size n ≤ logSlack 4 n := by
      unfold logSlack
      rw [← Nat.size_eq_bits_len]
      omega
    have e3 : c₁ + c₂ + c₃ + c_fw ≤ logSlack (c₁ + c₂ + c₃ + c_fw) n := by
      unfold logSlack
      omega
    omega
  omega

/-- The xor step relative to `A`: the complexity of the `n`-prefix of `a` is at most the sum of
the complexities of the `n`-prefix of `b` and of the `n`-prefix of the xor sequence `a ⊕ b`, up
to a constant. -/
private lemma abs_oraclePrefixDim_sub_le_xor_step (A : Set ℕ) :
    ∃ c : ℕ, ∀ (a b : CantorSeq) (n : ℕ),
      (KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix a n)).toNat ≤
        (KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat +
        (KPPlain (PointToSet.optimalOraclePrefix A)
          (cantorPrefix (fun i => xor (a i) (b i)) n)).toNat + c := by
  have hg : Computable (fun xs : List BitString =>
      abs_effectiveHausdorffDim_sub_le_xorDecode (pairCode (xs.getD 0 []) (xs.getD 1 []))) := by
    have h0 : Primrec (fun xs : List BitString => xs.getD 0 []) :=
      (Primrec.list_getD []).comp Primrec.id (Primrec.const 0)
    have h1 : Primrec (fun xs : List BitString => xs.getD 1 []) :=
      (Primrec.list_getD []).comp Primrec.id (Primrec.const 1)
    have hpair : Primrec (fun xs : List BitString => pairCode (xs.getD 0 []) (xs.getD 1 [])) :=
      CodedFiniteDistribution.pairCode_primrec.comp h0 h1
    exact Computable.comp (f := abs_effectiveHausdorffDim_sub_le_xorDecode)
      (g := fun xs : List BitString => pairCode (xs.getD 0 []) (xs.getD 1 []))
      abs_effectiveHausdorffDim_sub_le_xorDecode_computable hpair.to_comp
  obtain ⟨c, hc⟩ := PointToSet.oracle_tuple_bounds_composition A 2
    (fun xs => Part.some (abs_effectiveHausdorffDim_sub_le_xorDecode
      (pairCode (xs.getD 0 []) (xs.getD 1 [])))) hg.computableIn
  refine ⟨c, fun a b n => ?_⟩
  have h := hc [cantorPrefix b n, cantorPrefix (fun i => xor (a i) (b i)) n]
    (cantorPrefix a n) rfl (by
      rw [Part.mem_some_iff]
      exact (abs_effectiveHausdorffDim_sub_le_xorDecode_pairCode a b n).symm)
  simpa [PointToSet.oracleComplexity, PointToSet.oraclePrefixComplexityNat,
    PointToSet.oraclePrefixComplexity, KPPlain, add_assoc] using h

/-- The pointwise form of the book's argument, relative to `A`: the prefix complexity of the
`n`-prefix of `a` exceeds the one of `b` by at most the binary length of `n choose d_n(a, b)`
plus `O(log n)`, with a constant independent of `a`, `b` and `n`. -/
private lemma abs_oraclePrefixDim_sub_le_prefix_le (A : Set ℕ) :
    ∃ C : ℕ, ∀ (a b : CantorSeq) (n : ℕ),
      ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix a n)).toNat : ℝ) ≤
        ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat : ℝ) +
          (Nat.size (n.choose (discrepancies a b n)) : ℝ) + (logSlack C n : ℝ) := by
  obtain ⟨c₁, hc₁⟩ := abs_oraclePrefixDim_sub_le_xor_step A
  obtain ⟨C₂, hC₂⟩ := abs_oraclePrefixDim_sub_le_sparse A
  refine ⟨C₂ + c₁, fun a b n => ?_⟩
  have h1 := hc₁ a b n
  have h2 := hC₂ n (discrepancies a b n) (cantorPrefix (fun i => xor (a i) (b i)) n)
    (by simp) (abs_effectiveHausdorffDim_sub_le_count_xor a b n)
  have h3 : c₁ ≤ logSlack c₁ n := by
    unfold logSlack
    omega
  have hnat : (KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix a n)).toNat ≤
      (KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat +
        (Nat.size (n.choose (discrepancies a b n)) + logSlack (C₂ + c₁) n) := by
    rw [logSlack_add_constants]
    omega
  have hreal : ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix a n)).toNat : ℝ) ≤
      ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat : ℝ) +
        ((Nat.size (n.choose (discrepancies a b n)) + logSlack (C₂ + c₁) n : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hreal
  linarith

/-- The one-sided form of Lemma 2, relativized: if `ρ(a, b) < ε` and `ε ≤ 1/2`, then
`dim^A a ≤ dim^A b + H(ε)`. -/
private lemma abs_oraclePrefixDim_sub_le_dim_le_add (A : Set ℕ) {a b : CantorSeq} {ε : ℝ}
    (hε : ε ≤ 1 / 2) (hρ : besicovitchDist a b < ε) :
    oraclePrefixDim A a ≤ oraclePrefixDim A b + binaryEntropy ε := by
  unfold oraclePrefixDim
  obtain ⟨C, hC⟩ := abs_oraclePrefixDim_sub_le_prefix_le A
  obtain ⟨c_lin, hc_lin⟩ := abs_oraclePrefixDim_sub_le_linear_bound A
  have hdens := abs_effectiveHausdorffDim_sub_le_eventually_discrepancies_lt hρ
  have hε0 : 0 < ε := by
    obtain ⟨n, hn, hn1⟩ := (hdens.and (eventually_gt_atTop 0)).exists
    have h0 : (0 : ℝ) ≤ discrepancies a b n := Nat.cast_nonneg _
    have hn1' : (0 : ℝ) < n := by exact_mod_cast hn1
    by_contra hneg
    have hneg' : ε ≤ 0 := not_lt.1 hneg
    nlinarith
  have hbound : ∀ n : ℕ,
      (KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat ≤ 2 * n + c_lin := by
    intro n
    have h := hc_lin (cantorPrefix b n)
    simpa only [cantorPrefix_length] using h
  refine abs_effectiveHausdorffDim_sub_le_liminf_le_liminf_add
    (fun n => ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix a n)).toNat : ℝ) / n)
    (fun n => ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat : ℝ) / n)
    (fun n => (1 + (logSlack C n : ℝ)) / n) (binaryEntropy ε) ?_ ?_ ?_ ?_
  · intro n
    positivity
  · refine ⟨2 + c_lin, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [CharP.cast_eq_zero, div_zero]
      positivity
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos
      have h1 : ((KPPlain (PointToSet.optimalOraclePrefix A)
          (cantorPrefix b n)).toNat : ℝ) ≤ 2 * n + c_lin := by
        exact_mod_cast hbound n
      have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      have h3 : (0 : ℝ) ≤ c_lin := Nat.cast_nonneg _
      change ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat : ℝ) / n ≤
        2 + c_lin
      rw [div_le_iff₀ hnpos]
      nlinarith
  · have h := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add
      (PointToSet.normalized_additive_slack_logSlack C)
    rw [add_zero] at h
    exact h.congr fun n => (add_div _ _ _).symm
  · filter_upwards [hdens, eventually_gt_atTop 0] with n hn hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 := hC a b n
    have h2 := abs_effectiveHausdorffDim_sub_le_size_choose_le hε0 hε hn.le
    have hkey : ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix a n)).toNat : ℝ) ≤
        ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat : ℝ) +
          n * binaryEntropy ε + (1 + (logSlack C n : ℝ)) := by linarith
    change ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix a n)).toNat : ℝ) / n ≤
      ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat : ℝ) / n +
        binaryEntropy ε + (1 + (logSlack C n : ℝ)) / n
    calc ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix a n)).toNat : ℝ) / n
        ≤ (((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat : ℝ) +
            n * binaryEntropy ε + (1 + (logSlack C n : ℝ))) / n :=
          div_le_div_of_nonneg_right hkey hnpos.le
      _ = ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix b n)).toNat : ℝ) / n +
            binaryEntropy ε + (1 + (logSlack C n : ℝ)) / n := by
          field_simp

/-- Lemma 2 relativized. -/
theorem abs_oraclePrefixDim_sub_le (A : Set ℕ) {a b : CantorSeq} {ε : ℝ} (hε : ε ≤ 1 / 2)
    (hρ : besicovitchDist a b < ε) :
    |oraclePrefixDim A a - oraclePrefixDim A b| ≤ binaryEntropy ε := by
  have h1 := abs_oraclePrefixDim_sub_le_dim_le_add A hε hρ
  have hρ' : besicovitchDist b a < ε := by
    rwa [abs_effectiveHausdorffDim_sub_le_besicovitchDist_comm] at hρ
  have h2 := abs_oraclePrefixDim_sub_le_dim_le_add A hε hρ'
  rw [abs_le]
  constructor <;> linarith



/-- The prefix of the constant sequence is a replicated list. -/
private lemma oraclePrefixDim_extremes_constant_prefix (n : ℕ) :
    cantorPrefix (fun _ => false) n = List.replicate n false := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [cantorPrefix_getElem]
    simp

/-- A logarithmic bound for the complexity of the constant sequence prefixes. -/
private lemma oraclePrefixDim_extremes_constant_bound (A : Set ℕ) :
    ∃ c : ℕ, ∀ n : ℕ,
      (KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix (fun _ => false) n)).toNat ≤
        2 * (Nat.bits n).length + c := by
  obtain ⟨U₀, hU₀⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := abs_oraclePrefixDim_sub_le_transfer A hU₀
  have hg : Computable (fun s : BitString => List.replicate (decodeBits s) false) :=
    (Primrec.list_replicate.comp primrec_decodeBits (Primrec.const false)).to_comp
  obtain ⟨c₂, hc₂⟩ := KPPlain_map_le U₀ hU₀ _ hg
  obtain ⟨c₃, hc₃⟩ := KPPlain_le_two_mul_length U₀ hU₀
  refine ⟨c₃ + c₂ + c₁, fun n => ?_⟩
  have hrep : cantorPrefix (fun _ => false) n =
      (fun s : BitString => List.replicate (decodeBits s) false) (Nat.bits n) := by
    rw [oraclePrefixDim_extremes_constant_prefix]
    simp
  have h : KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix (fun _ => false) n) ≤
      ((2 * (Nat.bits n).length + (c₃ + c₂ + c₁) : ℕ) : ℕ∞) := by
    rw [hrep]
    calc _ ≤ KPPlain U₀ _ + (c₁ : ℕ∞) := hc₁ _
      _ ≤ (KPPlain U₀ (Nat.bits n) + (c₂ : ℕ∞)) + (c₁ : ℕ∞) := by
          gcongr
          exact hc₂ _
      _ ≤ ((2 * (Nat.bits n).length : ℕ∞) + (c₃ : ℕ∞) + (c₂ : ℕ∞)) + (c₁ : ℕ∞) := by
          gcongr
          exact hc₃ _
      _ = _ := by push_cast; ring
  have := ENat.toNat_le_toNat h (ENat.natCast_ne_top _)
  rwa [ENat.toNat_natCast] at this

/-- `(2 |bits n| + c) / n → 0`. -/
private lemma oraclePrefixDim_extremes_constant_tendsto (c : ℕ) :
    Tendsto (fun n : ℕ => ((2 * (Nat.bits n).length + c : ℕ) : ℝ) / n) atTop (nhds 0) := by
  have h1 : Tendsto (fun m : ℕ => Real.logb 2 ((m : ℝ) + 2) / (m : ℝ)) atTop (nhds 0) := by
    have := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 (-2) 1 one_ne_zero)
    have h2 := this.comp (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    refine h2.congr (fun m => ?_)
    simp
  have h3 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h4 : Tendsto (fun n : ℕ => 2 * (Real.logb 2 ((n : ℝ) + 2) / n) + (2 + c) * ((1 : ℝ) / n))
      atTop (nhds 0) := by
    simpa using (h1.const_mul 2).add (h3.const_mul (2 + c : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h4 (fun n => ?_) (fun n => ?_)
  · positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      have hb := PointToSet.length_bits_le_logb_add_one n
      have hl : Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 ((n : ℝ) + 2) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
      rw [div_le_iff₀ hnr]
      have : 2 * (Real.logb 2 ((n : ℝ) + 2) / n) * n = 2 * Real.logb 2 ((n : ℝ) + 2) := by
        field_simp
      have h5 : (2 + (c : ℝ)) * (1 / (n : ℝ)) * n = 2 + c := by field_simp
      push_cast
      nlinarith

/-- Step 1 of the proof of `oraclePrefixDim_extremes`: the plain Kolmogorov complexity of
a constant sequence is bounded, leading to an effective Hausdorff dimension of 0. -/
private lemma oraclePrefixDim_extremes_constant (A : Set ℕ) :
    oraclePrefixDim A (fun _ => false) = 0 := by
  obtain ⟨c, hc⟩ := oraclePrefixDim_extremes_constant_bound A
  have hlim : Tendsto (fun n : ℕ =>
      ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix (fun _ => false) n)).toNat : ℝ)
        / n) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (oraclePrefixDim_extremes_constant_tendsto c) (fun n => ?_) (fun n => ?_)
    · positivity
    · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hc n)) (Nat.cast_nonneg n)
  unfold oraclePrefixDim
  exact hlim.liminf_eq

/-- `|Nat.bits n| / n → 0`. -/
private lemma oraclePrefixDim_extremes_random_tendsto_bits :
    Tendsto (fun n : ℕ => ((Nat.bits n).length : ℝ) / n) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.logb 2 x ^ 1 / (1 * x + -2)) atTop (nhds 0) :=
    Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 (-2) 1 one_ne_zero
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have h3 := h1.comp h2
  have h4 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have h5 := h3.add h4
  rw [add_zero] at h5
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h5 ?_ ?_
  · exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hb := PointToSet.length_bits_le_logb_add_one n
    have hl : Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 ((n : ℝ) + 2) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
    simp only [Function.comp, one_mul, pow_one]
    have : (n : ℝ) + 2 + -2 = n := by ring
    rw [this, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hn'.le

/-- Upper bound: `K^A(x) ≤ |x| + 2 |Nat.bits |x|| + C`. -/
private lemma oraclePrefixDim_extremes_random_upper (A : Set ℕ) :
    ∃ C : ℕ, ∀ x : BitString,
      (KPPlain (PointToSet.optimalOraclePrefix A) x).toNat ≤
        x.length + 2 * (Nat.bits x.length).length + C := by
  obtain ⟨U₀, hU₀⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := abs_oraclePrefixDim_sub_le_transfer A hU₀
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_length_add_log U₀ hU₀
  refine ⟨c₂ + c₁, fun x => ?_⟩
  have h : KPPlain (PointToSet.optimalOraclePrefix A) x ≤
      ((x.length + 2 * (Nat.bits x.length).length + (c₂ + c₁) : ℕ) : ℕ∞) := by
    calc KPPlain (PointToSet.optimalOraclePrefix A) x ≤ KPPlain U₀ x + (c₁ : ℕ∞) := hc₁ x
      _ ≤ ((x.length : ℕ∞) + 2 * ((Nat.bits x.length).length : ℕ∞) + (c₂ : ℕ∞)) + (c₁ : ℕ∞) := by
          gcongr
          exact hc₂ x
      _ = ((x.length + 2 * (Nat.bits x.length).length + (c₂ + c₁) : ℕ) : ℕ∞) := by
          push_cast
          ring
  have := ENat.toNat_le_toNat h (ENat.natCast_ne_top _)
  rwa [ENat.toNat_natCast] at this

/-- Step 2 of the proof of `oraclePrefixDim_extremes`: a Martin-Löf random sequence
relative to an oracle has effective Hausdorff dimension 1. -/
private lemma oraclePrefixDim_extremes_random (A : Set ℕ) :
    ∃ w, oraclePrefixDim A w = 1 := by
  obtain ⟨c, hc⟩ := PointToSet.exists_complex_digit_sequence
  obtain ⟨ξ, hξ⟩ := hc A
  obtain ⟨C, hC⟩ := oraclePrefixDim_extremes_random_upper A
  refine ⟨ξ, ?_⟩
  unfold oraclePrefixDim
  have hbits := oraclePrefixDim_extremes_random_tendsto_bits
  have hCn : Tendsto (fun n : ℕ => (C : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)
  have hcn : Tendsto (fun n : ℕ => (c : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (c : ℝ)
  have hlow : Tendsto (fun n : ℕ => 1 - (c : ℝ) / n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hcn
  have hup : Tendsto (fun n : ℕ => 1 + (2 * (((Nat.bits n).length : ℝ) / n) + (C : ℝ) / n))
      atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((hbits.const_mul 2).add hCn)
    simpa using this
  apply Filter.Tendsto.liminf_eq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (n : ℝ) ≤
        ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix ξ n)).toNat : ℝ) + c := by
      exact_mod_cast hξ n
    rw [le_div_iff₀ hn']
    have : (1 - (c : ℝ) / n) * n = n - c := by field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := hC (cantorPrefix ξ n)
    rw [cantorPrefix_length] at h1
    have h2 : ((KPPlain (PointToSet.optimalOraclePrefix A) (cantorPrefix ξ n)).toNat : ℝ) ≤
        n + 2 * ((Nat.bits n).length : ℝ) + C := by exact_mod_cast h1
    rw [div_le_iff₀ hn']
    have : (1 + (2 * (((Nat.bits n).length : ℝ) / n) + (C : ℝ) / n)) * n =
        n + 2 * ((Nat.bits n).length : ℝ) + C := by
      field_simp
      ring
    linarith

/-- **SUV p. 260.**  Relative to any oracle, the constant sequence has dimension `0` and some
sequence has dimension `1`: the two ends of the proof of Theorem 165. -/
theorem oraclePrefixDim_extremes (A : Set ℕ) :
    oraclePrefixDim A (fun _ => false) = 0 ∧ ∃ w, oraclePrefixDim A w = 1 := by
  exact ⟨oraclePrefixDim_extremes_constant A, oraclePrefixDim_extremes_random A⟩


/-- Step 1 of the proof of `not_isBesicovitchTransitive_of_isCantorLipschitz`: if `f` is
Besicovitch transitive and `f` is computable lipschitz relative to `A`, then the bounds on dimension
imply `1 ≤ 0`, a contradiction. -/
private lemma not_isBesicovitchTransitive_of_isCantorLipschitz_step1
    {f : CantorSeq → CantorSeq}
    (A : Set ℕ)
    (h_trans : IsBesicovitchTransitive f)
    (h_extremes : oraclePrefixDim A (fun _ => false) = 0 ∧ ∃ w, oraclePrefixDim A w = 1)
    (h_le : ∀ (w : CantorSeq), oraclePrefixDim A (f w) ≤ oraclePrefixDim A w)
    (h_sub : ∀ (a b : CantorSeq), ∀ ε : ℝ, ε ≤ 1 / 2 → besicovitchDist a b < ε →
      |oraclePrefixDim A a - oraclePrefixDim A b| ≤ binaryEntropy ε) :
    False := by
  have hcont : Continuous binaryEntropy := by
    unfold binaryEntropy negMulLog2
    have := Real.continuous_negMulLog
    fun_prop
  have h0 : binaryEntropy 0 = 0 := by simp [binaryEntropy, negMulLog2]
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (1 / 2) (by norm_num)
  set ε : ℝ := min (δ / 2) (1 / 2) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε2 : ε ≤ 1 / 2 := min_le_right _ _
  have hHε : binaryEntropy ε < 1 / 2 := by
    have h := hδ' (x := ε) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hεpos]
      have : ε ≤ δ / 2 := min_le_left _ _
      linarith)
    rw [Real.dist_eq, h0, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  obtain ⟨w, hw⟩ := h_extremes.2
  obtain ⟨N, a', b', hb', h1, h2⟩ := h_trans (fun _ => false) w ε hεpos
  have hiter : ∀ n : ℕ, ∀ x, oraclePrefixDim A (f^[n] x) ≤ oraclePrefixDim A x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      exact (h_le _).trans (ih x)
  have e1 := abs_le.mp (h_sub _ _ ε hε2 h1)
  have e2 := abs_le.mp (h_sub _ _ ε hε2 h2)
  rw [h_extremes.1] at e1
  rw [hw] at e2
  have e3 := hiter N a'
  rw [← hb'] at e3
  linarith [e1.1, e1.2, e2.1, e2.2]

/-- **SUV Theorem 165, p. 259.**  No Lipschitz mapping, for the Cantor distance, is
Besicovitch-transitive.  In particular the left shift is not, although it is transitive for the
Cantor distance. -/
theorem not_isBesicovitchTransitive_of_isCantorLipschitz {f : CantorSeq → CantorSeq}
    (hf : IsCantorLipschitz f) : ¬ IsBesicovitchTransitive f := by
  intro h_trans
  have h_lipschitz := exists_isComputableLipschitzIn_of_isCantorLipschitz hf
  rcases h_lipschitz with ⟨A, h_lip_A⟩
  have h_extremes := oraclePrefixDim_extremes A
  have h_le : ∀ w, oraclePrefixDim A (f w) ≤ oraclePrefixDim A w :=
      fun w => oraclePrefixDim_apply_le h_lip_A w
  have h_sub : ∀ (a b : CantorSeq) (ε : ℝ), ε ≤ 1 / 2 → besicovitchDist a b < ε →
      |oraclePrefixDim A a - oraclePrefixDim A b| ≤ binaryEntropy ε :=
          fun a b ε => abs_oraclePrefixDim_sub_le A
  exact not_isBesicovitchTransitive_of_isCantorLipschitz_step1 A h_trans h_extremes h_le h_sub

end Applications
end Kolmogorov

