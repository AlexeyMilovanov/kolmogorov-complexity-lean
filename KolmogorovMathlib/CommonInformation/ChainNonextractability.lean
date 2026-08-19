import KolmogorovMathlib.CommonInformation.ChainSample
import KolmogorovMathlib.CommonInformation.ChainNonextractabilityEngine
import Mathlib.Data.Nat.Choose.Central

/-!
# Chain non-extractability and Exercise 316

This file is the C7 endpoint for SUV Exercise 316 (strategy iterations 3 and 4).
It builds on the "one maximal full-chain sample" layer of `ChainSample.lean`
(`IsMaximalChainSample`, `chainWordAt`, `chain_single_projection_complexity_close`)
and the arithmetic backbone
`iterated_conditional_independence_bound_values`.

The endpoint is assembled from three kernel-checked layers:

* Numeric type bounds:
  * `balanced_binary_typeLog_lower` — the type-log lower bound
    `2 ^ N ≤ (N + 1) * multinomial (N/2, N/2)`, i.e. a balanced binary
    marginal has type-log `≥ N - O(log N)`.  It is the exact form used to show
    the bottom marginals `x`, `y` are `N`-incompressible.
  * `five_pow_twenty_mul_three_pow_twelve_ge` — the closed exponential margin
    `2 ^ 65 ≤ 5 ^ 20 * 3 ^ 12` behind the `N / 32` bottom mutual-information gap.
* Exact chain and type assembly:
  * `fiveEighths_bottom_typeLog_gap` — the pure bottom-type multinomial
    inequality giving the linear mutual-information gap;
  * `chain_sample_iterated_nonextractability` — iteration-3 engine: for a maximal
    sample of an independence chain the free string `z` obeys
    `C(z) ≤ 2 ^ k · (C(z|α₀) + C(z|β₀)) + O(log N)` (coefficient exactly `2 ^ k`).
* `exercise_316_nonextractability` assembles those inputs into the public
  denominator-aligned plain-complexity statement for one pair `x, y`.
-/

namespace Kolmogorov
open Finset

/-- The closed exponential margin behind the `N / 32` bottom mutual-information
gap of Exercise 316.  With `∏ f ^ f = N ^ N · (5/16) ^ (5N/8) · (3/16) ^ (3N/8)`,
the separation `2 ^ (N/32)` reduces to `(5 ^ 10 · 3 ^ 6) ^ 2 ≥ 2 ^ 65`. -/
theorem five_pow_twenty_mul_three_pow_twelve_ge : 2 ^ 65 ≤ 5 ^ 20 * 3 ^ 12 := by
  norm_num

/-- **Balanced binary type-log lower bound.**  The multinomial coefficient of the
balanced binary histogram `(N/2, N/2)` satisfies `2 ^ N ≤ (N + 1) · multinomial`.
Equivalently the balanced marginal type-log is `≥ N - O(log N)`, which forces the
two bottom projections `x`, `y` of the Exercise-316 sample to be `N`-incompressible
up to a logarithmic term.  Proved from the central-binomial bounds
`Nat.four_pow_le_two_mul_self_mul_centralBinom` (even `N`) and
`Nat.four_pow_lt_mul_centralBinom` (odd `N`). -/
theorem balanced_binary_typeLog_lower (N : ℕ) :
    2 ^ N ≤ (N + 1) * Nat.multinomial Finset.univ (fun _ : Bool => N / 2) := by
  have hmul : Nat.multinomial Finset.univ (fun _ : Bool => N / 2)
      = Nat.centralBinom (N / 2) := by
    rw [show (Finset.univ : Finset Bool) = {true, false} by decide,
        Nat.binomial_eq_choose (by decide : true ≠ false)]
    rw [Nat.centralBinom_eq_two_mul_choose]
    congr 1
    omega
  rw [hmul]
  rcases Nat.even_or_odd N with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- even: `N = r + r`, so `N / 2 = r`
    have hm : N / 2 = r := by omega
    rw [hm, hr]
    have hpow : 2 ^ (r + r) = 4 ^ r := by
      rw [← two_mul, pow_mul]; norm_num
    rw [hpow]
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0; decide
    · calc 4 ^ r ≤ 2 * r * Nat.centralBinom r :=
            Nat.four_pow_le_two_mul_self_mul_centralBinom r hpos
        _ ≤ (r + r + 1) * Nat.centralBinom r :=
            Nat.mul_le_mul (by omega) (le_refl _)
  · -- odd: `N = 2 * r + 1`, so `N / 2 = r`
    have hm : N / 2 = r := by omega
    rw [hm, hr]
    have hpow : 2 ^ (2 * r + 1) = 2 * 4 ^ r := by
      rw [pow_succ, pow_mul]; ring
    rw [hpow]
    have hcore : 4 ^ r ≤ (r + 1) * Nat.centralBinom r := by
      rcases Nat.lt_or_ge r 4 with hlt | hge
      · interval_cases r <;> decide
      · calc 4 ^ r ≤ r * Nat.centralBinom r :=
              (Nat.four_pow_lt_mul_centralBinom r hge).le
          _ ≤ (r + 1) * Nat.centralBinom r :=
              Nat.mul_le_mul (by omega) (le_refl _)
    calc 2 * 4 ^ r ≤ 2 * ((r + 1) * Nat.centralBinom r) :=
          Nat.mul_le_mul (le_refl _) hcore
      _ = (2 * r + 1 + 1) * Nat.centralBinom r := by ring

/-- Any bottom coordinate with a uniform marginal contributes the balanced
histogram `(N / 2, N / 2)`.  This is the index-generic form of
`fiveEighths_bottom_histogram1`, needed for the `beta` coordinate as well. -/
private lemma bottom_histogram1_of_half {N : ℕ} {D : ChainDist 1}
    (hQ : D.RationalAtoms 32) (j : Fin (2 * 1 + 2))
    (h_half : ∀ a, D.prAt j a = 1 / 2) (hdiv : 32 ∣ N) (a : Bool) :
    chainHistogram1 D hQ N j a = N / 2 := by
  have H := chainMarginal_eq_nat_of_pr D hQ (fun v => v j == a)
    (q := 2) (m := 1) (by norm_num) hdiv
    (by
      obtain ⟨c, hc⟩ := hdiv
      exact ⟨16 * c, by omega⟩)
    (by
      have h1 : D.pr (fun v => v j == a) = D.prAt j a := rfl
      rw [h1, h_half a]
      norm_num)
  unfold chainHistogram1
  rw [H]
  omega

/-- **Method-of-types bound for the `5 / 8` joint bottom type.**  The joint
histogram `(10u, 6u, 6u, 10u)` with total mass `32u` has multinomial coefficient
at most `2 ^ (63 u)`, i.e. entropy rate `63 / 32` bits per symbol instead of the
`2` bits of the independent product type.  The `1 / 32` deficit is exactly the
`2 ^ 65 ≤ 5 ^ 20 · 3 ^ 12` margin. -/
theorem fiveEighths_joint_multinomial_le (u : ℕ) :
    Nat.multinomial (Finset.univ : Finset (Bool × Bool))
        (fun p => if p.1 = p.2 then 10 * u else 6 * u) ≤ 2 ^ (63 * u) := by
  set g : Bool × Bool → ℕ := fun p => if p.1 = p.2 then 10 * u else 6 * u with hg
  have hsum : ∑ p, g p = 32 * u := by
    simp [hg, Fintype.sum_prod_type]
    ring
  have hprod : ∏ p, g p ^ g p = (10 * u) ^ (20 * u) * (6 * u) ^ (12 * u) := by
    simp [hg, Fintype.prod_prod_type, ← pow_add]
    ring_nf
  have key := multinomial_mul_prod_pow_self_le g
  rw [hsum, hprod] at key
  have h10 : (10 : ℕ) ^ (20 * u) = 2 ^ (20 * u) * 5 ^ (20 * u) := by
    rw [← mul_pow]; norm_num
  have h6 : (6 : ℕ) ^ (12 * u) = 2 ^ (12 * u) * 3 ^ (12 * u) := by
    rw [← mul_pow]; norm_num
  have h2 : (2 : ℕ) ^ (20 * u) * 2 ^ (12 * u) = 2 ^ (32 * u) := by
    rw [← pow_add]; ring_nf
  have hu32 : u ^ (20 * u) * u ^ (12 * u) = u ^ (32 * u) := by
    rw [← pow_add]; ring_nf
  have hL : (10 * u) ^ (20 * u) * (6 * u) ^ (12 * u)
      = 2 ^ (32 * u) * (5 ^ (20 * u) * 3 ^ (12 * u)) * u ^ (32 * u) := by
    rw [mul_pow, mul_pow, h10, h6, ← h2, ← hu32]; ring
  have hR : (32 * u) ^ (32 * u) = 2 ^ (160 * u) * u ^ (32 * u) := by
    rw [mul_pow, show (32 : ℕ) = 2 ^ 5 from rfl, ← pow_mul]
    ring_nf
  rw [hL, hR, ← mul_assoc] at key
  have hupos : 0 < u ^ (32 * u) := by
    rcases Nat.eq_zero_or_pos u with rfl | h
    · simp
    · exact Nat.pow_pos h
  have key2 : Nat.multinomial Finset.univ g *
      (2 ^ (32 * u) * (5 ^ (20 * u) * 3 ^ (12 * u))) ≤ 2 ^ (160 * u) := by
    have h := Nat.le_of_mul_le_mul_right key hupos
    simpa [mul_assoc] using h
  have hA : 2 ^ (65 * u) ≤ 5 ^ (20 * u) * 3 ^ (12 * u) := by
    have h := Nat.pow_le_pow_left five_pow_twenty_mul_three_pow_twelve_ge u
    calc 2 ^ (65 * u) = ((2 : ℕ) ^ 65) ^ u := by rw [← pow_mul]
      _ ≤ (5 ^ 20 * 3 ^ 12) ^ u := h
      _ = 5 ^ (20 * u) * 3 ^ (12 * u) := by rw [mul_pow, ← pow_mul, ← pow_mul]
  have key3 : Nat.multinomial Finset.univ g * 2 ^ (97 * u) ≤ 2 ^ (160 * u) := by
    refine le_trans ?_ key2
    have hstep : (2 : ℕ) ^ (97 * u)
        ≤ 2 ^ (32 * u) * (5 ^ (20 * u) * 3 ^ (12 * u)) := by
      calc (2 : ℕ) ^ (97 * u) = 2 ^ (32 * u) * 2 ^ (65 * u) := by
            rw [← pow_add]; ring_nf
        _ ≤ 2 ^ (32 * u) * (5 ^ (20 * u) * 3 ^ (12 * u)) := Nat.mul_le_mul_left _ hA
    exact Nat.mul_le_mul_left _ hstep
  have hsplit : (2 : ℕ) ^ (160 * u) = 2 ^ (63 * u) * 2 ^ (97 * u) := by
    rw [← pow_add]; ring_nf
  rw [hsplit] at key3
  exact Nat.le_of_mul_le_mul_right key3 (Nat.pow_pos (by norm_num))

/-- The pure method-of-types inequality for the concrete `5 / 8` bottom
distribution. This is the multinomial arithmetic behind the linear
mutual-information gap; it contains no complexity assumptions. -/
theorem fiveEighths_bottom_typeLog_gap :
    ∃ C : ℕ, ∀ (D : ChainDist 1) (hQ : D.RationalAtoms 32)
      (_hAlpha : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
      (_hBeta : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
      (_hAgree : D.prAgree01 = 5 / 8) (N : ℕ), 32 ∣ N →
      histogramTypeLog (fun p : Bool × Bool =>
          chainHistogram2 D hQ N (chainAlphaIdx 0) (chainBetaIdx 0) p.1 p.2) +
        N / 32 ≤
      histogramTypeLog (fun a => chainHistogram1 D hQ N (chainAlphaIdx 0) a) +
        histogramTypeLog (fun b => chainHistogram1 D hQ N (chainBetaIdx 0) b) +
        logSlack C (N + 1) := by
  refine ⟨2, ?_⟩
  intro D hQ hAlpha hBeta hAgree N hdiv
  have hN : N = 32 * (N / 32) := by omega
  set u := N / 32 with hu
  have hjoint : (fun p : Bool × Bool =>
      chainHistogram2 D hQ N (chainAlphaIdx 0) (chainBetaIdx 0) p.1 p.2)
      = fun p : Bool × Bool => if p.1 = p.2 then 10 * u else 6 * u := by
    funext p
    exact fiveEighths_bottom_histogram2 hQ hAgree hAlpha hBeta hdiv p.1 p.2
  have halpha : (fun a => chainHistogram1 D hQ N (chainAlphaIdx 0) a)
      = fun _ : Bool => N / 2 :=
    funext fun a => bottom_histogram1_of_half hQ _ hAlpha hdiv a
  have hbeta : (fun b => chainHistogram1 D hQ N (chainBetaIdx 0) b)
      = fun _ : Bool => N / 2 :=
    funext fun b => bottom_histogram1_of_half hQ _ hBeta hdiv b
  rw [hjoint, halpha, hbeta]
  unfold histogramTypeLog logSlack
  set M := Nat.multinomial (Finset.univ : Finset (Bool × Bool))
      (fun p => if p.1 = p.2 then 10 * u else 6 * u) with hM
  set B := Nat.multinomial (Finset.univ : Finset Bool) (fun _ : Bool => N / 2) with hB
  have hMpos : M ≠ 0 := Nat.multinomial_pos _ _ |>.ne'
  have hMle : M * 2 ^ u ≤ ((N + 1) * B) * ((N + 1) * B) := by
    have h1 : M * 2 ^ u ≤ 2 ^ (63 * u) * 2 ^ u :=
      Nat.mul_le_mul_right _ (fiveEighths_joint_multinomial_le u)
    have h2 : (2 : ℕ) ^ (63 * u) * 2 ^ u = 2 ^ N * 2 ^ N := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have h3 : (2 : ℕ) ^ N * 2 ^ N ≤ ((N + 1) * B) * ((N + 1) * B) :=
      Nat.mul_le_mul (balanced_binary_typeLog_lower N) (balanced_binary_typeLog_lower N)
    omega
  have hsize : Nat.size M + u ≤ Nat.size (N + 1) + Nat.size B +
      (Nat.size (N + 1) + Nat.size B) := by
    have e1 : Nat.size M + u = Nat.size (M * 2 ^ u) := (size_mul_two_pow hMpos u).symm
    have e2 : Nat.size (M * 2 ^ u) ≤ Nat.size (((N + 1) * B) * ((N + 1) * B)) :=
      Nat.size_le_size hMle
    have e3 : Nat.size (((N + 1) * B) * ((N + 1) * B))
        ≤ Nat.size ((N + 1) * B) + Nat.size ((N + 1) * B) :=
      size_mul_le _ _
    have e4 : Nat.size ((N + 1) * B) ≤ Nat.size (N + 1) + Nat.size B := size_mul_le _ _
    omega
  have hbits : (Nat.bits (N + 1)).length = Nat.size (N + 1) := Nat.size_eq_bits_len _
  rw [hbits]
  omega

/-- The direct bottom-type half of Exercise 316. For the concrete `5 / 8`
chain, the bottom projections of the same maximal full-chain sample have a
linear plain mutual-information gap. -/
theorem fiveEighths_sample_mutualInformation_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (D : ChainDist 1) (hQ : D.RationalAtoms 32)
      (_hAlpha : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
      (_hBeta : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
      (_hAgree : D.prAgree01 = 5 / 8) (N : ℕ) (_hdiv : 32 ∣ N)
      (W : List (Fin 4 → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∃ kx ky kxy,
        HasPlainComplexityValue V
          (chainWordAt (k := 1) W (chainAlphaIdx (k := 1) 0)) kx ∧
        HasPlainComplexityValue V
          (chainWordAt (k := 1) W (chainBetaIdx (k := 1) 0)) ky ∧
        HasPlainComplexityValue V
          (pairCode (chainWordAt (k := 1) W (chainAlphaIdx (k := 1) 0))
            (chainWordAt (k := 1) W (chainBetaIdx (k := 1) 0))) kxy ∧
        kxy + N / 32 ≤ kx + ky + logSlack C (N + 1) := by
  obtain ⟨cType, hType⟩ := fiveEighths_bottom_typeLog_gap
  obtain ⟨cSingle, hSingle⟩ := chain_single_projection_complexity_close V hV 1
  obtain ⟨cPair, hPair⟩ := chain_pair_projection_complexity_close V hV 1
  refine ⟨cType + 2 * cSingle + cPair, ?_⟩
  intro D hQ hAlpha hBeta hAgree N hdiv W kW hsample
  obtain ⟨kx, hx, hAlphaLower, _hAlphaUpper⟩ :=
    hSingle D 32 N hQ hdiv W kW hsample (chainAlphaIdx 0)
  obtain ⟨ky, hy, hBetaLower, _hBetaUpper⟩ :=
    hSingle D 32 N hQ hdiv W kW hsample (chainBetaIdx 0)
  obtain ⟨kxy, hxy, _hPairLower, hPairUpper⟩ :=
    hPair D 32 N hQ hdiv W kW hsample (chainAlphaIdx 0) (chainBetaIdx 0)
  refine ⟨kx, ky, kxy, hx, hy, hxy, ?_⟩
  have hgap := hType D hQ hAlpha hBeta hAgree N hdiv
  have hfold : logSlack cType (N + 1) + 2 * logSlack cSingle (N + 1) +
      logSlack cPair (N + 1) =
        logSlack (cType + 2 * cSingle + cPair) (N + 1) := by
    unfold logSlack
    ring
  omega

/-- **Iteration-3 engine.**  For one maximal sample `W` of an
`IsIndep315Chain` with rational atoms and `Q ∣ N`, every string `z` obeys the
iterated non-extractability bound with coefficient exactly `2 ^ k`:
`C(z) ≤ 2 ^ k · (C(z | α₀) + C(z | β₀)) + O(log N)`, the constant depending only
on `k`.  Proof route: convert each `chain_link_mutualInformation_defect` /
`chain_top_mutualInformation_defect` to complexity form on the *same* `W`, apply
`base_conditional_mutualInformation_inequality` per link, and close with
`iterated_conditional_independence_bound_values`. -/
theorem chain_sample_iterated_nonextractability (V : Map)
    (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q : ℕ) (hQ : D.RationalAtoms Q) (N : ℕ)
      (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      Q ∣ N → D.IsIndep315Chain →
      IsMaximalChainSample V D hQ N W kW →
      ∀ z kz kzx kzy,
        HasPlainComplexityValue V z kz →
        HasPlainConditionalComplexityValue V z
          (chainWordAt W (chainAlphaIdx 0)) kzx →
        HasPlainConditionalComplexityValue V z
          (chainWordAt W (chainBetaIdx 0)) kzy →
        kz ≤ 2 ^ k * (kzx + kzy) + logSlack (2 ^ k * C) (N + 1) := by
  obtain ⟨E, hE⟩ := large_complexity_case V hV
  obtain ⟨A1, B1, hLin1⟩ := chain_projection_value_le_linear_N V hV k
  obtain ⟨Cl, hl⟩ := chain_link_condK_step V hV k (8 * A1) (E + 8 * B1)
  obtain ⟨Ct, ht⟩ := chain_top_condK_step V hV k (8 * A1) (E + 8 * B1)
  refine ⟨2 * Cl + Ct, ?_⟩
  intro D Q hQ N W kW hdiv hchain hsample z kz kzx kzy hkz hkzx hkzy
  set C := 2 * Cl + Ct with hCdef
  have hex : ∀ u : BitString, ∃ m, HasPlainConditionalComplexityValue V z u m :=
    fun u => exists_plainConditionalComplexityValue V hV z u
  choose f hf using hex
  have hfval : ∀ (u : BitString) (m : ℕ),
      HasPlainConditionalComplexityValue V z u m → f u = m := by
    intro u m hm
    have h : ((f u : ℕ) : ENat) = (m : ENat) := (hf u).symm.trans hm
    exact_mod_cast h
  obtain ⟨kx, hkx⟩ :=
    exists_plainComplexityValue V hV (chainWordAt W (chainAlphaIdx (0 : Fin (k + 1))))
  obtain ⟨ky, hky⟩ :=
    exists_plainComplexityValue V hV (chainWordAt W (chainBetaIdx (0 : Fin (k + 1))))
  have hlinx : kx ≤ A1 * N + B1 := hLin1 D Q N hQ hdiv W kW hsample _ kx hkx
  have hliny : ky ≤ A1 * N + B1 := hLin1 D Q N hQ hdiv W kW hsample _ ky hky
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  by_cases hbig : E + 4 * (kx + ky) ≤ kz
  · have hsmallgoal :=
      hE (chainWordAt W (chainAlphaIdx (0 : Fin (k + 1))))
        (chainWordAt W (chainBetaIdx (0 : Fin (k + 1)))) z kz kzx kzy kx ky
        hkz hkzx hkzy hkx hky hbig
    have hmul : kzx + kzy ≤ 2 ^ k * (kzx + kzy) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have hprod : 8 * A1 * N = 8 * (A1 * N) := by ring
    have hkzlin : kz ≤ 8 * A1 * N + (E + 8 * B1) := by omega
    have hidx_cast : ∀ (i : ℕ) (hi : i < k),
        (⟨min i k, by omega⟩ : Fin (k + 1)) = (⟨i, hi⟩ : Fin k).castSucc := by
      intro i hi
      apply Fin.ext
      simp only [Fin.val_castSucc]
      omega
    have hidx_succ : ∀ (i : ℕ) (hi : i < k),
        (⟨min (i + 1) k, by omega⟩ : Fin (k + 1)) = (⟨i, hi⟩ : Fin k).succ := by
      intro i hi
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    have hidx_last : (⟨min k k, by omega⟩ : Fin (k + 1)) = Fin.last k := by
      apply Fin.ext
      simp
    have hidx_zero : (⟨min 0 k, by omega⟩ : Fin (k + 1)) = (0 : Fin (k + 1)) := by
      apply Fin.ext
      simp
    have hslackl : logSlack Cl (N + 1) + logSlack Cl (N + 1) ≤ logSlack C (N + 1) := by
      have heq : logSlack Cl (N + 1) + logSlack Cl (N + 1) = logSlack (2 * Cl) (N + 1) := by
        unfold logSlack; ring
      rw [heq]
      exact logSlack_mono_left (by omega) _
    have hslackt : logSlack Ct (N + 1) ≤ logSlack C (N + 1) :=
      logSlack_mono_left (by omega) _
    have hstep : ∀ i, i < k →
        f (chainWordAt W (chainAlphaIdx ⟨min (i + 1) k, by omega⟩)) +
            f (chainWordAt W (chainBetaIdx ⟨min (i + 1) k, by omega⟩)) ≤
          2 * (f (chainWordAt W (chainAlphaIdx ⟨min i k, by omega⟩)) +
            f (chainWordAt W (chainBetaIdx ⟨min i k, by omega⟩))) +
            logSlack C (N + 1) := by
      intro i hi
      rw [hidx_cast i hi, hidx_succ i hi]
      have hA := hchain.1 ⟨i, hi⟩
      have hB := hchain.2.1 ⟨i, hi⟩
      have h1 := hl D Q N hQ hdiv W kW hsample
        (chainAlphaIdx (⟨i, hi⟩ : Fin k).castSucc)
        (chainBetaIdx (⟨i, hi⟩ : Fin k).castSucc)
        (chainAlphaIdx (⟨i, hi⟩ : Fin k).succ) hA z kz
        (f (chainWordAt W (chainAlphaIdx (⟨i, hi⟩ : Fin k).castSucc)))
        (f (chainWordAt W (chainBetaIdx (⟨i, hi⟩ : Fin k).castSucc)))
        (f (chainWordAt W (chainAlphaIdx (⟨i, hi⟩ : Fin k).succ)))
        hkz hkzlin (hf _) (hf _) (hf _)
      have h2 := hl D Q N hQ hdiv W kW hsample
        (chainAlphaIdx (⟨i, hi⟩ : Fin k).castSucc)
        (chainBetaIdx (⟨i, hi⟩ : Fin k).castSucc)
        (chainBetaIdx (⟨i, hi⟩ : Fin k).succ) hB z kz
        (f (chainWordAt W (chainAlphaIdx (⟨i, hi⟩ : Fin k).castSucc)))
        (f (chainWordAt W (chainBetaIdx (⟨i, hi⟩ : Fin k).castSucc)))
        (f (chainWordAt W (chainBetaIdx (⟨i, hi⟩ : Fin k).succ)))
        hkz hkzlin (hf _) (hf _) (hf _)
      omega
    have htop : kz ≤
        f (chainWordAt W (chainAlphaIdx ⟨min k k, by omega⟩)) +
          f (chainWordAt W (chainBetaIdx ⟨min k k, by omega⟩)) + logSlack C (N + 1) := by
      rw [hidx_last]
      have h := ht D Q N hQ hdiv W kW hsample
        (chainAlphaIdx (Fin.last k)) (chainBetaIdx (Fin.last k)) hchain.2.2 z kz
        (f (chainWordAt W (chainAlphaIdx (Fin.last k))))
        (f (chainWordAt W (chainBetaIdx (Fin.last k))))
        hkz hkzlin (hf _) (hf _)
      omega
    have hres := iterated_conditional_independence_bound_values k C N kz
      (fun i => f (chainWordAt W (chainAlphaIdx ⟨min i k, by omega⟩)) +
        f (chainWordAt W (chainBetaIdx ⟨min i k, by omega⟩))) hstep htop
    have hres' : kz ≤ 2 ^ k * (f (chainWordAt W (chainAlphaIdx ⟨min 0 k, by omega⟩)) +
        f (chainWordAt W (chainBetaIdx ⟨min 0 k, by omega⟩))) +
        logSlack (2 ^ k * C) (N + 1) := hres
    have hzero : f (chainWordAt W (chainAlphaIdx ⟨min 0 k, by omega⟩)) +
        f (chainWordAt W (chainBetaIdx ⟨min 0 k, by omega⟩)) = kzx + kzy := by
      rw [hidx_zero, hfval _ kzx hkzx, hfval _ kzy hkzy]
    rw [hzero] at hres'
    exact hres'

/-- **Public Exercise 316.**  For every `N` with `32 ∣ N` there is a
bottom pair `x, y` of length `N` with a *linear* mutual-information gap
`I(x : y) ≥ N / 32 - O(log N)` (encoded additively as
`C(x, y) + N/32 ≤ C(x) + C(y) + O(log N)`) whose common information is
non-extractable: `C(z) ≤ 2 · (C(z | x) + C(z | y)) + O(log N)` for every `z`.
Both faces hold for the *same* `x, y` and use plain complexity throughout.
Instantiates `chain_sample_iterated_nonextractability` at the concrete `k = 1`,
`Q = 32` chain of `exists_fiveEighths_rationalAtom_chain`, with the bottom
gap discharged by `balanced_binary_typeLog_lower` and
`five_pow_twenty_mul_three_pow_twelve_ge`. -/
theorem exercise_316_nonextractability (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ N, 32 ∣ N → ∃ x y kx ky kxy,
      x.length = N ∧ y.length = N ∧
      HasPlainComplexityValue V x kx ∧ HasPlainComplexityValue V y ky ∧
      HasPlainComplexityValue V (pairCode x y) kxy ∧
      kxy + N / 32 ≤ kx + ky + logSlack C (N + 1) ∧
      ∀ z kz kzx kzy, HasPlainComplexityValue V z kz →
        HasPlainConditionalComplexityValue V z x kzx →
        HasPlainConditionalComplexityValue V z y kzy →
        kz ≤ 2 * (kzx + kzy) + logSlack C (N + 1) := by
  obtain ⟨D, hQ, hchain, hAlpha, hBeta, hAgree⟩ :=
    exists_fiveEighths_rationalAtom_chain
  obtain ⟨cIter, hIter⟩ := chain_sample_iterated_nonextractability V hV 1
  obtain ⟨cGap, hGap⟩ := fiveEighths_sample_mutualInformation_values V hV
  refine ⟨cGap + 2 * cIter, fun N hdiv => ?_⟩
  obtain ⟨W, kW, hsample⟩ := exists_maximal_chainSample V hV D hQ N hdiv
  obtain ⟨kx, ky, kxy, hx, hy, hxy, hgap⟩ :=
    hGap D hQ hAlpha hBeta hAgree N hdiv W kW hsample
  let x := chainWordAt W (chainAlphaIdx 0)
  let y := chainWordAt W (chainBetaIdx 0)
  refine ⟨x, y, kx, ky, kxy, ?_, ?_, hx, hy, hxy, ?_, ?_⟩
  · dsimp [x, chainWordAt]
    rw [List.length_map]
    exact hsample.length_eq hdiv
  · dsimp [y, chainWordAt]
    rw [List.length_map]
    exact hsample.length_eq hdiv
  · exact hgap.trans (Nat.add_le_add_left
      (logSlack_mono_left (by omega) (N + 1)) (kx + ky))
  · intro z kz kzx kzy hz hzx hzy
    have h := hIter D 32 hQ N W kW hdiv hchain hsample z kz kzx kzy hz hzx hzy
    have hslack : logSlack (2 * cIter) (N + 1) ≤
        logSlack (cGap + 2 * cIter) (N + 1) :=
      logSlack_mono_left (by omega) (N + 1)
    simpa only [pow_one, x, y] using
      h.trans (Nat.add_le_add_left hslack (2 * (kzx + kzy)))

end Kolmogorov
