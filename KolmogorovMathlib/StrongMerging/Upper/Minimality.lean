import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StepWiseTotal.Reduction
import KolmogorovMathlib.StrongMerging.Upper.Tradeoff

/-!
# Enlarged-window one-sided minimality (blueprint Q02, `UpperOneSidedMinimality`)

`sublinear-merging.tex`, appendix Proposition `bp-upper-one-sided-minimality` (tex ~4109) and its
proof.  If `A` is strong-only robustly minimal (`StrongRobustMin`, S00) at the enlarged tolerance
`e + c_win S`, `S = √(n H)`, with gap `δ`, then `CT(A | B) ≤ δ + c_out S`.

The proof follows the blueprint:
1. the square-root merger `D` (H07, `exists_sqrt_merger'`) is a permitted competitor once
   `c_win ≥ 2 c_m + 1` (`S ≥ e`, `S ≥ 1`), so `C(A) < C(D) + δ`;
2. plain chain reversal and composition give
   `C(A | B) ≤ C(A) - C(D) + C(D | A) + C(D | B) + O(log n)` (`condC_le_of_common`), with all
   joint complexities `O(n)` and no `log δ` term;
3. the library's `strongSufficientStatistic_total_reduction` turns `C(A | B)` into `CT(A | B)` at
   cost `O(e + log n)` (`totalC_le_condC_of_strong`);
4. `e ≤ S`, `⌈log₂ (n + 2)⌉ ≤ H ≤ 2 S` absorb everything into `c_out S` (`rootScale_bounds`).
All constants are chosen before `n, e, x, A, B, δ`.
-/

namespace Kolmogorov.StrongMerging.Upper

/-- **The square-root scale dominates the budgets** (tex ~4150): for `n ≥ 2` and `e ≤ n`, with
`S = √(n H)`: `e ≤ S`, `1 ≤ S`, `H ≤ 2 S` and `S ≤ 2 n`. -/
theorem rootScale_bounds {n e : ℕ} (hn : 2 ≤ n) (he : e ≤ n) :
    (e : ℝ) ≤ rootScale n e ∧ 1 ≤ rootScale n e ∧ (baseBudget n e : ℝ) ≤ 2 * rootScale n e ∧
      rootScale n e ≤ 2 * n := by
  obtain ⟨hH2, hHn⟩ := baseBudget_bounds hn he
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have he' : (e : ℝ) ≤ n := by exact_mod_cast he
  have hH2' : (2 : ℝ) ≤ baseBudget n e := by exact_mod_cast hH2
  have hHn' : (baseBudget n e : ℝ) ≤ 2 * n := by exact_mod_cast hHn
  have heH : (e : ℝ) ≤ baseBudget n e := by
    exact_mod_cast (show e ≤ baseBudget n e by unfold baseBudget; omega)
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hprod : (0 : ℝ) ≤ (n : ℝ) * baseBudget n e := by positivity
  unfold rootScale
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.le_sqrt he0 hprod]
    nlinarith
  · rw [Real.le_sqrt zero_le_one hprod]
    nlinarith
  · have h : (baseBudget n e : ℝ) / 2 ≤ Real.sqrt (n * baseBudget n e) := by
      rw [Real.le_sqrt (by positivity) hprod]
      nlinarith
    linarith
  · rw [show (2 * (n : ℝ)) = Real.sqrt ((2 * n) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)

/-- **Chain reversal and composition** (Q02 proof, tex ~4135): for finite models `A, B, D` with
`C(A), C(D), C(D | A), C(D | B) ≤ N`,
`C(A | B) ≤ C(A) - C(D) + C(D | A) + C(D | B) + c log₂ (N + 2)`.  First
`C(A | D) ≤ C(A) + C(D | A) - C(D) + O(log)` by the two chain rules at `(D, A)` and `(A, D)`,
then the composition `C(A | B) ≤ C(D | B) + C(A | D) + O(log)`; every joint complexity is
`≤ 4 N + c'`, so no logarithm of `δ` or of a model's literal length appears. -/
theorem condC_le_of_common (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (N : ℝ) (A B D : Finset BitString), setC V A ≤ N → setC V D ≤ N →
      condC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode A) ≤ N →
      condC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode B) ≤ N →
        condC V (canonicalFiniteSetCode A) (canonicalFiniteSetCode B) ≤
          setC V A - setC V D + condC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode A) +
            condC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode B) +
              c * Real.logb 2 (N + 2) := by
  obtain ⟨c₁, h₁⟩ := upperComplexityChain_lower V hV
  obtain ⟨c₂, h₂⟩ := upperComplexityChain_upper V hV
  obtain ⟨c₃, h₃⟩ := upperComplexityChain_trans V hV
  obtain ⟨csw, hsw⟩ := pairC_swap_le V hV
  obtain ⟨ccr, hcr⟩ := pairC_le_crude V hV
  obtain ⟨cpl, hpl⟩ := condC_le_plainC_add V hV
  obtain ⟨k, hk⟩ := logb_affine_le 4 (ccr + cpl)
  refine ⟨c₁ * k + c₂ * k + c₃ * k + csw, fun N A B D hA hD hDA hDB => ?_⟩
  have hA' : plainC V (canonicalFiniteSetCode A) ≤ N := hA
  have hD' : plainC V (canonicalFiniteSetCode D) ≤ N := hD
  have hA0 := plainC_nonneg V (canonicalFiniteSetCode A)
  have hD0 := plainC_nonneg V (canonicalFiniteSetCode D)
  have hN0 : 0 ≤ N := le_trans hA0 hA'
  have hL1 := one_le_logb_add_two hN0
  have hccr : (0 : ℝ) ≤ ccr := Nat.cast_nonneg ccr
  have hcpl : (0 : ℝ) ≤ cpl := Nat.cast_nonneg cpl
  have hbound : ∀ s : ℝ, 0 ≤ s → s ≤ ((4 : ℕ) : ℝ) * N + ((ccr + cpl : ℕ) : ℝ) →
      Real.logb 2 (s + 2) ≤ k * Real.logb 2 (N + 2) := fun s hs hsN =>
    (logb_add_two_mono hs hsN).trans (hk N hN0)
  have p1 := hcr (canonicalFiniteSetCode D) (canonicalFiniteSetCode A)
  have p2 := hcr (canonicalFiniteSetCode A) (canonicalFiniteSetCode D)
  have p3 := hpl (canonicalFiniteSetCode A) (canonicalFiniteSetCode D)
  have hAD0 := condC_nonneg V (canonicalFiniteSetCode A) (canonicalFiniteSetCode D)
  have hDB0 := condC_nonneg V (canonicalFiniteSetCode D) (canonicalFiniteSetCode B)
  have l1 := hbound (pairC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode A))
    (pairC_nonneg V _ _) (by push_cast; linarith)
  have l2 := hbound (pairC V (canonicalFiniteSetCode A) (canonicalFiniteSetCode D))
    (pairC_nonneg V _ _) (by push_cast; linarith)
  have l3 := hbound (condC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode B) +
    condC V (canonicalFiniteSetCode A) (canonicalFiniteSetCode D)) (by linarith)
    (by push_cast; linarith)
  have e1 := h₁ (canonicalFiniteSetCode D) (canonicalFiniteSetCode A)
  have e2 := hsw (canonicalFiniteSetCode D) (canonicalFiniteSetCode A)
  have e3 := h₂ (canonicalFiniteSetCode A) (canonicalFiniteSetCode D)
  have e4 := h₃ (canonicalFiniteSetCode A) (canonicalFiniteSetCode D) (canonicalFiniteSetCode B)
  have m1 := mul_le_mul_of_nonneg_left l1 (Nat.cast_nonneg (α := ℝ) c₁)
  have m2 := mul_le_mul_of_nonneg_left l2 (Nat.cast_nonneg (α := ℝ) c₂)
  have m3 := mul_le_mul_of_nonneg_left l3 (Nat.cast_nonneg (α := ℝ) c₃)
  have hcsw : (csw : ℝ) ≤ csw * Real.logb 2 (N + 2) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hL1
  change condC V (canonicalFiniteSetCode A) (canonicalFiniteSetCode B) ≤
    plainC V (canonicalFiniteSetCode A) - plainC V (canonicalFiniteSetCode D) +
      condC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode A) +
        condC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode B) +
          ((c₁ * k + c₂ * k + c₃ * k + csw : ℕ) : ℝ) * Real.logb 2 (N + 2)
  push_cast
  nlinarith

/-- **Strong sufficient statistics reduce totally** (blueprint Q02 obligation: instantiate
`strongSufficientStatistic_total_reduction`): if `A` is `e`-strong and `e`-sufficient and `B` is
`e`-sufficient for an `n`-bit `x`, then `CT(A | B) ≤ C(A | B) + c e + c ⌈log₂ (n + 2)⌉`, from the
library's `strongSufficientStatistic_total_reduction` at the canonical total interpreter (S01)
and the integer-tolerance bridges of U00. -/
theorem totalC_le_condC_of_strong (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString), x.length = n →
      IsStrongModel x A e → IsSufficientModel V x A e → IsSufficientModel V x B e →
        setTotalC A B ≤ condC V (canonicalFiniteSetCode A) (canonicalFiniteSetCode B) +
          c * e + c * headerLog n := by
  obtain ⟨c, hc⟩ := strongSufficientStatistic_total_reduction V universalDecompressor hV
    isOptimalTotalConditional_universalDecompressor
  refine ⟨2 * c, fun n e x A B hx hsA hfA hfB => ?_⟩
  have hA : A.Nonempty := ⟨x, hfA.1⟩
  have hB : B.Nonempty := ⟨x, hfB.1⟩
  have h := hc x n e A B hA hB hx ((isSufficientModel_natCast_iff V hV x A hA e).1 hfA)
    ((isSufficientModel_natCast_iff V hV x B hB e).1 hfB)
    ((isStrongModel_natCast_iff x A hA e).1 hsA)
  rw [← canonicalFiniteSetCode_eq_codedUniformOn_code A hA,
    ← canonicalFiniteSetCode_eq_codedUniformOn_code B hB] at h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp
    (condK_ne_top_of_optimal V hV (canonicalFiniteSetCode A) (canonicalFiniteSetCode B))
  have h1 : totalCondK universalDecompressor (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)
      ≤ ((k + (c * e + logSlack c n) : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact h
  have h2 := toNat_le_of_le_natCast h1
  have h3 : condC V (canonicalFiniteSetCode A) (canonicalFiniteSetCode B) = k := by
    rw [condC, ← hk, ENat.toNat_natCast]
  have hsize : (Nat.bits n).length ≤ headerLog n := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact lt_of_lt_of_le (by omega) (Nat.le_pow_clog one_lt_two (n + 2))
  have hl1 := one_le_headerLog n
  have hslack : logSlack c n ≤ 2 * c * headerLog n := by
    unfold logSlack
    have := Nat.mul_le_mul_left c hsize
    have := Nat.mul_le_mul_left c hl1
    nlinarith
  have h2' : ((totalCondK universalDecompressor (canonicalFiniteSetCode A)
      (canonicalFiniteSetCode B)).toNat : ℝ) ≤ (k : ℝ) + c * e + logSlack c n := by
    have := (Nat.cast_le (α := ℝ)).2 h2
    push_cast at this
    linarith
  have hslack' : (logSlack c n : ℝ) ≤ 2 * c * headerLog n := by exact_mod_cast hslack
  unfold setTotalC totalC
  rw [h3]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) c, Nat.cast_nonneg (α := ℝ) e]

/-- Arithmetic of the final Q02 estimate (pure inequalities between reals). -/
theorem arith_q02 {t cab ca cd dA dB lg te th δ S H cM ct cq kl ctr : ℝ}
    (h1 : t ≤ cab + ctr * te + ctr * th) (h2 : cab ≤ ca - cd + dA + dB + cq * lg)
    (h3 : ca < cd + δ) (h4 : dA ≤ cM * S + ct) (h5 : dB ≤ cM * S + ct) (h6 : lg ≤ kl * H)
    (h7 : te ≤ S) (h8 : th ≤ H) (h9 : H ≤ 2 * S) (h10 : 1 ≤ S) (hct : 0 ≤ ct) (hcq : 0 ≤ cq)
    (hkl : 0 ≤ kl) (hctr : 0 ≤ ctr) :
    t ≤ δ + (2 * cM + 2 * ct + 2 * cq * kl + 4 * ctr + 1) * S := by
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have e1 : cq * lg ≤ cq * (kl * H) := mul_le_mul_of_nonneg_left h6 hcq
  have e2 : cq * (kl * H) ≤ cq * (kl * (2 * S)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h9 hkl) hcq
  have e3 : ctr * te ≤ ctr * S := mul_le_mul_of_nonneg_left h7 hctr
  have e4 : ctr * th ≤ ctr * (2 * S) := mul_le_mul_of_nonneg_left (h8.trans h9) hctr
  have e5 : ct ≤ ct * S := le_mul_of_one_le_right hct h10
  nlinarith

/-- **Enlarged-window one-sided minimality (blueprint Q02, `UpperOneSidedMinimality`;
Proposition `bp-upper-one-sided-minimality`).**  The frozen statement
`setTotalC_le_of_strongRobustMin` of `Statements.lean`, verbatim. -/
theorem setTotalC_le_of_strongRobustMin' (V : Map) (hV : isOptimalConditional V) :
    ∃ cwin cout : ℕ, 0 < cwin ∧ 0 < cout ∧
      ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString), IsMergingInstance V n e x A B →
        ∀ δ : ℝ, 0 ≤ δ → StrongRobustMin V x A (e + cwin * rootScale n e) δ →
          setTotalC A B ≤ δ + cout * rootScale n e := by
  obtain ⟨cM, hM⟩ := exists_sqrt_merger' V hV
  obtain ⟨cq, hq⟩ := condC_le_of_common V hV
  obtain ⟨ctr, htr⟩ := totalC_le_condC_of_strong V hV
  obtain ⟨ct, hct⟩ := condC_le_totalC_add V hV
  obtain ⟨blit, hblit⟩ := plainC_le_length_add V hV
  obtain ⟨kl, hkl⟩ := logb_le_baseBudget (3 + 2 * cM + blit + ct)
  refine ⟨2 * cM + 1, 2 * cM + 2 * ct + 2 * cq * kl + 4 * ctr + 1, by omega, by omega,
    fun n e x A B hI δ hδ hmin => ?_⟩
  have hceil : ⌈(e : ℝ)⌉₊ = e := Nat.ceil_natCast e
  obtain ⟨D, hxD, hpt, hsuf, hDA, hDB, -⟩ := hM n e x A B hI
  rw [hceil] at hpt hsuf hDA hDB
  obtain ⟨hn, -, hen, hx, hsA, hfA, -, hfB⟩ := hI
  have hen' : e ≤ n := by exact_mod_cast hen
  obtain ⟨hSe, hS1, hHS, hSn⟩ := rootScale_bounds hn hen'
  have hcM0 : (0 : ℝ) ≤ cM := Nat.cast_nonneg cM
  have hct0 : (0 : ℝ) ≤ ct := Nat.cast_nonneg ct
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hcMS : (cM : ℝ) * rootScale n e ≤ ((2 * cM + 1 : ℕ) : ℝ) * rootScale n e := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    push_cast
    linarith
  -- the merger is a permitted competitor at the enlarged tolerance
  have hDstrong : IsStrongModel x D (e + ((2 * cM + 1 : ℕ) : ℝ) * rootScale n e) := by
    have h1 : (cM : ℝ) * ((e : ℝ) + 1) ≤ cM * (2 * rootScale n e) :=
      mul_le_mul_of_nonneg_left (by linarith) hcM0
    have h2 : (cM : ℝ) * (2 * rootScale n e) ≤ ((2 * cM + 1 : ℕ) : ℝ) * rootScale n e := by
      push_cast
      nlinarith
    exact hpt.trans (by linarith)
  have hDsuff : IsSufficientModel V x D (e + ((2 * cM + 1 : ℕ) : ℝ) * rootScale n e) :=
    ⟨hxD, hsuf.trans (by linarith)⟩
  have hlt := hmin D hDstrong hDsuff
  -- complexity bounds
  have hCx : plainC V x ≤ n + blit := by
    have := hblit x
    rw [hx] at this
    exact this
  have hCA := setC_le_of_sufficient hfA
  have hCD : setC V D ≤ plainC V x + cM * rootScale n e := by
    have := logb_card_nonneg_of_mem hxD
    linarith
  have hDA' : condC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode A) ≤
      cM * rootScale n e + ct := by
    have h1 := hct (canonicalFiniteSetCode D) (canonicalFiniteSetCode A)
    have h2 : totalC (canonicalFiniteSetCode D) (canonicalFiniteSetCode A) ≤
        cM * rootScale n e := hDA
    linarith
  have hDB' : condC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode B) ≤
      cM * rootScale n e + ct := by
    have h1 := hct (canonicalFiniteSetCode D) (canonicalFiniteSetCode B)
    have h2 : totalC (canonicalFiniteSetCode D) (canonicalFiniteSetCode B) ≤
        cM * rootScale n e := hDB
    linarith
  have hS0 : (0 : ℝ) ≤ cM * rootScale n e := by positivity
  have hq' := hq ((n : ℝ) + blit + e + cM * rootScale n e + ct) A B D (by linarith)
    (by linarith) (by linarith) (by linarith)
  have hlogN : Real.logb 2 ((n : ℝ) + blit + e + cM * rootScale n e + ct + 2) ≤
      kl * baseBudget n e := by
    refine le_trans ?_ (hkl n e)
    have hpos : (0 : ℝ) ≤ (n : ℝ) + blit + e + cM * rootScale n e + ct := by positivity
    apply Real.logb_le_logb_of_le one_lt_two (by positivity)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hcMn : (cM : ℝ) * rootScale n e ≤ cM * (2 * n) := mul_le_mul_of_nonneg_left hSn hcM0
    have hen'' : (e : ℝ) ≤ n := by exact_mod_cast hen'
    push_cast
    nlinarith
  have htr' := htr n e x A B hx hsA hfA hfB
  have hth : (headerLog n : ℝ) ≤ baseBudget n e := by
    unfold baseBudget
    push_cast
    linarith
  have hfin := arith_q02 (cq := (cq : ℝ)) htr' hq' hlt hDA' hDB' hlogN hSe hth hHS hS1 hct0
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hC : ((2 * cM + 2 * ct + 2 * cq * kl + 4 * ctr + 1 : ℕ) : ℝ) =
      2 * (cM : ℝ) + 2 * ct + 2 * cq * kl + 4 * ctr + 1 := by
    push_cast
    ring
  rw [hC]
  exact hfin

end Kolmogorov.StrongMerging.Upper
