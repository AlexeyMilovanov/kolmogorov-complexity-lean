import KolmogorovMathlib.InformationInequalities.Combinatorial.Partition
import KolmogorovMathlib.InformationInequalities.Combinatorial.TypizationBounds

/-!
# Combinatorial interpretation by covers (Theorem 213)

SUV Section 10.8, pp. 330–332.

An inequality `∑ λ_I C(x_I) ≤ ∑ μ_J C(x_J) + O(log N)` with positive coefficients holds if and
only if every finite set `A` is covered by sets `B_I` whose `I`-projections are at most the
prescribed sizes `n_I`, up to a polylogarithmic factor, whenever `∏ n_I^{λ_I} = ∏ m_A(J)^{μ_J}`
(`cover_iff_complexity_inequality`).  Problem 290, the version with conditional terms, is
archived in `docs/ARCHIVED_TARGETS.md`.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}
/-! ### Section 10.8: the general case -/
/-- **Weighted pigeonhole.**  From a weighted inequality `∑_I λ_I a_I ≤ ∑_I λ_I b_I` with
positive weights over a non-empty `L`, at least one coordinate satisfies `a_I ≤ b_I`.  This is
the book's step "for each element of `A` at least one term of the left-hand side is
upperbounded by the corresponding term of the right-hand side". -/
private lemma exists_le_of_weighted_sum_le {L : Finset (Finset (Fin n))} (hLne : L.Nonempty)
    {lam a b : Finset (Fin n) → ℝ} (hlam : ∀ I ∈ L, 0 < lam I)
    (h : ∑ I ∈ L, lam I * a I ≤ ∑ I ∈ L, lam I * b I) : ∃ I ∈ L, a I ≤ b I := by
  by_contra hcon
  push Not at hcon
  exact absurd h (not_le.2 (Finset.sum_lt_sum_of_nonempty hLne fun I hI =>
    mul_lt_mul_of_pos_left (hcon I hI) (hlam I hI)))

/- Passing from logarithms of the typization projections back to tuple complexities costs the
sum of the coefficient masses times the common approximation error. -/
private lemma weighted_complexity_le_of_projection_logs
    (L R : Finset (Finset (Fin n))) (lam mu : Finset (Fin n) → ℝ)
    (hlam : ∀ I ∈ L, 0 ≤ lam I) (hmu : ∀ J ∈ R, 0 ≤ mu J)
    (a p : Finset (Fin n) → ℝ) {e q : ℝ}
    (hL : ∀ I ∈ L, |p I - a I| ≤ e) (hR : ∀ J ∈ R, |p J - a J| ≤ e)
    (hlog : ∑ I ∈ L, lam I * p I ≤ ∑ J ∈ R, mu J * p J + q) :
    ∑ I ∈ L, lam I * a I ≤ ∑ J ∈ R, mu J * a J + q +
      ((∑ I ∈ L, lam I) + ∑ J ∈ R, mu J) * e := by
  have hleft : ∑ I ∈ L, lam I * a I ≤ ∑ I ∈ L, lam I * (p I + e) := by
    exact Finset.sum_le_sum fun I hI => mul_le_mul_of_nonneg_left
      (by have := (abs_le.1 (hL I hI)).1; linarith) (hlam I hI)
  have hright : ∑ J ∈ R, mu J * (p J - e) ≤ ∑ J ∈ R, mu J * a J := by
    exact Finset.sum_le_sum fun J hJ => mul_le_mul_of_nonneg_left
      (by have := (abs_le.1 (hR J hJ)).2; linarith) (hmu J hJ)
  simp_rw [mul_add] at hleft
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hleft
  simp_rw [mul_sub] at hright
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hright
  linarith

/- A weighted product of positive numbers is the base-two exponential of the corresponding
weighted sum of logarithms. -/
private lemma prod_rpow_eq_two_rpow_weighted_log (S : Finset (Finset (Fin n)))
    (w x : Finset (Fin n) → ℝ) (hx : ∀ I ∈ S, 0 < x I) :
    ∏ I ∈ S, x I ^ w I = (2 : ℝ) ^ ∑ I ∈ S, w I * Real.logb 2 (x I) := by
  rw [Real.rpow_sum_of_pos (by norm_num)]
  refine Finset.prod_congr rfl fun I hI => ?_
  rw [mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (hx I hI)]

/- A subset of a `c`-uniform set occupies at most `c` times its fraction of any projection.
This is the cardinal form of the small-fraction estimate used in the typization argument. -/
private lemma card_mul_projCard_le_of_subset_isCUniform {Y : Fin n → Type}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] {c : ℝ}
    {A C : Finset (∀ i, Y i)} (hU : IsCUniform c A) (hCA : C ⊆ A)
    (I : Finset (Fin n)) :
    (C.card : ℝ) * projCard A I ≤ c * A.card * projCard C I := by
  have hcard : C.card ≤ projCard C I * maxSection C Iᶜ I := by
    have h := maxSection_union_le C ∅ I Iᶜ (Finset.disjoint_empty_left _)
      (Finset.disjoint_empty_left _) disjoint_compl_right
    simpa only [Finset.empty_union, maxSection_empty, Finset.union_compl,
      projCard_univ] using h
  have hsection : maxSection C Iᶜ I ≤ maxSection A Iᶜ I :=
    Finset.sup_mono_fun fun _ _ =>
      Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset_filter _ hCA))
  have huniform := maxSection_mul_le_of_isCUniform A hU ∅ I Iᶜ
    (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _) disjoint_compl_right
  simp only [Finset.empty_union, maxSection_empty, Finset.union_compl,
    projCard_univ] at huniform
  push_cast at huniform
  have hcard' : (C.card : ℝ) ≤ projCard C I * maxSection A Iᶜ I := by
    exact_mod_cast hcard.trans (Nat.mul_le_mul_left _ hsection)
  calc
    (C.card : ℝ) * projCard A I = projCard A I * C.card := by ring
    _ ≤ projCard A I * (projCard C I * maxSection A Iᶜ I) :=
      mul_le_mul_of_nonneg_left hcard' (Nat.cast_nonneg _)
    _ = (projCard A I * maxSection A Iᶜ I) * projCard C I := by ring
    _ ≤ (c * A.card) * projCard C I :=
      mul_le_mul_of_nonneg_right huniform (Nat.cast_nonneg _)
    _ = c * A.card * projCard C I := rfl

/- **Balanced thresholds and the small-fraction argument.**  Lower every projection size by
the same logarithmic amount until the two weighted products agree.  The assumed cover then
cuts a `c`-uniform set into `L.card` pieces, each occupying at most its projection fraction
times `c`; since those pieces cover the set, the common decrease is bounded by the displayed
logarithm.  This is the quantitative core requested by Problem 289. -/
private lemma projection_log_gap_le_of_uniform_cover
    (L R : Finset (Finset (Fin n))) (hLne : L.Nonempty)
    (lam mu : Finset (Fin n) → ℝ) (hlam : ∀ I ∈ L, 0 < lam I)
    (d : ℕ)
    (hcover : ∀ (Y : Fin n → Type) [∀ i, DecidableEq (Y i)]
      (A : Finset (∀ i, Y i)) (nI : Finset (Fin n) → ℝ),
      (∀ I ∈ L, 0 < nI I) →
      ∏ I ∈ L, nI I ^ lam I = ∏ J ∈ R, (projCard A J : ℝ) ^ mu J →
      ∃ B : Finset (Fin n) → Finset (∀ i, Y i), A ⊆ L.biUnion B ∧
        ∀ I ∈ L,
          (projCard (B I) I : ℝ) ≤ nI I * (2 + Real.logb 2 A.card) ^ d)
    {m : ℕ} (A : Finset (Fin n → Fin m)) (hA : A.Nonempty) {c : ℝ} (hc : 0 < c)
    (hU : IsCUniform c A) :
    ∑ I ∈ L, lam I * Real.logb 2 (projCard A I) ≤
      ∑ J ∈ R, mu J * Real.logb 2 (projCard A J) +
        (∑ I ∈ L, lam I) *
          Real.logb 2 (L.card * c * (2 + Real.logb 2 A.card) ^ d) := by
  classical
  let s : ℝ := ∑ I ∈ L, lam I
  let g : ℝ := ∑ I ∈ L, lam I * Real.logb 2 (projCard A I) -
    ∑ J ∈ R, mu J * Real.logb 2 (projCard A J)
  let t : ℝ := (2 : ℝ) ^ (g / s)
  let slack : ℝ := (2 + Real.logb 2 A.card) ^ d
  let nI : Finset (Fin n) → ℝ := fun I => (projCard A I : ℝ) / t
  have hs : 0 < s := Finset.sum_pos (fun I hI => hlam I hI) hLne
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hproj : ∀ I : Finset (Fin n), (0 : ℝ) < projCard A I := fun I => by
    exact_mod_cast Finset.card_pos.2 (hA.image (restrictTo I))
  have hnI : ∀ I ∈ L, 0 < nI I := fun I _ => div_pos (hproj I) ht
  have hlogt : Real.logb 2 t = g / s := by
    dsimp [t]
    rw [Real.logb_rpow (by norm_num) (by norm_num)]
  have hlogn : ∀ I ∈ L,
      Real.logb 2 (nI I) = Real.logb 2 (projCard A I) - g / s := by
    intro I _
    dsimp [nI]
    rw [Real.logb_div (hproj I).ne' ht.ne', hlogt]
  have hsumlog : ∑ I ∈ L, lam I * Real.logb 2 (nI I) =
      ∑ J ∈ R, mu J * Real.logb 2 (projCard A J) := by
    have hrewrite : ∑ I ∈ L, lam I * Real.logb 2 (nI I) =
        ∑ I ∈ L, lam I * (Real.logb 2 (projCard A I) - g / s) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [hlogn I hI]
    rw [hrewrite]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    field_simp [hs.ne']
    dsimp [g, s]
    ring
  have hprod : ∏ I ∈ L, nI I ^ lam I =
      ∏ J ∈ R, (projCard A J : ℝ) ^ mu J := by
    rw [prod_rpow_eq_two_rpow_weighted_log L lam nI hnI,
      prod_rpow_eq_two_rpow_weighted_log R mu
        (fun J => (projCard A J : ℝ)) (fun J _ => hproj J), hsumlog]
  obtain ⟨B, hAB, hB⟩ := hcover (fun _ => Fin m) A nI hnI hprod
  let C : Finset (Fin n) → Finset (Fin n → Fin m) := fun I => A ∩ B I
  have hAC : A ⊆ L.biUnion C := by
    intro x hx
    obtain ⟨I, hIL, hxB⟩ := Finset.mem_biUnion.1 (hAB hx)
    exact Finset.mem_biUnion.2 ⟨I, hIL, Finset.mem_inter.2 ⟨hx, hxB⟩⟩
  have hcle : ∀ I ∈ L, (C I).card * t ≤ c * A.card * slack := by
    intro I hIL
    have hfrac := card_mul_projCard_le_of_subset_isCUniform hU
      (Finset.inter_subset_left (s₁ := A) (s₂ := B I)) I
    have hprojCB : projCard (C I) I ≤ projCard (B I) I :=
      Finset.card_le_card (Finset.image_subset_image (Finset.inter_subset_right))
    have hcA : 0 ≤ c * (A.card : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg _)
    have hfrac' : (C I).card * projCard A I ≤
        c * A.card * (nI I * slack) :=
      hfrac.trans ((mul_le_mul_of_nonneg_left (by exact_mod_cast hprojCB) hcA).trans
        (mul_le_mul_of_nonneg_left (hB I hIL) hcA))
    have hcancel : ((C I).card : ℝ) ≤ c * A.card * slack / t := by
      apply le_of_mul_le_mul_right
      · calc
          ((C I).card : ℝ) * projCard A I ≤
              c * A.card * (nI I * slack) := hfrac'
          _ = (c * A.card * slack / t) * projCard A I := by
            dsimp [nI]
            field_simp
      · exact hproj I
    exact (le_div_iff₀ ht).mp hcancel
  have hAt : (A.card : ℝ) * t ≤ L.card * (c * A.card * slack) := by
    calc
      (A.card : ℝ) * t ≤ (∑ I ∈ L, (C I).card : ℝ) * t := by
        apply mul_le_mul_of_nonneg_right _ ht.le
        exact_mod_cast (Finset.card_le_card hAC).trans Finset.card_biUnion_le
      _ = ∑ I ∈ L, (C I).card * t := by rw [Finset.sum_mul]
      _ ≤ ∑ _I ∈ L, c * A.card * slack := Finset.sum_le_sum hcle
      _ = L.card * (c * A.card * slack) := by rw [Finset.sum_const, nsmul_eq_mul]
  have htK : t ≤ L.card * c * slack := by
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.2 hA
    apply le_of_mul_le_mul_left (a := (A.card : ℝ))
    · calc
        (A.card : ℝ) * t ≤ L.card * (c * A.card * slack) := hAt
        _ = A.card * (L.card * c * slack) := by ring
    · exact hApos
  have hlogle : Real.logb 2 t ≤ Real.logb 2 (L.card * c * slack) :=
    Real.logb_le_logb_of_le (by norm_num) ht htK
  have hg : g = s * Real.logb 2 t := by
    rw [hlogt]
    field_simp
  have hweighted := mul_le_mul_of_nonneg_left hlogle hs.le
  dsimp [g, s, slack] at hg hweighted ⊢
  linarith

/- The polynomial uniformity loss, the polynomial cover slack, and all typization errors are
`O(log N)`.  The singleton projections bound `log |A|` using the coordinate complexity
budget, so one constant absorbs the complete error after replacing `N` by `max N 2`. -/
private lemma exists_typization_cover_error_bound
    (D : Map) (hD : isOptimalConditional D)
    (L R : Finset (Finset (Fin n))) (hLne : L.Nonempty)
    (lam mu : Finset (Fin n) → ℝ) (hlam : ∀ I ∈ L, 0 < lam I)
    (hmu : ∀ J ∈ R, 0 < mu J) (d dt : ℕ) :
    ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString),
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ (m : ℕ) (A : Finset (Fin n → Fin m)), A.Nonempty →
        (∀ I J : Finset (Fin n), Disjoint I J →
          |Real.logb 2 (maxSection A J I) - ((tupleCondK D x J I).toNat : ℝ)| ≤
            (logSlack dt (max N 2) : ℝ)) →
        (∑ I ∈ L, lam I) * Real.logb 2
              (L.card * ((max N 2 : ℕ) : ℝ) ^ dt *
                (2 + Real.logb 2 A.card) ^ d) +
            ((∑ I ∈ L, lam I) + ∑ J ∈ R, mu J) *
              (logSlack dt (max N 2) : ℝ) ≤
          (logSlack c N : ℝ) := by
  classical
  obtain ⟨c0, hc0⟩ := exists_tuplePlainK_singleton_le (n := n) D hD
  let sL : ℝ := ∑ I ∈ L, lam I
  let sT : ℝ := sL + ∑ J ∈ R, mu J
  have hsL0 : 0 ≤ sL := Finset.sum_nonneg fun I hI => (hlam I hI).le
  have hsT0 : 0 ≤ sT := add_nonneg hsL0
    (Finset.sum_nonneg fun J hJ => (hmu J hJ).le)
  have hLcard : 0 < L.card := Finset.card_pos.2 hLne
  have hlogL0 : 0 ≤ Real.logb 2 L.card :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hLcard)
  let kK : ℕ := ⌈Real.logb 2 ((2 + n * (1 + c0 + 3 * dt) : ℕ) : ℝ)⌉₊
  let alpha : ℝ := sL * (dt + d) + sT * dt
  let beta : ℝ := sL * (Real.logb 2 L.card + d * kK) + sT * dt
  let C : ℕ := ⌈alpha + beta⌉₊
  refine ⟨3 * C, fun N x hx m A hA happrox => ?_⟩
  let N' := max N 2
  let b := (Nat.bits N').length
  have hN'1 : 1 ≤ N' := by omega
  have hsingleR : ∀ k, ((tuplePlainK D x {k}).toNat : ℝ) ≤ N' + c0 := by
    intro k
    have h : tuplePlainK D x {k} ≤ ((N' + c0 : ℕ) : ℕ∞) := by
      refine (hc0 x k).trans ?_
      push_cast
      exact add_le_add ((hx k).trans (by exact_mod_cast le_max_left N 2)) le_rfl
    exact_mod_cast ENat.toNat_le_of_le_natCast h
  have hproj : ∀ k, Real.logb 2 (projCard A {k}) ≤ N' + c0 + logSlack dt N' := by
    intro k
    have h := happrox ∅ {k} (Finset.disjoint_empty_left {k})
    have hplain : tupleCondK D x {k} ∅ = tuplePlainK D x {k} := by
      simp [tupleCondK, tuplePlainK, plainK]
    rw [maxSection_empty, hplain] at h
    linarith [(abs_le.1 h).2, hsingleR k]
  have hlogTwoA : Real.logb 2 (2 + Real.logb 2 A.card) ≤ kK + b :=
    logb_two_add_logb_card_le hA hN'1 hproj
  have hslack : (logSlack dt N' : ℝ) = dt * (b : ℝ) + dt := by
    simp only [logSlack, b]
    push_cast
    ring
  have hlogN : Real.logb 2 N' ≤ b := logb_le_length_bits N'
  have hAone : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.card_pos.2 hA
  have hbasepos : 0 < 2 + Real.logb 2 A.card := by
    have : 0 ≤ Real.logb 2 A.card := Real.logb_nonneg (by norm_num) hAone
    linarith
  have hlogProduct :
      Real.logb 2
          (L.card * ((N' : ℕ) : ℝ) ^ dt *
            (2 + Real.logb 2 A.card) ^ d) ≤
        Real.logb 2 L.card + dt * b + d * (kK + b) := by
    have hLcpos : (0 : ℝ) < L.card := by exact_mod_cast hLcard
    have hNpow : (0 : ℝ) < ((N' : ℕ) : ℝ) ^ dt := by
      have : (0 : ℝ) < N' := by exact_mod_cast hN'1
      positivity
    have hBpow : (0 : ℝ) < (2 + Real.logb 2 A.card) ^ d := by positivity
    rw [Real.logb_mul (mul_pos hLcpos hNpow).ne' hBpow.ne',
      Real.logb_mul hLcpos.ne' hNpow.ne', Real.logb_pow, Real.logb_pow]
    have hdt0 : (0 : ℝ) ≤ dt := Nat.cast_nonneg dt
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [mul_le_mul_of_nonneg_left hlogN hdt0,
      mul_le_mul_of_nonneg_left hlogTwoA hd0]
  have halpha0 : 0 ≤ alpha := by
    dsimp only [alpha]
    positivity
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have halphaC : alpha ≤ C :=
    (le_add_of_nonneg_right hbeta0).trans (Nat.le_ceil _)
  have hbetaC : beta ≤ C :=
    (le_add_of_nonneg_left halpha0).trans (Nat.le_ceil _)
  have hmain :
      sL * Real.logb 2
          (L.card * ((N' : ℕ) : ℝ) ^ dt *
            (2 + Real.logb 2 A.card) ^ d) +
          sT * (logSlack dt N' : ℝ) ≤ (C : ℝ) * b + C := by
    rw [hslack]
    have h1 := mul_le_mul_of_nonneg_left hlogProduct hsL0
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have ha := mul_le_mul_of_nonneg_right halphaC hb0
    dsimp only [alpha, beta] at ha halphaC hbetaC ⊢
    linarith
  have hmax : (logSlack C N' : ℝ) ≤ logSlack (3 * C) N := by
    exact_mod_cast logSlack_max_two_le_three_mul C N
  have hmain' : (C : ℝ) * b + C = logSlack C N' := by
    simp only [logSlack, b]
    push_cast
    ring
  rw [hmain'] at hmain
  dsimp only [sL, sT, N'] at hmain ⊢
  exact hmain.trans hmax

/-- **Cover ⟹ inequality (SUV Theorem 213, first half).**  If every finite set admits a cover
with polylogarithmic slack, then the weighted complexity inequality holds.  The book argues by
contradiction: a would-be violation is fed to the typization trick (Theorem 211), producing an
almost-uniform set that a cover by sets with small `I`-projections cannot fill.  Quantifying the
typization and almost-uniform estimates is Problem 289. -/
private lemma complexity_of_cover (D : Map) (hD : isOptimalConditional D)
    (L R : Finset (Finset (Fin n))) (hLne : L.Nonempty)
    (lam mu : Finset (Fin n) → ℝ) (hlam : ∀ I ∈ L, 0 < lam I) (hmu : ∀ J ∈ R, 0 < mu J) :
    (∃ d : ℕ, ∀ (Y : Fin n → Type) [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i))
        (nI : Finset (Fin n) → ℝ), (∀ I ∈ L, 0 < nI I) →
        ∏ I ∈ L, nI I ^ lam I = ∏ J ∈ R, (projCard A J : ℝ) ^ mu J →
        ∃ B : Finset (Fin n) → Finset (∀ i, Y i), A ⊆ L.biUnion B ∧
          ∀ I ∈ L, (projCard (B I) I : ℝ) ≤ nI I * (2 + Real.logb 2 A.card) ^ d) →
      ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
        ∑ I ∈ L, lam I * ((tuplePlainK D x I).toNat : ℝ)
          ≤ ∑ J ∈ R, mu J * ((tuplePlainK D x J).toNat : ℝ) + (logSlack c N : ℝ) := by
  intro hcover
  obtain ⟨d, hd⟩ := hcover
  obtain ⟨dt, htyp⟩ := exists_cUniform_typization (n := n) D hD
  obtain ⟨c, herr⟩ := exists_typization_cover_error_bound D hD L R hLne
    lam mu hlam hmu d dt
  refine ⟨c, fun N x hx => ?_⟩
  let N' := max N 2
  have hN' : 1 < N' := by omega
  have hx' : ∀ i, plainK D (x i) ≤ (N' : ℕ∞) :=
    fun i => (hx i).trans (by exact_mod_cast le_max_left N 2)
  obtain ⟨m, A, hA, hU, happrox⟩ := htyp N' hN' x hx'
  have hgap := projection_log_gap_le_of_uniform_cover L R hLne lam mu hlam d hd A hA
    (by positivity : (0 : ℝ) < (N' : ℕ) ^ dt) hU
  have hplain : ∀ I : Finset (Fin n), tupleCondK D x I ∅ = tuplePlainK D x I := by
    intro I
    simp [tupleCondK, tuplePlainK, plainK]
  have happrox' : ∀ I : Finset (Fin n),
      |Real.logb 2 (projCard A I) - ((tuplePlainK D x I).toNat : ℝ)| ≤
        (logSlack dt N' : ℝ) := by
    intro I
    simpa only [maxSection_empty, hplain I] using
      happrox ∅ I (Finset.disjoint_empty_left I)
  have hweighted := weighted_complexity_le_of_projection_logs L R lam mu
    (fun I hI => (hlam I hI).le) (fun J hJ => (hmu J hJ).le)
    (fun I => ((tuplePlainK D x I).toNat : ℝ))
    (fun I => Real.logb 2 (projCard A I))
    (fun I _ => happrox' I) (fun J _ => happrox' J) hgap
  have herr' := herr N x hx m A hA (by simpa only [N'] using happrox)
  dsimp [N'] at hweighted herr'
  linarith

/-- The linear form `∑_{I ∈ L} λ_I h(x_I) − ∑_{J ∈ R} μ_J h(x_J)` of Theorem 213. -/
private def pairForm (L R : Finset (Finset (Fin n))) (lam mu : Finset (Fin n) → ℝ) :
    LinearForm n :=
  fun I => if I ∈ L then lam I else if I ∈ R then -mu I else 0

/- For disjoint families of non-empty sets, evaluating `pairForm` on any values separates the
two weighted sums. -/
private lemma sum_pairForm_mul {L R : Finset (Finset (Fin n))} (hLR : Disjoint L R)
    (hL : ∀ I ∈ L, I.Nonempty) (hR : ∀ J ∈ R, J.Nonempty) (lam mu : Finset (Fin n) → ℝ)
    (v : Finset (Fin n) → ℝ) :
    ∑ I ∈ nonemptyParts n, pairForm L R lam mu I * v I =
      ∑ I ∈ L, lam I * v I - ∑ J ∈ R, mu J * v J := by
  have hsub : L ∪ R ⊆ nonemptyParts n := Finset.union_subset
    (fun I hI => mem_nonemptyParts.2 (hL I hI)) (fun J hJ => mem_nonemptyParts.2 (hR J hJ))
  rw [← Finset.sum_subset hsub (fun I _ hI => by
      simp only [Finset.mem_union, not_or] at hI
      simp [pairForm, hI.1, hI.2]), Finset.sum_union hLR,
    Finset.sum_congr rfl (fun I hI => by simp [pairForm, hI] :
      ∀ I ∈ L, pairForm L R lam mu I * v I = lam I * v I),
    Finset.sum_congr rfl (fun J hJ => by simp [pairForm, hJ, Finset.disjoint_right.1 hLR hJ] :
      ∀ J ∈ R, pairForm L R lam mu J * v J = -(mu J * v J)),
    Finset.sum_neg_distrib]
  ring

/- The weighted complexity inequality of Theorem 213 makes the corresponding entropy inequality
true (Theorem 210). -/
private lemma holdsForEntropies_pairForm (D : Map) (hD : isOptimalConditional D)
    {L R : Finset (Finset (Fin n))} (hLR : Disjoint L R)
    (hL : ∀ I ∈ L, I.Nonempty) (hR : ∀ J ∈ R, J.Nonempty) {lam mu : Finset (Fin n) → ℝ}
    (hcomplexity : ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString),
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∑ I ∈ L, lam I * ((tuplePlainK D x I).toNat : ℝ) ≤
        ∑ J ∈ R, mu J * ((tuplePlainK D x J).toNat : ℝ) + (logSlack c N : ℝ)) :
    HoldsForEntropies (pairForm L R lam mu) := by
  refine (holdsForEntropies_iff_holdsForComplexitiesCplx _ D hD).2 ?_
  obtain ⟨c, hc⟩ := hcomplexity
  refine ⟨c, fun N x hx => ?_⟩
  rw [LinearForm.evalComplexity, sum_pairForm_mul hLR hL hR]
  linarith [hc N x hx]

/- Taking logarithms in the balance condition `∏ n_I^{λ_I} = ∏ m_A(J)^{μ_J}`. -/
private lemma weighted_logb_eq_of_prod_eq {Y : Fin n → Type} [∀ i, DecidableEq (Y i)]
    {L R : Finset (Finset (Fin n))} {lam mu nI : Finset (Fin n) → ℝ}
    {A : Finset (∀ i, Y i)} (hnI : ∀ I ∈ L, 0 < nI I) (hA : A.Nonempty)
    (hprod : ∏ I ∈ L, nI I ^ lam I = ∏ J ∈ R, (projCard A J : ℝ) ^ mu J) :
    ∑ I ∈ L, lam I * Real.logb 2 (nI I) = ∑ J ∈ R, mu J * Real.logb 2 (projCard A J) := by
  rw [prod_rpow_eq_two_rpow_weighted_log L lam nI hnI,
    prod_rpow_eq_two_rpow_weighted_log R mu (fun J => (projCard A J : ℝ))
      (fun J _ => Nat.cast_pos.2 (Finset.card_pos.2 (hA.image (restrictTo J))))] at hprod
  have h := congrArg (Real.logb 2) hprod
  simpa only [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num)] using h

/- **Scores from a decomposition.**  Score a point `z` of an `I`-projection by the smallest
`log |proj_I B_k| + log m` over the parts `B_k` whose `I`-projection contains `z`.  When every
non-empty part satisfies the weighted bound, so does every point of `A` with its own scores,
and the points whose `I`-score is at most `t_I` have at most `2^{t_I}` distinct
`I`-projections: each of the at most `m` parts that contribute has at most `2^{t_I} / m`. -/
private lemma exists_scores_of_decomposition {Y : Fin n → Type} [∀ i, DecidableEq (Y i)]
    (L : Finset (Finset (Fin n))) (lam : Finset (Fin n) → ℝ) (hlam : ∀ I ∈ L, 0 ≤ lam I)
    (A : Finset (∀ i, Y i)) {m : ℕ} (B : Fin m → Finset (∀ i, Y i))
    (hAB : A = Finset.univ.biUnion B) (threshold : Finset (Fin n) → ℝ)
    (hpart : ∀ k, (B k).Nonempty →
      ∑ I ∈ L, lam I * (Real.logb 2 (projCard (B k) I) + Real.logb 2 m) ≤
        ∑ I ∈ L, lam I * threshold I) :
    ∃ score : (I : Finset (Fin n)) → ((i : I) → Y i) → ℝ,
      (∀ x ∈ A, ∑ I ∈ L, lam I * score I (restrictTo I x) ≤ ∑ I ∈ L, lam I * threshold I) ∧
      ∀ I, (projCard (A.filter fun x => score I (restrictTo I x) ≤ threshold I) I : ℝ) ≤
        2 ^ threshold I := by
  classical
  let S_z (I : Finset (Fin n)) (z : ∀ i : I, Y i) : Finset ℝ :=
    (Finset.univ.filter (fun k => z ∈ proj (B k) I)).image
      (fun k => Real.logb 2 (projCard (B k) I))
  let score (I : Finset (Fin n)) (z : ∀ i : I, Y i) : ℝ :=
    if h : (S_z I z).Nonempty then (S_z I z).min' h + Real.logb 2 m else 0
  have hmemS : ∀ {I : Finset (Fin n)} {x : ∀ i, Y i} {k : Fin m}, x ∈ B k →
      Real.logb 2 (projCard (B k) I) ∈ S_z I (restrictTo I x) := fun {I x k} hk =>
    Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      Finset.mem_image_of_mem _ hk⟩, rfl⟩
  refine ⟨score, fun x hx => ?_, fun I => ?_⟩
  · rw [hAB, Finset.mem_biUnion] at hx
    obtain ⟨k, -, hk⟩ := hx
    refine le_trans (Finset.sum_le_sum fun I hI => mul_le_mul_of_nonneg_left ?_ (hlam I hI))
      (hpart k ⟨x, hk⟩)
    have hmem := hmemS (I := I) hk
    have hne : (S_z I (restrictTo I x)).Nonempty := ⟨_, hmem⟩
    simp only [score, dite_eq_left hne]
    linarith [Finset.min'_le _ _ hmem]
  · set C := threshold I
    let good := Finset.univ.filter fun k => Real.logb 2 (projCard (B k) I) + Real.logb 2 m ≤ C
    have h_sub : (A.filter fun x => score I (restrictTo I x) ≤ C).image (restrictTo I) ⊆
        good.biUnion fun k => proj (B k) I := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨hxA, h_score⟩ := Finset.mem_filter.1 hx
      rw [hAB, Finset.mem_biUnion] at hxA
      obtain ⟨k, -, hk_in⟩ := hxA
      have hne : (S_z I (restrictTo I x)).Nonempty := ⟨_, hmemS hk_in⟩
      simp only [score, dite_eq_left hne] at h_score
      obtain ⟨k0, hk0, hk_eq⟩ := Finset.mem_image.1 (Finset.min'_mem _ hne)
      exact Finset.mem_biUnion.2 ⟨k0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk_eq ▸ h_score⟩,
        (Finset.mem_filter.1 hk0).2⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hA : A = ∅ := by
        rw [hAB]
        simp
      subst hA
      simp only [Finset.filter_empty, projCard, proj, Finset.image_empty, Finset.card_empty,
        Nat.cast_zero]
      positivity
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    calc (projCard (A.filter fun x => score I (restrictTo I x) ≤ C) I : ℝ)
        = (((A.filter fun x => score I (restrictTo I x) ≤ C).image (restrictTo I)).card : ℝ) :=
          rfl
      _ ≤ ((good.biUnion fun k => proj (B k) I).card : ℝ) := by
        exact_mod_cast Finset.card_le_card h_sub
      _ ≤ ∑ k ∈ good, (projCard (B k) I : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ good, (2 : ℝ) ^ C / m := by
        refine Finset.sum_le_sum fun k hk => ?_
        have h_C := (Finset.mem_filter.1 hk).2
        rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) (projCard (B k) I)) with h0 | hpos
        · rw [← h0]
          positivity
        · have h_pow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h_C
          rw [← Real.logb_mul hpos.ne' hm_pos.ne',
            Real.rpow_logb (by norm_num) (by norm_num) (mul_pos hpos hm_pos)] at h_pow
          exact (le_div_iff₀ hm_pos).mpr h_pow
      _ = good.card * ((2 : ℝ) ^ C / m) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ m * ((2 : ℝ) ^ C / m) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
      _ = (2 : ℝ) ^ C := mul_div_cancel₀ _ hm_pos.ne'

/- **From projection descriptions to a cover.**  Put a point into the part indexed by `I`
when its `I`-projection lies below the corresponding description threshold.  Weighted
pigeonhole guarantees that every point enters some part, while the sublevel-set estimate gives
the required projection bound. -/
private lemma exists_cover_of_projection_scores
    (L : Finset (Finset (Fin n))) (hLne : L.Nonempty)
    (lam : Finset (Fin n) → ℝ) (hlam : ∀ I ∈ L, 0 < lam I)
    {Y : Fin n → Type} [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i))
    (threshold sizeBound : Finset (Fin n) → ℝ)
    (score : (I : Finset (Fin n)) → ((i : I) → Y i) → ℝ)
    (hscore : ∀ x ∈ A,
      ∑ I ∈ L, lam I * score I (restrictTo I x) ≤
        ∑ I ∈ L, lam I * threshold I)
    (hcard : ∀ I ∈ L,
      (projCard (A.filter fun x => score I (restrictTo I x) ≤ threshold I) I : ℝ) ≤
        sizeBound I) :
    ∃ B : Finset (Fin n) → Finset (∀ i, Y i), A ⊆ L.biUnion B ∧
      ∀ I ∈ L, (projCard (B I) I : ℝ) ≤ sizeBound I := by
  classical
  let B : Finset (Fin n) → Finset (∀ i, Y i) := fun I =>
    A.filter fun x => score I (restrictTo I x) ≤ threshold I
  refine ⟨B, ?_, ?_⟩
  · intro x hx
    obtain ⟨I, hIL, hI⟩ := exists_le_of_weighted_sum_le hLne hlam (hscore x hx)
    exact Finset.mem_biUnion.2 ⟨I, hIL, Finset.mem_filter.2 ⟨hx, hI⟩⟩
  · intro I hIL
    simpa only [B] using hcard I hIL

/-- **Inequality ⟹ cover (SUV Theorem 213, second half).**  If the weighted complexity
inequality holds, then every finite set admits a cover with polylogarithmic slack.  The book
reduces to a simple worst-case `A` by exhaustive search; then every element of `A` satisfies a
summed complexity bound, and `exists_le_of_weighted_sum_le` selects the coordinate `I` that
names its part `B_I`.  The simple-set estimate and the worst-case reduction are Problem 289. -/
private lemma cover_of_complexity (D : Map) (hD : isOptimalConditional D)
    (L R : Finset (Finset (Fin n))) (hLR : Disjoint L R) (hLne : L.Nonempty)
    (hL : ∀ I ∈ L, I.Nonempty) (hR : ∀ J ∈ R, J.Nonempty)
    (lam mu : Finset (Fin n) → ℝ) (hlam : ∀ I ∈ L, 0 < lam I) (hmu : ∀ J ∈ R, 0 < mu J) :
    (∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
        ∑ I ∈ L, lam I * ((tuplePlainK D x I).toNat : ℝ)
          ≤ ∑ J ∈ R, mu J * ((tuplePlainK D x J).toNat : ℝ) + (logSlack c N : ℝ)) →
      ∃ d : ℕ, ∀ (Y : Fin n → Type) [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i))
        (nI : Finset (Fin n) → ℝ), (∀ I ∈ L, 0 < nI I) →
        ∏ I ∈ L, nI I ^ lam I = ∏ J ∈ R, (projCard A J : ℝ) ^ mu J →
        ∃ B : Finset (Fin n) → Finset (∀ i, Y i), A ⊆ L.biUnion B ∧
          ∀ I ∈ L, (projCard (B I) I : ℝ) ≤ nI I * (2 + Real.logb 2 A.card) ^ d := by
  intro hcomplexity
  obtain ⟨d, hd⟩ := exists_union_decomposition_of_holdsForEntropies (pairForm L R lam mu)
    (holdsForEntropies_pairForm D hD hLR hL hR hcomplexity)
  set S : ℝ := ∑ I ∈ L, lam I
  have hS : 0 < S := Finset.sum_pos (fun I hI => hlam I hI) hLne
  set e : ℕ := d * ⌈(1 + S) / S⌉₊ with he_def
  have he : (d : ℝ) * (1 + S) ≤ e * S := by
    have h : 1 + S ≤ ⌈(1 + S) / S⌉₊ * S := (div_le_iff₀ hS).1 (Nat.le_ceil _)
    rw [he_def]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  refine ⟨e, fun Y _ A nI hnI hprod => ?_⟩
  rcases A.eq_empty_or_nonempty with rfl | hA
  · refine ⟨fun _ => ∅, by simp, fun I hI => ?_⟩
    have hnI0 := (hnI I hI).le
    simp only [projCard, proj, Finset.image_empty, Finset.card_empty, Nat.cast_zero,
      Real.logb_zero, add_zero]
    positivity
  set K : ℝ := 2 + Real.logb 2 A.card
  have hlogA : 0 ≤ Real.logb 2 A.card :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast Finset.card_pos.2 hA)
  have hKpos : 0 < K := by linarith
  have hlogK : 0 ≤ Real.logb 2 K := Real.logb_nonneg one_lt_two (by linarith)
  obtain ⟨m, B, hm, hAB, hpartB⟩ := hd Y A
  have hlogeq := weighted_logb_eq_of_prod_eq hnI hA hprod
  obtain ⟨score, hscore, hcard⟩ := exists_scores_of_decomposition L lam
    (fun I hI => (hlam I hI).le) A B hAB (fun I => Real.logb 2 (nI I * K ^ e)) fun k hk => by
      have hBA : B k ⊆ A := hAB ▸ Finset.subset_biUnion_of_mem B (Finset.mem_univ k)
      have hEval : (pairForm L R lam mu).evalLogSize (B k) ≤ d * Real.logb 2 K := by
        have h := hpartB k
        rw [prod_projCard_rpow_eq_two_rpow _ hk] at h
        have h' := Real.logb_le_logb_of_le (b := 2) one_lt_two (by positivity) h
        rwa [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_pow] at h'
      rw [LinearForm.evalLogSize, sum_pairForm_mul hLR hL hR] at hEval
      have hRle : ∑ J ∈ R, mu J * Real.logb 2 (projCard (B k) J) ≤
          ∑ J ∈ R, mu J * Real.logb 2 (projCard A J) :=
        Finset.sum_le_sum fun J hJ => mul_le_mul_of_nonneg_left
          (Real.logb_le_logb_of_le one_lt_two
            (by exact_mod_cast Finset.card_pos.2 (hk.image (restrictTo J)))
            (by exact_mod_cast Finset.card_le_card (Finset.image_subset_image hBA)))
          (hmu J hJ).le
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast k.pos
      have hmlog : Real.logb 2 m ≤ d * Real.logb 2 K := by
        rw [← Real.logb_pow]
        exact Real.logb_le_logb_of_le one_lt_two (by linarith) hm
      have hlhs : ∑ I ∈ L, lam I * (Real.logb 2 (projCard (B k) I) + Real.logb 2 m) =
          ∑ I ∈ L, lam I * Real.logb 2 (projCard (B k) I) + S * Real.logb 2 m := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        rfl
      have hrhs : ∑ I ∈ L, lam I * Real.logb 2 (nI I * K ^ e) =
          ∑ I ∈ L, lam I * Real.logb 2 (nI I) + S * (e * Real.logb 2 K) := by
        rw [Finset.sum_congr rfl fun I hI => by
          rw [Real.logb_mul (hnI I hI).ne' (pow_pos hKpos e).ne', Real.logb_pow, mul_add],
          Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [hlhs, hrhs]
      have h1 := mul_le_mul_of_nonneg_left hmlog hS.le
      have h2 := mul_le_mul_of_nonneg_right he hlogK
      nlinarith
  exact exists_cover_of_projection_scores L hLne lam hlam A _ (fun I => nI I * K ^ e) score
    hscore fun I hI => (hcard I).trans_eq
      (Real.rpow_logb (by norm_num) (by norm_num) (mul_pos (hnI I hI) (pow_pos hKpos e)))

/-- **Theorem 213.**  Let `L` and `R` be disjoint families of non-empty sets of indices with
positive coefficients `λ_I` (`I ∈ L`) and `μ_J` (`J ∈ R`).  The following are equivalent:
* there is a constant `d` such that for every finite `A ⊆ Y_1 × ⋯ × Y_n` and every family of
  positive reals `n_I` (`I ∈ L`) with `∏_I n_I^{λ_I} = ∏_J m_A(J)^{μ_J}`, the set `A` is
  covered by sets `B_I` (`I ∈ L`) with `m_{B_I}(I) ≤ n_I · (2 + log |A|)^d`;
* `∑_I λ_I C(x_I) ≤ ∑_J μ_J C(x_J) + O(log N)` for all `N` and all strings of complexity at
  most `N`.
The book writes the slack as `(log |A|)^d`; the factor used here is `(2 + log₂ |A|)^d`, a
repair of the degenerate small-alphabet case (`(log |A|)^d ≤ 1` for `|A| ≤ 2`), equivalent to
the printed one up to a change of `d` for `|A| ≥ 4`; see the module docstring.  The left-hand
family `L` is non-empty: for `L = ∅` the complexity side reads `0 ≤ ∑_J μ_J C(x_J) + O(log N)`
and is automatic, while the cover side asks a non-empty `A` to be covered by the empty union.
The book's own proof is sketchy (Problem 289 asks to make it precise) and patches a flaw about
non-rational coefficients informally.  SUV Theorem 213, p. 331. -/
theorem cover_iff_complexity_inequality (D : Map) (hD : isOptimalConditional D)
    (L R : Finset (Finset (Fin n))) (hLR : Disjoint L R) (hLne : L.Nonempty)
    (hL : ∀ I ∈ L, I.Nonempty) (hR : ∀ J ∈ R, J.Nonempty)
    (lam mu : Finset (Fin n) → ℝ) (hlam : ∀ I ∈ L, 0 < lam I) (hmu : ∀ J ∈ R, 0 < mu J) :
    (∃ d : ℕ, ∀ (Y : Fin n → Type) [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i))
        (nI : Finset (Fin n) → ℝ), (∀ I ∈ L, 0 < nI I) →
        ∏ I ∈ L, nI I ^ lam I = ∏ J ∈ R, (projCard A J : ℝ) ^ mu J →
        ∃ B : Finset (Fin n) → Finset (∀ i, Y i), A ⊆ L.biUnion B ∧
          ∀ I ∈ L, (projCard (B I) I : ℝ) ≤ nI I * (2 + Real.logb 2 A.card) ^ d) ↔
      ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
        ∑ I ∈ L, lam I * ((tuplePlainK D x I).toNat : ℝ)
          ≤ ∑ J ∈ R, mu J * ((tuplePlainK D x J).toNat : ℝ) + (logSlack c N : ℝ) := by
  exact ⟨complexity_of_cover D hD L R hLne lam mu hlam hmu,
    cover_of_complexity D hD L R hLR hLne hL hR lam mu hlam hmu⟩

end Kolmogorov
