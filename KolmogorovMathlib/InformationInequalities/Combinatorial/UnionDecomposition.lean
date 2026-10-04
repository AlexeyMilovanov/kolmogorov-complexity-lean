import KolmogorovMathlib.InformationInequalities.Combinatorial.Partition
import KolmogorovMathlib.InformationInequalities.Combinatorial.TypizationBounds

/-!
# Combinatorial interpretation by union decompositions (Theorem 214)

SUV Section 10.9, pp. 333–336.

For coefficients of arbitrary signs, `∑ λ_I C(x_I) ≤ O(log N)` holds if and only if every finite
set is a union of polylogarithmically many parts, each satisfying the product inequality
`∏ m(I)^{λ_I} ≤ (2 + log₂ |A|)^d` for its own projections
(`union_decomposition_iff_holdsForComplexitiesCplx`).
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}
/-- Projection sizes of a large subset of a uniform set are comparable. -/
private lemma projCard_le_mul_projCard_of_subset {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] {c M : ℝ} {A B : Finset (∀ i, Y i)} (hA : IsCUniform c A)
    (hBA : B ⊆ A) (hB : B.Nonempty) (hcard : (A.card : ℝ) ≤ M * B.card)
    (I : Finset (Fin n)) : (projCard A I : ℝ) ≤ c * M * projCard B I := by
  have h1 : B.card ≤ projCard B I * maxSection B Iᶜ I := by
    have h := maxSection_union_le B ∅ I Iᶜ (Finset.disjoint_empty_left _)
      (Finset.disjoint_empty_left _) disjoint_compl_right
    simpa only [Finset.empty_union, maxSection_empty, Finset.union_compl, projCard_univ] using h
  have h2 : maxSection B Iᶜ I ≤ maxSection A Iᶜ I :=
    Finset.sup_mono_fun fun _ _ =>
      Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset_filter _ hBA))
  have h3 := maxSection_mul_le_of_isCUniform A hA ∅ I Iᶜ (Finset.disjoint_empty_left _)
    (Finset.disjoint_empty_left _) disjoint_compl_right
  simp only [Finset.empty_union, maxSection_empty, Finset.union_compl, projCard_univ] at h3
  push_cast at h3
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.2 hB
  have hApos : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.2 (hB.mono hBA)
  have hc : 0 ≤ c := by
    have hu := hA (Equiv.refl _)
    have hch : (A.card : ℝ) ≤ chainBound A (Equiv.refl _) := by
      exact_mod_cast card_le_chainBound A (Equiv.refl _)
    nlinarith
  have h1' : (B.card : ℝ) ≤ projCard B I * maxSection A Iᶜ I := by
    exact_mod_cast h1.trans (Nat.mul_le_mul_left _ h2)
  have key : (projCard A I : ℝ) * B.card ≤ (c * M * projCard B I) * B.card := by
    calc
      (projCard A I : ℝ) * B.card
          ≤ projCard A I * (projCard B I * maxSection A Iᶜ I) :=
        mul_le_mul_of_nonneg_left h1' (Nat.cast_nonneg _)
      _ = (projCard A I * maxSection A Iᶜ I) * projCard B I := by ring
      _ ≤ (c * A.card) * projCard B I :=
        mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
      _ ≤ (c * (M * B.card)) * projCard B I :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hc) (Nat.cast_nonneg _)
      _ = (c * M * projCard B I) * B.card := by ring
  exact le_of_mul_le_mul_right key hBpos

/-- Passing to a large subset changes a uniform set's log-sizes by a controlled amount. -/
private lemma evalLogSize_le_add_of_subset {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] (f : LinearForm n) {c M : ℝ} {A B : Finset (∀ i, Y i)}
    (hA : IsCUniform c A) (hBA : B ⊆ A) (hB : B.Nonempty)
    (hcard : (A.card : ℝ) ≤ M * B.card) :
    f.evalLogSize A ≤
      f.evalLogSize B + (∑ I ∈ nonemptyParts n, |f I|) * Real.logb 2 (c * M) := by
  unfold LinearForm.evalLogSize
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun I _ => ?_
  have hpB : (0 : ℝ) < projCard B I := by exact_mod_cast Finset.card_pos.2 (hB.image _)
  have hle' : projCard B I ≤ projCard A I :=
    Finset.card_le_card (Finset.image_subset_image hBA)
  have hle : (projCard B I : ℝ) ≤ projCard A I := by exact_mod_cast hle'
  have hup := projCard_le_mul_projCard_of_subset hA hBA hB hcard I
  have hcM : 0 < c * M := by
    by_contra h
    push Not at h
    nlinarith
  have h1 : Real.logb 2 (projCard B I) ≤ Real.logb 2 (projCard A I) :=
    Real.logb_le_logb_of_le (by norm_num) hpB hle
  have h2 : Real.logb 2 (projCard A I) ≤
      Real.logb 2 (c * M) + Real.logb 2 (projCard B I) := by
    rw [← Real.logb_mul hcM.ne' hpB.ne']
    exact Real.logb_le_logb_of_le (by norm_num) (hpB.trans_le hle) hup
  have h3 : f I * (Real.logb 2 (projCard A I) - Real.logb 2 (projCard B I)) ≤
      |f I| * Real.logb 2 (c * M) :=
    calc
      f I * (Real.logb 2 (projCard A I) - Real.logb 2 (projCard B I)) ≤
          |f I| * (Real.logb 2 (projCard A I) - Real.logb 2 (projCard B I)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |f I| * Real.logb 2 (c * M) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  linarith


/-- Approximate projection log-sizes control evaluation on complexities. -/
private lemma evalComplexity_le_evalLogSize_add {Y : Fin n → Type} [∀ i, DecidableEq (Y i)]
    (f : LinearForm n) (D : Map) (x : Fin n → BitString) (A : Finset (∀ i, Y i)) {e : ℝ}
    (h : ∀ I ∈ nonemptyParts n,
      |Real.logb 2 (projCard A I) - ((tuplePlainK D x I).toNat : ℝ)| ≤ e) :
    f.evalComplexity D x ≤ f.evalLogSize A + (∑ I ∈ nonemptyParts n, |f I|) * e := by
  unfold LinearForm.evalComplexity LinearForm.evalLogSize
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun I hI => ?_
  have h1 := h I hI
  have h2 : f I * (((tuplePlainK D x I).toNat : ℝ) - Real.logb 2 (projCard A I)) ≤
      |f I| * e :=
    calc
      f I * (((tuplePlainK D x I).toNat : ℝ) - Real.logb 2 (projCard A I)) ≤
          |f I * (((tuplePlainK D x I).toNat : ℝ) - Real.logb 2 (projCard A I))| :=
        le_abs_self _
      _ = |f I| * |Real.logb 2 (projCard A I) - ((tuplePlainK D x I).toNat : ℝ)| := by
        rw [abs_mul, abs_sub_comm]
      _ ≤ |f I| * e := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  linarith


/-- A union decomposition applied to a typization set implies the complexity inequality. -/
private lemma holdsForComplexitiesCplx_of_union_decomposition (f : LinearForm n) (D : Map)
    (hD : isOptimalConditional D) (d : ℕ)
    (hC : ∀ (Y : Fin n → Type) [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i)),
        ∃ (m : ℕ) (B : Fin m → Finset (∀ i, Y i)),
          (m : ℝ) ≤ (2 + Real.logb 2 A.card) ^ d ∧ A = Finset.univ.biUnion B ∧
          ∀ k, ∏ I ∈ nonemptyParts n, (projCard (B k) I : ℝ) ^ f I
            ≤ (2 + Real.logb 2 A.card) ^ d) :
    HoldsForComplexitiesCplx f D := by
  obtain ⟨dt, hdt⟩ := exists_cUniform_typization (n := n) D hD
  obtain ⟨c0, hc0⟩ := exists_tuplePlainK_singleton_le (n := n) D hD
  set S : ℝ := ∑ I ∈ nonemptyParts n, |f I|
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun I _ => abs_nonneg _
  set T : ℕ := ⌈S⌉₊
  have hST : S ≤ T := Nat.le_ceil S
  set K : ℕ := 2 + n * (1 + c0 + 3 * dt) with hK
  set kK : ℕ := ⌈Real.logb 2 K⌉₊
  set C : ℕ := 2 * T * dt + d * kK + d + T * d * kK + T * d with hC'
  refine ⟨3 * C, fun N x hN => ?_⟩
  set N' := max N 2
  have hN' : 1 < N' := by omega
  have hN'r : (1 : ℝ) ≤ N' := by exact_mod_cast hN'.le
  have hplain : ∀ i, plainK D (x i) ≤ (N' : ℕ∞) :=
    fun i => (hN i).trans (by exact_mod_cast le_max_left N 2)
  obtain ⟨m, A, hAne, hAunif, hAbound⟩ := hdt N' hN' x hplain
  have hdiff : ∀ I ∈ nonemptyParts n,
      |Real.logb 2 (projCard A I) - ((tuplePlainK D x I).toNat : ℝ)| ≤ logSlack dt N' := by
    intro I _
    have h := hAbound ∅ I (Finset.disjoint_empty_left I)
    have hplainI : tupleCondK D x I ∅ = tuplePlainK D x I := by
      rw [tupleCondK, subtupleCode_empty, tuplePlainK]
      rfl
    rwa [maxSection_empty, hplainI] at h
  set b : ℕ := (Nat.bits N').length with hb
  have hslack : (logSlack dt N' : ℝ) = dt * b + dt := by
    simp only [logSlack, hb]
    push_cast
    ring
  have hlogN : Real.logb 2 N' ≤ b := logb_le_length_bits N'
  have hCk : ∀ k, ((tuplePlainK D x {k}).toNat : ℝ) ≤ N' + c0 := by
    intro k
    have h : tuplePlainK D x {k} ≤ ((N' + c0 : ℕ) : ℕ∞) := by
      refine (hc0 x k).trans ?_
      push_cast
      exact add_le_add (hplain k) le_rfl
    exact_mod_cast ENat.toNat_le_of_le_natCast h
  have hproj : ∀ k, Real.logb 2 (projCard A {k}) ≤ N' + c0 + logSlack dt N' := by
    intro k
    have h := hdiff {k} (mem_nonemptyParts.2 (Finset.singleton_nonempty k))
    have := (abs_le.1 h).2
    linarith [hCk k]
  set L := Real.logb 2 A.card
  have hlog2L : Real.logb 2 (2 + L) ≤ kK + b := logb_two_add_logb_card_le hAne hN'.le hproj
  have hApos : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.card_pos.2 hAne
  have hL0 : 0 ≤ L := Real.logb_nonneg one_lt_two hApos
  have hlog2L0 : 0 ≤ Real.logb 2 (2 + L) :=
    Real.logb_nonneg one_lt_two (by linarith)
  obtain ⟨m', B, hm', hAB, hprod⟩ := hC (fun _ => Fin m) A
  have hm'pos : 0 < m' := by
    obtain ⟨a, ha⟩ := hAne
    rw [hAB, Finset.mem_biUnion] at ha
    obtain ⟨k, -, -⟩ := ha
    exact k.pos
  obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image Finset.univ (fun k => (B k).card)
    (Finset.univ_nonempty_iff.2 ⟨⟨0, hm'pos⟩⟩)
  have hcardA : (A.card : ℝ) ≤ m' * (B k0).card := by
    have h1 : A.card ≤ ∑ k, (B k).card := by
      conv_lhs => rw [hAB]
      exact Finset.card_biUnion_le
    have h2 : ∑ k, (B k).card ≤ ∑ _k : Fin m', (B k0).card :=
      Finset.sum_le_sum fun k _ => hk0 k (Finset.mem_univ _)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
    exact_mod_cast h1.trans h2
  have hB0 : (B k0).Nonempty := by
    rw [← Finset.card_pos, ← Nat.cast_pos (α := ℝ)]
    by_contra h
    push Not at h
    have := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) m')
    linarith
  have hsub : B k0 ⊆ A := by
    rw [hAB]
    exact Finset.subset_biUnion_of_mem B (Finset.mem_univ k0)
  have h1 := evalLogSize_le_add_of_subset f hAunif hsub hB0 hcardA
  have h2 : f.evalLogSize (B k0) ≤ d * Real.logb 2 (2 + L) := by
    have h := hprod k0
    rw [prod_projCard_rpow_eq_two_rpow f hB0] at h
    have h' := Real.logb_le_logb_of_le (b := 2) one_lt_two (by positivity) h
    rwa [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_pow] at h'
  have hm'r : (1 : ℝ) ≤ m' := by exact_mod_cast hm'pos
  have h3 : Real.logb 2 ((N' : ℝ) ^ dt * m') ≤ dt * b + d * (kK + b) := by
    rw [Real.logb_mul (by positivity) (by linarith), Real.logb_pow]
    have hm'log : Real.logb 2 m' ≤ d * Real.logb 2 (2 + L) := by
      rw [← Real.logb_pow]
      exact Real.logb_le_logb_of_le one_lt_two (by linarith) hm'
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hdt0 : (0 : ℝ) ≤ dt := Nat.cast_nonneg dt
    nlinarith [mul_le_mul_of_nonneg_left hlog2L hd0,
      mul_le_mul_of_nonneg_left hlogN hdt0]
  have h3' : 0 ≤ Real.logb 2 ((N' : ℝ) ^ dt * m') :=
    Real.logb_nonneg one_lt_two
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN'r) hm'r)
  have h4 := evalComplexity_le_evalLogSize_add f D x A hdiff
  rw [hslack] at h4
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hdtb : (0 : ℝ) ≤ dt * b + dt := by positivity
  have hfinal : f.evalComplexity D x ≤ C * b + C := by
    have e1 : S * (dt * b + dt) ≤ T * (dt * b + dt) :=
      mul_le_mul_of_nonneg_right hST hdtb
    have e2 : S * Real.logb 2 ((N' : ℝ) ^ dt * m') ≤
        T * (dt * b + d * (kK + b)) := mul_le_mul hST h3 h3' hT0
    have e3 : (d : ℝ) * Real.logb 2 (2 + L) ≤ d * (kK + b) :=
      mul_le_mul_of_nonneg_left hlog2L (Nat.cast_nonneg d)
    have hCr : (C : ℝ) = 2 * T * dt + d * kK + d + T * d * kK + T * d := by
      rw [hC']
      push_cast
      ring
    have hkK0 : (0 : ℝ) ≤ kK := Nat.cast_nonneg _
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hdt0 : (0 : ℝ) ≤ dt := Nat.cast_nonneg dt
    rw [hCr]
    have p1 := mul_nonneg (mul_nonneg hd0 hkK0) hb0
    have p2 := mul_nonneg (mul_nonneg (mul_nonneg hT0 hd0) hkK0) hb0
    have p3 := mul_nonneg hT0 hdt0
    have p4 := mul_nonneg hT0 hd0
    have e4 : f.evalComplexity D x ≤
        T * (dt * b + dt) + T * (dt * b + d * (kK + b)) + d * (kK + b) := by
      linarith
    linarith
  have hslackC : (C : ℝ) * b + C = logSlack C N' := by
    simp only [logSlack, hb]
    push_cast
    ring
  have hmax : (logSlack C N' : ℝ) ≤ logSlack (3 * C) N := by
    exact_mod_cast logSlack_max_two_le_three_mul C N
  linarith

/-- **Theorem 214.**  For real coefficients `λ_I` of arbitrary signs, the following are
equivalent:
* there is a constant `d` such that every finite `A ⊆ Y_1 × ⋯ × Y_n` is the union of at most
  `(2 + log |A|)^d` sets (possibly overlapping), each of which satisfies
  `∏_I m(I)^{λ_I} ≤ (2 + log |A|)^d` for its own projections;
* `∑_I λ_I C(x_I) ≤ O(log N)` for all strings of complexity at most `N`, i.e.
  `HoldsForComplexitiesCplx f D`.
The book writes `(log |A|)^d` for both bounds; the factor `(2 + log₂ |A|)^d` used here is a
repair of the degenerate small-alphabet case (`(log |A|)^d ≤ 1` for `|A| ≤ 2`), equivalent to
the printed one up to a change of `d` for `|A| ≥ 4`; see the module docstring.
SUV Theorem 214, p. 333. -/
theorem union_decomposition_iff_holdsForComplexitiesCplx (f : LinearForm n) (D : Map)
    (hD : isOptimalConditional D) :
    (∃ d : ℕ, ∀ (Y : Fin n → Type) [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i)),
        ∃ (m : ℕ) (B : Fin m → Finset (∀ i, Y i)),
          (m : ℝ) ≤ (2 + Real.logb 2 A.card) ^ d ∧ A = Finset.univ.biUnion B ∧
          ∀ k, ∏ I ∈ nonemptyParts n, (projCard (B k) I : ℝ) ^ f I
            ≤ (2 + Real.logb 2 A.card) ^ d) ↔
      HoldsForComplexitiesCplx f D := by
  constructor
  · rintro ⟨d, hd⟩
    exact holdsForComplexitiesCplx_of_union_decomposition f D hD d hd
  · intro h
    exact exists_union_decomposition_of_holdsForEntropies f
      ((holdsForEntropies_iff_holdsForComplexitiesCplx f D hD).2 h)

end Kolmogorov
