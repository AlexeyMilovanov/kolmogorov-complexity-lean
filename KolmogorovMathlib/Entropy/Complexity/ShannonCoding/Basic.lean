import KolmogorovMathlib.Entropy.Complexity.Basic
import KolmogorovMathlib.CommonInformation.FixedHistogramRank.PlainAndFibreDecoders
import KolmogorovMathlib.Complexity.CanonicalObjects.Counting
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Entropy.Conditional
import KolmogorovMathlib.Entropy.Inequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.EquivFin

/-!
# The Shannon coding theorem for rational probabilities (Theorems 150 and 151)

SUV Section 7.3.5, pp. 231–232, Theorems 150 and 151.

Theorem 150 (`exists_code_error_le_iff_exists_card_le`) characterises the pairs `(N, m)` for
which an encoder `A^N → 𝔹^m` and a decoder `𝔹^m → A^N` with error probability at most `ε` exist:
the `2^m` most probable values of `ξ^N` must carry probability at least `1 − ε`.  Theorem 151
shows that `N H(ξ) ± c√N` bits are the threshold, for a distribution with rational `p_i`: with
`N H(ξ) + c√N` bits the error can be made at most `ε` (`exists_const_code_error_le`), and with
`N H(ξ) − c√N` bits the probability of correct decoding is at most `ε`
(`exists_const_prob_correct_le`).
-/

namespace Kolmogorov

open Finset

/-! ### Theorem 150 -/

/-- **A code of `m` bits with error probability at most `ε` exists if and only if the `2^m` most
probable values of `ξ^N` have total probability at least `1 − ε`.**  "The `2^m` most probable
values" (ties allowed, and possibly fewer than `2^m` values) is read as "some set of at most `2^m`
values", whose largest possible probability is exactly the probability of the `2^m` most probable
values.  SUV Theorem 150, p. 231. -/
theorem exists_code_error_le_iff_exists_card_le (A : Type*) [Fintype A]
    (μ : FiniteProbSpace A) (N m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (∃ (e : (Fin N → A) → Fin m → Bool) (d : (Fin m → Bool) → Fin N → A),
        (μ.power N).probOfPred (fun w => d (e w) ≠ w) ≤ ε) ↔
      ∃ S : Finset (Fin N → A), S.card ≤ 2 ^ m ∧ 1 - ε ≤ (μ.power N).probOf S := by
  have _ := hε
  constructor
  · rintro ⟨e, d, h_err⟩
    let P : (Fin N → A) → Prop := fun w => d (e w) = w
    let S := @Finset.filter _ P (Classical.decPred _) Finset.univ
    use S
    constructor
    · have h_inj : ∀ w₁ w₂ : S, e w₁ = e w₂ → w₁ = w₂ := by
        intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h_eq
        have h_w1 : w₁ = d (e w₁) := (@mem_filter _ _ (Classical.decPred _) _ _).mp hw₁ |>.2.symm
        have h_w2 : w₂ = d (e w₂) := (@mem_filter _ _ (Classical.decPred _) _ _).mp hw₂ |>.2.symm
        apply Subtype.ext
        change w₁ = w₂
        rw [h_w1, h_w2, h_eq]
      have h_card_S_le_card_codomain : Fintype.card S ≤ Fintype.card (Fin m → Bool) := by
        let e_S : S → (Fin m → Bool) := fun w => e w
        exact Fintype.card_le_of_injective e_S h_inj
      have h_card_codomain : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
      have h_S_card : S.card = Fintype.card S := Fintype.card_coe S |>.symm
      omega
    · have h_probOf : (μ.power N).probOf S = (μ.power N).probOfPred P := by
        unfold FiniteProbSpace.probOfPred FiniteProbSpace.probOf
        have h_sum_S : ∑ ω ∈ S, (μ.power N).prob ω =
            ∑ ω ∈ Finset.univ, @ite _ (P ω) (Classical.propDecidable _)
              ((μ.power N).prob ω) (0 : ℝ) := by
          apply @sum_filter _ _ _ _ _ (Classical.decPred _)
        rw [h_sum_S]
        apply sum_congr rfl
        intro w _
        simp [Set.indicator]
      have h_sum_total : (μ.power N).probOfPred P +
          (μ.power N).probOfPred (fun w => d (e w) ≠ w) = 1 := by
        unfold FiniteProbSpace.probOfPred
        rw [← sum_add_distrib]
        have h_add : ∑ x, (Set.indicator {ω | P ω} (μ.power N).prob x +
            Set.indicator {ω | d (e ω) ≠ ω} (μ.power N).prob x) = ∑ x, (μ.power N).prob x := by
          apply sum_congr rfl
          intro w _
          simp [Set.indicator]
          by_cases h_eq : d (e w) = w
          · have hp : P w := h_eq
            simp [h_eq, hp]
          · have hnp : ¬ P w := h_eq
            simp [h_eq, hnp]
        rw [h_add]
        exact (μ.power N).sum_prob
      linarith
  · rintro ⟨S, h_card, h_prob⟩
    have h_nonempty_A : Nonempty A := by
      by_contra h_empty
      have h_univ_empty : (Finset.univ : Finset A) = ∅ := by
        ext x
        simp only [not_nonempty_iff_imp_false] at h_empty
        exact (h_empty x).elim
      have h_sum := μ.sum_prob
      rw [h_univ_empty, sum_empty] at h_sum
      exact zero_ne_one h_sum
    have h_nonempty : Nonempty (Fin N → A) := by
      obtain ⟨a⟩ := h_nonempty_A
      exact ⟨fun _ => a⟩
    obtain ⟨w₀⟩ := h_nonempty
    have h_card_S_le : Fintype.card S ≤ Fintype.card (Fin m → Bool) := by
      have h_S_card : Fintype.card S = S.card := Fintype.card_coe S
      have h_codomain : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
      omega
    have h_inj : Nonempty (S ↪ (Fin m → Bool)) := Function.Embedding.nonempty_of_card_le h_card_S_le
    obtain ⟨f_emb⟩ := h_inj
    let f : S → (Fin m → Bool) := f_emb
    have h_inj_f : Function.Injective f := f_emb.injective
    have hd : ∃ d : (Fin m → Bool) → Fin N → A, ∀ s : S, d (f s) = s := by
      let d_partial (b : Fin m → Bool) : Fin N → A :=
        if h : ∃ s : S, f s = b then
          (@Classical.choose S (fun s => f s = b) h).val
        else w₀
      use d_partial
      intro s
      have h : ∃ s' : S, f s' = f s := ⟨s, rfl⟩
      have eq : @Classical.choose S (fun s' => f s' = f s) h = s :=
        h_inj_f (@Classical.choose_spec S (fun s' => f s' = f s) h)
      have eq2 : d_partial (f s) = (@Classical.choose S (fun s' => f s' = f s) h).val := by
        unfold d_partial
        rw [dite_eq_left h]
      rw [eq2, eq]
    obtain ⟨d, hd_eq⟩ := hd
    let b₀ : Fin m → Bool := fun _ => false
    have h_dec : DecidablePred (· ∈ S) := Classical.decPred _
    let e (w : Fin N → A) : Fin m → Bool :=
      if h : w ∈ S then f ⟨w, h⟩ else b₀
    use e, d
    have h_prob_succ_ge : (μ.power N).probOf S ≤ (μ.power N).probOfPred (fun w => d (e w) = w) := by
      unfold FiniteProbSpace.probOfPred FiniteProbSpace.probOf
      have h_sum_S : ∑ ω ∈ S, (μ.power N).prob ω =
          ∑ ω ∈ Finset.univ, @ite _ (ω ∈ S) (Classical.propDecidable _)
              ((μ.power N).prob ω) (0 : ℝ) := by
        have h_filter : S = @Finset.filter _ (· ∈ S)
          (Classical.decPred _) Finset.univ := by ext x; simp
        nth_rw 1 [h_filter]
        apply @sum_filter _ _ _ _ _ (Classical.decPred _)
      rw [h_sum_S]
      apply sum_le_sum
      intro w _
      simp only [Set.indicator]
      split_ifs with h_S h_eq
      · rfl
      · have eq1 : e w = f ⟨w, h_S⟩ := by
          unfold e
          rw [dite_eq_left h_S]
        have eq2 : d (f ⟨w, h_S⟩) = w := hd_eq ⟨w, h_S⟩
        have h_contradiction : d (e w) = w := by rw [eq1, eq2]
        exact (h_eq h_contradiction).elim
      · exact (μ.power N).prob_nonneg w
      · exact le_rfl
    have h_prob_err : (μ.power N).probOfPred (fun w => d (e w) ≠ w) =
        1 - (μ.power N).probOfPred (fun w => d (e w) = w) := by
      have h_sum_total : (μ.power N).probOfPred (fun w => d (e w) = w) +
          (μ.power N).probOfPred (fun w => d (e w) ≠ w) = 1 := by
        unfold FiniteProbSpace.probOfPred
        rw [← sum_add_distrib]
        have h_add : ∑ x, (Set.indicator {ω | d (e ω) = ω} (μ.power N).prob x +
            Set.indicator {ω | d (e ω) ≠ ω} (μ.power N).prob x) = ∑ x, (μ.power N).prob x := by
          apply sum_congr rfl
          intro w _
          simp [Set.indicator]
          by_cases h_eq : d (e w) = w
          · simp [h_eq]
          · simp [h_eq]
        rw [h_add]
        exact (μ.power N).sum_prob
      linarith
    linarith

/-! ### Theorem 151 -/

/-- The upper-tail half of Theorem 149: with high probability, an i.i.d. word has a description
shorter than `N H(μ) + c√N`.  This is the probabilistic input to the direct coding theorem. -/
private lemma power_sum_mul_prod_for_upper {Ω : Type*} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (N : ℕ) (h : Fin N → Ω → ℝ) :
    ∑ w : Fin N → Ω, (μ.power N).prob w * ∏ k, h k (w k) =
      ∏ k, ∑ a, μ.prob a * h k a := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [FiniteProbSpace.power, Finset.prod_mul_distrib]

private lemma power_sum_sq_eq_for_upper {Ω : Type*} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (g : Ω → ℝ) (hg : ∑ a, μ.prob a * g a = 0) (N : ℕ) :
    ∑ w : Fin N → Ω, (μ.power N).prob w * (∑ i, g (w i)) ^ 2 =
      N * ∑ a, μ.prob a * g a ^ 2 := by
  classical
  have hsq : ∀ w : Fin N → Ω, (∑ i, g (w i)) ^ 2 = ∑ i, ∑ j,
      ∏ k, (if k = i then g (w k) else 1) * (if k = j then g (w k) else 1) := by
    intro w
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp
  have h1 : ∀ i j : Fin N, (∏ k, ∑ a, μ.prob a *
      ((if k = i then g a else 1) * (if k = j then g a else 1))) =
      if i = j then ∑ a, μ.prob a * g a ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      rw [Finset.prod_eq_single i]
      · simp [sq]
      · intro k _ hk
        simp [hk, μ.sum_prob]
      · exact fun h => absurd (Finset.mem_univ i) h
    · exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [hij] using hg)
  calc
    ∑ w : Fin N → Ω, (μ.power N).prob w * (∑ i, g (w i)) ^ 2 =
        ∑ i, ∑ j, ∑ w : Fin N → Ω, (μ.power N).prob w *
          ∏ k, (if k = i then g (w k) else 1) *
            (if k = j then g (w k) else 1) := by
      simp_rw [hsq, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin N, ∑ j : Fin N,
        if i = j then ∑ a, μ.prob a * g a ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← h1, ← power_sum_mul_prod_for_upper μ N
        (fun k a => (if k = i then g a else 1) * (if k = j then g a else 1))]
    _ = N * ∑ a, μ.prob a * g a ^ 2 := by simp

private lemma multinomial_count_mul_prod_le_one_for_upper {k : ℕ}
    (q : Fin k → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1)
    (v : List (Fin k)) :
    (Nat.multinomial univ (fun j => v.count j) : ℝ) * (v.map q).prod ≤ 1 := by
  classical
  have hprod : (v.map q).prod = ∏ j, q j ^ v.count j := by
    rw [Finset.prod_list_map_count]
    exact Finset.prod_subset (Finset.subset_univ _) fun j _ hj => by
      simp [List.count_eq_zero_of_not_mem (by simpa using hj)]
  have hmem : (fun j => v.count j) ∈ (univ : Finset (Fin k)).piAntidiag v.length := by
    simp only [mem_piAntidiag, ne_eq, mem_univ, implies_true, and_true]
    exact (length_eq_sum_count v).symm
  have hexp := Finset.sum_pow_eq_sum_piAntidiag (univ : Finset (Fin k)) q v.length
  rw [hq1, one_pow] at hexp
  rw [hprod, hexp]
  exact Finset.single_le_sum
    (f := fun κ => (Nat.multinomial univ κ : ℝ) * ∏ i, q i ^ κ i)
    (fun κ _ => mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (hq0 i) _)) hmem

private lemma power_prob_eq_rpow_neg_selfInfo_for_upper {Ω : Type*} [Fintype Ω]
    (μ : FiniteProbSpace Ω) {N : ℕ} (w : Fin N → Ω)
    (hP : 0 < (μ.power N).prob w) :
    (μ.power N).prob w = 2 ^ (-∑ i, -Real.logb 2 (μ.prob (w i))) := by
  have hP' : 0 < ∏ i, μ.prob (w i) := hP
  have hne : ∀ i ∈ (univ : Finset (Fin N)), μ.prob (w i) ≠ 0 :=
    Finset.prod_ne_zero_iff.1 hP'.ne'
  rw [Finset.sum_neg_distrib, neg_neg, ← Real.logb_prod _ _ hne,
    Real.rpow_logb (by norm_num) (by norm_num) hP']
  rfl

private lemma exists_plainK_le_selfInfo_add_size_for_upper
    (A : Type*) [Fintype A] [Encodable A] (μ : FiniteProbSpace A)
    (D : Map) (hD : isOptimalConditional D) :
    ∃ C : ℕ, ∀ (N : ℕ) (w : Fin N → A), 0 < (μ.power N).prob w →
      ((plainK D (finWordBits A w)).toNat : ℝ) ≤
        ∑ i, -Real.logb 2 (μ.prob (w i)) + C * Nat.size N + C := by
  classical
  set k := Fintype.card A
  let idx : A → Fin k := fun a => ⟨alphabetIndex A a, alphabetIndex_lt_card a⟩
  have hbij : Function.Bijective idx := (Fintype.bijective_iff_injective_and_card idx).2
    ⟨fun a b h => alphabetIndex_injective (congrArg Fin.val h), by simp [k]⟩
  let e := Equiv.ofBijective idx hbij
  let table : List BitString := (List.range k).map (natBitsFixed (alphabetWidth A))
  let g : BitString → BitString := fun x =>
    ((Encodable.decode (bitsToNat x) : Option (List ℕ)).getD []).flatMap
      (fun n => table.getD n [])
  have hg : Computable g := (Primrec.list_flatMap
    (Primrec.option_getD.comp (Primrec.decode.comp bitsToNat_primrec) (Primrec.const []))
    ((Primrec.list_getD []).comp (Primrec.const table) Primrec.snd).to₂).to_comp
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD g hg
  obtain ⟨c2, hc2⟩ := plainK_fixedHistogramWord_le_size_multinomial_add_params D hD
  refine ⟨3 * k + 2 * Nat.size k + c1 + c2 + 1, fun N w hP => ?_⟩
  set v : List (Fin k) := List.ofFn fun i => idx (w i)
  have hgv : g (finiteWordCode v) = finWordBits A w := by
    have hmap : v.map FiniteLetterCode.encode =
        List.ofFn fun i => alphabetIndex A (w i) := by
      simp [v, List.map_ofFn]
      rfl
    simp only [g, finiteWordCode, bitsToNat_bits, hmap, Encodable.encodek,
      Option.getD_some]
    simp only [finWordBits, wordBits, Code.encodeWord, List.flatMap, List.map_ofFn]
    congr 2
    funext i
    have hi : alphabetIndex A (w i) < k := alphabetIndex_lt_card (w i)
    simp [table, alphabetCode, List.getElem?_range hi]
  set f : Fin k → ℕ := fun j => v.count j
  set M := Nat.multinomial univ f
  set L := ∑ i, -Real.logb 2 (μ.prob (w i))
  have hK : plainK D (finWordBits A w) ≤
      ((M.size + 2 * k.size + 2 * ∑ j, (f j).size + k + c2 + c1 : ℕ) : ENat) := by
    rw [← hgv]
    refine (hc1 _).trans ?_
    refine (add_le_add_left (hc2 k f v fun j => rfl) _).trans (le_of_eq ?_)
    push_cast
    ring
  have hK' : ((plainK D (finWordBits A w)).toNat : ℝ) ≤
      ((M.size + 2 * k.size + 2 * ∑ j, (f j).size + k + c2 + c1 : ℕ) : ℝ) := by
    exact_mod_cast ENat.toNat_le_of_le_natCast hK
  have hp1 : ∀ a, μ.prob a ≤ 1 := fun a => by
    simpa [μ.sum_prob] using
      Finset.single_le_sum (fun b _ => μ.prob_nonneg b) (Finset.mem_univ a)
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ =>
    neg_nonneg.2 (Real.logb_nonpos one_lt_two (μ.prob_nonneg _) (hp1 _))
  have hMP : (M : ℝ) * (μ.power N).prob w ≤ 1 := by
    have h := multinomial_count_mul_prod_le_one_for_upper
      (fun j => μ.prob (e.symm j)) (fun j => μ.prob_nonneg _)
      (by rw [e.symm.sum_comp]; exact μ.sum_prob) v
    convert h using 2
    simp [v, List.map_ofFn, FiniteProbSpace.power, List.prod_ofFn, e]
  have hM : (M : ℝ) < 2 ^ (⌊L⌋₊ + 1) := by
    calc
      (M : ℝ) ≤ 1 / (μ.power N).prob w := (le_div_iff₀ hP).2 hMP
      _ = 2 ^ L := by
        rw [power_prob_eq_rpow_neg_selfInfo_for_upper μ w hP,
          Real.rpow_neg (by norm_num), one_div, inv_inv]
      _ < 2 ^ ((⌊L⌋₊ + 1 : ℕ) : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
          (by push_cast; exact Nat.lt_floor_add_one L)
      _ = _ := Real.rpow_natCast _ _
  have hsM : M.size ≤ ⌊L⌋₊ + 1 := Nat.size_le.2 (by exact_mod_cast hM)
  have hsMr : (M.size : ℝ) ≤ L + 1 := by
    have h1 := Nat.floor_le hL0
    have h2 : (M.size : ℝ) ≤ ⌊L⌋₊ + 1 := by exact_mod_cast hsM
    linarith
  have hsum : ∑ j, (f j).size ≤ k * N.size := by
    calc
      ∑ j, (f j).size ≤ ∑ _j : Fin k, N.size := Finset.sum_le_sum fun j _ =>
        Nat.size_le_size (by
          simpa [f, v] using List.count_le_length (a := j) (l := v))
      _ = k * N.size := by simp
  have hsumr : ((∑ j, (f j).size : ℕ) : ℝ) ≤ k * N.size := by
    exact_mod_cast hsum
  push_cast at hK' hsumr ⊢
  have hNs : (0 : ℝ) ≤ N.size := Nat.cast_nonneg _
  have hks : (0 : ℝ) ≤ k.size := Nat.cast_nonneg _
  nlinarith

private lemma exists_const_prob_abs_sum_sub_gt_le_for_upper
    {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω) (f : Ω → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℕ, ∀ N : ℕ, (μ.power N).probOfPred
      (fun w => c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|) ≤ δ := by
  classical
  set g : Ω → ℝ := fun a => f a - μ.expect f
  set V := ∑ a, μ.prob a * g a ^ 2
  have hV : 0 ≤ V := Finset.sum_nonneg fun a _ =>
    mul_nonneg (μ.prob_nonneg a) (sq_nonneg _)
  obtain ⟨c, hc⟩ := exists_nat_gt (V / δ)
  have hVc : V < δ * c := by
    rw [div_lt_iff₀ hδ] at hc
    linarith
  have hc1 : (1 : ℝ) ≤ c := by
    have : (0 : ℝ) < c := lt_of_le_of_lt (div_nonneg hV hδ.le) hc
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at this)
  refine ⟨c, fun N => ?_⟩
  have hg : ∑ a, μ.prob a * g a = 0 := by
    simp only [g, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, μ.sum_prob,
      one_mul]
    simp [FiniteProbSpace.expect]
  have hpt : ∀ w : Fin N → Ω, Set.indicator
      {w | c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|}
        (μ.power N).prob w * ((c : ℝ) ^ 2 * N) ≤
        (μ.power N).prob w * (∑ i, g (w i)) ^ 2 := by
    intro w
    have hcent : ∑ i, g (w i) = ∑ i, f (w i) - N * μ.expect f := by
      simp [g]
    by_cases hw : w ∈
        {w | c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|}
    · rw [Set.indicator_of_mem hw]
      refine mul_le_mul_of_nonneg_left ?_ ((μ.power N).prob_nonneg w)
      have hw' : c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f| := hw
      calc
        (c : ℝ) ^ 2 * N = (c * Real.sqrt N) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
        _ ≤ |∑ i, f (w i) - N * μ.expect f| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hw'.le 2
        _ = (∑ i, g (w i)) ^ 2 := by rw [sq_abs, hcent]
    · rw [Set.indicator_of_notMem hw, zero_mul]
      exact mul_nonneg ((μ.power N).prob_nonneg w) (sq_nonneg _)
  have hmul : (μ.power N).probOfPred
      (fun w => c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|) *
        ((c : ℝ) ^ 2 * N) ≤ N * V := by
    rw [FiniteProbSpace.probOfPred, Finset.sum_mul,
      ← power_sum_sq_eq_for_upper μ g hg N]
    exact Finset.sum_le_sum fun w _ => hpt w
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [FiniteProbSpace.probOfPred, hδ.le]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 := (μ.power N).probOfPred_nonneg
    (fun w => c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|)
  have h2 : (μ.power N).probOfPred
      (fun w => c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|) *
        (c : ℝ) ^ 2 ≤ V := by
    nlinarith
  nlinarith

private lemma size_le_two_mul_sqrt_for_upper (N : ℕ) :
    (Nat.size N : ℝ) ≤ 2 * Real.sqrt N := by
  have key : ∀ s : ℕ, s ^ 2 ≤ 2 ^ (s + 1) := by
    intro s
    induction s with
    | zero => norm_num
    | succ n ih =>
      rcases lt_or_ge n 3 with h | h
      · interval_cases n <;> norm_num
      · rw [pow_succ 2 (n + 1)]
        nlinarith
  have hnat : Nat.size N ^ 2 ≤ 4 * N := by
    rcases N.eq_zero_or_pos with rfl | hN
    · simp
    have hs : 0 < Nat.size N := Nat.size_pos.2 hN
    have h2 : 2 ^ (Nat.size N - 1) ≤ N := Nat.lt_size.1 (by omega)
    calc
      Nat.size N ^ 2 ≤ 2 ^ (Nat.size N - 1 + 2) := by
        rw [show Nat.size N - 1 + 2 = Nat.size N + 1 by omega]
        exact key _
      _ = 4 * 2 ^ (Nat.size N - 1) := by ring
      _ ≤ 4 * N := by omega
  have h : (Nat.size N : ℝ) ^ 2 ≤ (2 * Real.sqrt N) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    exact_mod_cast (show Nat.size N ^ 2 ≤ 2 ^ 2 * N by simpa using hnat)
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) two_ne_zero).1 h

private lemma expect_neg_logb_prob_for_upper (A : Type*) [Fintype A]
    (μ : FiniteProbSpace A) :
    μ.expect (fun a => -Real.logb 2 (μ.prob a)) = entropyDist μ.prob := by
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [negMulLog2, Real.negMulLog, Real.logb]
  ring

private lemma probOfPred_congr_imp {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (P Q : Ω → Prop) (h : ∀ ω, P ω → Q ω) :
    μ.probOfPred P ≤ μ.probOfPred Q := by
  have H : ∀ ω, P ω → Q ω ∨ False := fun ω hω => Or.inl (h ω hω)
  have h_le_add : μ.probOfPred P ≤ μ.probOfPred Q + μ.probOfPred (fun _ => False) := by
    classical
    unfold FiniteProbSpace.probOfPred
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hP : P i
    · have hQ : Q i ∨ False := H i hP
      rcases hQ with hQi | hF
      · rw [Set.indicator_of_mem (s := {ω | P ω}) hP, Set.indicator_of_mem (s := {ω | Q ω}) hQi]
        have h_nonneg : 0 ≤ {ω | False}.indicator μ.prob i := by
          by_cases hF : i ∈ {ω | False}
          · rw [Set.indicator_of_mem hF]; exact μ.prob_nonneg i
          · rw [Set.indicator_of_notMem hF]
        linarith
      · contradiction
    · rw [Set.indicator_of_notMem (s := {ω | P ω}) hP]
      have hn1 : 0 ≤ {ω | Q ω}.indicator μ.prob i := by
        by_cases hQi : i ∈ {ω | Q ω}
        · rw [Set.indicator_of_mem hQi]; exact μ.prob_nonneg i
        · rw [Set.indicator_of_notMem hQi]
      have hn2 : 0 ≤ {ω | False}.indicator μ.prob i := by
        by_cases hF : i ∈ {ω | False}
        · rw [Set.indicator_of_mem hF]; exact μ.prob_nonneg i
        · rw [Set.indicator_of_notMem hF]
      linarith
  have hF : μ.probOfPred (fun _ => False) = 0 := by
    unfold FiniteProbSpace.probOfPred
    exact Finset.sum_eq_zero (fun i _ =>
      by rw [Set.indicator_of_notMem (s := {ω | False}) (by simp)])
  rw [hF, add_zero] at h_le_add
  exact h_le_add

private lemma exists_const_prob_plainK_lt_mul_entropyDist (A : Type*) [Fintype A]
    [Encodable A] (μ : FiniteProbSpace A) (hrat : ∀ a, ∃ r : ℚ, μ.prob a = (r : ℝ))
    (D : Map) (hD : isOptimalConditional D) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N : ℕ, 0 < N →
      1 - ε ≤ (μ.power N).probOfPred fun w =>
        ((plainK D (finWordBits A w)).toNat : ℝ) <
          (N : ℝ) * entropyDist μ.prob + c * Real.sqrt N := by
  classical
  have _ := hrat
  obtain ⟨c₀, hc₀⟩ := exists_const_prob_abs_sum_sub_gt_le_for_upper μ
    (fun a => -Real.logb 2 (μ.prob a)) hε
  rw [expect_neg_logb_prob_for_upper] at hc₀
  obtain ⟨C, hC⟩ := exists_plainK_le_selfInfo_add_size_for_upper A μ D hD
  refine ⟨c₀ + 3 * C + 1, fun N hN => ?_⟩
  let bad : (Fin N → A) → Prop := fun w =>
    c₀ * Real.sqrt N <
      |∑ i, -Real.logb 2 (μ.prob (w i)) - N * entropyDist μ.prob|
  have hbad : (μ.power N).probOfPred bad ≤ ε := hc₀ N
  have hcompl : (μ.power N).probOfPred bad +
      (μ.power N).probOfPred (fun w => ¬bad w) = 1 := by
    unfold FiniteProbSpace.probOfPred
    rw [← Finset.sum_add_distrib, ← (μ.power N).sum_prob]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases hw : bad w <;> simp [hw]
  have hgood : 1 - ε ≤ (μ.power N).probOfPred (fun w => ¬bad w) := by
    linarith
  have herase : (μ.power N).probOfPred (fun w => ¬bad w) =
      (μ.power N).probOfPred
        (fun w => ¬bad w ∧ (μ.power N).prob w ≠ 0) := by
    unfold FiniteProbSpace.probOfPred
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases hw : bad w
    · simp [hw]
    · by_cases hp : (μ.power N).prob w = 0 <;> simp [hw, hp]
  rw [herase] at hgood
  refine hgood.trans (probOfPred_congr_imp (μ.power N) _ _ fun w hw => ?_)
  have hpos : 0 < (μ.power N).prob w :=
    lt_of_le_of_ne ((μ.power N).prob_nonneg w) (Ne.symm hw.2)
  have hup := hC N w hpos
  have hdev :
      |∑ i, -Real.logb 2 (μ.prob (w i)) - N * entropyDist μ.prob| ≤
        c₀ * Real.sqrt N := not_lt.1 hw.1
  have hself : ∑ i, -Real.logb 2 (μ.prob (w i)) ≤
      N * entropyDist μ.prob + c₀ * Real.sqrt N := by
    linarith [le_abs_self
      (∑ i, -Real.logb 2 (μ.prob (w i)) - N * entropyDist μ.prob)]
  have hsize := size_le_two_mul_sqrt_for_upper N
  have hsqrt : (1 : ℝ) ≤ Real.sqrt N :=
    Real.one_le_sqrt.2 (by exact_mod_cast hN)
  push_cast at hup hself ⊢
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  nlinarith

/-- Words having plain descriptions shorter than `m` form a set of at most `2^m` elements.
Consequently, if those words have probability at least `1 - ε`, they are a valid typical set. -/
private lemma exists_card_le_pow_of_prob_plainK_lt (A : Type*) [Fintype A] [Encodable A]
    (μ : FiniteProbSpace A) (D : Map) (hD : isOptimalConditional D) (N m : ℕ) {ε : ℝ}
    (hprob : 1 - ε ≤ (μ.power N).probOfPred fun w =>
      plainK D (finWordBits A w) < (m : ENat)) :
    ∃ S : Finset (Fin N → A), S.card ≤ 2 ^ m ∧ 1 - ε ≤ (μ.power N).probOf S := by
  classical
  obtain ⟨_, hcount⟩ := card_plainK_lt_mem_Icc D hD
  let T := {x : BitString | plainK D x < (m : ENat)}
  let S := (Finset.univ : Finset (Fin N → A)).filter fun w => finWordBits A w ∈ T
  have hT : T.Finite := by simpa [T] using (hcount m).1
  have hcard : S.card ≤ T.ncard := by
    rw [Set.ncard_eq_toFinset_card T hT]
    refine Finset.card_le_card_of_injOn (finWordBits A) (t := hT.toFinset) ?_ ?_
    · intro w hw
      simpa [T] using (Finset.mem_filter.1 hw).2
    · intro w _ w' _ h
      exact List.ofFn_injective (wordBits_injective h)
  refine ⟨S, hcard.trans (hcount m).2.2, ?_⟩
  calc
    1 - ε ≤ (μ.power N).probOfPred fun w => plainK D (finWordBits A w) < (m : ENat) :=
      hprob
    _ = (μ.power N).probOf S := by
      unfold FiniteProbSpace.probOfPred FiniteProbSpace.probOf
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w _
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      by_cases hw : plainK D (finWordBits A w) < (m : ENat) <;> simp [T, hw]

/-- **`N H(ξ) + c√N` bits suffice.**  For every `ε > 0` there is a `c` such that for every `N` the
values of `ξ^N` can be encoded and decoded with `N H(ξ) + c√N` bits with error probability at
most `ε`.  The number of bits must be an integer; the statement allows every `m` with
`N H(ξ) + c√N ≤ m`, which is the book's claim since more bits can only help.
SUV Theorem 151(a), p. 231. -/
theorem exists_const_code_error_le (A : Type*) [Fintype A]
    (μ : FiniteProbSpace A) (hrat : ∀ a, ∃ r : ℚ, μ.prob a = (r : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N m : ℕ, (N : ℝ) * entropyDist μ.prob + c * Real.sqrt N ≤ m →
      ∃ (e : (Fin N → A) → Fin m → Bool) (d : (Fin m → Bool) → Fin N → A),
        (μ.power N).probOfPred (fun w => d (e w) ≠ w) ≤ ε := by
  classical
  let : Encodable A := Fintype.toEncodable A
  obtain ⟨D, hD⟩ := exists_isOptimalConditional
  obtain ⟨c, hc⟩ :=
    exists_const_prob_plainK_lt_mul_entropyDist A μ hrat D hD hε
  refine ⟨c, fun N m hm => ?_⟩
  apply (exists_code_error_le_iff_exists_card_le A μ N m hε).2
  rcases N.eq_zero_or_pos with rfl | hN
  · refine ⟨Finset.univ, by simpa using Nat.one_le_pow m 2 (by decide), ?_⟩
    rw [show (μ.power 0).probOf (Finset.univ : Finset (Fin 0 → A)) = 1 by
      simpa [FiniteProbSpace.probOf] using (μ.power 0).sum_prob]
    linarith
  have hfinite : ∀ w : Fin N → A, plainK D (finWordBits A w) ≠ ⊤ := by
    obtain ⟨k, hk⟩ := plainK_le_length D hD
    exact fun w => ne_top_of_le_natCast_add (hk (finWordBits A w))
  apply exists_card_le_pow_of_prob_plainK_lt A μ D hD N m
  refine (hc N hN).trans ?_
  unfold FiniteProbSpace.probOfPred
  apply Finset.sum_le_sum
  intro w _
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs with hw hshort
  · rfl
  · exfalso
    apply hshort
    rw [← ENat.natCast_toNat (hfinite w)]
    exact_mod_cast lt_of_lt_of_le hw hm
  · exact (μ.power N).prob_nonneg w
  · rfl

/-- Correctly decoded words whose self-information is at least `t` have total probability at
most `2^m 2^{-t}`. -/
private lemma prob_correct_selfInfo_ge_le {A : Type*} [Fintype A]
    (μ : FiniteProbSpace A) (N m : ℕ) (t : ℝ)
    (e : (Fin N → A) → Fin m → Bool) (d : (Fin m → Bool) → Fin N → A) :
    (μ.power N).probOfPred
      (fun w => d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) ≤
      (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (-t) := by
  classical
  have hpt : ∀ w : Fin N → A,
      Set.indicator
          {w | d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))}
          (μ.power N).prob w ≤
        (2 : ℝ) ^ (-t) * if d (e w) = w then 1 else 0 := by
    intro w
    by_cases hw : w ∈
        {w | d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))}
    · rw [Set.indicator_of_mem hw, ite_eq_left hw.1]
      simp only [mul_one]
      rcases eq_or_lt_of_le ((μ.power N).prob_nonneg w) with hzero | hpos
      · rw [← hzero]
        positivity
      · rw [power_prob_eq_rpow_neg_selfInfo_for_upper μ w hpos]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hw.2])
    · rw [Set.indicator_of_notMem hw]
      positivity
  calc
    (μ.power N).probOfPred
        (fun w => d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) =
        ∑ w : Fin N → A,
          Set.indicator
            {w | d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))}
            (μ.power N).prob w := rfl
    _ ≤ ∑ w : Fin N → A,
        (2 : ℝ) ^ (-t) * if d (e w) = w then 1 else 0 :=
      Finset.sum_le_sum fun w _ => hpt w
    _ = (2 : ℝ) ^ (-t) *
        ∑ w : Fin N → A, if d (e w) = w then 1 else 0 := by
      rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (-t) * (2 : ℝ) ^ (m : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
      let S : Finset (Fin N → A) :=
        Finset.filter (fun w => d (e w) = w) Finset.univ
      have hsum : (∑ w : Fin N → A, if d (e w) = w then (1 : ℝ) else 0) =
          S.card := by
        rw [Finset.sum_ite]
        simp [S]
      rw [hsum]
      have hinj : Function.Injective (fun w : S => e w) := by
        intro ⟨w, hw⟩ ⟨w', hw'⟩ he
        apply Subtype.ext
        have hwc : d (e w) = w := (Finset.mem_filter.mp hw).2
        have hwc' : d (e w') = w' := (Finset.mem_filter.mp hw').2
        change w = w'
        change e w = e w' at he
        rw [← hwc, ← hwc', he]
      have hcard : Fintype.card S ≤ Fintype.card (Fin m → Bool) :=
        Fintype.card_le_of_injective _ hinj
      have hnat : S.card ≤ 2 ^ m := by
        simpa using hcard
      calc
        (S.card : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (2 : ℝ) ^ (m : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
    _ = (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (-t) := mul_comm _ _

/-- **`N H(ξ) − c√N` bits do not suffice.**  For every `ε > 0` there is a `c` such that for every
`N`, any code for `ξ^N` of length at most `N H(ξ) − c√N` decodes correctly with probability at
most `ε` (its error probability is at least `1 − ε`).  The book says "for all `N`"; `N = 0` is
excluded, because the only word of length zero is always decoded correctly.
SUV Theorem 151(b), pp. 231–232. -/
theorem exists_const_prob_correct_le (A : Type*) [Fintype A]
    (μ : FiniteProbSpace A) (hrat : ∀ a, ∃ r : ℚ, μ.prob a = (r : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N m : ℕ, 0 < N → (m : ℝ) ≤ (N : ℝ) * entropyDist μ.prob - c * Real.sqrt N →
      ∀ (e : (Fin N → A) → Fin m → Bool) (d : (Fin m → Bool) → Fin N → A),
        (μ.power N).probOfPred (fun w => d (e w) = w) ≤ ε := by
  classical
  have _ := hrat
  obtain ⟨c₁, hc₁⟩ := exists_const_prob_abs_sum_sub_gt_le_for_upper μ
    (fun a => -Real.logb 2 (μ.prob a)) (half_pos hε)
  rw [expect_neg_logb_prob_for_upper] at hc₁
  obtain ⟨c₂, hc₂⟩ := exists_nat_gt (2 / ε)
  refine ⟨c₁ + c₂, fun N m hN hm e d => ?_⟩
  have hsqrt : (1 : ℝ) ≤ Real.sqrt N :=
    Real.one_le_sqrt.2 (by exact_mod_cast hN)
  set t : ℝ := (N : ℝ) * entropyDist μ.prob - c₁ * Real.sqrt N
  have hlow : (μ.power N).probOfPred
      (fun w => ∑ i, -Real.logb 2 (μ.prob (w i)) < t) ≤ ε / 2 := by
    refine (probOfPred_congr_imp (μ.power N) _ _ fun w hw => ?_).trans (hc₁ N)
    dsimp only [t] at hw ⊢
    have hneg : (N : ℝ) * entropyDist μ.prob -
        ∑ i, -Real.logb 2 (μ.prob (w i)) > c₁ * Real.sqrt N := by
      linarith
    calc
      c₁ * Real.sqrt N <
          - (∑ i, -Real.logb 2 (μ.prob (w i)) -
            (N : ℝ) * entropyDist μ.prob) := by linarith
      _ ≤ |∑ i, -Real.logb 2 (μ.prob (w i)) -
          (N : ℝ) * entropyDist μ.prob| := neg_le_abs _
  have hhigh : (μ.power N).probOfPred
      (fun w => d (e w) = w ∧
        t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) ≤ ε / 2 := by
    refine (prob_correct_selfInfo_ge_le μ N m t e d).trans ?_
    rw [← Real.rpow_add (by norm_num)]
    have hexp : (m : ℝ) + -t ≤ -(c₂ : ℝ) := by
      dsimp only [t]
      push_cast at hm
      have hc₂0 : (0 : ℝ) ≤ c₂ := Nat.cast_nonneg c₂
      nlinarith
    calc
      (2 : ℝ) ^ ((m : ℝ) + -t) ≤ (2 : ℝ) ^ (-(c₂ : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = ((2 : ℝ) ^ (c₂ : ℝ))⁻¹ := by rw [Real.rpow_neg (by norm_num)]
      _ ≤ ε / 2 := by
        have hc₂pos : 0 < (c₂ : ℝ) := by
          have htwoeps : 0 < 2 / ε := div_pos (by norm_num) hε
          exact lt_trans htwoeps (by exact_mod_cast hc₂)
        have hpow : 2 / ε < (2 : ℝ) ^ (c₂ : ℝ) := by
          calc
            2 / ε < c₂ := by exact_mod_cast hc₂
            _ ≤ (2 : ℝ) ^ (c₂ : ℝ) := by
              have hnat : (c₂ : ℝ) ≤ (2 : ℝ) ^ c₂ := by
                exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 2) |>.le
              have hrpow : (2 : ℝ) ^ c₂ = (2 : ℝ) ^ (c₂ : ℝ) := by
                rw [Real.rpow_natCast]
              rw [← hrpow]
              exact hnat
        have hinv : ((2 : ℝ) ^ (c₂ : ℝ))⁻¹ < (2 / ε)⁻¹ :=
          (inv_lt_inv₀ (Real.rpow_pos_of_pos (by norm_num) _)
            (div_pos (by norm_num) hε)).mpr hpow
        rw [inv_div] at hinv
        exact hinv.le
  refine le_trans (probOfPred_congr_imp (μ.power N)
    (fun w => d (e w) = w)
    (fun w => (d (e w) = w ∧
      t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) ∨
      ∑ i, -Real.logb 2 (μ.prob (w i)) < t) fun w hw => ?_) ?_
  · by_cases htw : t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))
    · exact Or.inl ⟨hw, htw⟩
    · exact Or.inr (lt_of_not_ge htw)
  · have hadd : (μ.power N).probOfPred
        (fun w => d (e w) = w ∧
          t ≤ ∑ i, -Real.logb 2 (μ.prob (w i)) ∨
          ∑ i, -Real.logb 2 (μ.prob (w i)) < t) ≤
        (μ.power N).probOfPred
          (fun w => d (e w) = w ∧
            t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) +
          (μ.power N).probOfPred
            (fun w => ∑ i, -Real.logb 2 (μ.prob (w i)) < t) := by
      classical
      unfold FiniteProbSpace.probOfPred
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro w _
      rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
      change (if (d (e w) = w ∧
          t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) ∨
          (∑ i, -Real.logb 2 (μ.prob (w i)) < t)
        then (μ.power N).prob w else 0) ≤
        (if d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))
          then (μ.power N).prob w else 0) +
        if ∑ i, -Real.logb 2 (μ.prob (w i)) < t
          then (μ.power N).prob w else 0
      by_cases hp : d (e w) = w ∧
          t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))
      · rw [ite_eq_left (Or.inl hp), ite_eq_left hp]
        by_cases hq : ∑ i, -Real.logb 2 (μ.prob (w i)) < t
        · rw [ite_eq_left hq]
          linarith [(μ.power N).prob_nonneg w]
        · rw [ite_eq_right hq, add_zero]
      · by_cases hq : ∑ i, -Real.logb 2 (μ.prob (w i)) < t
        · rw [ite_eq_left (Or.inr hq), ite_eq_right hp, ite_eq_left hq, zero_add]
        · rw [ite_eq_right (not_or_intro hp hq), ite_eq_right hp, ite_eq_right hq, zero_add]
    exact hadd.trans (by linarith)

end Kolmogorov
