import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import KolmogorovMathlib.Restricted.Examples.HammingBalls
import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.Restricted.EffectiveSelection
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The properties of the list-decoding set E needed for the Hamming gap.
    `N` is the target cardinality. -/
def IsHammingListDecodingSet (n r N : ℕ) (E : Finset BitString) : Prop :=
  (∀ x ∈ E, x.length = n) ∧
  E.card = N ∧
  (∀ A : Finset BitString, hammingFamilyMem A → A.card ≤ hammingVol n r → (A ∩ E).card ≤ n)

/-! ### Helper lemmas for the Hamming volume bound -/

/-
Binomial coefficients are increasing below the midpoint.
-/
lemma choose_le_choose_right_of_le {n s r : ℕ} (hsr : s ≤ r) (hr : 2 * r ≤ n) :
    n.choose s ≤ n.choose r := by
  -- We'll use induction on $r - s$.
  induction hsr with
  | refl => rfl
  | @step r hr ih =>
    exact le_trans ( ih ( by linarith ) )
      ( Nat.choose_le_succ_of_lt_half_left ( by omega ) )

/-
The Hamming volume (sum of binomials up to `r`) is at most `(r + 1)` times the
largest term, when `2 * r ≤ n`.
-/
lemma hammingVol_le_succ_mul_choose {n r : ℕ} (hr : 2 * r ≤ n) :
    hammingVol n r ≤ (r + 1) * n.choose r := by
  exact le_trans
    (Finset.sum_le_sum fun i hi =>
      choose_le_choose_right_of_le (Finset.mem_range_succ_iff.mp hi) hr)
    (by norm_num)

/-
Stirling lower bound, specialised: `(r / e) ^ r ≤ r!`.
-/
lemma pow_div_exp_le_factorial (r : ℕ) :
    ((r : ℝ) / Real.exp 1) ^ r ≤ (r.factorial : ℝ) := by
  rcases r.eq_zero_or_pos with rfl | hr;
  · norm_num;
  · convert Stirling.le_factorial_stirling r |> le_trans _ using 1;
    exact le_mul_of_one_le_left (by positivity)
      (Real.le_sqrt_of_sq_le (by
        nlinarith [Real.pi_gt_three, show (r : ℝ) ≥ 1 by norm_cast]))

/-
Single binomial coefficient exponential bound: `C(n, r) ≤ (e * n / r) ^ r`.
-/
lemma choose_le_exp_mul_div_pow {n r : ℕ} (hr : 1 ≤ r) :
    (n.choose r : ℝ) ≤ (Real.exp 1 * n / r) ^ r := by
  have h_bound : (n.choose r : ℝ) ≤ (n : ℝ)^r / r.factorial :=
    Nat.choose_le_pow_div r n
  refine le_trans h_bound ?_;
  convert div_le_div_of_nonneg_left _ _ ( pow_div_exp_le_factorial r ) using 1;
  · rw [← div_pow]
    have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
    field_simp
  · positivity;
  · positivity

/-
Core volume estimate: a Hamming ball of radius `n / 64` has volume at most
`2 ^ (n / 2)`.
-/
lemma hammingVol_le_two_pow_half (n : ℕ) :
    hammingVol n (n / 64) ≤ 2 ^ (n / 2) := by
  by_cases hn : n < 64;
  · have hdiv : n / 64 = 0 := Nat.div_eq_of_lt hn
    rw [hdiv]
    unfold hammingVol
    simpa using Nat.one_le_pow (n / 2) 2 (by decide : 0 < 2)
  · -- Let r = n / 64. Then 2 * r ≤ n and r ≥ 1.
    set r := n / 64
    have hr1 : 1 ≤ r := by
      exact Nat.div_pos ( le_of_not_gt hn ) ( by decide )
    have hr2 : 2 * r ≤ n := by
      omega;
    -- By combining the inequalities, we get the desired result.
    have h_combined : (hammingVol n r : ℝ) ≤ (r + 1) * (2 : ℝ) ^ (16 * r) := by
      refine le_trans ( Nat.cast_le.mpr ( hammingVol_le_succ_mul_choose hr2 ) ) ?_;
      have h_combined : (Nat.choose n r : ℝ) ≤ (Real.exp 1 * n / r) ^ r := by
        convert choose_le_exp_mul_div_pow hr1 using 1;
      -- We'll use that $Real.exp 1 * n / r \leq 2^{16}$ to bound the expression.
      have h_bound : Real.exp 1 * n / r ≤ 2 ^ 16 := by
        rw [ div_le_iff₀ ] <;> norm_num;
        · have := Real.exp_one_lt_d9.le;
          norm_num at this
          nlinarith [show (n : ℝ) ≥ 64 by norm_cast; linarith,
            show (r : ℝ) ≥ 1 by norm_cast,
            show (n : ℝ) ≤ 64 * r + 63 by norm_cast; omega]
        · linarith;
      norm_num [ pow_mul ];
      exact mul_le_mul_of_nonneg_left
        (h_combined.trans (pow_le_pow_left₀ (by positivity) h_bound _)) (by positivity) |>
          le_trans <| by norm_num
    -- Since $r \geq 1$, we have $(r + 1) \leq 2^r$.
    have h_r_plus_one : (r + 1 : ℝ) ≤ (2 : ℝ) ^ r := by
      exact mod_cast Nat.recOn r (by norm_num) fun n ihn => by
        norm_num [Nat.pow_succ] at *
        linarith
    -- By combining the inequalities, we get the desired result: $(r + 1) * 2^{16r} \leq 2^{17r}$.
    have h_final : (hammingVol n r : ℝ) ≤ (2 : ℝ) ^ (17 * r) := by
      exact h_combined.trans (by
        rw [show 17 * r = r + 16 * r by ring, pow_add]
        exact mul_le_mul_of_nonneg_right h_r_plus_one (by positivity))
    exact_mod_cast h_final.trans ( pow_le_pow_right₀ ( by norm_num ) ( by omega ) )

/-- Combinatorial counting bound: estimating the volume of Hamming balls.
    This provides the necessary parameters for the probabilistic argument.
    For a fixed ratio, the volume V = hammingVol n r is exponentially smaller than 2^n. -/
theorem exists_hamming_volume_bound :
    ∃ c_alpha : ℕ, c_alpha > 0 ∧ ∃ c_vol : ℕ, c_vol > 0 ∧ ∀ n ≥ c_vol,
      hammingVol n (n / c_alpha) ≤ 2 ^ n / 2 ^ (n / c_vol) := by
  refine ⟨64, by norm_num, 3, by norm_num, ?_⟩
  intro n hn
  have h3 : 2 ^ n / 2 ^ (n / 3) = 2 ^ (n - n / 3) :=
    Nat.pow_div (by omega) (by norm_num)
  rw [h3]
  refine le_trans (hammingVol_le_two_pow_half n) ?_
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma card_powersetCard_filter_inter_eq_card {α : Type*} [DecidableEq α]
    (univ_set A : Finset α) (hA : A ⊆ univ_set) (N k : ℕ) (hkN : k ≤ N) :
    ((Finset.powersetCard N univ_set).filter (fun E => (A ∩ E).card = k)).card =
    A.card.choose k * (univ_set.card - A.card).choose (N - k) := by
  classical
  let source : Finset (Finset α) :=
    (Finset.powersetCard N univ_set).filter (fun E => (A ∩ E).card = k)
  let target : Finset (Finset α × Finset α) :=
    Finset.powersetCard k A ×ˢ Finset.powersetCard (N - k) (univ_set \ A)
  have htarget_card :
      target.card = A.card.choose k * (univ_set.card - A.card).choose (N - k) := by
    simp [target, Finset.card_product, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset hA]
  have hcard : source.card = target.card := by
    refine Finset.card_bij'
      (fun E _hE => (A ∩ E, E \ A))
      (fun P _hP => P.1 ∪ P.2)
      ?hi ?hj ?left ?right
    · intro E hE
      simp only [target, Finset.mem_product, Finset.mem_powersetCard]
      simp only [source, Finset.mem_filter, Finset.mem_powersetCard] at hE
      refine ⟨⟨?_, hE.2⟩, ⟨?_, ?_⟩⟩
      · intro x hx
        exact (Finset.mem_inter.mp hx).1
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨hE.1.1 hx.1, hx.2⟩
      · rw [Finset.card_sdiff]
        rw [hE.1.2, hE.2]
    · intro P hP
      simp only [source, Finset.mem_filter, Finset.mem_powersetCard]
      simp only [target, Finset.mem_product, Finset.mem_powersetCard] at hP
      rcases hP with ⟨hP, hQ⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro x hx
        rw [Finset.mem_union] at hx
        cases hx with
        | inl hxP => exact hA (hP.1 hxP)
        | inr hxQ => exact (Finset.mem_sdiff.mp (hQ.1 hxQ)).1
      · have hdisj : Disjoint P.1 P.2 := by
          rw [Finset.disjoint_left]
          intro x hxP hxQ
          exact (Finset.mem_sdiff.mp (hQ.1 hxQ)).2 (hP.1 hxP)
        rw [Finset.card_union_of_disjoint hdisj, hP.2, hQ.2]
        omega
      · have hinter : A ∩ (P.1 ∪ P.2) = P.1 := by
          ext x
          constructor
          · intro hx
            rw [Finset.mem_inter, Finset.mem_union] at hx
            rcases hx with ⟨hxA, hxP | hxQ⟩
            · exact hxP
            · exact False.elim ((Finset.mem_sdiff.mp (hQ.1 hxQ)).2 hxA)
          · intro hxP
            rw [Finset.mem_inter, Finset.mem_union]
            exact ⟨hP.1 hxP, Or.inl hxP⟩
        rw [hinter, hP.2]
    · intro E _hE
      simp only
      rw [Finset.inter_comm A E, Finset.union_comm]
      exact Finset.sdiff_union_inter E A
    · intro P hP
      simp only [target, Finset.mem_product, Finset.mem_powersetCard] at hP
      rcases hP with ⟨hP, hQ⟩
      apply Prod.ext
      · have hinter : A ∩ (P.1 ∪ P.2) = P.1 := by
          ext x
          constructor
          · intro hx
            rw [Finset.mem_inter, Finset.mem_union] at hx
            rcases hx with ⟨hxA, hxP | hxQ⟩
            · exact hxP
            · exact False.elim ((Finset.mem_sdiff.mp (hQ.1 hxQ)).2 hxA)
          · intro hxP
            rw [Finset.mem_inter, Finset.mem_union]
            exact ⟨hP.1 hxP, Or.inl hxP⟩
        exact hinter
      · have hdiff : (P.1 ∪ P.2) \ A = P.2 := by
          ext x
          constructor
          · intro hx
            rw [Finset.mem_sdiff, Finset.mem_union] at hx
            rcases hx with ⟨hxP | hxQ, hxnotA⟩
            · exact False.elim (hxnotA (hP.1 hxP))
            · exact hxQ
          · intro hxQ
            rw [Finset.mem_sdiff, Finset.mem_union]
            exact ⟨Or.inr hxQ, (Finset.mem_sdiff.mp (hQ.1 hxQ)).2⟩
        exact hdiff
  simpa [source] using hcard.trans htarget_card

lemma card_bad_sets {α : Type*} [DecidableEq α] (univ_set A : Finset α)
    (hA : A ⊆ univ_set) (N n : ℕ) :
    ((Finset.powersetCard N univ_set).filter (fun E => (A ∩ E).card > n)).card =
    ∑ k ∈ Finset.Ico (n + 1) (N + 1),
      A.card.choose k * (univ_set.card - A.card).choose (N - k) := by
  have h_split : ((Finset.powersetCard N univ_set).filter (fun E => (A ∩ E).card > n)) =
    (Finset.Ico (n + 1) (N + 1)).biUnion fun k =>
      (Finset.powersetCard N univ_set).filter fun E => (A ∩ E).card = k := by
    ext E
    rw [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hE, hn⟩
      refine ⟨(A ∩ E).card, ?_, ?_⟩
      · rw [Finset.mem_Ico]
        refine ⟨hn, ?_⟩
        rw [Finset.mem_powersetCard] at hE
        have h_sub : A ∩ E ⊆ E := by
          intro x hx
          rw [Finset.mem_inter] at hx
          exact hx.2
        have h_card := Finset.card_le_card h_sub
        omega
      · rw [Finset.mem_filter]
        exact ⟨hE, rfl⟩
    · rintro ⟨k, hk, h_in⟩
      rw [Finset.mem_filter] at h_in
      rw [Finset.mem_Ico] at hk
      refine ⟨h_in.1, ?_⟩
      omega
  rw [h_split]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k hk
    exact card_powersetCard_filter_inter_eq_card univ_set A hA N k (by
      rw [Finset.mem_Ico] at hk
      omega)
  · intro k1 hk1 k2 hk2 h_neq
    apply Finset.disjoint_left.mpr
    intro E hE1 hE2
    rw [Finset.mem_filter] at hE1 hE2
    omega

lemma exists_subset_inter_le_of_counting_bound {α : Type*} [DecidableEq α]
    (univ_set : Finset α) (N n : ℕ)
    (families : Finset (Finset α))
    (h_sub : ∀ A ∈ families, A ⊆ univ_set)
    (h_bound : (∑ A ∈ families, ∑ k ∈ Finset.Ico (n + 1) (N + 1),
      A.card.choose k * (univ_set.card - A.card).choose (N - k)) <
        univ_set.card.choose N) :
    ∃ E : Finset α, E ⊆ univ_set ∧ E.card = N ∧ ∀ A ∈ families, (A ∩ E).card ≤ n := by
  let S := Finset.powersetCard N univ_set
  have h_S_card : S.card = univ_set.card.choose N := Finset.card_powersetCard N univ_set
  let Bad := fun A => S.filter (fun E => (A ∩ E).card > n)
  let AllBad := families.biUnion Bad
  have h_AllBad_card : AllBad.card ≤ ∑ A ∈ families, (Bad A).card := Finset.card_biUnion_le
  have h_sum_eq : (∑ A ∈ families, (Bad A).card) =
      ∑ A ∈ families, ∑ k ∈ Finset.Ico (n + 1) (N + 1),
        A.card.choose k * (univ_set.card - A.card).choose (N - k) := by
    apply Finset.sum_congr rfl
    intro A hA
    exact card_bad_sets univ_set A (h_sub A hA) N n
  rw [h_sum_eq] at h_AllBad_card
  have h_AllBad_lt : AllBad.card < S.card := by
    rw [h_S_card]
    exact lt_of_le_of_lt h_AllBad_card h_bound
  have h_not_subset : ¬ S ⊆ AllBad := by
    intro h_sub
    have h_card_le := Finset.card_le_card h_sub
    omega
  rw [Finset.subset_iff] at h_not_subset
  push_neg at h_not_subset
  rcases h_not_subset with ⟨E, hE_in_S, hE_not_in_AllBad⟩
  use E
  rw [Finset.mem_powersetCard] at hE_in_S
  refine ⟨hE_in_S.1, hE_in_S.2, ?_⟩
  intro A hA
  have h_not_in_Bad : E ∉ Bad A := by
    intro h_in
    apply hE_not_in_AllBad
    rw [Finset.mem_biUnion]
    exact ⟨A, hA, h_in⟩
  rw [Finset.mem_filter] at h_not_in_Bad
  push_neg at h_not_in_Bad
  have h_not_gt := h_not_in_Bad (by rw [Finset.mem_powersetCard]; exact ⟨hE_in_S.1, hE_in_S.2⟩)
  omega

/-
Union-bound helper: the number of `N`-subsets of an `M`-set meeting a fixed
`a`-subset in more than `n` points is bounded by first choosing `n+1` of the
meeting points and then filling in the rest (Vandermonde).
-/
lemma per_ball_bad_le (a M N n : ℕ) (haM : a ≤ M) :
    (∑ k ∈ Finset.Ico (n + 1) (N + 1), a.choose k * (M - a).choose (N - k))
      ≤ a.choose (n + 1) * (M - (n + 1)).choose (N - (n + 1)) := by
  by_cases h : n + 1 ≤ a ∧ n + 1 ≤ N;
  · have h_reindex :
        ∑ k ∈ Finset.Ico (n + 1) (N + 1), a.choose k * (M - a).choose (N - k) ≤
          a.choose (n + 1) * ∑ j ∈ Finset.range (N - n),
            (a - (n + 1)).choose j * (M - a).choose (N - (n + 1 + j)) := by
      have h_reindex : ∀ k ∈ Finset.Ico (n + 1) (N + 1),
          a.choose k * (M - a).choose (N - k) ≤
            a.choose (n + 1) * (a - (n + 1)).choose (k - (n + 1)) *
              (M - a).choose (N - k) := by
        intros k hk
        have h_choose : a.choose k ≤ a.choose (n + 1) * (a - (n + 1)).choose (k - (n + 1)) := by
          rw [ ← Nat.choose_mul ];
          · exact le_mul_of_one_le_right (Nat.zero_le _)
              (Nat.choose_pos (by linarith [Finset.mem_Ico.mp hk]))
          · linarith [ Finset.mem_Ico.mp hk ];
        exact Nat.mul_le_mul_right _ h_choose;
      convert Finset.sum_le_sum h_reindex using 1;
      rw [ Finset.mul_sum _ _ _, Finset.sum_Ico_eq_sum_range ];
      simp +decide [mul_assoc];
    have h_vandermonde :
        ∑ j ∈ Finset.range (N - n),
          (a - (n + 1)).choose j * (M - a).choose (N - (n + 1 + j)) =
            ((a - (n + 1)) + (M - a)).choose (N - (n + 1)) := by
      rw [ Nat.add_choose_eq ];
      rw [ Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ];
      grind;
    grind;
  · cases le_or_gt ( n + 1 ) a
    · cases le_or_gt ( n + 1 ) N
      · omega
      · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]; exact Nat.zero_le _
    · cases le_or_gt ( n + 1 ) N
      · have : ∑ k ∈ Finset.Ico (n + 1) (N + 1), a.choose k * (M - a).choose (N - k) = 0 := by
          apply Finset.sum_eq_zero; intro k hk; rw [Finset.mem_Ico] at hk
          rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
        rw [this]; exact Nat.zero_le _
      · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]; exact Nat.zero_le _

/-
`hammingVol n r = 2 ^ n` as soon as `n ≤ r`.
-/
lemma hammingVol_eq_two_pow_of_ge {n r : ℕ} (h : n ≤ r) : hammingVol n r = 2 ^ n := by
  rw [← Nat.sum_range_choose]
  rw [Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h))]
  · aesop
  · exact fun x hx₁ hx₂ => Nat.choose_eq_zero_of_lt <| by aesop

/-
Descending-factorial comparison used for the union bound: if `V * N ≤ M`
and `1 ≤ V`, then `V ^ (n+1) * C(N, n+1) ≤ C(M, n+1)`.
-/
lemma choose_ge_pow_mul_choose {M N V n : ℕ} (hV : 1 ≤ V) (hVN : V * N ≤ M) :
    V ^ (n + 1) * N.choose (n + 1) ≤ M.choose (n + 1) := by
  have h_mul : V ^ (n + 1) * Nat.descFactorial N (n + 1) ≤ Nat.descFactorial M (n + 1) := by
    have h_mul : ∏ i ∈ Finset.range (n + 1), (V * (N - i)) ≤
        ∏ i ∈ Finset.range (n + 1), (M - i) := by
      apply Finset.prod_le_prod';
      intro i hi; by_cases hi' : i ≤ N <;> simp_all +decide [ mul_tsub ] ;
      · nlinarith [ Nat.sub_add_cancel ( show i ≤ M from by nlinarith ) ];
      · nlinarith [ Nat.sub_le M i ];
    convert h_mul using 2 <;> norm_num [ Finset.prod_mul_distrib, Nat.descFactorial_eq_prod_range ];
    · exact Or.inl ( by rw [ Finset.prod_range_succ_comm ] );
    · rw [ Finset.prod_range_succ_comm ];
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at h_mul
  nlinarith [ Nat.factorial_pos ( n + 1 ) ]

/-- `2 ^ n < n !` for `n ≥ 4`. -/
lemma two_pow_lt_factorial {n : ℕ} (h : 4 ≤ n) : 2 ^ n < n.factorial := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m <;> simp_all only [
        Nat.reduceLeDiff, Nat.reducePow, IsEmpty.forall_iff, Nat.reduceAdd, le_refl,
        Nat.lt_add_one
      ]; decide
    · have := ih hm
      rw [Nat.factorial_succ, pow_succ]
      calc 2 ^ m * 2 < m.factorial * 2 := by omega
        _ ≤ (m + 1) * m.factorial := by nlinarith [Nat.factorial_pos m]
        _ = (m + 1).factorial := by rw [Nat.factorial_succ]

/-
Numeric core of the union bound, valid in the nontrivial regime
`n+1 ≤ hammingVol n r` and `n+1 ≤ 2^n / hammingVol n r`.
-/
lemma counting_core_bound {n r : ℕ} (hn : 0 < n)
    (hV : n + 1 ≤ hammingVol n r)
    (hN : n + 1 ≤ 2 ^ n / hammingVol n r) :
    (r + 1) * 2 ^ n * (hammingVol n r).choose (n + 1) < (hammingVol n r) ^ (n + 1) := by
  by_cases hr : r < n;
  · by_cases h : 4 ≤ n;
    · have h_step6 : (r + 1) * 2 ^ n < Nat.factorial (n + 1) := by
        have h_step6 : n * 2 ^ n < Nat.factorial (n + 1) := by
          exact Nat.le_induction (by decide) (fun k hk ih ↦ by
            rw [Nat.factorial_succ, pow_succ']
            nlinarith [Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hk]) n h
        exact lt_of_le_of_lt ( Nat.mul_le_mul_right _ ( Nat.succ_le_of_lt hr ) ) h_step6;
      refine lt_of_lt_of_le ( Nat.mul_lt_mul_of_pos_right h_step6 ( Nat.choose_pos hV ) ) ?_;
      rw [ ← Nat.descFactorial_eq_factorial_mul_choose ];
      exact Nat.descFactorial_le_pow _ _;
    · interval_cases n <;> interval_cases r <;> trivial;
  · contrapose! hN;
    rw [hammingVol_eq_two_pow_of_ge]
    · norm_num
      linarith
    · linarith

/-
The counting bound for the union bound argument.
-/
lemma list_decoding_counting_bound (n r N : ℕ) (hn : 0 < n)
    (hN : N = 2 ^ n / hammingVol n r) :
    let families := (Finset.Iic r).biUnion fun r' =>
      (stringsOfLength n).image fun x => hammingBall n x r'
    (∑ A ∈ families, ∑ k ∈ Finset.Ico (n + 1) (N + 1),
      A.card.choose k * (2 ^ n - A.card).choose (N - k)) < (2 ^ n).choose N := by
  by_cases hV : hammingVol n r ≤ n;
  · refine lt_of_le_of_lt (Finset.sum_nonpos ?_) ?_;
    · simp +zetaDelta only [
        Finset.mem_biUnion, Finset.mem_Iic, Finset.mem_image, nonpos_iff_eq_zero,
        Finset.sum_eq_zero_iff, Finset.mem_Ico, Order.add_one_le_iff,
        Order.lt_add_one_iff, mul_eq_zero, and_imp, forall_exists_index
      ] at *;
      intros; subst_vars; rw [ Nat.choose_eq_zero_of_lt ] ;
      · norm_num;
      · rw [ hammingBall_card ];
        · exact lt_of_le_of_lt
            (show hammingVol n _ ≤ hammingVol n r from
              Finset.sum_le_sum_of_subset (Finset.range_mono (by linarith)))
            (by linarith)
        · unfold stringsOfLength at *; aesop;
    · exact Nat.choose_pos ( hN.symm ▸ Nat.div_le_self _ _ );
  · by_cases hN' : n + 1 ≤ N;
    · have h_bound :
          (r + 1) * 2 ^ n * (hammingVol n r).choose (n + 1) *
              (2 ^ n - (n + 1)).choose (N - (n + 1)) <
            (2 ^ n).choose N := by
        have h_bound :
            (r + 1) * 2 ^ n * (hammingVol n r).choose (n + 1) <
              (hammingVol n r) ^ (n + 1) := by
          apply counting_core_bound hn (by linarith) (by
          linarith);
        have h_bound :
            (hammingVol n r) ^ (n + 1) *
                (2 ^ n - (n + 1)).choose (N - (n + 1)) ≤
              (2 ^ n).choose N := by
          have h_bound :
              (hammingVol n r) ^ (n + 1) * N.choose (n + 1) ≤
                (2 ^ n).choose (n + 1) := by
            apply choose_ge_pow_mul_choose;
            · linarith;
            · nlinarith [ Nat.div_mul_le_self ( 2 ^ n ) ( hammingVol n r ) ];
          have h_bound :
              (2 ^ n).choose (n + 1) *
                  (2 ^ n - (n + 1)).choose (N - (n + 1)) =
                (2 ^ n).choose N * N.choose (n + 1) := by
            rw [ ← Nat.choose_mul ];
            grind;
          nlinarith [ Nat.choose_pos hN' ];
        exact lt_of_lt_of_le
          (mul_lt_mul_of_pos_right ‹_› (Nat.choose_pos (Nat.sub_le_sub_right
            (show N ≤ 2 ^ n from hN.symm ▸ Nat.div_le_self _ _) _))) h_bound
      refine lt_of_le_of_lt ?_ h_bound;
      refine le_trans (Finset.sum_le_sum (g := fun _ =>
        (hammingVol n r).choose (n + 1) *
          (2 ^ n - (n + 1)).choose (N - (n + 1))) ?_) ?_;
      · intro A hA
        have hA_card : A.card ≤ 2 ^ n := by
          simp +zetaDelta only [
            not_le, Order.add_one_le_iff, Finset.mem_biUnion, Finset.mem_Iic,
            Finset.mem_image
          ] at *;
          obtain ⟨ a, ha, b, hb, rfl ⟩ := hA
          exact le_trans (Finset.card_le_card (show hammingBall n b a ⊆
            stringsOfLength n from Finset.filter_subset _ _))
            (by simp +decide [cardStringsOfLength])
        refine le_trans (per_ball_bad_le A.card (2 ^ n) N n hA_card) ?_;
        apply Nat.mul_le_mul_right
        apply Nat.choose_le_choose
        simp +zetaDelta only [
          not_le, Order.add_one_le_iff, Finset.mem_biUnion, Finset.mem_Iic,
          Finset.mem_image
        ] at *;
        obtain ⟨ a, ha, b, hb, rfl ⟩ := hA;
        rw [ hammingBall_card ];
        · exact Finset.sum_le_sum_of_subset ( Finset.range_mono ( by linarith ) );
        · grind +suggestions;
      · simp +decide only [Finset.sum_const, smul_eq_mul, mul_comm, mul_assoc, mul_left_comm];
        refine le_trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Finset.card_biUnion_le.trans <|
            Finset.sum_le_card_nsmul _ _ _ fun x hx => Finset.card_image_le) <|
              Nat.zero_le _) <| Nat.zero_le _) ?_
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, cardStringsOfLength ];
    · simp_all +decide only [
        not_le, Order.add_one_le_iff, not_lt, add_le_add_iff_right,
        Finset.Ico_eq_empty_of_le, Finset.sum_empty, Finset.sum_const_zero
      ];
      exact Nat.choose_pos ( Nat.div_le_self _ _ )

/-- Probabilistic existence of the list-decoding set E.
    For appropriate n, r, N where N * V ≈ 2^n, there exists a set E
    such that every ball of radius r contains at most n points of E. -/
theorem exists_list_decoding_set (n r N : ℕ) (hn : 0 < n)
    (hN : N = 2 ^ n / hammingVol n r) :
    ∃ E : Finset BitString, IsHammingListDecodingSet n r N E := by
  let families := (Finset.Iic r).biUnion fun r' =>
    (stringsOfLength n).image fun x => hammingBall n x r'
  have h_bound := list_decoding_counting_bound n r N hn hN
  have h_sub : ∀ A ∈ families, A ⊆ stringsOfLength n := by
    intro A hA
    simp only [families, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Iic] at hA
    rcases hA with ⟨r', _, x, _, rfl⟩
    intro y hy
    rw [hammingBall, Finset.mem_filter] at hy
    exact hy.1
  have h_univ_card : (stringsOfLength n).card = 2 ^ n := cardStringsOfLength n
  have h_bound' :
      (∑ A ∈ families, ∑ k ∈ Finset.Ico (n + 1) (N + 1),
        A.card.choose k * ((stringsOfLength n).card - A.card).choose (N - k)) <
          (stringsOfLength n).card.choose N := by
    rw [h_univ_card]
    exact h_bound
  obtain ⟨E, hE_sub, hE_card, hE_inter⟩ :=
    exists_subset_inter_le_of_counting_bound
      (stringsOfLength n) N n families h_sub h_bound'
  use E
  unfold IsHammingListDecodingSet
  refine ⟨fun x hx => ?_, hE_card, fun A hA_mem hA_card => ?_⟩
  · exact memStringsOfLength n x |>.mp (hE_sub hx)
  · rcases hA_mem with ⟨n', x', r', hx'len, rfl⟩
    by_cases hn_eq : n' = n
    · have h_len_eq : x'.length = n := hx'len.trans hn_eq
      rw [hn_eq]
      have hA_eq : hammingBall n x' r' = hammingBall n x' (min r' n) := by
        ext y
        simp only [hammingBall, Finset.mem_filter]
        apply and_congr_right
        intro hy
        have h_len : y.length = n := memStringsOfLength n y |>.mp hy
        have h_dist_le : hammingDist x' y ≤ n := by
          have h1 := hammingDist_le_right_length x' y
          rw [h_len] at h1
          exact h1
        constructor
        · intro h1; exact le_min h1 h_dist_le
        · intro h1; exact le_trans h1 (Nat.min_le_left _ _)
      have hr'_le : min r' n ≤ r := by
        have h_vol_eq : (hammingBall n x' (min r' n)).card = hammingVol n (min r' n) :=
          hammingBall_card n x' (min r' n) (by rw [hx'len, hn_eq])
        have h_card_eq : (hammingBall n x' r').card = (hammingBall n x' (min r' n)).card := by
          congr 1
        rw [hn_eq] at hA_card
        rw [h_card_eq] at hA_card
        rw [h_vol_eq] at hA_card
        by_contra h_not
        push_neg at h_not
        have h_lt : hammingVol n r < hammingVol n (min r' n) := by
          unfold hammingVol
          have h_split : Finset.range (min r' n + 1) =
              Finset.range (r + 1) ∪ Finset.Ico (r + 1) (min r' n + 1) := by
            ext a
            rw [Finset.mem_union, Finset.mem_range, Finset.mem_range, Finset.mem_Ico]
            omega
          rw [h_split]
          rw [Finset.sum_union]
          · have h_pos : 0 < ∑ x ∈ Finset.Ico (r + 1) (min r' n + 1), Nat.choose n x := by
              refine Finset.sum_pos ?_ ?_
              · intro i hi
                have hi2 : i ≤ n := by
                  have h1 : i < min r' n + 1 := Finset.mem_Ico.mp hi |>.2
                  omega
                exact Nat.choose_pos hi2
              · rw [Finset.nonempty_Ico]
                omega
            omega
          · apply Finset.disjoint_left.mpr
            intro a ha1 ha2
            rw [Finset.mem_range] at ha1
            rw [Finset.mem_Ico] at ha2
            omega
        omega
      have hA_in : hammingBall n x' (min r' n) ∈ families := by
        simp only [families, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Iic]
        refine ⟨min r' n, hr'_le, x', ?_, rfl⟩
        exact memStringsOfLength n x' |>.mpr h_len_eq
      have h_inter := hE_inter (hammingBall n x' (min r' n)) hA_in
      rw [hA_eq]
      exact h_inter
    · have h_inter_empty : hammingBall n' x' r' ∩ E = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        rw [Finset.mem_inter] at hy
        rcases hy with ⟨hyA, hyE⟩
        rw [hammingBall, Finset.mem_filter] at hyA
        have h1 := memStringsOfLength n' y |>.mp hyA.1
        have h2 := hE_sub hyE
        have h3 := memStringsOfLength n y |>.mp h2
        rw [h3] at h1
        exact hn_eq h1.symm
      rw [h_inter_empty, Finset.card_empty]
      exact Nat.zero_le n

lemma IsHammingListDecodingSet_equiv_finite (n r N : ℕ) (E : Finset BitString)
    (hE : ∀ x ∈ E, x.length = n) (hE_card : E.card = N) :
    IsHammingListDecodingSet n r N E ↔
    ∀ A ∈ (Finset.Iic r).biUnion (fun r' =>
      (stringsOfLength n).image fun x => hammingBall n x r'),
      (A ∩ E).card ≤ n := by
  unfold IsHammingListDecodingSet
  constructor
  · rintro ⟨_, _, h3⟩ A hA
    simp only [Finset.mem_biUnion, Finset.mem_Iic, Finset.mem_image] at hA
    rcases hA with ⟨r', hr', x', hx', rfl⟩
    have h_mem : hammingFamilyMem (hammingBall n x' r') :=
      ⟨n, x', r', memStringsOfLength _ _ |>.mp hx', rfl⟩
    have h_card : (hammingBall n x' r').card ≤ hammingVol n r := by
      rw [hammingBall_card]
      · exact hammingVol_mono hr'
      · exact memStringsOfLength _ _ |>.mp hx'
    exact h3 _ h_mem h_card
  · intro h
    refine ⟨hE, hE_card, fun A hA_mem hA_card => ?_⟩
    rcases hA_mem with ⟨n', x', r', rfl, rfl⟩
    by_cases hn_eq : x'.length = n
    · have hA_eq : hammingBall x'.length x' r' = hammingBall n x' (min r' n) := by
        ext y
        simp only [hammingBall, Finset.mem_filter, hn_eq]
        apply and_congr_right
        intro hy
        have h_len : y.length = n := memStringsOfLength n y |>.mp hy
        have h_dist_le : hammingDist x' y ≤ n := by
          have h1 := hammingDist_le_right_length x' y
          rw [h_len] at h1
          exact h1
        constructor
        · intro h1; exact le_min h1 h_dist_le
        · intro h1; exact le_trans h1 (Nat.min_le_left _ _)
      have hr'_le : min r' n ≤ r := by
        have h_vol_eq : (hammingBall n x' (min r' n)).card = hammingVol n (min r' n) :=
          hammingBall_card n x' (min r' n) hn_eq
        have h_card_eq : (hammingBall x'.length x' r').card =
            (hammingBall n x' (min r' n)).card := by
          rw [hA_eq]
        rw [h_card_eq] at hA_card
        rw [h_vol_eq] at hA_card
        by_contra h_not
        push_neg at h_not
        have h_lt : hammingVol n r < hammingVol n (min r' n) := by
          unfold hammingVol
          have h_split : Finset.range (min r' n + 1) =
              Finset.range (r + 1) ∪ Finset.Ico (r + 1) (min r' n + 1) := by
            ext a
            rw [Finset.mem_union, Finset.mem_range, Finset.mem_range, Finset.mem_Ico]
            omega
          rw [h_split]
          rw [Finset.sum_union]
          · have h_pos : 0 < ∑ x ∈ Finset.Ico (r + 1) (min r' n + 1), Nat.choose n x := by
              refine Finset.sum_pos ?_ ?_
              · intro i hi
                have hi2 : i ≤ n := by
                  have h1 : i < min r' n + 1 := Finset.mem_Ico.mp hi |>.2
                  omega
                exact Nat.choose_pos hi2
              · rw [Finset.nonempty_Ico]
                omega
            omega
          · apply Finset.disjoint_left.mpr
            intro a ha1 ha2
            rw [Finset.mem_range] at ha1
            rw [Finset.mem_Ico] at ha2
            omega
        omega
      have hA_in : hammingBall n x' (min r' n) ∈
          (Finset.Iic r).biUnion (fun r' =>
            (stringsOfLength n).image fun x => hammingBall n x r') := by
        simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Iic]
        refine ⟨min r' n, hr'_le, x', ?_, rfl⟩
        exact memStringsOfLength n x' |>.mpr hn_eq
      have h_inter := h (hammingBall n x' (min r' n)) hA_in
      rw [hA_eq]
      exact h_inter
    · have h_inter_empty : hammingBall x'.length x' r' ∩ E = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        rw [Finset.mem_inter] at hy
        rcases hy with ⟨hyA, hyE⟩
        rw [hammingBall, Finset.mem_filter] at hyA
        have h1 := memStringsOfLength x'.length y |>.mp hyA.1
        have h2 := hE y hyE
        rw [h2] at h1
        exact hn_eq h1.symm
      rw [h_inter_empty, Finset.card_empty]
      exact Nat.zero_le n

/-- The finite Hamming balls that have to be checked for the list-decoding
condition: centers are `n`-bit strings and radii are bounded by `r`. -/
def hammingListDecodingCandidates (n r : ℕ) : Finset (Finset BitString) :=
  (Finset.Iic r).biUnion (fun r' =>
    (stringsOfLength n).image (fun x => hammingBall n x r'))

lemma mem_hammingListDecodingCandidates {n r : ℕ} {A : Finset BitString} :
    A ∈ hammingListDecodingCandidates n r ↔
      ∃ r' ≤ r, ∃ x ∈ stringsOfLength n, A = hammingBall n x r' := by
  unfold hammingListDecodingCandidates
  simp only [Finset.mem_biUnion, Finset.mem_Iic, Finset.mem_image]
  constructor
  · rintro ⟨r', hr', x, hx, hA⟩
    exact ⟨r', hr', x, hx, hA.symm⟩
  · rintro ⟨r', hr', x, hx, rfl⟩
    exact ⟨r', hr', x, hx, rfl⟩

/-- A decidable finite predicate equivalent to `IsHammingListDecodingSet`. -/
def IsHammingListDecodingSetFinite (n r N : ℕ) (E : Finset BitString) : Prop :=
  (∀ x ∈ E, x.length = n) ∧
  E.card = N ∧
  (∀ A ∈ hammingListDecodingCandidates n r, (A ∩ E).card ≤ n)

lemma IsHammingListDecodingSet_iff_finite (n r N : ℕ) (E : Finset BitString) :
    IsHammingListDecodingSet n r N E ↔
      IsHammingListDecodingSetFinite n r N E := by
  unfold IsHammingListDecodingSetFinite hammingListDecodingCandidates
  constructor
  · intro h
    exact ⟨h.1, h.2.1,
      (IsHammingListDecodingSet_equiv_finite n r N E h.1 h.2.1).mp h⟩
  · intro h
    exact (IsHammingListDecodingSet_equiv_finite n r N E h.1 h.2.1).mpr h.2.2

noncomputable def IsHammingListDecodingSetFinite_decidable (n r N : ℕ) (E : Finset BitString) :
    Decidable (IsHammingListDecodingSetFinite n r N E) := by
  classical
  exact inferInstance

/-- Canonical finite search list for the list-decoding witness.  It scans all
sublists of `allStrings n`, so every subset of the length-`n` cube appears as
`L.toFinset`. -/
noncomputable def hammingListDecodingSearchList (n : ℕ) : List BitString :=
  ((allStrings n).sublists.find? (fun L =>
    @decide (IsHammingListDecodingSetFinite n (n / 64)
      (2 ^ n / hammingVol n (n / 64)) L.toFinset)
      (IsHammingListDecodingSetFinite_decidable n (n / 64)
        (2 ^ n / hammingVol n (n / 64)) L.toFinset))).getD []

/-
`hammingVol n r` counts, over `allStrings n`, the strings within Hamming
distance `r` of the all-`false` string; a primrec-friendly reformulation.
-/
lemma hammingVol_eq_countP (n r : ℕ) :
    hammingVol n r =
      (allStrings n).countP
        (fun y => decide (hammingDist (List.replicate n false) y ≤ r)) := by
  have h_filter : (stringsOfLength n).filter
      (fun y => hammingDist (List.replicate n false) y ≤ r) =
        (allStrings n).toFinset.filter
          (fun y => hammingDist (List.replicate n false) y ≤ r) := by
    unfold stringsOfLength; aesop;
  convert congr_arg Finset.card h_filter using 1;
  · convert hammingBall_card n (List.replicate n false) r
      List.length_replicate |>.symm using 1
  · rw [ List.countP_eq_length_filter ];
    rw [ ← Multiset.coe_card ];
    rw [← Multiset.toFinset_card_of_nodup]
    · aesop
    · exact List.Nodup.filter _ (allStrings_nodup n)

lemma hammingVol_primrec₂ : Primrec₂ (fun n r : ℕ => hammingVol n r) := by
  -- Express the Hamming volume using primitive-recursive list operations.
  have h_hammingVol_primrec : Primrec₂ (fun (n r : ℕ) =>
      (allStrings n).countP fun y => hammingDist (List.replicate n false) y ≤ r) := by
    have h_hammingDist_primrec : Primrec₂ (fun (x y : BitString) => hammingDist x y) := by
      exact hammingDist_primrec;
    have h_hammingVol_primrec : Primrec (fun p : ℕ × ℕ =>
        (allStrings p.1).countP fun y =>
          decide (hammingDist (List.replicate p.1 false) y ≤ p.2)) := by
      have h_pred : Primrec₂ (fun p : ℕ × ℕ => fun y : BitString =>
          decide (hammingDist (List.replicate p.1 false) y ≤ p.2)) := by
        have h_pred : Primrec (fun p : ℕ × ℕ => (List.replicate p.1 false, p.2)) := by
          exact Primrec.pair
            (Primrec.list_replicate.comp Primrec.fst (Primrec.const false)) Primrec.snd
        have h_pred : Primrec (fun p : (BitString × ℕ) × BitString =>
            decide (hammingDist p.1.1 p.2 ≤ p.1.2)) := by
          have h_pred : Primrec (fun p : (BitString × ℕ) × BitString =>
              (hammingDist p.1.1 p.2, p.1.2)) := by
            exact Primrec.pair
              (h_hammingDist_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
              (Primrec.snd.comp Primrec.fst)
          convert Primrec.comp
            (show Primrec (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) from ?_) h_pred using 1
          convert Primrec.nat_le using 1;
          constructor <;> intro h <;> simp_all +decide [ PrimrecRel ]; all_goals grind +suggestions;
        convert h_pred.comp
          (‹Primrec fun p : ℕ × ℕ => (List.replicate p.1 false, p.2)›.comp Primrec.fst |>
            Primrec.pair <| Primrec.snd) using 1
      have := @list_countP_primrec;
      convert this ( show Primrec fun p : ℕ × ℕ => allStrings p.1 from ?_ ) h_pred using 1;
      exact allStrings_primrec.comp ( Primrec.fst );
    exact h_hammingVol_primrec;
  convert h_hammingVol_primrec using 1;
  exact funext fun n => funext fun r => hammingVol_eq_countP n r

private lemma primrec_decide_natEq {α} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => decide (f a = g a)) :=
  PrimrecPred.decide (PrimrecRel.comp Primrec.eq hf hg)

private lemma primrec_decide_natLe {α} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => decide (f a ≤ g a)) :=
  PrimrecPred.decide (PrimrecRel.comp Primrec.nat_le hf hg)

/-- A primitive-recursive Boolean reformulation of the decidable predicate
`IsHammingListDecodingSetFinite n (n/64) (2^n / hammingVol n (n/64)) L.toFinset`,
used to establish computability of the search. -/
def hammingListDecodingCheckBool (n : ℕ) (L : List BitString) : Bool :=
  L.all (fun x => decide (x.length = n)) &&
    decide (L.dedup.length = 2 ^ n / hammingVol n (n / 64)) &&
    (List.range (n / 64 + 1)).all (fun r' =>
      (allStrings n).all (fun x =>
        decide (L.dedup.countP
          (fun y => decide (y.length = n) && decide (hammingDist x y ≤ r')) ≤ n)))

/-- The radius-`r` Hamming slice of `L` around `y`, counted as a `Finset`, has the
same cardinality as the corresponding filtered sublist of `L.dedup`.  Both sides
carry the length constraint, so no hypothesis on `L` is needed. -/
private lemma hammingSlice_card_eq (n r : ℕ) (y : BitString) (L : List BitString) :
    ({z ∈ stringsOfLength n | hammingDist y z ≤ r} ∩ L.toFinset).card =
      (L.dedup.filter
        (fun z => decide (z.length = n) && decide (hammingDist y z ≤ r))).length := by
  rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_dedup L))]
  congr 1
  ext z
  simp [stringsOfLength, and_comm]

/-
The Boolean check agrees with the decidable finite list-decoding predicate.
-/
lemma hammingListDecodingCheckBool_eq (n : ℕ) (L : List BitString) :
    hammingListDecodingCheckBool n L =
      @decide (IsHammingListDecodingSetFinite n (n / 64)
        (2 ^ n / hammingVol n (n / 64)) L.toFinset)
        (IsHammingListDecodingSetFinite_decidable n (n / 64)
          (2 ^ n / hammingVol n (n / 64)) L.toFinset) := by
  revert L n;
  unfold IsHammingListDecodingSetFinite;
  intro n L
  by_cases h : ∀ x ∈ L, x.length = n <;>
    simp_all +decide only [not_forall, List.mem_toFinset, Bool.decide_and]
  · unfold hammingListDecodingCheckBool hammingListDecodingCandidates
    simp_all +decide only [
      implies_true, decide_true, Finset.mem_biUnion, Finset.mem_Iic, Finset.mem_image,
      Finset.ext_iff, forall_exists_index, and_imp, Bool.true_and
    ]
    simp_all +decide only [List.all_eq, decide_true, implies_true, Bool.true_and,
      List.countP_eq_length_filter, mem_allStrings, decide_eq_true_eq, List.mem_range,
      Order.lt_add_one_iff, Finset.mem_biUnion, Finset.mem_Iic, Finset.mem_image,
      forall_exists_index, and_imp]
    congr! 2
    constructor
    · intro h
      simp_all +decide only [Finset.mem_biUnion, Finset.mem_Iic, Finset.mem_image,
        forall_exists_index, and_imp, List.mem_range, Order.lt_add_one_iff,
        mem_allStrings, decide_eq_true_eq]
      rintro A x hx y hy rfl
      specialize h x hx y
      simp_all +decide only [stringsOfLength, List.mem_toFinset, mem_allStrings,
        forall_const, hammingBall]
      convert h using 1
      exact hammingSlice_card_eq n x y L
    · intro h
      simp_all +decide only [List.mem_range, Order.lt_add_one_iff, mem_allStrings,
        decide_eq_true_eq, Finset.mem_biUnion, Finset.mem_Iic, Finset.mem_image,
        forall_exists_index, and_imp]
      intro x hx y hy
      specialize h (hammingBall n y x) x hx y
      simp_all +decide only [hammingBall, forall_const]
      convert h (by unfold stringsOfLength; aesop) using 1
      exact ( hammingSlice_card_eq n x y L ).symm
  · grind +locals

/-
The Boolean check is primitive recursive jointly in `(n, L)`.
-/
lemma hammingListDecodingCheckBool_primrec :
    Primrec (fun p : ℕ × List BitString => hammingListDecodingCheckBool p.1 p.2) := by
  have h_hammingListDecodingCheckBool : Primrec (fun p : ℕ × List BitString =>
      List.all p.2 fun x => decide (x.length = p.1)) := by
    convert list_all_primrec _ _ using 1;
    all_goals try exact Primrec.snd;
    exact primrec_decide_natEq (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have h_hammingListDecodingCheckBool : Primrec (fun p : ℕ × List BitString =>
      decide (p.2.dedup.length = 2 ^ p.1 / hammingVol p.1 (p.1 / 64))) := by
    have h_hammingListDecodingCheckBool : Primrec (fun p : ℕ × List BitString =>
        p.2.dedup.length) := by
      convert Primrec.list_length.comp ( dedup_primrec.comp ( Primrec.snd ) ) using 1;
    convert primrec_decide_natEq h_hammingListDecodingCheckBool
      (show Primrec (fun p : ℕ × List BitString =>
        2 ^ p.1 / hammingVol p.1 (p.1 / 64)) from ?_) using 1
    convert Primrec.nat_div.comp (primrec_two_pow.comp Primrec.fst)
      (hammingVol_primrec₂.comp Primrec.fst
        (Primrec.nat_div.comp Primrec.fst (Primrec.const 64))) using 1
  have h_hammingListDecodingCheckBool : Primrec (fun p : ℕ × List BitString =>
      List.all (List.range (p.1 / 64 + 1)) fun r' =>
        List.all (allStrings p.1) fun x =>
          p.2.dedup.countP (fun y => decide (y.length = p.1) &&
            decide (hammingDist x y ≤ r')) ≤ p.1) := by
    have h_countP : Primrec (fun p : ℕ × List BitString × ℕ × BitString =>
        p.2.1.dedup.countP fun y =>
          decide (y.length = p.1) && decide (hammingDist p.2.2.2 y ≤ p.2.2.1)) := by
      have h_countP : Primrec (fun p : ℕ × List BitString × ℕ × BitString =>
          List.countP (fun y => decide (y.length = p.1) &&
            decide (hammingDist p.2.2.2 y ≤ p.2.2.1)) p.2.1) := by
        convert list_countP_primrec
          (show Primrec fun p : ℕ × List BitString × ℕ × BitString =>
            p.2.1 from ?_) ?_ using 1
        · exact Primrec.fst.comp ( Primrec.snd );
        · apply Primrec.and.comp;
          · convert primrec_decide_natEq (Primrec.list_length.comp Primrec.snd)
              (Primrec.fst.comp Primrec.fst) using 1
          · convert primrec_decide_natLe
              (hammingDist_primrec.comp
                (show Primrec fun p :
                    (ℕ × List BitString × ℕ × BitString) × BitString =>
                  p.1.2.2.2 from ?_)
                (show Primrec fun p :
                    (ℕ × List BitString × ℕ × BitString) × BitString => p.2 from ?_))
              (show Primrec fun p :
                  (ℕ × List BitString × ℕ × BitString) × BitString =>
                p.1.2.2.1 from ?_) using 1
            · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) );
            · exact Primrec.snd;
            · exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) );
      convert h_countP.comp
        (show Primrec (fun p : ℕ × List BitString × ℕ × BitString =>
          (p.1, p.2.1.dedup, p.2.2.1, p.2.2.2)) from ?_) using 1
      convert Primrec.pair Primrec.fst
        (Primrec.pair (dedup_primrec.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))) using 1
    have h_all : Primrec (fun p : ℕ × List BitString × ℕ =>
        List.all (allStrings p.1) fun x =>
          p.2.1.dedup.countP (fun y => decide (y.length = p.1) &&
            decide (hammingDist x y ≤ p.2.2)) ≤ p.1) := by
      convert list_all_primrec
        (show Primrec fun p : ℕ × List BitString × ℕ => allStrings p.1 from ?_) _ using 1
      · exact allStrings_primrec.comp ( Primrec.fst );
      · convert Primrec.comp
          (show Primrec (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) from ?_)
          (h_countP.pair Primrec.fst) using 1
        · constructor <;> intro h <;> simp_all +decide only [Primrec₂];
          · convert h.comp
              (show Primrec (fun p : ℕ × List BitString × ℕ × BitString =>
                ((p.1, p.2.1, p.2.2.1), p.2.2.2)) from ?_) using 1
            exact Primrec.pair
              (Primrec.pair Primrec.fst
                (Primrec.pair (Primrec.fst.comp Primrec.snd)
                  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
              (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          · convert h.comp
              (show Primrec (fun p : ℕ × List BitString × ℕ × BitString =>
                (p.1, p.2.1, p.2.2.1, p.2.2.2)) from ?_) using 1
            · constructor <;> intro h <;> simp_all +decide only;
              convert h.comp
                (show Primrec (fun p : (ℕ × List BitString × ℕ) × BitString =>
                  (p.1.1, p.1.2.1, p.1.2.2, p.2)) from ?_) using 1
              exact Primrec.pair (Primrec.fst.comp Primrec.fst)
                (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
                  (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
                    Primrec.snd))
            · exact Primrec.id;
        · exact PrimrecPred.decide
            (PrimrecRel.comp Primrec.nat_le Primrec.fst Primrec.snd)
    convert list_all_primrec _ _ using 1
    · exact inferInstance
    · convert Primrec.list_range.comp
        (Primrec.nat_div.comp Primrec.fst (Primrec.const 64) |>
          Primrec.comp Primrec.succ) using 1
    · convert h_all.comp
        (Primrec.fst.comp Primrec.fst |> Primrec.pair <|
          Primrec.snd.comp Primrec.fst |> Primrec.pair <| Primrec.snd) using 1
  convert Primrec.and.comp
    (Primrec.and.comp
      ‹Primrec fun p : ℕ × List BitString =>
        p.2.all fun x => decide (List.length x = p.1)›
      ‹Primrec fun p : ℕ × List BitString =>
        decide (p.2.dedup.length = 2 ^ p.1 / hammingVol p.1 (p.1 / 64))›)
    h_hammingListDecodingCheckBool using 1

lemma hammingListDecodingSearchList_computable :
    Computable hammingListDecodingSearchList := by
  convert Primrec.to_comp _;
  convert Primrec.option_getD.comp
    (list_find?_primrec (primrec_sublists_gen allStrings_primrec)
      (show Primrec₂ (fun n L => hammingListDecodingCheckBool n L) from ?_))
    (Primrec.const []) using 1
  · ext n; unfold hammingListDecodingSearchList; simp +decide [ hammingListDecodingCheckBool_eq ] ;
  · -- Apply the lemma that states the function is primitive recursive.
    apply hammingListDecodingCheckBool_primrec

noncomputable def hammingListDecodingSearchSet (n : ℕ) : Finset BitString :=
  (hammingListDecodingSearchList n).toFinset

noncomputable def hammingListDecodingSearchCode (w : BitString) : BitString :=
  let n := bitsToNat w
  canonicalUniformCodeOfList (canonicalFinsetList (hammingListDecodingSearchSet n))

lemma hammingListDecodingSearchCode_computable :
    Computable hammingListDecodingSearchCode := by
  have h := hammingListDecodingSearchList_computable
  have hc : Computable (fun w : BitString =>
      canonicalUniformCodeOfList (canonicalFinsetList
        (hammingListDecodingSearchList (bitsToNat w)).toFinset)) :=
    (canonicalUniformCodeOfList_primrec.to_comp).comp
      ((canonicalFinsetList_toFinset_primrec.to_comp).comp
        (h.comp bitsToNat_primrec.to_comp))
  exact hc.of_eq (fun w => rfl)

lemma hammingListDecodingSearchSet_correct (n : ℕ)
    (h_exists : ∃ E : Finset BitString,
      IsHammingListDecodingSet n (n / 64) (2 ^ n / hammingVol n (n / 64)) E) :
    ∃ _hE : (hammingListDecodingSearchSet n).Nonempty,
      IsHammingListDecodingSet n (n / 64) (2 ^ n / hammingVol n (n / 64))
        (hammingListDecodingSearchSet n) := by
  classical
  set r := n / 64
  set N := 2 ^ n / hammingVol n r
  let pred : List BitString → Bool :=
    fun L => @decide (IsHammingListDecodingSetFinite n r N L.toFinset)
      (IsHammingListDecodingSetFinite_decidable n r N L.toFinset)
  obtain ⟨E, hE⟩ := h_exists
  have hE_canon : IsHammingListDecodingSet n r N E := by
    simpa [r, N] using hE
  have hE_fin : IsHammingListDecodingSetFinite n r N E :=
    (IsHammingListDecodingSet_iff_finite n r N E).mp hE_canon
  let L : List BitString := (allStrings n).filter (fun x => decide (x ∈ E))
  have hL_mem : L ∈ (allStrings n).sublists := by
    exact List.mem_sublists.mpr List.filter_sublist
  have hL_set : L.toFinset = E := by
    ext x
    constructor
    · intro hx
      rw [List.mem_toFinset, List.mem_filter] at hx
      exact of_decide_eq_true hx.2
    · intro hx
      rw [List.mem_toFinset, List.mem_filter]
      exact ⟨(mem_allStrings n x).mpr (hE_canon.1 x hx), decide_eq_true hx⟩
  have hL_good : pred L = true := by
    unfold pred
    rw [hL_set]
    exact decide_eq_true hE_fin
  obtain ⟨L₀, hfind⟩ : ∃ L₀, (allStrings n).sublists.find? pred = some L₀ := by
    exact Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr ⟨L, hL_mem, hL_good⟩)
  have hL₀_good_bool : pred L₀ = true := List.find?_some hfind
  have hL₀_fin : IsHammingListDecodingSetFinite n r N L₀.toFinset := by
    unfold pred at hL₀_good_bool
    exact of_decide_eq_true hL₀_good_bool
  have hsearch_eq : hammingListDecodingSearchSet n = L₀.toFinset := by
    unfold hammingListDecodingSearchSet hammingListDecodingSearchList
    exact congrArg List.toFinset
      (congrArg (fun o : Option (List BitString) => o.getD []) hfind)
  have hN_pos : 0 < N := by
    have hV_pos : 0 < hammingVol n r := by
      have h1 : 1 ≤ hammingVol n r := by
        rw [← hammingVol_zero n]
        exact hammingVol_mono (n := n) (Nat.zero_le r)
      exact h1
    have hV_le : hammingVol n r ≤ 2 ^ n := hammingVol_le_two_pow n r
    exact Nat.div_pos hV_le hV_pos
  have hnonempty₀ : L₀.toFinset.Nonempty := by
    apply Finset.card_pos.mp
    rw [hL₀_fin.2.1]
    exact hN_pos
  refine ⟨hsearch_eq ▸ hnonempty₀, ?_⟩
  rw [hsearch_eq]
  exact (IsHammingListDecodingSet_iff_finite n r N L₀.toFinset).mpr hL₀_fin

lemma exists_computable_list_decoding_search :
    ∃ f : BitString → BitString, Computable f ∧
      ∀ n r N : ℕ, r = n / 64 → N = 2 ^ n / hammingVol n r →
      (∃ E : Finset BitString, IsHammingListDecodingSet n r N E) →
      ∃ E : Finset BitString, ∃ hE : E.Nonempty,
        IsHammingListDecodingSet n r N E ∧
        f (Nat.bits n) = (codedUniformOn E hE).code := by
  refine ⟨hammingListDecodingSearchCode, hammingListDecodingSearchCode_computable, ?_⟩
  intro n r N hr hN h_exists
  subst r
  subst N
  obtain ⟨hE, hprop⟩ := hammingListDecodingSearchSet_correct n h_exists
  refine ⟨hammingListDecodingSearchSet n, hE, hprop, ?_⟩
  unfold hammingListDecodingSearchCode
  rw [bitsToNat_bits]
  exact canonicalUniformCodeOfList_canonicalFinsetList (hammingListDecodingSearchSet n) hE

/--
Leaf 1 for M6: The list-decoding set E can be chosen to have logarithmic complexity.
This follows from the exhaustive search / lexicographically first witness pattern.
-/
lemma exists_list_decoding_set_low_complexity (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n r N : ℕ,
    r = n / 64 →
    N = 2 ^ n / hammingVol n r →
    (∃ E : Finset BitString, IsHammingListDecodingSet n r N E) →
    ∃ E : Finset BitString, ∃ hE : E.Nonempty, IsHammingListDecodingSet n r N E ∧
      setComplexity U E hE ≤ (logSlack c n : ENat) := by
  obtain ⟨f, hf_comp, hf_spec⟩ := exists_computable_list_decoding_search
  obtain ⟨c_map, hc_map⟩ := KPPlain_map_le U hU f hf_comp
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  refine ⟨3 + c_len + c_map, fun n r N hr hN hE => ?_⟩
  obtain ⟨E, hE_nonempty, hE_prop, hf_eq⟩ := hf_spec n r N hr hN hE
  refine ⟨E, hE_nonempty, hE_prop, ?_⟩
  unfold setComplexity
  rw [← hf_eq]
  have hc1 := hc_map (Nat.bits n)
  have hc2 := hc_len (Nat.bits n)
  have hlen : (Nat.bits n).length.bits.length ≤ (Nat.bits n).length := by
    exact length_natBits_le_self _
  have h_bound :
      (Nat.bits n).length + 2 * (Nat.bits (Nat.bits n).length).length + c_len + c_map ≤
        logSlack (3 + c_len + c_map) n := by
    unfold logSlack
    nlinarith
  calc KPPlain U (f (Nat.bits n))
    ≤ KPPlain U (Nat.bits n) + (c_map : ENat) := hc1
    _ ≤ ((Nat.bits n).length + 2 * (Nat.bits (Nat.bits n).length).length + c_len : ℕ) +
        (c_map : ENat) := by exact add_le_add hc2 le_rfl
    _ = (((Nat.bits n).length + 2 * (Nat.bits (Nat.bits n).length).length + c_len +
        c_map : ℕ) : ENat) := by push_cast; ring
    _ ≤ logSlack (3 + c_len + c_map) n := by exact_mod_cast h_bound

/--
Leaf 2 for M6: Any non-empty finite set contains an element whose complexity is
close to the log-cardinality of the set (incompressible in the set).
-/
lemma exists_high_complexity_element_in_finset (U : Map) (_hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ E : Finset BitString, ∀ _hE : E.Nonempty,
    ∃ x ∈ E, (Nat.bits E.card).length ≤ KPPlain U x + (c : ENat) := by
  classical
  refine ⟨1, fun E hE => ?_⟩
  let L := (Nat.bits E.card).length
  by_cases hL_small : L ≤ 1
  · obtain ⟨x, hx⟩ := hE
    refine ⟨x, hx, ?_⟩
    calc
      (L : ENat) ≤ (1 : ENat) := by exact_mod_cast hL_small
      _ = (0 : ENat) + (1 : ENat) := by norm_num
      _ ≤ KPPlain U x + (1 : ENat) := by
        exact add_le_add (zero_le (KPPlain U x)) le_rfl
  · have hL_ge2 : 2 ≤ L := by omega
    by_contra hno
    have hsubset : E ⊆ compressibleWords U [] (L - 2) := by
      intro x hx
      have hfail : ¬ ((L : ENat) ≤ KPPlain U x + (1 : ENat)) := by
        intro hgood
        exact hno ⟨x, hx, by simpa [L] using hgood⟩
      have hlt : KPPlain U x + (1 : ENat) < (L : ENat) :=
        lt_of_not_ge hfail
      have hne : KPPlain U x ≠ ⊤ := by
        intro htop
        have htop_add : KPPlain U x + (1 : ENat) = ⊤ := by
          rw [htop]
          simp
        rw [htop_add] at hlt
        exact not_top_lt hlt
      obtain ⟨kx, hkx_raw⟩ := ENat.ne_top_iff_exists.mp hne
      have hkx : KPPlain U x = (kx : ENat) := hkx_raw.symm
      have hKP : KP U x [] = (kx : ENat) := by
        simpa [KPPlain] using hkx
      have hkx_lt : kx + 1 < L := by
        have hcast : ((kx + 1 : ℕ) : ENat) < (L : ENat) := by
          simpa [hKP, Nat.cast_add] using hlt
        exact ENat.coe_lt_coe.mp hcast
      have hle : KPPlain U x ≤ ((L - 2 : ℕ) : ENat) := by
        rw [hkx]
        exact_mod_cast (by omega : kx ≤ L - 2)
      have hle_cond : condK U x [] ≤ ((L - 2 : ℕ) : ENat) := by
        simpa [KPPlain, KP, plainK] using hle
      rw [compressibleWords, Finset.mem_filter]
      refine ⟨?_, hle_cond⟩
      obtain ⟨p, hp_len, hp_prod⟩ := (condKLeIff U x [] (L - 2)).mp hle_cond
      rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
      exact ⟨p, mem_programsLe (L - 2) p hp_len, progToOut_eq_some.mpr hp_prod⟩
    have hcard_le : E.card ≤ (compressibleWords U [] (L - 2)).card :=
      Finset.card_le_card hsubset
    have hcard_lt : E.card < 2 ^ (L - 1) := by
      have hlt := lt_of_le_of_lt hcard_le (cardCompressibleWordsLt U [] (L - 2))
      have hpow : 2 ^ ((L - 2) + 1) = 2 ^ (L - 1) := by
        congr
        omega
      simpa [hpow] using hlt
    have hE_card_pos : 0 < E.card := Finset.card_pos.mpr hE
    have hlower : 2 ^ (L - 1) ≤ E.card := by
      by_contra hnot
      have hltM : E.card < 2 ^ (L - 1) := Nat.lt_of_not_ge hnot
      have hsize_le : Nat.size E.card ≤ L - 1 := Nat.size_le.mpr hltM
      have hsize_eq : Nat.size E.card = L := by
        dsimp [L]
        exact (Nat.size_eq_bits_len E.card).symm
      omega
    omega

/-- Lemma 1: A ball of radius `R` can be covered by balls of radius `r`,
with the same radius-bracketing hypotheses used by `hammingBall_cover_centers`.
The bounds `c ≤ hammingVol n R` and `c ≤ hammingVol n (r+1)` are necessary:
without them, the `length * c` conclusion is false for tiny target balls. -/
lemma hammingBall_covered_by_smaller_balls (n : ℕ) (z : BitString) (R r c : ℕ)
    (hz : z.length = n) (hc : 0 < c)
    (h_R_bound : c ≤ hammingVol n R)
    (h_r_vol : hammingVol n r ≤ c)
    (h_r_next : c ≤ hammingVol n (r + 1))
    (h_c_le : c ≤ (n + 1) * hammingVol n r) :
    ∃ 𝒞 : List BitString,
      (∀ x ∈ 𝒞, x.length = n) ∧
      (∀ y ∈ hammingBall n z R, ∃ x ∈ 𝒞, hammingDist x y ≤ r) ∧
      𝒞.length * c ≤ (n + 1)^7 * (hammingBall n z R).card := by
  exact hammingBall_cover_centers n z R c r hz hc h_R_bound h_r_vol h_r_next h_c_le

/-- Lemma 2: Intersection bound for a list-decoding set and an arbitrary ball.
The `+ 1` is the ceiling/trivial-cover term needed when the target ball is
smaller than the decoding radius volume. -/
lemma hamming_list_decoding_intersection (n r N R : ℕ) (E : Finset BitString) (z : BitString)
    (h_list : IsHammingListDecodingSet n r N E) (hz : z.length = n) :
    (E ∩ hammingBall n z R).card ≤
      n * (((n + 1)^7 * (hammingBall n z R).card) / hammingVol n r + 1) := by
  classical
  set A := hammingBall n z R
  set V := hammingVol n r
  set M := (n + 1)^7 * A.card
  have hA_mem : hammingFamilyMem A := ⟨n, z, R, hz, rfl⟩
  have hV_pos : 0 < V := by
    have h1 : 1 ≤ hammingVol n r := by
      rw [← hammingVol_zero n]
      exact hammingVol_mono (n := n) (Nat.zero_le r)
    exact h1
  by_cases hsmall : A.card ≤ V
  · have hdirect : (A ∩ E).card ≤ n := h_list.2.2 A hA_mem (by simpa [V] using hsmall)
    rw [Finset.inter_comm]
    calc
      (A ∩ E).card ≤ n := hdirect
      _ ≤ n * (M / V + 1) := by
        have hone : 1 ≤ M / V + 1 := Nat.succ_le_succ (Nat.zero_le _)
        nlinarith
  · have hlarge : V ≤ A.card := Nat.le_of_lt (Nat.lt_of_not_ge hsmall)
    obtain ⟨𝒞, h𝒞_small, h𝒞_cover, h𝒞_count⟩ :=
      hammingFamily_cover hA_mem n V hV_pos hlarge
    have hsub : E ∩ A ⊆ 𝒞.toFinset.biUnion (fun B => E ∩ B) := by
      intro y hy
      rw [Finset.mem_inter] at hy
      rcases hy with ⟨hyE, hyA⟩
      have hylen : y.length = n := by
        change y ∈ hammingBall n z R at hyA
        rw [hammingBall, Finset.mem_filter] at hyA
        exact (memStringsOfLength n y).mp hyA.1
      obtain ⟨B, hB𝒞, hyB⟩ := h𝒞_cover y hyA hylen
      rw [Finset.mem_biUnion]
      exact ⟨B, List.mem_toFinset.mpr hB𝒞, by rw [Finset.mem_inter]; exact ⟨hyE, hyB⟩⟩
    have h_each : ∀ B ∈ 𝒞.toFinset, (E ∩ B).card ≤ n := by
      intro B hB
      have hB_list : B ∈ 𝒞 := List.mem_toFinset.mp hB
      rcases h𝒞_small B hB_list with ⟨hB_mem, hB_card⟩
      rw [Finset.inter_comm]
      exact h_list.2.2 B hB_mem (by simpa [V] using hB_card)
    have h_inter_le : (E ∩ A).card ≤ 𝒞.length * n := by
      calc
        (E ∩ A).card ≤ (𝒞.toFinset.biUnion (fun B => E ∩ B)).card :=
          Finset.card_le_card hsub
        _ ≤ ∑ B ∈ 𝒞.toFinset, (E ∩ B).card := Finset.card_biUnion_le
        _ ≤ ∑ _B ∈ 𝒞.toFinset, n := Finset.sum_le_sum (fun B hB => h_each B hB)
        _ = 𝒞.toFinset.card * n := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 𝒞.length * n := by
          exact Nat.mul_le_mul_right n (List.toFinset_card_le 𝒞)
    have hlen_le : 𝒞.length ≤ M / V := by
      rw [Nat.le_div_iff_mul_le hV_pos]
      simpa [M, V, hammingOverhead] using h𝒞_count
    rw [show E ∩ hammingBall n z R = E ∩ A by rfl]
    calc
      (E ∩ A).card ≤ 𝒞.length * n := h_inter_le
      _ ≤ (M / V) * n := Nat.mul_le_mul_right n hlen_le
      _ ≤ n * (M / V + 1) := by nlinarith

/-- The computable decoder underlying `setComplexity_inter_le`: reading a pair of
canonical uniform codes, it recovers both point-lists, intersects them, and
re-encodes the intersection as a canonical uniform code. -/
noncomputable def interDecoder (w : BitString) : BitString :=
  let LE := (decodeDistributionData (decodeFirst w)).map CodedDistributionEntry.point
  let LB := (decodeDistributionData (decodeSecond w)).map CodedDistributionEntry.point
  canonicalUniformCodeOfList
    (canonicalFinsetList (LE.filter (fun x => decide (x ∈ LB))).toFinset)

theorem interDecoder_computable : Computable interDecoder := by
  have hLE : Primrec (fun w : BitString =>
      (decodeDistributionData (decodeFirst w)).map CodedDistributionEntry.point) :=
    Primrec.list_map (decodeDistributionData_primrec.comp decodeFirst_primrec)
      (entry_point_primrec.comp Primrec.snd).to₂
  have hLB : Primrec (fun w : BitString =>
      (decodeDistributionData (decodeSecond w)).map CodedDistributionEntry.point) :=
    Primrec.list_map (decodeDistributionData_primrec.comp decodeSecond_primrec)
      (entry_point_primrec.comp Primrec.snd).to₂
  have hp : Primrec₂ (fun (w : BitString) (x : BitString) =>
      decide (x ∈ (decodeDistributionData (decodeSecond w)).map CodedDistributionEntry.point)) :=
    bitString_mem_primrec.comp Primrec.snd (hLB.comp Primrec.fst)
  have hfilter : Primrec (fun w : BitString =>
      ((decodeDistributionData (decodeFirst w)).map CodedDistributionEntry.point).filter
        (fun x => decide (x ∈
          (decodeDistributionData (decodeSecond w)).map CodedDistributionEntry.point))) :=
    list_filter_primrec hLE hp
  exact (canonicalUniformCodeOfList_primrec.comp
    (canonicalFinsetList_toFinset_primrec.comp hfilter)).to_comp

theorem interDecoder_eq (E B : Finset BitString) (hE : E.Nonempty) (hB : B.Nonempty)
    (hI : (E ∩ B).Nonempty) :
    interDecoder (pairCode (codedUniformOn E hE).code (codedUniformOn B hB).code)
      = (codedUniformOn (E ∩ B) hI).code := by
  unfold interDecoder
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, dataPoints_codedUniformOn]
  have hset : ((canonicalFinsetList E).filter
      (fun x => decide (x ∈ canonicalFinsetList B))).toFinset = E ∩ B := by
    ext y
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_canonicalFinsetList,
      Finset.mem_inter]
  rw [hset]
  exact canonicalUniformCodeOfList_canonicalFinsetList (E ∩ B) hI

/-- Helper A for `KPPlain_le_intersection`: the canonical uniform code of an
intersection has complexity bounded by the sum of the two set complexities, up
to an additive constant.  Proved by a computable decoder that reads the two
uniform codes, recovers both point-lists (`dataPoints_codedUniformOn`),
intersects them, and re-encodes. -/
lemma setComplexity_inter_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (E B : Finset BitString) (hE : E.Nonempty) (hB : B.Nonempty)
      (hI : (E ∩ B).Nonempty),
      setComplexity U (E ∩ B) hI ≤ setComplexity U E hE + setComplexity U B hB + (c : ENat) := by
  obtain ⟨c_map, hmap⟩ := KPPlain_map_le U hU interDecoder interDecoder_computable
  obtain ⟨c_pair, hpair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  refine ⟨c_map + c_pair, fun E B hE hB hI => ?_⟩
  have hcode := interDecoder_eq E B hE hB hI
  calc
    setComplexity U (E ∩ B) hI
        = KPPlain U (interDecoder (pairCode (codedUniformOn E hE).code
            (codedUniformOn B hB).code)) := by rw [hcode]; rfl
    _ ≤ KPPlain U (pairCode (codedUniformOn E hE).code (codedUniformOn B hB).code)
          + (c_map : ENat) := hmap _
    _ = KPPair U (codedUniformOn E hE).code (codedUniformOn B hB).code + (c_map : ENat) := by
          rw [KPPlain_eq_KP, KPPair_eq_KP_pairCode]
    _ ≤ (KPPlain U (codedUniformOn E hE).code + KPPlain U (codedUniformOn B hB).code
          + (c_pair : ENat)) + (c_map : ENat) := by
          gcongr; exact hpair _ _
    _ = setComplexity U E hE + setComplexity U B hB + ((c_map + c_pair : ℕ) : ENat) := by
          unfold setComplexity; push_cast; ring

/-- The option-valued core of the fixed-length set-index decompressor: given a
program `pr.1` (the fixed-length index bits) and a context `pr.2` (a canonical
uniform set code), it decodes the point-list, checks that the program length
matches `⌈log₂ card⌉`, and returns the indexed element. -/
def setIndexDecompressorOpt (pr : BitString × BitString) : Option BitString :=
  let L := (decodeDistributionData pr.2).map CodedDistributionEntry.point
  bif (pr.1.length == (Nat.bits L.length).length) then some (L.getD (bitsToNat pr.1) []) else none

/-- The fixed-length set-index conditional decompressor.  For each fixed context,
all halting programs share one length, so the halting domain is prefix-free. -/
noncomputable def setIndexDecompressor : Map := fun pr =>
  Part.ofOption (setIndexDecompressorOpt pr)

theorem setIndexDecompressor_computable : isDecompressor setIndexDecompressor := by
  have hL : Primrec (fun pr : BitString × BitString =>
        (decodeDistributionData pr.2).map CodedDistributionEntry.point) :=
    Primrec.list_map (decodeDistributionData_primrec.comp Primrec.snd)
      (entry_point_primrec.comp Primrec.snd).to₂
  have hs : Primrec (fun pr : BitString × BitString =>
        (Nat.bits
          ((decodeDistributionData pr.2).map CodedDistributionEntry.point).length).length) :=
    Primrec.list_length.comp (primrecNatBits.comp (Primrec.list_length.comp hL))
  have hlen : Primrec (fun pr : BitString × BitString => pr.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have h_beq : Primrec (fun pr : BitString × BitString =>
      (pr.1.length ==
        (Nat.bits
          ((decodeDistributionData pr.2).map CodedDistributionEntry.point).length).length)) :=
    Primrec.beq.comp hlen hs
  have hcond : PrimrecPred (fun pr : BitString × BitString =>
      (pr.1.length ==
        (Nat.bits
          ((decodeDistributionData pr.2).map CodedDistributionEntry.point).length).length) =
            true) :=
    Primrec.eq.comp h_beq (Primrec.const true)
  have hidx : Primrec (fun pr : BitString × BitString => bitsToNat pr.1) :=
    bitsToNat_primrec.comp Primrec.fst
  have hout : Primrec (fun pr : BitString × BitString =>
        ((decodeDistributionData pr.2).map CodedDistributionEntry.point).getD
          (bitsToNat pr.1) []) :=
    (Primrec.list_getD []).comp hL hidx
  have h_opt : Primrec setIndexDecompressorOpt := by
    refine (Primrec.ite hcond (Primrec.option_some.comp hout)
      (Primrec.const none)).of_eq (fun pr => ?_)
    cases h : (pr.1.length ==
        (Nat.bits
          ((decodeDistributionData pr.2).map CodedDistributionEntry.point).length).length) <;>
      simp only [setIndexDecompressorOpt, h, cond_true, cond_false,
        Bool.false_eq_true, eq_self, if_true, if_false]
  exact Computable.ofOption h_opt.to_comp

theorem setIndexDecompressor_isPrefixMachine : IsPrefixMachine setIndexDecompressor := by
  have key : ∀ (y r : BitString), setIndexDecompressorOpt (r, y) ≠ none →
      r.length =
        (Nat.bits ((decodeDistributionData y).map CodedDistributionEntry.point).length).length := by
    intro y r hr
    by_cases h : (r.length ==
        (Nat.bits
          ((decodeDistributionData y).map CodedDistributionEntry.point).length).length) = true
    · exact beq_iff_eq.mp h
    · exfalso
      rw [Bool.not_eq_true] at h
      simp only [setIndexDecompressorOpt, h, cond_false, ne_eq, not_true_eq_false] at hr
  intro y p hp q hq hpre
  have hp' : setIndexDecompressorOpt (p, y) ≠ none := by
    intro h
    change (Part.ofOption (setIndexDecompressorOpt (p, y))).Dom at hp
    rw [h] at hp; exact hp
  have hq' : setIndexDecompressorOpt (q, y) ≠ none := by
    intro h
    change (Part.ofOption (setIndexDecompressorOpt (q, y))).Dom at hq
    rw [h] at hq; exact hq
  exact hpre.eq_of_length (by rw [key y p hp', key y q hq'])

theorem setIndexDecompressor_produces (S : Finset BitString) (hS : S.Nonempty) (x : BitString)
    (hx : x ∈ S) :
    produces setIndexDecompressor
      (chunkAddress ((canonicalFinsetList S).findIdx (· == x)) (Nat.bits S.card).length)
      (codedUniformOn S hS).code x := by
  set idx := (canonicalFinsetList S).findIdx (· == x) with hidx
  set s := (Nat.bits S.card).length with hs
  have hxL : x ∈ canonicalFinsetList S := mem_canonicalFinsetList.mpr hx
  have hlt : (canonicalFinsetList S).findIdx (· == x) < (canonicalFinsetList S).length := by
    rw [List.findIdx_lt_length]; exact ⟨x, hxL, by simp⟩
  have hidx_lt : idx < S.card := by rw [hidx, ← length_canonicalFinsetList]; exact hlt
  have hcard_lt : S.card < 2 ^ s := by
    rw [hs, Nat.size_eq_bits_len]; exact Nat.lt_size_self S.card
  have hplen : (chunkAddress idx s).length = s :=
    chunkAddress_length idx s (lt_trans hidx_lt hcard_lt)
  have hgetD : (canonicalFinsetList S).getD idx [] = x := by
    rw [hidx, List.getD_eq_getElem _ _ hlt]
    have hpred := List.findIdx_getElem (w := hlt) (p := (· == x)) (xs := canonicalFinsetList S)
    simpa using hpred
  change x ∈ Part.ofOption (setIndexDecompressorOpt
    (chunkAddress idx s, (codedUniformOn S hS).code))
  rw [Part.mem_ofOption]
  unfold setIndexDecompressorOpt
  simp only [dataPoints_codedUniformOn S hS, length_canonicalFinsetList, hplen, ← hs,
    beq_self_eq_true, cond_true, Option.mem_def, Option.some.injEq]
  rw [bitsToNat_chunkAddress]
  exact hgetD

/-- Helper B for `KPPlain_le_intersection`: given the canonical uniform code of a
finite set `S` as the conditioning string, any element of `S` can be described by
its (fixed-length) index within `S`, so its conditional complexity is bounded by
`log₂ |S| + O(1)`. -/
lemma KP_le_log_card_given_setCode (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (S : Finset BitString) (hS : S.Nonempty) (x : BitString),
      x ∈ S →
      KP U x (codedUniformOn S hS).code ≤ (Nat.bits S.card).length + (c : ENat) := by
  obtain ⟨c, hc⟩ := hU.invariance
    ⟨setIndexDecompressor_computable, setIndexDecompressor_isPrefixMachine⟩
  refine ⟨c, fun S hS x hx => ?_⟩
  set idx := (canonicalFinsetList S).findIdx (· == x) with hidx
  set s := (Nat.bits S.card).length with hs
  have hxL : x ∈ canonicalFinsetList S := mem_canonicalFinsetList.mpr hx
  have hlt : (canonicalFinsetList S).findIdx (· == x) < (canonicalFinsetList S).length := by
    rw [List.findIdx_lt_length]; exact ⟨x, hxL, by simp⟩
  have hidx_lt : idx < S.card := by rw [hidx, ← length_canonicalFinsetList]; exact hlt
  have hcard_lt : S.card < 2 ^ s := by
    rw [hs, Nat.size_eq_bits_len]; exact Nat.lt_size_self S.card
  have hplen : (chunkAddress idx s).length = s :=
    chunkAddress_length idx s (lt_trans hidx_lt hcard_lt)
  have hprod := setIndexDecompressor_produces S hS x hx
  calc KP U x (codedUniformOn S hS).code
      ≤ KP setIndexDecompressor x (codedUniformOn S hS).code + (c : ENat) :=
        hc x (codedUniformOn S hS).code
    _ ≤ (programLength (chunkAddress idx s) : ENat) + (c : ENat) := by
        gcongr; exact KP_le_programLength_of_produces hprod
    _ = ((Nat.bits S.card).length : ENat) + (c : ENat) := by
        rw [programLength, hplen]

/-- Lemma 3: Complexity of an element in the intersection. -/
lemma KPPlain_le_intersection (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_int : ℕ, ∀ (E B : Finset BitString) (hE : E.Nonempty) (hB : B.Nonempty) (x : BitString),
      x ∈ E ∩ B →
      KPPlain U x ≤ setComplexity U E hE + setComplexity U B hB +
                    (Nat.bits (E ∩ B).card).length + c_int := by
  obtain ⟨cA, hA⟩ := setComplexity_inter_le U hU
  obtain ⟨cB, hB'⟩ := KP_le_log_card_given_setCode U hU
  obtain ⟨c2, h2⟩ := KPPlain_le_KPPlain_add_KP U hU
  refine ⟨cA + cB + c2, fun E B hE hB x hx => ?_⟩
  have hxE : x ∈ E := (Finset.mem_inter.mp hx).1
  have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
  have hI : (E ∩ B).Nonempty := ⟨x, hx⟩
  calc
    KPPlain U x
        ≤ setComplexity U (E ∩ B) hI + KP U x (codedUniformOn (E ∩ B) hI).code + (c2 : ENat) :=
          h2 x (codedUniformOn (E ∩ B) hI).code
    _ ≤ (setComplexity U E hE + setComplexity U B hB + (cA : ENat))
          + ((Nat.bits (E ∩ B).card).length + (cB : ENat)) + (c2 : ENat) := by
          gcongr
          · exact hA E B hE hB hI
          · exact hB' (E ∩ B) hI x hx
    _ = setComplexity U E hE + setComplexity U B hB + (Nat.bits (E ∩ B).card).length
          + ((cA + cB + c2 : ℕ) : ENat) := by push_cast; ring

/-
Linear lower bound on the Hamming volume at radius `n / 64`:
`2 ^ (5 * (n / 64)) ≤ hammingVol n (n / 64)`.  This gives `log₂ V ≥ 5 * ⌊n/64⌋`,
the volume lower bound the Hamming gap argument needs.
-/
lemma hammingVol_ge_two_pow_lin (n : ℕ) :
    2 ^ (5 * (n / 64)) ≤ hammingVol n (n / 64) := by
  rw [ pow_mul ];
  -- The selected binomial coefficient is large enough by induction on the radius.
  suffices h_ind : ∀ r : ℕ, ∀ n : ℕ, 64 * r ≤ n → 32 ^ r ≤ Nat.choose n r by
    exact le_trans (h_ind _ _ (by omega))
      (Finset.single_le_sum (fun x _ => Nat.zero_le (Nat.choose n x))
        (Finset.mem_range.mpr (Nat.lt_succ_self _)))
  intro r n hn
  induction r generalizing n with
  | zero => norm_num [ Nat.pow_succ', Nat.choose ] at *
  | succ r ih =>
    norm_num [ Nat.pow_succ', Nat.choose ] at *
    have := Nat.add_one_mul_choose_eq n r
    nlinarith! [ ih n ( by linarith ), Nat.choose_succ_succ n r ]

/-
Any linear function of `(Nat.bits n).length` (i.e. `O(log n)`) is eventually
dominated by `n / 16`: for all `A B`, there is a threshold `M` beyond which
`16 * (A * (Nat.bits n).length + B) ≤ n`.  Used to pick `c_min` in the Hamming
gap argument, where a linear-in-`n` volume term beats the `O(log n)` slack.
-/
lemma exists_bits_linear_domination (K A B : ℕ) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → K * (A * (Nat.bits n).length + B) ≤ n := by
  -- Beyond a fixed threshold, the exponential `2 ^ (m - 1)` dominates the
  -- linear expression in `m`.
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, ∀ m ≥ m₀, K * (A * m + B) ≤ 2^(m-1) := by
    use 8 * K * ( A + B + 1 ) + 8;
    intro m hm;
    -- We'll use that $2^{m-1} \geq m^2$ for $m \geq 8$.
    have h_exp : 2 ^ (m - 1) ≥ m ^ 2 := by
      rcases m with ( _ | _ | _ | _ | _ | _ | _ | _ | m ) <;>
        simp +arith +decide only [
          ge_iff_le, add_le_add_iff_right, Nat.add_one_sub_one, Nat.pow_succ, pow_one
        ] at *;
      exact Nat.recOn m ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; nlinarith;
    nlinarith [mul_nonneg (Nat.zero_le K) (Nat.zero_le A),
      mul_nonneg (Nat.zero_le K) (Nat.zero_le B)]
  refine ⟨ 2 ^ m₀, fun n hn => le_trans ( hm₀ _ ?_ ) ?_ ⟩;
  · rw [ Nat.size_eq_bits_len ];
    exact Nat.le_of_not_lt fun h => by linarith [ Nat.size_le.mp h.le ] ;
  · convert Nat.pow_le_of_le_log ( by linarith [ Nat.one_le_pow m₀ 2 zero_lt_two ] ) _ using 1;
    rw [ Nat.le_iff_lt_or_eq ];
    refine lt_or_eq_of_le ( Nat.sub_le_of_le_add <| ?_ );
    convert Nat.size_le.2 _
    · convert Nat.size_eq_bits_len n
    · exact Nat.lt_pow_succ_log_self (by decide) _

/-
Bits-length bound for the list-decoding intersection.  If `V ≥ 2 ^ v` and the
ball cardinality `Bcard ≤ 2 ^ t`, and `W` is bounded by the covering estimate
`n * ((n+1)^7 * Bcard / V + 1)`, then `(Nat.bits W).length` is bounded by
`8 * (Nat.bits (n+1)).length + (t - v) + 1`.  This packages the messy division /
size arithmetic of the Hamming gap argument.
-/
lemma bits_intersection_bound (n Bcard V W t v : ℕ)
    (hv : 2 ^ v ≤ V) (hBcard : Bcard ≤ 2 ^ t)
    (hW : W ≤ n * ((n + 1) ^ 7 * Bcard / V + 1)) :
    (Nat.bits W).length ≤ 8 * (Nat.bits (n + 1)).length + (t - v) + 1 := by
  -- Apply the size bound to W
  have hW_size : W ≤ (n + 1) ^ 8 * 2 ^ (t - v) := by
    -- Bound the quotient using the lower bound on `V`.
    have h_simp : n * ((n + 1) ^ 7 * Bcard / V + 1) ≤ (n + 1) ^ 8 * 2 ^ (t - v) := by
      have h_div : (n + 1) ^ 7 * Bcard / V ≤ (n + 1) ^ 7 * 2 ^ (t - v) := by
        by_cases h : t ≥ v;
        · refine Nat.div_le_of_le_mul ?_;
          rw [show 2 ^ t = 2 ^ (t - v) * 2 ^ v by
            rw [← pow_add, Nat.sub_add_cancel h]] at hBcard
          nlinarith [show 0 < (n + 1) ^ 7 by positivity,
            show 0 < 2 ^ v by positivity, show 0 < 2 ^ (t - v) by positivity,
            mul_le_mul_right hv ((n + 1) ^ 7)]
        · simp_all +decide only [
            ge_iff_le, not_le, Nat.sub_eq_zero_of_le (le_of_not_ge h), pow_zero, mul_one
          ];
          exact Nat.div_le_of_le_mul <| by
            nlinarith [pow_pos (Nat.succ_pos n) 7, pow_pos (zero_lt_two' ℕ) t,
              pow_le_pow_right₀ (by decide : 1 ≤ 2) h.le]
      by_cases h : t - v ≥ 0 <;> simp_all +decide [ Nat.pow_succ' ];
      nlinarith [pow_pos (Nat.succ_pos n) 2, pow_pos (Nat.succ_pos n) 3,
        pow_pos (Nat.succ_pos n) 4, pow_pos (Nat.succ_pos n) 5,
        pow_pos (Nat.succ_pos n) 6, pow_pos (Nat.succ_pos n) 7,
        pow_pos (Nat.succ_pos n) 8, pow_pos (zero_lt_two' ℕ) (t - v)]
    exact Nat.le_trans hW h_simp;
  -- Apply the size bound to W and simplify
  have hW_size_simplified : W < 2 ^ (8 * (n + 1).size + (t - v) + 1) := by
    refine lt_of_le_of_lt hW_size ?_;
    rw [ pow_add, pow_add, pow_mul' ];
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.lt_size_self _ |>.le) _))
      (lt_mul_of_one_lt_right (by positivity) (by norm_num))
  rw [ Nat.size_eq_bits_len ] at *;
  convert Nat.size_le.mpr hW_size_simplified using 1;
  rw [ Nat.size_eq_bits_len ]

/-
The deterministic profile-exclusion lemma.
If E is a list-decoding set of low complexity, and x ∈ E is an element of high complexity,
then x is excluded from a region of the restricted profile P_x^𝒜 (for 𝒜 = Hamming balls).
-/
lemma hamming_gap_exclusion (U : Map) (hU : IsOptimalPrefixConditional U) (c : ℕ) :
    ∃ c_gap : ℕ, c_gap > 0 ∧ ∃ c_min : ℕ, ∀ n N : ℕ, ∀ E : Finset BitString, ∀ hE : E.Nonempty,
    IsHammingListDecodingSet n (n / 64) N E →
    N = 2 ^ n / hammingVol n (n / 64) →
    setComplexity U E hE ≤ (logSlack c n : ENat) →
    (n ≥ c_min) →
    ∀ x ∈ E, (Nat.bits N).length ≤ KPPlain U x + (c : ENat) →
    ∃ i j : ℕ, InDescriptionProfile U x i j ∧
      ¬ InDescriptionProfileIn hammingFamily U x (i + n / c_gap) (j + n / c_gap) := by
  obtain ⟨ c_int, hc_int ⟩ := KPPlain_le_intersection U hU
  simp +decide only [
    gt_iff_lt, ge_iff_le, KPPlain_eq_KP, InDescriptionProfile,
    InDescriptionProfileIn, not_exists
  ]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ≥ M,
      64 * ((2 * c + 8) * (Nat.bits n).length + (3 * c + 9 + c_int)) ≤ n := by
    exact exists_bits_linear_domination 64 ( 2 * c + 8 ) ( 3 * c + 9 + c_int );
  refine ⟨ 128, by norm_num, Max.max M 64, ?_ ⟩;
  intro n N E hE h_list hN hEcomp hn x hxE hxK
  use logSlack c n, N.bits.length
  constructor;
  · refine ⟨ E, hE, hxE, hEcomp, ?_ ⟩;
    rw [ h_list.2.1, Nat.le_iff_lt_or_eq ];
    exact lt_or_eq_of_le (Nat.le_of_lt (Nat.lt_size_self N) |>
      le_trans <| by rw [Nat.size_eq_bits_len])
  · intro B hB hBdesc
    obtain ⟨hBmem, hBdesc⟩ := hBdesc
    obtain ⟨m, z, r', hzlen, hBeq⟩ := hBmem
    have hz : z.length = n := by
      have := hBdesc.1; simp_all +decide [ hammingBall ] ;
      have := h_list.1 x hxE; simp_all +decide [ stringsOfLength ] ;
    have hBcard : B.card ≤ 2^(N.bits.length + n / 128) := by
      have := hBdesc.2.2; aesop;
    have hW : (E ∩ B).card ≤ n * ((n + 1)^7 * B.card / hammingVol n (n / 64) + 1) := by
      have := hamming_list_decoding_intersection n ( n / 64 ) N r' E z h_list hz; aesop;
    have hbits : (Nat.bits (E ∩ B).card).length ≤
        8 * (Nat.bits (n + 1)).length +
          ((N.bits.length + n / 128) - 5 * (n / 64)) + 1 := by
      apply bits_intersection_bound n B.card (hammingVol n (n / 64)) (E ∩ B).card
        (N.bits.length + n / 128) (5 * (n / 64)) (hammingVol_ge_two_pow_lin n)
        hBcard hW
    have hkey : N.bits.length ≤
        (logSlack c n + (logSlack c n + n / 128) +
          (8 * (Nat.bits (n + 1)).length +
            ((N.bits.length + n / 128) - 5 * (n / 64)) + 1) + c_int : ℕ) + c := by
      have hkey : KPPlain U x ≤
          setComplexity U E hE + setComplexity U B hB +
            (Nat.bits (E ∩ B).card).length + c_int := by
        exact hc_int E B hE hB x ( Finset.mem_inter.mpr ⟨ hxE, hBdesc.1 ⟩ );
      have hkey : KPPlain U x ≤
          (logSlack c n + (logSlack c n + n / 128) +
            (8 * (Nat.bits (n + 1)).length +
              ((N.bits.length + n / 128) - 5 * (n / 64)) + 1) + c_int : ℕ) := by
        refine le_trans hkey ?_;
        norm_num +zetaDelta at *;
        gcongr;
        · exact_mod_cast hBdesc.2.1;
        · norm_cast;
      contrapose! hxK;
      refine lt_of_le_of_lt ?_ ( Nat.cast_lt.mpr hxK );
      convert add_le_add_right hkey ( c : ENat ) using 1;
      · rw [ add_comm, KPPlain_eq_KP ];
      · norm_cast ; ring;
    have hlog : 2 ^ (5 * (n / 64)) ≤ N := by
      rw [ hN ];
      refine Nat.le_div_iff_mul_le ( Nat.pos_of_ne_zero ?_ ) |>.2 ?_;
      · exact ne_of_gt ( hammingVol_ge_two_pow_lin n |> lt_of_lt_of_le ( by norm_num ) );
      · refine le_trans ( Nat.mul_le_mul_left _ ( hammingVol_le_two_pow_half n ) ) ?_;
        rw [ ← pow_add ] ; exact pow_le_pow_right₀ ( by decide ) ( by omega ) ;
    have hlog : 5 * (n / 64) ≤ N.bits.length := by
      rw [ Nat.le_iff_lt_or_eq ];
      refine lt_or_eq_of_le ( Nat.le_of_not_lt fun h => ?_ );
      have := Nat.lt_size_self N
      simp_all +decide only [
        Finset.mem_inter, KPPlain_eq_KP, Nat.size_eq_bits_len, and_imp, ge_iff_le,
        sup_le_iff
      ]
      exact not_le_of_gt this ( Nat.le_trans ( pow_le_pow_right₀ ( by decide ) h.le ) hlog );
    unfold logSlack at *;
    grind

/--
M6 (stretch): Hamming gap.
Consider the family 𝒜 that consists of all Hamming balls. For some positive ε
and for all sufficiently large n there exists a string x of length n such that
the distance between P_x^𝒜 and P_x exceeds ε n.

We state "distance > ε n" formally as: there exists a point (i, j)
in the unrestricted profile P_x such that the restricted profile P_x^𝒜 does not
contain (i + ⌊n / c_gap⌋, j + ⌊n / c_gap⌋).
-/
theorem prop_hamming_gap (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_gap : ℕ, c_gap > 0 ∧ ∃ c : ℕ, ∀ n ≥ c, ∃ x : BitString,
      x.length = n ∧
      ∃ i j : ℕ, InDescriptionProfile U x i j ∧
        ¬ InDescriptionProfileIn hammingFamily U x (i + n / c_gap) (j + n / c_gap) := by
  obtain ⟨c_E, hc_E⟩ := exists_list_decoding_set_low_complexity U hU
  obtain ⟨c_x, hc_x⟩ := exists_high_complexity_element_in_finset U hU
  let c_total := max c_x c_E
  obtain ⟨c_gap, hgap_pos, c_min, hex⟩ := hamming_gap_exclusion U hU c_total
  refine ⟨c_gap, hgap_pos, max c_min (max c_total 64), ?_⟩
  intro n hn
  set r := n / 64
  set N := 2 ^ n / hammingVol n r
  have hn_pos : 0 < n := by omega
  have hN_eq : N = 2 ^ n / hammingVol n r := rfl
  have hr_eq : r = n / 64 := rfl
  have hE_exists := exists_list_decoding_set n r N hn_pos hN_eq
  obtain ⟨E, hE_ne, hE_is, hE_K⟩ := hc_E n r N hr_eq hN_eq hE_exists
  obtain ⟨x, hx_in, hx_K⟩ := hc_x E hE_ne
  have h_len : ∀ x ∈ E, x.length = n := hE_is.1
  have hn_ge : n ≥ c_min := by omega
  have hcE_le : c_E ≤ c_total := by
    dsimp [c_total]
    exact le_max_right _ _
  have hcx_le : c_x ≤ c_total := by
    dsimp [c_total]
    exact le_max_left _ _
  have hE_K' : setComplexity U E hE_ne ≤ (logSlack c_total n : ENat) := by
    calc
      setComplexity U E hE_ne ≤ (logSlack c_E n : ENat) := hE_K
      _ ≤ (logSlack c_total n : ENat) := by
        exact_mod_cast logSlack_mono_left hcE_le n
  have hx_K' : (Nat.bits N).length ≤ KPPlain U x + (c_total : ENat) := by
    have hx_KN : ((Nat.bits N).length : ENat) ≤ KPPlain U x + (c_x : ENat) := by
      simpa [hE_is.2.1] using hx_K
    calc
      ((Nat.bits N).length : ENat) ≤ KPPlain U x + (c_x : ENat) := hx_KN
      _ ≤ KPPlain U x + (c_total : ENat) := by
        exact add_le_add le_rfl (by exact_mod_cast hcx_le : (c_x : ENat) ≤ (c_total : ENat))
  obtain ⟨i, j, h_in_prof, h_not_in_prof⟩ := hex n N E hE_ne hE_is hN_eq hE_K' hn_ge x hx_in hx_K'
  refine ⟨x, h_len x hx_in, i, j, h_in_prof, h_not_in_prof⟩

end Kolmogorov
