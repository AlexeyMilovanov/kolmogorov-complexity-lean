import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.Restricted.Examples.HammingBalls.Part01
import KolmogorovMathlib.Restricted.Examples.HammingBalls
import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.Restricted.EffectiveSelection

/-!
# Finite Hamming list-decoding sets

`IsHammingListDecodingSet n r N E` says that every Hamming ball of radius `r` in
`{0,1}^n` contains at most `N` elements of `E`. This module proves the finite counting
theorem that produces a large set with this property.

The proof develops upper bounds for Hamming-ball volume and for the number of subsets bad for a
fixed ball, then applies a finite selection argument. `exists_list_decoding_set` is the main
existence result.

For effectivization, the property is reduced to `hammingListDecodingCandidates`, represented by
`IsHammingListDecodingSetFinite` and the Boolean check `hammingListDecodingCheckBool`.
-/



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

/-- The number of `N`-element subsets of the ambient set meeting `A` in exactly `k` points is
`C(#A, k) · C(#univ - #A, N - k)`. -/
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

/-- The number of `N`-element subsets meeting `A` in more than `n` points, summed over the
possible intersection sizes. -/
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

/-- If the bad sets are fewer than all `N`-element subsets, some `N`-element subset meets every
member of the family in at most `n` points. -/
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
  push Not at h_not_subset
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
  push Not at h_not_in_Bad
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
        ∑ k ∈ Finset.Ico (n + 1) (N + 1),
            a.choose k * (M - a).choose (N - k) ≤
          a.choose (n + 1) * ∑ j ∈ Finset.range (N - n),
            (a - (n + 1)).choose j *
              (M - a).choose (N - (n + 1 + j)) := by
      have h_each : ∀ k ∈ Finset.Ico (n + 1) (N + 1),
          a.choose k * (M - a).choose (N - k) ≤
            a.choose (n + 1) *
                (a - (n + 1)).choose (k - (n + 1)) *
              (M - a).choose (N - k) := by
        intro k hk
        have h_choose : a.choose k ≤
            a.choose (n + 1) *
              (a - (n + 1)).choose (k - (n + 1)) := by
          rw [← Nat.choose_mul]
          · exact le_mul_of_one_le_right (Nat.zero_le _)
              (Nat.choose_pos (by linarith [Finset.mem_Ico.mp hk]))
          · linarith [Finset.mem_Ico.mp hk]
        exact Nat.mul_le_mul_right _ h_choose
      calc
        ∑ k ∈ Finset.Ico (n + 1) (N + 1),
            a.choose k * (M - a).choose (N - k) ≤
            ∑ k ∈ Finset.Ico (n + 1) (N + 1),
              a.choose (n + 1) *
                  (a - (n + 1)).choose (k - (n + 1)) *
                (M - a).choose (N - k) :=
          Finset.sum_le_sum h_each
        _ = a.choose (n + 1) * ∑ j ∈ Finset.range (N - n),
              (a - (n + 1)).choose j *
                (M - a).choose (N - (n + 1 + j)) := by
          rw [Finset.mul_sum _ _ _, Finset.sum_Ico_eq_sum_range]
          simp +decide [mul_assoc]
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
      apply Finset.prod_le_prod;
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
            (by simp +decide [card_stringsOfLength])
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
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, card_stringsOfLength ];
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
  have h_univ_card : (stringsOfLength n).card = 2 ^ n := card_stringsOfLength n
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
  · exact mem_stringsOfLength n x |>.mp (hE_sub hx)
  · rcases hA_mem with ⟨n', x', r', hx'len, rfl⟩
    by_cases hn_eq : n' = n
    · have h_len_eq : x'.length = n := hx'len.trans hn_eq
      rw [hn_eq]
      have hA_eq : hammingBall n x' r' = hammingBall n x' (min r' n) := by
        ext y
        simp only [hammingBall, Finset.mem_filter]
        apply and_congr_right
        intro hy
        have h_len : y.length = n := mem_stringsOfLength n y |>.mp hy
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
        push Not at h_not
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
        exact mem_stringsOfLength n x' |>.mpr h_len_eq
      have h_inter := hE_inter (hammingBall n x' (min r' n)) hA_in
      rw [hA_eq]
      exact h_inter
    · have h_inter_empty : hammingBall n' x' r' ∩ E = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        rw [Finset.mem_inter] at hy
        rcases hy with ⟨hyA, hyE⟩
        rw [hammingBall, Finset.mem_filter] at hyA
        have h1 := mem_stringsOfLength n' y |>.mp hyA.1
        have h2 := hE_sub hyE
        have h3 := mem_stringsOfLength n y |>.mp h2
        rw [h3] at h1
        exact hn_eq h1.symm
      rw [h_inter_empty, Finset.card_empty]
      exact Nat.zero_le n

/-- Being a list-decoding set is equivalent to meeting every Hamming ball of radius at most `r`
in at most `n` points. -/
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
      ⟨n, x', r', mem_stringsOfLength _ _ |>.mp hx', rfl⟩
    have h_card : (hammingBall n x' r').card ≤ hammingVol n r := by
      rw [hammingBall_card]
      · exact hammingVol_mono hr'
      · exact mem_stringsOfLength _ _ |>.mp hx'
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
        have h_len : y.length = n := mem_stringsOfLength n y |>.mp hy
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
        push Not at h_not
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
        exact mem_stringsOfLength n x' |>.mpr hn_eq
      have h_inter := h (hammingBall n x' (min r' n)) hA_in
      rw [hA_eq]
      exact h_inter
    · have h_inter_empty : hammingBall x'.length x' r' ∩ E = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        rw [Finset.mem_inter] at hy
        rcases hy with ⟨hyA, hyE⟩
        rw [hammingBall, Finset.mem_filter] at hyA
        have h1 := mem_stringsOfLength x'.length y |>.mp hyA.1
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

/-- The candidate sets are exactly the Hamming balls of radius at most `r` around length-`n`
centres. -/
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

/-- The list-decoding property agrees with its finitary reformulation. -/
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

/-- The finitary list-decoding property is decidable. -/
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
  · simpa [hammingBall] using
      (hammingBall_card n (List.replicate n false) r (by simp)).symm
  · rw [ List.countP_eq_length_filter ];
    rw [ ← Multiset.coe_card ];
    rw [← Multiset.toFinset_card_of_nodup]
    · aesop
    · exact List.Nodup.filter _ (allStrings_nodup n)

/-- The Hamming ball volume is primitive recursive in the dimension and the radius. -/
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
        have hargs : Primrec (fun p : (ℕ × ℕ) × BitString =>
            ((List.replicate p.1.1 false, p.1.2), p.2)) :=
          Primrec.pair
            (‹Primrec fun p : ℕ × ℕ =>
              (List.replicate p.1 false, p.2)›.comp Primrec.fst)
            Primrec.snd
        exact (h_pred.comp hargs).to₂.of_eq (fun _ _ => rfl)
      have := @list_countP_primrec;
      convert this ( show Primrec fun p : ℕ × ℕ => allStrings p.1 from ?_ ) h_pred using 1;
      exact allStrings_primrec.comp ( Primrec.fst );
    exact h_hammingVol_primrec;
  convert h_hammingVol_primrec using 1;
  exact funext fun n => funext fun r => hammingVol_eq_countP n r

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

/-
The Boolean check agrees with the decidable finite list-decoding predicate.
-/
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

/-- The boolean list-decoding test agrees with the decision procedure for the finitary property. -/
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

end Kolmogorov
