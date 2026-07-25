import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# M4: Greedy Cover Lemma

This file provides the purely combinatorial greedy covering lemma: if every
element of a finite set `T` is covered by at least `m` of the sets in a finite
family `S` (where `M := |S|`), then greedy selection covers `T` with at most
`(M / m) * (log₂ |T| + 1)` sets, i.e. `|C| · m ≤ M · (log₂ |T| + 1)`.

Proof strategy (constant-exact): group greedy picks into batches of
`q := ⌊M/m⌋`.  A single greedy pick removes a `≥ m/M`-fraction of the uncovered
set (`pick_step`, by double counting), so after a batch of `q` picks the
uncovered set at least *halves* — because `2·(M-m)^q ≤ M^q` (`halving_pow`, whose
core `2·q^q ≤ (q+1)^q` is Bernoulli, `two_mul_pow_le_succ_pow`).  Hence
`⌊log₂|T|⌋ + 1` batches suffice to cover everything, giving
`|C| ≤ q·(⌊log₂|T|⌋+1)` and `|C|·m ≤ (q·m)·(…) ≤ M·(…)` since `q·m ≤ M`.
-/

namespace Kolmogorov

open Finset

/-- `2 · q^q ≤ (q+1)^q` for `q ≥ 1` (Bernoulli's inequality `(1+1/q)^q ≥ 2`). -/
theorem two_mul_pow_le_succ_pow (q : ℕ) (hq : 1 ≤ q) : 2 * q ^ q ≤ (q + 1) ^ q := by
  have hqpos : (0:ℚ) < (q:ℚ) := by exact_mod_cast hq
  have hqne : (q:ℚ) ≠ 0 := ne_of_gt hqpos
  have hb : (2:ℚ) ≤ (1 + 1/(q:ℚ)) ^ q := by
    have hstep := one_add_mul_le_pow (a := (1:ℚ)/(q:ℚ))
      (by have : (0:ℚ) ≤ 1/(q:ℚ) := by positivity
          linarith) q
    have he : (1:ℚ) + (q:ℚ) * (1/(q:ℚ)) = 2 := by
      rw [mul_one_div, div_self hqne]; norm_num
    rwa [he] at hstep
  have hqq : (0:ℚ) ≤ (q:ℚ)^q := (pow_pos hqpos q).le
  have hh : (2:ℚ) * (q:ℚ)^q ≤ (1 + 1/(q:ℚ))^q * (q:ℚ)^q :=
    mul_le_mul_of_nonneg_right hb hqq
  have h3 : ((1:ℚ) + 1/(q:ℚ)) * (q:ℚ) = (q:ℚ) + 1 := by field_simp
  have hpow : (2:ℚ) * (q:ℚ)^q ≤ ((q:ℚ)+1)^q := by rw [← mul_pow, h3] at hh; exact hh
  exact_mod_cast hpow

/-- Batch-halving power inequality: with `q = ⌊M/m⌋` and `1 ≤ m ≤ M`,
`2·(M-m)^q ≤ M^q`.  Combined with the per-step `×(M-m)/M` decrease, one batch of
`q` greedy picks halves the uncovered set. -/
theorem halving_pow (M m : ℕ) (hm : 1 ≤ m) (hmM : m ≤ M) :
    2 * (M - m) ^ (M / m) ≤ M ^ (M / m) := by
  set q := M / m with hqdef
  have hq1 : 1 ≤ q := (Nat.one_le_div_iff (by omega)).mpr hmM
  have hdle : M - m ≤ q * m := by
    have h1 : q * m + M % m = M := by rw [hqdef]; exact Nat.div_add_mod' M m
    have h2 : M % m < m := Nat.mod_lt M (by omega)
    omega
  have hstep : (q + 1) * (M - m) ≤ q * M := by
    have hcancel : (M - m) + m = M := Nat.sub_add_cancel hmM
    calc (q + 1) * (M - m) = q * (M - m) + (M - m) := by ring
      _ ≤ q * (M - m) + q * m := Nat.add_le_add_left hdle _
      _ = q * ((M - m) + m) := by rw [Nat.mul_add]
      _ = q * M := by rw [hcancel]
  have hpow : (q + 1) ^ q * (M - m) ^ q ≤ q ^ q * M ^ q := by
    have := Nat.pow_le_pow_left hstep q
    rwa [mul_pow, mul_pow] at this
  have htwo : 2 * q ^ q ≤ (q + 1) ^ q := two_mul_pow_le_succ_pow q hq1
  have hfin : (q + 1) ^ q * (2 * (M - m) ^ q) ≤ (q + 1) ^ q * M ^ q := by
    calc (q + 1) ^ q * (2 * (M - m) ^ q)
        = 2 * ((q + 1) ^ q * (M - m) ^ q) := by ring
      _ ≤ 2 * (q ^ q * M ^ q) := Nat.mul_le_mul_left 2 hpow
      _ = (2 * q ^ q) * M ^ q := by ring
      _ ≤ (q + 1) ^ q * M ^ q := Nat.mul_le_mul_right (M ^ q) htwo
  exact Nat.le_of_mul_le_mul_left hfin (pow_pos (show 0 < q + 1 by omega) q)

/-- A single greedy pick.  If every element of `R ⊆ T` is covered by `≥ m` of the
`M := |S|` sets, some set `A ∈ S` covers a `≥ m/M`-fraction of `R`, so removing it
shrinks `R` by that factor: `M·|R \ A| ≤ (M-m)·|R|`.  (Averaging via double
counting: `∑_{A∈S} |A ∩ R| = ∑_{x∈R} |{A∈S : x∈A}| ≥ m·|R|`, then max ≥ average.) -/
theorem pick_step {α : Type*} [DecidableEq α] (T : Finset α)
    (S : Finset (Finset α)) (m : ℕ) (hm_pos : 0 < m)
    (hm : ∀ x ∈ T, m ≤ (S.filter (fun A => x ∈ A)).card)
    (R : Finset α) (hRT : R ⊆ T) (hR : R.Nonempty) :
    ∃ A ∈ S, S.card * (R \ A).card ≤ (S.card - m) * R.card := by
  classical
  obtain ⟨x0, hx0R⟩ := hR
  have hx0T : x0 ∈ T := hRT hx0R
  have hSne : S.Nonempty := by
    have h := hm x0 hx0T
    have hne : (S.filter (fun A => x0 ∈ A)).Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨A, hA⟩ := hne
    exact ⟨A, (Finset.mem_filter.mp hA).1⟩
  have hdc : ∑ A ∈ S, (A ∩ R).card = ∑ x ∈ R, (S.filter (fun A => x ∈ A)).card := by
    have e1 : ∀ A ∈ S, (A ∩ R).card = ∑ x ∈ R, (if x ∈ A then 1 else 0) := by
      intro A _; rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    have e2 : ∀ x ∈ R, (S.filter (fun A => x ∈ A)).card = ∑ A ∈ S, (if x ∈ A then 1 else 0) := by
      intro x _; rw [Finset.card_filter]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]
  have hlb : m * R.card ≤ ∑ x ∈ R, (S.filter (fun A => x ∈ A)).card := by
    have := Finset.card_nsmul_le_sum R (fun x => (S.filter (fun A => x ∈ A)).card) m
      (fun x hx => hm x (hRT hx))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  obtain ⟨Astar, hAstarS, hmax⟩ := Finset.exists_max_image S (fun A => (A ∩ R).card) hSne
  have hub : ∑ A ∈ S, (A ∩ R).card ≤ S.card * (Astar ∩ R).card := by
    calc ∑ A ∈ S, (A ∩ R).card ≤ ∑ _A ∈ S, (Astar ∩ R).card :=
          Finset.sum_le_sum (fun A hA => hmax A hA)
      _ = S.card * (Astar ∩ R).card := by rw [Finset.sum_const, smul_eq_mul]
  have hkey : m * R.card ≤ S.card * (Astar ∩ R).card :=
    le_trans hlb (le_of_eq hdc.symm |>.trans hub)
  refine ⟨Astar, hAstarS, ?_⟩
  set M := S.card
  have hmM : m ≤ M := le_trans (hm x0 hx0T) (Finset.card_filter_le S _)
  have E1 : M * (R \ Astar).card + M * (R ∩ Astar).card = M * R.card := by
    rw [← Nat.mul_add, Finset.card_sdiff_add_card_inter]
  have E2 : (M - m) * R.card + m * R.card = M * R.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hmM]
  have Hcomm : (Astar ∩ R).card = (R ∩ Astar).card := by rw [Finset.inter_comm]
  have H : m * R.card ≤ M * (R ∩ Astar).card := by rw [← Hcomm]; exact hkey
  omega

/-- Greedy cover lemma: pure finite combinatorics.  If every element of `T` is
covered by at least `m` of the sets in `S`, then some subfamily `C ⊆ S` covers
`T` with `|C| · m ≤ |S| · (log₂ |T| + 1)`. -/
theorem greedy_cover {α : Type*} [DecidableEq α] (T : Finset α)
    (S : Finset (Finset α)) (m : ℕ)
    (hm_pos : 0 < m)
    (hm : ∀ x ∈ T, m ≤ (S.filter (fun A => x ∈ A)).card) :
    ∃ C ⊆ S, T ⊆ C.biUnion id ∧
      C.card * m ≤ S.card * (Nat.log2 T.card + 1) := by
  classical
  set M := S.card with hMdef
  set q := M / m with hqdef
  have hqm : q * m ≤ M := Nat.div_mul_le_self M m
  -- `iter p`: after `p` greedy picks, the uncovered part shrinks by `((M-m)/M)^p`.
  have iter : ∀ (p : ℕ) (R : Finset α), R ⊆ T →
      ∃ C ⊆ S, C.card ≤ p ∧ M ^ p * (R \ C.biUnion id).card ≤ (M - m) ^ p * R.card := by
    intro p
    induction p with
    | zero =>
        intro R hRT
        exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    | succ p ih =>
        intro R hRT
        obtain ⟨C, hCS, hCcard, hCbound⟩ := ih R hRT
        by_cases hRc : (R \ C.biUnion id).Nonempty
        · have hRcT : (R \ C.biUnion id) ⊆ T := (Finset.sdiff_subset).trans hRT
          obtain ⟨A, hAS, hAbound⟩ := pick_step T S m hm_pos hm _ hRcT hRc
          refine ⟨insert A C, Finset.insert_subset hAS hCS,
            (Finset.card_insert_le _ _).trans (by omega), ?_⟩
          have hsdiff : R \ (insert A C).biUnion id = (R \ C.biUnion id) \ A := by
            ext y
            simp only [Finset.mem_sdiff, Finset.biUnion_insert, id_eq, Finset.mem_union]
            tauto
          rw [hsdiff]
          calc M ^ (p + 1) * ((R \ C.biUnion id) \ A).card
              = M ^ p * (M * ((R \ C.biUnion id) \ A).card) := by rw [pow_succ]; ring
            _ ≤ M ^ p * ((M - m) * (R \ C.biUnion id).card) := by
                  have hA' : M * ((R \ C.biUnion id) \ A).card
                      ≤ (M - m) * (R \ C.biUnion id).card := by simpa [hMdef] using hAbound
                  exact Nat.mul_le_mul_left _ hA'
            _ = (M - m) * (M ^ p * (R \ C.biUnion id).card) := by ring
            _ ≤ (M - m) * ((M - m) ^ p * R.card) := Nat.mul_le_mul_left _ hCbound
            _ = (M - m) ^ (p + 1) * R.card := by rw [pow_succ]; ring
        · rw [Finset.not_nonempty_iff_eq_empty] at hRc
          refine ⟨C, hCS, by omega, ?_⟩
          rw [hRc]
          simp
  -- `halve`: one batch of `q` picks at least halves the uncovered part.
  have halve : ∀ (R : Finset α), R ⊆ T → m ≤ M →
      ∃ C ⊆ S, C.card ≤ q ∧ 2 * (R \ C.biUnion id).card ≤ R.card := by
    intro R hRT hmM
    obtain ⟨C, hCS, hCcard, hbound⟩ := iter q R hRT
    refine ⟨C, hCS, hCcard, ?_⟩
    have hhp : 2 * (M - m) ^ q ≤ M ^ q := by rw [hqdef]; exact halving_pow M m hm_pos hmM
    have step : M ^ q * (2 * (R \ C.biUnion id).card) ≤ M ^ q * R.card := by
      calc M ^ q * (2 * (R \ C.biUnion id).card)
          = 2 * (M ^ q * (R \ C.biUnion id).card) := by ring
        _ ≤ 2 * ((M - m) ^ q * R.card) := Nat.mul_le_mul_left 2 hbound
        _ = (2 * (M - m) ^ q) * R.card := by ring
        _ ≤ M ^ q * R.card := Nat.mul_le_mul_right R.card hhp
    exact Nat.le_of_mul_le_mul_left step (pow_pos (show 0 < M by omega) q)
  -- `main`: `d` halving batches cover any `R` with `|R| < 2^d`, using `≤ q·d` sets.
  have main : ∀ (d : ℕ) (R : Finset α), R ⊆ T → R.card < 2 ^ d →
      ∃ C ⊆ S, R ⊆ C.biUnion id ∧ C.card ≤ q * d := by
    intro d
    induction d with
    | zero =>
        intro R hRT hR0
        have hRempty : R = ∅ := by rw [← Finset.card_eq_zero]; omega
        exact ⟨∅, Finset.empty_subset _, by rw [hRempty]; exact Finset.empty_subset _, by simp⟩
    | succ d ih =>
        intro R hRT hRcard
        by_cases hR : R.Nonempty
        · obtain ⟨x, hx⟩ := hR
          have hmM : m ≤ M := le_trans (hm x (hRT hx)) (Finset.card_filter_le S _)
          obtain ⟨C1, hC1S, hC1card, hhalf⟩ := halve R hRT hmM
          have hRccard : (R \ C1.biUnion id).card < 2 ^ d := by
            have hlt : 2 * (R \ C1.biUnion id).card < 2 * 2 ^ d := by
              calc 2 * (R \ C1.biUnion id).card ≤ R.card := hhalf
                _ < 2 ^ (d + 1) := hRcard
                _ = 2 * 2 ^ d := by rw [pow_succ]; ring
            omega
          have hRcT : (R \ C1.biUnion id) ⊆ T := (Finset.sdiff_subset).trans hRT
          obtain ⟨C2, hC2S, hC2cov, hC2card⟩ := ih (R \ C1.biUnion id) hRcT hRccard
          refine ⟨C1 ∪ C2, Finset.union_subset hC1S hC2S, ?_, ?_⟩
          · intro y hy
            by_cases hyc : y ∈ C1.biUnion id
            · have hsub : C1.biUnion id ⊆ (C1 ∪ C2).biUnion id :=
                Finset.biUnion_subset_biUnion_of_subset_left id Finset.subset_union_left
              exact hsub hyc
            · have hyRc : y ∈ R \ C1.biUnion id := Finset.mem_sdiff.mpr ⟨hy, hyc⟩
              have hsub : C2.biUnion id ⊆ (C1 ∪ C2).biUnion id :=
                Finset.biUnion_subset_biUnion_of_subset_left id Finset.subset_union_right
              exact hsub (hC2cov hyRc)
          · calc (C1 ∪ C2).card ≤ C1.card + C2.card := Finset.card_union_le _ _
              _ ≤ q + q * d := Nat.add_le_add hC1card hC2card
              _ = q * (d + 1) := by rw [Nat.mul_succ]; ring
        · rw [Finset.not_nonempty_iff_eq_empty] at hR
          exact ⟨∅, Finset.empty_subset _, by rw [hR]; exact Finset.empty_subset _, by simp⟩
  -- Final assembly: `d := ⌊log₂|T|⌋ + 1` batches suffice, and `q·m ≤ M`.
  have hlog : T.card < 2 ^ (Nat.log2 T.card + 1) := by
    rw [Nat.log2_eq_log_two]; exact Nat.lt_pow_succ_log_self (by norm_num) T.card
  obtain ⟨C, hCS, hCcov, hCcard⟩ := main (Nat.log2 T.card + 1) T (Finset.Subset.refl T) hlog
  refine ⟨C, hCS, hCcov, ?_⟩
  calc C.card * m ≤ (q * (Nat.log2 T.card + 1)) * m := Nat.mul_le_mul_right m hCcard
    _ = (q * m) * (Nat.log2 T.card + 1) := by ring
    _ ≤ M * (Nat.log2 T.card + 1) := Nat.mul_le_mul_right _ hqm

/-- Indexed version of `pick_step`.  The indexing type is important when
different indices determine extensionally equal cover-sets: multiplicity is
counted in the index set `S`, not after quotienting by equality of subsets. -/
theorem pick_step_indexed {α β : Type*} [DecidableEq α]
    (T : Finset α) (S : Finset β) (cover : β → Finset α) (m : ℕ)
    (hm_pos : 0 < m)
    (hm : ∀ x ∈ T, m ≤ (S.filter (fun b => x ∈ cover b)).card)
    (R : Finset α) (hRT : R ⊆ T) (hR : R.Nonempty) :
    ∃ b ∈ S, S.card * (R \ cover b).card ≤ (S.card - m) * R.card := by
  classical
  obtain ⟨x0, hx0R⟩ := hR
  have hx0T : x0 ∈ T := hRT hx0R
  have hSne : S.Nonempty := by
    have h := hm x0 hx0T
    have hne : (S.filter (fun b => x0 ∈ cover b)).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨b, hb⟩ := hne
    exact ⟨b, (Finset.mem_filter.mp hb).1⟩
  have hdc : ∑ b ∈ S, ((cover b) ∩ R).card =
      ∑ x ∈ R, (S.filter (fun b => x ∈ cover b)).card := by
    have e1 : ∀ b ∈ S, ((cover b) ∩ R).card =
        ∑ x ∈ R, (if x ∈ cover b then 1 else 0) := by
      intro b _
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    have e2 : ∀ x ∈ R, (S.filter (fun b => x ∈ cover b)).card =
        ∑ b ∈ S, (if x ∈ cover b then 1 else 0) := by
      intro x _
      rw [Finset.card_filter]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]
  have hlb : m * R.card ≤ ∑ x ∈ R, (S.filter (fun b => x ∈ cover b)).card := by
    have := Finset.card_nsmul_le_sum R
      (fun x => (S.filter (fun b => x ∈ cover b)).card) m
      (fun x hx => hm x (hRT hx))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  obtain ⟨bstar, hbstarS, hmax⟩ :=
    Finset.exists_max_image S (fun b => ((cover b) ∩ R).card) hSne
  have hub : ∑ b ∈ S, ((cover b) ∩ R).card ≤ S.card * ((cover bstar) ∩ R).card := by
    calc ∑ b ∈ S, ((cover b) ∩ R).card ≤ ∑ _b ∈ S, ((cover bstar) ∩ R).card :=
          Finset.sum_le_sum (fun b hb => hmax b hb)
      _ = S.card * ((cover bstar) ∩ R).card := by rw [Finset.sum_const, smul_eq_mul]
  have hkey : m * R.card ≤ S.card * ((cover bstar) ∩ R).card :=
    le_trans hlb (le_of_eq hdc.symm |>.trans hub)
  refine ⟨bstar, hbstarS, ?_⟩
  set M := S.card
  have hmM : m ≤ M := le_trans (hm x0 hx0T) (Finset.card_filter_le S _)
  have E1 : M * (R \ cover bstar).card + M * (R ∩ cover bstar).card = M * R.card := by
    rw [← Nat.mul_add, Finset.card_sdiff_add_card_inter]
  have E2 : (M - m) * R.card + m * R.card = M * R.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hmM]
  have Hcomm : ((cover bstar) ∩ R).card = (R ∩ cover bstar).card := by rw [Finset.inter_comm]
  have H : m * R.card ≤ M * (R ∩ cover bstar).card := by
    rw [← Hcomm]
    exact hkey
  omega

/-- Indexed greedy cover lemma.  If every element of `T` is covered by at least
`m` indices from a finite index set `S`, then a subfamily of indices covers `T`
with the same logarithmic bound as `greedy_cover`. -/
theorem greedy_cover_indexed {α β : Type*} [DecidableEq α]
    (T : Finset α) (S : Finset β) (cover : β → Finset α) (m : ℕ)
    (hm_pos : 0 < m)
    (hm : ∀ x ∈ T, m ≤ (S.filter (fun b => x ∈ cover b)).card) :
    ∃ C ⊆ S, T ⊆ C.biUnion cover ∧
      C.card * m ≤ S.card * (Nat.log2 T.card + 1) := by
  classical
  set M := S.card with hMdef
  set q := M / m with hqdef
  have hqm : q * m ≤ M := Nat.div_mul_le_self M m
  have iter : ∀ (p : ℕ) (R : Finset α), R ⊆ T →
      ∃ C ⊆ S, C.card ≤ p ∧ M ^ p * (R \ C.biUnion cover).card ≤
        (M - m) ^ p * R.card := by
    intro p
    induction p with
    | zero =>
        intro R hRT
        exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    | succ p ih =>
        intro R hRT
        obtain ⟨C, hCS, hCcard, hCbound⟩ := ih R hRT
        by_cases hRc : (R \ C.biUnion cover).Nonempty
        · have hRcT : (R \ C.biUnion cover) ⊆ T := (Finset.sdiff_subset).trans hRT
          obtain ⟨b, hbS, hbbound⟩ :=
            pick_step_indexed T S cover m hm_pos hm _ hRcT hRc
          refine ⟨insert b C, Finset.insert_subset hbS hCS,
            (Finset.card_insert_le _ _).trans (by omega), ?_⟩
          have hsdiff : R \ (insert b C).biUnion cover =
              (R \ C.biUnion cover) \ cover b := by
            ext y
            simp only [Finset.mem_sdiff, Finset.biUnion_insert, Finset.mem_union]
            tauto
          rw [hsdiff]
          calc M ^ (p + 1) * ((R \ C.biUnion cover) \ cover b).card
              = M ^ p * (M * ((R \ C.biUnion cover) \ cover b).card) := by rw [pow_succ]; ring
            _ ≤ M ^ p * ((M - m) * (R \ C.biUnion cover).card) := by
                  have hb' : M * ((R \ C.biUnion cover) \ cover b).card
                      ≤ (M - m) * (R \ C.biUnion cover).card := by
                    simpa [hMdef] using hbbound
                  exact Nat.mul_le_mul_left _ hb'
            _ = (M - m) * (M ^ p * (R \ C.biUnion cover).card) := by ring
            _ ≤ (M - m) * ((M - m) ^ p * R.card) := Nat.mul_le_mul_left _ hCbound
            _ = (M - m) ^ (p + 1) * R.card := by rw [pow_succ]; ring
        · rw [Finset.not_nonempty_iff_eq_empty] at hRc
          refine ⟨C, hCS, by omega, ?_⟩
          rw [hRc]
          simp
  have halve : ∀ (R : Finset α), R ⊆ T → m ≤ M →
      ∃ C ⊆ S, C.card ≤ q ∧ 2 * (R \ C.biUnion cover).card ≤ R.card := by
    intro R hRT hmM
    obtain ⟨C, hCS, hCcard, hbound⟩ := iter q R hRT
    refine ⟨C, hCS, hCcard, ?_⟩
    have hhp : 2 * (M - m) ^ q ≤ M ^ q := by
      rw [hqdef]
      exact halving_pow M m hm_pos hmM
    have step : M ^ q * (2 * (R \ C.biUnion cover).card) ≤ M ^ q * R.card := by
      calc M ^ q * (2 * (R \ C.biUnion cover).card)
          = 2 * (M ^ q * (R \ C.biUnion cover).card) := by ring
        _ ≤ 2 * ((M - m) ^ q * R.card) := Nat.mul_le_mul_left 2 hbound
        _ = (2 * (M - m) ^ q) * R.card := by ring
        _ ≤ M ^ q * R.card := Nat.mul_le_mul_right R.card hhp
    exact Nat.le_of_mul_le_mul_left step (pow_pos (show 0 < M by omega) q)
  have main : ∀ (d : ℕ) (R : Finset α), R ⊆ T → R.card < 2 ^ d →
      ∃ C ⊆ S, R ⊆ C.biUnion cover ∧ C.card ≤ q * d := by
    intro d
    induction d with
    | zero =>
        intro R hRT hR0
        have hRempty : R = ∅ := by rw [← Finset.card_eq_zero]; omega
        exact ⟨∅, Finset.empty_subset _, by rw [hRempty]; exact Finset.empty_subset _, by simp⟩
    | succ d ih =>
        intro R hRT hRcard
        by_cases hR : R.Nonempty
        · obtain ⟨x, hx⟩ := hR
          have hmM : m ≤ M := le_trans (hm x (hRT hx)) (Finset.card_filter_le S _)
          obtain ⟨C1, hC1S, hC1card, hhalf⟩ := halve R hRT hmM
          have hRccard : (R \ C1.biUnion cover).card < 2 ^ d := by
            have hlt : 2 * (R \ C1.biUnion cover).card < 2 * 2 ^ d := by
              calc 2 * (R \ C1.biUnion cover).card ≤ R.card := hhalf
                _ < 2 ^ (d + 1) := hRcard
                _ = 2 * 2 ^ d := by rw [pow_succ]; ring
            omega
          have hRcT : (R \ C1.biUnion cover) ⊆ T := (Finset.sdiff_subset).trans hRT
          obtain ⟨C2, hC2S, hC2cov, hC2card⟩ := ih (R \ C1.biUnion cover) hRcT hRccard
          refine ⟨C1 ∪ C2, Finset.union_subset hC1S hC2S, ?_, ?_⟩
          · intro y hy
            by_cases hyc : y ∈ C1.biUnion cover
            · have hsub : C1.biUnion cover ⊆ (C1 ∪ C2).biUnion cover :=
                Finset.biUnion_subset_biUnion_of_subset_left cover Finset.subset_union_left
              exact hsub hyc
            · have hyRc : y ∈ R \ C1.biUnion cover := Finset.mem_sdiff.mpr ⟨hy, hyc⟩
              have hsub : C2.biUnion cover ⊆ (C1 ∪ C2).biUnion cover :=
                Finset.biUnion_subset_biUnion_of_subset_left cover Finset.subset_union_right
              exact hsub (hC2cov hyRc)
          · calc (C1 ∪ C2).card ≤ C1.card + C2.card := Finset.card_union_le _ _
              _ ≤ q + q * d := Nat.add_le_add hC1card hC2card
              _ = q * (d + 1) := by rw [Nat.mul_succ]; ring
        · rw [Finset.not_nonempty_iff_eq_empty] at hR
          exact ⟨∅, Finset.empty_subset _, by rw [hR]; exact Finset.empty_subset _, by simp⟩
  have hlog : T.card < 2 ^ (Nat.log2 T.card + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by norm_num) T.card
  obtain ⟨C, hCS, hCcov, hCcard⟩ :=
    main (Nat.log2 T.card + 1) T (Finset.Subset.refl T) hlog
  refine ⟨C, hCS, hCcov, ?_⟩
  calc C.card * m ≤ (q * (Nat.log2 T.card + 1)) * m := Nat.mul_le_mul_right m hCcard
    _ = (q * m) * (Nat.log2 T.card + 1) := by ring
    _ ≤ M * (Nat.log2 T.card + 1) := Nat.mul_le_mul_right _ hqm

end Kolmogorov
