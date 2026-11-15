/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.LibraryAPI
import KolmogorovMathlib.Complexity.InfiniteSequences.PrefixComplexity
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubsequences
import KolmogorovMathlib.Complexity.ConditionalComplexity.AverageBounds.Expectation
import KolmogorovMathlib.CommonInformation.ConditionalIndependence.Part01
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.Computability
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.CommonInformation.ChainNonextractabilityEngine
import KolmogorovMathlib.Complexity.KolmogorovLevin.ShortDescriptions

/-!
# Set Pair Complexity

The complexity `C(F, ω(F) | t)` of the pair formed by a finite set `F` of positions and the
restriction of an infinite binary sequence `ω` to `F`, given a number `t`.  The main declarations
are `finsetCode`, the code of a finite set of positions, and `setPairComplexity`, the conditional
complexity of the pair (set, restricted bits).  The main results, proved by a counting argument,
are that for every `α ∈ (0, 1)` there is a sequence `ω` such that every large enough finite set
`F` has a position `t ∈ F` with `C(F, ω(F) | t) ≥ α|F|` (`exists_max_setPairComplexity_ge`,
Theorem 162 of the book by Shen, Uspensky and Vereshchagin), together with consequences for
the complexity of `ω(F)` given `F` (`exists_condK_restrictBits_ge`,
`condK_restrictBits_ge_of_forall_le`).
-/

namespace Kolmogorov.Applications

open MeasureTheory

/-- The code of a finite set of positions: the list of its elements, in increasing order. -/
def finsetCode (F : Finset ℕ) : BitString := listCode ((F.sort (· ≤ ·)).map natBits)

/-- The complexity `C(F, ω(F) | t)`. -/
noncomputable def setPairComplexity (V : Map) (w : CantorSeq) (F : Finset ℕ) (t : ℕ) : ℝ :=
  ((condK V (pairCode (finsetCode F) (restrictBits w F)) (natBits t)).toNat : ℝ)


private def badRestrictions (V : Map) (α : ℝ) : Set Restriction :=
  { r | ∀ t ∈ r.indices, ((condK V (pairCode (finsetCode r.indices) r.values) (natBits t)).toNat :
      ℝ) < α * r.size }

private lemma restriction_inj : Function.Injective (fun r : Restriction =>
  pairCode (finsetCode r.indices) r.values) := by
  intro r1 r2 h
  have h_pair := pairCode_injective (a₁ := (finsetCode r1.indices, r1.values))
      (a₂ := (finsetCode r2.indices, r2.values)) h
  have h1 : finsetCode r1.indices = finsetCode r2.indices := congr_arg Prod.fst h_pair
  have h2 : r1.values = r2.values := congr_arg Prod.snd h_pair
  have h3 : r1.indices = r2.indices := by
    dsimp [finsetCode] at h1
    have h_list := listCode_injective h1
    have h_map : (r1.indices.sort (· ≤ ·)) = (r2.indices.sort (· ≤ ·)) := by
      have h_map_inj : Function.Injective (List.map natBits) := by
        intro l1 l2 h
        exact List.map_injective_iff.mpr natBits_injective h
      exact h_map_inj h_list
    have h_finset : (r1.indices.sort (· ≤ ·)).toFinset = (r2.indices.sort (· ≤ ·)).toFinset := by
      rw [h_map]
    rw [Finset.sort_toFinset, Finset.sort_toFinset] at h_finset
    exact h_finset
  rcases r1 with ⟨i1, v1, l1⟩
  rcases r2 with ⟨i2, v2, l2⟩
  dsimp at h2 h3
  subst h2 h3
  rfl

/-- Step 1 of the proof of exists_max_setPairComplexity_ge: the large bad restrictions are
bounded with a larger exponent. -/
private lemma exists_max_setPairComplexity_ge_boundedRestrictions
    (V : Map) (hV : isOptimalConditional V) {α α' : ℝ} (hα0 : 0 < α) (hαα' : α < α') (hα'1 : α' < 1)
        :
    ∃ N0 : ℕ, IsBoundedRestrictions α' {r ∈ badRestrictions V α | N0 ≤ r.size} := by
  use ⌈1 / (α' - α)⌉₊
  dsimp [IsBoundedRestrictions]
  intro i n hn
  let R := {r ∈ badRestrictions V α | ⌈1 / (α' - α)⌉₊ ≤ r.size}
  have h_cases : n < ⌈1 / (α' - α)⌉₊ ∨ ⌈1 / (α' - α)⌉₊ ≤ n := by omega
  rcases h_cases with h_lt | h_ge
  · have hS_emp : {r | (r ∈ badRestrictions V α ∧ ⌈1 / (α' - α)⌉₊ ≤ r.size) ∧ r.size = n ∧ i ∈
      r.indices} = ∅ := by
      ext r
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hr
      have hr2 : r.size = n := hr.2.1
      have hr3 : ⌈1 / (α' - α)⌉₊ ≤ r.size := hr.1.2
      linarith
    rw [hS_emp]
    exact ⟨Set.finite_empty, by simp only [Set.ncard_empty, Nat.cast_zero]; positivity⟩
  · let m := ⌊α * n⌋₊
    let S := {r | (r ∈ badRestrictions V α ∧ ⌈1 / (α' - α)⌉₊ ≤ r.size) ∧ r.size = n ∧ i ∈ r.indices}
    let ι : Restriction → BitString := fun r => pairCode (finsetCode r.indices) r.values
    have h_inj : Function.Injective ι := restriction_inj
    have h_injS : Set.InjOn ι S := h_inj.injOn
    let T := {x : BitString | (condK V x (natBits i)).toNat ≤ m}
    have h_map : Set.MapsTo ι S T := by
      intro r hr
      have hr_bad : ∀ t ∈ r.indices, ((condK V (pairCode (finsetCode r.indices) r.values)
          (natBits t)).toNat : ℝ) < α * r.size := hr.1.1
      have hi_in : i ∈ r.indices := hr.2.2
      have h_eval := hr_bad i hi_in
      have h_size : r.size = n := hr.2.1
      rw [h_size] at h_eval
      dsimp [ι, T, Set.MapsTo]
      apply Nat.le_floor
      exact le_of_lt h_eval
    have hT_fin : T.Finite := by
      by_contra h_inf
      have h_inf' : T.Infinite := h_inf
      obtain ⟨A, hA_sub, hA_card⟩ := h_inf'.exists_subset_card_eq (2 ^ (m + 1))
      have h_bound : A.card < 2 ^ (m + 1) := by
        apply card_lt_of_condK_le V (natBits i) m A
        intro x hx
        have hx' := hA_sub hx
        dsimp [T] at hx'
        have h_cond_ne_top : condK V x (natBits i) ≠ ⊤ := avgCond_condK_ne_top V hV x (natBits i)
        have h_eq : ((condK V x (natBits i)).toNat : ENat) = condK V x (natBits i) :=
            ENat.natCast_toNat h_cond_ne_top
        rw [← h_eq]
        exact ENat.natCast_le_natCast.mpr hx'
      omega
    have hS_fin : S.Finite := Set.Finite.of_injOn h_map h_injS hT_fin
    have hS_card : S.ncard ≤ T.ncard := Set.ncard_le_ncard_of_injOn ι h_map h_injS hT_fin
    have hT_card : T.ncard < 2 ^ (m + 1) := by
      have h_eq : T.ncard = hT_fin.toFinset.card := Set.ncard_eq_toFinset_card T hT_fin
      rw [h_eq]
      apply card_lt_of_condK_le V (natBits i) m
      intro x hx
      rw [Set.Finite.mem_toFinset] at hx
      have hx' := hx
      dsimp [T] at hx'
      have h_cond_ne_top : condK V x (natBits i) ≠ ⊤ := avgCond_condK_ne_top V hV x (natBits i)
      have h_eq' : ((condK V x (natBits i)).toNat : ENat) = condK V x (natBits i) :=
          ENat.natCast_toNat h_cond_ne_top
      rw [← h_eq']
      exact ENat.natCast_le_natCast.mpr hx'
    have hm_le : (m : ℝ) ≤ α * n := Nat.floor_le (mul_nonneg (le_of_lt hα0) (by positivity))
    have hm_add : (m + 1 : ℝ) ≤ α * n + 1 := by linarith
    have h_n_ge : (⌈1 / (α' - α)⌉₊ : ℝ) ≤ n := by exact_mod_cast h_ge
    have h_ceil : 1 / (α' - α) ≤ (⌈1 / (α' - α)⌉₊ : ℝ) := Nat.le_ceil (1 / (α' - α))
    have h_n_bound : 1 / (α' - α) ≤ n := by linarith
    have h_n_bound' : 1 ≤ (α' - α) * n := by
      have h_pos : 0 < α' - α := sub_pos.mpr hαα'
      have h_mul := (div_le_iff₀ h_pos).mp h_n_bound
      linarith
    have h_m_bound : (m + 1 : ℝ) ≤ α' * n := by
      have h1 : α * n + 1 ≤ α * n + (α' - α) * n := by linarith
      have h2 : α * n + (α' - α) * n = α' * n := by ring
      linarith
    have hS_card_le : (S.ncard : ℝ) ≤ 2 ^ (α' * n) := by
      have h1 : (S.ncard : ℝ) ≤ (T.ncard : ℝ) := Nat.cast_le.mpr hS_card
      have h2 : (T.ncard : ℝ) < ((2 ^ (m + 1) : ℕ) : ℝ) := Nat.cast_lt.mpr hT_card
      have h3 : ((2 ^ (m + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (m + 1 : ℝ) := by
        have hh1 : ((2 ^ (m + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (m + 1 : ℕ) := by norm_cast
        have hh2 : (2 : ℝ) ^ (m + 1 : ℕ) = (2 : ℝ) ^ (m + 1 : ℝ) := by
          exact_mod_cast Real.rpow_natCast 2 (m + 1)
        rw [hh1, hh2]
      have h4 : (2 : ℝ) ^ (m + 1 : ℝ) ≤ (2 : ℝ) ^ (α' * n) := Real.rpow_le_rpow_of_exponent_le
          (by linarith) h_m_bound
      linarith
    exact ⟨hS_fin, hS_card_le⟩

/-- **SUV Theorem 162, p. 251.**  Let `α ∈ (0, 1)`.  There are a sequence `ω` and a constant `N`
with `max_{t ∈ F} C(F, ω(F) | t) ≥ α|F|` for every `F` with at least `N` elements. -/
theorem exists_max_setPairComplexity_ge (V : Map) (hV : isOptimalConditional V) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (w : CantorSeq) (N : ℕ), ∀ F : Finset ℕ, N ≤ F.card →
      ∃ t ∈ F, α * F.card ≤ setPairComplexity V w F t := by
  set α' := (α + 1) / 2
  have hα0' : 0 < α' := by
    dsimp [α']
    linarith
  have hαα' : α < α' := by
    dsimp [α']
    linarith
  have hα'1 : α' < 1 := by
    dsimp [α']
    linarith
  obtain ⟨N0, h_bound⟩ := exists_max_setPairComplexity_ge_boundedRestrictions V hV hα0 hαα' hα'1
  obtain ⟨N, w, hw⟩ := exists_not_forbidden hα0' hα'1 h_bound
  use w, max N N0 + 1
  intro F hF
  by_contra h_contra
  push Not at h_contra
  let r : Restriction :=
    { indices := F
      values := restrictBits w F
      length_eq := by dsimp [restrictBits]; rw [List.length_map, Finset.length_sort] }
  have h_in_R : r ∈ badRestrictions V α := by
    dsimp [badRestrictions]
    intro t ht
    have h1 := h_contra t ht
    have h2 : ((condK V (pairCode (finsetCode r.indices) r.values) (natBits t)).toNat : ℝ) =
        setPairComplexity V w F t := rfl
    have h3 : (r.size : ℝ) = F.card := by
      dsimp [Restriction.size]
      dsimp [r]
      dsimp [restrictBits]
      rw [List.length_map, Finset.length_sort]
    rwa [h2, h3]
  have h_size : N0 ≤ r.size := by
    dsimp [Restriction.size]
    dsimp [r]
    dsimp [restrictBits]
    rw [List.length_map, Finset.length_sort]
    have : N0 ≤ max N N0 := le_max_right N N0
    omega
  have h_in_R' : r ∈ {r ∈ badRestrictions V α | N0 ≤ r.size} := ⟨h_in_R, h_size⟩
  have h_forbids : r.Forbids w := by rfl
  have h_N_lt : N < r.size := by
    dsimp [Restriction.size]
    dsimp [r]
    dsimp [restrictBits]
    rw [List.length_map, Finset.length_sort]
    have : N ≤ max N N0 := le_max_left N N0
    omega
  have := hw r h_in_R' h_N_lt
  contradiction


private lemma exists_condK_restrictBits_ge_logSlack_bound (c : ℕ) :
    ∃ D : ℝ, ∀ b : ℕ, (logSlack c (b + 1) : ℝ) ≤ b / 2 + D := by
  obtain ⟨T, hT⟩ :=
    Kolmogorov.exists_size_linear_threshold (2 * c) (2 * c + 1)
  refine ⟨(logSlack c (T + 1) : ℝ), ?_⟩
  intro b
  by_cases hb : b < T
  · have hm : logSlack c (b + 1) ≤ logSlack c (T + 1) :=
      monotone_logSlack c (by omega)
    have hmR : (logSlack c (b + 1) : ℝ) ≤
        (logSlack c (T + 1) : ℝ) := by
      exact_mod_cast hm
    have hbR : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    linarith
  · have ht := hT (b + 1) (by omega)
    have hn : 2 * logSlack c (b + 1) ≤ b := by
      rw [logSlack, Nat.size_eq_bits_len]
      nlinarith [ht]
    have hnR : (2 : ℝ) * (logSlack c (b + 1) : ℝ) ≤
        (b : ℝ) := by
      exact_mod_cast hn
    have hD : (0 : ℝ) ≤ (logSlack c (T + 1) : ℝ) :=
      Nat.cast_nonneg _
    linarith

private lemma exists_condK_restrictBits_ge_b_bound (c C : ℕ) (α : ℝ) (D : ℝ) :
    ∀ n a b q : ℕ,
      (a : ℝ) < α * n / 2 →
      q ≤ n + C →
      (b : ℝ) ≤ a + q + logSlack c (b + 1) →
      (logSlack c (b + 1) : ℝ) ≤ b / 2 + D →
      (b : ℝ) ≤ (α + 2) * n + 2 * C + 2 * D := by
  intro n a b q ha hqn h_chain hD
  have h1 : (b : ℝ) ≤ (a : ℝ) + (q : ℝ) + ((b : ℝ) / 2 + D) := by linarith
  have h2 : (b : ℝ) / 2 ≤ (a : ℝ) + (q : ℝ) + D := by linarith
  have h3 : (b : ℝ) ≤ 2 * (a : ℝ) + 2 * (q : ℝ) + 2 * D := by linarith
  have h4 : 2 * (a : ℝ) < α * n := by linarith
  have h_qn_cast : (q : ℝ) ≤ (n : ℝ) + (C : ℝ) := by exact_mod_cast hqn
  have h5 : 2 * (q : ℝ) ≤ 2 * n + 2 * C := by linarith
  linarith

private lemma exists_condK_restrictBits_ge_eventual_bound (c C : ℕ) (α α' : ℝ)
    (D : ℝ) (hαα' : α < α') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (c : ℝ) * ((Nat.bits (⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1)).length) +
        c ≤ (α' - α) * n := by
  have hd : 0 < α' - α := by linarith
  have H (n : ℕ) : ((Nat.bits (⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1)).length : ℝ) ≤ Real.logb 2
      ((⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1 : ℕ) : ℝ) + 1 := by
    exact natBits_length_le_logb_add_one (⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1)
  
  have H_bound2 (n : ℕ) : ((⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1 : ℕ) : ℝ) ≤ (max (α + 2) 0) * n +
      (max (2 * C + 2 * D) 0 + 1) := by
    by_cases h0 : 0 ≤ (α + 2) * n + 2 * C + 2 * D
    · have h1 : (⌊(α + 2) * n + 2 * C + 2 * D⌋₊ : ℝ) ≤ (α + 2) * n + 2 * C + 2 * D :=
        Nat.floor_le h0
      have h2 : (α + 2) * n + 2 * C + 2 * D ≤ max (α + 2) 0 * n + max (2 * C + 2 * D) 0 := by
        have h3 : α + 2 ≤ max (α + 2) 0 := le_max_left _ _
        have h4 : 2 * (C : ℝ) + 2 * D ≤ max (2 * C + 2 * D) 0 := le_max_left _ _
        have h5 : (α + 2) * (n : ℝ) ≤ max (α + 2) 0 * n := by
          gcongr
        linarith
      push_cast
      linarith
    · push Not at h0
      have h1 : ⌊(α + 2) * n + 2 * C + 2 * D⌋₊ = 0 := Nat.floor_of_nonpos h0.le
      rw [h1]
      simp only [zero_add]
      have h3 : 0 ≤ max (α + 2) 0 := le_max_right _ _
      have h4 : 0 ≤ max (2 * C + 2 * D) 0 := le_max_right _ _
      have h5 : 0 ≤ max (α + 2) 0 * (n : ℝ) := mul_nonneg h3 (Nat.cast_nonneg n)
      push_cast
      linarith
  
  have H_bound3 (n : ℕ) : (c : ℝ) * ((Nat.bits (⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1)).length) + c ≤
      (c : ℝ) * (Real.logb 2 ((max (α + 2) 0) * n + (max (2 * C + 2 * D) 0 + 1)) + 1) + c := by
    have h1 := H n
    have h2 := H_bound2 n
    have h3 : Real.logb 2 ((⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1 : ℕ) : ℝ) ≤ Real.logb 2
        ((max (α + 2) 0) * (n : ℝ) + (max (2 * C + 2 * D) 0 + 1)) := by
      have h_log : Real.logb 2 ((⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1 : ℕ) : ℝ) = Real.log
          ((⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1 : ℕ) : ℝ) / Real.log 2 := rfl
      have h_log2 : Real.logb 2 ((max (α + 2) 0) * (n : ℝ) + (max (2 * C + 2 * D) 0 + 1)) = Real.log
          ((max (α + 2) 0) * (n : ℝ) + (max (2 * C + 2 * D) 0 + 1)) / Real.log 2 := rfl
      rw [h_log, h_log2]
      apply div_le_div_of_nonneg_right
      · apply Real.log_le_log
        · positivity
        · exact h2
      · positivity
    have h_c_nonneg : 0 ≤ (c : ℝ) := Nat.cast_nonneg c
    nlinarith
  
  have hA0 : 0 < max (α + 2) 0 + (max (2 * C + 2 * D) 0 + 1) := by
    have : 0 ≤ max (α + 2) 0 := le_max_right _ _
    linarith [le_max_right (2 * (C : ℝ) + 2 * D) 0]
  have H_rw : ∀ᶠ (n : ℝ) in Filter.atTop, Real.log ((max (α + 2) 0 + (max (2 * C + 2 * D) 0 + 1)) *
      n) = Real.log (max (α + 2) 0 + (max (2 * C + 2 * D) 0 + 1)) + Real.log n := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact Real.log_mul hA0.ne' hn.ne'
  have H_le : ∀ᶠ (n : ℝ) in Filter.atTop, Real.log (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1))
      ≤ Real.log ((max (α + 2) 0 + (max (2 * C + 2 * D) 0 + 1)) * n) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have h1 : 0 < max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1) := by
      have : 0 ≤ max (α + 2) 0 * n := mul_nonneg (le_max_right _ _) (by linarith)
      linarith [le_max_right (2 * (C : ℝ) + 2 * D) 0]
    apply Real.log_le_log
    · exact h1
    · have h2 : max (2 * C + 2 * D) 0 + 1 ≤ (max (2 * C + 2 * D) 0 + 1) * n := by
        have : 0 ≤ max (2 * (C : ℝ) + 2 * D) 0 + 1 := by
          linarith [le_max_right (2 * (C : ℝ) + 2 * D) 0]
        nlinarith
      linarith
  have H_O : (fun (n : ℝ) => Real.log (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1)))
      =O[Filter.atTop] Real.log := by
    have H : ∀ᶠ (n : ℝ) in Filter.atTop, ‖Real.log (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 +
        1))‖ ≤ 2 * ‖Real.log n‖ := by
      filter_upwards [H_le, H_rw, Filter.eventually_ge_atTop (max 1 (Real.exp (Real.log (max (α +
          2) 0 + (max (2 * C + 2 * D) 0 + 1)))))] with n h_le h_rw hn
      have hn1 : 1 ≤ n := le_trans (le_max_left 1 _) hn
      have hn2 : Real.exp (Real.log (max (α + 2) 0 + (max (2 * C + 2 * D) 0 + 1))) ≤ n :=
          le_trans (le_max_right _ _) hn
      have h_log_n_pos : 0 ≤ Real.log n := Real.log_nonneg hn1
      have H1 : Real.log (max (α + 2) 0 + (max (2 * C + 2 * D) 0 + 1)) ≤ Real.log n := by
        have hrw : Real.log (max (α + 2) 0 + (max (2 * C + 2 * D) 0 + 1)) = Real.log
            (Real.exp (Real.log (max (α + 2) 0 + (max (2 * C + 2 * D) 0 + 1)))) := by
          rw [Real.log_exp]
        rw [hrw]
        apply Real.log_le_log
        · exact Real.exp_pos _
        · exact hn2
      rw [h_rw] at h_le
      have H4 : Real.log (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1)) ≤ 2 * Real.log n := by
        linarith
      have h1 : 1 ≤ max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1) := by
        have : 0 ≤ max (α + 2) 0 * n := mul_nonneg (le_max_right _ _) (by linarith)
        have : 1 ≤ max (2 * (C : ℝ) + 2 * D) 0 + 1 := by
          linarith [le_max_right (2 * (C : ℝ) + 2 * D) 0]
        linarith
      have H5 : 0 ≤ Real.log (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1)) := Real.log_nonneg h1
      have h_norm1 : ‖Real.log (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1))‖ = Real.log
          (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1)) := by simp [abs_of_nonneg H5]
      have h_norm2 : ‖Real.log n‖ = Real.log n := by simp [abs_of_nonneg h_log_n_pos]
      rw [h_norm1, h_norm2]
      exact H4
    exact Asymptotics.isBigO_iff.mpr ⟨2, H⟩
  
  have H_o : (fun (n : ℝ) => Real.log (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1)))
      =o[Filter.atTop] id := H_O.trans_isLittleO Real.isLittleO_log_id_atTop
  
  have H_o_logb : (fun (n : ℝ) => Real.logb 2 (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1)))
      =o[Filter.atTop] id := by
    have h_rw : (fun (n : ℝ) => Real.logb 2 (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1))) =
        (fun (n : ℝ) => (1 / Real.log 2) * Real.log (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 +
                          1))) := by
      ext n
      have h_log : Real.logb 2 (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1)) = Real.log
          (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1)) / Real.log 2 := rfl
      rw [h_log]
      ring
    rw [h_rw]
    exact Asymptotics.IsLittleO.const_mul_left H_o (1 / Real.log 2)
  
  have H_o_const : (fun (_ : ℝ) => (2 * c : ℝ)) =o[Filter.atTop] id := by
    have H1 : (fun (n : ℝ) => (2 * c : ℝ)) =O[Filter.atTop] (fun _ : ℝ => (1 : ℝ)) :=
        Asymptotics.isBigO_const_const _ (by norm_num) Filter.atTop
    have H2 : (fun _ : ℝ => (1 : ℝ)) =o[Filter.atTop] id := by
      apply Asymptotics.IsLittleO.of_bound
      intro ε hε
      filter_upwards [Filter.eventually_gt_atTop (1/ε)] with n hn
      have h_norm1 : ‖(1 : ℝ)‖ = 1 := norm_one
      have hn_pos : 0 ≤ n := by
        have hzz_div_le : 0 ≤ 1 / ε := div_nonneg (by norm_num) hε.le
        linarith
      have h_norm2 : ‖id (n : ℝ)‖ = n := by simp [abs_of_nonneg hn_pos]
      rw [h_norm1, h_norm2]
      have h_le : 1 / ε ≤ n := hn.le
      rw [div_le_iff₀ hε] at h_le
      linarith
    exact H1.trans_isLittleO H2
  have H_o_final : (fun n : ℝ => c * (Real.logb 2 (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1))
                                   + 1) + c) =o[Filter.atTop] id := by
    have h_rw : (fun n : ℝ => c * (Real.logb 2 (max (α + 2) 0 * n + (max (2 * C + 2 * D) 0 + 1)) +
                                1) + c) = (fun n : ℝ => c * Real.logb 2 (max (α + 2) 0 * n +
                                                          (max (2 * C + 2 * D) 0 + 1)) + 2 * c) :=
                                                          by
      ext n
      ring
    rw [h_rw]
    exact Asymptotics.IsLittleO.add (Asymptotics.IsLittleO.const_mul_left H_o_logb c) H_o_const
  have H_lim : Filter.Tendsto (fun n : ℝ => (c * (Real.logb 2 (max (α + 2) 0 * n + (max (2 * C + 2 *
                                              D) 0 + 1)) + 1) + c) / n) Filter.atTop (nhds 0) :=
                                              H_o_final.tendsto_div_nhds_zero
  rw [Metric.tendsto_atTop] at H_lim
  have h_eps : 0 < α' - α := hd
  obtain ⟨N', hN'⟩ := H_lim (α' - α) h_eps
  
  have hN_max : ∃ N : ℕ, (N' : ℝ) ≤ (N : ℝ) ∧ 1 ≤ N := by
    use ⌈max N' 1⌉₊
    have h_ceil : max N' 1 ≤ (⌈max N' 1⌉₊ : ℝ) := Nat.le_ceil _
    constructor
    · calc N' ≤ max N' 1 := le_max_left _ _
        _ ≤ (⌈max N' 1⌉₊ : ℝ) := h_ceil
    · have h_1 : (1 : ℝ) ≤ max N' 1 := le_max_right _ _
      exact_mod_cast (h_1.trans h_ceil)
  obtain ⟨N, hN1, hN2⟩ := hN_max
  
  use N
  intro n hn
  have hn_R : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn' : N' ≤ (n : ℝ) := by linarith
  have h_n_pos : 0 < (n : ℝ) := by
    have h1_le_n : 1 ≤ n := le_trans hN2 hn
    exact_mod_cast h1_le_n
    
  have h_abs := hN' (n : ℝ) hn'
  have h_dist : dist (((c : ℝ) * (Real.logb 2 (max (α + 2) 0 * ↑n + (max (2 * ↑C + 2 * D) 0 + 1)) +
      1) + ↑c) / ↑n) 0 = ‖(((c : ℝ) * (Real.logb 2 (max (α + 2) 0 * ↑n + (max (2 * ↑C + 2 * D) 0 +
      1)) + 1) + ↑c) / ↑n)‖ := by
    rw [dist_zero_right]
  rw [h_dist] at h_abs
  
  have h_le : ((c : ℝ) * (Real.logb 2 (max (α + 2) 0 * ↑n + (max (2 * ↑C + 2 * D) 0 + 1)) + 1) + ↑c)
      / ↑n ≤ ‖(((c : ℝ) * (Real.logb 2 (max (α + 2) 0 * ↑n + (max (2 * ↑C + 2 * D) 0 + 1)) + 1) +
      ↑c) / ↑n)‖ := le_abs_self _
  have h_le2 : ((c : ℝ) * (Real.logb 2 (max (α + 2) 0 * ↑n + (max (2 * ↑C + 2 * D) 0 + 1)) + 1) +
      ↑c) / ↑n < α' - α := by linarith
  have h_le3 : ((c : ℝ) * (Real.logb 2 (max (α + 2) 0 * ↑n + (max (2 * ↑C + 2 * D) 0 + 1)) + 1) +
      ↑c) < (α' - α) * n := (div_lt_iff₀ h_n_pos).mp h_le2
  have h_bound3_n := H_bound3 n
  linarith

private lemma exists_condK_restrictBits_ge_n_bound (c C : ℕ) (α α' : ℝ) (D : ℝ)
    (hαα' : α < α') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ b : ℕ, (b : ℝ) ≤ (α + 2) * n + 2 * C + 2 * D →
      (logSlack c (b + 1) : ℝ) ≤ (α' - α) * n := by
  have hd : 0 < α' - α := by linarith
  obtain ⟨N, hN⟩ := exists_condK_restrictBits_ge_eventual_bound c C α α' D hαα'
  use N
  intro n hn b hb
  have hb_nonneg : 0 ≤ (α + 2) * n + 2 * C + 2 * D := by
    calc 0 ≤ (b : ℝ) := Nat.cast_nonneg b
      _ ≤ (α + 2) * n + 2 * C + 2 * D := hb
  have h_floor : b + 1 ≤ ⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1 := by
    apply Nat.succ_le_succ
    exact Nat.le_floor hb
  have h_mono : logSlack c (b + 1) ≤ logSlack c (⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1) :=
      monotone_logSlack c h_floor
  have h1 : (logSlack c (b + 1) : ℝ) ≤ (logSlack c (⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1) : ℝ) := by
    exact_mod_cast h_mono
  have h2 : (logSlack c (⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1) : ℝ) = (c : ℝ) *
      ((Nat.bits (⌊(α + 2) * n + 2 * C + 2 * D⌋₊ + 1)).length) + c := by
    unfold logSlack
    push_cast
    rfl
  have h3 := hN n hn
  linarith

/-- Step 1 of the proof of `exists_condK_restrictBits_ge`: the chain-rule logarithmic
overhead is absorbed by one copy of the condition complexity and the exponent gap. -/
private theorem exists_condK_restrictBits_ge_absorb
    (c C : ℕ) {α α' : ℝ} (hαα' : α < α') :
    ∃ N : ℕ, ∀ n a b q : ℕ, N ≤ n →
      α' * n ≤ (b : ℝ) →
      q ≤ n + C →
      b ≤ a + q + logSlack c (b + 1) →
      α * n - 2 * (a : ℝ) ≤ (q : ℝ) := by
  by_cases hα0 : α ≤ 0
  · use 0; intro n a b q _ _ hq _
    have h1 : α * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hα0 (Nat.cast_nonneg n)
    have h2 : 0 ≤ 2 * (a : ℝ) := mul_nonneg zero_le_two (Nat.cast_nonneg a)
    have h3 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  push Not at hα0
  obtain ⟨D, hD⟩ := exists_condK_restrictBits_ge_logSlack_bound c
  obtain ⟨N, hN⟩ := exists_condK_restrictBits_ge_n_bound c C α α' D hαα'
  use N
  intro n a b q hn hbn hqn h_chain
  by_cases ha : α * n / 2 ≤ a
  · linarith
  push Not at ha
  have hb_bound := exists_condK_restrictBits_ge_b_bound c C α D n a b q ha hqn
      (by exact_mod_cast h_chain) (hD b)
  have h_slack := hN n hn b hb_bound
  have h1 : α' * n ≤ (a : ℝ) + q + (α' - α) * n := by
    calc α' * n ≤ b := hbn
      _ ≤ a + q + logSlack c (b + 1) := by exact_mod_cast h_chain
      _ ≤ a + q + (α' - α) * n := by linarith
  linarith


/-- **SUV p. 251**, first corollary: for every `F` of size at least `N` there is `t ∈ F` with
`C(ω(F) | F, t) ≥ α|F| - 2 C(F | t)`. -/
theorem exists_condK_restrictBits_ge (V : Map) (hV : isOptimalConditional V) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ (w : CantorSeq) (N : ℕ), ∀ F : Finset ℕ, N ≤ F.card → ∃ t ∈ F,
      α * F.card - 2 * ((condK V (finsetCode F) (natBits t)).toNat : ℝ) ≤
        ((condK V (restrictBits w F) (pairCode (finsetCode F) (natBits t))).toNat : ℝ) := by
  set α' := (α + 1) / 2
  have hα0' : 0 < α' := by dsimp [α']; linarith
  have hα'1 : α' < 1 := by dsimp [α']; linarith
  have hαα' : α < α' := by dsimp [α']; linarith
  
  have H := exists_max_setPairComplexity_ge V hV hα0' hα'1
  rcases H with ⟨w, N', hN'⟩
  obtain ⟨c_chain, hc_chain⟩ := condK_pairCode_chain_upper_values V hV
  obtain ⟨c1, hc1⟩ := plainK_le_length V hV
  obtain ⟨c2, hc2⟩ := condK_le_plainK V hV
  
  obtain ⟨N_abs, hN_abs⟩ := exists_condK_restrictBits_ge_absorb c_chain (c1 + c2) hαα'
  
  use w, max N' N_abs
  intro F hF
  have hF_N' : N' ≤ F.card := le_trans (le_max_left _ _) hF
  have hF_N_abs : N_abs ≤ F.card := le_trans (le_max_right _ _) hF
  
  rcases hN' F hF_N' with ⟨t, ht, hbound⟩
  use t, ht
  
  set n := F.card
  set a := (condK V (finsetCode F) (natBits t)).toNat
  set q := (condK V (restrictBits w F) (pairCode (finsetCode F) (natBits t))).toNat
  set b := (condK V (pairCode (finsetCode F) (restrictBits w F)) (natBits t)).toNat
  
  have hb_bound : α' * n ≤ (b : ℝ) := by
    have h_b_eq : (b : ℝ) = setPairComplexity V w F t := rfl
    rwa [h_b_eq]
    
  have ha_val : HasPlainConditionalComplexityValue V (finsetCode F) (natBits t) a := by
    dsimp [a, HasPlainConditionalComplexityValue]
    exact (ENat.natCast_toNat (avgCond_condK_ne_top V hV _ _)).symm
  have hq_val : HasPlainConditionalComplexityValue V (restrictBits w F) (pairCode (finsetCode F)
      (natBits t)) q := by
    dsimp [q, HasPlainConditionalComplexityValue]
    exact (ENat.natCast_toNat (avgCond_condK_ne_top V hV _ _)).symm
  have hb_val : HasPlainConditionalComplexityValue V (pairCode (finsetCode F) (restrictBits w F))
      (natBits t) b := by
    dsimp [b, HasPlainConditionalComplexityValue]
    exact (ENat.natCast_toNat (avgCond_condK_ne_top V hV _ _)).symm
    
  have h_chain := hc_chain (finsetCode F) (restrictBits w F) (natBits t) a q b ha_val hq_val hb_val
  
  have h_len : programLength (restrictBits w F) = F.card := by
    change (restrictBits w F).length = F.card
    dsimp [restrictBits]
    rw [List.length_map, Finset.length_sort]
    
  have h_le2 : condK V (restrictBits w F) (pairCode (finsetCode F) (natBits t)) ≤
      ((n + c1 + c2 : ℕ) : ENat) := by
    calc condK V (restrictBits w F) (pairCode (finsetCode F) (natBits t))
      _ ≤ plainK V (restrictBits w F) + (c2 : ENat) := hc2 _ _
      _ ≤ (programLength (restrictBits w F) : ENat) + (c1 : ENat) + (c2 : ENat) :=
          add_le_add (hc1 _) le_rfl
      _ = (n : ENat) + (c1 : ENat) + (c2 : ENat) := by rw [h_len]
      _ = ((n + c1 + c2 : ℕ) : ENat) := by push_cast; rfl
      
  have h_q_bound : q ≤ n + (c1 + c2) := by
    have h_toNat := ENat.toNat_le_toNat h_le2 (by exact ENat.natCast_ne_top _)
    have h_toNat2 : ((n + c1 + c2 : ℕ) : ENat).toNat = n + c1 + c2 := rfl
    rw [h_toNat2] at h_toNat
    have eq : n + c1 + c2 = n + (c1 + c2) := by omega
    rwa [eq] at h_toNat
    
  exact hN_abs n a b q hF_N_abs hb_bound h_q_bound h_chain

/-- **SUV p. 251**, second corollary: `C(ω(F) | F) ≥ α|F| - 2 max_{t ∈ F} C(F | t)`.  The book says
"for every finite `F`"; this is for `|F| ≥ N`, as the derivation gives.  Smaller sets only change
the statement by a constant.  The maximum is expressed through its upper bounds `B`. -/
theorem condK_restrictBits_ge_of_forall_le (V : Map) (hV : isOptimalConditional V) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (w : CantorSeq) (N : ℕ), ∀ F : Finset ℕ, N ≤ F.card → ∀ B : ℝ,
      (∀ t ∈ F, ((condK V (finsetCode F) (natBits t)).toNat : ℝ) ≤ B) →
        α * F.card - 2 * B ≤ ((condK V (restrictBits w F) (finsetCode F)).toNat : ℝ) := by
  set α' := (α + 1) / 2
  have hα'0 : 0 < α' := by dsimp [α']; linarith
  have hα'1 : α' < 1 := by dsimp [α']; linarith
  have H := exists_condK_restrictBits_ge V hV hα'0 hα'1
  rcases H with ⟨w, N', hN'⟩
  obtain ⟨c, hc⟩ := condK_condPair_left_le V hV
  have h_diff : 0 < α' - α := by dsimp [α']; linarith
  have h_ceil : ∃ N_c : ℕ, (c : ℝ) ≤ (α' - α) * N_c := by
    obtain ⟨N_c, hN_c⟩ := exists_nat_gt (c / (α' - α))
    use N_c
    have h1 := (div_lt_iff₀ h_diff).mp hN_c
    linarith
  rcases h_ceil with ⟨N_c, hNc⟩
  use w, max N' N_c
  intro F hF B hB
  have hF_N' : N' ≤ F.card := le_trans (le_max_left N' N_c) hF
  have hF_Nc : N_c ≤ F.card := le_trans (le_max_right N' N_c) hF
  rcases hN' F hF_N' with ⟨t, ht, hbound⟩
  have hBt := hB t ht
  have h_le := hc (restrictBits w F) (finsetCode F) (natBits t)
  have h_top_ne : condK V (restrictBits w F) (finsetCode F) + (c : ℕ∞) ≠ ⊤ := by
    apply WithTop.add_ne_top.mpr
    constructor
    · exact avgCond_condK_ne_top V hV _ _
    · exact WithTop.coe_ne_top
  have h_le_nat : ((condK V (restrictBits w F) (pairCode (finsetCode F) (natBits t))).toNat : ℝ) ≤
      ((condK V (restrictBits w F) (finsetCode F)).toNat : ℝ) + c := by
    have h1 := ENat.toNat_le_toNat h_le h_top_ne
    have h2 : (condK V (restrictBits w F) (finsetCode F) + (c : ℕ∞)).toNat =
        (condK V (restrictBits w F) (finsetCode F)).toNat + c := by
      exact ENat.toNat_add (avgCond_condK_ne_top V hV _ _) WithTop.coe_ne_top
    rw [h2] at h1
    exact_mod_cast h1
  have hc_le_F : (c : ℝ) ≤ (α' - α) * F.card := calc
    (c : ℝ) ≤ (α' - α) * N_c := hNc
    _ ≤ (α' - α) * F.card := mul_le_mul_of_nonneg_left (by exact_mod_cast hF_Nc) (le_of_lt h_diff)
  calc α * F.card - 2 * B
    _ ≤ α' * F.card - c - 2 * B := by linarith
    _ ≤ α' * F.card - c - 2 * ((condK V (finsetCode F) (natBits t)).toNat : ℝ) := by linarith
    _ ≤ ((condK V (restrictBits w F) (pairCode (finsetCode F) (natBits t))).toNat : ℝ) - c :=
      by linarith
    _ ≤ ((condK V (restrictBits w F) (finsetCode F)).toNat : ℝ) := by linarith

end Kolmogorov.Applications
