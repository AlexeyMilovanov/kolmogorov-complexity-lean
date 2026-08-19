import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedChargedHeavyNoiseGain
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedAddNoiseLowBranch
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseComplexity
import KolmogorovMathlib.Prefix.Kraft
import KolmogorovMathlib.Prefix.Encoding

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

def stratumPrefixCode (stratum : BitString) : BitString :=
  natCode stratum.length ++ stratum

theorem length_stratumPrefixCode (stratum : BitString) :
    (stratumPrefixCode stratum).length = 2 * stratum.length + 1 := by
  simp [stratumPrefixCode]
  omega

theorem isPrefixFree_range_stratumPrefixCode : IsPrefixFree (Set.range stratumPrefixCode) := by
  rintro _ ⟨s1, rfl⟩ _ ⟨s2, rfl⟩ ⟨t, ht⟩
  unfold stratumPrefixCode at ht
  rw [List.append_assoc] at ht
  have hinj := natCode_append_inj ht
  have heq : s1.length = s2.length := hinj.1
  have happ : s1 ++ t = s2 := hinj.2
  have hlen : (s1 ++ t).length = s2.length := by rw [happ]
  rw [List.length_append, heq] at hlen
  have ht_empty : t.length = 0 := by omega
  cases t with
  | nil =>
    rw [List.append_nil] at happ
    rw [happ]
  | cons _ _ => cases ht_empty

theorem stratumPrefixCode_injective : Function.Injective stratumPrefixCode := by
  intro s1 s2 heq
  exact (natCode_append_inj heq).2

/-- **Weighted Kraft pigeonhole.**  If a finite family `F` of strata carries a
total natural weight `∑ N s ≥ 2^K`, then some stratum `s` carries weight at
least `2^(K - |stratumPrefixCode s|)`.  The subtracted length is exactly the
Kraft charge of the self-delimiting stratum address, so it is later cancelled by
the multiplicity exponent.  Proof: real-valued contrapositive against the finite
Kraft inequality `finset_kraft_real_le_one` for the prefix-free image of `F`
under the injective code `stratumPrefixCode`, with one strict term supplied by a
positive weight (which must exist since `∑ N s ≥ 2^K ≥ 1`). -/
lemma finset_kraft_pigeonhole
    (F : Finset BitString) (N : BitString → ℕ) (K : ℕ)
    (h_sum : 2 ^ K ≤ ∑ s ∈ F, N s) :
    ∃ s ∈ F, 2 ^ (K - (stratumPrefixCode s).length) ≤ N s := by
  by_contra hcon
  push Not at hcon
  have h2Kpos : 0 < 2 ^ K := pow_pos (by norm_num) K
  -- Kraft sum over `F` via the injective prefix-free code.
  have hpf : IsPrefixFree ((F.image stratumPrefixCode : Finset BitString) : Set BitString) := by
    apply isPrefixFree_range_stratumPrefixCode.mono
    intro w hw
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hw
    obtain ⟨s, _, rfl⟩ := hw
    exact ⟨s, rfl⟩
  have hkraft : ∑ s ∈ F, ((1 : ℝ) / 2) ^ (stratumPrefixCode s).length ≤ 1 := by
    have h := finset_kraft_real_le_one (F.image stratumPrefixCode) hpf
    rwa [Finset.sum_image (fun a _ b _ hab => stratumPrefixCode_injective hab)] at h
  -- Real per-element bound: `N s ≤ 2^K * (1/2)^|code s|`.
  have hNf : ∀ s ∈ F,
      (N s : ℝ) ≤ (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s).length := by
    intro s hs
    by_cases hlen : (stratumPrefixCode s).length ≤ K
    · have hfs : (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s).length
          = (2 : ℝ) ^ (K - (stratumPrefixCode s).length) := by
        rw [div_pow, one_pow, pow_sub₀ (2 : ℝ) (by norm_num) hlen]; field_simp
      rw [hfs]
      have hlt : (N s : ℝ) < (2 : ℝ) ^ (K - (stratumPrefixCode s).length) := by
        exact_mod_cast hcon s hs
      linarith
    · push Not at hlen
      have hK0 : K - (stratumPrefixCode s).length = 0 := by omega
      have hlt := hcon s hs
      rw [hK0, pow_zero] at hlt
      have hN0 : N s = 0 := by omega
      rw [hN0]; simp only [Nat.cast_zero]; positivity
  -- A positive term exists since the sum is `≥ 2^K ≥ 1`.
  have hex : ∃ s ∈ F, 0 < N s := by
    by_contra hcon2
    push Not at hcon2
    have hz : ∑ s ∈ F, N s = 0 := Finset.sum_eq_zero (fun s hs => Nat.le_zero.mp (hcon2 s hs))
    omega
  obtain ⟨s₀, hs₀F, hs₀pos⟩ := hex
  have hs₀lt := hcon s₀ hs₀F
  have hlen₀ : (stratumPrefixCode s₀).length ≤ K := by
    by_contra hc
    push Not at hc
    have hK0 : K - (stratumPrefixCode s₀).length = 0 := by omega
    rw [hK0, pow_zero] at hs₀lt
    omega
  -- Strict bound at `s₀`: `N s₀ ≤ f s₀ - 1`.
  have hf₀ : (N s₀ : ℝ)
      ≤ (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s₀).length - 1 := by
    have hfs : (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s₀).length
        = (2 : ℝ) ^ (K - (stratumPrefixCode s₀).length) := by
      rw [div_pow, one_pow, pow_sub₀ (2 : ℝ) (by norm_num) hlen₀]; field_simp
    rw [hfs]
    have h1 : N s₀ + 1 ≤ 2 ^ (K - (stratumPrefixCode s₀).length) := hs₀lt
    have h1' : (N s₀ : ℝ) + 1 ≤ (2 : ℝ) ^ (K - (stratumPrefixCode s₀).length) := by
      exact_mod_cast h1
    linarith
  -- Sum bound over `F` of the real weights.
  have hsumf : ∑ s ∈ F, (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s).length
      ≤ (2 : ℝ) ^ K := by
    rw [← Finset.mul_sum]
    calc (2 : ℝ) ^ K * ∑ s ∈ F, ((1 : ℝ) / 2) ^ (stratumPrefixCode s).length
        ≤ (2 : ℝ) ^ K * 1 := by
          apply mul_le_mul_of_nonneg_left hkraft (by positivity)
      _ = (2 : ℝ) ^ K := by ring
  -- Split the `N`-sum at `s₀` and derive the contradiction.
  have hsplit : (∑ s ∈ F, (N s : ℝ))
      = (N s₀ : ℝ) + ∑ s ∈ F.erase s₀, (N s : ℝ) :=
    (Finset.add_sum_erase F (fun s => (N s : ℝ)) hs₀F).symm
  have herase : ∑ s ∈ F.erase s₀, (N s : ℝ)
      ≤ ∑ s ∈ F.erase s₀, (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s).length := by
    apply Finset.sum_le_sum
    intro s hs
    exact hNf s (Finset.mem_of_mem_erase hs)
  have hfsplit : ∑ s ∈ F, (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s).length
      = (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s₀).length
        + ∑ s ∈ F.erase s₀, (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s).length :=
    (Finset.add_sum_erase F _ hs₀F).symm
  have hlow : (2 : ℝ) ^ K ≤ ∑ s ∈ F, (N s : ℝ) := by
    have h : ((2 ^ K : ℕ) : ℝ) ≤ ((∑ s ∈ F, N s : ℕ) : ℝ) := by exact_mod_cast h_sum
    push_cast at h
    exact h
  rw [hsplit] at hlow
  have hcombine : (N s₀ : ℝ) + ∑ s ∈ F.erase s₀, (N s : ℝ) ≤ (2 : ℝ) ^ K - 1 := by
    calc (N s₀ : ℝ) + ∑ s ∈ F.erase s₀, (N s : ℝ)
        ≤ ((2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s₀).length - 1)
          + ∑ s ∈ F.erase s₀, (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s).length := by
          linarith [herase, hf₀]
      _ = (∑ s ∈ F, (2 : ℝ) ^ K * ((1 : ℝ) / 2) ^ (stratumPrefixCode s).length) - 1 := by
          rw [hfsplit]; ring
      _ ≤ (2 : ℝ) ^ K - 1 := by linarith [hsumf]
  linarith

/-- A subset of a bounded union has cardinality at most the sum of the parts.
Standard `Finset` bookkeeping used to translate "the `x`-containing pooled codes
lie in the union of the per-stratum candidate families" into a per-stratum
count. -/
lemma card_le_sum_of_subset_biUnion {α β : Type} [DecidableEq α]
    (A : Finset α) (F : Finset β) (B : β → Finset α)
    (h_sub : A ⊆ F.biUnion B) :
    A.card ≤ ∑ s ∈ F, (B s).card :=
  le_trans (Finset.card_le_card h_sub) Finset.card_biUnion_le

/-! ### The heavy truncation as a description of `x`

The two lemmas below record the two coordinates of the true heavy truncation as
a description of `x`: its prefix set complexity is the complexity coordinate of
the pair model plus logarithmic advice for the threshold, and its size is the
size coordinate of the pair model reduced by the threshold. -/

/-- The heavy truncation of a pair model of complexity budget `i` has prefix set
complexity at most `i` plus logarithmic advice for the truncation threshold. -/
theorem setComplexity_finiteSetFstHeavyTruncation_le_of_mem_descriptions
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (i j threshold : ℕ) (B : Finset BitString),
      B ∈ descriptionsWithComplexityLeAndSizeLe U i j →
      ∀ (_hB : B.Nonempty) (hH : (finiteSetFstHeavyTruncation B threshold).Nonempty),
        setComplexity U (finiteSetFstHeavyTruncation B threshold) hH ≤
          ((i + logSlack c threshold : ℕ) : ENat) := by
  obtain ⟨c₀, hc₀⟩ := setComplexity_le_of_mem_descriptionsWithComplexityLe U
  obtain ⟨c₁, hc₁⟩ := finiteSetFstHeavyTruncation_setComplexity_le U hU
  refine ⟨c₀ + c₁, ?_⟩
  intro i j threshold B hB hBne hH
  have hBcomp : setComplexity U B hBne ≤ ((i + c₀ : ℕ) : ENat) := by
    have h := hc₀ i B hBne (Finset.mem_filter.mp hB).1
    exact_mod_cast h
  have hnum : i + c₀ + logSlack c₁ threshold ≤ i + logSlack (c₀ + c₁) threshold := by
    unfold logSlack
    have hmul : c₁ * (Nat.bits threshold).length ≤
        (c₀ + c₁) * (Nat.bits threshold).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  calc setComplexity U (finiteSetFstHeavyTruncation B threshold) hH
      ≤ setComplexity U B hBne + (logSlack c₁ threshold : ENat) :=
        hc₁ B hBne threshold hH
    _ ≤ ((i + c₀ : ℕ) : ENat) + (logSlack c₁ threshold : ENat) := by gcongr
    _ = ((i + c₀ + logSlack c₁ threshold : ℕ) : ENat) := by push_cast; ring
    _ ≤ ((i + logSlack (c₀ + c₁) threshold : ℕ) : ENat) := by exact_mod_cast hnum

/-- The heavy truncation of a model of log-size `j` has at most
`2 ^ (j - threshold + 1)` elements. -/
theorem finiteSetFstHeavyTruncation_card_le_of_mem_descriptions
    {U : Map} {i j threshold : ℕ} {B : Finset BitString}
    (hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j) :
    (finiteSetFstHeavyTruncation B threshold).card ≤ 2 ^ (j - threshold + 1) := by
  have hlogB : finiteSetLogCard B ≤ j :=
    (finiteSetLogCard_le_iff B j).mpr (Finset.mem_filter.mp hB).2
  refine (finiteSetFstHeavyTruncation_card_le B threshold).trans ?_
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Zero-multiplicity witness.**  The true heavy truncation is by itself a
description of `x` with complexity coordinate `i + logSlack c (y.length)` and
size coordinate `j - threshold + 1`.  This is the `k = 0` case of the projection
statement, and it is what discharges the small-gain regime. -/
theorem manyIJDescriptions_finiteSetFstHeavyTruncation_zero
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString) (i j threshold : ℕ) (B : Finset BitString)
      (_hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
      (_hpair : pairCode x y ∈ B),
      threshold ≤ y.length →
      threshold ≤ finiteSetLogCard (finiteSetFstFiber B x) →
      ManyIJDescriptions U x (i + logSlack c y.length) (j - threshold + 1) 0 := by
  obtain ⟨c, hc⟩ := setComplexity_finiteSetFstHeavyTruncation_le_of_mem_descriptions U hU
  refine ⟨c, ?_⟩
  intro x y i j threshold B hB hpair hthr hheavy
  have hBne : B.Nonempty := ⟨_, hpair⟩
  have hxH : x ∈ finiteSetFstHeavyTruncation B threshold :=
    finiteSetFstHeavyTruncation_mem hpair hheavy
  have hHne : (finiteSetFstHeavyTruncation B threshold).Nonempty := ⟨x, hxH⟩
  have hcompl : setComplexity U (finiteSetFstHeavyTruncation B threshold) hHne ≤
      ((i + logSlack c y.length : ℕ) : ENat) := by
    refine le_trans (hc i j threshold B hB hBne hHne) ?_
    have hmono : logSlack c threshold ≤ logSlack c y.length :=
      logSlack_mono_right c hthr
    exact_mod_cast Nat.add_le_add_left hmono i
  have hmem : finiteSetFstHeavyTruncation B threshold ∈
      (descriptionsWithComplexityLeAndSizeLe U (i + logSlack c y.length)
        (j - threshold + 1)).filter (fun S => x ∈ S) := by
    rw [Finset.mem_filter]
    refine ⟨?_, hxH⟩
    rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
    exact ⟨mem_descriptionsWithComplexityLe_of_complexity hHne hcompl,
      finiteSetFstHeavyTruncation_card_le_of_mem_descriptions hB⟩
  have hpos := Finset.card_pos.mpr ⟨_, hmem⟩
  simpa [ManyIJDescriptions] using hpos

/-- **Charged-heavy multiplicity conversion, honest budget.**  This is the
version of `manyIJDescriptions_of_budgetedChargedHeavy_information_gain` below
that the standard argument actually supports: the complexity drop `I - K` is
`i - gain` plus the conditional-randomness deficiency `epsilon` of `y` given `x`
and a slack logarithmic in the *visible parameters* `i`, `j` and `l(y)`.

The proof is the classical rank/compression argument.  Let `H` be the heavy
truncation, `i1` its exact prefix set complexity and `j1 = j - threshold + 1`
its size coordinate.  If `x` had fewer than `2 ^ m` distinct `(i1, j1)`
descriptions, then `[H]` would be determined by its rank given `x`
(`condK_description_code_le_of_not_many`), so composing that description with a
shortest description of `y` from `⟨x, [H]⟩` (`condK_two_stage_pair_context`)
would describe `y` from `x` in fewer than `l(y) - epsilon` bits, contradicting
the assumed conditional randomness of `y`. -/
theorem manyIJDescriptions_of_heavyTruncation_information_gain
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString) (epsilon i j threshold gain : ℕ)
      (B : Finset BitString)
      (_hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
      (hpair : pairCode x y ∈ B)
      (hheavy : threshold ≤ finiteSetLogCard (finiteSetFstFiber B x)),
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      condK V y
          (pairCode x
            (codedUniformOn (finiteSetFstHeavyTruncation B threshold)
              ⟨x, finiteSetFstHeavyTruncation_mem hpair hheavy⟩).code) +
            (gain : ENat) ≤ (y.length : ENat) →
      ∃ I J K : ℕ,
        ManyIJDescriptions U x I J K ∧
        K ≤ I ∧
        I - K ≤ i - gain + epsilon + logSlack c (i + j + y.length) ∧
        J ≤ j - threshold + 1 := by
  obtain ⟨cC, hcC⟩ := setComplexity_finiteSetFstHeavyTruncation_le_of_mem_descriptions U hU
  obtain ⟨cR, hcR⟩ := condK_description_code_le_of_not_many V U hV hU
  obtain ⟨cT, hcT⟩ := condK_two_stage_pair_context V hV
  obtain ⟨bC, hbC⟩ := logSlack_le_add_const cC
  obtain ⟨cR2, hcR2⟩ := logSlack_linear_bound cR 3 (bC + 1)
  obtain ⟨bR2, hbR2⟩ := logSlack_le_add_const cR2
  obtain ⟨c2, hc2⟩ := logSlack_linear_bound 2 2 bR2
  refine ⟨cC + cR2 + c2 + cT + 1, ?_⟩
  intro x y epsilon i j threshold gain B hB hpair hheavy hincompressible hgain
  have hxH : x ∈ finiteSetFstHeavyTruncation B threshold :=
    finiteSetFstHeavyTruncation_mem hpair hheavy
  set H := finiteSetFstHeavyTruncation B threshold with hHdef
  have hHne : H.Nonempty := ⟨x, hxH⟩
  have hBne : B.Nonempty := ⟨_, hpair⟩
  have hgain' : condK V y (pairCode x (codedUniformOn H hHne).code) +
      (gain : ENat) ≤ (y.length : ENat) := hgain
  -- Visible parameter scale.
  set N := i + j + y.length with hNdef
  have hlogB : finiteSetLogCard B ≤ j :=
    (finiteSetLogCard_le_iff B j).mpr (Finset.mem_filter.mp hB).2
  have hfib : finiteSetFstFiber B x ⊆ B := Finset.filter_subset _ _
  have hthrj : threshold ≤ j :=
    le_trans (le_trans hheavy (finiteSetLogCard_mono (Finset.card_le_card hfib))) hlogB
  -- The truncation is a description of `x` with exact complexity `i1`.
  have hcompl : setComplexity U H hHne ≤ ((i + logSlack cC threshold : ℕ) : ENat) :=
    hcC i j threshold B hB hBne hHne
  have hfin : setComplexity U H hHne ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hcompl
  set i1 := (setComplexity U H hHne).toNat with hi1def
  have hi1 : setComplexity U H hHne = (i1 : ENat) := (ENat.natCast_toNat hfin).symm
  have hi1le : i1 ≤ i + logSlack cC threshold := by
    have h : (i1 : ENat) ≤ ((i + logSlack cC threshold : ℕ) : ENat) := by
      rw [← hi1]; exact hcompl
    exact_mod_cast h
  set j1 := j - threshold + 1 with hj1def
  have hHcard : H.card ≤ 2 ^ j1 :=
    finiteSetFstHeavyTruncation_card_le_of_mem_descriptions hB
  -- Slack bookkeeping against the visible scale `N`.
  have hslackC : logSlack cC threshold ≤ logSlack cC N :=
    logSlack_mono_right cC (by omega)
  have hbCN := hbC N
  have hi1N : i1 ≤ 2 * N + bC := by omega
  have hj1N : j1 ≤ N + 1 := by omega
  set R := logSlack cR (i1 + j1) with hRdef
  have hR : R ≤ logSlack cR2 N :=
    le_trans (logSlack_mono_right cR (show i1 + j1 ≤ 3 * N + (bC + 1) by omega)) (hcR2 N)
  have hbR2N := hbR2 N
  set A := y.length + R with hAdef
  have hAN : A ≤ 2 * N + bR2 := by omega
  have hbits : 2 * (Nat.bits A).length + 2 ≤ logSlack c2 N := by
    have h1 : logSlack 2 A ≤ logSlack 2 (2 * N + bR2) := logSlack_mono_right 2 hAN
    have h2 := hc2 N
    have h3 : logSlack 2 A = 2 * (Nat.bits A).length + 2 := rfl
    omega
  set S := R + 2 * (Nat.bits A).length + cT with hSdef
  set m := gain - epsilon - S - 1 with hmdef
  -- The gain hypothesis in natural-number form.
  have hgainLen : gain ≤ y.length := by
    have h : (gain : ENat) ≤ (y.length : ENat) := le_trans le_add_self hgain'
    exact_mod_cast h
  have hshort : condK V y (pairCode x (codedUniformOn H hHne).code) ≤
      ((y.length - gain : ℕ) : ENat) := by
    have hfin2 : condK V y (pairCode x (codedUniformOn H hHne).code) ≠ ⊤ := by
      intro htop
      rw [htop] at hgain'
      simp at hgain'
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin2
    rw [← hn] at hgain' ⊢
    have hnGain : n + gain ≤ y.length := by exact_mod_cast hgain'
    exact_mod_cast Nat.le_sub_of_add_le hnGain
  -- The multiplicity.
  have hmany : ManyIJDescriptions U x i1 j1 m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0]
      have hmem : H ∈ (descriptionsWithComplexityLeAndSizeLe U i1 j1).filter
          (fun S => x ∈ S) := by
        rw [Finset.mem_filter]
        refine ⟨?_, hxH⟩
        rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
        exact ⟨mem_descriptionsWithComplexityLe_of_complexity hHne (le_of_eq hi1), hHcard⟩
      have hpos := Finset.card_pos.mpr ⟨H, hmem⟩
      simpa [ManyIJDescriptions] using hpos
    · by_contra hnot
      have hrank : condK V (codedUniformOn H hHne).code x ≤ ((m + R : ℕ) : ENat) :=
        hcR H hHne x i1 j1 m hxH hi1 hHcard hnot
      have hchain := hcT y x (codedUniformOn H hHne).code (m + R)
        (y.length - gain) hrank hshort
      have hnat : y.length ≤
          (m + R) + (y.length - gain) + 2 * (Nat.bits (m + R)).length + cT + epsilon := by
        have h := hincompressible.trans (add_le_add hchain (le_refl (epsilon : ENat)))
        exact_mod_cast h
      have hmono : (Nat.bits (m + R)).length ≤ (Nat.bits A).length :=
        length_natBits_mono (by omega)
      omega
  refine ⟨i1, j1, min m i1, hmany.mono_k (min_le_left _ _), min_le_right _ _, ?_, le_rfl⟩
  have hadd : logSlack cC N + logSlack cR2 N + logSlack c2 N =
      logSlack (cC + cR2 + c2) N := by
    unfold logSlack; ring
  have hadd2 : logSlack (cC + cR2 + c2) N + (cT + 1) ≤
      logSlack (cC + cR2 + c2 + cT + 1) N := by
    have h := logSlack_add_const_le (cC + cR2 + c2) (cT + 1) N
    have h2 : cC + cR2 + c2 + (cT + 1) = cC + cR2 + c2 + cT + 1 := by ring
    rwa [h2] at h
  omega

/-
**RETIRED: the budget-scale charged-heavy conversion.**

The theorem previously stated here — an `epsilon`-free, `j`-free budget-scale
`ManyIJDescriptions` conclusion `I - K ≤ i - gain + logSlack c baseBudget +
logSlack c y.length` — has a MATHEMATICALLY FALSE large-gain branch, so it cannot
be honestly proved; its open leaf has been removed rather than relocated.

Refutation (the file's own analysis (1), independently confirmed): take `y = x`
with `x` incompressible of length `n`, `B = {pairCode x x}`, `i = C(B) ≈ n`,
`baseBudget = i`, `j = 0`, `threshold = 0`, `epsilon = n`.  Then
`C(y | ⟨x,[H]⟩) = O(1)`, so `gain = n - O(1)` satisfies the gain hypothesis, while
`J ≤ j - threshold + 1 = 1` forces every counted description to be a ≤2-element
set.  A `ManyIJDescriptions U x I 1 K` meeting `I - K = O(log n)` would, via the
length-free complexity drop, give `x` an `(O(log n), O(log n))`-description,
contradicting `C(x) ≈ n`.  So no witness exists, yet the stated bound is
`i - gain + O(log n) = O(log n)`.  Contradiction.

The HONEST form of this conversion is proved above as
`manyIJDescriptions_of_heavyTruncation_information_gain`, whose complexity-drop
bound keeps the `epsilon` term and the visible size scale
  `I - K ≤ i - gain + epsilon + logSlack c (i + j + y.length)`,
and which implements exactly the mandated many/few dichotomy (its `by_contra`
branch builds the conditional rank decoder contradicting `C(y|x) ≥ |y|-epsilon`).

INTERFACE NOTE (see `iter_003_proof/02_opus.md`).  The frozen research interface
`BudgetedPairProjectionManyStatement` (`BudgetedAddNoiseLowBranch.lean`) is itself
PROVABLY FALSE, and this pair-projection lane is a DECOY: it is imported by
nothing on the `prop_upward` critical path, which runs
`budgetedRandomNoiseTransport_of_budgetedPlainCorner →
propUpward_of_budgetedRandomNoiseTransport`.  The Many statement's constraint
  `I - K + logSlack cDrop (I+J) + cBridge ≤ i + epsilon + logSlack c baseBudget
    + logSlack c y.length`
puts `logSlack cDrop (I+J)` on the LHS, forcing `I+J ≤ 2^O(baseBudget)`; but any
`(I,J)`-description of an incompressible `x ∈ B` — take `B =` all length-`BB(bB)`
strings paired with the empty string, of complexity `≤ bB` — has
`I+J ≥ C(x) - O(log) ≈ BB(bB) ≫ 2^O(bB)`.  The `def` is left unedited (it is
unasserted, hence harmless to the build) and is reported as `INTERFACE_PROBLEM`;
proof effort should target the corner/ordinal route instead.
-/

end Kolmogorov
