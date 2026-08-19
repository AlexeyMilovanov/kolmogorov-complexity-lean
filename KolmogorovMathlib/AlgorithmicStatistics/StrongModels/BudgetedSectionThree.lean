import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedStochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionSnapshot

/-!
# The Section 3 chain at the complexity scale

Every step of the §3 chain (improving descriptions → gap counting → the tight
deficiencies theorem → the optimal-set conversion) is stated in
`KolmogorovMathlib.AlgorithmicStatistics.TwoPart` with a logarithmic slack
measured against the *length* `l(x)`.  For the budgeted statements of §7 this is
useless: a string of small complexity can be exponentially long.

This module reproves the chain with all slacks measured against the *complexity*
`C(x)` (in fact against the visible parameters `i + j`, respectively
`kx + delta + d`).  Inspecting the length-scale proofs shows that `l(x)` is only
ever used as a proxy for `KPPlain U x` (through `KPPlain_le_length_add_log`) or
for the size of the encoded parameters, so the length hypothesis can be dropped
altogether.
-/

namespace Kolmogorov

open Nat
open Nat.Partrec (Code)
open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- **Length-free complexity-portion bound.**  Identical to
`setComplexity_halfRichComplexityPortion_le` except that the slack is measured
against the visible parameters `i + j` instead of `l(x) + i + j`. -/
theorem setComplexity_halfRichComplexityPortion_le_length_free
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x i j k, ManyIJDescriptions U x i j k → k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (i + j) : ENat) ∧
        S.card ≤ 2 ^ j := by
  obtain ⟨f, hf, hf_spec⟩ := halfRichComplexityPortion_selector_correct U hU
  obtain ⟨c₃, hc₃⟩ := KPPlain_partrec_map_le U hU f hf
  obtain ⟨c₄, hc₄⟩ := richInput_KPPlain_le_addr U hU c₃
  refine ⟨4 * c₄ + 4, fun x i j k hmany hk => ?_⟩
  obtain ⟨h, hh, S, hS, hxS, hcard, hfeq⟩ := hf_spec x x.length i j k rfl hmany hk
  refine ⟨S, hS, hxS, ?_, hcard⟩
  have hmem : (codedUniformOn S hS).code ∈ f (richInput i j k h) := by
    rw [hfeq]; exact Part.mem_some _
  have hbound : setComplexity U S hS
      ≤ ((i - k : ℕ) : ENat) + 4 + logSlack c₄ (i + j + k + (i - k + 3)) :=
    le_trans (hc₃ _ _ hmem) (hc₄ i j k h (i - k + 3) hh)
  have habs : 4 + logSlack c₄ (i + j + k + (i - k + 3)) ≤ logSlack (4 * c₄ + 4) (i + j) := by
    apply logSlack_four_add_le
    omega
  refine le_trans hbound ?_
  rw [← ENat.coe_sub, add_assoc]
  gcongr
  exact_mod_cast habs

/-- **Length-free complexity-improvement.**  The `A → C` half of the improving
descriptions machinery with a slack in the visible parameters `i + j` only. -/
theorem improvingDescriptionsComplexity_length_free
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x i j k, ManyIJDescriptions U x i j k → k ≤ i →
      InDescriptionProfile U x (i - k + logSlack c (i + j)) (j + logSlack c (i + j)) := by
  obtain ⟨c, hc⟩ := setComplexity_halfRichComplexityPortion_le_length_free U hU
  refine ⟨c, fun x i j k hmany hk => ?_⟩
  obtain ⟨S, hS, hxS, hcomp, hcard⟩ := hc x i j k hmany hk
  exact ⟨S, hS, hxS, hcomp, hcard.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩

/-- **Length-free tight gap lower bound.**  Identical to
`gap_lowerBound_conditional_setComplexity_tight`, with the slack measured
against `kx + delta + d` (`kx = C_P(x)` is part of the realized gap data)
instead of `l(x) + delta + d`. -/
theorem gap_lowerBound_conditional_setComplexity_tight_budget
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (delta d i j kx c_soi : ℕ),
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      (delta - d : ENat) ≤ KP U (codedUniformOn A hA).code (prefixComplexityContext x kx)
        + logSlack c (kx + delta + d) := by
  obtain ⟨c_lower, hc_lower⟩ := KPPair_chain_lower U hU
  obtain ⟨c_upper, hc_upper⟩ := KPPair_chain_upper U hU
  obtain ⟨c_symm, hc_symm⟩ := KPPair_symm U hU
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c1, hc1⟩ := KP_le_prefixComplexityContext_add_logSlack U hU
  obtain ⟨C1, hC1⟩ := logSlack_linear_bound c1 1 1
  use C1 + c_lower + c_upper + c_symm + 1
  intros A hA x delta d i j kx c_soi h_gap h_def hd
  have hxA := h_gap.1
  have hi := h_gap.2.1
  have hj2 := h_gap.2.2.2.1
  have hkx := h_gap.2.2.2.2.1
  have hdelta := h_gap.2.2.2.2.2
  set code := (codedUniformOn A hA).code
  have hkcode : HasPrefixComplexityValue U code i := hi.symm
  have hkx' : HasPrefixComplexityValue U x kx := hkx
  have h1 : KPPair U x code ≤ (kx : ENat) + KP U code (prefixComplexityContext x kx) + c_upper := by
    have h := hc_upper x code kx hkx'
    rw [hkx'.symm] at h
    exact h
  have h2 : KPPair U code x ≤ KPPair U x code + c_symm := hc_symm code x
  have h3 : (i : ENat) + KP U x (prefixComplexityContext code i) ≤ KPPair U code x + c_lower := by
    have h := hc_lower code x i hkcode
    rw [hkcode.symm] at h
    exact h
  by_cases h_top : KP U code (prefixComplexityContext x kx) = ⊤
  · rw [h_top, top_add]; exact le_top
  obtain ⟨kp_code_kx, hkp_code_kx_raw⟩ := ENat.ne_top_iff_exists.mp h_top
  have hkp_code_kx : KP U code (prefixComplexityContext x kx) = kp_code_kx := hkp_code_kx_raw.symm
  have h_kppair_x_code_ne_top : KPPair U x code ≠ ⊤ := by
    intro h_contra
    have h1_top : ⊤ ≤ (kx : ENat) + kp_code_kx + c_upper := by
      calc ⊤ = KPPair U x code := h_contra.symm
           _ ≤ (kx : ENat) + KP U code (prefixComplexityContext x kx) + c_upper := h1
           _ = (kx : ENat) + kp_code_kx + c_upper := by rw [hkp_code_kx]
    exact ENat.coe_ne_top _ (top_le_iff.mp h1_top)
  obtain ⟨kppair_x_code, hkppair_x_code_raw⟩ := ENat.ne_top_iff_exists.mp h_kppair_x_code_ne_top
  have hkppair_x_code : KPPair U x code = kppair_x_code := hkppair_x_code_raw.symm
  have h_kppair_code_x_ne_top : KPPair U code x ≠ ⊤ := by
    intro h_contra
    have h2_top : ⊤ ≤ (kppair_x_code : ENat) + c_symm := by
      calc ⊤ = KPPair U code x := h_contra.symm
           _ ≤ KPPair U x code + c_symm := h2
           _ = (kppair_x_code : ENat) + c_symm := by rw [hkppair_x_code]
    exact ENat.coe_ne_top _ (top_le_iff.mp h2_top)
  obtain ⟨kppair_code_x, hkppair_code_x_raw⟩ := ENat.ne_top_iff_exists.mp h_kppair_code_x_ne_top
  have hkppair_code_x : KPPair U code x = kppair_code_x := hkppair_code_x_raw.symm
  have h_kp_code_x_ne_top : KP U x (prefixComplexityContext code i) ≠ ⊤ := by
    intro h_contra
    have h3_top : ⊤ ≤ (kppair_code_x : ENat) + c_lower := by
      calc ⊤ = (i : ENat) + ⊤ := (add_top (i : ENat)).symm
           _ = (i : ENat) + KP U x (prefixComplexityContext code i) := by rw [h_contra]
           _ ≤ KPPair U code x + c_lower := h3
           _ = (kppair_code_x : ENat) + c_lower := by rw [hkppair_code_x]
    exact ENat.coe_ne_top _ (top_le_iff.mp h3_top)
  obtain ⟨kp_code_i, hkp_code_i_raw⟩ := ENat.ne_top_iff_exists.mp h_kp_code_x_ne_top
  have hkp_code_i : KP U x (prefixComplexityContext code i) = kp_code_i := hkp_code_i_raw.symm
  have h_kp_x_code_ne_top : KP U x code ≠ ⊤ := by
    intro h_contra
    have hp := hc_plain x code
    have h_top_ineq : ⊤ ≤ (kx : ENat) + c_plain := by
      calc ⊤ = KP U x code := h_contra.symm
           _ ≤ KPPlain U x + c_plain := hp
           _ = (kx : ENat) + c_plain := by rw [← hkx']
    exact ENat.coe_ne_top _ (top_le_iff.mp h_top_ineq)
  obtain ⟨kp_x_code, hkp_x_code_raw⟩ := ENat.ne_top_iff_exists.mp h_kp_x_code_ne_top
  have hkp_x_code : KP U x code = kp_x_code := hkp_x_code_raw.symm
  -- Convert the KPPair symmetry-of-information chain to ℕ.
  have h1n : kppair_x_code ≤ kx + kp_code_kx + c_upper := by
    have h := h1; rw [hkppair_x_code, hkp_code_kx] at h; exact_mod_cast h
  have h2n : kppair_code_x ≤ kppair_x_code + c_symm := by
    have h := h2; rw [hkppair_code_x, hkppair_x_code] at h; exact_mod_cast h
  have h3n : i + kp_code_i ≤ kppair_code_x + c_lower := by
    have h := h3; rw [hkp_code_i, hkppair_code_x] at h; exact_mod_cast h
  -- Deficiency lower bound, tied to the specific `j`.
  obtain ⟨j', hj'card, hj'le⟩ := card_le_of_deficiency hxA h_def
  have hjle : j ≤ j' + 1 := two_pow_half_ennreal_bracket_le hj2 hj'card
  have hj'n : j' ≤ kp_x_code + d := by
    have h := hj'le; rw [hkp_x_code] at h; exact_mod_cast h
  -- Chain rule: drop the index `i` from the context at log cost.
  have hBn : kp_x_code ≤ kp_code_i + logSlack c1 (i + 1) := by
    have h := hc1 x code i; rw [hkp_x_code, hkp_code_i] at h; exact_mod_cast h
  -- Visible-budget bound for `i`: the realized gap pins `delta = i + j - kx`.
  have hi_bound : i + 1 ≤ 1 * (kx + delta + d) + 1 := by omega
  have h10 : logSlack c1 (i + 1) ≤ logSlack C1 (kx + delta + d) :=
    le_trans (logSlack_mono hi_bound) (hC1 _)
  set S := logSlack c1 (i + 1) with hSdef
  -- Absorb the log slack and constants into a single visible-budget slack.
  have habs : S + (c_lower + c_upper + c_symm + 1)
      ≤ logSlack (C1 + c_lower + c_upper + c_symm + 1) (kx + delta + d) := by
    have e : C1 + c_lower + c_upper + c_symm + 1 = C1 + (c_lower + c_upper + c_symm + 1) := by ring
    rw [e]
    calc S + (c_lower + c_upper + c_symm + 1)
        ≤ logSlack C1 (kx + delta + d) + (c_lower + c_upper + c_symm + 1) := by omega
      _ ≤ logSlack (C1 + (c_lower + c_upper + c_symm + 1)) (kx + delta + d) :=
          logSlack_add_const_le _ _ _
  -- Final ℕ inequality, then cast to `ENat`.
  have hfin : delta ≤ kp_code_kx
      + logSlack (C1 + c_lower + c_upper + c_symm + 1) (kx + delta + d) + d := by omega
  rw [hkp_code_kx, tsub_le_iff_right]
  exact_mod_cast hfin

/-- **Length-free description-count bound.**  Identical to
`description_count_of_conditional_complexity_gap`, with the slack measured
against the visible parameters `i + j` alone. -/
theorem description_count_of_conditional_complexity_gap_length_free (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (i j m kx : ℕ),
      x ∈ A →
      setComplexity U A hA = (i : ENat) →
      A.card ≤ 2 ^ j →
      HasPrefixComplexityValue U x kx →
      ¬ ManyIJDescriptions U x i j m →
      KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤
          (m + logSlack c (i + j) : ENat) := by
  obtain ⟨c_opt, hc_opt⟩ : ∃ c_opt : Code, IsCodeFor c_opt U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨c_kp, hkp⟩ := KP_partrec_cond_first_map_le U hU (indexSelectorFn c_opt)
    (partrec_indexSelectorFn c_opt)
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨C2, hC2⟩ := logSlack_linear_bound 2 3 7
  let C1 := C2 + c_kp + c_plain + c_len + 6
  use C1
  intro A hA x i j m kx hx hi hj hkx h_not_many
  obtain ⟨t₀, ht₀⟩ := code_mem_appearanceListCodes hc_opt A hA x i j hx hi hj
  set y := prefixComplexityContext x kx
  set code := (codedUniformOn A hA).code
  have hy : decodeFirst y = x := by
    dsimp [y, prefixComplexityContext]
    rw [decodeFirst_pairCode]
  obtain ⟨r, hr_lt, hr_spec⟩ := indexSelectorFn_eq_code c_opt i j x code t₀ ht₀
  set w := richInput i j 0 r
  have hw_i : selNat w = i := selNat_richInput i j 0 r
  have hw_j : selAlpha w = j := selAlpha_richInput i j 0 r
  have hw_h : selH w = r := selH_richInput i j 0 r
  have h_some : indexSelectorFn c_opt y w = Part.some code := hr_spec y w hy hw_i hw_j hw_h
  have h_in : code ∈ indexSelectorFn c_opt y w := Part.eq_some_iff.mp h_some
  have h_bound1 : KP U code y ≤ KP U w y + (c_kp : ENat) := hkp w code y h_in
  have h_bound2 : KP U w y ≤ KPPlain U w + (c_plain : ENat) := hc_plain w y
  have h_bound3 : KPPlain U w ≤
      (w.length : ENat) + 2 * (Nat.bits w.length).length + c_len := hc_len w
  have h_w_len_r : w.length ≤ 2 * (Nat.bits i).length + 2 * (Nat.bits j).length +
      (Nat.bits r).length + 6 := by
    unfold w richInput selectorInput pack4
    simp [length_pairCode]
    omega
  have hr_lt_2m : r < 2 ^ m := lt_trans hr_lt
    (appearanceListCodes_length_lt_of_not_manyIJ hc_opt h_not_many t₀)
  have hr_lt_2i : r < 2 ^ (i + 1) := by
    have h1 := appearanceListCodes_length_le_descriptionsContaining hc_opt i j x t₀
    have h2 := Finset.card_filter_le (descriptionsWithComplexityLeAndSizeLe U i j) (fun S => x ∈ S)
    have h3 := card_descriptionsWithComplexityLeAndSizeLe U i j
    exact lt_of_lt_of_le hr_lt (h1.trans (h2.trans h3))
  let M := i + j
  have h_w_len_M : w.length ≤ 3 * M + 7 := by
    have hi_len : (Nat.bits i).length ≤ i := length_natBits_le_self i
    have hj_len : (Nat.bits j).length ≤ j := length_natBits_le_self j
    have hr_len : (Nat.bits r).length ≤ i + 1 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr hr_lt_2i
    simp only [M]
    omega
  have h_slack : c_kp + c_plain + c_len + 2 * (Nat.bits i).length + 2 * (Nat.bits j).length + 6 + 2
      * (Nat.bits w.length).length ≤ logSlack C1 M := by
    have hw1 : (Nat.bits w.length).length ≤ (Nat.bits (3 * M + 7)).length := by
      have h : w.length < 2 ^ (Nat.size (3 * M + 7)) :=
        lt_of_le_of_lt h_w_len_M (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hw3 : 2 * (Nat.bits (3 * M + 7)).length ≤ logSlack 2 (3 * M + 7) := by
      unfold logSlack
      omega
    have hw5 : logSlack C2 M = C2 * (Nat.bits M).length + C2 := rfl
    have hw6 : logSlack C1 M =
        (C2 + c_kp + c_plain + c_len + 6) * (Nat.bits M).length +
          (C2 + c_kp + c_plain + c_len + 6) := rfl
    have hiM : i ≤ M := by simp only [M]; omega
    have hjM : j ≤ M := by simp only [M]; omega
    have hi_len : (Nat.bits i).length ≤ (Nat.bits M).length := by
      have h : i < 2 ^ (Nat.size M) := lt_of_le_of_lt hiM (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hj_len : (Nat.bits j).length ≤ (Nat.bits M).length := by
      have h : j < 2 ^ (Nat.size M) := lt_of_le_of_lt hjM (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hC2_M := hC2 M
    nlinarith
  calc KP U code y ≤ KP U w y + c_kp := h_bound1
    _ ≤ KPPlain U w + c_plain + c_kp := by gcongr
    _ ≤ (w.length : ENat) + 2 * (Nat.bits w.length).length + c_len + c_plain + c_kp := by gcongr
    _ ≤ ((2 * (Nat.bits i).length + 2 * (Nat.bits j).length + (Nat.bits r).length + 6 : ℕ) : ENat) +
        2 * (Nat.bits w.length).length + c_len + c_plain + c_kp := by
      have h : w.length + 2 * w.length.bits.length + c_len + c_plain + c_kp ≤
          (2 * i.bits.length + 2 * j.bits.length + r.bits.length + 6) +
            2 * w.length.bits.length + c_len + c_plain + c_kp := by omega
      exact_mod_cast h
    _ ≤ ((2 * (Nat.bits i).length + 2 * (Nat.bits j).length + m + 6 : ℕ) : ENat) + 2 *
        (Nat.bits w.length).length + c_len + c_plain + c_kp := by
      have h_r_m : (Nat.bits r).length ≤ m := by
        rw [Nat.size_eq_bits_len]
        exact Nat.size_le.mpr hr_lt_2m
      have h : (2 * i.bits.length + 2 * j.bits.length + r.bits.length + 6) +
          2 * w.length.bits.length + c_len + c_plain + c_kp ≤
            (2 * i.bits.length + 2 * j.bits.length + m + 6) +
              2 * w.length.bits.length + c_len + c_plain + c_kp := by omega
      exact_mod_cast h
    _ = (m : ENat) + (c_kp + c_plain + c_len + 2 * (Nat.bits i).length +
        2 * (Nat.bits j).length + 6 + 2 * (Nat.bits w.length).length : ℕ) := by
      push_cast
      ring
    _ ≤ (m : ENat) + logSlack C1 M := by gcongr

/-- **Length-free slack arithmetic.**  The two internal slacks of the gap-counting
bridge fold into a single slack at the complexity scale `kx + delta + d`. -/
theorem gapCounting_slack_arithmetic_budget (U : Map) (hU : IsOptimalPrefixConditional U)
    (c1 c2 : ℕ) :
    ∃ c_out : ℕ, ∀ (delta d i j_min kx : ℕ) (x : BitString) (code : BitString),
      KPPlain U x = (kx : ENat) →
      (i : ENat) ≤ KPPlain U x + (delta : ENat) →
      (j_min : ENat) ≤ KP U x code + (d : ENat) →
      logSlack c2 (i + j_min) + logSlack c1 (kx + delta + d) <
        logSlack c_out (kx + delta + d) := by
  obtain ⟨cKP, hcKP⟩ := KP_le_KPPlain U hU
  obtain ⟨C, hC⟩ := logSlack_linear_bound c2 2 cKP
  refine ⟨C + c1 + 1, fun delta d i j_min kx x code hkx hi hj => ?_⟩
  have hi' : i ≤ kx + delta := by
    rw [hkx] at hi
    exact_mod_cast hi
  have hj' : j_min ≤ kx + cKP + d := by
    have h : (j_min : ENat) ≤ ((kx + cKP + d : ℕ) : ENat) := by
      refine hj.trans ?_
      have h1 : KP U x code ≤ (kx : ENat) + (cKP : ENat) := by
        refine (hcKP x code).trans ?_
        rw [hkx]
      calc KP U x code + (d : ENat) ≤ ((kx : ENat) + (cKP : ENat)) + (d : ENat) := by gcongr
        _ = ((kx + cKP + d : ℕ) : ENat) := by push_cast; ring
    exact_mod_cast h
  have hsum : i + j_min ≤ 2 * (kx + delta + d) + cKP := by omega
  have hfold : logSlack c2 (i + j_min) ≤ logSlack C (kx + delta + d) :=
    (logSlack_mono_right c2 hsum).trans (hC (kx + delta + d))
  have hlt : logSlack (C + c1) (kx + delta + d) < logSlack (C + c1 + 1) (kx + delta + d) := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits (kx + delta + d)).length)]
  have heq : logSlack C (kx + delta + d) + logSlack c1 (kx + delta + d)
      = logSlack (C + c1) (kx + delta + d) := logSlack_add_const _ _ _
  omega

/-- **Length-free tight gap-counting bridge.**  A realized optimality gap yields
many `(i, j)`-descriptions, with the counting loss measured at the complexity
scale `kx + delta + d`. -/
theorem manyIJDescriptions_of_realizedSetOptimalityGap_budget (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (delta d i j kx c_soi : ℕ),
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ slack : ℕ, slack ≤ logSlack c (kx + delta + d) ∧
        ManyIJDescriptions U x i j (delta - d - slack) := by
  obtain ⟨c1, hc1⟩ := gap_lowerBound_conditional_setComplexity_tight_budget U hU
  obtain ⟨c2, hc2⟩ := description_count_of_conditional_complexity_gap_length_free U hU
  obtain ⟨c3, hc3⟩ := gapCounting_slack_arithmetic_budget U hU c1 c2
  refine ⟨c3, fun A hA x delta d i j kx c_soi h_realized hdef hd => ?_⟩
  have hxA := h_realized.1
  have hi := h_realized.2.1
  have hj := h_realized.2.2.1
  have hkx := h_realized.2.2.2.2.1
  have hdelta_eq := h_realized.2.2.2.2.2
  set M := kx + delta + d with hM
  refine ⟨logSlack c3 M, le_rfl, ?_⟩
  set slack := logSlack c3 M with hslack
  by_cases h_zero : delta - d ≤ slack
  · rw [Nat.sub_eq_zero_of_le h_zero]
    exact manyIJDescriptions_zero U A hA x i j hxA hi hj
  · push Not at h_zero
    by_contra h_not_many_j
    obtain ⟨j_opt, hj_opt, hj_bound⟩ := card_le_of_deficiency hxA hdef
    set jm := min j j_opt with hjm_def
    have hcard_min : A.card ≤ 2 ^ jm := by
      rcases le_total j j_opt with hle | hle
      · rw [hjm_def, Nat.min_eq_left hle]; exact hj
      · rw [hjm_def, Nat.min_eq_right hle]; exact hj_opt
    have h_not_many : ¬ ManyIJDescriptions U x i jm (delta - d - slack) := fun h =>
      h_not_many_j (h.mono_j (min_le_left _ _))
    have hcount := hc2 A hA x i jm (delta - d - slack) kx hxA hi hcard_min hkx h_not_many
    have hgap := hc1 A hA x delta d i j kx c_soi h_realized hdef hd
    have hi_bound : (i : ENat) ≤ KPPlain U x + (delta : ENat) := by
      rw [← hkx]
      have : i ≤ kx + delta := by omega
      exact_mod_cast this
    have hjm_bound : (jm : ENat) ≤ KP U x (codedUniformOn A hA).code + (d : ENat) :=
      le_trans (by exact_mod_cast min_le_right j j_opt) hj_bound
    have harith := hc3 delta d i jm kx x (codedUniformOn A hA).code hkx.symm hi_bound hjm_bound
    rw [← hM, ← hslack] at harith
    have hchain : ((delta - d : ℕ) : ENat)
        ≤ (((delta - d - slack) + logSlack c2 (i + jm) + logSlack c1 M : ℕ) : ENat) := by
      refine hgap.trans ?_
      calc KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) + logSlack c1 M
          ≤ (((delta - d - slack) + logSlack c2 (i + jm) : ℕ) : ENat) + logSlack c1 M := by
            gcongr
            simpa using hcount
        _ = (((delta - d - slack) + logSlack c2 (i + jm) + logSlack c1 M : ℕ) : ENat) := by
            push_cast; ring
    have hnat : delta - d ≤ (delta - d - slack) + logSlack c2 (i + jm) + logSlack c1 M := by
      exact_mod_cast hchain
    omega

/-- **The tight deficiencies theorem at the complexity scale.**  Same conclusion
as `deficiencies_theorem_tight_of_optimal`, with every logarithmic loss measured
against `kx + delta + d` instead of `l(x) + delta + d`. -/
theorem deficiencies_theorem_tight_budget (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (delta d i j kx c_soi : ℕ),
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ (B : Finset BitString) (hB : B.Nonempty), x ∈ B ∧
        setComplexity U B hB + (delta - d : ℕ) ≤
          setComplexity U A hA + (logSlack c (kx + delta + d) : ENat) ∧
        SetOptimalityDeficiencyLe U B hB x (d + logSlack c (kx + delta + d)) := by
  obtain ⟨c1, hc1⟩ := manyIJDescriptions_of_realizedSetOptimalityGap_budget U hU
  obtain ⟨c2, hc2⟩ := improvingDescriptionsComplexity_length_free U hU
  refine ⟨c1 + 2 * c2 + 2, ?_⟩
  intro A hA x delta d i j kx c_soi h_realized h_def hd
  have hxA := h_realized.1
  have h_compA := h_realized.2.1
  have hj_card := h_realized.2.2.1
  have hkx := h_realized.2.2.2.2.1
  have hdelta_eq := h_realized.2.2.2.2.2
  have hkx_eq : KPPlain U x = (kx : ENat) := hkx.symm
  set M := kx + delta + d with hM
  obtain ⟨slack1, hslack1, h_many⟩ := hc1 A hA x delta d i j kx c_soi h_realized h_def hd
  set k := min (delta - d - slack1) i with hk_def
  have hk_le_i : k ≤ i := Nat.min_le_right _ _
  have h_many' : ManyIJDescriptions U x i j k :=
    ManyIJDescriptions.mono_k (Nat.min_le_left _ _) h_many
  have hkc : delta - d - slack1 ≤ i + 1 := ManyIJDescriptions_k_le_i_add_one h_many
  obtain ⟨B, hB, hxB, hcompB, hsizeB⟩ := hc2 x i j k h_many' hk_le_i
  set s := logSlack c2 (i + j) with hs
  -- The two visible parameters of the improvement step fit inside the complexity budget.
  have hij : i + j ≤ kx + delta := by omega
  have hsM : s ≤ logSlack c2 M := by
    rw [hs, hM]
    exact logSlack_mono_right c2 (by omega)
  have hslack1M : slack1 ≤ logSlack c1 M := hslack1
  -- The redistributed gap `delta - d` is paid for by the gap-counting slack `slack1`.
  have hdk : (delta - d) - k ≤ slack1 + 1 := by omega
  have hdeltak : delta - k ≤ d + slack1 + 1 := by omega
  have hcomb : logSlack c1 M + 2 * logSlack c2 M + 1 ≤ logSlack (c1 + 2 * c2 + 2) M := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits M).length)]
  refine ⟨B, hB, hxB, ?_, ?_⟩
  · refine le_trans (add_le_add hcompB (le_refl ((delta - d : ℕ) : ENat))) ?_
    rw [h_compA]
    norm_cast
    omega
  · refine setOptimalityDeficiencyLe_of_profile hxB hcompB hsizeB ?_
    rw [hkx_eq]
    have hnat : (i - k + s) + (j + s) ≤ kx + (d + logSlack (c1 + 2 * c2 + 2) M) := by omega
    exact_mod_cast hnat

/-- **The uniform-set realized gap at the complexity scale.**  Same conclusion as
`exists_realizedGap_uniformSet_of_stochastic`, with all bounds measured against
`kx + alpha + beta` (`kx = C_P(x)`) instead of `l(x) + alpha + beta`. -/
theorem exists_realizedGap_uniformSet_of_stochastic_budget
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx alpha beta : ℕ),
      KPPlain U x = (kx : ENat) →
      IsStochastic U x alpha beta →
      ∃ (A : Finset BitString) (hA : A.Nonempty) (delta i j d : ℕ),
        RealizedSetOptimalityGap U A hA x delta i j kx ∧
        CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d ∧
        d ≤ delta + c ∧
        i ≤ alpha + logSlack c (kx + alpha + beta) ∧
        d ≤ beta + logSlack c (kx + alpha + beta) ∧
        kx + delta + d ≤ 8 * (kx + alpha + beta) + c := by
  obtain ⟨c_gate, h_gate⟩ := levelSet_randomness_deficiency_le_gate U hU
  obtain ⟨c_comp, h_comp⟩ := levelSetModel_setComplexity_le U hU
  obtain ⟨c_lb, h_lb⟩ := levelSet_level_bound_of_KPPlain_le U hU
  obtain ⟨c_soi, h_soi⟩ := KPPlain_toNat_le_setComplexity_add_condKP U hU
  obtain ⟨C2, hC2⟩ := logSlack_fold_level c_comp c_lb
  obtain ⟨C3, hC3⟩ := logSlack_fold_level c_gate c_lb
  obtain ⟨b_lb, hb_lb⟩ := logSlack_le_add_const c_lb
  obtain ⟨b_comp, hb_comp⟩ := logSlack_le_add_const c_comp
  obtain ⟨b_gate, hb_gate⟩ := logSlack_le_add_const c_gate
  refine ⟨C2 + C3 + c_lb + c_soi + 3 * b_lb + 2 * b_comp + 2 * b_gate + 10, ?_⟩
  intro x kx alpha beta hkx h_stoch
  set W := C2 + C3 + c_lb + c_soi + 3 * b_lb + 2 * b_comp + 2 * b_gate + 10 with hW
  have hkx_val : HasPrefixComplexityValue U x kx := hkx.symm
  have hkx_toNat : (KPPlain U x).toNat = kx := by rw [hkx]; simp
  obtain ⟨P, h_prob, h_comp_P, h_def_P⟩ := h_stoch
  have h_mass_pos : P.mass x > 0 :=
    mass_pos_of_deficiencyLe_of_KP_ne_top h_def_P (KP_ne_top_of_optimal U hU x P.code)
  have h_mass_le1 : P.mass x ≤ 1 := mass_le_one_of_isProbability P h_prob x
  obtain ⟨k, h_k_lower, h_k_upper⟩ := exists_k_mass P x h_mass_pos h_mass_le1
  have h_supp : x ∈ P.support := by
    by_contra hx
    exact absurd (CodedFiniteDistribution.mass_eq_zero_of_not_mem_support P x hx)
      (ne_of_gt h_mass_pos)
  obtain ⟨d0, hd0_def, hd0_le⟩ := h_gate P x k h_prob h_supp h_k_lower h_k_upper beta h_def_P
  set A := levelSet P k with hA_def
  have hA : A.Nonempty := levelSet_nonempty_of_mass_ge P x k h_supp h_k_lower
  have hxA : x ∈ A := mem_levelSet h_supp h_k_lower
  obtain ⟨j, hj_lower, hj_upper⟩ := exists_card_dyadic_bracket A hA
  set i := (setComplexity U A hA).toNat with hi_def
  set delta := i + j - kx with hdelta_def
  set d := min d0 (delta + c_soi) with hd_def
  have hi_eq : setComplexity U A hA = (i : ENat) :=
    (ENat.coe_toNat (setComplexity_ne_top_of_optimal U hU A hA)).symm
  have h_realized : RealizedSetOptimalityGap U A hA x delta i j kx :=
    ⟨hxA, hi_eq, hj_upper, hj_lower, hkx_val, rfl⟩
  -- The `delta + c_soi` deficiency bound from Symmetry of Information.
  have h_def_soi :
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x (delta + c_soi) := by
    unfold CodedFiniteDistribution.DeficiencyLe
    have h_mass : (codedUniformOn A hA).mass x = ((A.card : ℝ≥0∞)⁻¹) :=
      codedUniformOn_mass_of_mem _ _ _ hxA
    rw [h_mass]
    have h_soi_bound := h_soi A hA x hxA
    rw [hkx_toNat] at h_soi_bound
    have h_i : (setComplexity U A hA).toNat = i := rfl
    rw [h_i] at h_soi_bound
    have h_kp : (KP U x (codedUniformOn A hA).code).toNat + c_soi + delta ≥ j := by
      simp only [hdelta_def]
      omega
    have h4 : ((2 : ℝ≥0∞) ^ j)⁻¹ ≤ (A.card : ℝ≥0∞)⁻¹ := by
      apply ENNReal.inv_le_inv.mpr
      exact_mod_cast hj_upper
    have hkp_eq : complexityWeight (KP U x (codedUniformOn A hA).code) = (2 : ℝ≥0∞)⁻¹ ^
        (KP U x (codedUniformOn A hA).code).toNat := by
      have : KP U x (codedUniformOn A hA).code =
          ((KP U x (codedUniformOn A hA).code).toNat : ENat) :=
        (ENat.coe_toNat (KP_ne_top_of_optimal U hU x _)).symm
      rw [this]
      rfl
    rw [hkp_eq]
    have h1_inv : (2 : ℝ≥0∞)⁻¹ ^ (KP U x (codedUniformOn A hA).code).toNat =
        ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ := by
      rw [ENNReal.inv_pow]
    rw [h1_inv]
    have h2_pow : (2 : ℝ≥0∞) ^ j ≤ (2 : ℝ≥0∞) ^ (delta + c_soi) * (2 : ℝ≥0∞) ^
        (KP U x (codedUniformOn A hA).code).toNat := by
      rw [← pow_add]
      apply pow_le_pow_right' (by norm_num)
      omega
    have h4_inv :
        ((2 : ℝ≥0∞) ^ (delta + c_soi) * (2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ =
        ((2 : ℝ≥0∞) ^ (delta + c_soi))⁻¹ *
        ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ :=
      ENNReal.mul_inv (by norm_num) (by norm_num)
    have h6 : ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ ≤ (2 : ℝ≥0∞) ^
        (delta + c_soi) * ((2 : ℝ≥0∞) ^ j)⁻¹ := by
      calc ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹
        _ = 1 * ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ := by rw [one_mul]
        _ = ((2 : ℝ≥0∞) ^ (delta + c_soi) * ((2 : ℝ≥0∞) ^ (delta + c_soi))⁻¹) *
            ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ := by
          have : (2 : ℝ≥0∞) ^ (delta + c_soi) *
              ((2 : ℝ≥0∞) ^ (delta + c_soi))⁻¹ = 1 :=
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
          rw [this]
        _ = (2 : ℝ≥0∞) ^ (delta + c_soi) *
            (((2 : ℝ≥0∞) ^ (delta + c_soi))⁻¹ *
              ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹) := by
                rw [mul_assoc]
        _ = (2 : ℝ≥0∞) ^ (delta + c_soi) *
            ((2 : ℝ≥0∞) ^ (delta + c_soi) *
              (2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ := by
                rw [h4_inv]
        _ ≤ (2 : ℝ≥0∞) ^ (delta + c_soi) * ((2 : ℝ≥0∞) ^ j)⁻¹ := by gcongr
    exact le_trans h6 (mul_le_mul_right h4 _)
  have h_def_d : CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d := by
    by_cases h_min : d0 ≤ delta + c_soi
    · rw [hd_def, Nat.min_eq_left h_min]
      exact hd0_def
    · rw [hd_def, Nat.min_eq_right (le_of_not_ge h_min)]
      exact h_def_soi
  -- The level `k` is controlled at the complexity scale.
  have hk_bd : k ≤ kx + beta + logSlack c_lb kx := by
    have h := h_lb P x kx beta k (le_of_eq hkx) h_def_P h_k_upper
    have hcl : c_lb ≤ logSlack c_lb kx := by unfold logSlack; omega
    omega
  -- `i ≤ alpha + O(log)`.
  have h_i_raw : i ≤ alpha + logSlack c_comp k := by
    have h1 : setComplexity U A hA ≤ (alpha : ENat) + (logSlack c_comp k : ENat) := by
      refine le_trans (h_comp P k hA) ?_
      gcongr
    rw [hi_eq] at h1
    exact_mod_cast h1
  have hfoldC2 : logSlack c_comp k ≤ logSlack C2 (kx + alpha + beta) := hC2 kx alpha beta k hk_bd
  have hfoldC3 : logSlack c_gate k ≤ logSlack C3 (kx + alpha + beta) := hC3 kx alpha beta k hk_bd
  have hfoldW : logSlack C2 (kx + alpha + beta) + logSlack C3 (kx + alpha + beta)
      ≤ logSlack W (kx + alpha + beta) := by
    have h1 : logSlack C2 (kx + alpha + beta) + logSlack C3 (kx + alpha + beta)
        = logSlack (C2 + C3) (kx + alpha + beta) := logSlack_add_const _ _ _
    have h2 : logSlack (C2 + C3) (kx + alpha + beta) ≤ logSlack W (kx + alpha + beta) :=
      logSlack_mono_left (by omega) _
    omega
  have h_i_bound : i ≤ alpha + logSlack W (kx + alpha + beta) := by omega
  have h_d_bound : d ≤ beta + logSlack W (kx + alpha + beta) := by
    have hd_le0 : d ≤ d0 := Nat.min_le_left _ _
    have : d0 ≤ beta + logSlack c_gate k := hd0_le
    omega
  -- Linear control of the visible budget.
  have hj_k : j ≤ k + 1 := by
    have hcard_k : A.card ≤ 2 ^ k := by
      have h := levelSet_card_le P k h_prob
      exact_mod_cast h
    have hj2 : 2 ^ j ≤ 2 * A.card := by
      have h := hj_lower
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)] at h
      have h' : (2 : ℝ≥0∞) ^ j ≤ ((2 * A.card : ℕ) : ℝ≥0∞) := by
        push_cast; simpa [mul_comm] using h
      exact_mod_cast h'
    have hpow : 2 ^ j ≤ 2 ^ (k + 1) := by
      calc 2 ^ j ≤ 2 * A.card := hj2
        _ ≤ 2 * 2 ^ k := by gcongr
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow
  -- Linear (slack-free) control of the level and of the three parameters.
  have hk_lin : k ≤ 2 * kx + beta + b_lb := by
    have := hb_lb kx
    omega
  have hi_lin : i ≤ alpha + 2 * kx + beta + b_lb + b_comp := by
    have := hb_comp k
    omega
  have hd_lin : d ≤ 2 * beta + 2 * kx + b_lb + b_gate := by
    have hd_le0 : d ≤ d0 := Nat.min_le_left _ _
    have h1 : d0 ≤ beta + logSlack c_gate k := hd0_le
    have := hb_gate k
    omega
  have h_linear : kx + delta + d ≤ 8 * (kx + alpha + beta) + W := by
    have hdelta_le : delta ≤ i + j := by simp only [hdelta_def]; omega
    omega
  have hd_delta : d ≤ delta + W := by omega
  exact ⟨A, hA, delta, i, j, d, h_realized, h_def_d, hd_delta,
    by omega, h_d_bound, h_linear⟩

/-- **Theorem 3 at the complexity scale.**  An arbitrary stochasticity witness is
converted into an optimal *finite-set* witness, with the logarithmic loss
measured against `C_P(x) + alpha + beta` instead of `l(x) + alpha + beta`. -/
theorem stochasticity_to_optimal_set_budget (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx alpha beta : ℕ),
      KPPlain U x = (kx : ENat) →
      IsStochastic U x alpha beta →
      IsOptimalSetStochastic U x (alpha + logSlack c (kx + alpha + beta))
        (beta + logSlack c (kx + alpha + beta)) := by
  obtain ⟨c_def, hc_def⟩ := deficiencies_theorem_tight_budget U hU
  obtain ⟨c_br, hc_br⟩ := exists_realizedGap_uniformSet_of_stochastic_budget U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c_def 8 c_br
  refine ⟨max (c_br + C0) (c_def + c_br + 1) + 1, ?_⟩
  intro x kx alpha beta hkx hst
  obtain ⟨A, hA, delta, i, j, d, hgap, hdef, hdd, hi, hd, hlin⟩ := hc_br x kx alpha beta hkx hst
  obtain ⟨B, hB, hxB, hcompB, hoptB⟩ := hc_def A hA x delta d i j kx c_br hgap hdef hdd
  have hlogSlack : logSlack c_def (kx + delta + d) ≤ logSlack C0 (kx + alpha + beta) :=
    le_trans (logSlack_mono_right _ hlin) (hC0 _)
  have hcompA : setComplexity U A hA = (i : ENat) := hgap.2.1
  have hslack : logSlack c_br (kx + alpha + beta) + logSlack C0 (kx + alpha + beta)
      ≤ logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (kx + alpha + beta) := by
    have h1 : logSlack c_br (kx + alpha + beta) + logSlack C0 (kx + alpha + beta)
        ≤ logSlack (c_br + C0 + 1) (kx + alpha + beta) := by
      unfold logSlack; ring_nf; omega
    exact le_trans h1 (logSlack_mono_left (Nat.succ_le_succ (le_max_left _ _)) _)
  refine ⟨B, hB, hxB, ?_, ?_⟩
  · rw [hcompA] at hcompB
    have hcompB' : setComplexity U B hB ≤ (i : ENat) + (logSlack c_def (kx + delta + d) : ENat) :=
      le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) hcompB
    refine le_trans hcompB' ?_
    have hnat : i + logSlack c_def (kx + delta + d)
        ≤ alpha + logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (kx + alpha + beta) := by
      omega
    exact_mod_cast hnat
  · refine hoptB.mono_beta ?_
    omega

/-- **Budget-scale optimal-set conversion.**  If a complexity budget `m` bounds
`K(x)` and both stochasticity parameters, then an `(alpha, beta)`-stochasticity
witness yields an optimal finite-set witness with slack `logSlack c m`; no length
appears. -/
theorem stochasticity_to_optimal_set_of_budget
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c, ∀ (x : BitString) (m alpha beta : ℕ),
      KPPlain U x ≤ (m : ENat) →
      alpha ≤ m →
      beta ≤ m →
      IsStochastic U x alpha beta →
      IsOptimalSetStochastic U x
        (alpha + logSlack c m)
        (beta + logSlack c m) := by
  obtain ⟨c0, hc0⟩ := stochasticity_to_optimal_set_budget U hU
  obtain ⟨C, hC⟩ := logSlack_linear_bound c0 3 0
  refine ⟨C, fun x m alpha beta hm halpha hbeta hst => ?_⟩
  obtain ⟨kx, hkx_raw⟩ := ENat.ne_top_iff_exists.mp (KPPlain_ne_top_of_optimal U hU x)
  have hkx : KPPlain U x = (kx : ENat) := hkx_raw.symm
  have hkxm : kx ≤ m := by
    rw [hkx] at hm
    exact_mod_cast hm
  have hstoch := hc0 x kx alpha beta hkx hst
  have hfold : logSlack c0 (kx + alpha + beta) ≤ logSlack C m :=
    (logSlack_mono_right c0 (by omega : kx + alpha + beta ≤ 3 * m + 0)).trans (hC m)
  exact (hstoch.mono_alpha (by omega)).mono_beta (by omega)

/-- **The budgeted forward plain corner, `beta ≤ baseBudget` regime.**  An
`(alpha, beta)`-stochasticity witness for `x` yields an ordinary plain `(i, j)`
description with the budget-scale slack `logSlack c baseBudget`:

* `i ≤ alpha + logSlack c baseBudget`,
* `i + j ≤ C(x) + beta + logSlack c baseBudget`.

Unlike `budgeted_stochasticity_to_plain_corner_of_length_le` no hypothesis on the
length `l(x)` is needed: the whole §3 chain is available at the complexity scale
(`stochasticity_to_optimal_set_budget`).  The parameter `alpha` needs no bound
(the `alpha`-reduction removes it); only `beta` must fit the budget, since the
level of `x` inside its own witness can be as large as `K(x) + beta`. -/
theorem budgeted_stochasticity_to_plain_corner_of_beta_le
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      beta ≤ baseBudget →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨cR, hR⟩ := isStochastic_alpha_le_budget V U hV hU
  obtain ⟨cOpt, hOpt⟩ := stochasticity_to_optimal_set_budget U hU
  obtain ⟨cProf, hProf⟩ := isOptimalSetStochastic_imp_profile U hU
  obtain ⟨cBr, hBr⟩ := inPlainDescriptionProfile_of_inDescriptionProfile V U hV hU
  obtain ⟨cKP, hKP⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨bR, hbR⟩ := logSlack_le_add_const cR
  obtain ⟨bOpt, hbOpt⟩ := logSlack_le_add_const cOpt
  set constP := cBits + cKP with hconstP
  obtain ⟨COpt, hCOpt⟩ := logSlack_linear_bound cOpt 6 (constP + bR)
  obtain ⟨CProf, hCProf⟩ := logSlack_linear_bound cProf 25 (3 * bOpt + 4 * constP + 4 * bR + 4)
  set C := COpt + CProf + 2 + cR + cBits + cKP + cBr + 1 with hCdef
  refine ⟨C, fun x kx N alpha beta hkx hkxN hbetaN hstoch => ?_⟩
  -- `alpha`-reduction: cap the complexity parameter at `kx + O(log kx)`.
  have hstoch'' : IsStochastic U x (min alpha (kx + logSlack cR kx)) beta :=
    hR x kx kx alpha beta hkx (le_refl kx) hstoch
  set alpha'' := min alpha (kx + logSlack cR kx) with halpha''
  have halpha''_le : alpha'' ≤ alpha := min_le_left _ _
  have halpha''_bud : alpha'' ≤ kx + logSlack cR kx := min_le_right _ _
  -- the exact prefix complexity of `x`.
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp (KPPlain_ne_top_of_optimal U hU x)
  have hp_eq : KPPlain U x = (p : ENat) := hp.symm
  have hbits_self : (Nat.bits kx).length ≤ kx := length_natBits_le_self kx
  have hp_bd : p ≤ kx + 2 * (Nat.bits kx).length + cBits + cKP := by
    have h3 : (p : ENat) ≤ ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) := by
      calc (p : ENat) = KPPlain U x := hp
        _ ≤ (kx : ENat) + KPPlain U (Nat.bits kx) + (cKP : ENat) := hKP x kx hkx
        _ ≤ (kx : ENat) + ((2 * (Nat.bits kx).length + cBits : ℕ) : ENat) + (cKP : ENat) := by
              gcongr; exact hBits (Nat.bits kx)
        _ = ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) := by push_cast; ring
    exact_mod_cast h3
  -- optimal finite-set model at the complexity scale.
  have hopt : IsOptimalSetStochastic U x
      (alpha'' + logSlack cOpt (p + alpha'' + beta))
      (beta + logSlack cOpt (p + alpha'' + beta)) :=
    hOpt x p alpha'' beta hp_eq hstoch''
  set sOpt := logSlack cOpt (p + alpha'' + beta) with hsOpt
  set A1 := alpha'' + sOpt with hA1
  set B1 := beta + sOpt with hB1
  set j := (p + B1) - A1 with hj
  have harith : KPPlain U x + (B1 : ENat) ≤ (A1 : ENat) + (j : ENat) := by
    rw [hp_eq]
    have hnat : p + B1 ≤ A1 + j := by omega
    exact_mod_cast hnat
  have hprofU : InDescriptionProfile U x (A1 + logSlack cProf (A1 + B1 + j)) (j + 1) :=
    hProf x A1 B1 j hopt harith
  set iPre := A1 + logSlack cProf (A1 + B1 + j) with hiPre
  have hplain : InPlainDescriptionProfile V x (iPre + cBr) (j + 1) :=
    hBr x iPre (j + 1) hprofU
  -- All internal parameters are controlled by the visible budget `N`.
  have hbits_slack : 2 * (Nat.bits kx).length ≤ logSlack 2 N := by
    have h1 : 2 * (Nat.bits kx).length ≤ logSlack 2 kx := by unfold logSlack; omega
    exact h1.trans (logSlack_mono_right 2 hkxN)
  have hpN : p ≤ 3 * N + constP := by
    have := hbits_self
    omega
  have halphaN : alpha'' ≤ 2 * N + bR := by
    have h1 : logSlack cR kx ≤ kx + bR := hbR kx
    omega
  have hsOptN : sOpt ≤ logSlack COpt N := by
    have hle : p + alpha'' + beta ≤ 6 * N + (constP + bR) := by omega
    exact (logSlack_mono_right cOpt hle).trans (hCOpt N)
  have hsOpt_lin : sOpt ≤ 6 * N + (constP + bR) + bOpt := by
    have h1 : sOpt ≤ (p + alpha'' + beta) + bOpt := hbOpt _
    omega
  have hABj : A1 + B1 + j ≤ 25 * N + (3 * bOpt + 4 * constP + 4 * bR + 4) := by
    have hj_le : j ≤ p + B1 := by omega
    omega
  have hprofN : logSlack cProf (A1 + B1 + j) ≤ logSlack CProf N :=
    (logSlack_mono_right cProf hABj).trans (hCProf N)
  have hcR_le : logSlack cR kx ≤ logSlack cR N := logSlack_mono_right cR hkxN
  -- Fold every slack into the single visible-budget slack.
  have hMaster : logSlack COpt N + logSlack CProf N + logSlack 2 N + logSlack cR N
      + (cBits + cKP + cBr + 1) ≤ logSlack C N := by
    calc logSlack COpt N + logSlack CProf N + logSlack 2 N + logSlack cR N
            + (cBits + cKP + cBr + 1)
        = logSlack (COpt + CProf) N + logSlack 2 N + logSlack cR N
            + (cBits + cKP + cBr + 1) := by rw [logSlack_add_const]
      _ = logSlack (COpt + CProf + 2) N + logSlack cR N + (cBits + cKP + cBr + 1) := by
          rw [logSlack_add_const]
      _ = logSlack (COpt + CProf + 2 + cR) N + (cBits + cKP + cBr + 1) := by
          rw [logSlack_add_const]
      _ ≤ logSlack (COpt + CProf + 2 + cR + (cBits + cKP + cBr + 1)) N :=
          logSlack_add_nat_le _ _ _
      _ ≤ logSlack C N := logSlack_mono_left (by omega) N
  refine ⟨iPre + cBr, j + 1, hplain, ?_, ?_⟩
  · omega
  · omega

/-- **The forward plain corner with no restriction on the deficiency parameter.**
For every stochasticity witness the plain `(i, j)` description exists with a
slack logarithmic in `baseBudget + beta`:

* `i ≤ alpha + logSlack c (baseBudget + beta)`,
* `i + j ≤ C(x) + beta + logSlack c (baseBudget + beta)`.

No hypothesis on `alpha`, on `beta`, or on the length `l(x)` is needed; only the
complexity budget `C(x) ≤ baseBudget`.  This isolates exactly what separates the
proved chain from `BudgetedPlainProfileCornerStatement`: the latter asks for the
slack `logSlack c baseBudget`, i.e. for the residual `O(log beta)` term to be
removed.  Whenever `beta ≤ baseBudget` the two coincide up to the constant, which
is `budgeted_stochasticity_to_plain_corner_of_beta_le`. -/
theorem budgeted_stochasticity_to_plain_corner_of_budget_add_beta
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c (baseBudget + beta) ∧
        i + j ≤ kx + beta + logSlack c (baseBudget + beta) := by
  obtain ⟨c, hc⟩ := budgeted_stochasticity_to_plain_corner_of_beta_le V U hV hU
  exact ⟨c, fun x kx N alpha beta hkx hkxN hstoch =>
    hc x kx (N + beta) alpha beta hkx (by omega) (by omega) hstoch⟩

/-- **The residual term made explicit.**  Splitting the slack of
`budgeted_stochasticity_to_plain_corner_of_budget_add_beta` shows that the
budget-scale corner holds up to a single additive `logSlack c beta`. -/
theorem budgeted_stochasticity_to_plain_corner_add_logSlack_beta
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget + logSlack c beta ∧
        i + j ≤ kx + beta + logSlack c baseBudget + logSlack c beta := by
  obtain ⟨c, hc⟩ := budgeted_stochasticity_to_plain_corner_of_budget_add_beta V U hV hU
  refine ⟨c, fun x kx N alpha beta hkx hkxN hstoch => ?_⟩
  obtain ⟨i, j, hprof, hi, hij⟩ := hc x kx N alpha beta hkx hkxN hstoch
  have hsplit : logSlack c (N + beta) ≤ logSlack c N + logSlack c beta :=
    logSlack_add_le c N beta
  exact ⟨i, j, hprof, by omega, by omega⟩

end Kolmogorov
