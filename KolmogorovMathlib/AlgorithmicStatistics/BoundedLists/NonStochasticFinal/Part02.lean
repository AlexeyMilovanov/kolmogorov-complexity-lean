import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyTest
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.NonStochasticFinal.Part01

/-!
# Non-stochastic strings: the counting statements

The three propositions of VS40 §5 that the standard-block construction proves.

`prop_dilemma` states the dilemma of `Part01` in the prefix form the rest of the section uses.
`prop_information_rare` bounds the a priori mass of the strings carrying much information
about the high bits of `Ω`.  Combining them, `prop_nonstochastic_counting_improved` bounds
`nonStochasticAprioriMass`, the total a priori mass of the length-`n` strings that are not
`(alpha, logSlack C n)`-stochastic.
-/

namespace Kolmogorov

open CodedFiniteDistribution
open Nat.Partrec (Code)
open scoped ENNReal

/-- Proposition `prop:dilemma`.  Mutual information is stated directly in the
prefix form needed by `prop_information_rare`:
`KP(x | Omega_n) + i - O(log n) ≤ KP(x)`. -/
theorem prop_dilemma
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (n i : ℕ),
      x.length = n →
      i ≤ n →
      IsStochastic U x
          (i + logSlack C n) (logSlack C n) ∨
        KP U x (omegaFixedCode c n) +
            ((i - logSlack C n : ℕ) : ENat) ≤
          KPPlain U x := by
  obtain ⟨Clen, hlen⟩ :=
    plainK_le_length V hV
  obtain ⟨Cstoch, hstoch⟩ :=
    stochastic_of_standardBlock_at_plainK
      V U hV hU c hc
  obtain ⟨Cinfo, hinfo⟩ :=
    KP_information_of_standardBlock_additive
      V U hV hU c hc
  obtain ⟨Ctransport, htransport⟩ :=
    KP_omegaPrefix_condition_transport
      V U hV hU c hc Clen
  obtain ⟨CinfoN, hinfoN⟩ :=
    logSlack_linear_bound Cinfo 1 Clen
  let Cgap := CinfoN + Ctransport
  let C := Cgap + Cstoch
  refine ⟨C, fun x n i hn _hi => ?_⟩
  have hplainFinite : plainK V x ≠ ⊤ := by
    have hbound := hlen x
    refine ne_top_of_le_ne_top ?_ hbound
    rw [← Nat.cast_add]
    exact ENat.natCast_ne_top _
  obtain ⟨m, hmRaw⟩ :=
    ENat.ne_top_iff_exists.mp hplainFinite
  have hm : plainK V x = (m : ENat) :=
    hmRaw.symm
  have hmn : m ≤ n + Clen := by
    have hbound := hlen x
    rw [hm] at hbound
    change (m : ENat) ≤
      (x.length : ENat) + (Clen : ENat) at hbound
    rw [hn] at hbound
    exact_mod_cast hbound
  have hxCompleted :
      x ∈ completedBoundedOutput c m := by
    apply
      (mem_completedBoundedOutput_iff_plainK_le
        hc m x).2
    rw [hm]
  obtain ⟨r, hxBlock⟩ :=
    exists_standardBlock_of_mem_completed
      c m x hxCompleted
  let gap := m - r
  have hgapM : gap ≤ m := by
    dsimp [gap]
    omega
  have hinfoM :
      KP U x ((omegaFixedCode c m).take gap) +
          (gap : ENat) ≤
        KPPlain U x + (logSlack Cinfo m : ENat) := by
    simpa [gap] using hinfo x m r hxBlock
  have htransportM :
      KP U x (omegaFixedCode c n) ≤
        KP U x ((omegaFixedCode c m).take gap) +
          (logSlack Ctransport n : ENat) :=
    htransport x n m gap hgapM hmn
  have hinfoSlack :
      logSlack Cinfo m ≤ logSlack CinfoN n := by
    calc
      logSlack Cinfo m
          ≤ logSlack Cinfo (n + Clen) :=
        logSlack_mono_right Cinfo hmn
      _ = logSlack Cinfo (1 * n + Clen) := by
        rw [one_mul]
      _ ≤ logSlack CinfoN n := hinfoN n
  have hgapSlack :
      logSlack CinfoN n +
          logSlack Ctransport n =
        logSlack Cgap n := by
    dsimp [Cgap]
    unfold logSlack
    ring
  have hinfoAtN :
      KP U x (omegaFixedCode c n) + (gap : ENat) ≤
        KPPlain U x + (logSlack Cgap n : ENat) := by
    calc
      KP U x (omegaFixedCode c n) + (gap : ENat)
          ≤ (KP U x ((omegaFixedCode c m).take gap) +
              (logSlack Ctransport n : ENat)) +
              (gap : ENat) := by
            gcongr
      _ = (KP U x ((omegaFixedCode c m).take gap) +
              (gap : ENat)) +
              (logSlack Ctransport n : ENat) := by
            abel
      _ ≤ (KPPlain U x +
              (logSlack Cinfo m : ENat)) +
              (logSlack Ctransport n : ENat) := by
            gcongr
      _ ≤ (KPPlain U x +
              (logSlack CinfoN n : ENat)) +
              (logSlack Ctransport n : ENat) := by
            gcongr
      _ = KPPlain U x +
              (logSlack Cgap n : ENat) := by
            rw [← hgapSlack]
            push_cast
            abel
  by_cases hsmall :
      gap ≤ i + logSlack Cgap n
  · left
    have hs :=
      hstoch x n m r hn hm hxBlock
    refine (hs.mono_alpha ?_).mono_beta ?_
    · have hslack :
          logSlack C n =
            logSlack Cgap n +
              logSlack Cstoch n := by
        dsimp [C]
        unfold logSlack
        ring
      omega
    · exact logSlack_mono_left
        (show Cstoch ≤ C by
          dsimp [C]
          omega) n
  · right
    apply ENat_add_truncated_le_of_add_gap
      (KP U x (omegaFixedCode c n))
      (KPPlain U x) i gap
      (logSlack Cgap n) (logSlack C n)
      hinfoAtN
    omega

/-- Proposition `prop:information-rare`.  The mass is the prefix a priori mass
of the fixed optimal prefix machine.  Its coding-theorem normalization costs a
single uniform factor `2^C`, displayed on the left.  The selected strings are
exactly those satisfying `KP(x | u) + d ≤ KP(x)`. -/
theorem prop_information_rare
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (u : BitString) (d : ℕ),
      (2 : ℝ≥0∞)⁻¹ ^ C *
          (∑' x : BitString,
            if KP U x u + (d : ENat) ≤ KPPlain U x
            then aprioriMeasure U x []
            else 0)
        ≤ (2 : ℝ≥0∞)⁻¹ ^ d := by
  obtain ⟨C, hC⟩ :=
    aprioriMeasure_le_complexityWeight_optimal hU
      hU.isPrefixDecompressor
  refine ⟨C, fun u d => ?_⟩
  calc
    (2 : ℝ≥0∞)⁻¹ ^ C *
          (∑' x : BitString,
            if KP U x u + (d : ENat) ≤ KPPlain U x
            then aprioriMeasure U x []
            else 0)
        =
          ∑' x : BitString,
            (2 : ℝ≥0∞)⁻¹ ^ C *
              (if KP U x u + (d : ENat) ≤ KPPlain U x
              then aprioriMeasure U x []
              else 0) := by
            rw [ENNReal.tsum_mul_left]
    _ ≤
          ∑' x : BitString,
            if KP U x u + (d : ENat) ≤ KPPlain U x
            then complexityWeight (KPPlain U x)
            else 0 := by
          apply ENNReal.tsum_le_tsum
          intro x
          split_ifs
          · exact hC x []
          · simp
    _ ≤
          ∑' x : BitString,
            (2 : ℝ≥0∞)⁻¹ ^ d *
              complexityWeight (KP U x u) := by
          apply ENNReal.tsum_le_tsum
          intro x
          split_ifs with hx
          · calc
              complexityWeight (KPPlain U x)
                  ≤ complexityWeight (KP U x u + (d : ENat)) :=
                    complexityWeight_le_of_le hx
              _ = complexityWeight (KP U x u) *
                    (2 : ℝ≥0∞)⁻¹ ^ d :=
                    complexityWeight_add_nat _ _
              _ = (2 : ℝ≥0∞)⁻¹ ^ d *
                    complexityWeight (KP U x u) := by ring
          · exact zero_le
    _ =
          (2 : ℝ≥0∞)⁻¹ ^ d *
            (∑' x : BitString, complexityWeight (KP U x u)) := by
          rw [ENNReal.tsum_mul_left]
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ d * 1 := by
          gcongr
          exact KP_kraft_sum_le_one U hU.isPrefixDecompressor u
    _ = (2 : ℝ≥0∞)⁻¹ ^ d := by rw [mul_one]

/-- The total a priori mass, for the conditional map `U` with empty condition, of the
strings of length `n` that are not `(alpha, beta)`-stochastic:
`∑' x, if x.length = n ∧ ¬ IsStochastic U x alpha beta then aprioriMeasure U x [] else 0`. -/
noncomputable def nonStochasticAprioriMass
    (U : Map) (n alpha beta : ℕ) : ℝ≥0∞ := by
  classical
  exact
    ∑' x : BitString,
      if x.length = n ∧ ¬ IsStochastic U x alpha beta
      then aprioriMeasure U x []
      else 0

/-- The a priori mass of the strings of length `n` that are not `(alpha, logSlack C n)`-stochastic
is at most `2 ^ (logSlack C n) * 2 ^ (-alpha)`, an improvement of the counting bound for
non-stochastic strings. -/
theorem prop_nonstochastic_counting_improved
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (n alpha : ℕ),
      (2 : ℝ≥0∞)⁻¹ ^ (logSlack C n) *
          nonStochasticAprioriMass U n alpha (logSlack C n)
        ≤ (2 : ℝ≥0∞)⁻¹ ^ alpha := by
  obtain ⟨Cdil, hdil⟩ := prop_dilemma V U hV hU c hc
  obtain ⟨Crare, hrare⟩ := prop_information_rare U hU
  obtain ⟨Csing, hsing⟩ := isStochastic_singleton_length U hU
  set Dc := Cdil + Csing with hDc
  refine ⟨2 * Dc + Crare + 1, fun n alpha => ?_⟩
  set C := 2 * Dc + Crare + 1 with hCdef
  set S := logSlack C n with hSdef
  set SD := logSlack Dc n with hSDdef
  set μ := nonStochasticAprioriMass U n alpha S with hμdef
  -- `logSlack` is monotone in its constant, so the smaller-constant slacks fit
  -- under `SD ≤ S`.
  have hCdil_SD : logSlack Cdil n ≤ SD := by
    rw [hSDdef]; exact logSlack_mono_left (by omega) n
  have hCsing_SD : logSlack Csing n ≤ SD := by
    rw [hSDdef]; exact logSlack_mono_left (by omega) n
  have hSD_le_S : SD ≤ S := by
    rw [hSDdef, hSdef]; exact logSlack_mono_left (by omega) n
  have hbig : 2 * SD + Crare ≤ S := by
    rw [hSDdef, hSdef, hCdef]; unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length),
      Nat.zero_le (Crare * (Nat.bits n).length)]
  -- The dilemma, re-expressed at the combined constant `Dc`.
  have hdilD : ∀ (x : BitString), x.length = n → ∀ i, i ≤ n →
      IsStochastic U x (i + SD) SD ∨
        KP U x (omegaFixedCode c n) + ((i - SD : ℕ) : ENat) ≤ KPPlain U x := by
    intro x hx i hi
    rcases hdil x n i hx hi with hst | hkp
    · left
      exact (hst.mono_alpha (by omega)).mono_beta hCdil_SD
    · right
      have hsub : ((i - SD : ℕ) : ENat) ≤ ((i - logSlack Cdil n : ℕ) : ENat) := by
        exact_mod_cast (show i - SD ≤ i - logSlack Cdil n by omega)
      exact le_trans (add_le_add le_rfl hsub) hkp
  -- Every `n`-bit string is stochastic at the combined constant `Dc`.
  have hsingD : ∀ (x : BitString), x.length = n → IsStochastic U x (n + SD) 0 := by
    intro x hx
    exact (hsing x n hx).mono_alpha (by omega)
  by_cases hcase1 : alpha ≤ S
  · -- Small `alpha`: the mass is at most `1` (Kraft), and `2⁻¹^S ≤ 2⁻¹^alpha`.
    have hμ1 : μ ≤ 1 := by
      rw [hμdef]; unfold nonStochasticAprioriMass
      refine le_trans (ENNReal.tsum_le_tsum (fun x => ?_))
        (tsum_aprioriMeasure_le_one U [] hU.isPrefixMachine)
      split_ifs
      · exact le_rfl
      · exact zero_le
    calc (2 : ℝ≥0∞)⁻¹ ^ S * μ
        ≤ (2 : ℝ≥0∞)⁻¹ ^ S * 1 := by gcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ S := mul_one _
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ alpha :=
          pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two) hcase1
  · push Not at hcase1
    by_cases hcase2b : n + SD < alpha
    · -- `alpha` beyond `n + O(log n)`: every `n`-bit string is stochastic, so the
      -- non-stochastic mass is zero.
      have hμ0 : μ = 0 := by
        rw [hμdef]; unfold nonStochasticAprioriMass
        refine ENNReal.tsum_eq_zero.mpr (fun x => ?_)
        by_cases hcond : x.length = n ∧ ¬ IsStochastic U x alpha S
        · exfalso
          obtain ⟨hxn, hnstoch⟩ := hcond
          exact hnstoch
            (((hsingD x hxn).mono_alpha (by omega)).mono_beta (Nat.zero_le S))
        · rw [if_neg hcond]
      rw [hμ0, mul_zero]
      exact zero_le
    · -- Intermediate `alpha`: use the dilemma at `i₀ = alpha - SD ≤ n`, then the
      -- information-rarity bound.
      push Not at hcase2b
      set i₀ := alpha - SD with hi0def
      set d' := i₀ - SD with hd'def
      have hi0_le_n : i₀ ≤ n := by rw [hi0def]; omega
      set ν := ∑' x : BitString,
          if KP U x (omegaFixedCode c n) + (d' : ENat) ≤ KPPlain U x
          then aprioriMeasure U x [] else 0 with hνdef
      have hμν : μ ≤ ν := by
        rw [hμdef]; unfold nonStochasticAprioriMass
        rw [hνdef]
        refine ENNReal.tsum_le_tsum (fun x => ?_)
        by_cases hc1 : x.length = n ∧ ¬ IsStochastic U x alpha S
        · rw [if_pos hc1]
          have hcondB :
              KP U x (omegaFixedCode c n) + (d' : ENat) ≤ KPPlain U x := by
            obtain ⟨hxn, hnstoch⟩ := hc1
            rcases hdilD x hxn i₀ hi0_le_n with hst | hkp
            · exfalso
              apply hnstoch
              have hi0SD : i₀ + SD = alpha := by rw [hi0def]; omega
              rw [hi0SD] at hst
              exact hst.mono_beta hSD_le_S
            · rw [hd'def]; exact hkp
          exact le_of_eq (if_pos hcondB).symm
        · rw [if_neg hc1]; exact zero_le
      have hCrare_S : Crare ≤ S := by omega
      have hSν : (2 : ℝ≥0∞)⁻¹ ^ S * ν ≤ (2 : ℝ≥0∞)⁻¹ ^ alpha := by
        calc (2 : ℝ≥0∞)⁻¹ ^ S * ν
            = (2 : ℝ≥0∞)⁻¹ ^ (S - Crare) * ((2 : ℝ≥0∞)⁻¹ ^ Crare * ν) := by
              rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hCrare_S]
          _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (S - Crare) * (2 : ℝ≥0∞)⁻¹ ^ d' := by
              gcongr
              rw [hνdef]; exact hrare (omegaFixedCode c n) d'
          _ = (2 : ℝ≥0∞)⁻¹ ^ ((S - Crare) + d') := by rw [← pow_add]
          _ ≤ (2 : ℝ≥0∞)⁻¹ ^ alpha :=
              pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two) (by omega)
      calc (2 : ℝ≥0∞)⁻¹ ^ S * μ
          ≤ (2 : ℝ≥0∞)⁻¹ ^ S * ν := by gcongr
        _ ≤ (2 : ℝ≥0∞)⁻¹ ^ alpha := hSν

end Kolmogorov
