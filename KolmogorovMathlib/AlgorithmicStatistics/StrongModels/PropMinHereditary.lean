import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Support
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.StandardDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MinimalModelBounds

namespace Kolmogorov
open scoped ENNReal

theorem logSlack_add_logSlack_absorb (c d : Nat) :
    ∃ C, ∀ n, logSlack c (n + logSlack d n) ≤ logSlack C n := by
  obtain ⟨C, hC⟩ := logSlack_linear_bound c (d + 2) d
  refine ⟨C, fun n => ?_⟩
  have ha2 : n + logSlack d n ≤ (d + 2) * n + d := by
    unfold logSlack
    have : (Nat.bits n).length ≤ n := length_natBits_le_self n
    nlinarith
  exact (logSlack_mono_right c ha2).trans (hC n)

theorem logSlack_add_delta_absorb (c d : Nat) :
    ∃ C, ∀ n delta, delta < n → logSlack c (n + delta + logSlack d n) ≤ logSlack C n := by
  obtain ⟨C, hC⟩ := logSlack_linear_bound c (d + 2) d
  refine ⟨C, fun n delta hdelta => ?_⟩
  have ha2 : n + delta + logSlack d n ≤ (d + 2) * n + d := by
    unfold logSlack
    have : (Nat.bits n).length ≤ n := length_natBits_le_self n
    nlinarith
  exact (logSlack_mono_right c ha2).trans (hC n)

theorem prop_min_hereditary
    (V : Map) (hV : isOptimalConditional V) :
    PropMinHereditaryStatement V := by
  unfold PropMinHereditaryStatement
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cKappa₀, cBound, hBound⟩ :=
    minimalModel_plainSetComplexity_le V hV
  obtain ⟨cBetter, hBetter⟩ := prop_better_std V U hV hU c hc
  obtain ⟨cStd, hStd⟩ := prop_std_omega V hV c hc
  obtain ⟨cPrefix, hPrefix⟩ :=
    KP_le_condK_of_logSlack_budget V U hV hU
  obtain ⟨cTrans, hTrans⟩ := condK_trans_nat V hV
  obtain ⟨cDrop, hDrop⟩ := condKLePlainK V hV
  obtain ⟨cOmega, hOmega⟩ := plainK_omegaFixedCode_upper V hV c
  obtain ⟨cBridge, hBridge⟩ :=
    omegaFixedCode_bridge_linear V hV c hc 0
  obtain ⟨cBetterFold, hBetterFold⟩ :=
    logSlack_add_logSlack_absorb cBetter cBetter
  obtain ⟨cStdFold, hStdFold⟩ :=
    logSlack_add_logSlack_absorb cStd cBetter
  obtain ⟨cPrefixAbsorb, hPrefixAbsorb⟩ :=
    logSlack_add_delta_absorb cPrefix cBound
  let cModel := cBetter + cBetterFold + cBound
  obtain ⟨cBridgeAbsorb, hBridgeAbsorb⟩ :=
    logSlack_add_delta_absorb cBridge cModel
  let cKappa :=
    cKappa₀ + cPrefixAbsorb + cBetter + cBetterFold + 1
  let cOut :=
    4 * cBetterFold + 2 * cStdFold + cBridgeAbsorb +
      3 * cTrans + cBound + cOmega + cDrop + 4
  refine ⟨cKappa, cOut, ?_⟩
  intro x n A hA delta q hq hx hmin
  have hmin₀ :
      IsMinimalModel V x A hA delta (logSlack cKappa₀ n) :=
    IsMinimalModel.mono (le_refl delta)
      (logSlack_mono_left (by dsimp [cKappa]; omega) n) hmin
  have hABound := hBound x n A hA delta hx hmin₀
  let codeA := (codedUniformOn A hA).code
  let a := (plainK V codeA).toNat
  have haFinite : plainK V codeA ≠ ⊤ := by
    change plainSetComplexity V A hA ≠ ⊤
    exact ne_top_of_le_ne_top
      (ENat.coe_ne_top (n + delta + logSlack cBound n)) hABound
  have haValue : plainK V codeA = (a : ENat) :=
    (ENat.coe_toNat haFinite).symm
  have haBound : a ≤ n + delta + logSlack cBound n := by
    have h : (a : ENat) ≤
        ((n + delta + logSlack cBound n : Nat) : ENat) := by
      rw [← haValue]
      exact hABound
    exact_mod_cast h
  have hCodeSwap : omegaFixedCode q a = omegaFixedCode c a :=
    omegaFixedCode_eq_of_isCodeFor hq hc a
  rw [hCodeSwap]
  by_cases hDelta : delta < n
  · let i := (setComplexity U A hA).toNat
    have hiFinite : setComplexity U A hA ≠ ⊤ := by
      obtain ⟨cTwo, hTwo⟩ := KPPlain_le_two_mul_length U hU
      unfold setComplexity
      exact ne_top_of_le_ne_top
        (ENat.coe_ne_top (2 * codeA.length + cTwo)) (hTwo codeA)
    have hiValue : setComplexity U A hA = (i : ENat) :=
      (ENat.coe_toNat hiFinite).symm
    let j := finiteSetLogCard A
    have hDescA : IsIJDescription U x A hA i j := by
      exact ⟨hmin.1, le_of_eq hiValue, finiteSetLogCard_spec A⟩
    obtain ⟨m, r, hxB, hm, hcardB, hplainB, _hprefixB,
        _hmLower, htwoB, hBA⟩ :=
      hBetter x n i j A hA hx hDescA
    let B := standardBlock c m r x
    let hB : B.Nonempty := ⟨x, hxB⟩
    let b := (plainK V (codedUniformOn B hB).code).toNat
    have hbFinite : plainK V (codedUniformOn B hB).code ≠ ⊤ := by
      exact ne_top_of_le_ne_top
        (ENat.coe_ne_top (i + logSlack cBetter m)) hplainB
    have hbValue : plainK V (codedUniformOn B hB).code = (b : ENat) :=
      (ENat.coe_toNat hbFinite).symm
    have hmVisible : m ≤ n + logSlack cBetter n := by
      exact hm.trans (by omega)
    have hBetterSlack :
        logSlack cBetter m ≤ logSlack cBetterFold n := by
      exact (logSlack_mono_right cBetter hmVisible).trans
        (hBetterFold n)
    have hStdSlack : logSlack cStd m ≤ logSlack cStdFold n := by
      exact (logSlack_mono_right cStd hmVisible).trans (hStdFold n)
    have hiBound : i ≤ a + logSlack cPrefix
        (n + delta + logSlack cBound n) := by
      have hp := hPrefix codeA [] a
        (n + delta + logSlack cBound n) haValue haBound
      have h : (i : ENat) ≤
          (a : ENat) +
            (logSlack cPrefix
              (n + delta + logSlack cBound n) : ENat) := by
        rw [← hiValue]
        exact hp
      exact_mod_cast h
    have hPrefixSlack :
        logSlack cPrefix (n + delta + logSlack cBound n) ≤
          logSlack cPrefixAbsorb n :=
      hPrefixAbsorb n delta hDelta
    have hlogB : finiteSetLogCard B = r := by
      unfold finiteSetLogCard
      rw [hcardB, Nat.clog_pow 2 r (by norm_num)]
    have hTwoPartB :
        plainSetComplexity V B hB +
            (finiteSetLogCard B : ENat) ≤
          plainSetComplexity V A hA +
            (finiteSetLogCard A : ENat) +
            (logSlack cKappa n : ENat) := by
      have hSlackSum :
          logSlack cPrefix
              (n + delta + logSlack cBound n) +
              logSlack cBetter n + logSlack cBetter m ≤
            logSlack cKappa n := by
        calc
          logSlack cPrefix
                (n + delta + logSlack cBound n) +
                logSlack cBetter n + logSlack cBetter m
              ≤ logSlack cPrefixAbsorb n +
                  logSlack cBetter n + logSlack cBetterFold n := by
                omega
          _ = logSlack
                (cPrefixAbsorb + cBetter + cBetterFold) n := by
                unfold logSlack
                ring
          _ ≤ logSlack cKappa n :=
                logSlack_mono_left (by dsimp [cKappa]; omega) n
      change plainK V (codedUniformOn B hB).code +
          (finiteSetLogCard B : ENat) ≤
        plainK V codeA + (finiteSetLogCard A : ENat) +
          (logSlack cKappa n : ENat)
      rw [hlogB]
      calc
        plainK V (codedUniformOn B hB).code + (r : ENat)
            ≤ (m : ENat) + (logSlack cBetter m : ENat) := htwoB
        _ ≤ ((i + j + logSlack cBetter n : Nat) : ENat) +
              (logSlack cBetter m : ENat) := by
            gcongr
            exact_mod_cast (hm.trans (by omega))
        _ ≤ ((a + j +
              logSlack cPrefix
                (n + delta + logSlack cBound n) +
              logSlack cBetter n : Nat) : ENat) +
              (logSlack cBetter m : ENat) := by
            have hnat : i + j + logSlack cBetter n ≤
                a + j +
                  logSlack cPrefix
                    (n + delta + logSlack cBound n) +
                  logSlack cBetter n := by omega
            exact add_le_add (Nat.cast_le.mpr hnat) le_rfl
        _ = (a : ENat) + (j : ENat) +
              ((logSlack cPrefix
                  (n + delta + logSlack cBound n) +
                logSlack cBetter n + logSlack cBetter m : Nat) : ENat) := by
            push_cast
            ring
        _ ≤ (a : ENat) + (j : ENat) +
              (logSlack cKappa n : ENat) := by
            gcongr
        _ = plainK V codeA + (finiteSetLogCard A : ENat) +
              (logSlack cKappa n : ENat) := by
            rw [haValue]
    have hGap : plainSetComplexity V A hA ≤
        plainSetComplexity V B hB + (delta : ENat) :=
      minimalModel_competitor_complexity_gap hmin hxB hTwoPartB
    have hab : a ≤ b + delta := by
      have h : (a : ENat) ≤ (b : ENat) + (delta : ENat) := by
        rw [← haValue, ← hbValue]
        exact hGap
      exact_mod_cast h
    have hbRaw : b ≤ m + logSlack cBetter m := by
      have h : (b : ENat) ≤
          ((m + logSlack cBetter m : Nat) : ENat) := by
        rw [← hbValue]
        calc
          plainK V (codedUniformOn B hB).code
              ≤ plainK V (codedUniformOn B hB).code + (r : ENat) :=
                le_add_of_nonneg_right (zero_le)
          _ ≤ (m : ENat) + (logSlack cBetter m : ENat) := htwoB
          _ = ((m + logSlack cBetter m : Nat) : ENat) := by
                rw [Nat.cast_add]
      exact_mod_cast h
    have hbBound : b ≤ n + logSlack cModel n := by
      calc
        b ≤ m + logSlack cBetter m := hbRaw
        _ ≤ n + logSlack cBetter n + logSlack cBetterFold n := by
          omega
        _ = n + logSlack (cBetter + cBetterFold) n := by
          unfold logSlack
          ring
        _ ≤ n + logSlack cModel n := by
          gcongr
          exact logSlack_mono_left (by dsimp [cModel]; omega) n
    let N := n + delta + logSlack cModel n
    have haN : a ≤ N := by
      calc
        a ≤ n + delta + logSlack cBound n := haBound
        _ ≤ n + delta + logSlack cModel n := by
          gcongr
          exact logSlack_mono_left (by dsimp [cModel]; omega) n
    have hbN : b ≤ N := by
      dsimp [N]
      omega
    have hOmegaB := (hStd m r b x hxB hbValue).2
    have hOmegaBVisible :
        condK V (omegaFixedCode c b) (codedUniformOn B hB).code ≤
          (logSlack cStdFold n : ENat) :=
      hOmegaB.trans (by exact_mod_cast hStdSlack)
    have hBAVisible :
        condK V (codedUniformOn B hB).code codeA ≤
          (logSlack cBetterFold n : ENat) :=
      hBA.trans (by exact_mod_cast hBetterSlack)
    have hOmegaGapRaw := hBridge N a b (by simpa [logSlack] using haN)
      (by simpa [logSlack] using hbN)
    have hBridgeSlack : logSlack cBridge N ≤
        logSlack cBridgeAbsorb n := by
      exact hBridgeAbsorb n delta hDelta
    have hOmegaGap :
        condK V (omegaFixedCode c a) (omegaFixedCode c b) ≤
          ((delta + logSlack cBridgeAbsorb n : Nat) : ENat) := by
      calc
        condK V (omegaFixedCode c a) (omegaFixedCode c b)
            ≤ (((a - b) + logSlack cBridge N : Nat) : ENat) := hOmegaGapRaw
        _ ≤ ((delta + logSlack cBridgeAbsorb n : Nat) : ENat) := by
            exact_mod_cast (show a - b + logSlack cBridge N ≤
              delta + logSlack cBridgeAbsorb n by omega)
    have hFirst := hTrans codeA (codedUniformOn B hB).code
      (omegaFixedCode c b)
      (logSlack cBetterFold n) (logSlack cStdFold n)
      hBAVisible hOmegaBVisible
    have hFinal := hTrans codeA (omegaFixedCode c b)
      (omegaFixedCode c a)
      (2 * logSlack cBetterFold n + logSlack cStdFold n + cTrans)
      (delta + logSlack cBridgeAbsorb n) hFirst hOmegaGap
    calc
      condK V (omegaFixedCode c a) codeA
          ≤ ((2 * (2 * logSlack cBetterFold n +
              logSlack cStdFold n + cTrans) +
              (delta + logSlack cBridgeAbsorb n) + cTrans : Nat) : ENat) := hFinal
      _ ≤ ((cOut * delta + logSlack cOut n : Nat) : ENat) := by
          apply Nat.cast_le.mpr
          dsimp [cOut]
          unfold logSlack
          nlinarith [Nat.zero_le (Nat.bits n).length]
  · have hLarge : n ≤ delta := Nat.le_of_not_gt hDelta
    calc
      condK V (omegaFixedCode c a) codeA
          ≤ plainK V (omegaFixedCode c a) + (cDrop : ENat) := hDrop _ _
      _ ≤ ((a + cOmega : Nat) : ENat) + (cDrop : ENat) := by
          gcongr
          exact hOmega a
      _ = ((a + cOmega + cDrop : Nat) : ENat) := by
          push_cast
          rfl
      _ ≤ ((cOut * delta + logSlack cOut n : Nat) : ENat) := by
          apply Nat.cast_le.mpr
          unfold logSlack
          show a + cOmega + cDrop ≤ cOut * delta +
            (cOut * (Nat.bits n).length + cOut)
          have hcTwo : 2 ≤ cOut := by dsimp [cOut]; omega
          have hcBits : cBound ≤ cOut := by dsimp [cOut]; omega
          have hcConst : cBound + cOmega + cDrop ≤ cOut := by
            dsimp [cOut]
            omega
          have hDeltaMul := Nat.mul_le_mul_right delta hcTwo
          have hBitsMul := Nat.mul_le_mul_right (Nat.bits n).length hcBits
          have haBound' := haBound
          unfold logSlack at haBound'
          omega

end Kolmogorov
