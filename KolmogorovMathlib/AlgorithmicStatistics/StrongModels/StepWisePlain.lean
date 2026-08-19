import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PropMinHereditary
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongSufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MinimalModelBounds

/-!
# The ordinary half of the step-wise theorem

This file proves the plain conditional-complexity half of VS40's step-wise
theorem: for a minimal sufficient statistic `A` and any sufficient statistic
`B` for the same string, `C(A | B)` is bounded by `O(delta) + O(log n)`.

The argument standardizes both models and connects them through the five-link
chain `B → B' → Omega_{C(B')} → Omega_{C(A')} → A' → A`.
-/

namespace Kolmogorov
open scoped ENNReal

/-- A finite upper bound transfers to `ENat.toNat`. -/
private lemma toNat_le_of_le_nat {e : ENat} {k : Nat} (h : e ≤ (k : ENat)) :
    e.toNat ≤ k := by
  simpa using ENat.toNat_le_toNat h (ENat.natCast_ne_top k)

/-- Five logarithmic slacks and a constant fold into a single slack. -/
private lemma logSlack_five_le (c₁ c₂ c₃ c₄ c₅ k C n : Nat)
    (h : c₁ + c₂ + c₃ + c₄ + c₅ + k ≤ C) :
    logSlack c₁ n + logSlack c₂ n + logSlack c₃ n + logSlack c₄ n +
        logSlack c₅ n + k ≤ logSlack C n := by
  unfold logSlack
  nlinarith [Nat.mul_le_mul_right (Nat.bits n).length h,
    Nat.zero_le (Nat.bits n).length]

/-- The zero slack vanishes. -/
private lemma logSlack_zero (n : Nat) : logSlack 0 n = 0 := by
  unfold logSlack
  ring

/-- A natural multiple of a slack is again a slack. -/
private lemma logSlack_nat_mul (k c n : Nat) :
    k * logSlack c n = logSlack (k * c) n := by
  unfold logSlack
  ring



/-- Packaged standardization of an arbitrary model: every model `S` for a
string of length `n` admits a standard block `S'` containing `x` which is at
least as good a description, is simple given `S`, and is interchangeable with
the finite Omega code at its own plain complexity. -/
theorem stepWise_standardModel_package
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Nat.Partrec.Code) (hc : IsCodeFor c V) :
    ∃ C : Nat, ∀ (x : BitString) (n : Nat) (S : Finset BitString) (hS : S.Nonempty),
      x.length = n → x ∈ S →
      ∃ (S' : Finset BitString) (hS' : S'.Nonempty), x ∈ S' ∧
        plainSetComplexity V S' hS' + (finiteSetLogCard S' : ENat) ≤
          ((min n ((setComplexity U S hS).toNat + finiteSetLogCard S)
              + logSlack C n : Nat) : ENat) ∧
        plainSetComplexity V S' hS' ≤
          (((setComplexity U S hS).toNat + logSlack C n : Nat) : ENat) ∧
        condK V (codedUniformOn S' hS').code (codedUniformOn S hS).code ≤
          (logSlack C n : ENat) ∧
        condK V (codedUniformOn S' hS').code
            (omegaFixedCode c (plainSetComplexity V S' hS').toNat) ≤
          (logSlack C n : ENat) ∧
        condK V (omegaFixedCode c (plainSetComplexity V S' hS').toNat)
            (codedUniformOn S' hS').code ≤
          (logSlack C n : ENat) := by
  obtain ⟨cBetter, hBetter⟩ := prop_better_std V U hV hU c hc
  obtain ⟨cStd, hStd⟩ := prop_std_omega V hV c hc
  obtain ⟨cBetterFold, hBetterFold⟩ := logSlack_add_logSlack_absorb cBetter cBetter
  obtain ⟨cStdFold, hStdFold⟩ := logSlack_add_logSlack_absorb cStd cBetter
  obtain ⟨cTwo, hTwo⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨cBetter + cBetterFold + cStdFold, ?_⟩
  intro x n S hS hx hxS
  have hiFinite : setComplexity U S hS ≠ ⊤ := by
    unfold setComplexity
    exact ne_top_of_le_ne_top
      (ENat.natCast_ne_top (2 * (codedUniformOn S hS).code.length + cTwo))
      (hTwo (codedUniformOn S hS).code)
  set i := (setComplexity U S hS).toNat with hi
  have hiValue : setComplexity U S hS = (i : ENat) := (ENat.natCast_toNat hiFinite).symm
  set j := finiteSetLogCard S with hj
  have hDesc : IsIJDescription U x S hS i j :=
    ⟨hxS, le_of_eq hiValue, finiteSetLogCard_spec S⟩
  obtain ⟨m, r, hxB, hm, hcardB, hplainB, _hprefixB, _hmLower, htwoB, hBS⟩ :=
    hBetter x n i j S hS hx hDesc
  set B := standardBlock c m r x with hBdef
  have hBne : B.Nonempty := ⟨x, hxB⟩
  have hmVisible : m ≤ n + logSlack cBetter n := by
    have hmin : min n (i + j) ≤ n := min_le_left _ _
    omega
  have hBetterSlack : logSlack cBetter m ≤ logSlack cBetterFold n :=
    (logSlack_mono_right cBetter hmVisible).trans (hBetterFold n)
  have hStdSlack : logSlack cStd m ≤ logSlack cStdFold n :=
    (logSlack_mono_right cStd hmVisible).trans (hStdFold n)
  have hlogB : finiteSetLogCard B = r := by
    unfold finiteSetLogCard
    rw [hcardB, Nat.clog_pow 2 r (by norm_num)]
  have hbFinite : plainSetComplexity V B hBne ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top (i + logSlack cBetter m)) hplainB
  set b := (plainSetComplexity V B hBne).toNat with hb
  have hbValue : plainK V (codedUniformOn B hBne).code = (b : ENat) :=
    (ENat.natCast_toNat hbFinite).symm
  have hFoldLe : logSlack cBetterFold n ≤
      logSlack (cBetter + cBetterFold + cStdFold) n :=
    logSlack_mono_left (by omega) n
  have hStdFoldLe : logSlack cStdFold n ≤
      logSlack (cBetter + cBetterFold + cStdFold) n :=
    logSlack_mono_left (by omega) n
  obtain ⟨hOmega₁, hOmega₂⟩ := hStd m r b x hxB hbValue
  refine ⟨B, hBne, hxB, ?_, ?_, ?_, ?_, ?_⟩
  · have hnat : m + logSlack cBetter m ≤
        min n (i + j) + logSlack (cBetter + cBetterFold + cStdFold) n := by
      have h1 : logSlack cBetter n + logSlack cBetterFold n =
          logSlack (cBetter + cBetterFold) n := logSlack_add_const _ _ _
      have h2 : logSlack (cBetter + cBetterFold) n ≤
          logSlack (cBetter + cBetterFold + cStdFold) n :=
        logSlack_mono_left (by omega) n
      omega
    rw [hlogB]
    calc plainSetComplexity V B hBne + (r : ENat)
        ≤ (m : ENat) + (logSlack cBetter m : ENat) := htwoB
      _ = ((m + logSlack cBetter m : Nat) : ENat) := by push_cast; ring
      _ ≤ _ := by exact_mod_cast hnat
  · calc plainSetComplexity V B hBne
        ≤ ((i + logSlack cBetter m : Nat) : ENat) := hplainB
      _ ≤ _ := by
          exact_mod_cast
            (by omega : i + logSlack cBetter m ≤
              i + logSlack (cBetter + cBetterFold + cStdFold) n)
  · exact hBS.trans (by exact_mod_cast (hBetterSlack.trans hFoldLe))
  · exact hOmega₁.trans (by exact_mod_cast (hStdSlack.trans hStdFoldLe))
  · exact hOmega₂.trans (by exact_mod_cast (hStdSlack.trans hStdFoldLe))



/-- The ordinary (plain conditional) half of the step-wise theorem. -/
theorem stepWise_plain_half
    (V : Map) (hV : isOptimalConditional V) :
    ∃ cKappa cPlain : Nat,
      ∀ x n A (hA : A.Nonempty) B (hB : B.Nonempty)
          epsilon delta,
        x.length = n →
        IsSufficientStatistic V x A hA epsilon →
        IsSufficientStatistic V x B hB epsilon →
        IsMinimalModel V x A hA delta
          (epsilon + logSlack cKappa n) →
        condK V (codedUniformOn A hA).code
            (codedUniformOn B hB).code ≤
          (cPlain * delta + logSlack cPlain n : ENat) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cStd, hStdPkg⟩ := stepWise_standardModel_package V U hV hU c hc
  obtain ⟨cKappa₀, cBound, hBound⟩ := minimalModel_plainSetComplexity_le V hV
  obtain ⟨cPrefix, hPrefix⟩ := KP_le_condK_of_logSlack_budget V U hV hU
  obtain ⟨cMem, hMem⟩ := plainK_mem_le_of_plainSetComplexity_le V hV
  obtain ⟨cLit, hLit⟩ := plainKLeLength V hV
  obtain ⟨cDrop, hDrop⟩ := condKLePlainK V hV
  obtain ⟨cRev, hRev⟩ := condK_reverse_of_plain_complexity_gap V U hV hU
  obtain ⟨cChain, hChain⟩ := condK_chain_five V hV
  obtain ⟨cBridge, hBridge⟩ := omegaFixedCode_bridge_linear V hV c hc 0
  obtain ⟨cBridgeAbs, hBridgeAbs⟩ :=
    logSlack_add_delta_absorb cBridge (cBound + cStd + 1)
  obtain ⟨cPrefixAbs, hPrefixAbs⟩ :=
    logSlack_add_delta_absorb cPrefix (cBound + cStd + 1)
  obtain ⟨cRevAbs, hRevAbs⟩ :=
    logSlack_add_delta_absorb cRev (cBound + cStd + 1)
  obtain ⟨cBits, hBits⟩ :=
    logSlack_add_delta_absorb 1 (cBound + cStd + 1)
  obtain ⟨cPrefixLin, hPrefixLin⟩ := logSlack_linear_bound cPrefix 2 cLit
  refine ⟨cKappa₀ + cPrefixAbs + 2 * cStd + 2 * cBits + cPrefixLin + cMem + 1,
    5 + 31 * cStd + 4 * cPrefixAbs + 4 * cBridgeAbs + cRevAbs + cChain +
      cBound + cDrop + 2, ?_⟩
  set cModel := cBound + cStd + 1 with hcModel
  set cKappa := cKappa₀ + cPrefixAbs + 2 * cStd + 2 * cBits + cPrefixLin + cMem + 1
    with hcKappa
  set cPlain := 5 + 31 * cStd + 4 * cPrefixAbs + 4 * cBridgeAbs + cRevAbs + cChain +
    cBound + cDrop + 2 with hcPlain
  intro x n A hA B hB epsilon delta hx hSuffA hSuffB hmin
  have hxA : x ∈ A := hmin.1
  have hxB : x ∈ B := hSuffB.1
  have hmin₀ : IsMinimalModel V x A hA delta (logSlack cKappa₀ n) := by
    refine IsMinimalModel.mono le_rfl ?_ hmin
    have h := logSlack_mono_left (show cKappa₀ ≤ cKappa by omega) n
    omega
  have hABound := hBound x n A hA delta hx hmin₀
  have haFinite : plainSetComplexity V A hA ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hABound
  set a := (plainSetComplexity V A hA).toNat with ha
  have haValue : plainSetComplexity V A hA = (a : ENat) :=
    (ENat.natCast_toNat haFinite).symm
  have haBound : a ≤ n + delta + logSlack cBound n := by
    rw [ha]
    exact toNat_le_of_le_nat hABound
  by_cases hDelta : delta < n
  · -- the interesting branch: the model complexities are visible in `n`
    have hcBoundModel : logSlack cBound n ≤ logSlack cModel n :=
      logSlack_mono_left (by omega) n
    have hcStdModel : logSlack cStd n ≤ logSlack cModel n :=
      logSlack_mono_left (by omega) n
    have haN : a ≤ n + delta + logSlack cModel n := by omega
    have hiA : (setComplexity U A hA).toNat ≤
        a + logSlack cPrefix (n + delta + logSlack cModel n) := by
      refine toNat_le_of_le_nat ?_
      have h := hPrefix (codedUniformOn A hA).code [] a
        (n + delta + logSlack cModel n) haValue haN
      calc setComplexity U A hA
          ≤ (a : ENat) +
              (logSlack cPrefix (n + delta + logSlack cModel n) : ENat) := h
        _ = ((a + logSlack cPrefix (n + delta + logSlack cModel n) : Nat) : ENat) := by
            push_cast; ring
    have hPrefixSlack :
        logSlack cPrefix (n + delta + logSlack cModel n) ≤ logSlack cPrefixAbs n :=
      hPrefixAbs n delta hDelta
    obtain ⟨A', hA', hxA', hTwoA', hPlainA', hCondA'A, hCondA'Om, hCondOmA'⟩ :=
      hStdPkg x n A hA hx hxA
    obtain ⟨B', hB', hxB', hTwoB', hPlainB', hCondB'B, hCondB'Om, hCondOmB'⟩ :=
      hStdPkg x n B hB hx hxB
    have ha'Finite : plainSetComplexity V A' hA' ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) (le_trans le_self_add hTwoA')
    have hb'Finite : plainSetComplexity V B' hB' ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) (le_trans le_self_add hTwoB')
    set a' := (plainSetComplexity V A' hA').toNat with ha'
    set b' := (plainSetComplexity V B' hB').toNat with hb'
    have ha'Value : plainSetComplexity V A' hA' = (a' : ENat) :=
      (ENat.natCast_toNat ha'Finite).symm
    have hb'Value : plainSetComplexity V B' hB' = (b' : ENat) :=
      (ENat.natCast_toNat hb'Finite).symm
    have ha'TwoNat : a' + finiteSetLogCard A' ≤
        min n ((setComplexity U A hA).toNat + finiteSetLogCard A) + logSlack cStd n := by
      have h : ((a' + finiteSetLogCard A' : Nat) : ENat) ≤
          ((min n ((setComplexity U A hA).toNat + finiteSetLogCard A) +
            logSlack cStd n : Nat) : ENat) := by
        rw [Nat.cast_add, ← ha'Value]
        exact hTwoA'
      exact_mod_cast h
    have hb'TwoNat : b' + finiteSetLogCard B' ≤
        min n ((setComplexity U B hB).toNat + finiteSetLogCard B) + logSlack cStd n := by
      have h : ((b' + finiteSetLogCard B' : Nat) : ENat) ≤
          ((min n ((setComplexity U B hB).toNat + finiteSetLogCard B) +
            logSlack cStd n : Nat) : ENat) := by
        rw [Nat.cast_add, ← hb'Value]
        exact hTwoB'
      exact_mod_cast h
    have ha'PlainNat : a' ≤ (setComplexity U A hA).toNat + logSlack cStd n := by
      rw [ha']
      exact toNat_le_of_le_nat hPlainA'
    have hminA' : min n ((setComplexity U A hA).toNat + finiteSetLogCard A) ≤ n :=
      min_le_left _ _
    have hminA'' : min n ((setComplexity U A hA).toNat + finiteSetLogCard A) ≤
        (setComplexity U A hA).toNat + finiteSetLogCard A := min_le_right _ _
    have hminB' : min n ((setComplexity U B hB).toNat + finiteSetLogCard B) ≤ n :=
      min_le_left _ _
    have hminB'' : min n ((setComplexity U B hB).toNat + finiteSetLogCard B) ≤
        (setComplexity U B hB).toNat + finiteSetLogCard B := min_le_right _ _
    -- `A'` is an admissible competitor for the minimality of `A`
    have hA'compet : plainSetComplexity V A' hA' + (finiteSetLogCard A' : ENat) ≤
        plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
          ((epsilon + logSlack cKappa n : Nat) : ENat) := by
      have hfold : logSlack cPrefixAbs n + logSlack cStd n ≤ logSlack cKappa n := by
        simpa [logSlack_zero] using
          logSlack_five_le cPrefixAbs cStd 0 0 0 0 cKappa n (by omega)
      have hnat : a' + finiteSetLogCard A' ≤
          a + finiteSetLogCard A + (epsilon + logSlack cKappa n) := by omega
      calc plainSetComplexity V A' hA' + (finiteSetLogCard A' : ENat)
          = ((a' + finiteSetLogCard A' : Nat) : ENat) := by
            rw [ha'Value]; push_cast; ring
        _ ≤ ((a + finiteSetLogCard A + (epsilon + logSlack cKappa n) : Nat) : ENat) := by
            exact_mod_cast hnat
        _ = plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
              ((epsilon + logSlack cKappa n : Nat) : ENat) := by
            rw [haValue]; push_cast; ring
    have hGapA : plainSetComplexity V A hA ≤
        plainSetComplexity V A' hA' + (delta : ENat) :=
      minimalModel_competitor_complexity_gap hmin hxA' hA'compet
    -- `B'` is an admissible competitor as well
    have hB'compet : plainSetComplexity V B' hB' + (finiteSetLogCard B' : ENat) ≤
        plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
          ((epsilon + logSlack cKappa n : Nat) : ENat) := by
      have hnat : b' + finiteSetLogCard B' ≤
          a + finiteSetLogCard A + (epsilon + logSlack cKappa n) := by
        by_cases hEps : n ≤ epsilon
        · have hfold : logSlack cStd n ≤ logSlack cKappa n :=
            logSlack_mono_left (by omega) n
          omega
        · have hEps' : epsilon < n := Nat.lt_of_not_ge hEps
          have hKx : plainK V x ≤ ((n + cLit : Nat) : ENat) := by
            calc plainK V x ≤ (programLength x : ENat) + (cLit : ENat) := hLit x
              _ = ((x.length + cLit : Nat) : ENat) := by push_cast; rfl
              _ = ((n + cLit : Nat) : ENat) := by rw [hx]
          have hkxFinite : plainK V x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hKx
          set kx := (plainK V x).toNat with hkx
          have hkxValue : plainK V x = (kx : ENat) := (ENat.natCast_toNat hkxFinite).symm
          have hkxBound : kx ≤ n + cLit := by
            rw [hkx]; exact toNat_le_of_le_nat hKx
          have hkxMem : kx ≤ a + finiteSetLogCard A + 2 * (Nat.bits a).length + cMem := by
            rw [hkx]
            exact toNat_le_of_le_nat (hMem A hA x a hxA (le_of_eq haValue))
          have hbvFinite : plainSetComplexity V B hB ≠ ⊤ := by
            refine ne_top_of_le_ne_top (ENat.natCast_ne_top (n + cLit + epsilon)) ?_
            calc plainSetComplexity V B hB
                ≤ plainSetComplexity V B hB + (finiteSetLogCard B : ENat) := le_self_add
              _ ≤ plainK V x + (epsilon : ENat) := hSuffB.2
              _ ≤ ((n + cLit : Nat) : ENat) + (epsilon : ENat) := by gcongr
              _ = ((n + cLit + epsilon : Nat) : ENat) := by push_cast; ring
          set bv := (plainSetComplexity V B hB).toNat with hbv
          have hbvValue : plainSetComplexity V B hB = (bv : ENat) :=
            (ENat.natCast_toNat hbvFinite).symm
          have hbvSuff : bv + finiteSetLogCard B ≤ kx + epsilon := by
            have h : ((bv + finiteSetLogCard B : Nat) : ENat) ≤
                ((kx + epsilon : Nat) : ENat) := by
              rw [Nat.cast_add, Nat.cast_add, ← hbvValue, ← hkxValue]
              exact hSuffB.2
            exact_mod_cast h
          have hbvBound : bv ≤ 2 * n + cLit := by omega
          have hiB : (setComplexity U B hB).toNat ≤ bv + logSlack cPrefix (2 * n + cLit) := by
            refine toNat_le_of_le_nat ?_
            calc setComplexity U B hB
                ≤ (bv : ENat) + (logSlack cPrefix (2 * n + cLit) : ENat) :=
                  hPrefix (codedUniformOn B hB).code [] bv (2 * n + cLit) hbvValue hbvBound
              _ = ((bv + logSlack cPrefix (2 * n + cLit) : Nat) : ENat) := by
                  push_cast; ring
          have hLin : logSlack cPrefix (2 * n + cLit) ≤ logSlack cPrefixLin n := hPrefixLin n
          have hBitsA : (Nat.bits a).length ≤ logSlack cBits n := by
            calc (Nat.bits a).length
                ≤ (Nat.bits (n + delta + logSlack cModel n)).length :=
                  length_natBits_mono haN
              _ ≤ logSlack 1 (n + delta + logSlack cModel n) := by unfold logSlack; omega
              _ ≤ logSlack cBits n := hBits n delta hDelta
          have hfold : logSlack cBits n + logSlack cBits n + logSlack cPrefixLin n +
              logSlack cStd n + cMem ≤ logSlack cKappa n := by
            simpa [logSlack_zero] using
              logSlack_five_le cBits cBits cPrefixLin cStd 0 cMem cKappa n (by omega)
          omega
      calc plainSetComplexity V B' hB' + (finiteSetLogCard B' : ENat)
          = ((b' + finiteSetLogCard B' : Nat) : ENat) := by
            rw [hb'Value]; push_cast; ring
        _ ≤ ((a + finiteSetLogCard A + (epsilon + logSlack cKappa n) : Nat) : ENat) := by
            exact_mod_cast hnat
        _ = plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
              ((epsilon + logSlack cKappa n : Nat) : ENat) := by
            rw [haValue]; push_cast; ring
    have hGapB : plainSetComplexity V A hA ≤
        plainSetComplexity V B' hB' + (delta : ENat) :=
      minimalModel_competitor_complexity_gap hmin hxB' hB'compet
    have hGapBNat : a ≤ b' + delta := by
      have h : (a : ENat) ≤ ((b' + delta : Nat) : ENat) := by
        rw [← haValue]
        calc plainSetComplexity V A hA
            ≤ plainSetComplexity V B' hB' + (delta : ENat) := hGapB
          _ = ((b' + delta : Nat) : ENat) := by rw [hb'Value]; push_cast; ring
      exact_mod_cast h
    -- visibility of the standardized complexities
    have ha'Upper : a' ≤ a + logSlack cPrefixAbs n + logSlack cStd n := by omega
    have ha'N : a' ≤ n + delta + logSlack cModel n := by omega
    have hb'N : b' ≤ n + delta + logSlack cModel n := by omega
    -- the Omega link
    have hBridgeApp := hBridge (n + delta + logSlack cModel n) a' b'
      (by simpa [logSlack] using ha'N) (by simpa [logSlack] using hb'N)
    have hBridgeSlack :
        logSlack cBridge (n + delta + logSlack cModel n) ≤ logSlack cBridgeAbs n :=
      hBridgeAbs n delta hDelta
    have hOmegaGap : condK V (omegaFixedCode c a') (omegaFixedCode c b') ≤
        ((delta + (logSlack cPrefixAbs n + logSlack cStd n) +
          logSlack cBridgeAbs n : Nat) : ENat) := by
      refine hBridgeApp.trans ?_
      exact_mod_cast
        (by omega : (a' - b') + logSlack cBridge (n + delta + logSlack cModel n) ≤
          delta + (logSlack cPrefixAbs n + logSlack cStd n) + logSlack cBridgeAbs n)
    -- reversing the standardization of `A` by plain symmetry of information
    have hRevApp := hRev (codedUniformOn A hA).code (codedUniformOn A' hA').code
      (n + delta + logSlack cModel n) delta (logSlack cStd n)
      (by
        change plainSetComplexity V A hA ≤ ((n + delta + logSlack cModel n : Nat) : ENat)
        rw [haValue]
        exact_mod_cast haN)
      (by
        change plainSetComplexity V A' hA' ≤ ((n + delta + logSlack cModel n : Nat) : ENat)
        rw [ha'Value]
        exact_mod_cast ha'N)
      hCondA'A (by omega) hGapA
    have hRevSlack :
        logSlack cRev (n + delta + logSlack cModel n) ≤ logSlack cRevAbs n :=
      hRevAbs n delta hDelta
    have hLink5 : condK V (codedUniformOn A hA).code (codedUniformOn A' hA').code ≤
        ((delta + logSlack cStd n + logSlack cRevAbs n : Nat) : ENat) := by
      refine hRevApp.trans ?_
      calc ((delta + logSlack cStd n : Nat) : ENat) +
            (logSlack cRev (n + delta + logSlack cModel n) : ENat)
          = ((delta + logSlack cStd n +
              logSlack cRev (n + delta + logSlack cModel n) : Nat) : ENat) := by
            push_cast; ring
        _ ≤ ((delta + logSlack cStd n + logSlack cRevAbs n : Nat) : ENat) := by
            exact_mod_cast (by omega :
              delta + logSlack cStd n +
                logSlack cRev (n + delta + logSlack cModel n) ≤
              delta + logSlack cStd n + logSlack cRevAbs n)
    -- assembling the five links
    have hFinal := hChain (codedUniformOn B hB).code (codedUniformOn B' hB').code
      (omegaFixedCode c b') (omegaFixedCode c a') (codedUniformOn A' hA').code
      (codedUniformOn A hA).code
      (logSlack cStd n) (logSlack cStd n)
      (delta + (logSlack cPrefixAbs n + logSlack cStd n) + logSlack cBridgeAbs n)
      (logSlack cStd n)
      (delta + logSlack cStd n + logSlack cRevAbs n)
      hCondB'B hCondOmB' hOmegaGap hCondA'Om hLink5
    refine hFinal.trans ?_
    have hmul : 5 * delta ≤ cPlain * delta := Nat.mul_le_mul_right delta (by omega)
    have h31 : 31 * logSlack cStd n = logSlack (31 * cStd) n := logSlack_nat_mul _ _ _
    have h4p : 4 * logSlack cPrefixAbs n = logSlack (4 * cPrefixAbs) n :=
      logSlack_nat_mul _ _ _
    have h4b : 4 * logSlack cBridgeAbs n = logSlack (4 * cBridgeAbs) n :=
      logSlack_nat_mul _ _ _
    have hslack : logSlack (31 * cStd) n + logSlack (4 * cPrefixAbs) n +
        logSlack (4 * cBridgeAbs) n + logSlack cRevAbs n + cChain ≤ logSlack cPlain n := by
      simpa [logSlack_zero] using
        logSlack_five_le (31 * cStd) (4 * cPrefixAbs) (4 * cBridgeAbs) cRevAbs 0
          cChain cPlain n (by omega)
    exact_mod_cast
      (by omega : 16 * logSlack cStd n + 8 * logSlack cStd n +
        4 * (delta + (logSlack cPrefixAbs n + logSlack cStd n) + logSlack cBridgeAbs n) +
        2 * logSlack cStd n +
        (delta + logSlack cStd n + logSlack cRevAbs n) + cChain ≤
        cPlain * delta + logSlack cPlain n)
  · -- the coarse branch: `n ≤ delta`
    have hLarge : n ≤ delta := Nat.le_of_not_gt hDelta
    calc condK V (codedUniformOn A hA).code (codedUniformOn B hB).code
        ≤ plainK V (codedUniformOn A hA).code + (cDrop : ENat) := hDrop _ _
      _ ≤ ((n + delta + logSlack cBound n : Nat) : ENat) + (cDrop : ENat) := by
          gcongr
          exact hABound
      _ = ((n + delta + logSlack cBound n + cDrop : Nat) : ENat) := by push_cast; ring
      _ ≤ ((cPlain * delta + logSlack cPlain n : Nat) : ENat) := by
          have h1 : logSlack cBound n + cDrop ≤ logSlack (cBound + cDrop) n :=
            logSlack_add_nat_le _ _ _
          have h2 : logSlack (cBound + cDrop) n ≤ logSlack cPlain n :=
            logSlack_mono_left (by omega) n
          have hmul : 2 * delta ≤ cPlain * delta := Nat.mul_le_mul_right delta (by omega)
          exact_mod_cast (by omega :
            n + delta + logSlack cBound n + cDrop ≤ cPlain * delta + logSlack cPlain n)

/-- VS40 Theorem `thm:step-wise`. -/
theorem thm_step_wise
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ThmStepWiseStatement V T :=
  thmStepWise_of_plain V T hV hT (stepWise_plain_half V hV)

end Kolmogorov
