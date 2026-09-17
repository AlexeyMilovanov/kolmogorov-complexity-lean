import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Support
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MinimalModelBounds

/-!
# Minimality is hereditary

`prop_min_hereditary`: for an optimal plain conditional machine, a minimal model of a minimal
model is again minimal — the minimality of models is inherited.

The proof is a chain of estimates, each named: `prop_min_hereditary_a_setup` and
`prop_min_hereditary_i_bound` fix the complexity parameters of the model,
`prop_min_hereditary_b_bound` bounds the complexity of the standard block,
`prop_min_hereditary_omega_gap` the distance between finite Omega codes, and
`prop_min_hereditary_condK_chain` the triangle inequality for conditional complexity; the two
regimes `delta < n` and `n ≤ delta` are closed by
`prop_min_hereditary_arith_of_lt_delta` and `prop_min_hereditary_arith_of_le_delta`.

`logSlack_add_logSlack_absorb`, `logSlack_add_delta_absorb` and
`plainSetComplexity_two_part_le_of_two_part_le` are the slack lemmas used throughout.
-/

namespace Kolmogorov
open scoped ENNReal

/-- A logarithmic slack evaluated at `n + logSlack d n` is again a logarithmic slack in `n`. -/
theorem logSlack_add_logSlack_absorb (c d : Nat) :
    ∃ C, ∀ n, logSlack c (n + logSlack d n) ≤ logSlack C n := by
  obtain ⟨C, hC⟩ := logSlack_absorb_of_le_linear c (d + 2) d
  refine ⟨C, fun n => hC n _ ?_⟩
  unfold logSlack
  have : (Nat.bits n).length ≤ n := length_natBits_le n
  nlinarith

/-- For `delta < n`, a logarithmic slack evaluated at `n + delta + logSlack d n` is again a
logarithmic slack in `n`. -/
theorem logSlack_add_delta_absorb (c d : Nat) :
    ∃ C, ∀ n delta, delta < n → logSlack c (n + delta + logSlack d n) ≤ logSlack C n := by
  obtain ⟨C, hC⟩ := logSlack_absorb_of_le_linear c (d + 2) d
  refine ⟨C, fun n delta hdelta => hC n _ ?_⟩
  unfold logSlack
  have : (Nat.bits n).length ≤ n := length_natBits_le n
  nlinarith

/-- Transfer of a two-part bound from `B` to `A`.  If the set complexity of `A` is the natural
number `a`, the two-part cost of `B` is at most `m + s`, and `m ≤ i + finiteSetLogCard A + t`
with `i ≤ a + p` and `p + t + s ≤ kappa`, then the two-part cost of `B` exceeds that of `A` by
at most `kappa`. -/
private theorem plainSetComplexity_two_part_le_of_two_part_le
    (V : Map) {A B : Finset BitString} (hA : A.Nonempty) (hB : B.Nonempty)
    {a i m p s t kappa : ℕ}
    (haValue : plainSetComplexity V A hA = (a : ENat))
    (htwoB : plainSetComplexity V B hB + (finiteSetLogCard B : ENat) ≤
      (m : ENat) + (s : ENat))
    (hm : m ≤ i + finiteSetLogCard A + t)
    (hiBound : i ≤ a + p)
    (hSlackSum : p + t + s ≤ kappa) :
    plainSetComplexity V B hB + (finiteSetLogCard B : ENat) ≤
      plainSetComplexity V A hA + (finiteSetLogCard A : ENat) + (kappa : ENat) := by
  have hnat : m + s ≤ a + finiteSetLogCard A + kappa := by omega
  calc
    plainSetComplexity V B hB + (finiteSetLogCard B : ENat)
        ≤ (m : ENat) + (s : ENat) := htwoB
    _ = ((m + s : Nat) : ENat) := by push_cast; ring
    _ ≤ ((a + finiteSetLogCard A + kappa : Nat) : ENat) := Nat.cast_le.mpr hnat
    _ = plainSetComplexity V A hA + (finiteSetLogCard A : ENat) + (kappa : ENat) := by
        rw [haValue]; push_cast; ring

/-- Bounded complexity `a` and value equality for set model `A`. -/
private theorem prop_min_hereditary_a_setup
    (V : Map) (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
    (n delta cKappa₀ cBound cKappa : ℕ)
    (hBound : List.length x = n → IsMinimalModel V x A hA delta (logSlack cKappa₀ n) →
      plainSetComplexity V A hA ≤ ((n + delta + logSlack cBound n : ℕ) : ENat))
    (hx : x.length = n)
    (hmin : IsMinimalModel V x A hA delta (logSlack cKappa n))
    (hcKappa : cKappa₀ ≤ cKappa) :
    plainK V (codedUniformOn A hA).code ≠ ⊤ ∧
      plainK V (codedUniformOn A hA).code = ((plainK V (codedUniformOn A hA).code).toNat : ENat) ∧
      (plainK V (codedUniformOn A hA).code).toNat ≤ n + delta + logSlack cBound n := by
  have hmin₀ : IsMinimalModel V x A hA delta (logSlack cKappa₀ n) :=
    IsMinimalModel.mono (le_refl delta) (logSlack_mono_left hcKappa n) hmin
  have hABound := hBound hx hmin₀
  have haFinite : plainK V (codedUniformOn A hA).code ≠ ⊤ := by
    change plainSetComplexity V A hA ≠ ⊤
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top (n + delta + logSlack cBound n)) hABound
  have haValue : plainK V (codedUniformOn A hA).code =
      ((plainK V (codedUniformOn A hA).code).toNat : ENat) :=
    (ENat.natCast_toNat haFinite).symm
  have haBound : (plainK V (codedUniformOn A hA).code).toNat ≤ n + delta + logSlack cBound n := by
    have h : ((plainK V (codedUniformOn A hA).code).toNat : ENat) ≤
        ((n + delta + logSlack cBound n : Nat) : ENat) := by
      rw [← haValue]
      exact hABound
    exact_mod_cast h
  exact ⟨haFinite, haValue, haBound⟩

/-- Bounded set complexity index `i` from prefix complexity budget. -/
private theorem prop_min_hereditary_i_bound
    (V U : Map) (A : Finset BitString) (hA : A.Nonempty)
    (a i n delta cPrefix cBound : ℕ)
    (haValue : plainK V (codedUniformOn A hA).code = (a : ENat))
    (haBound : a ≤ n + delta + logSlack cBound n)
    (hPrefix : condK V (codedUniformOn A hA).code [] = (a : ENat) →
      a ≤ n + delta + logSlack cBound n →
      KP U (codedUniformOn A hA).code [] ≤
        ((a + logSlack cPrefix (n + delta + logSlack cBound n) : ℕ) : ENat))
    (hiValue : setComplexity U A hA = (i : ENat)) :
    i ≤ a + logSlack cPrefix (n + delta + logSlack cBound n) := by
  have hp := hPrefix haValue haBound
  have h : (i : ENat) ≤ (a : ENat) + (logSlack cPrefix (n + delta + logSlack cBound n) : ENat) := by
    unfold setComplexity at hiValue
    rw [← hiValue]
    exact hp
  exact_mod_cast h

/-- Upper bound on complexity `b` of block `B`. -/
private theorem prop_min_hereditary_b_bound
    (V : Map) (B : Finset BitString) (hB : B.Nonempty)
    (b r m n cBetter cBetterFold cBound cModel : ℕ)
    (hbValue : plainK V (codedUniformOn B hB).code = (b : ENat))
    (htwoB : plainK V (codedUniformOn B hB).code + (r : ENat) ≤
      (m : ENat) + (logSlack cBetter m : ENat))
    (hmVisible : m ≤ n + logSlack cBetter n)
    (hSlackFold : logSlack cBetter m ≤ logSlack cBetterFold n)
    (hcModel : cBetter + cBetterFold + cBound ≤ cModel) :
    b ≤ n + logSlack cModel n := by
  have hbRaw : b ≤ m + logSlack cBetter m := by
    have h : (b : ENat) ≤ ((m + logSlack cBetter m : Nat) : ENat) := by
      rw [← hbValue]
      calc
        plainK V (codedUniformOn B hB).code
            ≤ plainK V (codedUniformOn B hB).code + (r : ENat) := le_add_of_nonneg_right zero_le
        _ ≤ (m : ENat) + (logSlack cBetter m : ENat) := htwoB
        _ = ((m + logSlack cBetter m : Nat) : ENat) := by rw [Nat.cast_add]
    exact_mod_cast h
  calc
    b ≤ m + logSlack cBetter m := hbRaw
    _ ≤ n + logSlack cBetter n + logSlack cBetterFold n := by omega
    _ = n + logSlack (cBetter + cBetterFold) n := by
      unfold logSlack
      ring
    _ ≤ n + logSlack cModel n := by
      gcongr
      exact logSlack_mono_left (by omega) n

/-- Bound on omega fixed code distance from logarithmic slack absorption. -/
private theorem prop_min_hereditary_omega_gap
    (V : Map) (c : Nat.Partrec.Code) (a b n delta cBridge cBridgeAbsorb cModel : ℕ)
    (hBridge : ∀ (m a b : ℕ), a ≤ m + logSlack 0 m → b ≤ m + logSlack 0 m →
      condK V (omegaFixedCode c a) (omegaFixedCode c b) ≤
        (((a - b) + logSlack cBridge m : Nat) : ENat))
    (hBridgeAbsorb : delta < n →
      logSlack cBridge (n + delta + logSlack cModel n) ≤ logSlack cBridgeAbsorb n)
    (hab : a ≤ b + delta)
    (haBound : a ≤ n + delta + logSlack cModel n)
    (hbBound : b ≤ n + logSlack cModel n)
    (hDelta : delta < n) :
    condK V (omegaFixedCode c a) (omegaFixedCode c b) ≤
      ((delta + logSlack cBridgeAbsorb n : Nat) : ENat) := by
  let N := n + delta + logSlack cModel n
  have haN : a ≤ N := haBound
  have hbN : b ≤ N := by dsimp [N]; omega
  have hRaw := hBridge N a b (by simpa [logSlack] using haN) (by simpa [logSlack] using hbN)
  have hAbs : logSlack cBridge N ≤ logSlack cBridgeAbsorb n := hBridgeAbsorb hDelta
  calc
    condK V (omegaFixedCode c a) (omegaFixedCode c b)
        ≤ (((a - b) + logSlack cBridge N : Nat) : ENat) := hRaw
    _ ≤ ((delta + logSlack cBridgeAbsorb n : Nat) : ENat) := by
        exact_mod_cast (show a - b + logSlack cBridge N ≤ delta + logSlack cBridgeAbsorb n by omega)

/-- Triangle inequality chain for conditional complexity in hereditary minimal models. -/
private theorem prop_min_hereditary_condK_chain
    (V : Map) (codeA : BitString) (Bcode : BitString) (qa qb : BitString)
    (sBetter sStd sBridge cTrans : ℕ)
    (hTrans : ∀ (x y z : BitString) (a b : ℕ),
      condK V y x ≤ (a : ENat) → condK V z y ≤ (b : ENat) →
      condK V z x ≤ ((2 * a + b + cTrans : ℕ) : ENat))
    (hBA : condK V Bcode codeA ≤ (sBetter : ENat))
    (hOmegaB : condK V qb Bcode ≤ (sStd : ENat))
    (hOmegaGap : condK V qa qb ≤ (sBridge : ENat)) :
    condK V qa codeA ≤
      ((2 * (2 * sBetter + sStd + cTrans) + sBridge + cTrans : ℕ) : ENat) := by
  have hFirst := hTrans codeA Bcode qb sBetter sStd hBA hOmegaB
  exact hTrans codeA qb qa (2 * sBetter + sStd + cTrans) sBridge hFirst hOmegaGap

/-- Arithmetic inequality for conditional complexity when `delta < n`. -/
private theorem prop_min_hereditary_arith_of_lt_delta
    {cOut cBetterFold cStdFold cBridgeAbsorb cTrans cBound cOmega cDrop : ℕ}
    (hcOut : cOut = 4 * cBetterFold + 2 * cStdFold + cBridgeAbsorb +
      3 * cTrans + cBound + cOmega + cDrop + 4)
    (n delta : ℕ) :
    2 * (2 * logSlack cBetterFold n + logSlack cStdFold n + cTrans) +
        (delta + logSlack cBridgeAbsorb n) + cTrans ≤
      cOut * delta + logSlack cOut n := by
  rw [hcOut]
  unfold logSlack
  nlinarith [Nat.zero_le (Nat.bits n).length]

/-- Upper bound on complexity sum when `n ≤ delta`. -/
private theorem prop_min_hereditary_arith_of_le_delta
    {cOut cBound cOmega cDrop : ℕ} (cBetterFold cStdFold cBridgeAbsorb cTrans : ℕ)
    (hcOut : cOut = 4 * cBetterFold + 2 * cStdFold + cBridgeAbsorb +
      3 * cTrans + cBound + cOmega + cDrop + 4)
    {a n delta : ℕ} (ha : a ≤ n + delta + logSlack cBound n) (hn : n ≤ delta) :
    a + cOmega + cDrop ≤ cOut * delta + logSlack cOut n := by
  rw [hcOut]
  unfold logSlack
  have hcTwo : 2 ≤ 4 * cBetterFold + 2 * cStdFold + cBridgeAbsorb +
      3 * cTrans + cBound + cOmega + cDrop + 4 := by omega
  have hcBits : cBound ≤ 4 * cBetterFold + 2 * cStdFold + cBridgeAbsorb +
      3 * cTrans + cBound + cOmega + cDrop + 4 := by omega
  have hcConst : cBound + cOmega + cDrop ≤ 4 * cBetterFold + 2 * cStdFold + cBridgeAbsorb +
      3 * cTrans + cBound + cOmega + cDrop + 4 := by omega
  have hDeltaMul := Nat.mul_le_mul_right delta hcTwo
  have hBitsMul := Nat.mul_le_mul_right (Nat.bits n).length hcBits
  unfold logSlack at ha
  omega

/-- Minimality of models is hereditary for an optimal plain conditional machine. -/
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
  obtain ⟨cDrop, hDrop⟩ := condK_le_plainK V hV
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
  let codeA := (codedUniformOn A hA).code
  obtain ⟨_haFinite, haValue, haBound⟩ := prop_min_hereditary_a_setup V A hA x n delta
    cKappa₀ cBound cKappa (hBound x n A hA delta) hx hmin (by dsimp [cKappa]; omega)
  let a := (plainK V codeA).toNat
  have hCodeSwap : omegaFixedCode q a = omegaFixedCode c a :=
    omegaFixedCode_eq_of_isCodeFor hq hc a
  rw [hCodeSwap]
  by_cases hDelta : delta < n
  · let i := (setComplexity U A hA).toNat
    have hiFinite : setComplexity U A hA ≠ ⊤ := by
      obtain ⟨cTwo, hTwo⟩ := KPPlain_le_two_mul_length U hU
      unfold setComplexity
      exact ne_top_of_le_ne_top
        (ENat.natCast_ne_top (2 * codeA.length + cTwo)) (hTwo codeA)
    have hiValue : setComplexity U A hA = (i : ENat) :=
      (ENat.natCast_toNat hiFinite).symm
    have hDescA : IsIJDescription U x A hA i (finiteSetLogCard A) :=
      ⟨hmin.1, le_of_eq hiValue, finiteSetLogCard_spec A⟩
    obtain ⟨m, r, hxB, hm, hcardB, hplainB, _hprefixB,
        _hmLower, htwoB, hBA⟩ :=
      hBetter x n i (finiteSetLogCard A) A hA hx hDescA
    let B := standardBlock c m r x
    let hB : B.Nonempty := ⟨x, hxB⟩
    let b := (plainK V (codedUniformOn B hB).code).toNat
    have hbFinite : plainK V (codedUniformOn B hB).code ≠ ⊤ := by
      exact ne_top_of_le_ne_top
        (ENat.natCast_ne_top (i + logSlack cBetter m)) hplainB
    have hbValue : plainK V (codedUniformOn B hB).code = (b : ENat) :=
      (ENat.natCast_toNat hbFinite).symm
    have hmVisible : m ≤ n + logSlack cBetter n := by
      exact hm.trans (by omega)
    have hBetterSlack :
        logSlack cBetter m ≤ logSlack cBetterFold n := by
      exact (logSlack_mono_right cBetter hmVisible).trans
        (hBetterFold n)
    have hStdSlack : logSlack cStd m ≤ logSlack cStdFold n := by
      exact (logSlack_mono_right cStd hmVisible).trans (hStdFold n)
    have hiBound := prop_min_hereditary_i_bound V U A hA a i n delta cPrefix cBound
      haValue haBound
      (hPrefix codeA [] a (n + delta + logSlack cBound n)) hiValue
    have hlogB : finiteSetLogCard B = r := by
      unfold finiteSetLogCard
      rw [hcardB, Nat.clog_pow 2 r (by norm_num)]
    have hcKappaBound : cPrefixAbsorb + cBetter + cBetterFold ≤ cKappa := by
      dsimp [cKappa]; omega
    have hSlackSum :
        logSlack cPrefix (n + delta + logSlack cBound n) +
            logSlack cBetter n + logSlack cBetter m ≤
          logSlack cKappa n := by
      have hmerge : logSlack cPrefixAbsorb n + logSlack cBetter n + logSlack cBetterFold n =
          logSlack (cPrefixAbsorb + cBetter + cBetterFold) n := by
        unfold logSlack
        ring
      have hmono := logSlack_mono_left hcKappaBound n
      have hprefix := hPrefixAbsorb n delta hDelta
      omega
    have hTwoPartB := plainSetComplexity_two_part_le_of_two_part_le V hA hB
      haValue (by rw [hlogB]; exact htwoB) (by omega) hiBound hSlackSum
    have hGap : plainSetComplexity V A hA ≤
        plainSetComplexity V B hB + (delta : ENat) :=
      minimalModel_competitor_complexity_gap hmin hxB hTwoPartB
    have hab : a ≤ b + delta := by
      have h : (a : ENat) ≤ (b : ENat) + (delta : ENat) := by
        rw [← haValue, ← hbValue]
        exact hGap
      exact_mod_cast h
    have hcModelBound : cBetter + cBetterFold + cBound ≤ cModel := by
      dsimp [cModel]; omega
    have hbBound := prop_min_hereditary_b_bound V B hB b r m n cBetter cBetterFold cBound
      cModel hbValue htwoB hmVisible hBetterSlack hcModelBound
    have haN : a ≤ n + delta + logSlack cModel n := by
      calc
        a ≤ n + delta + logSlack cBound n := haBound
        _ ≤ n + delta + logSlack cModel n := by
          gcongr
          exact logSlack_mono_left (by dsimp [cModel]; omega) n
    have hOmegaB := (hStd m r b x hxB hbValue).2
    have hOmegaBVisible :
        condK V (omegaFixedCode c b) (codedUniformOn B hB).code ≤
          (logSlack cStdFold n : ENat) :=
      hOmegaB.trans (by exact_mod_cast hStdSlack)
    have hBAVisible :
        condK V (codedUniformOn B hB).code codeA ≤
          (logSlack cBetterFold n : ENat) :=
      hBA.trans (by exact_mod_cast hBetterSlack)
    have hOmegaGap := prop_min_hereditary_omega_gap V c a b n delta cBridge cBridgeAbsorb
      cModel hBridge (hBridgeAbsorb n delta) hab haN hbBound hDelta
    have hFinal := prop_min_hereditary_condK_chain V codeA (codedUniformOn B hB).code
      (omegaFixedCode c a) (omegaFixedCode c b) (logSlack cBetterFold n) (logSlack cStdFold n)
      (delta + logSlack cBridgeAbsorb n) cTrans hTrans hBAVisible hOmegaBVisible hOmegaGap
    calc
      condK V (omegaFixedCode c a) codeA
          ≤ ((2 * (2 * logSlack cBetterFold n +
              logSlack cStdFold n + cTrans) +
              (delta + logSlack cBridgeAbsorb n) + cTrans : Nat) : ENat) := hFinal
      _ ≤ ((cOut * delta + logSlack cOut n : Nat) : ENat) := by
          apply Nat.cast_le.mpr
          exact prop_min_hereditary_arith_of_lt_delta rfl n delta
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
          exact prop_min_hereditary_arith_of_le_delta cBetterFold cStdFold cBridgeAbsorb
            cTrans rfl haBound hLarge

end Kolmogorov
