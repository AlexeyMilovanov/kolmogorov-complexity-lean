import KolmogorovMathlib.CommonInformation.Basic

/-!
# Common Information: intermediate conditional descriptions

Chapter-local infrastructure for SUV Exercise 306.  The central reusable fact
is a logarithmic plain conditional-complexity chain inequality in exact-value
form.  It is proved through the existing conditional two-stage prefix builder;
no plain chain rule is assumed.
-/

namespace Kolmogorov

/-- The concrete decoder that treats its program literally and pairs it with
the current condition. -/
def pairConditionProgramDecompressor : Map := fun pr =>
  Part.some (pairCode pr.2 pr.1)

lemma pairConditionProgramDecompressor_isDecompressor :
    isDecompressor pairConditionProgramDecompressor := by
  change Partrec
    (fun pr : BitString × BitString =>
      Part.some (pairCode pr.2 pr.1))
  exact (pairCode_primrec.comp Primrec.snd Primrec.fst).to_comp.partrec

/-- Given `x`, a literal program `p` describes the canonical pair `(x,p)` with
only a uniform additive overhead. -/
theorem condK_pair_condition_program_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x p : BitString,
      condK V (pairCode x p) x ≤ (p.length : ENat) + (c : ENat) := by
  obtain ⟨c, hc⟩ := hV.2 pairConditionProgramDecompressor
    pairConditionProgramDecompressor_isDecompressor
  refine ⟨c, fun x p => ?_⟩
  calc
    condK V (pairCode x p) x
        ≤ condK pairConditionProgramDecompressor (pairCode x p) x +
            (c : ENat) := hc (pairCode x p) x
    _ ≤ (p.length : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨p, ⟨trivial, rfl⟩, rfl⟩

/-- Decoder for the suffix of a split conditional program: recover the saved
prefix and original condition from the intermediate pair. -/
def splitConditionSuffixDecompressor (V : Map) : Map := fun pr =>
  V (decodeSecond pr.2 ++ pr.1, decodeFirst pr.2)

lemma splitConditionSuffixDecompressor_isDecompressor
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (splitConditionSuffixDecompressor V) := by
  change Partrec
    (fun pr : BitString × BitString =>
      V (decodeSecond pr.2 ++ pr.1, decodeFirst pr.2))
  have hInput :
      Computable
        (fun pr : BitString × BitString =>
          (decodeSecond pr.2 ++ pr.1, decodeFirst pr.2)) :=
    (Computable.list_append.comp
      (decodeSecond_computable.comp Computable.snd)
      Computable.fst).pair
        (decodeFirst_computable.comp Computable.snd)
  exact Partrec.comp hV hInput

/-- If `p₁ ++ p₂` produces `y` from `x`, then `p₂` describes `y` given the
intermediate condition `(x,p₁)`, with only a uniform additive overhead. -/
theorem condK_output_given_splitCondition_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y p₁ p₂ : BitString,
      produces V (p₁ ++ p₂) x y →
      condK V y (pairCode x p₁) ≤ (p₂.length : ENat) + (c : ENat) := by
  obtain ⟨c, hc⟩ := hV.2 (splitConditionSuffixDecompressor V)
    (splitConditionSuffixDecompressor_isDecompressor V hV.1)
  refine ⟨c, fun x y p₁ p₂ hp => ?_⟩
  have hprod :
      produces (splitConditionSuffixDecompressor V) p₂
        (pairCode x p₁) y := by
    change y ∈ V
      (decodeSecond (pairCode x p₁) ++ p₂,
        decodeFirst (pairCode x p₁))
    simpa [decodeFirst_pairCode, decodeSecond_pairCode] using hp
  calc
    condK V y (pairCode x p₁)
        ≤ condK (splitConditionSuffixDecompressor V) y
            (pairCode x p₁) + (c : ENat) :=
      hc y (pairCode x p₁)
    _ ≤ (p₂.length : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨p₂, hprod, rfl⟩

/-- Plain conditional transitivity with logarithmic overhead, stated using
exact finite values and without subtraction:

`C(y | x) ≤ C(z | x) + C(y | z) + O(log(C(z|x)+C(y|z))))`.

The proof turns the two exact plain descriptions into prefix descriptions and
uses the existing conditional two-stage prefix builder with second-stage
context `z`. -/
theorem condK_chain_upper_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y z : BitString, ∀ kzx kyz kyx : Nat,
      HasPlainConditionalComplexityValue V z x kzx →
      HasPlainConditionalComplexityValue V y z kyz →
      HasPlainConditionalComplexityValue V y x kyx →
      kyx ≤ kzx + kyz + logSlack c (kzx + kyz + 1) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cBridge, hBridge⟩ :=
    KP_le_condK_add_log_of_value U V hU hV
  obtain ⟨cDecode, hDecode⟩ :=
    condK_map_le_KP V U hV hU decodeSecond decodeSecond_computable
  let ctx : BitString → BitString → Nat → BitString := fun _ z _ => z
  have hctx :
      Computable
        (fun p : (BitString × BitString) × Nat =>
          ctx p.1.1 p.1.2 p.2) :=
    Computable.snd.comp Computable.fst
  have hM :
      IsPrefixDecompressor (condTwoStagePairBuilder U ctx) :=
    condTwoStagePairBuilder_isPrefixDecompressor
      hU.isDecompressor hU.isPrefixMachine hctx
  obtain ⟨cInv, hInv⟩ := hU.invariance hM
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound (cBridge + cBridge) 1 1
  let cConst := cInv + cDecode
  let C := cFold + cConst
  refine ⟨C, fun x y z kzx kyz kyx hzx hyz hyx => ?_⟩
  have hkzxFinite : KP U z x ≠ ⊤ := by
    have hle := hBridge z x kzx hzx
    exact ne_top_of_le_ne_top
      (by
        rw [WithTop.add_ne_top]
        exact ⟨ENat.coe_ne_top _, ENat.coe_ne_top _⟩)
      hle
  have hkyzFinite : KP U y z ≠ ⊤ := by
    have hle := hBridge y z kyz hyz
    exact ne_top_of_le_ne_top
      (by
        rw [WithTop.add_ne_top]
        exact ⟨ENat.coe_ne_top _, ENat.coe_ne_top _⟩)
      hle
  obtain ⟨p, hp, hpLen⟩ :=
    exists_program_of_KP_ne_top (M := U) (x := z) (y := x) hkzxFinite
  obtain ⟨q, hq, hqLen⟩ :=
    exists_program_of_KP_ne_top (M := U) (x := y) (y := z) hkyzFinite
  have hBuilder :
      KP (condTwoStagePairBuilder U ctx) (pairCode z y) x ≤
        KP U z x + KP U y z := by
    calc
      KP (condTwoStagePairBuilder U ctx) (pairCode z y) x
          ≤ ((p.length + q.length : Nat) : ENat) :=
        KP_condTwoStagePairBuilder_le_of_produces
          (ctx := ctx) hU.isPrefixMachine hp hq
      _ = KP U z x + KP U y z := by
        rw [Nat.cast_add, hpLen, hqLen]
  have hPair :
      KP U (pairCode z y) x ≤
        KP U z x + KP U y z + (cInv : ENat) := by
    calc
      KP U (pairCode z y) x
          ≤ KP (condTwoStagePairBuilder U ctx) (pairCode z y) x +
              (cInv : ENat) := hInv (pairCode z y) x
      _ ≤ (KP U z x + KP U y z) + (cInv : ENat) := by
        gcongr
      _ = KP U z x + KP U y z + (cInv : ENat) := rfl
  have hLogs :
      logSlack cBridge (kzx + 1) +
          logSlack cBridge (kyz + 1) ≤
        logSlack cFold (kzx + kyz + 1) := by
    calc
      logSlack cBridge (kzx + 1) +
            logSlack cBridge (kyz + 1)
          ≤ logSlack (cBridge + cBridge)
              ((kzx + 1) + (kyz + 1)) :=
        logSlack_add_logSlack_le cBridge cBridge (kzx + 1) (kyz + 1)
      _ = logSlack (cBridge + cBridge)
            (1 * (kzx + kyz + 1) + 1) := by
        congr 1
        omega
      _ ≤ logSlack cFold (kzx + kyz + 1) :=
        hFold (kzx + kyz + 1)
  have hOverhead :
      logSlack cBridge (kzx + 1) +
          logSlack cBridge (kyz + 1) + cConst ≤
        logSlack C (kzx + kyz + 1) := by
    calc
      logSlack cBridge (kzx + 1) +
            logSlack cBridge (kyz + 1) + cConst
          ≤ logSlack cFold (kzx + kyz + 1) + cConst := by
        omega
      _ ≤ logSlack C (kzx + kyz + 1) := by
        simpa [C] using
          logSlack_add_nat_le cFold cConst (kzx + kyz + 1)
  have hMain :
      (kyx : ENat) ≤
        ((kzx + kyz + logSlack C (kzx + kyz + 1) : Nat) : ENat) := by
    calc
      (kyx : ENat) = condK V y x := hyx.symm
      _ = condK V (decodeSecond (pairCode z y)) x := by
        rw [decodeSecond_pairCode]
      _ ≤ KP U (pairCode z y) x + (cDecode : ENat) :=
        hDecode (pairCode z y) x
      _ ≤ (KP U z x + KP U y z + (cInv : ENat)) +
            (cDecode : ENat) := by
        gcongr
      _ ≤ (((kzx : ENat) +
              (logSlack cBridge (kzx + 1) : ENat)) +
            ((kyz : ENat) +
              (logSlack cBridge (kyz + 1) : ENat)) +
            (cInv : ENat)) + (cDecode : ENat) := by
        gcongr
        · exact hBridge z x kzx hzx
        · exact hBridge y z kyz hyz
      _ = ((kzx + kyz +
            (logSlack cBridge (kzx + 1) +
              logSlack cBridge (kyz + 1) + cConst) : Nat) : ENat) := by
        dsimp [cConst]
        push_cast
        ring
      _ ≤ ((kzx + kyz + logSlack C
            (kzx + kyz + 1) : Nat) : ENat) := by
        exact_mod_cast Nat.add_le_add_left hOverhead (kzx + kyz)
  exact_mod_cast hMain

/-- SUV Exercise 306: if `C(y|x)=n`, there is an intermediate string `z`
which divides this conditional information into two near-equal parts.  The two
conditional complexities are given exact natural witnesses, and closeness is
expressed by two additive inequalities rather than truncated subtraction.  The
uniform logarithmic budget is measured at the exact pair complexity
`C(x,y)`. -/
theorem exists_intermediate_split_conditionalComplexity
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString, ∀ n kxy : Nat,
      HasPlainConditionalComplexityValue V y x n →
      HasPlainComplexityValue V (pairCode x y) kxy →
      ∃ z : BitString, ∃ nzx nyz : Nat,
        HasPlainConditionalComplexityValue V z x nzx ∧
        HasPlainConditionalComplexityValue V y z nyz ∧
        nzx ≤ n / 2 + logSlack c (kxy + 1) ∧
        n / 2 ≤ nzx + logSlack c (kxy + 1) ∧
        nyz ≤ n - n / 2 + logSlack c (kxy + 1) ∧
        n - n / 2 ≤ nyz + logSlack c (kxy + 1) := by
  obtain ⟨cLeft, hLeft⟩ := condK_pair_condition_program_le V hV
  obtain ⟨cRight, hRight⟩ :=
    condK_output_given_splitCondition_le V hV
  obtain ⟨cChain, hChain⟩ := condK_chain_upper_values V hV
  obtain ⟨cPair, hPair⟩ := condK_right_le_pairPlainK V hV
  let b := cPair + cLeft + cRight
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain 1 b
  let C := cFold + cLeft + cRight
  refine ⟨C, fun x y n kxy hnyx hxy => ?_⟩
  obtain ⟨p, hp, hpLen⟩ := hnyx.exists_program
  let p₁ := p.take (n / 2)
  let p₂ := p.drop (n / 2)
  let z := pairCode x p₁
  have hp₁Len : p₁.length = n / 2 := by
    dsimp [p₁]
    rw [List.length_take, hpLen]
    exact Nat.min_eq_left (Nat.div_le_self n 2)
  have hp₂Len : p₂.length = n - n / 2 := by
    dsimp [p₂]
    rw [List.length_drop, hpLen]
  have hpAppend : p₁ ++ p₂ = p := by
    dsimp [p₁, p₂]
    exact List.take_append_drop (n / 2) p
  obtain ⟨nzx, hnzx⟩ :=
    exists_plainConditionalComplexityValue V hV z x
  obtain ⟨nyz, hnyz⟩ :=
    exists_plainConditionalComplexityValue V hV y z
  have hnzxUpperRaw : nzx ≤ n / 2 + cLeft := by
    have h :
        (nzx : ENat) ≤ ((n / 2 + cLeft : Nat) : ENat) := by
      calc
        (nzx : ENat) = condK V z x := hnzx.symm
        _ ≤ (p₁.length : ENat) + (cLeft : ENat) := hLeft x p₁
        _ = ((n / 2 + cLeft : Nat) : ENat) := by
          rw [hp₁Len, Nat.cast_add]
    exact_mod_cast h
  have hnyzUpperRaw : nyz ≤ n - n / 2 + cRight := by
    have h :
        (nyz : ENat) ≤
          ((n - n / 2 + cRight : Nat) : ENat) := by
      calc
        (nyz : ENat) = condK V y z := hnyz.symm
        _ ≤ (p₂.length : ENat) + (cRight : ENat) := by
          dsimp [z]
          apply hRight x y p₁ p₂
          rw [hpAppend]
          exact hp
        _ = ((n - n / 2 + cRight : Nat) : ENat) := by
          rw [hp₂Len, Nat.cast_add]
    exact_mod_cast h
  have hnPair : n ≤ kxy + cPair := by
    have h :
        (n : ENat) ≤ (kxy : ENat) + (cPair : ENat) := by
      calc
        (n : ENat) = condK V y x := hnyx.symm
        _ ≤ pairPlainK V x y + (cPair : ENat) := hPair x y
        _ = (kxy : ENat) + (cPair : ENat) := by
          rw [pairPlainK, hxy]
    exact_mod_cast h
  have hChainInst :
      n ≤ nzx + nyz + logSlack cChain (nzx + nyz + 1) :=
    hChain x y z nzx nyz n hnzx hnyz hnyx
  have hSumArg :
      nzx + nyz + 1 ≤ 1 * (kxy + 1) + b := by
    dsimp [b]
    omega
  have hChainFold :
      logSlack cChain (nzx + nyz + 1) ≤
        logSlack cFold (kxy + 1) :=
    (logSlack_mono_right cChain hSumArg).trans
      (hFold (kxy + 1))
  have hConstBudget (d : Nat) (hd : d ≤ C) :
      d ≤ logSlack C (kxy + 1) := by
    unfold logSlack
    omega
  have hLeftBudget :
      logSlack cFold (kxy + 1) + cLeft ≤
        logSlack C (kxy + 1) := by
    calc
      logSlack cFold (kxy + 1) + cLeft
          ≤ logSlack (cFold + cLeft) (kxy + 1) :=
        logSlack_add_nat_le cFold cLeft (kxy + 1)
      _ ≤ logSlack C (kxy + 1) :=
        logSlack_mono_left (by dsimp [C]; omega) (kxy + 1)
  have hRightBudget :
      logSlack cFold (kxy + 1) + cRight ≤
        logSlack C (kxy + 1) := by
    calc
      logSlack cFold (kxy + 1) + cRight
          ≤ logSlack (cFold + cRight) (kxy + 1) :=
        logSlack_add_nat_le cFold cRight (kxy + 1)
      _ ≤ logSlack C (kxy + 1) :=
        logSlack_mono_left (by dsimp [C]; omega) (kxy + 1)
  have hnzxUpper :
      nzx ≤ n / 2 + logSlack C (kxy + 1) := by
    exact hnzxUpperRaw.trans
      (Nat.add_le_add_left
        (hConstBudget cLeft (by dsimp [C]; omega)) (n / 2))
  have hnyzUpper :
      nyz ≤ n - n / 2 + logSlack C (kxy + 1) := by
    exact hnyzUpperRaw.trans
      (Nat.add_le_add_left
        (hConstBudget cRight (by dsimp [C]; omega))
        (n - n / 2))
  have hnzxLower :
      n / 2 ≤ nzx + logSlack C (kxy + 1) := by
    omega
  have hnyzLower :
      n - n / 2 ≤ nyz + logSlack C (kxy + 1) := by
    omega
  exact
    ⟨z, nzx, nyz, hnzx, hnyz, hnzxUpper, hnzxLower,
      hnyzUpper, hnyzLower⟩

end Kolmogorov
