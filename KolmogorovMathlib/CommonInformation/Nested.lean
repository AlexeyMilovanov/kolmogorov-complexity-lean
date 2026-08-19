import KolmogorovMathlib.CommonInformation.Intermediate

/-!
# Common Information: nested representations

Small literal-prefix decoders and the proof of SUV Theorem 222.
-/

namespace Kolmogorov

open CodedFiniteDistribution

/-- A literal prefix of `w` is uniformly simple given `w` and the encoded
prefix length. -/
theorem condK_take_given_pairCode_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (w : BitString) (n : Nat),
      condK V (w.take n) (pairCode w (natCode n)) ≤ (c : ENat) := by
  let f : BitString → BitString := fun ctx =>
    (decodeFirst ctx).take (decodeNatCode (decodeSecond ctx))
  have hf : Computable f := by
    exact
      (Primrec.list_take.comp (decodeNatCode_primrec.comp decodeSecond_primrec')
        decodeFirst_primrec').to_comp
  obtain ⟨c, hc⟩ := condKComp V hV f hf
  refine ⟨c, fun w n => ?_⟩
  simpa [f, decodeFirst_pairCode, decodeSecond_pairCode,
    decodeNatCode_natCode] using hc (pairCode w (natCode n))

/-- Literal concatenation is uniformly recoverable from the canonical pair of
its two parts. -/
theorem condK_append_recover_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ a b : BitString,
      condK V (a ++ b) (pairCode a b) ≤ (c : ENat) := by
  let f : BitString → BitString := fun ctx =>
    decodeFirst ctx ++ decodeSecond ctx
  have hf : Computable f :=
    Computable.list_append.comp decodeFirst_computable decodeSecond_computable
  obtain ⟨c, hc⟩ := condKComp V hV f hf
  refine ⟨c, fun a b => ?_⟩
  simpa [f, decodeFirst_pairCode, decodeSecond_pairCode] using
    hc (pairCode a b)

theorem plainIncompressible_of_conditionalPrefixProgram_value
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ x y p (k kp : Nat),
      HasPlainConditionalComplexityValue V x y k →
      (kp : ENat) = KP U x y →
      produces U p y x →
      p.length = kp →
      PlainIncompressibleWithin V p (logSlack c (k + 1)) := by
  obtain ⟨cBridge, hBridge⟩ :=
    KP_le_condK_add_log_of_value U V hU hV
  let D : Map := fun pr =>
    (V (pr.1, [])).bind (fun p => U (p, pr.2))
  have hFirst :
      Partrec (fun pr : BitString × BitString => V (pr.1, [])) :=
    Partrec.comp hV.1
      (Computable.pair Computable.fst (Computable.const []))
  have hSecond :
      Partrec
        (fun q : (BitString × BitString) × BitString =>
          U (q.2, q.1.2)) :=
    Partrec.comp hU.isDecompressor
      (Computable.pair Computable.snd
        (Computable.snd.comp Computable.fst))
  have hD : isDecompressor D := Partrec.bind hFirst hSecond
  obtain ⟨cRun, hRun⟩ := hV.2 D hD
  let C := cBridge + cRun
  refine ⟨C, fun x y p k kp hx hkp hp hpLen => ?_⟩
  obtain ⟨kPlain, hkPlain⟩ :=
    exists_plainComplexityValue V hV p
  obtain ⟨r, hr, hrLen⟩ := hkPlain.exists_program
  have hDprod : produces D r y x := by
    exact Part.mem_bind_iff.mpr ⟨p, hr, hp⟩
  have hkLowerE :
      (k : ENat) ≤ (kPlain : ENat) + (cRun : ENat) := by
    calc
      (k : ENat) = condK V x y := hx.symm
      _ ≤ condK D x y + (cRun : ENat) := hRun x y
      _ ≤ (r.length : ENat) + (cRun : ENat) := by
        gcongr
        exact sInf_le ⟨r, hDprod, rfl⟩
      _ = (kPlain : ENat) + (cRun : ENat) := by
        rw [hrLen]
  have hkLower : k ≤ kPlain + cRun := by
    exact_mod_cast hkLowerE
  have hkpUpperE :
      (kp : ENat) ≤
        (k : ENat) + (logSlack cBridge (k + 1) : ENat) := by
    rw [hkp]
    exact hBridge x y k hx
  have hkpUpper :
      kp ≤ k + logSlack cBridge (k + 1) := by
    exact_mod_cast hkpUpperE
  have hSlack :
      logSlack cBridge (k + 1) + cRun ≤
        logSlack C (k + 1) := by
    simpa [C] using
      logSlack_add_nat_le cBridge cRun (k + 1)
  have hIncomp :
      kp ≤ kPlain + logSlack C (k + 1) := by
    calc
      kp ≤ k + logSlack cBridge (k + 1) := hkpUpper
      _ ≤ (kPlain + cRun) +
          logSlack cBridge (k + 1) :=
        Nat.add_le_add_right hkLower _
      _ = kPlain +
          (logSlack cBridge (k + 1) + cRun) := by omega
      _ ≤ kPlain + logSlack C (k + 1) :=
        Nat.add_le_add_left hSlack _
  unfold PlainIncompressibleWithin
  rw [hpLen, hkPlain]
  exact_mod_cast hIncomp


theorem condK_output_given_prefixConcat_le
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ p q x y,
      produces U p [] y →
      produces U q y x →
      condK V x (p ++ q) ≤ (c : ENat) := by
  let ctx : BitString → Nat → BitString := fun y _ => y
  have hctx :
      Computable (fun pr : BitString × Nat => ctx pr.1 pr.2) :=
    Computable.fst
  have hBuilder :
      isDecompressor (twoStagePairBuilder U ctx) :=
    twoStagePairBuilder_isDecompressor
      hU.isDecompressor hU.isPrefixMachine hctx
  let f : BitString →. BitString := fun w =>
    (twoStagePairBuilder U ctx (w, [])).map decodeSecond
  have hBuilderRun :
      Partrec (fun w : BitString =>
        twoStagePairBuilder U ctx (w, [])) :=
    Partrec.comp hBuilder
      (Computable.pair Computable.id (Computable.const []))
  have hf : Partrec f :=
    Partrec.map hBuilderRun
      (decodeSecond_computable.comp Computable.snd)
  let D : Map := fun pr => f pr.2
  have hD : isDecompressor D :=
    Partrec.comp hf Computable.snd
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c, fun p q x y hp hq => ?_⟩
  have hPair :
      produces (twoStagePairBuilder U ctx) (p ++ q) []
        (pairCode y x) := by
    apply twoStagePairBuilder_produces_of_spec hU.isPrefixMachine
    exact ⟨p, q, y, x, rfl, hp, by simpa [ctx] using hq, rfl⟩
  have hfProd : x ∈ f (p ++ q) := by
    exact
      (Part.mem_map decodeSecond hPair) |>
        (by simpa [f, decodeSecond_pairCode] using ·)
  have hDprod : produces D [] (p ++ q) x := hfProd
  calc
    condK V x (p ++ q)
        ≤ condK D x (p ++ q) + (c : ENat) :=
      hc x (p ++ q)
    _ ≤ (0 : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨[], hDprod, rfl⟩
    _ = (c : ENat) := zero_add _

theorem prefixShortestDescription_equivalent
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ y p (k kp : Nat),
      HasPlainComplexityValue V y k →
      (kp : ENat) = KPPlain U y →
      produces U p [] y →
      p.length = kp →
      PlainEquivalentWithin V y p (logSlack c (k + 1)) := by
  obtain ⟨cBridge, hBridge⟩ :=
    KP_le_condK_add_log_of_value U V hU hV
  obtain ⟨cChain, hChain⟩ :=
    pairPlainK_chain_lower_values V hV
  obtain ⟨bBridge, hBridgeLinear⟩ :=
    logSlack_le_add_const cBridge
  let evalCondition : Map := fun pr => U (pr.2, [])
  have hEvalCondition : isDecompressor evalCondition :=
    Partrec.comp hU.isDecompressor
      (Computable.pair Computable.snd (Computable.const []))
  obtain ⟨cForward, hForward⟩ :=
    hV.2 evalCondition hEvalCondition
  let pairProgram : Map := fun pr =>
    (U (pr.1, [])).map (fun y => pairCode y pr.1)
  have hPairRun :
      Partrec
        (fun pr : BitString × BitString => U (pr.1, [])) :=
    Partrec.comp hU.isDecompressor
      (Computable.pair Computable.fst (Computable.const []))
  have hPairCode₂ :
      Computable₂ (fun x y : BitString => pairCode x y) :=
    pairCode_computable
  have hPairOutput :
      Computable
        (fun q : (BitString × BitString) × BitString =>
          pairCode q.2 q.1.1) :=
    hPairCode₂.comp Computable.snd
      (Computable.fst.comp Computable.fst)
  have hPairProgram : isDecompressor pairProgram :=
    Partrec.map hPairRun hPairOutput
  obtain ⟨cPair, hPair⟩ := hV.2 pairProgram hPairProgram
  let bPair := bBridge + cPair
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cChain 2 bPair
  let C := cForward + cBridge + cFold + cPair
  refine ⟨C, fun y p k kp hy hkp hp hpLen => ?_⟩
  obtain ⟨kPair, hkPair⟩ :=
    exists_plainComplexityValue V hV (pairCode y p)
  obtain ⟨kCond, hkCond⟩ :=
    exists_plainConditionalComplexityValue V hV p y
  have hkpUpperE :
      (kp : ENat) ≤
        (k : ENat) + (logSlack cBridge (k + 1) : ENat) := by
    rw [hkp]
    exact hBridge y [] k hy
  have hkpUpper :
      kp ≤ k + logSlack cBridge (k + 1) := by
    exact_mod_cast hkpUpperE
  have hPairProd :
      produces pairProgram p [] (pairCode y p) := by
    exact Part.mem_map (fun z => pairCode z p) hp
  have hkPairUpperE :
      (kPair : ENat) ≤ (kp : ENat) + (cPair : ENat) := by
    calc
      (kPair : ENat) = pairPlainK V y p := by
        rw [pairPlainK, hkPair]
      _ ≤ plainK pairProgram (pairCode y p) + (cPair : ENat) :=
        hPair (pairCode y p) []
      _ ≤ (p.length : ENat) + (cPair : ENat) := by
        gcongr
        exact sInf_le ⟨p, hPairProd, rfl⟩
      _ = (kp : ENat) + (cPair : ENat) := by
        rw [hpLen]
  have hkPairUpper :
      kPair ≤ kp + cPair := by
    exact_mod_cast hkPairUpperE
  have hkPairLinear :
      kPair + 1 ≤ 2 * (k + 1) + bPair := by
    have hLog := hBridgeLinear (k + 1)
    dsimp [bPair]
    omega
  have hChainLog :
      logSlack cChain (kPair + 1) ≤
        logSlack cFold (k + 1) := by
    calc
      logSlack cChain (kPair + 1)
          ≤ logSlack cChain
              (2 * (k + 1) + bPair) :=
        logSlack_mono_right cChain hkPairLinear
      _ ≤ logSlack cFold (k + 1) := by
        exact hFold (k + 1)
  have hChainInst :
      k + kCond ≤ kPair + logSlack cChain (kPair + 1) :=
    hChain y p k kCond kPair hy hkCond hkPair
  have hReverseRaw :
      kCond ≤
        logSlack cBridge (k + 1) + cPair +
          logSlack cFold (k + 1) := by
    omega
  have hReverseBudget :
      kCond ≤ logSlack C (k + 1) := by
    calc
      kCond
          ≤ logSlack cBridge (k + 1) + cPair +
              logSlack cFold (k + 1) := hReverseRaw
      _ = (logSlack cBridge (k + 1) +
              logSlack cFold (k + 1)) + cPair := by omega
      _ = logSlack (cBridge + cFold) (k + 1) + cPair := by
        rw [logSlack_add_const]
      _ ≤ logSlack (cBridge + cFold + cPair) (k + 1) :=
        logSlack_add_nat_le (cBridge + cFold) cPair (k + 1)
      _ ≤ logSlack C (k + 1) :=
        logSlack_mono_left (by dsimp [C]; omega) (k + 1)
  have hForwardProd :
      produces evalCondition [] p y := hp
  have hForwardBound :
      condK V y p ≤ (cForward : ENat) := by
    calc
      condK V y p
          ≤ condK evalCondition y p + (cForward : ENat) :=
        hForward y p
      _ ≤ (0 : ENat) + (cForward : ENat) := by
        gcongr
        exact sInf_le ⟨[], hForwardProd, rfl⟩
      _ = (cForward : ENat) := zero_add _
  have hForwardBudget :
      cForward ≤ logSlack C (k + 1) := by
    unfold logSlack
    dsimp [C]
    omega
  unfold PlainEquivalentWithin
  constructor
  · exact hForwardBound.trans (by exact_mod_cast hForwardBudget)
  · calc
      condK V p y = (kCond : ENat) := hkCond
      _ ≤ (logSlack C (k + 1) : ENat) := by
        exact_mod_cast hReverseBudget

/-- A concatenated pair of prefix programs carries both the represented pair
and the represented second output together with the literal concatenation.
These two plain-complexity bounds are the computable content used in Theorem
222; the shortest prefix programs themselves are not selected computably. -/
theorem prefixConcat_plainPair_bounds
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ p q x y : BitString,
      produces U p [] y →
      produces U q y x →
      pairPlainK V x y ≤ plainK V (p ++ q) + (c : ENat) ∧
      pairPlainK V x (p ++ q) ≤
        plainK V (p ++ q) + (c : ENat) := by
  let ctx : BitString → Nat → BitString := fun y _ => y
  have hctx :
      Computable (fun pr : BitString × Nat => ctx pr.1 pr.2) :=
    Computable.fst
  have hBuilder :
      isDecompressor (twoStagePairBuilder U ctx) :=
    twoStagePairBuilder_isDecompressor
      hU.isDecompressor hU.isPrefixMachine hctx
  have hBuilderRun :
      Partrec
        (fun w : BitString =>
          twoStagePairBuilder U ctx (w, [])) :=
    Partrec.comp hBuilder
      (Computable.pair Computable.id (Computable.const []))
  let pairXY : BitString →. BitString := fun w =>
    (twoStagePairBuilder U ctx (w, [])).map
      (fun yx => pairCode (decodeSecond yx) (decodeFirst yx))
  have hPairCode₂ :
      Computable₂ (fun a b : BitString => pairCode a b) :=
    pairCode_computable
  have hPairXYMap :
      Computable
        (fun r : BitString × BitString =>
          pairCode (decodeSecond r.2) (decodeFirst r.2)) :=
    hPairCode₂.comp
      (decodeSecond_computable.comp Computable.snd)
      (decodeFirst_computable.comp Computable.snd)
  have hPairXY : Partrec pairXY :=
    Partrec.map hBuilderRun hPairXYMap
  let pairXW : BitString →. BitString := fun w =>
    (twoStagePairBuilder U ctx (w, [])).map
      (fun yx => pairCode (decodeSecond yx) w)
  have hPairXWMap :
      Computable
        (fun r : BitString × BitString =>
          pairCode (decodeSecond r.2) r.1) :=
    hPairCode₂.comp
      (decodeSecond_computable.comp Computable.snd)
      Computable.fst
  have hPairXW : Partrec pairXW :=
    Partrec.map hBuilderRun hPairXWMap
  let DXY : Map := fun pr =>
    (V (pr.1, [])).bind pairXY
  have hVRun :
      Partrec
        (fun pr : BitString × BitString => V (pr.1, [])) :=
    Partrec.comp hV.1
      (Computable.pair Computable.fst (Computable.const []))
  have hDXY : isDecompressor DXY :=
    Partrec.bind hVRun
      (Partrec.comp hPairXY Computable.snd)
  obtain ⟨cXY, hXY⟩ := hV.2 DXY hDXY
  let DXX : Map := fun pr =>
    (V (pr.1, [])).bind pairXW
  have hDXX : isDecompressor DXX :=
    Partrec.bind hVRun
      (Partrec.comp hPairXW Computable.snd)
  obtain ⟨cXX, hXX⟩ := hV.2 DXX hDXX
  let C := cXY + cXX
  refine ⟨C, fun p q x y hp hq => ?_⟩
  have hBuilderProd :
      produces (twoStagePairBuilder U ctx) (p ++ q) []
        (pairCode y x) := by
    apply twoStagePairBuilder_produces_of_spec hU.isPrefixMachine
    exact ⟨p, q, y, x, rfl, hp, by simpa [ctx] using hq, rfl⟩
  have hPairXYProd :
      pairCode x y ∈ pairXY (p ++ q) := by
    have h :=
      Part.mem_map
        (fun yx => pairCode (decodeSecond yx) (decodeFirst yx))
        hBuilderProd
    simpa [pairXY, decodeFirst_pairCode, decodeSecond_pairCode] using h
  have hPairXWProd :
      pairCode x (p ++ q) ∈ pairXW (p ++ q) := by
    have h :=
      Part.mem_map
        (fun yx => pairCode (decodeSecond yx) (p ++ q))
        hBuilderProd
    simpa [pairXW, decodeSecond_pairCode] using h
  obtain ⟨kw, hkw⟩ :=
    exists_plainComplexityValue V hV (p ++ q)
  obtain ⟨r, hr, hrLen⟩ := hkw.exists_program
  have hDXYProd :
      produces DXY r [] (pairCode x y) :=
    Part.mem_bind_iff.mpr
      ⟨p ++ q, hr, hPairXYProd⟩
  have hDXXProd :
      produces DXX r [] (pairCode x (p ++ q)) :=
    Part.mem_bind_iff.mpr
      ⟨p ++ q, hr, hPairXWProd⟩
  constructor
  · calc
      pairPlainK V x y
          ≤ plainK DXY (pairCode x y) + (cXY : ENat) :=
        hXY (pairCode x y) []
      _ ≤ (r.length : ENat) + (cXY : ENat) := by
        gcongr
        exact sInf_le ⟨r, hDXYProd, rfl⟩
      _ = plainK V (p ++ q) + (cXY : ENat) := by
        rw [hrLen, hkw]
      _ ≤ plainK V (p ++ q) + (C : ENat) := by
        gcongr
        exact_mod_cast (show cXY ≤ C by dsimp [C]; omega)
  · calc
      pairPlainK V x (p ++ q)
          ≤ plainK DXX (pairCode x (p ++ q)) +
              (cXX : ENat) :=
        hXX (pairCode x (p ++ q)) []
      _ ≤ (r.length : ENat) + (cXX : ENat) := by
        gcongr
        exact sInf_le ⟨r, hDXXProd, rfl⟩
      _ = plainK V (p ++ q) + (cXX : ENat) := by
        rw [hrLen, hkw]
      _ ≤ plainK V (p ++ q) + (C : ENat) := by
        gcongr
        exact_mod_cast (show cXX ≤ C by dsimp [C]; omega)

/-- SUV Theorem 222: two strings have incompressible representatives
which are nested by literal prefix.  The equivalence and incompressibility
budget is exactly the source's
`O(C(y|x) + log C(x,y))`, expressed from exact finite values. -/
theorem exists_nested_incompressibleRepresentations
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString, ∀ kyx kxy : Nat,
      HasPlainConditionalComplexityValue V y x kyx →
      HasPlainComplexityValue V (pairCode x y) kxy →
      ∃ x' y' : BitString,
        y' <+: x' ∧
        PlainEquivalentWithin V x x'
          (kyx + logSlack c (kxy + 1)) ∧
        PlainEquivalentWithin V y y'
          (kyx + logSlack c (kxy + 1)) ∧
        PlainIncompressibleWithin V x'
          (kyx + logSlack c (kxy + 1)) ∧
        PlainIncompressibleWithin V y'
          (kyx + logSlack c (kxy + 1)) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cIncomp, hIncomp⟩ :=
    plainIncompressible_of_conditionalPrefixProgram_value V U hV hU
  obtain ⟨cConcat, hConcat⟩ :=
    condK_output_given_prefixConcat_le V U hV hU
  obtain ⟨cEquiv, hEquiv⟩ :=
    prefixShortestDescription_equivalent V U hV hU
  obtain ⟨cMeta, hMeta⟩ :=
    prefixConcat_plainPair_bounds V U hV hU
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cLower, hLower⟩ :=
    pairPlainK_chain_lower_values V hV
  obtain ⟨cUpper, hUpper⟩ :=
    pairPlainK_chain_upper_values V hV
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le V hV
  obtain ⟨cLeft, hLeft⟩ := pairPlainK_left_le V hV
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  obtain ⟨cBridge, hBridge⟩ :=
    KP_le_condK_add_log_of_value U V hU hV
  let swapPair : BitString → BitString := fun w =>
    pairCode (decodeSecond w) (decodeFirst w)
  have hPairCode₂ :
      Computable₂ (fun a b : BitString => pairCode a b) :=
    pairCode_computable
  have hSwapComputable : Computable swapPair :=
    hPairCode₂.comp decodeSecond_computable
      decodeFirst_computable
  obtain ⟨cSwap, hSwap⟩ :=
    plainKMapLe V hV swapPair hSwapComputable
  obtain ⟨cBridgeLogs, hBridgeLogs⟩ :=
    logSlack_two_values_le_pair cBridge cBridge
      cRight (cCond + cLeft)
  obtain ⟨cSwapFold, hSwapFold⟩ :=
    logSlack_linear_bound cLower 1 cSwap
  let cRep := cSwapFold + cBridgeLogs + cSwap
  obtain ⟨cYEquiv, hYEquiv⟩ :=
    logSlack_linear_bound cEquiv 1 cRight
  obtain ⟨cYIncomp, hYIncomp⟩ :=
    logSlack_linear_bound cIncomp 1 cRight
  let cXIncomp := cRep + cMeta
  obtain ⟨bRep, hRepLinear⟩ :=
    logSlack_le_add_const cRep
  let bXX := bRep + cLen + cMeta
  obtain ⟨cLowerXX, hLowerXX⟩ :=
    logSlack_linear_bound cLower 2 bXX
  let cReverse :=
    cRep + cUpper + cLowerXX + (cLen + cMeta)
  let C :=
    cConcat + cYEquiv + cYIncomp + cXIncomp + cReverse
  refine ⟨C, fun x y kyx kxy hkyx hkxy => ?_⟩
  obtain ⟨ky, hky⟩ := exists_plainComplexityValue V hV y
  obtain ⟨kxyCond, hkxyCond⟩ :=
    exists_plainConditionalComplexityValue V hV x y
  obtain ⟨kx, hkx⟩ := exists_plainComplexityValue V hV x
  obtain ⟨kp, hkp⟩ := exists_prefixComplexityValue U hU y
  have hkqFinite : KP U x y ≠ ⊤ := by
    have h := hBridge x y kxyCond hkxyCond
    exact ne_top_of_le_ne_top
      (by
        rw [← Nat.cast_add]
        exact ENat.coe_ne_top _)
      h
  obtain ⟨kq, hkq⟩ := ENat.ne_top_iff_exists.mp hkqFinite
  obtain ⟨p, hp, hpLenE⟩ :=
    exists_program_of_KP_ne_top
      (M := U) (x := y) (y := [])
      (by
        change KPPlain U y ≠ ⊤
        rw [← hkp]
        exact ENat.coe_ne_top kp)
  obtain ⟨q, hq, hqLenE⟩ :=
    exists_program_of_KP_ne_top
      (M := U) (x := x) (y := y) hkqFinite
  have hpLen : p.length = kp := by
    exact_mod_cast (hpLenE.trans hkp.symm)
  have hqLen : q.length = kq := by
    exact_mod_cast (hqLenE.trans hkq.symm)
  let x' := p ++ q
  let y' := p
  have hyx : y' <+: x' := List.prefix_append p q
  obtain ⟨kSwap, hkSwap⟩ :=
    exists_plainComplexityValue V hV (pairCode y x)
  have hkyBoundE :
      (ky : ENat) ≤ (kxy : ENat) + (cRight : ENat) := by
    calc
      (ky : ENat) = plainK V y := hky.symm
      _ ≤ pairPlainK V x y + (cRight : ENat) := hRight x y
      _ = (kxy : ENat) + (cRight : ENat) := by
        rw [pairPlainK, hkxy]
  have hkyBound : ky ≤ kxy + cRight := by
    exact_mod_cast hkyBoundE
  have hkxyCondBoundE :
      (kxyCond : ENat) ≤
        (kxy : ENat) + ((cCond + cLeft : Nat) : ENat) := by
    calc
      (kxyCond : ENat) = condK V x y := hkxyCond.symm
      _ ≤ plainK V x + (cCond : ENat) := hCond x y
      _ ≤ (pairPlainK V x y + (cLeft : ENat)) +
          (cCond : ENat) := by
        gcongr
        exact hLeft x y
      _ = (kxy : ENat) +
          ((cCond + cLeft : Nat) : ENat) := by
        rw [pairPlainK, hkxy]
        push_cast
        simp [add_assoc, add_comm, add_left_comm]
  have hkxyCondBound :
      kxyCond ≤ kxy + (cCond + cLeft) := by
    exact_mod_cast hkxyCondBoundE
  have hkSwapBoundE :
      (kSwap : ENat) ≤ (kxy : ENat) + (cSwap : ENat) := by
    calc
      (kSwap : ENat) = plainK V (pairCode y x) := hkSwap.symm
      _ = plainK V (swapPair (pairCode x y)) := by
        simp [swapPair, decodeFirst_pairCode, decodeSecond_pairCode]
      _ ≤ plainK V (pairCode x y) + (cSwap : ENat) :=
        hSwap (pairCode x y)
      _ = (kxy : ENat) + (cSwap : ENat) := by
        rw [hkxy]
  have hkSwapBound : kSwap ≤ kxy + cSwap := by
    exact_mod_cast hkSwapBoundE
  have hChain :
      ky + kxyCond ≤
        kSwap + logSlack cLower (kSwap + 1) :=
    hLower y x ky kxyCond kSwap hky hkxyCond hkSwap
  have hSwapLog :
      logSlack cLower (kSwap + 1) ≤
        logSlack cSwapFold (kxy + 1) := by
    calc
      logSlack cLower (kSwap + 1)
          ≤ logSlack cLower
              (1 * (kxy + 1) + cSwap) :=
        logSlack_mono_right cLower (by omega)
      _ ≤ logSlack cSwapFold (kxy + 1) :=
        hSwapFold (kxy + 1)
  have hTwoBridgeLogs :
      logSlack cBridge (ky + 1) +
          logSlack cBridge (kxyCond + 1) ≤
        logSlack cBridgeLogs (kxy + 1) :=
    hBridgeLogs ky kxyCond kxy hkyBound hkxyCondBound
  have hkpUpperE :
      (kp : ENat) ≤
        (ky : ENat) +
          (logSlack cBridge (ky + 1) : ENat) := by
    rw [hkp]
    exact hBridge y [] ky hky
  have hkpUpper :
      kp ≤ ky + logSlack cBridge (ky + 1) := by
    exact_mod_cast hkpUpperE
  have hkqUpperE :
      (kq : ENat) ≤
        (kxyCond : ENat) +
          (logSlack cBridge (kxyCond + 1) : ENat) := by
    rw [hkq]
    exact hBridge x y kxyCond hkxyCond
  have hkqUpper :
      kq ≤ kxyCond +
        logSlack cBridge (kxyCond + 1) := by
    exact_mod_cast hkqUpperE
  have hRepOverhead :
      logSlack cSwapFold (kxy + 1) +
          logSlack cBridgeLogs (kxy + 1) + cSwap ≤
        logSlack cRep (kxy + 1) := by
    calc
      logSlack cSwapFold (kxy + 1) +
            logSlack cBridgeLogs (kxy + 1) + cSwap
          = logSlack (cSwapFold + cBridgeLogs)
              (kxy + 1) + cSwap := by
        rw [logSlack_add_const]
      _ ≤ logSlack cRep (kxy + 1) := by
        simpa [cRep] using
          logSlack_add_nat_le
            (cSwapFold + cBridgeLogs) cSwap (kxy + 1)
  have hxLen :
      x'.length ≤ kxy + logSlack cRep (kxy + 1) := by
    dsimp [x']
    rw [List.length_append, hpLen, hqLen]
    omega
  obtain ⟨kxPrime, hkxPrime⟩ :=
    exists_plainComplexityValue V hV x'
  obtain ⟨kPairXX, hkPairXX⟩ :=
    exists_plainComplexityValue V hV (pairCode x x')
  obtain ⟨kCondXX, hkCondXX⟩ :=
    exists_plainConditionalComplexityValue V hV x' x
  have hMetaInst := hMeta p q x y hp hq
  have hkxyToPrimeE :
      (kxy : ENat) ≤
        (kxPrime : ENat) + (cMeta : ENat) := by
    calc
      (kxy : ENat) = pairPlainK V x y := by
        rw [pairPlainK, hkxy]
      _ ≤ plainK V (p ++ q) + (cMeta : ENat) :=
        hMetaInst.1
      _ = (kxPrime : ENat) + (cMeta : ENat) := by
        rw [show p ++ q = x' from rfl, hkxPrime]
  have hkxyToPrime : kxy ≤ kxPrime + cMeta := by
    exact_mod_cast hkxyToPrimeE
  have hkPairXXBoundE :
      (kPairXX : ENat) ≤
        (kxPrime : ENat) + (cMeta : ENat) := by
    calc
      (kPairXX : ENat) = pairPlainK V x x' := by
        rw [pairPlainK, hkPairXX]
      _ = pairPlainK V x (p ++ q) := rfl
      _ ≤ plainK V (p ++ q) + (cMeta : ENat) :=
        hMetaInst.2
      _ = (kxPrime : ENat) + (cMeta : ENat) := by
        rw [show p ++ q = x' from rfl, hkxPrime]
  have hkPairXXBound :
      kPairXX ≤ kxPrime + cMeta := by
    exact_mod_cast hkPairXXBoundE
  have hkxPrimeLengthE :
      (kxPrime : ENat) ≤
        (x'.length : ENat) + (cLen : ENat) := by
    calc
      (kxPrime : ENat) = plainK V x' := hkxPrime.symm
      _ ≤ (x'.length : ENat) + (cLen : ENat) := hLen x'
  have hkxPrimeLength :
      kxPrime ≤ x'.length + cLen := by
    exact_mod_cast hkxPrimeLengthE
  have hXIncompOverhead :
      logSlack cRep (kxy + 1) + cMeta ≤
        logSlack cXIncomp (kxy + 1) := by
    simpa [cXIncomp] using
      logSlack_add_nat_le cRep cMeta (kxy + 1)
  have hXIncomp :
      x'.length ≤
        kxPrime + logSlack cXIncomp (kxy + 1) := by
    omega
  have hkPairXXLinear :
      kPairXX + 1 ≤ 2 * (kxy + 1) + bXX := by
    have hLog := hRepLinear (kxy + 1)
    dsimp [bXX]
    omega
  have hLowerXXLog :
      logSlack cLower (kPairXX + 1) ≤
        logSlack cLowerXX (kxy + 1) := by
    calc
      logSlack cLower (kPairXX + 1)
          ≤ logSlack cLower
              (2 * (kxy + 1) + bXX) :=
        logSlack_mono_right cLower hkPairXXLinear
      _ ≤ logSlack cLowerXX (kxy + 1) :=
        hLowerXX (kxy + 1)
  have hUpperXY :
      kxy ≤ kx + kyx + logSlack cUpper (kxy + 1) :=
    hUpper x y kx kyx kxy hkx hkyx hkxy
  have hLowerXXInst :
      kx + kCondXX ≤
        kPairXX + logSlack cLower (kPairXX + 1) :=
    hLower x x' kx kCondXX kPairXX
      hkx hkCondXX hkPairXX
  have hReverseOverhead :
      logSlack cRep (kxy + 1) +
          logSlack cUpper (kxy + 1) +
          logSlack cLowerXX (kxy + 1) +
          (cLen + cMeta) ≤
        logSlack cReverse (kxy + 1) := by
    calc
      logSlack cRep (kxy + 1) +
            logSlack cUpper (kxy + 1) +
            logSlack cLowerXX (kxy + 1) +
            (cLen + cMeta)
          = (logSlack (cRep + cUpper) (kxy + 1) +
              logSlack cLowerXX (kxy + 1)) +
              (cLen + cMeta) := by
        rw [← logSlack_add_const cRep cUpper (kxy + 1)]
      _ = logSlack (cRep + cUpper + cLowerXX)
              (kxy + 1) + (cLen + cMeta) := by
        rw [logSlack_add_const]
      _ ≤ logSlack cReverse (kxy + 1) := by
        simpa [cReverse] using
          logSlack_add_nat_le
            (cRep + cUpper + cLowerXX)
            (cLen + cMeta) (kxy + 1)
  have hReverse :
      kCondXX ≤ kyx + logSlack cReverse (kxy + 1) := by
    omega
  have hYEquivFold :
      logSlack cEquiv (ky + 1) ≤
        logSlack cYEquiv (kxy + 1) := by
    calc
      logSlack cEquiv (ky + 1)
          ≤ logSlack cEquiv
              (1 * (kxy + 1) + cRight) :=
        logSlack_mono_right cEquiv (by omega)
      _ ≤ logSlack cYEquiv (kxy + 1) :=
        hYEquiv (kxy + 1)
  have hYIncompFold :
      logSlack cIncomp (ky + 1) ≤
        logSlack cYIncomp (kxy + 1) := by
    calc
      logSlack cIncomp (ky + 1)
          ≤ logSlack cIncomp
              (1 * (kxy + 1) + cRight) :=
        logSlack_mono_right cIncomp (by omega)
      _ ≤ logSlack cYIncomp (kxy + 1) :=
        hYIncomp (kxy + 1)
  have hConstBudget (d : Nat) (hd : d ≤ C) :
      d ≤ kyx + logSlack C (kxy + 1) := by
    unfold logSlack
    omega
  have hLogBudget (d : Nat) (hd : d ≤ C) :
      logSlack d (kxy + 1) ≤
        kyx + logSlack C (kxy + 1) := by
    exact (logSlack_mono_left hd (kxy + 1)).trans
      (Nat.le_add_left _ _)
  refine ⟨x', y', hyx, ?_, ?_, ?_, ?_⟩
  · unfold PlainEquivalentWithin
    constructor
    · exact (hConcat p q x y hp hq).trans
        (by
          exact_mod_cast hConstBudget cConcat
            (by dsimp [C]; omega))
    · calc
        condK V x' x = (kCondXX : ENat) := hkCondXX
        _ ≤ ((kyx + logSlack cReverse
              (kxy + 1) : Nat) : ENat) := by
          exact_mod_cast hReverse
        _ ≤ ((kyx + logSlack C
              (kxy + 1) : Nat) : ENat) := by
          exact_mod_cast Nat.add_le_add_left
            (logSlack_mono_left
              (show cReverse ≤ C by dsimp [C]; omega)
              (kxy + 1)) kyx
  · have h :=
      hEquiv y p ky kp hky hkp hp hpLen
    unfold PlainEquivalentWithin at h ⊢
    constructor
    · exact h.1.trans (by
        exact_mod_cast
          (hYEquivFold.trans
            (hLogBudget cYEquiv
              (by dsimp [C]; omega))))
    · exact h.2.trans (by
        exact_mod_cast
          (hYEquivFold.trans
            (hLogBudget cYEquiv
              (by dsimp [C]; omega))))
  · unfold PlainIncompressibleWithin
    rw [hkxPrime]
    exact_mod_cast hXIncomp.trans
      (Nat.add_le_add_left
        (hLogBudget cXIncomp
          (by dsimp [C]; omega)) kxPrime)
  · have h :=
      hIncomp y [] p ky kp hky hkp hp hpLen
    unfold PlainIncompressibleWithin at h ⊢
    dsimp [y']
    exact h.trans (by
      have hs :
          logSlack cIncomp (ky + 1) ≤
            kyx + logSlack C (kxy + 1) :=
        hYIncompFold.trans
          (hLogBudget cYIncomp
            (by dsimp [C]; omega))
      exact add_le_add_right (by exact_mod_cast hs) _)

end Kolmogorov
