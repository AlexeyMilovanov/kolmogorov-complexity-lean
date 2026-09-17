import KolmogorovMathlib.CommonInformation.Intermediate

/-!
# Common Information: Interfaces
-/

namespace Kolmogorov

/-- Closeness of natural numbers is symmetric. -/
lemma NatCloseWithin.symm {a b d : Nat}
    (h : NatCloseWithin a b d) : NatCloseWithin b a d := by
  exact ⟨h.2, h.1⟩

/-- Closeness is preserved when the slack is enlarged. -/
lemma NatCloseWithin.mono {a b d d' : Nat}
    (h : NatCloseWithin a b d) (hd : d ≤ d') :
    NatCloseWithin a b d' := by
  exact ⟨h.1.trans (Nat.add_le_add_left hd _),
    h.2.trans (Nat.add_le_add_left hd _)⟩

/-- Closeness composes with the sum of the slacks. -/
lemma NatCloseWithin.trans {a b c d e : Nat}
    (h1 : NatCloseWithin a b d) (h2 : NatCloseWithin b c e) :
    NatCloseWithin a c (d + e) := by
  unfold NatCloseWithin at h1 h2 ⊢
  constructor <;> omega

/-- The common-information slack is monotone in its constant. -/
lemma commonInformationSlack_mono_left {c c' d n : Nat}
    (h : c ≤ c') :
    commonInformationSlack c d n ≤
      commonInformationSlack c' d n := by
  unfold commonInformationSlack
  exact Nat.add_le_add (Nat.mul_le_mul_right d h)
    (logSlack_mono_left h n)

/-- Plain equivalence within a slack is symmetric. -/
lemma PlainEquivalentWithin.symm {V : Map} {x y : BitString} {d : Nat}
    (h : PlainEquivalentWithin V x y d) :
    PlainEquivalentWithin V y x d := by
  exact ⟨h.2, h.1⟩

/-- Plain equivalence is preserved when the slack is enlarged. -/
lemma PlainEquivalentWithin.mono
    {V : Map} {x y : BitString} {d d' : Nat}
    (h : PlainEquivalentWithin V x y d) (hd : d ≤ d') :
    PlainEquivalentWithin V x y d' := by
  unfold PlainEquivalentWithin at h ⊢
  have hd' : (d : ENat) ≤ (d' : ENat) := by exact_mod_cast hd
  exact ⟨h.1.trans hd', h.2.trans hd'⟩

/-- Plain incompressibility is preserved when the slack is enlarged. -/
lemma PlainIncompressibleWithin.mono
    {V : Map} {x : BitString} {d d' : Nat}
    (h : PlainIncompressibleWithin V x d) (hd : d ≤ d') :
    PlainIncompressibleWithin V x d' := by
  unfold PlainIncompressibleWithin at h ⊢
  exact h.trans (by gcongr)

/-- Plain equivalence composes, with the slacks adding up to a logarithmic term. -/
theorem PlainEquivalentWithin.trans_log
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ x y z a b,
      PlainEquivalentWithin V x y a →
      PlainEquivalentWithin V y z b →
      PlainEquivalentWithin V x z
        (a + b + logSlack c (a + b + 1)) := by
  obtain ⟨c, hc⟩ := condK_chain_upper_values V hV
  refine ⟨c, fun x y z a b hxy hyz => ?_⟩
  obtain ⟨kzx, hkzx⟩ :=
    exists_plainConditionalComplexityValue V hV z x
  obtain ⟨kyz, hkyz⟩ :=
    exists_plainConditionalComplexityValue V hV y z
  obtain ⟨kxz, hkxz⟩ :=
    exists_plainConditionalComplexityValue V hV x z
  obtain ⟨kzy, hkzy⟩ :=
    exists_plainConditionalComplexityValue V hV z y
  obtain ⟨kyx, hkyx⟩ :=
    exists_plainConditionalComplexityValue V hV y x
  obtain ⟨kxy, hkxy⟩ :=
    exists_plainConditionalComplexityValue V hV x y
  have hkxy_le : kxy ≤ a := by
    have h := hxy.1
    rw [hkxy] at h
    exact_mod_cast h
  have hkyx_le : kyx ≤ a := by
    have h := hxy.2
    rw [hkyx] at h
    exact_mod_cast h
  have hkyz_le : kyz ≤ b := by
    have h := hyz.1
    rw [hkyz] at h
    exact_mod_cast h
  have hkzy_le : kzy ≤ b := by
    have h := hyz.2
    rw [hkzy] at h
    exact_mod_cast h
  have hxz :
      kxz ≤ kyz + kxy + logSlack c (kyz + kxy + 1) :=
    hc z x y kyz kxy kxz hkyz hkxy hkxz
  have hzx :
      kzx ≤ kzy + kyx + logSlack c (kzy + kyx + 1) :=
    by
      simpa [add_comm] using
        hc x z y kyx kzy kzx hkyx hkzy hkzx
  have harg₁ : kyz + kxy + 1 ≤ a + b + 1 := by omega
  have harg₂ : kzy + kyx + 1 ≤ a + b + 1 := by omega
  unfold PlainEquivalentWithin
  constructor
  · rw [hkxz]
    exact_mod_cast
      (hxz.trans (by
        have := logSlack_mono_right c harg₁
        omega))
  · rw [hkzx]
    exact_mod_cast
      (hzx.trans (by
        have := logSlack_mono_right c harg₂
        omega))

/-- Exact mutual information is the case of zero slack. -/
lemma MutualInformationEq_iff_within_zero {V : Map} {x y : BitString} {m : Nat} :
    MutualInformationEq V x y m ↔ MutualInformationWithin V x y m 0 := by
  unfold MutualInformationEq MutualInformationWithin
  simp only [Nat.cast_zero, add_zero]
  constructor
  · intro h
    exact ⟨h.le, h.ge⟩
  · intro h
    exact h.1.antisymm h.2

/-- The mutual information statement is preserved when the slack is enlarged. -/
lemma MutualInformationWithin.mono
    {V : Map} {x y : BitString} {m d d' : Nat}
    (h : MutualInformationWithin V x y m d) (hd : d ≤ d') :
    MutualInformationWithin V x y m d' := by
  unfold MutualInformationWithin at h ⊢
  have hd' : (d : ENat) ≤ (d' : ENat) := by exact_mod_cast hd
  constructor
  · exact h.1.trans (by gcongr)
  · exact h.2.trans (by gcongr)

/-- Extractability is preserved when the slack is enlarged. -/
lemma ExtractableCommonInformationWithin.mono
    {V : Map} {x y z : BitString} {m d d' : Nat}
    (h : ExtractableCommonInformationWithin V x y z m d)
    (hd : d ≤ d') :
    ExtractableCommonInformationWithin V x y z m d' := by
  unfold ExtractableCommonInformationWithin at h ⊢
  have hd' : (d : ENat) ≤ (d' : ENat) := by exact_mod_cast hd
  refine ⟨h.1.trans hd', h.2.1.trans hd', ?_, ?_⟩
  · exact h.2.2.1.trans (by exact_mod_cast Nat.add_le_add_left hd m)
  · exact h.2.2.2.trans (by gcongr)

/-- A raw shared description remains one when the slack is enlarged. -/
lemma RawSharedDescriptionWithin.mono
    {V : Map} {x y z a p b : BitString}
    {kx ky kxy m d d' : Nat}
    (h : RawSharedDescriptionWithin V x y z a p b
      kx ky kxy m d)
    (hd : d ≤ d') :
    RawSharedDescriptionWithin V x y z a p b
      kx ky kxy m d' := by
  rcases h with ⟨hp, ha, hb, hpm, hx, hy, hxy⟩
  exact ⟨hp, ha, hb, hpm.mono hd, hx.mono hd,
    hy.mono hd, hxy.mono hd⟩

/-- An overlap representation remains one when the slack is enlarged. -/
lemma OverlapRepresentationWithin.mono
    {V : Map} {x y u : BitString}
    {kx ky kxy d d' : Nat}
    (h : OverlapRepresentationWithin V x y u kx ky kxy d)
    (hd : d ≤ d') :
    OverlapRepresentationWithin V x y u kx ky kxy d' := by
  rcases h with
    ⟨lx, ly, hu, hlx, hly, hxl, hyl, hx, hy, hxy, huInc⟩
  exact ⟨lx, ly, hu, hlx, hly, hxl.mono hd, hyl.mono hd,
    hx.mono hd, hy.mono hd, hxy.mono hd, huInc.mono hd⟩

/-- Swapping the components of a pair changes its complexity by at most a constant. -/
theorem pairPlainK_swap_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y,
      pairPlainK V y x ≤ pairPlainK V x y + (c : ENat) := by
  let swapPair : BitString → BitString := fun w =>
    pairCode (decodeSecond w) (decodeFirst w)
  have hPairCode₂ :
      Computable₂ (fun a b : BitString => pairCode a b) :=
    pairCode_computable
  have hSwap : Computable swapPair :=
    hPairCode₂.comp decodeSecond_computable decodeFirst_computable
  obtain ⟨c, hc⟩ := plainK_map_le V hV swapPair hSwap
  refine ⟨c, fun x y => ?_⟩
  simpa [pairPlainK, swapPair, decodeFirst_pairCode,
    decodeSecond_pairCode] using hc (pairCode x y)

/-- The common information region is upward closed in each of the three coordinates. -/
theorem commonInformationRegion_upward_closed
    {V : Map} {x y : BitString} {s t : CommonInformationTriple} :
    s.1 ≤ t.1 → s.2.1 ≤ t.2.1 → s.2.2 ≤ t.2.2 →
    s ∈ CommonInformationRegion V x y →
    t ∈ CommonInformationRegion V x y := by
  rintro h₁ h₂ h₃ ⟨z, hz, hx, hy⟩
  refine ⟨z, hz.trans_le ?_, hx.trans_le ?_, hy.trans_le ?_⟩
  · exact_mod_cast h₁
  · exact_mod_cast h₂
  · exact_mod_cast h₃

/-- A coarse linear bound for a plain two-stage pair description.  The first
program produces `r` unconditionally; the second produces `x` given `r`.
Encoding the two programs with `pairCode` is not the final logarithmically
tight chain rule, but supplies the linear size bound needed to fold the
chain-rule logarithm back to the visible parameters. -/
theorem pairPlainK_twoStage_crude_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ r x kr kxr,
      HasPlainComplexityValue V r kr →
      HasPlainConditionalComplexityValue V x r kxr →
      ∃ kpair,
        HasPlainComplexityValue V (pairCode r x) kpair ∧
        kpair ≤ 2 * kr + 1 + kxr + c := by
  let D : Map := fun pr =>
    (V (decodeFirst pr.1, [])).bind fun r =>
      (V (decodeSecond pr.1, r)).map fun x => pairCode r x
  have hFirst :
      Partrec
        (fun pr : BitString × BitString =>
          V (decodeFirst pr.1, [])) :=
    Partrec.comp hV.1
      (Computable.pair
        (decodeFirst_computable.comp Computable.fst)
        (Computable.const []))
  have hRun :
      Partrec
        (fun q : (BitString × BitString) × BitString =>
          V (decodeSecond q.1.1, q.2)) :=
    Partrec.comp hV.1
      (Computable.pair
        (decodeSecond_computable.comp
          (Computable.fst.comp Computable.fst))
        Computable.snd)
  have hPairCode₂ :
      Computable₂ (fun a b : BitString => pairCode a b) :=
    pairCode_computable
  have hPair :
      Computable
        (fun q : ((BitString × BitString) × BitString) × BitString =>
          pairCode q.1.2 q.2) :=
    hPairCode₂.comp
      (Computable.snd.comp Computable.fst) Computable.snd
  have hSecond :
      Partrec
        (fun q : (BitString × BitString) × BitString =>
          (V (decodeSecond q.1.1, q.2)).map
            fun x => pairCode q.2 x) :=
    Partrec.map hRun hPair
  have hD : isDecompressor D := Partrec.bind hFirst hSecond
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c, fun r x kr kxr hr hxr => ?_⟩
  obtain ⟨p, hp, hpLen⟩ := hr.exists_program
  obtain ⟨q, hq, hqLen⟩ := hxr.exists_program
  obtain ⟨kpair, hkpair⟩ :=
    exists_plainComplexityValue V hV (pairCode r x)
  have hDprod :
      produces D (pairCode p q) [] (pairCode r x) := by
    apply Part.mem_bind_iff.mpr
    refine ⟨r, ?_, ?_⟩
    · simpa [decodeFirst_pairCode] using hp
    · exact Part.mem_map (fun w => pairCode r w)
        (by simpa [decodeSecond_pairCode] using hq)
  have hBoundE :
      (kpair : ENat) ≤
        ((2 * kr + 1 + kxr + c : Nat) : ENat) := by
    calc
      (kpair : ENat) = plainK V (pairCode r x) := hkpair.symm
      _ ≤ plainK D (pairCode r x) + (c : ENat) :=
        hc (pairCode r x) []
      _ ≤ ((pairCode p q).length : ENat) + (c : ENat) := by
        gcongr
        exact sInf_le ⟨pairCode p q, hDprod, rfl⟩
      _ = ((2 * kr + 1 + kxr + c : Nat) : ENat) := by
        rw [length_pairCode, hpLen, hqLen]
        push_cast
        ring
  exact ⟨kpair, hkpair, by exact_mod_cast hBoundE⟩

/-- Bounding `logSlack c (k + d + 1)` by `logSlack c (k + 1) + c * d + c`. -/
private lemma logSlack_add_one_le (c k d : Nat) :
    logSlack c (k + d + 1) ≤
      logSlack c (k + 1) + c * d + c := by
  calc
    logSlack c (k + d + 1)
        = logSlack c ((k + 1) + d) := by congr 1; omega
    _ ≤ logSlack c (k + 1) + logSlack c d :=
      logSlack_add_le c (k + 1) d
    _ ≤ logSlack c (k + 1) + c * d + c := by
      unfold logSlack
      have := length_natBits_le d
      nlinarith

/-- Bounding folded `logSlack` using a linear bound on its argument. -/
private lemma logSlack_fold_le {c cFold b p k d : Nat}
    (hFold : ∀ n, logSlack c (3 * n + b) ≤ logSlack cFold n)
    (hLinear : p + 1 ≤ 3 * (k + d + 1) + b) :
    logSlack c (p + 1) ≤ logSlack cFold (k + d + 1) :=
  (logSlack_mono_right c hLinear).trans (hFold (k + d + 1))

/-- Reverse chain-rule bound in free variables: from `kxr ≤ d`, the length bound
`kr ≤ k + d + cLen`, the two visible pair bounds and the swap bound `kPairXR ≤ kPairRX + cSwap`,
the conditional complexity of `x` given `r` obeys
`krx ≤ (2 + cUpper + cLower) * d + logSlack (cUpper + cLower) (k + 1) +
(cLen + cSwap + cUpper + cLower)`: the two folded slacks merge into one at the summed constant,
and the `d`-linear coefficient is `2 + cUpper + cLower`. -/
private lemma nearLength_reverse_bound
    (cLen cSwap cUpper cLower k d kr kxr krx kPairRX kPairXR : Nat)
    (hkxr : kxr ≤ d)
    (hkr : kr ≤ k + d + cLen)
    (hUpper : kPairRX ≤ kr + kxr +
      (logSlack cUpper (k + 1) + cUpper * d + cUpper))
    (hLower : k + krx ≤ kPairXR +
      (logSlack cLower (k + 1) + cLower * d + cLower))
    (hSwap : kPairXR ≤ kPairRX + cSwap) :
    krx ≤ (2 + cUpper + cLower) * d + logSlack (cUpper + cLower) (k + 1) +
      (cLen + cSwap + cUpper + cLower) := by
  generalize hL1 : logSlack cUpper (k + 1) = L1
  generalize hL2 : logSlack cLower (k + 1) = L2
  have h1 : k + krx ≤ (k + d + cLen) + d +
      (L1 + cUpper * d + cUpper) + cSwap +
      (L2 + cLower * d + cLower) := by omega
  have hLog : L1 + L2 = logSlack (cUpper + cLower) (k + 1) := by
    subst hL1 hL2
    exact logSlack_add_const _ _ _
  have hCoeff : (2 + cUpper + cLower) * d = 2 * d + cUpper * d + cLower * d := by ring
  omega

/-- Linear and logarithmic slack accumulation into `commonInformationSlack`. -/
private lemma linear_log_slack_le (cLogs cConst cLinear k d : Nat) :
    cLinear * d + logSlack cLogs (k + 1) + cConst ≤
      commonInformationSlack (cLogs + cConst + cLinear) d (k + 1) := by
  unfold commonInformationSlack
  have hLog : logSlack cLogs (k + 1) + cConst ≤ logSlack (cLogs + cConst) (k + 1) :=
    logSlack_add_nat_le cLogs cConst (k + 1)
  have hLogMono : logSlack (cLogs + cConst) (k + 1) ≤
      logSlack (cLogs + cConst + cLinear) (k + 1) :=
    logSlack_mono_left (by omega) (k + 1)
  have hLin : cLinear * d ≤ (cLogs + cConst + cLinear) * d :=
    Nat.mul_le_mul_right d (by omega)
  omega

/-- A string of about the right length from which `x` is cheaply decodable is plain equivalent to
`x` and itself incompressible. -/
theorem nearLength_decodable_is_equivalent_incompressible
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ x r k d,
      HasPlainComplexityValue V x k →
      NatCloseWithin r.length k d →
      condK V x r ≤ (d : ENat) →
      PlainEquivalentWithin V x r
          (commonInformationSlack c d (k + 1)) ∧
      PlainIncompressibleWithin V r
          (commonInformationSlack c d (k + 1)) := by
  obtain ⟨cCrude, hCrude⟩ := pairPlainK_twoStage_crude_values V hV
  obtain ⟨cLen, hLen⟩ := plainK_le_length V hV
  obtain ⟨cSwap, hSwap⟩ := pairPlainK_swap_le V hV
  obtain ⟨cUpper, hUpper⟩ := pairPlainK_chain_upper_values V hV
  obtain ⟨cLower, hLower⟩ := pairPlainK_chain_lower_values V hV
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le V hV
  let bUpper := 2 * cLen + cCrude
  obtain ⟨cUpperFold, hUpperFold⟩ := logSlack_linear_bound cUpper 3 bUpper
  let bLower := bUpper + cSwap
  obtain ⟨cLowerFold, hLowerFold⟩ := logSlack_linear_bound cLower 3 bLower
  let cLogs := cUpperFold + cLowerFold
  let cConst := cLen + cSwap + cRight + cUpperFold + cLowerFold
  let cLinear := 2 + cUpperFold + cLowerFold
  let C := cLogs + cConst + cLinear
  refine ⟨C, fun x r k d hx hrx hDecode => ?_⟩
  unfold NatCloseWithin at hrx
  obtain ⟨kr, hkr⟩ := exists_plainComplexityValue V hV r
  obtain ⟨kxr, hkxr⟩ := exists_plainConditionalComplexityValue V hV x r
  obtain ⟨krx, hkrx⟩ := exists_plainConditionalComplexityValue V hV r x
  obtain ⟨kPairRX, hkPairRX, hPairRXCrude⟩ := hCrude r x kr kxr hkr hkxr
  obtain ⟨kPairXR, hkPairXR⟩ := exists_plainComplexityValue V hV (pairCode x r)
  have hkxrLe : kxr ≤ d := by
    have h := hDecode
    rw [hkxr] at h
    exact_mod_cast h
  have hkrLength : kr ≤ r.length + cLen := by
    have h := hLen r
    rw [hkr] at h
    exact_mod_cast h
  have hkrVisible : kr ≤ k + d + cLen := by omega
  have hPairRXLinear : kPairRX + 1 ≤ 3 * (k + d + 1) + bUpper := by
    dsimp [bUpper]; omega
  have hPairSwap : kPairXR ≤ kPairRX + cSwap := by
    have h := hSwap r x
    change plainK V (pairCode x r) ≤ plainK V (pairCode r x) + (cSwap : ENat) at h
    rw [hkPairXR, hkPairRX] at h
    exact_mod_cast h
  have hPairXRLinear : kPairXR + 1 ≤ 3 * (k + d + 1) + bLower := by
    dsimp [bLower]; omega
  have hUpperLog : logSlack cUpper (kPairRX + 1) ≤ logSlack cUpperFold (k + d + 1) :=
    logSlack_fold_le hUpperFold hPairRXLinear
  have hLowerLog : logSlack cLower (kPairXR + 1) ≤ logSlack cLowerFold (k + d + 1) :=
    logSlack_fold_le hLowerFold hPairXRLinear
  have hUpperVisible :
      logSlack cUpperFold (k + d + 1) ≤
        logSlack cUpperFold (k + 1) + cUpperFold * d + cUpperFold :=
    logSlack_add_one_le cUpperFold k d
  have hLowerVisible :
      logSlack cLowerFold (k + d + 1) ≤
        logSlack cLowerFold (k + 1) + cLowerFold * d + cLowerFold :=
    logSlack_add_one_le cLowerFold k d
  have hPairUpper :
      kPairRX ≤ kr + kxr + logSlack cUpper (kPairRX + 1) :=
    hUpper r x kr kxr kPairRX hkr hkxr hkPairRX
  have hPairLower :
      k + krx ≤ kPairXR + logSlack cLower (kPairXR + 1) :=
    hLower x r k krx kPairXR hx hkrx hkPairXR
  have hProjection : k ≤ kPairRX + cRight := by
    have h := hRight r x
    rw [pairPlainK, hx, hkPairRX] at h
    exact_mod_cast h
  have hUpperBound :
      logSlack cUpper (kPairRX + 1) ≤
        logSlack cUpperFold (k + 1) + cUpperFold * d + cUpperFold :=
    hUpperLog.trans hUpperVisible
  have hLowerBound :
      logSlack cLower (kPairXR + 1) ≤
        logSlack cLowerFold (k + 1) + cLowerFold * d + cLowerFold :=
    hLowerLog.trans hLowerVisible
  have hPairUpperVisible :
      kPairRX ≤ kr + kxr +
          (logSlack cUpperFold (k + 1) + cUpperFold * d + cUpperFold) :=
    hPairUpper.trans (Nat.add_le_add_left hUpperBound _)
  have hPairLowerVisible :
      k + krx ≤ kPairXR +
          (logSlack cLowerFold (k + 1) + cLowerFold * d + cLowerFold) :=
    hPairLower.trans (Nat.add_le_add_left hLowerBound _)
  have hReverse :
      krx ≤ cLinear * d + logSlack cLogs (k + 1) + cConst := by
    have h := nearLength_reverse_bound cLen cSwap cUpperFold cLowerFold k d kr kxr krx
      kPairRX kPairXR hkxrLe hkrVisible hPairUpperVisible hPairLowerVisible hPairSwap
    simp only [cLinear, cLogs, cConst]
    omega
  have hIncompressible :
      r.length ≤ kr + (cLinear * d + logSlack cLogs (k + 1) + cConst) := by
    have hlen : r.length ≤ k + d := hrx.1
    have hLogVisible : logSlack cUpperFold (k + 1) ≤ logSlack cLogs (k + 1) :=
      logSlack_mono_left (by omega) _
    have hLinear : 2 * d + cUpperFold * d ≤ cLinear * d := by
      have hring : 2 * d + cUpperFold * d = (2 + cUpperFold) * d := by ring
      rw [hring]
      exact Nat.mul_le_mul_right d (by omega)
    have hConst : cRight + cUpperFold ≤ cConst := by omega
    omega
  have hFinalBudget :
      cLinear * d + logSlack cLogs (k + 1) + cConst ≤
        commonInformationSlack C d (k + 1) :=
    linear_log_slack_le cLogs cConst cLinear k d
  have hdBudget : d ≤ commonInformationSlack C d (k + 1) := by
    have h1 : d ≤ cLinear * d := by
      calc d = 1 * d := by ring
      _ ≤ cLinear * d := Nat.mul_le_mul_right d (by omega)
    omega
  constructor
  · unfold PlainEquivalentWithin
    constructor
    · exact hDecode.trans (by exact_mod_cast hdBudget)
    · rw [hkrx]
      exact_mod_cast hReverse.trans hFinalBudget
  · unfold PlainIncompressibleWithin
    rw [hkr]
    exact_mod_cast
      hIncompressible.trans (Nat.add_le_add_left hFinalBudget kr)

end Kolmogorov
