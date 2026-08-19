import KolmogorovMathlib.CommonInformation.RegionEnvelopes
import KolmogorovMathlib.CommonInformation.OverlapExtraction

/-!
# Constructive lower-envelope witnesses for SUV Theorem 225

This module turns the three concrete shortest-description-prefix decoders into
exact `CommonInformationRegion` witnesses.  The finite five-way case cover is
proved in `RegionEnvelopes`; the eventual universal lower inclusion will combine
these leaves with exact minimizing programs and the conditional-value estimates.
-/

namespace Kolmogorov

/-- Prefixes of independent plain
descriptions realize the joint sloping face: their literal concatenation is the
common string, and each missing suffix recovers its corresponding output. -/
theorem commonInformationRegion_contains_combinedPlainPrefixProfile
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ p q x y : BitString, ∀ i j : Nat,
      produces V p [] x →
      produces V q [] y →
      i ≤ p.length →
      j ≤ q.length →
      commonInformationTripleInflate
          (logSlack c (p.length + q.length + 1))
          (i + j, (p.length - i, q.length - j)) ∈
        CommonInformationRegion V x y := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainK_combinedProgramPrefixes_le V hV
  obtain ⟨cCond, hCond⟩ :=
    condK_outputs_given_combined_plainProgramPrefixes_le V hV
  let C := cPlain + cCond + 1
  refine ⟨C, ?_⟩
  intro p q x y i j hpx hqy hi hj
  let N := p.length + q.length + 1
  let z := p.take i ++ q.take j
  have hPlainBound := hPlain p q i j hi hj
  have hCondBounds := hCond p q x y i j hpx hqy hi hj
  dsimp only at hCondBounds
  have hPlainSlack : logSlack cPlain N < logSlack C N := by
    dsimp only [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  have hCondSlack : logSlack cCond N < logSlack C N := by
    dsimp only [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  change
    ∃ w,
      plainK V w <
          (((i + j + logSlack C N : Nat)) : ENat) ∧
        condK V x w <
          (((p.length - i + logSlack C N : Nat)) : ENat) ∧
        condK V y w <
          (((q.length - j + logSlack C N : Nat)) : ENat)
  refine ⟨z, ?_, ?_, ?_⟩
  · exact hPlainBound.trans_lt (by
      exact_mod_cast Nat.add_lt_add_left hPlainSlack (i + j))
  · exact hCondBounds.1.trans_lt (by
      exact_mod_cast Nat.add_lt_add_left hCondSlack (p.length - i))
  · exact hCondBounds.2.trans_lt (by
      exact_mod_cast Nat.add_lt_add_left hCondSlack (q.length - j))

/-- A complete plain
description of `y` followed by a prefix of a conditional description of `x | y`
realizes the face with negligible `C(y | z)`. -/
theorem commonInformationRegion_contains_anchoredConditionalPrefixProfile
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ p q x y : BitString, ∀ i : Nat,
      produces V p [] y →
      produces V q y x →
      i ≤ q.length →
      commonInformationTripleInflate
          (logSlack c (p.length + q.length + 1))
          (p.length + i, (q.length - i, 0)) ∈
        CommonInformationRegion V x y := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainK_combinedProgramPrefixes_le V hV
  obtain ⟨cCond, hCond⟩ :=
    condK_outputs_given_plain_and_conditionalProgramPrefix_le V hV
  let C := cPlain + cCond + 1
  refine ⟨C, ?_⟩
  intro p q x y i hpy hqyx hi
  let N := p.length + q.length + 1
  let z := p ++ q.take i
  have hPlainBound := hPlain p q p.length i le_rfl hi
  simp only [List.take_length] at hPlainBound
  have hCondBounds := hCond p q x y i hpy hqyx hi
  dsimp only at hCondBounds
  have hPlainSlack : logSlack cPlain N < logSlack C N := by
    dsimp only [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  have hCondSlack : logSlack cCond N < logSlack C N := by
    dsimp only [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  change
    ∃ w,
      plainK V w <
          (((p.length + i + logSlack C N : Nat)) : ENat) ∧
        condK V x w <
          (((q.length - i + logSlack C N : Nat)) : ENat) ∧
        condK V y w < (((0 + logSlack C N : Nat)) : ENat)
  simp only [Nat.zero_add]
  refine ⟨z, ?_, ?_, ?_⟩
  · exact hPlainBound.trans_lt (by
      exact_mod_cast Nat.add_lt_add_left hPlainSlack (p.length + i))
  · exact hCondBounds.2.trans_lt (by
      exact_mod_cast Nat.add_lt_add_left hCondSlack (q.length - i))
  · exact hCondBounds.1.trans_lt (by exact_mod_cast hCondSlack)

/-- **Single-prefix transitive region witness.**  A prefix of a plain
description of `y` realizes the intermediate face: its missing suffix recovers
`y`, and that suffix followed by one conditional program recovers `x`. -/
theorem commonInformationRegion_contains_plainPrefixTransitiveProfile
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ p q x y : BitString, ∀ i : Nat,
      produces V p [] y →
      produces V q y x →
      i ≤ p.length →
      commonInformationTripleInflate
          (logSlack c (p.length + q.length + 1))
          (i, (p.length - i + q.length, p.length - i)) ∈
        CommonInformationRegion V x y := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainK_combinedProgramPrefixes_le V hV
  obtain ⟨cY, hY⟩ :=
    condK_output_given_plainProgramPrefix_le V hV
  obtain ⟨cX, hX⟩ :=
    condK_output_given_plainProgramPrefix_then_conditionalProgram_le V hV
  let C := cPlain + cY + cX + 1
  refine ⟨C, ?_⟩
  intro p q x y i hpy hqyx hi
  let N := p.length + q.length + 1
  let z := p.take i
  have hPlainBound := hPlain p [] i 0 hi (by simp)
  simp only [List.take_nil, List.append_nil, Nat.add_zero,
    List.length_nil] at hPlainBound
  have hYBound := hY p y i hpy
  have hXBound := hX p q x y i hpy hqyx hi
  have hBits :
      (Nat.bits (p.length + 1)).length ≤ (Nat.bits N).length := by
    apply length_natBits_mono
    dsimp only [N]
    omega
  have hPlainSlack :
      logSlack cPlain (p.length + 1) < logSlack C N := by
    dsimp only [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  have hYSlack : logSlack cY (p.length + 1) < logSlack C N := by
    dsimp only [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  have hXSlack : logSlack cX N < logSlack C N := by
    dsimp only [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  change
    ∃ w,
      plainK V w < (((i + logSlack C N : Nat)) : ENat) ∧
        condK V x w <
          (((p.length - i + q.length + logSlack C N : Nat)) : ENat) ∧
        condK V y w <
          (((p.length - i + logSlack C N : Nat)) : ENat)
  refine ⟨z, ?_, ?_, ?_⟩
  · exact hPlainBound.trans_lt (by
      exact_mod_cast Nat.add_lt_add_left hPlainSlack i)
  · exact hXBound.trans_lt (by
      exact_mod_cast Nat.add_lt_add_left hXSlack
        (p.length - i + q.length))
  · exact hYBound.trans_lt (by
      exact_mod_cast Nat.add_lt_add_left hYSlack (p.length - i))

/-- Swapping the two source strings swaps the two conditional coordinates of
the common-information region. -/
theorem commonInformationRegion_swap
    {V : Map} {x y : BitString} {t : CommonInformationTriple} :
    t ∈ CommonInformationRegion V y x ↔
      (t.1, (t.2.2, t.2.1)) ∈ CommonInformationRegion V x y := by
  constructor
  · rintro ⟨z, hz, hy, hx⟩
    exact ⟨z, hz, hx, hy⟩
  · rintro ⟨z, hz, hx, hy⟩
    exact ⟨z, hz, hy, hx⟩


/-- The constructive universal lower inclusion for SUV Theorem 225.
Given any optimal conditional machine, the common information region of any pair
with the (2n, 2n, 3n) complexity profile contains the entire finite case cover
of the theoretical lower envelope, up to uniform logarithmic slack. -/
theorem theorem_225_common_information_universal_lower
    (V : Map) (hV : isOptimalConditional V) :
    ∀ A : Nat, ∃ C : Nat, ∀ n : Nat, ∀ x y : BitString,
      ∀ kx ky kxy : Nat,
        HasPlainComplexityValue V x kx →
        HasPlainComplexityValue V y ky →
        HasPlainComplexityValue V (pairCode x y) kxy →
        NatCloseWithin kx (2 * n) (logSlack A n) →
        NatCloseWithin ky (2 * n) (logSlack A n) →
        NatCloseWithin kxy (3 * n) (logSlack A n) →
        ∀ t ∈ CommonInformationLowerEnvelope n,
          commonInformationTripleInflate (logSlack C n) t ∈ CommonInformationRegion V x y := by
  intro A
  obtain ⟨cCond, hCondClose⟩ :=
    theorem_225_conditional_values_close V hV A
  obtain ⟨cCombined, hCombined⟩ :=
    commonInformationRegion_contains_combinedPlainPrefixProfile V hV
  obtain ⟨cAnchored, hAnchored⟩ :=
    commonInformationRegion_contains_anchoredConditionalPrefixProfile V hV
  obtain ⟨cTrans, hTrans⟩ :=
    commonInformationRegion_contains_plainPrefixTransitiveProfile V hV
  let cWitness := cCombined + cAnchored + cTrans
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cWitness
      (4 + 2 * A + 2 * cCond) (2 * A + 2 * cCond + 1)
  let C := A + cCond + cFold
  refine ⟨C, ?_⟩
  intro n x y kx ky kxy hx hy hxy hxClose hyClose hxyClose
  obtain ⟨kxyCond, hkxyCond⟩ :=
    exists_plainConditionalComplexityValue V hV x y
  obtain ⟨kyxCond, hkyxCond⟩ :=
    exists_plainConditionalComplexityValue V hV y x
  obtain ⟨hkxyClose, hkyxClose⟩ :=
    hCondClose n x y kx ky kxy kxyCond kyxCond
      hx hy hxy hkxyCond hkyxCond hxClose hyClose hxyClose
  obtain ⟨px, hpx, hpxLength⟩ := hx.exists_program
  obtain ⟨py, hpy, hpyLength⟩ := hy.exists_program
  obtain ⟨pxy, hpxy, hpxyLength⟩ := hkxyCond.exists_program
  obtain ⟨pyx, hpyx, hpyxLength⟩ := hkyxCond.exists_program
  have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
  have hALinear : logSlack A n ≤ A * n + A := by
    unfold logSlack
    nlinarith [Nat.mul_le_mul_left A hBits]
  have hCondLinear : logSlack cCond n ≤ cCond * n + cCond := by
    unfold logSlack
    nlinarith [Nat.mul_le_mul_left cCond hBits]
  have hCombinedArgument :
      kx + ky + 1 ≤
        (4 + 2 * A + 2 * cCond) * n +
          (2 * A + 2 * cCond + 1) := by
    unfold NatCloseWithin at hxClose hyClose
    nlinarith
  have hXYArgument :
      ky + kxyCond + 1 ≤
        (4 + 2 * A + 2 * cCond) * n +
          (2 * A + 2 * cCond + 1) := by
    unfold NatCloseWithin at hyClose hkxyClose
    nlinarith
  have hYXArgument :
      kx + kyxCond + 1 ≤
        (4 + 2 * A + 2 * cCond) * n +
          (2 * A + 2 * cCond + 1) := by
    unfold NatCloseWithin at hxClose hkyxClose
    nlinarith
  have hCombinedSlack :
      logSlack cCombined (kx + ky + 1) ≤ logSlack cFold n := by
    calc
      logSlack cCombined (kx + ky + 1) ≤
          logSlack cWitness (kx + ky + 1) :=
        logSlack_mono_left (by dsimp [cWitness]; omega) _
      _ ≤ logSlack cWitness
          ((4 + 2 * A + 2 * cCond) * n +
            (2 * A + 2 * cCond + 1)) :=
        logSlack_mono_right cWitness hCombinedArgument
      _ ≤ logSlack cFold n := hFold n
  have hXYSlack :
      logSlack cAnchored (ky + kxyCond + 1) ≤
        logSlack cFold n := by
    calc
      logSlack cAnchored (ky + kxyCond + 1) ≤
          logSlack cWitness (ky + kxyCond + 1) :=
        logSlack_mono_left (by dsimp [cWitness]; omega) _
      _ ≤ logSlack cWitness
          ((4 + 2 * A + 2 * cCond) * n +
            (2 * A + 2 * cCond + 1)) :=
        logSlack_mono_right cWitness hXYArgument
      _ ≤ logSlack cFold n := hFold n
  have hYXSlack :
      logSlack cAnchored (kx + kyxCond + 1) ≤
        logSlack cFold n := by
    calc
      logSlack cAnchored (kx + kyxCond + 1) ≤
          logSlack cWitness (kx + kyxCond + 1) :=
        logSlack_mono_left (by dsimp [cWitness]; omega) _
      _ ≤ logSlack cWitness
          ((4 + 2 * A + 2 * cCond) * n +
            (2 * A + 2 * cCond + 1)) :=
        logSlack_mono_right cWitness hYXArgument
      _ ≤ logSlack cFold n := hFold n
  have hXYTransSlack :
      logSlack cTrans (ky + kxyCond + 1) ≤
        logSlack cFold n := by
    calc
      logSlack cTrans (ky + kxyCond + 1) ≤
          logSlack cWitness (ky + kxyCond + 1) :=
        logSlack_mono_left (by dsimp [cWitness]; omega) _
      _ ≤ logSlack cWitness
          ((4 + 2 * A + 2 * cCond) * n +
            (2 * A + 2 * cCond + 1)) :=
        logSlack_mono_right cWitness hXYArgument
      _ ≤ logSlack cFold n := hFold n
  have hYXTransSlack :
      logSlack cTrans (kx + kyxCond + 1) ≤
        logSlack cFold n := by
    calc
      logSlack cTrans (kx + kyxCond + 1) ≤
          logSlack cWitness (kx + kyxCond + 1) :=
        logSlack_mono_left (by dsimp [cWitness]; omega) _
      _ ≤ logSlack cWitness
          ((4 + 2 * A + 2 * cCond) * n +
            (2 * A + 2 * cCond + 1)) :=
        logSlack_mono_right cWitness hYXArgument
      _ ≤ logSlack cFold n := hFold n
  have hBudget :
      logSlack A n + logSlack cCond n + logSlack cFold n =
        logSlack C n := by
    dsimp [C]
    unfold logSlack
    ring
  have hCombinedError :
      logSlack A n + logSlack cCond n +
          logSlack cCombined (kx + ky + 1) ≤
        logSlack C n := by
    rw [← hBudget]
    omega
  have hXYAnchoredError :
      logSlack A n + logSlack cCond n +
          logSlack cAnchored (ky + kxyCond + 1) ≤
        logSlack C n := by
    rw [← hBudget]
    omega
  have hYXAnchoredError :
      logSlack A n + logSlack cCond n +
          logSlack cAnchored (kx + kyxCond + 1) ≤
        logSlack C n := by
    rw [← hBudget]
    omega
  have hXYTransError :
      logSlack A n + logSlack cCond n +
          logSlack cTrans (ky + kxyCond + 1) ≤
        logSlack C n := by
    rw [← hBudget]
    omega
  have hYXTransError :
      logSlack A n + logSlack cCond n +
          logSlack cTrans (kx + kyxCond + 1) ≤
        logSlack C n := by
    rw [← hBudget]
    omega
  intro t ht
  rcases commonInformationLowerEnvelope_prefix_case_cover ht with
    hCombinedCase | hAnchoredXY | hAnchoredYX | hTransXY | hTransYX
  · rcases hCombinedCase with
      ⟨i, j, hi, hj, hFirst, hLeft, hRight⟩
    let i' := min i kx
    let j' := min j ky
    have hi' : i' ≤ px.length := by
      rw [hpxLength]
      exact min_le_right _ _
    have hj' : j' ≤ py.length := by
      rw [hpyLength]
      exact min_le_right _ _
    have hMem := hCombined px py x y i' j' hpx hpy hi' hj'
    refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
    · simp only [commonInformationTripleInflate, hpxLength, hpyLength]
      dsimp only [i', j']
      omega
    · simp only [commonInformationTripleInflate, hpxLength, hpyLength]
      dsimp only [i']
      unfold NatCloseWithin at hxClose
      omega
    · simp only [commonInformationTripleInflate, hpxLength, hpyLength]
      dsimp only [j']
      unfold NatCloseWithin at hyClose
      omega
  · rcases hAnchoredXY with ⟨i, hi, hFirst, hLeft⟩
    let i' := min i kxyCond
    have hi' : i' ≤ pxy.length := by
      rw [hpxyLength]
      exact min_le_right _ _
    have hMem := hAnchored py pxy x y i' hpy hpxy hi'
    refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
    · simp only [commonInformationTripleInflate, hpyLength, hpxyLength]
      dsimp only [i']
      unfold NatCloseWithin at hyClose
      omega
    · simp only [commonInformationTripleInflate, hpyLength, hpxyLength]
      dsimp only [i']
      unfold NatCloseWithin at hkxyClose
      omega
    · simp only [commonInformationTripleInflate, hpyLength, hpxyLength]
      omega
  · rcases hAnchoredYX with ⟨i, hi, hFirst, hRight⟩
    let i' := min i kyxCond
    have hi' : i' ≤ pyx.length := by
      rw [hpyxLength]
      exact min_le_right _ _
    have hMemYX := hAnchored px pyx y x i' hpx hpyx hi'
    have hMem :
        commonInformationTripleInflate
            (logSlack cAnchored (px.length + pyx.length + 1))
            (px.length + i', (0, pyx.length - i')) ∈
          CommonInformationRegion V x y := by
      have hSwap := (commonInformationRegion_swap (V := V)
        (x := x) (y := y)).mp hMemYX
      simpa [commonInformationTripleInflate] using hSwap
    refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
    · simp only [commonInformationTripleInflate, hpxLength, hpyxLength]
      dsimp only [i']
      unfold NatCloseWithin at hxClose
      omega
    · simp only [commonInformationTripleInflate, hpxLength, hpyxLength]
      omega
    · simp only [commonInformationTripleInflate, hpxLength, hpyxLength]
      dsimp only [i']
      unfold NatCloseWithin at hkyxClose
      omega
  · rcases hTransXY with ⟨i, hi, hFirst, hLeft, hRight⟩
    let i' := min i ky
    have hi' : i' ≤ py.length := by
      rw [hpyLength]
      exact min_le_right _ _
    have hMem := hTrans py pxy x y i' hpy hpxy hi'
    refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
    · simp only [commonInformationTripleInflate, hpyLength, hpxyLength]
      dsimp only [i']
      omega
    · simp only [commonInformationTripleInflate, hpyLength, hpxyLength]
      dsimp only [i']
      unfold NatCloseWithin at hyClose hkxyClose
      omega
    · simp only [commonInformationTripleInflate, hpyLength, hpxyLength]
      dsimp only [i']
      unfold NatCloseWithin at hyClose
      omega
  · rcases hTransYX with ⟨i, hi, hFirst, hLeft, hRight⟩
    let i' := min i kx
    have hi' : i' ≤ px.length := by
      rw [hpxLength]
      exact min_le_right _ _
    have hMemYX := hTrans px pyx y x i' hpx hpyx hi'
    have hMem :
        commonInformationTripleInflate
            (logSlack cTrans (px.length + pyx.length + 1))
            (i', (px.length - i', px.length - i' + pyx.length)) ∈
          CommonInformationRegion V x y := by
      have hSwap := (commonInformationRegion_swap (V := V)
        (x := x) (y := y)).mp hMemYX
      simpa [commonInformationTripleInflate] using hSwap
    refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
    · simp only [commonInformationTripleInflate, hpxLength, hpyxLength]
      dsimp only [i']
      omega
    · simp only [commonInformationTripleInflate, hpxLength, hpyxLength]
      dsimp only [i']
      unfold NatCloseWithin at hxClose
      omega
    · simp only [commonInformationTripleInflate, hpxLength, hpyxLength]
      dsimp only [i']
      unfold NatCloseWithin at hxClose hkyxClose
      omega

/-- The source's universal upper envelope with a uniform `O(log n)` error.
The value-level coding bounds initially contain logarithms of the triple
coordinates.  If a relevant coordinate sum is not already above its ideal
face, that sum is at most `3n`, so the logarithm folds back to `log n`. -/
theorem theorem_225_common_information_profile_upper
    (V : Map) (hV : isOptimalConditional V) :
    ∀ A : Nat, ∃ C : Nat, ∀ n : Nat, ∀ x y : BitString,
      ∀ kx ky kxy : Nat,
        HasPlainComplexityValue V x kx →
        HasPlainComplexityValue V y ky →
        HasPlainComplexityValue V (pairCode x y) kxy →
        NatCloseWithin kx (2 * n) (logSlack A n) →
        NatCloseWithin ky (2 * n) (logSlack A n) →
        NatCloseWithin kxy (3 * n) (logSlack A n) →
        ∀ t ∈ CommonInformationRegion V x y,
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationUpperEnvelope (2 * n) (2 * n) (3 * n) := by
  intro A
  obtain ⟨cLeft, hLeft⟩ :=
    commonInformationRegion_left_profile_bound_values V hV
  obtain ⟨cRight, hRight⟩ :=
    commonInformationRegion_right_profile_bound_values V hV
  obtain ⟨cPair, hPair⟩ :=
    commonInformationRegion_pair_profile_bound_values V hV
  let cWitness := cLeft + cRight + cPair
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cWitness 3 1
  let C := A + cFold
  refine ⟨C, ?_⟩
  intro n x y kx ky kxy hx hy hxy hxClose hyClose hxyClose t ht
  have hLeftBound := hLeft hx ht
  have hRightBound := hRight hy ht
  have hPairBound := hPair hxy ht
  have hBudget :
      logSlack A n + logSlack cFold n = logSlack C n := by
    dsimp [C]
    unfold logSlack
    ring
  change
    2 * n < (t.1 + logSlack C n) + (t.2.1 + logSlack C n) ∧
      2 * n < (t.1 + logSlack C n) + (t.2.2 + logSlack C n) ∧
      3 * n < (t.1 + logSlack C n) + (t.2.1 + logSlack C n) +
        (t.2.2 + logSlack C n)
  constructor
  · by_cases hAlready : 2 * n < t.1 + t.2.1
    · omega
    · have hArgument : t.1 + t.2.1 + 1 ≤ 3 * n + 1 := by
        omega
      have hSlack :
          logSlack cLeft (t.1 + t.2.1 + 1) ≤
            logSlack cFold n := by
        calc
          logSlack cLeft (t.1 + t.2.1 + 1) ≤
              logSlack cWitness (t.1 + t.2.1 + 1) :=
            logSlack_mono_left (by dsimp [cWitness]; omega) _
          _ ≤ logSlack cWitness (3 * n + 1) :=
            logSlack_mono_right cWitness hArgument
          _ ≤ logSlack cFold n := hFold n
      unfold NatCloseWithin at hxClose
      omega
  constructor
  · by_cases hAlready : 2 * n < t.1 + t.2.2
    · omega
    · have hArgument : t.1 + t.2.2 + 1 ≤ 3 * n + 1 := by
        omega
      have hSlack :
          logSlack cRight (t.1 + t.2.2 + 1) ≤
            logSlack cFold n := by
        calc
          logSlack cRight (t.1 + t.2.2 + 1) ≤
              logSlack cWitness (t.1 + t.2.2 + 1) :=
            logSlack_mono_left (by dsimp [cWitness]; omega) _
          _ ≤ logSlack cWitness (3 * n + 1) :=
            logSlack_mono_right cWitness hArgument
          _ ≤ logSlack cFold n := hFold n
      unfold NatCloseWithin at hyClose
      omega
  · by_cases hAlready : 3 * n < t.1 + t.2.1 + t.2.2
    · omega
    · have hArgument :
          t.1 + t.2.1 + t.2.2 + 1 ≤ 3 * n + 1 := by
        omega
      have hSlack :
          logSlack cPair (t.1 + t.2.1 + t.2.2 + 1) ≤
            logSlack cFold n := by
        calc
          logSlack cPair (t.1 + t.2.1 + t.2.2 + 1) ≤
              logSlack cWitness (t.1 + t.2.1 + t.2.2 + 1) :=
            logSlack_mono_left (by dsimp [cWitness]; omega) _
          _ ≤ logSlack cWitness (3 * n + 1) :=
            logSlack_mono_right cWitness hArgument
          _ ≤ logSlack cFold n := hFold n
      unfold NatCloseWithin at hxyClose
      omega

/-- The Muchnik pair from Theorem 224 realizes the lower envelope of SUV
Theorem 225, in both containment directions and with one uniform logarithmic
coordinate error. -/
theorem theorem_225_common_information_lower_envelope_achieved
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ n : Nat,
      ∃ x y : BitString, ∃ kx ky kxy : Nat,
        HasPlainComplexityValue V x kx ∧
        HasPlainComplexityValue V y ky ∧
        HasPlainComplexityValue V (pairCode x y) kxy ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) ∧
        (∀ t ∈ CommonInformationLowerEnvelope n,
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationRegion V x y) ∧
        (∀ t ∈ CommonInformationRegion V x y,
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationLowerEnvelope n) := by
  obtain ⟨cFace, hFace⟩ :=
    theorem_224_common_information_threeFace_containment V hV
  obtain ⟨cLower, hLower⟩ :=
    theorem_225_common_information_universal_lower V hV cFace
  obtain ⟨cUpper, hUpper⟩ :=
    theorem_225_common_information_profile_upper V hV cFace
  let C := cFace + cLower + cUpper
  refine ⟨C, fun n => ?_⟩
  obtain ⟨x, y, kx, ky, kxy, _hxLength, _hyLength,
    hx, hy, hxy, hxClose, hyClose, hxyClose, _hMutual, hFaceContainment⟩ :=
    hFace n
  have hcFace : cFace ≤ C := by dsimp [C]; omega
  have hcLower : cLower ≤ C := by dsimp [C]; omega
  have hcUpper : cUpper ≤ C := by dsimp [C]; omega
  have hFaceSlack : logSlack cFace n ≤ logSlack C n :=
    logSlack_mono_left hcFace n
  have hLowerSlack : logSlack cLower n ≤ logSlack C n :=
    logSlack_mono_left hcLower n
  have hUpperSlack : logSlack cUpper n ≤ logSlack C n :=
    logSlack_mono_left hcUpper n
  refine ⟨x, y, kx, ky, kxy, hx, hy, hxy,
    hxClose.mono hFaceSlack, hyClose.mono hFaceSlack,
    hxyClose.mono hFaceSlack, ?_, ?_⟩
  · intro t ht
    have hMem := hLower n x y kx ky kxy hx hy hxy
      hxClose hyClose hxyClose t ht
    refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
    all_goals
      simp only [commonInformationTripleInflate]
      omega
  · intro t ht
    have hUpperContainment := hUpper n x y kx ky kxy hx hy hxy
      hxClose hyClose hxyClose t ht
    have hThreeFaceContainment := hFaceContainment t ht
    exact commonInformationTripleInflate_mem_lowerEnvelope
      hUpperContainment hThreeFaceContainment hUpperSlack hFaceSlack

/-- Exact finite case cover for the overlapping-factor realization of the
upper envelope.  Either a prefix of the `n`-bit overlap suffices, or the whole
overlap is combined with suitable portions of the two private `n`-bit blocks. -/
theorem commonInformationUpperEnvelope_overlap_case_cover
    {n : Nat} {t : CommonInformationTriple}
    (ht : t ∈ CommonInformationUpperEnvelope (2 * n) (2 * n) (3 * n)) :
    (∃ i,
        i ≤ n ∧ i ≤ t.1 ∧
        2 * n - i ≤ t.2.1 ∧ 2 * n - i ≤ t.2.2) ∨
    (∃ i j,
        i ≤ n ∧ j ≤ n ∧ n + i + j ≤ t.1 ∧
        n - i ≤ t.2.1 ∧ n - j ≤ t.2.2) := by
  change
    2 * n < t.1 + t.2.1 ∧
      2 * n < t.1 + t.2.2 ∧
      3 * n < t.1 + t.2.1 + t.2.2 at ht
  by_cases hFirst : t.1 ≤ n
  · exact Or.inl ⟨t.1, hFirst, le_rfl, by omega, by omega⟩
  · exact Or.inr
      ⟨n - t.2.1, n - t.2.2,
        by omega, by omega, by omega, by omega, by omega⟩

/-- Literal code for the overlapping factors of three blocks. -/
def overlapFactorsLiteralCode
    (left shared right : BitString) : BitString :=
  pairCode (Nat.bits left.length)
    (pairCode (Nat.bits shared.length) (left ++ shared ++ right))

/-- Decoder paired with `overlapFactorsLiteralCode`. -/
def overlapFactorsLiteralLeftLength (q : BitString) : Nat :=
  decodeBits (decodeFirst q)

def overlapFactorsLiteralSharedLength (q : BitString) : Nat :=
  decodeBits (decodeFirst (decodeSecond q))

def overlapFactorsLiteralBody (q : BitString) : BitString :=
  decodeSecond (decodeSecond q)

theorem overlapFactorsLiteralLeftLength_computable :
    Computable overlapFactorsLiteralLeftLength :=
  decodeBitsComputable.comp decodeFirst_computable

theorem overlapFactorsLiteralSharedLength_computable :
    Computable overlapFactorsLiteralSharedLength :=
  decodeBitsComputable.comp
    (decodeFirst_computable.comp decodeSecond_computable)

theorem overlapFactorsLiteralBody_computable :
    Computable overlapFactorsLiteralBody :=
  decodeSecond_computable.comp decodeSecond_computable

def overlapFactorsLiteralLeftSharedLength (q : BitString) : Nat :=
  overlapFactorsLiteralLeftLength q + overlapFactorsLiteralSharedLength q

theorem overlapFactorsLiteralLeftSharedLength_computable :
    Computable overlapFactorsLiteralLeftSharedLength :=
  Primrec.nat_add.to_comp.comp
    overlapFactorsLiteralLeftLength_computable
    overlapFactorsLiteralSharedLength_computable

def overlapFactorsLiteralFirst (q : BitString) : BitString :=
  (overlapFactorsLiteralBody q).take
    (overlapFactorsLiteralLeftSharedLength q)

theorem overlapFactorsLiteralFirst_computable :
    Computable overlapFactorsLiteralFirst :=
  Primrec.list_take.to_comp.comp overlapFactorsLiteralLeftSharedLength_computable
    overlapFactorsLiteralBody_computable

def overlapFactorsLiteralSecond (q : BitString) : BitString :=
  (overlapFactorsLiteralBody q).drop
    (overlapFactorsLiteralLeftLength q)

theorem overlapFactorsLiteralSecond_computable :
    Computable overlapFactorsLiteralSecond :=
  Primrec.list_drop.to_comp.comp overlapFactorsLiteralLeftLength_computable
    overlapFactorsLiteralBody_computable

def decodeOverlapFactorsLiteralCode (q : BitString) : BitString :=
  pairCode (overlapFactorsLiteralFirst q) (overlapFactorsLiteralSecond q)

theorem decodeOverlapFactorsLiteralCode_computable :
    Computable decodeOverlapFactorsLiteralCode := by
  have hPair : Computable₂ (fun a b : BitString => pairCode a b) :=
    pairCode_computable
  exact hPair.comp overlapFactorsLiteralFirst_computable
    overlapFactorsLiteralSecond_computable

@[simp] theorem decodeOverlapFactorsLiteralCode_spec
    (left shared right : BitString) :
    decodeOverlapFactorsLiteralCode
        (overlapFactorsLiteralCode left shared right) =
      pairCode (left ++ shared) (shared ++ right) := by
  simp only [decodeOverlapFactorsLiteralCode, overlapFactorsLiteralCode,
    overlapFactorsLiteralFirst, overlapFactorsLiteralSecond,
    overlapFactorsLiteralLeftSharedLength,
    overlapFactorsLiteralBody, overlapFactorsLiteralLeftLength,
    overlapFactorsLiteralSharedLength,
    decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
  have hTake :
      (left ++ shared ++ right).take (left.length + shared.length) =
        left ++ shared := by
    rw [← List.length_append, List.take_left]
  have hDrop :
      (left ++ shared ++ right).drop left.length = shared ++ right := by
    rw [show left ++ shared ++ right = left ++ (shared ++ right) by simp,
      List.drop_left]
  rw [hTake, hDrop]

theorem overlapFactorsLiteralCode_length_le
    (left shared right : BitString) :
    (overlapFactorsLiteralCode left shared right).length ≤
      left.length + shared.length + right.length +
        logSlack 6 (left.length + shared.length + right.length + 1) := by
  have hBitsLeft :
      (Nat.bits left.length).length ≤
        (Nat.bits (left.length + shared.length + right.length + 1)).length :=
    length_natBits_mono (by omega)
  have hBitsShared :
      (Nat.bits shared.length).length ≤
        (Nat.bits (left.length + shared.length + right.length + 1)).length :=
    length_natBits_mono (by omega)
  simp only [overlapFactorsLiteralCode, length_pairCode,
    List.length_append]
  unfold logSlack
  nlinarith [Nat.zero_le
    (Nat.bits (left.length + shared.length + right.length + 1)).length]

/-- The two overlapping factors of three literal blocks have joint plain
complexity at most the total block length plus logarithmic parsing metadata. -/
theorem pairPlainK_overlapFactors_le_length
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ left shared right : BitString,
      pairPlainK V (left ++ shared) (shared ++ right) ≤
        (((left.length + shared.length + right.length +
          logSlack c (left.length + shared.length + right.length + 1) : Nat)) : ENat) := by
  let D : Map := fun pr =>
    Part.some (decodeOverlapFactorsLiteralCode pr.1)
  have hD : isDecompressor D := Computable.partrec
    (decodeOverlapFactorsLiteralCode_computable.comp Computable.fst)
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  let C := 6 + cD
  refine ⟨C, fun left shared right => ?_⟩
  let prog := overlapFactorsLiteralCode left shared right
  have hProd : produces D prog []
      (pairCode (left ++ shared) (shared ++ right)) := by
    change pairCode (left ++ shared) (shared ++ right) ∈
      Part.some (decodeOverlapFactorsLiteralCode prog)
    rw [show decodeOverlapFactorsLiteralCode prog =
        pairCode (left ++ shared) (shared ++ right) by
      exact decodeOverlapFactorsLiteralCode_spec left shared right]
    exact Part.mem_some _
  have hBound :
      pairPlainK V (left ++ shared) (shared ++ right) ≤
        (prog.length : ENat) + (cD : ENat) := by
    calc
      pairPlainK V (left ++ shared) (shared ++ right)
          ≤ plainK D (pairCode (left ++ shared) (shared ++ right)) +
              (cD : ENat) := hcD _ []
      _ ≤ (prog.length : ENat) + (cD : ENat) := by
        gcongr
        exact sInf_le ⟨prog, hProd, rfl⟩
  have hLength := overlapFactorsLiteralCode_length_le left shared right
  have hSlack := logSlack_add_nat_le 6 cD
    (left.length + shared.length + right.length + 1)
  exact hBound.trans (by
    rw [← Nat.cast_add]
    exact_mod_cast (Nat.add_le_add_right hLength cD |>.trans (by
      dsimp [C]
      omega)))

/-- Conversely, the three literal blocks are recoverable from their two
overlapping factors with logarithmic metadata specifying the shared length. -/
theorem plainK_threeBlocks_le_overlapPair
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ left shared right : BitString,
      plainK V (left ++ shared ++ right) ≤
        pairPlainK V (left ++ shared) (shared ++ right) +
          (logSlack c (left.length + shared.length + right.length + 1) : ENat) := by
  let sharedLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst q)
  let pairProgram : BitString → BitString := fun q =>
    decodeSecond q
  let D : Map := fun pr =>
    (V (pairProgram pr.1, [])).map fun w =>
      decodeFirst w ++ (decodeSecond w).drop (sharedLength pr.1)
  have hSharedLength : Computable sharedLength :=
    decodeBitsComputable.comp decodeFirst_computable
  have hPairProgram : Computable pairProgram := decodeSecond_computable
  have hRun : Partrec (fun pr : BitString × BitString =>
      V (pairProgram pr.1, [])) :=
    Partrec.comp hV.1
      ((hPairProgram.comp Computable.fst).pair (Computable.const []))
  have hOutput : Computable
      (fun q : (BitString × BitString) × BitString =>
        decodeFirst q.2 ++ (decodeSecond q.2).drop (sharedLength q.1.1)) :=
    Computable.list_append.comp
      (decodeFirst_computable.comp Computable.snd)
      (Primrec.list_drop.to_comp.comp
        (hSharedLength.comp (Computable.fst.comp Computable.fst))
        (decodeSecond_computable.comp Computable.snd))
  have hD : isDecompressor D := Partrec.map hRun hOutput
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  let C := cD + 3
  refine ⟨C, fun left shared right => ?_⟩
  obtain ⟨kPair, hkPair⟩ :=
    exists_plainComplexityValue V hV
      (pairCode (left ++ shared) (shared ++ right))
  obtain ⟨p, hp, hpLength⟩ := hkPair.exists_program
  let prog := pairCode (Nat.bits shared.length) p
  have hProd : produces D prog [] (left ++ shared ++ right) := by
    change left ++ shared ++ right ∈
      (V (pairProgram prog, [])).map fun w =>
        decodeFirst w ++ (decodeSecond w).drop (sharedLength prog)
    simp only [prog, pairProgram, sharedLength, decodeFirst_pairCode,
      decodeSecond_pairCode, decodeBits_natBits]
    have h := Part.mem_map
      (fun w => decodeFirst w ++ (decodeSecond w).drop shared.length) hp
    simpa [decodeFirst_pairCode, decodeSecond_pairCode,
      List.drop_left] using h
  have hBound :
      plainK V (left ++ shared ++ right) ≤
        (prog.length : ENat) + (cD : ENat) := by
    calc
      plainK V (left ++ shared ++ right)
          ≤ plainK D (left ++ shared ++ right) + (cD : ENat) :=
        hcD _ []
      _ ≤ (prog.length : ENat) + (cD : ENat) := by
        gcongr
        exact sInf_le ⟨prog, hProd, rfl⟩
  let total := left.length + shared.length + right.length
  have hBitsShared :
      (Nat.bits shared.length).length ≤ (Nat.bits (total + 1)).length :=
    length_natBits_mono (by dsimp [total]; omega)
  have hProgLength :
      prog.length = 2 * (Nat.bits shared.length).length + 1 + kPair := by
    simp only [prog, length_pairCode, hpLength]
    omega
  have hLength :
      prog.length + cD ≤ kPair + logSlack C (total + 1) := by
    rw [hProgLength]
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits (total + 1)).length]
  calc
    plainK V (left ++ shared ++ right)
        ≤ (prog.length : ENat) + (cD : ENat) := hBound
    _ = ((prog.length + cD : Nat) : ENat) := by push_cast; ring
    _ ≤ ((kPair + logSlack C (total + 1) : Nat) : ENat) := by
      exact_mod_cast hLength
    _ = pairPlainK V (left ++ shared) (shared ++ right) +
          (logSlack C (left.length + shared.length + right.length + 1) : ENat) := by
      rw [pairPlainK, hkPair]
      dsimp [total]
      push_cast
      ring

/-- Profile-construction leaf for the upper extremizer.  Split one
incompressible `3n`-bit string into three `n`-bit blocks; the left-plus-middle
and middle-plus-right factors have the required exact finite complexity
profile up to one uniform logarithmic error. -/
theorem exists_incompressibleOverlapPairProfile
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ n : Nat,
      ∃ left shared right : BitString, ∃ kx ky kxy : Nat,
        left.length = n ∧ shared.length = n ∧ right.length = n ∧
        HasPlainComplexityValue V (left ++ shared) kx ∧
        HasPlainComplexityValue V (shared ++ right) ky ∧
        HasPlainComplexityValue V
          (pairCode (left ++ shared) (shared ++ right)) kxy ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) := by
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cThree, hThree⟩ := plainK_threeBlock_le V hV
  obtain ⟨cPairUpper, hPairUpper⟩ :=
    pairPlainK_overlapFactors_le_length V hV
  obtain ⟨cPairLower, hPairLower⟩ :=
    plainK_threeBlocks_le_overlapPair V hV
  let cWitness := cThree + cPairUpper + cPairLower
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cWitness 3 1
  let C := cLen + cFold
  refine ⟨C, fun n => ?_⟩
  obtain ⟨u, huLength, huIncompressible⟩ :=
    existsIncompressibleString V [] (3 * n)
  let left := u.take n
  let rest := u.drop n
  let shared := rest.take n
  let right := rest.drop n
  have hLeftLength : left.length = n := by
    dsimp [left]
    rw [List.length_take, huLength]
    omega
  have hRestLength : rest.length = 2 * n := by
    dsimp [rest]
    rw [List.length_drop, huLength]
    omega
  have hSharedLength : shared.length = n := by
    dsimp [shared]
    rw [List.length_take, hRestLength]
    omega
  have hRightLength : right.length = n := by
    dsimp [right]
    rw [List.length_drop, hRestLength]
    omega
  have hFactor : left ++ shared ++ right = u := by
    rw [List.append_assoc]
    change u.take n ++ ((u.drop n).take n ++ (u.drop n).drop n) = u
    rw [List.take_append_drop, List.take_append_drop]
  obtain ⟨kx, hx⟩ :=
    exists_plainComplexityValue V hV (left ++ shared)
  obtain ⟨ky, hy⟩ :=
    exists_plainComplexityValue V hV (shared ++ right)
  obtain ⟨kxy, hxy⟩ :=
    exists_plainComplexityValue V hV
      (pairCode (left ++ shared) (shared ++ right))
  have hcThree : cThree ≤ cWitness := by dsimp [cWitness]; omega
  have hcPairUpper : cPairUpper ≤ cWitness := by
    dsimp [cWitness]
    omega
  have hcPairLower : cPairLower ≤ cWitness := by
    dsimp [cWitness]
    omega
  have hcFold : cFold ≤ C := by dsimp [C]; omega
  have hThreeSlack :
      logSlack cThree
          (left.length + shared.length + right.length + 1) ≤
        logSlack C n := by
    rw [hLeftLength, hSharedLength, hRightLength]
    calc
      logSlack cThree (n + n + n + 1) ≤
          logSlack cWitness (3 * n + 1) := by
        have h := logSlack_mono_left hcThree (3 * n + 1)
        simpa [show n + n + n + 1 = 3 * n + 1 by omega] using h
      _ ≤ logSlack cFold n := hFold n
      _ ≤ logSlack C n := logSlack_mono_left hcFold n
  have hPairUpperSlack :
      logSlack cPairUpper
          (left.length + shared.length + right.length + 1) ≤
        logSlack C n := by
    rw [hLeftLength, hSharedLength, hRightLength]
    calc
      logSlack cPairUpper (n + n + n + 1) ≤
          logSlack cWitness (3 * n + 1) := by
        have h := logSlack_mono_left hcPairUpper (3 * n + 1)
        simpa [show n + n + n + 1 = 3 * n + 1 by omega] using h
      _ ≤ logSlack cFold n := hFold n
      _ ≤ logSlack C n := logSlack_mono_left hcFold n
  have hPairLowerSlack :
      logSlack cPairLower
          (left.length + shared.length + right.length + 1) ≤
        logSlack C n := by
    rw [hLeftLength, hSharedLength, hRightLength]
    calc
      logSlack cPairLower (n + n + n + 1) ≤
          logSlack cWitness (3 * n + 1) := by
        have h := logSlack_mono_left hcPairLower (3 * n + 1)
        simpa [show n + n + n + 1 = 3 * n + 1 by omega] using h
      _ ≤ logSlack cFold n := hFold n
      _ ≤ logSlack C n := logSlack_mono_left hcFold n
  have hLenSlack : cLen ≤ logSlack C n := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits n).length]
  have hxUpper : kx ≤ 2 * n + logSlack C n := by
    have h := hLen (left ++ shared)
    rw [hx] at h
    have hNat : kx ≤ (left ++ shared).length + cLen := by
      exact_mod_cast h
    simp only [List.length_append, hLeftLength, hSharedLength] at hNat
    omega
  have hyUpper : ky ≤ 2 * n + logSlack C n := by
    have h := hLen (shared ++ right)
    rw [hy] at h
    have hNat : ky ≤ (shared ++ right).length + cLen := by
      exact_mod_cast h
    simp only [List.length_append, hSharedLength, hRightLength] at hNat
    omega
  have hxReconstruct := hThree [] (left ++ shared) right
  have hyReconstruct := hThree left (shared ++ right) []
  have hxLower : 2 * n ≤ kx + logSlack C n := by
    simp only [List.nil_append, List.length_nil, Nat.zero_add,
      List.length_append] at hxReconstruct
    rw [hFactor, hx] at hxReconstruct
    have hE := huIncompressible.trans hxReconstruct
    have hNat : 3 * n ≤
        kx + (right.length + logSlack cThree
          (left.length + shared.length + right.length + 1)) := by
      exact_mod_cast hE
    have hSlack := hThreeSlack
    omega
  have hyLower : 2 * n ≤ ky + logSlack C n := by
    simp only [List.append_nil, List.length_nil, Nat.add_zero,
      List.length_append] at hyReconstruct
    have hFactor' : left ++ (shared ++ right) = u := by
      simpa [List.append_assoc] using hFactor
    rw [hFactor', hy] at hyReconstruct
    have hE := huIncompressible.trans hyReconstruct
    have hNat : 3 * n ≤
        ky + (left.length + logSlack cThree
          (left.length + (shared.length + right.length) + 1)) := by
      exact_mod_cast hE
    have hSlack :
        logSlack cThree
            (left.length + (shared.length + right.length) + 1) ≤
          logSlack C n := by
      simpa [Nat.add_assoc] using hThreeSlack
    omega
  have hxyUpper : kxy ≤ 3 * n + logSlack C n := by
    have h := hPairUpper left shared right
    rw [pairPlainK, hxy] at h
    have hNat : kxy ≤ left.length + shared.length + right.length +
        logSlack cPairUpper
          (left.length + shared.length + right.length + 1) := by
      exact_mod_cast h
    have hSlack := hPairUpperSlack
    omega
  have hxyLower : 3 * n ≤ kxy + logSlack C n := by
    have h := hPairLower left shared right
    rw [hFactor, pairPlainK, hxy] at h
    have hE : (3 * n : ENat) ≤
        (kxy : ENat) +
          (logSlack cPairLower
            (left.length + shared.length + right.length + 1) : ENat) :=
      huIncompressible.trans h
    have hNat : 3 * n ≤ kxy +
        logSlack cPairLower
          (left.length + shared.length + right.length + 1) := by
      exact_mod_cast hE
    have hSlack := hPairLowerSlack
    omega
  exact ⟨left, shared, right, kx, ky, kxy,
    hLeftLength, hSharedLength, hRightLength, hx, hy, hxy,
    ⟨hxUpper, hxLower⟩, ⟨hyUpper, hyLower⟩,
    ⟨hxyUpper, hxyLower⟩⟩

/-- Code for inserting the visible condition between two literal blocks. -/
def insertVisibleContextCode (before after : BitString) : BitString :=
  pairCode (Nat.bits before.length) (before ++ after)

def insertVisibleContext (p context : BitString) : BitString :=
  let beforeLength := decodeBits (decodeFirst p)
  let body := decodeSecond p
  body.take beforeLength ++ context ++ body.drop beforeLength

theorem insertVisibleContext_computable :
    Computable (fun p : BitString × BitString =>
      insertVisibleContext p.1 p.2) := by
  have hLength : Computable (fun p : BitString × BitString =>
      decodeBits (decodeFirst p.1)) :=
    (decodeBitsComputable.comp decodeFirst_computable).comp Computable.fst
  have hBody : Computable (fun p : BitString × BitString =>
      decodeSecond p.1) := decodeSecond_computable.comp Computable.fst
  have hBefore := Primrec.list_take.to_comp.comp hLength hBody
  have hAfter := Primrec.list_drop.to_comp.comp hLength hBody
  exact Computable.list_append.comp
    (Computable.list_append.comp hBefore Computable.snd) hAfter

@[simp] theorem insertVisibleContext_spec
    (before middle after : BitString) :
    insertVisibleContext (insertVisibleContextCode before after) middle =
      before ++ middle ++ after := by
  simp only [insertVisibleContext, insertVisibleContextCode,
    decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
  rw [List.take_left, List.drop_left]

theorem insertVisibleContextCode_length_le
    (before middle after : BitString) :
    (insertVisibleContextCode before after).length ≤
      before.length + after.length +
        logSlack 3 (before.length + middle.length + after.length + 1) := by
  have hBits :
      (Nat.bits before.length).length ≤
        (Nat.bits (before.length + middle.length + after.length + 1)).length :=
    length_natBits_mono (by omega)
  simp only [insertVisibleContextCode, length_pairCode, List.length_append]
  unfold logSlack
  nlinarith [Nat.zero_le
    (Nat.bits (before.length + middle.length + after.length + 1)).length]

/-- Literal blocks around a visible condition cost exactly their total length,
plus logarithmic metadata for the insertion point. -/
theorem condK_insert_visible_context_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ before middle after : BitString,
      condK V (before ++ middle ++ after) middle ≤
        ((before.length + after.length +
          logSlack c (before.length + middle.length + after.length + 1) : Nat) : ENat) := by
  let D : Map := fun pr => Part.some (insertVisibleContext pr.1 pr.2)
  have hD : isDecompressor D :=
    Computable.partrec insertVisibleContext_computable
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  let C := 3 + cD
  refine ⟨C, fun before middle after => ?_⟩
  let prog := insertVisibleContextCode before after
  have hProd : produces D prog middle (before ++ middle ++ after) := by
    change before ++ middle ++ after ∈
      Part.some (insertVisibleContext prog middle)
    rw [show insertVisibleContext prog middle = before ++ middle ++ after by
      exact insertVisibleContext_spec before middle after]
    exact Part.mem_some _
  have hBound : condK V (before ++ middle ++ after) middle ≤
      (prog.length : ENat) + (cD : ENat) := by
    calc
      condK V (before ++ middle ++ after) middle ≤
          condK D (before ++ middle ++ after) middle + (cD : ENat) :=
        hcD _ _
      _ ≤ (prog.length : ENat) + (cD : ENat) := by
        gcongr
        exact sInf_le ⟨prog, hProd, rfl⟩
  have hLength := insertVisibleContextCode_length_le before middle after
  have hSlack := logSlack_add_nat_le 3 cD
    (before.length + middle.length + after.length + 1)
  exact hBound.trans (by
    rw [← Nat.cast_add]
    exact_mod_cast (Nat.add_le_add_right hLength cD |>.trans (by
      dsimp [C]
      omega)))

def overlapMaterialCompletionCode
    (sharedLength leftPrefixLength : Nat) (payload : BitString) : BitString :=
  pairCode (Nat.bits sharedLength)
    (pairCode (Nat.bits leftPrefixLength) payload)

def overlapMaterialSharedLength (p : BitString) : Nat :=
  decodeBits (decodeFirst p)

def overlapMaterialLeftPrefixLength (p : BitString) : Nat :=
  decodeBits (decodeFirst (decodeSecond p))

def overlapMaterialPayload (p : BitString) : BitString :=
  decodeSecond (decodeSecond p)

def recoverLeftOverlapFactor (p context : BitString) : BitString :=
  (context.drop (overlapMaterialSharedLength p)).take
      (overlapMaterialLeftPrefixLength p) ++
    overlapMaterialPayload p ++
    context.take (overlapMaterialSharedLength p)

def recoverRightOverlapFactor (p context : BitString) : BitString :=
  context.take (overlapMaterialSharedLength p) ++
    context.drop
      (overlapMaterialSharedLength p +
        overlapMaterialLeftPrefixLength p) ++
    overlapMaterialPayload p

theorem overlapMaterialSharedLength_computable :
    Computable overlapMaterialSharedLength :=
  decodeBitsComputable.comp decodeFirst_computable

theorem overlapMaterialLeftPrefixLength_computable :
    Computable overlapMaterialLeftPrefixLength :=
  decodeBitsComputable.comp
    (decodeFirst_computable.comp decodeSecond_computable)

theorem overlapMaterialPayload_computable :
    Computable overlapMaterialPayload :=
  decodeSecond_computable.comp decodeSecond_computable

theorem recoverLeftOverlapFactor_computable :
    Computable (fun p : BitString × BitString =>
      recoverLeftOverlapFactor p.1 p.2) := by
  have hShared : Computable (fun p : BitString × BitString =>
      overlapMaterialSharedLength p.1) :=
    overlapMaterialSharedLength_computable.comp Computable.fst
  have hLeft : Computable (fun p : BitString × BitString =>
      overlapMaterialLeftPrefixLength p.1) :=
    overlapMaterialLeftPrefixLength_computable.comp Computable.fst
  have hPayload : Computable (fun p : BitString × BitString =>
      overlapMaterialPayload p.1) :=
    overlapMaterialPayload_computable.comp Computable.fst
  have hDrop : Computable (fun p : BitString × BitString =>
      p.2.drop (overlapMaterialSharedLength p.1)) :=
    Primrec.list_drop.to_comp.comp hShared Computable.snd
  have hPrefix : Computable (fun p : BitString × BitString =>
      (p.2.drop (overlapMaterialSharedLength p.1)).take
        (overlapMaterialLeftPrefixLength p.1)) :=
    Primrec.list_take.to_comp.comp hLeft hDrop
  have hSharedPrefix : Computable (fun p : BitString × BitString =>
      p.2.take (overlapMaterialSharedLength p.1)) :=
    Primrec.list_take.to_comp.comp hShared Computable.snd
  exact Computable.list_append.comp
    (Computable.list_append.comp hPrefix hPayload) hSharedPrefix

theorem recoverRightOverlapFactor_computable :
    Computable (fun p : BitString × BitString =>
      recoverRightOverlapFactor p.1 p.2) := by
  have hShared : Computable (fun p : BitString × BitString =>
      overlapMaterialSharedLength p.1) :=
    overlapMaterialSharedLength_computable.comp Computable.fst
  have hLeft : Computable (fun p : BitString × BitString =>
      overlapMaterialLeftPrefixLength p.1) :=
    overlapMaterialLeftPrefixLength_computable.comp Computable.fst
  have hPayload : Computable (fun p : BitString × BitString =>
      overlapMaterialPayload p.1) :=
    overlapMaterialPayload_computable.comp Computable.fst
  have hSum : Computable (fun p : BitString × BitString =>
      overlapMaterialSharedLength p.1 +
        overlapMaterialLeftPrefixLength p.1) :=
    Primrec.nat_add.to_comp.comp hShared hLeft
  have hSharedPrefix : Computable (fun p : BitString × BitString =>
      p.2.take (overlapMaterialSharedLength p.1)) :=
    Primrec.list_take.to_comp.comp hShared Computable.snd
  have hRightPrefix : Computable (fun p : BitString × BitString =>
      p.2.drop (overlapMaterialSharedLength p.1 +
        overlapMaterialLeftPrefixLength p.1)) :=
    Primrec.list_drop.to_comp.comp hSum Computable.snd
  exact Computable.list_append.comp
    (Computable.list_append.comp hSharedPrefix hRightPrefix) hPayload

theorem overlapMaterialCompletionCode_length_le
    (sharedLength leftPrefixLength : Nat) (payload : BitString) (N : Nat)
    (hShared : sharedLength ≤ N) (hLeft : leftPrefixLength ≤ N) :
    (overlapMaterialCompletionCode
        sharedLength leftPrefixLength payload).length ≤
      payload.length + logSlack 6 (N + 1) := by
  have hBitsShared :
      (Nat.bits sharedLength).length ≤ (Nat.bits (N + 1)).length :=
    length_natBits_mono (by omega)
  have hBitsLeft :
      (Nat.bits leftPrefixLength).length ≤ (Nat.bits (N + 1)).length :=
    length_natBits_mono (by omega)
  simp only [overlapMaterialCompletionCode, length_pairCode]
  unfold logSlack
  nlinarith [Nat.zero_le (Nat.bits (N + 1)).length]

/-- Completing the private prefixes stored beside the entire shared block
recovers both overlapping factors with the exact missing-private-bit costs. -/
theorem condK_overlapFactors_given_materialPrefixes_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ left shared right : BitString, ∀ i j : Nat,
      i ≤ left.length → j ≤ right.length →
      let z := shared ++ left.take i ++ right.take j
      condK V (left ++ shared) z ≤
          ((left.length - i +
            logSlack c (left.length + shared.length + right.length + 1) : Nat) : ENat) ∧
        condK V (shared ++ right) z ≤
          ((right.length - j +
            logSlack c (left.length + shared.length + right.length + 1) : Nat) : ENat) := by
  let Dx : Map := fun pr => Part.some (recoverLeftOverlapFactor pr.1 pr.2)
  let Dy : Map := fun pr => Part.some (recoverRightOverlapFactor pr.1 pr.2)
  have hDx : isDecompressor Dx :=
    Computable.partrec recoverLeftOverlapFactor_computable
  have hDy : isDecompressor Dy :=
    Computable.partrec recoverRightOverlapFactor_computable
  obtain ⟨cx, hcx⟩ := hV.2 Dx hDx
  obtain ⟨cy, hcy⟩ := hV.2 Dy hDy
  let C := 6 + cx + cy
  refine ⟨C, ?_⟩
  intro left shared right i j hi hj
  let z := shared ++ left.take i ++ right.take j
  let N := left.length + shared.length + right.length
  let px := overlapMaterialCompletionCode shared.length i (left.drop i)
  let py := overlapMaterialCompletionCode shared.length i (right.drop j)
  have hLeftTake : (left.take i).length = i := by
    rw [List.length_take]
    omega
  have hRightTake : (right.take j).length = j := by
    rw [List.length_take]
    omega
  have hRecoverX : recoverLeftOverlapFactor px z = left ++ shared := by
    have hDrop : z.drop shared.length = left.take i ++ right.take j := by
      dsimp [z]
      rw [show shared ++ left.take i ++ right.take j =
          shared ++ (left.take i ++ right.take j) by simp,
        List.drop_left]
    have hPrefix : (z.drop shared.length).take i = left.take i := by
      rw [hDrop, List.take_append_of_le_length (by omega),
        List.take_take, Nat.min_self]
    have hSharedPrefix : z.take shared.length = shared := by
      dsimp [z]
      rw [show shared ++ left.take i ++ right.take j =
          shared ++ (left.take i ++ right.take j) by simp,
        List.take_left]
    simp only [recoverLeftOverlapFactor, px,
      overlapMaterialCompletionCode, overlapMaterialSharedLength,
      overlapMaterialLeftPrefixLength, overlapMaterialPayload,
      decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
    rw [hPrefix, hSharedPrefix, List.take_append_drop]
  have hRecoverY : recoverRightOverlapFactor py z = shared ++ right := by
    have hSharedPrefix : z.take shared.length = shared := by
      dsimp [z]
      rw [show shared ++ left.take i ++ right.take j =
          shared ++ (left.take i ++ right.take j) by simp,
        List.take_left]
    have hRightPrefix : z.drop (shared.length + i) = right.take j := by
      dsimp [z]
      rw [← List.drop_drop, show shared ++ left.take i ++ right.take j =
          shared ++ (left.take i ++ right.take j) by simp,
        List.drop_left,
        List.drop_append_of_le_length hLeftTake.symm.le,
        List.drop_eq_nil_of_le hLeftTake.le, List.nil_append]
    simp only [recoverRightOverlapFactor, py,
      overlapMaterialCompletionCode, overlapMaterialSharedLength,
      overlapMaterialLeftPrefixLength, overlapMaterialPayload,
      decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
    rw [hSharedPrefix, hRightPrefix]
    calc
      shared ++ right.take j ++ right.drop j =
          shared ++ (right.take j ++ right.drop j) := by simp
      _ = shared ++ right := by rw [List.take_append_drop]
  have hProdX : produces Dx px z (left ++ shared) := by
    change left ++ shared ∈ Part.some (recoverLeftOverlapFactor px z)
    rw [hRecoverX]
    exact Part.mem_some _
  have hProdY : produces Dy py z (shared ++ right) := by
    change shared ++ right ∈ Part.some (recoverRightOverlapFactor py z)
    rw [hRecoverY]
    exact Part.mem_some _
  have hBoundX : condK V (left ++ shared) z ≤
      (px.length : ENat) + (cx : ENat) := by
    calc
      condK V (left ++ shared) z ≤ condK Dx (left ++ shared) z + (cx : ENat) :=
        hcx _ _
      _ ≤ (px.length : ENat) + (cx : ENat) := by
        gcongr
        exact sInf_le ⟨px, hProdX, rfl⟩
  have hBoundY : condK V (shared ++ right) z ≤
      (py.length : ENat) + (cy : ENat) := by
    calc
      condK V (shared ++ right) z ≤ condK Dy (shared ++ right) z + (cy : ENat) :=
        hcy _ _
      _ ≤ (py.length : ENat) + (cy : ENat) := by
        gcongr
        exact sInf_le ⟨py, hProdY, rfl⟩
  have hSharedN : shared.length ≤ N := by dsimp [N]; omega
  have hiN : i ≤ N := by dsimp [N]; omega
  have hPxLength := overlapMaterialCompletionCode_length_le
    shared.length i (left.drop i) N hSharedN hiN
  have hPyLength := overlapMaterialCompletionCode_length_le
    shared.length i (right.drop j) N hSharedN hiN
  have hSlackX := logSlack_add_nat_le 6 cx (N + 1)
  have hSlackY := logSlack_add_nat_le (6 + cx) cy (N + 1)
  have hFinalSlackX :
      logSlack 6 (N + 1) + cx ≤ logSlack C (N + 1) := by
    exact hSlackX.trans
      (logSlack_mono_left (by dsimp [C]; omega) (N + 1))
  have hFinalSlackY :
      logSlack 6 (N + 1) + cy ≤ logSlack C (N + 1) := by
    calc
      logSlack 6 (N + 1) + cy ≤
          logSlack (6 + cx) (N + 1) + cy :=
        Nat.add_le_add_right
          (logSlack_mono_left (by omega) (N + 1)) cy
      _ ≤ logSlack C (N + 1) := by
        simpa [C] using hSlackY
  have hNatX :
      px.length + cx ≤ left.length - i +
        logSlack C (left.length + shared.length + right.length + 1) := by
    have hL : px.length ≤ left.length - i +
        logSlack 6 (left.length + shared.length + right.length + 1) := by
      simpa [px, N, List.length_drop] using hPxLength
    have hS :
        logSlack 6 (left.length + shared.length + right.length + 1) + cx ≤
          logSlack C (left.length + shared.length + right.length + 1) := by
      simpa [N] using hFinalSlackX
    omega
  have hNatY :
      py.length + cy ≤ right.length - j +
        logSlack C (left.length + shared.length + right.length + 1) := by
    have hL : py.length ≤ right.length - j +
        logSlack 6 (left.length + shared.length + right.length + 1) := by
      simpa [py, N, List.length_drop] using hPyLength
    have hS :
        logSlack 6 (left.length + shared.length + right.length + 1) + cy ≤
          logSlack C (left.length + shared.length + right.length + 1) := by
      simpa [N] using hFinalSlackY
    omega
  constructor
  · exact hBoundX.trans (by
      rw [← Nat.cast_add]
      exact_mod_cast hNatX)
  · exact hBoundY.trans (by
      rw [← Nat.cast_add]
      exact_mod_cast hNatY)

/-- Decoder leaf for the two material-bit families in the source proof of the
upper extremizer.  A common string is either a prefix of the shared block, or
the whole shared block together with prefixes of the two private blocks. -/
theorem commonInformationRegion_contains_overlapMaterialProfiles
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ left shared right : BitString,
      (∀ i : Nat, i ≤ shared.length →
        commonInformationTripleInflate
            (logSlack c (left.length + shared.length + right.length + 1))
            (i,
              (left.length + shared.length - i,
                shared.length + right.length - i)) ∈
          CommonInformationRegion V
            (left ++ shared) (shared ++ right)) ∧
      (∀ i j : Nat, i ≤ left.length → j ≤ right.length →
        commonInformationTripleInflate
            (logSlack c (left.length + shared.length + right.length + 1))
            (shared.length + i + j,
              (left.length - i, right.length - j)) ∈
          CommonInformationRegion V
            (left ++ shared) (shared ++ right)) := by
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cInsert, hInsert⟩ := condK_insert_visible_context_le V hV
  obtain ⟨cPrivate, hPrivate⟩ :=
    condK_overlapFactors_given_materialPrefixes_le V hV
  let C := cLen + cInsert + cPrivate + 1
  refine ⟨C, fun left shared right => ?_⟩
  let N := left.length + shared.length + right.length + 1
  have hLenSlack : cLen < logSlack C N := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  have hInsertSlack : logSlack cInsert N < logSlack C N := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  have hPrivateSlack : logSlack cPrivate N < logSlack C N := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  constructor
  · intro i hi
    let z := shared.take i
    have hzLength : z.length = i := by
      dsimp [z]
      rw [List.length_take]
      omega
    have hxRaw := hInsert left z (shared.drop i)
    have hyRaw := hInsert [] z (shared.drop i ++ right)
    have hTakeDrop : shared.take i ++ shared.drop i = shared :=
      List.take_append_drop i shared
    have hxBound : condK V (left ++ shared) z ≤
        ((left.length + shared.length - i + logSlack cInsert N : Nat) : ENat) := by
      have h := hxRaw
      rw [show left ++ z ++ shared.drop i = left ++ shared by
        simp [z, List.append_assoc, hTakeDrop]] at h
      have hArg :
          left.length + z.length + (shared.drop i).length + 1 ≤ N := by
        dsimp [N]
        rw [hzLength, List.length_drop]
        omega
      have hNat :
          left.length + (shared.drop i).length +
              logSlack cInsert
                (left.length + z.length + (shared.drop i).length + 1) ≤
            left.length + shared.length - i + logSlack cInsert N := by
        have hArg' :
            left.length + z.length + (shared.length - i) + 1 ≤ N := by
          simpa [List.length_drop] using hArg
        have hSlack := logSlack_mono_right cInsert hArg'
        rw [List.length_drop]
        omega
      exact h.trans (by exact_mod_cast hNat)
    have hyBound : condK V (shared ++ right) z ≤
        ((shared.length + right.length - i + logSlack cInsert N : Nat) : ENat) := by
      have h := hyRaw
      rw [show [] ++ z ++ (shared.drop i ++ right) = shared ++ right by
        simp only [List.nil_append]
        rw [← List.append_assoc, hTakeDrop]] at h
      have hArg :
          0 + z.length + (shared.drop i ++ right).length + 1 ≤ N := by
        dsimp [N]
        rw [hzLength, List.length_append, List.length_drop]
        omega
      have hNat :
          0 + (shared.drop i ++ right).length +
              logSlack cInsert
                (0 + z.length + (shared.drop i ++ right).length + 1) ≤
            shared.length + right.length - i + logSlack cInsert N := by
        have hArg' :
            z.length + (shared.length - i + right.length) + 1 ≤ N := by
          simpa [List.length_append, List.length_drop] using hArg
        have hSlack := logSlack_mono_right cInsert hArg'
        simp only [List.length_append, List.length_drop,
          Nat.zero_add]
        omega
      exact h.trans (by exact_mod_cast hNat)
    change ∃ w,
      plainK V w < ((i + logSlack C N : Nat) : ENat) ∧
        condK V (left ++ shared) w <
          ((left.length + shared.length - i + logSlack C N : Nat) : ENat) ∧
        condK V (shared ++ right) w <
          ((shared.length + right.length - i + logSlack C N : Nat) : ENat)
    refine ⟨z, ?_, ?_, ?_⟩
    · have h := hLen z
      change plainK V z ≤ (z.length : ENat) + (cLen : ENat) at h
      rw [hzLength] at h
      exact h.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hLenSlack i)
    · exact hxBound.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hInsertSlack
          (left.length + shared.length - i))
    · exact hyBound.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hInsertSlack
          (shared.length + right.length - i))
  · intro i j hi hj
    let z := shared ++ left.take i ++ right.take j
    have hzLength : z.length = shared.length + i + j := by
      dsimp [z]
      simp only [List.length_append, List.length_take]
      omega
    obtain ⟨hxBound, hyBound⟩ := hPrivate left shared right i j hi hj
    change ∃ w,
      plainK V w <
          ((shared.length + i + j + logSlack C N : Nat) : ENat) ∧
        condK V (left ++ shared) w <
          ((left.length - i + logSlack C N : Nat) : ENat) ∧
        condK V (shared ++ right) w <
          ((right.length - j + logSlack C N : Nat) : ENat)
    refine ⟨z, ?_, ?_, ?_⟩
    · have h := hLen z
      change plainK V z ≤ (z.length : ENat) + (cLen : ENat) at h
      rw [hzLength] at h
      exact h.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hLenSlack
          (shared.length + i + j))
    · exact hxBound.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hPrivateSlack (left.length - i))
    · exact hyBound.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hPrivateSlack (right.length - j))

/-- The remaining extremal direction of SUV Theorem 225: overlapping length
`2n` factors of an incompressible length-`3n` string realize the universal
upper envelope.  The two quantified containments state equality up to one
uniform coordinatewise logarithmic inflation. -/
theorem theorem_225_common_information_upper_envelope_achieved
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ n : Nat,
      ∃ x y : BitString, ∃ kx ky kxy : Nat,
        HasPlainComplexityValue V x kx ∧
        HasPlainComplexityValue V y ky ∧
        HasPlainComplexityValue V (pairCode x y) kxy ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) ∧
        (∀ t ∈ CommonInformationUpperEnvelope (2 * n) (2 * n) (3 * n),
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationRegion V x y) ∧
        (∀ t ∈ CommonInformationRegion V x y,
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationUpperEnvelope (2 * n) (2 * n) (3 * n)) := by
  obtain ⟨cProfile, hProfile⟩ :=
    exists_incompressibleOverlapPairProfile V hV
  obtain ⟨cMaterial, hMaterial⟩ :=
    commonInformationRegion_contains_overlapMaterialProfiles V hV
  obtain ⟨cUpper, hUpper⟩ :=
    theorem_225_common_information_profile_upper V hV cProfile
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cMaterial 3 1
  let C := cProfile + cUpper + cFold
  refine ⟨C, fun n => ?_⟩
  obtain ⟨left, shared, right, kx, ky, kxy,
    hLeftLength, hSharedLength, hRightLength,
    hx, hy, hxy, hxClose, hyClose, hxyClose⟩ := hProfile n
  let x := left ++ shared
  let y := shared ++ right
  have hcProfile : cProfile ≤ C := by dsimp [C]; omega
  have hcUpper : cUpper ≤ C := by dsimp [C]; omega
  have hcFold : cFold ≤ C := by dsimp [C]; omega
  have hProfileSlack : logSlack cProfile n ≤ logSlack C n :=
    logSlack_mono_left hcProfile n
  have hUpperSlack : logSlack cUpper n ≤ logSlack C n :=
    logSlack_mono_left hcUpper n
  have hMaterialSlack :
      logSlack cMaterial
          (left.length + shared.length + right.length + 1) ≤
        logSlack C n := by
    rw [hLeftLength, hSharedLength, hRightLength]
    have hArgument : n + n + n + 1 = 3 * n + 1 := by omega
    rw [hArgument]
    exact (hFold n).trans (logSlack_mono_left hcFold n)
  have hMaterialSlack' :
      logSlack cMaterial (n + n + n + 1) ≤ logSlack C n := by
    simpa only [hLeftLength, hSharedLength, hRightLength] using
      hMaterialSlack
  refine ⟨x, y, kx, ky, kxy, hx, hy, hxy,
    hxClose.mono hProfileSlack, hyClose.mono hProfileSlack,
    hxyClose.mono hProfileSlack, ?_, ?_⟩
  · intro t ht
    obtain ⟨hSharedProfiles, hPrivateProfiles⟩ :=
      hMaterial left shared right
    rcases commonInformationUpperEnvelope_overlap_case_cover ht with
      hSharedCase | hPrivateCase
    · rcases hSharedCase with ⟨i, hi, hFirst, hLeft, hRight⟩
      have hMem := hSharedProfiles i (by simpa [hSharedLength] using hi)
      refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
      all_goals
        simp only [commonInformationTripleInflate,
          hLeftLength, hSharedLength, hRightLength]
        omega
    · rcases hPrivateCase with
        ⟨i, j, hi, hj, hFirst, hLeft, hRight⟩
      have hMem := hPrivateProfiles i j
        (by simpa [hLeftLength] using hi)
        (by simpa [hRightLength] using hj)
      refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
      all_goals
        simp only [commonInformationTripleInflate,
          hLeftLength, hSharedLength, hRightLength]
        omega
  · intro t ht
    have hContainment := hUpper n x y kx ky kxy hx hy hxy
      hxClose hyClose hxyClose t ht
    refine commonInformationUpperEnvelope_upward_closed
      (2 * n) (2 * n) (3 * n) hContainment ?_ ?_ ?_
    all_goals
      simp only [commonInformationTripleInflate]
      omega

end Kolmogorov
