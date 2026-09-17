import KolmogorovMathlib.CommonInformation.RegionEnvelopes
import KolmogorovMathlib.CommonInformation.OverlapExtraction

/-!
# Realizing the lower envelope by explicit witnesses

The constructive half of SUV Theorem 225: every triple of the lower envelope is realized by a
common witness.  The witnesses are prefixes of plain programs, and this part builds them case
by case — `CombinedCase`, `AnchoredXYCase` and `AnchoredYXCase` name the three regimes of the
cover, with `ProducesOfLength` fixing what a program of a given length is.

The three realization statements are
`commonInformationRegion_contains_combinedPlainPrefixProfile` (prefixes of two independent
plain descriptions realize the sloping face),
`commonInformationRegion_contains_anchoredConditionalPrefixProfile` (a full description of `y`
followed by a prefix of a conditional one) and
`commonInformationRegion_contains_plainPrefixTransitiveProfile`;
`commonInformationRegion_swap` halves the work by symmetry.

The overlap coding (`overlapFactorsLiteralCode`, `decodeOverlapFactorsLiteralCode_spec`,
`pairPlainK_overlapFactors_le_length`, `plainK_threeBlocks_le_overlapPair`) is what lets three
literal blocks be traded for their two overlapping factors, and the `logSlack_universal_lower_*`
lemmas absorb the case-by-case errors.
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
  obtain ⟨cPlain, hPlain⟩ := plainK_combinedProgramPrefixes_le V hV
  obtain ⟨cCond, hCond⟩ := condK_outputs_given_combined_plainProgramPrefixes_le V hV
  let C := cPlain + cCond + 1
  refine ⟨C, ?_⟩
  intro p q x y i j hpx hqy hi hj
  let N := p.length + q.length + 1
  let z := p.take i ++ q.take j
  have hPlainBound := hPlain p q i j hi hj
  have hCondBounds := hCond p q x y i j hpx hqy hi hj
  dsimp only at hCondBounds
  have hPlainSlack : logSlack cPlain N < logSlack C N := by
    dsimp only [C, logSlack]; nlinarith [Nat.zero_le (Nat.bits N).length]
  have hCondSlack : logSlack cCond N < logSlack C N := by
    dsimp only [C, logSlack]; nlinarith [Nat.zero_le (Nat.bits N).length]
  change ∃ w, plainK V w < (((i + j + logSlack C N : Nat)) : ENat) ∧
      condK V x w < (((p.length - i + logSlack C N : Nat)) : ENat) ∧
      condK V y w < (((q.length - j + logSlack C N : Nat)) : ENat)
  refine ⟨z, ?_, ?_, ?_⟩
  · exact hPlainBound.trans_lt (by exact_mod_cast Nat.add_lt_add_left hPlainSlack (i + j))
  · exact hCondBounds.1.trans_lt (by exact_mod_cast Nat.add_lt_add_left hCondSlack (p.length - i))
  · exact hCondBounds.2.trans_lt (by exact_mod_cast Nat.add_lt_add_left hCondSlack (q.length - j))

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
  obtain ⟨cPlain, hPlain⟩ := plainK_combinedProgramPrefixes_le V hV
  obtain ⟨cCond, hCond⟩ := condK_outputs_given_plain_and_conditionalProgramPrefix_le V hV
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
    dsimp only [C, logSlack]; nlinarith [Nat.zero_le (Nat.bits N).length]
  have hCondSlack : logSlack cCond N < logSlack C N := by
    dsimp only [C, logSlack]; nlinarith [Nat.zero_le (Nat.bits N).length]
  change ∃ w, plainK V w < (((p.length + i + logSlack C N : Nat)) : ENat) ∧
      condK V x w < (((q.length - i + logSlack C N : Nat)) : ENat) ∧
      condK V y w < (((0 + logSlack C N : Nat)) : ENat)
  simp only [Nat.zero_add]
  refine ⟨z, ?_, ?_, ?_⟩
  · exact hPlainBound.trans_lt (by exact_mod_cast Nat.add_lt_add_left hPlainSlack (p.length + i))
  · exact hCondBounds.2.trans_lt (by exact_mod_cast Nat.add_lt_add_left hCondSlack (q.length - i))
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
  obtain ⟨cPlain, hPlain⟩ := plainK_combinedProgramPrefixes_le V hV
  obtain ⟨cY, hY⟩ := condK_output_given_plainProgramPrefix_le V hV
  obtain ⟨cX, hX⟩ := condK_output_given_plainProgramPrefix_then_conditionalProgram_le V hV
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
  have hBits : (Nat.bits (p.length + 1)).length ≤ (Nat.bits N).length :=
    length_natBits_mono (by dsimp only [N]; omega)
  have hPlainSlack : logSlack cPlain (p.length + 1) < logSlack C N := by
    dsimp only [C, logSlack]; nlinarith [Nat.zero_le (Nat.bits N).length]
  have hYSlack : logSlack cY (p.length + 1) < logSlack C N := by
    dsimp only [C, logSlack]; nlinarith [Nat.zero_le (Nat.bits N).length]
  have hXSlack : logSlack cX N < logSlack C N := by
    dsimp only [C, logSlack]; nlinarith [Nat.zero_le (Nat.bits N).length]
  change ∃ w, plainK V w < (((i + logSlack C N : Nat)) : ENat) ∧
      condK V x w < (((p.length - i + q.length + logSlack C N : Nat)) : ENat) ∧
      condK V y w < (((p.length - i + logSlack C N : Nat)) : ENat)
  refine ⟨z, ?_, ?_, ?_⟩
  · exact hPlainBound.trans_lt (by exact_mod_cast Nat.add_lt_add_left hPlainSlack i)
  · exact hXBound.trans_lt (by exact_mod_cast Nat.add_lt_add_left hXSlack (p.length - i + q.length))
  · exact hYBound.trans_lt (by exact_mod_cast Nat.add_lt_add_left hYSlack (p.length - i))

/-- Swapping the two source strings swaps the two conditional coordinates of
the common-information region. -/
theorem commonInformationRegion_swap
    {V : Map} {x y : BitString} {t : CommonInformationTriple} :
    t ∈ CommonInformationRegion V y x ↔ (t.1, (t.2.2, t.2.1)) ∈ CommonInformationRegion V x y :=
  ⟨fun ⟨z, hz, hy, hx⟩ => ⟨z, hz, hx, hy⟩, fun ⟨z, hz, hx, hy⟩ => ⟨z, hz, hy, hx⟩⟩


/-- Upper bound on logSlack arg for universal lower bound profile cases. -/
private lemma logSlack_universal_lower_arg_le (A cCond n kx ky kxyCond kyxCond : Nat)
    (hxClose : NatCloseWithin kx (2 * n) (logSlack A n))
    (hyClose : NatCloseWithin ky (2 * n) (logSlack A n))
    (hkxyClose : NatCloseWithin kxyCond n (logSlack cCond n))
    (hkyxClose : NatCloseWithin kyxCond n (logSlack cCond n)) :
    kx + ky + 1 ≤ (4 + 2 * A + 2 * cCond) * n + (2 * A + 2 * cCond + 1) ∧
    ky + kxyCond + 1 ≤ (4 + 2 * A + 2 * cCond) * n + (2 * A + 2 * cCond + 1) ∧
    kx + kyxCond + 1 ≤ (4 + 2 * A + 2 * cCond) * n + (2 * A + 2 * cCond + 1) := by
  have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
  have hALinear : logSlack A n ≤ A * n + A := by
    dsimp [logSlack]; nlinarith [Nat.mul_le_mul_left A hBits]
  have hCondLinear : logSlack cCond n ≤ cCond * n + cCond := by
    dsimp [logSlack]; nlinarith [Nat.mul_le_mul_left cCond hBits]
  unfold NatCloseWithin at hxClose hyClose hkxyClose hkyxClose
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- Bounded component logSlack bound for universal lower envelope cases. -/
private lemma logSlack_universal_lower_component_bound
    (cComp cCombined cAnchored cTrans cFold n A cCond kComp : Nat)
    (hcComp : cComp ≤ cCombined + cAnchored + cTrans)
    (hFold : logSlack (cCombined + cAnchored + cTrans)
      ((4 + 2 * A + 2 * cCond) * n + (2 * A + 2 * cCond + 1)) ≤ logSlack cFold n)
    (hkComp : kComp ≤ (4 + 2 * A + 2 * cCond) * n + (2 * A + 2 * cCond + 1)) :
    logSlack cComp kComp ≤ logSlack cFold n := by
  calc
    logSlack cComp kComp ≤ logSlack (cCombined + cAnchored + cTrans) kComp :=
      logSlack_mono_left hcComp _
    _ ≤ logSlack (cCombined + cAnchored + cTrans)
        ((4 + 2 * A + 2 * cCond) * n + (2 * A + 2 * cCond + 1)) :=
      logSlack_mono_right _ hkComp
    _ ≤ logSlack cFold n := hFold

/-- Combined logSlack error bound for universal lower envelope cases. -/
private lemma logSlack_universal_lower_error_le
    (A cCond cFold C cComp n kComp : Nat)
    (hBudget : logSlack A n + logSlack cCond n + logSlack cFold n = logSlack C n)
    (hSlack : logSlack cComp kComp ≤ logSlack cFold n) :
    logSlack A n + logSlack cCond n + logSlack cComp kComp ≤ logSlack C n := by
  rw [← hBudget]
  omega

/-- `p` is a program of length `k` that produces `x` from the condition `cond`. -/
private def ProducesOfLength (V : Map) (p cond x : BitString) (k : Nat) : Prop :=
  produces V p cond x ∧ p.length = k

/-- The combined case of the envelope cover at `(i, j)`: both indices are at most `2 * n` and
`t` dominates the threshold triple `(i + j, (2 * n - i, 2 * n - j))`. -/
private def CombinedCase (n : Nat) (t : CommonInformationTriple) (i j : Nat) : Prop :=
  i ≤ 2 * n ∧ j ≤ 2 * n ∧ i + j ≤ t.1 ∧ 2 * n - i ≤ t.2.1 ∧ 2 * n - j ≤ t.2.2

/-- The anchored `y`-then-`x` case of the envelope cover at `i`: the index is at most `n` and
`t` dominates the threshold triple `(2 * n + i, (n - i, 0))`. -/
private def AnchoredXYCase (n : Nat) (t : CommonInformationTriple) (i : Nat) : Prop :=
  i ≤ n ∧ 2 * n + i ≤ t.1 ∧ n - i ≤ t.2.1

/-- The anchored `x`-then-`y` case of the envelope cover at `i`: the index is at most `n` and
`t` dominates the threshold triple `(2 * n + i, (0, n - i))`. -/
private def AnchoredYXCase (n : Nat) (t : CommonInformationTriple) (i : Nat) : Prop :=
  i ≤ n ∧ 2 * n + i ≤ t.1 ∧ n - i ≤ t.2.2

/-- The transitive `y`-then-`x` case of the envelope cover at `i`: the index is at most `2 * n`
and `t` dominates the threshold triple `(i, (3 * n - i, 2 * n - i))`. -/
private def TransXYCase (n : Nat) (t : CommonInformationTriple) (i : Nat) : Prop :=
  i ≤ 2 * n ∧ i ≤ t.1 ∧ 3 * n - i ≤ t.2.1 ∧ 2 * n - i ≤ t.2.2

/-- The transitive `x`-then-`y` case of the envelope cover at `i`: the index is at most `2 * n`
and `t` dominates the threshold triple `(i, (2 * n - i, 3 * n - i))`. -/
private def TransYXCase (n : Nat) (t : CommonInformationTriple) (i : Nat) : Prop :=
  i ≤ 2 * n ∧ i ≤ t.1 ∧ 2 * n - i ≤ t.2.1 ∧ 3 * n - i ≤ t.2.2

/-- The combined inflation rule at the constant `c`: two unconditional programs `p` for `x`
and `q` for `y` put every triple `(i + j, (|p| - i, |q| - j))` with `i ≤ |p|`, `j ≤ |q|` into
the common information region, once inflated by `logSlack c (|p| + |q| + 1)`.
This is an assumption on `V` and `c`; it is discharged for an optimal `V` in
`common_information_universal_lower`, from
`commonInformationRegion_contains_combinedPlainPrefixProfile`. -/
private def CommonInformationCombinedRule (V : Map) (c : Nat) : Prop :=
  ∀ (p q x y : BitString) (i j : ℕ),
    produces V p [] x → produces V q [] y → i ≤ p.length → j ≤ q.length →
    commonInformationTripleInflate (logSlack c (p.length + q.length + 1))
      (i + j, (p.length - i, q.length - j)) ∈ CommonInformationRegion V x y

/-- The anchored inflation rule at the constant `c`: a program `p` for `y` and a program `q`
for `x` given `y` put every triple `(|p| + i, (|q| - i, 0))` with `i ≤ |q|` into the common
information region, once inflated by `logSlack c (|p| + |q| + 1)`.
This is an assumption on `V` and `c`; it is discharged for an optimal `V` in
`common_information_universal_lower`, from
`commonInformationRegion_contains_anchoredConditionalPrefixProfile`. -/
private def CommonInformationAnchoredRule (V : Map) (c : Nat) : Prop :=
  ∀ (p q x y : BitString) (i : ℕ),
    produces V p [] y → produces V q y x → i ≤ q.length →
    commonInformationTripleInflate (logSlack c (p.length + q.length + 1))
      (p.length + i, (q.length - i, 0)) ∈ CommonInformationRegion V x y

/-- The transitive inflation rule at the constant `c`: a program `p` for `y` and a program `q`
for `x` given `y` put every triple `(i, (|p| - i + |q|, |p| - i))` with `i ≤ |p|` into the
common information region, once inflated by `logSlack c (|p| + |q| + 1)`.
This is an assumption on `V` and `c`; it is discharged for an optimal `V` in
`common_information_universal_lower`, from
`commonInformationRegion_contains_plainPrefixTransitiveProfile`. -/
private def CommonInformationTransRule (V : Map) (c : Nat) : Prop :=
  ∀ (p q x y : BitString) (i : ℕ),
    produces V p [] y → produces V q y x → i ≤ p.length →
    commonInformationTripleInflate (logSlack c (p.length + q.length + 1))
      (i, (p.length - i + q.length, p.length - i)) ∈ CommonInformationRegion V x y

/-- Combined case: from shortest programs `px`, `py` for `x` and `y` of lengths within
`logSlack A n` of `2 * n`, every triple `t` dominating `(i + j, (2 * n - i, 2 * n - j))` for some
`i, j ≤ 2 * n` lies in `CommonInformationRegion V x y` once inflated by `logSlack C n`. -/
private lemma common_information_universal_lower_combined_case
    (V : Map) (cCombined A cCond n kx ky C : Nat) (x y : BitString)
    (px py : BitString)
    (hCombined : CommonInformationCombinedRule V cCombined)
    (hpx : ProducesOfLength V px [] x kx) (hpy : ProducesOfLength V py [] y ky)
    (hxClose : NatCloseWithin kx (2 * n) (logSlack A n))
    (hyClose : NatCloseWithin ky (2 * n) (logSlack A n))
    (hCombinedError : logSlack A n + logSlack cCond n +
      logSlack cCombined (kx + ky + 1) ≤ logSlack C n)
    (t : CommonInformationTriple) (i j : Nat) (hCase : CombinedCase n t i j) :
    commonInformationTripleInflate (logSlack C n) t ∈ CommonInformationRegion V x y := by
  obtain ⟨hpx, hpxLength⟩ := hpx
  obtain ⟨hpy, hpyLength⟩ := hpy
  obtain ⟨hi, hj, hFirst, hLeft, hRight⟩ := hCase
  let i' := min i kx
  let j' := min j ky
  have hi' : i' ≤ px.length := by rw [hpxLength]; exact min_le_right _ _
  have hj' : j' ≤ py.length := by rw [hpyLength]; exact min_le_right _ _
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

/-- Anchored case in the `y`-then-`x` direction: from a program `py` for `y` and a program `pxy`
for `x` given `y`, every triple `t` dominating `(2 * n + i, (n - i, 0))` for some `i ≤ n` lies in
`CommonInformationRegion V x y` once inflated by `logSlack C n`. -/
private lemma common_information_universal_lower_anchored_xy_case
    (V : Map) (cAnchored A cCond n ky kxyCond C : Nat) (x y : BitString)
    (py pxy : BitString)
    (hAnchored : CommonInformationAnchoredRule V cAnchored)
    (hpy : ProducesOfLength V py [] y ky) (hpxy : ProducesOfLength V pxy y x kxyCond)
    (hyClose : NatCloseWithin ky (2 * n) (logSlack A n))
    (hkxyClose : NatCloseWithin kxyCond n (logSlack cCond n))
    (hXYAnchoredError : logSlack A n + logSlack cCond n +
      logSlack cAnchored (ky + kxyCond + 1) ≤ logSlack C n)
    (t : CommonInformationTriple) (i : Nat) (hCase : AnchoredXYCase n t i) :
    commonInformationTripleInflate (logSlack C n) t ∈ CommonInformationRegion V x y := by
  obtain ⟨hpy, hpyLength⟩ := hpy
  obtain ⟨hpxy, hpxyLength⟩ := hpxy
  obtain ⟨hi, hFirst, hLeft⟩ := hCase
  let i' := min i kxyCond
  have hi' : i' ≤ pxy.length := by rw [hpxyLength]; exact min_le_right _ _
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

/-- Anchored case in the `x`-then-`y` direction: from a program `px` for `x` and a program `pyx`
for `y` given `x`, every triple `t` dominating `(2 * n + i, (0, n - i))` for some `i ≤ n` lies in
`CommonInformationRegion V x y` once inflated by `logSlack C n`. -/
private lemma common_information_universal_lower_anchored_yx_case
    (V : Map) (cAnchored A cCond n kx kyxCond C : Nat) (x y : BitString)
    (px pyx : BitString)
    (hAnchored : CommonInformationAnchoredRule V cAnchored)
    (hpx : ProducesOfLength V px [] x kx) (hpyx : ProducesOfLength V pyx x y kyxCond)
    (hxClose : NatCloseWithin kx (2 * n) (logSlack A n))
    (hkyxClose : NatCloseWithin kyxCond n (logSlack cCond n))
    (hYXAnchoredError : logSlack A n + logSlack cCond n +
      logSlack cAnchored (kx + kyxCond + 1) ≤ logSlack C n)
    (t : CommonInformationTriple) (i : Nat) (hCase : AnchoredYXCase n t i) :
    commonInformationTripleInflate (logSlack C n) t ∈ CommonInformationRegion V x y := by
  obtain ⟨hpx, hpxLength⟩ := hpx
  obtain ⟨hpyx, hpyxLength⟩ := hpyx
  obtain ⟨hi, hFirst, hRight⟩ := hCase
  let i' := min i kyxCond
  have hi' : i' ≤ pyx.length := by rw [hpyxLength]; exact min_le_right _ _
  have hMemYX := hAnchored px pyx y x i' hpx hpyx hi'
  have hMem :
      commonInformationTripleInflate
          (logSlack cAnchored (px.length + pyx.length + 1))
          (px.length + i', (0, pyx.length - i')) ∈
        CommonInformationRegion V x y := by
    have hSwap := (commonInformationRegion_swap (V := V) (x := x) (y := y)).mp hMemYX
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

/-- Transitive case in the `y`-then-`x` direction: from a program `py` for `y` and a program
`pxy` for `x` given `y`, every triple `t` dominating `(i, (3 * n - i, 2 * n - i))` for some
`i ≤ 2 * n` lies in `CommonInformationRegion V x y` once inflated by `logSlack C n`. -/
private lemma common_information_universal_lower_trans_xy_case
    (V : Map) (cTrans A cCond n ky kxyCond C : Nat) (x y : BitString)
    (py pxy : BitString)
    (hTrans : CommonInformationTransRule V cTrans)
    (hpy : ProducesOfLength V py [] y ky) (hpxy : ProducesOfLength V pxy y x kxyCond)
    (hyClose : NatCloseWithin ky (2 * n) (logSlack A n))
    (hkxyClose : NatCloseWithin kxyCond n (logSlack cCond n))
    (hXYTransError : logSlack A n + logSlack cCond n +
      logSlack cTrans (ky + kxyCond + 1) ≤ logSlack C n)
    (t : CommonInformationTriple) (i : Nat) (hCase : TransXYCase n t i) :
    commonInformationTripleInflate (logSlack C n) t ∈ CommonInformationRegion V x y := by
  obtain ⟨hpy, hpyLength⟩ := hpy
  obtain ⟨hpxy, hpxyLength⟩ := hpxy
  obtain ⟨hi, hFirst, hLeft, hRight⟩ := hCase
  let i' := min i ky
  have hi' : i' ≤ py.length := by rw [hpyLength]; exact min_le_right _ _
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

/-- Transitive case in the `x`-then-`y` direction: from a program `px` for `x` and a program
`pyx` for `y` given `x`, every triple `t` dominating `(i, (2 * n - i, 3 * n - i))` for some
`i ≤ 2 * n` lies in `CommonInformationRegion V x y` once inflated by `logSlack C n`. -/
private lemma common_information_universal_lower_trans_yx_case
    (V : Map) (cTrans A cCond n kx kyxCond C : Nat) (x y : BitString)
    (px pyx : BitString)
    (hTrans : CommonInformationTransRule V cTrans)
    (hpx : ProducesOfLength V px [] x kx) (hpyx : ProducesOfLength V pyx x y kyxCond)
    (hxClose : NatCloseWithin kx (2 * n) (logSlack A n))
    (hkyxClose : NatCloseWithin kyxCond n (logSlack cCond n))
    (hYXTransError : logSlack A n + logSlack cCond n +
      logSlack cTrans (kx + kyxCond + 1) ≤ logSlack C n)
    (t : CommonInformationTriple) (i : Nat) (hCase : TransYXCase n t i) :
    commonInformationTripleInflate (logSlack C n) t ∈ CommonInformationRegion V x y := by
  obtain ⟨hpx, hpxLength⟩ := hpx
  obtain ⟨hpyx, hpyxLength⟩ := hpyx
  obtain ⟨hi, hFirst, hLeft, hRight⟩ := hCase
  let i' := min i kx
  have hi' : i' ≤ px.length := by rw [hpxLength]; exact min_le_right _ _
  have hMemYX := hTrans px pyx y x i' hpx hpyx hi'
  have hMem :
      commonInformationTripleInflate
          (logSlack cTrans (px.length + pyx.length + 1))
          (i', (px.length - i', px.length - i' + pyx.length)) ∈
        CommonInformationRegion V x y := by
    have hSwap := (commonInformationRegion_swap (V := V) (x := x) (y := y)).mp hMemYX
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

/-- The constructive universal lower inclusion for SUV Theorem 225.
Given any optimal conditional machine, the common information region of any pair
with the (2n, 2n, 3n) complexity profile contains the entire finite case cover
of the theoretical lower envelope, up to uniform logarithmic slack. -/
theorem common_information_universal_lower
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
  obtain ⟨cCond, hCondClose⟩ := common_information_conditional_values_close V hV A
  obtain ⟨cCombined, hCombined⟩ := commonInformationRegion_contains_combinedPlainPrefixProfile V hV
  obtain ⟨cAnchored, hAnchored⟩ :=
    commonInformationRegion_contains_anchoredConditionalPrefixProfile V hV
  obtain ⟨cTrans, hTrans⟩ := commonInformationRegion_contains_plainPrefixTransitiveProfile V hV
  let cWitness := cCombined + cAnchored + cTrans
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cWitness
      (4 + 2 * A + 2 * cCond) (2 * A + 2 * cCond + 1)
  let C := A + cCond + cFold
  refine ⟨C, ?_⟩
  intro n x y kx ky kxy hx hy hxy hxClose hyClose hxyClose
  obtain ⟨kxyCond, hkxyCond⟩ := exists_plainConditionalComplexityValue V hV x y
  obtain ⟨kyxCond, hkyxCond⟩ := exists_plainConditionalComplexityValue V hV y x
  obtain ⟨hkxyClose, hkyxClose⟩ :=
    hCondClose n x y kx ky kxy kxyCond kyxCond
      hx hy hxy hkxyCond hkyxCond hxClose hyClose hxyClose
  obtain ⟨px, hpx, hpxLength⟩ := hx.exists_program
  obtain ⟨py, hpy, hpyLength⟩ := hy.exists_program
  obtain ⟨pxy, hpxy, hpxyLength⟩ := hkxyCond.exists_program
  obtain ⟨pyx, hpyx, hpyxLength⟩ := hkyxCond.exists_program
  obtain ⟨hCombinedArgument, hXYArgument, hYXArgument⟩ :=
    logSlack_universal_lower_arg_le A cCond n kx ky kxyCond kyxCond
      hxClose hyClose hkxyClose hkyxClose
  have hcCombined : cCombined ≤ cWitness := by dsimp [cWitness]; omega
  have hcAnchored : cAnchored ≤ cWitness := by dsimp [cWitness]; omega
  have hcTrans : cTrans ≤ cWitness := by dsimp [cWitness]; omega
  have hCombinedSlack : logSlack cCombined (kx + ky + 1) ≤ logSlack cFold n :=
    logSlack_universal_lower_component_bound cCombined cCombined cAnchored cTrans cFold n A
      cCond (kx + ky + 1) hcCombined (hFold n) hCombinedArgument
  have hXYSlack : logSlack cAnchored (ky + kxyCond + 1) ≤ logSlack cFold n :=
    logSlack_universal_lower_component_bound cAnchored cCombined cAnchored cTrans cFold n A
      cCond (ky + kxyCond + 1) hcAnchored (hFold n) hXYArgument
  have hYXSlack : logSlack cAnchored (kx + kyxCond + 1) ≤ logSlack cFold n :=
    logSlack_universal_lower_component_bound cAnchored cCombined cAnchored cTrans cFold n A
      cCond (kx + kyxCond + 1) hcAnchored (hFold n) hYXArgument
  have hXYTransSlack : logSlack cTrans (ky + kxyCond + 1) ≤ logSlack cFold n :=
    logSlack_universal_lower_component_bound cTrans cCombined cAnchored cTrans cFold n A
      cCond (ky + kxyCond + 1) hcTrans (hFold n) hXYArgument
  have hYXTransSlack : logSlack cTrans (kx + kyxCond + 1) ≤ logSlack cFold n :=
    logSlack_universal_lower_component_bound cTrans cCombined cAnchored cTrans cFold n A
      cCond (kx + kyxCond + 1) hcTrans (hFold n) hYXArgument
  have hBudget : logSlack A n + logSlack cCond n + logSlack cFold n = logSlack C n := by
    dsimp [C, logSlack]; ring
  have hCombinedError := logSlack_universal_lower_error_le A cCond cFold C cCombined
    n (kx + ky + 1) hBudget hCombinedSlack
  have hXYAnchoredError := logSlack_universal_lower_error_le A cCond cFold C cAnchored
    n (ky + kxyCond + 1) hBudget hXYSlack
  have hYXAnchoredError := logSlack_universal_lower_error_le A cCond cFold C cAnchored
    n (kx + kyxCond + 1) hBudget hYXSlack
  have hXYTransError := logSlack_universal_lower_error_le A cCond cFold C cTrans
    n (ky + kxyCond + 1) hBudget hXYTransSlack
  have hYXTransError := logSlack_universal_lower_error_le A cCond cFold C cTrans
    n (kx + kyxCond + 1) hBudget hYXTransSlack
  intro t ht
  rcases commonInformationLowerEnvelope_prefix_case_cover ht with
    hCombinedCase | hAnchoredXY | hAnchoredYX | hTransXY | hTransYX
  · rcases hCombinedCase with ⟨i, j, hi, hj, hFirst, hLeft, hRight⟩
    exact common_information_universal_lower_combined_case V cCombined A cCond n kx ky C x y px py
      hCombined ⟨hpx, hpxLength⟩ ⟨hpy, hpyLength⟩ hxClose hyClose hCombinedError t i j
      ⟨hi, hj, hFirst, hLeft, hRight⟩
  · rcases hAnchoredXY with ⟨i, hi, hFirst, hLeft⟩
    exact common_information_universal_lower_anchored_xy_case V cAnchored A cCond n ky kxyCond C
      x y py pxy hAnchored ⟨hpy, hpyLength⟩ ⟨hpxy, hpxyLength⟩ hyClose hkxyClose
      hXYAnchoredError t i ⟨hi, hFirst, hLeft⟩
  · rcases hAnchoredYX with ⟨i, hi, hFirst, hRight⟩
    exact common_information_universal_lower_anchored_yx_case V cAnchored A cCond n kx kyxCond C
      x y px pyx hAnchored ⟨hpx, hpxLength⟩ ⟨hpyx, hpyxLength⟩ hxClose hkyxClose
      hYXAnchoredError t i ⟨hi, hFirst, hRight⟩
  · rcases hTransXY with ⟨i, hi, hFirst, hLeft, hRight⟩
    exact common_information_universal_lower_trans_xy_case V cTrans A cCond n ky kxyCond C x y py
      pxy hTrans ⟨hpy, hpyLength⟩ ⟨hpxy, hpxyLength⟩ hyClose hkxyClose hXYTransError t i
      ⟨hi, hFirst, hLeft, hRight⟩
  · rcases hTransYX with ⟨i, hi, hFirst, hLeft, hRight⟩
    exact common_information_universal_lower_trans_yx_case V cTrans A cCond n kx kyxCond C x y px
      pyx hTrans ⟨hpx, hpxLength⟩ ⟨hpyx, hpyxLength⟩ hxClose hkyxClose hYXTransError t i
      ⟨hi, hFirst, hLeft, hRight⟩

/-- The source's universal upper envelope with a uniform `O(log n)` error.
The value-level coding bounds initially contain logarithms of the triple
coordinates.  If a relevant coordinate sum is not already above its ideal
face, that sum is at most `3n`, so the logarithm folds back to `log n`. -/
theorem common_information_profile_upper
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
  obtain ⟨cLeft, hLeft⟩ := commonInformationRegion_left_profile_bound_values V hV
  obtain ⟨cRight, hRight⟩ := commonInformationRegion_right_profile_bound_values V hV
  obtain ⟨cPair, hPair⟩ := commonInformationRegion_pair_profile_bound_values V hV
  let cWitness := cLeft + cRight + cPair
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cWitness 3 1
  let C := A + cFold
  refine ⟨C, ?_⟩
  intro n x y kx ky kxy hx hy hxy hxClose hyClose hxyClose t ht
  have hLeftBound := hLeft hx ht
  have hRightBound := hRight hy ht
  have hPairBound := hPair hxy ht
  have hBudget : logSlack A n + logSlack cFold n = logSlack C n := by dsimp [C, logSlack]; ring
  change 2 * n < (t.1 + logSlack C n) + (t.2.1 + logSlack C n) ∧
      2 * n < (t.1 + logSlack C n) + (t.2.2 + logSlack C n) ∧
      3 * n < (t.1 + logSlack C n) + (t.2.1 + logSlack C n) + (t.2.2 + logSlack C n)
  constructor
  · by_cases hAlready : 2 * n < t.1 + t.2.1
    · omega
    · have hArgument : t.1 + t.2.1 + 1 ≤ 3 * n + 1 := by omega
      have hSlack : logSlack cLeft (t.1 + t.2.1 + 1) ≤ logSlack cFold n := by
        calc logSlack cLeft (t.1 + t.2.1 + 1)
          _ ≤ logSlack cWitness (t.1 + t.2.1 + 1) :=
            logSlack_mono_left (by dsimp [cWitness]; omega) _
          _ ≤ logSlack cWitness (3 * n + 1) := logSlack_mono_right cWitness hArgument
          _ ≤ logSlack cFold n := hFold n
      unfold NatCloseWithin at hxClose; omega
  constructor
  · by_cases hAlready : 2 * n < t.1 + t.2.2
    · omega
    · have hArgument : t.1 + t.2.2 + 1 ≤ 3 * n + 1 := by omega
      have hSlack : logSlack cRight (t.1 + t.2.2 + 1) ≤ logSlack cFold n := by
        calc logSlack cRight (t.1 + t.2.2 + 1)
          _ ≤ logSlack cWitness (t.1 + t.2.2 + 1) :=
            logSlack_mono_left (by dsimp [cWitness]; omega) _
          _ ≤ logSlack cWitness (3 * n + 1) := logSlack_mono_right cWitness hArgument
          _ ≤ logSlack cFold n := hFold n
      unfold NatCloseWithin at hyClose; omega
  · by_cases hAlready : 3 * n < t.1 + t.2.1 + t.2.2
    · omega
    · have hArgument : t.1 + t.2.1 + t.2.2 + 1 ≤ 3 * n + 1 := by omega
      have hSlack : logSlack cPair (t.1 + t.2.1 + t.2.2 + 1) ≤ logSlack cFold n := by
        calc logSlack cPair (t.1 + t.2.1 + t.2.2 + 1)
          _ ≤ logSlack cWitness (t.1 + t.2.1 + t.2.2 + 1) :=
            logSlack_mono_left (by dsimp [cWitness]; omega) _
          _ ≤ logSlack cWitness (3 * n + 1) := logSlack_mono_right cWitness hArgument
          _ ≤ logSlack cFold n := hFold n
      unfold NatCloseWithin at hxyClose; omega

/-- The Muchnik pair from Theorem 224 realizes the lower envelope of SUV
Theorem 225, in both containment directions and with one uniform logarithmic
coordinate error. -/
theorem common_information_lower_envelope_achieved
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
  obtain ⟨cFace, hFace⟩ := common_information_threeFace_containment V hV
  obtain ⟨cLower, hLower⟩ := common_information_universal_lower V hV cFace
  obtain ⟨cUpper, hUpper⟩ := common_information_profile_upper V hV cFace
  let C := cFace + cLower + cUpper
  refine ⟨C, fun n => ?_⟩
  obtain ⟨x, y, kx, ky, kxy, _hxLength, _hyLength,
    hx, hy, hxy, hxClose, hyClose, hxyClose, _hMutual, hFaceContainment⟩ :=
    hFace n
  have hcFace : cFace ≤ C := by dsimp [C]; omega
  have hcLower : cLower ≤ C := by dsimp [C]; omega
  have hcUpper : cUpper ≤ C := by dsimp [C]; omega
  have hFaceSlack : logSlack cFace n ≤ logSlack C n := logSlack_mono_left hcFace n
  have hLowerSlack : logSlack cLower n ≤ logSlack C n := logSlack_mono_left hcLower n
  have hUpperSlack : logSlack cUpper n ≤ logSlack C n := logSlack_mono_left hcUpper n
  refine ⟨x, y, kx, ky, kxy, hx, hy, hxy,
    hxClose.mono hFaceSlack, hyClose.mono hFaceSlack,
    hxyClose.mono hFaceSlack, ?_, ?_⟩
  · intro t ht
    have hMem := hLower n x y kx ky kxy hx hy hxy hxClose hyClose hxyClose t ht
    refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
    all_goals
      simp only [commonInformationTripleInflate]
      omega
  · intro t ht
    have hUpperContainment := hUpper n x y kx ky kxy hx hy hxy hxClose hyClose hxyClose t ht
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

/-- The length of the shared block read off from an overlap factor code. -/
def overlapFactorsLiteralSharedLength (q : BitString) : Nat :=
  decodeBits (decodeFirst (decodeSecond q))

/-- The concatenated body read off from an overlap factor code. -/
def overlapFactorsLiteralBody (q : BitString) : BitString :=
  decodeSecond (decodeSecond q)

/-- The left block length of an overlap factor code is computable. -/
theorem overlapFactorsLiteralLeftLength_computable :
    Computable overlapFactorsLiteralLeftLength :=
  decodeBits_computable.comp decodeFirst_computable

/-- The shared block length of an overlap factor code is computable. -/
theorem overlapFactorsLiteralSharedLength_computable :
    Computable overlapFactorsLiteralSharedLength :=
  decodeBits_computable.comp
    (decodeFirst_computable.comp decodeSecond_computable)

/-- The body of an overlap factor code is computable. -/
theorem overlapFactorsLiteralBody_computable :
    Computable overlapFactorsLiteralBody :=
  decodeSecond_computable.comp decodeSecond_computable

/-- The combined length of the left and shared blocks of an overlap factor code. -/
def overlapFactorsLiteralLeftSharedLength (q : BitString) : Nat :=
  overlapFactorsLiteralLeftLength q + overlapFactorsLiteralSharedLength q

/-- The combined left-and-shared length is computable. -/
theorem overlapFactorsLiteralLeftSharedLength_computable :
    Computable overlapFactorsLiteralLeftSharedLength :=
  Primrec.nat_add.to_comp.comp
    overlapFactorsLiteralLeftLength_computable
    overlapFactorsLiteralSharedLength_computable

/-- The first factor `left ++ shared` recovered from an overlap factor code. -/
def overlapFactorsLiteralFirst (q : BitString) : BitString :=
  (overlapFactorsLiteralBody q).take
    (overlapFactorsLiteralLeftSharedLength q)

/-- The first factor of an overlap factor code is computable. -/
theorem overlapFactorsLiteralFirst_computable :
    Computable overlapFactorsLiteralFirst :=
  Primrec.list_take.to_comp.comp
    overlapFactorsLiteralLeftSharedLength_computable
    overlapFactorsLiteralBody_computable

/-- The second factor `shared ++ right` recovered from an overlap factor code. -/
def overlapFactorsLiteralSecond (q : BitString) : BitString :=
  (overlapFactorsLiteralBody q).drop
    (overlapFactorsLiteralLeftLength q)

/-- The second factor of an overlap factor code is computable. -/
theorem overlapFactorsLiteralSecond_computable :
    Computable overlapFactorsLiteralSecond :=
  Primrec.list_drop.to_comp.comp
    overlapFactorsLiteralLeftLength_computable
    overlapFactorsLiteralBody_computable

/-- The pair of overlapping factors recovered from an overlap factor code. -/
def decodeOverlapFactorsLiteralCode (q : BitString) : BitString :=
  pairCode (overlapFactorsLiteralFirst q) (overlapFactorsLiteralSecond q)

/-- Decoding an overlap factor code is computable. -/
theorem decodeOverlapFactorsLiteralCode_computable :
    Computable decodeOverlapFactorsLiteralCode := by
  have hPair : Computable₂ (fun a b : BitString => pairCode a b) := pairCode_computable
  exact hPair.comp overlapFactorsLiteralFirst_computable
    overlapFactorsLiteralSecond_computable

/-- Decoding the code of the blocks `left`, `shared`, `right` returns the pair of overlapping
factors `left ++ shared` and `shared ++ right`. -/
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

/-- The overlap factor code costs only a logarithmic overhead over the total block length. -/
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
  let D : Map := fun pr => Part.some (decodeOverlapFactorsLiteralCode pr.1)
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
  have hSlack := logSlack_add_nat_le 6 cD (left.length + shared.length + right.length + 1)
  exact hBound.trans (by
    rw [← Nat.cast_add]
    exact_mod_cast (Nat.add_le_add_right hLength cD |>.trans (by
      dsimp [C]
      omega)))

/- Helpers for recovering three literal blocks from two overlapping factors. -/
private def overlapSharedLength (q : BitString) : Nat :=
  decodeBits (decodeFirst q)

private def overlapPairProgram (q : BitString) : BitString :=
  decodeSecond q

private def overlapDecodedSecond
    (q : (BitString × BitString) × BitString) : BitString :=
  decodeSecond q.2

private def overlapSharedLengthAt
    (q : (BitString × BitString) × BitString) : Nat :=
  overlapSharedLength q.1.1

private def overlapRightSuffix
    (q : (BitString × BitString) × BitString) : BitString :=
  (overlapDecodedSecond q).drop (overlapSharedLengthAt q)

private def overlapThreeBlocksOutput
    (q : (BitString × BitString) × BitString) : BitString :=
  decodeFirst q.2 ++ overlapRightSuffix q

private def overlapThreeBlocksDecompressor (V : Map) : Map := fun pr =>
  (V (overlapPairProgram pr.1, [])).map fun w =>
    overlapThreeBlocksOutput (pr, w)

private theorem overlapSharedLength_computable :
    Computable overlapSharedLength :=
  decodeBits_computable.comp decodeFirst_computable

private theorem overlapPairProgram_computable :
    Computable overlapPairProgram :=
  decodeSecond_computable

private theorem overlapDecodedSecond_computable :
    Computable overlapDecodedSecond :=
  decodeSecond_computable.comp Computable.snd

private theorem overlapSharedLengthAt_computable :
    Computable overlapSharedLengthAt :=
  overlapSharedLength_computable.comp
    (Computable.fst.comp Computable.fst)

private theorem overlapThreeBlocksRun_partrec
    (V : Map) (hV : isDecompressor V) :
    Partrec (fun pr : BitString × BitString =>
      V (overlapPairProgram pr.1, [])) :=
  Partrec.comp hV
    ((overlapPairProgram_computable.comp Computable.fst).pair
      (Computable.const []))

private theorem overlapRightSuffix_computable :
    Computable overlapRightSuffix := by
  change Computable
    (fun q : (BitString × BitString) × BitString =>
      (overlapDecodedSecond q).drop (overlapSharedLengthAt q))
  exact (Primrec.list_drop (α := Bool)).to_comp.comp
    overlapSharedLengthAt_computable
    overlapDecodedSecond_computable

private theorem overlapThreeBlocksOutput_computable :
    Computable overlapThreeBlocksOutput := by
  change Computable
    (fun q : (BitString × BitString) × BitString =>
      decodeFirst q.2 ++ overlapRightSuffix q)
  exact (Computable.list_append (α := Bool)).comp
    (decodeFirst_computable.comp Computable.snd)
    overlapRightSuffix_computable

private theorem overlapThreeBlocksDecompressor_isDecompressor
    (V : Map) (hV : isOptimalConditional V) :
    isDecompressor (overlapThreeBlocksDecompressor V) :=
  Partrec.map (overlapThreeBlocksRun_partrec V hV.1)
    overlapThreeBlocksOutput_computable

private theorem overlapThreeBlocksDecompressor_produces
    (V : Map) (left shared right p : BitString)
    (hp : produces V p []
      (pairCode (left ++ shared) (shared ++ right))) :
    produces (overlapThreeBlocksDecompressor V)
      (pairCode (Nat.bits shared.length) p) []
      (left ++ shared ++ right) := by
  change left ++ shared ++ right ∈
    (V (overlapPairProgram (pairCode (Nat.bits shared.length) p), [])).map fun w =>
      overlapThreeBlocksOutput
        ((pairCode (Nat.bits shared.length) p, []), w)
  simp only [overlapPairProgram, overlapThreeBlocksOutput, overlapRightSuffix,
    overlapDecodedSecond, overlapSharedLengthAt, overlapSharedLength,
    decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
  have h := Part.mem_map
    (fun w => decodeFirst w ++ (decodeSecond w).drop shared.length) hp
  simpa [decodeFirst_pairCode, decodeSecond_pairCode, List.drop_left] using h

/-- Conversely, the three literal blocks are recoverable from their two
overlapping factors with logarithmic metadata specifying the shared length. -/
theorem plainK_threeBlocks_le_overlapPair
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ left shared right : BitString,
      plainK V (left ++ shared ++ right) ≤
        pairPlainK V (left ++ shared) (shared ++ right) +
          (logSlack c (left.length + shared.length + right.length + 1) : ENat) := by
  obtain ⟨cD, hcD⟩ := hV.2 (overlapThreeBlocksDecompressor V)
    (overlapThreeBlocksDecompressor_isDecompressor V hV)
  let C := cD + 3
  refine ⟨C, fun left shared right => ?_⟩
  obtain ⟨kPair, hkPair⟩ :=
    exists_plainComplexityValue V hV
      (pairCode (left ++ shared) (shared ++ right))
  obtain ⟨p, hp, hpLength⟩ := hkPair.exists_program
  let prog := pairCode (Nat.bits shared.length) p
  have hProd : produces (overlapThreeBlocksDecompressor V) prog []
      (left ++ shared ++ right) := by
    exact overlapThreeBlocksDecompressor_produces V left shared right p hp
  have hBound : plainK V (left ++ shared ++ right) ≤ (prog.length : ENat) + (cD : ENat) := by
    calc plainK V (left ++ shared ++ right)
      _ ≤ plainK (overlapThreeBlocksDecompressor V) (left ++ shared ++ right) + (cD : ENat) :=
        hcD _ []
      _ ≤ (prog.length : ENat) + (cD : ENat) := by gcongr; exact sInf_le ⟨prog, hProd, rfl⟩
  let total := left.length + shared.length + right.length
  have hBitsShared :
      (Nat.bits shared.length).length ≤ (Nat.bits (total + 1)).length :=
    length_natBits_mono (by dsimp [total]; omega)
  have hProgLength : prog.length = 2 * (Nat.bits shared.length).length + 1 + kPair := by
    simp only [prog, length_pairCode, hpLength]; omega
  have hLength : prog.length + cD ≤ kPair + logSlack C (total + 1) := by
    rw [hProgLength]; dsimp [C, logSlack]; nlinarith [Nat.zero_le (Nat.bits (total + 1)).length]
  calc plainK V (left ++ shared ++ right)
    _ ≤ (prog.length : ENat) + (cD : ENat) := hBound
    _ = ((prog.length + cD : Nat) : ENat) := by push_cast; ring
    _ ≤ ((kPair + logSlack C (total + 1) : Nat) : ENat) := by exact_mod_cast hLength
    _ = pairPlainK V (left ++ shared) (shared ++ right) +
          (logSlack C (left.length + shared.length + right.length + 1) : ENat) := by
      rw [pairPlainK, hkPair]; dsimp [total]; push_cast; ring

end Kolmogorov
