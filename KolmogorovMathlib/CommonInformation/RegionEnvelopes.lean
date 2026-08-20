import KolmogorovMathlib.CommonInformation.CommonWitnessCoding
import KolmogorovMathlib.CommonInformation.Interfaces
import KolmogorovMathlib.CommonInformation.WorstCaseRegion

namespace Kolmogorov

open ENat

def commonInformationTripleInflate
    (c : Nat) (t : CommonInformationTriple) : CommonInformationTriple :=
  (t.1 + c, (t.2.1 + c, t.2.2 + c))

theorem commonInformationTripleInflate_mono
    {c1 c2 : Nat} (h : c1 ≤ c2) (t : CommonInformationTriple) :
    t.1 + c1 ≤ t.1 + c2 ∧ t.2.1 + c1 ≤ t.2.1 + c2 ∧ t.2.2 + c1 ≤ t.2.2 + c2 := by
  omega

def CommonInformationUpperEnvelope (kx ky kxy : Nat) : Set CommonInformationTriple :=
  { t | kx < t.1 + t.2.1 ∧ ky < t.1 + t.2.2 ∧ kxy < t.1 + t.2.1 + t.2.2 }

/-- The union of the three obstruction half-spaces from SUV Theorem 224.
The inequalities are strict because `CommonInformationRegion` itself uses
strict complexity thresholds. -/
def CommonInformationThreeFaceEnvelope (n : Nat) : Set CommonInformationTriple :=
  { t |
    3 * n < t.1 + t.2.1 ∨
    3 * n < t.1 + t.2.2 ∨
    4 * n < t.1 + t.2.1 + t.2.2 }

/-- The exact lower polyhedral envelope from SUV Theorem 225: the profile
upper envelope intersected with the three obstruction faces. -/
def CommonInformationLowerEnvelope (n : Nat) : Set CommonInformationTriple :=
  CommonInformationUpperEnvelope (2 * n) (2 * n) (3 * n) ∩
    CommonInformationThreeFaceEnvelope n

theorem commonInformationUpperEnvelope_upward_closed (kx ky kxy : Nat)
    {s t : CommonInformationTriple} :
    s ∈ CommonInformationUpperEnvelope kx ky kxy →
    s.1 ≤ t.1 → s.2.1 ≤ t.2.1 → s.2.2 ≤ t.2.2 →
    t ∈ CommonInformationUpperEnvelope kx ky kxy := by
  intro hs hFirst hLeft hRight
  change
    kx < s.1 + s.2.1 ∧ ky < s.1 + s.2.2 ∧
      kxy < s.1 + s.2.1 + s.2.2 at hs
  change
    kx < t.1 + t.2.1 ∧ ky < t.1 + t.2.2 ∧
      kxy < t.1 + t.2.1 + t.2.2
  omega

theorem commonInformationThreeFaceEnvelope_upward_closed (n : Nat)
    {s t : CommonInformationTriple} :
    s ∈ CommonInformationThreeFaceEnvelope n →
    s.1 ≤ t.1 → s.2.1 ≤ t.2.1 → s.2.2 ≤ t.2.2 →
    t ∈ CommonInformationThreeFaceEnvelope n := by
  intro hs hFirst hLeft hRight
  change
    3 * n < s.1 + s.2.1 ∨ 3 * n < s.1 + s.2.2 ∨
      4 * n < s.1 + s.2.1 + s.2.2 at hs
  change
    3 * n < t.1 + t.2.1 ∨ 3 * n < t.1 + t.2.2 ∨
      4 * n < t.1 + t.2.1 + t.2.2
  rcases hs with hs | hs | hs
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

theorem commonInformationLowerEnvelope_upward_closed (n : Nat)
    {s t : CommonInformationTriple} :
    s ∈ CommonInformationLowerEnvelope n →
    s.1 ≤ t.1 → s.2.1 ≤ t.2.1 → s.2.2 ≤ t.2.2 →
    t ∈ CommonInformationLowerEnvelope n := by
  rintro ⟨hUpper, hThreeFace⟩ hFirst hLeft hRight
  exact ⟨
    commonInformationUpperEnvelope_upward_closed
      (2 * n) (2 * n) (3 * n) hUpper hFirst hLeft hRight,
    commonInformationThreeFaceEnvelope_upward_closed
      n hThreeFace hFirst hLeft hRight⟩

theorem commonInformationRegion_subset_upperEnvelope
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ {x y : BitString} {kx ky kxy : Nat},
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V y ky →
      HasPlainComplexityValue V (pairCode x y) kxy →
      ∀ t ∈ CommonInformationRegion V x y,
        commonInformationTripleInflate (logSlack c (t.1 + t.2.1 + t.2.2 + 1)) t ∈
          CommonInformationUpperEnvelope kx ky kxy := by
  obtain ⟨cLeft, hLeft⟩ :=
    commonInformationRegion_left_profile_bound_values V hV
  obtain ⟨cRight, hRight⟩ :=
    commonInformationRegion_right_profile_bound_values V hV
  obtain ⟨cPair, hPair⟩ :=
    commonInformationRegion_pair_profile_bound_values V hV
  let c := cLeft + cRight + cPair
  refine ⟨c, ?_⟩
  intro x y kx ky kxy hx hy hxy t ht
  have hLeftBound := hLeft hx ht
  have hRightBound := hRight hy ht
  have hPairBound := hPair hxy ht
  let d := logSlack c (t.1 + t.2.1 + t.2.2 + 1)
  have hcLeft : cLeft ≤ c := by
    dsimp only [c]
    omega
  have hcRight : cRight ≤ c := by
    dsimp only [c]
    omega
  have hcPair : cPair ≤ c := by
    dsimp only [c]
    omega
  have hLeftSlack :
      logSlack cLeft (t.1 + t.2.1 + 1) ≤ d := by
    have hConstant :
        logSlack cLeft (t.1 + t.2.1 + 1) ≤
          logSlack c (t.1 + t.2.1 + 1) :=
      logSlack_mono_left hcLeft _
    have hArgument :
        logSlack c (t.1 + t.2.1 + 1) ≤ d :=
      logSlack_mono_right c (by omega)
    exact hConstant.trans hArgument
  have hRightSlack :
      logSlack cRight (t.1 + t.2.2 + 1) ≤ d := by
    have hConstant :
        logSlack cRight (t.1 + t.2.2 + 1) ≤
          logSlack c (t.1 + t.2.2 + 1) :=
      logSlack_mono_left hcRight _
    have hArgument :
        logSlack c (t.1 + t.2.2 + 1) ≤ d :=
      logSlack_mono_right c (by omega)
    exact hConstant.trans hArgument
  have hPairSlack :
      logSlack cPair (t.1 + t.2.1 + t.2.2 + 1) ≤ d :=
    logSlack_mono_left hcPair _
  change
    kx < (t.1 + d) + (t.2.1 + d) ∧
      ky < (t.1 + d) + (t.2.2 + d) ∧
      kxy < (t.1 + d) + (t.2.1 + d) + (t.2.2 + d)
  refine ⟨hLeftBound.trans_le ?_, hRightBound.trans_le ?_,
    hPairBound.trans_le ?_⟩ <;> omega

/-- The region of the pair supplied by Theorem 224 lies in the union of its
three obstruction faces after the same uniform logarithmic inflation. -/
theorem theorem_224_common_information_threeFace_containment
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ n : Nat,
      ∃ x y : BitString, ∃ kx ky kxy : Nat,
        x.length = 2 * n + 2 ∧
        y.length = 2 * n + 2 ∧
        HasPlainComplexityValue V x kx ∧
        HasPlainComplexityValue V y ky ∧
        HasPlainComplexityValue V (pairCode x y) kxy ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) ∧
        MutualInformationWithin V x y n (logSlack C n) ∧
        ∀ t ∈ CommonInformationRegion V x y,
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationThreeFaceEnvelope n := by
  obtain ⟨C, hC⟩ :=
    theorem_224_muchnik_worst_case_region V hV
  refine ⟨C, fun n => ?_⟩
  obtain ⟨x, y, kx, ky, kxy, hxLength, hyLength, hx, hy, hxy,
    hxClose, hyClose, hxyClose, hMutual, hObstruction⟩ := hC n
  refine ⟨x, y, kx, ky, kxy, hxLength, hyLength, hx, hy, hxy,
    hxClose, hyClose, hxyClose, hMutual, ?_⟩
  intro t ht
  rcases ht with ⟨z, hz, hxz, hyz⟩
  obtain ⟨kz, hkz⟩ := exists_plainComplexityValue V hV z
  obtain ⟨kxz, hkxz⟩ :=
    exists_plainConditionalComplexityValue V hV x z
  obtain ⟨kyz, hkyz⟩ :=
    exists_plainConditionalComplexityValue V hV y z
  have hzNat : kz < t.1 := by
    rw [hkz] at hz
    exact_mod_cast hz
  have hxzNat : kxz < t.2.1 := by
    rw [hkxz] at hxz
    exact_mod_cast hxz
  have hyzNat : kyz < t.2.2 := by
    rw [hkyz] at hyz
    exact_mod_cast hyz
  have hFaces := hObstruction z
  rw [hkz, hkxz, hkyz] at hFaces
  change
    3 * n <
        (t.1 + logSlack C n) + (t.2.1 + logSlack C n) ∨
      3 * n <
        (t.1 + logSlack C n) + (t.2.2 + logSlack C n) ∨
      4 * n <
        (t.1 + logSlack C n) + (t.2.1 + logSlack C n) +
          (t.2.2 + logSlack C n)
  rcases hFaces with hLeft | hRight | hPair
  · left
    have hLeftNat :
        3 * n ≤ kz + kxz + logSlack C n := by
      exact_mod_cast hLeft
    omega
  · right
    left
    have hRightNat :
        3 * n ≤ kz + kyz + logSlack C n := by
      exact_mod_cast hRight
    omega
  · right
    right
    have hPairNat :
        4 * n ≤ kz + kxz + kyz + logSlack C n := by
      exact_mod_cast hPair
    omega

theorem theorem_225_common_information_universal_upper
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ {x y : BitString} {kx ky kxy : Nat},
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V y ky →
      HasPlainComplexityValue V (pairCode x y) kxy →
      ∀ t ∈ CommonInformationRegion V x y,
        commonInformationTripleInflate (logSlack c (t.1 + t.2.1 + t.2.2 + 1)) t ∈
          CommonInformationUpperEnvelope kx ky kxy := by
  exact commonInformationRegion_subset_upperEnvelope V hV

theorem commonInformationTripleInflate_add
    (c₁ c₂ : Nat) (t : CommonInformationTriple) :
    commonInformationTripleInflate c₁
      (commonInformationTripleInflate c₂ t) =
    commonInformationTripleInflate (c₁ + c₂) t := by
  rcases t with ⟨a, b, c⟩
  simp [commonInformationTripleInflate, Nat.add_comm, Nat.add_left_comm]

theorem theorem_225_conditional_values_close
    (V : Map) (hV : isOptimalConditional V) :
    ∀ A, ∃ C, ∀ n x y kx ky kxy kxyCond kyxCond,
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V y ky →
      HasPlainComplexityValue V (pairCode x y) kxy →
      HasPlainConditionalComplexityValue V x y kxyCond →
      HasPlainConditionalComplexityValue V y x kyxCond →
      NatCloseWithin kx (2 * n) (logSlack A n) →
      NatCloseWithin ky (2 * n) (logSlack A n) →
      NatCloseWithin kxy (3 * n) (logSlack A n) →
      NatCloseWithin kxyCond n (logSlack C n) ∧
      NatCloseWithin kyxCond n (logSlack C n) := by
  intro A
  obtain ⟨cSym, hSym⟩ :=
    pairPlainK_symmetryOfInformation_values V hV
  obtain ⟨cSwap, hSwap⟩ := pairPlainK_swap_le V hV
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cSym (3 + A) (A + cSwap + 1)
  let C := 2 * A + cFold + cSwap
  refine ⟨C, ?_⟩
  intro n x y kx ky kxy kxyCond kyxCond
    hx hy hxy hxyCond hyxCond hxClose hyClose hxyClose
  obtain ⟨kSwap, hkSwap⟩ :=
    exists_plainComplexityValue V hV (pairCode y x)
  have hSwapForward : kSwap ≤ kxy + cSwap := by
    have h := hSwap x y
    rw [pairPlainK, pairPlainK, hkSwap, hxy] at h
    exact_mod_cast h
  have hSwapReverse : kxy ≤ kSwap + cSwap := by
    have h := hSwap y x
    rw [pairPlainK, pairPlainK, hxy, hkSwap] at h
    exact_mod_cast h
  have hBits : (Nat.bits n).length ≤ n :=
    length_natBits_le n
  let d := logSlack A n
  have hdLinear : d ≤ A * n + A := by
    dsimp only [d]
    unfold logSlack
    nlinarith [Nat.mul_le_mul_left A hBits]
  have hkxyLinearTight :
      kxy + 1 ≤ (3 + A) * n + (A + 1) := by
    unfold NatCloseWithin at hxyClose
    simp only [Nat.add_mul]
    omega
  have hkxyLinear :
      kxy + 1 ≤ (3 + A) * n + (A + cSwap + 1) := by
    simp only [Nat.add_mul] at hkxyLinearTight ⊢
    omega
  have hkSwapLinear :
      kSwap + 1 ≤ (3 + A) * n + (A + cSwap + 1) := by
    simp only [Nat.add_mul] at hkxyLinearTight ⊢
    omega
  have hKxyLog :
      logSlack cSym (kxy + 1) ≤ logSlack cFold n := by
    exact (logSlack_mono_right cSym hkxyLinear).trans (hFold n)
  have hKSwapLog :
      logSlack cSym (kSwap + 1) ≤ logSlack cFold n := by
    exact (logSlack_mono_right cSym hkSwapLinear).trans (hFold n)
  have hBudget :
      2 * d + cSwap + logSlack cFold n ≤ logSlack C n := by
    dsimp only [d, C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits n).length]
  have hOriginal :=
    hSym x y kx kyxCond kxy hx hyxCond hxy
  have hSwapped :=
    hSym y x ky kxyCond kSwap hy hxyCond hkSwap
  unfold NatCloseWithin at hxClose hyClose hxyClose ⊢
  constructor
  · constructor <;> omega
  · constructor <;> omega

theorem commonInformationTripleInflate_mem_lowerEnvelope
    {n dUpper dFace D : Nat} {t : CommonInformationTriple}
    (hUpper :
      commonInformationTripleInflate dUpper t ∈
        CommonInformationUpperEnvelope (2 * n) (2 * n) (3 * n))
    (hFace :
      commonInformationTripleInflate dFace t ∈
        CommonInformationThreeFaceEnvelope n)
    (hu : dUpper ≤ D) (hf : dFace ≤ D) :
    commonInformationTripleInflate D t ∈
      CommonInformationLowerEnvelope n := by
  refine ⟨
    commonInformationUpperEnvelope_upward_closed
      (2 * n) (2 * n) (3 * n) hUpper ?_ ?_ ?_,
    commonInformationThreeFaceEnvelope_upward_closed
      n hFace ?_ ?_ ?_⟩
  all_goals
    simp only [commonInformationTripleInflate]
    omega

/-- Shortest-description prefix leaf for SUV Theorem 225.
Supplying the missing suffix of a plain program reconstructs its output from
the visible prefix, with only logarithmic parsing overhead. -/
theorem condK_output_given_plainProgramPrefix_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ p x : BitString, ∀ i : Nat,
      produces V p [] x →
      condK V x (p.take i) ≤
        (((p.length - i +
          logSlack c (p.length + 1)) : Nat) : ENat) := by
  let D : Map := fun input =>
    V (input.2 ++ input.1, [])
  have hD : isDecompressor D :=
    Partrec.comp hV.1
      (Computable.pair
        (Computable.list_append.comp Computable.snd Computable.fst)
        (Computable.const []))
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c, fun p x i hp => ?_⟩
  have hProduced :
      produces D (p.drop i) (p.take i) x := by
    change x ∈ V (p.take i ++ p.drop i, [])
    simpa using hp
  have hFixed : c ≤ logSlack c (p.length + 1) := by
    unfold logSlack
    omega
  calc
    condK V x (p.take i) ≤
        condK D x (p.take i) + (c : ENat) :=
      hc x (p.take i)
    _ ≤ ((p.drop i).length : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨p.drop i, hProduced, rfl⟩
    _ = (((p.length - i + c) : Nat) : ENat) := by
      simp only [List.length_drop, Nat.cast_add]
    _ ≤ (((p.length - i +
          logSlack c (p.length + 1)) : Nat) : ENat) := by
      exact_mod_cast Nat.add_le_add_left hFixed (p.length - i)

/-- Two-description line leaf for SUV Theorem 225.
Raw prefixes of shortest descriptions may be concatenated once: the missing
suffix of each program recovers its corresponding output, and the boundary
between the two visible prefixes costs only logarithmic advice. -/
theorem condK_outputs_given_combined_plainProgramPrefixes_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ p q x y : BitString, ∀ i j : Nat,
      produces V p [] x →
      produces V q [] y →
      i ≤ p.length →
      j ≤ q.length →
      let z := p.take i ++ q.take j
      condK V x z ≤
          (((p.length - i +
            logSlack c (p.length + q.length + 1)) : Nat) : ENat) ∧
        condK V y z ≤
          (((q.length - j +
            logSlack c (p.length + q.length + 1)) : Nat) : ENat) := by
  let Dx : Map := fun input =>
    V (input.2.take (bitsToNat (decodeFirst input.1)) ++
      decodeSecond input.1, [])
  have hDx : isDecompressor Dx := by
    have h_i : Computable (fun input : BitString × BitString =>
        bitsToNat (decodeFirst input.1)) :=
      bitsToNat_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst)
    have h_take : Computable (fun input : BitString × BitString =>
        input.2.take (bitsToNat (decodeFirst input.1))) :=
      primrec_list_take.to_comp.comp Computable.snd h_i
    have h_sec : Computable (fun input : BitString × BitString =>
        decodeSecond input.1) :=
      decodeSecond_computable.comp Computable.fst
    have h_app : Computable (fun input : BitString × BitString =>
        input.2.take (bitsToNat (decodeFirst input.1)) ++
          decodeSecond input.1) :=
      Computable.list_append.comp h_take h_sec
    exact Partrec.comp hV.1 (Computable.pair h_app (Computable.const []))
  obtain ⟨cx, hcx⟩ := hV.2 Dx hDx
  let Dy : Map := fun input =>
    V (input.2.drop (bitsToNat (decodeFirst input.1)) ++
      decodeSecond input.1, [])
  have hDy : isDecompressor Dy := by
    have h_i : Computable (fun input : BitString × BitString =>
        bitsToNat (decodeFirst input.1)) :=
      bitsToNat_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst)
    have h_drop : Computable (fun input : BitString × BitString =>
        input.2.drop (bitsToNat (decodeFirst input.1))) :=
      primrec_list_drop.to_comp.comp Computable.snd h_i
    have h_sec : Computable (fun input : BitString × BitString =>
        decodeSecond input.1) :=
      decodeSecond_computable.comp Computable.fst
    have h_app : Computable (fun input : BitString × BitString =>
        input.2.drop (bitsToNat (decodeFirst input.1)) ++
          decodeSecond input.1) :=
      Computable.list_append.comp h_drop h_sec
    exact Partrec.comp hV.1 (Computable.pair h_app (Computable.const []))
  obtain ⟨cy, hcy⟩ := hV.2 Dy hDy
  let c := max (max cx cy) 3
  use c
  intro p q x y i j hpx hqy hip hjq z
  have h_px : produces Dx (pairCode (Nat.bits i) (p.drop i)) z x := by
    change x ∈ V
      (z.take (bitsToNat (decodeFirst (pairCode (Nat.bits i) (p.drop i)))) ++
        decodeSecond (pairCode (Nat.bits i) (p.drop i)), [])
    rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    have h_take : z.take i = p.take i := by
      dsimp only [z]
      have hlen : (p.take i).length = i := by rw [List.length_take]; omega
      rw [List.take_append_of_le_length hlen.symm.le, List.take_take, Nat.min_self]
    rw [h_take, List.take_append_drop]
    exact hpx
  have h_qy : produces Dy (pairCode (Nat.bits i) (q.drop j)) z y := by
    change y ∈ V
      (z.drop (bitsToNat (decodeFirst (pairCode (Nat.bits i) (q.drop j)))) ++
        decodeSecond (pairCode (Nat.bits i) (q.drop j)), [])
    rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    have h_drop : z.drop i = q.take j := by
      dsimp only [z]
      have hlen : (p.take i).length = i := by rw [List.length_take]; omega
      rw [List.drop_append_of_le_length hlen.symm.le,
        List.drop_eq_nil_of_le hlen.le, List.nil_append]
    rw [h_drop, List.take_append_drop]
    exact hqy
  have hx_eval := hcx x z
  have hy_eval := hcy y z
  have h_len_x :
      (pairCode (Nat.bits i) (p.drop i)).length =
        2 * (Nat.bits i).length + 1 + p.length - i := by
    rw [length_pairCode, List.length_drop]
    omega
  have h_len_y :
      (pairCode (Nat.bits i) (q.drop j)).length =
        2 * (Nat.bits i).length + 1 + q.length - j := by
    rw [length_pairCode, List.length_drop]
    omega
  have hcx_le : cx ≤ c := by dsimp [c]; omega
  have hcy_le : cy ≤ c := by dsimp [c]; omega
  have hc3 : 3 ≤ c := by dsimp [c]; omega
  have h_A_ge_1 : 1 ≤ (Nat.bits (p.length + q.length + 1)).length := by
    have : 1 ≤ p.length + q.length + 1 := by omega
    have h := length_natBits_mono this
    exact h
  constructor
  · calc
      condK V x z ≤ condK Dx x z + (cx : ENat) := hx_eval
      _ ≤ ((pairCode (Nat.bits i) (p.drop i)).length : ENat) + (cx : ENat) := by
        gcongr
        exact sInf_le ⟨_, h_px, rfl⟩
      _ = (((pairCode (Nat.bits i) (p.drop i)).length + cx : Nat) : ENat) := by
        push_cast
        rfl
      _ ≤ (((p.length - i +
          logSlack c (p.length + q.length + 1)) : Nat) : ENat) := by
        norm_cast
        have : (Nat.bits i).length ≤
            (Nat.bits (p.length + q.length + 1)).length := by
          apply length_natBits_mono
          omega
        rw [h_len_x]
        change 2 * (Nat.bits i).length + 1 + p.length - i + cx ≤
          p.length - i +
            (c * (Nat.bits (p.length + q.length + 1)).length + c)
        have h_bound : 2 * (Nat.bits i).length + 1 + cx ≤
            c * (Nat.bits (p.length + q.length + 1)).length + c := by
          nlinarith
        omega
  · calc
      condK V y z ≤ condK Dy y z + (cy : ENat) := hy_eval
      _ ≤ ((pairCode (Nat.bits i) (q.drop j)).length : ENat) + (cy : ENat) := by
        gcongr
        exact sInf_le ⟨_, h_qy, rfl⟩
      _ = (((pairCode (Nat.bits i) (q.drop j)).length + cy : Nat) : ENat) := by
        push_cast
        rfl
      _ ≤ (((q.length - j +
          logSlack c (p.length + q.length + 1)) : Nat) : ENat) := by
        norm_cast
        have : (Nat.bits i).length ≤
            (Nat.bits (p.length + q.length + 1)).length := by
          apply length_natBits_mono
          omega
        rw [h_len_y]
        change 2 * (Nat.bits i).length + 1 + q.length - j + cy ≤
          q.length - j +
            (c * (Nat.bits (p.length + q.length + 1)).length + c)
        have h_bound : 2 * (Nat.bits i).length + 1 + cy ≤
            c * (Nat.bits (p.length + q.length + 1)).length + c := by
          nlinarith
        omega

/-- Anchored conditional-prefix leaf for SUV Theorem 225.
Concatenating a full plain description of `y` with a prefix of a conditional
description of `x` given `y` makes `y` logarithmically simple and leaves only
the missing conditional suffix needed for `x`. -/
theorem condK_outputs_given_plain_and_conditionalProgramPrefix_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ p q x y : BitString, ∀ i : Nat,
      produces V p [] y →
      produces V q y x →
      i ≤ q.length →
      let z := p ++ q.take i
      condK V y z ≤
          (logSlack c (p.length + q.length + 1) : ENat) ∧
        condK V x z ≤
          (((q.length - i +
            logSlack c (p.length + q.length + 1)) : Nat) : ENat) := by
  let Dx : Map := fun input =>
    (V (input.2.take (bitsToNat (decodeFirst input.1)), [])).bind
      (fun y => V
        (input.2.drop (bitsToNat (decodeFirst input.1)) ++
          decodeSecond input.1, y))
  have hDx : isDecompressor Dx := by
    have h_i : Computable (fun input : BitString × BitString =>
        bitsToNat (decodeFirst input.1)) :=
      bitsToNat_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst)
    have h_take : Computable (fun input : BitString × BitString =>
        input.2.take (bitsToNat (decodeFirst input.1))) :=
      primrec_list_take.to_comp.comp Computable.snd h_i
    have h_V1 : Partrec (fun input : BitString × BitString =>
        V (input.2.take (bitsToNat (decodeFirst input.1)), [])) :=
      Partrec.comp hV.1 (Computable.pair h_take (Computable.const []))
    have h_drop : Computable (fun input : BitString × BitString =>
        input.2.drop (bitsToNat (decodeFirst input.1))) :=
      primrec_list_drop.to_comp.comp Computable.snd h_i
    have h_sec : Computable (fun input : BitString × BitString =>
        decodeSecond input.1) :=
      decodeSecond_computable.comp Computable.fst
    have h_app : Computable (fun input : BitString × BitString =>
        input.2.drop (bitsToNat (decodeFirst input.1)) ++
          decodeSecond input.1) :=
      Computable.list_append.comp h_drop h_sec
    have h_V2 : Partrec₂
        (fun (input : BitString × BitString) (y : BitString) =>
          V (input.2.drop (bitsToNat (decodeFirst input.1)) ++
            decodeSecond input.1, y)) := by
      have h_app2 : Computable
          (fun (p : (BitString × BitString) × BitString) =>
            p.1.2.drop (bitsToNat (decodeFirst p.1.1)) ++
              decodeSecond p.1.1) :=
        h_app.comp Computable.fst
      exact Partrec.comp hV.1 (Computable.pair h_app2 Computable.snd)
    exact Partrec.bind h_V1 h_V2
  obtain ⟨cx, hcx⟩ := hV.2 Dx hDx
  let Dy : Map := fun input =>
    V (input.2.take (bitsToNat (decodeFirst input.1)), [])
  have hDy : isDecompressor Dy := by
    have h_i : Computable (fun input : BitString × BitString =>
        bitsToNat (decodeFirst input.1)) :=
      bitsToNat_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst)
    have h_take : Computable (fun input : BitString × BitString =>
        input.2.take (bitsToNat (decodeFirst input.1))) :=
      primrec_list_take.to_comp.comp Computable.snd h_i
    exact Partrec.comp hV.1 (Computable.pair h_take (Computable.const []))
  obtain ⟨cy, hcy⟩ := hV.2 Dy hDy
  let c := max (max cx cy) 3
  use c
  intro p q x y i hpy hqyx hiq z
  have h_px : produces Dx (pairCode (Nat.bits p.length) (q.drop i)) z x := by
    change x ∈
      (V (z.take (bitsToNat
        (decodeFirst (pairCode (Nat.bits p.length) (q.drop i)))), [])).bind
        (fun y => V
          (z.drop (bitsToNat
              (decodeFirst (pairCode (Nat.bits p.length) (q.drop i)))) ++
            decodeSecond (pairCode (Nat.bits p.length) (q.drop i)), y))
    rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    have h_take : z.take p.length = p := by
      dsimp only [z]
      rw [List.take_left]
    rw [h_take]
    have h_drop : z.drop p.length = q.take i := by
      dsimp only [z]
      rw [List.drop_left]
    rw [h_drop, List.take_append_drop]
    rw [Part.mem_bind_iff]
    exact ⟨y, hpy, hqyx⟩
  have h_qy : produces Dy (pairCode (Nat.bits p.length) []) z y := by
    change y ∈ V
      (z.take (bitsToNat
        (decodeFirst (pairCode (Nat.bits p.length) []))), [])
    rw [decodeFirst_pairCode, bitsToNat_bits]
    have h_take : z.take p.length = p := by
      dsimp only [z]
      rw [List.take_left]
    rw [h_take]
    exact hpy
  have hx_eval := hcx x z
  have hy_eval := hcy y z
  have h_len_x :
      (pairCode (Nat.bits p.length) (q.drop i)).length =
        2 * (Nat.bits p.length).length + 1 + q.length - i := by
    rw [length_pairCode, List.length_drop]
    omega
  have h_len_y :
      (pairCode (Nat.bits p.length) []).length =
        2 * (Nat.bits p.length).length + 1 := by
    rw [length_pairCode, List.length_nil]
    omega
  have hcx_le : cx ≤ c := by dsimp [c]; omega
  have hcy_le : cy ≤ c := by dsimp [c]; omega
  have hc3 : 3 ≤ c := by dsimp [c]; omega
  have h_A_ge_1 : 1 ≤ (Nat.bits (p.length + q.length + 1)).length := by
    have : 1 ≤ p.length + q.length + 1 := by omega
    have h := length_natBits_mono this
    exact h
  constructor
  · calc
      condK V y z ≤ condK Dy y z + (cy : ENat) := hy_eval
      _ ≤ ((pairCode (Nat.bits p.length) []).length : ENat) + (cy : ENat) := by
        gcongr
        exact sInf_le ⟨_, h_qy, rfl⟩
      _ = (((pairCode (Nat.bits p.length) []).length + cy : Nat) : ENat) := by
        push_cast
        rfl
      _ ≤ (logSlack c (p.length + q.length + 1) : ENat) := by
        norm_cast
        have : (Nat.bits p.length).length ≤
            (Nat.bits (p.length + q.length + 1)).length := by
          apply length_natBits_mono
          omega
        rw [h_len_y]
        change 2 * (Nat.bits p.length).length + 1 + cy ≤
          c * (Nat.bits (p.length + q.length + 1)).length + c
        have h_bound : 2 * (Nat.bits p.length).length + 1 + cy ≤
            c * (Nat.bits (p.length + q.length + 1)).length + c := by
          nlinarith
        omega
  · calc
      condK V x z ≤ condK Dx x z + (cx : ENat) := hx_eval
      _ ≤ ((pairCode (Nat.bits p.length) (q.drop i)).length : ENat) + (cx : ENat) := by
        gcongr
        exact sInf_le ⟨_, h_px, rfl⟩
      _ = (((pairCode (Nat.bits p.length) (q.drop i)).length + cx : Nat) : ENat) := by
        push_cast
        rfl
      _ ≤ (((q.length - i +
          logSlack c (p.length + q.length + 1)) : Nat) : ENat) := by
        norm_cast
        have : (Nat.bits p.length).length ≤
            (Nat.bits (p.length + q.length + 1)).length := by
          apply length_natBits_mono
          omega
        rw [h_len_x]
        change 2 * (Nat.bits p.length).length + 1 + q.length - i + cx ≤
          q.length - i +
            (c * (Nat.bits (p.length + q.length + 1)).length + c)
        have h_bound : 2 * (Nat.bits p.length).length + 1 + cx ≤
            c * (Nat.bits (p.length + q.length + 1)).length + c := by
          nlinarith
        omega

/-- A concatenation of two visible raw-program prefixes has plain complexity
at most its literal length plus one uniform logarithmic parsing budget. -/
theorem plainK_combinedProgramPrefixes_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ p q : BitString, ∀ i j : Nat,
      i ≤ p.length →
      j ≤ q.length →
      plainK V (p.take i ++ q.take j) ≤
        (((i + j +
          logSlack c (p.length + q.length + 1)) : Nat) : ENat) := by
  obtain ⟨c, hc⟩ := plainKLeLength V hV
  refine ⟨c, fun p q i j hi hj => ?_⟩
  have hPrefixLength :
      (p.take i ++ q.take j).length = i + j := by
    simp only [List.length_append, List.length_take]
    omega
  have hFixed : c ≤ logSlack c (p.length + q.length + 1) := by
    unfold logSlack
    omega
  calc
    plainK V (p.take i ++ q.take j) ≤
        ((p.take i ++ q.take j).length : ENat) + (c : ENat) :=
      hc (p.take i ++ q.take j)
    _ = (((i + j + c : Nat)) : ENat) := by
      rw [hPrefixLength]
      push_cast
      ring
    _ ≤ (((i + j +
          logSlack c (p.length + q.length + 1) : Nat)) : ENat) := by
      exact_mod_cast Nat.add_le_add_left hFixed (i + j)

/-- Tight prefix-completion/transitivity leaf for SUV Theorem 225.  From a
visible prefix of a plain program for `y`, one raw program supplies the missing
suffix and then runs a conditional program for `x | y`; each raw program is
stored once, and only their split point is self-delimited. -/
theorem condK_output_given_plainProgramPrefix_then_conditionalProgram_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ p q x y : BitString, ∀ i : Nat,
      produces V p [] y →
      produces V q y x →
      i ≤ p.length →
      condK V x (p.take i) ≤
        (((p.length - i + q.length +
          logSlack c (p.length + q.length + 1)) : Nat) : ENat) := by
  let D : Map := fun input =>
    let body := decodeSecond input.1
    let suffixLength := bitsToNat (decodeFirst input.1)
    (V (input.2 ++ body.take suffixLength, [])).bind fun y =>
      V (body.drop suffixLength, y)
  have hD : isDecompressor D := by
    have hBody : Computable (fun input : BitString × BitString =>
        decodeSecond input.1) :=
      decodeSecond_computable.comp Computable.fst
    have hSuffixLength : Computable (fun input : BitString × BitString =>
        bitsToNat (decodeFirst input.1)) :=
      bitsToNat_primrec.to_comp.comp
        (decodeFirst_computable.comp Computable.fst)
    have hSuffix : Computable (fun input : BitString × BitString =>
        (decodeSecond input.1).take
          (bitsToNat (decodeFirst input.1))) :=
      primrec_list_take.to_comp.comp hBody hSuffixLength
    have hRest : Computable (fun input : BitString × BitString =>
        (decodeSecond input.1).drop
          (bitsToNat (decodeFirst input.1))) :=
      primrec_list_drop.to_comp.comp hBody hSuffixLength
    have hProgram : Computable (fun input : BitString × BitString =>
        input.2 ++ (decodeSecond input.1).take
          (bitsToNat (decodeFirst input.1))) :=
      Computable.list_append.comp Computable.snd hSuffix
    have hFirst : Partrec (fun input : BitString × BitString =>
        V (input.2 ++ (decodeSecond input.1).take
          (bitsToNat (decodeFirst input.1)), [])) :=
      Partrec.comp hV.1
        (Computable.pair hProgram (Computable.const []))
    have hSecond : Partrec₂
        (fun (input : BitString × BitString) (y : BitString) =>
          V ((decodeSecond input.1).drop
            (bitsToNat (decodeFirst input.1)), y)) :=
      Partrec.comp hV.1
        (Computable.pair (hRest.comp Computable.fst) Computable.snd)
    exact Partrec.bind hFirst hSecond
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  let c := max cD 3
  refine ⟨c, ?_⟩
  intro p q x y i hpy hqyx hi
  let code := pairCode (Nat.bits (p.length - i)) (p.drop i ++ q)
  have hProduced : produces D code (p.take i) x := by
    change x ∈
      (V (p.take i ++
          (decodeSecond code).take
            (bitsToNat (decodeFirst code)), [])).bind fun y =>
        V ((decodeSecond code).drop
          (bitsToNat (decodeFirst code)), y)
    dsimp only [code]
    rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    have hDropLength : (p.drop i).length = p.length - i :=
      List.length_drop
    rw [← hDropLength, List.take_left, List.drop_left,
      List.take_append_drop, Part.mem_bind_iff]
    exact ⟨y, hpy, hqyx⟩
  have hCodeLength :
      code.length =
        2 * (Nat.bits (p.length - i)).length + 1 +
          (p.length - i + q.length) := by
    dsimp only [code]
    rw [length_pairCode, List.length_append, List.length_drop]
    omega
  have hcD_le : cD ≤ c := by
    dsimp only [c]
    omega
  have hc3 : 3 ≤ c := by
    dsimp only [c]
    omega
  have hBitsPositive :
      1 ≤ (Nat.bits (p.length + q.length + 1)).length := by
    have hOne : 1 ≤ p.length + q.length + 1 := by omega
    exact length_natBits_mono hOne
  have hBits :
      (Nat.bits (p.length - i)).length ≤
        (Nat.bits (p.length + q.length + 1)).length :=
    length_natBits_mono (by omega)
  calc
    condK V x (p.take i) ≤ condK D x (p.take i) + (cD : ENat) :=
      hcD x (p.take i)
    _ ≤ (code.length : ENat) + (cD : ENat) := by
      gcongr
      exact sInf_le ⟨code, hProduced, rfl⟩
    _ = (((code.length + cD : Nat)) : ENat) := by
      push_cast
      rfl
    _ ≤ (((p.length - i + q.length +
          logSlack c (p.length + q.length + 1) : Nat)) : ENat) := by
      norm_cast
      rw [hCodeLength]
      unfold logSlack
      have hOverhead :
          2 * (Nat.bits (p.length - i)).length + 1 + cD ≤
            c * (Nat.bits (p.length + q.length + 1)).length + c := by
        nlinarith
      omega

/-- Exact finite case cover behind the constructive lower inclusion in SUV
Theorem 225.  Every point of the lower envelope dominates one of the five
canonical shortest-description-prefix profiles used in the source proof. -/
theorem commonInformationLowerEnvelope_prefix_case_cover
    {n : Nat} {t : CommonInformationTriple}
    (ht : t ∈ CommonInformationLowerEnvelope n) :
    (∃ i j,
        i ≤ 2 * n ∧ j ≤ 2 * n ∧
        i + j ≤ t.1 ∧
        2 * n - i ≤ t.2.1 ∧ 2 * n - j ≤ t.2.2) ∨
    (∃ i,
        i ≤ n ∧ 2 * n + i ≤ t.1 ∧ n - i ≤ t.2.1) ∨
    (∃ i,
        i ≤ n ∧ 2 * n + i ≤ t.1 ∧ n - i ≤ t.2.2) ∨
    (∃ i,
        i ≤ 2 * n ∧ i ≤ t.1 ∧
        3 * n - i ≤ t.2.1 ∧ 2 * n - i ≤ t.2.2) ∨
    (∃ i,
        i ≤ 2 * n ∧ i ≤ t.1 ∧
        2 * n - i ≤ t.2.1 ∧ 3 * n - i ≤ t.2.2) := by
  rcases ht with ⟨hUpper, hFaces⟩
  change
    2 * n < t.1 + t.2.1 ∧
      2 * n < t.1 + t.2.2 ∧
      3 * n < t.1 + t.2.1 + t.2.2 at hUpper
  change
    3 * n < t.1 + t.2.1 ∨
      3 * n < t.1 + t.2.2 ∨
      4 * n < t.1 + t.2.1 + t.2.2 at hFaces
  rcases hFaces with hLeft | hRight | hJoint
  · by_cases hSmall : t.2.1 ≤ n
    · exact Or.inr (Or.inl ⟨n - t.2.1, by omega, by omega, by omega⟩)
    · by_cases hLarge : 2 * n ≤ t.1
      · exact Or.inr (Or.inl ⟨0, by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨t.1, by omega, le_rfl, by omega, by omega⟩)))
  · by_cases hSmall : t.2.2 ≤ n
    · exact Or.inr (Or.inr (Or.inl
        ⟨n - t.2.2, by omega, by omega, by omega⟩))
    · by_cases hLarge : 2 * n ≤ t.1
      · exact Or.inr (Or.inr (Or.inl
          ⟨0, by omega, by omega, by omega⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨t.1, by omega, le_rfl, by omega, by omega⟩)))
  · exact Or.inl
      ⟨2 * n - t.2.1, 2 * n - t.2.2,
        by omega, by omega, by omega, by omega, by omega⟩

end Kolmogorov
