import KolmogorovMathlib.CommonInformation.IncidenceCoding
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.CommonInformation.PlainSymmetry

namespace Kolmogorov

lemma exists_incidentPairCode_not_compressible
    (V : Map) {n : Nat} (hn : 0 < n) :
    ∃ w, w ∈ concreteIncidentPairCodes n ∧
      w ∉ compressibleWords V [] (3 * n - 1) := by
  classical
  by_contra h
  push Not at h
  have hsub :
      (concreteIncidentPairCodes n).toFinset ⊆
        compressibleWords V [] (3 * n - 1) := by
    intro w hw
    exact h w (List.mem_toFinset.mp hw)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (concreteIncidentPairCodes_nodup n),
    concreteIncidentPairCodes_length] at hcard
  have hcompress := cardCompressibleWordsLt V [] (3 * n - 1)
  have hexponent : 3 * n - 1 + 1 = 3 * n := by omega
  rw [hexponent] at hcompress
  have hprime : 2 ^ (3 * n) < concretePrime n ^ 3 := by
    rw [show 2 ^ (3 * n) = (2 ^ n) ^ 3 by
      rw [← pow_mul]
      congr 1
      omega]
    exact Nat.pow_lt_pow_left (concretePrime_lower n) (by omega)
  omega

lemma exists_highComplexity_concreteIncidentEdge
    (V : Map) (hV : isOptimalConditional V) {n : Nat} (hn : 0 < n) :
    ∃ e : ConcreteIncidentEdge n, ∃ kxy,
      HasPlainComplexityValue V
        (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2)) kxy ∧
      3 * n ≤ kxy := by
  obtain ⟨w, hw, hwNot⟩ := exists_incidentPairCode_not_compressible V hn
  obtain ⟨e, rfl⟩ := (concreteIncidentPairCodes_mem_iff n w).mp hw
  obtain ⟨kxy, hkxy⟩ := exists_plainComplexityValue V hV
    (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2))
  refine ⟨e, kxy, hkxy, ?_⟩
  have hnotLe : ¬ kxy ≤ 3 * n - 1 := by
    intro hle
    apply hwNot
    apply (mem_compressibleWords_iff V [] _ (3 * n - 1)).mpr
    change plainK V
      (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2)) ≤
        (3 * n - 1 : Nat)
    rw [hkxy]
    exact_mod_cast hle
  omega

lemma pairPlainK_swap_values_close
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ x y kxy kyx,
      HasPlainComplexityValue V (pairCode x y) kxy →
      HasPlainComplexityValue V (pairCode y x) kyx →
      NatCloseWithin kxy kyx c := by
  obtain ⟨c, hc⟩ := pairPlainK_swap_le V hV
  refine ⟨c, fun x y kxy kyx hxy hyx => ?_⟩
  unfold NatCloseWithin
  constructor
  · have h := hc y x
    rw [pairPlainK, pairPlainK, hxy, hyx] at h
    exact_mod_cast h
  · have h := hc x y
    rw [pairPlainK, pairPlainK, hyx, hxy] at h
    exact_mod_cast h

lemma mutualInformationWithin_of_close_plain_values
    (V : Map) {x y : BitString} {kx ky kxy ax ay axy d m : Nat} :
    HasPlainComplexityValue V x kx →
    HasPlainComplexityValue V y ky →
    HasPlainComplexityValue V (pairCode x y) kxy →
    NatCloseWithin kx ax d →
    NatCloseWithin ky ay d →
    NatCloseWithin kxy axy d →
    axy + m = ax + ay →
    MutualInformationWithin V x y m (3 * d) := by
  intro hx hy hxy hxClose hyClose hxyClose htargets
  unfold NatCloseWithin at hxClose hyClose hxyClose
  unfold MutualInformationWithin
  rw [pairPlainK, hxy, hx, hy]
  constructor
  · exact_mod_cast (show kxy + m ≤ kx + ky + 3 * d by omega)
  · exact_mod_cast (show kx + ky ≤ kxy + m + 3 * d by omega)

lemma logSlack_profile_fold (c₁ c₂ c₃ : Nat) :
    ∃ C, ∀ n, logSlack c₁ n + logSlack c₂ n + logSlack c₃ n ≤ logSlack C n := by
  refine ⟨c₁ + c₂ + c₃, fun n => ?_⟩
  rw [logSlack_add_const, logSlack_add_const]

theorem exercise_309_incident_edge_profile
    (V : Map) (hV : isOptimalConditional V) :
    ∀ d, ∃ C, ∀ n (e : ConcreteIncidentEdge n) kxy,
      HasPlainComplexityValue V
        (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2)) kxy →
      3 * n ≤ kxy + logSlack d n →
      ∃ kx ky,
        HasPlainComplexityValue V (concretePointCode n e.1.1) kx ∧
        HasPlainComplexityValue V (concreteLineCode n e.1.2) ky ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) ∧
        MutualInformationWithin V
          (concretePointCode n e.1.1) (concreteLineCode n e.1.2) n (logSlack C n) := by
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
  obtain ⟨cPair, hPair⟩ := plainK_concreteIncidentPair_le V hV
  obtain ⟨cLine, hLine⟩ := condK_concreteLine_given_point_le V hV
  obtain ⟨cPoint, hPoint⟩ := condK_concretePoint_given_line_le V hV
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_upper_values V hV
  obtain ⟨cSwap, hSwap⟩ := pairPlainK_swap_values_close V hV
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cChain 3 (cPair + cSwap + 4)
  intro d
  let K := cLength + cPair + cLine + cPoint + cSwap + 6
  let D := d + cFold + K
  let C := 3 * D
  refine ⟨C, ?_⟩
  intro n e kxy hkxy hHigh
  let x := concretePointCode n e.1.1
  let y := concreteLineCode n e.1.2
  have hxy : HasPlainComplexityValue V (pairCode x y) kxy := by
    simpa only [x, y] using hkxy
  obtain ⟨kx, hx⟩ := exists_plainComplexityValue V hV x
  obtain ⟨ky, hy⟩ := exists_plainComplexityValue V hV y
  obtain ⟨kyxCond, hyxCond⟩ :=
    exists_plainConditionalComplexityValue V hV y x
  obtain ⟨kxyCond, hxyCond⟩ :=
    exists_plainConditionalComplexityValue V hV x y
  obtain ⟨kSwap, hkSwap⟩ :=
    exists_plainComplexityValue V hV (pairCode y x)
  have hkxUpper : kx ≤ 2 * (n + 1) + cLength := by
    have h := hLength x
    rw [hx] at h
    have hxLength : x.length = 2 * (n + 1) := by
      simp only [x, concretePointCode_length]
    change (kx : ENat) ≤ (x.length : ENat) + (cLength : ENat) at h
    rw [hxLength] at h
    exact_mod_cast h
  have hkyUpper : ky ≤ 2 * (n + 1) + cLength := by
    have h := hLength y
    rw [hy] at h
    have hyLength : y.length = 2 * (n + 1) := by
      simp only [y, concreteLineCode_length]
    change (ky : ENat) ≤ (y.length : ENat) + (cLength : ENat) at h
    rw [hyLength] at h
    exact_mod_cast h
  have hkxyUpper : kxy ≤ 3 * (n + 1) + cPair := by
    have h := hPair n e
    change pairPlainK V x y ≤ ((3 * (n + 1) + cPair : Nat) : ENat) at h
    rw [pairPlainK, hxy] at h
    exact_mod_cast h
  have hyxCondUpper : kyxCond ≤ n + 1 + cLine := by
    have h := hLine n e
    change condK V y x ≤ ((n + 1 + cLine : Nat) : ENat) at h
    rw [hyxCond] at h
    exact_mod_cast h
  have hxyCondUpper : kxyCond ≤ n + 1 + cPoint := by
    have h := hPoint n e
    change condK V x y ≤ ((n + 1 + cPoint : Nat) : ENat) at h
    rw [hxyCond] at h
    exact_mod_cast h
  have hSwapClose : NatCloseWithin kxy kSwap cSwap :=
    hSwap x y kxy kSwap hxy hkSwap
  have hkxySwap : kxy ≤ kSwap + cSwap := hSwapClose.1
  have hSwapKxy : kSwap ≤ kxy + cSwap := hSwapClose.2
  have hChainXY :
      kxy ≤ kx + kyxCond + logSlack cChain (kxy + 1) :=
    hChain x y kx kyxCond kxy hx hyxCond hxy
  have hChainYX :
      kSwap ≤ ky + kxyCond + logSlack cChain (kSwap + 1) :=
    hChain y x ky kxyCond kSwap hy hxyCond hkSwap
  have hkxyArg : kxy + 1 ≤ 3 * n + (cPair + cSwap + 4) := by
    omega
  have hkSwapArg : kSwap + 1 ≤ 3 * n + (cPair + cSwap + 4) := by
    omega
  have hLogXY : logSlack cChain (kxy + 1) ≤ logSlack cFold n :=
    (logSlack_mono_right cChain hkxyArg).trans (hFold n)
  have hLogYX : logSlack cChain (kSwap + 1) ≤ logSlack cFold n :=
    (logSlack_mono_right cChain hkSwapArg).trans (hFold n)
  have hBudget :
      logSlack d n + logSlack cFold n + K ≤ logSlack D n := by
    calc
      logSlack d n + logSlack cFold n + K
          = logSlack (d + cFold) n + K := by
            rw [logSlack_add_const]
      _ ≤ logSlack (d + cFold + K) n :=
        logSlack_add_nat_le (d + cFold) K n
      _ = logSlack D n := by rfl
  have hxCloseD : NatCloseWithin kx (2 * n) (logSlack D n) := by
    unfold NatCloseWithin
    constructor <;> omega
  have hyCloseD : NatCloseWithin ky (2 * n) (logSlack D n) := by
    unfold NatCloseWithin
    constructor <;> omega
  have hxyCloseD : NatCloseWithin kxy (3 * n) (logSlack D n) := by
    unfold NatCloseWithin
    constructor <;> omega
  have hMID :
      MutualInformationWithin V x y n (3 * logSlack D n) :=
    mutualInformationWithin_of_close_plain_values V hx hy hxy
      hxCloseD hyCloseD hxyCloseD (by omega)
  have hDC : D ≤ C := by
    dsimp only [C]
    omega
  have hSlackMono : logSlack D n ≤ logSlack C n :=
    logSlack_mono_left hDC n
  have hMI : MutualInformationWithin V x y n (logSlack C n) := by
    have hEq : 3 * logSlack D n = logSlack C n := by
      dsimp only [C]
      exact logSlack_nsmul 3 D n
    rw [← hEq]
    exact hMID
  have hResult :
      ∃ kx ky,
        HasPlainComplexityValue V x kx ∧
        HasPlainComplexityValue V y ky ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) ∧
        MutualInformationWithin V x y n (logSlack C n) :=
    ⟨kx, ky, hx, hy, hxCloseD.mono hSlackMono,
      hyCloseD.mono hSlackMono, hxyCloseD.mono hSlackMono, hMI⟩
  simpa only [x, y] using hResult

end Kolmogorov
