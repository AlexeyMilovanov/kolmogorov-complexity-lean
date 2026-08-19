import KolmogorovMathlib.CommonInformation.WorstCaseSelector
import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaCount

namespace Kolmogorov

theorem theorem_223_muchnik_nonextractability
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
        (muchnikThreshold n, muchnikThreshold n, muchnikThreshold n) ∉
          CommonInformationRegion V x y := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
  obtain ⟨cSelector, hSelector⟩ :=
    plainK_partrec_map_le V hV (muchnikSelector code)
      (muchnikSelector_partrec code)
  let B := 10 + 2 * cLength + cSelector
  let C := 4 + 2 * B
  refine ⟨C, fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    let x : BitString := [false, false]
    let y : BitString := [true, true]
    obtain ⟨kx, hkx⟩ := exists_plainComplexityValue V hV x
    obtain ⟨ky, hky⟩ := exists_plainComplexityValue V hV y
    obtain ⟨kxy, hkxy⟩ :=
      exists_plainComplexityValue V hV (pairCode x y)
    have hxUpper : kx ≤ 2 + cLength := by
      have h := hLength x
      rw [hkx] at h
      change (kx : ENat) ≤ (x.length : ENat) + (cLength : ENat) at h
      have hxLength : x.length = 2 := rfl
      rw [hxLength] at h
      exact_mod_cast h
    have hyUpper : ky ≤ 2 + cLength := by
      have h := hLength y
      rw [hky] at h
      change (ky : ENat) ≤ (y.length : ENat) + (cLength : ENat) at h
      have hyLength : y.length = 2 := rfl
      rw [hyLength] at h
      exact_mod_cast h
    have hxyUpper : kxy ≤ 7 + cLength := by
      have h := hLength (pairCode x y)
      rw [hkxy] at h
      change (kxy : ENat) ≤
        ((pairCode x y).length : ENat) + (cLength : ENat) at h
      rw [length_pairCode] at h
      have hxLength : x.length = 2 := rfl
      have hyLength : y.length = 2 := rfl
      rw [hxLength, hyLength] at h
      exact_mod_cast h
    have hSlack : 2 * B ≤ logSlack C 0 := by
      simp only [logSlack, Nat.bits, C]
      omega
    have hxClose : NatCloseWithin kx 0 (logSlack C 0) := by
      unfold NatCloseWithin
      constructor <;> omega
    have hyClose : NatCloseWithin ky 0 (logSlack C 0) := by
      unfold NatCloseWithin
      constructor <;> omega
    have hxyClose : NatCloseWithin kxy 0 (logSlack C 0) := by
      unfold NatCloseWithin
      constructor <;> omega
    have hMutual : MutualInformationWithin V x y 0 (logSlack C 0) := by
      unfold MutualInformationWithin
      rw [pairPlainK, hkxy, hkx, hky]
      have hOne : kxy ≤ kx + ky + logSlack C 0 := by omega
      have hTwo : kx + ky ≤ kxy + logSlack C 0 := by omega
      constructor
      · exact_mod_cast hOne
      · exact_mod_cast hTwo
    have hNoCommon :
        (muchnikThreshold 0, muchnikThreshold 0, muchnikThreshold 0) ∉
          CommonInformationRegion V x y := by
      change ¬∃ z,
        plainK V z < (muchnikThreshold 0 : ENat) ∧
        condK V x z < (muchnikThreshold 0 : ENat) ∧
        condK V y z < (muchnikThreshold 0 : ENat)
      rintro ⟨z, hz, _hx, _hy⟩
      have hzero : muchnikThreshold 0 = 0 := rfl
      rw [hzero] at hz
      exact (not_lt_of_ge bot_le) hz
    exact ⟨x, y, kx, ky, kxy, rfl, rfl, hkx, hky, hkxy,
      hxClose, hyClose, hxyClose, hMutual, hNoCommon⟩
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨x, y, hSelected, hSurvivor⟩ :=
      muchnikSelector_spec hcode hnPos
    let input :=
      pairCode (Nat.bits n) (Nat.bits (muchnikAdviceCount V n))
    have hAdviceCount :
        muchnikAdviceCount V n < 2 ^ (3 * n + 2) :=
      muchnikAdviceCount_lt V hnPos
    have hInputLength :
        input.length ≤ 3 * n + 2 * (Nat.bits n).length + 3 := by
      simpa only [input] using muchnik_advice_length_le hAdviceCount
    have hSelectedMem :
        pairCode x y ∈ muchnikSelector code input := by
      apply Part.eq_some_iff.mp
      simpa only [input] using hSelected
    have hPairUpperENat :
        pairPlainK V x y ≤
          ((3 * n + 2 * (Nat.bits n).length + 3 +
            cLength + cSelector : Nat) : ENat) := by
      calc
        pairPlainK V x y = plainK V (pairCode x y) := rfl
        _ ≤ plainK V input + (cSelector : ENat) :=
          hSelector input (pairCode x y) hSelectedMem
        _ ≤ ((input.length : Nat) : ENat) + (cLength : ENat) +
            (cSelector : ENat) := by
          gcongr
          exact hLength input
        _ ≤ ((3 * n + 2 * (Nat.bits n).length + 3 : Nat) : ENat) +
            (cLength : ENat) + (cSelector : ENat) := by
          gcongr
        _ = ((3 * n + 2 * (Nat.bits n).length + 3 +
            cLength + cSelector : Nat) : ENat) := by push_cast; rfl
    obtain ⟨kx, hkx⟩ := exists_plainComplexityValue V hV x
    obtain ⟨ky, hky⟩ := exists_plainComplexityValue V hV y
    obtain ⟨kxy, hkxy⟩ :=
      exists_plainComplexityValue V hV (pairCode x y)
    have hxLower : 2 * n ≤ kx := by
      have h := hSurvivor.2.2.1
      rw [hkx] at h
      exact_mod_cast h
    have hyLower : 2 * n ≤ ky := by
      have h := hSurvivor.2.2.2.1
      rw [hky] at h
      exact_mod_cast h
    have hxyLower : 3 * n ≤ kxy := by
      have h := hSurvivor.2.2.2.2.1
      rw [pairPlainK, hkxy] at h
      exact_mod_cast h
    have hxUpper : kx ≤ 2 * n + 2 + cLength := by
      have h := hLength x
      rw [hkx] at h
      change (kx : ENat) ≤ (x.length : ENat) + (cLength : ENat) at h
      rw [hSurvivor.1] at h
      exact_mod_cast h
    have hyUpper : ky ≤ 2 * n + 2 + cLength := by
      have h := hLength y
      rw [hky] at h
      change (ky : ENat) ≤ (y.length : ENat) + (cLength : ENat) at h
      rw [hSurvivor.2.1] at h
      exact_mod_cast h
    have hxyUpper :
        kxy ≤ 3 * n + 2 * (Nat.bits n).length + 3 +
          cLength + cSelector := by
      rw [pairPlainK, hkxy] at hPairUpperENat
      exact_mod_cast hPairUpperENat
    let d := 2 * (Nat.bits n).length + B
    have hxUpperD : kx ≤ 2 * n + d := by
      dsimp [d, B]
      omega
    have hyUpperD : ky ≤ 2 * n + d := by
      dsimp [d, B]
      omega
    have hxyUpperD : kxy ≤ 3 * n + d := by
      dsimp [d, B]
      omega
    have hTwiceD : 2 * d ≤ logSlack C n := by
      simp only [d, C, logSlack]
      nlinarith [Nat.zero_le (Nat.bits n).length]
    have hD : d ≤ logSlack C n := by omega
    have hxClose : NatCloseWithin kx (2 * n) (logSlack C n) := by
      unfold NatCloseWithin
      constructor <;> omega
    have hyClose : NatCloseWithin ky (2 * n) (logSlack C n) := by
      unfold NatCloseWithin
      constructor <;> omega
    have hxyClose : NatCloseWithin kxy (3 * n) (logSlack C n) := by
      unfold NatCloseWithin
      constructor <;> omega
    have hMutualNat :=
      mutualInformation_nat_bounds hxLower hxUpperD hyLower hyUpperD
        hxyLower hxyUpperD
    have hMutual : MutualInformationWithin V x y n (logSlack C n) := by
      unfold MutualInformationWithin
      rw [pairPlainK, hkxy, hkx, hky]
      have hOne :
          kxy + n ≤ kx + ky + logSlack C n := by omega
      have hTwo :
          kx + ky ≤ kxy + n + logSlack C n := by omega
      constructor
      · exact_mod_cast hOne
      · exact_mod_cast hTwo
    exact ⟨x, y, kx, ky, kxy, hSurvivor.1, hSurvivor.2.1,
      hkx, hky, hkxy, hxClose, hyClose, hxyClose, hMutual,
      hSurvivor.2.2.2.2.2⟩

end Kolmogorov
