import KolmogorovMathlib.CommonInformation.WorstCaseRegionSelector
import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaCount

namespace Kolmogorov

theorem muchnikRegion_selector_input_length_le
    {V : Map} {n : Nat} (hn : 0 < n) :
    (pairCode (Nat.bits n)
      (Nat.bits (muchnikRegionAdviceCount V n))).length ≤
      3 * n + 2 * (Nat.bits n).length + 3 := by
  exact muchnik_advice_length_le
    (muchnikRegionAdviceCount_lt V hn)

theorem muchnikRegion_obstruction_mono_margin
    {V : Map} {n d : Nat} {x y : BitString}
    (h : IsMuchnikRegionSurvivor V n x y)
    (hd : muchnikRegionMargin n ≤ d) :
    ∀ z,
      (3 * n : ENat) ≤ plainK V z + condK V x z + d ∨
      (3 * n : ENat) ≤ plainK V z + condK V y z + d ∨
      (4 * n : ENat) ≤
        plainK V z + condK V x z + condK V y z + d := by
  intro z
  rcases h.2.2.2.2.2 z with hLeft | hRight | hPair
  · left
    exact hLeft.trans (by
      gcongr)
  · right
    left
    exact hRight.trans (by
      gcongr)
  · right
    right
    exact hPair.trans (by
      gcongr)

theorem muchnikRegionSelector_pairPlainK_upper
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ {n : Nat}, 0 < n →
      ∃ x y,
        IsMuchnikRegionSurvivor V n x y ∧
        pairPlainK V x y ≤
          ((3 * n + logSlack C n : Nat) : ENat) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
  obtain ⟨cSelector, hSelector⟩ :=
    plainK_partrec_map_le V hV (muchnikRegionSelector code)
      (muchnikRegionSelector_partrec code)
  let C := 3 + cLength + cSelector
  refine ⟨C, ?_⟩
  intro n hn
  obtain ⟨x, y, hSelected, hSurvivor⟩ :=
    muchnikRegionSelector_spec hcode hn
  let input :=
    pairCode (Nat.bits n)
      (Nat.bits (muchnikRegionAdviceCount V n))
  have hInputLength :
      input.length ≤ 3 * n + 2 * (Nat.bits n).length + 3 := by
    simpa only [input] using
      muchnikRegion_selector_input_length_le (V := V) hn
  have hSelectedMem :
      pairCode x y ∈ muchnikRegionSelector code input := by
    apply Part.eq_some_iff.mp
    simpa only [input] using hSelected
  have hPairUpper :
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
          cLength + cSelector : Nat) : ENat) := by
        push_cast
        rfl
  have hSlack :
      2 * (Nat.bits n).length + 3 + cLength + cSelector ≤
        logSlack C n := by
    simp only [C, logSlack]
    nlinarith [Nat.zero_le (Nat.bits n).length]
  refine ⟨x, y, hSurvivor, hPairUpper.trans ?_⟩
  have hFinal :
      3 * n + 2 * (Nat.bits n).length + 3 +
          cLength + cSelector ≤
        3 * n + logSlack C n := by
    omega
  exact_mod_cast hFinal

/-- SUV Theorem 224: there are pairs with marginal complexities near `2n`,
joint complexity near `3n`, and no common witness below all three faces of the
simultaneous Muchnik obstruction. -/
theorem theorem_224_muchnik_worst_case_region
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
        ∀ z,
          (3 * n : ENat) ≤
              plainK V z + condK V x z + logSlack C n ∨
          (3 * n : ENat) ≤
              plainK V z + condK V y z + logSlack C n ∨
          (4 * n : ENat) ≤
              plainK V z + condK V x z + condK V y z +
                logSlack C n := by
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
  obtain ⟨cPair, hPair⟩ :=
    muchnikRegionSelector_pairPlainK_upper V hV
  let B := 34 + 2 * cLength + cPair
  let C := 2 * B
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
    have hSlack : 7 + 2 * cLength ≤ logSlack C 0 := by
      simp only [logSlack, Nat.bits, C, B]
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
      constructor <;> exact_mod_cast (by omega)
    have hObstruction : ∀ z,
        (0 : ENat) ≤ plainK V z + condK V x z + logSlack C 0 ∨
        (0 : ENat) ≤ plainK V z + condK V y z + logSlack C 0 ∨
        (0 : ENat) ≤
          plainK V z + condK V x z + condK V y z + logSlack C 0 := by
      intro z
      exact Or.inl bot_le
    exact ⟨x, y, kx, ky, kxy, rfl, rfl, hkx, hky, hkxy,
      hxClose, hyClose, hxyClose, hMutual, hObstruction⟩
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨x, y, hSurvivor, hPairUpperENat⟩ :=
      hPair hnPos
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
        kxy ≤ 3 * n + logSlack cPair n := by
      rw [pairPlainK, hkxy] at hPairUpperENat
      exact_mod_cast hPairUpperENat
    let d := logSlack B n
    have hLiteralSlack : 2 + cLength ≤ d := by
      simp only [d, B, logSlack]
      nlinarith [Nat.zero_le (Nat.bits n).length]
    have hPairSlack : logSlack cPair n ≤ d := by
      exact logSlack_mono_left (by
        dsimp only [B]
        omega) n
    have hxUpperD : kx ≤ 2 * n + d := by omega
    have hyUpperD : ky ≤ 2 * n + d := by omega
    have hxyUpperD : kxy ≤ 3 * n + d := by omega
    have hTwiceD : 2 * d = logSlack C n := by
      simp only [d, C, logSlack]
      ring
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
      constructor <;> exact_mod_cast (by omega)
    have hMargin : muchnikRegionMargin n ≤ logSlack C n := by
      unfold muchnikRegionMargin
      apply logSlack_mono_left
      dsimp only [C, B]
      omega
    have hObstruction :=
      muchnikRegion_obstruction_mono_margin hSurvivor hMargin
    exact ⟨x, y, kx, ky, kxy, hSurvivor.1, hSurvivor.2.1,
      hkx, hky, hkxy, hxClose, hyClose, hxyClose, hMutual,
      hObstruction⟩

end Kolmogorov
