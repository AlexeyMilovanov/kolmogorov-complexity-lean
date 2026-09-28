import KolmogorovMathlib.CommonInformation.WorstCaseRegionSelector
import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaCount

/-!
# The worst-case common-information region

`muchnik_worst_case_region` (SUV Theorem 224): there are pairs with marginal complexities near
`2n` and joint complexity near `3n` for which every common witness violates one of the three
region inequalities — so the achievable region is bounded away from the trivial one.  The base
and inductive cases are `muchnik_worst_case_region_zero` and `muchnik_worst_case_region_pos`,
at the slack constant `muchnikRegionSlackConst`.

The pair comes from the selector of `WorstCaseRegionSelector`:
`muchnikRegion_selector_input_length_le` bounds the advice it is given by `3n + 2|bits n| + 3`,
`muchnikRegionSelector_pairPlainK_upper` bounds the complexity of the pair it returns, and
`muchnikRegion_obstruction_mono_margin` lets the obstruction be widened.
-/

namespace Kolmogorov

/-- The advice fed to the region selector has length at most `3n + 2|bits n| + 3`. -/
theorem muchnikRegion_selector_input_length_le
    {V : Map} {n : Nat} (hn : 0 < n) :
    (pairCode (Nat.bits n)
      (Nat.bits (muchnikRegionAdviceCount V n))).length ≤
      3 * n + 2 * (Nat.bits n).length + 3 := by
  exact muchnik_advice_length_le
    (muchnikRegionAdviceCount_lt V hn)

/-- The obstruction satisfied by a survivor of the region construction is preserved when the
margin is enlarged. -/
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

/-- The region construction produces survivors whose pair has plain complexity at most
`3n` up to a logarithmic slack. -/
theorem muchnikRegionSelector_pairPlainK_upper
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ {n : Nat}, 0 < n →
      ∃ x y,
        IsMuchnikRegionSurvivor V n x y ∧
        pairPlainK V x y ≤
          ((3 * n + logSlack C n : Nat) : ENat) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cLength, hLength⟩ := plainK_le_length V hV
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

/-- Base case `n = 0` for SUV Theorem 224. -/
private theorem muchnik_worst_case_region_zero
    (V : Map) (hV : isOptimalConditional V) (cLength C : Nat)
    (hLength : ∀ w, plainK V w ≤ ((w.length : Nat) : ENat) + (cLength : ENat))
    (hSlack : 7 + 2 * cLength ≤ logSlack C 0) :
    ∃ x y : BitString, ∃ kx ky kxy : Nat,
      x.length = 2 * 0 + 2 ∧
      y.length = 2 * 0 + 2 ∧
      HasPlainComplexityValue V x kx ∧
      HasPlainComplexityValue V y ky ∧
      HasPlainComplexityValue V (pairCode x y) kxy ∧
      NatCloseWithin kx (2 * 0) (logSlack C 0) ∧
      NatCloseWithin ky (2 * 0) (logSlack C 0) ∧
      NatCloseWithin kxy (3 * 0) (logSlack C 0) ∧
      MutualInformationWithin V x y 0 (logSlack C 0) ∧
      ∀ z,
        (3 * 0 : ENat) ≤
            plainK V z + condK V x z + logSlack C 0 ∨
        (3 * 0 : ENat) ≤
            plainK V z + condK V y z + logSlack C 0 ∨
        (4 * 0 : ENat) ≤
            plainK V z + condK V x z + condK V y z +
              logSlack C 0 := by
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

/-- The slack constant `2 * (34 + 2 * cLength + cPair)` at which the inductive case of
SUV Theorem 224 is stated. -/
private def muchnikRegionSlackConst (cLength cPair : Nat) : Nat :=
  2 * (34 + 2 * cLength + cPair)

/-- Inductive case `0 < n` for SUV Theorem 224. -/
private theorem muchnik_worst_case_region_pos
    (V : Map) (hV : isOptimalConditional V)
    (cLength cPair : Nat)
    (hLength : ∀ w, plainK V w ≤ ((w.length : Nat) : ENat) + (cLength : ENat))
    (hPair : ∀ {n : Nat}, 0 < n →
      ∃ x y,
        IsMuchnikRegionSurvivor V n x y ∧
        pairPlainK V x y ≤
          ((3 * n + logSlack cPair n : Nat) : ENat))
    {n : Nat} (hnPos : 0 < n) :
    ∃ x y : BitString, ∃ kx ky kxy : Nat,
      x.length = 2 * n + 2 ∧
      y.length = 2 * n + 2 ∧
      HasPlainComplexityValue V x kx ∧
      HasPlainComplexityValue V y ky ∧
      HasPlainComplexityValue V (pairCode x y) kxy ∧
      NatCloseWithin kx (2 * n) (logSlack (muchnikRegionSlackConst cLength cPair) n) ∧
      NatCloseWithin ky (2 * n) (logSlack (muchnikRegionSlackConst cLength cPair) n) ∧
      NatCloseWithin kxy (3 * n) (logSlack (muchnikRegionSlackConst cLength cPair) n) ∧
      MutualInformationWithin V x y n (logSlack (muchnikRegionSlackConst cLength cPair) n) ∧
      ∀ z,
        (3 * n : ENat) ≤
            plainK V z + condK V x z + logSlack (muchnikRegionSlackConst cLength cPair) n ∨
        (3 * n : ENat) ≤
            plainK V z + condK V y z + logSlack (muchnikRegionSlackConst cLength cPair) n ∨
        (4 * n : ENat) ≤
            plainK V z + condK V x z + condK V y z +
              logSlack (muchnikRegionSlackConst cLength cPair) n := by
  set C := muchnikRegionSlackConst cLength cPair with hCdef
  have hC : 2 * (34 + 2 * cLength + cPair) ≤ C := le_of_eq hCdef.symm
  set B := 34 + 2 * cLength + cPair with hBdef
  have hB : 34 + 2 * cLength + cPair ≤ B := le_of_eq hBdef.symm
  have hCB : 2 * B ≤ C := by rw [hBdef]; exact hC
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
    dsimp only [d, logSlack]
    nlinarith [Nat.zero_le (Nat.bits n).length, hB]
  have hPairSlack : logSlack cPair n ≤ d := by
    exact logSlack_mono_left (by omega) n
  have hxUpperD : kx ≤ 2 * n + d := by omega
  have hyUpperD : ky ≤ 2 * n + d := by omega
  have hxyUpperD : kxy ≤ 3 * n + d := by omega
  have hTwiceD : 2 * d ≤ logSlack C n := by
    dsimp only [d, logSlack]
    nlinarith [Nat.zero_le (Nat.bits n).length, hCB]
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
    omega
  have hObstruction :=
    muchnikRegion_obstruction_mono_margin hSurvivor hMargin
  exact ⟨x, y, kx, ky, kxy, hSurvivor.1, hSurvivor.2.1,
    hkx, hky, hkxy, hxClose, hyClose, hxyClose, hMutual,
    hObstruction⟩

/-- SUV Theorem 224: there are pairs with marginal complexities near `2n`,
joint complexity near `3n`, and no common witness below all three faces of the
simultaneous Muchnik obstruction. -/
theorem muchnik_worst_case_region
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
  obtain ⟨cLength, hLength⟩ := plainK_le_length V hV
  obtain ⟨cPair, hPair⟩ :=
    muchnikRegionSelector_pairPlainK_upper V hV
  let B := 34 + 2 * cLength + cPair
  let C := 2 * B
  refine ⟨C, fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    have hSlack : 7 + 2 * cLength ≤ logSlack C 0 := by
      simp only [logSlack, Nat.bits, C, B]
      omega
    exact muchnik_worst_case_region_zero V hV cLength C hLength hSlack
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    exact muchnik_worst_case_region_pos V hV cLength cPair hLength
      hPair hnPos

end Kolmogorov
