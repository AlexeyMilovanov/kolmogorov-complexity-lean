import Mathlib.FieldTheory.Finite.GaloisField
import KolmogorovMathlib.CommonInformation.IncidenceCodecs
import KolmogorovMathlib.CommonInformation.IncidenceProfile
import KolmogorovMathlib.CommonInformation.QuadraticIncidenceClasses
import KolmogorovMathlib.CommonInformation.QuadraticClassDecoders
import KolmogorovMathlib.CommonInformation.QuadraticEdgeDecoders
import KolmogorovMathlib.CommonInformation.RegionEnvelopes
import KolmogorovMathlib.CommonInformation.WorstCase

/-!
# Exercise 311: the quadratic-extension incidence graph

The quadratic extension `ConcreteQuadraticField m = GF(q²)`, its computably
presented basis `concreteQuadraticBasis m = (1, quadGen m)`, and the fixed-width
codes `quadraticFieldCode`, `quadraticPointCode`, `quadraticLineCode` are
developed in `QuadraticModel.lean` and `QuadraticIncidenceDecoders.lean`; the
uniform decoders behind the coding bounds live in
`QuadraticIncidenceDecoders.lean` and `QuadraticEdgeDecoders.lean`.
-/

namespace Kolmogorov

open AffineIncidence
open QuadraticIncidence


/-- The encoded point/line pair map is injective. -/
lemma quadraticIncidentPairCode_injective (m : Nat) :
    Function.Injective
      (fun e : Point (ConcreteQuadraticField m) × Line (ConcreteQuadraticField m) =>
        pairCode (quadraticPointCode m e.1) (quadraticLineCode m e.2)) := by
  intro e e' he
  apply Prod.ext
  · apply quadraticPointCode_injective m
    simpa only [decodeFirst_pairCode] using congrArg decodeFirst he
  · apply quadraticLineCode_injective m
    simpa only [decodeSecond_pairCode] using congrArg decodeSecond he

/-- The finite set of encoded incident point/line pairs over `GF(q²)`.  This is
a cardinality object only; no computability claim is made here. -/
noncomputable def quadraticIncidentPairCodes (m : Nat) : Finset BitString :=
  (incidentEdges (ConcreteQuadraticField m)).image fun e =>
    pairCode (quadraticPointCode m e.1) (quadraticLineCode m e.2)

lemma mem_quadraticIncidentPairCodes_iff (m : Nat) (w : BitString) :
    w ∈ quadraticIncidentPairCodes m ↔
      ∃ e : ↑(incidentEdges (ConcreteQuadraticField m)),
        w = pairCode (quadraticPointCode m e.1.1) (quadraticLineCode m e.1.2) := by
  simp only [quadraticIncidentPairCodes, Finset.mem_image]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩
  · rintro ⟨⟨e, he⟩, rfl⟩
    exact ⟨e, he, rfl⟩

lemma quadraticIncidentPairCodes_card (m : Nat) :
    (quadraticIncidentPairCodes m).card = concretePrime m ^ 6 := by
  rw [quadraticIncidentPairCodes,
    Finset.card_image_of_injective _ (quadraticIncidentPairCode_injective m),
    incidentEdges_card]
  rw [show Fintype.card (ConcreteQuadraticField m) = concretePrime m ^ 2 by
    rw [Fintype.card_eq_nat_card]
    change Nat.card (GaloisField (concretePrime m) 2) = concretePrime m ^ 2
    exact GaloisField.card (concretePrime m) 2 (by omega)]
  ring

/-- A cardinality-only incompressibility selector for the quadratic incidence
graph.  Effectivity is not needed for this lower bound. -/
lemma exists_quadraticIncidentPairCode_not_compressible
    (V : Map) {m : Nat} (hm : 0 < m) :
    ∃ w, w ∈ quadraticIncidentPairCodes m ∧
      w ∉ compressibleWords V [] (6 * m - 1) := by
  classical
  by_contra h
  push Not at h
  have hsub : quadraticIncidentPairCodes m ⊆
      compressibleWords V [] (6 * m - 1) := by
    intro w hw
    exact h w hw
  have hcard := Finset.card_le_card hsub
  rw [quadraticIncidentPairCodes_card] at hcard
  have hcompress := cardCompressibleWordsLt V [] (6 * m - 1)
  have hexponent : 6 * m - 1 + 1 = 6 * m := by omega
  rw [hexponent] at hcompress
  have hprime : 2 ^ (6 * m) < concretePrime m ^ 6 := by
    rw [show 2 ^ (6 * m) = (2 ^ m) ^ 6 by
      rw [← pow_mul]
      congr 1
      omega]
    exact Nat.pow_lt_pow_left (concretePrime_lower m) (by omega)
  omega

/-- High-complexity incident edges exist in the quadratic incidence graph. -/
theorem exists_highComplexity_quadraticIncidentEdge
    (V : Map) (hV : isOptimalConditional V) {m : Nat} (hm : 0 < m) :
    ∃ e : ↑(incidentEdges (ConcreteQuadraticField m)), ∃ kxy,
      HasPlainComplexityValue V
        (pairCode (quadraticPointCode m e.1.1) (quadraticLineCode m e.1.2)) kxy ∧
      6 * m ≤ kxy := by
  obtain ⟨w, hw, hwNot⟩ :=
    exists_quadraticIncidentPairCode_not_compressible V hm
  obtain ⟨e, rfl⟩ := (mem_quadraticIncidentPairCodes_iff m w).mp hw
  obtain ⟨kxy, hkxy⟩ := exists_plainComplexityValue V hV
    (pairCode (quadraticPointCode m e.1.1) (quadraticLineCode m e.1.2))
  refine ⟨e, kxy, hkxy, ?_⟩
  have hnotLe : ¬ kxy ≤ 6 * m - 1 := by
    intro hle
    apply hwNot
    apply (mem_compressibleWords_iff V [] _ (6 * m - 1)).mpr
    change plainK V
      (pairCode (quadraticPointCode m e.1.1) (quadraticLineCode m e.1.2)) ≤
        (6 * m - 1 : Nat)
    rw [hkxy]
    exact_mod_cast hle
  omega

/-- Effective coding bounds still required from a uniform coordinate model of
the quadratic fields.  This is the executable-content leaf of Exercise 311:
an incident pair has a `6m + O(1)` joint description, and either endpoint has a
`2m + O(1)` conditional description from the other. -/
theorem quadraticIncident_coding_bounds
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ m (p : Point (ConcreteQuadraticField m))
      (ell : Line (ConcreteQuadraticField m)),
      Incident p ell →
      let x := quadraticPointCode m p
      let y := quadraticLineCode m ell
      pairPlainK V x y ≤ ((6 * (m + 1) + c : Nat) : ENat) ∧
      condK V y x ≤ ((2 * (m + 1) + c : Nat) : ENat) ∧
      condK V x y ≤ ((2 * (m + 1) + c : Nat) : ENat) := by
  obtain ⟨cPair, hPair⟩ := pairPlainK_quadraticIncident_le V hV
  obtain ⟨cPoint, hPoint⟩ := condK_quadraticPoint_given_line_le V hV
  obtain ⟨cLine, hLine⟩ := condK_quadraticLine_given_point_le V hV
  refine ⟨cPair + cPoint + cLine, fun m p ell hinc => ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (hPair m p ell hinc).trans (by exact_mod_cast Nat.add_le_add_left (by omega) _)
  · exact (hLine m p ell hinc).trans (by exact_mod_cast Nat.add_le_add_left (by omega) _)
  · exact (hPoint m p ell hinc).trans (by exact_mod_cast Nat.add_le_add_left (by omega) _)

/-- Effective class-key coding for Exercise 311.  The class key `(r, t, s)` of
an incident pair is described by `3 * (m + 1)` bits, and each endpoint is
recovered from the key together with `2 * (m + 1)` further bits. -/
theorem quadraticIncidenceClass_region_witness
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ m (p : Point (ConcreteQuadraticField m))
      (ell : Line (ConcreteQuadraticField m)),
      Incident p ell →
      let n := 2 * m
      commonInformationTripleInflate (logSlack c n) (3 * n / 2, n, n) ∈
        CommonInformationRegion V (quadraticPointCode m p) (quadraticLineCode m ell) := by
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
  obtain ⟨cPoint, hPoint⟩ := condK_quadraticPoint_given_classKey_le V hV
  obtain ⟨cLine, hLine⟩ := condK_quadraticLine_given_classKey_le V hV
  refine ⟨cLength + cPoint + cLine + 4, ?_⟩
  intro m p ell hinc
  have hslack : ∀ k : Nat, cLength + cPoint + cLine + 4 ≤
      logSlack (cLength + cPoint + cLine + 4) k := by
    intro k
    unfold logSlack
    exact Nat.le_add_left _ _
  have hs := hslack (2 * m)
  refine ⟨quadClassKeyOf m p ell, ?_, ?_, ?_⟩
  · have hkey : plainK V (quadClassKeyOf m p ell) ≤ ((3 * (m + 1) + cLength : Nat) : ENat) := by
      have h := hLength (quadClassKeyOf m p ell)
      simp only [programLength, quadClassKeyOf_length] at h
      exact_mod_cast h
    refine lt_of_le_of_lt hkey ?_
    have hnat : 3 * (m + 1) + cLength <
        3 * (2 * m) / 2 + logSlack (cLength + cPoint + cLine + 4) (2 * m) := by omega
    exact_mod_cast hnat
  · refine lt_of_le_of_lt (hPoint m p ell hinc) ?_
    have hnat : 2 * (m + 1) + cPoint <
        2 * m + logSlack (cLength + cPoint + cLine + 4) (2 * m) := by omega
    exact_mod_cast hnat
  · refine lt_of_le_of_lt (hLine m p ell) ?_
    have hnat : 2 * (m + 1) + cLine <
        2 * m + logSlack (cLength + cPoint + cLine + 4) (2 * m) := by omega
    exact_mod_cast hnat

/--
Exercise 311:
By considering the incidence graph over the quadratic extension `GF(q^2)`,
every high-complexity incident point `x` and line `y` has unconditional
complexity `~2n`, pair complexity `~3n`, and mutual information `~n`, and its
common-information region contains the point `(1.5n, n, n)` to logarithmic
precision.
Here, `n = 2m` where `m` is the parameter of the base field `GF(q)`.
-/
theorem exercise_311_region_witness
    (V : Map) (hV : isOptimalConditional V) :
    ∀ d, ∃ C, ∀ m (p : Point (ConcreteQuadraticField m))
      (ell : Line (ConcreteQuadraticField m)) kxy,
        Incident p ell →
        let n := 2 * m
        let x := quadraticPointCode m p
        let y := quadraticLineCode m ell
        HasPlainComplexityValue V (pairCode x y) kxy →
        3 * n ≤ kxy + logSlack d n →
        ∃ kx ky,
        x.length = 4 * (m + 1) ∧
        y.length = 4 * (m + 1) ∧
        HasPlainComplexityValue V (pairCode x y) kxy ∧
        HasPlainComplexityValue V x kx ∧
        HasPlainComplexityValue V y ky ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        MutualInformationWithin V x y n (logSlack C n) ∧
        commonInformationTripleInflate (logSlack C n) (3 * n / 2, n, n) ∈
          CommonInformationRegion V x y :=
  by
    obtain ⟨cCodec, hCodec⟩ := quadraticIncident_coding_bounds V hV
    obtain ⟨cRegion, hRegion⟩ := quadraticIncidenceClass_region_witness V hV
    obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
    obtain ⟨cChain, hChain⟩ := pairPlainK_chain_upper_values V hV
    obtain ⟨cSwap, hSwap⟩ := pairPlainK_swap_values_close V hV
    obtain ⟨cFold, hFold⟩ :=
      logSlack_linear_bound cChain 3 (cCodec + cSwap + 7)
    intro d
    let K := cLength + cCodec + cRegion + cSwap + 10
    let D := d + cFold + K
    let C := 3 * D
    refine ⟨C, ?_⟩
    intro m p ell kxy hinc
    dsimp only
    intro hkxy hHigh
    let n := 2 * m
    let x := quadraticPointCode m p
    let y := quadraticLineCode m ell
    have hHighN : 3 * n ≤ kxy + logSlack d n := by
      simpa only [n] using hHigh
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
    have hCodec' := hCodec m p ell hinc
    have hPair := hCodec'.1
    have hLine := hCodec'.2.1
    have hPoint := hCodec'.2.2
    have hkxUpper : kx ≤ 2 * n + 4 + cLength := by
      have h := hLength x
      rw [hx] at h
      have hxLength : x.length = 4 * (m + 1) := by
        simp only [x, quadraticPointCode_length]
      change (kx : ENat) ≤ (x.length : ENat) + (cLength : ENat) at h
      rw [hxLength] at h
      have hnat : kx ≤ 4 * (m + 1) + cLength := by exact_mod_cast h
      dsimp only [n]
      omega
    have hkyUpper : ky ≤ 2 * n + 4 + cLength := by
      have h := hLength y
      rw [hy] at h
      have hyLength : y.length = 4 * (m + 1) := by
        simp only [y, quadraticLineCode_length]
      change (ky : ENat) ≤ (y.length : ENat) + (cLength : ENat) at h
      rw [hyLength] at h
      have hnat : ky ≤ 4 * (m + 1) + cLength := by exact_mod_cast h
      dsimp only [n]
      omega
    have hkxyUpper : kxy ≤ 3 * n + 6 + cCodec := by
      change pairPlainK V x y ≤ ((6 * (m + 1) + cCodec : Nat) : ENat) at hPair
      rw [pairPlainK, hxy] at hPair
      have h : kxy ≤ 6 * (m + 1) + cCodec := by exact_mod_cast hPair
      dsimp only [n]
      omega
    have hyxCondUpper : kyxCond ≤ n + 2 + cCodec := by
      change condK V y x ≤ ((2 * (m + 1) + cCodec : Nat) : ENat) at hLine
      rw [hyxCond] at hLine
      have h : kyxCond ≤ 2 * (m + 1) + cCodec := by exact_mod_cast hLine
      dsimp only [n]
      omega
    have hxyCondUpper : kxyCond ≤ n + 2 + cCodec := by
      change condK V x y ≤ ((2 * (m + 1) + cCodec : Nat) : ENat) at hPoint
      rw [hxyCond] at hPoint
      have h : kxyCond ≤ 2 * (m + 1) + cCodec := by exact_mod_cast hPoint
      dsimp only [n]
      omega
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
    have hkxyArg : kxy + 1 ≤ 3 * n + (cCodec + cSwap + 7) := by
      omega
    have hkSwapArg : kSwap + 1 ≤ 3 * n + (cCodec + cSwap + 7) := by
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
    have hMID : MutualInformationWithin V x y n (3 * logSlack D n) :=
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
    have hcRegionC : cRegion ≤ C := by
      dsimp only [C, D, K]
      omega
    have hRegionSlack : logSlack cRegion n ≤ logSlack C n :=
      logSlack_mono_left hcRegionC n
    have hRegionBase :
        commonInformationTripleInflate (logSlack cRegion n) (3 * n / 2, n, n) ∈
          CommonInformationRegion V x y := by
      simpa only [n, x, y] using hRegion m p ell hinc
    have hInflateMono := commonInformationTripleInflate_mono hRegionSlack (3 * n / 2, n, n)
    have hRegionFinal :
        commonInformationTripleInflate (logSlack C n) (3 * n / 2, n, n) ∈
          CommonInformationRegion V x y :=
      commonInformationRegion_upward_closed hInflateMono.1 hInflateMono.2.1
        hInflateMono.2.2 hRegionBase
    refine ⟨kx, ky, quadraticPointCode_length m p, quadraticLineCode_length m ell,
      hxy, hx, hy, hxyCloseD.mono hSlackMono, hxCloseD.mono hSlackMono,
      hyCloseD.mono hSlackMono, hMI, ?_⟩
    simpa only [n, x, y] using hRegionFinal

end Kolmogorov
