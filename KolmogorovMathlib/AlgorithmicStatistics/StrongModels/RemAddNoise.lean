import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseProduct
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseFibres
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Support
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseLowBranch
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FullCube

/-!
# The ordinary-profile add-noise transformation

This file records the source-facing transformation used by VS40
`rem:add-noise`.  Its first (uniform-extension) branch is proved here, and so
is the reverse inclusion: its high-coordinate half-plane branch, and both the
small-gap and the projection parts of its low-coordinate branch.  No transport
or purification assumption is used.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The profile transformation from VS40 `rem:add-noise`.  Below the base
complexity `kx`, a model of `x` is extended by every noise string of length
`l`.  Above `kx`, the transformation contains the sufficiency half-plane of
the pair, whose plain complexity is `kxy`. -/
def AddNoiseProfileTransform
    (P : Set (Nat × Nat)) (kx kxy l : Nat) : Set (Nat × Nat) :=
  {q | (∃ i j, i ≤ kx ∧ (i, j) ∈ P ∧ q = (i, j + l)) ∨
    (kx < q.1 ∧ kxy ≤ q.1 + q.2)}

theorem addNoiseProfileTransform_base_mem
    {P : Set (Nat × Nat)} {kx kxy l i j : Nat}
    (hi : i ≤ kx) (hij : (i, j) ∈ P) :
    (i, j + l) ∈ AddNoiseProfileTransform P kx kxy l := by
  exact Or.inl ⟨i, j, hi, hij, rfl⟩

/-- Source-facing interface for VS40 `rem:add-noise`.  Conditional randomness
of `y` over `x`, with loss `epsilon`, makes the ordinary plain profile of the
canonical pair `O(epsilon + log (|x|+|y|))`-close to the displayed source
transformation.  The exact natural witnesses `kx` and `kxy` avoid silently
coercing a potentially infinite complexity. -/
def RemAddNoiseStatement (V : Map) : Prop :=
  ∃ c : Nat, ∀ (x y : BitString) (epsilon kx kxy : Nat),
    plainK V x = (kx : ENat) →
    plainK V (pairCode x y) = (kxy : ENat) →
    (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
    ProfileSetsWithinNeighborhood
      (plainDescriptionProfileSet V (pairCode x y))
      (AddNoiseProfileTransform
        (plainDescriptionProfileSet V x) kx kxy y.length)
      (c * epsilon + logSlack c (x.length + y.length))

/-- The unconditional uniform-extension branch of `rem:add-noise`: every
ordinary plain `(i,j)` model of `x` yields an
`(i + O(log |y|), j + |y|)` model of `pairCode x y`. -/
theorem inPlainDescriptionProfile_pair_of_base
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x y : BitString) (i j : Nat),
      InPlainDescriptionProfile V x i j →
      InPlainDescriptionProfile V (pairCode x y)
        (i + logSlack c y.length) (j + y.length) := by
  obtain ⟨c, hc⟩ :=
    finiteSetPairUniformExtension_plainSetComplexity_le V hV
  refine ⟨c, ?_⟩
  rintro x y i j ⟨A, hA, hxA, hcomplexity, hcard⟩
  let hExt : (finiteSetPairUniformExtension A y.length).Nonempty :=
    finiteSetPairUniformExtension_nonempty hA y.length
  refine ⟨finiteSetPairUniformExtension A y.length, hExt,
    finiteSetPairUniformExtension_mem hxA rfl, ?_, ?_⟩
  · calc
      plainSetComplexity V (finiteSetPairUniformExtension A y.length) hExt
          ≤ plainSetComplexity V A hA + logSlack c y.length :=
        hc A hA y.length
      _ ≤ (i : ENat) + (logSlack c y.length : ENat) := by gcongr
      _ = ((i + logSlack c y.length : Nat) : ENat) := by norm_cast
  · rw [finiteSetPairUniformExtension_card]
    calc
      A.card * 2 ^ y.length ≤ 2 ^ j * 2 ^ y.length :=
        Nat.mul_le_mul_right (2 ^ y.length) hcard
      _ = 2 ^ (j + y.length) := by rw [pow_add]

/-- Arithmetic for the final neighborhood radius in `rem:add-noise`. -/
theorem addNoise_radius_arith (i k epsilon slack1 slack2 : Nat) (hk : k ≤ i) :
    i - (k - epsilon - slack1) + slack2 ≤
      i - k + epsilon + slack1 + slack2 := by
  omega

/-- A stable ENat/Nat case split producing either the target coordinate or an
exact gain inequality. -/
theorem truncation_or_exact_gain (V : Map) (x y A_code : BitString) (k0 : Nat) :
    (y.length : ENat) ≤ condK V y (pairCode x A_code) + (k0 : ENat) ∨
    ∃ k : Nat, condK V y (pairCode x A_code) + (k : ENat) ≤ (y.length : ENat) ∧
      k0 < k := by
  by_cases h : (y.length : ENat) ≤ condK V y (pairCode x A_code) + (k0 : ENat)
  · exact Or.inl h
  · refine Or.inr ?_
    push_neg at h
    -- `h : condK V y (pairCode x A_code) + k0 < y.length`.  Since the RHS is a
    -- finite `Nat` coercion, the conditional complexity `C` is finite; write
    -- `C = c` and take the exact gain `k = |y| - c`.
    set C := condK V y (pairCode x A_code) with hC
    have hCne : C ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at h
      exact absurd h (not_top_lt)
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hCne
    rw [← hc, ← Nat.cast_add] at h
    have hlt : c + k0 < y.length := by exact_mod_cast h
    refine ⟨y.length - c, ?_, ?_⟩
    · rw [← hc, ← Nat.cast_add]
      exact_mod_cast (by omega : c + (y.length - c) ≤ y.length)
    · omega

/-- Bookkeeping in the shape required by `ImprovingDescriptionsComplexityLogSlack`. -/
theorem clamped_gain_le_complexity_budget (k i c0 : Nat) :
    min k (i + c0) ≤ i + c0 := by
  exact Nat.min_le_right k (i + c0)


/-- **High-coordinate branch of the reverse inclusion of `rem:add-noise`.**
If `(i, j)` is an ordinary plain model of the pair whose complexity coordinate
already exceeds `C(x)`, then the sufficiency half-plane of the source
transformation contains a point at distance `O(log (|x| + |y|))` from `(i, j)`.
No randomness hypothesis is needed for this branch. -/
theorem pairProfile_high_coordinate_to_transform
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x y : BitString) (kx kxy i j : Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) = (kxy : ENat) →
      kx < i →
      InPlainDescriptionProfile V (pairCode x y) i j →
      ∃ q' ∈ AddNoiseProfileTransform
          (plainDescriptionProfileSet V x) kx kxy y.length,
        natPairLInfDistance (i, j) q' ≤
          logSlack c (x.length + y.length) := by
  obtain ⟨c0, hc0⟩ := plainK_mem_le_of_plainSetComplexity_le V hV
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨C, hC⟩ := logSlack_linear_bound 2 2 (1 + cLen)
  refine ⟨C + c0, ?_⟩
  intro x y kx kxy i j _hkx hkxy hlow hprof
  by_cases hcase : kxy ≤ i + j
  · refine ⟨(i, j), Or.inr ⟨hlow, hcase⟩, ?_⟩
    simp [natPairLInfDistance]
  · obtain ⟨S, hS, hmem, hcompl, hcard⟩ := hprof
    have hlogcard : finiteSetLogCard S ≤ j :=
      (finiteSetLogCard_le_iff S j).mpr hcard
    have hbound :
        kxy ≤ i + finiteSetLogCard S + 2 * (Nat.bits i).length + c0 := by
      have h := hc0 S hS (pairCode x y) i hmem hcompl
      rw [hkxy] at h
      exact_mod_cast h
    have hkxyLen : kxy ≤ 2 * (x.length + y.length) + (1 + cLen) := by
      have h := hLen (pairCode x y)
      rw [hkxy] at h
      have h' : kxy ≤ (pairCode x y).length + cLen := by exact_mod_cast h
      rw [length_pairCode] at h'
      omega
    have hbits : 2 * (Nat.bits i).length ≤
        2 * (Nat.bits (2 * (x.length + y.length) + (1 + cLen))).length :=
      Nat.mul_le_mul_left 2 (length_natBits_mono (by omega))
    have hslack :
        logSlack 2 (2 * (x.length + y.length) + (1 + cLen)) ≤
          logSlack C (x.length + y.length) := hC _
    have habsorb : logSlack C (x.length + y.length) + c0 ≤
        logSlack (C + c0) (x.length + y.length) :=
      logSlack_add_const_le C c0 _
    have h2 : logSlack 2 (2 * (x.length + y.length) + (1 + cLen)) =
        2 * (Nat.bits (2 * (x.length + y.length) + (1 + cLen))).length + 2 := by
      unfold logSlack; ring
    refine ⟨(i, kxy - i), Or.inr ⟨hlow, by omega⟩, ?_⟩
    unfold natPairLInfDistance
    simp only
    omega

/-- **Prefix packaging of an ordinary plain model of the pair.**  The
plain-to-prefix profile bridge turns an ordinary plain `(i, j)` model of
`pairCode x y` into a concrete member `B` of the finite description universe
`descriptionsWithComplexityLeAndSizeLe U (i + O(log i)) j` containing the pair.
This is the shape required by the add-noise multiplicity theorem. -/
theorem prefix_pair_model_of_plain_profile
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (i j : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      ∃ B : Finset BitString,
        B ∈ descriptionsWithComplexityLeAndSizeLe U (i + logSlack c i) j ∧
        pairCode x y ∈ B := by
  obtain ⟨c, hc⟩ := inDescriptionProfile_of_inPlainDescriptionProfile V U hV hU
  refine ⟨c, ?_⟩
  intro x y i j hprof
  obtain ⟨S, hS, hmem, hcomp, hcard⟩ := hc (pairCode x y) i j hprof
  refine ⟨S, ?_, hmem⟩
  rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
  exact ⟨mem_descriptionsWithComplexityLe_of_complexity hS hcomp, hcard⟩

/-- A two-line wrapper composing the two profile bridges with one combined constant. -/
theorem plain_prefix_roundtrip_shift
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ x i j,
      InPlainDescriptionProfile V x i j →
      InPlainDescriptionProfile V x (i + logSlack c i) j := by
  obtain ⟨c1, hc1⟩ := inDescriptionProfile_of_inPlainDescriptionProfile V U hV hU
  obtain ⟨c2, hc2⟩ := inPlainDescriptionProfile_of_inDescriptionProfile V U hV hU
  refine ⟨c1 + c2, fun x i j hprof => ?_⟩
  have h1 := hc1 x i j hprof
  have h2 := hc2 x (i + logSlack c1 i) j h1
  have h3 : i + logSlack c1 i + c2 ≤ i + logSlack (c1 + c2) i := by
    have h4 : logSlack c1 i + c2 ≤ logSlack (c1 + c2) i := logSlack_add_const_le c1 c2 i
    omega
  exact h2.mono_i h3

/-- **Small-gap part of the low-coordinate branch of `rem:add-noise`.**  For an
ordinary plain `(i, j)`-model of `pairCode x y` with `i ≤ C(x)`, the sufficiency
half-plane of the source transformation contains a point at distance at most
`(C(x) - i) + O(log (|x| + |y|))` from `(i, j)`. -/
theorem pairProfile_low_coordinate_to_transform_gap
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x y : BitString) (kx kxy i j : Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) = (kxy : ENat) →
      i ≤ kx →
      InPlainDescriptionProfile V (pairCode x y) i j →
      ∃ q' ∈ AddNoiseProfileTransform
          (plainDescriptionProfileSet V x) kx kxy y.length,
        natPairLInfDistance (i, j) q' ≤
          (kx - i) + logSlack c (x.length + y.length) := by
  obtain ⟨c0, hc0⟩ := plainK_mem_le_of_plainSetComplexity_le V hV
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨C, hC⟩ := logSlack_linear_bound 2 1 cLen
  refine ⟨C + c0 + 1, ?_⟩
  intro x y kx kxy i j hkx hkxy hle hprof
  obtain ⟨S, hS, hmem, hcompl, hcard⟩ := hprof
  -- Every `(i, j)`-model of the pair certifies `C(x, y) ≤ i + j + O(log i)`.
  have hlogcard : finiteSetLogCard S ≤ j :=
    (finiteSetLogCard_le_iff S j).mpr hcard
  have hbound : kxy ≤ i + j + 2 * (Nat.bits i).length + c0 := by
    have h := hc0 S hS (pairCode x y) i hmem hcompl
    rw [hkxy] at h
    have h' : kxy ≤ i + finiteSetLogCard S + 2 * (Nat.bits i).length + c0 := by
      exact_mod_cast h
    omega
  -- The complexity coordinate is bounded by `|x| + O(1)`, so its binary length
  -- is logarithmic in `|x| + |y|`.
  have hkxLen : kx ≤ x.length + cLen := by
    have h := hLen x
    rw [hkx] at h
    exact_mod_cast h
  have hbits : 2 * (Nat.bits i).length ≤
      2 * (Nat.bits (x.length + y.length + cLen)).length :=
    Nat.mul_le_mul_left 2 (length_natBits_mono (by omega))
  have hslack :
      logSlack 2 (1 * (x.length + y.length) + cLen) ≤
        logSlack C (x.length + y.length) := hC _
  have h2 : logSlack 2 (1 * (x.length + y.length) + cLen) =
      2 * (Nat.bits (x.length + y.length + cLen)).length + 2 := by
    unfold logSlack
    ring_nf
  have habsorb : logSlack C (x.length + y.length) + (c0 + 1) ≤
      logSlack (C + c0 + 1) (x.length + y.length) := by
    have h := logSlack_add_const_le C (c0 + 1) (x.length + y.length)
    have hmono : logSlack (C + (c0 + 1)) (x.length + y.length) ≤
        logSlack (C + c0 + 1) (x.length + y.length) :=
      logSlack_mono_left (c := C + (c0 + 1)) (c' := C + c0 + 1) (by omega) _
    omega
  refine ⟨(kx + 1, max j (kxy - (kx + 1))), Or.inr ⟨by omega, ?_⟩, ?_⟩
  · rcases le_total kxy (kx + 1 + j) with hcase | hcase
    · have : j ≤ max j (kxy - (kx + 1)) := le_max_left _ _
      omega
    · have : kxy - (kx + 1) ≤ max j (kxy - (kx + 1)) := le_max_right _ _
      omega
  · unfold natPairLInfDistance
    simp only
    rcases le_total (kxy - (kx + 1)) j with hcase | hcase
    · rw [max_eq_left hcase]
      omega
    · rw [max_eq_right hcase]
      omega

/-- **Low-coordinate branch of the reverse inclusion of `rem:add-noise`.**

Given an ordinary plain `(i, j)`-model `B` of `pairCode x y` whose complexity
coordinate satisfies `i ≤ C(x)`, with `y` conditionally `epsilon`-random given
`x`, this branch produces a point of `AddNoiseProfileTransform` at
`l∞`-distance `O(epsilon + log(|x|+|y|))` from `(i, j)`.

The proof splits into three regimes.

* If `C(x) - i` is already `O(epsilon + log)` — in particular whenever `C(x)`
  itself is logarithmically small — the sufficiency half-plane of the pair is
  close enough, which is `pairProfile_low_coordinate_to_transform_gap`.
* If `j ≥ |x| + |y|`, the full cube of length `|x|` is a model of `x` of
  complexity `O(log |x|)` and log-size `|x| ≤ j - |y|`, so the base part of the
  transformation contains `(max i (O(log |x|)), j)`.
* Otherwise `j < |x| + |y|` and `inPlainDescriptionProfile_fst_of_pair_model`
  projects `B` onto a model of `x` of complexity `i + epsilon + O(log)` and
  log-size `j - |y| + O(log)`; the corresponding base point of the
  transformation is `(i + epsilon + O(log), j - |y| + O(log) + |y|)`.  Plain
  symmetry of information for the pair (`plainK_pair_ge_plainK_add_length_of_random`)
  bounds `|y| - j` by `epsilon + O(log)`, so this point is close to `(i, j)`
  even when `|y|` exceeds `j`. -/
theorem pairProfile_low_coordinate_to_transform
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon kx kxy i j : Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) = (kxy : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      i ≤ kx →
      InPlainDescriptionProfile V (pairCode x y) i j →
      ∃ q' ∈ AddNoiseProfileTransform
        (plainDescriptionProfileSet V x) kx kxy y.length,
        natPairLInfDistance (i, j) q' ≤
          c * epsilon + logSlack c (x.length + y.length) := by
  obtain ⟨cGap, hcGap⟩ := pairProfile_low_coordinate_to_transform_gap V hV
  obtain ⟨cCube, hCube⟩ := plainSetComplexity_fullCube_le_logSlack V hV
  obtain ⟨cLow, hLow⟩ := inPlainDescriptionProfile_fst_of_pair_model V U hV hU
  obtain ⟨c0, hc0⟩ := plainK_mem_le_of_plainSetComplexity_le V hV
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cPair, hPair⟩ := plainK_pair_ge_plainK_add_length_of_random V U hV hU
  obtain ⟨cLow2, hcLow2⟩ := logSlack_linear_bound cLow 1 cLen
  obtain ⟨cBits, hcBits⟩ := logSlack_linear_bound 2 1 cLen
  refine ⟨cGap + cCube + cLow2 + cPair + cBits + c0 + 2, ?_⟩
  intro x y epsilon kx kxy i j hkx hkxy hcond hle hprof
  set c := cGap + cCube + cLow2 + cPair + cBits + c0 + 2 with hc
  set T := c * epsilon + logSlack c (x.length + y.length) with hT
  -- A single logarithmic budget absorbing every auxiliary constant.
  have hTbig : 2 * epsilon +
      (logSlack cGap (x.length + y.length) + logSlack cCube (x.length + y.length) +
        logSlack cLow2 (x.length + y.length) + logSlack cPair (x.length + y.length) +
        logSlack cBits (x.length + y.length) + c0) ≤ T := by
    have h1 : 2 * epsilon ≤ c * epsilon := Nat.mul_le_mul_right epsilon (by omega)
    have hsum : logSlack cGap (x.length + y.length) + logSlack cCube (x.length + y.length) +
        logSlack cLow2 (x.length + y.length) + logSlack cPair (x.length + y.length) +
        logSlack cBits (x.length + y.length)
        = logSlack (cGap + cCube + cLow2 + cPair + cBits) (x.length + y.length) := by
      simp only [logSlack_add_const]
    have h2 := logSlack_add_const_le (cGap + cCube + cLow2 + cPair + cBits) c0
      (x.length + y.length)
    have h3 : logSlack (cGap + cCube + cLow2 + cPair + cBits + c0) (x.length + y.length) ≤
        logSlack c (x.length + y.length) := logSlack_mono_left (by omega) _
    have h4 : logSlack cGap (x.length + y.length) + logSlack cCube (x.length + y.length) +
        logSlack cLow2 (x.length + y.length) + logSlack cPair (x.length + y.length) +
        logSlack cBits (x.length + y.length) + c0 ≤ logSlack c (x.length + y.length) := by
      omega
    rw [hT]
    omega
  -- The gap theorem, packaged as a fallback whenever `kx - i` is already small.
  have hfallback : ∀ M : Nat, kx - i ≤ M →
      M + logSlack cGap (x.length + y.length) ≤ T →
      ∃ q' ∈ AddNoiseProfileTransform
        (plainDescriptionProfileSet V x) kx kxy y.length,
        natPairLInfDistance (i, j) q' ≤ T := by
    intro M hM hMle
    obtain ⟨q', hq'mem, hq'dist⟩ := hcGap x y kx kxy i j hkx hkxy hle hprof
    exact ⟨q', hq'mem, by omega⟩
  have hkxLen : kx ≤ x.length + cLen := by
    have h := hLen x
    rw [hkx] at h
    exact_mod_cast h
  by_cases hbig : x.length + y.length ≤ j
  · -- Large log-size: the full cube of length `|x|` already is a model of `x`
    -- of log-size at most `j - |y|`.
    by_cases hcube : logSlack cCube x.length ≤ kx
    · have hCubeSlack : logSlack cCube x.length ≤ logSlack cCube (x.length + y.length) :=
        logSlack_mono_right _ (by omega)
      refine ⟨(max i (logSlack cCube x.length), (j - y.length) + y.length),
        addNoiseProfileTransform_base_mem (max_le hle hcube) ?_, ?_⟩
      · have hfull : InPlainDescriptionProfile V x (logSlack cCube x.length) x.length := by
          refine ⟨stringsOfLength x.length, codedStringsOfLength_nonempty x.length,
            (memStringsOfLength x.length x).mpr rfl, hCube x.length, ?_⟩
          rw [cardStringsOfLength]
        exact (hfull.mono_i (le_max_right _ _)).mono_j (by omega)
      · unfold natPairLInfDistance
        simp only
        refine max_le ?_ ?_
        · rcases le_total i (logSlack cCube x.length) with h | h
          · rw [max_eq_right h]; omega
          · rw [max_eq_left h]; omega
        · omega
    · have hCubeSlack : logSlack cCube x.length ≤ logSlack cCube (x.length + y.length) :=
        logSlack_mono_right _ (by omega)
      exact hfallback kx (by omega) (by omega)
  · -- Small log-size: project the pair model onto its first coordinate.
    have hs : logSlack cLow (x.length + y.length + cLen) ≤
        logSlack cLow2 (x.length + y.length) := by
      have h := hcLow2 (x.length + y.length)
      rwa [Nat.one_mul] at h
    have hprofx := hLow x y epsilon i j (x.length + y.length + cLen) hprof hcond
      (by omega) (by omega) (by omega)
    -- `|y|` cannot exceed `j` by much: this is where conditional randomness
    -- of the noise is used quantitatively.
    have hkxyle : kxy ≤ i + j + 2 * (Nat.bits i).length + c0 := by
      obtain ⟨S, hS, hmem, hcompl, hcard⟩ := hprof
      have hlogcard : finiteSetLogCard S ≤ j := (finiteSetLogCard_le_iff S j).mpr hcard
      have h := hc0 S hS (pairCode x y) i hmem hcompl
      rw [hkxy] at h
      have h' : kxy ≤ i + finiteSetLogCard S + 2 * (Nat.bits i).length + c0 := by
        exact_mod_cast h
      omega
    have hpair : kx + y.length ≤
        kxy + epsilon + logSlack cPair (x.length + y.length) :=
      hPair x y epsilon kx kxy hkx hkxy hcond
    have hbits : 2 * (Nat.bits i).length ≤ logSlack cBits (x.length + y.length) := by
      have h2 : logSlack 2 (1 * (x.length + y.length) + cLen) ≤
          logSlack cBits (x.length + y.length) := hcBits _
      have h3 : logSlack 2 (1 * (x.length + y.length) + cLen) =
          2 * (Nat.bits (x.length + y.length + cLen)).length + 2 := by
        unfold logSlack
        ring_nf
      have h4 : (Nat.bits i).length ≤ (Nat.bits (x.length + y.length + cLen)).length :=
        length_natBits_mono (by omega)
      omega
    have hlj : y.length ≤ j + epsilon + logSlack cBits (x.length + y.length) + c0 +
        logSlack cPair (x.length + y.length) := by omega
    by_cases hi1 : i + epsilon + logSlack cLow (x.length + y.length + cLen) ≤ kx
    · refine ⟨(i + epsilon + logSlack cLow (x.length + y.length + cLen),
        (j - y.length + logSlack cLow (x.length + y.length + cLen)) + y.length),
        addNoiseProfileTransform_base_mem hi1 hprofx, ?_⟩
      unfold natPairLInfDistance
      simp only
      exact max_le (by omega) (by omega)
    · exact hfallback (epsilon + logSlack cLow (x.length + y.length + cLen))
        (by omega) (by omega)

/-- Reverse inclusion of VS40 `rem:add-noise`, assembled from its
high-coordinate (sufficiency half-plane) and low-coordinate
(truncation/multiplicity) branches. -/
theorem pairProfile_to_addNoiseProfileTransform
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon kx kxy : Nat) (q : Nat × Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) = (kxy : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      q ∈ plainDescriptionProfileSet V (pairCode x y) →
      ∃ q' ∈ AddNoiseProfileTransform
        (plainDescriptionProfileSet V x) kx kxy y.length,
        natPairLInfDistance q q' ≤
          c * epsilon + logSlack c (x.length + y.length) := by
  obtain ⟨cHigh, hHigh⟩ := pairProfile_high_coordinate_to_transform V hV
  obtain ⟨cLow, hLow⟩ := pairProfile_low_coordinate_to_transform V U hV hU
  refine ⟨cHigh + cLow, ?_⟩
  intro x y epsilon kx kxy q hkx hkxy hrandom hq
  have hslackHigh : logSlack cHigh (x.length + y.length) ≤
      logSlack (cHigh + cLow) (x.length + y.length) :=
    logSlack_mono_left (by omega) _
  have hslackLow : logSlack cLow (x.length + y.length) ≤
      logSlack (cHigh + cLow) (x.length + y.length) :=
    logSlack_mono_left (by omega) _
  have hepsLow : cLow * epsilon ≤ (cHigh + cLow) * epsilon :=
    Nat.mul_le_mul_right epsilon (by omega)
  have hprofile : InPlainDescriptionProfile V (pairCode x y) q.1 q.2 := hq
  rcases lt_or_ge kx q.1 with hcase | hcase
  · obtain ⟨q', hq', hdist⟩ :=
      hHigh x y kx kxy q.1 q.2 hkx hkxy hcase hprofile
    exact ⟨q', hq', by simpa using hdist.trans (by omega)⟩
  · obtain ⟨q', hq', hdist⟩ :=
      hLow x y epsilon kx kxy q.1 q.2 hkx hkxy hrandom hcase hprofile
    exact ⟨q', hq', by simpa using hdist.trans (by omega)⟩

end Kolmogorov
