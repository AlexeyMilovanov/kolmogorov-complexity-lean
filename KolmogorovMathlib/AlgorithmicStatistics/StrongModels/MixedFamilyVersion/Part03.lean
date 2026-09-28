import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MixedFamilyRun
import KolmogorovMathlib.Restricted.FamilyCurve
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MixedFamilyVersion.Part02

/-!
# Joint restricted-curve realization

`prop_family_curve_against`: rebuilding in `𝒢` while excluding the bad descriptions of `ℬ`
realizes the target curve in both families at once.  This is the mixed-family form of
`prop_family_curve`, and the statement the joint realization of `JointRealization` rests on.

The assembly uses the run of `Part01` and the counting of `Part02`:
`restrictedAnchoredState_model_complexity_against` bounds the complexity of a terminal sampled
model through its version code, `exists_restricted_coupled_output_against_complexity` bounds
the set complexity of every good set along the path, and
`exists_restricted_coupled_output_against_candidate` bounds the prefix complexity of a
surviving candidate, with the two `O(1)` coding facts bundled as `UniformCodingConstants`.
`exists_restricted_coupled_output_against` puts them together.
-/

namespace Kolmogorov
open Nat.Partrec (Code)

/-- Every terminal sampled model in a mixed run has a version-coded
description whose overhead is controlled solely by the good family. -/
theorem restrictedAnchoredState_model_complexity_against
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒢 ℬ : DescriptionFamily) (hPoly : 𝒢.HasPolynomialOverhead)
    (c : Code) (_hc : IsCodeFor c U) :
    ∃ c_ver : ℕ, ∀ {n k N : ℕ} {t : ℕ → ℕ}
      (grid : RestrictedCurveGrid n k N t)
      (_hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
      (_hkn : k ≤ n) (_ht0 : t 0 ≤ n)
      (_hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i)
      (T : ℕ) (output : BitString)
      (state : RestrictedSampledRunState 𝒢 (N + 1)
          (n + logSlack 8 n)
          (2 * 𝒢.overhead (n + logSlack 8 n))
          (restrictedAnchoredTarget (n + logSlack 8 n)
            (sqrtSlack 8 n) grid)),
      restrictedEffectiveAnchoredSampledRunAgainst 𝒢 ℬ c
          (n + logSlack 8 n) (sqrtSlack 8 n) grid (T + 1) =
            Part.some output →
      DecodesToRestrictedSampledRunState output state →
      ∀ s (_hs : s ≤ N) (hS : (state.B (s + 1)).Nonempty),
        setComplexity U (state.B (s + 1)) hS ≤
          (grid.i s + sqrtSlack c_ver n +
            KPPlain U (restrictedCurveGridCode grid) : ENat) := by
  classical
  obtain ⟨c_F, hF⟩ := KPPlain_partrec_map_le U hU
    (anchoredVersionDecoderAgainst 𝒢 ℬ c)
    (anchoredVersionDecoderAgainst_partrec 𝒢 ℬ c)
  obtain ⟨c_L, hLc⟩ := KPPlain_listCode_le U hU
  obtain ⟨c_lg, hlg⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c_P, hPex⟩ := anchoredVersionExp_le_sqrtSlack 𝒢 hPoly
  obtain ⟨c_over, hover⟩ := 𝒢.overhead_bits_le_logSlack hPoly
  set c_ver := c_P + 15 * c_over + 3 * c_lg + 5 * c_L + c_F +
    2 * Nat.size (c_P + 1) + 40 with hc_ver
  refine ⟨c_ver, ?_⟩
  intro n k N t grid hN hkn ht0 hstrict T output state hrun hdec
    s hs hS
  obtain ⟨chain, codes, hfold, _hbads, _hB0, _hlive0, hcount⟩ :=
    exists_restrictedAnchoredEventChain_with_count_against 𝒢 ℬ c grid
      hN hkn ht0 hstrict T
  have hboundary :=
    restrictedEffectiveAnchoredSampledRunAgainst_eq_eventPrefix
      𝒢 ℬ c (n + logSlack 8 n) (sqrtSlack 8 n) grid (le_refl T)
  have hout :
      output = codes ((restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) ℬ.toPre N
        (sqrtSlack 8 n) T).length) := by
    rw [hboundary] at hrun
    exact Part.some_injective (hrun.symm.trans (hfold _).1)
  have hdec' :
      DecodesToRestrictedSampledRunState
        (codes ((restrictedSampledBadCodeStream c
          (restrictedCurveGridCode grid) ℬ.toPre N
          (sqrtSlack 8 n) T).length)) state :=
    hout ▸ hdec
  have hBeq := decodesTo_eq_B_live hdec'
    ((hfold ((restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) ℬ.toPre N
      (sqrtSlack 8 n) T).length)).2) (s := s + 1) (by omega)
  have hS' :
      ((chain.states ((restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) ℬ.toPre N
        (sqrtSlack 8 n) T).length)).B (s + 1)).Nonempty := by
    rw [← hBeq.1]
    exact hS
  obtain ⟨v, hvle, heval⟩ :=
    anchoredVersionDecoderAgainst_terminal 𝒢 ℬ c grid hN T
      chain codes hfold s hs hS'
  have hv2 :
      v ≤ 2 ^ (grid.i s + anchoredVersionExp 𝒢 n N) :=
    hvle.trans (hcount s hs)
  have hmem :
      (codedUniformOn ((chain.states
        ((restrictedSampledBadCodeStream c
          (restrictedCurveGridCode grid) ℬ.toPre N
          (sqrtSlack 8 n) T).length)).B (s + 1)) hS').code ∈
        anchoredVersionDecoderAgainst 𝒢 ℬ c
          (listCode [restrictedCurveGridCode grid,
            Nat.bits (𝒢.overhead (n + logSlack 8 n)),
            Nat.bits s, Nat.bits v]) := by
    rw [heval]
    exact Part.mem_some_iff.mpr rfl
  have hKP1 := hF _ _ hmem
  have hKP2 := hLc [restrictedCurveGridCode grid,
    Nat.bits (𝒢.overhead (n + logSlack 8 n)), Nat.bits s, Nat.bits v]
  have hq0c := KPPlain_le_selfDelimitedCost hlg (Nat.bits (𝒢.overhead (n + logSlack 8 n)))
  have hsc := KPPlain_le_selfDelimitedCost hlg (Nat.bits s)
  have hvc := KPPlain_le_selfDelimitedCost hlg (Nat.bits v)
  have hNat :=
    decoderBundleFieldCost_le 𝒢 grid hN hkn hover
      (hPex n N hN) hs hv2 c_lg c_L c_F
  rw [setComplexity_eq_KPPlain_codedUniformOn U hS hS' hBeq.1]
  have hbound_calc := KPPlain_le_grid_add_bundleCost
    U (restrictedCurveGridCode grid)
    (Nat.bits (𝒢.overhead (n + logSlack 8 n))) (Nat.bits s) (Nat.bits v)
    ((codedUniformOn ((chain.states
      ((restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) ℬ.toPre N
        (sqrtSlack 8 n) T).length)).B (s + 1)) hS').code)
    c_lg c_L c_F
    (grid.i s + sqrtSlack c_ver n)
    hKP1 hKP2 hq0c hsc hvc hNat
  have hcomm :
    KPPlain U (restrictedCurveGridCode grid) +
        ((grid.i s + sqrtSlack c_ver n : ℕ) : ENat) =
      (grid.i s + sqrtSlack c_ver n +
        KPPlain U (restrictedCurveGridCode grid) : ENat) := add_comm _ _
  exact hbound_calc.trans hcomm.le

private lemma exists_codeFor_map (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Code, IsCodeFor c U :=
  Nat.Partrec.Code.exists_code.mp hU.isDecompressor

/-- The set complexity of every good set `state.B (s + 1)` along the path is at most
`grid.i s + sqrtSlack cfin n`, once the grid code itself costs at most `sqrtSlack c_grid n`. -/
private lemma exists_restricted_coupled_output_against_complexity
    {𝒢 : DescriptionFamily} {U : Map} {n k N c_grid c_ver : ℕ} {t : ℕ → ℕ}
    {grid : RestrictedCurveGrid n k N t} {cfin : ℕ}
    {state : RestrictedSampledRunState 𝒢 (N + 1) (n + logSlack 8 n)
      (2 * 𝒢.overhead (n + logSlack 8 n))
      (restrictedAnchoredTarget (n + logSlack 8 n) (sqrtSlack 8 n) grid)}
    (hbound : ∀ s (_hs : s ≤ N) (hS : (state.B (s + 1)).Nonempty),
      setComplexity U (state.B (s + 1)) hS ≤ (grid.i s + sqrtSlack c_ver n +
        KPPlain U (restrictedCurveGridCode grid) : ENat))
    (hgrid : KPPlain U (restrictedCurveGridCode grid) ≤ (sqrtSlack c_grid n : ENat))
    (hslack_le : sqrtSlack (c_grid + c_ver) n ≤ sqrtSlack cfin n) :
    ∀ s (_hs : s ≤ N) (hS : (state.B (s + 1)).Nonempty),
      setComplexity U (state.B (s + 1)) hS ≤ (grid.i s + sqrtSlack cfin n : ENat) := by
  intro s hs hS
  have hraw := hbound s hs hS
  calc
    setComplexity U (state.B (s + 1)) hS
        ≤ (grid.i s + sqrtSlack c_ver n : ENat) + KPPlain U (restrictedCurveGridCode grid) := by
          exact_mod_cast hraw
    _ ≤ (grid.i s + sqrtSlack c_ver n : ENat) + sqrtSlack c_grid n := by gcongr
    _ = (grid.i s : ENat) + ((sqrtSlack c_ver n : ENat) + sqrtSlack c_grid n) := by ac_rfl
    _ = (grid.i s : ENat) + (sqrtSlack (c_grid + c_ver) n : ENat) := by
          exact_mod_cast (show grid.i s + (sqrtSlack c_ver n + sqrtSlack c_grid n) =
            grid.i s + sqrtSlack (c_grid + c_ver) n by rw [← sqrtSlack_add c_grid c_ver n]; omega)
    _ ≤ (grid.i s + sqrtSlack cfin n : ENat) := by
          exact_mod_cast Nat.add_le_add_left hslack_le (grid.i s)

/-- The two `O(1)` coding facts for uniformly coded sets that the candidate bound uses: plain
prefix complexity is bounded by two-part coding through the set, and the index of an element
inside the uniform code of the set costs the bits of its cardinality plus a constant. -/
structure UniformCodingConstants (U : Map) (c_two c_idx : ℕ) : Prop where
  /-- Two-part coding through a uniformly coded set. -/
  two_part : ∀ (S : Finset BitString) (hS : S.Nonempty) (x : BitString), x ∈ S →
    KPPlain U x ≤ setComplexity U S hS + KP U x (codedUniformOn S hS).code + (c_two : ENat)
  /-- The index of an element inside the uniform code of the set. -/
  index_le : ∀ (S : Finset BitString) (hS : S.Nonempty) (x : BitString), x ∈ S →
    KP U x (codedUniformOn S hS).code ≤ (((Nat.bits S.card).length + c_idx : ℕ) : ENat)

/-- Every string still live at stage `N + 1` has prefix complexity at most
`k + sqrtSlack cfin n`, by describing it inside its good set (two-part coding plus index). -/
private lemma exists_restricted_coupled_output_against_candidate
    {𝒢 : DescriptionFamily} {U : Map}
    {n k N c_grid c_ver c_two c_idx cfin : ℕ} {t : ℕ → ℕ}
    {grid : RestrictedCurveGrid n k N t} {state : RestrictedAnchoredState 𝒢 grid}
    (hconst : UniformCodingConstants U c_two c_idx)
    (hbound : ∀ s (_hs : s ≤ N) (hS : (state.B (s + 1)).Nonempty),
      setComplexity U (state.B (s + 1)) hS ≤ (grid.i s + sqrtSlack c_ver n +
        KPPlain U (restrictedCurveGridCode grid) : ENat))
    (hgrid : KPPlain U (restrictedCurveGridCode grid) ≤ (sqrtSlack c_grid n : ENat))
    (hcfin : cfin = c_grid + 8 + (c_ver + c_two + c_idx + 9)) :
    ∀ x ∈ state.live (N + 1), KPPlain U x ≤ (k + sqrtSlack cfin n : ENat) := by
  obtain ⟨htwo, hidx⟩ := hconst
  intro x hx
  have hxB : x ∈ state.B (N + 1) := state.live_subset (N + 1) le_rfl hx
  have hSne : (state.B (N + 1)).Nonempty := ⟨x, hxB⟩
  have hsetC : setComplexity U (state.B (N + 1)) hSne ≤
      ((k + sqrtSlack (c_grid + c_ver) n : ℕ) : ENat) := by
    have h := hbound N le_rfl hSne
    rw [grid.i_end] at h
    calc
      setComplexity U (state.B (N + 1)) hSne
          ≤ (k + sqrtSlack c_ver n : ENat) + KPPlain U (restrictedCurveGridCode grid) := by
            exact_mod_cast h
      _ ≤ (k + sqrtSlack c_ver n : ENat) + sqrtSlack c_grid n := by gcongr
      _ = ((k + sqrtSlack (c_grid + c_ver) n : ℕ) : ENat) := by
            exact_mod_cast (show k + sqrtSlack c_ver n + sqrtSlack c_grid n =
              k + sqrtSlack (c_grid + c_ver) n by rw [← sqrtSlack_add c_grid c_ver n]; omega)
  have hcard : (state.B (N + 1)).card ≤ 1 := by
    have hsb := state.size_bound (N + 1) le_rfl
    have htar : restrictedAnchoredTarget (n + logSlack 8 n) (sqrtSlack 8 n) grid (N + 1) = 0 := by
      rw [restrictedAnchoredTarget_succ, grid.j_end]; omega
    rw [htar] at hsb
    simpa using hsb
  have hbits : (Nat.bits (state.B (N + 1)).card).length ≤ 1 := by
    have h1 : (Nat.bits 1).length = 1 := by decide
    exact (length_natBits_mono hcard).trans (le_of_eq h1)
  have hKPcond : KP U x (codedUniformOn (state.B (N + 1)) hSne).code ≤
      ((1 + c_idx : ℕ) : ENat) := by
    refine (hidx _ hSne x hxB).trans ?_
    have : (Nat.bits (state.B (N + 1)).card).length + c_idx ≤ 1 + c_idx :=
      Nat.add_le_add_right hbits c_idx
    exact_mod_cast this
  calc
    KPPlain U x
        ≤ setComplexity U (state.B (N + 1)) hSne +
            KP U x (codedUniformOn (state.B (N + 1)) hSne).code + (c_two : ENat) :=
          htwo (state.B (N + 1)) hSne x hxB
    _ ≤ ((k + sqrtSlack (c_grid + c_ver) n : ℕ) : ENat) +
            ((1 + c_idx : ℕ) : ENat) + (c_two : ENat) := by gcongr
    _ = ((k + sqrtSlack (c_grid + c_ver) n + (1 + c_idx) + c_two : ℕ) : ENat) := by
          push_cast; rfl
    _ ≤ ((k + sqrtSlack cfin n : ℕ) : ENat) := by
          apply Nat.cast_le.mpr
          have habs : sqrtSlack (c_grid + c_ver) n + (1 + c_idx + c_two) ≤
                sqrtSlack cfin n := by
            subst hcfin
            exact sqrtSlack_add_const_le n (by omega)
          omega

/-- The mixed structural run, version decoder, and static grid interpolation
assemble into a common all-index output. -/
theorem exists_restricted_coupled_output_against
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒢 ℬ : DescriptionFamily) (hPoly : 𝒢.HasPolynomialOverhead) :
    ∃ c_run : ℕ, ∀ (c_grid n k N : ℕ) (t : ℕ → ℕ)
        (grid : RestrictedCurveGrid n k N t),
      N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1 →
      KPPlain U (restrictedCurveGridCode grid) ≤
        (sqrtSlack c_grid n : ENat) →
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      Nonempty (RestrictedCoupledOutputAgainst 𝒢 ℬ U n k
        (c_grid + 8 + c_run) t) := by
  classical
  obtain ⟨c, hc⟩ := exists_codeFor_map U hU
  obtain ⟨c_two, htwo⟩ := KP_le_setComplexity_add_condKP U hU
  obtain ⟨c_idx, hidx⟩ := KP_le_log_card_given_setCode U hU
  obtain ⟨c_ver, hver⟩ :=
    restrictedAnchoredState_model_complexity_against
      U hU 𝒢 ℬ hPoly c hc
  refine ⟨c_ver + c_two + c_idx + 9, ?_⟩
  intro c_grid n k N t grid hN hgrid hkn ht0 _htk hstrict
  obtain ⟨T, output, state, hrun, hdec, survivor, hsurvivor, hsurvivorAvoid⟩ :=
    exists_restricted_anchored_structural_output_for_code_against
      U 𝒢 ℬ c hc grid hN hkn ht0 hstrict
  have hbound := hver grid hN hkn ht0 hstrict T output state hrun hdec
  set cfin := c_grid + 8 + (c_ver + c_two + c_idx + 9) with hcfin
  have hslack_le : sqrtSlack (c_grid + c_ver) n ≤ sqrtSlack cfin n :=
    sqrtSlack_mono_left (by omega) n
  have hcomplexity := exists_restricted_coupled_output_against_complexity
    hbound hgrid hslack_le
  have hcandidate := exists_restricted_coupled_output_against_candidate
    ⟨htwo, hidx⟩ hbound hgrid hcfin
  have havoids : survivor ∉ restrictedProfileBadSet ℬ U (state.live (N + 1)) k
      (sqrtSlack cfin n) t := by
    intro hmem
    exact hsurvivorAvoid
      (restrictedProfileBadSet_antitone ℬ U (state.live (N + 1)) k
        (sqrtSlack_mono_left (by omega) n) t hmem)
  have h8c : 8 ≤ cfin := by omega
  have hlive_le : ∀ {s₁ s₂ : ℕ}, s₁ ≤ s₂ → s₂ ≤ N + 1 →
      state.live s₂ ⊆ state.live s₁ := by
    intro s₁ s₂ h12
    induction h12 with
    | refl => exact fun _ _ hx => hx
    | @step m hm ih =>
        intro hm1 x hx
        exact ih (by omega) (state.live_monotonic m (by omega) hx)
  have hmesh : n / N + 1 ≤ sqrtSlack cfin n := by
    rw [hN]
    exact (restrictedCurveGrid_mesh_le_sqrtSlack n).trans (sqrtSlack_mono_left h8c n)
  let pred : ℕ → ℕ := restrictedCurveGridPredecessor grid hstrict
  refine ⟨{
    ambientLength := n + logSlack 8 n
    n_le_ambient := Nat.le_add_right _ _
    ambient_le := Nat.add_le_add_left (logSlack_mono_left h8c n) n
    goodSets := fun idx => state.B (pred idx + 1)
    mem_family := ?_
    size_bound := ?_
    complexity_bound := ?_
    candidates := state.live (N + 1)
    candidates_nonempty := ⟨survivor, hsurvivor⟩
    candidate_len := fun x hx => state.live_ambient (N + 1) le_rfl x hx
    candidate_mem := ?_
    candidate_complexity := hcandidate
    survivor := survivor
    survivor_mem := hsurvivor
    survivor_not_bad := havoids }⟩
  · intro idx hidx
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    change pred idx < N ∧
      grid.i (pred idx) ≤ idx ∧
      grid.j (pred idx) ≤ t idx + (n / N + 1) at hp
    exact state.mem_family (pred idx + 1) (by omega)
  · intro idx hidx
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    change pred idx < N ∧
      grid.i (pred idx) ≤ idx ∧
      grid.j (pred idx) ≤ t idx + (n / N + 1) at hp
    calc
      (state.B (pred idx + 1)).card
          ≤ 2 ^ restrictedAnchoredTarget (n + logSlack 8 n)
              (sqrtSlack 8 n) grid (pred idx + 1) :=
            state.size_bound (pred idx + 1) (by omega)
      _ ≤ 2 ^ grid.j (pred idx) := by
            apply Nat.pow_le_pow_right (by norm_num)
            rw [restrictedAnchoredTarget_succ]
            exact Nat.sub_le _ _
      _ ≤ 2 ^ (t idx + sqrtSlack cfin n) := by
            apply Nat.pow_le_pow_right (by norm_num)
            exact hp.2.2.trans (Nat.add_le_add_left hmesh (t idx))
  · intro idx hidx hS
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    change pred idx < N ∧
      grid.i (pred idx) ≤ idx ∧
      grid.j (pred idx) ≤ t idx + (n / N + 1) at hp
    calc
      setComplexity U (state.B (pred idx + 1)) hS
          ≤ (grid.i (pred idx) + sqrtSlack cfin n : ENat) :=
            hcomplexity (pred idx) (Nat.le_of_lt hp.1) hS
      _ ≤ (idx + sqrtSlack cfin n : ENat) := by
            exact_mod_cast Nat.add_le_add_right hp.2.1 (sqrtSlack cfin n)
  · intro x hx idx hidx
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    change pred idx < N ∧
      grid.i (pred idx) ≤ idx ∧
      grid.j (pred idx) ≤ t idx + (n / N + 1) at hp
    exact state.live_subset (pred idx + 1) (by omega)
      (hlive_le (Nat.succ_le_succ (Nat.le_of_lt hp.1)) le_rfl hx)

/-- Joint restricted-curve realization: rebuilding in `𝒢` and excluding bad
descriptions from `ℬ` produces one string realizing the curve in both
families. -/
theorem prop_family_curve_against
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒢 ℬ : DescriptionFamily)
    (hPoly : 𝒢.HasPolynomialOverhead)
    (hsub : ∀ S, 𝒢.mem S → ℬ.mem S) :
    ∃ c : ℕ, ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      ∃ x : BitString, ∃ n' : ℕ,
        x.length = n' ∧
        n ≤ n' ∧
        n' ≤ n + logSlack c n ∧
        KPPlain U x ≤ (k + sqrtSlack c n : ENat) ∧
        RestrictedProfileWithinCurve 𝒢 U x k t
          (sqrtSlack c n) ∧
        RestrictedProfileWithinCurve ℬ U x k t
          (sqrtSlack c n) := by
  obtain ⟨c_grid, hgrid⟩ :=
    exists_encoded_restricted_curve_grid U hU
  obtain ⟨c_run, hrun⟩ :=
    exists_restricted_coupled_output_against U hU 𝒢 ℬ hPoly
  refine ⟨c_grid + 8 + c_run, ?_⟩
  intro n k t hkn ht0 htk hstrict
  obtain ⟨N, grid, hN, hgridComplexity⟩ :=
    hgrid n k t hkn ht0 htk hstrict
  obtain ⟨output⟩ :=
    hrun c_grid n k N t grid hN hgridComplexity
      hkn ht0 htk hstrict
  obtain ⟨hprofileG, hprofileB⟩ := output.profiles hsub
  exact ⟨output.survivor, output.ambientLength,
    output.candidate_len output.survivor output.survivor_mem,
    output.n_le_ambient, output.ambient_le,
    output.candidate_complexity output.survivor output.survivor_mem,
    hprofileG, hprofileB⟩

end Kolmogorov
