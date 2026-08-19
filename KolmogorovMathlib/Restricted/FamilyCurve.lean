import KolmogorovMathlib.Restricted.FamilyCurve.Basic
import KolmogorovMathlib.Restricted.FamilyCurve.RunCoding
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun
import KolmogorovMathlib.Restricted.FamilyCurve.RunBounds
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredChain
import KolmogorovMathlib.Restricted.FamilyCurve.VersionDecoder
import KolmogorovMathlib.Restricted.FamilyCurve.VersionClose
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems
import KolmogorovMathlib.Restricted.HammingGap

namespace Kolmogorov
open scoped ENNReal

/-- Slack absorption: a `sqrtSlack` budget survives an additive constant as
long as the visible constant grows at least as much. -/
lemma sqrtSlack_add_const_le {c d e : ℕ} (n : ℕ) (h : c + e ≤ d) :
    sqrtSlack c n + e ≤ sqrtSlack d n := by
  unfold sqrtSlack
  generalize Nat.sqrt (n * (Nat.bits n).length) = S
  rw [Nat.add_assoc]
  exact Nat.add_le_add (Nat.mul_le_mul_right S (by omega)) (by omega)

/-- The forbidden-profile filter is antitone in its slack parameter: widening
the slack only removes forbidden witnesses. -/
lemma restrictedProfileBadSet_antitone (𝒜 : DescriptionFamily) (U : Map)
    (candidates : Finset BitString) (k : ℕ) {Δ Δ' : ℕ} (hΔ : Δ ≤ Δ')
    (t : ℕ → ℕ) :
    restrictedProfileBadSet 𝒜 U candidates k Δ' t ⊆
      restrictedProfileBadSet 𝒜 U candidates k Δ t := by
  intro y hy
  obtain ⟨hsub, hspec⟩ := restrictedProfileBadSet_spec 𝒜 U candidates k Δ' t
  obtain ⟨hsub', hspec'⟩ := restrictedProfileBadSet_spec 𝒜 U candidates k Δ t
  have hycand : y ∈ candidates := hsub hy
  obtain ⟨i, hik, hti, hprof⟩ := (hspec y hycand).mp hy
  refine (hspec' y hycand).mpr ⟨i, hik, by omega, hprof.mono_j (by omega)⟩

/-- `sqrtSlack` splits additively over its constant. -/
lemma sqrtSlack_add (a b n : ℕ) :
    sqrtSlack a n + sqrtSlack b n = sqrtSlack (a + b) n := by
  unfold sqrtSlack
  generalize Nat.sqrt (n * (Nat.bits n).length) = S
  rw [Nat.add_mul]
  omega

/-- The version-coding core of M7: the anchored effective run (replayed with a
canonical code for `U` chosen inside the proof) reaches a terminal state whose
survivor avoids every forbidden restricted-profile witness AND whose sampled
models carry version-coded complexity bounds: each terminal model is decodable
from the encoded grid together with a bounded binary version ordinal, so its
set complexity is bounded by the grid's `i`-coordinate plus slack.  The
structural part is `exists_restricted_anchored_structural_output`; the
rebuild-count budget follows the survey's large/small charging and the
fixed-length code uses the self-delimiting `listCode` framing. -/
lemma exists_restricted_anchored_output_with_model_complexity
    (U : Map) (_hU : IsOptimalPrefixConditional U)
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_ver : ℕ, ∀ (c_grid n k N : ℕ) (t : ℕ → ℕ)
        (grid : RestrictedCurveGrid n k N t),
      N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1 →
      KPPlain U (restrictedCurveGridCode grid) ≤ (sqrtSlack c_grid n : ENat) →
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      ∃ state : RestrictedSampledRunState 𝒜 (N + 1) (n + logSlack 8 n)
          (2 * 𝒜.overhead (n + logSlack 8 n))
          (restrictedAnchoredTarget (n + logSlack 8 n) (sqrtSlack 8 n) grid),
        (∃ x : BitString, x ∈ state.live (N + 1) ∧
          x ∉ restrictedProfileBadSet 𝒜 U (state.live (N + 1)) k
            (sqrtSlack 8 n) t) ∧
        ∀ s (_hs : s ≤ N) (hS : (state.B (s + 1)).Nonempty),
          setComplexity U (state.B (s + 1)) hS ≤
            (grid.i s + sqrtSlack (c_grid + c_ver) n : ENat) := by
  obtain ⟨c, hc⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c U :=
    Nat.Partrec.Code.exists_code.mp _hU.isDecompressor
  obtain ⟨c_ver, h_ver⟩ :=
    restrictedAnchoredState_model_complexity U _hU 𝒜 hPoly c hc
  refine ⟨c_ver, ?_⟩
  intro c_grid n k N t grid hN h_kp_grid hkn ht0 htk hstrict
  obtain ⟨T, output, state, hrun, hdecodes, hsurv⟩ :=
    exists_restricted_anchored_structural_output_for_code U 𝒜 c hc grid hN
      hkn ht0 hstrict
  refine ⟨state, hsurv, ?_⟩
  intro s hs hS
  have h_bound := h_ver grid hN hkn ht0 hstrict T output state hrun hdecodes
    s hs hS
  have hslack_eq : (sqrtSlack c_ver n : ENat) + (sqrtSlack c_grid n : ENat) =
      (sqrtSlack (c_grid + c_ver) n : ENat) := by
    rw [← ENat.coe_add]
    have : sqrtSlack c_ver n + sqrtSlack c_grid n =
        sqrtSlack (c_grid + c_ver) n := by
      rw [sqrtSlack_add, add_comm]
    rw [this]
  calc
    setComplexity U (state.B (s + 1)) hS
      ≤ (grid.i s + sqrtSlack c_ver n : ENat) + KPPlain U (restrictedCurveGridCode grid) := by
        exact_mod_cast h_bound
    _ ≤ (grid.i s + sqrtSlack c_ver n : ENat) + sqrtSlack c_grid n := by
        gcongr
    _ = (grid.i s : ENat) + (sqrtSlack c_ver n : ENat) + sqrtSlack c_grid n := by
        rfl
    _ = (grid.i s : ENat) + ((sqrtSlack c_ver n : ENat) + sqrtSlack c_grid n) := by
        rw [add_assoc]
    _ = (grid.i s : ENat) + (sqrtSlack (c_grid + c_ver) n : ENat) := by
        rw [hslack_eq]
    _ = (grid.i s + sqrtSlack (c_grid + c_ver) n : ENat) := by
        rfl

/-- The core M7 assembly.  `RunBounds` supplies the balanced ambient
padding, terminating anchored run, nonempty terminal survivor, and
forbidden-profile avoidance; `restrictedAnchoredRun_model_setComplexity`
supplies the version-coded model complexities.  The candidate complexity
follows from the two-part decoder bound because the terminal anchored level
has unit size (`grid.j N = 0`), and the packaged core is produced by
`restrictedAnchoredState_to_sampledOutputCore`. -/
lemma exists_restricted_sampled_output_core
    (U : Map) (_hU : IsOptimalPrefixConditional U)
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_run : ℕ, ∀ (c_grid n k N : ℕ) (t : ℕ → ℕ)
        (grid : RestrictedCurveGrid n k N t),
      N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1 →
      KPPlain U (restrictedCurveGridCode grid) ≤ (sqrtSlack c_grid n : ENat) →
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      Nonempty (RestrictedSampledOutputCore 𝒜 U n k N
        (c_grid + 8 + c_run) t grid) := by
  classical
  obtain ⟨c_two, htwo⟩ := KP_le_setComplexity_add_condKP U _hU
  obtain ⟨c_idx, hidx⟩ := KP_le_log_card_given_setCode U _hU
  obtain ⟨c_ver, hver⟩ :=
    exists_restricted_anchored_output_with_model_complexity U _hU 𝒜 hPoly
  refine ⟨c_ver + c_two + c_idx + 9, ?_⟩
  intro c_grid n k N t grid hN hgrid hkn ht0 htk hstrict
  obtain ⟨state, ⟨survivor, hsurv_mem, hsurv_avoid⟩, hbound⟩ :=
    hver c_grid n k N t grid hN hgrid hkn ht0 htk hstrict
  set cfin := c_grid + 8 + (c_ver + c_two + c_idx + 9) with hcfin
  have hslack_le : sqrtSlack (c_grid + c_ver) n ≤ sqrtSlack cfin n :=
    sqrtSlack_mono_left (by omega) n
  have hcomplexity : ∀ s (_hs : s ≤ N) (hS : (state.B (s + 1)).Nonempty),
      setComplexity U (state.B (s + 1)) hS ≤
        (grid.i s + sqrtSlack cfin n : ENat) := by
    intro s hs hS
    refine (hbound s hs hS).trans ?_
    have : grid.i s + sqrtSlack (c_grid + c_ver) n ≤
        grid.i s + sqrtSlack cfin n := Nat.add_le_add_left hslack_le _
    exact_mod_cast this
  have hcandidate : ∀ x ∈ state.live (N + 1),
      KPPlain U x ≤ (k + sqrtSlack cfin n : ENat) := by
    intro x hx
    have hxB : x ∈ state.B (N + 1) := state.live_subset (N + 1) le_rfl hx
    have hSne : (state.B (N + 1)).Nonempty := ⟨x, hxB⟩
    have hsetC : setComplexity U (state.B (N + 1)) hSne ≤
        ((k + sqrtSlack (c_grid + c_ver) n : ℕ) : ENat) := by
      have h := hbound N le_rfl hSne
      rw [grid.i_end] at h
      exact_mod_cast h
    have hcard : (state.B (N + 1)).card ≤ 1 := by
      have hsb := state.size_bound (N + 1) le_rfl
      have htar : restrictedAnchoredTarget (n + logSlack 8 n)
          (sqrtSlack 8 n) grid (N + 1) = 0 := by
        rw [restrictedAnchoredTarget_succ, grid.j_end]
        omega
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
    calc KPPlain U x
        ≤ setComplexity U (state.B (N + 1)) hSne +
            KP U x (codedUniformOn (state.B (N + 1)) hSne).code +
            (c_two : ENat) := htwo (state.B (N + 1)) hSne x hxB
      _ ≤ ((k + sqrtSlack (c_grid + c_ver) n : ℕ) : ENat) +
            ((1 + c_idx : ℕ) : ENat) + (c_two : ENat) := by gcongr
      _ = ((k + sqrtSlack (c_grid + c_ver) n + (1 + c_idx) + c_two : ℕ) :
            ENat) := by
          push_cast
          rfl
      _ ≤ ((k + sqrtSlack cfin n : ℕ) : ENat) := by
          apply Nat.cast_le.mpr
          have habs : sqrtSlack (c_grid + c_ver) n + (1 + c_idx + c_two) ≤
              sqrtSlack cfin n := sqrtSlack_add_const_le n (by omega)
          omega
  have havoids : survivor ∉ restrictedProfileBadSet 𝒜 U
      (state.live (N + 1)) k (sqrtSlack cfin n) t := fun hmem =>
    hsurv_avoid (restrictedProfileBadSet_antitone 𝒜 U (state.live (N + 1)) k
      (sqrtSlack_mono_left (by omega) n) t hmem)
  obtain ⟨core⟩ := restrictedAnchoredState_to_sampledOutputCore 𝒜 U
    (c := cfin) grid state
    (Nat.le_add_right n (logSlack 8 n))
    (Nat.add_le_add_left (logSlack_mono_left (by omega) n) n)
    hcomplexity hcandidate survivor hsurv_mem havoids
  exact ⟨core⟩

/-- Stabilization and fixed-length version-coding core, exposed through the
all-index output expected by the frozen coupled-process theorem. -/
lemma exists_restricted_coupled_output
    (U : Map) (_hU : IsOptimalPrefixConditional U)
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_run : ℕ, ∀ (c_grid n k N : ℕ) (t : ℕ → ℕ)
        (grid : RestrictedCurveGrid n k N t),
      N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1 →
      KPPlain U (restrictedCurveGridCode grid) ≤ (sqrtSlack c_grid n : ENat) →
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      Nonempty (RestrictedCoupledOutput 𝒜 U n k (c_grid + 8 + c_run) t) := by
  obtain ⟨c_run, hcore⟩ :=
    exists_restricted_sampled_output_core U _hU 𝒜 hPoly
  refine ⟨c_run, ?_⟩
  intro c_grid n k N t grid hN hgridComplexity hkn ht0 htk hstrict
  obtain ⟨core⟩ :=
    hcore c_grid n k N t grid hN hgridComplexity hkn ht0 htk hstrict
  have hmesh : n / N + 1 ≤ sqrtSlack (c_grid + 8 + c_run) n := by
    rw [hN]
    exact (restrictedCurveGrid_mesh_le_sqrtSlack n).trans
      (sqrtSlack_mono_left (by omega) n)
  let output := core.toSampledOutput hmesh
  obtain ⟨base⟩ := output.toCoupledOutput hstrict
  exact ⟨base⟩

/-- Assemble the frozen coupled-process interface from the encoded grid and the
separately stabilized dynamic output. -/
lemma exists_restricted_coupled_scale_process
    (U : Map) (_hU : IsOptimalPrefixConditional U)
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_process : ℕ, ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      Nonempty (RestrictedCoupledScaleProcess 𝒜 U n k c_process t) := by
  obtain ⟨c_grid, hgrid⟩ := exists_encoded_restricted_curve_grid U _hU
  obtain ⟨c_run, hrun⟩ := exists_restricted_coupled_output U _hU 𝒜 hPoly
  refine ⟨c_grid + 8 + c_run, ?_⟩
  intro n k t hkn ht0 htk hstrict
  obtain ⟨N, grid, hN, hgridComplexity⟩ :=
    hgrid n k t hkn ht0 htk hstrict
  obtain ⟨output⟩ :=
    hrun c_grid n k N t grid hN hgridComplexity hkn ht0 htk hstrict
  have hslack : sqrtSlack c_grid n ≤ sqrtSlack (c_grid + 8 + c_run) n := by
    unfold sqrtSlack
    nlinarith [Nat.zero_le ((8 + c_run) * Nat.sqrt (n * (Nat.bits n).length))]
  exact ⟨{
    gridSteps := N
    grid := grid
    gridSteps_eq := hN
    grid_code_complexity := hgridComplexity.trans (by exact_mod_cast hslack)
    ambientLength := output.ambientLength
    n_le_ambient := output.n_le_ambient
    ambient_le := output.ambient_le
    goodSets := output.goodSets
    mem_family := output.mem_family
    size_bound := output.size_bound
    complexity_bound := output.complexity_bound
    candidates := output.candidates
    candidates_nonempty := output.candidates_nonempty
    candidate_len := output.candidate_len
    candidate_mem := output.candidate_mem
    candidate_complexity := output.candidate_complexity
    survivor := output.survivor
    survivor_mem := output.survivor_mem
    survivor_not_bad := output.survivor_not_bad }⟩

/-- Hard M7 leaf: construct the computably generated, survivor-preserving
multi-scale good-set process.  The bad-profile union bound is now provided by
`restrictedProfileBadSet_card_le`; the coupled process is isolated in
`exists_restricted_coupled_scale_process`. -/
lemma exists_restricted_scale_template (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_template : ℕ, ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      Nonempty (RestrictedScaleTemplate 𝒜 U n k c_template t) := by
  obtain ⟨c, hc⟩ := exists_restricted_coupled_scale_process U hU 𝒜 hPoly
  refine ⟨c, ?_⟩
  intro n k t hkn ht0 htk hstrict
  obtain ⟨process⟩ := hc n k t hkn ht0 htk hstrict
  exact process.toTemplate

/-- Now that the template has an explicit survivor, a final candidate
can be trivially selected outside all forbidden restricted profile witnesses. -/
lemma RestrictedScaleTemplate.exists_good_candidate
    {𝒜 : DescriptionFamily} {U : Map} {n k c : ℕ} {t : ℕ → ℕ}
    (template : RestrictedScaleTemplate 𝒜 U n k c t) :
    ∃ x : BitString, x ∈ template.candidates ∧
      (∀ i : ℕ, i ≤ k →
        ¬ InDescriptionProfileIn 𝒜 U x i (t i - (sqrtSlack c n + 1)) ∨
          t i ≤ sqrtSlack c n) ∧
      KPPlain U x ≤ (k + sqrtSlack c n : ENat) := by
  classical
  refine ⟨template.survivor, template.survivor_mem, ?_,
    template.candidate_complexity template.survivor template.survivor_mem⟩
  intro i hi
  by_cases hsmall : t i ≤ sqrtSlack c n
  · exact Or.inr hsmall
  · refine Or.inl ?_
    intro hprof
    exact template.survivor_not_bad
      ((template.badSet_exact template.survivor template.survivor_mem).mpr
        ⟨i, hi, Nat.lt_of_not_ge hsmall, hprof⟩)

/-- The core scale construction: there exists a valid restricted scale state
whose target string `x` also avoids the low-complexity bad sets (the lower bound). -/
lemma exists_restricted_scale_state (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_scale : ℕ, ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      ∃ state : RestrictedScaleState 𝒜 U n k c_scale t,
        (∀ i : ℕ, i ≤ k →
          ¬ InDescriptionProfileIn 𝒜 U state.x i
              (t i - (sqrtSlack c_scale n + 1)) ∨
            t i ≤ sqrtSlack c_scale n) ∧
        KPPlain U state.x ≤ (k + sqrtSlack c_scale n : ENat) := by
  obtain ⟨c, hc⟩ := exists_restricted_scale_template U hU 𝒜 hPoly
  refine ⟨c, ?_⟩
  intro n k t hkn ht0 htk hstrict
  obtain ⟨template⟩ := hc n k t hkn ht0 htk hstrict
  obtain ⟨x, hxcand, hlower, hkp⟩ := template.exists_good_candidate
  refine ⟨{
    x := x
    ambientLength := template.ambientLength
    x_len := template.candidate_len x hxcand
    n_le_ambient := template.n_le_ambient
    ambient_le := template.ambient_le
    goodSets := template.goodSets
    mem_family := template.mem_family
    x_mem := fun s hs => template.candidate_mem x hxcand s hs
    size_bound := template.size_bound
    complexity_bound := ?_ }, hlower, hkp⟩
  intro s hs
  exact template.complexity_bound s hs ⟨x, template.candidate_mem x hxcand s hs⟩

/--
M7: restricted curve realization (`thm:family-curve`).

For a fixed restricted description family `𝒜`, every strictly decreasing boundary
sequence `t 0 > t 1 > ... > t k = 0`, with `k ≤ n` and `t 0 ≤ n`, is realized up
to `O(sqrt(n log n))` precision by the restricted profile of some string whose
length is `n + O(log n)` and whose plain complexity is `k + O(sqrt(n log n))`.
-/
theorem prop_family_curve (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_curve : ℕ, ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      ∃ x : BitString, ∃ n' : ℕ,
        x.length = n' ∧
        n ≤ n' ∧ n' ≤ n + logSlack c_curve n ∧
        KPPlain U x ≤ (k + sqrtSlack c_curve n : ENat) ∧
        RestrictedProfileWithinCurve 𝒜 U x k t (sqrtSlack c_curve n) := by
  obtain ⟨c, hc⟩ := exists_restricted_scale_state U hU 𝒜 hPoly
  use c
  intro n k t hkn ht0 htk hstrict
  obtain ⟨state, h_lower, h_KP⟩ := hc n k t hkn ht0 htk hstrict
  refine ⟨state.x, state.ambientLength, state.x_len, state.n_le_ambient,
    state.ambient_le, h_KP, ?_⟩
  constructor
  · intro i hi
    unfold InDescriptionProfileIn IsIJDescriptionIn IsIJDescription
    refine ⟨state.goodSets i, ⟨state.x, state.x_mem i hi⟩,
      state.mem_family i hi, state.x_mem i hi, ?_, state.size_bound i hi⟩
    exact state.complexity_bound i hi
  · exact h_lower

end Kolmogorov
