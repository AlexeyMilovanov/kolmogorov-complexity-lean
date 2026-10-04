import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.Restricted.FamilyCurve.SampledRun
import KolmogorovMathlib.Restricted.FamilyCurve.Selector
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Restricted.FamilyCurve.Basic.Part01

/-!
# Finite bad-description counting

The coupled process must charge rebuilds to actual bad descriptions and to
actual deleted survivors.  The following definitions and lemmas expose the
finite objects being counted; in particular, none of the witnesses below is an
unconstrained natural number.
-/

namespace Kolmogorov
open scoped ENNReal

/-- Restricted family members whose canonical uniform codes have complexity at
most `i` and whose cardinality is at most `2^j`. -/
noncomputable def restrictedBadDescriptions (𝒜 : DescriptionFamily) (U : Map)
    (i j : ℕ) : Finset (Finset BitString) := by
  classical
  exact (descriptionsWithComplexityLeAndSizeLe U i j).filter 𝒜.mem

/-- There are at most `2^(i+1)` distinct restricted bad descriptions of
complexity at most `i`.  This is the honest large-description appearance
bound: appearances are counted by canonical finite sets, not by an arbitrary
existential counter. -/
lemma restricted_large_bad_appearances_le (𝒜 : DescriptionFamily) (U : Map)
    (i j : ℕ) :
    (restrictedBadDescriptions 𝒜 U i j).card ≤ 2 ^ (i + 1) := by
  classical
  calc
    (restrictedBadDescriptions 𝒜 U i j).card
        ≤ (descriptionsWithComplexityLeAndSizeLe U i j).card := by
          unfold restrictedBadDescriptions
          exact Finset.card_filter_le _ _
    _ ≤ 2 ^ (i + 1) := card_descriptionsWithComplexityLeAndSizeLe U i j

/-- The union of all restricted bad descriptions at parameters `(i,j)` has
volume at most `2^(i+1) * 2^j`. -/
lemma restricted_small_bad_deleted_volume_le (𝒜 : DescriptionFamily) (U : Map)
    (i j : ℕ) :
    ((restrictedBadDescriptions 𝒜 U i j).biUnion id).card ≤
      2 ^ (i + 1) * 2 ^ j := by
  classical
  have hsize : ∀ A ∈ restrictedBadDescriptions 𝒜 U i j, A.card ≤ 2 ^ j := by
    intro A hA
    unfold restrictedBadDescriptions at hA
    rw [Finset.mem_filter] at hA
    exact (Finset.mem_filter.mp hA.1).2
  calc
    ((restrictedBadDescriptions 𝒜 U i j).biUnion id).card
        ≤ ∑ A ∈ restrictedBadDescriptions 𝒜 U i j, A.card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ restrictedBadDescriptions 𝒜 U i j, 2 ^ j :=
          Finset.sum_le_sum hsize
    _ = (restrictedBadDescriptions 𝒜 U i j).card * 2 ^ j := by simp
    _ ≤ 2 ^ (i + 1) * 2 ^ j :=
          Nat.mul_le_mul_right (2 ^ j)
            (restricted_large_bad_appearances_le 𝒜 U i j)

/-- If every rebuild charged to small bad descriptions deletes at least `ν`
fresh survivors, and the charged deletion blocks are pairwise disjoint, then
the number of such rebuilds times `ν` is bounded by the total small-bad volume.
This is the exact finite combinatorial charging step used by the coupled
process. -/
lemma restricted_rebuilds_charged_to_deleted_volume
    {ι α : Type*}
    (rebuilds : Finset ι) (deleted : ι → Finset α)
    (smallBad : Finset α) (ν : ℕ)
    (hdisjoint : (↑rebuilds : Set ι).PairwiseDisjoint deleted)
    (hsubset : ∀ r ∈ rebuilds, deleted r ⊆ smallBad)
    (hthreshold : ∀ r ∈ rebuilds, ν ≤ (deleted r).card) :
    rebuilds.card * ν ≤ smallBad.card := by
  classical
  have hUnion : rebuilds.biUnion deleted ⊆ smallBad := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨r, hr, hxr⟩ := hx
    exact hsubset r hr hxr
  calc
    rebuilds.card * ν = ∑ _r ∈ rebuilds, ν := by simp
    _ ≤ ∑ r ∈ rebuilds, (deleted r).card := Finset.sum_le_sum hthreshold
    _ = (rebuilds.biUnion deleted).card := (Finset.card_biUnion hdisjoint).symm
    _ ≤ smallBad.card := Finset.card_le_card hUnion

/-- A decreasing chronological survivor sequence makes its fresh deletion
blocks pairwise disjoint, so the general finite deleted-volume charge applies
without requiring disjointness as a separate process invariant. -/
lemma restricted_self_rebuilds_charged_to_deleted_volume
    (rebuilds : Finset ℕ)
    (survivors deleted : ℕ → Finset BitString)
    (smallBad : Finset BitString) (threshold : ℕ)
    (h_mono : ∀ i j, i ≤ j → survivors j ⊆ survivors i)
    (h_deleted_sub : ∀ i, deleted i ⊆ survivors i)
    (h_fresh : ∀ i, Disjoint (deleted i) (survivors (i + 1)))
    (h_smallBad : ∀ r ∈ rebuilds, deleted r ⊆ smallBad)
    (h_threshold : ∀ r ∈ rebuilds, threshold ≤ (deleted r).card) :
    rebuilds.card * threshold ≤ smallBad.card := by
  have h_all := restricted_self_rebuild_deletedBlocks_pairwiseDisjoint
    survivors deleted h_mono h_deleted_sub h_fresh
  apply restricted_rebuilds_charged_to_deleted_volume
    rebuilds deleted smallBad threshold
  · intro i _hi j _hj hij
    exact h_all (Set.mem_univ i) (Set.mem_univ j) hij
  · exact h_smallBad
  · exact h_threshold

/-- The candidates already carrying a forbidden restricted-profile witness.
This concrete filter is the bad set packaged by `RestrictedScaleTemplate`. -/
noncomputable def restrictedProfileBadSet (𝒜 : DescriptionFamily) (U : Map)
    (candidates : Finset BitString) (k Δ : ℕ) (t : ℕ → ℕ) :
    Finset BitString := by
  classical
  exact candidates.filter fun x => ∃ i : ℕ, i ≤ k ∧ t i > Δ ∧
    InDescriptionProfileIn 𝒜 U x i (t i - (Δ + 1))

/-
Filtering candidates by the forbidden-profile predicate simultaneously gives
the subset and exact-membership fields required by the scale template.
-/
lemma restrictedProfileBadSet_spec (𝒜 : DescriptionFamily) (U : Map)
    (candidates : Finset BitString) (k Δ : ℕ) (t : ℕ → ℕ) :
    restrictedProfileBadSet 𝒜 U candidates k Δ t ⊆ candidates ∧
      ∀ x ∈ candidates,
        x ∈ restrictedProfileBadSet 𝒜 U candidates k Δ t ↔
          ∃ i : ℕ, i ≤ k ∧ t i > Δ ∧
            InDescriptionProfileIn 𝒜 U x i (t i - (Δ + 1)) := by
  unfold restrictedProfileBadSet
  aesop

/-- The concrete forbidden-profile filter is bounded by the sum of the
per-boundary-point bad-description volumes.  This reduces the lower-profile
side of the scale construction to finite cardinal arithmetic; overlap between
bad descriptions only improves the estimate. -/
lemma restrictedProfileBadSet_card_le_bad_volume
    (𝒜 : DescriptionFamily) (U : Map)
    (candidates : Finset BitString) (k Δ : ℕ) (t : ℕ → ℕ) :
    (restrictedProfileBadSet 𝒜 U candidates k Δ t).card ≤
      ∑ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
        2 ^ (i + 1) * 2 ^ (t i - (Δ + 1)) := by
  classical
  let allBad : Finset BitString :=
    ((Finset.range (k + 1)).filter fun i => Δ < t i).biUnion fun i =>
      (restrictedBadDescriptions 𝒜 U i (t i - (Δ + 1))).biUnion id
  have hsub : restrictedProfileBadSet 𝒜 U candidates k Δ t ⊆ allBad := by
    intro x hx
    rw [restrictedProfileBadSet, Finset.mem_filter] at hx
    obtain ⟨i, hi, ht, hprof⟩ := hx.2
    obtain ⟨S, hS, hmem, hdesc⟩ := hprof
    obtain ⟨hxS, hcomp, hcard⟩ := hdesc
    dsimp [allBad]
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi), ht⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨S, ?_, hxS⟩
    unfold restrictedBadDescriptions
    rw [Finset.mem_filter, descriptionsWithComplexityLeAndSizeLe,
      Finset.mem_filter]
    exact ⟨⟨mem_descriptionsWithComplexityLe_of_complexity hS hcomp, hcard⟩,
      hmem⟩
  calc
    (restrictedProfileBadSet 𝒜 U candidates k Δ t).card
        ≤ allBad.card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
          ((restrictedBadDescriptions 𝒜 U i
            (t i - (Δ + 1))).biUnion id).card := by
          dsimp [allBad]
          exact Finset.card_biUnion_le
    _ ≤ ∑ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
          2 ^ (i + 1) * 2 ^ (t i - (Δ + 1)) := by
          exact Finset.sum_le_sum fun i _hi =>
            restricted_small_bad_deleted_volume_le 𝒜 U i
              (t i - (Δ + 1))

/-- Along a strictly decreasing boundary, the total bad-description volume is
at most `(k+1) * 2^(t 0 - Δ)`.  The filter to levels with `Δ < t i` is essential:
at lower levels the forbidden-profile predicate is inactive. -/
lemma restricted_bad_volume_sum_le
    {k Δ : ℕ} {t : ℕ → ℕ}
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i) :
    (∑ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
        2 ^ (i + 1) * 2 ^ (t i - (Δ + 1))) ≤
      (k + 1) * 2 ^ (t 0 - Δ) := by
  have hterm : ∀ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
      2 ^ (i + 1) * 2 ^ (t i - (Δ + 1)) ≤ 2 ^ (t 0 - Δ) := by
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp
      (Finset.mem_filter.mp hi).1)
    have hΔ : Δ < t i := (Finset.mem_filter.mp hi).2
    have hcurve : i + t i ≤ t 0 :=
      restricted_curve_index_add_le_start hstrict hik
    have hexp : i + 1 + (t i - (Δ + 1)) ≤ t 0 - Δ := by
      omega
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) hexp
  calc
    (∑ i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
        2 ^ (i + 1) * 2 ^ (t i - (Δ + 1)))
        ≤ ∑ _i ∈ (Finset.range (k + 1)).filter (fun i => Δ < t i),
            2 ^ (t 0 - Δ) := Finset.sum_le_sum hterm
    _ = ((Finset.range (k + 1)).filter (fun i => Δ < t i)).card *
          2 ^ (t 0 - Δ) := by simp
    _ ≤ (k + 1) * 2 ^ (t 0 - Δ) := by
      exact Nat.mul_le_mul_right _
        ((Finset.card_filter_le _ _).trans_eq (Finset.card_range (k + 1)))

/-- Final bad-candidate cardinality estimate obtained by combining the finite
description count with strict decrease of the target boundary. -/
lemma restrictedProfileBadSet_card_le
    (𝒜 : DescriptionFamily) (U : Map)
    (candidates : Finset BitString) (k Δ : ℕ) (t : ℕ → ℕ)
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i) :
    (restrictedProfileBadSet 𝒜 U candidates k Δ t).card ≤
      (k + 1) * 2 ^ (t 0 - Δ) := by
  exact (restrictedProfileBadSet_card_le_bad_volume 𝒜 U candidates k Δ t).trans
    (restricted_bad_volume_sum_le hstrict)

/-- Output data of the computably generated coupled rebuild process, before
filtering out candidates with a forbidden restricted-profile witness.

The explicit `survivor` is the dynamic invariant replacing the false global
comparison between bad-set volume and the terminal common candidate pool. -/
structure RestrictedCoupledScaleProcess (𝒜 : DescriptionFamily) (U : Map)
    (n k c : ℕ) (t : ℕ → ℕ) where
  gridSteps : ℕ
  grid : RestrictedCurveGrid n k gridSteps t
  gridSteps_eq : gridSteps = Nat.sqrt (n / (Nat.log2 n + 1)) + 1
  grid_code_complexity :
    KPPlain U (restrictedCurveGridCode grid) ≤ (sqrtSlack c n : ENat)
  ambientLength : ℕ
  n_le_ambient : n ≤ ambientLength
  ambient_le : ambientLength ≤ n + logSlack c n
  goodSets : ℕ → Finset BitString
  mem_family : ∀ s (_hs : s ≤ k), 𝒜.mem (goodSets s)
  size_bound : ∀ s (_hs : s ≤ k),
    (goodSets s).card ≤ 2 ^ (t s + sqrtSlack c n)
  complexity_bound : ∀ s (_hs : s ≤ k) (hS : (goodSets s).Nonempty),
    setComplexity U (goodSets s) hS ≤ (s + sqrtSlack c n : ENat)
  candidates : Finset BitString
  candidates_nonempty : candidates.Nonempty
  candidate_len : ∀ x ∈ candidates, x.length = ambientLength
  candidate_mem : ∀ x ∈ candidates, ∀ s (_hs : s ≤ k), x ∈ goodSets s
  candidate_complexity : ∀ x ∈ candidates,
    KPPlain U x ≤ (k + sqrtSlack c n : ENat)
  survivor : BitString
  survivor_mem : survivor ∈ candidates
  survivor_not_bad :
    survivor ∉ restrictedProfileBadSet 𝒜 U candidates k (sqrtSlack c n) t

/-- The dynamic output of the sampled run, separated from the already-proved
encoded-grid construction.  This is the part that stabilization and fixed-length
version coding must produce. -/
structure RestrictedCoupledOutput (𝒜 : DescriptionFamily) (U : Map)
    (n k c : ℕ) (t : ℕ → ℕ) where
  ambientLength : ℕ
  n_le_ambient : n ≤ ambientLength
  ambient_le : ambientLength ≤ n + logSlack c n
  goodSets : ℕ → Finset BitString
  mem_family : ∀ s (_hs : s ≤ k), 𝒜.mem (goodSets s)
  size_bound : ∀ s (_hs : s ≤ k),
    (goodSets s).card ≤ 2 ^ (t s + sqrtSlack c n)
  complexity_bound : ∀ s (_hs : s ≤ k) (hS : (goodSets s).Nonempty),
    setComplexity U (goodSets s) hS ≤ (s + sqrtSlack c n : ENat)
  candidates : Finset BitString
  candidates_nonempty : candidates.Nonempty
  candidate_len : ∀ x ∈ candidates, x.length = ambientLength
  candidate_mem : ∀ x ∈ candidates, ∀ s (_hs : s ≤ k), x ∈ goodSets s
  candidate_complexity : ∀ x ∈ candidates,
    KPPlain U x ≤ (k + sqrtSlack c n : ENat)
  survivor : BitString
  survivor_mem : survivor ∈ candidates
  survivor_not_bad :
    survivor ∉ restrictedProfileBadSet 𝒜 U candidates k (sqrtSlack c n) t

/-- The genuine dynamic and coding output at the `N + 1` sampled boundary
scales.  It deliberately omits the elementary mesh inequality, which is added
by `RestrictedSampledOutputCore.toSampledOutput`. -/
structure RestrictedSampledOutputCore (𝒜 : DescriptionFamily) (U : Map)
    (n k N c : ℕ) (t : ℕ → ℕ) (grid : RestrictedCurveGrid n k N t) where
  ambientLength : ℕ
  n_le_ambient : n ≤ ambientLength
  ambient_le : ambientLength ≤ n + logSlack c n
  sampledSets : ℕ → Finset BitString
  mem_family : ∀ s (_hs : s ≤ N), 𝒜.mem (sampledSets s)
  size_bound : ∀ s (_hs : s ≤ N), (sampledSets s).card ≤ 2 ^ grid.j s
  complexity_bound : ∀ s (_hs : s ≤ N) (hS : (sampledSets s).Nonempty),
    setComplexity U (sampledSets s) hS ≤ (grid.i s + sqrtSlack c n : ENat)
  candidates : Finset BitString
  candidates_nonempty : candidates.Nonempty
  candidate_len : ∀ x ∈ candidates, x.length = ambientLength
  candidate_mem : ∀ x ∈ candidates, ∀ s (_hs : s ≤ N), x ∈ sampledSets s
  candidate_complexity : ∀ x ∈ candidates,
    KPPlain U x ≤ (k + sqrtSlack c n : ENat)
  survivor : BitString
  survivor_mem : survivor ∈ candidates
  survivor_not_bad :
    survivor ∉ restrictedProfileBadSet 𝒜 U candidates k (sqrtSlack c n) t

/-- Output at the `N + 1` sampled boundary scales maintained by the coupled
rebuild construction.  The all-index `RestrictedCoupledOutput` is obtained by
interpolating with the predecessor sample supplied by `grid`.

Keeping this intermediate object explicit prevents the dynamic run from being
artificially indexed by all `k + 1` boundary coordinates. -/
structure RestrictedSampledOutput (𝒜 : DescriptionFamily) (U : Map)
    (n k N c : ℕ) (t : ℕ → ℕ) (grid : RestrictedCurveGrid n k N t)
    extends RestrictedSampledOutputCore 𝒜 U n k N c t grid where
  mesh_le_slack : n / N + 1 ≤ sqrtSlack c n

/-- Add the separately proved numeric mesh estimate to the dynamic sampled
output. -/
def RestrictedSampledOutputCore.toSampledOutput
    {𝒜 : DescriptionFamily} {U : Map} {n k N c : ℕ} {t : ℕ → ℕ}
    {grid : RestrictedCurveGrid n k N t}
    (output : RestrictedSampledOutputCore 𝒜 U n k N c t grid)
    (hmesh : n / N + 1 ≤ sqrtSlack c n) :
    RestrictedSampledOutput 𝒜 U n k N c t grid :=
  { toRestrictedSampledOutputCore := output
    mesh_le_slack := hmesh }

/-- The predecessor sample used to interpolate a sampled family-curve output
at an arbitrary horizontal coordinate `idx ≤ k`. -/
noncomputable def restrictedCurveGridPredecessor
    {n k N : ℕ} {t : ℕ → ℕ} (grid : RestrictedCurveGrid n k N t)
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i) (idx : ℕ) : ℕ :=
  if hidx : idx ≤ k then
    Classical.choose (restrictedCurveGrid_height_le_target_add_mesh grid hstrict idx hidx)
  else 0

/-- The predecessor sample lies below `idx` horizontally and at most one mesh
above `t idx` vertically. -/
lemma restrictedCurveGridPredecessor_spec
    {n k N : ℕ} {t : ℕ → ℕ} (grid : RestrictedCurveGrid n k N t)
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i) (idx : ℕ) (hidx : idx ≤ k) :
    restrictedCurveGridPredecessor grid hstrict idx < N ∧
      grid.i (restrictedCurveGridPredecessor grid hstrict idx) ≤ idx ∧
      grid.j (restrictedCurveGridPredecessor grid hstrict idx) ≤
        t idx + (n / N + 1) := by
  unfold restrictedCurveGridPredecessor
  rw [dite_eq_left hidx]
  have hs := Classical.choose_spec
    (restrictedCurveGrid_height_le_target_add_mesh grid hstrict idx hidx)
  exact ⟨hs.1, hs.2.1, hs.2.2.2⟩

/-- Interpolate sampled good sets to every `idx ≤ k`.  This is the purely
static final assembly step applied after the dynamic construction produces the
`N + 1` sampled versions and their common surviving candidate. -/
lemma RestrictedSampledOutput.toCoupledOutput
    {𝒜 : DescriptionFamily} {U : Map} {n k N c : ℕ} {t : ℕ → ℕ}
    {grid : RestrictedCurveGrid n k N t}
    (output : RestrictedSampledOutput 𝒜 U n k N c t grid)
    (hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i) :
    Nonempty (RestrictedCoupledOutput 𝒜 U n k c t) := by
  let pred : ℕ → ℕ := restrictedCurveGridPredecessor grid hstrict
  refine ⟨{
    ambientLength := output.ambientLength
    n_le_ambient := output.n_le_ambient
    ambient_le := output.ambient_le
    goodSets := fun idx => output.sampledSets (pred idx)
    mem_family := ?_
    size_bound := ?_
    complexity_bound := ?_
    candidates := output.candidates
    candidates_nonempty := output.candidates_nonempty
    candidate_len := output.candidate_len
    candidate_mem := ?_
    candidate_complexity := output.candidate_complexity
    survivor := output.survivor
    survivor_mem := output.survivor_mem
    survivor_not_bad := output.survivor_not_bad }⟩
  · intro idx hidx
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    exact output.mem_family (pred idx) (Nat.le_of_lt hp.1)
  · intro idx hidx
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    calc
      (output.sampledSets (pred idx)).card ≤ 2 ^ grid.j (pred idx) :=
        output.size_bound (pred idx) (Nat.le_of_lt hp.1)
      _ ≤ 2 ^ (t idx + sqrtSlack c n) := by
        apply Nat.pow_le_pow_right (by decide)
        exact hp.2.2.trans (Nat.add_le_add_left output.mesh_le_slack (t idx))
  · intro idx hidx hS
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    calc
      setComplexity U (output.sampledSets (pred idx)) hS ≤
          (grid.i (pred idx) + sqrtSlack c n : ENat) :=
        output.complexity_bound (pred idx) (Nat.le_of_lt hp.1) hS
      _ ≤ (idx + sqrtSlack c n : ENat) := by
        exact_mod_cast Nat.add_le_add_right hp.2.1 (sqrtSlack c n)
  · intro x hx idx hidx
    have hp := restrictedCurveGridPredecessor_spec grid hstrict idx hidx
    exact output.candidate_mem x hx (pred idx) (Nat.le_of_lt hp.1)

/-
Package the output of the coupled construction once its survivor and
forbidden-profile cardinality estimates have been established.
-/
lemma RestrictedScaleTemplate.ofCandidates
    {𝒜 : DescriptionFamily} {U : Map} {n k c : ℕ} {t : ℕ → ℕ}
    (ambientLength : ℕ)
    (h_n_le : n ≤ ambientLength)
    (h_ambient_le : ambientLength ≤ n + logSlack c n)
    (goodSets : ℕ → Finset BitString)
    (h_mem : ∀ s (_hs : s ≤ k), 𝒜.mem (goodSets s))
    (h_size : ∀ s (_hs : s ≤ k), (goodSets s).card ≤ 2 ^ (t s + sqrtSlack c n))
    (h_complexity : ∀ s (_hs : s ≤ k) (hS : (goodSets s).Nonempty),
      setComplexity U (goodSets s) hS ≤ (s + sqrtSlack c n : ENat))
    (candidates : Finset BitString)
    (h_candidates_nonempty : candidates.Nonempty)
    (h_candidate_len : ∀ x ∈ candidates, x.length = ambientLength)
    (h_candidate_mem : ∀ x ∈ candidates, ∀ s (_hs : s ≤ k), x ∈ goodSets s)
    (h_candidate_complexity : ∀ x ∈ candidates,
      KPPlain U x ≤ (k + sqrtSlack c n : ENat))
    (survivor : BitString)
    (h_survivor_mem : survivor ∈ candidates)
    (h_survivor_not_bad :
      survivor ∉ restrictedProfileBadSet 𝒜 U candidates k (sqrtSlack c n) t) :
    Nonempty (RestrictedScaleTemplate 𝒜 U n k c t) := by
  obtain ⟨h_bad_subset, h_bad_exact⟩ :=
    restrictedProfileBadSet_spec 𝒜 U candidates k (sqrtSlack c n) t
  exact ⟨{
    ambientLength := ambientLength
    n_le_ambient := h_n_le
    ambient_le := h_ambient_le
    goodSets := goodSets
    mem_family := h_mem
    size_bound := h_size
    complexity_bound := h_complexity
    candidates := candidates
    candidates_nonempty := h_candidates_nonempty
    candidate_len := h_candidate_len
    candidate_mem := h_candidate_mem
    candidate_complexity := h_candidate_complexity
    badSet := restrictedProfileBadSet 𝒜 U candidates k (sqrtSlack c n) t
    badSet_subset_candidates := h_bad_subset
    badSet_exact := h_bad_exact
    survivor := survivor
    survivor_mem := h_survivor_mem
    survivor_not_bad := h_survivor_not_bad }⟩

/-- Filtering the output of a coupled process by the concrete forbidden-profile
set produces a scale template. -/
lemma RestrictedCoupledScaleProcess.toTemplate
    {𝒜 : DescriptionFamily} {U : Map} {n k c : ℕ} {t : ℕ → ℕ}
    (process : RestrictedCoupledScaleProcess 𝒜 U n k c t) :
    Nonempty (RestrictedScaleTemplate 𝒜 U n k c t) := by
  apply RestrictedScaleTemplate.ofCandidates
    process.ambientLength process.n_le_ambient process.ambient_le
    process.goodSets process.mem_family process.size_bound
    process.complexity_bound process.candidates process.candidates_nonempty
    process.candidate_len process.candidate_mem process.candidate_complexity
    process.survivor process.survivor_mem process.survivor_not_bad

/-
Polynomial covering overhead supplies a uniform square-root budget for
all sampled-scale covering costs.  This specializes
`restrictedCurveGrid_scale_budget` to the overhead function carried by the
family.
-/
lemma DescriptionFamily.sampled_cover_cost_le_sqrtSlack
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_budget : ℕ, ∀ (n N : ℕ),
      N ≤ Nat.sqrt (n / (Nat.log2 n + 1)) + 1 →
      N * (Nat.log2 (𝒜.overhead n) + 1) ≤ sqrtSlack c_budget n := by
  obtain ⟨C, d, hC, hbound⟩ := hPoly
  obtain ⟨c_budget, hc⟩ := restrictedCurveGrid_scale_budget C d hC
  exact ⟨c_budget, fun n N hN => hc n _ _ hbound hN⟩

/-
The pointwise suffix-density recurrence preserves a nonempty terminal
survivor pool.  This isolates the final positivity argument from the
chronological version-counting construction.
-/
lemma restricted_rebuild_suffix_preserves_terminal_nonempty
    (s k overheadBound : ℕ) (t : ℕ → ℕ)
    (live : ℕ → Finset BitString)
    (hsk : s ≤ k) (hLive : (live s).Nonempty)
    (hstep : ∀ i, s ≤ i → i < k →
      (2 ^ t (i + 1)) * (live i).card ≤
        (overheadBound * 2 ^ t i) * (live (i + 1)).card) :
    (live k).Nonempty := by
  have h_density :
      (2 ^ t k) * (live s).card ≤
        (overheadBound ^ (k - s) * 2 ^ t s) * (live k).card := by
    exact restricted_rebuild_suffix_density s k t overheadBound live hsk hstep
  exact restricted_rebuild_suffix_terminal_nonempty
    s k overheadBound t live hLive h_density

/-
A strict cardinality gap between a candidate pool and its bad subset
produces a concrete surviving candidate.
-/
lemma restricted_exists_survivor_outside_bad
    (candidates bad : Finset BitString)
    (hbad : bad ⊆ candidates) (hcard : bad.card < candidates.card) :
    ∃ x ∈ candidates, x ∉ bad := by
  exact Finset.exists_of_ssubset
    (hbad.ssubset_of_ne (by
      intro heq
      subst bad
      simp at hcard))

/-
Filtering a stabilized coupled output by the concrete forbidden-profile
set produces the corresponding scale template.
-/
lemma RestrictedCoupledOutput.toTemplate
    {𝒜 : DescriptionFamily} {U : Map} {n k c : ℕ} {t : ℕ → ℕ}
    (output : RestrictedCoupledOutput 𝒜 U n k c t) :
    Nonempty (RestrictedScaleTemplate 𝒜 U n k c t) := by
  apply RestrictedScaleTemplate.ofCandidates
    output.ambientLength output.n_le_ambient output.ambient_le
    output.goodSets output.mem_family output.size_bound
    output.complexity_bound output.candidates output.candidates_nonempty
    output.candidate_len output.candidate_mem output.candidate_complexity
    output.survivor output.survivor_mem output.survivor_not_bad

/-
A coupled output remains valid when its uniform slack constant is enlarged.
-/
lemma RestrictedCoupledOutput.mono_slack
    {𝒜 : DescriptionFamily} {U : Map} {n k c c' : ℕ} {t : ℕ → ℕ}
    (output : RestrictedCoupledOutput 𝒜 U n k c t) (hcc' : c ≤ c') :
    Nonempty (RestrictedCoupledOutput 𝒜 U n k c' t) := by
  obtain ⟨ ambientLength, n_le_ambient, ambient_le, goodSets, mem_family, size_bound,
           complexity_bound, candidates, candidates_nonempty, candidate_len, candidate_mem,
               candidate_complexity, survivor, survivor_mem, survivor_not_bad ⟩ := output;
  refine ⟨ ⟨ ambientLength, n_le_ambient, ?_, goodSets, mem_family, ?_, ?_, candidates,
              candidates_nonempty, candidate_len, candidate_mem, ?_, survivor, survivor_mem, ?_
                  ⟩ ⟩ <;> try linarith [ logSlack_mono_left hcc' n ];
  · exact fun s hs =>
      le_trans ( size_bound s hs )
          ( pow_le_pow_right₀ ( by decide ) ( Nat.add_le_add_left ( sqrtSlack_mono_left hcc' n ) _
                                              ) );
  · intro s hs hS; specialize complexity_bound s hs hS; exact le_trans complexity_bound (by
    exact_mod_cast Nat.add_le_add_left ( sqrtSlack_mono_left hcc' n ) s);
  · exact fun x hx =>
      le_trans ( candidate_complexity x hx ) ( by gcongr ; exact sqrtSlack_mono_left hcc' n );
  · intro h; contrapose! survivor_not_bad
    simp_all +decide only [KPPlain_eq_KP, restrictedProfileBadSet, gt_iff_lt, Finset.mem_filter,
      true_and]
    obtain ⟨ i, hi, hi', hi'' ⟩ := h; use i, hi; refine ⟨ lt_of_le_of_lt ?_ hi', ?_ ⟩;
    · exact sqrtSlack_mono_left hcc' n;
    · exact InDescriptionProfileIn.mono_j
        (Nat.sub_le_sub_left (Nat.succ_le_succ (sqrtSlack_mono_left hcc' n)) _) hi''

/-
It suffices to construct the dynamic output with a base slack constant:
the separate grid-coding allowance can then be absorbed monotonically.
-/
lemma restricted_coupled_output_uniform_of_base
    (𝒜 : DescriptionFamily) (U : Map) (c_run : ℕ)
    (hbase : ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      Nonempty (RestrictedCoupledOutput 𝒜 U n k c_run t)) :
    ∀ (c_grid n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      Nonempty (RestrictedCoupledOutput 𝒜 U n k (c_grid + c_run) t) := by
  intros c_grid n k t hk h0 hk0 ht;
  exact RestrictedCoupledOutput.mono_slack ( hbase n k t hk h0 hk0 ht |> Classical.choice )
      ( by linarith )

end Kolmogorov


