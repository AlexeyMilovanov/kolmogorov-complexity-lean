import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Part03

/-!
# Improving a description: the size form

`improvingDescriptionsSize_of_complexity` derives the size form of the improving-description
statement from the complexity form, in the standard VS40 §3 way, and
`exists_description_smaller_size_of_many_logSlack` is the faithful logarithmic-slack target:
a string with many `(i, j)`-descriptions has one of strictly smaller size.

`snapshotCodes_toFinset_eq_of_max` and `snapshotDescList_eq_of_max` are the stabilisation
facts these use: past a time at which the halting count is maximal, the snapshot no longer
changes.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- **Size form as a corollary of the complexity form.**

The standard Section 3 derivation: the `(i, j - k)` size-improvement statement is
*not* an independent selector obligation but a corollary of the stronger
`(i - k, j)` complexity-improvement statement, obtained by the
portion/description-shift move (`inDescriptionProfile_portion`).

Sketch.  Set `k₀ = min k i` (so the complexity form, which needs `k₀ ≤ i`,
applies).  The complexity form gives an `(i - k₀ + s, j + s)`-description with
`s = logSlack c₁ (n+i+j)`.  Slicing it into `2^k` contiguous chunks and keeping
the chunk containing `x` (`inDescriptionProfile_portion`, `s := k`, legal since
`k ≤ j ≤ j + s`) yields complexity `(i - k₀ + s) + k + 2·|bits k| + c₀` and size
exponent `(j + s) - k + 1`.  Since `i - k₀ + k ≤ i + 1` (using
`ManyIJDescriptions.le_succ`: `k ≤ i + 1`), the complexity is `≤ i + (1 + s + 2·|bits k| + c₀)`,
and `2·|bits k| ≤ 2·|bits (n+i+j)|`, so the whole address overhead is absorbed
into the single visible slack `logSlack (c₁ + c₀ + 3) (n+i+j)`; the size exponent
`(j - k) + s + 1` is likewise `≤ (j - k) + logSlack (c₁ + c₀ + 3) (n+i+j)`. -/
theorem improvingDescriptionsSize_of_complexity (U : Map)
    (hU : IsOptimalPrefixConditional U) (hC : ImprovingDescriptionsComplexityLogSlack U) :
    ImprovingDescriptionsSizeLogSlack U := by
  obtain ⟨c1, hC⟩ := hC
  obtain ⟨c0, hportion⟩ := inDescriptionProfile_portion U hU
  refine ⟨c1 + c0 + 3, fun x n i j k hn hmany hk => ?_⟩
  have hk_le : k ≤ i + 1 := hmany.le_succ
  set k₀ := min k i with hk0
  have hk0k : k₀ ≤ k := min_le_left k i
  have hk0i : k₀ ≤ i := min_le_right k i
  have hmany0 : ManyIJDescriptions U x i j k₀ := hmany.mono_k hk0k
  set s1 := logSlack c1 (n + i + j) with hs1
  have hprof : InDescriptionProfile U x (i - k₀ + s1) (j + s1) := hC x n i j k₀ hn hmany0 hk0i
  have hk_le_size : k ≤ j + s1 := le_trans hk (Nat.le_add_right j s1)
  have hport := hportion x (i - k₀ + s1) (j + s1) k hprof hk_le_size
  set L := (Nat.bits k).length with hL
  set slack := logSlack (c1 + c0 + 3) (n + i + j) with hslack
  -- The single absorption inequality: address overhead fits inside the slack.
  have hkey : 1 + s1 + 2 * L + c0 ≤ slack := by
    have hLM : L ≤ (Nat.bits (n + i + j)).length := by
      rw [hL]; exact length_natBits_mono (by omega)
    rw [hs1, hslack, hL]
    unfold logSlack
    nlinarith [hLM, Nat.zero_le ((Nat.bits (n + i + j)).length), Nat.zero_le c0,
      Nat.zero_le c1, Nat.zero_le L]
  have hik : i - k₀ + k ≤ i + 1 := by omega
  have hBcomp : i - k₀ + s1 + k + 2 * L + c0 ≤ i + slack := by omega
  have hQsize : j + s1 - k + 1 ≤ j - k + slack := by omega
  exact (hport.mono_i hBcomp).mono_j hQsize

/-- Faithful logarithmic-slack target for the size-improvement half, now obtained
as the standard corollary of the complexity form via
`improvingDescriptionsSize_of_complexity`. -/
theorem exists_description_smaller_size_of_many_logSlack
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ImprovingDescriptionsSizeLogSlack U :=
  improvingDescriptionsSize_of_complexity U hU
    (exists_description_smaller_complexity_of_many_logSlack U hU)

/-- After a time at which the halting count at level `alpha` is maximal, the set of snapshot
codes no longer changes. -/
theorem snapshotCodes_toFinset_eq_of_max {c : Code} {U : Map} (hc : IsCodeFor c U) (alpha t t₀ : ℕ)
    (h_ge : t₀ ≤ t)
    (hmax : ∀ t', countHalts c alpha t' ≤ countHalts c alpha t₀) :
    (snapshotCodes c alpha t).toFinset = (snapshotCodes c alpha t₀).toFinset := by
  ext w
  simp only [List.mem_toFinset]
  constructor
  · intro hw
    unfold snapshotCodes at hw
    rw [List.mem_filterMap] at hw
    obtain ⟨p, hp, hw_run⟩ := hw
    have h_prod := runOut_sound hc hw_run
    exact code_mem_snapshot_of_max hc alpha t₀ hmax hp h_prod
  · intro hw
    exact snapshotCodes_mem_of_le h_ge hw

/-- After a time at which the halting count at level `i` is maximal, the snapshot description
list no longer changes. -/
theorem snapshotDescList_eq_of_max {c : Code} {U : Map} (hc : IsCodeFor c U) (i j t t₀ : ℕ)
    (h_ge : t₀ ≤ t)
    (hmax : ∀ t', countHalts c i t' ≤ countHalts c i t₀) :
    snapshotDescList c i j t = snapshotDescList c i j t₀ := by
  unfold snapshotDescList
  have h_eq : ((snapshotCodes c i t).filter isCanonicalUniformCodeBool).toFinset =
              ((snapshotCodes c i t₀).filter isCanonicalUniformCodeBool).toFinset := by
    ext w
    simp only [List.mem_toFinset, List.mem_filter]
    have h_set := snapshotCodes_toFinset_eq_of_max hc i t t₀ h_ge hmax
    rw [Finset.ext_iff] at h_set
    specialize h_set w
    simp only [List.mem_toFinset] at h_set
    rw [h_set]
  rw [h_eq]

end Kolmogorov
