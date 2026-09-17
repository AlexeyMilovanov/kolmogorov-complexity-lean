import KolmogorovMathlib.Restricted.Selection
import KolmogorovMathlib.Restricted.EffectiveSelection
import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.Restricted.Improving.RestrictedDescriptions
import KolmogorovMathlib.Restricted.Improving.UniformComputability

/-!
# The restricted improving-description theorem

This module transfers the uniformly selected marked code back to an actual family member.
`selected_family_setComplexity_bound` controls the selected finite set, while
`exists_familyComplexityRefinedSet` produces a family member containing the target string with
both its cardinality and set complexity improved.

`inDescriptionProfileIn_improving_complexity` combines that construction with the elementary
size improvement. It is the restricted analogue of the improving-description theorem, with the
explicit logarithmic overhead carried by the marked address.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- The complexity bound for elements extracted from the marked stream.  The
nontrivial coding work is isolated in `selected_family_code_setComplexity_bound`;
this wrapper just decodes `IsFamilyDescriptionCode`, carrying forward family
membership, membership of `x`, and the `2^j` size bound. -/
theorem selected_family_setComplexity_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c U) (𝒜 : PreDescriptionFamily) :
    ∃ c_slack : ℕ, ∀ (x : BitString) (n i j k t : ℕ) (w : BitString),
      k ≤ i →
      w ∈ familyMarkedCodeStream c i 𝒜 n j k t →
      IsFamilyDescriptionCode 𝒜 j x w →
      ∃ (S : Finset BitString) (hS : S.Nonempty), 𝒜.mem S ∧ x ∈ S ∧
        setComplexity U S hS ≤ (i - k : ENat) + logSlack c_slack (n + i + j) ∧
        S.card ≤ 2 ^ j := by
  obtain ⟨c_slack, hcode⟩ := selected_family_code_setComplexity_bound U hU c hc 𝒜
  refine ⟨c_slack, fun x n i j k t w hk hw_stream hw_desc => ?_⟩
  rcases hw_desc with ⟨S, hS, hmem, hcode_eq, hcard, hxS⟩
  exact ⟨S, hS, hmem, hxS, hcode n i j k t w S hS hk hw_stream hcode_eq, hcard⟩

/-- **Selector obligation for the restricted complexity half.**

The concrete set-existence content of the restricted Improving Descriptions
theorem (complexity half), phrased exactly as the unrestricted
`setComplexity_halfRichComplexityPortion_le` /
`exists_halfRichComplexityRefinedSet_logSlack` (`Snapshots.lean`): an
effective selection over the family enumeration produces, for every length-`n`
string `x` with `2^k` restricted `(i,j)`-descriptions, a family member `S ∋ x`
of complexity `≤ (i-k) + O(log(n+i+j))` and log-size `≤ j + O(log(n+i+j))`.

Construction (parallel to the unrestricted `emittedHalfRichChunks` proof):
* `EffectiveSelection.lean` makes the finite-stage greedy selection effective,
  as an explicit computable marked-code stream over the family enumeration
  (`𝒜.enumeration.computable`); coverage is `selectionStrategy_covers`, and the
  count bound is `selectionStrategy_length_bound`
  (`≤ (i+1)²(n+1)2^(i+1-k)`, i.e. `2^(i-k)` up to the visible `poly(n)` factor);
* the marked set containing `x` is then recovered by its ordinal index in the
  marked stream, of length `≤ (i-k) + O(log n)`, via the M0 fixed-length index
  bound `StagedEnumeration.KP_le_fixed_length_index_of_cond_enumeration`.
Family membership `𝒜.mem S` is automatic from the enumeration soundness
(condition (1)); the complexity half uses only condition (1). -/
theorem exists_familyComplexityRefinedSet (U : Map)
    (hU : IsOptimalPrefixConditional U) (𝒜 : PreDescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      ManyIJDescriptionsIn 𝒜 U x i j k →
      k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), 𝒜.mem S ∧ x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (n + i + j) : ENat) ∧
        S.card ≤ 2 ^ (j + logSlack c (n + i + j)) := by
  obtain ⟨c_code, hc_code⟩ : ∃ c_code : Code, IsCodeFor c_code U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨c_slack, hc_slack⟩ := selected_family_setComplexity_bound U hU c_code hc_code 𝒜
  refine ⟨c_slack, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨t, ht⟩ := manyIJDescriptionsIn_visible_stage hc_code 𝒜 x n i j k hn hmany
  obtain ⟨w, hw_stream, hw_desc⟩ := familyMarkedCodeStream_covers_many c_code i 𝒜 n j k t x hn ht
  obtain ⟨S, hS, hmem, hxS, hcomp, hcard⟩ := hc_slack x n i j k t w hk hw_stream hw_desc
  refine ⟨S, hS, hmem, hxS, ?_, ?_⟩
  · exact hcomp
  · refine le_trans (Nat.cast_le.mpr hcard) ?_
    exact Nat.cast_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))

/-- Restricted Improving Descriptions (complexity half).  Proved from the
concrete selector obligation `exists_familyComplexityRefinedSet` by the standard
profile assembly (the same trivial glue as the proved unrestricted
`exists_description_smaller_complexity_of_many_logSlack`): the selected family
member `S ∋ x` is exactly an `𝒜`-description witnessing the shifted profile
point. -/
theorem inDescriptionProfileIn_improving_complexity (U : Map)
    (hU : IsOptimalPrefixConditional U) (𝒜 : DescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      ManyIJDescriptionsIn 𝒜 U x i j k →
      k ≤ i →
      InDescriptionProfileIn 𝒜 U x
        (i - k + logSlack c (n + i + j))
        (j + logSlack c (n + i + j)) := by
  obtain ⟨c, hc⟩ := exists_familyComplexityRefinedSet U hU 𝒜
  refine ⟨c, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨S, hS, hmem, hxS, hcomp, hcard⟩ := hc x n i j k hn hmany hk
  exact ⟨S, hS, hmem, hxS, hcomp, hcard⟩

end Kolmogorov


