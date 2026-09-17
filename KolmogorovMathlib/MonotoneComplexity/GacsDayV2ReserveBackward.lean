import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFresh

/-!
# v15 support: backward persistence of a family reserve (the weak R5)

If a cylinder `R` is a family tail reserve at a later time `T` and is
comparable with an allocation present at the son's node at an earlier time
`t`, then `R` is already a tail reserve at `t` (the cross-node exclusion
clauses are inherited backwards along `allocationSubset_mono_time`).
Hence, when the exhaustive plain search is empty at `t`, no allocation present
at `t` is comparable with `R`: a served ε-reserve of a raised son is fresh from
all of the son's earlier allocations, without claiming that none existed.
-/

namespace Kolmogorov

/-- Backward persistence: a family reserve at `T` comparable with an
allocation present at `t ≤ T` is a tail reserve at `t`. -/
lemma IsTailFamilyReserve.tail_at_earlier_of_comparable
    {e b n i t T : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {x : GacsDayNode} {R y : BitString}
    (hleg : familyServerPlayLegal n b A sm) (hi : i < n) (htT : t <= T)
    (hR : IsTailFamilyReserve e b A n i (sm T) x R)
    (hy : y ∈ getAlloc (familyServerMoveAt (sm t) i) x)
    (hRy : R <+: y ∨ y <+: R) :
    IsTailReserve e b A (familyServerMoveAt (sm t) i) x R := by
  obtain ⟨⟨hlen, -, hincomp, hA⟩, -⟩ := hR
  refine ⟨hlen, ⟨y, hy, hRy⟩, ?_, hA⟩
  intro z hz hzx c hc hcomp
  have hmono := allocationSubset_mono_time (hleg.1 i hi) htT z
  obtain ⟨d, hd, hdc⟩ := hmono c hc
  apply hincomp z hz hzx d hd
  exact prefixComparable_of_common_extension hcomp hdc

/-- **The weak R5**: when the plain search is empty at `t`, no allocation
present at the son's node at `t` is comparable with a cylinder that is a
family reserve at a later time `T`. -/
theorem IsTailFamilyReserve.earlier_allocation_incomparable_of_search_none
    {e b n i t T : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {x : GacsDayNode} {R y : BitString}
    (hleg : familyServerPlayLegal n b A sm) (hi : i < n) (htT : t <= T)
    (hR : IsTailFamilyReserve e b A n i (sm T) x R)
    (hnone : (getTailFamilyReserve e b A n i (sm t) x).isNone)
    (hy : y ∈ getAlloc (familyServerMoveAt (sm t) i) x) :
    ¬ (R <+: y ∨ y <+: R) := by
  intro hRy
  exact hR.not_tail_of_search_none hleg htT hnone
    (hR.tail_at_earlier_of_comparable hleg hi htT hy hRy)

end Kolmogorov
