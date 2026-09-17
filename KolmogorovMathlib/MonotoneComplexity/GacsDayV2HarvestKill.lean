import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailConstruction

/-!
# The harvest straddle-kill (v15, step 1)

The geometric core of the Gács-faithful repair (blueprint "v15 direction
2026-09-05", audit R4): a cell of the pass's fine depth `δ` that is fresh with
respect to an unavailable list containing the pass's foreign harvest is
prefix-incomparable with every cylinder of length `≥ δ` that is comparable
with a harvested allocation.  Length ordering decides the direction
(`w <+: R`), the prefix chain transfers comparability to the allocation, and
the `δ`-truncation of that allocation is in the harvest.  No anchoring
(allocated prefix) is used anywhere.
-/

namespace Kolmogorov

/-- Length-ordered comparability: the shorter of two comparable strings is a
prefix of the longer. -/
lemma prefix_of_comparable_of_length_le {w R : BitString}
    (hlen : w.length ≤ R.length) (hcmp : w <+: R ∨ R <+: w) : w <+: R := by
  rcases hcmp with h | h
  · exact h
  · have heq : R = w := h.eq_of_length (le_antisymm h.length_le hlen)
    rw [heq]

/-- Prefix chain: a coarser-or-equal cell comparable with a cylinder that is
comparable with an allocation is comparable with the allocation. -/
lemma comparable_of_le_length_chain {w R y : BitString}
    (hlen : w.length ≤ R.length) (hwR : w <+: R ∨ R <+: w)
    (hRy : R <+: y ∨ y <+: R) : w <+: y ∨ y <+: w :=
  prefixComparable_of_prefix_of_prefixComparable
    (prefix_of_comparable_of_length_le hlen hwR) hRy

/-- A string of length `δ` comparable with `y` is comparable with `y.take δ`. -/
lemma comparable_take_of_comparable {w y : BitString} {δ : Nat}
    (hw : w.length = δ) (hcmp : w <+: y ∨ y <+: w) :
    w <+: y.take δ ∨ y.take δ <+: w := by
  rcases hcmp with h | h
  · left
    have hwy : y.take w.length = w := (List.prefix_iff_eq_take.mp h).symm
    rw [← hw, hwy]
  · right
    exact (List.take_prefix δ y).trans h

/-- A prefix of length `≤ k` is a prefix of the `k`-truncation. -/
lemma prefix_take_of_prefix_of_le {w z : BitString} {k : Nat}
    (hwz : w <+: z) (hk : w.length ≤ k) : w <+: z.take k := by
  have hw : w = z.take w.length := List.prefix_iff_eq_take.mp hwz
  have htt : (z.take k).take w.length = z.take w.length := by
    rw [List.take_take, min_eq_left hk]
  rw [List.prefix_iff_eq_take, htt]
  exact hw

/-- A coarser-or-equal cell comparable with `z` is a prefix of `z.take k`
whenever its length is at most `k`. -/
lemma prefix_take_of_comparable {w z : BitString} {k : Nat}
    (hk : w.length ≤ k) (hkz : k ≤ z.length) (hcmp : w <+: z ∨ z <+: w) :
    w <+: z.take k :=
  prefix_take_of_prefix_of_le
    (prefix_of_comparable_of_length_le (le_trans hk hkz) hcmp) hk

/-- **The harvest straddle-kill.**  A cell `w` of length `δ`, fresh with
respect to an unavailable list `U` containing the pass's harvest, is
prefix-incomparable with every cylinder `R` of length `≥ δ` comparable with
an allocation `c` at a valid foreign node of the snapshot. -/
theorem grayHarvest_kills_comparable {n b δ nn : Nat}
    {slots : List (GrayTailSlot n b)} {sm : FamilyServerMove} {U : Allocation}
    (hsub : ∀ u ∈ grayHarvest (n := n) (b := b) δ slots nn sm, u ∈ U)
    {w R c : BitString} {i : Nat} {x : GacsDayNode}
    (hw : w.length = δ) (hR : δ ≤ R.length)
    (hfresh : ¬ ∃ u ∈ U, w <+: u ∨ u <+: w)
    (hi : i < nn) (hx : grayNodeValidB b x = true)
    (hforeign : grayNodeForeignB slots i x = true)
    (hxmem : x ∈ (familyServerMoveAt sm i).map Prod.fst)
    (hc : c ∈ getAlloc (familyServerMoveAt sm i) x)
    (hRc : R <+: c ∨ c <+: R) :
    ¬ (w <+: R ∨ R <+: w) := by
  intro hwR
  have hlen : w.length ≤ R.length := by
    rw [hw]
    exact hR
  have hwc : w <+: c ∨ c <+: w := comparable_of_le_length_chain hlen hwR hRc
  have hwt : w <+: c.take δ ∨ c.take δ <+: w :=
    comparable_take_of_comparable hw hwc
  have hmem : c.take δ ∈ grayHarvest (n := n) (b := b) δ slots nn sm :=
    mem_grayHarvest.mpr ⟨i, x, c, hi, hx, hforeign, hxmem, hc, rfl⟩
  exact hfresh ⟨c.take δ, hsub _ hmem, hwt⟩

/-- The kill for a certified new-gray cell of the pass (its freshness clause
is the `newGrayCellsList` membership). -/
theorem newGrayCell_incomparable_of_harvest {n b δ nn eps : Nat}
    {slots : List (GrayTailSlot n b)} {sm : FamilyServerMove}
    {S U : List BitString}
    (hsub : ∀ u ∈ grayHarvest (n := n) (b := b) δ slots nn sm, u ∈ U)
    {p R c : BitString} {i : Nat} {x : GacsDayNode}
    (hp : p ∈ newGrayCellsList eps δ S U) (hR : δ ≤ R.length)
    (hi : i < nn) (hx : grayNodeValidB b x = true)
    (hforeign : grayNodeForeignB slots i x = true)
    (hxmem : x ∈ (familyServerMoveAt sm i).map Prod.fst)
    (hc : c ∈ getAlloc (familyServerMoveAt sm i) x)
    (hRc : R <+: c ∨ c <+: R) :
    ¬ (p <+: R ∨ R <+: p) := by
  obtain ⟨hlen, -, hfresh⟩ := mem_newGrayCellsList.mp hp
  exact grayHarvest_kills_comparable hsub hlen hR hfresh hi hx hforeign hxmem hc hRc

end Kolmogorov
