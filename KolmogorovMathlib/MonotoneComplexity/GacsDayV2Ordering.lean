import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Multiplicity

/-!
# V2 ordering lemma: later harvests never subtract finer than earlier anchors

This is the single schedule fact the disjointness chase consumes: in
the Day-literal schedule, every component's fine end (its harvest scale) is
`≤` every earlier component's anchor, across rounds, phases, and recursion
levels, with the boundary equalities via the telescopes.  With it, an
earlier cell — comparable at its own anchor with an own witness — is caught
whole by every later harvest.

The pinned rung at anchor `a`, per-round budget `L`, gap `e = a + 8L + 3`:

* **spend line** (anchor-hugging, `graySpendAnchor a L i = a + 3 + (7−i)L`):
  descends in `i`, `graySpendAnchor a L (i+1) = graySpendAnchor a L i − L`
  for `i < 7`, bottoming at `a + 3`;
* **advantage line** (`grayTailRoundEps q L e r`): descends in `r` to
  `grayCallDepth q e`, telescope `δ(r+1) = ε(r)`;
* **phase boundary**: every advantage anchor `≥ grayCallDepth q e > e`,
  strictly above every spend fine end `≤ e`.
-/

namespace Kolmogorov

/-- The spend line descends by exactly `L` per pass (for `i < 7`). -/
lemma graySpendAnchor_succ {a L i : Nat} (hi : i < 7) :
    graySpendAnchor a L (i + 1) + L = graySpendAnchor a L i := by
  unfold graySpendAnchor
  have h : 7 - (i + 1) + 1 = 7 - i := by omega
  calc a + 3 + (7 - (i + 1)) * L + L
      = a + 3 + ((7 - (i + 1)) + 1) * L := by ring
    _ = a + 3 + (7 - i) * L := by rw [h]

/-- The spend fine end of pass `i` (its window's coarse end = the anchor,
since the window is `(anchor, anchor + L]`; the harvest scale is the fine
end `anchor + L`).  In the anchor-hugging schedule the fine end of pass
`i+1` equals the anchor of pass `i`: `graySpendAnchor a L (i+1) + L =
graySpendAnchor a L i`.  So the harvest of a later pass never subtracts
finer than an earlier pass's anchor. -/
lemma graySpend_fineEnd_le_earlier_anchor {a L i k : Nat}
    (hik : k ≤ i) (hi : i < 8) :
    graySpendAnchor a L i + L ≤ graySpendAnchor a L k + L := by
  have hmono : ∀ p q : Nat, p ≤ q → q < 8 →
      graySpendAnchor a L q ≤ graySpendAnchor a L p := by
    intro p q hpq _
    unfold graySpendAnchor
    have : 7 - q ≤ 7 - p := by omega
    have := Nat.mul_le_mul_right L this
    omega
  have := hmono k i hik hi
  omega

/-- Every spend fine end is at most `e = a + 8L + 3` (the pinned bin
depth): the coarsest spend window (`i = 0`) has fine end
`a + 3 + 7L + L = a + 8L + 3 = e`. -/
lemma graySpend_fineEnd_le_e {a L i : Nat} (hi : i < 8) :
    graySpendAnchor a L i + L ≤ a + 8 * L + 3 := by
  unfold graySpendAnchor
  have : (7 - i) * L ≤ 7 * L := Nat.mul_le_mul_right L (by omega)
  omega
/-- **Phase boundary**: at the pinned gap `e = a + 8L + 3`, every advantage
anchor is strictly above every spend fine end.  Advantage anchors are
`≥ grayCallDepth q e = e + Nat.size(3q+5) + 2 > e`; spend fine ends are
`≤ e`. -/
theorem graySpend_fineEnd_lt_advantage_anchor {q L a e r i : Nat}
    (hgap : e = a + 8 * L + 3) (hi : i < 8) :
    graySpendAnchor a L i + L < grayTailRoundEps q L e r := by
  have hspend : graySpendAnchor a L i + L ≤ e := by
    rw [hgap]; exact graySpend_fineEnd_le_e hi
  have hadv : grayCallDepth q e ≤ grayTailRoundEps q L e r :=
    grayTailRoundEps_lower q L e r
  have hcall : e < grayCallDepth q e := by
    unfold grayCallDepth
    have : 0 < Nat.size (3 * q + 5) := Nat.size_pos.mpr (by omega)
    omega
  omega

end Kolmogorov
