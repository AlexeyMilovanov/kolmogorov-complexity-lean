import KolmogorovMathlib.MonotoneComplexity.GacsDayBlockGeometry

/-!
# V2 spend-block spare-pair layout

Blueprint Stage C1 (proof doc v14 §9.0 item 2), the part both readings of the
block-encoding question agree on: spend pass `i` occupies a block of
`graySpendMult L i = 2^{(7−i)L}` spare `(subson, grandson)` pairs, laid out by
the cumulative offset `grayBlockSpendOffset`.  This module gives the block, its
size, and the pairwise disjointness / nodup of the eight blocks — the geometry
the block controller's slot construction and the source-ledger nodup consume.

Everything here is standalone (it does not touch the committed controller); the
capacity fact `grayBlockSpend_capacity` (in `GacsDayBlockGeometry`) guarantees
the offsets stay inside the spare region at the pinned gap.
-/

namespace Kolmogorov

/-- The spare-pair block of spend pass `pass`: `graySpendMult L pass` spare
pairs, starting at the cumulative offset of the earlier passes. -/
def grayBlockSpendPairs (b source L pass : Nat) : List (Fin b × Fin b) :=
  ((grayChargedSparePairs b source).drop (grayBlockSpendOffset L pass)).take
    (graySpendMult L pass)

/-- The spend pairs of a block pass are listed without repetition. -/
lemma grayBlockSpendPairs_nodup (b source L pass : Nat) :
    (grayBlockSpendPairs b source L pass).Nodup :=
  (grayChargedSparePairs_nodup b source).drop.take

/-- Each block has exactly its multiplicity many pairs, once the whole spend
population fits in the spare region (`grayBlockSpendOffset L 8 ≤ (b−source)·b`,
implied by `grayBlockSpend_capacity` at the pinned gap). -/
lemma grayBlockSpendPairs_length {b source L pass : Nat} (hpass : pass < 8)
    (hfit : grayBlockSpendOffset L 8 ≤ (b - source) * b) :
    (grayBlockSpendPairs b source L pass).length = graySpendMult L pass := by
  simp only [grayBlockSpendPairs, List.length_take, List.length_drop,
    grayChargedSparePairs_length]
  rw [Nat.min_eq_left]
  -- offset(pass) + mult(pass) = offset(pass+1) ≤ offset(8) ≤ (b−source)·b
  have hstep : grayBlockSpendOffset L pass + graySpendMult L pass =
      grayBlockSpendOffset L (pass + 1) := (grayBlockSpendOffset_succ L pass).symm
  have hmono : grayBlockSpendOffset L (pass + 1) ≤ grayBlockSpendOffset L 8 :=
    grayBlockSpendOffset_mono (by omega)
  omega

/-- A slice `(l.drop a).take b` of a nodup list is disjoint from a later slice
`(l.drop c).take d` whenever `a + b ≤ c`: the first lives in the prefix
`l.take (a+b)`, the second in the suffix `l.drop (a+b)`, and a nodup list
splits disjointly there. -/
lemma nodup_slice_disjoint {α : Type _} {l : List α} (hl : l.Nodup)
    {a b c d : Nat} (h : a + b ≤ c) :
    List.Disjoint ((l.drop a).take b) ((l.drop c).take d) := by
  have hsplit : l = l.take (a + b) ++ l.drop (a + b) := (List.take_append_drop _ _).symm
  have hdisj : (l.take (a + b)).Disjoint (l.drop (a + b)) := by
    have := hl
    rw [hsplit, List.nodup_append] at this
    exact List.disjoint_iff_ne.mpr this.2.2
  intro x hx hx'
  -- x is in the first slice ⊆ prefix
  have hxpre : x ∈ l.take (a + b) := by
    have hsub : (l.drop a).take b ⊆ l.take (a + b) := by
      rw [List.take_add]
      exact List.subset_append_right _ _
    exact hsub hx
  -- x is in the second slice ⊆ suffix
  have hxsuf : x ∈ l.drop (a + b) := by
    have hsub : (l.drop c).take d ⊆ l.drop (a + b) := by
      have hdd : l.drop c = (l.drop (a + b)).drop (c - (a + b)) := by
        rw [List.drop_drop]
        congr 1
        omega
      calc (l.drop c).take d ⊆ l.drop c := List.take_subset _ _
        _ = (l.drop (a + b)).drop (c - (a + b)) := hdd
        _ ⊆ l.drop (a + b) := List.drop_subset _ _
    exact hsub hx'
  exact hdisj hxpre hxsuf

/-- **The eight spend blocks are pairwise disjoint** (blueprint C1): distinct
passes occupy disjoint cumulative windows of the spare-pair list. -/
lemma grayBlockSpendPairs_disjoint {b source L i j : Nat} (hij : i < j) :
    List.Disjoint (grayBlockSpendPairs b source L i)
      (grayBlockSpendPairs b source L j) := by
  apply nodup_slice_disjoint (grayChargedSparePairs_nodup b source)
  -- offset i + mult i = offset (i+1) ≤ offset j
  have hstep : grayBlockSpendOffset L i + graySpendMult L i =
      grayBlockSpendOffset L (i + 1) := (grayBlockSpendOffset_succ L i).symm
  have hmono : grayBlockSpendOffset L (i + 1) ≤ grayBlockSpendOffset L j :=
    grayBlockSpendOffset_mono (by omega)
  omega

end Kolmogorov
