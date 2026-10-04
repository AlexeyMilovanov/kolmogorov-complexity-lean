import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailOwner

/-!
# The owner index as a total function, and owner fibres

`GacsDayLadderTailOwner.lean` produces, for one inactive used son at a terminal
state, a decomposition `frozen = pre ++ ownerRound :: post` of the frozen list
at the son's **last** participation, and proves that the decomposition is
unique.  Step 6.6 of the Gacs-Day tail blueprint needs more than one
son at a time: it charges the owner-round increment of *every* selected son,
grouped by round.  For that the owner has to be available as a total function
of the son, and the resulting fibres have to reassemble the total owner charge.

This module supplies exactly that layer, and nothing geometric:

* `GrayTailOwnerSplitAt frozen i c k` -- the son `(i, c)` leaves the frozen list
  after position `k`;
* `grayTail_ownerSplit_unique` and `grayTail_terminal_ownerSplit_existsUnique`
  -- there is exactly one such `k` for every inactive used son at a terminal
  state;
* `grayTailOwnerIndex`, a total (noncomputable) function returning that `k`,
  with `grayTailOwnerIndex_spec`, `grayTailOwnerIndex_eq`,
  `grayTailOwnerIndex_lt_length`, and `grayTailOwnerRound_mem`;
* `sum_owner_fibres`, the bookkeeping identity that regrouping any charge by
  owner round reproduces the total charge.

`sum_owner_fibres` is the precise sense in which the aggregate owner charge of
`GacsDayLadderTailFloorArithmetic` and the per-round owner charges of
`GacsDayLadderTailRoundSplit` describe the same data: the round-split credit
differs from the aggregated credit only through the clamping, never through the
bookkeeping.
-/

namespace Kolmogorov

open Finset

/-! ### The owner split, indexed by its position -/

/-- The son `(i, c)` participates in the frozen round at position `k` and in no
later round. -/
def GrayTailOwnerSplitAt {n b : Nat} (frozen : GrayTailFrozen n b)
    (i : Fin n) (c : Fin b) (k : Nat) : Prop :=
  ∃ pre p post, frozen = pre ++ p :: post ∧ pre.length = k ∧
    GrayTailRoundHasSon p i c ∧
    ∀ r ∈ post, ¬ GrayTailRoundHasSon r i c

/-- A threshold exit is an owner split at the length of its prefix. -/
theorem GrayTailThresholdExit.ownerSplitAt {n b e : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b} (h : GrayTailThresholdExit e A sm frozen i c) :
    ∃ k, GrayTailOwnerSplitAt frozen i c k := by
  obtain ⟨pre, p, post, hsplit, hson, _, hpost⟩ := h
  exact ⟨pre.length, pre, p, post, hsplit, rfl, hson, hpost⟩

/-- The position of the owner split is unique. -/
theorem grayTail_ownerSplit_unique {n b : Nat} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b} {k₁ k₂ : Nat}
    (h₁ : GrayTailOwnerSplitAt frozen i c k₁)
    (h₂ : GrayTailOwnerSplitAt frozen i c k₂) : k₁ = k₂ := by
  obtain ⟨pre₁, p₁, post₁, hs₁, hl₁, hson₁, hpost₁⟩ := h₁
  obtain ⟨pre₂, p₂, post₂, hs₂, hl₂, hson₂, hpost₂⟩ := h₂
  have := (last_split_unique hs₁ hs₂ hson₁ hson₂ hpost₁ hpost₂).1
  omega

/-- **Existence and uniqueness of the owner position** for every inactive used
son at a terminal controller state. -/
theorem grayTail_terminal_ownerSplit_existsUnique
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true)
    (i : Fin n) (c : Fin (grayTailBranch q L a e))
    (hused : c.val < 2 ^ (e - a))
    (hinactive : ¬ GrayTailHasSon
      (grayTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).slots i c) :
    ∃! k, GrayTailOwnerSplitAt
      (grayTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).frozen i c k := by
  obtain ⟨k, hk⟩ :=
    (grayTail_terminal_owner_decomposition hterminal i c hused hinactive).ownerSplitAt
  exact ⟨k, hk, fun k' hk' => grayTail_ownerSplit_unique hk' hk⟩

/-! ### The owner index as a total function -/

open Classical in
/-- The owner index of a son: the chosen `k` with `GrayTailOwnerSplitAt frozen i c k`, that is the
position of the last frozen round the son participates in, and `0` when the son participates in
no frozen round. Being total, it can be used to group the owner charges by round without a side
condition on the son. -/
noncomputable def grayTailOwnerIndex {n b : Nat} (frozen : GrayTailFrozen n b)
    (i : Fin n) (c : Fin b) : Nat :=
  if h : ∃ k, GrayTailOwnerSplitAt frozen i c k then h.choose else 0

/-- Where an owner split exists, `grayTailOwnerIndex` returns one. -/
theorem grayTailOwnerIndex_spec {n b : Nat} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b} (h : ∃ k, GrayTailOwnerSplitAt frozen i c k) :
    GrayTailOwnerSplitAt frozen i c (grayTailOwnerIndex frozen i c) := by
  classical
  rw [grayTailOwnerIndex, dite_eq_left h]
  exact h.choose_spec

/-- Any owner position is *the* owner index. -/
theorem grayTailOwnerIndex_eq {n b : Nat} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b} {k : Nat}
    (hk : GrayTailOwnerSplitAt frozen i c k) :
    grayTailOwnerIndex frozen i c = k :=
  grayTail_ownerSplit_unique (grayTailOwnerIndex_spec ⟨k, hk⟩) hk

/-- The owner index is a genuine position in the frozen list. -/
theorem grayTailOwnerIndex_lt_length {n b : Nat} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b} (h : ∃ k, GrayTailOwnerSplitAt frozen i c k) :
    grayTailOwnerIndex frozen i c < frozen.length := by
  obtain ⟨pre, p, post, hsplit, hlen, _, _⟩ := grayTailOwnerIndex_spec h
  rw [← hlen, hsplit]
  simp

/-- The frozen round sitting at the owner index really contains the son. -/
theorem grayTailOwnerIndex_getElem {n b : Nat} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b} (h : ∃ k, GrayTailOwnerSplitAt frozen i c k) :
    GrayTailRoundHasSon
      (frozen[grayTailOwnerIndex frozen i c]'(grayTailOwnerIndex_lt_length h)) i c := by
  obtain ⟨pre, p, post, hsplit, hlen, hson, _⟩ := grayTailOwnerIndex_spec h
  have : frozen[grayTailOwnerIndex frozen i c]'(grayTailOwnerIndex_lt_length h) = p := by
    simp only [← hlen]
    rw [List.getElem_of_eq hsplit]
    simp
  rw [this]
  exact hson

/-! ### Regrouping a charge by owner round -/

/-- **Owner fibres reassemble the total charge.**  Grouping any per-son charge
by the son's owner round and summing the rounds returns the total charge.  This
is the bookkeeping half of step 6.6; the arithmetic half is the clamping gain
of `GacsDayLadderTailRoundSplit`. -/
theorem sum_owner_fibres {σ : Type*} (S : Finset σ)
    (owner : σ → Nat) (m : Nat) (hm : ∀ s ∈ S, owner s < m) (f : σ → ℚ) :
    ∑ k ∈ range m, ∑ s ∈ S.filter (fun s => owner s = k), f s = ∑ s ∈ S, f s := by
  classical
  refine Finset.sum_fiberwise_of_maps_to ?_ f
  intro s hs
  exact mem_range.mpr (hm s hs)

end Kolmogorov
