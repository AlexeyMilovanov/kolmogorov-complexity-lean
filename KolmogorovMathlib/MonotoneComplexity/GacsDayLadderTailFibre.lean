import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafB

/-!
# Slot fibres of one frozen round

Every accounting statement about a frozen tail round compares two descriptions
of the same finite data: a sum over the *slot positions* of the round (this is
what `totalRootRequestOnList` and `totalRootRequest` are) and a sum over the
*sons* `(i, c)` of the round (this is what `grayTailSonBase`,
`grayTailFrozenSonBase` and `grayTailOwnerCharge` are).

This module proves that the two descriptions agree, once and for all:

```text
grayTailSonBase_slotEntries_eq_sum   son increment  = sum over its slots
grayTail_selectedRequest_eq_sum_slots  selected request = sum over kept slots
grayTail_selectedRequest_eq_fibreSum   selected request = sum over kept sons
grayTail_totalRootRequest_eq_fibreSum  total request    = sum over all sons
```

No hypothesis on the round is needed: the identities are pure finite
bookkeeping, valid for an arbitrary slot list and an arbitrary move.  In
particular no `Nodup` assumption is used -- both sides are indexed by slot
positions, and a son that occupied several slots would simply collect the sum
of their requests.

`grayTail_frozenSonBase_eq_sum_rounds` (the former child `D1`) also lives here,
since Leaves C and D both need it; its statement and proof are unchanged.
-/

namespace Kolmogorov

open scoped BigOperators

/-! ### Auxiliary list identities -/

/-- Filtering a list before mapping is mapping with the discarded entries set
to zero. -/
theorem grayTail_list_sum_map_filter {α β : Type*} [AddCommMonoid β]
    (l : List α) (g : α → Bool) (f : α → β) :
    ((l.filter g).map f).sum = (l.map fun a => if g a then f a else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : g a = true <;> simp [h, ih]

/-- A mapped `List.range` sum is the corresponding `Finset.range` sum. -/
theorem grayTail_list_map_range_sum {β : Type*} [AddCommMonoid β] (N : ℕ) (f : ℕ → β) :
    ((List.range N).map f).sum = ∑ j ∈ Finset.range N, f j := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

/-- Exchanging a list sum with a finite sum. -/
theorem grayTail_list_sum_map_finsetSum {α σ : Type*} (l : List α) (s : Finset σ)
    (F : α → σ → ℚ) :
    (l.map fun p => ∑ z ∈ s, F p z).sum = ∑ z ∈ s, (l.map fun p => F p z).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

/-- A signed list sum splits. -/
theorem grayTail_list_map_signed_sum {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map fun p => 2 * f p - g p).sum = 2 * (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-! ### The son increment of a round as a sum over slot positions -/

/-- The accumulated increment of one son inside a list of slot entries. -/
theorem grayTailSonBase_eq_sum_map {n b : ℕ}
    (es : List (GrayTailSlot n b × ClientMove)) (i : Fin n) (c : Fin b) :
    grayTailSonBase es i c =
      (es.map fun p => if p.1.1 = i ∧ p.1.2.1 = c then getReq p.2 [] else 0).sum := by
  unfold grayTailSonBase
  induction es with
  | nil => simp
  | cons x l ih => by_cases h : x.1.1 = i ∧ x.1.2.1 = c <;> simp [h, ih]

/-- The increment a round gives to one son is the sum of the requests displayed
at the slot positions occupied by that son. -/
theorem grayTailSonBase_slotEntries_eq_sum {n b : ℕ}
    (slots : List (GrayTailSlot n b)) (m : FamilyClientMove) (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries slots m) i c =
      ∑ j : Fin slots.length,
        if (slots.get j).1 = i ∧ (slots.get j).2.1 = c then getFamilyReq m j.val [] else 0 := by
  rw [grayTailSonBase_eq_sum_map]
  unfold grayTailSlotEntries
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-! ### Selected requests as slot sums and as son sums -/

/-- The selected root request of a round is the sum over the kept slot
positions. -/
theorem grayTail_selectedRequest_eq_sum_slots {n b : ℕ}
    (keep : GrayTailSlot n b → Bool) (p : GrayTailRound n b) :
    totalRootRequestOnList (grayTailSelectedIndices keep p) p.move =
      ∑ j : Fin p.slots.length,
        if keep (p.slots.get j) then getFamilyReq p.move j.val [] else 0 := by
  classical
  set F : ℕ → ℚ := fun j =>
    if hj : j < p.slots.length then
      (if keep (p.slots.get ⟨j, hj⟩) then getFamilyReq p.move j [] else 0)
    else 0 with hF
  have hfin : ∑ j : Fin p.slots.length,
      (if keep (p.slots.get j) then getFamilyReq p.move j.val [] else 0)
      = ∑ j ∈ Finset.range p.slots.length, F j := by
    rw [← Fin.sum_univ_eq_sum_range F p.slots.length]
    exact Finset.sum_congr rfl (fun j _ => by simp [hF, j.isLt])
  rw [hfin, totalRootRequestOnList_eq_sum_map]
  unfold grayTailSelectedIndices
  rw [grayTail_list_sum_map_filter, grayTail_list_map_range_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjlt : j < p.slots.length := Finset.mem_range.mp hj
  simp [hF, hjlt]

/-- **The fibre identity.**  When the retained slots are selected by a
predicate on the son `(i, c)` alone, the selected root request of the round is
the sum of the son increments over the retained sons. -/
theorem grayTail_selectedRequest_eq_fibreSum {n b : ℕ} (p : GrayTailRound n b)
    (keepIC : Fin n → Fin b → Bool) :
    totalRootRequestOnList (grayTailSelectedIndices (fun s => keepIC s.1 s.2.1) p) p.move =
      ∑ z ∈ Finset.univ.filter (fun z : Fin n × Fin b => keepIC z.1 z.2 = true),
        grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2 := by
  classical
  rw [grayTail_selectedRequest_eq_sum_slots]
  simp only [grayTailSonBase_slotEntries_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hcond : ∀ z : Fin n × Fin b,
      ((p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2) ↔
        z = ((p.slots.get j).1, (p.slots.get j).2.1) :=
    fun z => ⟨fun h => Prod.ext h.1.symm h.2.symm, fun h => by subst h; exact ⟨rfl, rfl⟩⟩
  simp only [hcond]
  rw [Finset.sum_ite_eq' (Finset.univ.filter (fun z : Fin n × Fin b => keepIC z.1 z.2 = true))
    ((p.slots.get j).1, (p.slots.get j).2.1) (fun _ => getFamilyReq p.move j.val [])]
  by_cases hk : keepIC (p.slots.get j).1 (p.slots.get j).2.1 = true <;> simp

/-- The total root request of a round is the sum of all its son increments. -/
theorem grayTail_totalRootRequest_eq_fibreSum {n b : ℕ} (p : GrayTailRound n b) :
    totalRootRequest p.slots.length p.move =
      ∑ z : Fin n × Fin b, grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2 := by
  classical
  have h := grayTail_selectedRequest_eq_fibreSum p (fun _ _ => true)
  simp only [grayTailSelectedIndices_true, Finset.filter_true_of_mem,
    Finset.mem_univ, implies_true] at h
  rw [← totalRootRequestOnList_range]
  exact h

/-! ### The accumulated son increment (former child `D1`) -/

/-- **Child D1 (proved).**  The accumulated request of a source son is the sum
of the increments the individual frozen rounds gave it. -/
theorem grayTail_frozenSonBase_eq_sum_rounds {n b : ℕ}
    (frozen : GrayTailFrozen n b) (i : Fin n) (c : Fin b) :
    grayTailFrozenSonBase frozen i c =
      (frozen.map fun p =>
        grayTailSonBase (grayTailSlotEntries p.slots p.move) i c).sum := by
  unfold grayTailFrozenSonBase grayTailFrozenEntries
  induction frozen with
  | nil => simp [grayTailSonBase]
  | cons p rest ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [grayTailSonBase_append_globalEntries, ih]

end Kolmogorov
