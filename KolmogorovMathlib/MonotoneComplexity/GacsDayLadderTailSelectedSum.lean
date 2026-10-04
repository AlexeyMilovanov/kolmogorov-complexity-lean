import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailSelected

/-!
# Request identities and positive parts for selected tail slots

This module packages the two routine "Leaf 1 / Leaf 2" facts of
the Gacs-Day tail blueprint:

* the selected root-request of a frozen round is an honest filtered sum over
  the round's slots (`grayTail_selected_request_eq`), together with the two
  degenerate instances `keep = true` and `keep = false`;
* every frozen round supplies its hereditary inequality in *positive part*
  form (`grayTailRound_selected_positivePart`).

The positive-part form is the one the coupled hereditary arithmetic has to
retain: `grayMassOfCount` is nonnegative, so clamping the signed left-hand
side of `grayTailRound_selected_inequality` at zero costs nothing, while
summing the raw signed bounds over rounds and clamping only afterwards is a
strictly weaker (and in fact false) statement.
-/

namespace Kolmogorov

/-! ### `totalRootRequestOnList` as a plain list sum -/

/-- The root request over a list of clients is the sum of their root requests. -/
lemma totalRootRequestOnList_eq_sum_map (indices : List Nat)
    (c : FamilyClientMove) :
    totalRootRequestOnList indices c =
      (indices.map fun i => getFamilyReq c i []).sum := by
  unfold totalRootRequestOnList
  induction indices with
  | nil => simp
  | cons i l ih => simp [ih]

/-- The root request over no clients is zero. -/
@[simp] lemma totalRootRequestOnList_nil (c : FamilyClientMove) :
    totalRootRequestOnList [] c = 0 := rfl

/-- The root request over the first `n` clients is the total root request. -/
lemma totalRootRequestOnList_range (n : Nat) (c : FamilyClientMove) :
    totalRootRequestOnList (List.range n) c = totalRootRequest n c :=
  (totalRootRequest_eq_foldr n c).symm

/-! ### Selected indices -/

/-- A selected index is a slot index of the round. -/
lemma grayTailSelectedIndices_lt {n b : Nat}
    (keep : GrayTailSlot n b -> Bool) (p : GrayTailRound n b)
    {j : Nat} (hj : j ∈ grayTailSelectedIndices keep p) :
    j < p.slots.length := by
  have := List.mem_of_mem_filter (l := List.range p.slots.length) hj
  simpa using this

/-- The selected indices are listed without repetition. -/
lemma grayTailSelectedIndices_nodup {n b : Nat}
    (keep : GrayTailSlot n b -> Bool) (p : GrayTailRound n b) :
    (grayTailSelectedIndices keep p).Nodup :=
  (grayTailSelectedIndices_sublist keep p).nodup (List.nodup_range)

/-- An index is selected exactly when it is a slot index whose slot passes `keep`. -/
lemma mem_grayTailSelectedIndices_iff {n b : Nat}
    (keep : GrayTailSlot n b -> Bool) (p : GrayTailRound n b) (j : Nat) :
    j ∈ grayTailSelectedIndices keep p ↔
      ∃ hj : j < p.slots.length, keep (p.slots.get ⟨j, hj⟩) = true := by
  unfold grayTailSelectedIndices
  simp only [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hj, hkeep⟩
    rw [dite_eq_left hj] at hkeep
    exact ⟨hj, hkeep⟩
  · rintro ⟨hj, hkeep⟩
    exact ⟨hj, by rw [dite_eq_left hj]; exact hkeep⟩

/-- **Leaf 2.** The selected root-request of a frozen round is the sum of the
requests of exactly those slot positions the predicate keeps. -/
theorem grayTail_selected_request_eq {n b : Nat}
    (keep : GrayTailSlot n b -> Bool) (p : GrayTailRound n b) :
    totalRootRequestOnList (grayTailSelectedIndices keep p) p.move =
      (((List.range p.slots.length).filter fun j =>
          if hj : j < p.slots.length then keep (p.slots.get ⟨j, hj⟩)
          else false).map fun i => getFamilyReq p.move i []).sum := by
  rw [totalRootRequestOnList_eq_sum_map]
  rfl

/-- Keeping every slot recovers the round's total root request. -/
@[simp] theorem grayTailSelectedIndices_true {n b : Nat}
    (p : GrayTailRound n b) :
    grayTailSelectedIndices (fun _ => true) p = List.range p.slots.length := by
  unfold grayTailSelectedIndices
  refine List.filter_eq_self.2 ?_
  intro j hj
  simp only [List.mem_range] at hj
  rw [dite_eq_left hj]

/-- Selecting nothing yields no indices. -/
@[simp] theorem grayTailSelectedIndices_false {n b : Nat}
    (p : GrayTailRound n b) :
    grayTailSelectedIndices (fun _ => false) p = [] := by
  unfold grayTailSelectedIndices
  refine List.filter_eq_nil_iff.2 ?_
  intro j hj
  simp only [List.mem_range] at hj
  simp [dite_eq_left hj]

/-! ### Positive parts -/

/-- The mass attached to a cell count is nonnegative. -/
lemma grayMassOfCount_nonneg (deltaDepth count : Nat) :
    (0 : ℚ) ≤ grayMassOfCount deltaDepth count := by
  unfold grayMassOfCount
  positivity

/-- **Leaf 1.** The hereditary inequality of a frozen round, retained in
positive-part form.  Because the right-hand side is a nonnegative mass, the
clamped left-hand side is still a valid lower bound; this is the form that
must be summed over rounds. -/
theorem grayTailRound_selected_positivePart
    {n b q L e t : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {st : GrayTailState n b}
    (hcert : GrayTailCertified q L e A sm t st)
    {p : GrayTailRound n b} (hp : p ∈ st.frozen)
    (keep : GrayTailSlot n b -> Bool) :
    max 0 (halfAmplification q *
        (2 * totalRootRequestOnList
            (grayTailSelectedIndices keep p) p.move -
          totalRootRequest p.slots.length p.move)) <=
      grayMassOfCount (p.epsDepth + L)
        (newGrayCount p.epsDepth (p.epsDepth + L)
          (familyAllocatedOnList (grayTailSelectedIndices keep p)
            (grayTailLocalServerMove (p.epsDepth + L) p.slots
              (sm p.serverTime)))
          p.unavailable) :=
  max_le (grayMassOfCount_nonneg _ _)
    (grayTailRound_selected_inequality hcert hp keep)

end Kolmogorov
