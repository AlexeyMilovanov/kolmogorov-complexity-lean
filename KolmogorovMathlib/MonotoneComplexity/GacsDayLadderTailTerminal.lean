import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFlow
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayCompositionList

/-!
# Terminal certificates for the gray-ladder tail

A terminal controller has resolved every source son.  If the outer play has no
positive unserved request, both resolution branches yield a genuine
epsilon-reserve: an already detected reserve is unpacked, while a threshold
crossing makes the terminal strategy request exactly epsilon at that son, so
the request must eventually be served.
-/

namespace Kolmogorov

/-- Entries that request nothing at the root give son base zero. -/
lemma grayTailSonBase_eq_zero_of_root_zero {n b : Nat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    (i : Fin n) (c : Fin b)
    (hzero : forall p, p ∈ entries -> getReq p.2 [] = 0) :
    grayTailSonBase entries i c = 0 := by
  induction entries with
  | nil => simp [grayTailSonBase]
  | cons p entries ih =>
      have hp : getReq p.2 [] = 0 := hzero p (by simp)
      have ht : forall r, r ∈ entries -> getReq r.2 [] = 0 := by
        intro r hr
        exact hzero r (by simp [hr])
      unfold grayTailSonBase at ih ⊢
      simp only [List.foldr_cons]
      split_ifs <;> simp [hp, ih ht]

/-- With an empty current move the slots contribute nothing to any son base. -/
lemma grayTailSonBase_slotEntries_emptyMove {n b : Nat}
    (slots : List (GrayTailSlot n b)) (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries slots []) i c = 0 := by
  apply grayTailSonBase_eq_zero_of_root_zero
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  rfl

/-- In a terminal tail state the son base comes entirely from the frozen rounds. -/
lemma grayTail_terminal_sonBase_eq_frozen
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) :
    let st := grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
    grayTailSonBase
        (grayTailEntries st.frozen st.slots
          (if st.done then [] else grayTailCurrentMove q L e sigma st))
        i c = grayTailFrozenSonBase st.frozen i c := by
  dsimp only
  let st := grayTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  by_cases hdone : st.done = true
  · rw [ite_eq_left hdone, grayTailEntries, grayTailSonBase_append_globalEntries,
      grayTailSonBase_slotEntries_emptyMove]
    simp [grayTailFrozenSonBase]
  · have hempty : st.slots.isEmpty = true := by
      cases hs : st.slots.isEmpty with
      | false => simp [st, hdone, hs] at hterminal
      | true => rfl
    have hnil := List.isEmpty_iff.mp hempty
    rw [ite_eq_right hdone, hnil]
    simp [grayTailEntries, grayTailSlotEntries, grayTailFrozenSonBase]

/-- The tail output requests at a child of a client the son request computed from its entries. -/
lemma getFamilyReq_grayTailOutput_son
    {n b q L a e i c : Nat} {sigma : FamilyStrategyScheme}
    (st : GrayTailState n b) (hi : i < n) (hc : c < b) :
    getFamilyReq (grayTailOutput q L a e sigma st) i [c] =
      grayTailSonRequest
        (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
        (dyadicScale e)
        (grayTailEntries st.frozen st.slots
          (if st.done then [] else grayTailCurrentMove q L e sigma st))
        ⟨i, hi⟩ ⟨c, hc⟩ := by
  unfold grayTailOutput grayTailFamilyMove getFamilyReq familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi, hc]

/-- In a terminal state, a child whose frozen son base exceeds the service threshold is displayed
at the full scale `dyadicScale e`. -/
lemma getFamilyReq_grayTailOutput_son_of_terminal_threshold
    {n q L a e t i c : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hi : i < n) (hc : c < grayTailBranch q L a e)
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true)
    (hthreshold :
      dyadicScale e - dyadicScale e / (6 * halfAmplification q) <
        grayTailFrozenSonBase
          (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen
          ⟨i, hi⟩ ⟨c, hc⟩) :
    getFamilyReq
        (grayTailOutput q L a e sigma
          (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t))
        i [c] = dyadicScale e := by
  let st := grayTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  rw [getFamilyReq_grayTailOutput_son st hi hc]
  unfold grayTailSonRequest
  rw [grayTail_terminal_sonBase_eq_frozen hterminal]
  rw [ite_eq_left]
  simpa [st] using hthreshold

/-- In a terminal play without a positive unserved request, every resolved
source son owns an epsilon-reserve at some (son-dependent) time. -/
theorem grayTail_terminal_resolved_son_has_reserve
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (_ha : 1 <= a) (_hae : a <= e)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true)
    (hnotwin : ¬ familyClientWinsUnservedPositive n (2 * (q + 1))
      (grayTailBranch q L a e)
      (playClientFamily A n (grayTailStrategy q L a e sigma) sm) sm) :
    forall (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      GrayTailSonResolved e
          (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
          A sm
          (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen i c ->
        exists T R, IsTailFamilyReserve e (grayTailBranch q L a e)
          A n i.val (sm T) [c.val] R := by
  intro i c hresolved
  rcases hresolved with hthreshold | ⟨T, hreserve⟩
  · have hdisplay :
        playClientFamily A n (grayTailStrategy q L a e sigma) sm t =
          grayTailOutput q L a e sigma
            (grayTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t) := by
      simpa [grayTailBranch] using
        (playClientFamily_grayTailStrategy
          q L a e n sigma A sm t)
    have hreq :
        getFamilyReq
            (playClientFamily A n
              (grayTailStrategy q L a e sigma) sm t)
            i.val [c.val] = dyadicScale e := by
      rw [hdisplay]
      exact getFamilyReq_grayTailOutput_son_of_terminal_threshold
        i.isLt c.isLt hterminal hthreshold
    have hserve : exists T,
        Serves (getFamilyAlloc (sm T) i.val [c.val])
          (getFamilyReq
            (playClientFamily A n
              (grayTailStrategy q L a e sigma) sm t)
            i.val [c.val]) := by
      by_contra h
      push Not at h
      apply hnotwin
      refine ⟨i.val, i.isLt, t, [c.val], ?_, ?_, h, ?_⟩
      · simp
        omega
      · intro d hd
        simp only [List.mem_singleton] at hd
        subst d
        exact c.isLt
      · change 0 < getFamilyReq
          (playClientFamily A n (grayTailStrategy q L a e sigma) sm t)
          i.val [c.val]
        rw [hreq]
        exact dyadicScale_pos e
    obtain ⟨T, hT⟩ := hserve
    have hnode : forall d, d ∈ ([c.val] : GacsDayNode) ->
        d < grayTailBranch q L a e := by
      intro d hd
      simp only [List.mem_singleton] at hd
      subst d
      exact c.isLt
    rw [hreq] at hT
    obtain ⟨R, hR⟩ := exists_tailFamilyReserve_of_serves
      hsm i.isLt hnode hT
    exact ⟨T, R, hR⟩
  · obtain ⟨R, hR⟩ :=
      (getTailFamilyReserve_isSome_iff e
        (grayTailBranch q L a e) A n i.val (sm T) [c.val]).mp hreserve
    exact ⟨T, R, hR⟩

end Kolmogorov
