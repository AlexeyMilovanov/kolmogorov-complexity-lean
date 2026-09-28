import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafA

/-!
# The geometric core of Leaf B

Leaf B has to certify, for one inactive source son `(i, c)`, an epsilon-reserve
`R` at a son-dependent time together with *exact freshness*: `R` is
incomparable with every cylinder that any frozen recursive call of the tail
controller displays, except the call of the son's own owner round at the son's
own slot.

The frozen calls split into two very different kinds:

* calls sitting at a slot **other** than `(i, c)` -- these are separated from
  `R` purely spatially, and the separation is what this module proves once and
  for all in `grayTail_anchoredReserve_fresh_of_slot_ne`;
* calls sitting at the son's **own** slot -- these can only be handled by the
  exit certificates `GrayTailReserveExit.prefix_allocations_fresh` and
  `GrayTailThresholdExit.prefix_allocations_fresh`, which is where the exit's
  checkpoint (no reserve existed before the owner round) enters.

For a call later than a reserve, the *anchored* predicate is genuinely needed:
an ordinary reserve carries no future-time information.  For a call no later than
the reserve, the ordinary predicate suffices because allocations only coarsen along
a legal play.  The terminal controller now records a persistent exit whose reserve
time dominates every frozen round, so Leaf B uses the latter direction.
-/

namespace Kolmogorov

/-- A cylinder displayed by the local server move of a round at slot `j` is a
cylinder allocated at the grandchild vertex that slot points to. -/
theorem grayTail_mem_localAlloc_imp_mem_family {n b D u : ℕ}
    {sm : ℕ → FamilyServerMove} (p : GrayTailRound n b)
    (j : Fin p.slots.length) {d : BitString}
    (hd : d ∈ getFamilyAlloc (grayTailLocalServerMove D p.slots (sm u)) j.val []) :
    d ∈ getFamilyAlloc (sm u) (p.slots.get j).1.val
      [(p.slots.get j).2.1.val, (p.slots.get j).2.2.val] := by
  rw [getFamilyAlloc_grayTailLocalServerMove p.slots (sm u) j.val j.isLt []
    (by simp)] at hd
  have hd' := (mem_truncAlloc.mp hd).1
  simpa [getFamilyAlloc, getAlloc_extractSubtreeServerMove] using hd'

/-- **Spatial separation of an anchored reserve from a foreign slot.**

If `R` is an anchored family reserve of the son `(i, c)` at time `t`, then `R`
is incomparable with every cylinder displayed by a frozen round at a slot whose
root or whose source son differs from `(i, c)` -- at *any* server time, earlier
or later than `t`.

For a later time the anchor is used through
`IsAnchoredTailFamilyReserve.excludes_incomparable_later` (same tree) and
`IsAnchoredTailFamilyReserve.excludes_other_tree_later` (other tree).  For an
earlier time the cylinder has a coarser companion at time `t`, and the
unanchored clauses of `IsTailFamilyReserve` already exclude it. -/
theorem grayTail_anchoredReserve_fresh_of_slot_ne
    {n b e L t : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm)
    {i : Fin n} {c : Fin b} {R : BitString}
    (hR : IsAnchoredTailFamilyReserve e b A n i.val (sm t) [c.val] R)
    (p : GrayTailRound n b) (j : Fin p.slots.length)
    (hne : (p.slots.get j).1 ≠ i ∨ (p.slots.get j).2.1 ≠ c)
    {d : BitString}
    (hd : d ∈ getFamilyAlloc
      (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm p.serverTime))
      j.val []) :
    ¬ (R <+: d ∨ d <+: R) := by
  classical
  set s := p.slots.get j with hs
  have hnode : ∀ z ∈ ([c.val] : GacsDayNode), z < b := by
    intro z hz
    simp only [List.mem_singleton] at hz
    subst z
    exact c.isLt
  have hgrand : ∀ z ∈ ([s.2.1.val, s.2.2.val] : GacsDayNode), z < b := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact s.2.1.isLt
    · exact s.2.2.isLt
  have hdfam : d ∈ getFamilyAlloc (sm p.serverTime) s.1.val
      [s.2.1.val, s.2.2.val] := grayTail_mem_localAlloc_imp_mem_family p j hd
  rcases hne with hroot | hson
  · -- a different outer root
    have hroot' : s.1.val ≠ i.val := fun h => hroot (Fin.ext h)
    obtain ⟨w, hw, hwd⟩ :=
      allocationSubset_getAlloc_root ((hsm.1 s.1.val s.1.isLt).1 p.serverTime)
        [s.2.1.val, s.2.2.val] hgrand d hdfam
    have hwroot : w ∈ getFamilyAlloc (sm p.serverTime) s.1.val [] := hw
    have hwfresh : ¬ (R <+: w ∨ w <+: R) := by
      rcases le_total t p.serverTime with hle | hle
      · exact IsAnchoredTailFamilyReserve.excludes_other_tree_later hsm i.isLt
          s.1.isLt hroot' hle hnode hR hwroot
      · obtain ⟨w', hw', hw'w⟩ :=
          allocationSubset_mono_time (hsm.1 s.1.val s.1.isLt) hle []
            w hwroot
        intro hcomp
        exact hR.1.2 s.1.val s.1.isLt hroot' w' hw'
          (prefixComparable_of_common_extension hcomp hw'w)
    intro hcomp
    exact hwfresh (prefixComparable_of_common_extension hcomp hwd)
  · -- the same outer root but a different source son
    have hincomp : ¬ (([c.val] : GacsDayNode) <+: [s.2.1.val, s.2.2.val] ∨
        ([s.2.1.val, s.2.2.val] : GacsDayNode) <+: [c.val]) := by
      have hne' : s.2.1.val ≠ c.val := fun h => hson (Fin.ext h)
      rintro (hpre | hpre)
      · exact hne' (Eq.symm (by simpa using (List.prefix_iff_eq_take.mp hpre)))
      · exact hne' (by simpa using (List.prefix_iff_eq_take.mp hpre))
    by_cases hi : s.1 = i
    · have hdfam' : d ∈ getFamilyAlloc (sm p.serverTime) i.val
          [s.2.1.val, s.2.2.val] := by
        rwa [hi] at hdfam
      rcases le_total t p.serverTime with hle | hle
      · exact IsAnchoredTailFamilyReserve.excludes_incomparable_later hsm i.isLt
          hle hnode hR hgrand hincomp hdfam'
      · obtain ⟨w, hw, hwd⟩ :=
          allocationSubset_mono_time (hsm.1 i.val i.isLt) hle
            [s.2.1.val, s.2.2.val] d hdfam'
        intro hcomp
        exact hR.1.1.2.2.1 [s.2.1.val, s.2.2.val] hgrand hincomp w hw
          (prefixComparable_of_common_extension hcomp hwd)
    · -- a different outer root again
      have hroot' : s.1.val ≠ i.val := fun h => hi (Fin.ext h)
      obtain ⟨w, hw, hwd⟩ :=
        allocationSubset_getAlloc_root ((hsm.1 s.1.val s.1.isLt).1 p.serverTime)
          [s.2.1.val, s.2.2.val] hgrand d hdfam
      have hwfresh : ¬ (R <+: w ∨ w <+: R) := by
        rcases le_total t p.serverTime with hle | hle
        · exact IsAnchoredTailFamilyReserve.excludes_other_tree_later hsm i.isLt
            s.1.isLt hroot' hle hnode hR hw
        · obtain ⟨w', hw', hw'w⟩ :=
            allocationSubset_mono_time (hsm.1 s.1.val s.1.isLt) hle []
              w hw
          intro hcomp
          exact hR.1.2 s.1.val s.1.isLt hroot' w' hw'
            (prefixComparable_of_common_extension hcomp hw'w)
      intro hcomp
      exact hwfresh (prefixComparable_of_common_extension hcomp hwd)

/-- **Freshness of a reserve against the son's own earlier calls.**

This is the common core of `GrayTailReserveExit.prefix_allocations_fresh` and
`GrayTailThresholdExit.prefix_allocations_fresh`, stated for an arbitrary
reserve time `t` and an arbitrary checkpoint before it: if no family reserve
existed at a checkpoint `S` which dominates the server times of the rounds of
`pre` and precedes `t`, then the reserve seen at time `t` is incomparable with
everything those rounds displayed at the son's own slot. -/
theorem grayTail_prefix_alloc_fresh_of_checkpoint
    {n b e L t : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hleg : familyServerPlayLegal n b A sm)
    {i : Fin n} {c : Fin b} {R : BitString}
    (hR : IsTailFamilyReserve e b A n i.val (sm t) [c.val] R)
    {pre : GrayTailFrozen n b}
    (hfresh : pre = [] ∨ ∃ S, (∀ r, r ∈ pre → r.serverTime ≤ S) ∧ S ≤ t ∧
      (getTailFamilyReserve e b A n i.val (sm S) [c.val]).isNone) :
    ∀ r, r ∈ pre → ∀ j : Fin r.slots.length,
      (r.slots.get j).1 = i → (r.slots.get j).2.1 = c →
      ∀ d ∈ getFamilyAlloc
        (grayTailLocalServerMove (r.epsDepth + L) r.slots (sm r.serverTime))
        j.val [],
        ¬ (R <+: d ∨ d <+: R) := by
  intro r hr j hji hjc d hd
  rcases hfresh with hempty | ⟨S, hmax, hSt, hnone⟩
  · subst pre
    simp at hr
  · have hrS : r.serverTime ≤ S := hmax r hr
    have hmono := allocationSubset_mono_time
      (hleg.1 i.val i.isLt) hrS [c.val, (r.slots.get j).2.2.val]
    have hdRaw : d ∈ getFamilyAlloc (sm r.serverTime) i.val
        [c.val, (r.slots.get j).2.2.val] := by
      have hd'' := grayTail_mem_localAlloc_imp_mem_family r j hd
      simpa only [hji, hjc] using hd''
    obtain ⟨d', hd', hd'd⟩ := hmono d hdRaw
    have hnot := IsTailFamilyReserve.not_tail_of_search_none hleg hSt hR hnone
    have hfreshR := IsTailReserve.fresh_of_not_before
      (hleg.1 i.val i.isLt) hSt
      (x := [c.val]) (by simp)
      hR.1 hnot
      (y := [c.val, (r.slots.get j).2.2.val]) (by simp)
      (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact c.isLt
        · exact (r.slots.get j).2.2.isLt)
      hd'
    intro hcomp
    exact hfreshR (prefixComparable_of_common_extension hcomp hd'd)

/-- A reserve observed after a frozen round is separated from every foreign
slot of that round. No anchor is needed because the displayed allocation is
transported forward to the reserve time. -/
theorem grayTail_reserve_fresh_of_slot_ne_before
    {n b e L t : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm)
    {i : Fin n} {c : Fin b} {R : BitString}
    (hR : IsTailFamilyReserve e b A n i.val (sm t) [c.val] R)
    (p : GrayTailRound n b) (j : Fin p.slots.length)
    (hpt : p.serverTime ≤ t)
    (hne : (p.slots.get j).1 ≠ i ∨ (p.slots.get j).2.1 ≠ c)
    {d : BitString}
    (hd : d ∈ getFamilyAlloc
      (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm p.serverTime))
      j.val []) :
    ¬ (R <+: d ∨ d <+: R) := by
  classical
  set s := p.slots.get j with hs
  have hgrand : ∀ z ∈ ([s.2.1.val, s.2.2.val] : GacsDayNode), z < b := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact s.2.1.isLt
    · exact s.2.2.isLt
  have hdfam : d ∈ getFamilyAlloc (sm p.serverTime) s.1.val
      [s.2.1.val, s.2.2.val] := grayTail_mem_localAlloc_imp_mem_family p j hd
  rcases hne with hroot | hson
  · have hrootNe : s.1.val ≠ i.val := fun h => hroot (Fin.ext h)
    obtain ⟨w, hw, hwd⟩ :=
      allocationSubset_getAlloc_root ((hsm.1 s.1.val s.1.isLt).1 p.serverTime)
        [s.2.1.val, s.2.2.val] hgrand d hdfam
    obtain ⟨wLater, hwLater, hwLaterPrefix⟩ :=
      allocationSubset_mono_time (hsm.1 s.1.val s.1.isLt) hpt [] w hw
    intro hcomp
    exact hR.2 s.1.val s.1.isLt hrootNe wLater hwLater
      (prefixComparable_of_common_extension
        (prefixComparable_of_common_extension hcomp hwd) hwLaterPrefix)
  · have hincomp : ¬ (([c.val] : GacsDayNode) <+: [s.2.1.val, s.2.2.val] ∨
        ([s.2.1.val, s.2.2.val] : GacsDayNode) <+: [c.val]) := by
      have hsonNe : s.2.1.val ≠ c.val := fun h => hson (Fin.ext h)
      rintro (hpre | hpre)
      · exact hsonNe (Eq.symm (by simpa using (List.prefix_iff_eq_take.mp hpre)))
      · exact hsonNe (by simpa using (List.prefix_iff_eq_take.mp hpre))
    by_cases hi : s.1 = i
    · have hdfamSame : d ∈ getFamilyAlloc (sm p.serverTime) i.val
          [s.2.1.val, s.2.2.val] := by
        rwa [hi] at hdfam
      obtain ⟨w, hw, hwd⟩ := allocationSubset_mono_time
        (hsm.1 i.val i.isLt) hpt [s.2.1.val, s.2.2.val] d hdfamSame
      intro hcomp
      exact hR.1.2.2.1 [s.2.1.val, s.2.2.val] hgrand hincomp w hw
        (prefixComparable_of_common_extension hcomp hwd)
    · have hrootNe : s.1.val ≠ i.val := fun h => hi (Fin.ext h)
      obtain ⟨w, hw, hwd⟩ :=
        allocationSubset_getAlloc_root ((hsm.1 s.1.val s.1.isLt).1 p.serverTime)
          [s.2.1.val, s.2.2.val] hgrand d hdfam
      obtain ⟨wLater, hwLater, hwLaterPrefix⟩ :=
        allocationSubset_mono_time (hsm.1 s.1.val s.1.isLt) hpt [] w hw
      intro hcomp
      exact hR.2 s.1.val s.1.isLt hrootNe wLater hwLater
        (prefixComparable_of_common_extension
          (prefixComparable_of_common_extension hcomp hwd) hwLaterPrefix)

end Kolmogorov
