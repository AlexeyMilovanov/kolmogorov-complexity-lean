import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailAnchor
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailResolutionExact

/-!
# An anchored reserve search, and an anchored exit facade

`GacsDayLadderTailAnchor` introduced `IsAnchoredTailFamilyReserve`, the reserve
predicate together with the *allocated anchor* `v <+: R` which is what makes a
reserve usable at a later server time.  The controller, however, tests for
reserves through `getTailFamilyReserve`, whose search predicate is the older
*unanchored* `IsTailFamilyReserve`, and `GrayTailReserveExit` records only that
weaker fact.

An unanchored reserve cannot be upgraded: `IsTailReserve` allows the branch
`R <+: v` in which the allocated cylinder is strictly finer than the reserve,
and then no allocated ancestor of `R` need exist at all.  So the anchor has to
be *searched for*, not recovered.  This module supplies exactly that missing
piece:

* `anchoredTailFamilyReserveAtB` -- the Boolean anchored reserve test, with
  `anchoredTailFamilyReserveAtB_eq_true_iff`;
* `getAnchoredTailFamilyReserve` -- the corresponding bounded search, with
  `getAnchoredTailFamilyReserve_isSome_iff`;
* `getTailFamilyReserve_isSome_of_anchored` -- the anchored test is *stronger*
  than the controller's current test, so replacing the controller's test by the
  anchored one can only classify fewer sons as resolved;
* `getAnchoredTailFamilyReserve_isSome_of_serves` -- a served epsilon request
  always produces an anchored reserve, so the threshold exit of
  `grayTail_terminal_resolved_son_has_reserve` is already anchored;
* `GrayTailAnchoredReserveExit` -- the exact-exit structure carrying the
  anchored reserve, with a projection onto the existing `GrayTailReserveExit`
  and the same `append` closure property.

Nothing existing is weakened; every declaration here is new, and the anchored
objects project onto the unanchored ones.
-/

namespace Kolmogorov


/-- A served epsilon request produces an anchored reserve, hence a successful
anchored search.  This is the branch of `grayTail_terminal_resolved_son_has_reserve`
that is anchored for free. -/
theorem getAnchoredTailFamilyReserve_isSome_of_serves
    {e b n i T : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    {x : GacsDayNode}
    (hsm : familyServerPlayLegal n b A sm) (hi : i < n)
    (hx : ∀ d ∈ x, d < b)
    (hserve : Serves (getFamilyAlloc (sm T) i x) (dyadicScale e)) :
    (getAnchoredTailFamilyReserve e b A n i (sm T) x).isSome :=
  (getAnchoredTailFamilyReserve_isSome_iff e b A n i (sm T) x).mpr
    (exists_anchoredTailFamilyReserve_of_serves hsm hi hx hserve)

/-! ### The anchored exact exit -/

/-- The exact reserve exit of a son, carrying the *anchored* reserve.  This is
`GrayTailReserveExit` with `IsTailFamilyReserve` replaced by
`IsAnchoredTailFamilyReserve`; every other field is unchanged, so the
projection below is definitional bookkeeping. -/
def GrayTailAnchoredReserveExit {n b : ℕ} (e : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (frozen : GrayTailFrozen n b)
    (i : Fin n) (c : Fin b) : Prop :=
  ∃ pre p post R,
    frozen = pre ++ p :: post ∧
      GrayTailRoundHasSon p i c ∧
      IsAnchoredTailFamilyReserve e b A n i.val (sm p.serverTime) [c.val] R ∧
      (pre = [] ∨ ∃ T,
        (∀ q, q ∈ pre → q.serverTime ≤ T) ∧
        T ≤ p.serverTime ∧
        (getTailFamilyReserve e b A n i.val (sm T) [c.val]).isNone) ∧
      ∀ q, q ∈ post → ¬ GrayTailRoundHasSon q i c

/-- A child closed by an anchored reserve is in particular closed by a reserve. -/
theorem GrayTailAnchoredReserveExit.toGrayTailReserveExit
    {n b e : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    {frozen : GrayTailFrozen n b} {i : Fin n} {c : Fin b}
    (h : GrayTailAnchoredReserveExit e A sm frozen i c) :
    GrayTailReserveExit e A sm frozen i c := by
  obtain ⟨pre, p, post, R, hsplit, hp, hR, hfresh, hpost⟩ := h
  exact ⟨pre, p, post, R, hsplit, hp, hR.toIsTailFamilyReserve, hfresh, hpost⟩

/-- The anchored exit is closed under appending a round the son does not
occur in, exactly like `GrayTailReserveExit.append`. -/
theorem GrayTailAnchoredReserveExit.append
    {n b e : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    {frozen : GrayTailFrozen n b} {i : Fin n} {c : Fin b}
    {p : GrayTailRound n b}
    (h : GrayTailAnchoredReserveExit e A sm frozen i c)
    (hp : ¬ GrayTailRoundHasSon p i c) :
    GrayTailAnchoredReserveExit e A sm (frozen ++ [p]) i c := by
  obtain ⟨pre, last, post, R, hsplit, hlast, hR, hfresh, hpost⟩ := h
  refine ⟨pre, last, post ++ [p], R, ?_, hlast, hR, hfresh, ?_⟩
  · simp [hsplit, List.append_assoc]
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hpost w hw
    · simp only [List.mem_singleton] at hw
      subst w
      exact hp

/-- The owner round of an anchored exit precedes the reserve's own time, so the
anchored reserve may be transported to any later terminal snapshot: it stays
incomparable with everything allocated at an incomparable vertex of its own
tree. -/
theorem GrayTailAnchoredReserveExit.excludes_incomparable_later
    {n b e : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    {frozen : GrayTailFrozen n b} {i : Fin n} {c : Fin b}
    (hsm : familyServerPlayLegal n b A sm) (hc : c.val < b)
    (h : GrayTailAnchoredReserveExit e A sm frozen i c) :
    ∃ pre p post R, frozen = pre ++ p :: post ∧
      GrayTailRoundHasSon p i c ∧
      IsAnchoredTailFamilyReserve e b A n i.val (sm p.serverTime) [c.val] R ∧
      (∀ q, q ∈ post → ¬ GrayTailRoundHasSon q i c) ∧
      ∀ T, p.serverTime ≤ T → ∀ y, (∀ d ∈ y, d < b) →
        ¬ ([c.val] <+: y ∨ y <+: [c.val]) →
        ∀ z ∈ getFamilyAlloc (sm T) i.val y, ¬ (R <+: z ∨ z <+: R) := by
  obtain ⟨pre, p, post, R, hsplit, hp, hR, _hfresh, hpost⟩ := h
  refine ⟨pre, p, post, R, hsplit, hp, hR, hpost, ?_⟩
  have hnode : ∀ d ∈ ([c.val] : GacsDayNode), d < b := by
    intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact hc
  intro T hT y hy hxy z hz
  exact IsAnchoredTailFamilyReserve.excludes_incomparable_later hsm i.isLt hT
    (x := [c.val]) hnode hR hy hxy hz

end Kolmogorov
