import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailResolutionExact

/-!
# The owner round of a resolved son

Step 6.4 of the Gacs-Day tail blueprint asks for an *owner* round for
every son that has left the active set: the **last** frozen round in which the
son participated, together with the guarantee that it participates in no later
round.  Both terminal exits already carry that data.
`GrayTailPersistentReserveExit` and `GrayTailThresholdExit` use the same owner
decomposition; the former additionally records a reserve time dominating every
frozen round -- but the two branches
are exposed separately, and the resulting owner is not yet known to be unique.

This module

* projects reserve exits onto the common owner decomposition;
* derives one *branch-free* owner decomposition for every inactive used son at
  a terminal state (`grayTail_terminal_owner_decomposition`);
* records that the owner is a genuine element of the frozen list; and
* proves the owner is **unique**: any two decompositions of the same frozen
  list whose tail avoids the son have the same prefix length and the same
  owner round (`grayTail_owner_unique`).

Uniqueness is what step 6.6 needs in order to charge each selected son's
owner-round increment exactly once.
-/

namespace Kolmogorov

/-! ### The common owner decomposition -/

/-- A reserve exit is in particular an owner decomposition. -/
theorem GrayTailReserveExit.toThresholdExit {n b e : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b}
    (h : GrayTailReserveExit e A sm frozen i c) :
    GrayTailThresholdExit e A sm frozen i c := by
  obtain ⟨pre, p, post, R, hsplit, hson, _hres, hfresh, hpost⟩ := h
  exact ⟨pre, p, post, hsplit, hson, hfresh, hpost⟩

/-- A persistent reserve exit carries the same owner decomposition. -/
theorem GrayTailPersistentReserveExit.toThresholdExit {n b e : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {frozen : GrayTailFrozen n b} {i : Fin n} {c : Fin b}
    (h : GrayTailPersistentReserveExit e A sm frozen i c) :
    GrayTailThresholdExit e A sm frozen i c := by
  obtain ⟨pre, p, post, reserveTime, R, hsplit, hson, _hres, _hmax,
    hfresh, hpost⟩ := h
  exact ⟨pre, p, post, hsplit, hson, hfresh, hpost⟩

/-- **Every inactive used son has an owner round.**  This is the branch-free
form of `grayTail_terminal_detailed_resolution`: whichever exit the son took,
the frozen list splits at its last participation. -/
theorem grayTail_terminal_owner_decomposition
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
    GrayTailThresholdExit e A sm
      (grayTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).frozen i c := by
  rcases grayTail_terminal_detailed_resolution hterminal i c hused hinactive with
    ⟨_, hexit⟩ | ⟨hexit, _⟩
  · exact hexit
  · exact hexit.toThresholdExit

/-- The owner round really belongs to the frozen list. -/
theorem GrayTailThresholdExit.owner_mem {n b e : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b}
    (h : GrayTailThresholdExit e A sm frozen i c) :
    ∃ p ∈ frozen, GrayTailRoundHasSon p i c := by
  obtain ⟨pre, p, post, hsplit, hson, _, _⟩ := h
  exact ⟨p, by rw [hsplit]; simp, hson⟩

/-! ### Uniqueness of the owner -/

/-- A list decomposition whose tail avoids a predicate pins down the split
point.  This is the abstract content of owner uniqueness. -/
theorem last_split_unique {α : Type*} {P : α → Prop}
    {l pre₁ post₁ pre₂ post₂ : List α} {p₁ p₂ : α}
    (h₁ : l = pre₁ ++ p₁ :: post₁) (h₂ : l = pre₂ ++ p₂ :: post₂)
    (hp₁ : P p₁) (hp₂ : P p₂)
    (hpost₁ : ∀ r ∈ post₁, ¬ P r) (hpost₂ : ∀ r ∈ post₂, ¬ P r) :
    pre₁.length = pre₂.length ∧ p₁ = p₂ := by
  have key : ∀ (a₁ a₂ : List α) (q₁ q₂ : α) (b₁ b₂ : List α),
      l = a₁ ++ q₁ :: b₁ → l = a₂ ++ q₂ :: b₂ → P q₂ →
      (∀ r ∈ b₁, ¬ P r) → a₁.length < a₂.length → False := by
    intro a₁ a₂ q₁ q₂ b₁ b₂ hl₁ hl₂ hq₂ hb₁ hlt
    have hd₁ : l.drop (a₁.length + 1) = b₁ := by
      rw [hl₁, ← List.drop_drop]
      simp
    have hd₂ : l.drop a₂.length = q₂ :: b₂ := by
      rw [hl₂]
      simp
    have hsplit : l.drop a₂.length =
        (l.drop (a₁.length + 1)).drop (a₂.length - (a₁.length + 1)) := by
      rw [List.drop_drop]
      congr 1
      omega
    have hmem : q₂ ∈ b₁ := by
      have : q₂ ∈ (l.drop (a₁.length + 1)).drop (a₂.length - (a₁.length + 1)) := by
        rw [← hsplit, hd₂]; simp
      rw [hd₁] at this
      exact List.mem_of_mem_drop this
    exact hb₁ q₂ hmem hq₂
  have hlen : pre₁.length = pre₂.length := by
    rcases lt_trichotomy pre₁.length pre₂.length with hlt | heq | hgt
    · exact absurd (key pre₁ pre₂ p₁ p₂ post₁ post₂ h₁ h₂ hp₂ hpost₁ hlt) (by simp)
    · exact heq
    · exact absurd (key pre₂ pre₁ p₂ p₁ post₂ post₁ h₂ h₁ hp₁ hpost₂ hgt) (by simp)
  refine ⟨hlen, ?_⟩
  have hd₁ : l.drop pre₁.length = p₁ :: post₁ := by rw [h₁]; simp
  have hd₂ : l.drop pre₂.length = p₂ :: post₂ := by rw [h₂]; simp
  rw [hlen, hd₂] at hd₁
  exact ((List.cons.injEq _ _ _ _ ▸ hd₁).1).symm

/-- **The owner round of a son is unique.** -/
theorem grayTail_owner_unique {n b e : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b}
    (h₁ : GrayTailThresholdExit e A sm frozen i c) :
    ∃ p, (∃ pre post, frozen = pre ++ p :: post ∧
      (∀ r ∈ post, ¬ GrayTailRoundHasSon r i c)) ∧
      GrayTailRoundHasSon p i c ∧
      ∀ pre₁ p₁ post₁, frozen = pre₁ ++ p₁ :: post₁ →
        GrayTailRoundHasSon p₁ i c →
        (∀ r ∈ post₁, ¬ GrayTailRoundHasSon r i c) → p₁ = p := by
  obtain ⟨pre, p, post, hsplit, hson, _, hpost⟩ := h₁
  refine ⟨p, ⟨pre, post, hsplit, hpost⟩, hson, ?_⟩
  intro pre₁ p₁ post₁ hsplit₁ hson₁ hpost₁
  exact (last_split_unique hsplit₁ hsplit hson₁ hson hpost₁ hpost).2

end Kolmogorov
