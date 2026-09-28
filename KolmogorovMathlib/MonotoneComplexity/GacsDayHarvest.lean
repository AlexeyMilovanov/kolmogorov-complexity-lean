import KolmogorovMathlib.MonotoneComplexity.GacsDayRoundCounting
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLegality

/-!
# The truncated foreign-union harvest (pre-controller)

The client's per-round exclusion list: for a component (a round's slots)
against a snapshot server move, the `δ`-truncations of the effective
allocations at valid *foreign* node tags.  For a single node this is Day's
`[I_δ(σ,t₀)]`; at the set level no `⋂`-identity is claimed.

This file sits below the charged controller so the spend phase can consult
the harvest in its own gray goal (plan XIII.1: the harvest is required for
the pass-0 reserve collision).  `grayHarvest_untouchable` is the two-case
length-cap legality lemma that keeps the presented sub-game server legal
against the augmented exclusion list.

The harvest chain invariant (`GrayTailHarvestChainV2`, needing the V2 round
record) is the audited chain design (now relocated into the controller).
-/

namespace Kolmogorov

/-- Two prefix-incomparable lists diverge: they share a common prefix and
then split on distinct heads. -/
lemma exists_divergence {x y : GacsDayNode}
    (hxy : ¬ (x <+: y ∨ y <+: x)) :
    ∃ z c₁ c₂ x' y', c₁ ≠ c₂ ∧
      x = z ++ c₁ :: x' ∧ y = z ++ c₂ :: y' := by
  induction x generalizing y with
  | nil => exact absurd (Or.inl (List.nil_prefix)) hxy
  | cons a x'' ih =>
      cases y with
      | nil => exact absurd (Or.inr (List.nil_prefix)) hxy
      | cons c y'' =>
          by_cases hac : a = c
          · subst hac
            have hxy' : ¬ (x'' <+: y'' ∨ y'' <+: x'') := by
              intro h
              rcases h with h | h
              · exact hxy (Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
              · exact hxy (Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
            obtain ⟨z, c₁, c₂, x', y', hne, hx, hy⟩ := ih hxy'
            exact ⟨a :: z, c₁, c₂, x', y', hne, by simp [hx], by simp [hy]⟩
          · exact ⟨[], a, c, x'', y'', hac, rfl, rfl⟩

/-- **Within-tree divergence.**  Cells allocated at prefix-incomparable
nodes of the same tree, at arbitrary times, are prefix-incomparable. -/
theorem not_prefixComparable_of_node_divergence {n b : Nat} {A : Allocation}
    {sm : Nat → FamilyServerMove} (hleg : familyServerPlayLegal n b A sm)
    {i : Nat} (hi : i < n) {s t : Nat} {x y : GacsDayNode}
    (hx : ∀ d ∈ x, d < b) (hy : ∀ d ∈ y, d < b)
    (hxy : ¬ (x <+: y ∨ y <+: x))
    {p q : BitString} (hp : p ∈ getFamilyAlloc (sm s) i x)
    (hq : q ∈ getFamilyAlloc (sm t) i y) :
    ¬ (p <+: q ∨ q <+: p) := by
  obtain ⟨z, c₁, c₂, x', y', hne, rfl, rfl⟩ := exists_divergence hxy
  have hplay := hleg.1 i hi
  have hc₁ : c₁ < b := hx c₁ (by simp)
  have hc₂ : c₂ < b := hy c₂ (by simp)
  -- lift both cells to the diverging sibling level, at a common time
  have hpz : allocationSubset
      (getAlloc (familyServerMoveAt (sm s) i) (z ++ c₁ :: x'))
      (getAlloc (familyServerMoveAt (sm s) i) (z ++ [c₁])) :=
    allocationSubset_getAlloc_of_prefix (hplay.1 s)
      ⟨x', by simp⟩ hx
  have hqz : allocationSubset
      (getAlloc (familyServerMoveAt (sm t) i) (z ++ c₂ :: y'))
      (getAlloc (familyServerMoveAt (sm t) i) (z ++ [c₂])) :=
    allocationSubset_getAlloc_of_prefix (hplay.1 t)
      ⟨y', by simp⟩ hy
  obtain ⟨p₁, hp₁, hp₁p⟩ := hpz p hp
  obtain ⟨q₁, hq₁, hq₁q⟩ := hqz q hq
  obtain ⟨p₀, hp₀, hp₀p₁⟩ := allocationSubset_mono_time hplay
    (le_max_left s t) (z ++ [c₁]) p₁ hp₁
  obtain ⟨q₀, hq₀, hq₀q₁⟩ := allocationSubset_mono_time hplay
    (le_max_right s t) (z ++ [c₂]) q₁ hq₁
  have hdisj := (hplay.1 (max s t)).2 z ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
    (by intro h; exact hne (congrArg Fin.val h))
  have hsep := hdisj p₀ hp₀ q₀ hq₀
  intro hcomp
  refine hsep ?_
  have hp₀p : p₀ <+: p := hp₀p₁.trans hp₁p
  have hq₀q : q₀ <+: q := hq₀q₁.trans hq₁q
  rcases hcomp with h | h
  · exact isPrefix_or_isPrefix_of_isPrefix (hp₀p.trans h) hq₀q
  · exact isPrefix_or_isPrefix_of_isPrefix hp₀p (hq₀q.trans h)

/-- A node incomparable with a slot's address is incomparable with every
extension of that address. -/
lemma node_foreign_of_extension {y z x' : GacsDayNode}
    (hyz : ¬ (y <+: z ∨ z <+: y)) :
    ¬ (y <+: z ++ x' ∨ z ++ x' <+: y) := by
  intro h
  rcases h with h | h
  · rcases Nat.lt_or_ge z.length y.length with hlen | hlen
    · exact hyz (Or.inr (List.prefix_of_prefix_length_le
        (z.prefix_append x') h (Nat.le_of_lt hlen)))
    · exact hyz (Or.inl (List.prefix_of_prefix_length_le h
        (z.prefix_append x') hlen))
  · exact hyz (Or.inr ((z.prefix_append x').trans h))

/-- **The harvest is untouchable** (the two-case length-cap argument): a
cell allocated at (an extension of) a slot's node, of length at most the
truncation scale `δ`, is prefix-incomparable with every harvest entry. -/
theorem grayHarvest_untouchable {n b : Nat} {A : Allocation}
    {sm : Nat → FamilyServerMove} (hleg : familyServerPlayLegal n b A sm)
    {δ t₀ u₁ : Nat} {slots : List (GrayTailSlot n b)}
    {s : GrayTailSlot n b} (hs : s ∈ slots)
    {x' : GacsDayNode} (hx' : ∀ d ∈ grayTailSlotNode s ++ x', d < b)
    {cs : BitString}
    (hcs : cs ∈ getFamilyAlloc (sm u₁) s.1.val (grayTailSlotNode s ++ x'))
    (hlen : cs.length ≤ δ)
    {u : BitString}
    (hu : u ∈ grayHarvest (n := n) (b := b) δ slots n (sm t₀)) :
    ¬ (cs <+: u ∨ u <+: cs) := by
  rw [mem_grayHarvest] at hu
  obtain ⟨i, y, c, hi, hvalid, hforeign, -, hc, rfl⟩ := hu
  have hyb : ∀ d ∈ y, d < b := by
    intro d hd
    have := List.all_eq_true.mp hvalid d hd
    exact of_decide_eq_true this
  -- the raw foreign cell is incomparable with the shown cell
  have hraw : ¬ (cs <+: c ∨ c <+: cs) := by
    have hfor := List.all_eq_true.mp hforeign s hs
    rw [Bool.or_eq_true] at hfor
    by_cases htree : i = s.1.val
    · subst htree
      have hnode : ¬ (y <+: grayTailSlotNode s ∨ grayTailSlotNode s <+: y) := by
        rcases hfor with h | h
        · exact absurd rfl (of_decide_eq_true h)
        · rw [Bool.not_eq_true'] at h
          exact of_decide_eq_false h
      have hdiv := node_foreign_of_extension (x' := x') hnode
      have hxy : ¬ ((grayTailSlotNode s ++ x') <+: y ∨
          y <+: (grayTailSlotNode s ++ x')) := fun h => hdiv h.symm
      intro hcomp
      exact not_prefixComparable_of_node_divergence hleg s.1.isLt
        hx' hyb hxy hcs hc hcomp
    · intro hcomp
      exact not_prefixComparable_of_family_regions hleg s.1.isLt hi
        (fun h => htree h.symm) hx' hyb hcs hc hcomp
  -- the two-case length-cap reduction to the raw cell
  intro hcomp
  rcases Nat.lt_or_ge δ c.length with hcd | hcd
  case inr =>
    rw [List.take_of_length_le hcd] at hcomp
    exact hraw hcomp
  case inl =>
    have hulen : (c.take δ).length = δ := by
      rw [List.length_take]
      omega
    have hcs_c : cs <+: c := by
      rcases hcomp with h | h
      · exact h.trans (List.take_prefix δ c)
      · have hlen2 : (c.take δ).length ≤ cs.length := h.length_le
        have hcseq : c.take δ = cs := List.IsPrefix.eq_of_length h
          (by omega)
        rw [← hcseq]
        exact List.take_prefix δ c
    exact hraw (Or.inl hcs_c)

end Kolmogorov
