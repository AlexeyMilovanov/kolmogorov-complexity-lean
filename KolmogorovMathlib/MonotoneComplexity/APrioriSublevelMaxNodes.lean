import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelTree
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelStage

/-!
# Maximal nodes of a finite set of bitstrings

Auxiliary combinatorics for the address-assignment construction: the set `maxNodes S` of
prefix-maximal elements of a finite set `S` of bitstrings, its cardinality bound coming from
the Kraft inequality for the a priori semimeasure, and how its cardinality changes when a new
leaf is inserted.
-/

noncomputable section

namespace Kolmogorov

open Classical in
/-- The members of `S` that no other member of `S` extends. -/
def maxNodes (S : Finset BitString) : Finset BitString :=
  S.filter (fun x => ∀ y ∈ S, x <+: y → x = y)

/-- The maximal nodes of a finite set form an antichain for the prefix order. -/
lemma maxNodes_antichain (S : Finset BitString) :
    ∀ x ∈ maxNodes S, ∀ y ∈ maxNodes S, x <+: y → x = y := by
  intro x hx y hy hxy
  rw [maxNodes, Finset.mem_filter] at hx hy
  exact hx.2 y hy.1 hxy

/-- Every member of a finite set extends to a maximal node of that set. -/
lemma exists_le_maxNode (S : Finset BitString) (x : BitString) (hx : x ∈ S) :
    ∃ y ∈ maxNodes S, x <+: y := by
  classical
  let S_above := S.filter (fun y => x <+: y)
  have h_nonempty : S_above.Nonempty := ⟨x, Finset.mem_filter.2 ⟨hx, List.prefix_refl x⟩⟩
  obtain ⟨y, hy, hmax⟩ := S_above.exists_max_image (fun y => y.length) h_nonempty
  use y
  rw [Finset.mem_filter] at hy
  constructor
  · rw [maxNodes, Finset.mem_filter]
    refine ⟨hy.1, ?_⟩
    intro z hz hyz
    have hz_above : z ∈ S_above := Finset.mem_filter.2 ⟨hz, List.IsPrefix.trans hy.2 hyz⟩
    have hlen := hmax z hz_above
    exact hyz.eq_of_length (le_antisymm hyz.length_le hlen)
  · exact hy.2

open Classical in
/-- A finite set inside the `k`-th a priori sublevel has at most `2 ^ k` maximal nodes. -/
lemma maxNodes_card_le_of_subset_kaSublevel {k : ℕ} {S : Finset BitString}
    (hS : ∀ x ∈ S, x ∈ kaSublevel k) :
    (maxNodes S).card ≤ 2 ^ k := by
  apply kaSublevel_card_le_pow _ (fun x hx => hS x (Finset.mem_filter.1 hx).1)
  exact maxNodes_antichain S

/-- Every nonempty string has an immediate prefix, one bit shorter. -/
lemma exists_immediate_prefix (x : BitString) (hx_not_empty : x ≠ []) :
    ∃ y, y <+: x ∧ y.length + 1 = x.length := by
  refine ⟨x.dropLast, List.dropLast_prefix x, ?_⟩
  rw [List.length_dropLast]
  have : x.length ≥ 1 := by
    cases x with
    | nil => exact absurd rfl hx_not_empty
    | cons h t => simp
  omega

/-- Adding a string whose immediate prefix is not maximal increases the number of maximal nodes by
one. -/
lemma maxNodes_insert_of_not_maximal {S : Finset BitString} {x : BitString}
    (hx_not_mem : x ∉ S)
    (hS_pc : ∀ a b, a <+: b → b ∈ S → a ∈ S)
    (hx_prefixes : ∀ z, z <+: x → z ≠ x → z ∈ S)
    (y : BitString) (hy_imm : y <+: x ∧ y.length + 1 = x.length) (hy_not_max : y ∉ maxNodes S) :
    (maxNodes (insert x S)).card = (maxNodes S).card + 1 := by
  classical
  have hno_ext : ∀ w ∈ S, x <+: w → x = w := by
    intro w hw hxw
    by_contra hne
    exact hx_not_mem (hS_pc x w hxw hw)
  have prefix_of_prefix_le {a b : BitString} (ha : a <+: x) (hb : b <+: x)
      (hle : a.length ≤ b.length) : a <+: b := by
    have hax := ha.length_le
    rw [List.prefix_iff_eq_take] at ha hb ⊢
    rw [ha, hb, List.length_take, min_eq_left hax, List.take_take, min_eq_left hle]
  have hno_strict_max : ∀ z, z ∈ maxNodes S → z <+: x → z = x := by
    intro z hz hzx
    rw [maxNodes, Finset.mem_filter] at hz
    by_contra hne
    have hy_in_S : y ∈ S := hx_prefixes y hy_imm.1 (by
      intro heq; subst heq; omega)
    have hzlen : z.length < x.length := by
      rcases lt_or_eq_of_le hzx.length_le with h | h
      · exact h
      · exact absurd (hzx.eq_of_length h) hne
    have hzy : z <+: y := by
      apply prefix_of_prefix_le hzx hy_imm.1; omega
    by_cases heq : z = y
    · subst heq; exact hy_not_max (Finset.mem_filter.mpr hz)
    · exact absurd (hz.2 y hy_in_S hzy) heq
  suffices h : maxNodes (insert x S) = maxNodes S ∪ {x} by
    rw [h, Finset.card_union_of_disjoint]
    · simp
    · exact Finset.disjoint_singleton_right.mpr (fun hx =>
        hx_not_mem (Finset.mem_filter.mp hx).1)
  ext z
  simp only [Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro hz
    rw [maxNodes, Finset.mem_filter] at hz
    rcases Finset.mem_insert.mp hz.1 with rfl | hzS
    · right; rfl
    · left; rw [maxNodes, Finset.mem_filter]
      exact ⟨hzS, fun w hw hzw => hz.2 w (Finset.mem_insert_of_mem hw) hzw⟩
  · intro hz
    rw [maxNodes, Finset.mem_filter]
    rcases hz with hz | rfl
    · rw [maxNodes, Finset.mem_filter] at hz
      refine ⟨Finset.mem_insert_of_mem hz.1, fun w hw hzw => ?_⟩
      rcases Finset.mem_insert.mp hw with rfl | hwS
      · exact hno_strict_max z (Finset.mem_filter.mpr hz) hzw
      · exact hz.2 w hwS hzw
    · refine ⟨Finset.mem_insert_self _ S, fun w hw hxw => ?_⟩
      rcases Finset.mem_insert.mp hw with rfl | hwS
      · rfl
      · exact hno_ext w hwS hxw

/-- Adding a string whose immediate prefix is maximal leaves the number of maximal nodes unchanged.
-/
lemma maxNodes_insert_of_maximal {S : Finset BitString} {x : BitString}
    (hx_not_mem : x ∉ S)
    (hS_pc : ∀ a b, a <+: b → b ∈ S → a ∈ S)
    (hx_prefixes : ∀ z, z <+: x → z ≠ x → z ∈ S)
    (y : BitString) (hy_imm : y <+: x ∧ y.length + 1 = x.length) (hy_max : y ∈ maxNodes S) :
    (maxNodes (insert x S)).card = (maxNodes S).card := by
  classical
  have hno_ext : ∀ w ∈ S, x <+: w → x = w := by
    intro w hw hxw; by_contra hne
    exact hx_not_mem (hS_pc x w hxw hw)
  have prefix_of_prefix_le {a b : BitString} (ha : a <+: x) (hb : b <+: x)
      (hle : a.length ≤ b.length) : a <+: b := by
    have hax := ha.length_le
    rw [List.prefix_iff_eq_take] at ha hb ⊢
    rw [ha, hb, List.length_take, min_eq_left hax, List.take_take, min_eq_left hle]
  -- y is the unique maximal node of S that is a strict prefix of x
  have hy_unique_max : ∀ z, z ∈ maxNodes S → z <+: x → z ≠ x → z = y := by
    intro z hz hzx hne
    rw [maxNodes, Finset.mem_filter] at hz
    have hy_in_S : y ∈ S := (Finset.mem_filter.mp hy_max).1
    have hzlen : z.length < x.length := by
      rcases lt_or_eq_of_le hzx.length_le with h | h
      · exact h
      · exact absurd (hzx.eq_of_length h) hne
    have hzy : z <+: y := by apply prefix_of_prefix_le hzx hy_imm.1; omega
    exact hz.2 y hy_in_S hzy
  -- maxNodes (insert x S) = (maxNodes S \ {y}) ∪ {x}
  suffices h : maxNodes (insert x S) = (maxNodes S).erase y ∪ {x} by
    rw [h, Finset.card_union_of_disjoint]
    · simp only [Finset.card_erase_of_mem hy_max, Finset.card_singleton]
      exact Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨y, hy_max⟩)
    · apply Finset.disjoint_singleton_right.mpr
      intro hx_in
      exact hx_not_mem ((Finset.mem_filter.mp (Finset.mem_erase.mp hx_in).2).1)
  ext z
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · intro hz
    rw [maxNodes, Finset.mem_filter] at hz
    rcases Finset.mem_insert.mp hz.1 with rfl | hzS
    · right; rfl
    · left
      constructor
      · -- z ≠ y: if z = y then z <+: x (from hy_imm) and x ∈ insert x S,
        -- so z is not maximal in insert x S, contradiction
        intro heq; subst heq
        have := hz.2 x (Finset.mem_insert_self x S) hy_imm.1
        exact hx_not_mem (this ▸ hzS)
      · rw [maxNodes, Finset.mem_filter]
        exact ⟨hzS, fun w hw hzw => hz.2 w (Finset.mem_insert_of_mem hw) hzw⟩
  · intro hz
    rw [maxNodes, Finset.mem_filter]
    rcases hz with ⟨hne, hz⟩ | rfl
    · rw [maxNodes, Finset.mem_filter] at hz
      refine ⟨Finset.mem_insert_of_mem hz.1, fun w hw hzw => ?_⟩
      rcases Finset.mem_insert.mp hw with rfl | hwS
      · -- w = x, z <+: x, z is maximal in S and z ≠ y
        -- by hy_unique_max, z = y, contradiction
        by_contra hne'
        exact hne (hy_unique_max z (Finset.mem_filter.mpr hz) hzw hne')
      · exact hz.2 w hwS hzw
    · refine ⟨Finset.mem_insert_self _ S, fun w hw hxw => ?_⟩
      rcases Finset.mem_insert.mp hw with rfl | hwS
      · rfl
      · exact hno_ext w hwS hxw

/-- Two prefixes of a common string are comparable: the shorter one is a prefix of the
longer one. -/
lemma prefix_of_prefix_of_length_le {a b c : BitString} (ha : a <+: c) (hb : b <+: c)
    (hle : a.length ≤ b.length) : a <+: b := by
  have hax := ha.length_le
  rw [List.prefix_iff_eq_take] at ha hb ⊢
  rw [ha, hb, List.length_take, min_eq_left hax, List.take_take, min_eq_left hle]

/-- The finset of nonempty prefixes of a bitstring. -/
def nonemptyPrefixes (x : BitString) : Finset BitString :=
  (Finset.Icc 1 x.length).image (fun i => x.take i)

/-- The nonempty prefixes of `x` are exactly the prefixes of `x` other than the empty string. -/
lemma mem_nonemptyPrefixes {x z : BitString} :
    z ∈ nonemptyPrefixes x ↔ z <+: x ∧ z ≠ [] := by
  classical
  simp only [nonemptyPrefixes, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    refine ⟨List.take_prefix i x, ?_⟩
    intro h
    have hlen : (x.take i).length = 0 := by rw [h]; rfl
    rw [List.length_take] at hlen
    omega
  · rintro ⟨hz, hne⟩
    refine ⟨z.length, ⟨?_, hz.length_le⟩, (List.prefix_iff_eq_take.mp hz).symm⟩
    cases z with
    | nil => exact absurd rfl hne
    | cons a t => simp

/-- Inserting a string all of whose proper prefixes are already present preserves
prefix-closedness. -/
lemma insert_prefixClosed {S : Finset BitString} {x : BitString}
    (hS : ∀ a b, a <+: b → b ∈ S → a ∈ S)
    (hx_prefixes : ∀ z, z <+: x → z ≠ x → z ∈ S) :
    ∀ a b, a <+: b → b ∈ insert x S → a ∈ insert x S := by
  intro a b hab hb
  rcases Finset.mem_insert.mp hb with hbx | hbS
  · rw [hbx] at hab
    by_cases h : a = x
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hx_prefixes a hab h)
  · exact Finset.mem_insert_of_mem (hS a b hab hbS)


end Kolmogorov
