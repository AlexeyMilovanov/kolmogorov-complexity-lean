import KolmogorovMathlib.MonotoneComplexity.AntichainSum
import KolmogorovMathlib.Prefix.Basic

/-!
# Raw flows and finite antichain envelopes

The local processes of the selected-bit argument are real-valued tree flows with an arbitrary
root budget: nonnegative functions that are superadditive over the two children at every
extension of a fixed node `u`, with no normalization of the root.  This module proves their
finite antichain bound and introduces the finite antichain envelope.

* `IsRawFlowFrom u a`: `a ≥ 0` and `a (x 0) + a (x 1) ≤ a x` for every extension `x` of `u`.
* `IsRawFlowFrom.sum_antichain_le_of_extends`, `IsRawFlowFrom.sum_antichain_le`: the sum of a
  raw flow over a finite prefix-free set of extensions of `x` is at most `a x`.
* `eq_of_append_singleton_prefix`, `isPrefixFree_union_of_children`: the two children of a word
  have no common extension, so prefix-free sets below them unite into a prefix-free set.
* `finiteEnvelope H d x`: the depth-`d` antichain envelope of `H` at `x`, defined by the
  recursion `max (H x) (envelope at x 0 + envelope at x 1)`.  It dominates `H`
  (`le_finiteEnvelope`), is monotone in `H` (`finiteEnvelope_mono`), bounds every antichain sum
  below `x` within depth `d` (`sum_le_finiteEnvelope`) and is attained by such an antichain
  (`exists_prefixFree_sum_eq_finiteEnvelope`).
* `truncatedEnvelope H v D`: the envelope at `y` with the remaining depth `D - |y|` on the
  extensions `y` of `v` with `|y| ≤ D`, and `0` elsewhere; it is a raw flow from `v`
  (`isRawFlowFrom_truncatedEnvelope`).
-/

namespace Kolmogorov.SelectedBits

/-! ### Raw flows -/

/-- A **raw flow from `u`**: a nonnegative real function on words that is superadditive over the
two children at every extension `x` of `u`.  The root value `a u` is an arbitrary budget. -/
structure IsRawFlowFrom (u : BitString) (a : BitString → ℝ) : Prop where
  /-- A raw flow is nonnegative everywhere. -/
  nonneg : ∀ x, 0 ≤ a x
  /-- The two children of an extension of `u` together carry at most its value. -/
  coherent : ∀ x, u <+: x → a (x ++ [false]) + a (x ++ [true]) ≤ a x

/-- A raw flow from `u` is a raw flow from every extension of `u`. -/
theorem IsRawFlowFrom.of_prefix {u u' : BitString} {a : BitString → ℝ}
    (ha : IsRawFlowFrom u a) (hu : u <+: u') : IsRawFlowFrom u' a :=
  ⟨ha.nonneg, fun x hx => ha.coherent x (hu.trans hx)⟩

/-- **Antichain bound for raw flows.**  The sum of a raw flow from `u` over a finite prefix-free
set of extensions of an extension `x` of `u`, of lengths at most `x.length + d`, is at most
`a x`. -/
theorem IsRawFlowFrom.sum_antichain_le_of_extends {u : BitString} {a : BitString → ℝ}
    (ha : IsRawFlowFrom u a) :
    ∀ (d : ℕ) (x : BitString), u <+: x → ∀ S : Finset BitString,
      (∀ y ∈ S, x <+: y) → (∀ y ∈ S, y.length ≤ x.length + d) →
      IsPrefixFree (S : Set BitString) → ∑ y ∈ S, a y ≤ a x := by
  intro d
  induction d with
  | zero =>
    intro x _ S hpref hlen _
    have hsub : S ⊆ {x} := by
      intro y hy
      have h1 := hpref y hy
      have h2 := hlen y hy
      have : y = x := (h1.eq_of_length (by have := h1.length_le; omega)).symm
      simp [this]
    calc ∑ y ∈ S, a y ≤ ∑ y ∈ ({x} : Finset BitString), a y :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => ha.nonneg y)
      _ = a x := Finset.sum_singleton _ _
  | succ n ih =>
    intro x hux S hpref hlen hanti
    by_cases hxS : x ∈ S
    · have hS : S = {x} := by
        ext y
        simp only [Finset.mem_singleton]
        exact ⟨fun hy => (hanti (Finset.mem_coe.mpr hxS) (Finset.mem_coe.mpr hy)
          (hpref y hy)).symm, fun hy => hy ▸ hxS⟩
      simp [hS]
    · have hchild : ∀ y ∈ S, ∀ b : Bool, ¬ (x ++ [!b]) <+: y → (x ++ [b]) <+: y := by
        intro y hy b hb
        obtain ⟨c, hc⟩ := exists_child_prefix_of_prefix_of_ne (hpref y hy)
          (fun h => hxS (h ▸ hy))
        cases b <;> cases c <;> simp_all
      have hbound : ∀ (b : Bool), ∑ y ∈ S.filter (fun y => (x ++ [b]) <+: y), a y
          ≤ a (x ++ [b]) := by
        intro b
        refine ih (x ++ [b]) (hux.trans (List.prefix_append x [b])) _ ?_ ?_ ?_
        · intro y hy
          exact (Finset.mem_filter.mp hy).2
        · intro y hy
          have := hlen y (Finset.mem_filter.mp hy).1
          simp only [List.length_append, List.length_singleton]
          omega
        · intro y hy z hz hyz
          exact hanti (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1)
            (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).1) hyz
      have hsplit : ∑ y ∈ S, a y
          = ∑ y ∈ S.filter (fun y => (x ++ [false]) <+: y), a y
            + ∑ y ∈ S.filter (fun y => ¬ (x ++ [false]) <+: y), a y :=
        (Finset.sum_filter_add_sum_filter_not S _ a).symm
      have hnot : S.filter (fun y => ¬ (x ++ [false]) <+: y)
          ⊆ S.filter (fun y => (x ++ [true]) <+: y) := by
        intro y hy
        obtain ⟨hyS, hy'⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨hyS, hchild y hyS true (by simpa using hy')⟩
      calc ∑ y ∈ S, a y
          = ∑ y ∈ S.filter (fun y => (x ++ [false]) <+: y), a y
            + ∑ y ∈ S.filter (fun y => ¬ (x ++ [false]) <+: y), a y := hsplit
        _ ≤ ∑ y ∈ S.filter (fun y => (x ++ [false]) <+: y), a y
            + ∑ y ∈ S.filter (fun y => (x ++ [true]) <+: y), a y :=
              add_le_add le_rfl
                (Finset.sum_le_sum_of_subset_of_nonneg hnot (fun y _ _ => ha.nonneg y))
        _ ≤ a (x ++ [false]) + a (x ++ [true]) := add_le_add (hbound false) (hbound true)
        _ ≤ a x := ha.coherent x hux

/-- **Antichain bound for raw flows**, without a depth bound: the sum of a raw flow from `u`
over a finite prefix-free set of extensions of `u` is at most the root budget `a u`. -/
theorem IsRawFlowFrom.sum_antichain_le {u : BitString} {a : BitString → ℝ}
    (ha : IsRawFlowFrom u a) (S : Finset BitString) (hext : ∀ y ∈ S, u <+: y)
    (hS : IsPrefixFree (S : Set BitString)) : ∑ y ∈ S, a y ≤ a u :=
  ha.sum_antichain_le_of_extends (S.sup List.length) u List.prefix_rfl S hext
    (fun y hy => by have := Finset.le_sup (f := List.length) hy; omega) hS

/-! ### The finite antichain envelope -/

/-- The **depth-`d` antichain envelope** of `H` at `x`: `H x` at depth `0`, and at depth
`d + 1` the larger of `H x` and the sum of the depth-`d` envelopes at the two children.  For
nonnegative `H` it is the largest sum of `H` over a prefix-free set of extensions of `x` of
length at most `x.length + d`. -/
noncomputable def finiteEnvelope (H : BitString → ℝ) : ℕ → BitString → ℝ
  | 0, x => H x
  | d + 1, x => max (H x) (finiteEnvelope H d (x ++ [false]) + finiteEnvelope H d (x ++ [true]))

/-- The envelope of depth `0` is the function itself. -/
@[simp] theorem finiteEnvelope_zero (H : BitString → ℝ) (x : BitString) :
    finiteEnvelope H 0 x = H x := rfl

/-- One step of the envelope recursion. -/
theorem finiteEnvelope_succ (H : BitString → ℝ) (d : ℕ) (x : BitString) :
    finiteEnvelope H (d + 1) x =
      max (H x) (finiteEnvelope H d (x ++ [false]) + finiteEnvelope H d (x ++ [true])) := rfl

/-- The envelope dominates the function. -/
theorem le_finiteEnvelope (H : BitString → ℝ) (d : ℕ) (x : BitString) :
    H x ≤ finiteEnvelope H d x := by
  cases d with
  | zero => exact le_rfl
  | succ d => exact le_max_left _ _

/-- The envelope of a nonnegative function is nonnegative. -/
theorem finiteEnvelope_nonneg {H : BitString → ℝ} (hH : ∀ x, 0 ≤ H x) (d : ℕ)
    (x : BitString) : 0 ≤ finiteEnvelope H d x :=
  (hH x).trans (le_finiteEnvelope H d x)

/-- The envelope is monotone in the function. -/
theorem finiteEnvelope_mono {H H' : BitString → ℝ} (h : ∀ x, H x ≤ H' x) (d : ℕ)
    (x : BitString) : finiteEnvelope H d x ≤ finiteEnvelope H' d x := by
  induction d generalizing x with
  | zero => exact h x
  | succ d ih => exact max_le_max (h x) (add_le_add (ih _) (ih _))

/-- Two children of the same word that are both prefixes of one word coincide. -/
theorem eq_of_append_singleton_prefix {x y : BitString} {b c : Bool} (hb : x ++ [b] <+: y)
    (hc : x ++ [c] <+: y) : b = c := by
  simpa using List.prefix_of_prefix_length_le hb hc (by simp)

/-- The union of a prefix-free set of extensions of `x ++ [false]` and a prefix-free set of
extensions of `x ++ [true]` is a prefix-free set of extensions of `x`, and the two parts are
disjoint. -/
theorem isPrefixFree_union_of_children {x : BitString} {S₀ S₁ : Finset BitString}
    (hfree₀ : IsPrefixFree (S₀ : Set BitString)) (hfree₁ : IsPrefixFree (S₁ : Set BitString))
    (hext₀ : ∀ y ∈ S₀, x ++ [false] <+: y) (hext₁ : ∀ y ∈ S₁, x ++ [true] <+: y) :
    IsPrefixFree ((S₀ ∪ S₁ : Finset BitString) : Set BitString) ∧ Disjoint S₀ S₁ ∧
      ∀ y ∈ S₀ ∪ S₁, x <+: y := by
  refine ⟨?_, Finset.disjoint_left.mpr fun y hy₀ hy₁ =>
    Bool.false_ne_true (eq_of_append_singleton_prefix (hext₀ y hy₀) (hext₁ y hy₁)), ?_⟩
  · rw [Finset.coe_union]
    intro y hy z hz hyz
    rcases hy with hy₀ | hy₁ <;> rcases hz with hz₀ | hz₁
    · exact hfree₀ hy₀ hz₀ hyz
    · exact absurd (eq_of_append_singleton_prefix ((hext₀ y hy₀).trans hyz) (hext₁ z hz₁))
        Bool.false_ne_true
    · exact absurd (eq_of_append_singleton_prefix (hext₀ z hz₀) ((hext₁ y hy₁).trans hyz))
        Bool.false_ne_true
    · exact hfree₁ hy₁ hz₁ hyz
  · intro y hy
    rcases Finset.mem_union.mp hy with hy₀ | hy₁
    · exact (List.prefix_append x [false]).trans (hext₀ y hy₀)
    · exact (List.prefix_append x [true]).trans (hext₁ y hy₁)

/-- The singleton `{x}` is a prefix-free set of extensions of `x` of lengths at most
`x.length + d`, with `H`-sum `H x`. -/
theorem singleton_isPrefixFree_extends (H : BitString → ℝ) (d : ℕ) (x : BitString) :
    IsPrefixFree (({x} : Finset BitString) : Set BitString) ∧
      (∀ y ∈ ({x} : Finset BitString), x <+: y) ∧
      (∀ y ∈ ({x} : Finset BitString), y.length ≤ x.length + d) ∧
      ∑ y ∈ ({x} : Finset BitString), H y = H x :=
  ⟨by simpa only [Finset.coe_singleton] using isPrefixFree_singleton x, by simp, by simp,
    Finset.sum_singleton _ _⟩

/-- The envelope is attained: some prefix-free set of extensions of `x`, of lengths at most
`x.length + d`, has `H`-sum equal to `finiteEnvelope H d x`.  At depth `d + 1` it is `{x}` when
`H x` is the larger term, and otherwise the union of the two sets of the children, which is
disjoint and prefix-free because its parts lie below different children
(`isPrefixFree_union_of_children`). -/
theorem exists_prefixFree_sum_eq_finiteEnvelope (H : BitString → ℝ) (d : ℕ) (x : BitString) :
    ∃ S : Finset BitString, IsPrefixFree (S : Set BitString) ∧ (∀ y ∈ S, x <+: y) ∧
      (∀ y ∈ S, y.length ≤ x.length + d) ∧ ∑ y ∈ S, H y = finiteEnvelope H d x := by
  induction d generalizing x with
  | zero => exact ⟨{x}, singleton_isPrefixFree_extends H 0 x⟩
  | succ d ih =>
    by_cases hle : H x ≤ finiteEnvelope H d (x ++ [false]) + finiteEnvelope H d (x ++ [true])
    · obtain ⟨S₀, hfree₀, hext₀, hlen₀, hsum₀⟩ := ih (x ++ [false])
      obtain ⟨S₁, hfree₁, hext₁, hlen₁, hsum₁⟩ := ih (x ++ [true])
      obtain ⟨hfree, hdisj, hext⟩ := isPrefixFree_union_of_children hfree₀ hfree₁ hext₀ hext₁
      refine ⟨S₀ ∪ S₁, hfree, hext, fun y hy => ?_, ?_⟩
      · rcases Finset.mem_union.mp hy with hy | hy
        · have h := hlen₀ y hy
          simp only [List.length_append, List.length_singleton] at h
          omega
        · have h := hlen₁ y hy
          simp only [List.length_append, List.length_singleton] at h
          omega
      · rw [Finset.sum_union hdisj, hsum₀, hsum₁, finiteEnvelope_succ, max_eq_right hle]
    · obtain ⟨hfree, hext, hlen, hsum⟩ := singleton_isPrefixFree_extends H (d + 1) x
      refine ⟨{x}, hfree, hext, hlen, ?_⟩
      rw [hsum, finiteEnvelope_succ, max_eq_left (not_le.mp hle).le]

/-! ### The truncated envelope as a raw flow -/

/-- The envelope below `v` truncated at the absolute length `D`: at an extension `y` of `v` with
`|y| ≤ D` it is the envelope of the remaining depth `D - |y|`, and it vanishes elsewhere. -/
noncomputable def truncatedEnvelope (H : BitString → ℝ) (v : BitString) (D : ℕ)
    (y : BitString) : ℝ :=
  if v <+: y ∧ y.length ≤ D then finiteEnvelope H (D - y.length) y else 0

/-- Inside its domain the truncated envelope is the envelope of the remaining depth. -/
theorem truncatedEnvelope_of_prefix {H : BitString → ℝ} {v y : BitString} {D : ℕ}
    (hvy : v <+: y) (hyD : y.length ≤ D) :
    truncatedEnvelope H v D y = finiteEnvelope H (D - y.length) y := by
  rw [truncatedEnvelope, ite_eq_left ⟨hvy, hyD⟩]

/-- Outside its domain the truncated envelope vanishes. -/
theorem truncatedEnvelope_of_not {H : BitString → ℝ} {v y : BitString} {D : ℕ}
    (h : ¬ (v <+: y ∧ y.length ≤ D)) : truncatedEnvelope H v D y = 0 := by
  rw [truncatedEnvelope, ite_eq_right h]

/-- The truncated envelope dominates the function inside its domain. -/
theorem le_truncatedEnvelope (H : BitString → ℝ) {v y : BitString} {D : ℕ} (hvy : v <+: y)
    (hyD : y.length ≤ D) : H y ≤ truncatedEnvelope H v D y := by
  rw [truncatedEnvelope_of_prefix hvy hyD]
  exact le_finiteEnvelope H _ y

/-- The truncated envelope of a nonnegative function is nonnegative. -/
theorem truncatedEnvelope_nonneg {H : BitString → ℝ} (hH : ∀ x, 0 ≤ H x) (v : BitString)
    (D : ℕ) (y : BitString) : 0 ≤ truncatedEnvelope H v D y := by
  unfold truncatedEnvelope
  split_ifs
  · exact finiteEnvelope_nonneg hH _ _
  · exact le_rfl

/-- The truncated envelope is monotone in the function. -/
theorem truncatedEnvelope_mono {H H' : BitString → ℝ} (h : ∀ x, H x ≤ H' x) (v : BitString)
    (D : ℕ) (y : BitString) : truncatedEnvelope H v D y ≤ truncatedEnvelope H' v D y := by
  unfold truncatedEnvelope
  split_ifs
  · exact finiteEnvelope_mono h _ _
  · exact le_rfl

/-- The truncated envelope of a nonnegative function is a raw flow from `v`. -/
theorem isRawFlowFrom_truncatedEnvelope {H : BitString → ℝ} (hH : ∀ x, 0 ≤ H x)
    (v : BitString) (D : ℕ) : IsRawFlowFrom v (truncatedEnvelope H v D) := by
  refine ⟨truncatedEnvelope_nonneg hH v D, fun x hvx => ?_⟩
  by_cases hlen : x.length + 1 ≤ D
  · have hb : ∀ b : Bool, v <+: x ++ [b] ∧ (x ++ [b]).length ≤ D := by
      intro b
      refine ⟨hvx.trans (List.prefix_append _ _), ?_⟩
      simp only [List.length_append, List.length_singleton]
      omega
    rw [truncatedEnvelope_of_prefix (hb false).1 (hb false).2,
      truncatedEnvelope_of_prefix (hb true).1 (hb true).2,
      truncatedEnvelope_of_prefix hvx (by omega)]
    have hD : D - x.length = (D - (x.length + 1)) + 1 := by omega
    simp only [List.length_append, List.length_singleton]
    rw [hD, finiteEnvelope_succ]
    exact le_max_right _ _
  · have hb : ∀ b : Bool, ¬ (v <+: x ++ [b] ∧ (x ++ [b]).length ≤ D) := fun b h =>
      hlen (by simpa using h.2)
    rw [truncatedEnvelope_of_not (hb false), truncatedEnvelope_of_not (hb true), add_zero]
    exact truncatedEnvelope_nonneg hH v D x

/-- **The envelope bounds antichain sums.**  For nonnegative `H`, the `H`-sum over a finite
prefix-free set of extensions of `x` of lengths at most `x.length + d` is at most
`finiteEnvelope H d x`. -/
theorem sum_le_finiteEnvelope {H : BitString → ℝ} (hH : ∀ x, 0 ≤ H x) (d : ℕ) (x : BitString)
    (S : Finset BitString) (hext : ∀ y ∈ S, x <+: y) (hlen : ∀ y ∈ S, y.length ≤ x.length + d)
    (hS : IsPrefixFree (S : Set BitString)) : ∑ y ∈ S, H y ≤ finiteEnvelope H d x := by
  have hflow := isRawFlowFrom_truncatedEnvelope hH x (x.length + d)
  calc ∑ y ∈ S, H y ≤ ∑ y ∈ S, truncatedEnvelope H x (x.length + d) y :=
        Finset.sum_le_sum fun y hy => le_truncatedEnvelope H (hext y hy) (hlen y hy)
    _ ≤ truncatedEnvelope H x (x.length + d) x :=
        hflow.sum_antichain_le_of_extends d x List.prefix_rfl S hext hlen hS
    _ = finiteEnvelope H d x := by
        rw [truncatedEnvelope_of_prefix List.prefix_rfl (by omega)]
        congr 1
        omega

end Kolmogorov.SelectedBits
