import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelStage
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.Foundation.UnboundedSearch
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelGreedy.AddressState
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelGreedy.GreedyStages
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelGreedy

/-!
# Covering an a priori sublevel set by a prefix-free address assignment

The combinatorial core behind the description of `{x | KA x ≤ k}` by short addresses. A
`CoverState` is a finite stage of the construction: a prefix-closed set of covered strings
together with an injective assignment of length-`k` addresses that respects the tree order.
`fresh_address_allocation` supplies an unused address while fewer than `2 ^ k` are in use, the
two insertion lemmas (`coverState_insert_freshAddress`, `coverState_insert_reuseAddress`) and
`one_node_insertion` add a single string, and `coverState_extend` / `exists_coverState` iterate
this to any finite prefix-closed subset of `kaSublevel k`. The recursive-enumerability helpers
`isRE_eq` and `stageExistenceIsRE` make the union of the stages enumerable.
-/

noncomputable section

namespace Kolmogorov

/-- A finite stage of the construction covering the `k`-th a priori sublevel: a prefix-closed set of
strings together with an assignment of length-`k` addresses forming a lower graph, one chain per
address, covering every nonempty member and using no more addresses than there are maximal nodes. -/
structure CoverState (k : ℕ) where
  S : Finset BitString
  S_prefixClosed : ∀ x y, x <+: y → y ∈ S → x ∈ S
  R : Finset (BitString × BitString)
  R_domain : ∀ p x, (p, x) ∈ R → p.length = k ∧ x ∈ S ∧ x ≠ []
  R_lowerGraph : ∀ p x z, (p, x) ∈ R → z <+: x → z ≠ [] → (p, z) ∈ R
  R_chain : ∀ p x y, (p, x) ∈ R → (p, y) ∈ R → x <+: y ∨ y <+: x
  R_covers : ∀ x ∈ S, x ≠ [] → ∃ p, (p, x) ∈ R
  R_address_bound : (R.image Prod.fst).card ≤ (maxNodes S).card

/-- The cover state at which nothing has been assigned yet. -/
def emptyCoverState (k : ℕ) : CoverState k where
  S := ∅
  S_prefixClosed := by simp
  R := ∅
  R_domain := by simp
  R_lowerGraph := by simp
  R_chain := by simp
  R_covers := by simp
  R_address_bound := by simp

/-- While fewer than `2 ^ k` addresses are in use, a length-`k` address unused by the current state
is available. -/
lemma fresh_address_allocation {k : ℕ} (state : CoverState k)
    (h_card : (maxNodes state.S).card < 2 ^ k) :
    ∃ p, p.length = k ∧ ∀ x, (p, x) ∉ state.R := by
  have h1 : (state.R.image Prod.fst).card < 2 ^ k := lt_of_le_of_lt state.R_address_bound h_card
  have h2 : (stringsOfLength k).card = 2 ^ k := card_stringsOfLength k
  have h3 : (state.R.image Prod.fst).card < (stringsOfLength k).card := by linarith
  have h4 : ¬ (stringsOfLength k ⊆ state.R.image Prod.fst) :=
    fun h => not_le.mpr h3 (Finset.card_le_card h)
  rw [Finset.subset_iff] at h4
  push Not at h4
  obtain ⟨p, hp_len, hp_not_mem⟩ := h4
  use p
  constructor
  · exact (mem_stringsOfLength k p).mp hp_len
  · intro x h_mem
    apply hp_not_mem
    rw [Finset.mem_image]
    exact ⟨(p, x), h_mem, rfl⟩

/-- Extend a cover state by a new leaf `x`, using a completely fresh address `p` for the
whole nonempty part of the branch leading to `x`. -/
lemma coverState_insert_freshAddress {k : ℕ} (state : CoverState k) (x : BitString)
    (hx_prefixes : ∀ z, z <+: x → z ≠ x → z ∈ state.S)
    (p : BitString) (hp_len : p.length = k) (hp_fresh : ∀ z, (p, z) ∉ state.R)
    (hbound : (state.R.image Prod.fst).card + 1 ≤ (maxNodes (insert x state.S)).card) :
    ∃ state' : CoverState k, state'.S = insert x state.S ∧ state.R ⊆ state'.R := by
  classical
  set T : Finset (BitString × BitString) :=
    state.R ∪ (nonemptyPrefixes x).image (fun z => (p, z)) with hT
  have hmemT : ∀ q z, (q, z) ∈ T ↔ ((q, z) ∈ state.R ∨ (q = p ∧ z <+: x ∧ z ≠ [])) := by
    intro q z
    rw [hT]
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · exact Or.inl h
      · obtain ⟨w, hw, hwq⟩ := Finset.mem_image.mp h
        simp only [Prod.mk.injEq] at hwq
        exact Or.inr ⟨hwq.1.symm, hwq.2 ▸ (mem_nonemptyPrefixes.mp hw)⟩
    · rintro (h | ⟨hq, hz⟩)
      · exact Finset.mem_union_left _ h
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, mem_nonemptyPrefixes.mpr hz, ?_⟩)
        rw [hq]
  refine ⟨⟨insert x state.S, insert_prefixClosed state.S_prefixClosed hx_prefixes, T,
    ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro q z hz
    rcases (hmemT q z).mp hz with h | ⟨hq, hzx, hzne⟩
    · obtain ⟨h1, h2, h3⟩ := state.R_domain q z h
      exact ⟨h1, Finset.mem_insert_of_mem h2, h3⟩
    · refine ⟨by rw [hq]; exact hp_len, ?_, hzne⟩
      by_cases hzx' : z = x
      · rw [hzx']; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hx_prefixes z hzx hzx')
  · intro q a z ha hza hzne
    rcases (hmemT q a).mp ha with h | ⟨hq, hax, -⟩
    · exact (hmemT q z).mpr (Or.inl (state.R_lowerGraph q a z h hza hzne))
    · exact (hmemT q z).mpr (Or.inr ⟨hq, hza.trans hax, hzne⟩)
  · intro q a b ha hb
    rcases (hmemT q a).mp ha with ha' | ⟨hqa, hax, -⟩
    · rcases (hmemT q b).mp hb with hb' | ⟨hqb, -, -⟩
      · exact state.R_chain q a b ha' hb'
      · exfalso; rw [hqb] at ha'; exact hp_fresh a ha'
    · rcases (hmemT q b).mp hb with hb' | ⟨-, hbx, -⟩
      · exfalso; rw [hqa] at hb'; exact hp_fresh b hb'
      · rcases le_total a.length b.length with hle | hle
        · exact Or.inl (prefix_of_prefix_of_length_le hax hbx hle)
        · exact Or.inr (prefix_of_prefix_of_length_le hbx hax hle)
  · intro z hz hzne
    rcases Finset.mem_insert.mp hz with hzx | hzS
    · exact ⟨p, (hmemT p z).mpr (Or.inr ⟨rfl, by simp [hzx], hzne⟩)⟩
    · obtain ⟨q, hq⟩ := state.R_covers z hzS hzne
      exact ⟨q, (hmemT q z).mpr (Or.inl hq)⟩
  · have hsub : T.image Prod.fst ⊆ insert p (state.R.image Prod.fst) := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
      rcases (hmemT w.1 w.2).mp (by simpa using hw) with h | ⟨hq1, -, -⟩
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, h, rfl⟩)
      · rw [hq1]; exact Finset.mem_insert_self _ _
    calc (T.image Prod.fst).card ≤ (insert p (state.R.image Prod.fst)).card :=
          Finset.card_le_card hsub
      _ ≤ (state.R.image Prod.fst).card + 1 := Finset.card_insert_le _ _
      _ ≤ _ := hbound
  · change state.R ⊆ T
    rw [hT]
    exact Finset.subset_union_left

/-- Extend a cover state by a new leaf `x` whose immediate predecessor `y` is a maximal
node: the address of `y` is simply reused for `x`. -/
lemma coverState_insert_reuseAddress {k : ℕ} (state : CoverState k) (x y p : BitString)
    (hx_ne : x ≠ []) (hx_prefixes : ∀ z, z <+: x → z ≠ x → z ∈ state.S)
    (hy_pre : y <+: x) (hy_len : y.length + 1 = x.length)
    (hy_max : y ∈ maxNodes state.S) (hpy : (p, y) ∈ state.R)
    (hcard : (maxNodes (insert x state.S)).card = (maxNodes state.S).card) :
    ∃ state' : CoverState k, state'.S = insert x state.S ∧ state.R ⊆ state'.R := by
  classical
  have hp_len : p.length = k := (state.R_domain p y hpy).1
  have hy_maxS : ∀ w ∈ state.S, y <+: w → y = w := (Finset.mem_filter.mp hy_max).2
  have key : ∀ z, z <+: x → z ≠ [] → z ≠ x → (p, z) ∈ state.R := by
    intro z hzx hzne hznex
    have hzlen : z.length ≤ y.length := by
      have h1 : z.length ≤ x.length := hzx.length_le
      have h2 : z.length ≠ x.length := fun h => hznex (hzx.eq_of_length h)
      omega
    exact state.R_lowerGraph p y z hpy (prefix_of_prefix_of_length_le hzx hy_pre hzlen) hzne
  set T : Finset (BitString × BitString) := insert (p, x) state.R with hT
  have hmemT : ∀ q z, (q, z) ∈ T ↔ ((q = p ∧ z = x) ∨ (q, z) ∈ state.R) := by
    intro q z
    rw [hT, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · simp only [Prod.mk.injEq] at h; exact Or.inl h
      · exact Or.inr h
    · rintro (⟨h1, h2⟩ | h)
      · exact Or.inl (by rw [h1, h2])
      · exact Or.inr h
  refine ⟨⟨insert x state.S, insert_prefixClosed state.S_prefixClosed hx_prefixes, T,
    ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro q z hz
    rcases (hmemT q z).mp hz with ⟨hq, hzx⟩ | h
    · exact ⟨by rw [hq]; exact hp_len, by rw [hzx]; exact Finset.mem_insert_self _ _,
        by rw [hzx]; exact hx_ne⟩
    · obtain ⟨h1, h2, h3⟩ := state.R_domain q z h
      exact ⟨h1, Finset.mem_insert_of_mem h2, h3⟩
  · intro q a z ha hza hzne
    rcases (hmemT q a).mp ha with ⟨hq, hax⟩ | h
    · rw [hax] at hza
      by_cases hzx : z = x
      · exact (hmemT q z).mpr (Or.inl ⟨hq, hzx⟩)
      · refine (hmemT q z).mpr (Or.inr ?_)
        rw [hq]
        exact key z hza hzne hzx
    · exact (hmemT q z).mpr (Or.inr (state.R_lowerGraph q a z h hza hzne))
  · intro q a b ha hb
    rcases (hmemT q a).mp ha with ⟨hqa, hax⟩ | ha'
    · rcases (hmemT q b).mp hb with ⟨-, hbx⟩ | hb'
      · left; rw [hax, hbx]
      · right
        have hbS : b ∈ state.S := (state.R_domain q b hb').2.1
        have hchain := state.R_chain q b y hb' (by rw [hqa]; exact hpy)
        have hby : b <+: y := by
          rcases hchain with h | h
          · exact h
          · have hyb := hy_maxS b hbS h
            rw [hyb]
        rw [hax]
        exact hby.trans hy_pre
    · rcases (hmemT q b).mp hb with ⟨hqb, hbx⟩ | hb'
      · left
        have haS : a ∈ state.S := (state.R_domain q a ha').2.1
        have hchain := state.R_chain q a y ha' (by rw [hqb]; exact hpy)
        have hay : a <+: y := by
          rcases hchain with h | h
          · exact h
          · have hya := hy_maxS a haS h
            rw [hya]
        rw [hbx]
        exact hay.trans hy_pre
      · exact state.R_chain q a b ha' hb'
  · intro z hz hzne
    rcases Finset.mem_insert.mp hz with hzx | hzS
    · exact ⟨p, (hmemT p z).mpr (Or.inl ⟨rfl, hzx⟩)⟩
    · obtain ⟨q, hq⟩ := state.R_covers z hzS hzne
      exact ⟨q, (hmemT q z).mpr (Or.inr hq)⟩
  · have himg : T.image Prod.fst = state.R.image Prod.fst := by
      rw [hT, Finset.image_insert]
      exact Finset.insert_eq_self.mpr (Finset.mem_image.mpr ⟨(p, y), hpy, rfl⟩)
    rw [himg, hcard]
    exact state.R_address_bound
  · change state.R ⊆ T
    rw [hT]
    exact Finset.subset_insert _ _

/-- A new string all of whose proper prefixes are already covered can be added to a cover state
without withdrawing any assignment. -/
lemma one_node_insertion {k : ℕ} (state : CoverState k) (x : BitString)
    (hx_not_mem : x ∉ state.S)
    (hx_prefixes : ∀ z, z <+: x → z ≠ x → z ∈ state.S)
    (hS : ∀ z ∈ insert x state.S, z ∈ kaSublevel k) :
    ∃ state' : CoverState k, state'.S = insert x state.S ∧ state.R ⊆ state'.R := by
  classical
  by_cases hx_ne : x = []
  · -- `x = []` forces `state.S = ∅` (it is prefix-closed and misses `[]`), hence `state.R = ∅`.
    have hS_empty : state.S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      refine hx_not_mem ?_
      rw [hx_ne]
      exact state.S_prefixClosed [] w (List.nil_prefix) hw
    have hR_empty : state.R = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro ⟨q, z⟩ hq
      have h := (state.R_domain q z hq).2.1
      rw [hS_empty] at h
      exact absurd h (Finset.notMem_empty _)
    refine ⟨⟨insert x state.S, insert_prefixClosed state.S_prefixClosed hx_prefixes, ∅,
      ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
    · intro q z hz; exact absurd hz (Finset.notMem_empty _)
    · intro q a z hz; exact absurd hz (Finset.notMem_empty _)
    · intro q a b ha; exact absurd ha (Finset.notMem_empty _)
    · intro z hz hzne
      rcases Finset.mem_insert.mp hz with h | h
      · exact absurd (h.trans hx_ne) hzne
      · rw [hS_empty] at h; exact absurd h (Finset.notMem_empty _)
    · simp
    · simp [hR_empty]
  · obtain ⟨y, hy_pre, hy_len⟩ := exists_immediate_prefix x hx_ne
    have hy_ne_x : y ≠ x := by intro h; rw [h] at hy_len; omega
    have hy_mem : y ∈ state.S := hx_prefixes y hy_pre hy_ne_x
    have hle2k : (maxNodes (insert x state.S)).card ≤ 2 ^ k :=
      maxNodes_card_le_of_subset_kaSublevel hS
    by_cases hymax : y ∈ maxNodes state.S
    · have hcard := maxNodes_insert_of_maximal hx_not_mem state.S_prefixClosed hx_prefixes y
        ⟨hy_pre, hy_len⟩ hymax
      by_cases hy_nil : y = []
      · -- `y = []` is maximal, so `state.S ⊆ {[]}` and `state.R` is empty.
        have hR_empty : ∀ q z, (q, z) ∉ state.R := by
          intro q z hq
          obtain ⟨-, hzS, hzne⟩ := state.R_domain q z hq
          have hz_nil := (Finset.mem_filter.mp hymax).2 z hzS
            (by rw [hy_nil]; exact List.nil_prefix)
          rw [hy_nil] at hz_nil
          exact hzne hz_nil.symm
        refine coverState_insert_freshAddress state x hx_prefixes
          (List.replicate k false) (by simp) (fun z => hR_empty _ z) ?_
        have himg : state.R.image Prod.fst = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro q hq
          obtain ⟨w, hw, -⟩ := Finset.mem_image.mp hq
          exact hR_empty w.1 w.2 (by simpa using hw)
        rw [himg, hcard]
        simp only [Finset.card_empty, zero_add]
        exact Finset.one_le_card.mpr ⟨y, hymax⟩
      · obtain ⟨p, hpy⟩ := state.R_covers y hy_mem hy_nil
        exact coverState_insert_reuseAddress state x y p hx_ne hx_prefixes hy_pre hy_len
          hymax hpy hcard
    · have hcard := maxNodes_insert_of_not_maximal hx_not_mem state.S_prefixClosed hx_prefixes y
        ⟨hy_pre, hy_len⟩ hymax
      have hlt : (maxNodes state.S).card < 2 ^ k := by omega
      obtain ⟨p, hp_len, hp_fresh⟩ := fresh_address_allocation state hlt
      refine coverState_insert_freshAddress state x hx_prefixes p hp_len hp_fresh ?_
      have hb := state.R_address_bound
      omega

/-- Auxiliary form of `coverState_extend`, with the size of the set of nodes still to be
inserted made explicit so that strong induction applies. -/
lemma coverState_extend_aux {k : ℕ} :
    ∀ (n : ℕ) (state : CoverState k) (F : Finset BitString),
      (F \ state.S).card = n →
      (∀ a b, a <+: b → b ∈ F → a ∈ F) →
      (∀ z ∈ F, z ∈ kaSublevel k) →
      state.S ⊆ F →
      ∃ state' : CoverState k, state'.S = F ∧ state.R ⊆ state'.R := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro state F hcard hpc hsub hSF
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · have hempty : F \ state.S = ∅ := Finset.card_eq_zero.mp (by omega)
      have hFS : F ⊆ state.S := Finset.sdiff_eq_empty_iff_subset.mp hempty
      exact ⟨state, Finset.Subset.antisymm hSF hFS, Finset.Subset.refl _⟩
    · have hne : (F \ state.S).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx, hmin⟩ := (F \ state.S).exists_min_image (fun z => z.length) hne
      rw [Finset.mem_sdiff] at hx
      have hx_prefixes : ∀ z, z <+: x → z ≠ x → z ∈ state.S := by
        intro z hzx hzne
        by_contra hz
        have hzF : z ∈ F := hpc z x hzx hx.1
        have hle := hmin z (Finset.mem_sdiff.mpr ⟨hzF, hz⟩)
        have hlt : z.length < x.length :=
          lt_of_le_of_ne hzx.length_le (fun h => hzne (hzx.eq_of_length h))
        omega
      have hins : ∀ z ∈ insert x state.S, z ∈ kaSublevel k := by
        intro z hz
        rcases Finset.mem_insert.mp hz with h | h
        · rw [h]; exact hsub x hx.1
        · exact hsub z (hSF h)
      obtain ⟨st1, hst1S, hst1R⟩ := one_node_insertion state x hx.2 hx_prefixes hins
      have hdiff : F \ st1.S = (F \ state.S).erase x := by
        rw [hst1S]
        ext w
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
        tauto
      have hcard1 : (F \ st1.S).card = n - 1 := by
        rw [hdiff, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hx.1, hx.2⟩), hcard]
      obtain ⟨st2, hst2S, hst2R⟩ := ih (n - 1) (by omega) st1 F hcard1 hpc hsub
        (by rw [hst1S]; exact Finset.insert_subset hx.1 hSF)
      exact ⟨st2, hst2S, hst1R.trans hst2R⟩

/-- A cover state can be extended to any larger finite prefix-closed subset of
`kaSublevel k`, keeping all previously assigned addresses. -/
lemma coverState_extend {k : ℕ} (state : CoverState k) (F : Finset BitString)
    (hpc : ∀ a b, a <+: b → b ∈ F → a ∈ F)
    (hsub : ∀ z ∈ F, z ∈ kaSublevel k)
    (hSF : state.S ⊆ F) :
    ∃ state' : CoverState k, state'.S = F ∧ state.R ⊆ state'.R :=
  coverState_extend_aux (F \ state.S).card state F rfl hpc hsub hSF

/-- Every finite prefix-closed subset of `kaSublevel k` carries a cover state. -/
lemma exists_coverState {k : ℕ} (F : Finset BitString)
    (hpc : ∀ a b, a <+: b → b ∈ F → a ∈ F)
    (hsub : ∀ z ∈ F, z ∈ kaSublevel k) :
    ∃ state : CoverState k, state.S = F := by
  obtain ⟨state, hstate, -⟩ :=
    coverState_extend (emptyCoverState k) F hpc hsub (by simp [emptyCoverState])
  exact ⟨state, hstate⟩

/-- Equality on a primitively codable type is recursively enumerable. -/
lemma isRE_eq {α : Type*} [Primcodable α] : IsRE (fun p : α × α => p.1 = p.2) := by
  have h_pred : PrimrecPred (fun p : α × α => p.1 = p.2) := @Primrec.eq α _
  obtain ⟨dec, h_prim⟩ := h_pred
  have h_comp : Computable (fun p : α × α => @decide (p.1 = p.2) (dec p)) := Primrec.to_comp h_prim
  apply isRE_of_computable_bool _ _ _ h_comp
  intro p
  exact @decide_eq_true_iff _ (dec p)

/-- For a computable family of finite stages, membership in the union of the stages is recursively
enumerable uniformly in the family index. -/
theorem stageExistenceIsRE
    (R_stage : ℕ → ℕ → Finset (BitString × BitString))
    (h_comp : Computable₂ (fun k s => (R_stage k s).toList)) :
    IsRE (fun q : ℕ × (BitString × BitString) =>
      ∃ s, q.2 ∈ R_stage q.1 s) := by
  have h_eq : (fun q : ℕ × (BitString × BitString) => ∃ s, q.2 ∈ R_stage q.1 s) =
              
(fun q : ℕ × (BitString × BitString) => ∃ s, ∃ b ∈ (R_stage q.1 s).toList, b = q.2) := by
    ext q
    simp only [Finset.mem_toList, exists_eq_right]
  rw [h_eq]
  apply IsRE.exists_encodable
  apply IsRE.existsInList
  · have h_snd : Computable
      (fun p : ((ℕ × (BitString × BitString)) × ℕ) × (BitString × BitString) => p.2) :=
        Computable.snd
    have h_fst_fst_snd : Computable
      (fun p : ((ℕ × (BitString × BitString)) × ℕ) × (BitString × BitString) => p.1.1.2) :=
      Computable.snd.comp (Computable.fst.comp Computable.fst)
    exact IsRE.comp_computable isRE_eq (Computable.pair h_snd h_fst_fst_snd)
  · have h_R : Computable
      (fun p : (ℕ × (BitString × BitString)) × ℕ => (R_stage p.1.1 p.2).toList) :=
      h_comp.comp (Computable.fst.comp Computable.fst) Computable.snd
    exact h_R

end Kolmogorov
