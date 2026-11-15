import KolmogorovMathlib.InformationLogic.IntuitionisticBounds
import KolmogorovMathlib.InformationLogic.DiagonalLowerBounds
import KolmogorovMathlib.InformationLogic.Kripke

/-!
# Medvedev's reduction to critical implications and the main theorem (SUV §13.4)

Theorem 245 (Medvedev; quoted without proof by the book) reduces every unprovable formula to a
critical implication; with Theorem 244 it gives the main result of the chapter, Theorem 238:
an unprovable negation-free formula has linear complexity on suitable finite sets.
-/

namespace Kolmogorov
namespace InformationLogic

open ProblemCalculus PFormula

/-- Worlds of the unravelled model: finite chains of the original model containing the root. -/
private def exists_subst_provable_imp_criticalData_tree_Ch {W0 : Type} [PartialOrder W0]
    (r0 : W0) (c : Finset W0) : Prop :=
  r0 ∈ c ∧ ∀ x ∈ c, ∀ y ∈ c, x ≤ y ∨ y ≤ x

/-- The type of worlds (a non-reducible wrapper, to avoid the order of the subtype). -/
private def exists_subst_provable_imp_criticalData_tree_World {W0 : Type} [PartialOrder W0]
    (r0 : W0) : Type :=
  {c : Finset W0 // exists_subst_provable_imp_criticalData_tree_Ch r0 c}

/-- End-extension order on finite sets. -/
private def exists_subst_provable_imp_criticalData_tree_Le {W0 : Type} [PartialOrder W0]
    (c c' : Finset W0) : Prop :=
  c ⊆ c' ∧ ∀ x ∈ c', x ∉ c → ∀ y ∈ c, y ≤ x

private lemma exists_subst_provable_imp_criticalData_tree_exists_last {W0 : Type}
    [PartialOrder W0] {r0 : W0} {c : Finset W0}
    (h : exists_subst_provable_imp_criticalData_tree_Ch r0 c) :
    ∃ m ∈ c, ∀ y ∈ c, y ≤ m := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal (s := c) ⟨r0, h.1⟩
  refine ⟨m, hm, fun y hy => ?_⟩
  rcases h.2 y hy m hm with h1 | h1
  · exact h1
  · exact hmax hy h1

/-- Step 1 of the proof of `exists_subst_provable_imp_criticalData`: unravelling.  An
unprovable formula is refuted at the root of a finite Kripke model whose order is a *tree*
(every set `{a | a ≤ w}` is a chain).  Proof: take the finite countermodel of
`exists_finite_kripke_countermodel`, and replace its worlds by the strictly increasing chains
`r = w₀ < w₁ < … < wₙ` of worlds (ordered by being a prefix, valuation of the last world); the
map "last world" is a p-morphism, so it preserves forcing; there are finitely many chains because
the original model is finite. -/
private theorem exists_subst_provable_imp_criticalData_tree {m : ℕ} (Φ : PFormula (Fin m))
    (hΦ : ¬ Φ.Provable) :
    ∃ (W : Type) (_ : Finite W) (_ : PartialOrder W) (r : W) (V : W → Fin m → Prop),
      (∀ w, r ≤ w) ∧ IsMonotoneValuation V ∧
      (∀ a b w : W, a ≤ w → b ≤ w → a ≤ b ∨ b ≤ a) ∧ ¬ Forces V r Φ := by
  classical
  obtain ⟨W0, hF0, hP0, r0, V0, hr0, hV0, hf0⟩ := exists_finite_kripke_countermodel Φ hΦ
  have := hF0
  let W : Type := exists_subst_provable_imp_criticalData_tree_World r0
  have hWfin : Finite W :=
    Finite.of_injective (fun c : W => (c : {c : Finset W0 //
      exists_subst_provable_imp_criticalData_tree_Ch r0 c}).1)
      (fun a b h => Subtype.ext h)
  have hLe_refl : ∀ c : Finset W0,
      exists_subst_provable_imp_criticalData_tree_Le c c := fun c =>
    ⟨subset_rfl, fun x hx hxn => absurd hx hxn⟩
  have hLe_trans : ∀ a b c : Finset W0,
      exists_subst_provable_imp_criticalData_tree_Le a b →
      exists_subst_provable_imp_criticalData_tree_Le b c →
      exists_subst_provable_imp_criticalData_tree_Le a c := by
    intro a b c ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨h1.trans h3, fun x hx hxa y hy => ?_⟩
    by_cases hxb : x ∈ b
    · exact h2 x hxb hxa y hy
    · exact h4 x hx hxb y (h1 hy)
  have hLe_antisymm : ∀ a b : Finset W0,
      exists_subst_provable_imp_criticalData_tree_Le a b →
      exists_subst_provable_imp_criticalData_tree_Le b a → a = b :=
    fun a b h1 h2 => Finset.Subset.antisymm h1.1 h2.1
  let : PartialOrder W :=
    { le := fun a b => exists_subst_provable_imp_criticalData_tree_Le a.1 b.1
      le_refl := fun a => hLe_refl a.1
      le_trans := fun a b c h1 h2 => hLe_trans _ _ _ h1 h2
      le_antisymm := fun a b h1 h2 => Subtype.ext (hLe_antisymm _ _ h1 h2) }
  let last : W → W0 := fun c =>
    Classical.choose (exists_subst_provable_imp_criticalData_tree_exists_last c.2)
  have hlast_mem : ∀ c : W, last c ∈ c.1 := fun c =>
    (Classical.choose_spec (exists_subst_provable_imp_criticalData_tree_exists_last c.2)).1
  have hlast_max : ∀ c : W, ∀ y ∈ c.1, y ≤ last c := fun c =>
    (Classical.choose_spec (exists_subst_provable_imp_criticalData_tree_exists_last c.2)).2
  have hlast_unique : ∀ (c : W) (m : W0), m ∈ c.1 → (∀ y ∈ c.1, y ≤ m) → m = last c :=
    fun c m hm hmax => le_antisymm (hlast_max c m hm) (hmax _ (hlast_mem c))
  have hlast_mono : ∀ a b : W, a ≤ b → last a ≤ last b :=
    fun a b h => hlast_max b _ (h.1 (hlast_mem a))
  let V : W → Fin m → Prop := fun c i => V0 (last c) i
  have hVm : IsMonotoneValuation V := fun a b h i hi => hV0 (hlast_mono a b h) i hi
  have hroot : exists_subst_provable_imp_criticalData_tree_Ch r0 {r0} :=
    ⟨Finset.mem_singleton_self r0, fun x hx y hy => by
      rw [Finset.mem_singleton] at hx hy; subst hx; subst hy; exact Or.inl le_rfl⟩
  have htruth : ∀ (Ψ : PFormula (Fin m)) (c : W), Forces V c Ψ ↔ Forces V0 (last c) Ψ := by
    intro Ψ
    induction Ψ with
    | var i => intro c; rfl
    | conj A B ihA ihB => intro c; simp only [Forces, ihA, ihB]
    | disj A B ihA ihB => intro c; simp only [Forces, ihA, ihB]
    | imp A B ihA ihB =>
      intro c
      simp only [Forces]
      constructor
      · intro h w' hw' hA
        by_cases heq : w' = last c
        · subst heq
          exact (ihB c).1 (h c le_rfl ((ihA c).2 hA))
        · have hlt : last c < w' := lt_of_le_of_ne hw' (Ne.symm heq)
          have hch : exists_subst_provable_imp_criticalData_tree_Ch r0 (insert w' c.1) := by
            refine ⟨Finset.mem_insert_of_mem c.2.1, fun x hx y hy => ?_⟩
            rw [Finset.mem_insert] at hx hy
            rcases hx with rfl | hx <;> rcases hy with rfl | hy
            · exact Or.inl le_rfl
            · exact Or.inr ((hlast_max c y hy).trans hw')
            · exact Or.inl ((hlast_max c x hx).trans hw')
            · exact c.2.2 x hx y hy
          let c' : W := ⟨insert w' c.1, hch⟩
          have hcc' : c ≤ c' := by
            refine ⟨Finset.subset_insert _ _, fun x hx hxn y hy => ?_⟩
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · exact (hlast_max c y hy).trans hw'
            · exact absurd hx hxn
          have hl : last c' = w' :=
            (hlast_unique c' w' (Finset.mem_insert_self _ _) (fun y hy => by
              rw [Finset.mem_insert] at hy
              rcases hy with rfl | hy
              · exact le_rfl
              · exact (hlast_max c y hy).trans hw')).symm
          have := (ihB c').1 (h c' hcc' ((ihA c').2 (hl ▸ hA)))
          rwa [hl] at this
      · intro h c' hc' hA
        exact (ihB c').2 (h _ (hlast_mono c c' hc') ((ihA c').1 hA))
  refine ⟨W, hWfin, inferInstance, ⟨{r0}, hroot⟩, V, ?_, hVm, ?_, ?_⟩
  · intro w
    refine ⟨fun x hx => ?_, fun x hx hxn y hy => ?_⟩
    · rw [Finset.mem_singleton] at hx; subst hx; exact w.2.1
    · rw [Finset.mem_singleton] at hy; subst hy; exact hr0 x
  · intro a b w ha hb
    by_cases hab : a.1 ⊆ b.1
    · left
      refine ⟨hab, fun x hx hxn y hy => ?_⟩
      exact ha.2 x (hb.1 hx) hxn y hy
    · right
      obtain ⟨x, hxa, hxb⟩ := Finset.not_subset.1 hab
      have hba : b.1 ⊆ a.1 := by
        intro z hz
        by_contra hza
        have h1 := ha.2 z (hb.1 hz) hza x hxa
        have h2 := hb.2 x (ha.1 hxa) hxb z hz
        exact hza (le_antisymm h2 h1 ▸ hxa)
      refine ⟨hba, fun x hx hxn y hy => ?_⟩
      exact hb.2 x (ha.1 hx) hxn y hy
  · intro hf
    have hl : r0 = last ⟨{r0}, hroot⟩ :=
      hlast_unique ⟨{r0}, hroot⟩ r0 (Finset.mem_singleton_self r0) (fun y hy => by
        rw [Finset.mem_singleton] at hy; subst hy; exact le_rfl)
    rw [hl] at hf0
    exact hf0 ((htruth Φ _).1 hf)

section Step2Semantic

/-- `y` is collapsed: `s_⊤` holds, or two incomparable `s_u`, `s_v` hold. -/
private def exists_subst_provable_imp_criticalData_semantic_coll {ι W N : Type} [LE W]
    (V' : N → ι → Prop) (sv : Option W → ι) (y : N) : Prop :=
  V' y (sv none) ∨ ∃ u v : W, V' y (sv (some u)) ∧ V' y (sv (some v)) ∧ ¬ u ≤ v ∧ ¬ v ≤ u

/-- The formula `Q_w`: `s_⊤` or some `s_u` with `¬ u ≤ w` holds. -/
private def exists_subst_provable_imp_criticalData_semantic_Q {ι W N : Type} [LE W]
    (V' : N → ι → Prop) (sv : Option W → ι) (w : W) (y : N) : Prop :=
  V' y (sv none) ∨ ∃ u : W, ¬ u ≤ w ∧ V' y (sv (some u))

private theorem exists_subst_provable_imp_criticalData_semantic_coll_mono
    {ι W N : Type} [LE W] [Preorder N] {V' : N → ι → Prop} (hV' : IsMonotoneValuation V')
    (sv : Option W → ι) {y y' : N} (hy : y ≤ y')
    (h : exists_subst_provable_imp_criticalData_semantic_coll V' sv y) :
    exists_subst_provable_imp_criticalData_semantic_coll V' sv y' := by
  rcases h with h | ⟨u, v, hu, hv, h1, h2⟩
  · exact Or.inl (hV' hy _ h)
  · exact Or.inr ⟨u, v, hV' hy _ hu, hV' hy _ hv, h1, h2⟩

private theorem exists_subst_provable_imp_criticalData_semantic_Q_notcoll
    {ι W N : Type} [PartialOrder W] {V' : N → ι → Prop} (sv : Option W → ι)
    (htree : ∀ a b w : W, a ≤ w → b ≤ w → a ≤ b ∨ b ≤ a) {w : W} {z : N}
    (hQ : ¬ exists_subst_provable_imp_criticalData_semantic_Q V' sv w z) :
    ¬ exists_subst_provable_imp_criticalData_semantic_coll V' sv z := by
  rintro (h | ⟨u, v, hu, hv, h1, h2⟩)
  · exact hQ (Or.inl h)
  · have hu' : u ≤ w := by_contra fun hn => hQ (Or.inr ⟨u, hn, hu⟩)
    have hv' : v ≤ w := by_contra fun hn => hQ (Or.inr ⟨v, hn, hv⟩)
    rcases htree u v w hu' hv' with h | h
    · exact h1 h
    · exact h2 h

private theorem exists_subst_provable_imp_criticalData_semantic_greatest
    {ι W N : Type} [PartialOrder W] [Finite W] {V' : N → ι → Prop} (sv : Option W → ι) {y : N}
    (hc : ¬ exists_subst_provable_imp_criticalData_semantic_coll V' sv y) {w : W}
    (hw : V' y (sv (some w))) :
    ∃ w', V' y (sv (some w')) ∧ ∀ u, V' y (sv (some u)) → u ≤ w' := by
  obtain ⟨m, hm⟩ := (Set.toFinite {u : W | V' y (sv (some u))}).exists_maximal ⟨w, hw⟩
  refine ⟨m, hm.1, fun u hu => ?_⟩
  by_contra hn
  by_cases h2 : m ≤ u
  · exact hn (hm.2 hu h2)
  · exact hc (Or.inr ⟨u, m, hu, hm.1, hn, h2⟩)

/-- The truth lemma of Medvedev's construction, over an abstract assignment `sv` of variables. -/
private theorem exists_subst_provable_imp_criticalData_semantic_truth
    {ι W N : Type} [PartialOrder W] [Finite W] [PartialOrder N] {m : ℕ}
    (htree : ∀ a b w : W, a ≤ w → b ≤ w → a ≤ b ∨ b ≤ a)
    (V : W → Fin m → Prop) (hV : IsMonotoneValuation V)
    (V' : N → ι → Prop) (hV' : IsMonotoneValuation V') (sv : Option W → ι)
    (T : Fin m → PFormula ι)
    (hT : ∀ y i, Forces V' y (T i) ↔
      exists_subst_provable_imp_criticalData_semantic_coll V' sv y ∨
        ∃ u, V u i ∧ V' y (sv (some u)))
    (y₀ : N)
    (hH : ∀ (w : W) (y' : N), y₀ ≤ y' →
      ((∀ y'', y' ≤ y'' → V' y'' (sv (some w)) →
        exists_subst_provable_imp_criticalData_semantic_Q V' sv w y'') →
        exists_subst_provable_imp_criticalData_semantic_Q V' sv w y')) :
    ∀ Ψ : PFormula (Fin m),
      (∀ y, exists_subst_provable_imp_criticalData_semantic_coll V' sv y →
        Forces V' y (Ψ.subst T)) ∧
      (∀ y, y₀ ≤ y →
        ¬ exists_subst_provable_imp_criticalData_semantic_coll V' sv y →
        ∀ w, V' y (sv (some w)) → (∀ u, V' y (sv (some u)) → u ≤ w) →
        (Forces V' y (Ψ.subst T) ↔ Forces V w Ψ)) := by
  intro Ψ
  induction Ψ with
  | var i =>
    refine ⟨fun y hc => (hT y i).2 (Or.inl hc), ?_⟩
    intro y hy hnc w hw hmax
    change Forces V' y (T i) ↔ V w i
    rw [hT]
    constructor
    · rintro (hc | ⟨u, hu, hs⟩)
      · exact absurd hc hnc
      · exact hV (hmax u hs) i hu
    · intro h
      exact Or.inr ⟨w, h, hw⟩
  | conj A B ihA ihB =>
    refine ⟨fun y hc => ⟨ihA.1 y hc, ihB.1 y hc⟩, ?_⟩
    intro y hy hnc w hw hmax
    change Forces V' y (A.subst T) ∧ Forces V' y (B.subst T) ↔ Forces V w A ∧ Forces V w B
    rw [ihA.2 y hy hnc w hw hmax, ihB.2 y hy hnc w hw hmax]
  | disj A B ihA ihB =>
    refine ⟨fun y hc => Or.inl (ihA.1 y hc), ?_⟩
    intro y hy hnc w hw hmax
    change Forces V' y (A.subst T) ∨ Forces V' y (B.subst T) ↔ Forces V w A ∨ Forces V w B
    rw [ihA.2 y hy hnc w hw hmax, ihB.2 y hy hnc w hw hmax]
  | imp A B ihA ihB =>
    refine ⟨fun y hc y' hy' _ => ihB.1 y'
      (exists_subst_provable_imp_criticalData_semantic_coll_mono hV' sv hy' hc), ?_⟩
    intro y hy hnc w hw hmax
    change (∀ y', y ≤ y' → Forces V' y' (A.subst T) → Forces V' y' (B.subst T)) ↔
      ∀ w', w ≤ w' → Forces V w' A → Forces V w' B
    constructor
    · intro h w' hw' hA
      have hQ : ¬ exists_subst_provable_imp_criticalData_semantic_Q V' sv w' y := by
        rintro (h1 | ⟨u, hu, h2⟩)
        · exact hnc (Or.inl h1)
        · exact hu ((hmax u h2).trans hw')
      obtain ⟨y', hy', hP, hQ'⟩ : ∃ y', y ≤ y' ∧ V' y' (sv (some w')) ∧
          ¬ exists_subst_provable_imp_criticalData_semantic_Q V' sv w' y' := by
        by_contra hno
        exact hQ (hH w' y hy fun y'' h1 h2 => by_contra fun hq => hno ⟨y'', h1, h2, hq⟩)
      have hnc' := exists_subst_provable_imp_criticalData_semantic_Q_notcoll sv htree hQ'
      have hmax' : ∀ u, V' y' (sv (some u)) → u ≤ w' := fun u hu =>
        by_contra fun hn => hQ' (Or.inr ⟨u, hn, hu⟩)
      have hy0' : y₀ ≤ y' := hy.trans hy'
      have hAy' := (ihA.2 y' hy0' hnc' w' hP hmax').2 hA
      exact (ihB.2 y' hy0' hnc' w' hP hmax').1 (h y' hy' hAy')
    · intro h y' hy' hA
      by_cases hc : exists_subst_provable_imp_criticalData_semantic_coll V' sv y'
      · exact ihB.1 y' hc
      · have hwy' : V' y' (sv (some w)) := hV' hy' _ hw
        obtain ⟨w', hw', hmax'⟩ :=
          exists_subst_provable_imp_criticalData_semantic_greatest sv hc hwy'
        have hy0' : y₀ ≤ y' := hy.trans hy'
        have hww' : w ≤ w' := hmax' w hwy'
        exact (ihB.2 y' hy0' hc w' hw' hmax').2
          (h w' hww' ((ihA.2 y' hy0' hc w' hw' hmax').1 hA))

private theorem exists_subst_provable_imp_criticalData_semantic_forces_conjList
    {ι W : Type} [Preorder W] {V : W → ι → Prop} (w : W) (d : PFormula ι) :
    ∀ l : List (PFormula ι), l ≠ [] → (Forces V w (conjList d l) ↔ ∀ A ∈ l, Forces V w A)
  | [], h => absurd rfl h
  | [A], _ => by simp [conjList]
  | A :: B :: l, _ => by
      rw [conjList, Forces,
        exists_subst_provable_imp_criticalData_semantic_forces_conjList w d (B :: l)
          (by simp)]
      simp

private theorem exists_subst_provable_imp_criticalData_semantic_forces_disjList
    {ι W : Type} [Preorder W] {V : W → ι → Prop} (w : W) (d : PFormula ι) :
    ∀ l : List (PFormula ι), l ≠ [] → (Forces V w (disjList d l) ↔ ∃ A ∈ l, Forces V w A)
  | [], h => absurd rfl h
  | [A], _ => by simp [disjList]
  | A :: B :: l, _ => by
      rw [disjList, Forces,
        exists_subst_provable_imp_criticalData_semantic_forces_disjList w d (B :: l)
          (by simp)]
      simp

private theorem exists_subst_provable_imp_criticalData_semantic_impFree_disjList
    {ι : Type} {d : PFormula ι} (hd : d.ImpFree) :
    ∀ l : List (PFormula ι), (∀ B ∈ l, B.ImpFree) → (disjList d l).ImpFree
  | [], _ => hd
  | [A], h => h A (by simp)
  | A :: B :: l, h =>
      ⟨h A (by simp),
        exists_subst_provable_imp_criticalData_semantic_impFree_disjList hd (B :: l)
          (fun C hC => h C (List.mem_cons_of_mem _ hC))⟩

private theorem exists_subst_provable_imp_criticalData_semantic_finsetVars_ne {k : ℕ}
    {I : Finset (Fin k)} (hI : I.Nonempty) : finsetVars I ≠ [] := by
  obtain ⟨i, hi⟩ := hI
  intro h
  have : var i ∈ finsetVars I := by
    simp only [finsetVars, List.mem_map, List.mem_filter, List.mem_finRange, decide_eq_true_eq,
      true_and]
    exact ⟨i, hi, rfl⟩
  rw [h] at this
  simp at this

private theorem exists_subst_provable_imp_criticalData_semantic_forces_premise {k : ℕ}
    {N : Type} [Preorder N] {V : N → Fin k → Prop} (w : N) (C : CriticalData k)
    {I : Finset (Fin k)} (hI : I.Nonempty) :
    Forces V w (C.premise I) ↔ ∀ i ∈ I, V w i := by
  unfold CriticalData.premise
  rw [exists_subst_provable_imp_criticalData_semantic_forces_conjList _ _ _
    (exists_subst_provable_imp_criticalData_semantic_finsetVars_ne hI)]
  simp [finsetVars, Forces]

private theorem exists_subst_provable_imp_criticalData_semantic_forces_target {k : ℕ}
    {N : Type} [Preorder N] {V : N → Fin k → Prop} (w : N) (C : CriticalData k)
    {J : Finset (Fin k)} (hJ : J.Nonempty) :
    Forces V w (C.target J) ↔ ∃ i ∈ J, V w i := by
  unfold CriticalData.target
  rw [exists_subst_provable_imp_criticalData_semantic_forces_disjList _ _ _
    (exists_subst_provable_imp_criticalData_semantic_finsetVars_ne hJ)]
  simp [finsetVars, Forces]

end Step2Semantic

/-- Step 2 of the proof of `exists_subst_provable_imp_criticalData`: the semantic core
(Medvedev's construction).  Let `(W, ≤, r, V)` be a finite tree model refuting `Φ` at the root.
Put `k = |W| + 1` with variables `s_u` (`u ∈ W`) and an extra `s_⊤`.  Let
`T_i = (⋁_{u ⊩ t_i} s_u) ∨ s_⊤ ∨ ⋁_{u, v incomparable} (s_u ∧ s_v)` (implication-free) and let
the critical data have, for each `w ∈ W`, the pair `I_w = {s_w}`,
`J_w = {s_⊤} ∪ {s_u | ¬ u ≤ w}`.  For a world `y` of an arbitrary Kripke model let
`S(y) = {u | s_u true at y}`; call `y` *collapsed* if `s_⊤ ∈ S(y)` or `S(y)` contains two
incomparable worlds.  Truth lemma (induction on `Ψ`): a collapsed `y` forces `Ψ(T)` (all the
atoms are true in its whole upper cone); a non-collapsed `y` with `S(y) ≠ ∅` (then `S(y)` is a
chain, with greatest element `w`) forces `Ψ(T)` iff `w` forces `Ψ`; the implication case `⇒` uses
the conjunct `((P_{w'} → Q_{w'}) → Q_{w'})` for `w' ≥ w`.  Then a world `x` forcing `Φ(T)` and
all the conjuncts but not `R` has `S(x) = ∅`, the conjunct of the root gives `z ≥ x` with
`S(z) = {r}`, and `r` forces `Φ` — a contradiction. -/
private theorem exists_subst_provable_imp_criticalData_semantic {m : ℕ}
    (Φ : PFormula (Fin m)) (W : Type) [Finite W] [PartialOrder W] (r : W)
    (V : W → Fin m → Prop) (hV : IsMonotoneValuation V)
    (htree : ∀ a b w : W, a ≤ w → b ≤ w → a ≤ b ∨ b ≤ a) (hΦ : ¬ Forces V r Φ) :
    ∃ (k : ℕ) (T : Fin m → PFormula (Fin k)) (C : CriticalData k),
      (∀ i, (T i).ImpFree) ∧
      ∀ (N : Type) (_ : PartialOrder N) (V' : N → Fin k → Prop), IsMonotoneValuation V' →
        ∀ x : N, Forces V' x (Φ.subst T) → Forces V' x C.formula := by
  classical
  have : Fintype W := Fintype.ofFinite W
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin (Option W)
  let ul : List W := (Finset.univ : Finset W).toList
  have hul : ∀ u, u ∈ ul := fun u => by simp [ul]
  let top : PFormula (Fin k) := PFormula.var (e none)
  let atom : W → PFormula (Fin k) := fun u => PFormula.var (e (some u))
  let L : Fin m → List (PFormula (Fin k)) := fun i =>
    top :: ((ul.filter (fun u => decide (V u i))).map atom ++
      ul.flatMap (fun u => (ul.filter (fun v => decide (¬ u ≤ v ∧ ¬ v ≤ u))).map
        (fun v => PFormula.conj (atom u) (atom v))))
  let T : Fin m → PFormula (Fin k) := fun i => disjList top (L i)
  let J : W → Finset (Fin k) := fun w => insert (e none)
    ((Finset.univ.filter (fun u : W => ¬ u ≤ w)).image (fun u => e (some u)))
  let C : CriticalData k :=
    { pairs := ul.map (fun w => ({e (some w)}, J w))
      pairs_ne_nil := List.ne_nil_of_mem (List.mem_map.2 ⟨r, hul r, rfl⟩)
      left_nonempty := fun p hp => by
        obtain ⟨w, _, rfl⟩ := List.mem_map.1 hp
        exact Finset.singleton_nonempty _
      right_nonempty := fun p hp => by
        obtain ⟨w, _, rfl⟩ := List.mem_map.1 hp
        exact ⟨e none, Finset.mem_insert_self _ _⟩
      disjoint := fun p hp => by
        obtain ⟨w, _, rfl⟩ := List.mem_map.1 hp
        refine Finset.disjoint_singleton_left.2 ?_
        intro h
        simp only [J, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and] at h
        rcases h with h | ⟨u, hu, hu'⟩
        · exact Option.some_ne_none _ (e.injective h)
        · exact hu (Option.some.inj (e.injective hu')).le
      pos := Fin.pos (e none) }
  have hTfree : ∀ i, (T i).ImpFree := by
    intro i
    refine exists_subst_provable_imp_criticalData_semantic_impFree_disjList
      (by trivial) _ ?_
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · trivial
    · rcases List.mem_append.1 hB with hB | hB
      · obtain ⟨u, _, rfl⟩ := List.mem_map.1 hB
        trivial
      · obtain ⟨u, -, hB⟩ := List.mem_flatMap.1 hB
        obtain ⟨v, _, rfl⟩ := List.mem_map.1 hB
        exact ⟨trivial, trivial⟩
  refine ⟨k, T, C, hTfree, ?_⟩
  intro N hN V' hV' x hx
  have hT : ∀ y i, Forces V' y (T i) ↔
      exists_subst_provable_imp_criticalData_semantic_coll V' e y ∨
        ∃ u, V u i ∧ V' y (e (some u)) := by
    intro y i
    simp only [T]
    rw [exists_subst_provable_imp_criticalData_semantic_forces_disjList _ _ _
      (List.cons_ne_nil _ _)]
    constructor
    · rintro ⟨B, hB, hF⟩
      rcases List.mem_cons.1 hB with rfl | hB
      · exact Or.inl (Or.inl hF)
      · rcases List.mem_append.1 hB with hB | hB
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hB
          have := (List.mem_filter.1 hu).2
          simp only [decide_eq_true_eq] at this
          exact Or.inr ⟨u, this, hF⟩
        · obtain ⟨u, -, hB⟩ := List.mem_flatMap.1 hB
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hB
          have := (List.mem_filter.1 hv).2
          simp only [decide_eq_true_eq] at this
          exact Or.inl (Or.inr ⟨u, v, hF.1, hF.2, this.1, this.2⟩)
    · rintro ((h | ⟨u, v, hu, hv, h1, h2⟩) | ⟨u, hu, hs⟩)
      · exact ⟨top, List.mem_cons_self .., h⟩
      · refine ⟨PFormula.conj (atom u) (atom v), List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_flatMap.2 ⟨u, hul u, List.mem_map.2 ⟨v, List.mem_filter.2 ⟨hul v, ?_⟩, rfl⟩⟩)),
          hu, hv⟩
        simpa using ⟨h1, h2⟩
      · refine ⟨atom u, List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_map.2 ⟨u, List.mem_filter.2 ⟨hul u, ?_⟩, rfl⟩)), hs⟩
        simpa using hu
  intro x' hxx' hconj
  have hΦx' := forces_mono hV' (Φ.subst T) hxx' hx
  have hne : (C.pairs.map fun p =>
      PFormula.imp (PFormula.imp (C.premise p.1) (C.target p.2)) (C.target p.2)) ≠ [] :=
    fun h => C.pairs_ne_nil (List.map_eq_nil_iff.1 h)
  have hmem : ∀ w, Forces V' x' (PFormula.imp
      (PFormula.imp (C.premise {e (some w)}) (C.target (J w))) (C.target (J w))) := fun w =>
    (exists_subst_provable_imp_criticalData_semantic_forces_conjList x' C.dflt _ hne).1
      hconj _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨w, hul w, rfl⟩, rfl⟩)
  have hH : ∀ (w : W) (y' : N), x' ≤ y' →
      ((∀ y'', y' ≤ y'' → V' y'' (e (some w)) →
        exists_subst_provable_imp_criticalData_semantic_Q V' e w y'') →
        exists_subst_provable_imp_criticalData_semantic_Q V' e w y') := by
    intro w y' hy' hall
    have hJne : (J w).Nonempty := ⟨e none, Finset.mem_insert_self _ _⟩
    have hQiff : ∀ y, Forces V' y (C.target (J w)) ↔
        exists_subst_provable_imp_criticalData_semantic_Q V' e w y := by
      intro y
      rw [exists_subst_provable_imp_criticalData_semantic_forces_target y C hJne]
      simp only [J, exists_subst_provable_imp_criticalData_semantic_Q, Finset.mem_insert,
        Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi | ⟨u, hu, rfl⟩, hv⟩
        · subst hi; exact Or.inl hv
        · exact Or.inr ⟨u, hu, hv⟩
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨_, Or.inl rfl, h⟩
        · exact ⟨_, Or.inr ⟨u, hu, rfl⟩, h⟩
    have hPiff : ∀ y, Forces V' y (C.premise {e (some w)}) ↔ V' y (e (some w)) := by
      intro y
      rw [exists_subst_provable_imp_criticalData_semantic_forces_premise y C
        (Finset.singleton_nonempty _)]
      simp
    rw [← hQiff]
    refine hmem w y' hy' ?_
    intro y'' hy'' hP
    rw [hQiff]
    exact hall y'' hy'' ((hPiff y'').1 hP)
  by_cases hQ : exists_subst_provable_imp_criticalData_semantic_Q V' e r x'
  · have hall : (Finset.univ : Finset (Fin k)).Nonempty := ⟨e none, Finset.mem_univ _⟩
    change Forces V' x' (C.target Finset.univ)
    rw [exists_subst_provable_imp_criticalData_semantic_forces_target x' C hall]
    rcases hQ with h | ⟨u, _, h⟩
    · exact ⟨_, Finset.mem_univ _, h⟩
    · exact ⟨_, Finset.mem_univ _, h⟩
  · exfalso
    obtain ⟨z, hz, hPz, hQz⟩ : ∃ z, x' ≤ z ∧ V' z (e (some r)) ∧
        ¬ exists_subst_provable_imp_criticalData_semantic_Q V' e r z := by
      by_contra hno
      exact hQ (hH r x' le_rfl fun y'' h1 h2 => by_contra fun hq => hno ⟨y'', h1, h2, hq⟩)
    have hnc := exists_subst_provable_imp_criticalData_semantic_Q_notcoll e htree hQz
    have hmax : ∀ u, V' z (e (some u)) → u ≤ r := fun u hu =>
      by_contra fun hn => hQz (Or.inr ⟨u, hn, hu⟩)
    exact hΦ (((exists_subst_provable_imp_criticalData_semantic_truth htree V hV V' hV' e
      T hT x' hH Φ).2 z hz hnc r hPz hmax).1 (forces_mono hV' (Φ.subst T) hz hΦx'))

/-- Step 3 of the proof of `exists_subst_provable_imp_criticalData`: completeness glue.
If `A → B` is forced at every world of every finite Kripke model with a monotone valuation, it is
provable.  Proof: otherwise `exists_finite_kripke_countermodel` gives a finite model refuting it
at the root `r`, so some `x ≥ r` forces `A` and not `B`. -/
private theorem exists_subst_provable_imp_criticalData_complete {k : ℕ}
    (A B : PFormula (Fin k))
    (h : ∀ (N : Type) (_ : Finite N) (_ : PartialOrder N) (V' : N → Fin k → Prop),
      IsMonotoneValuation V' → ∀ x : N, Forces V' x A → Forces V' x B) :
    (PFormula.imp A B).Provable := by
  by_contra hn
  obtain ⟨N, hN, hP, r, V', -, hV', hf⟩ := exists_finite_kripke_countermodel _ hn
  apply hf
  intro x _ hA
  exact h N hN hP V' hV' x hA

/-- SUV Theorem 245 (Section 13.4, printed p. 413), Yu. T. Medvedev: if a formula
`Φ(t₁, …, t_m)` with `∧`, `∨`, `→` is not provable in IPC, then there are `k`, formulas
`T₁, …, T_m` in new variables `s₁, …, s_k` built with `∧` and `∨` only, and a critical
implication `J(s₁, …, s_k)` such that `Φ(T₁, …, T_m) → J` is provable in IPC.
The book does not prove it ("belongs to logic and proof theory"); it refers to the paper [42]
of its bibliography, where the proof is given. -/
theorem exists_subst_provable_imp_criticalData {m : ℕ} (Φ : PFormula (Fin m))
    (hΦ : ¬ Φ.Provable) :
    ∃ (k : ℕ) (T : Fin m → PFormula (Fin k)) (C : CriticalData k),
      (∀ i, (T i).ImpFree) ∧ (PFormula.imp (Φ.subst T) C.formula).Provable := by
  obtain ⟨W, hW, hP, r, V, _, hV, htree, hf⟩ :=
    exists_subst_provable_imp_criticalData_tree Φ hΦ
  obtain ⟨k, T, C, hT, hsem⟩ :=
    exists_subst_provable_imp_criticalData_semantic Φ W r V hV htree hf
  exact ⟨k, T, C, hT, exists_subst_provable_imp_criticalData_complete _ _
    fun N _ hP' V' hV' x hx => hsem N hP' V' hV' x hx⟩

/-- Implication-free formulas evaluated at nonempty problems of strings of length at most `ℓ`
in the standard calculus are nonempty problems of strings of length `O(ℓ + 1)`. -/
private lemma exists_finite_sets_le_mul_problemK_eval_aux_eval (L : Map) {ι : Type}
    (F : PFormula ι) (hF : F.ImpFree) :
    ∃ A : ℕ, ∀ (ℓ : ℕ) (v : ι → Set BitString), (∀ i, (v i).Nonempty) →
      (∀ i, ∀ x ∈ v i, x.length ≤ ℓ) →
      (F.eval (std L) v).Nonempty ∧ ∀ x ∈ F.eval (std L) v, x.length ≤ A * (ℓ + 1) := by
  induction F with
  | var i =>
    refine ⟨1, fun ℓ v hne hlen => ⟨hne i, fun x hx => ?_⟩⟩
    have := hlen i x hx
    simp only [PFormula.eval] at hx ⊢
    omega
  | conj F G ihF ihG =>
    obtain ⟨A, hA⟩ := ihF hF.1
    obtain ⟨B, hB⟩ := ihG hF.2
    refine ⟨2 * A + B + 1, fun ℓ v hne hlen => ?_⟩
    obtain ⟨n1, l1⟩ := hA ℓ v hne hlen
    obtain ⟨n2, l2⟩ := hB ℓ v hne hlen
    refine ⟨n1.image2 n2, ?_⟩
    rintro z ⟨a, ha, b, hb, rfl⟩
    have h1 := l1 a ha
    have h2 := l2 b hb
    change (pairCode a b).length ≤ _
    rw [length_pairCode]
    nlinarith
  | disj F G ihF ihG =>
    obtain ⟨A, hA⟩ := ihF hF.1
    obtain ⟨B, hB⟩ := ihG hF.2
    refine ⟨A + B + 3, fun ℓ v hne hlen => ?_⟩
    obtain ⟨n1, l1⟩ := hA ℓ v hne hlen
    obtain ⟨n2, l2⟩ := hB ℓ v hne hlen
    obtain ⟨a, ha⟩ := n1
    refine ⟨⟨_, Or.inl ⟨a, ha, rfl⟩⟩, ?_⟩
    rintro z (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · have h1 := l1 a ha
      change (pairCode [false] a).length ≤ _
      rw [length_pairCode]
      simp only [List.length_cons, List.length_nil]
      nlinarith
    · have h2 := l2 b hb
      change (pairCode [true] b).length ≤ _
      rw [length_pairCode]
      simp only [List.length_cons, List.length_nil]
      nlinarith
  | imp F G _ _ => exact hF.elim

/-- Counting: for every `ℓ` there is a tuple of strings of length `ℓ`, each incompressible up
to the additive constant `k` given all the others. -/
private lemma exists_finite_sets_le_mul_problemK_eval_aux_tuple (D : Map) (k ℓ : ℕ) :
    ∃ u : Fin k → BitString, (∀ i, (u i).length = ℓ) ∧
      ∀ m, (ℓ : ℕ∞) ≤ condK D (u m) (othersCode u m) + (k : ℕ∞) := by
  classical
  by_cases hℓ : ℓ ≤ k
  · refine ⟨fun _ => List.replicate ℓ false, fun _ => by simp, fun m => ?_⟩
    calc (ℓ : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hℓ
      _ ≤ _ := le_add_self
  push Not at hℓ
  by_cases hk : k = 0
  · subst hk
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun m => m.elim0⟩
  -- the bound `b + 1 = ℓ - k`
  obtain ⟨b, hb⟩ : ∃ b, b + 1 = ℓ - k := ⟨ℓ - k - 1, by omega⟩
  let S : Finset (Fin k → BitString) :=
    Fintype.piFinset (fun _ => stringsOfLength ℓ)
  let Bad : Fin k → Finset (Fin k → BitString) := fun m =>
    S.filter (fun u => condK D (u m) (othersCode u m) ≤ (b : ℕ∞))
  have hS : S.card = (2 ^ ℓ) ^ k := by
    simp [S, Fintype.card_piFinset, card_stringsOfLength]
  have hBad : ∀ m, (Bad m).card ≤ 2 ^ (b + 1) * (2 ^ ℓ) ^ (k - 1) := by
    intro m
    let T : Finset (Fin k → BitString) :=
      Fintype.piFinset (fun i => if i = m then {[]} else stringsOfLength ℓ)
    have hT : T.card = (2 ^ ℓ) ^ (k - 1) := by
      rw [Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m)]
      have : ∀ i ∈ Finset.univ.erase m,
          (if i = m then ({[]} : Finset BitString) else stringsOfLength ℓ).card = 2 ^ ℓ := by
        intro i hi
        rw [ite_eq_right (Finset.ne_of_mem_erase hi), card_stringsOfLength]
      rw [Finset.prod_congr rfl this]
      simp
    let g : (Fin k → BitString) → (Fin k → BitString) := fun u => Function.update u m []
    have hmaps : ∀ u ∈ Bad m, g u ∈ T := by
      intro u hu
      have hu' := (Finset.mem_filter.1 hu).1
      simp only [S, Fintype.mem_piFinset] at hu'
      simp only [T, g, Fintype.mem_piFinset]
      intro i
      by_cases him : i = m
      · subst him; simp
      · simp [him, hu' i]
    have hfib : ∀ a ∈ (Bad m).image g, ((Bad m).filter (fun u => g u = a)).card ≤ 2 ^ (b + 1) := by
      intro a _
      refine le_trans ?_ (card_compressibleWordsLt D (othersCode a m) b).le
      refine Finset.card_le_card_of_injOn (fun u => u m) ?_ ?_
      · intro u hu
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hu
        obtain ⟨hu1, hu2⟩ := hu
        have hoth : othersCode u m = othersCode a m := by
          rw [← hu2]
          simp only [othersCode, g]
          congr 1
          apply List.map_congr_left
          intro t ht
          have : t ≠ m := by simpa using (List.mem_filter.1 ht).2
          simp [Function.update_of_ne this]
        have := (Finset.mem_filter.1 hu1).2
        exact (mem_compressibleWords_iff D _ _ _).2 (hoth ▸ this)
      · intro u hu v hv huv
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hu hv
        funext i
        by_cases him : i = m
        · subst him; exact huv
        · have h1 := congrFun hu.2 i
          have h2 := congrFun hv.2 i
          simp only [g, Function.update_of_ne him] at h1 h2
          rw [h1, h2]
    calc (Bad m).card ≤ 2 ^ (b + 1) * ((Bad m).image g).card :=
          Finset.card_le_mul_card_image _ _ hfib
      _ ≤ 2 ^ (b + 1) * T.card := by
          gcongr
          intro a ha
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
          exact hmaps u hu
      _ = _ := by rw [hT]
  have hlt : (Finset.univ.biUnion Bad).card < S.card := by
    calc (Finset.univ.biUnion Bad).card ≤ ∑ m, (Bad m).card := Finset.card_biUnion_le
      _ ≤ ∑ _m : Fin k, 2 ^ (b + 1) * (2 ^ ℓ) ^ (k - 1) := Finset.sum_le_sum (fun m _ => hBad m)
      _ = k * (2 ^ (b + 1) * (2 ^ ℓ) ^ (k - 1)) := by simp
      _ < S.card := by
          rw [hS]
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have h2 : 2 ^ ℓ = 2 ^ (b + 1) * 2 ^ (k' + 1) := by
            rw [← pow_add]; congr 1; omega
          have hk2 : k' + 1 < 2 ^ (k' + 1) := Nat.lt_two_pow_self
          simp only [Nat.add_sub_cancel]
          rw [pow_succ (2 ^ ℓ) k']
          have hpos : 0 < (2 ^ ℓ) ^ k' := by positivity
          have hp2 : 0 < 2 ^ (b + 1) := by positivity
          calc (k' + 1) * (2 ^ (b + 1) * (2 ^ ℓ) ^ k')
              = ((k' + 1) * 2 ^ (b + 1)) * (2 ^ ℓ) ^ k' := by ring
            _ < (2 ^ ℓ) * (2 ^ ℓ) ^ k' := by
                apply Nat.mul_lt_mul_of_pos_right _ hpos
                rw [h2, mul_comm (2 ^ (b + 1))]
                exact Nat.mul_lt_mul_of_pos_right hk2 hp2
            _ = _ := by ring
  obtain ⟨u, huS, hu⟩ : ∃ u ∈ S, u ∉ Finset.univ.biUnion Bad := by
    by_contra h
    push Not at h
    exact absurd (Finset.card_le_card (fun u hu => h u hu)) (not_le.2 hlt)
  refine ⟨u, fun i => ?_, fun m => ?_⟩
  · simp only [S, Fintype.mem_piFinset, mem_stringsOfLength] at huS
    exact huS i
  · have hm : u ∉ Bad m := fun h => hu (Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, h⟩)
    have : ¬ condK D (u m) (othersCode u m) ≤ (b : ℕ∞) := fun h =>
      hm (Finset.mem_filter.2 ⟨huS, h⟩)
    push Not at this
    have h1 : ((b + 1 : ℕ) : ℕ∞) ≤ condK D (u m) (othersCode u m) := by
      exact_mod_cast Order.add_one_le_of_lt this
    calc (ℓ : ℕ∞) = ((b + 1 : ℕ) : ℕ∞) + (k : ℕ∞) := by
          rw [← Nat.cast_add]; congr 1; omega
      _ ≤ _ := by gcongr

/-- SUV Theorem 238 (Section 13.2, printed p. 405; proof in §13.4, printed p. 413), the main
result of the chapter (A. Chernov): if a formula `Φ(t₁, …, t_k)` with `∧`, `∨`, `→` (no `⊥`) is
not provable in IPC, then there are `ε > 0` and finite nonempty sets `X₁ⁿ, …, X_kⁿ` of strings of
length at most `n` such that `C(Φ(X₁ⁿ, …, X_kⁿ)) ≥ εn` for all sufficiently large `n`.
We write `ε = 1/d` with a natural `d > 0`, so the bound reads `n ≤ d · C(Φ(Xⁿ))` in `ℕ∞`
(equivalent to the real formulation).
Book's proof: Theorem 245 gives `T₁, …, T_m` and a critical implication `J`; substitute into
the `T_i` (via `std`, with the linear pair code `pairCode`) singletons of `k` strings of length
`n / c` each incompressible given the others, getting finite nonempty sets
(`eval_finite_of_impFree`, `eval_subst`) of strings of length at most `n`; then
`C(J(u)) ≥ n/c − O(1)` (Theorem 244, `condK_others_le_problemK_criticalData`) and
`C(J(u)) ≤ C(Φ(X)) + O(1)` (`problemK_eval_le_of_provable_imp`); transfer from `std` to `P` by
Problem 339 (`problemK_eval_calculus_le`). -/
theorem exists_finite_sets_le_mul_problemK_eval (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (Φ : PFormula (Fin k))
    (hΦ : ¬ Φ.Provable) :
    ∃ d : ℕ, 0 < d ∧ ∃ X : ℕ → Fin k → Set BitString,
      (∀ n i, (X n i).Finite ∧ (X n i).Nonempty ∧ ∀ x ∈ X n i, x.length ≤ n) ∧
      ∃ N : ℕ, ∀ n ≥ N, (n : ℕ∞) ≤ (d : ℕ∞) * problemK D (Φ.eval P (X n)) := by
  obtain ⟨k', T, C, hT, hprov⟩ := exists_subst_provable_imp_criticalData Φ hΦ
  obtain ⟨L, hL⟩ : ∃ L, IsGodelLang L := ⟨_, isGodelLang_universalDecompressor⟩
  have hQ := std_admissible hL
  obtain ⟨c1, hc1⟩ := problemK_eval_calculus_le D hD P (std L) hP hQ Φ
  obtain ⟨c2, hc2⟩ := problemK_eval_le_of_provable_imp D hD (std L) hQ hprov
  obtain ⟨c3, hc3⟩ := condK_others_le_problemK_criticalData D hD (std L) hQ C
  choose A hA using fun i =>
    exists_finite_sets_le_mul_problemK_eval_aux_eval L (T i) (hT i)
  obtain ⟨a, haA⟩ : ∃ a : ℕ, ∀ i, A i ≤ a :=
    ⟨∑ i, A i, fun i => Finset.single_le_sum (f := A) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)⟩
  choose u hulen hu using fun ℓ => exists_finite_sets_le_mul_problemK_eval_aux_tuple D k' ℓ
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = c1 + c2 + c3 + k' := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (a + 1) * (2 * K + 3) := ⟨_, rfl⟩
  let ℓf : ℕ → ℕ := fun n => n / (a + 1) - 1
  let X : ℕ → Fin k → Set BitString := fun n i =>
    if N ≤ n then (T i).eval (std L) (fun j => {u (ℓf n) j}) else {[]}
  have hdiv : ∀ n, N ≤ n → 2 * K + 3 ≤ n / (a + 1) := by
    intro n hn
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos a)]
    rw [hN] at hn
    linarith
  have hX : ∀ n i, (X n i).Finite ∧ (X n i).Nonempty ∧ ∀ x ∈ X n i, x.length ≤ n := by
    intro n i
    by_cases hn : N ≤ n
    · simp only [X, ite_eq_left hn]
      have hne : ∀ j, ({u (ℓf n) j} : Set BitString).Nonempty := fun j => Set.singleton_nonempty _
      have hlen : ∀ j, ∀ x ∈ ({u (ℓf n) j} : Set BitString), x.length ≤ ℓf n := by
        intro j x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact (hulen _ j).le
      obtain ⟨hn1, hn2⟩ := hA i (ℓf n) _ hne hlen
      refine ⟨PFormula.eval_finite_of_impFree _ (fun j => Set.finite_singleton _) (hT i), hn1,
        fun x hx => ?_⟩
      refine (hn2 x hx).trans ?_
      have h3 := hdiv n hn
      have h4 : ℓf n + 1 = n / (a + 1) := by simp only [ℓf]; omega
      calc A i * (ℓf n + 1) ≤ a * (n / (a + 1)) := by
            rw [h4]; exact Nat.mul_le_mul_right _ (haA i)
        _ ≤ (a + 1) * (n / (a + 1)) := Nat.mul_le_mul_right _ (Nat.le_succ _)
        _ ≤ n := Nat.mul_div_le n (a + 1)
    · simp only [X, ite_eq_right hn]
      exact ⟨Set.finite_singleton _, Set.singleton_nonempty _, fun x hx => by
        rw [Set.mem_singleton_iff] at hx; subst hx; simp⟩
  refine ⟨2 * (a + 1), by omega, X, hX, N, fun n hn => ?_⟩
  have hXn : X n = fun i => (T i).eval (std L) (fun j => {u (ℓf n) j}) := by
    funext i; simp only [X, ite_eq_left hn]
  obtain ⟨m, hm⟩ := hc3 (u (ℓf n))
  have key : (ℓf n : ℕ∞) ≤ problemK D (Φ.eval P (X n)) + (K : ℕ∞) := by
    calc (ℓf n : ℕ∞) ≤ condK D (u (ℓf n) m) (othersCode (u (ℓf n)) m) + (k' : ℕ∞) := hu _ m
      _ ≤ (problemK D (C.formula.eval (std L) (fun i => {u (ℓf n) i})) + (c3 : ℕ∞)) + k' := by
          gcongr
      _ ≤ ((problemK D ((Φ.subst T).eval (std L) (fun i => {u (ℓf n) i})) + (c2 : ℕ∞))
            + c3) + k' := by
          gcongr
          exact hc2 _
      _ = ((problemK D (Φ.eval (std L) (X n)) + (c2 : ℕ∞)) + c3) + k' := by
          rw [PFormula.eval_subst, hXn]
      _ ≤ (((problemK D (Φ.eval P (X n)) + (c1 : ℕ∞)) + c2) + c3) + k' := by
          gcongr
          exact hc1 _
      _ = problemK D (Φ.eval P (X n)) + (K : ℕ∞) := by
          rw [hK]; push_cast; ring
  generalize problemK D (Φ.eval P (X n)) = q at key ⊢
  induction q using ENat.recTopCoe with
  | top => simp
  | coe q =>
    have key' : ℓf n ≤ q + K := by exact_mod_cast key
    have h3 := hdiv n hn
    have h5 := Nat.div_add_mod n (a + 1)
    have h6 := Nat.mod_lt n (Nat.succ_pos a)
    have h7 : ℓf n + 1 = n / (a + 1) := by simp only [ℓf]; omega
    have : n ≤ 2 * (a + 1) * q := by
      generalize n / (a + 1) = t at *
      generalize n % (a + 1) = r at *
      nlinarith
    exact_mod_cast this

end InformationLogic
end Kolmogorov
