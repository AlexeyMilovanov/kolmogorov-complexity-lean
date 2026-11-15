import KolmogorovMathlib.InformationLogic.Formulas

/-!
# Kripke semantics of positive intuitionistic logic (SUV §§13.4, 13.5)

Two standard facts of logic that SUV Chapter 13 uses without proof: soundness of IPC for
Kripke models and the completeness theorem for *finite* Kripke models (SUV §13.5, printed
p. 413: "using only the completeness theorem for Kripke models and IPC").  The book's remark that
critical implications are not provable in IPC ("this can be easily shown using Kripke models",
printed p. 412) is the third statement.
-/

namespace Kolmogorov
namespace InformationLogic

open PFormula

/-- SUV Section 13.5, fact used without proof (printed p. 415, "due to monotonicity"):
persistence — forcing is monotone along the order of worlds, for a monotone valuation.
Proof: induction on the formula; the implication case is transitivity of the order. -/
theorem forces_mono {ι W : Type*} [Preorder W] {V : W → ι → Prop}
    (hV : IsMonotoneValuation V) (A : PFormula ι) {w w' : W} (hw : w ≤ w')
    (h : Forces V w A) : Forces V w' A := by
  induction A generalizing w w' with
  | var i => exact hV hw i h
  | conj A B ihA ihB => exact ⟨ihA hw h.1, ihB hw h.2⟩
  | disj A B ihA ihB => exact h.elim (fun h => Or.inl (ihA hw h)) (fun h => Or.inr (ihB hw h))
  | imp A B _ _ => exact fun w'' hw'' hA => h w'' (hw.trans hw'') hA

/-- SUV Section 13.4, fact used without proof (printed p. 412, critical implications are not
provable: "this can be easily shown using Kripke models"): soundness of IPC for Kripke models —
a provable formula is forced at every world of every Kripke model with a monotone valuation.
Proof: induction on the derivation; each axiom scheme is checked with `forces_mono`. -/
theorem forces_of_provable {ι W : Type*} [Preorder W] {V : W → ι → Prop}
    (hV : IsMonotoneValuation V) {Φ : PFormula ι} (h : Provable Φ) (w : W) : Forces V w Φ := by
  induction h generalizing w with
  | ax_k A B =>
      intro w1 _ hA w2 h12 _
      exact forces_mono hV A h12 hA
  | ax_s A B C =>
      intro w1 _ hABC w2 h12 hAB w3 h23 hA
      exact hABC w3 (h12.trans h23) hA w3 le_rfl (hAB w3 h23 hA)
  | ax_conj_left A B => intro w1 _ h; exact h.1
  | ax_conj_right A B => intro w1 _ h; exact h.2
  | ax_conj_intro A B =>
      intro w1 _ hA w2 h12 hB
      exact ⟨forces_mono hV A h12 hA, hB⟩
  | ax_disj_left A B => intro w1 _ h; exact Or.inl h
  | ax_disj_right A B => intro w1 _ h; exact Or.inr h
  | ax_disj_elim A B C =>
      intro w1 _ hAC w2 h12 hBC w3 h23 hAB
      rcases hAB with hA | hB
      · exact hAC w3 (h12.trans h23) hA
      · exact hBC w3 h23 hB
  | mp _ _ ihAB ihA => exact ihAB w w le_rfl (ihA w)

/-- Step 1 of the proof of `exists_finite_kripke_countermodel`: derivability from a
set of hypotheses in the Hilbert system (impredicative closure definition). -/
private def exists_finite_kripke_countermodel_Der {ι : Type} (Γ : Set (PFormula ι)) (A : PFormula ι)
    : Prop :=
  ∀ T : Set (PFormula ι), Γ ⊆ T → (∀ C, Provable C → C ∈ T) →
    (∀ C D, imp C D ∈ T → C ∈ T → D ∈ T) → A ∈ T

private theorem exists_finite_kripke_countermodel_der_hyp {ι : Type} {Γ : Set (PFormula ι)} {A :
    PFormula ι} (h : A ∈ Γ) :
    exists_finite_kripke_countermodel_Der Γ A :=
  fun _ hΓ _ _ => hΓ h

private theorem exists_finite_kripke_countermodel_der_ax {ι : Type} {Γ : Set (PFormula ι)} {A :
    PFormula ι}
    (h : Provable A) : exists_finite_kripke_countermodel_Der Γ A :=
  fun _ _ hP _ => hP A h

private theorem exists_finite_kripke_countermodel_der_mp {ι : Type} {Γ : Set (PFormula ι)} {A B :
    PFormula ι}
    (h1 : exists_finite_kripke_countermodel_Der Γ (imp A B)) (h2 :
        exists_finite_kripke_countermodel_Der Γ A) : exists_finite_kripke_countermodel_Der Γ B :=
  fun T hΓ hP hm => hm A B (h1 T hΓ hP hm) (h2 T hΓ hP hm)

private theorem exists_finite_kripke_countermodel_provable_self {ι : Type} (A : PFormula ι) :
    Provable (imp A A) :=
  Provable.mp (Provable.mp (Provable.ax_s A (imp A A) A) (Provable.ax_k A (imp A A)))
    (Provable.ax_k A A)

private theorem exists_finite_kripke_countermodel_deduction {ι : Type} {Γ : Set (PFormula ι)} {A B :
    PFormula ι}
    (h : exists_finite_kripke_countermodel_Der (insert A Γ) B) :
        exists_finite_kripke_countermodel_Der Γ (imp A B) := by
  intro T hΓ hP hm
  refine h {C | imp A C ∈ T} ?_ ?_ ?_
  · intro C hC
    rcases hC with rfl | hC
    · exact hP _ (exists_finite_kripke_countermodel_provable_self _)
    · exact hm _ _ (hP _ (Provable.ax_k C A)) (hΓ hC)
  · intro C hC
    exact hm _ _ (hP _ (Provable.ax_k C A)) (hP _ hC)
  · intro C D hCD hC
    have hCD' : imp A (imp C D) ∈ T := hCD
    have hC' : imp A C ∈ T := hC
    exact hm _ _ (hm _ _ (hP _ (Provable.ax_s A C D)) hCD') hC'

private theorem exists_finite_kripke_countermodel_der_disj_elim {ι : Type} {Γ : Set (PFormula ι)} {A
    B C : PFormula ι}
    (hA : exists_finite_kripke_countermodel_Der (insert A Γ) C) (hB :
        exists_finite_kripke_countermodel_Der (insert B Γ) C) (h :
        exists_finite_kripke_countermodel_Der Γ (disj A B)) :
    exists_finite_kripke_countermodel_Der Γ C :=
  exists_finite_kripke_countermodel_der_mp (exists_finite_kripke_countermodel_der_mp
      (exists_finite_kripke_countermodel_der_mp (exists_finite_kripke_countermodel_der_ax
      (Provable.ax_disj_elim A B C))
    (exists_finite_kripke_countermodel_deduction hA)) (exists_finite_kripke_countermodel_deduction
        hB)) h

private theorem exists_finite_kripke_countermodel_der_empty {ι : Type} {Φ : PFormula ι}
    (h : exists_finite_kripke_countermodel_Der (∅ : Set (PFormula ι)) Φ) : Provable Φ :=
  h {C | Provable C} (Set.empty_subset _) (fun _ hC => hC) (fun _ _ h1 h2 => Provable.mp h1 h2)

/-- Step 2 of the proof of `exists_finite_kripke_countermodel`: the (finite) set of
subformulas of a formula. -/
private def exists_finite_kripke_countermodel_subs {ι : Type} : PFormula ι → Set (PFormula ι)
  | var i => {var i}
  | conj A B => insert (conj A B) (exists_finite_kripke_countermodel_subs A ∪
      exists_finite_kripke_countermodel_subs B)
  | disj A B => insert (disj A B) (exists_finite_kripke_countermodel_subs A ∪
      exists_finite_kripke_countermodel_subs B)
  | imp A B => insert (imp A B) (exists_finite_kripke_countermodel_subs A ∪
      exists_finite_kripke_countermodel_subs B)

private theorem exists_finite_kripke_countermodel_subs_self {ι : Type} (Φ : PFormula ι) : Φ ∈
    exists_finite_kripke_countermodel_subs Φ := by
  cases Φ <;> simp [exists_finite_kripke_countermodel_subs]

private theorem exists_finite_kripke_countermodel_subs_finite {ι : Type} (Φ : PFormula ι) :
    (exists_finite_kripke_countermodel_subs Φ).Finite := by
  induction Φ with
  | var i => simp [exists_finite_kripke_countermodel_subs]
  | conj A B ihA ihB => exact (ihA.union ihB).insert _
  | disj A B ihA ihB => exact (ihA.union ihB).insert _
  | imp A B ihA ihB => exact (ihA.union ihB).insert _

private theorem exists_finite_kripke_countermodel_subs_trans {ι : Type} (Φ : PFormula ι) :
    ∀ C, C ∈ exists_finite_kripke_countermodel_subs Φ → exists_finite_kripke_countermodel_subs C ⊆
        exists_finite_kripke_countermodel_subs Φ := by
  induction Φ with
  | var i =>
    intro C h
    simp only [exists_finite_kripke_countermodel_subs, Set.mem_singleton_iff] at h
    subst h; exact subset_rfl
  | conj A B ihA ihB =>
    intro C h x hx
    simp only [exists_finite_kripke_countermodel_subs, Set.mem_insert_iff, Set.mem_union] at h ⊢
    rcases h with rfl | h | h
    · simpa [exists_finite_kripke_countermodel_subs] using hx
    · exact Or.inr (Or.inl (ihA C h hx))
    · exact Or.inr (Or.inr (ihB C h hx))
  | disj A B ihA ihB =>
    intro C h x hx
    simp only [exists_finite_kripke_countermodel_subs, Set.mem_insert_iff, Set.mem_union] at h ⊢
    rcases h with rfl | h | h
    · simpa [exists_finite_kripke_countermodel_subs] using hx
    · exact Or.inr (Or.inl (ihA C h hx))
    · exact Or.inr (Or.inr (ihB C h hx))
  | imp A B ihA ihB =>
    intro C h x hx
    simp only [exists_finite_kripke_countermodel_subs, Set.mem_insert_iff, Set.mem_union] at h ⊢
    rcases h with rfl | h | h
    · simpa [exists_finite_kripke_countermodel_subs] using hx
    · exact Or.inr (Or.inl (ihA C h hx))
    · exact Or.inr (Or.inr (ihB C h hx))

private theorem exists_finite_kripke_countermodel_subs_conj {ι : Type} {Φ : PFormula ι} {A B :
    PFormula ι}
    (h : conj A B ∈ exists_finite_kripke_countermodel_subs Φ) : A ∈
        exists_finite_kripke_countermodel_subs Φ ∧ B ∈ exists_finite_kripke_countermodel_subs Φ :=
  ⟨exists_finite_kripke_countermodel_subs_trans Φ _ h (by simp
      [exists_finite_kripke_countermodel_subs, exists_finite_kripke_countermodel_subs_self]),
    exists_finite_kripke_countermodel_subs_trans Φ _ h (by simp
        [exists_finite_kripke_countermodel_subs, exists_finite_kripke_countermodel_subs_self])⟩

private theorem exists_finite_kripke_countermodel_subs_disj {ι : Type} {Φ : PFormula ι} {A B :
    PFormula ι}
    (h : disj A B ∈ exists_finite_kripke_countermodel_subs Φ) : A ∈
        exists_finite_kripke_countermodel_subs Φ ∧ B ∈ exists_finite_kripke_countermodel_subs Φ :=
  ⟨exists_finite_kripke_countermodel_subs_trans Φ _ h (by simp
      [exists_finite_kripke_countermodel_subs, exists_finite_kripke_countermodel_subs_self]),
    exists_finite_kripke_countermodel_subs_trans Φ _ h (by simp
        [exists_finite_kripke_countermodel_subs, exists_finite_kripke_countermodel_subs_self])⟩

private theorem exists_finite_kripke_countermodel_subs_imp {ι : Type} {Φ : PFormula ι} {A B :
    PFormula ι}
    (h : imp A B ∈ exists_finite_kripke_countermodel_subs Φ) : A ∈
        exists_finite_kripke_countermodel_subs Φ ∧ B ∈ exists_finite_kripke_countermodel_subs Φ :=
  ⟨exists_finite_kripke_countermodel_subs_trans Φ _ h (by simp
      [exists_finite_kripke_countermodel_subs, exists_finite_kripke_countermodel_subs_self]),
    exists_finite_kripke_countermodel_subs_trans Φ _ h (by simp
        [exists_finite_kripke_countermodel_subs, exists_finite_kripke_countermodel_subs_self])⟩

/-- Step 3 of the proof of `exists_finite_kripke_countermodel`: worlds are the subsets
of `S` that are closed under derivability (within `S`) and prime. -/
private def exists_finite_kripke_countermodel_IsWorld {ι : Type} (S Γ : Set (PFormula ι)) : Prop :=
  Γ ⊆ S ∧ (∀ A ∈ S, exists_finite_kripke_countermodel_Der Γ A → A ∈ Γ) ∧ (∀ A B, disj A B ∈ Γ → A ∈
      Γ ∨ B ∈ Γ)

/-- Step 4 of the proof of `exists_finite_kripke_countermodel`: Lindenbaum lemma in
the finite setting. -/
private theorem exists_finite_kripke_countermodel_lindenbaum {ι : Type} {S : Set (PFormula ι)} (hfin
    : S.Finite)
    (hdisj : ∀ A B, disj A B ∈ S → A ∈ S ∧ B ∈ S) {Δ : Set (PFormula ι)} (hΔS : Δ ⊆ S)
    {B : PFormula ι} (hB : ¬ exists_finite_kripke_countermodel_Der Δ B) :
    ∃ Γ, Δ ⊆ Γ ∧ exists_finite_kripke_countermodel_IsWorld S Γ ∧ ¬
        exists_finite_kripke_countermodel_Der Γ B := by
  set F : Set (Set (PFormula ι)) := {Γ | Δ ⊆ Γ ∧ Γ ⊆ S ∧ ¬ exists_finite_kripke_countermodel_Der Γ
      B} with hF
  have hFfin : F.Finite := hfin.finite_subsets.subset (fun Γ hΓ => hΓ.2.1)
  obtain ⟨M, hΔM, hMF, hmax⟩ := hFfin.exists_le_maximal (a := Δ) ⟨subset_rfl, hΔS, hB⟩
  obtain ⟨hΔM', hMS, hMB⟩ := hMF
  have key : ∀ C, C ∈ S → ¬ exists_finite_kripke_countermodel_Der (insert C M) B → C ∈ M := by
    intro C hCS hn
    exact hmax ⟨hΔM'.trans (Set.subset_insert _ _), Set.insert_subset hCS hMS, hn⟩
      (Set.subset_insert _ _) (Set.mem_insert _ _)
  refine ⟨M, hΔM, ⟨hMS, ?_, ?_⟩, hMB⟩
  · intro C hCS hC
    by_contra hCM
    have : exists_finite_kripke_countermodel_Der (insert C M) B := by
      by_contra hn; exact hCM (key C hCS hn)
    exact hMB (exists_finite_kripke_countermodel_der_mp (exists_finite_kripke_countermodel_deduction
        this) hC)
  · intro A' B' h
    by_contra hn
    push Not at hn
    obtain ⟨hA'S, hB'S⟩ := hdisj A' B' (hMS h)
    have h1 : exists_finite_kripke_countermodel_Der (insert A' M) B := by
      by_contra hn'; exact hn.1 (key A' hA'S hn')
    have h2 : exists_finite_kripke_countermodel_Der (insert B' M) B := by
      by_contra hn'; exact hn.2 (key B' hB'S hn')
    exact hMB (exists_finite_kripke_countermodel_der_disj_elim h1 h2
        (exists_finite_kripke_countermodel_der_hyp h))

private abbrev exists_finite_kripke_countermodel_World {ι : Type} (S Γ0 : Set (PFormula ι)) : Type
    :=
  {Γ : Set (PFormula ι) // exists_finite_kripke_countermodel_IsWorld S Γ ∧ Γ0 ⊆ Γ}

/-- Step 5 of the proof of `exists_finite_kripke_countermodel`: truth lemma for the
formulas of `S`. -/
private theorem exists_finite_kripke_countermodel_truth {ι : Type} {S Γ0 : Set (PFormula ι)} (hfin :
    S.Finite)
    (hconj : ∀ A B, conj A B ∈ S → A ∈ S ∧ B ∈ S)
    (hdisj : ∀ A B, disj A B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ A B, imp A B ∈ S → A ∈ S ∧ B ∈ S) :
    ∀ (A : PFormula ι) (w : exists_finite_kripke_countermodel_World S Γ0), A ∈ S →
      (Forces (fun (w : exists_finite_kripke_countermodel_World S Γ0) i => var i ∈ w.1) w A ↔ A ∈
          w.1) := by
  intro A
  induction A with
  | var i => intro w _; exact Iff.rfl
  | conj A B ihA ihB =>
    intro w hS
    obtain ⟨hA, hB⟩ := hconj A B hS
    simp only [Forces]
    rw [ihA w hA, ihB w hB]
    constructor
    · rintro ⟨h1, h2⟩
      exact w.2.1.2.1 _ hS (exists_finite_kripke_countermodel_der_mp
          (exists_finite_kripke_countermodel_der_mp
        (exists_finite_kripke_countermodel_der_ax (Provable.ax_conj_intro A B))
            (exists_finite_kripke_countermodel_der_hyp h1))
            (exists_finite_kripke_countermodel_der_hyp h2))
    · intro h
      exact ⟨w.2.1.2.1 A hA (exists_finite_kripke_countermodel_der_mp
          (exists_finite_kripke_countermodel_der_ax (Provable.ax_conj_left A B))
          (exists_finite_kripke_countermodel_der_hyp h)),
        w.2.1.2.1 B hB (exists_finite_kripke_countermodel_der_mp
            (exists_finite_kripke_countermodel_der_ax (Provable.ax_conj_right A B))
            (exists_finite_kripke_countermodel_der_hyp h))⟩
  | disj A B ihA ihB =>
    intro w hS
    obtain ⟨hA, hB⟩ := hdisj A B hS
    simp only [Forces]
    rw [ihA w hA, ihB w hB]
    constructor
    · rintro (h | h)
      · exact w.2.1.2.1 _ hS (exists_finite_kripke_countermodel_der_mp
          (exists_finite_kripke_countermodel_der_ax (Provable.ax_disj_left A B))
          (exists_finite_kripke_countermodel_der_hyp h))
      · exact w.2.1.2.1 _ hS (exists_finite_kripke_countermodel_der_mp
          (exists_finite_kripke_countermodel_der_ax (Provable.ax_disj_right A B))
          (exists_finite_kripke_countermodel_der_hyp h))
    · intro h; exact w.2.1.2.2 A B h
  | imp A B ihA ihB =>
    intro w hS
    obtain ⟨hA, hB⟩ := himp A B hS
    constructor
    · intro hf
      by_contra hn
      have hnd : ¬ exists_finite_kripke_countermodel_Der (insert A w.1) B := by
        intro hd
        exact hn (w.2.1.2.1 _ hS (exists_finite_kripke_countermodel_deduction hd))
      have hsub : insert A w.1 ⊆ S :=
        Set.insert_subset hA w.2.1.1
      obtain ⟨Γ', hΓ'1, hΓ'2, hΓ'3⟩ := exists_finite_kripke_countermodel_lindenbaum hfin hdisj hsub
          hnd
      let w' : exists_finite_kripke_countermodel_World S Γ0 :=
        ⟨Γ', hΓ'2, w.2.2.trans ((Set.subset_insert _ _).trans hΓ'1)⟩
      have hle : w ≤ w' := (Set.subset_insert _ _).trans hΓ'1
      have hAw' : Forces (fun (w : exists_finite_kripke_countermodel_World S Γ0) i => var i ∈ w.1)
          w' A :=
        (ihA w' hA).2 (hΓ'1 (Set.mem_insert _ _))
      have := (ihB w' hB).1 (hf w' hle hAw')
      exact hΓ'3 (exists_finite_kripke_countermodel_der_hyp this)
    · intro h w' hle hAw'
      have h1 : A ∈ w'.1 := (ihA w' hA).1 hAw'
      have h2 : imp A B ∈ w'.1 := hle h
      have h3 := w'.2.1.2.1 B hB (exists_finite_kripke_countermodel_der_mp
          (exists_finite_kripke_countermodel_der_hyp h2) (exists_finite_kripke_countermodel_der_hyp
          h1))
      exact (ihB w' hB).2 h3

/-- SUV Section 13.5, fact used without proof (printed pp. 413-414: "using only the
completeness theorem for Kripke models and IPC"; "Let a finite Kripke model be given such that
`Φ` is false (in the root)"): completeness of IPC for finite Kripke models (finite model
property), for the negation-free formulas of Chapter 13 — an unprovable formula is refuted at
the root of a finite rooted partially ordered Kripke model with a monotone valuation.
Standard proof (not in the book): canonical model of prime theories restricted to the
subformulas of `Φ` (filtration), or a Gentzen-style proof search; then restrict to the cone
above a refuting world. -/
theorem exists_finite_kripke_countermodel {ι : Type} (Φ : PFormula ι) (h : ¬ Provable Φ) :
    ∃ (W : Type) (_ : Finite W) (_ : PartialOrder W) (r : W) (V : W → ι → Prop),
      (∀ w, r ≤ w) ∧ IsMonotoneValuation V ∧ ¬ Forces V r Φ := by
  have hfin := exists_finite_kripke_countermodel_subs_finite Φ
  have hΦ := exists_finite_kripke_countermodel_subs_self Φ
  have hnd : ¬ exists_finite_kripke_countermodel_Der (∅ : Set (PFormula ι)) Φ :=
    fun hd => h (exists_finite_kripke_countermodel_der_empty hd)
  obtain ⟨Γ0, -, hΓ0, hΓ0Φ⟩ := exists_finite_kripke_countermodel_lindenbaum hfin
    (fun A B h => exists_finite_kripke_countermodel_subs_disj h) (Set.empty_subset _) hnd
  have : Finite ↥{t : Set (PFormula ι) | t ⊆ exists_finite_kripke_countermodel_subs Φ} :=
    hfin.finite_subsets.to_subtype
  have hF : Finite (exists_finite_kripke_countermodel_World (exists_finite_kripke_countermodel_subs
      Φ) Γ0) :=
    Finite.of_injective
      (β := ↥{t : Set (PFormula ι) | t ⊆ exists_finite_kripke_countermodel_subs Φ})
      (fun w => ⟨w.1, w.2.1.1⟩)
      (fun a b hab => Subtype.ext (Subtype.mk.inj hab))
  refine ⟨exists_finite_kripke_countermodel_World (exists_finite_kripke_countermodel_subs Φ) Γ0, hF,
      inferInstance, ⟨Γ0, hΓ0, subset_rfl⟩,
    fun w i => var i ∈ w.1, fun w => w.2.2, fun w w' hle i hi => hle hi, ?_⟩
  intro hf
  have := (exists_finite_kripke_countermodel_truth hfin
    (fun A B h => exists_finite_kripke_countermodel_subs_conj h)
    (fun A B h => exists_finite_kripke_countermodel_subs_disj h)
    (fun A B h => exists_finite_kripke_countermodel_subs_imp h) Φ ⟨Γ0, hΓ0, subset_rfl⟩ hΦ).1 hf
  exact hΓ0Φ (exists_finite_kripke_countermodel_der_hyp this)

private theorem not_provable_criticalData_formula_forces_conjList {ι W : Type*} [Preorder W]
    {V : W → ι → Prop} (w : W) (d : PFormula ι) :
    ∀ l : List (PFormula ι), l ≠ [] → (Forces V w (conjList d l) ↔ ∀ A ∈ l, Forces V w A)
  | [], h => absurd rfl h
  | [A], _ => by simp [conjList]
  | A :: B :: l, _ => by
      rw [conjList, Forces, not_provable_criticalData_formula_forces_conjList w d (B :: l) (by
          simp)]
      simp

private theorem not_provable_criticalData_formula_forces_disjList {ι W : Type*} [Preorder W]
    {V : W → ι → Prop} (w : W) (d : PFormula ι) :
    ∀ l : List (PFormula ι), l ≠ [] → (Forces V w (disjList d l) ↔ ∃ A ∈ l, Forces V w A)
  | [], h => absurd rfl h
  | [A], _ => by simp [disjList]
  | A :: B :: l, _ => by
      rw [disjList, Forces, not_provable_criticalData_formula_forces_disjList w d (B :: l) (by
          simp)]
      simp

private theorem not_provable_criticalData_formula_finsetVars_ne {k : ℕ} {I : Finset (Fin k)}
    (hI : I.Nonempty) : finsetVars I ≠ [] := by
  obtain ⟨i, hi⟩ := hI
  intro h
  have : var i ∈ finsetVars I := by
    simp only [finsetVars, List.mem_map, List.mem_filter, List.mem_finRange, decide_eq_true_eq,
      true_and]
    exact ⟨i, hi, rfl⟩
  rw [h] at this
  simp at this

private theorem not_provable_criticalData_formula_forces_conj_vars {k : ℕ} {W : Type}
    [Preorder W] {V : W → Fin k → Prop} (w : W) (C : CriticalData k) {I : Finset (Fin k)}
    (hI : I.Nonempty) : Forces V w (C.premise I) ↔ ∀ i ∈ I, V w i := by
  unfold CriticalData.premise
  rw [not_provable_criticalData_formula_forces_conjList _ _ _
    (not_provable_criticalData_formula_finsetVars_ne hI)]
  simp [finsetVars, Forces]

private theorem not_provable_criticalData_formula_forces_disj_vars {k : ℕ} {W : Type}
    [Preorder W] {V : W → Fin k → Prop} (w : W) (C : CriticalData k) {J : Finset (Fin k)}
    (hJ : J.Nonempty) : Forces V w (C.target J) ↔ ∃ i ∈ J, V w i := by
  unfold CriticalData.target
  rw [not_provable_criticalData_formula_forces_disjList _ _ _
    (not_provable_criticalData_formula_finsetVars_ne hJ)]
  simp [finsetVars, Forces]

/-- SUV Section 13.4, remark on critical implications (printed p. 412): critical implications
are not provable in IPC.
The book: "this can be easily shown using Kripke models, and also follows from the previous
theorem".  A countermodel (by `forces_of_provable`): worlds are the finsets `T ⊆ Fin k` with
`T ≠ univ`, ordered by inclusion, root `∅`, `V T i ↔ i ∈ T`.  No variable holds at `∅`, so the
disjunction `R` fails there.  Each conjunct `(P_l → Q_l) → Q_l` holds everywhere: if `Q_l`
fails at `T` (i.e. `T ∩ J_l = ∅`) then the world `univ \ J_l ⊇ T` (proper since `J_l ≠ ∅`)
makes `P_l` true (`I_l ∩ J_l = ∅`) and `Q_l` false, so `P_l → Q_l` fails at `T`.
(The complexity route, Problem 340 plus Theorem 244, lives in modules importing this one.) -/
theorem not_provable_criticalData_formula {k : ℕ} (C : CriticalData k) :
    ¬ Provable C.formula := by
  classical
  intro hprov
  let W := {T : Finset (Fin k) // T ≠ Finset.univ}
  let V : W → Fin k → Prop := fun T i => i ∈ T.1
  have hV : IsMonotoneValuation V := fun T T' h i hi => h hi
  have h0 : (∅ : Finset (Fin k)) ≠ Finset.univ := by
    intro h
    have : (⟨0, C.pos⟩ : Fin k) ∈ (∅ : Finset (Fin k)) := by rw [h]; exact Finset.mem_univ _
    simp at this
  have hroot := forces_of_provable hV hprov ⟨∅, h0⟩
  unfold CriticalData.formula at hroot
  have hall : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, C.pos⟩, Finset.mem_univ _⟩
  have hcl : Forces V ⟨∅, h0⟩ (conjList C.dflt (C.pairs.map fun p =>
      imp (imp (C.premise p.1) (C.target p.2)) (C.target p.2))) := by
    rw [not_provable_criticalData_formula_forces_conjList _ _ _
      (by simpa using C.pairs_ne_nil)]
    intro A hA
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hA
    intro w'' _ hPQ
    by_contra hQ
    rw [not_provable_criticalData_formula_forces_disj_vars _ C (C.right_nonempty p hp)] at hQ
    push Not at hQ
    have hJ : (Finset.univ \ p.2) ≠ Finset.univ := by
      obtain ⟨j, hj⟩ := C.right_nonempty p hp
      intro h
      have : j ∈ Finset.univ \ p.2 := by rw [h]; exact Finset.mem_univ _
      simp [hj] at this
    have hle : w'' ≤ (⟨Finset.univ \ p.2, hJ⟩ : W) := by
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hiJ => hQ i hiJ hi
    have hP : Forces V (⟨Finset.univ \ p.2, hJ⟩ : W) (C.premise p.1) := by
      rw [not_provable_criticalData_formula_forces_conj_vars _ C (C.left_nonempty p hp)]
      intro i hi
      simp only [V, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hiJ => Finset.disjoint_left.1 (C.disjoint p hp) hi hiJ
    have hQ' := hPQ _ hle hP
    rw [not_provable_criticalData_formula_forces_disj_vars _ C (C.right_nonempty p hp)] at hQ'
    obtain ⟨i, hi, hiV⟩ := hQ'
    simp only [V, Finset.mem_sdiff, Finset.mem_univ, true_and] at hiV
    exact hiV hi
  have hR := hroot _ le_rfl hcl
  unfold CriticalData.conclusion at hR
  rw [not_provable_criticalData_formula_forces_disjList _ _ _
    (not_provable_criticalData_formula_finsetVars_ne hall)] at hR
  obtain ⟨A, hA, hF⟩ := hR
  simp only [finsetVars, List.mem_map, List.mem_filter, List.mem_finRange, decide_eq_true_eq,
    true_and] at hA
  obtain ⟨i, -, rfl⟩ := hA
  simp [Forces, V] at hF

end InformationLogic
end Kolmogorov
