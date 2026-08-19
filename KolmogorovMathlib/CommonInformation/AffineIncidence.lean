import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.LinearCombination
import KolmogorovMathlib.CommonInformation.RectangleCover
import KolmogorovMathlib.Restricted.GreedyCover

namespace Kolmogorov
namespace AffineIncidence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Point (F : Type*) := F × F
abbrev Line (F : Type*) := F × F

def Incident (p : Point F) (ℓ : Line F) : Prop :=
  p.2 = ℓ.1 * p.1 + ℓ.2

omit [Fintype F] in
instance instDecidableIncident : DecidableRel (Incident (F := F)) := fun p ℓ =>
  inferInstanceAs (Decidable (p.2 = ℓ.1 * p.1 + ℓ.2))

/-- The finite edge set of the nonvertical affine incidence graph over `F`. -/
def incidentEdges (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Point F × Line F) :=
  Rel.interedges Incident Finset.univ Finset.univ

@[simp]
lemma mem_incidentEdges_iff {e : Point F × Line F} :
    e ∈ incidentEdges F ↔ Incident e.1 e.2 := by
  classical
  rw [incidentEdges, Rel.mem_interedges_iff]
  simp

omit [Fintype F] [DecidableEq F] in
lemma incident_iff {p : Point F} {ℓ : Line F} :
  Incident p ℓ ↔ p.2 = ℓ.1 * p.1 + ℓ.2 := by
  rfl

omit [Fintype F] [DecidableEq F] in
lemma line_eq_of_two_distinct_incident_points {p₁ p₂ : Point F} {ℓ₁ ℓ₂ : Line F} :
  p₁ ≠ p₂ →
  Incident p₁ ℓ₁ →
  Incident p₂ ℓ₁ →
  Incident p₁ ℓ₂ →
  Incident p₂ ℓ₂ →
  ℓ₁ = ℓ₂ := by
  rintro hp h₁₁ h₂₁ h₁₂ h₂₂
  rcases p₁ with ⟨x₁, y₁⟩
  rcases p₂ with ⟨x₂, y₂⟩
  rcases ℓ₁ with ⟨m₁, b₁⟩
  rcases ℓ₂ with ⟨m₂, b₂⟩
  simp only [Incident] at h₁₁ h₂₁ h₁₂ h₂₂
  have hx : x₁ ≠ x₂ := by
    intro hxx
    apply hp
    apply Prod.ext hxx
    exact h₁₁.trans ((hxx ▸ h₂₁).symm)
  have hprod : (m₁ - m₂) * (x₁ - x₂) = 0 := by
    linear_combination -h₁₁ + h₁₂ + h₂₁ - h₂₂
  have hm : m₁ = m₂ := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hx))
  subst m₂
  have hb : b₁ = b₂ := by
    exact add_left_cancel (h₁₁.symm.trans h₁₂)
  exact Prod.ext rfl hb

def incidentPointEquiv (ℓ : Line F) :
  {p : Point F // Incident p ℓ} ≃ F :=
  { toFun := fun p => p.1.1
    invFun := fun x => ⟨(x, ℓ.1 * x + ℓ.2), rfl⟩
    left_inv := by
      rintro ⟨⟨x, y⟩, hy⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hy.symm
    right_inv := fun _ => rfl }

def incidentEdgeEquiv :
  {e : Point F × Line F // Incident e.1 e.2} ≃ Line F × F :=
  { toFun := fun e => (e.1.2, e.1.1.1)
    invFun := fun e =>
      ⟨((e.2, e.1.1 * e.2 + e.1.2), e.1), rfl⟩
    left_inv := by
      rintro ⟨⟨⟨x, y⟩, ⟨m, b⟩⟩, he⟩
      apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact he.symm
      · rfl
    right_inv := by
      rintro ⟨⟨m, b⟩, x⟩
      rfl }

omit [Field F] [DecidableEq F] in
lemma point_card :
  Fintype.card (Point F) = (Fintype.card F) ^ 2 := by
  simp [Point, pow_two]

omit [Field F] [DecidableEq F] in
lemma line_card :
  Fintype.card (Line F) = (Fintype.card F) ^ 2 := by
  simp [Line, pow_two]

open Classical in
lemma incident_points_card (ℓ : Line F) :
  (Rel.interedges Incident Finset.univ {ℓ}).card = Fintype.card F := by
  let edgeEquiv :
      ↥(Rel.interedges Incident
        (Finset.univ : Finset (Point F)) {ℓ}) ≃
      {p : Point F // Incident p ℓ} :=
    { toFun := fun e =>
        ⟨e.1.1, by
          have he := Rel.mem_interedges_iff.mp e.2
          have hline : e.1.2 = ℓ := by simpa using he.2.1
          simpa [hline] using he.2.2⟩
      invFun := fun p =>
        ⟨(p.1, ℓ), Rel.mem_interedges_iff.mpr ⟨Finset.mem_univ _, by simp, p.2⟩⟩
      left_inv := by
        rintro ⟨⟨p, line⟩, he⟩
        apply Subtype.ext
        have hline : line = ℓ := by
          simpa using (Rel.mem_interedges_iff.mp he).2.1
        exact Prod.ext rfl hline.symm
      right_inv := by
        rintro ⟨p, hp⟩
        rfl }
  calc
    (Rel.interedges Incident Finset.univ {ℓ}).card =
        Fintype.card ↥(Rel.interedges Incident
          (Finset.univ : Finset (Point F)) {ℓ}) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {p : Point F // Incident p ℓ} :=
      Fintype.card_congr edgeEquiv
    _ = Fintype.card F := Fintype.card_congr (incidentPointEquiv ℓ)

open Classical in
lemma incidentEdges_card :
  (incidentEdges F).card = (Fintype.card F) ^ 3 := by
  let edgeEquiv :
      ↥(incidentEdges F) ≃
      {e : Point F × Line F // Incident e.1 e.2} :=
    { toFun := fun e =>
        ⟨e.1, mem_incidentEdges_iff.mp e.2⟩
      invFun := fun e =>
        ⟨e.1, mem_incidentEdges_iff.mpr e.2⟩
      left_inv := fun e => Subtype.ext rfl
      right_inv := fun e => Subtype.ext rfl }
  calc
    (incidentEdges F).card = Fintype.card ↥(incidentEdges F) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {e : Point F × Line F // Incident e.1 e.2} :=
      Fintype.card_congr edgeEquiv
    _ = Fintype.card (Line F × F) :=
      Fintype.card_congr incidentEdgeEquiv
    _ = (Fintype.card F) ^ 3 := by
      simp [Line, pow_succ]

omit [Fintype F] [DecidableEq F] in
lemma noFourCycle :
  NoFourCycle (Incident (F := F)) := by
  classical
  intro p₁ p₂ ℓ₁ ℓ₂ h₁₁ h₁₂ h₂₁ h₂₂
  by_cases hp : p₁ = p₂
  · exact Or.inl hp
  · exact Or.inr
      (line_eq_of_two_distinct_incident_points hp h₁₁ h₂₁ h₁₂ h₂₂)

omit [Fintype F] [DecidableEq F] in
def pointShearEquiv (A s B : F) : Point F ≃ Point F where
  toFun p := (p.1 + A, p.2 + s * p.1 + B)
  invFun p := (p.1 - A, p.2 - s * (p.1 - A) - B)
  left_inv := by intro p; dsimp; ext <;> ring
  right_inv := by intro p; dsimp; ext <;> ring

omit [Fintype F] [DecidableEq F] in
def lineShearEquiv (A s B : F) : Line F ≃ Line F where
  toFun ell := (ell.1 + s, ell.2 + B - (ell.1 + s) * A)
  invFun ell := (ell.1 - s, ell.2 - B + ell.1 * A)
  left_inv := by intro ell; dsimp; ext <;> ring
  right_inv := by intro ell; dsimp; ext <;> ring

omit [Fintype F] [DecidableEq F] in
theorem pointShear_lineShear_incident_iff
    (A s B : F) (p : Point F) (ell : Line F) :
  Incident p ell ↔
    Incident (pointShearEquiv A s B p)
      (lineShearEquiv A s B ell) := by
  dsimp [Incident, pointShearEquiv, lineShearEquiv]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

omit [Field F] [Fintype F] in
lemma rectangle_image_side_cards
    (fp : Point F ≃ Point F) (fl : Line F ≃ Line F)
    (R : CombinatorialRectangle (Point F) (Line F)) :
  (R.1.image fp).card = R.1.card ∧
  (R.2.image fl).card = R.2.card := by
  constructor
  · exact Finset.card_image_of_injective R.1 fp.injective
  · exact Finset.card_image_of_injective R.2 fl.injective

omit [Fintype F] [DecidableEq F] in
theorem incidentEdge_shear_transitive
    (e₁ e₂ : {e : Point F × Line F // Incident e.1 e.2}) :
  ∃ A s B : F,
    pointShearEquiv A s B e₁.1.1 = e₂.1.1 ∧
    lineShearEquiv A s B e₁.1.2 = e₂.1.2 := by
  obtain ⟨⟨⟨x₁, y₁⟩, ⟨m₁, b₁⟩⟩, h₁⟩ := e₁
  obtain ⟨⟨⟨x₂, y₂⟩, ⟨m₂, b₂⟩⟩, h₂⟩ := e₂
  dsimp [Incident] at h₁ h₂
  let A := x₂ - x₁
  let s := m₂ - m₁
  let B := y₂ - y₁ - s * x₁
  refine ⟨A, s, B, ?_, ?_⟩
  · dsimp [pointShearEquiv]
    ext <;> ring
  · dsimp [lineShearEquiv]
    ext
    · ring
    · linear_combination h₂ - h₁

omit [Fintype F] [DecidableEq F] in
theorem incidentEdge_transitive
    (e₁ e₂ : {e : Point F × Line F // Incident e.1 e.2}) :
  ∃ fp : Point F ≃ Point F, ∃ fl : Line F ≃ Line F,
    fp e₁.1.1 = e₂.1.1 ∧
    fl e₁.1.2 = e₂.1.2 ∧
    ∀ p ell, Incident p ell ↔ Incident (fp p) (fl ell) := by
  obtain ⟨A, s, B, hp, hl⟩ := incidentEdge_shear_transitive e₁ e₂
  exact ⟨pointShearEquiv A s B, lineShearEquiv A s B, hp, hl,
    pointShear_lineShear_incident_iff A s B⟩

omit [Fintype F] in
/-- **Rectangle edge-count invariance under the affine action.**  Any pair of
equivalences `(fp, fl)` that preserves incidence carries the incident edges of a
rectangle `A × B` bijectively onto the incident edges of its image rectangle
`fp(A) × fl(B)`.  Hence the number of incident edges in a rectangle is invariant
under the shear action (`pointShearEquiv`/`lineShearEquiv`).  This is the
structural core of Razenshteyn's covering argument for Exercise 312: since the
affine group acts transitively on edges (`incidentEdge_transitive`) while
preserving both side cardinalities (`rectangle_image_side_cards`) and incident
edge counts, a single dense rectangle can be moved to cover any target edge. -/
theorem interedges_image_card_eq
    (fp : Point F ≃ Point F) (fl : Line F ≃ Line F)
    (hinc : ∀ p ell, Incident p ell ↔ Incident (fp p) (fl ell))
    (A : Finset (Point F)) (B : Finset (Line F)) :
    (Rel.interedges Incident (A.image fp) (B.image fl)).card
      = (Rel.interedges Incident A B).card := by
  classical
  have hinj : Function.Injective (Prod.map fp fl) := fp.injective.prodMap fl.injective
  rw [← Finset.card_image_of_injective (Rel.interedges Incident A B) hinj]
  congr 1
  ext e
  constructor
  · intro hmem
    rw [Rel.mem_interedges_iff] at hmem
    obtain ⟨hp', hell', hI⟩ := hmem
    rw [Finset.mem_image] at hp' hell'
    obtain ⟨p, hp, hpeq⟩ := hp'
    obtain ⟨ell, hell, helleq⟩ := hell'
    rw [Finset.mem_image]
    refine ⟨(p, ell), ?_, Prod.ext hpeq helleq⟩
    rw [Rel.mem_interedges_iff]
    refine ⟨hp, hell, ?_⟩
    rw [hinc p ell, hpeq, helleq]
    exact hI
  · intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨⟨p, ell⟩, hpe, hmap⟩ := hmem
    rw [Rel.mem_interedges_iff] at hpe
    obtain ⟨hp, hell, hI⟩ := hpe
    rw [Rel.mem_interedges_iff, ← hmap]
    exact ⟨Finset.mem_image_of_mem fp hp, Finset.mem_image_of_mem fl hell,
      (hinc p ell).mp hI⟩

omit [Fintype F] [DecidableEq F] in
lemma interedges_decidable_congr (A : Finset (Point F)) (B : Finset (Line F))
    (d1 d2 : DecidableRel (Incident (F := F))) :
  @Rel.interedges _ _ (Incident (F := F)) d1 A B =
    @Rel.interedges _ _ (Incident (F := F)) d2 A B := by
  ext ⟨a, b⟩
  simp [Rel.mem_interedges_iff]

open Classical in
theorem incidentEdges_card_le_family_card_mul
    (𝓡 : Finset (CombinatorialRectangle (Point F) (Line F))) (M : ℕ) :
  (∀ R ∈ 𝓡, (Rel.interedges (Incident (F := F)) R.1 R.2).card ≤ M) →
  RectangleFamilyCovers (Incident (F := F)) 𝓡 (incidentEdges F) →
  (incidentEdges F).card ≤ 𝓡.card * M := by
  intro hM hcover
  have hsum := card_of_rectangleFamilyCovers_le_sum (Incident (F := F)) hcover
  have h_congr : ∀ R : CombinatorialRectangle (Point F) (Line F),
    (@Rel.interedges _ _ (Incident (F := F))
      (fun a a_1 => propDecidable (Incident a a_1)) R.1 R.2).card =
    (@Rel.interedges _ _ (Incident (F := F))
      (fun a a_1 => instDecidableIncident a a_1) R.1 R.2).card := by
    intro R
    congr 1
    apply interedges_decidable_congr
  simp_rw [h_congr] at hsum
  calc
    (incidentEdges F).card ≤ ∑ R ∈ 𝓡, (Rel.interedges (Incident (F := F)) R.1 R.2).card := hsum
    _ ≤ ∑ _ ∈ 𝓡, M := Finset.sum_le_sum (fun R hR => hM R hR)
    _ = 𝓡.card * M := by simp

open Classical in
omit [Fintype F] in
theorem exists_image_rectangle_covering_edge
    (e₁ e₂ : {e : Point F × Line F // Incident e.1 e.2})
    (R : CombinatorialRectangle (Point F) (Line F))
    (he₁ : e₁.1 ∈ Rel.interedges (Incident (F := F)) R.1 R.2) :
  ∃ R' : CombinatorialRectangle (Point F) (Line F),
    e₂.1 ∈ Rel.interedges (Incident (F := F)) R'.1 R'.2 ∧
    (Rel.interedges (Incident (F := F)) R'.1 R'.2).card =
      (Rel.interedges (Incident (F := F)) R.1 R.2).card ∧
    R'.1.card = R.1.card ∧
    R'.2.card = R.2.card := by
  obtain ⟨fp, fl, hfp, hfl, hinc⟩ := incidentEdge_transitive e₁ e₂
  let R' : CombinatorialRectangle (Point F) (Line F) := (R.1.image fp, R.2.image fl)
  use R'
  refine ⟨?_, ?_, ?_⟩
  · rw [Rel.mem_interedges_iff] at he₁ ⊢
    have h1 : e₂.1.1 = fp e₁.1.1 := hfp.symm
    have h2 : e₂.1.2 = fl e₁.1.2 := hfl.symm
    rw [h1, h2]
    refine ⟨Finset.mem_image_of_mem fp he₁.1, Finset.mem_image_of_mem fl he₁.2.1, ?_⟩
    rw [← hinc]
    exact he₁.2.2
  · exact interedges_image_card_eq fp fl hinc R.1 R.2
  · exact rectangle_image_side_cards fp fl R

/-- The image of a combinatorial rectangle under the shear with parameters
`g = (A, s, B)`. -/
def shearRectangle (g : F × F × F)
    (R : CombinatorialRectangle (Point F) (Line F)) :
    CombinatorialRectangle (Point F) (Line F) :=
  (R.1.image (pointShearEquiv g.1 g.2.1 g.2.2),
    R.2.image (lineShearEquiv g.1 g.2.1 g.2.2))

omit [Fintype F] in
lemma mem_shearRectangle_interedges_iff (g : F × F × F)
    (R : CombinatorialRectangle (Point F) (Line F)) (e : Point F × Line F) :
    e ∈ Rel.interedges Incident (shearRectangle g R).1 (shearRectangle g R).2 ↔
      ((pointShearEquiv g.1 g.2.1 g.2.2).symm e.1 ∈ R.1 ∧
        (lineShearEquiv g.1 g.2.1 g.2.2).symm e.2 ∈ R.2 ∧ Incident e.1 e.2) := by
  classical
  rw [Rel.mem_interedges_iff]
  have hp : e.1 ∈ (shearRectangle g R).1 ↔
      (pointShearEquiv g.1 g.2.1 g.2.2).symm e.1 ∈ R.1 := by
    constructor
    · intro h
      obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp h
      simpa [← hpe] using hp
    · intro h
      exact Finset.mem_image.mpr ⟨_, h, by simp⟩
  have hl : e.2 ∈ (shearRectangle g R).2 ↔
      (lineShearEquiv g.1 g.2.1 g.2.2).symm e.2 ∈ R.2 := by
    constructor
    · intro h
      obtain ⟨l, hl, hle⟩ := Finset.mem_image.mp h
      simpa [← hle] using hl
    · intro h
      exact Finset.mem_image.mpr ⟨_, h, by simp⟩
  rw [hp, hl]

omit [Fintype F] [DecidableEq F] in
/-- Explicit shear parameters carrying one incident edge onto another. -/
lemma shearParams_apply {p₀ p : Point F} {ell₀ ell : Line F}
    (h₀ : Incident p₀ ell₀) (h : Incident p ell) :
    pointShearEquiv (p.1 - p₀.1) (ell.1 - ell₀.1)
        (p.2 - p₀.2 - (ell.1 - ell₀.1) * p₀.1) p₀ = p ∧
      lineShearEquiv (p.1 - p₀.1) (ell.1 - ell₀.1)
        (p.2 - p₀.2 - (ell.1 - ell₀.1) * p₀.1) ell₀ = ell := by
  obtain ⟨x₀, y₀⟩ := p₀
  obtain ⟨x, y⟩ := p
  obtain ⟨m₀, b₀⟩ := ell₀
  obtain ⟨m, b⟩ := ell
  dsimp [Incident] at h₀ h
  refine ⟨?_, ?_⟩
  · dsimp [pointShearEquiv]
    ext <;> dsimp <;> ring
  · dsimp [lineShearEquiv]
    ext
    · dsimp; ring
    · dsimp; linear_combination h - h₀

omit [Fintype F] [DecidableEq F] in
/-- The shear parameters carrying a given point and line to their images are unique. -/
lemma shearParams_unique {A s B A' s' B' : F} {p₀ : Point F} {ell₀ : Line F}
    (hp : pointShearEquiv A s B p₀ = pointShearEquiv A' s' B' p₀)
    (hl : lineShearEquiv A s B ell₀ = lineShearEquiv A' s' B' ell₀) :
    ((A, s, B) : F × F × F) = (A', s', B') := by
  dsimp [pointShearEquiv] at hp
  dsimp [lineShearEquiv] at hl
  rw [Prod.ext_iff] at hp hl
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hl1, _⟩ := hl
  dsimp at hp1 hp2 hl1
  have hA : A = A' := by linear_combination hp1
  have hs : s = s' := by linear_combination hl1
  have hB : B = B' := by
    rw [hs] at hp2
    linear_combination hp2
  simp [hA, hs, hB]

/-- **Exact shear-cover multiplicity.**  For a fixed incident edge `e`, the number
of shear parameters `g` whose translated rectangle `shearRectangle g R` contains
`e` equals the number of incident edges of `R` itself. -/
theorem shearRectangle_cover_multiplicity
    (e : {e : Point F × Line F // Incident e.1 e.2})
    (R : CombinatorialRectangle (Point F) (Line F)) :
    (Finset.univ.filter (fun g : F × F × F =>
        e.1 ∈ Rel.interedges Incident
          (shearRectangle g R).1 (shearRectangle g R).2)).card =
      (Rel.interedges Incident R.1 R.2).card := by
  classical
  refine Finset.card_bij'
    (fun g _ => ((pointShearEquiv g.1 g.2.1 g.2.2).symm e.1.1,
      (lineShearEquiv g.1 g.2.1 g.2.2).symm e.1.2))
    (fun c _ => (e.1.1.1 - c.1.1, e.1.2.1 - c.2.1,
      e.1.1.2 - c.1.2 - (e.1.2.1 - c.2.1) * c.1.1))
    ?_ ?_ ?_ ?_
  · -- image of a covering parameter is an incident edge of `R`
    intro g hg
    rw [Finset.mem_filter] at hg
    obtain ⟨hmem1, hmem2, _⟩ :=
      (mem_shearRectangle_interedges_iff g R e.1).mp hg.2
    rw [Rel.mem_interedges_iff]
    refine ⟨hmem1, hmem2, ?_⟩
    rw [pointShear_lineShear_incident_iff g.1 g.2.1 g.2.2]
    simpa using e.2
  · -- the explicit parameters cover `e`
    intro c hc
    rw [Rel.mem_interedges_iff] at hc
    obtain ⟨hc1, hc2, hcI⟩ := hc
    obtain ⟨hap, hal⟩ := shearParams_apply hcI e.2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [mem_shearRectangle_interedges_iff]
    refine ⟨?_, ?_, e.2⟩
    · dsimp only
      rw [(Equiv.symm_apply_eq _).mpr hap.symm]
      exact hc1
    · dsimp only
      rw [(Equiv.symm_apply_eq _).mpr hal.symm]
      exact hc2
  · -- recovering the parameters from the preimage edge
    intro g hg
    rw [Finset.mem_filter] at hg
    obtain ⟨hmem1, hmem2, _⟩ :=
      (mem_shearRectangle_interedges_iff g R e.1).mp hg.2
    set p₀ := (pointShearEquiv g.1 g.2.1 g.2.2).symm e.1.1 with hp₀
    set ell₀ := (lineShearEquiv g.1 g.2.1 g.2.2).symm e.1.2 with hell₀
    have hI₀ : Incident p₀ ell₀ := by
      rw [pointShear_lineShear_incident_iff g.1 g.2.1 g.2.2]
      simpa [hp₀, hell₀] using e.2
    obtain ⟨hap, hal⟩ := shearParams_apply hI₀ e.2
    have hgp : pointShearEquiv g.1 g.2.1 g.2.2 p₀ = e.1.1 := by
      rw [hp₀, Equiv.apply_symm_apply]
    have hgl : lineShearEquiv g.1 g.2.1 g.2.2 ell₀ = e.1.2 := by
      rw [hell₀, Equiv.apply_symm_apply]
    have := shearParams_unique (hap.trans hgp.symm) (hal.trans hgl.symm)
    simpa using this
  · -- recovering the edge from the explicit parameters
    intro c hc
    rw [Rel.mem_interedges_iff] at hc
    obtain ⟨-, -, hcI⟩ := hc
    obtain ⟨hap, hal⟩ := shearParams_apply hcI e.2
    have h1 : (pointShearEquiv (e.1.1.1 - c.1.1) (e.1.2.1 - c.2.1)
        (e.1.1.2 - c.1.2 - (e.1.2.1 - c.2.1) * c.1.1)).symm e.1.1 = c.1 :=
      (Equiv.symm_apply_eq _).mpr hap.symm
    have h2 : (lineShearEquiv (e.1.1.1 - c.1.1) (e.1.2.1 - c.2.1)
        (e.1.1.2 - c.1.2 - (e.1.2.1 - c.2.1) * c.1.1)).symm e.1.2 = c.2 :=
      (Equiv.symm_apply_eq _).mpr hal.symm
    dsimp only
    rw [h1, h2]

/-- Membership in `Rel.interedges` for an arbitrary decidability instance. -/
lemma mem_interedges_iff_of_decidable {α β : Type*} (r : α → β → Prop)
    (d : (a : α) → DecidablePred (r a))
    (A : Finset α) (B : Finset β) (x : α × β) :
    x ∈ @Rel.interedges _ _ r d A B ↔ x.1 ∈ A ∧ x.2 ∈ B ∧ r x.1 x.2 := by
  simp [Rel.interedges, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- **Polynomial shear-image cover.**  Any rectangle `R` with at least one
incident edge can be translated by finitely many shears so that the resulting
family of congruent rectangles covers *every* incident edge of the affine
incidence graph, with total weight `|𝓡| · |edges of R|` bounded by
`|E| · (log₂ |E| + 1)`. -/
theorem exists_polynomial_shear_cover
    (R : CombinatorialRectangle (Point F) (Line F))
    (hR : (Rel.interedges Incident R.1 R.2).Nonempty) :
    ∃ 𝓡 : Finset (CombinatorialRectangle (Point F) (Line F)),
      RectangleFamilyCovers Incident 𝓡 (incidentEdges F) ∧
      (∀ R' ∈ 𝓡, R'.1.card = R.1.card ∧ R'.2.card = R.2.card ∧
        (Rel.interedges Incident R'.1 R'.2).card =
          (Rel.interedges Incident R.1 R.2).card) ∧
      𝓡.card * (Rel.interedges Incident R.1 R.2).card ≤
        (incidentEdges F).card *
          (Nat.log2 (incidentEdges F).card + 1) := by
  classical
  set m := (Rel.interedges Incident R.1 R.2).card with hm
  have hm_pos : 0 < m := Finset.card_pos.mpr hR
  set cover : F × F × F → Finset (Point F × Line F) := fun g =>
    Rel.interedges Incident (shearRectangle g R).1 (shearRectangle g R).2 with hcover
  have hmulti : ∀ x ∈ incidentEdges F,
      m ≤ ((Finset.univ : Finset (F × F × F)).filter (fun g => x ∈ cover g)).card := by
    intro x hx
    have hxI : Incident x.1 x.2 := mem_incidentEdges_iff.mp hx
    have hmul := shearRectangle_cover_multiplicity (⟨x, hxI⟩ :
      {e : Point F × Line F // Incident e.1 e.2}) R
    have heq : ((Finset.univ : Finset (F × F × F)).filter (fun g => x ∈ cover g))
        = (Finset.univ.filter (fun g : F × F × F =>
            (⟨x, hxI⟩ : {e : Point F × Line F // Incident e.1 e.2}).1 ∈
              Rel.interedges Incident
                (shearRectangle g R).1 (shearRectangle g R).2)) := by
      ext g
      simp [hcover]
    rw [hm, heq, hmul]
  obtain ⟨C, -, hcov, hcard⟩ :=
    greedy_cover_indexed (incidentEdges F) (Finset.univ : Finset (F × F × F))
      cover m hm_pos hmulti
  refine ⟨C.image (fun g => shearRectangle g R), ?_, ?_, ?_⟩
  · -- coverage
    intro x hx
    have hx' := hcov hx
    rw [Finset.mem_biUnion] at hx'
    obtain ⟨g, hgC, hxg⟩ := hx'
    simp only [rectangleFamilyEdges, Finset.mem_biUnion, Finset.mem_image]
    refine ⟨shearRectangle g R, ⟨g, hgC, rfl⟩, ?_⟩
    rw [mem_interedges_iff_of_decidable]
    rw [hcover, mem_interedges_iff_of_decidable] at hxg
    exact hxg
  · -- congruence of the translated rectangles
    intro R' hR'
    rw [Finset.mem_image] at hR'
    obtain ⟨g, -, rfl⟩ := hR'
    obtain ⟨h1, h2⟩ := rectangle_image_side_cards
      (pointShearEquiv g.1 g.2.1 g.2.2) (lineShearEquiv g.1 g.2.1 g.2.2) R
    refine ⟨h1, h2, ?_⟩
    exact interedges_image_card_eq (pointShearEquiv g.1 g.2.1 g.2.2)
      (lineShearEquiv g.1 g.2.1 g.2.2)
      (pointShear_lineShear_incident_iff g.1 g.2.1 g.2.2) R.1 R.2
  · -- the weight bound
    have hunivcard : (Finset.univ : Finset (F × F × F)).card
        = (incidentEdges F).card := by
      rw [incidentEdges_card, Finset.card_univ]
      simp [pow_succ, mul_comm]
    calc (C.image (fun g => shearRectangle g R)).card * m
        ≤ C.card * m := Nat.mul_le_mul_right _ (Finset.card_image_le)
      _ ≤ (Finset.univ : Finset (F × F × F)).card
            * (Nat.log2 (incidentEdges F).card + 1) := hcard
      _ = (incidentEdges F).card * (Nat.log2 (incidentEdges F).card + 1) := by
            rw [hunivcard]

/-- **Exercise 312, two-sided shear-cover estimate.**  Combining the necessity
bound `incidentEdges_card_le_family_card_mul` with the greedy shear cover
`exists_polynomial_shear_cover`: for any rectangle `R` carrying at least one
incident edge there is a family `𝓡` of shear translates of `R` covering all
incident edges whose total weight `|𝓡| · |edges of R|` is squeezed between
`|E|` and `|E| · (log₂ |E| + 1)`.  Thus the greedy translate cover is optimal up
to a logarithmic factor. -/
theorem exists_shear_cover_card_between
    (R : CombinatorialRectangle (Point F) (Line F))
    (hR : (Rel.interedges Incident R.1 R.2).Nonempty) :
    ∃ 𝓡 : Finset (CombinatorialRectangle (Point F) (Line F)),
      RectangleFamilyCovers Incident 𝓡 (incidentEdges F) ∧
      (∀ R' ∈ 𝓡, R'.1.card = R.1.card ∧ R'.2.card = R.2.card ∧
        (Rel.interedges Incident R'.1 R'.2).card =
          (Rel.interedges Incident R.1 R.2).card) ∧
      (incidentEdges F).card ≤ 𝓡.card * (Rel.interedges Incident R.1 R.2).card ∧
      𝓡.card * (Rel.interedges Incident R.1 R.2).card ≤
        (incidentEdges F).card * (Nat.log2 (incidentEdges F).card + 1) := by
  obtain ⟨𝓡, hcov, hcongr, hupper⟩ := exists_polynomial_shear_cover R hR
  refine ⟨𝓡, hcov, hcongr, ?_, hupper⟩
  refine incidentEdges_card_le_family_card_mul 𝓡
    (Rel.interedges Incident R.1 R.2).card ?_ hcov
  intro R' hR'
  exact le_of_eq (hcongr R' hR').2.2

/-- **Optimality of the shear cover up to a logarithmic factor.**  If *some*
family `𝓢` covers all incident edges using rectangles with at most as many
incident edges as `R`, then the family of shear translates of `R` produced by
`exists_polynomial_shear_cover` has at most `|𝓢| · (log₂ |E| + 1)` members.  So
no cover by rectangles of comparable density can beat the homogeneous shear
cover by more than a logarithmic factor. -/
theorem exists_shear_cover_card_le_mul_log
    (R : CombinatorialRectangle (Point F) (Line F))
    (hR : (Rel.interedges Incident R.1 R.2).Nonempty)
    (𝓢 : Finset (CombinatorialRectangle (Point F) (Line F)))
    (hcov𝓢 : RectangleFamilyCovers Incident 𝓢 (incidentEdges F))
    (hsize𝓢 : ∀ R' ∈ 𝓢, (Rel.interedges Incident R'.1 R'.2).card ≤
      (Rel.interedges Incident R.1 R.2).card) :
    ∃ 𝓡 : Finset (CombinatorialRectangle (Point F) (Line F)),
      RectangleFamilyCovers Incident 𝓡 (incidentEdges F) ∧
      (∀ R' ∈ 𝓡, R'.1.card = R.1.card ∧ R'.2.card = R.2.card ∧
        (Rel.interedges Incident R'.1 R'.2).card =
          (Rel.interedges Incident R.1 R.2).card) ∧
      𝓡.card ≤ 𝓢.card * (Nat.log2 (incidentEdges F).card + 1) := by
  set m := (Rel.interedges Incident R.1 R.2).card
  have hm_pos : 0 < m := Finset.card_pos.mpr hR
  obtain ⟨𝓡, hcov, hcongr, -, hupper⟩ := exists_shear_cover_card_between R hR
  refine ⟨𝓡, hcov, hcongr, ?_⟩
  have hE : (incidentEdges F).card ≤ 𝓢.card * m :=
    incidentEdges_card_le_family_card_mul 𝓢 m hsize𝓢 hcov𝓢
  have hchain : 𝓡.card * m ≤ (𝓢.card * (Nat.log2 (incidentEdges F).card + 1)) * m := by
    calc 𝓡.card * m
        ≤ (incidentEdges F).card * (Nat.log2 (incidentEdges F).card + 1) := hupper
      _ ≤ (𝓢.card * m) * (Nat.log2 (incidentEdges F).card + 1) :=
          Nat.mul_le_mul_right _ hE
      _ = (𝓢.card * (Nat.log2 (incidentEdges F).card + 1)) * m := by ring
  exact Nat.le_of_mul_le_mul_right hchain hm_pos

end AffineIncidence
end Kolmogorov
