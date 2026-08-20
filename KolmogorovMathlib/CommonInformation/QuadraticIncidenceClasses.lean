import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import KolmogorovMathlib.CommonInformation.AffineIncidence

/-!
# Quadratic-extension incidence classes (SUV Exercise 311)

SUV Exercise 311 studies the affine point/line incidence graph over a field `F`
of cardinality `q ^ 2`, which contains a subfield `G` of cardinality `q`.  The
hint in the source splits the incident pairs into `q ^ 3` classes, each class
containing at most `q ^ 3` incident pairs, but involving only `q ^ 2` points and
`q ^ 2` lines.

This file formalizes exactly that combinatorial classification.  We work with a
field `G` and a field extension `F` with a two-element basis `b : Basis (Fin 2) G F`
(so `Fintype.card F = Fintype.card G ^ 2` whenever `G` is finite), and we write
`α = b 1` for the second basis vector, assuming `b 0 = 1`.

Following the hint, a line is written as `y = k x + c` with

* `k = f • 1 + r • α`,
* `c = h • 1 + (s - f * t) • α`,

and its points as

* `x = g • 1 + t • α`,
* `y = (f * g + h) • 1 + (g * r + s) • α + (r * t) • α ^ 2`.

Fixing the *key* `(r, t, s) ∈ G ^ 3` gives one class.  The line only depends on
the two parameters `(f, h)` and the point only depends on the two parameters
`(g, f * g + h)`, which is precisely the trick that makes both projections have
at most `q ^ 2` elements.

Main results:

* `incidenceClass_incident` — every pair in a class is a genuine incidence;
* `incidenceClass_lines_card_le`, `incidenceClass_points_card_le`,
  `incidenceClass_card_le` — the three counting bounds `q ^ 2`, `q ^ 2`, `q ^ 3`;
* `exists_incidenceClass_mem` — the classes cover all incident pairs;
* `exists_incidenceClass_containing_edge` — the packaged Exercise 311 statement;
* `quadraticRectangleFamily_covers` — the same data as a covering family of
  `q ^ 3` combinatorial rectangles of size at most `q ^ 2 × q ^ 2`.
-/

namespace Kolmogorov
namespace QuadraticIncidence

open AffineIncidence

variable {G F : Type*} [Field G] [Field F] [Algebra G F]

/-- The line `y = k x + c` with `k = f • b 0 + r • b 1` and
`c = h • b 0 + (s - f * t) • b 1`, where `(r, t, s)` is the class key and
`(f, h)` are the free parameters. -/
noncomputable def incidenceLine (b : Module.Basis (Fin 2) G F) (key : G × G × G)
    (fh : G × G) : Line F :=
  (fh.1 • b 0 + key.1 • b 1, fh.2 • b 0 + (key.2.2 - fh.1 * key.2.1) • b 1)

/-- The point `(x, y)` with `x = g • b 0 + t • b 1` and
`y = v • b 0 + (g * r + s) • b 1 + (r * t) • b 1 ^ 2`, where `(r, t, s)` is the
class key and `(g, v)` are the free parameters (`v = f * g + h`). -/
noncomputable def incidencePoint (b : Module.Basis (Fin 2) G F) (key : G × G × G)
    (gv : G × G) : Point F :=
  (gv.1 • b 0 + key.2.1 • b 1,
    gv.2 • b 0 + (gv.1 * key.1 + key.2.2) • b 1 + (key.1 * key.2.1) • b 1 ^ 2)

/-- The incidence class attached to a key `(r, t, s)`: all pairs obtained by
letting the parameters `(f, g, h)` range over `G ^ 3`. -/
noncomputable def incidenceClass [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) (key : G × G × G) : Finset (Point F × Line F) :=
  Finset.image
    (fun p : G × G × G =>
      (incidencePoint b key (p.2.1, p.1 * p.2.1 + p.2.2), incidenceLine b key (p.1, p.2.2)))
    Finset.univ

/-- The algebraic identity behind the classification: with `b 0 = 1`, the point
of `incidencePoint` with parameters `(g, f * g + h)` really lies on the line of
`incidenceLine` with parameters `(f, h)`. -/
lemma line_apply_eq (b : Module.Basis (Fin 2) G F) (hb : b 0 = 1) (r t s f g h : G) :
    (f • b 0 + r • b 1) * (g • b 0 + t • b 1) + (h • b 0 + (s - f * t) • b 1)
      = (f * g + h) • b 0 + (g * r + s) • b 1 + (r * t) • b 1 ^ 2 := by
  simp only [hb, Algebra.smul_def, map_add, map_sub, map_mul, mul_one]
  ring

lemma incident_incidencePoint_incidenceLine (b : Module.Basis (Fin 2) G F) (hb : b 0 = 1)
    (key : G × G × G) (f g h : G) :
    Incident (incidencePoint b key (g, f * g + h)) (incidenceLine b key (f, h)) := by
  obtain ⟨r, t, s⟩ := key
  simpa [Incident, incidencePoint, incidenceLine] using
    (line_apply_eq b hb r t s f g h).symm

/-- Incidence classes are never empty. -/
lemma incidenceClass_nonempty [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) (key : G × G × G) :
    (incidenceClass b key).Nonempty :=
  Finset.Nonempty.image ⟨(0, 0, 0), Finset.mem_univ _⟩ _

/-- Every pair in an incidence class is a genuine point/line incidence. -/
lemma incidenceClass_incident [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) (hb : b 0 = 1) (key : G × G × G)
    {e : Point F × Line F} (he : e ∈ incidenceClass b key) :
    Incident e.1 e.2 := by
  simp only [incidenceClass, Finset.mem_image, Finset.mem_univ, true_and] at he
  obtain ⟨⟨f, g, h⟩, hfe⟩ := he
  subst hfe
  exact incident_incidencePoint_incidenceLine b hb key f g h

/-- The lines occurring in a class are parametrized by two elements of `G`. -/
theorem incidenceClass_lines_card_le [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) (key : G × G × G) :
    ((incidenceClass b key).image Prod.snd).card ≤ Fintype.card G ^ 2 := by
  classical
  have hsub : (incidenceClass b key).image Prod.snd ⊆
      Finset.image (incidenceLine b key) (Finset.univ : Finset (G × G)) := by
    intro ℓ hℓ
    simp only [Finset.mem_image, incidenceClass, Finset.mem_univ, true_and] at hℓ ⊢
    obtain ⟨e, ⟨⟨f, g, h⟩, hfe⟩, hesnd⟩ := hℓ
    exact ⟨(f, h), by rw [← hesnd, ← hfe]⟩
  calc ((incidenceClass b key).image Prod.snd).card
      ≤ (Finset.image (incidenceLine b key) (Finset.univ : Finset (G × G))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (G × G)).card := Finset.card_image_le
    _ = Fintype.card G ^ 2 := by
        simp [Finset.card_univ, pow_two]

/-- The points occurring in a class are parametrized by two elements of `G`;
this is the point of the reparametrization `v = f * g + h` in the hint. -/
theorem incidenceClass_points_card_le [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) (key : G × G × G) :
    ((incidenceClass b key).image Prod.fst).card ≤ Fintype.card G ^ 2 := by
  classical
  have hsub : (incidenceClass b key).image Prod.fst ⊆
      Finset.image (incidencePoint b key) (Finset.univ : Finset (G × G)) := by
    intro p hp
    simp only [Finset.mem_image, incidenceClass, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨e, ⟨⟨f, g, h⟩, hfe⟩, hefst⟩ := hp
    exact ⟨(g, f * g + h), by rw [← hefst, ← hfe]⟩
  calc ((incidenceClass b key).image Prod.fst).card
      ≤ (Finset.image (incidencePoint b key) (Finset.univ : Finset (G × G))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (G × G)).card := Finset.card_image_le
    _ = Fintype.card G ^ 2 := by
        simp [Finset.card_univ, pow_two]

/-- A class contains at most `q ^ 3` incident pairs. -/
theorem incidenceClass_card_le [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) (key : G × G × G) :
    (incidenceClass b key).card ≤ Fintype.card G ^ 3 := by
  classical
  calc (incidenceClass b key).card
      ≤ (Finset.univ : Finset (G × G × G)).card := Finset.card_image_le
    _ = Fintype.card G ^ 3 := by
        simp [Finset.card_univ, pow_succ, mul_assoc]

/-- Coordinates of an element of `F` in the basis `b`. -/
private lemma basis_decomp (b : Module.Basis (Fin 2) G F) (x : F) :
    x = (b.repr x 0) • b 0 + (b.repr x 1) • b 1 := by
  have hsum := b.sum_repr x
  rw [Fin.sum_univ_two] at hsum
  exact hsum.symm

/-- The classes cover all incident point/line pairs: given an incidence, there is
a key `(r, t, s)` whose class contains it. -/
theorem exists_incidenceClass_mem [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) (hb : b 0 = 1)
    (p : Point F) (ℓ : Line F) (hpl : Incident p ℓ) :
    ∃ key : G × G × G, (p, ℓ) ∈ incidenceClass b key := by
  classical
  obtain ⟨x, y⟩ := p
  obtain ⟨k, c⟩ := ℓ
  set f : G := b.repr k 0 with hf
  set r : G := b.repr k 1 with hr
  set g : G := b.repr x 0 with hg
  set t : G := b.repr x 1 with ht
  set h : G := b.repr c 0 with hh
  set s' : G := b.repr c 1 with hs'
  have hkc : k = f • b 0 + r • b 1 := basis_decomp b k
  have hxc : x = g • b 0 + t • b 1 := basis_decomp b x
  have hcc : c = h • b 0 + s' • b 1 := basis_decomp b c
  refine ⟨(r, t, s' + f * t), ?_⟩
  simp only [incidenceClass, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨(f, g, h), ?_⟩
  have hident := line_apply_eq b hb r t (s' + f * t) f g h
  rw [add_sub_cancel_right] at hident
  have hline : incidenceLine b (r, t, s' + f * t) (f, h) = (k, c) := by
    simp only [incidenceLine, add_sub_cancel_right]
    rw [← hkc, ← hcc]
  have hyeq : y = (f * g + h) • b 0 + (g * r + (s' + f * t)) • b 1 + (r * t) • b 1 ^ 2 := by
    have hy : y = k * x + c := hpl
    rw [hy, hkc, hxc, hcc, hident]
  have hpoint : incidencePoint b (r, t, s' + f * t) (g, f * g + h) = (x, y) := by
    simp only [incidencePoint]
    rw [← hxc, ← hyeq]
  rw [hpoint, hline]

/-- SUV Exercise 311, combinatorial core: every incident point/line pair over a
quadratic extension `F` of `G` lies in a class that contains at most
`|G| ^ 3` incidences, involves at most `|G| ^ 2` points, and involves at most
`|G| ^ 2` lines. -/
theorem exists_incidenceClass_containing_edge [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) (hb : b 0 = 1)
    (p : Point F) (ℓ : Line F) (hpl : Incident p ℓ) :
    ∃ key : G × G × G,
      (p, ℓ) ∈ incidenceClass b key ∧
      (∀ e ∈ incidenceClass b key, Incident e.1 e.2) ∧
      (incidenceClass b key).card ≤ Fintype.card G ^ 3 ∧
      ((incidenceClass b key).image Prod.fst).card ≤ Fintype.card G ^ 2 ∧
      ((incidenceClass b key).image Prod.snd).card ≤ Fintype.card G ^ 2 := by
  obtain ⟨key, hkey⟩ := exists_incidenceClass_mem b hb p ℓ hpl
  exact ⟨key, hkey, fun _ he => incidenceClass_incident b hb key he,
    incidenceClass_card_le b key, incidenceClass_points_card_le b key,
    incidenceClass_lines_card_le b key⟩

/-! ### The induced rectangle family -/

/-- The family of combinatorial rectangles obtained from the incidence classes:
one rectangle (points of the class) × (lines of the class) per key. -/
noncomputable def quadraticRectangleFamily [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) :
    Finset (CombinatorialRectangle (Point F) (Line F)) :=
  Finset.image
    (fun key : G × G × G =>
      ((incidenceClass b key).image Prod.fst, (incidenceClass b key).image Prod.snd))
    Finset.univ

lemma quadraticRectangleFamily_card_le [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) :
    (quadraticRectangleFamily b).card ≤ Fintype.card G ^ 3 := by
  classical
  calc (quadraticRectangleFamily b).card
      ≤ (Finset.univ : Finset (G × G × G)).card := Finset.card_image_le
    _ = Fintype.card G ^ 3 := by
        simp [Finset.card_univ, pow_succ, mul_assoc]

/-- Every rectangle of the family has at most `|G| ^ 2` points on the left and at
most `|G| ^ 2` lines on the right. -/
lemma quadraticRectangleFamily_sides_card_le [Fintype G] [DecidableEq F]
    (b : Module.Basis (Fin 2) G F) {R : CombinatorialRectangle (Point F) (Line F)}
    (hR : R ∈ quadraticRectangleFamily b) :
    R.1.card ≤ Fintype.card G ^ 2 ∧ R.2.card ≤ Fintype.card G ^ 2 := by
  simp only [quadraticRectangleFamily, Finset.mem_image, Finset.mem_univ, true_and] at hR
  obtain ⟨key, hkey⟩ := hR
  subst hkey
  exact ⟨incidenceClass_points_card_le b key, incidenceClass_lines_card_le b key⟩

/-- The rectangle family covers the whole affine incidence graph: this is the
Exercise 311 covering statement, `|G| ^ 3` rectangles of size at most
`|G| ^ 2 × |G| ^ 2` covering all incidences. -/
theorem quadraticRectangleFamily_covers [Fintype G] [DecidableEq F] [Fintype F]
    (b : Module.Basis (Fin 2) G F) (hb : b 0 = 1) :
    RectangleFamilyCovers (Incident (F := F)) (quadraticRectangleFamily b)
      (incidentEdges F) := by
  intro e he
  obtain ⟨p, ℓ⟩ := e
  have hinc : Incident p ℓ := mem_incidentEdges_iff.mp he
  obtain ⟨key, hkey⟩ := exists_incidenceClass_mem b hb p ℓ hinc
  simp only [rectangleFamilyEdges, Finset.mem_biUnion, quadraticRectangleFamily,
    Finset.mem_image, Finset.mem_univ, true_and, Rel.mem_interedges_iff]
  exact ⟨_, ⟨key, rfl⟩, Finset.mem_image_of_mem Prod.fst hkey,
    Finset.mem_image_of_mem Prod.snd hkey, hinc⟩

end QuadraticIncidence
end Kolmogorov
