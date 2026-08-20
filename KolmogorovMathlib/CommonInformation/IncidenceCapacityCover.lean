import KolmogorovMathlib.CommonInformation.IncidenceRectangleCapacity
import KolmogorovMathlib.CommonInformation.IncidenceCapacityCode
import KolmogorovMathlib.CommonInformation.IncidenceShearCode
import KolmogorovMathlib.CommonInformation.AffineIncidence
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Restricted.EffectiveSelection

namespace Kolmogorov

open AffineIncidence

/-- Codes of all capacity-maximizing rectangles within the two side budgets. -/
def maximizingIncidenceRectangleCodes (n b c : Nat) : Finset BitString :=
  ((boundedIncidenceRectangles n b c).filter fun R =>
      (Rel.interedges Incident R.1 R.2).card = concreteIncidenceCapacity n b c).image
    (concreteIncidenceRectangleCode n)

lemma maximizingIncidenceRectangleCodes_nonempty (n b c : Nat) :
    (maximizingIncidenceRectangleCodes n b c).Nonempty := by
  obtain ⟨R, hb, hc, hcount⟩ := exists_capacity_rectangle n b c
  refine ⟨concreteIncidenceRectangleCode n R, ?_⟩
  rw [maximizingIncidenceRectangleCodes, Finset.mem_image]
  refine ⟨R, Finset.mem_filter.mpr ⟨?_, hcount⟩, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, hc⟩

/-- The canonical code of a capacity-maximizing rectangle: the first code
produced by the primitive-recursive enumeration of bounded rectangles whose
incident-edge count is maximal. -/
def incidenceCapacityRectangleCode (n b c : Nat) : BitString :=
  codeCapacityRectangleCode n b c

/-- The canonical capacity-maximizing rectangle selected by its code. -/
def incidenceCapacityRectangle (n b c : Nat) :
    CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)) :=
  concreteIncidenceRectangleDecode n (incidenceCapacityRectangleCode n b c)

lemma incidenceCapacityRectangle_spec (n b c : Nat) :
    let R := incidenceCapacityRectangle n b c
    R.1.card ≤ b ∧ R.2.card ≤ c ∧
      (Rel.interedges Incident R.1 R.2).card = concreteIncidenceCapacity n b c := by
  obtain ⟨R, hb, hc, hcount, hcode⟩ := codeCapacityRectangleCode_spec n b c
  have hrect : incidenceCapacityRectangle n b c = R := by
    rw [incidenceCapacityRectangle, incidenceCapacityRectangleCode, hcode,
      concreteIncidenceRectangleDecode_code]
  rw [hrect]
  exact ⟨hb, hc, hcount⟩

lemma incidenceCapacityRectangleCode_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      incidenceCapacityRectangleCode p.1 p.2.1 p.2.2) :=
  codeCapacityRectangleCode_primrec

/-- Canonical list of rectangle codes for a finite rectangle family. -/
def concreteIncidenceRectangleFamilyCode (n : Nat)
    (𝓡 : Finset (CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)))) :
    List BitString :=
  canonicalFinsetList (𝓡.image (concreteIncidenceRectangleCode n))

/-- Decode a list of rectangle codes, discarding duplicate rectangles. -/
def concreteIncidenceRectangleFamilyDecode (n : Nat) (codes : List BitString) :
    Finset (CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n))) :=
  (codes.map (concreteIncidenceRectangleDecode n)).toFinset

@[simp]
lemma concreteIncidenceRectangleFamilyDecode_code (n : Nat)
    (𝓡 : Finset (CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)))) :
    concreteIncidenceRectangleFamilyDecode n (concreteIncidenceRectangleFamilyCode n 𝓡) = 𝓡 := by
  ext R
  simp [concreteIncidenceRectangleFamilyDecode, concreteIncidenceRectangleFamilyCode]
  aesop

/-- Incident edges lying in one shear translate of a rectangle. -/
def shearRectangleEdgeList (n : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)))
    (g : ConcreteField n × ConcreteField n × ConcreteField n) :
    List (Point (ConcreteField n) × Line (ConcreteField n)) :=
  (concreteIncidentEdgeList n).filter fun e => decide
    (e ∈ Rel.interedges Incident (shearRectangle g R).1 (shearRectangle g R).2)

/-- Exhaustive finite search for a short sublist of shear parameters covering
all incident edges.  `computableGreedyCover` searches all sublists; the
combinatorial theorem is used only to prove that a suitable sublist exists. -/
def incidenceCapacityShearParams (n b c : Nat) :
    List (ConcreteField n × ConcreteField n × ConcreteField n) :=
  let T := concreteIncidentEdgeList n
  let R := incidenceCapacityRectangle n b c
  let K := concreteIncidenceCapacity n b c
  let bound := T.length * (Nat.log2 T.length + 1) / K
  computableGreedyCover T (concreteShearParams n)
    (shearRectangleEdgeList n R) K bound

lemma incidenceCapacityShearParams_eq (n b c : Nat) :
    incidenceCapacityShearParams n b c =
      computableGreedyCover (concreteIncidentEdgeList n) (concreteShearParams n)
        (shearRectangleEdgeList n (incidenceCapacityRectangle n b c))
        (concreteIncidenceCapacity n b c)
        ((concreteIncidentEdgeList n).length *
          (Nat.log2 (concreteIncidentEdgeList n).length + 1) /
            concreteIncidenceCapacity n b c) := rfl

/-- Singleton rectangle associated with an edge.  This is the harmless
zero-capacity fallback, where the weighted cardinality bound is automatic. -/
def singletonIncidentRectangle {n : Nat}
    (e : Point (ConcreteField n) × Line (ConcreteField n)) :
    CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)) :=
  ({e.1}, {e.2})

/-- Canonical codes for the computably selected shear cover.  Positive capacity
uses exhaustive subcover search among all shear translates; zero capacity uses
the singleton rectangle of every incident edge. -/
def incidenceCapacityShearCoverCode (n b c : Nat) : List BitString :=
  if concreteIncidenceCapacity n b c = 0 then
    (concreteIncidentEdgeList n).map fun e =>
      concreteIncidenceRectangleCode n (singletonIncidentRectangle e)
  else
    (incidenceCapacityShearParams n b c).map fun g =>
      concreteIncidenceRectangleCode n
        (shearRectangle g (incidenceCapacityRectangle n b c))

/-- The geometric cover decoded from `incidenceCapacityShearCoverCode`.  This
definition makes the code/cover connection judgmental instead of leaving a
vacuous standalone encoder theorem. -/
def incidenceCapacityShearCover (n b c : Nat) :
    Finset (CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n))) :=
  concreteIncidenceRectangleFamilyDecode n (incidenceCapacityShearCoverCode n b c)

lemma shearMultiplicityList (n b c : Nat) :
    ∀ x ∈ (concreteIncidentEdgeList n).toFinset,
      concreteIncidenceCapacity n b c ≤
        ((concreteShearParams n).toFinset.filter fun g =>
          x ∈ (shearRectangleEdgeList n (incidenceCapacityRectangle n b c) g).toFinset).card := by
  intro x hx
  have hxList : x ∈ concreteIncidentEdgeList n := List.mem_toFinset.mp hx
  have hxI : Incident x.1 x.2 := (mem_concreteIncidentEdgeList n x).mp hxList
  have hmul := shearRectangle_cover_multiplicity
    (⟨x, hxI⟩ : {e : Point (ConcreteField n) × Line (ConcreteField n) //
      Incident e.1 e.2}) (incidenceCapacityRectangle n b c)
  have hbase := (incidenceCapacityRectangle_spec n b c).2.2
  rw [concreteShearParams_toFinset]
  simpa [shearRectangleEdgeList, List.mem_toFinset, hxList, hbase] using hmul.ge

/-- The indexed greedy-cover theorem supplies a short sublist of the explicit
shear enumeration covering every explicit incident edge. -/
lemma exists_incidenceCapacityShearSublist (n b c : Nat)
    (hK : 0 < concreteIncidenceCapacity n b c) :
    ∃ C : List (ConcreteField n × ConcreteField n × ConcreteField n),
      C.Sublist (concreteShearParams n) ∧
      C.length ≤ (concreteIncidentEdgeList n).length *
        (Nat.log2 (concreteIncidentEdgeList n).length + 1) /
          concreteIncidenceCapacity n b c ∧
      ∀ x ∈ concreteIncidentEdgeList n,
        0 < (C.filter fun g => decide
          (x ∈ shearRectangleEdgeList n (incidenceCapacityRectangle n b c) g)).length := by
  let T := concreteIncidentEdgeList n
  let S := concreteShearParams n
  let cover := shearRectangleEdgeList n (incidenceCapacityRectangle n b c)
  let K := concreteIncidenceCapacity n b c
  let bound := T.length * (Nat.log2 T.length + 1) / K
  have hm : ∀ x ∈ T.toFinset, K ≤
      (S.toFinset.filter fun g => x ∈ (cover g).toFinset).card := by
    simpa [T, S, cover, K] using shearMultiplicityList n b c
  obtain ⟨C, hCS, hcov, hCbound⟩ :=
    greedy_cover_indexed T.toFinset S.toFinset (fun g => (cover g).toFinset)
      K hK hm
  let CList := S.filter fun g => decide (g ∈ C)
  have hCListSub : CList.Sublist S := List.filter_sublist
  have hCListNodup : CList.Nodup :=
    List.Sublist.nodup hCListSub (by simpa [S] using concreteShearParams_nodup n)
  have hCListFin : CList.toFinset = C := by
    ext g
    simp only [CList, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro hg
      exact ⟨List.mem_toFinset.mp (hCS hg), hg⟩
  have hCListLen : CList.length = C.card := by
    rw [← hCListFin]
    exact (List.toFinset_card_of_nodup hCListNodup).symm
  have hSTcard : S.toFinset.card = T.length := by
    rw [show S.toFinset =
        (Finset.univ : Finset (ConcreteField n × ConcreteField n × ConcreteField n)) by
          simpa [S] using concreteShearParams_toFinset n,
      Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
      show T.length = concretePrime n ^ 3 by
        simp [T],
      concreteField_card_eq]
    ring
  have hTcard : T.toFinset.card = T.length :=
    List.toFinset_card_of_nodup (by simpa [T] using concreteIncidentEdgeList_nodup n)
  have hCListBound : CList.length ≤ bound := by
    apply (Nat.le_div_iff_mul_le hK).mpr
    change CList.length * K ≤ T.length * (Nat.log2 T.length + 1)
    calc
      CList.length * K = C.card * K := by rw [hCListLen]
      _ ≤ S.toFinset.card * (Nat.log2 T.toFinset.card + 1) := hCbound
      _ = T.length * (Nat.log2 T.length + 1) := by rw [hSTcard, hTcard]
  have hCListCovers : ∀ x ∈ T,
      0 < (CList.filter fun g => decide (x ∈ cover g)).length := by
    intro x hx
    have hxfin : x ∈ T.toFinset := List.mem_toFinset.mpr hx
    have hxcover := hcov hxfin
    rw [Finset.mem_biUnion] at hxcover
    obtain ⟨g, hgC, hxg⟩ := hxcover
    apply List.length_pos_of_mem (a := g)
    rw [List.mem_filter]
    refine ⟨?_, decide_eq_true ?_⟩
    · change g ∈ S.filter fun g => decide (g ∈ C)
      rw [List.mem_filter]
      exact ⟨List.mem_toFinset.mp (hCS hgC), decide_eq_true hgC⟩
    · exact List.mem_toFinset.mp hxg
  exact ⟨CList, hCListSub, hCListBound, hCListCovers⟩

/-- Transporting the exhaustive-search coverage guarantee into the form
"some selected index covers `x`", with no decidability side conditions. -/
lemma exists_mem_computableGreedyCover {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : List α) (S : List β) (cover : β → List α) (m bound : ℕ)
    (hex : ∃ C : List β, C.Sublist S ∧ C.length ≤ bound ∧
      ∀ x ∈ T, ∃ g ∈ C, x ∈ cover g)
    (x : α) (hx : x ∈ T) :
    ∃ g ∈ computableGreedyCover T S cover m bound, x ∈ cover g := by
  obtain ⟨C, hsub, hlen, hcov⟩ := hex
  have hex' : ∃ C : List β, C.Sublist S ∧ C.length ≤ bound ∧ ∀ x ∈ T,
      0 < (C.filter (fun b => decide (x ∈ cover b))).length := by
    refine ⟨C, hsub, hlen, fun y hy => ?_⟩
    obtain ⟨g, hg, hyg⟩ := hcov y hy
    exact List.length_pos_of_mem (a := g) (List.mem_filter.mpr ⟨hg, decide_eq_true hyg⟩)
  have hpos := computableGreedyCover_covers_of_exists T S cover m bound hex' x hx
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos hpos)
  rw [List.mem_filter, decide_eq_true_eq] at hg
  exact ⟨g, hg.1, hg.2⟩

lemma incidenceCapacityShearCover_covers (n b c : Nat) :
    RectangleFamilyCovers Incident (incidenceCapacityShearCover n b c)
      (incidentEdges (ConcreteField n)) := by
  intro x hx
  have hxI : Incident x.1 x.2 := mem_incidentEdges_iff.mp hx
  have hxL : x ∈ concreteIncidentEdgeList n := (mem_concreteIncidentEdgeList n x).mpr hxI
  simp only [rectangleFamilyEdges, Finset.mem_biUnion]
  by_cases hK : concreteIncidenceCapacity n b c = 0
  · refine ⟨singletonIncidentRectangle x, ?_, ?_⟩
    · rw [incidenceCapacityShearCover, concreteIncidenceRectangleFamilyDecode,
        List.mem_toFinset, List.mem_map]
      refine ⟨concreteIncidenceRectangleCode n (singletonIncidentRectangle x), ?_,
        concreteIncidenceRectangleDecode_code n _⟩
      rw [incidenceCapacityShearCoverCode, if_pos hK, List.mem_map]
      exact ⟨x, hxL, rfl⟩
    · rw [mem_interedges_iff_of_decidable]
      exact ⟨by simp [singletonIncidentRectangle], by simp [singletonIncidentRectangle], hxI⟩
  · have hex : ∃ C : List (ConcreteField n × ConcreteField n × ConcreteField n),
        C.Sublist (concreteShearParams n) ∧
        C.length ≤ (concreteIncidentEdgeList n).length *
          (Nat.log2 (concreteIncidentEdgeList n).length + 1) /
            concreteIncidenceCapacity n b c ∧
        ∀ y ∈ concreteIncidentEdgeList n, ∃ g ∈ C,
          y ∈ shearRectangleEdgeList n (incidenceCapacityRectangle n b c) g := by
      obtain ⟨C, hsub, hlen, hcov⟩ :=
        exists_incidenceCapacityShearSublist n b c (Nat.pos_of_ne_zero hK)
      refine ⟨C, hsub, hlen, fun y hy => ?_⟩
      obtain ⟨g, hg⟩ :=
        List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos (hcov y hy))
      rw [List.mem_filter, decide_eq_true_eq] at hg
      exact ⟨g, hg.1, hg.2⟩
    have hmain : ∃ g ∈ incidenceCapacityShearParams n b c,
        x ∈ shearRectangleEdgeList n (incidenceCapacityRectangle n b c) g := by
      rw [incidenceCapacityShearParams_eq]
      exact exists_mem_computableGreedyCover _ _ _ _ _ hex x hxL
    obtain ⟨g, hgparams, hgx⟩ := hmain
    refine ⟨shearRectangle g (incidenceCapacityRectangle n b c), ?_, ?_⟩
    · rw [incidenceCapacityShearCover, concreteIncidenceRectangleFamilyDecode,
        List.mem_toFinset, List.mem_map]
      refine ⟨concreteIncidenceRectangleCode n
        (shearRectangle g (incidenceCapacityRectangle n b c)), ?_,
        concreteIncidenceRectangleDecode_code n _⟩
      rw [incidenceCapacityShearCoverCode, if_neg hK, List.mem_map]
      exact ⟨g, hgparams, rfl⟩
    · rw [shearRectangleEdgeList, List.mem_filter, decide_eq_true_eq] at hgx
      rw [mem_interedges_iff_of_decidable] at hgx ⊢
      exact hgx.2

/-- Every member of the positive-capacity cover is a translate of the selected
maximizer at the level needed by Exercise 312: both side budgets and the exact
capacity edge count are preserved. -/
lemma incidenceCapacityShearCover_member_spec (n b c : Nat)
    (hcap : 0 < concreteIncidenceCapacity n b c) :
    ∀ R ∈ incidenceCapacityShearCover n b c,
      R.1.card ≤ b ∧ R.2.card ≤ c ∧
        (Rel.interedges Incident R.1 R.2).card = concreteIncidenceCapacity n b c := by
  intro R hR
  rw [incidenceCapacityShearCover, concreteIncidenceRectangleFamilyDecode,
    List.mem_toFinset, List.mem_map] at hR
  obtain ⟨w, hw, rfl⟩ := hR
  rw [incidenceCapacityShearCoverCode, if_neg (Nat.ne_of_gt hcap), List.mem_map] at hw
  obtain ⟨g, hg, rfl⟩ := hw
  rw [concreteIncidenceRectangleDecode_code]
  obtain ⟨hbase1, hbase2, hbaseEdges⟩ := incidenceCapacityRectangle_spec n b c
  obtain ⟨hside1, hside2⟩ := rectangle_image_side_cards
    (pointShearEquiv g.1 g.2.1 g.2.2) (lineShearEquiv g.1 g.2.1 g.2.2)
    (incidenceCapacityRectangle n b c)
  refine ⟨?_, ?_, ?_⟩
  · calc
      (shearRectangle g (incidenceCapacityRectangle n b c)).1.card =
          (incidenceCapacityRectangle n b c).1.card := by
        simpa [shearRectangle] using hside1
      _ ≤ b := hbase1
  · calc
      (shearRectangle g (incidenceCapacityRectangle n b c)).2.card =
          (incidenceCapacityRectangle n b c).2.card := by
        simpa [shearRectangle] using hside2
      _ ≤ c := hbase2
  · calc
      (Rel.interedges Incident (shearRectangle g (incidenceCapacityRectangle n b c)).1
          (shearRectangle g (incidenceCapacityRectangle n b c)).2).card =
          (Rel.interedges Incident (incidenceCapacityRectangle n b c).1
            (incidenceCapacityRectangle n b c).2).card := by
        simpa [shearRectangle] using
          interedges_image_card_eq (pointShearEquiv g.1 g.2.1 g.2.2)
            (lineShearEquiv g.1 g.2.1 g.2.2)
            (pointShear_lineShear_incident_iff g.1 g.2.1 g.2.2)
            (incidenceCapacityRectangle n b c).1 (incidenceCapacityRectangle n b c).2
      _ = concreteIncidenceCapacity n b c := hbaseEdges

lemma incidenceCapacityShearCover_card_mul_le (n b c : Nat) :
    (incidenceCapacityShearCover n b c).card * concreteIncidenceCapacity n b c ≤
      (incidentEdges (ConcreteField n)).card *
        (Nat.log2 (incidentEdges (ConcreteField n)).card + 1) := by
  by_cases hK : concreteIncidenceCapacity n b c = 0
  · simp [hK]
  have hcodeLen : (incidenceCapacityShearCoverCode n b c).length =
      (incidenceCapacityShearParams n b c).length := by
    rw [incidenceCapacityShearCoverCode, if_neg hK, List.length_map]
  have hcardCode : (incidenceCapacityShearCover n b c).card ≤
      (incidenceCapacityShearCoverCode n b c).length := by
    simpa [incidenceCapacityShearCover, concreteIncidenceRectangleFamilyDecode] using
      List.toFinset_card_le
        ((incidenceCapacityShearCoverCode n b c).map
          (concreteIncidenceRectangleDecode n))
  have hparamLen : (incidenceCapacityShearParams n b c).length ≤
      (incidentEdges (ConcreteField n)).card *
        (Nat.log2 (incidentEdges (ConcreteField n)).card + 1) /
          concreteIncidenceCapacity n b c := by
    have h := computableGreedyCover_length_le
      (concreteIncidentEdgeList n) (concreteShearParams n)
      (shearRectangleEdgeList n (incidenceCapacityRectangle n b c))
      (concreteIncidenceCapacity n b c)
      ((concreteIncidentEdgeList n).length *
        (Nat.log2 (concreteIncidentEdgeList n).length + 1) /
          concreteIncidenceCapacity n b c)
    simpa [incidenceCapacityShearParams, incidentEdges_card, concreteField_card_eq] using h
  calc
    (incidenceCapacityShearCover n b c).card * concreteIncidenceCapacity n b c
        ≤ ((incidentEdges (ConcreteField n)).card *
            (Nat.log2 (incidentEdges (ConcreteField n)).card + 1) /
              concreteIncidenceCapacity n b c) * concreteIncidenceCapacity n b c := by
          apply Nat.mul_le_mul_right
          exact hcardCode.trans (hcodeLen.le.trans hparamLen)
    _ ≤ (incidentEdges (ConcreteField n)).card *
          (Nat.log2 (incidentEdges (ConcreteField n)).card + 1) :=
      Nat.div_mul_le_self _ _

/-- The canonical code of the selected capacity-maximizing rectangle is the
code produced by the code-level search. -/
lemma concreteIncidenceRectangleCode_capacityRectangle (n b c : Nat) :
    concreteIncidenceRectangleCode n (incidenceCapacityRectangle n b c) =
      incidenceCapacityRectangleCode n b c := by
  obtain ⟨R, -, -, -, hcode⟩ := codeCapacityRectangleCode_spec n b c
  have hrect : incidenceCapacityRectangle n b c = R := by
    rw [incidenceCapacityRectangle, incidenceCapacityRectangleCode, hcode,
      concreteIncidenceRectangleDecode_code]
  rw [hrect, ← hcode, incidenceCapacityRectangleCode]

/-- The cover codes are computed by a purely code-level search: an exhaustive
subcover search among the codes of all shear translates of the selected
maximizer, or the singleton rectangles of all incident edges. -/
lemma incidenceCapacityShearCoverCode_eq (n b c : Nat) :
    incidenceCapacityShearCoverCode n b c =
      if codeIncidenceCapacity n b c = 0 then
        (concreteIncidentEdgeCodePairs n).map fun pr =>
          pairCode (listCode [pr.1]) (listCode [pr.2])
      else
        computableGreedyCover (concreteIncidentEdgeCodePairs n)
          (codeShearRectangleCodes n (incidenceCapacityRectangleCode n b c))
          (codeShearCoverList n) (codeIncidenceCapacity n b c)
          (concretePrime n ^ 3 * (Nat.log2 (concretePrime n ^ 3) + 1) /
            codeIncidenceCapacity n b c) := by
  rw [incidenceCapacityShearCoverCode, codeIncidenceCapacity_eq]
  by_cases hK : concreteIncidenceCapacity n b c = 0
  · rw [if_pos hK, if_pos hK, concreteIncidentEdgeCodePairs_eq_map, List.map_map]
    refine List.map_congr_left ?_
    intro ed _
    exact concreteIncidenceRectangleCode_singleton n ed.1 ed.2
  · rw [if_neg hK, if_neg hK, incidenceCapacityShearParams_eq,
      concreteIncidentEdgeList_length, ← concreteIncidenceRectangleCode_capacityRectangle,
      codeShearRectangleCodes_eq, concreteIncidentEdgeCodePairs_eq_map]
    refine (computableGreedyCover_map _ _ _ _ _ (concreteEdgeCodePair n)
      (fun g => concreteIncidenceRectangleCode n
        (shearRectangle g (incidenceCapacityRectangle n b c)))
      (codeShearCoverList n) (concreteEdgeCodePair_injective n) ?_).symm
    intro g
    exact codeShearCoverList_code n (shearRectangle g (incidenceCapacityRectangle n b c))

private lemma incidenceEdgeCodePairs_primrec :
    Primrec (fun p : Nat × Nat × Nat => concreteIncidentEdgeCodePairs p.1) :=
  concreteIncidentEdgeCodePairs_primrec.comp Primrec.fst

private lemma singletonCoverCodes_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      (concreteIncidentEdgeCodePairs p.1).map fun pr =>
        pairCode (listCode [pr.1]) (listCode [pr.2])) :=
  Primrec.list_map incidenceEdgeCodePairs_primrec
    (pairCode_primrec.comp
      (listCode_primrec.comp (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.const [])))
      (listCode_primrec.comp (Primrec.list_cons.comp
        (Primrec.snd.comp Primrec.snd) (Primrec.const [])))).to₂

private lemma capacityShearCodes_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      codeShearRectangleCodes p.1 (incidenceCapacityRectangleCode p.1 p.2.1 p.2.2)) :=
  codeShearRectangleCodes_primrec Primrec.fst incidenceCapacityRectangleCode_primrec

private lemma capacityShearCover_primrec :
    Primrec₂ (fun (p : Nat × Nat × Nat) (w : BitString) => codeShearCoverList p.1 w) :=
  (codeShearCoverList_primrec (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

private lemma concretePrime_cube_primrec :
    Primrec (fun p : Nat × Nat × Nat => concretePrime p.1 ^ 3) :=
  (Primrec.nat_mul.comp (Primrec.nat_mul.comp
      (boundedPrimeSearch_primrec.comp Primrec.fst)
      (boundedPrimeSearch_primrec.comp Primrec.fst))
    (boundedPrimeSearch_primrec.comp Primrec.fst)).of_eq (fun _ => by ring)

private lemma capacityShearBound_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      concretePrime p.1 ^ 3 * (Nat.log2 (concretePrime p.1 ^ 3) + 1) /
        codeIncidenceCapacity p.1 p.2.1 p.2.2) :=
  Primrec.nat_div.comp
    (Primrec.nat_mul.comp concretePrime_cube_primrec
      (Primrec.succ.comp (nat_log2_primrec.comp concretePrime_cube_primrec)))
    codeIncidenceCapacity_primrec

private lemma capacityShearGreedy_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      computableGreedyCover (concreteIncidentEdgeCodePairs p.1)
        (codeShearRectangleCodes p.1 (incidenceCapacityRectangleCode p.1 p.2.1 p.2.2))
        (codeShearCoverList p.1) (codeIncidenceCapacity p.1 p.2.1 p.2.2)
        (concretePrime p.1 ^ 3 * (Nat.log2 (concretePrime p.1 ^ 3) + 1) /
          codeIncidenceCapacity p.1 p.2.1 p.2.2)) :=
  computableGreedyCover_primrec incidenceEdgeCodePairs_primrec capacityShearCodes_primrec
    capacityShearCover_primrec capacityShearBound_primrec

lemma incidenceCapacityShearCover_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      incidenceCapacityShearCoverCode p.1 p.2.1 p.2.2) := by
  have hcond : PrimrecPred (fun p : Nat × Nat × Nat =>
      codeIncidenceCapacity p.1 p.2.1 p.2.2 = 0) :=
    Primrec.eq.comp codeIncidenceCapacity_primrec (Primrec.const 0)
  exact (Primrec.ite hcond singletonCoverCodes_primrec capacityShearGreedy_primrec).of_eq
    (fun p => (incidenceCapacityShearCoverCode_eq p.1 p.2.1 p.2.2).symm)

end Kolmogorov
