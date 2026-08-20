import KolmogorovMathlib.CommonInformation.IncidenceRectangleCapacity
import KolmogorovMathlib.CommonInformation.AffineIncidence
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Restricted.EffectiveSelection

/-!
# Code-level enumeration of bounded incidence rectangles

This file provides the primitive-recursive, bitstring-level counterpart of the
capacity-maximizing rectangle search of Exercise 312.  Rectangles are
enumerated as pairs of sublists of the explicit list of all point (equivalently
line) codes, their incident-edge counts are computed by scanning the explicit
list of incident code pairs, and the capacity is the maximum of those counts.
-/

namespace Kolmogorov

open AffineIncidence

/-- Canonical bitstring code for a concrete point/line rectangle.  Each side is
sorted by the repository's canonical bitstring order before applying
`listCode`, so this code does not depend on a noncomputable `Finset.toList`. -/
def concreteIncidenceRectangleCode (n : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n))) :
    BitString :=
  pairCode
    (listCode (canonicalFinsetList (R.1.image (concretePointCode n))))
    (listCode (canonicalFinsetList (R.2.image (concreteLineCode n))))

/-- Decode the two canonical side lists of a concrete incidence rectangle. -/
def concreteIncidenceRectangleDecode (n : Nat) (w : BitString) :
    CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)) :=
  (((decodeListCode (decodeFirst w)).map (concretePointDecode n)).toFinset,
    ((decodeListCode (decodeSecond w)).map (concreteLineDecode n)).toFinset)

@[simp]
lemma concreteIncidenceRectangleDecode_code (n : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n))) :
    concreteIncidenceRectangleDecode n (concreteIncidenceRectangleCode n R) = R := by
  apply Prod.ext <;> ext p <;>
    simp [concreteIncidenceRectangleDecode, concreteIncidenceRectangleCode,
      decodeFirst_pairCode, decodeSecond_pairCode, decodeListCode_listCode] <;>
    aesop

/-- Explicit list of the fixed-width codes of all pairs of field elements,
i.e. of all points and, equivalently, of all nonvertical lines. -/
def concreteFieldPairCodeList (n : Nat) : List BitString :=
  (List.range (concretePrime n)).flatMap fun x =>
    (List.range (concretePrime n)).map fun y =>
      fixedWidthNatCode x (n + 1) ++ fixedWidthNatCode y (n + 1)

lemma mem_concreteFieldPairCodeList (n : Nat) (w : BitString) :
    w ∈ concreteFieldPairCodeList n ↔
      ∃ p : Point (ConcreteField n), concretePointCode n p = w := by
  constructor
  · intro hw
    simp only [concreteFieldPairCodeList, List.mem_flatMap, List.mem_range,
      List.mem_map] at hw
    obtain ⟨x, hx, y, hy, rfl⟩ := hw
    refine ⟨((x : ConcreteField n), (y : ConcreteField n)), ?_⟩
    simp [concretePointCode, concreteFieldCode,
      ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy]
  · rintro ⟨p, rfl⟩
    simp only [concreteFieldPairCodeList, List.mem_flatMap, List.mem_range,
      List.mem_map]
    exact ⟨p.1.val, ZMod.val_lt _, p.2.val, ZMod.val_lt _, rfl⟩

lemma concreteFieldPairCodeList_length (n : Nat) :
    (concreteFieldPairCodeList n).length = concretePrime n ^ 2 := by
  simp [concreteFieldPairCodeList, pow_succ]

lemma concreteFieldPairCodeList_nodup (n : Nat) :
    (concreteFieldPairCodeList n).Nodup := by
  have himage : (concreteFieldPairCodeList n).toFinset =
      Finset.univ.image (concretePointCode n) := by
    ext w
    simp only [List.mem_toFinset, mem_concreteFieldPairCodeList, Finset.mem_image,
      Finset.mem_univ, true_and]
  have hcard : (concreteFieldPairCodeList n).toFinset.card =
      (concreteFieldPairCodeList n).length := by
    rw [himage, Finset.card_image_of_injective _ (concretePointCode_injective n),
      Finset.card_univ, Fintype.card_prod, concreteField_card_eq,
      concreteFieldPairCodeList_length, pow_two]
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp hcard

lemma concreteLineCode_eq_pointCode (n : Nat) :
    concreteLineCode n = concretePointCode n := rfl

lemma concreteLineDecode_eq_pointDecode (n : Nat) :
    concreteLineDecode n = concretePointDecode n := rfl

lemma concretePointCode_decode_of_mem (n : Nat) {w : BitString}
    (hw : w ∈ concreteFieldPairCodeList n) :
    concretePointCode n (concretePointDecode n w) = w := by
  obtain ⟨p, rfl⟩ := (mem_concreteFieldPairCodeList n w).mp hw
  rw [concretePointDecode_code]

/-- The rectangle obtained by decoding a pair of code lists. -/
def decodedCodeRectangle (n : Nat) (A B : List BitString) :
    CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)) :=
  ((A.map (concretePointDecode n)).toFinset,
    (B.map (concretePointDecode n)).toFinset)

lemma mem_decodedCodeSide (n : Nat) {A : List BitString}
    (hA : ∀ w ∈ A, w ∈ concreteFieldPairCodeList n)
    (p : Point (ConcreteField n)) :
    p ∈ (A.map (concretePointDecode n)).toFinset ↔ concretePointCode n p ∈ A := by
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [concretePointCode_decode_of_mem n (hA w hw)]
    exact hw
  · intro h
    exact ⟨concretePointCode n p, h, concretePointDecode_code n p⟩

lemma decodedCodeSide_image (n : Nat) {A : List BitString}
    (hA : ∀ w ∈ A, w ∈ concreteFieldPairCodeList n) :
    ((A.map (concretePointDecode n)).toFinset).image (concretePointCode n) =
      A.toFinset := by
  ext w
  rw [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_decodedCodeSide n hA p).mp hp
  · intro hw
    refine ⟨concretePointDecode n w, ?_, concretePointCode_decode_of_mem n (hA w hw)⟩
    rw [mem_decodedCodeSide n hA, concretePointCode_decode_of_mem n (hA w hw)]
    exact hw

lemma decodedCodeSide_card (n : Nat) {A : List BitString}
    (hA : ∀ w ∈ A, w ∈ concreteFieldPairCodeList n) (hnd : A.Nodup) :
    ((A.map (concretePointDecode n)).toFinset).card = A.length := by
  have hcard := congrArg Finset.card (decodedCodeSide_image n hA)
  rw [Finset.card_image_of_injective _ (concretePointCode_injective n)] at hcard
  rw [hcard, List.toFinset_card_of_nodup hnd]

lemma decodedCodeRectangle_code (n : Nat) {A B : List BitString}
    (hA : ∀ w ∈ A, w ∈ concreteFieldPairCodeList n)
    (hB : ∀ w ∈ B, w ∈ concreteFieldPairCodeList n) :
    concreteIncidenceRectangleCode n (decodedCodeRectangle n A B) =
      pairCode (listCode (canonicalFinsetList A.toFinset))
        (listCode (canonicalFinsetList B.toFinset)) := by
  rw [concreteIncidenceRectangleCode, decodedCodeRectangle,
    concreteLineCode_eq_pointCode, decodedCodeSide_image n hA,
    decodedCodeSide_image n hB]

/-- Number of incident code pairs inside a pair of code lists. -/
def codeRectangleEdgeCount (n : Nat) (A B : List BitString) : Nat :=
  ((concreteIncidentEdgeCodePairs n).filter fun e =>
    decide (e.1 ∈ A) && decide (e.2 ∈ B)).length

lemma codeRectangleEdgeCount_eq (n : Nat) {A B : List BitString}
    (hA : ∀ w ∈ A, w ∈ concreteFieldPairCodeList n)
    (hB : ∀ w ∈ B, w ∈ concreteFieldPairCodeList n) :
    codeRectangleEdgeCount n A B =
      (Rel.interedges Incident (A.map (concretePointDecode n)).toFinset
        (B.map (concretePointDecode n)).toFinset).card := by
  have hfinj : Function.Injective
      (fun e : Point (ConcreteField n) × Line (ConcreteField n) =>
        (concretePointCode n e.1, concretePointCode n e.2)) := by
    intro e₁ e₂ h
    apply Prod.ext
    · exact concretePointCode_injective n (Prod.ext_iff.mp h).1
    · exact concretePointCode_injective n (Prod.ext_iff.mp h).2
  have hnd : ((concreteIncidentEdgeCodePairs n).filter fun e =>
      decide (e.1 ∈ A) && decide (e.2 ∈ B)).Nodup :=
    (concreteIncidentEdgeCodePairs_nodup n).filter _
  have hset : ((concreteIncidentEdgeCodePairs n).filter fun e =>
        decide (e.1 ∈ A) && decide (e.2 ∈ B)).toFinset =
      (Rel.interedges Incident (A.map (concretePointDecode n)).toFinset
        (B.map (concretePointDecode n)).toFinset).image
        (fun e => (concretePointCode n e.1, concretePointCode n e.2)) := by
    ext pair
    rw [List.mem_toFinset, List.mem_filter]
    simp only [Finset.mem_image, Bool.and_eq_true, decide_eq_true_eq,
      concreteIncidentEdgeCodePairs_mem_iff, mem_interedges_iff_of_decidable]
    constructor
    · rintro ⟨⟨e, rfl⟩, hmem1, hmem2⟩
      refine ⟨e.1, ⟨(mem_decodedCodeSide n hA e.1.1).mpr hmem1,
        (mem_decodedCodeSide n hB e.1.2).mpr hmem2, mem_incidentEdges_iff.mp e.2⟩, rfl⟩
    · rintro ⟨e, ⟨he1, he2, hinc⟩, rfl⟩
      exact ⟨⟨⟨e, mem_incidentEdges_iff.mpr hinc⟩, rfl⟩,
        (mem_decodedCodeSide n hA e.1).mp he1, (mem_decodedCodeSide n hB e.2).mp he2⟩
  rw [codeRectangleEdgeCount, ← List.toFinset_card_of_nodup hnd, hset,
    Finset.card_image_of_injective _ hfinj]

lemma sublist_mem_codeList {n : Nat} {A : List BitString}
    (hA : A.Sublist (concreteFieldPairCodeList n)) :
    ∀ w ∈ A, w ∈ concreteFieldPairCodeList n := fun _ hw => hA.subset hw

lemma exists_sublist_of_finset (n : Nat) (S : Finset (Point (ConcreteField n))) :
    ∃ A : List BitString, A.Sublist (concreteFieldPairCodeList n) ∧
      (A.map (concretePointDecode n)).toFinset = S ∧ A.length = S.card := by
  set A₀ := canonicalFinsetList (S.image (concretePointCode n)) with hA₀
  have hA₀nd : A₀.Nodup := canonicalFinsetList_nodup _
  have hA₀fin : A₀.toFinset = S.image (concretePointCode n) :=
    canonicalFinsetList_toFinset _
  have hA₀sub : A₀ ⊆ concreteFieldPairCodeList n := by
    intro w hw
    have : w ∈ S.image (concretePointCode n) := by
      rw [← hA₀fin]; exact List.mem_toFinset.mpr hw
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp this
    exact (mem_concreteFieldPairCodeList n _).mpr ⟨p, rfl⟩
  obtain ⟨A, hperm, hsub⟩ := List.subperm_of_subset hA₀nd hA₀sub
  have hAfin : A.toFinset = S.image (concretePointCode n) := by
    rw [← hA₀fin]
    exact List.toFinset_eq_of_perm _ _ hperm
  have himg : ((A.map (concretePointDecode n)).toFinset).image (concretePointCode n)
      = S.image (concretePointCode n) := by
    rw [decodedCodeSide_image n (sublist_mem_codeList hsub), hAfin]
  refine ⟨A, hsub, Finset.image_injective (concretePointCode_injective n) himg, ?_⟩
  rw [hperm.length_eq, ← List.toFinset_card_of_nodup hA₀nd, hA₀fin,
    Finset.card_image_of_injective _ (concretePointCode_injective n)]

/-- Explicit list of all bounded rectangle codes paired with their incident-edge
counts. -/
def boundedRectangleCodeCounts (n b c : Nat) : List (BitString × Nat) :=
  ((concreteFieldPairCodeList n).sublists.filter fun A => decide (A.length ≤ b)).flatMap
    fun A =>
      ((concreteFieldPairCodeList n).sublists.filter fun B => decide (B.length ≤ c)).map
        fun B =>
          (pairCode (listCode (canonicalFinsetList A.toFinset))
              (listCode (canonicalFinsetList B.toFinset)),
            codeRectangleEdgeCount n A B)

lemma mem_boundedRectangleCodeCounts_iff (n b c : Nat) (e : BitString × Nat) :
    e ∈ boundedRectangleCodeCounts n b c ↔
      ∃ A B : List BitString, A.Sublist (concreteFieldPairCodeList n) ∧
        B.Sublist (concreteFieldPairCodeList n) ∧ A.length ≤ b ∧ B.length ≤ c ∧
        e = (pairCode (listCode (canonicalFinsetList A.toFinset))
              (listCode (canonicalFinsetList B.toFinset)),
            codeRectangleEdgeCount n A B) := by
  simp only [boundedRectangleCodeCounts, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_sublists, decide_eq_true_eq]
  constructor
  · rintro ⟨A, ⟨hA, hAlen⟩, B, ⟨hB, hBlen⟩, rfl⟩
    exact ⟨A, B, hA, hB, hAlen, hBlen, rfl⟩
  · rintro ⟨A, B, hA, hB, hAlen, hBlen, rfl⟩
    exact ⟨A, ⟨hA, hAlen⟩, B, ⟨hB, hBlen⟩, rfl⟩

/-- Every enumerated entry is the code and edge count of a genuine bounded
rectangle. -/
lemma boundedRectangleCodeCounts_sound (n b c : Nat) {e : BitString × Nat}
    (he : e ∈ boundedRectangleCodeCounts n b c) :
    ∃ R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)),
      R.1.card ≤ b ∧ R.2.card ≤ c ∧
      e.1 = concreteIncidenceRectangleCode n R ∧
      e.2 = (Rel.interedges Incident R.1 R.2).card := by
  obtain ⟨A, B, hA, hB, hAlen, hBlen, rfl⟩ :=
    (mem_boundedRectangleCodeCounts_iff n b c e).mp he
  have hAmem := sublist_mem_codeList hA
  have hBmem := sublist_mem_codeList hB
  have hAnd : A.Nodup := hA.nodup (concreteFieldPairCodeList_nodup n)
  have hBnd : B.Nodup := hB.nodup (concreteFieldPairCodeList_nodup n)
  refine ⟨decodedCodeRectangle n A B, ?_, ?_, ?_, ?_⟩
  · rw [decodedCodeRectangle, decodedCodeSide_card n hAmem hAnd]
    exact hAlen
  · rw [decodedCodeRectangle, decodedCodeSide_card n hBmem hBnd]
    exact hBlen
  · exact (decodedCodeRectangle_code n hAmem hBmem).symm
  · exact codeRectangleEdgeCount_eq n hAmem hBmem

/-- Every bounded rectangle appears in the enumeration. -/
lemma boundedRectangleCodeCounts_complete (n b c : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)))
    (hb : R.1.card ≤ b) (hc : R.2.card ≤ c) :
    (concreteIncidenceRectangleCode n R, (Rel.interedges Incident R.1 R.2).card) ∈
      boundedRectangleCodeCounts n b c := by
  obtain ⟨A, hA, hAdec, hAlen⟩ := exists_sublist_of_finset n R.1
  obtain ⟨B, hB, hBdec, hBlen⟩ := exists_sublist_of_finset n R.2
  have hAmem := sublist_mem_codeList hA
  have hBmem := sublist_mem_codeList hB
  have hrect : decodedCodeRectangle n A B = R := by
    rw [decodedCodeRectangle, hAdec, hBdec]
  refine (mem_boundedRectangleCodeCounts_iff n b c _).mpr
    ⟨A, B, hA, hB, hAlen.trans_le hb, hBlen.trans_le hc, ?_⟩
  rw [Prod.ext_iff]
  constructor
  · rw [← decodedCodeRectangle_code n hAmem hBmem, hrect]
  · rw [codeRectangleEdgeCount_eq n hAmem hBmem, hAdec, hBdec]

lemma foldr_max_le {l : List Nat} {M : Nat} (h : ∀ v ∈ l, v ≤ M) :
    l.foldr max 0 ≤ M := by
  induction l with
  | nil => exact Nat.zero_le M
  | cons x t ih =>
      rw [List.foldr_cons, max_le_iff]
      exact ⟨h x (List.mem_cons_self ..), ih fun v hv => h v (List.mem_cons_of_mem _ hv)⟩

lemma le_foldr_max {l : List Nat} {v : Nat} (h : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons x t ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_max_left _ _
      · exact (ih h').trans (le_max_right _ _)

/-- The code-level capacity: the largest incident-edge count among enumerated
bounded rectangles. -/
def codeIncidenceCapacity (n b c : Nat) : Nat :=
  ((boundedRectangleCodeCounts n b c).map Prod.snd).foldr max 0

lemma exists_capacity_rectangle (n b c : Nat) :
    ∃ R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)),
      R.1.card ≤ b ∧ R.2.card ≤ c ∧
        (Rel.interedges Incident R.1 R.2).card = concreteIncidenceCapacity n b c := by
  have hmax : concreteIncidenceCapacity n b c ∈
      (boundedIncidenceRectangles n b c).image
        (fun R => (Rel.interedges Incident R.1 R.2).card) := by
    unfold concreteIncidenceCapacity
    apply Finset.max'_mem
  rw [Finset.mem_image] at hmax
  obtain ⟨R, hR, hEq⟩ := hmax
  rw [boundedIncidenceRectangles, Finset.mem_filter] at hR
  exact ⟨R, hR.2.1, hR.2.2, hEq⟩

lemma codeIncidenceCapacity_eq (n b c : Nat) :
    codeIncidenceCapacity n b c = concreteIncidenceCapacity n b c := by
  apply le_antisymm
  · apply foldr_max_le
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨e, he, rfl⟩ := hv
    obtain ⟨R, hb, hc, -, hcount⟩ := boundedRectangleCodeCounts_sound n b c he
    rw [hcount]
    exact interedges_card_le_concreteIncidenceCapacity n b c R.1 R.2 hb hc
  · obtain ⟨R, hb, hc, hcount⟩ := exists_capacity_rectangle n b c
    apply le_foldr_max
    rw [List.mem_map]
    refine ⟨(concreteIncidenceRectangleCode n R,
      (Rel.interedges Incident R.1 R.2).card), ?_, hcount⟩
    exact boundedRectangleCodeCounts_complete n b c R hb hc

/-- The code-level selection of a capacity-maximizing rectangle: the first
enumerated rectangle code whose incident-edge count is maximal. -/
def codeCapacityRectangleCode (n b c : Nat) : BitString :=
  (((boundedRectangleCodeCounts n b c).filter fun e =>
    decide (e.2 = codeIncidenceCapacity n b c)).map Prod.fst).headI

lemma codeCapacityRectangleCode_spec (n b c : Nat) :
    ∃ R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)),
      R.1.card ≤ b ∧ R.2.card ≤ c ∧
        (Rel.interedges Incident R.1 R.2).card = concreteIncidenceCapacity n b c ∧
        codeCapacityRectangleCode n b c = concreteIncidenceRectangleCode n R := by
  set L := ((boundedRectangleCodeCounts n b c).filter fun e =>
    decide (e.2 = codeIncidenceCapacity n b c)).map Prod.fst with hL
  have hne : L ≠ [] := by
    obtain ⟨R, hb, hc, hcount⟩ := exists_capacity_rectangle n b c
    refine List.ne_nil_of_mem (a := concreteIncidenceRectangleCode n R) ?_
    rw [hL, List.mem_map]
    refine ⟨(concreteIncidenceRectangleCode n R,
      (Rel.interedges Incident R.1 R.2).card), ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨boundedRectangleCodeCounts_complete n b c R hb hc,
      decide_eq_true (by rw [hcount, codeIncidenceCapacity_eq])⟩
  have hmem : L.headI ∈ L := by
    cases hcase : L with
    | nil => exact absurd hcase hne
    | cons x t => exact List.mem_cons_self ..
  rw [hL, List.mem_map] at hmem
  obtain ⟨e, he, hfst⟩ := hmem
  rw [List.mem_filter, decide_eq_true_eq] at he
  obtain ⟨R, hb, hc, hcode, hcount⟩ := boundedRectangleCodeCounts_sound n b c he.1
  refine ⟨R, hb, hc, ?_, ?_⟩
  · rw [← hcount, he.2, codeIncidenceCapacity_eq]
  · rw [codeCapacityRectangleCode, ← hL, ← hfst, hcode]

lemma concreteFieldPairCodeList_primrec : Primrec concreteFieldPairCodeList := by
  have hwidth : Primrec (fun q : (Nat × Nat) × Nat => q.1.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun q : (Nat × Nat) × Nat => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hy : Primrec (fun q : (Nat × Nat) × Nat => q.2) := Primrec.snd
  have hout : Primrec (fun q : (Nat × Nat) × Nat =>
      fixedWidthNatCode q.1.2 (q.1.1 + 1) ++ fixedWidthNatCode q.2 (q.1.1 + 1)) :=
    Primrec.list_append.comp
      (fixedWidthNatCode_primrec.comp (Primrec.pair hx hwidth))
      (fixedWidthNatCode_primrec.comp (Primrec.pair hy hwidth))
  have hmap : Primrec (fun q : Nat × Nat =>
      (List.range (concretePrime q.1)).map fun y =>
        fixedWidthNatCode q.2 (q.1 + 1) ++ fixedWidthNatCode y (q.1 + 1)) :=
    Primrec.list_map
      (Primrec.list_range.comp (boundedPrimeSearch_primrec.comp Primrec.fst))
      hout.to₂
  exact Primrec.list_flatMap
    (Primrec.list_range.comp boundedPrimeSearch_primrec) hmap.to₂

lemma codeRectangleEdgeCount_primrec :
    Primrec (fun q : Nat × List BitString × List BitString =>
      codeRectangleEdgeCount q.1 q.2.1 q.2.2) := by
  have hpairs : Primrec (fun q : Nat × List BitString × List BitString =>
      concreteIncidentEdgeCodePairs q.1) :=
    concreteIncidentEdgeCodePairs_primrec.comp Primrec.fst
  have hpred := (Primrec.and.comp
      (decide_mem_primrec.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst :
          Primrec (fun r : (Nat × List BitString × List BitString) ×
            (BitString × BitString) => r.1))))
        (Primrec.fst.comp Primrec.snd))
      (decide_mem_primrec.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.list_length.comp (list_filter_primrec hpairs hpred)).of_eq (fun q => by
    rw [codeRectangleEdgeCount]
    congr 1
    apply List.filter_congr
    intro e _
    congr 1 <;> exact decide_eq_decide.mpr Iff.rfl)

lemma boundedRectangleCodeCounts_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      boundedRectangleCodeCounts p.1 p.2.1 p.2.2) := by
  have hsubs : Primrec (fun p : Nat × Nat × Nat =>
      (concreteFieldPairCodeList p.1).sublists) :=
    primrec_sublists_gen (concreteFieldPairCodeList_primrec.comp Primrec.fst)
  have hfiltA : Primrec (fun p : Nat × Nat × Nat =>
      (concreteFieldPairCodeList p.1).sublists.filter fun A =>
        decide (A.length ≤ p.2.1)) :=
    list_filter_primrec hsubs
      ((PrimrecPred.decide (Primrec.nat_le.comp
        (Primrec.list_length.comp (Primrec.snd :
          Primrec (fun q : (Nat × Nat × Nat) × List BitString => q.2)))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).to₂)
  have hsubs' : Primrec (fun q : (Nat × Nat × Nat) × List BitString =>
      (concreteFieldPairCodeList q.1.1).sublists) :=
    primrec_sublists_gen
      (concreteFieldPairCodeList_primrec.comp (Primrec.fst.comp Primrec.fst))
  have hfiltB : Primrec (fun q : (Nat × Nat × Nat) × List BitString =>
      (concreteFieldPairCodeList q.1.1).sublists.filter fun B =>
        decide (B.length ≤ q.1.2.2)) :=
    list_filter_primrec hsubs'
      ((PrimrecPred.decide (Primrec.nat_le.comp
        (Primrec.list_length.comp (Primrec.snd :
          Primrec (fun r : ((Nat × Nat × Nat) × List BitString) × List BitString => r.2)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))).to₂)
  have hcanonA : Primrec (fun r : ((Nat × Nat × Nat) × List BitString) × List BitString =>
      listCode (canonicalFinsetList (r.1.2).toFinset)) :=
    listCode_primrec.comp
      (canonicalFinsetList_toFinset_primrec.comp (Primrec.snd.comp Primrec.fst))
  have hcanonB : Primrec (fun r : ((Nat × Nat × Nat) × List BitString) × List BitString =>
      listCode (canonicalFinsetList (r.2).toFinset)) :=
    listCode_primrec.comp (canonicalFinsetList_toFinset_primrec.comp Primrec.snd)
  have hcount : Primrec (fun r : ((Nat × Nat × Nat) × List BitString) × List BitString =>
      codeRectangleEdgeCount r.1.1.1 r.1.2 r.2) :=
    codeRectangleEdgeCount_primrec.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  have hentry : Primrec (fun r : ((Nat × Nat × Nat) × List BitString) × List BitString =>
      (pairCode (listCode (canonicalFinsetList (r.1.2).toFinset))
          (listCode (canonicalFinsetList (r.2).toFinset)),
        codeRectangleEdgeCount r.1.1.1 r.1.2 r.2)) :=
    Primrec.pair (pairCode_primrec.comp hcanonA hcanonB) hcount
  have hinner : Primrec (fun q : (Nat × Nat × Nat) × List BitString =>
      ((concreteFieldPairCodeList q.1.1).sublists.filter fun B =>
          decide (B.length ≤ q.1.2.2)).map fun B =>
        (pairCode (listCode (canonicalFinsetList (q.2).toFinset))
            (listCode (canonicalFinsetList B.toFinset)),
          codeRectangleEdgeCount q.1.1 q.2 B)) :=
    Primrec.list_map hfiltB hentry.to₂
  exact Primrec.list_flatMap hfiltA hinner.to₂

lemma codeIncidenceCapacity_primrec :
    Primrec (fun p : Nat × Nat × Nat => codeIncidenceCapacity p.1 p.2.1 p.2.2) := by
  have hcounts : Primrec (fun p : Nat × Nat × Nat =>
      (boundedRectangleCodeCounts p.1 p.2.1 p.2.2).map Prod.snd) :=
    Primrec.list_map boundedRectangleCodeCounts_primrec
      (Primrec.snd.comp (Primrec.snd :
        Primrec (fun q : (Nat × Nat × Nat) × (BitString × Nat) => q.2))).to₂
  have hstep : Primrec₂ (fun (_p : Nat × Nat × Nat) (bs : Nat × Nat) =>
      max bs.1 bs.2) :=
    (Primrec.nat_max.comp
      (Primrec.fst.comp (Primrec.snd :
        Primrec (fun q : (Nat × Nat × Nat) × (Nat × Nat) => q.2)))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr hcounts (Primrec.const 0) hstep).of_eq (fun p => rfl)

lemma codeCapacityRectangleCode_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      codeCapacityRectangleCode p.1 p.2.1 p.2.2) := by
  have hfilter : Primrec (fun p : Nat × Nat × Nat =>
      (boundedRectangleCodeCounts p.1 p.2.1 p.2.2).filter fun e =>
        decide (e.2 = codeIncidenceCapacity p.1 p.2.1 p.2.2)) :=
    list_filter_primrec boundedRectangleCodeCounts_primrec
      ((PrimrecPred.decide (Primrec.eq.comp
        (Primrec.snd.comp (Primrec.snd :
          Primrec (fun q : (Nat × Nat × Nat) × (BitString × Nat) => q.2)))
        (codeIncidenceCapacity_primrec.comp Primrec.fst))).to₂)
  have hmap : Primrec (fun p : Nat × Nat × Nat =>
      ((boundedRectangleCodeCounts p.1 p.2.1 p.2.2).filter fun e =>
        decide (e.2 = codeIncidenceCapacity p.1 p.2.1 p.2.2)).map Prod.fst) :=
    Primrec.list_map hfilter
      (Primrec.fst.comp (Primrec.snd :
        Primrec (fun q : (Nat × Nat × Nat) × (BitString × Nat) => q.2))).to₂
  exact (Primrec.option_getD.comp (Primrec.list_head?.comp hmap)
    (Primrec.const [])).of_eq (fun p => by
      rw [codeCapacityRectangleCode]
      cases h : ((boundedRectangleCodeCounts p.1 p.2.1 p.2.2).filter fun e =>
        decide (e.2 = codeIncidenceCapacity p.1 p.2.1 p.2.2)).map Prod.fst <;> rfl)

end Kolmogorov
