import KolmogorovMathlib.CommonInformation.IncidenceCapacityCode

/-!
# Code-level shear translates of an incidence rectangle

This file develops the bitstring-level counterpart of the shear-translate
search used in Exercise 312.  The affine shear maps are implemented directly on
fixed-width codes by modular arithmetic on the decoded coordinates, the list of
all shear translates of a coded rectangle is enumerated, and the exhaustive
subcover search is transported from the geometric side to the code side.
-/

namespace Kolmogorov

open AffineIncidence

/-! ### Transporting the exhaustive subcover search along encodings -/

private theorem find?_map_congr {β β' : Type} (l : List β) (F : β → β')
    (p : β → Bool) (p' : β' → Bool) (h : ∀ C, p' (F C) = p C) :
    (l.map F).find? p' = (l.find? p).map F := by
  have hfun : p' ∘ F = p := funext h
  rw [List.find?_map, hfun]

private theorem option_map_getD_nil {β β' : Type} (F : List β → List β')
    (hF : F [] = []) (o : Option (List β)) :
    (o.map F).getD [] = F (o.getD []) := by
  cases o with
  | none => exact hF.symm
  | some C => rfl

/-- The exhaustive subcover search commutes with injective encodings of the
target list, provided the code-level cover agrees with the encoded geometric
cover.  The index encoding `f` need not be injective. -/
theorem computableGreedyCover_map {α α' β β' : Type} [DecidableEq α] [DecidableEq α']
    [DecidableEq β] [DecidableEq β']
    (T : List α) (S : List β) (cover : β → List α) (m bound : ℕ)
    (e : α → α') (f : β → β') (cover' : β' → List α')
    (he : Function.Injective e)
    (hcover : ∀ g, cover' (f g) = (cover g).map e) :
    computableGreedyCover (T.map e) (S.map f) cover' m bound =
      (computableGreedyCover T S cover m bound).map f := by
  classical
  have hlen : ∀ (C : List β) (x : α),
      ((C.map f).filter fun b => decide (e x ∈ cover' b)).length
        = (C.filter fun b => decide (x ∈ cover b)).length := by
    intro C x
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro b _
    rw [Function.comp_apply, hcover b]
    exact decide_eq_decide.mpr (List.mem_map_of_injective he)
  have hpred : ∀ C : List β,
      (((T.map e).all fun x =>
          decide (0 < ((C.map f).filter fun b => decide (x ∈ cover' b)).length)) &&
        decide ((C.map f).length ≤ bound))
      = ((T.all fun x => decide (0 < (C.filter fun b => decide (x ∈ cover b)).length)) &&
        decide (C.length ≤ bound)) := by
    intro C
    rw [List.all_map, List.length_map]
    congr 1
    simp only [Function.comp_def, hlen C]
  rw [computableGreedyCover_eq, computableGreedyCover_eq, List.sublists_map,
    find?_map_congr _ _ _ _ hpred,
    option_map_getD_nil (List.map f) List.map_nil]

/-! ### Modular arithmetic on fixed-width field codes -/

/-- The fixed-width code of the residue of a natural number. -/
def codeFieldValue (n k : Nat) : BitString :=
  fixedWidthNatCode (k % concretePrime n) (n + 1)

lemma codeFieldValue_eq (n k : Nat) :
    codeFieldValue n k = concreteFieldCode n ((k : Nat) : ConcreteField n) := by
  rw [codeFieldValue, concreteFieldCode, ZMod.val_natCast]

lemma concreteFieldCode_take (n : Nat) (a b : ConcreteField n) :
    (concreteFieldCode n a ++ concreteFieldCode n b).take (n + 1) = concreteFieldCode n a := by
  rw [List.take_left' (concreteFieldCode_length n a)]

lemma concreteFieldCode_drop (n : Nat) (a b : ConcreteField n) :
    (concreteFieldCode n a ++ concreteFieldCode n b).drop (n + 1) = concreteFieldCode n b := by
  rw [List.drop_left' (concreteFieldCode_length n a)]

lemma decode_concreteFieldCode (n : Nat) (a : ConcreteField n) :
    decodeFixedWidthNatCode (concreteFieldCode n a) = a.val := by
  rw [concreteFieldCode, decodeFixedWidthNatCode_encode]

lemma natCast_concretePrime_sub_one (n : Nat) :
    ((concretePrime n - 1 : Nat) : ConcreteField n) = -1 := by
  have h1 : 1 ≤ concretePrime n := (concretePrime_prime n).one_lt.le
  rw [Nat.cast_sub h1, ZMod.natCast_self, Nat.cast_one, zero_sub]

/-! ### Code-level shear maps -/

/-- Code-level image of a point code under the affine shear `(A, s, B)`. -/
def codePointShear (n A s B : Nat) (w : BitString) : BitString :=
  codeFieldValue n (decodeFixedWidthNatCode (w.take (n + 1)) + A) ++
    codeFieldValue n (decodeFixedWidthNatCode (w.drop (n + 1)) +
      s * decodeFixedWidthNatCode (w.take (n + 1)) + B)

/-- Code-level image of a line code under the affine shear `(A, s, B)`. -/
def codeLineShear (n A s B : Nat) (w : BitString) : BitString :=
  codeFieldValue n (decodeFixedWidthNatCode (w.take (n + 1)) + s) ++
    codeFieldValue n (decodeFixedWidthNatCode (w.drop (n + 1)) + B +
      (concretePrime n - 1) * ((decodeFixedWidthNatCode (w.take (n + 1)) + s) * A))

lemma codePointShear_code (n A s B : Nat) (p : Point (ConcreteField n)) :
    codePointShear n A s B (concretePointCode n p) =
      concretePointCode n (pointShearEquiv ((A : Nat) : ConcreteField n)
        ((s : Nat) : ConcreteField n) ((B : Nat) : ConcreteField n) p) := by
  rw [codePointShear, concretePointCode, concreteFieldCode_take, concreteFieldCode_drop,
    decode_concreteFieldCode, decode_concreteFieldCode, codeFieldValue_eq, codeFieldValue_eq,
    concretePointCode]
  congr 1 <;>
    simp [pointShearEquiv, ZMod.natCast_val, ZMod.cast_id]

lemma codeLineShear_code (n A s B : Nat) (ell : Line (ConcreteField n)) :
    codeLineShear n A s B (concreteLineCode n ell) =
      concreteLineCode n (lineShearEquiv ((A : Nat) : ConcreteField n)
        ((s : Nat) : ConcreteField n) ((B : Nat) : ConcreteField n) ell) := by
  rw [codeLineShear, concreteLineCode, concreteFieldCode_take, concreteFieldCode_drop,
    decode_concreteFieldCode, decode_concreteFieldCode, codeFieldValue_eq, codeFieldValue_eq,
    concreteLineCode]
  congr 1
  · simp [lineShearEquiv, ZMod.natCast_val, ZMod.cast_id]
  · push_cast [natCast_concretePrime_sub_one]
    simp only [lineShearEquiv, Equiv.coe_fn_mk, ZMod.natCast_val, ZMod.cast_id]
    ring_nf


private lemma list_toFinset_map {β : Type} [DecidableEq β] (l : List BitString)
    (f : BitString → β) : (l.map f).toFinset = l.toFinset.image f := by
  ext x; simp

/-! ### Explicit enumerations of incident edges and shear parameters -/

/-- Explicit list of all concrete incident edges, parametrized by slope,
intercept, and point `x`-coordinate. -/
def concreteIncidentEdgeList (n : Nat) :
    List (Point (ConcreteField n) × Line (ConcreteField n)) :=
  let q := concretePrime n
  (List.range q).flatMap fun (m : Nat) =>
    (List.range q).flatMap fun (b : Nat) =>
      (List.range q).map fun (x : Nat) =>
        (((x : ConcreteField n),
            (m : ConcreteField n) * (x : ConcreteField n) + (b : ConcreteField n)),
          ((m : ConcreteField n), (b : ConcreteField n)))

@[simp]
lemma concreteIncidentEdgeList_length (n : Nat) :
    (concreteIncidentEdgeList n).length = concretePrime n ^ 3 := by
  simp [concreteIncidentEdgeList, pow_succ]
  ring

lemma mem_concreteIncidentEdgeList (n : Nat)
    (e : Point (ConcreteField n) × Line (ConcreteField n)) :
    e ∈ concreteIncidentEdgeList n ↔ Incident e.1 e.2 := by
  constructor
  · intro he
    simp only [concreteIncidentEdgeList, List.mem_flatMap, List.mem_map] at he
    obtain ⟨m, hm, b, hb, x, hx, rfl⟩ := he
    rfl
  · intro he
    obtain ⟨⟨x, y⟩, ⟨m, b⟩⟩ := e
    change y = m * x + b at he
    rw [concreteIncidentEdgeList]
    apply List.mem_flatMap.mpr
    refine ⟨m.val, List.mem_range.mpr (ZMod.val_lt m), ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨b.val, List.mem_range.mpr (ZMod.val_lt b), ?_⟩
    apply List.mem_map.mpr
    refine ⟨x.val, List.mem_range.mpr (ZMod.val_lt x), ?_⟩
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simpa using he.symm
    · apply Prod.ext <;> simp

lemma concreteIncidentEdgeList_toFinset (n : Nat) :
    (concreteIncidentEdgeList n).toFinset = incidentEdges (ConcreteField n) := by
  ext e
  rw [List.mem_toFinset, mem_concreteIncidentEdgeList, mem_incidentEdges_iff]

lemma concreteIncidentEdgeList_nodup (n : Nat) :
    (concreteIncidentEdgeList n).Nodup := by
  have hcard : (concreteIncidentEdgeList n).toFinset.card =
      (concreteIncidentEdgeList n).length := by
    rw [concreteIncidentEdgeList_toFinset, concreteIncidentEdgeList_length,
      incidentEdges_card, concreteField_card_eq]
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp hcard

/-- Explicit list of all three shear parameters in the concrete field. -/
def concreteShearParams (n : Nat) :
    List (ConcreteField n × ConcreteField n × ConcreteField n) :=
  let q := concretePrime n
  (List.range q).flatMap fun (A : Nat) =>
    (List.range q).flatMap fun (s : Nat) =>
      (List.range q).map fun (B : Nat) =>
        ((A : ConcreteField n), (s : ConcreteField n), (B : ConcreteField n))

@[simp]
lemma concreteShearParams_length (n : Nat) :
    (concreteShearParams n).length = concretePrime n ^ 3 := by
  simp [concreteShearParams, pow_succ]
  ring

lemma mem_concreteShearParams (n : Nat)
    (g : ConcreteField n × ConcreteField n × ConcreteField n) :
    g ∈ concreteShearParams n := by
  obtain ⟨A, s, B⟩ := g
  rw [concreteShearParams]
  apply List.mem_flatMap.mpr
  refine ⟨A.val, List.mem_range.mpr (ZMod.val_lt A), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨s.val, List.mem_range.mpr (ZMod.val_lt s), ?_⟩
  apply List.mem_map.mpr
  refine ⟨B.val, List.mem_range.mpr (ZMod.val_lt B), ?_⟩
  ext <;> simp

lemma concreteShearParams_toFinset (n : Nat) :
    (concreteShearParams n).toFinset =
      (Finset.univ : Finset (ConcreteField n × ConcreteField n × ConcreteField n)) := by
  ext g
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact mem_concreteShearParams n g

lemma concreteShearParams_nodup (n : Nat) :
    (concreteShearParams n).Nodup := by
  have hcard : (concreteShearParams n).toFinset.card =
      (concreteShearParams n).length := by
    rw [concreteShearParams_toFinset, Finset.card_univ,
      Fintype.card_prod, Fintype.card_prod, concreteShearParams_length,
      concreteField_card_eq]
    ring
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp hcard

/-! ### Code-level shear translates of a coded rectangle -/

/-- Code of the shear translate of the rectangle coded by `w`. -/
def codeShearRectangleCode (n A s B : Nat) (w : BitString) : BitString :=
  pairCode
    (listCode (canonicalFinsetList
      (((decodeListCode (decodeFirst w)).map (codePointShear n A s B)).toFinset)))
    (listCode (canonicalFinsetList
      (((decodeListCode (decodeSecond w)).map (codeLineShear n A s B)).toFinset)))

lemma codeShearRectangleCode_code (n A s B : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n))) :
    codeShearRectangleCode n A s B (concreteIncidenceRectangleCode n R) =
      concreteIncidenceRectangleCode n
        (shearRectangle (((A : Nat) : ConcreteField n), ((s : Nat) : ConcreteField n),
          ((B : Nat) : ConcreteField n)) R) := by
  rw [codeShearRectangleCode, concreteIncidenceRectangleCode, decodeFirst_pairCode,
    decodeSecond_pairCode, decodeListCode_listCode, decodeListCode_listCode,
    concreteIncidenceRectangleCode, shearRectangle]
  congr 3
  · rw [list_toFinset_map, canonicalFinsetList_toFinset, Finset.image_image,
      Finset.image_image]
    apply Finset.image_congr
    intro p _
    exact codePointShear_code n A s B p
  · rw [list_toFinset_map, canonicalFinsetList_toFinset, Finset.image_image,
      Finset.image_image]
    apply Finset.image_congr
    intro ell _
    exact codeLineShear_code n A s B ell

/-- Codes of all shear translates of the rectangle coded by `w`. -/
def codeShearRectangleCodes (n : Nat) (w : BitString) : List BitString :=
  (List.range (concretePrime n)).flatMap fun A =>
    (List.range (concretePrime n)).flatMap fun s =>
      (List.range (concretePrime n)).map fun B =>
        codeShearRectangleCode n A s B w

lemma codeShearRectangleCodes_eq (n : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n))) :
    codeShearRectangleCodes n (concreteIncidenceRectangleCode n R) =
      (concreteShearParams n).map fun g =>
        concreteIncidenceRectangleCode n (shearRectangle g R) := by
  rw [codeShearRectangleCodes, concreteShearParams, List.map_flatMap]
  refine List.flatMap_congr ?_
  intro A _
  rw [List.map_flatMap]
  refine List.flatMap_congr ?_
  intro s _
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro B _
  exact codeShearRectangleCode_code n A s B R


/-! ### The code-level incident edge list and cover -/

/-- Code pair of a point/line edge. -/
def concreteEdgeCodePair (n : Nat)
    (ed : Point (ConcreteField n) × Line (ConcreteField n)) : BitString × BitString :=
  (concretePointCode n ed.1, concreteLineCode n ed.2)

lemma concreteEdgeCodePair_injective (n : Nat) :
    Function.Injective (concreteEdgeCodePair n) := by
  intro e₁ e₂ h
  apply Prod.ext
  · exact concretePointCode_injective n (Prod.ext_iff.mp h).1
  · exact concreteLineCode_injective n (Prod.ext_iff.mp h).2

lemma concreteIncidentEdgeCodePairs_eq_map (n : Nat) :
    concreteIncidentEdgeCodePairs n =
      (concreteIncidentEdgeList n).map (concreteEdgeCodePair n) := by
  change _ = List.map _ (List.flatMap _ (List.range (concretePrime n)))
  rw [List.map_flatMap]
  refine List.flatMap_congr ?_
  intro m _
  rw [List.map_flatMap]
  refine List.flatMap_congr ?_
  intro b _
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro x _
  change (concretePointCode n _, concreteLineCode n _) = _
  congr 2
  rw [ZMod.natCast_mod]
  push_cast
  ring


/-- Code pairs of the incident edges lying in the rectangle coded by `w`. -/
def codeShearCoverList (n : Nat) (w : BitString) : List (BitString × BitString) :=
  (concreteIncidentEdgeCodePairs n).filter fun pr =>
    decide (pr.1 ∈ decodeListCode (decodeFirst w)) &&
      decide (pr.2 ∈ decodeListCode (decodeSecond w))

lemma codeShearCoverList_code (n : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n))) :
    codeShearCoverList n (concreteIncidenceRectangleCode n R) =
      ((concreteIncidentEdgeList n).filter fun ed =>
        decide (ed ∈ Rel.interedges Incident R.1 R.2)).map (concreteEdgeCodePair n) := by
  rw [codeShearCoverList, concreteIncidenceRectangleCode, decodeFirst_pairCode,
    decodeSecond_pairCode, decodeListCode_listCode, decodeListCode_listCode,
    concreteIncidentEdgeCodePairs_eq_map, List.filter_map]
  congr 1
  apply List.filter_congr
  intro ed hed
  have hinc : Incident ed.1 ed.2 := (mem_concreteIncidentEdgeList n ed).mp hed
  have h1 : concretePointCode n ed.1 ∈
      canonicalFinsetList (R.1.image (concretePointCode n)) ↔ ed.1 ∈ R.1 := by
    rw [mem_canonicalFinsetList, Finset.mem_image]
    exact ⟨fun h => by
      obtain ⟨p, hp, he⟩ := h
      exact concretePointCode_injective n he ▸ hp, fun h => ⟨ed.1, h, rfl⟩⟩
  have h2 : concreteLineCode n ed.2 ∈
      canonicalFinsetList (R.2.image (concreteLineCode n)) ↔ ed.2 ∈ R.2 := by
    rw [mem_canonicalFinsetList, Finset.mem_image]
    exact ⟨fun h => by
      obtain ⟨l, hl, he⟩ := h
      exact concreteLineCode_injective n he ▸ hl, fun h => ⟨ed.2, h, rfl⟩⟩
  rw [Function.comp_apply]
  change (decide (concretePointCode n ed.1 ∈ _) && decide (concreteLineCode n ed.2 ∈ _)) = _
  rw [← Bool.decide_and, decide_eq_decide, h1, h2, mem_interedges_iff_of_decidable]
  exact ⟨fun h => ⟨h.1, h.2, hinc⟩, fun h => ⟨h.1, h.2.1⟩⟩


/-! ### Primitive recursiveness of `Nat.log2` -/

/-- One halving step of the iteration computing `Nat.log2`. -/
def log2Step (p : Nat × Nat) : Nat × Nat :=
  if p.1 < 2 then p else (p.1 / 2, p.2 + 1)

/-- The halving iteration run for a fixed number of steps. -/
def log2Iter (k : Nat) (p : Nat × Nat) : Nat × Nat :=
  Nat.rec p (fun _ q => log2Step q) k

lemma log2Iter_succ (k : Nat) (p : Nat × Nat) :
    log2Iter (k + 1) p = log2Step (log2Iter k p) := rfl

lemma log2Iter_succ' (k : Nat) (p : Nat × Nat) :
    log2Iter (k + 1) p = log2Iter k (log2Step p) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [log2Iter_succ, ih, log2Iter_succ]

lemma lt_two_of_log2_eq_zero (n : Nat) (h : Nat.log2 n = 0) : n < 2 := by
  by_contra hc
  rw [Nat.log2_eq_log_two, Nat.log_of_one_lt_of_le one_lt_two (Nat.not_lt.mp hc)] at h
  omega

lemma log2_eq_succ (n : Nat) (h : 2 ≤ n) : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two, Nat.log_of_one_lt_of_le one_lt_two h]

lemma log2Iter_spec : ∀ (k n acc : Nat), Nat.log2 n ≤ k →
    (log2Iter k (n, acc)).1 < 2 ∧ (log2Iter k (n, acc)).2 = acc + Nat.log2 n := by
  intro k
  induction k with
  | zero =>
      intro n acc h
      have h0 : Nat.log2 n = 0 := Nat.le_zero.mp h
      exact ⟨lt_two_of_log2_eq_zero n h0, by simp [log2Iter, h0]⟩
  | succ k ih =>
      intro n acc h
      by_cases hn : n < 2
      · have h0 : Nat.log2 n = 0 := by
          rw [Nat.log2_eq_log_two, Nat.log_of_lt hn]
        have hstep : log2Step (n, acc) = (n, acc) := by
          rw [log2Step]; exact if_pos hn
        rw [log2Iter_succ', hstep]
        exact ih n acc (by omega)
      · have h2 : 2 ≤ n := Nat.not_lt.mp hn
        have hs := log2_eq_succ n h2
        have hstep : log2Step (n, acc) = (n / 2, acc + 1) := by
          rw [log2Step]; exact if_neg hn
        rw [log2Iter_succ', hstep]
        have hIH := ih (n / 2) (acc + 1) (by omega)
        exact ⟨hIH.1, by rw [hIH.2]; omega⟩

lemma log2Iter_eq_log2 (n : Nat) : (log2Iter n (n, 0)).2 = Nat.log2 n := by
  rw [(log2Iter_spec n n 0 (Nat.log2_le_self n)).2, Nat.zero_add]

lemma log2Step_primrec : Primrec log2Step := by
  refine Primrec.ite (Primrec.nat_lt.comp Primrec.fst (Primrec.const 2)) Primrec.id ?_
  exact Primrec.pair (Primrec.nat_div.comp Primrec.fst (Primrec.const 2))
    (Primrec.succ.comp Primrec.snd)

lemma nat_log2_primrec : Primrec Nat.log2 := by
  have hg : Primrec₂ (fun (_ : Nat) (q : Nat × (Nat × Nat)) => log2Step q.2) :=
    (log2Step_primrec.comp (Primrec.snd.comp Primrec.snd)).to₂
  have hf : Primrec (fun a : Nat => ((a, 0) : Nat × Nat)) :=
    Primrec.pair Primrec.id (Primrec.const 0)
  have hiter : Primrec (fun n : Nat => log2Iter n (n, 0)) :=
    ((Primrec.nat_rec hf hg).comp Primrec.id Primrec.id).of_eq (fun _ => rfl)
  exact (Primrec.snd.comp hiter).of_eq log2Iter_eq_log2


/-! ### Primitive recursiveness of the exhaustive subcover search -/

theorem computableGreedyCover_primrec {γ α β : Type} [Primcodable γ] [Primcodable α]
    [Primcodable β] [DecidableEq α] [DecidableEq β]
    {T : γ → List α} {S : γ → List β} {cover : γ → β → List α} {m bound : γ → Nat}
    (hT : Primrec T) (hS : Primrec S) (hcover : Primrec₂ cover) (hbound : Primrec bound) :
    Primrec (fun g => computableGreedyCover (T g) (S g) (cover g) (m g) (bound g)) := by
  have hcoverEl : Primrec (fun t : ((γ × List β) × α) × β => cover t.1.1.1 t.2) :=
    hcover.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have hx : Primrec (fun t : ((γ × List β) × α) × β => t.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hfilterPred : Primrec₂ (fun (r : (γ × List β) × α) (b : β) =>
      decide (r.2 ∈ cover r.1.1 b)) :=
    (decide_mem_primrec.comp hcoverEl hx).to₂
  have hfilter : Primrec (fun r : (γ × List β) × α =>
      r.1.2.filter fun b => decide (r.2 ∈ cover r.1.1 b)) :=
    list_filter_primrec (Primrec.snd.comp Primrec.fst) hfilterPred
  have hallPred : Primrec₂ (fun (q : γ × List β) (x : α) =>
      decide (0 < (q.2.filter fun b => decide (x ∈ cover q.1 b)).length)) :=
    (PrimrecPred.decide (Primrec.nat_lt.comp (Primrec.const 0)
      (Primrec.list_length.comp hfilter))).to₂
  have hall : Primrec (fun q : γ × List β =>
      (T q.1).all fun x => decide (0 < (q.2.filter fun b => decide (x ∈ cover q.1 b)).length)) :=
    list_all_primrec (hT.comp Primrec.fst) hallPred
  have hbnd : Primrec (fun q : γ × List β => decide (q.2.length ≤ bound q.1)) :=
    PrimrecPred.decide (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
      (hbound.comp Primrec.fst))
  have hpred : Primrec₂ (fun (g : γ) (C : List β) =>
      ((T g).all fun x => decide (0 < (C.filter fun b => decide (x ∈ cover g b)).length)) &&
        decide (C.length ≤ bound g)) :=
    (Primrec.and.comp hall hbnd).to₂
  have hfind : Primrec (fun g : γ => (S g).sublists.find? fun C =>
      ((T g).all fun x => decide (0 < (C.filter fun b => decide (x ∈ cover g b)).length)) &&
        decide (C.length ≤ bound g)) :=
    list_find?_primrec (primrec_sublists_gen hS) hpred
  exact (Primrec.option_getD.comp hfind (Primrec.const [])).of_eq
    (fun g => (computableGreedyCover_eq (T g) (S g) (cover g) (m g) (bound g)).symm)


/-! ### Primitive recursiveness of the code-level shear search data -/

lemma codeFieldValue_primrec {γ : Type} [Primcodable γ] {n k : γ → Nat}
    (hn : Primrec n) (hk : Primrec k) :
    Primrec (fun g => codeFieldValue (n g) (k g)) :=
  fixedWidthNatCode_primrec.comp (Primrec.pair
    (Primrec.nat_mod.comp hk (boundedPrimeSearch_primrec.comp hn))
    (Primrec.succ.comp hn))

lemma codePointShear_primrec {γ : Type} [Primcodable γ] {n A s B : γ → Nat}
    {w : γ → BitString} (hn : Primrec n) (hA : Primrec A) (hs : Primrec s)
    (hB : Primrec B) (hw : Primrec w) :
    Primrec (fun g => codePointShear (n g) (A g) (s g) (B g) (w g)) := by
  have hwidth : Primrec (fun g => n g + 1) := Primrec.succ.comp hn
  have hx : Primrec (fun g => decodeFixedWidthNatCode ((w g).take (n g + 1))) :=
    decodeFixedWidthNatCode_primrec.comp (Primrec.list_take.comp hwidth hw)
  have hy : Primrec (fun g => decodeFixedWidthNatCode ((w g).drop (n g + 1))) :=
    decodeFixedWidthNatCode_primrec.comp (Primrec.list_drop.comp hwidth hw)
  exact Primrec.list_append.comp
    (codeFieldValue_primrec hn (Primrec.nat_add.comp hx hA))
    (codeFieldValue_primrec hn (Primrec.nat_add.comp
      (Primrec.nat_add.comp hy (Primrec.nat_mul.comp hs hx)) hB))

lemma codeLineShear_primrec {γ : Type} [Primcodable γ] {n A s B : γ → Nat}
    {w : γ → BitString} (hn : Primrec n) (hA : Primrec A) (hs : Primrec s)
    (hB : Primrec B) (hw : Primrec w) :
    Primrec (fun g => codeLineShear (n g) (A g) (s g) (B g) (w g)) := by
  have hwidth : Primrec (fun g => n g + 1) := Primrec.succ.comp hn
  have hm : Primrec (fun g => decodeFixedWidthNatCode ((w g).take (n g + 1))) :=
    decodeFixedWidthNatCode_primrec.comp (Primrec.list_take.comp hwidth hw)
  have hd : Primrec (fun g => decodeFixedWidthNatCode ((w g).drop (n g + 1))) :=
    decodeFixedWidthNatCode_primrec.comp (Primrec.list_drop.comp hwidth hw)
  have hslope : Primrec (fun g => decodeFixedWidthNatCode ((w g).take (n g + 1)) + s g) :=
    Primrec.nat_add.comp hm hs
  have hqm : Primrec (fun g => concretePrime (n g) - 1) :=
    Primrec.nat_sub.comp (boundedPrimeSearch_primrec.comp hn) (Primrec.const 1)
  exact Primrec.list_append.comp
    (codeFieldValue_primrec hn hslope)
    (codeFieldValue_primrec hn (Primrec.nat_add.comp (Primrec.nat_add.comp hd hB)
      (Primrec.nat_mul.comp hqm (Primrec.nat_mul.comp hslope hA))))

lemma codeShearRectangleCode_primrec {γ : Type} [Primcodable γ] {n A s B : γ → Nat}
    {w : γ → BitString} (hn : Primrec n) (hA : Primrec A) (hs : Primrec s)
    (hB : Primrec B) (hw : Primrec w) :
    Primrec (fun g => codeShearRectangleCode (n g) (A g) (s g) (B g) (w g)) := by
  have hpt : Primrec₂ (fun (g : γ) (v : BitString) =>
      codePointShear (n g) (A g) (s g) (B g) v) :=
    (codePointShear_primrec (hn.comp Primrec.fst) (hA.comp Primrec.fst)
      (hs.comp Primrec.fst) (hB.comp Primrec.fst) Primrec.snd).to₂
  have hln : Primrec₂ (fun (g : γ) (v : BitString) =>
      codeLineShear (n g) (A g) (s g) (B g) v) :=
    (codeLineShear_primrec (hn.comp Primrec.fst) (hA.comp Primrec.fst)
      (hs.comp Primrec.fst) (hB.comp Primrec.fst) Primrec.snd).to₂
  exact pairCode_primrec.comp
    (listCode_primrec.comp (canonicalFinsetList_toFinset_primrec.comp
      (Primrec.list_map (decodeListCode_primrec.comp (decodeFirst_primrec'.comp hw)) hpt)))
    (listCode_primrec.comp (canonicalFinsetList_toFinset_primrec.comp
      (Primrec.list_map (decodeListCode_primrec.comp (decodeSecond_primrec'.comp hw)) hln)))

lemma codeShearRectangleCodes_primrec {γ : Type} [Primcodable γ] {n : γ → Nat}
    {w : γ → BitString} (hn : Primrec n) (hw : Primrec w) :
    Primrec (fun g => codeShearRectangleCodes (n g) (w g)) := by
  have hbase3 : Primrec (fun u : ((γ × Nat) × Nat) × Nat => u.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hentry : Primrec (fun u : ((γ × Nat) × Nat) × Nat =>
      codeShearRectangleCode (n u.1.1.1) u.1.1.2 u.1.2 u.2 (w u.1.1.1)) :=
    codeShearRectangleCode_primrec (hn.comp hbase3)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst) Primrec.snd (hw.comp hbase3)
  have hinner : Primrec (fun r : (γ × Nat) × Nat =>
      (List.range (concretePrime (n r.1.1))).map fun B =>
        codeShearRectangleCode (n r.1.1) r.1.2 r.2 B (w r.1.1)) :=
    Primrec.list_map
      (Primrec.list_range.comp (boundedPrimeSearch_primrec.comp
        (hn.comp (Primrec.fst.comp Primrec.fst))))
      hentry.to₂
  have hmid : Primrec (fun r : γ × Nat =>
      (List.range (concretePrime (n r.1))).flatMap fun s =>
        (List.range (concretePrime (n r.1))).map fun B =>
          codeShearRectangleCode (n r.1) r.2 s B (w r.1)) :=
    Primrec.list_flatMap
      (Primrec.list_range.comp (boundedPrimeSearch_primrec.comp (hn.comp Primrec.fst)))
      hinner.to₂
  exact Primrec.list_flatMap
    (Primrec.list_range.comp (boundedPrimeSearch_primrec.comp hn)) hmid.to₂

lemma codeShearCoverList_primrec {γ : Type} [Primcodable γ] {n : γ → Nat}
    {w : γ → BitString} (hn : Primrec n) (hw : Primrec w) :
    Primrec (fun g => codeShearCoverList (n g) (w g)) := by
  have hpairs : Primrec (fun g => concreteIncidentEdgeCodePairs (n g)) :=
    concreteIncidentEdgeCodePairs_primrec.comp hn
  have hfirst : Primrec (fun r : γ × (BitString × BitString) =>
      decodeListCode (decodeFirst (w r.1))) :=
    decodeListCode_primrec.comp (decodeFirst_primrec'.comp (hw.comp Primrec.fst))
  have hsecond : Primrec (fun r : γ × (BitString × BitString) =>
      decodeListCode (decodeSecond (w r.1))) :=
    decodeListCode_primrec.comp (decodeSecond_primrec'.comp (hw.comp Primrec.fst))
  have hpred := (Primrec.and.comp
      (decide_mem_primrec.comp hfirst (Primrec.fst.comp Primrec.snd))
      (decide_mem_primrec.comp hsecond (Primrec.snd.comp Primrec.snd))).to₂
  exact (list_filter_primrec hpairs hpred).of_eq (fun g => by
    unfold codeShearCoverList
    apply List.filter_congr
    intro pr _
    congr 1 <;> exact decide_eq_decide.mpr Iff.rfl)

/-! ### Singleton rectangles at the code level -/

lemma canonicalFinsetList_singleton (w : BitString) : canonicalFinsetList {w} = [w] :=
  Finset.sort_singleton _ _

lemma concreteIncidenceRectangleCode_singleton (n : Nat)
    (p : Point (ConcreteField n)) (ell : Line (ConcreteField n)) :
    concreteIncidenceRectangleCode n ({p}, {ell}) =
      pairCode (listCode [concretePointCode n p]) (listCode [concreteLineCode n ell]) := by
  rw [concreteIncidenceRectangleCode]
  simp only [Finset.image_singleton, canonicalFinsetList_singleton]


end Kolmogorov
