/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Definitions
import KolmogorovMathlib.CommonInformation.ConditionalIndependence.Part01
import KolmogorovMathlib.Complexity.Information.MutualInformation
import KolmogorovMathlib.Complexity.ConditionalComplexity.AverageBounds.Expectation
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileCardinality
import KolmogorovMathlib.Foundation.EnumerationComplexity

/-!
# Typization Size

This module proves bounds on the cardinality of typizations from conditional Kolmogorov complexity.
It formalizes the enumeration and lower-bound arguments in the proof of Lemma 1 of Muchnik and
Romashchenko, “Stability of properties of Kolmogorov complexity under relativization.”
-/

namespace Kolmogorov.Relativization

open Finset

variable {n m : ℕ}

/-- A full-block profile comparison bounds the
conditional complexity of every tuple in the typization. -/
private lemma lemma1_profile_bound (D : Map)
    (x x' : Fin n → BitString) (y : Fin m → BitString)
    (hx : x' ∈ typization D x y) :
    natCondK D (tupleCode x') (tupleCode y) ≤ natCondK D (tupleCode x) (tupleCode y) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hEq : x' = x := by
      funext i
      exact Fin.elim0 i
    rw [hEq]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let V : Finset (Fin (n + m)) := Finset.univ.map (Fin.castAddEmb m)
    let W : Finset (Fin (n + m)) := Finset.univ.map (Fin.natAddEmb n)
    have hV : V.Nonempty := by
      refine ⟨Fin.castAddEmb m ⟨0, hnpos⟩, ?_⟩
      exact Finset.mem_map.mpr ⟨⟨0, hnpos⟩, Finset.mem_univ _, rfl⟩
    have hdis : Disjoint V W := by
      rw [Finset.disjoint_left]
      intro a ha hna
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨j, hj, hEq⟩ := Finset.mem_map.mp hna
      have hEq' : Fin.castAdd m i = Fin.natAdd n j := by simpa using hEq.symm
      have hval := congrArg Fin.val hEq'
      rw [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
    have hVcode (a : Fin n → BitString) :
        subtupleCode (Fin.append a y) V = tupleCode a := by
      dsimp [V]
      unfold subtupleCode
      have hmono : StrictMonoOn (Fin.castAddEmb m : Fin n → Fin (n + m))
          (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
        intro i _ j _ hij
        simpa using Fin.strictMono_castAdd m hij
      rw [← hmono.map_finsetSort]
      simp [tupleCode, Fin.sort_univ, List.ofFn_eq_map, Function.comp_def]
    have hWcode (a : Fin n → BitString) :
        subtupleCode (Fin.append a y) W = tupleCode y := by
      dsimp [W]
      unfold subtupleCode
      have hmono : StrictMonoOn (Fin.natAddEmb n : Fin m → Fin (n + m))
          (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
        intro i _ j _ hij
        simpa using Fin.strictMono_natAdd n hij
      rw [← hmono.map_finsetSort]
      simp [tupleCode, Fin.sort_univ, List.ofFn_eq_map, Function.comp_def]
    change ExtProfileLe D (Fin.append x' y) (Fin.append x y) at hx
    have hp := hx V W hV hdis
    unfold subCondK at hp
    rw [hVcode x', hWcode x, hVcode x, hWcode x'] at hp
    exact hp

/-- A family of tuples whose codes have conditional
complexity at most `k` is finite, with at most `2^(k+1)` members. -/
private lemma lemma1_count (D : Map) (hD : isOptimalConditional D)
    (y : BitString) (k : ℕ) (A : Set (Fin n → BitString))
    (hA : ∀ a, a ∈ A → natCondK D (tupleCode a) y ≤ k) :
    A.Finite ∧ A.ncard ≤ 2 ^ (k + 1) := by
  classical
  let C := Kolmogorov.compressibleWords D y k
  have himage : tupleCode '' A ⊆ (C : Set BitString) := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hz
    have hnat := hA a ha
    have hne : condK D (tupleCode a) y ≠ ⊤ := by
      obtain ⟨c, hc⟩ := condK_le_plainK D hD
      obtain ⟨d, hd⟩ := plainK_le_length D hD
      apply ne_top_of_le_natCast_add
      calc
        condK D (tupleCode a) y ≤ plainK D (tupleCode a) + c := hc _ _
        _ ≤ (programLength (tupleCode a) : ENat) + d + c := by
          gcongr
          exact hd _
    have hcond : condK D (tupleCode a) y ≤ (k : ENat) := by
      rw [← ENat.natCast_toNat hne]
      exact_mod_cast hnat
    change tupleCode a ∈ Kolmogorov.compressibleWords D y k
    rw [Kolmogorov.compressibleWords, Finset.mem_filter]
    refine ⟨?_, hcond⟩
    obtain ⟨p, hpLen, hpProd⟩ := (Kolmogorov.condK_le_iff D (tupleCode a) y k).mp hcond
    rw [Kolmogorov.generatedWords, List.mem_toFinset, List.mem_filterMap]
    exact ⟨p, Kolmogorov.mem_programsLe k p hpLen,
      Kolmogorov.progToOut_eq_some.mpr hpProd⟩
  have himageFin : (tupleCode '' A).Finite :=
    (C.finite_toSet).subset himage
  have htupleInj : Function.Injective (tupleCode : (Fin n → BitString) → BitString) := by
    intro a b hab
    apply List.ofFn_injective
    exact Kolmogorov.listCode_injective hab
  have hAfin : A.Finite := himageFin.of_finite_image (fun a _ b _ hab => htupleInj hab)
  have himageCard : (tupleCode '' A).ncard = A.ncard :=
    Set.ncard_image_of_injective A htupleInj
  have hleC : (tupleCode '' A).ncard ≤ C.card := by
    calc
      (tupleCode '' A).ncard ≤ (C : Set BitString).ncard :=
        Set.ncard_le_ncard himage C.finite_toSet
      _ = C.card := Set.ncard_coe_finset C
  constructor
  · exact hAfin
  · calc
      A.ncard = (tupleCode '' A).ncard := himageCard.symm
      _ ≤ C.card := hleC
      _ ≤ 2 ^ (k + 1) := Nat.le_of_lt (Kolmogorov.card_compressibleWordsLt D y k)

/-- Encodes pairs of coordinate sets used to test an extended complexity profile. -/
private noncomputable def lemma1_profile_advice_coordinates
    (N : ℕ) : List (Finset (Fin N) × Finset (Fin N)) := by
  classical
  let S := (Finset.univ : Finset (Finset (Fin N))).toList
  exact S.flatMap fun V => S.map fun W => (V, W)

private lemma lemma1_profile_advice_coordinates_mem
    (N : ℕ) (V W : Finset (Fin N)) :
    (V, W) ∈
      lemma1_profile_advice_coordinates
        N := by
  classical
  simp [lemma1_profile_advice_coordinates]

private def lemma1_profile_advice_project
    (N : ℕ) (V : Finset (Fin N)) (w : BitString) : BitString :=
  listCode (((V.sort (· ≤ ·)).map Fin.val).map
    fun i => (decodeListCode w).getD i [])

private theorem lemma1_profile_advice_project_computable
    (N : ℕ) (V : Finset (Fin N)) :
    Computable
      (lemma1_profile_advice_project
        N V) := by
  classical
  let positions := (V.sort (· ≤ ·)).map Fin.val
  have hMap : Primrec (fun w : BitString =>
      positions.map fun i => (decodeListCode w).getD i []) := by
    induction positions with
    | nil => exact Primrec.const []
    | cons head tail ih =>
      have h_getD : Primrec (fun w : BitString => (decodeListCode w).getD head []) := by
        exact (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec
          (Primrec.const head)
      change Primrec (fun w =>
        (decodeListCode w).getD head [] ::
          tail.map (fun i => (decodeListCode w).getD i []))
      exact Primrec₂.comp Primrec.list_cons h_getD ih
  exact listCode_computable.comp hMap.to_comp

private theorem lemma1_profile_advice_project_correct
    (N : ℕ) (V : Finset (Fin N)) (z : Fin N → BitString) :
    lemma1_profile_advice_project
        N V (tupleCode z) = subtupleCode z V := by
  simp only [lemma1_profile_advice_project,
    tupleCode, decodeListCode_listCode]
  unfold subtupleCode
  apply congrArg listCode
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  change (List.ofFn z).getD i.val [] = z i
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
    List.getElem_ofFn]

private lemma lemma1_profile_advice_coordinate_bound
    (D : Map) (hD : isOptimalConditional D) (N : ℕ) :
    ∃ c : ℕ, ∀ (z : Fin N → BitString) (V W : Finset (Fin N)),
      subCondK D z V W ≤ natK D (tupleCode z) + c := by
  classical
  have hNatOfCond (a b x : BitString) (c : ℕ)
      (h : condK D a b ≤ plainK D x + (c : ℕ∞)) :
      natCondK D a b ≤ natK D x + c := by
    have hne := condK_ne_top_of_optimal D hD a b
    have hne' := plainK_ne_top D hD x
    change (condK D a b).toNat ≤ (plainK D x).toNat + c
    have h' : ((condK D a b).toNat : ℕ∞) ≤
        (((plainK D x).toNat + c : ℕ) : ℕ∞) := by
      calc
        ((condK D a b).toNat : ℕ∞) = condK D a b := ENat.natCast_toNat hne
        _ ≤ plainK D x + (c : ℕ∞) := h
        _ = ((plainK D x).toNat : ℕ∞) + (c : ℕ∞) := by rw [ENat.natCast_toNat hne']
        _ = (((plainK D x).toNat + c : ℕ) : ℕ∞) := by push_cast; rfl
    exact_mod_cast h'
  have hProjectionBound (V : Finset (Fin N)) :
      ∃ cV : ℕ, ∀ (z : Fin N → BitString),
        natK D (lemma1_profile_advice_project
          N V (tupleCode z)) ≤ natK D (tupleCode z) + cV := by
    obtain ⟨cV, hcV⟩ := plainK_map_le D hD
      (lemma1_profile_advice_project
        N V)
      (lemma1_profile_advice_project_computable
        N V)
    refine ⟨cV, fun z => ?_⟩
    have h := hcV (tupleCode z)
    rw [lemma1_profile_advice_project_correct]
      at h
    rw [lemma1_profile_advice_project_correct]
    have hne := plainK_ne_top D hD (subtupleCode z V)
    have hne' := plainK_ne_top D hD (tupleCode z)
    change (plainK D (subtupleCode z V)).toNat ≤ (plainK D (tupleCode z)).toNat + cV
    have h' : ((plainK D (subtupleCode z V)).toNat : ℕ∞) ≤
        (((plainK D (tupleCode z)).toNat + cV : ℕ) : ℕ∞) := by
      calc
        ((plainK D (subtupleCode z V)).toNat : ℕ∞) = plainK D (subtupleCode z V) :=
          ENat.natCast_toNat hne
        _ ≤ plainK D (tupleCode z) + (cV : ℕ∞) := h
        _ = ((plainK D (tupleCode z)).toNat : ℕ∞) + (cV : ℕ∞) := by
          rw [ENat.natCast_toNat hne']
        _ = (((plainK D (tupleCode z)).toNat + cV : ℕ) : ℕ∞) := by
          push_cast; rfl
    exact_mod_cast h'
  let overhead : Finset (Fin N) → ℕ := fun V => Classical.choose (hProjectionBound V)
  let cProjection := Finset.univ.sup overhead
  obtain ⟨cCondition, hCondition⟩ := condK_le_plainK D hD
  refine ⟨cProjection + cCondition, ?_⟩
  intro z V W
  have hProj := Classical.choose_spec (hProjectionBound V) z
  have hOverhead : overhead V ≤ cProjection := Finset.le_sup (Finset.mem_univ V)
  have hConditionNat := hNatOfCond (subtupleCode z V) (subtupleCode z W)
    (subtupleCode z V) cCondition (hCondition _ _)
  have hProjNat : natK D (subtupleCode z V) ≤ natK D (tupleCode z) + overhead V := by
    rw [lemma1_profile_advice_project_correct]
      at hProj
    exact hProj
  change natCondK D (subtupleCode z V) (subtupleCode z W) ≤
    natK D (tupleCode z) + (cProjection + cCondition)
  omega

private lemma lemma1_profile_advice_encoded_list_length
    (a c : ℕ) (xs : List ℕ)
    (hxs : ∀ v, v ∈ xs → v ≤ a + c) :
    (listCode (xs.map Nat.bits)).length ≤
      xs.length * (2 * ((Nat.bits a).length + (Nat.bits c).length + 1) + 1) := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
    have hv : v ≤ a + c := hxs v (by simp)
    have htail : ∀ w, w ∈ xs → w ≤ a + c := by
      intro w hw
      exact hxs w (by simp [hw])
    have hbits : (Nat.bits v).length ≤
        (Nat.bits a).length + (Nat.bits c).length + 1 := by
      exact (length_natBits_mono hv).trans (length_natBits_add_le a c)
    simp only [List.map_cons]
    rw [length_listCode_cons]
    have hrec := ih htail
    simp only [List.length_cons]
    nlinarith

private noncomputable def lemma1_profile_advice_values
    (D : Map) (N : ℕ) (z : Fin N → BitString) : List ℕ :=
  (lemma1_profile_advice_coordinates
    N).map fun q => subCondK D z q.1 q.2

private noncomputable def lemma1_profile_advice_code
    (D : Map) (N : ℕ) (z : Fin N → BitString) : BitString :=
  listCode ((lemma1_profile_advice_values
    D N z).map Nat.bits)

private noncomputable def lemma1_profile_advice_read
    (N : ℕ) (p : BitString) (V W : Finset (Fin N)) : ℕ :=
  decodeBits ((decodeListCode p).getD
    ((lemma1_profile_advice_coordinates
      N).idxOf (V, W)) [])

private theorem lemma1_profile_advice_read_computable
    (N : ℕ) :
    ∀ V W : Finset (Fin N),
      Computable (fun p : BitString =>
        lemma1_profile_advice_read
          N p V W) := by
  classical
  intro V W
  let coords :=
    lemma1_profile_advice_coordinates
      N
  let k := coords.idxOf (V, W)
  have hGet : Primrec (fun p : BitString => (decodeListCode p).getD k []) := by
    exact (Primrec.list_getD ([] : BitString)).comp
      decodeListCode_primrec (Primrec.const k)
  have hRead : Primrec (fun p : BitString => decodeBits ((decodeListCode p).getD k [])) :=
    primrec_decodeBits.comp hGet
  exact hRead.to_comp.of_eq (fun p => rfl)

private theorem lemma1_profile_advice
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ P : BitString → Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ,
      (∀ V W, Computable (fun p : BitString => P p V W)) ∧
      ∃ c : ℕ, ∀ (x : Fin n → BitString) (y : Fin m → BitString),
        ∃ p : BitString,
          p.length ≤ logSlack c (natK D (tupleCode (Fin.append x y))) ∧
          ∀ V W, V.Nonempty → Disjoint V W →
            P p V W = subCondK D (Fin.append x y) V W := by
  classical
  let N := n + m
  obtain ⟨cCoordinate, hCoordinate⟩ :=
    lemma1_profile_advice_coordinate_bound
      D hD N
  let values :=
      lemma1_profile_advice_values
    D N
  let coords :=
    lemma1_profile_advice_coordinates
      N
  let P := lemma1_profile_advice_read
    N
  refine ⟨P, ?_, ?_⟩
  · intro V W
    exact lemma1_profile_advice_read_computable
      N V W
  · let L := coords.length
    let b := (Nat.bits cCoordinate).length
    let c := 2 * L + L * (2 * b + 3)
    refine ⟨c, ?_⟩
    intro x y
    let z : Fin N → BitString := Fin.append x y
    let p := lemma1_profile_advice_code
      D N z
    have hvalues : ∀ v, v ∈ values z →
        v ≤ natK D (tupleCode z) + cCoordinate := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      exact hCoordinate z q.1 q.2
    have hcodeLen :=
      lemma1_profile_advice_encoded_list_length
        (natK D (tupleCode z)) cCoordinate (values z) hvalues
    have hcodeLen' : p.length ≤
        L * (2 * ((Nat.bits (natK D (tupleCode z))).length + b + 1) + 1) := by
      simpa [p, lemma1_profile_advice_code,
        values, lemma1_profile_advice_values,
        coords, lemma1_profile_advice_coordinates,
        List.length_map, b, L, Nat.add_assoc] using hcodeLen
    refine ⟨p, ?_, ?_⟩
    · have hcoef : 2 * L ≤ c := by dsimp [c]; omega
      have hconst : L * (2 * b + 3) ≤ c := by dsimp [c]; omega
      unfold logSlack
      calc
        p.length ≤ L * (2 * ((Nat.bits (natK D (tupleCode z))).length + b + 1) + 1) := hcodeLen'
        _ = (2 * L) * (Nat.bits (natK D (tupleCode z))).length + L * (2 * b + 3) := by ring
        _ ≤ c * (Nat.bits (natK D (tupleCode z))).length + c := by
          exact Nat.add_le_add
            (Nat.mul_le_mul_right _ hcoef) hconst
    · intro V W hV hdis
      have hmem :=
        lemma1_profile_advice_coordinates_mem
          N V W
      have hidx : (coords.idxOf (V, W)) < coords.length :=
        List.idxOf_lt_length_iff.mpr hmem
      have hidxValues : (coords.idxOf (V, W)) < (values z).length := by
        change coords.idxOf (V, W) <
          (coords.map fun q => subCondK D z q.1 q.2).length
        simpa using hidx
      have hidxMap : (coords.idxOf (V, W)) <
          (coords.map fun q => subCondK D z q.1 q.2).length := by
        simpa using hidx
      have hidxMapBits : (coords.idxOf (V, W)) <
          ((coords.map fun q => subCondK D z q.1 q.2).map Nat.bits).length := by
        simpa using hidxMap
      have hget : (values z).getD (coords.idxOf (V, W)) 0 =
          subCondK D z V W := by
        change (coords.map (fun q => subCondK D z q.1 q.2)).getD
          (coords.idxOf (V, W)) 0 = subCondK D z V W
        rw [List.getD_eq_getElem _ _ hidxMap]
        rw [List.getElem_map, List.getElem_idxOf hidx]
      have hbitsGet : ((values z).map Nat.bits).getD (coords.idxOf (V, W)) [] =
          Nat.bits (subCondK D z V W) := by
        change ((coords.map (fun q => subCondK D z q.1 q.2)).map Nat.bits).getD
          (coords.idxOf (V, W)) [] = Nat.bits (subCondK D z V W)
        rw [List.getD_eq_getElem _ _ hidxMapBits]
        rw [List.getElem_map, List.getElem_map, List.getElem_idxOf hidx]
      change lemma1_profile_advice_read
        N p V W = subCondK D z V W
      dsimp [lemma1_profile_advice_read,
        p, lemma1_profile_advice_code]
      rw [decodeListCode_listCode, hbitsGet, decodeBits_natBits]

private def lemma1_bounded_profile_test_run
    (c : Nat.Partrec.Code) (s : ℕ) (p y : BitString) : Option BitString :=
  (Nat.Partrec.Code.evaln s c (Encodable.encode (p, y))).bind
    (fun r => Encodable.decode r)

private noncomputable def lemma1_bounded_profile_test_pairs
    (N : ℕ) : List (Finset (Fin N) × Finset (Fin N)) := by
  classical
  exact (Finset.univ : Finset (Finset (Fin N))).toList.flatMap fun V =>
    ((Finset.univ : Finset (Finset (Fin N))).toList.map fun W => (V, W))

private noncomputable def lemma1_bounded_profile_test_check
    (n m : ℕ) (c : Nat.Partrec.Code)
    (P : BitString → Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ)
    (p w : BitString) (i : ℕ) : Bool := by
  classical
  let a : Fin n → BitString :=
    (@Encodable.decode (Fin n → BitString)
      (Primcodable.toEncodable (α := Fin n → BitString)) i.unpair.1).getD fun _ => []
  let y : Fin m → BitString := fun j => (decodeListCode w).getD j.val []
  let z : Fin (n + m) → BitString := Fin.append a y
  exact (lemma1_bounded_profile_test_pairs
    (n + m)).all fun q =>
      if h : q.1.Nonempty ∧ Disjoint q.1 q.2 then
        (Kolmogorov.boundedPrograms (P p q.1 q.2)).any fun prog =>
          decide
            (lemma1_bounded_profile_test_run
              c i.unpair.2 prog (subtupleCode z q.2) =
                some (subtupleCode z q.1))
      else true

--
-- The three following lemmas isolate the executable, soundness, and completeness steps of the
-- bounded-simulation test.
--

/-- The finite bounded-simulation checker is computable from the profile coordinates. -/
private theorem lemma1_computable
    (n m : ℕ) (c : Nat.Partrec.Code)
    (P : BitString → Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ)
    (hP : ∀ V W, Computable (fun p : BitString => P p V W)) :
    Computable₂
      (fun (q : BitString × BitString) (i : ℕ) =>
        lemma1_bounded_profile_test_check
          n m c P q.1 q.2 i) := by
  classical
  let input := (BitString × BitString) × ℕ
  let decodeTuple : ℕ → Fin n → BitString := fun i =>
    (@Encodable.decode (Fin n → BitString)
      (Primcodable.toEncodable (α := Fin n → BitString)) i).getD fun _ => []
  have hDecodeTuple : Primrec decodeTuple := by
    dsimp [decodeTuple]
    exact Primrec.option_getD.comp Primrec.decode
      (Primrec.const (fun _ : Fin n => ([] : BitString)))
  have hDecodeArg : Primrec (fun r : input => decodeTuple r.2.unpair.1) :=
    hDecodeTuple.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have hY : Primrec (fun w : BitString =>
      fun j : Fin m => (decodeListCode w).getD j.val []) := by
    apply (Primrec.fin_curry).2
    exact (Primrec.list_getD ([] : BitString)).comp
      (decodeListCode_primrec.comp Primrec.fst)
      (Primrec.fin_val.comp Primrec.snd)
  have hYArg : Primrec (fun r : input =>
      fun j : Fin m => (decodeListCode r.1.2).getD j.val []) :=
    hY.comp (Primrec.snd.comp Primrec.fst)
  have hAppend : Primrec
      (fun ab : (Fin n → BitString) × (Fin m → BitString) => Fin.append ab.1 ab.2) := by
    apply (Primrec.fin_curry).2
    have hSwitch : Primrec₂
        (fun i : Fin (n + m) => fun ab : (Fin n → BitString) × (Fin m → BitString) =>
          Fin.append ab.1 ab.2 i) := by
      apply (Primrec.fin_curry₁).2
      intro i
      induction i using Fin.addCases with
      | left j =>
          simpa using (Primrec.fin_app.comp Primrec.fst (Primrec.const j))
      | right j =>
          simpa using (Primrec.fin_app.comp Primrec.snd (Primrec.const j))
    exact hSwitch.comp Primrec.snd Primrec.fst
  have hTuple : Primrec (fun r : input =>
      Fin.append (decodeTuple r.2.unpair.1)
        (fun j : Fin m => (decodeListCode r.1.2).getD j.val [])) :=
    hAppend.comp (Primrec.pair hDecodeArg hYArg)
  have hSub (V : Finset (Fin (n + m))) :
      Primrec (fun r : input =>
        subtupleCode
          (Fin.append (decodeTuple r.2.unpair.1)
            (fun j : Fin m => (decodeListCode r.1.2).getD j.val [])) V) := by
    let positions := V.sort (· ≤ ·)
    have hMap : Primrec
        (fun z : Fin (n + m) → BitString => positions.map z) := by
      induction positions with
      | nil => exact Primrec.const []
      | cons i is ih =>
          exact Primrec.list_cons.comp
            (Primrec.fin_app.comp Primrec.id (Primrec.const i)) ih
    have hCode : Primrec (fun z : Fin (n + m) → BitString => subtupleCode z V) := by
      unfold subtupleCode
      exact Kolmogorov.listCode_primrec.comp hMap
    exact hCode.comp hTuple
  have hRun : Primrec (fun r : ℕ × (BitString × BitString) =>
      lemma1_bounded_profile_test_run
        c r.1 r.2.1 r.2.2) := by
    unfold lemma1_bounded_profile_test_run
    have hArg : Primrec (fun r : ℕ × (BitString × BitString) =>
        ((r.1, c), Encodable.encode r.2)) :=
      Primrec.pair
        (Primrec.pair Primrec.fst (Primrec.const c))
        (Primrec.encode.comp Primrec.snd)
    have hEval := Nat.Partrec.Code.primrec_evaln.comp hArg
    have hDecode : Primrec₂ (fun (_ : ℕ × (BitString × BitString)) (r : ℕ) =>
        (Encodable.decode r : Option BitString)) :=
      (Primrec.decode.comp Primrec.snd).to₂
    exact Primrec.option_bind hEval hDecode
  have hBoundedPrograms : Primrec Kolmogorov.boundedPrograms := by
    unfold Kolmogorov.boundedPrograms
    refine Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.succ.comp Primrec.id)) ?_
    have hExact : Primrec (fun q : ℕ × ℕ => Kolmogorov.exactLengthPrograms q.2) :=
      Kolmogorov.primrec_exactLengthPrograms.comp Primrec.snd
    exact hExact.to₂
  let pairs :=
    lemma1_bounded_profile_test_pairs
      (n + m)
  let pairTest := fun (V W : Finset (Fin (n + m))) (r : input) =>
    if h : V.Nonempty ∧ Disjoint V W then
      (Kolmogorov.boundedPrograms (P r.1.1 V W)).any fun prog =>
        decide
          (lemma1_bounded_profile_test_run
            c r.2.unpair.2 prog
            (subtupleCode
              (Fin.append (decodeTuple r.2.unpair.1)
                (fun j : Fin m => (decodeListCode r.1.2).getD j.val [])) W) =
              some (subtupleCode
                (Fin.append (decodeTuple r.2.unpair.1)
                  (fun j : Fin m => (decodeListCode r.1.2).getD j.val [])) V))
    else true
  have hCoord (V W : Finset (Fin (n + m))) :
      Computable (fun r : input => pairTest V W r) := by
    have hBound : Computable (fun r : input => P r.1.1 V W) :=
      (hP V W).comp (Computable.fst.comp Computable.fst)
    have hPrograms : Computable (fun r : input =>
        Kolmogorov.boundedPrograms (P r.1.1 V W)) :=
      hBoundedPrograms.to_comp.comp hBound
    have hPred : Primrec₂ (fun (r : input) (prog : BitString) =>
        decide
          (lemma1_bounded_profile_test_run
            c r.2.unpair.2 prog
            (subtupleCode
              (Fin.append (decodeTuple r.2.unpair.1)
                (fun j : Fin m => (decodeListCode r.1.2).getD j.val [])) W) =
              some (subtupleCode
                (Fin.append (decodeTuple r.2.unpair.1)
                  (fun j : Fin m => (decodeListCode r.1.2).getD j.val [])) V))) := by
      have hRunArg : Primrec (fun r : input × BitString =>
          (r.1.2.unpair.2, (r.2,
            subtupleCode
              (Fin.append (decodeTuple r.1.2.unpair.1)
                (fun j : Fin m => (decodeListCode r.1.1.2).getD j.val [])) W))) := by
        exact Primrec.pair
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair Primrec.snd ((hSub W).comp Primrec.fst))
      have hRunVal := hRun.comp hRunArg
      have hTarget : Primrec (fun r : input × BitString =>
          some
            (subtupleCode
              (Fin.append (decodeTuple r.1.2.unpair.1)
                (fun j : Fin m => (decodeListCode r.1.1.2).getD j.val [])) V)) :=
        Primrec.option_some.comp ((hSub V).comp Primrec.fst)
      exact (Primrec.eq.decide.comp hRunVal hTarget).to₂
    have hPredAny : Primrec₂ (fun (r : input × List BitString) (prog : BitString) =>
        decide
          (lemma1_bounded_profile_test_run
            c r.1.2.unpair.2 prog
            (subtupleCode
              (Fin.append (decodeTuple r.1.2.unpair.1)
                (fun j : Fin m => (decodeListCode r.1.1.2).getD j.val [])) W) =
              some (subtupleCode
                (Fin.append (decodeTuple r.1.2.unpair.1)
                  (fun j : Fin m => (decodeListCode r.1.1.2).getD j.val [])) V))) := by
      exact hPred.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
    have hAny : Primrec (fun r : input × List BitString =>
        r.2.any (fun prog =>
          decide
            (lemma1_bounded_profile_test_run
              c r.1.2.unpair.2 prog
              (subtupleCode
                (Fin.append (decodeTuple r.1.2.unpair.1)
                  (fun j : Fin m => (decodeListCode r.1.1.2).getD j.val [])) W) =
                some (subtupleCode
                  (Fin.append (decodeTuple r.1.2.unpair.1)
                    (fun j : Fin m => (decodeListCode r.1.1.2).getD j.val [])) V)))) :=
      Kolmogorov.list_any_primrec Primrec.snd hPredAny
    have hAnyComp : Computable (fun r : input =>
        (Kolmogorov.boundedPrograms (P r.1.1 V W)).any fun prog =>
          decide
            (lemma1_bounded_profile_test_run
              c r.2.unpair.2 prog
              (subtupleCode
                (Fin.append (decodeTuple r.2.unpair.1)
                  (fun j : Fin m => (decodeListCode r.1.2).getD j.val [])) W) =
              some (subtupleCode
                (Fin.append (decodeTuple r.2.unpair.1)
                  (fun j : Fin m => (decodeListCode r.1.2).getD j.val [])) V))) := by
      exact hAny.to_comp.comp (Computable.pair Computable.id hPrograms)
    by_cases hVW : V.Nonempty ∧ Disjoint V W
    · simpa [pairTest, hVW] using hAnyComp
    · by_cases hV : V.Nonempty
      · have hdis : ¬ Disjoint V W := by
          intro hd
          exact hVW ⟨hV, hd⟩
        exact (Computable.const true).of_eq (by
          intro r
          simp [pairTest, hV, hdis])
      · exact (Computable.const true).of_eq (by
          intro r
          simp [pairTest, hV])
  have hAll : ∀ xs : List (Finset (Fin (n + m)) × Finset (Fin (n + m))),
      Computable (fun r : input => xs.all (fun q => pairTest q.1 q.2 r)) := by
    intro xs
    induction xs with
    | nil => exact Computable.const true
    | cons q qs ih =>
        rcases q with ⟨V, W⟩
        have hAnd := (Primrec.and.to_comp).comp (hCoord V W) ih
        exact hAnd.of_eq (by intro r; simp [pairTest])
  apply Computable₂.mk
  simpa [lemma1_bounded_profile_test_check,
    pairs, pairTest, input, decodeTuple] using hAll pairs

/-- Every successful bounded run witnesses the associated complexity bound. -/
private theorem lemma1_bounded_profile_test_run_sound
    {D : Map} {c : Nat.Partrec.Code} (hc : Kolmogorov.IsCodeFor c D)
    {s : ℕ} {p y x : BitString}
    (h : lemma1_bounded_profile_test_run
      c s p y = some x) : x ∈ D (p, y) := by
  unfold lemma1_bounded_profile_test_run at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨r, hr, hx⟩ := h
  have hmem := Nat.Partrec.Code.evaln_sound (Option.mem_def.mp hr)
  rw [hc] at hmem
  simp only [Encodable.encodek, Part.ofOption, Part.bind_some, Part.mem_map_iff] at hmem
  obtain ⟨x', hx', hrx⟩ := hmem
  rw [← hrx, Encodable.encodek] at hx
  cases hx
  exact hx'

private theorem lemma1_bounded_profile_test_run_complete
    {D : Map} {c : Nat.Partrec.Code} (hc : Kolmogorov.IsCodeFor c D)
    {p y x : BitString} (h : x ∈ D (p, y)) :
    ∃ s, lemma1_bounded_profile_test_run
      c s p y = some x := by
  have hmem : Encodable.encode x ∈ c.eval (Encodable.encode (p, y)) := by
    rw [hc]
    simp only [Encodable.encodek, Part.ofOption, Part.bind_some]
    exact Part.mem_map _ h
  obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
  refine ⟨s, ?_⟩
  unfold lemma1_bounded_profile_test_run
  rw [Option.bind_eq_some_iff]
  exact ⟨Encodable.encode x, Option.mem_def.mp hs, by simp⟩

private theorem lemma1_bounded_profile_test_run_mono
    {c : Nat.Partrec.Code} {s s' : ℕ} {p y x : BitString}
    (h : lemma1_bounded_profile_test_run
      c s p y = some x) (hs : s ≤ s') :
    lemma1_bounded_profile_test_run
      c s' p y = some x := by
  unfold lemma1_bounded_profile_test_run at h ⊢
  rw [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r, hr, hx⟩ := h
  exact ⟨r, Nat.Partrec.Code.evaln_mono hs hr, hx⟩

private theorem lemma1_sound
    (n m : ℕ) (D : Map) (c : Nat.Partrec.Code)
    (hc : Kolmogorov.IsCodeFor c D)
    (P : BitString → Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ)
    (p w : BitString) (i : ℕ)
    (hi : lemma1_bounded_profile_test_check
      n m c P p w i = true) :
    ∀ V W, V.Nonempty → Disjoint V W →
      subCondK D
        (Fin.append
          ((@Encodable.decode (Fin n → BitString)
            (Primcodable.toEncodable (α := Fin n → BitString)) i.unpair.1).getD fun _ => [])
          (fun j : Fin m => (decodeListCode w).getD j.val [])) V W ≤ P p V W := by
  classical
  intro V W hV hdis
  let a : Fin n → BitString :=
    (@Encodable.decode (Fin n → BitString)
      (Primcodable.toEncodable (α := Fin n → BitString)) i.unpair.1).getD fun _ => []
  let y : Fin m → BitString := fun j => (decodeListCode w).getD j.val []
  let z : Fin (n + m) → BitString := Fin.append a y
  have hmem : (V, W) ∈
      lemma1_bounded_profile_test_pairs
        (n + m) := by
    simp [lemma1_bounded_profile_test_pairs]
  have hall :
      (lemma1_bounded_profile_test_pairs
        (n + m)).all (fun q =>
          if h : q.1.Nonempty ∧ Disjoint q.1 q.2 then
            (Kolmogorov.boundedPrograms (P p q.1 q.2)).any (fun prog =>
              decide
                (lemma1_bounded_profile_test_run
                  c i.unpair.2 prog (subtupleCode z q.2) =
                    some (subtupleCode z q.1)))
          else true) = true := by
    simpa [lemma1_bounded_profile_test_check,
      a, y, z] using hi
  have hcoord := List.all_eq_true.mp hall (V, W) hmem
  have hany :
      (Kolmogorov.boundedPrograms (P p V W)).any (fun prog =>
        decide
          (lemma1_bounded_profile_test_run
            c i.unpair.2 prog (subtupleCode z W) =
              some (subtupleCode z V))) = true := by
    simpa [hV, hdis] using hcoord
  obtain ⟨prog, hprog, hrunBool⟩ := List.any_eq_true.mp hany
  have hrun :
      lemma1_bounded_profile_test_run
        c i.unpair.2 prog (subtupleCode z W) = some (subtupleCode z V) :=
    of_decide_eq_true hrunBool
  have hproduces :=
    lemma1_bounded_profile_test_run_sound
      hc hrun
  have hlen : prog.length ≤ P p V W :=
    (Kolmogorov.mem_boundedPrograms_iff prog (P p V W)).mp hprog
  have hK := (Kolmogorov.condK_le_iff D (subtupleCode z V) (subtupleCode z W)
      (P p V W)).2 ⟨prog, hlen, hproduces⟩
  change (Kolmogorov.condK D (subtupleCode z V) (subtupleCode z W)).toNat ≤ P p V W
  exact ENat.toNat_le_of_le_natCast hK

/-- Finitely many witnessing simulations can be run with one common time bound. -/
private theorem lemma1_complete
    (n m : ℕ) (D : Map) (hD : isOptimalConditional D)
    (c : Nat.Partrec.Code) (hc : Kolmogorov.IsCodeFor c D)
    (P : BitString → Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ)
    (p w : BitString) (a : Fin n → BitString)
    (hbound : ∀ V W, V.Nonempty → Disjoint V W →
      subCondK D (Fin.append a
        (fun j : Fin m => (decodeListCode w).getD j.val [])) V W ≤ P p V W) :
    ∃ s, lemma1_bounded_profile_test_check
      n m c P p w (Nat.pair
        (@Encodable.encode (Fin n → BitString)
          (Primcodable.toEncodable (α := Fin n → BitString)) a) s) = true := by
  classical
  let y : Fin m → BitString := fun j => (decodeListCode w).getD j.val []
  let z : Fin (n + m) → BitString := Fin.append a y
  let L :=
    lemma1_bounded_profile_test_pairs
      (n + m)
  let good : Finset (Fin (n + m)) × Finset (Fin (n + m)) → ℕ → Bool := fun q t =>
    if hq : q.1.Nonempty ∧ Disjoint q.1 q.2 then
      (Kolmogorov.boundedPrograms (P p q.1 q.2)).any fun prog =>
        decide
          (lemma1_bounded_profile_test_run
            c t prog (subtupleCode z q.2) = some (subtupleCode z q.1))
    else true
  have hEach : ∀ q, q ∈ L → ∃ t, good q t = true := by
    intro q _
    by_cases hq : q.1.Nonempty ∧ Disjoint q.1 q.2
    · have hqBound := hbound q.1 q.2 hq.1 hq.2
      have hfinite := condK_ne_top_of_optimal D hD
        (subtupleCode z q.1) (subtupleCode z q.2)
      have hK : condK D (subtupleCode z q.1) (subtupleCode z q.2) ≤
          (P p q.1 q.2 : ℕ∞) := by
        rw [← ENat.natCast_toNat hfinite]
        exact_mod_cast hqBound
      obtain ⟨prog, hprog, hproduces⟩ :=
        (Kolmogorov.condK_le_iff D (subtupleCode z q.1) (subtupleCode z q.2)
          (P p q.1 q.2)).mp hK
      obtain ⟨t, hrun⟩ :=
        lemma1_bounded_profile_test_run_complete
          hc hproduces
      have hprogMem : prog ∈ Kolmogorov.boundedPrograms (P p q.1 q.2) :=
        (Kolmogorov.mem_boundedPrograms_iff prog (P p q.1 q.2)).2 hprog
      refine ⟨t, ?_⟩
      simp only [good, dite_eq_left hq]
      rw [List.any_eq_true]
      exact ⟨prog, hprogMem, by simp [hrun]⟩
    · refine ⟨0, ?_⟩
      simp only [good, dite_eq_right hq]
  have hMono : ∀ q t t', t ≤ t' → good q t = true → good q t' = true := by
    intro q t t' htt ht
    by_cases hq : q.1.Nonempty ∧ Disjoint q.1 q.2
    · have hAny :
          (Kolmogorov.boundedPrograms (P p q.1 q.2)).any (fun prog =>
            decide
              (lemma1_bounded_profile_test_run
                c t prog (subtupleCode z q.2) = some (subtupleCode z q.1))) = true := by
        simpa [good, hq] using ht
      obtain ⟨prog, hprog, hrBool⟩ := List.any_eq_true.mp hAny
      have hr := of_decide_eq_true hrBool
      have hr' :=
        lemma1_bounded_profile_test_run_mono
          hr htt
      have hrBool' :
          decide
            (lemma1_bounded_profile_test_run
              c t' prog (subtupleCode z q.2) = some (subtupleCode z q.1)) = true := by
        simp [hr']
      simp only [good, dite_eq_left hq]
      rw [List.any_eq_true]
      exact ⟨prog, hprog, hrBool'⟩
    · simp only [good, dite_eq_right hq]
  have hCommon : ∀ L' : List (Finset (Fin (n + m)) × Finset (Fin (n + m))),
      (∀ q, q ∈ L' → ∃ t, good q t = true) →
        ∃ s, ∀ q, q ∈ L' → good q s = true := by
    intro L'
    induction L' with
    | nil =>
        intro _
        exact ⟨0, by simp⟩
    | cons q qs ih =>
        intro h
        obtain ⟨tq, htq⟩ := h q (by simp)
        have htail : ∀ r, r ∈ qs → ∃ t, good r t = true := by
          intro r hr
          exact h r (by simp [hr])
        obtain ⟨ts, hts⟩ := ih htail
        refine ⟨max tq ts, ?_⟩
        intro r hr
        rcases List.mem_cons.mp hr with hEq | hTail
        · subst r
          exact hMono q tq (max tq ts) (Nat.le_max_left _ _) htq
        · exact hMono r ts (max tq ts) (Nat.le_max_right _ _) (hts r hTail)
  obtain ⟨s, hStage⟩ := hCommon L hEach
  have hAll : L.all (fun q => good q s) = true :=
    List.all_eq_true.mpr (by
      intro q hq
      exact hStage q hq)
  refine ⟨s, ?_⟩
  simpa [lemma1_bounded_profile_test_check,
    Nat.unpair_pair, Encodable.encodek, L, good, y, z] using hAll


/-- Bounded simulations recognize tuples satisfying all the profile bounds. The same finite
simulation time is used for every coordinate; the certificate index pairs a candidate tuple with
that time. -/
private theorem lemma1_bounded_profile_test
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ)
    (P : BitString → Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ)
    (hP : ∀ V W, Computable (fun p : BitString => P p V W)) :
    ∃ check : (BitString × BitString) → ℕ → Bool,
      Computable₂ check ∧
      (∀ p w i, check (p, w) i = true →
        ∀ V W, V.Nonempty → Disjoint V W →
          subCondK D
            (Fin.append
              ((@Encodable.decode (Fin n → BitString)
                (Primcodable.toEncodable (α := Fin n → BitString)) i.unpair.1).getD fun _ => [])
              (fun j : Fin m => (decodeListCode w).getD j.val [])) V W ≤ P p V W) ∧
      (∀ p w a, (∀ V W, V.Nonempty → Disjoint V W →
          subCondK D (Fin.append a (fun j : Fin m => (decodeListCode w).getD j.val []))
            V W ≤ P p V W) →
        ∃ s, check (p, w) (Nat.pair
          (@Encodable.encode (Fin n → BitString)
            (Primcodable.toEncodable (α := Fin n → BitString)) a) s) = true) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hD.1
  let check : (BitString × BitString) → ℕ → Bool := fun q i =>
    lemma1_bounded_profile_test_check
      n m c P q.1 q.2 i
  refine ⟨check, ?_, ?_, ?_⟩
  · exact lemma1_computable
      n m c P hP
  · intro p w i hi
    exact lemma1_sound
      n m D c hc P p w i hi
  · intro p w a hbound
    obtain ⟨s, hs⟩ :=
      lemma1_complete
        n m D hD c hc P p w a hbound
    exact ⟨s, hs⟩

/-- Enumerates the tuple/time certificates accepted by a computable profile test. -/
private theorem lemma1_enumerate_certificates
    (n : ℕ) (check : (BitString × BitString) → ℕ → Bool)
    (hcheck : Computable₂ check)
    (Q : BitString → BitString → (Fin n → BitString) → Prop)
    (hSound : ∀ p w i, check (p, w) i = true →
      Q p w ((@Encodable.decode (Fin n → BitString)
        (Primcodable.toEncodable (α := Fin n → BitString)) i.unpair.1).getD fun _ => []))
    (hComplete : ∀ p w a, Q p w a →
      ∃ s, check (p, w) (Nat.pair
        (@Encodable.encode (Fin n → BitString)
          (Primcodable.toEncodable (α := Fin n → BitString)) a) s) = true) :
    ∃ E : (BitString × BitString) → ℕ → List BitString,
      Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2) ∧
      (∀ q t, E q t <+: E q (t + 1)) ∧
      ∀ (p : BitString) (y : Fin m → BitString),
        (∀ t z, z ∈ (E (p, tupleCode y) t).eraseDups →
          ∃ a, tupleCode a = z ∧ Q p (tupleCode y) a) ∧
        (∀ a, Q p (tupleCode y) a →
          ∃ t, tupleCode a ∈ (E (p, tupleCode y) t).eraseDups) := by
  classical
  let decodeTuple : ℕ → Fin n → BitString := fun k =>
    (@Encodable.decode (Fin n → BitString)
      (Primcodable.toEncodable (α := Fin n → BitString)) k).getD fun _ => []
  let E : (BitString × BitString) → ℕ → List BitString := fun q t =>
    Nat.rec (motive := fun _ => List BitString) []
      (fun k acc =>
        if check q k then acc ++ [tupleCode (decodeTuple k.unpair.1)] else acc) t
  have hdecode : Computable decodeTuple := by
    have hdec : Computable (@Encodable.decode (Fin n → BitString)
        (Primcodable.toEncodable (α := Fin n → BitString))) := Computable.decode
    exact Computable.option_getD hdec (Computable.const (fun _ => []))
  have htupleCode : Computable (tupleCode : (Fin n → BitString) → BitString) := by
    unfold tupleCode
    apply Computable.comp Kolmogorov.listCode_computable
    exact Primrec.list_ofFn (fun i =>
      (Primrec.fin_app.comp Primrec.id (Primrec.const i))) |>.to_comp
  have hstep : Computable₂ (fun (q : (BitString × BitString) × ℕ)
      (r : ℕ × List BitString) =>
      if check q.1 r.1 then r.2 ++ [tupleCode (decodeTuple r.1.unpair.1)] else r.2) := by
    have hc : Computable (fun z : ((BitString × BitString) × ℕ) × (ℕ × List BitString) =>
        check z.1.1 z.2.1) :=
      Computable₂.comp hcheck
        (Computable.fst.comp (Computable.fst.comp Computable.id))
        (Computable.fst.comp Computable.snd)
    have ha : Computable (fun z : ((BitString × BitString) × ℕ) × (ℕ × List BitString) =>
        z.2.2 ++ [tupleCode (decodeTuple z.2.1.unpair.1)]) := by
      have hv : Computable (fun z : ((BitString × BitString) × ℕ) × (ℕ × List BitString) =>
          tupleCode (decodeTuple z.2.1.unpair.1)) := by
        exact htupleCode.comp (hdecode.comp
          (Computable.fst.comp (Computable.unpair.comp
            (Computable.fst.comp Computable.snd))))
      have hsingleton : Computable (fun z : ((BitString × BitString) × ℕ) × (ℕ × List BitString) =>
          [tupleCode (decodeTuple z.2.1.unpair.1)]) := by
        exact Computable.list_cons.comp hv (Computable.const [])
      exact Computable.list_append.comp
        (Computable.snd.comp (Computable.snd.comp Computable.id)) hsingleton
    have hcond := Computable.cond hc ha
      (Computable.snd.comp (Computable.snd.comp Computable.id))
    exact Computable₂.mk (hcond.of_eq fun z => by
      cases hh : check z.1.1 z.2.1 <;> simp)
  have hE : Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2) := by
    exact (Computable.nat_rec Computable.snd (Computable.const []) hstep).of_eq
      (fun q => rfl)
  have hmono : ∀ q t, E q t <+: E q (t + 1) := by
    intro q t
    change E q t <+: if check q t then E q t ++ [tupleCode (decodeTuple t.unpair.1)] else E q t
    by_cases hc : check q t = true
    · simp [hc, List.prefix_append]
    · simp [hc]
  have hmember : ∀ q t z, z ∈ E q t →
      ∃ i, i < t ∧ check q i = true ∧ tupleCode (decodeTuple i.unpair.1) = z := by
    intro q t
    induction t with
    | zero =>
        intro z hz
        simp [E] at hz
    | succ t ih =>
        intro z hz
        change z ∈ (if check q t then E q t ++ [tupleCode (decodeTuple t.unpair.1)]
          else E q t) at hz
        by_cases hc : check q t = true
        · simp only [ite_eq_left hc, List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | hz
          · obtain ⟨i, hit, hic, hiz⟩ := ih z hz
            exact ⟨i, by omega, hic, hiz⟩
          · subst z
            exact ⟨t, by omega, hc, rfl⟩
        · simp only [ite_eq_right hc] at hz
          obtain ⟨i, hit, hic, hiz⟩ := ih z hz
          exact ⟨i, by omega, hic, hiz⟩
  refine ⟨E, hE, hmono, ?_⟩
  intro p y
  constructor
  · intro t z hz
    have hzE : z ∈ E (p, tupleCode y) t := by simpa using hz
    obtain ⟨i, -, hi, hcode⟩ := hmember (p, tupleCode y) t z hzE
    refine ⟨decodeTuple i.unpair.1, hcode, ?_⟩
    exact hSound p (tupleCode y) i hi
  · intro a hQa
    obtain ⟨s, hs⟩ := hComplete p (tupleCode y) a hQa
    let i := Nat.pair
      (@Encodable.encode (Fin n → BitString)
        (Primcodable.toEncodable (α := Fin n → BitString)) a) s
    have hi : check (p, tupleCode y) i = true := by simpa [i] using hs
    have hdecodeA : decodeTuple i.unpair.1 = a := by
      simp [decodeTuple, i]
    have hmem : tupleCode a ∈ E (p, tupleCode y) (i + 1) := by
      change tupleCode a ∈
        (if check (p, tupleCode y) i then
          E (p, tupleCode y) i ++ [tupleCode (decodeTuple i.unpair.1)]
        else E (p, tupleCode y) i)
      simp [hi, hdecodeA]
    refine ⟨i + 1, ?_⟩
    simpa using hmem

/-- Uniformly enumerates all tuples whose extended-profile coordinates are bounded by a computable
profile, using bounded simulations of the decompressor. -/
private theorem lemma1_bounded_profile_enumeration
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ)
    (P : BitString → Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ)
    (hP : ∀ V W, Computable (fun p : BitString => P p V W)) :
    ∃ E : (BitString × BitString) → ℕ → List BitString,
      Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2) ∧
      (∀ q t, E q t <+: E q (t + 1)) ∧
      ∀ (p : BitString) (y : Fin m → BitString),
        (∀ t z, z ∈ (E (p, tupleCode y) t).eraseDups →
          ∃ a, tupleCode a = z ∧
            ∀ V W, V.Nonempty → Disjoint V W →
              subCondK D (Fin.append a y) V W ≤ P p V W) ∧
        (∀ a, (∀ V W, V.Nonempty → Disjoint V W →
            subCondK D (Fin.append a y) V W ≤ P p V W) →
          ∃ t, tupleCode a ∈ (E (p, tupleCode y) t).eraseDups) := by
  obtain ⟨check, hcheck, hSound, hComplete⟩ :=
    lemma1_bounded_profile_test
      D hD n m P hP
  let Q : BitString → BitString → (Fin n → BitString) → Prop := fun p w a =>
    ∀ V W, V.Nonempty → Disjoint V W →
      subCondK D (Fin.append a (fun j : Fin m => (decodeListCode w).getD j.val []))
        V W ≤ P p V W
  obtain ⟨E, hE, hmono, hEnum⟩ :=
    lemma1_enumerate_certificates
      n check hcheck Q (by
        intro p w i hi
        exact hSound p w i hi) (by
        intro p w a ha
        exact hComplete p w a ha)
  have hdecode (y : Fin m → BitString) :
      (fun j : Fin m => (decodeListCode (tupleCode y)).getD j.val []) = y := by
    funext j
    simp [tupleCode]
  refine ⟨E, hE, hmono, ?_⟩
  intro p y
  constructor
  · intro t z hz
    obtain ⟨a, hcode, hbound⟩ := (hEnum p y).1 t z hz
    refine ⟨a, hcode, ?_⟩
    change ∀ V W, V.Nonempty → Disjoint V W →
      subCondK D (Fin.append a (fun j : Fin m =>
        (decodeListCode (tupleCode y)).getD j.val [])) V W ≤ P p V W at hbound
    rw [hdecode y] at hbound
    exact hbound
  · intro a hbound
    apply (hEnum p y).2 a
    intro V W hV hdis
    rw [hdecode y]
    exact hbound V W hV hdis

/-- Removing repeated outputs gives a list with no duplicate elements. -/
private theorem lemma1_eraseDups_nodup
    (L : List BitString) : (L.eraseDups).Nodup := by
  classical
  have hloop : ∀ (l acc : List BitString), acc.Nodup →
      (List.eraseDupsBy.loop (fun a b : BitString => a == b) l acc).Nodup := by
    intro l
    induction l with
    | nil =>
        intro acc hacc
        simpa only [List.eraseDupsBy.loop.eq_1] using List.nodup_reverse.mpr hacc
    | cons a l ih =>
        intro acc hacc
        cases acc with
        | nil =>
            have hEq : List.eraseDupsBy.loop (fun a b : BitString => a == b) (a :: l) [] =
                List.eraseDupsBy.loop (fun a b : BitString => a == b) l [a] := by
              rw [List.eraseDupsBy.loop.eq_def]
              simp
            rw [hEq]
            exact ih [a] (by simp)
        | cons b bs =>
            have hEq : List.eraseDupsBy.loop (fun a b : BitString => a == b) (a :: l) (b :: bs) =
                (match (b :: bs).any (fun z => a == z) with
                | true => List.eraseDupsBy.loop (fun a b : BitString => a == b) l (b :: bs)
                | false => List.eraseDupsBy.loop (fun a b : BitString => a == b) l (a :: b :: bs))
                             := by
              rw [List.eraseDupsBy.loop.eq_def]
              simp only [List.any_cons]
              rfl
            rw [hEq]
            cases h : (b :: bs).any (fun z => a == z) with
            | true => exact ih (b :: bs) hacc
            | false =>
                have hnot : a ∉ b :: bs := by
                  intro ha
                  have hany : (b :: bs).any (fun z => a == z) = true :=
                    List.any_eq_true.mpr ⟨a, ha, by simp⟩
                  rw [h] at hany
                  contradiction
                exact ih (a :: b :: bs) (List.Nodup.cons hnot hacc)
  change (List.eraseDupsBy.loop (fun a b : BitString => a == b) L []).Nodup
  exact hloop L [] List.nodup_nil

/-- Encodes the extended
complexity profile with logarithmic advice and uniformly enumerate the typization from that advice
and the condition. -/
private theorem lemma1_profile_enumeration
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ E : (BitString × BitString) → ℕ → List BitString,
      Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2) ∧
      (∀ q t, E q t <+: E q (t + 1)) ∧
      ∃ c : ℕ, ∀ (x : Fin n → BitString) (y : Fin m → BitString),
        ∃ p : BitString,
          p.length ≤ logSlack c (natK D (tupleCode (Fin.append x y))) ∧
          (∀ t z, z ∈ (E (p, tupleCode y) t).eraseDups →
            ∃ a, a ∈ typization D x y ∧ tupleCode a = z) ∧
          (∀ a, a ∈ typization D x y →
            ∃ t, tupleCode a ∈ (E (p, tupleCode y) t).eraseDups) ∧
          (∀ t, ((E (p, tupleCode y) t).eraseDups).length ≤
            (typization D x y).ncard) := by
  obtain ⟨P, hP, ⟨cProfile, hProfile⟩⟩ :=
    lemma1_profile_advice
      D hD n m
  obtain ⟨E, hE, hmono, hEnum⟩ :=
    lemma1_bounded_profile_enumeration
      D hD n m P hP
  refine ⟨E, hE, hmono, cProfile, ?_⟩
  intro x y
  obtain ⟨p, hpLen, hpProfile⟩ := hProfile x y
  refine ⟨p, hpLen, ?_, ?_, ?_⟩
  · intro t z hz
    obtain ⟨a, hcode, hbound⟩ := (hEnum p y).1 t z hz
    refine ⟨a, ?_, hcode⟩
    change ExtProfileLe D (Fin.append a y) (Fin.append x y)
    intro V W hV hdis
    rw [← hpProfile V W hV hdis]
    exact hbound V W hV hdis
  · intro a ha
    have hbound : ∀ V W, V.Nonempty → Disjoint V W →
        subCondK D (Fin.append a y) V W ≤ P p V W := by
      intro V W hV hdis
      change ExtProfileLe D (Fin.append a y) (Fin.append x y) at ha
      rw [hpProfile V W hV hdis]
      exact ha V W hV hdis
    exact (hEnum p y).2 a hbound
  · intro t
    have hFinite : (typization D x y).Finite := by
      have hProfileBound : ∀ a, a ∈ typization D x y →
          natCondK D (tupleCode a) (tupleCode y) ≤ natCondK D (tupleCode x) (tupleCode y) := by
        intro a ha
        exact lemma1_profile_bound D x a y ha
      exact (lemma1_count D hD (tupleCode y)
        (natCondK D (tupleCode x) (tupleCode y)) (typization D x y) hProfileBound).1
    let L := (E (p, tupleCode y) t).eraseDups
    have hNodup : L.Nodup := by
      dsimp [L]
      exact lemma1_eraseDups_nodup _
    have hSound : ∀ z, z ∈ L → ∃ a, a ∈ typization D x y ∧ tupleCode a = z := by
      intro z hz
      exact (hEnum p y).1 t z hz |>.imp fun a ha => ⟨by
        change ExtProfileLe D (Fin.append a y) (Fin.append x y)
        intro V W hV hdis
        rw [← hpProfile V W hV hdis]
        exact ha.2 V W hV hdis, ha.1⟩
    have hLcard : L.length ≤ (typization D x y).ncard := by
      let S : Finset BitString := L.toFinset
      let T : Finset (Fin n → BitString) := hFinite.toFinset
      have hST : S ⊆ T.image tupleCode := by
        intro z hz
        have hzL : z ∈ L := by simpa [S] using hz
        obtain ⟨a, ha, hcode⟩ := hSound z hzL
        have haT : a ∈ T := hFinite.mem_toFinset.mpr ha
        rw [← hcode]
        exact Finset.mem_image.mpr ⟨a, haT, rfl⟩
      have hcard : S.card ≤ (T.image tupleCode).card := by
        exact Finset.card_le_card hST
      have hSTcard : (T.image tupleCode).card = T.card := by
        apply Finset.card_image_iff.mpr
        intro a ha b hb hab
        change tupleCode a = tupleCode b at hab
        change listCode (List.ofFn a) = listCode (List.ofFn b) at hab
        apply List.ofFn_injective
        exact Kolmogorov.listCode_injective hab
      have hlen : S.card = L.length := by
        exact List.toFinset_card_of_nodup hNodup
      calc
        L.length = S.card := hlen.symm
        _ ≤ (T.image tupleCode).card := hcard
        _ = T.card := hSTcard
        _ = (typization D x y).ncard := by
          symm
          exact Set.ncard_eq_toFinset_card _ hFinite
    simpa [L] using hLcard

private theorem partrec_comp_computable {α β γ : Type*}
    [Primcodable α] [Primcodable β] [Primcodable γ]
    (f : α → β) (g : β → Part γ) (hf : Computable f) (hg : Partrec g) :
    Partrec (fun x => g (f x)) := by
  exact hg.comp hf

/-- A fixed computable
enumeration can describe its `k`-th distinct output using the binary index and its profile code. -/
private theorem lemma1_index_description
    (D : Map) (hD : isOptimalConditional D)
    (E : (BitString × BitString) → ℕ → List BitString)
    (hE : Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2))
    (hmono : ∀ q t, E q t <+: E q (t + 1)) :
    ∃ c : ℕ, ∀ (p y : BitString) (t k : ℕ),
      k < ((E (p, y) t).eraseDups).length →
      natCondK D (((E (p, y) t).eraseDups).getD k []) y ≤
        (Nat.bits k).length + 2 * p.length + c := by
  let profileEnum : BitString → ℕ → List BitString := fun z s =>
    E (decodeFirst z, decodeSecond z) s
  have hProfileEnum : Computable (fun q : BitString × ℕ => profileEnum q.1 q.2) := by
    unfold profileEnum
    exact hE.comp (Computable.pair
      (Computable.pair (decodeFirst_computable.comp Computable.fst)
        (decodeSecond_computable.comp Computable.fst)) Computable.snd)
  have hProfileMono : ∀ z s, profileEnum z s <+: profileEnum z (s + 1) := by
    intro z s
    exact hmono (decodeFirst z, decodeSecond z) s
  have hExtractor : Partrec (fun q : BitString × BitString =>
      StagedEnumeration.condFFixedLength profileEnum q.2 q.1) :=
    StagedEnumeration.condFFixedLength_partrec profileEnum hProfileEnum
  let adviceLength (w : BitString) : ℕ := (w.takeWhile id).length
  let adviceProfile (w : BitString) : BitString :=
    (w.drop (adviceLength w + 1)).take (adviceLength w)
  let adviceIndexBits (w : BitString) : BitString :=
    w.drop (2 * adviceLength w + 1)
  let inputTransform : (BitString × BitString) → BitString × BitString := fun q =>
    (adviceIndexBits q.1, pairCode (adviceProfile q.1) q.2)
  let extractor : (BitString × BitString) → Part BitString := fun q =>
    StagedEnumeration.condFFixedLength profileEnum q.2 q.1
  let M : Map := extractor ∘ inputTransform
  have hAdviceLength : Primrec (fun q : BitString × BitString => adviceLength q.1) := by
    exact Primrec.list_length.comp
      ((Primrec.list_takeWhile Primrec.id).comp Primrec.fst)
  have hAdviceProfile : Primrec (fun q : BitString × BitString => adviceProfile q.1) := by
    dsimp [adviceProfile]
    exact Primrec.list_take.comp hAdviceLength
      (Primrec.list_drop.comp (Primrec.succ.comp hAdviceLength) Primrec.fst)
  have hAdviceIndexBits : Primrec (fun q : BitString × BitString => adviceIndexBits q.1) := by
    dsimp [adviceIndexBits]
    exact Primrec.list_drop.comp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) hAdviceLength)) Primrec.fst
  have hAdviceProfileLength : Computable (fun q : BitString × BitString =>
      (adviceProfile q.1).length) := Computable.list_length.comp hAdviceProfile.to_comp
  have hAdviceProfileTag : Computable (fun q : BitString × BitString =>
      natCode (adviceProfile q.1).length) :=
    natCode_computable.comp hAdviceProfileLength
  have hAdviceProfileTagAndValue : Computable (fun q : BitString × BitString =>
      natCode (adviceProfile q.1).length ++ adviceProfile q.1) :=
    Computable.list_append.comp hAdviceProfileTag hAdviceProfile.to_comp
  have hAdviceContext : Computable (fun q : BitString × BitString =>
      (natCode (adviceProfile q.1).length ++ adviceProfile q.1) ++ q.2) :=
    Computable.list_append.comp hAdviceProfileTagAndValue Computable.snd
  have hInputTransform : Computable (fun q : BitString × BitString =>
      (adviceIndexBits q.1, pairCode (adviceProfile q.1) q.2)) := by
    exact Computable.pair hAdviceIndexBits.to_comp hAdviceContext
  have hM : Partrec M :=
    partrec_comp_computable inputTransform extractor hInputTransform hExtractor
  obtain ⟨c, hc⟩ := hD.2 M hM
  refine ⟨c + 1, ?_⟩
  intro p y t k hk
  let code : BitString := natCode p.length ++ (p ++ Nat.bits k)
  have hCodeLength : code.length = (Nat.bits k).length + 2 * p.length + 1 := by
    simp [code, List.length_append, length_natCode]
    omega
  have hAdviceLengthCode : adviceLength code = p.length := by
    simp [code, adviceLength]
  have hAdviceProfileCode : adviceProfile code = p := by
    dsimp [adviceProfile]
    rw [hAdviceLengthCode]
    rw [show code = natCode p.length ++ (p ++ Nat.bits k) by rfl]
    rw [drop_natCode_append]
    simp
  have hCodeSuffix :
      (natCode p.length ++ (p ++ Nat.bits k)).drop (2 * p.length + 1) = Nat.bits k := by
    rw [List.drop_append]
    have hfirst : (natCode p.length).drop (2 * p.length + 1) = [] := by
      apply List.drop_eq_nil_of_le
      simp only [length_natCode]
      omega
    have hidx : 2 * p.length + 1 - (natCode p.length).length = p.length := by
      simp only [length_natCode]
      omega
    rw [hfirst, hidx]
    exact List.drop_left' (by simp)
  have hAdviceIndexCode : adviceIndexBits code = Nat.bits k := by
    dsimp [adviceIndexBits]
    rw [hAdviceLengthCode]
    rw [show code = natCode p.length ++ (p ++ Nat.bits k) by rfl]
    exact hCodeSuffix
  have hOutput : ((E (p, y) t).eraseDups).getD k [] ∈ M (code, y) := by
    change ((E (p, y) t).eraseDups).getD k [] ∈
      StagedEnumeration.condFFixedLength profileEnum
        (pairCode (adviceProfile code) y) (adviceIndexBits code)
    rw [hAdviceProfileCode, hAdviceIndexCode]
    have hEval := StagedEnumeration.condFFixedLength_eval profileEnum hProfileMono
      (pairCode p y) (Nat.bits k) t (by
        simpa [profileEnum, StagedEnumeration.condDistinctAt,
          decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits] using hk)
    simpa [profileEnum, StagedEnumeration.condDistinctAt,
      decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits] using hEval
  have hMachineBound : condK D (((E (p, y) t).eraseDups).getD k []) y ≤
      ((code.length + c : ℕ) : ENat) := by
    calc
      condK D (((E (p, y) t).eraseDups).getD k []) y ≤
          condK M (((E (p, y) t).eraseDups).getD k []) y + c := hc _ _
      _ ≤ (code.length : ENat) + c := by
        gcongr
        exact sInf_le ⟨code, hOutput, rfl⟩
      _ = ((code.length + c : ℕ) : ENat) := by simp
  have hNatBound : natCondK D (((E (p, y) t).eraseDups).getD k []) y ≤
      code.length + c := by
    exact ENat.toNat_le_toNat hMachineBound (ENat.natCast_ne_top _)
  rw [hCodeLength] at hNatBound
  omega

/-- Enumerating the typization from its condition
and extended complexity profile, then describing a tuple by its position, bounds its conditional
complexity by the logarithm of the typization size and the cost of the profile. -/
private theorem lemma1_enumeration_lower_bound (D : Map)
    (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (y : Fin m → BitString),
      natCondK D (tupleCode x) (tupleCode y) ≤
        Nat.log2 ((typization D x y).ncard) + 1 +
          logSlack c (natK D (tupleCode (Fin.append x y))) := by
  obtain ⟨E, hE, hmono, ⟨cProfile, hProfile⟩⟩ :=
    lemma1_profile_enumeration D hD n m
  obtain ⟨cIndex, hIndex⟩ :=
    lemma1_index_description D hD E hE hmono
  refine ⟨2 * cProfile + cIndex + 1, ?_⟩
  intro x y
  have hxTyp : x ∈ typization D x y := by
    change ExtProfileLe D (Fin.append x y) (Fin.append x y)
    intro V W hV hdis
    exact le_rfl
  obtain ⟨p, hpLen, hSound, hComplete, hEnumCard⟩ := hProfile x y
  obtain ⟨t, hMem⟩ := hComplete x hxTyp
  let L := (E (p, tupleCode y) t).eraseDups
  have hMemL : tupleCode x ∈ L := by simpa [L] using hMem
  let k := L.idxOf (tupleCode x)
  have hk : k < L.length := by
    dsimp [k]
    exact (List.idxOf_lt_length_iff).2 hMemL
  have hGet : L.getD k [] = tupleCode x := by
    dsimp [k]
    have hidx : List.idxOf (tupleCode x) L < L.length := hk
    have hget? := List.getElem?_idxOf hMemL
    have hget := (List.getElem?_eq_some_iff.mp hget?).2
    rw [List.getD_eq_getElem L [] hidx]
    exact hget
  have hkCard : k < (typization D x y).ncard := by
    have hLen := hEnumCard t
    dsimp [L] at hk hLen
    exact lt_of_lt_of_le hk hLen
  have hbits : (Nat.bits k).length ≤ Nat.log2 ((typization D x y).ncard) + 1 := by
    rw [Nat.size_eq_bits_len, Nat.log2_eq_log_two]
    apply Nat.size_le.mpr
    have hpow := Nat.lt_pow_succ_log_self (b := 2) (by decide)
      ((typization D x y).ncard)
    have hlt : k < 2 ^ (Nat.log 2 ((typization D x y).ncard) + 1) := by
      exact lt_trans hkCard (by simpa [Nat.succ_eq_add_one] using hpow)
    exact hlt
  have hmain := hIndex p (tupleCode y) t k (by simpa [L] using hk)
  rw [hGet] at hmain
  have hslack : 2 * logSlack cProfile (natK D (tupleCode (Fin.append x y))) + cIndex + 1 ≤
      logSlack (2 * cProfile + cIndex + 1)
        (natK D (tupleCode (Fin.append x y))) := by
    unfold logSlack
    nlinarith [Nat.zero_le (cIndex *
      (Nat.bits (natK D (tupleCode (Fin.append x y)))).length),
      Nat.zero_le ((Nat.bits (natK D (tupleCode (Fin.append x y)))).length)]
  calc
    natCondK D (tupleCode x) (tupleCode y) ≤
        (Nat.bits k).length + 2 * p.length + cIndex := hmain
    _ ≤ Nat.log2 ((typization D x y).ncard) + 1 +
        logSlack (2 * cProfile + cIndex + 1)
          (natK D (tupleCode (Fin.append x y))) := by
      calc
        _ ≤ (Nat.log2 ((typization D x y).ncard) + 1) +
            (2 * logSlack cProfile (natK D (tupleCode (Fin.append x y))) + cIndex) := by
          have hleft := Nat.add_le_add hbits (Nat.mul_le_mul_left 2 hpLen)
          omega
        _ ≤ (Nat.log2 ((typization D x y).ncard) + 1) +
            logSlack (2 * cProfile + cIndex + 1)
              (natK D (tupleCode (Fin.append x y))) := by omega

/-- **Lemma 1.** `log |T(x̄ | ȳ)| = K(x̄ | ȳ) + O(log N)`, `N = K(x̄, ȳ)`.  Proof: Appendix. -/
theorem lemma1 (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (y : Fin m → BitString),
      (typization D x y).Finite ∧
      (typization D x y).ncard ≤
        2 ^ (natCondK D (tupleCode x) (tupleCode y) +
          logSlack c (natK D (tupleCode (Fin.append x y)))) ∧
      2 ^ natCondK D (tupleCode x) (tupleCode y) ≤
        (typization D x y).ncard * 2 ^ logSlack c (natK D (tupleCode (Fin.append x y))) := by
  obtain ⟨cLower, hLower⟩ := lemma1_enumeration_lower_bound D hD n m
  refine ⟨max (cLower + 1) 1, ?_⟩
  intro x y
  have hProfile : ∀ a, a ∈ typization D x y →
      natCondK D (tupleCode a) (tupleCode y) ≤ natCondK D (tupleCode x) (tupleCode y) := by
    intro a ha
    exact lemma1_profile_bound D x a y ha
  obtain ⟨hFinite, hCount⟩ := lemma1_count D hD (tupleCode y)
    (natCondK D (tupleCode x) (tupleCode y)) (typization D x y) hProfile
  refine ⟨hFinite, ?_, ?_⟩
  · have hSlack : 1 ≤ logSlack (max (cLower + 1) 1)
        (natK D (tupleCode (Fin.append x y))) := by
      unfold logSlack
      calc
        1 ≤ max (cLower + 1) 1 := Nat.le_max_right _ _
        _ ≤ max (cLower + 1) 1 * (Nat.bits (natK D (tupleCode (Fin.append x y)))).length +
            max (cLower + 1) 1 := Nat.le_add_left _ _
    calc
      (typization D x y).ncard ≤
          2 ^ (natCondK D (tupleCode x) (tupleCode y) + 1) := hCount
      _ ≤ 2 ^ (natCondK D (tupleCode x) (tupleCode y) +
          logSlack (max (cLower + 1) 1) (natK D (tupleCode (Fin.append x y)))) :=
        Nat.pow_le_pow_right (by omega) (Nat.add_le_add_left hSlack _)
  · have hxTyp : x ∈ typization D x y := by
      change ExtProfileLe D (Fin.append x y) (Fin.append x y)
      intro V W hV hdis
      exact le_rfl
    have hCardNe : (typization D x y).ncard ≠ 0 :=
      Set.ncard_ne_zero_of_mem hxTyp hFinite
    have hSlackOne : 1 ≤ logSlack 1 (natK D (tupleCode (Fin.append x y))) := by
      unfold logSlack
      simp only [one_mul]
      exact Nat.le_add_left 1 ((Nat.bits (natK D (tupleCode (Fin.append x y)))).length)
    have hSlackAbsorb : 1 + logSlack cLower (natK D (tupleCode (Fin.append x y))) ≤
        logSlack (cLower + 1) (natK D (tupleCode (Fin.append x y))) := by
      calc
        1 + logSlack cLower (natK D (tupleCode (Fin.append x y))) =
            logSlack cLower (natK D (tupleCode (Fin.append x y))) + 1 := Nat.add_comm _ _
        _ ≤ logSlack cLower (natK D (tupleCode (Fin.append x y))) +
            logSlack 1 (natK D (tupleCode (Fin.append x y))) :=
          Nat.add_le_add_left hSlackOne _
        _ = logSlack (cLower + 1) (natK D (tupleCode (Fin.append x y))) :=
          (logSlack_add_constants cLower 1 _).symm
    have hExponent : natCondK D (tupleCode x) (tupleCode y) ≤
        Nat.log2 ((typization D x y).ncard) +
          logSlack (cLower + 1) (natK D (tupleCode (Fin.append x y))) := by
      calc
        natCondK D (tupleCode x) (tupleCode y) ≤
            Nat.log2 ((typization D x y).ncard) + 1 +
              logSlack cLower (natK D (tupleCode (Fin.append x y))) := hLower x y
        _ ≤ Nat.log2 ((typization D x y).ncard) +
            logSlack (cLower + 1) (natK D (tupleCode (Fin.append x y))) := by
          simpa [Nat.add_assoc] using Nat.add_le_add_left hSlackAbsorb
            (Nat.log2 ((typization D x y).ncard))
    have hLogPow : 2 ^ Nat.log2 ((typization D x y).ncard) ≤
        (typization D x y).ncard := by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 hCardNe
    have hSlackFinal := logSlack_mono_left
      (Nat.le_max_left (cLower + 1) 1) (natK D (tupleCode (Fin.append x y)))
    calc
      2 ^ natCondK D (tupleCode x) (tupleCode y) ≤
          2 ^ (Nat.log2 ((typization D x y).ncard) +
            logSlack (cLower + 1) (natK D (tupleCode (Fin.append x y)))) :=
        Nat.pow_le_pow_right (by omega) hExponent
      _ = 2 ^ Nat.log2 ((typization D x y).ncard) *
          2 ^ logSlack (cLower + 1) (natK D (tupleCode (Fin.append x y))) := by
        rw [Nat.pow_add]
      _ ≤ (typization D x y).ncard *
          2 ^ logSlack (cLower + 1) (natK D (tupleCode (Fin.append x y))) :=
        Nat.mul_le_mul_right _ hLogPow
      _ ≤ (typization D x y).ncard *
          2 ^ logSlack (max (cLower + 1) 1) (natK D (tupleCode (Fin.append x y))) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hSlackFinal)

end Kolmogorov.Relativization
