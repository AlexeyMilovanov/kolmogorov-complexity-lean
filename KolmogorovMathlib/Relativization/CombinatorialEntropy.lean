/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Definitions
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2

/-!
# Combinatorial entropy: Lemma 4 of Muchnik–Romashchenko

Section 3.3 of the paper.
-/

namespace Kolmogorov.Relativization

open Finset

private def lemma4_tupleDecode {n : ℕ} (w : BitString) : Fin n → BitString :=
  fun i => (decodeListCode w).getD i.val []

private def lemma4_subtupleDecode {n : ℕ} (V : Finset (Fin n)) (w : BitString) : BitString :=
  subtupleCode (lemma4_tupleDecode w) V

private def lemma4_sectionSet {n : ℕ} (V W : Finset (Fin n)) (z : BitString) :
    Finset BitString :=
  (((decodeListCode (decodeSecond z)).filter
      (fun t => decide (lemma4_subtupleDecode W t = decodeFirst z))).map
      (lemma4_subtupleDecode V)).toFinset

private def lemma4_sectionList {n : ℕ} (V W : Finset (Fin n)) (z : BitString) :
    List BitString :=
  canonicalFinsetList (lemma4_sectionSet V W z)

/-- The list of projections of tuples matching the fixed W-coordinates is computable
from the code of the tuple set and the coordinate sets. -/
private theorem lemma4_sectionList_computable {n : ℕ} (V W : Finset (Fin n)) :
    Computable (lemma4_sectionList V W) := by
  have hsub (S : Finset (Fin n)) : Primrec (lemma4_subtupleDecode S) := by
    have hget : Primrec (fun q : BitString × Fin n =>
        (decodeListCode q.1).getD q.2.val []) :=
      (Primrec.list_getD []).comp
        (decodeListCode_primrec.comp Primrec.fst)
        (Primrec.fin_val.comp Primrec.snd)
    have hselected : Primrec (fun w : BitString =>
        (S.sort (· ≤ ·)).map (fun i => (decodeListCode w).getD i.val [])) :=
      Primrec.list_map (Primrec.const (S.sort (· ≤ ·))) hget.to₂
    exact (listCode_primrec.comp hselected).of_eq fun w => by
      rfl
  have htuples : Primrec (fun z : BitString => decodeListCode (decodeSecond z)) :=
    decodeListCode_primrec.comp CodedFiniteDistribution.decodeSecond_primrec
  have htest : Primrec (fun q : BitString × BitString =>
      decide (lemma4_subtupleDecode W q.2 = decodeFirst q.1)) := by
    exact PrimrecPred.decide (PrimrecRel.comp Primrec.eq
      ((hsub W).comp Primrec.snd)
      (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst))
  have hfiltered : Primrec (fun z : BitString =>
      (decodeListCode (decodeSecond z)).filter
        (fun t => decide (lemma4_subtupleDecode W t = decodeFirst z))) :=
    Primrec.list_filter htuples htest.to₂
  have hmapped : Primrec (fun z : BitString =>
      ((decodeListCode (decodeSecond z)).filter
        (fun t => decide (lemma4_subtupleDecode W t = decodeFirst z))).map
          (lemma4_subtupleDecode V)) :=
    Primrec.list_map hfiltered ((hsub V).comp Primrec.snd).to₂
  exact (canonicalFinsetList_toFinset_primrec.comp hmapped).to_comp

/-- An element at a given position in a computable finite list has conditional complexity
bounded by the logarithm of the list length, up to an additive constant. -/
private theorem lemma4_rank_complexity (D : Map) (hD : isOptimalConditional D)
    (f : BitString → List BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ (y : BitString) (i : ℕ), i < (f y).length →
      natCondK D ((f y).getD i []) y ≤ Nat.clog 2 (f y).length + c := by
  let decoder : Map := fun q => Part.some ((f q.2).getD (decodeBits q.1) [])
  have hget : Computable (fun q : BitString × BitString =>
      (f q.2).getD (decodeBits q.1) []) := by
    have hf' : Computable (fun q : BitString × BitString => f q.2) := hf.comp Computable.snd
    have hi : Computable (fun q : BitString × BitString => decodeBits q.1) :=
      decodeBits_computable.comp Computable.fst
    exact (Primrec.list_getD []).to_comp.comp hf' hi
  have hdecoder : isDecompressor decoder := Computable.partrec hget
  obtain ⟨c, hc⟩ := hD.2 decoder hdecoder
  refine ⟨c, fun y i hi => ?_⟩
  have hprod : produces decoder (Nat.bits i) y ((f y).getD i []) := by
    simp [produces, decoder, decodeBits_natBits]
  have hcond : condK decoder ((f y).getD i []) y ≤ ((Nat.bits i).length : ℕ∞) := by
    change sInf (candidateLengths decoder ((f y).getD i []) y) ≤ _
    exact sInf_le ⟨Nat.bits i, hprod, rfl⟩
  have hD_bound : condK D ((f y).getD i []) y ≤
      ((Nat.bits i).length + c : ℕ∞) := by
    calc
      condK D ((f y).getD i []) y ≤ condK decoder ((f y).getD i []) y + c := hc _ _
      _ ≤ ((Nat.bits i).length : ℕ∞) + c := by
        simpa [add_comm] using add_le_add_left hcond (c : ℕ∞)
      _ = ((Nat.bits i).length + c : ℕ∞) := rfl
  have hNat : natCondK D ((f y).getD i []) y ≤ (Nat.bits i).length + c :=
    ENat.toNat_le_of_le_natCast hD_bound
  have hbit : (Nat.bits i).length ≤ Nat.clog 2 (f y).length := by
    rw [Nat.size_eq_bits_len]
    apply (Nat.size_le).2
    exact lt_of_lt_of_le hi (Nat.le_pow_clog (by decide) _)
  omega

private theorem lemma4_tupleDecode_tupleCode {n : ℕ} (x : Fin n → BitString) :
    lemma4_tupleDecode (tupleCode x) = x := by
  funext i
  simp [lemma4_tupleDecode, tupleCode]

/-- Filtering the decoded tuple set by its W-coordinates and projecting to V gives
the section projection of the tuple set. -/
private theorem lemma4_sectionSet_eq {n : ℕ}
    (A : Finset (Fin n → BitString)) (x : Fin n → BitString)
    (V W : Finset (Fin n)) :
    lemma4_sectionSet V W (pairCode (subtupleCode x W) (tupleSetCode A)) =
      sectionProjection A V W x := by
  ext b
  simp only [lemma4_sectionSet, sectionProjection, tupleSetCode, finsetListCode,
    decodeSecond_pairCode, decodeFirst_pairCode, decodeListCode_listCode,
    List.mem_toFinset, List.mem_map, List.mem_filter, mem_canonicalFinsetList,
    Finset.mem_image, Finset.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ⟨⟨a, ha, hta⟩, hW⟩, rfl⟩
    subst t
    have hWa : subtupleCode a W = subtupleCode x W := by
      simpa [lemma4_subtupleDecode, lemma4_tupleDecode_tupleCode] using hW
    refine ⟨a, ⟨ha, hWa⟩, ?_⟩
    simp [lemma4_subtupleDecode, lemma4_tupleDecode_tupleCode]
  · rintro ⟨a, ⟨ha, hWa⟩, rfl⟩
    refine ⟨tupleCode a, ?_, ?_⟩
    · exact ⟨⟨a, ha, rfl⟩,
        by simpa [lemma4_subtupleDecode, lemma4_tupleDecode_tupleCode] using hWa⟩
    · simp [lemma4_subtupleDecode, lemma4_tupleDecode_tupleCode]

/-- **Lemma 4.** For a finite set `A` of `n`-tuples and `x̄ ∈ A`,
`K(x̄_V | x̄_W, list(A)) ≤ ent_{V|W}(A) + O(1)`; the constant depends on `n`.  Proof:
Section 3.3 (the ordinal number of `x̄_V` in `π_V σ_W(A | x̄_W)`). -/
theorem lemma4 (D : Map) (hD : isOptimalConditional D) (n : ℕ) :
    ∃ c : ℕ, ∀ (A : Finset (Fin n → BitString)) (x : Fin n → BitString), x ∈ A →
      ∀ V W : Finset (Fin n),
        natCondK D (subtupleCode x V) (pairCode (subtupleCode x W) (tupleSetCode A)) ≤
          combEnt A V W + c := by
  let hBound : ∀ p : Finset (Fin n) × Finset (Fin n),
      ∃ c : ℕ, ∀ y i, i < (lemma4_sectionList p.1 p.2 y).length →
        natCondK D ((lemma4_sectionList p.1 p.2 y).getD i []) y ≤
          Nat.clog 2 (lemma4_sectionList p.1 p.2 y).length + c :=
    fun p => lemma4_rank_complexity D hD (lemma4_sectionList p.1 p.2)
      (lemma4_sectionList_computable p.1 p.2)
  let cFor : Finset (Fin n) × Finset (Fin n) → ℕ := fun p => Classical.choose (hBound p)
  let c := Finset.univ.sup cFor
  refine ⟨c, fun A x hx V W => ?_⟩
  let y := pairCode (subtupleCode x W) (tupleSetCode A)
  let L := lemma4_sectionList V W y
  have hmem : subtupleCode x V ∈ L := by
    change subtupleCode x V ∈ canonicalFinsetList (lemma4_sectionSet V W
      (pairCode (subtupleCode x W) (tupleSetCode A)))
    rw [mem_canonicalFinsetList, lemma4_sectionSet_eq A x V W]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩, rfl⟩
  let i := L.findIdx (fun b => decide (b = subtupleCode x V))
  have hi : i < L.length := by
    change L.findIdx (fun b => decide (b = subtupleCode x V)) < L.length
    rw [List.findIdx_lt_length]
    exact ⟨subtupleCode x V, hmem, by simp⟩
  have hget : L.getD i [] = subtupleCode x V := by
    change L.getD (L.findIdx (fun b => decide (b = subtupleCode x V))) [] = _
    have hlt : L.findIdx (fun b => decide (b = subtupleCode x V)) < L.length := hi
    rw [List.getD_eq_getElem L [] hlt]
    exact of_decide_eq_true
      (List.findIdx_getElem (p := fun b => decide (b = subtupleCode x V)) (w := hlt))
  have hcFor : cFor (V, W) ≤ c := by
    exact Finset.le_sup (f := cFor) (Finset.mem_univ (V, W))
  have hRank := Classical.choose_spec (hBound (V, W)) y i hi
  have hRank' : natCondK D (L.getD i []) y ≤ Nat.clog 2 L.length +
      cFor (V, W) := by
    change natCondK D ((lemma4_sectionList V W y).getD i []) y ≤
      Nat.clog 2 (lemma4_sectionList V W y).length + cFor (V, W)
    simpa [cFor] using hRank
  have hRankX : natCondK D (subtupleCode x V) y ≤ Nat.clog 2 L.length + cFor (V, W) := by
    rw [← hget]
    exact hRank'
  have hcard : (sectionProjection A V W x).card ≤ maxSectionCard A V W :=
    Finset.le_sup (f := fun u => (sectionProjection A V W u).card) hx
  have hlen : L.length = (sectionProjection A V W x).card := by
    change (canonicalFinsetList (lemma4_sectionSet V W
      (pairCode (subtupleCode x W) (tupleSetCode A)))).length = _
    rw [length_canonicalFinsetList, lemma4_sectionSet_eq A x V W]
  have hclog : Nat.clog 2 L.length ≤ combEnt A V W := by
    unfold combEnt maxSectionCard
    rw [hlen]
    exact Nat.clog_monotone 2 hcard
  change natCondK D (subtupleCode x V) y ≤ combEnt A V W + c
  omega

end Kolmogorov.Relativization
