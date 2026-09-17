import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.BusyBeaver
import KolmogorovMathlib.Complexity.CanonicalObjects.HubReductions
import KolmogorovMathlib.Complexity.CanonicalObjects.PrimitiveReductions

/-!
# The nine canonical objects reduce to one another

SUV Theorem 15 says the nine objects of level `n` are mutually reducible.  The reductions are
organised through a hub, the list of halting programs of length at most `n` (object (e)):
`canonicalReduces_haltingList_busyBeaver`, `…_maxTime`, `…_complexityGraph`,
`…_firstIncompressible` and `…_slowestProgram` reduce the hub to the others, and the reverse
edges compose with them.

`haltSel` is the halting-count diagonal selector — from the number of halting programs of a
level it recovers the level's halting set — with `haltSel_partrec` and `haltSel_intended`; the
`lower_*` lemmas are the complexity lower bounds for the individual objects, and
`outputsUpTo`, `bigNat` and `graphToGamma` the auxiliary computable maps.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

private theorem graphToGamma_primrec : Primrec graphToGamma := by
  have hn : Primrec (fun w : BitString =>
      (decodeFirst ((decodeListCode w).headI)).length) :=
    Primrec.list_length.comp
      (decodeFirst_primrec.comp (Primrec.list_headI.comp decodeListCode_primrec))
  have hp : Primrec₂ (fun (w : BitString) (z : BitString) =>
      decide ((decodeFirst ((decodeListCode w).headI)).length ≤
        decodeBits (decodeSecond z))) := by
    have h : Primrec (fun q : BitString × BitString =>
        decide ((decodeFirst ((decodeListCode q.1).headI)).length ≤
          decodeBits (decodeSecond q.2))) :=
      PrimrecPred.decide (PrimrecRel.comp Primrec.nat_le (hn.comp Primrec.fst)
        (primrec_decodeBits.comp (decodeSecond_primrec.comp Primrec.snd)))
    exact h.to₂
  have hfind : Primrec (fun w : BitString => (decodeListCode w).find?
      (fun z => decide ((decodeFirst ((decodeListCode w).headI)).length ≤
        decodeBits (decodeSecond z)))) :=
    list_find?_primrec decodeListCode_primrec hp
  have hmap : Primrec (fun w : BitString => ((decodeListCode w).find?
      (fun z => decide ((decodeFirst ((decodeListCode w).headI)).length ≤
        decodeBits (decodeSecond z)))).map decodeFirst) :=
    Primrec.option_map hfind (decodeFirst_primrec.comp Primrec.snd).to₂
  exact (Primrec₂.comp Primrec.option_getD hmap (Primrec.const [])).of_eq (fun w => rfl)

private theorem lower_7 (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∃ k : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c 7 n) + (k : ℕ∞) := by
  have _hc := hc
  obtain ⟨C, hC⟩ := plainK_partrec_map_le U hU
    (fun w => Part.some (graphToGamma w))
    graphToGamma_primrec.to_comp.partrec
  refine ⟨C, fun n => ?_⟩
  have h1 : plainK U (objFirstIncompressible U n)
      ≤ plainK U (objComplexityGraph U n) + (C : ℕ∞) := by
    have h2 := hC (objComplexityGraph U n)
      (graphToGamma (objComplexityGraph U n)) (Part.mem_some _)
    rwa [graphToGamma_spec U hU n] at h2
  calc (n : ℕ∞) ≤ plainK U (objFirstIncompressible U n) :=
        objFirstIncompressible_spec U n
    _ ≤ plainK U (objComplexityGraph U n) + (C : ℕ∞) := h1

private theorem lower_1 (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∃ k : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c 1 n) + (k : ℕ∞) := by
  obtain ⟨C, hC⟩ := plainKNat_omegaCount_lower U hU c hc
  refine ⟨C, fun n => ?_⟩
  exact hC n

/-- The halting-count diagonal selector.  On input `pairCode (Nat.bits e) p` it runs `U`
on `p` to obtain the number `N` of halting programs of length at most `m := |p| + e`,
searches for a stage `T` at which exactly `N` of them have halted (such a `T` is at
least `maxHaltingStage c m`, so the bound-`m` enumeration of simple strings is already
complete at `T`), and returns the first string of length `m + 1` missing from that
enumeration. -/
private noncomputable def haltSel (U : Map) (c : Code) (z : BitString) :
    Part BitString :=
  (U (decodeSecond z, [])).bind (fun cntBits =>
    (Nat.rfind (fun t => Part.some
      (countHalts c ((decodeSecond z).length + bitsToNat (decodeFirst z)) t
        == bitsToNat cntBits))).bind (fun t =>
      (Part.ofOption
        ((canonicalFinsetList (stringsOfLength
            ((decodeSecond z).length + bitsToNat (decodeFirst z) + 1))).find?
          (fun s => decide (s ∉ boundedOutputStage c
            ((decodeSecond z).length + bitsToNat (decodeFirst z)) t)))).bind
        (fun x => Part.some x)))

private theorem haltSel_partrec (U : Map) (hU : isDecompressor U) (c : Code) :
    Partrec (haltSel U c) := by
  have hrun : Partrec (fun z : BitString => U (decodeSecond z, [])) :=
    Partrec.comp hU (Computable.pair decodeSecond_computable (Computable.const []))
  have hm : Primrec (fun st : (BitString × BitString) × ℕ =>
      (decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1)) :=
    Primrec.nat_add.comp
      (Primrec.list_length.comp
        (decodeSecond_primrec.comp (Primrec.fst.comp Primrec.fst)))
      (bitsToNat_primrec.comp
        (decodeFirst_primrec.comp (Primrec.fst.comp Primrec.fst)))
  have hstage : Primrec (fun st : (BitString × BitString) × ℕ =>
      boundedOutputStage c
        ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1)) st.2) :=
    (boundedOutputStage_primrec c).comp (Primrec.pair hm Primrec.snd)
  have hcheck : Computable₂ (fun (q : BitString × BitString) (t : ℕ) =>
      countHalts c ((decodeSecond q.1).length + bitsToNat (decodeFirst q.1)) t ==
        bitsToNat q.2) :=
    (Primrec.beq.comp
      ((countHalts_primrec c).comp (Primrec.pair hm Primrec.snd))
      (bitsToNat_primrec.comp (Primrec.snd.comp Primrec.fst))).to_comp.to₂
  have hsearch : Partrec (fun q : BitString × BitString =>
      Nat.rfind (fun t => Part.some
        (countHalts c ((decodeSecond q.1).length + bitsToNat (decodeFirst q.1)) t ==
          bitsToNat q.2))) :=
    Partrec.rfind hcheck.partrec₂
  have hstrings : Primrec (fun st : (BitString × BitString) × ℕ =>
      canonicalFinsetList (stringsOfLength
        ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1) + 1))) := by
    exact (canonicalFinsetList_toFinset_primrec.comp
      (allStrings_primrec.comp (Primrec.succ.comp hm))).of_eq (fun _ => rfl)
  have hnotmem : Primrec₂
      (fun (st : (BitString × BitString) × ℕ) (s : BitString) =>
        decide (s ∉ boundedOutputStage c
          ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1)) st.2)) := by
    refine (Primrec.not.comp
      (bitString_mem_primrec.comp Primrec.snd (hstage.comp Primrec.fst))).to₂.of_eq ?_
    intro st s
    simp
  have hfindOpt : Primrec (fun st : (BitString × BitString) × ℕ =>
      (canonicalFinsetList (stringsOfLength
        ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1) + 1))).find?
          (fun s => decide (s ∉ boundedOutputStage c
            ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1)) st.2))) :=
    list_find?_primrec hstrings hnotmem
  have hfindPart : Partrec (fun st : (BitString × BitString) × ℕ =>
      Part.ofOption
        ((canonicalFinsetList (stringsOfLength
          ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1) + 1))).find?
            (fun s => decide (s ∉ boundedOutputStage c
              ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1)) st.2)))) :=
    hfindOpt.to_comp.ofOption
  have hpure : Partrec₂
      (fun (_ : (BitString × BitString) × ℕ) (x : BitString) => Part.some x) :=
    (Partrec.comp Partrec.some Computable.snd).to₂
  have hfind : Partrec₂ (fun (q : BitString × BitString) (t : ℕ) =>
      (Part.ofOption
        ((canonicalFinsetList (stringsOfLength
          ((decodeSecond q.1).length + bitsToNat (decodeFirst q.1) + 1))).find?
            (fun s => decide (s ∉ boundedOutputStage c
              ((decodeSecond q.1).length + bitsToNat (decodeFirst q.1)) t)))).bind
        (fun x => Part.some x)) :=
    (Partrec.bind hfindPart hpure).to₂
  have hafter : Partrec₂ (fun (z cntBits : BitString) =>
      (Nat.rfind (fun t => Part.some
        (countHalts c ((decodeSecond z).length + bitsToNat (decodeFirst z)) t ==
          bitsToNat cntBits))).bind
        (fun t =>
          (Part.ofOption
            ((canonicalFinsetList (stringsOfLength
              ((decodeSecond z).length + bitsToNat (decodeFirst z) + 1))).find?
                (fun s => decide (s ∉ boundedOutputStage c
                  ((decodeSecond z).length + bitsToNat (decodeFirst z)) t)))).bind
            (fun x => Part.some x))) :=
    (Partrec.bind hsearch hfind).to₂
  unfold haltSel
  exact Partrec.bind hrun hafter

/-- On its intended input `pairCode (Nat.bits e) p`, where `p` is a `U`-program for the
number of halting programs of length at most `m = |p| + e`, the halting-count selector
produces a string whose complexity exceeds `m`. -/
private theorem haltSel_intended (U : Map) (c : Code) {m e : ℕ} {p : BitString}
    (hm : m = p.length + e)
    (hp : produces U p [] (Nat.bits (haltingProgramsBounded c m).length)) :
    ∃ x, x ∈ haltSel U c (pairCode (Nat.bits e) p) ∧
      x ∉ completedBoundedOutput c m := by
  subst hm
  set M := p.length + e with hMdef
  have hex : ∃ t, countHalts c M t = (haltingProgramsBounded c M).length :=
    ⟨maxHaltingStage c M, countHalts_maxHaltingStage c M⟩
  set t0 := Nat.find hex with ht0def
  have ht0 : countHalts c M t0 = (haltingProgramsBounded c M).length := Nat.find_spec hex
  have ht0Complete : boundedOutputStage c M t0 = completedBoundedOutput c M :=
    boundedOutputStage_eq_completedBoundedOutput c M t0
      (maxHaltingStage_le_of_countHalts_eq c M t0 ht0)
  have ht0Nodup : (boundedOutputStage c M t0).Nodup := boundedOutputStage_nodup c M t0
  have ht0Short : (boundedOutputStage c M t0).length < 2 ^ (M + 1) :=
    boundedOutputStage_length_lt c M t0
  obtain ⟨x0, hx0all, hx0missing⟩ :=
    exists_mem_allStrings_not_mem_of_length_lt ht0Nodup ht0Short
  have hx0full : x0 ∈ canonicalFinsetList (stringsOfLength (M + 1)) :=
    mem_canonicalFinsetList.mpr
      ((mem_stringsOfLength (M + 1) x0).mpr ((mem_allStrings (M + 1) x0).mp hx0all))
  obtain ⟨x, hxfind⟩ : ∃ x, (canonicalFinsetList (stringsOfLength (M + 1))).find?
      (fun s => decide (s ∉ boundedOutputStage c M t0)) = some x := by
    apply Option.isSome_iff_exists.mp
    rw [List.find?_isSome]
    exact ⟨x0, hx0full, by simp [hx0missing]⟩
  have hxmissingStage : x ∉ boundedOutputStage c M t0 := by
    have hpred := List.find?_some hxfind
    simpa using hpred
  have hxmissingCompleted : x ∉ completedBoundedOutput c M := by
    simpa [ht0Complete] using hxmissingStage
  have ht0Search : t0 ∈ Nat.rfind (fun t => Part.some
      (countHalts c M t == (haltingProgramsBounded c M).length)) := by
    refine Nat.mem_rfind.mpr ⟨by simp [ht0], ?_⟩
    intro t ht
    have hne : countHalts c M t ≠ (haltingProgramsBounded c M).length := Nat.find_min hex ht
    simp [hne]
  refine ⟨x, ?_, hxmissingCompleted⟩
  unfold haltSel
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  change x ∈ (U (p, [])).bind (fun cntBits =>
    (Nat.rfind (fun t => Part.some (countHalts c M t == bitsToNat cntBits))).bind
      (fun t =>
        (Part.ofOption
          ((canonicalFinsetList (stringsOfLength (M + 1))).find?
            (fun s => decide (s ∉ boundedOutputStage c M t)))).bind
          (fun y => Part.some y)))
  rw [Part.mem_bind_iff]
  refine ⟨Nat.bits (haltingProgramsBounded c M).length, ?_, ?_⟩
  · simpa [M] using hp
  · simp only [bitsToNat_bits]
    rw [Part.mem_bind_iff]
    refine ⟨t0, ht0Search, ?_⟩
    rw [hxfind]
    rw [Part.mem_bind_iff]
    exact ⟨x, Part.mem_some x, Part.mem_some x⟩

private theorem lower_5 (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∃ k : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c 5 n) + (k : ℕ∞) := by
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le U hU (haltSel U c) (haltSel_partrec U hU.1 c)
  obtain ⟨Clen, hlen⟩ := plainK_le_length U hU
  obtain ⟨D, hD⟩ := deficit_bounded_of_le_two_mul_bits_length_add (Clen + Cmap)
  refine ⟨D, fun n => ?_⟩
  have hcanon : canonicalObject U c 5 n = Nat.bits (haltingProgramsBounded c n).length := rfl
  rw [hcanon]
  have hfinite : plainK U (Nat.bits (haltingProgramsBounded c n).length) ≠ ⊤ := by
    intro htop
    have h := hlen (Nat.bits (haltingProgramsBounded c n).length)
    rw [htop, top_le_iff] at h
    exact ENat.natCast_ne_top _ h
  have hfinite' : KP U (Nat.bits (haltingProgramsBounded c n).length) [] ≠ ⊤ := hfinite
  obtain ⟨p, hp, hpLength⟩ := exists_program_of_KP_ne_top hfinite'
  by_cases hpm : n ≤ p.length
  · calc (n : ℕ∞) ≤ (p.length : ℕ∞) := by exact_mod_cast hpm
      _ = plainK U (Nat.bits (haltingProgramsBounded c n).length) := by
          rw [hpLength]; rfl
      _ ≤ plainK U (Nat.bits (haltingProgramsBounded c n).length) + (D : ℕ∞) :=
          le_add_right le_rfl
  · push Not at hpm
    have hm : n = p.length + (n - p.length) := by omega
    obtain ⟨x, hxSel, hxMissing⟩ := haltSel_intended U c hm hp
    have hxLower : (n : ℕ∞) < plainK U x := plainK_gt_of_not_mem_completed hc hxMissing
    have hxUpper : plainK U x ≤
        plainK U (pairCode (Nat.bits (n - p.length)) p) + (Cmap : ℕ∞) := hmap _ _ hxSel
    have hinput : plainK U (pairCode (Nat.bits (n - p.length)) p) ≤
        ((pairCode (Nat.bits (n - p.length)) p).length : ℕ∞) + (Clen : ℕ∞) := hlen _
    have hmx : (n : ℕ∞) <
        ((pairCode (Nat.bits (n - p.length)) p).length : ℕ∞) + (Clen : ℕ∞) + (Cmap : ℕ∞) :=
      lt_of_lt_of_le hxLower (hxUpper.trans (by gcongr))
    have hmxNat : n < (pairCode (Nat.bits (n - p.length)) p).length + Clen + Cmap := by
      exact_mod_cast hmx
    have heDeficit : n - p.length ≤ 2 * (Nat.bits (n - p.length)).length + (Clen + Cmap) := by
      rw [length_pairCode] at hmxNat
      omega
    have heD : n - p.length ≤ D := hD _ heDeficit
    have hmD : n ≤ p.length + D := by omega
    calc (n : ℕ∞) ≤ ((p.length + D : ℕ) : ℕ∞) := by exact_mod_cast hmD
      _ = (p.length : ℕ∞) + (D : ℕ∞) := by rw [Nat.cast_add]
      _ = plainK U (Nat.bits (haltingProgramsBounded c n).length) + (D : ℕ∞) := by
          rw [hpLength]; rfl
private def outputsUpTo (c : Code) (t : ℕ) : List BitString :=
  (List.range t).filterMap
    (fun e => (Code.evaln t c e).bind (fun r => (Encodable.decode r : Option BitString)))

private def bigNat (c : Code) (t : ℕ) : ℕ :=
  maxCanon (outputsUpTo c t) + 1

private theorem outputsUpTo_primrec (c : Code) : Primrec (outputsUpTo c) := by
  have hev : Primrec (fun z : ℕ × ℕ => Code.evaln z.1 c z.2) :=
    Primrec₂.comp (evaln_primrec c) Primrec.fst Primrec.snd
  have hdec : Primrec₂ (fun (_ : ℕ × ℕ) (r : ℕ) => (Encodable.decode r : Option BitString)) :=
    (Primrec.decode.comp Primrec.snd).to₂
  have h : Primrec₂ (fun (t : ℕ) (e : ℕ) =>
      (Code.evaln t c e).bind (fun r => (Encodable.decode r : Option BitString))) :=
    (Primrec.option_bind hev hdec).to₂
  exact Primrec.listFilterMap Primrec.list_range h

private theorem bigNat_primrec (c : Code) : Primrec (bigNat c) :=
  (Primrec.succ.comp (maxCanon_primrec.comp (outputsUpTo_primrec c))).of_eq
    (fun _ => rfl)

private theorem mem_outputs_of_runOut (c : Code) (T : ℕ) {p y : BitString}
    (h : runOut c T p = some y) : y ∈ outputsUpTo c T := by
  unfold runOut at h
  set e : ℕ := Encodable.encode ((p, ([] : BitString)) : BitString × BitString) with he
  rcases hev : Code.evaln T c e with _ | r
  · rw [hev] at h; simp at h
  · rw [hev] at h
    simp only [Option.bind_some] at h
    have hlt : e < T := Nat.Partrec.Code.evaln_bound hev
    refine List.mem_filterMap.mpr ⟨e, List.mem_range.mpr hlt, ?_⟩
    rw [hev]
    simpa using h

private theorem lt_bigNat (c : Code) (n : ℕ) {x : ℕ} (hx : x ∈ boundedNatOutputs c n) :
    x < bigNat c (maxHaltingStage c n) := by
  set T := maxHaltingStage c n with hT
  have h1 : Nat.bits x ∈ completedBoundedOutput c n :=
    (mem_boundedNatOutputs_iff_mem_completed c n x).mp hx
  have h2 : Nat.bits x ∈ boundedOutputStage c n T := h1
  have h3 : Nat.bits x ∈ snapshotCodes c n T := by
    have hfin : Nat.bits x ∈ (boundedOutputStage c n T).toFinset := List.mem_toFinset.mpr h2
    rw [boundedOutputStage_toFinset_eq_snapshotCodes] at hfin
    exact List.mem_toFinset.mp hfin
  rw [show snapshotCodes c n T = (boundedPrograms n).filterMap (runOut c T) from rfl,
    List.mem_filterMap] at h3
  obtain ⟨p, _, hrun⟩ := h3
  have hmem : Nat.bits x ∈ outputsUpTo c T := mem_outputs_of_runOut c T hrun
  have hle : x ≤ maxCanon (outputsUpTo c T) :=
    le_foldr_max_of_mem ((mem_maxCanonList _ x).mpr hmem)
  unfold bigNat
  omega

private theorem lower_of_partrec (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) (i : ℕ) (F : BitString →. BitString) (hF : Partrec F)
    (K0 : ℕ) (M : ℕ → ℕ)
    (hFM : ∀ n : ℕ, K0 ≤ n → Nat.bits (M n) ∈ F (canonicalObject U c i n))
    (hbig : ∀ n : ℕ, K0 ≤ n → ∀ x ∈ boundedNatOutputs c n, x < M n) :
    ∃ k : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c i n) + (k : ℕ∞) := by
  obtain ⟨C, hC⟩ := plainK_partrec_map_le U hU F hF
  refine ⟨C + K0, fun n => ?_⟩
  by_cases hn : K0 ≤ n
  · have hnot : M n ∉ boundedNatOutputs c n := fun h => lt_irrefl _ (hbig n hn _ h)
    have h1 : ¬ (plainKNat U (M n) ≤ (n : ℕ∞)) := fun h =>
      hnot ((mem_boundedNatOutputs_iff_plainKNat_le hc n (M n)).mpr h)
    have h2 : (n : ℕ∞) < plainK U (Nat.bits (M n)) := not_le.mp h1
    have h3 : plainK U (Nat.bits (M n)) ≤ plainK U (canonicalObject U c i n) + (C : ℕ∞) :=
      hC _ _ (hFM n hn)
    calc (n : ℕ∞) ≤ plainK U (canonicalObject U c i n) + (C : ℕ∞) :=
          le_of_lt (lt_of_lt_of_le h2 h3)
      _ ≤ plainK U (canonicalObject U c i n) + ((C + K0 : ℕ) : ℕ∞) := by
          gcongr
          exact_mod_cast Nat.le_add_right C K0
  · push Not at hn
    calc (n : ℕ∞) ≤ ((C + K0 : ℕ) : ℕ∞) := by
          exact_mod_cast (by omega : n ≤ C + K0)
      _ = 0 + ((C + K0 : ℕ) : ℕ∞) := (zero_add _).symm
      _ ≤ plainK U (canonicalObject U c i n) + ((C + K0 : ℕ) : ℕ∞) := by
          gcongr
          exact zero_le

private theorem lower_3 (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∃ k : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c 3 n) + (k : ℕ∞) := by
  have hF : Partrec (fun w : BitString =>
      (Part.some (Nat.bits (bigNat c (decodeBits w))) : Part BitString)) :=
    (natBits_computable.comp ((bigNat_primrec c).to_comp.comp decodeBits_computable))
  refine lower_of_partrec U hU c hc 3 _ hF 0
    (fun n => bigNat c (maxHaltingStage c n)) (fun n _ => ?_)
    (fun n _ x hx => lt_bigNat c n hx)
  refine Part.mem_some_iff.mpr ?_
  rw [show canonicalObject U c 3 n = natBits (maxHaltTimeNat c n) from rfl,
    natBits, decodeBits_natBits, maxHaltTime_eq_maxHaltingStage c n]

private theorem lower_0 (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∃ k : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c 0 n) + (k : ℕ∞) := by
  have hcomp : Primrec (fun w : BitString => (decodeListCode w).map decodeFirst) :=
    Primrec.list_map decodeListCode_primrec (decodeFirst_primrec.comp Primrec.snd).to₂
  have hF : Partrec (fun w : BitString =>
      (Part.some (Nat.bits (maxCanon ((decodeListCode w).map decodeFirst) + 1)) :
        Part BitString)) :=
    natBits_computable.comp
      ((Primrec.succ.comp (maxCanon_primrec.comp hcomp)).of_eq (fun _ => rfl)).to_comp
  refine lower_of_partrec U hU c hc 0 _ hF 0
    (fun n => maxCanon (completedBoundedOutput c n) + 1) (fun n _ => ?_) (fun n _ x hx => ?_)
  · refine Part.mem_some_iff.mpr ?_
    rw [show canonicalObject U c 0 n = objComplexityList U c n from rfl,
      decode_objComplexityList U c n]
  · have h1 : Nat.bits x ∈ completedBoundedOutput c n :=
      (mem_boundedNatOutputs_iff_mem_completed c n x).mp hx
    have h2 : x ≤ maxCanon (completedBoundedOutput c n) :=
      le_foldr_max_of_mem ((mem_maxCanonList _ x).mpr h1)
    change x < maxCanon (completedBoundedOutput c n) + 1
    omega

private theorem lower_2 (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∃ k : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c 2 n) + (k : ℕ∞) := by
  obtain ⟨c_len, hlen⟩ := plainK_le_length U hU
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℕ, ∀ n, K0 ≤ n → (boundedNatOutputs c n).Nonempty := by
    have h0 : plainKNat U 0 ≠ ⊤ := by
      have h_top : (((Nat.bits 0).length + c_len : ℕ) : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top _
      intro h_inf
      have h_le := hlen (Nat.bits 0)
      change plainK U (Nat.bits 0) = ⊤ at h_inf
      rw [h_inf] at h_le
      exact h_top (top_le_iff.mp h_le)
    obtain ⟨k0, hk0⟩ := WithTop.ne_top_iff_exists.mp h0
    refine ⟨k0, fun n hn => ⟨0, ?_⟩⟩
    rw [mem_boundedNatOutputs_iff_plainKNat_le hc]
    rw [← hk0]
    exact Nat.cast_le.mpr hn
  have hF : Partrec (fun w : BitString =>
      (Part.some (Nat.bits (bitsToNat w + 1)) : Part BitString)) :=
    natBits_computable.comp
      ((Primrec.succ.comp bitsToNat_primrec).of_eq (fun _ => rfl)).to_comp
  refine lower_of_partrec U hU c hc 2 _ hF K0
    (fun n => (busyBeaver c n).getD 0 + 1) (fun n _ => ?_) (fun n hn x hx => ?_)
  · refine Part.mem_some_iff.mpr ?_
    rw [show canonicalObject U c 2 n = natBits ((busyBeaver c n).getD 0) from rfl,
      natBits, bitsToNat_bits]
  · obtain ⟨b, hb⟩ := busyBeaver_isSome_of_nonempty c n (hK0 n hn)
    have hle := ((busyBeaver_some_iff c n b).mp hb).2 x hx
    change x < (busyBeaver c n).getD 0 + 1
    rw [hb]
    simpa using hle

private theorem rfind_haltList (c : Code) (n : ℕ) :
    Nat.rfind (fun T => Part.some (decide
      ((haltingProgramsBounded c n).countP (fun p => haltsWithin c T p)
        = (haltingProgramsBounded c n).length))) = Part.some (maxHaltingStage c n) := by
  rw [Part.eq_some_iff]
  refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
  · simp only [Part.mem_some_iff]
    symm
    rw [decide_eq_true_iff, List.countP_eq_length]
    intro p hp
    have hp' := (mem_haltingProgramsBounded_iff c n p).mp hp
    exact (halts_maxStage_iff c n hp'.1).mpr hp'.2
  · intro k hk
    simp only [Part.mem_some_iff]
    symm
    rw [decide_eq_false_iff_not, List.countP_eq_length]
    intro hcon
    have hle : maxHaltTimeNat c n ≤ k := by
      unfold maxHaltTimeNat
      refine foldr_max_le_of_forall_mem ?_
      intro a ha
      rw [List.mem_map] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      exact haltTime_le_of_haltsWithin c (hcon p hp)
    rw [maxHaltTime_eq_maxHaltingStage] at hle
    omega

private theorem lower_4 (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∃ k : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c 4 n) + (k : ℕ∞) := by
  have hcount : Primrec (fun z : BitString × ℕ =>
      (decodeListCode z.1).countP (fun p => haltsWithin c z.2 p)) := by
    refine list_countP_primrec (decodeListCode_primrec.comp Primrec.fst) ?_
    exact (Primrec₂.comp (haltsWithin_primrec₂ c)
      (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hpred : Primrec₂ (fun (w : BitString) (T : ℕ) =>
      decide ((decodeListCode w).countP (fun p => haltsWithin c T p)
        = (decodeListCode w).length)) := by
    have hlen : Primrec (fun z : BitString × ℕ => (decodeListCode z.1).length) :=
      Primrec.list_length.comp (decodeListCode_primrec.comp Primrec.fst)
    exact (PrimrecPred.decide (PrimrecRel.comp Primrec.eq hcount hlen)).to₂
  have hF : Partrec (fun w : BitString =>
      (Nat.rfind (fun T => Part.some (decide ((decodeListCode w).countP
        (fun p => haltsWithin c T p) = (decodeListCode w).length)))).map
          (fun T => Nat.bits (bigNat c T))) :=
    (Partrec.rfind hpred.to_comp.partrec₂).map
      (natBits_computable.comp ((bigNat_primrec c).to_comp.comp Computable.snd)).to₂
  refine lower_of_partrec U hU c hc 4 _ hF 0
    (fun n => bigNat c (maxHaltingStage c n)) (fun n _ => ?_)
    (fun n _ x hx => lt_bigNat c n hx)
  change Nat.bits (bigNat c (maxHaltingStage c n)) ∈
    (Nat.rfind (fun T => Part.some (decide ((decodeListCode (canonicalObject U c 4 n)).countP
      (fun p => haltsWithin c T p) = (decodeListCode (canonicalObject U c 4 n)).length)))).map
        (fun T => Nat.bits (bigNat c T))
  rw [show canonicalObject U c 4 n = listCode (haltingProgramsBounded c n) from rfl,
    decodeListCode_listCode, rfind_haltList c n]
  simp

private theorem argmax_haltTime (c : Code) (n : ℕ) {q : BitString}
    (hq : q ∈ haltingProgramsBounded c n)
    (hmax : ∀ p ∈ haltingProgramsBounded c n, haltTimeNat c p ≤ haltTimeNat c q) :
    haltTimeNat c q = maxHaltingStage c n := by
  rw [← maxHaltTime_eq_maxHaltingStage]
  refine le_antisymm ?_ ?_
  · unfold maxHaltTimeNat
    exact le_foldr_max_of_mem (List.mem_map_of_mem hq)
  · unfold maxHaltTimeNat
    refine foldr_max_le_of_forall_mem ?_
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact hmax p hp

private theorem no_output_of_nil (c : Code) (n : ℕ)
    (h : haltingProgramsBounded c n = []) {x : ℕ} (hx : x ∈ boundedNatOutputs c n) : False := by
  have h1 : Nat.bits x ∈ completedBoundedOutput c n :=
    (mem_boundedNatOutputs_iff_mem_completed c n x).mp hx
  set T := maxHaltingStage c n with hT
  have h2 : Nat.bits x ∈ boundedOutputStage c n T := h1
  have h3 : Nat.bits x ∈ snapshotCodes c n T := by
    have hfin : Nat.bits x ∈ (boundedOutputStage c n T).toFinset := List.mem_toFinset.mpr h2
    rw [boundedOutputStage_toFinset_eq_snapshotCodes] at hfin
    exact List.mem_toFinset.mp hfin
  rw [show snapshotCodes c n T = (boundedPrograms n).filterMap (runOut c T) from rfl,
    List.mem_filterMap] at h3
  obtain ⟨p, hp, hrun⟩ := h3
  have hhalt : haltsWithin c T p = true := by
    unfold runOut at hrun
    unfold haltsWithin
    rcases hev : Code.evaln T c (Encodable.encode ((p, ([] : BitString)) : BitString × BitString))
      with _ | r
    · rw [hev] at hrun; simp at hrun
    · rfl
  have hmem : p ∈ haltingProgramsBounded c n :=
    (mem_haltingProgramsBounded_iff c n p).mpr ⟨hp, T, hhalt⟩
  rw [h] at hmem
  simp at hmem

private theorem lower_6 (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∃ k : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c 6 n) + (k : ℕ∞) := by
  by_cases hnil : ∃ t, haltsWithin c t ([] : BitString) = true
  · have hFA : Partrec (fun w : BitString =>
        (Nat.rfind (fun t => Part.some (haltsWithin c t w))).map
          (fun t => Nat.bits (bigNat c t))) := by
      have hpred : Primrec₂ (fun (x : BitString) (s : ℕ) => haltsWithin c s x) :=
        (Primrec₂.comp (haltsWithin_primrec₂ c) Primrec.snd Primrec.fst).to₂
      exact (Partrec.rfind hpred.to_comp.partrec₂).map
        (natBits_computable.comp ((bigNat_primrec c).to_comp.comp Computable.snd)).to₂
    refine lower_of_partrec U hU c hc 6 _ hFA 0
      (fun n => bigNat c (maxHaltingStage c n)) (fun n _ => ?_)
      (fun n _ x hx => lt_bigNat c n hx)
    have hmem0 : ([] : BitString) ∈ haltingProgramsBounded c n :=
      (mem_haltingProgramsBounded_iff c n []).mpr
        ⟨(mem_boundedPrograms_iff [] n).mpr (by simp), hnil⟩
    have hne : haltingProgramsBounded c n ≠ [] := by
      intro h
      rw [h] at hmem0
      simp at hmem0
    obtain ⟨q, hq⟩ : ∃ q, List.argmax (haltTimeNat c) (haltingProgramsBounded c n) = some q := by
      rcases hcase : List.argmax (haltTimeNat c) (haltingProgramsBounded c n) with _ | q
      · exact absurd (List.argmax_eq_none.mp hcase) hne
      · exact ⟨q, rfl⟩
    have hqmem : q ∈ haltingProgramsBounded c n := List.argmax_mem hq
    have hqmax : ∀ p ∈ haltingProgramsBounded c n, haltTimeNat c p ≤ haltTimeNat c q :=
      fun p hp => List.le_of_mem_argmax hp hq
    have hqt : haltTimeNat c q = maxHaltingStage c n := argmax_haltTime c n hqmem hqmax
    have hex : ∃ t, haltsWithin c t q = true :=
      ((mem_haltingProgramsBounded_iff c n q).mp hqmem).2
    have hX : canonicalObject U c 6 n = q := by
      change (List.argmax (haltTimeNat c) (haltingProgramsBounded c n)).getD [] = q
      rw [hq]
      rfl
    change Nat.bits (bigNat c (maxHaltingStage c n)) ∈
      (Nat.rfind (fun t => Part.some (haltsWithin c t (canonicalObject U c 6 n)))).map
        (fun t => Nat.bits (bigNat c t))
    rw [hX, rfind_haltTime c q hex, hqt]
    simp
  · have hFB : Partrec (fun w : BitString =>
        (Nat.rfind (fun t => Part.some (haltsWithin c t w || decide (w = ([] : BitString))))).map
          (fun t => Nat.bits (bigNat c t))) := by
      have h1 : Primrec (fun z : BitString × ℕ => haltsWithin c z.2 z.1) :=
        Primrec₂.comp (haltsWithin_primrec₂ c) Primrec.snd Primrec.fst
      have h2 : Primrec (fun z : BitString × ℕ => decide (z.1 = ([] : BitString))) :=
        PrimrecPred.decide (PrimrecRel.comp Primrec.eq Primrec.fst (Primrec.const []))
      have hpred : Primrec₂ (fun (w : BitString) (t : ℕ) =>
          (haltsWithin c t w || decide (w = ([] : BitString)))) :=
        ((Primrec.cond h1 (Primrec.const true) h2).of_eq (fun _ => rfl)).to₂
      exact (Partrec.rfind hpred.to_comp.partrec₂).map
        (natBits_computable.comp ((bigNat_primrec c).to_comp.comp Computable.snd)).to₂
    refine lower_of_partrec U hU c hc 6 _ hFB 0
      (fun n => if haltingProgramsBounded c n = [] then bigNat c 0
        else bigNat c (maxHaltingStage c n)) (fun n _ => ?_) (fun n _ x hx => ?_)
    · by_cases hnl : haltingProgramsBounded c n = []
      · have hX : canonicalObject U c 6 n = ([] : BitString) := by
          change (List.argmax (haltTimeNat c) (haltingProgramsBounded c n)).getD [] = []
          rw [hnl]
          rfl
        change Nat.bits (if haltingProgramsBounded c n = [] then bigNat c 0
            else bigNat c (maxHaltingStage c n)) ∈
          (Nat.rfind (fun t => Part.some (haltsWithin c t (canonicalObject U c 6 n) ||
            decide (canonicalObject U c 6 n = ([] : BitString))))).map
            (fun t => Nat.bits (bigNat c t))
        rw [hX, if_pos hnl]
        have hrf : Nat.rfind (fun t => Part.some
            (haltsWithin c t ([] : BitString) || decide (([] : BitString) = ([] : BitString))))
            = Part.some 0 := by
          rw [Part.eq_some_iff]
          refine Nat.mem_rfind.mpr ⟨by simp, ?_⟩
          intro k hk
          exact absurd hk (Nat.not_lt_zero k)
        rw [hrf]
        simp
      · obtain ⟨q, hq⟩ :
            ∃ q, List.argmax (haltTimeNat c) (haltingProgramsBounded c n) = some q := by
          rcases hcase : List.argmax (haltTimeNat c) (haltingProgramsBounded c n) with _ | q
          · exact absurd (List.argmax_eq_none.mp hcase) hnl
          · exact ⟨q, rfl⟩
        have hqmem : q ∈ haltingProgramsBounded c n := List.argmax_mem hq
        have hex : ∃ t, haltsWithin c t q = true :=
          ((mem_haltingProgramsBounded_iff c n q).mp hqmem).2
        have hqne : q ≠ ([] : BitString) := by
          intro hqeq
          rw [hqeq] at hex
          exact hnil hex
        have hqmax : ∀ p ∈ haltingProgramsBounded c n, haltTimeNat c p ≤ haltTimeNat c q :=
          fun p hp => List.le_of_mem_argmax hp hq
        have hqt : haltTimeNat c q = maxHaltingStage c n := argmax_haltTime c n hqmem hqmax
        have hX : canonicalObject U c 6 n = q := by
          change (List.argmax (haltTimeNat c) (haltingProgramsBounded c n)).getD [] = q
          rw [hq]
          rfl
        change Nat.bits (if haltingProgramsBounded c n = [] then bigNat c 0
            else bigNat c (maxHaltingStage c n)) ∈
          (Nat.rfind (fun t => Part.some (haltsWithin c t (canonicalObject U c 6 n) ||
            decide (canonicalObject U c 6 n = ([] : BitString))))).map
            (fun t => Nat.bits (bigNat c t))
        rw [hX, if_neg hnl]
        have hsimp : (fun t => Part.some (haltsWithin c t q || decide (q = ([] : BitString))))
            = (fun t => Part.some (haltsWithin c t q)) := by
          funext t
          rw [decide_eq_false hqne, Bool.or_false]
        rw [hsimp, rfind_haltTime c q hex, hqt]
        simp
    · by_cases hnl : haltingProgramsBounded c n = []
      · exact (no_output_of_nil c n hnl hx).elim
      · rw [if_neg hnl]
        exact lt_bigNat c n hx

private theorem lower_mono {U : Map} {c : Code} {i k k' : ℕ} (h : k ≤ k')
    (H : ∀ n : ℕ, (n : ℕ∞) ≤ plainK U (canonicalObject U c i n) + (k : ℕ∞)) :
    ∀ n : ℕ, (n : ℕ∞) ≤ plainK U (canonicalObject U c i n) + (k' : ℕ∞) := by
  intro n
  refine (H n).trans ?_
  gcongr

/-- **Theorem 15, lower half.** -/
private theorem lower (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) :
    ∃ k : ℕ, ∀ i, i ≤ 8 → ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c i n) + (k : ℕ∞) := by
  obtain ⟨k0, h0⟩ := lower_0 U hU c hc
  obtain ⟨k1, h1⟩ := lower_1 U hU c hc
  obtain ⟨k2, h2⟩ := lower_2 U hU c hc
  obtain ⟨k3, h3⟩ := lower_3 U hU c hc
  obtain ⟨k4, h4⟩ := lower_4 U hU c hc
  obtain ⟨k5, h5⟩ := lower_5 U hU c hc
  obtain ⟨k6, h6⟩ := lower_6 U hU c hc
  obtain ⟨k7, h7⟩ := lower_7 U hU c hc
  obtain ⟨k8, h8⟩ := lower_8 U hU c hc
  refine ⟨k0 + k1 + k2 + k3 + k4 + k5 + k6 + k7 + k8, fun i hi => ?_⟩
  interval_cases i
  · exact lower_mono (by omega) h0
  · exact lower_mono (by omega) h1
  · exact lower_mono (by omega) h2
  · exact lower_mono (by omega) h3
  · exact lower_mono (by omega) h4
  · exact lower_mono (by omega) h5
  · exact lower_mono (by omega) h6
  · exact lower_mono (by omega) h7
  · exact lower_mono (by omega) h8

/-- **Theorem 15, complexity half.** Each of the nine canonical objects has
complexity `n + O(1)`. -/
theorem canonicalObject_complexity_eq (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) :
    ∃ k : ℕ, ∀ i ≤ 8, ∀ n : ℕ,
      plainK U (canonicalObject U c i n) ≤ ((n + k : ℕ) : ℕ∞) ∧
        (n : ℕ∞) ≤ plainK U (canonicalObject U c i n) + (k : ℕ∞) := by
  obtain ⟨ku, hu⟩ := upper U hU c hc
  obtain ⟨kl, hl⟩ := lower U hU c hc
  refine ⟨ku + kl, fun i hi n => ⟨?_, ?_⟩⟩
  · exact upper_mono (by omega) (hu i hi) n
  · exact lower_mono (by omega) (hl i hi) n

/-- **Theorem 15, equivalence half.** From `n` and any one of the nine objects at
parameter `n`, a partial computable function produces any other of them at a
constantly shifted parameter. -/
theorem canonicalObject_mutual_reduction (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) :
    ∀ i ≤ 8, ∀ j ≤ 8, ∃ k : ℕ, ∃ A : ℕ × BitString →. BitString, Partrec A ∧
      ∀ n : ℕ,
        A (n, canonicalObject U c i n) = Part.some (canonicalObject U c j (n - k)) := by
  exact fun i hi j hj =>
    (hub_in U hU c hc i hi).trans' (hub_out U hU c hc j hj)

/-- (a) → (e). -/
private theorem canonicalReduces_complexityList_haltingList (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) : CanonicalObjectReduces U c 0 4 :=
  complexityList_reduces_haltingList U hU c hc

/-- (b) → (e). -/
private theorem canonicalReduces_complexityCount_haltingList (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) : CanonicalObjectReduces U c 1 4 :=
  complexityCount_reduces_haltingList U hU c hc

/-- (c) → (e). -/
private theorem canonicalReduces_busyBeaver_haltingList (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) : CanonicalObjectReduces U c 2 4 :=
  busyBeaver_reduces_haltingList U hU c hc

/-- (d) → (e). -/
private theorem canonicalReduces_maxTime_haltingList (U : Map) (c : Code) :
    CanonicalObjectReduces U c 3 4 :=
  maxTime_reduces_haltingList U c

/-- (f) → (e). -/
private theorem canonicalReduces_haltingCount_haltingList (U : Map) (c : Code) :
    CanonicalObjectReduces U c 5 4 :=
  haltingCount_reduces_haltingList U c

/-- (g) → (e). -/
private theorem canonicalReduces_slowestProgram_haltingList (U : Map) (c : Code) :
    CanonicalObjectReduces U c 6 4 :=
  slowestProgram_reduces_haltingList U c

/-- (h) → (e). -/
private theorem canonicalReduces_complexityGraph_haltingList (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) : CanonicalObjectReduces U c 7 4 :=
  complexityGraph_reduces_haltingList U hU c hc

/-- (i) → (e).  This is the hard direction of Theorem 15: from the lexicographically
first incompressible string of length `n` one recovers the halting problem for the
optimal decompressor on inputs of length at most `n - O(1)`. -/
private theorem canonicalReduces_firstIncompressible_haltingList (U : Map)
    (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) : CanonicalObjectReduces U c 8 4 :=
  firstIncompressible_reduces_haltingList U hU c hc

/-- (e) → (a). -/
private theorem canonicalReduces_haltingList_complexityList (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) : CanonicalObjectReduces U c 4 0 :=
  haltingList_reduces_complexityList U hU c hc

/-- (e) → (b). -/
private theorem canonicalReduces_haltingList_complexityCount (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) : CanonicalObjectReduces U c 4 1 :=
  haltingList_reduces_complexityCount U hU c hc

/-- (e) → (c). -/
private theorem canonicalReduces_haltingList_busyBeaver (U : Map) (c : Code) :
    CanonicalObjectReduces U c 4 2 :=
  haltingList_reduces_busyBeaver U c

/-- (e) → (d). -/
private theorem canonicalReduces_haltingList_maxTime (U : Map) (c : Code) :
    CanonicalObjectReduces U c 4 3 :=
  haltingList_reduces_maxTime U c

/-- (e) → (h). -/
private theorem canonicalReduces_haltingList_complexityGraph (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) : CanonicalObjectReduces U c 4 7 :=
  haltingList_reduces_complexityGraph U hU c hc

/-- (e) → (i). -/
private theorem canonicalReduces_haltingList_firstIncompressible (U : Map)
    (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) : CanonicalObjectReduces U c 4 8 :=
  haltingList_reduces_firstIncompressible U hU c hc

/-- (e) → (g). -/
private theorem canonicalReduces_haltingList_slowestProgram (U : Map) (c : Code) :
    CanonicalObjectReduces U c 4 6 :=
  haltingList_reduces_slowestProgram U c

end Kolmogorov
