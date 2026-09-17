import KolmogorovMathlib.Foundation.ListUtil
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

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-! #### The individual hub edges of Theorem 15

Each of the following is one of the eighteen reductions between a canonical object
and the hub object (the list of halting programs).  They are proved from the
primitive reductions established above and composed with `CanonicalObjectReduces.trans`. -/

/-- A program of length at most `m` halts at all if and only if it halts by the maximal
halting stage of the level `m`. -/
theorem halts_maxStage_iff (c : Code) (m : ℕ) {p : BitString}
    (hp : p ∈ boundedPrograms m) :
    haltsWithin c (maxHaltingStage c m) p = true ↔ ∃ t, haltsWithin c t p = true := by
  refine ⟨fun h => ⟨_, h⟩, ?_⟩
  rintro ⟨t, ht⟩
  by_contra hcon
  rw [Bool.not_eq_true] at hcon
  have hlt : countHalts c m (maxHaltingStage c m) <
      countHalts c m (max (maxHaltingStage c m) t) := by
    unfold countHalts
    exact countP_lt_of_witness hp hcon (haltsWithin_mono c (le_max_right _ _) p ht)
      (fun q _ hq => haltsWithin_mono c (le_max_left _ _) q hq)
  have hmax := maxHaltingStage_spec c m (max (maxHaltingStage c m) t)
  omega

/-- Membership in the list of halting programs of length at most `m`. -/
theorem mem_haltingProgramsBounded_iff (c : Code) (m : ℕ) (p : BitString) :
    p ∈ haltingProgramsBounded c m ↔ p ∈ boundedPrograms m ∧ ∃ t, haltsWithin c t p = true := by
  unfold haltingProgramsBounded
  rw [List.mem_filter]
  exact ⟨fun h => ⟨h.1, (halts_maxStage_iff c m h.1).mp h.2⟩,
    fun h => ⟨h.1, (halts_maxStage_iff c m h.1).mpr h.2⟩⟩

/-- A common bound on the entries of a list bounds their maximum. -/
theorem foldr_max_le_of_forall_mem {l : List ℕ} {M : ℕ} (h : ∀ a ∈ l, a ≤ M) :
    l.foldr max 0 ≤ M :=
  foldr_max_le_of_forall_le h

open Classical in
/-- The largest halting time among the halting programs of length at most `m` is the
maximal halting stage of that level. -/
theorem maxHaltTime_eq_maxHaltingStage (c : Code) (m : ℕ) :
    maxHaltTimeNat c m = maxHaltingStage c m := by
  refine le_antisymm ?_ ?_
  · unfold maxHaltTimeNat
    refine foldr_max_le_of_forall_mem ?_
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    have hp' := (mem_haltingProgramsBounded_iff c m p).mp hp
    exact haltTime_le_of_haltsWithin c ((halts_maxStage_iff c m hp'.1).mpr hp'.2)
  · have hmax : ∀ t', countHalts c m t' ≤ countHalts c m (maxHaltTimeNat c m) := by
      intro t'
      unfold countHalts
      refine List.countP_mono_left ?_
      intro p hp hpt
      have hmem : p ∈ haltingProgramsBounded c m :=
        (mem_haltingProgramsBounded_iff c m p).mpr ⟨hp, t', hpt⟩
      have hle : haltTimeNat c p ≤ maxHaltTimeNat c m := by
        unfold maxHaltTimeNat
        exact le_foldr_max_of_mem (List.mem_map_of_mem hmem)
      exact haltsWithin_mono c hle p (haltsWithin_haltTime c ⟨t', hpt⟩)
    unfold maxHaltingStage
    exact Nat.find_min' _ hmax

/-- Past the maximal halting stage, filtering the programs of length at most `m` by
halting within `T` steps yields exactly the halting ones. -/
theorem filter_haltsWithin_eq_haltingProgramsBounded (c : Code) (m T : ℕ)
    (hT : maxHaltingStage c m ≤ T) :
    (boundedPrograms m).filter (fun p => haltsWithin c T p) = haltingProgramsBounded c m := by
  unfold haltingProgramsBounded
  refine List.filter_congr (fun x hx => ?_)
  rw [Bool.eq_iff_iff]
  exact ⟨fun h => (halts_maxStage_iff c m hx).mpr ⟨T, h⟩,
    fun h => haltsWithin_mono c hT x h⟩

/-- Halting within a given number of steps is primitive recursive in the stage and the
program. -/
theorem haltsWithin_primrec₂ (c : Code) :
    Primrec₂ (fun (t : ℕ) (p : BitString) => haltsWithin c t p) := by
  have h : Primrec (fun q : ℕ × BitString =>
      Code.evaln q.1 c (Encodable.encode ((q.2, ([] : BitString)) : BitString × BitString))) :=
    Primrec₂.comp (evaln_primrec c) Primrec.fst
      (Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.const ([] : BitString))))
  exact (Primrec.option_isSome.comp h).to₂
/-- The canonical object `i` reduces to the canonical object `j`: some partial computable
map sends the object `i` at parameter `n` to the object `j` at parameter `n - k`, for a
constant `k`. -/
def HubReduces (U : Map) (c : Code) (i j : ℕ) : Prop :=
  ∃ k : ℕ, ∃ A : ℕ × BitString →. BitString, Partrec A ∧
    ∀ n : ℕ, A (n, canonicalObject U c i n) = Part.some (canonicalObject U c j (n - k))

/-- Reductions between canonical objects compose: the constants add. -/
theorem HubReduces.trans' {U : Map} {c : Code} {i j l : ℕ}
    (h1 : HubReduces U c i j) (h2 : HubReduces U c j l) : HubReduces U c i l := by
  obtain ⟨k1, A1, hA1p, hA1⟩ := h1
  obtain ⟨k2, A2, hA2p, hA2⟩ := h2
  refine ⟨k1 + k2, fun p => (A1 p).bind (fun y => A2 (p.1 - k1, y)), ?_, ?_⟩
  · refine hA1p.bind ?_
    have hfst : Computable (fun q : (ℕ × BitString) × BitString => q.1.1 - k1) :=
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.const k1)).to_comp
    exact (hA2p.comp (Computable.pair hfst Computable.snd)).to₂
  · intro n
    simp only [hA1 n, Part.bind_some]
    rw [hA2 (n - k1), Nat.sub_sub]

private theorem rfind_countHalts (c : Code) (n : ℕ) :
    Nat.rfind (fun T => Part.some
        (decide (countHalts c n T = (haltingProgramsBounded c n).length))) =
      Part.some (maxHaltingStage c n) := by
  rw [Part.eq_some_iff]
  refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
  · simp only [Part.mem_some_iff]
    rw [countHalts_maxHaltingStage c n]
    simp
  · intro k hk
    simp only [Part.mem_some_iff]
    symm
    rw [decide_eq_false_iff_not]
    intro hcon
    have hle := maxHaltingStage_le_of_countHalts_eq c n k hcon
    omega

private theorem hubReduces_maxTime (U : Map) (c : Code) (i : ℕ)
    (g : BitString → ℕ) (hg : Primrec g)
    (hgspec : ∀ n : ℕ, g (canonicalObject U c i n) = (haltingProgramsBounded c n).length) :
    HubReduces U c i 3 := by
  have hpred : Primrec₂ (fun (q : ℕ × BitString) (T : ℕ) =>
      decide (countHalts c q.1 T = g q.2)) := by
    have h1 : Primrec (fun z : (ℕ × BitString) × ℕ => countHalts c z.1.1 z.2) :=
      (countHalts_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
    have h2 : Primrec (fun z : (ℕ × BitString) × ℕ => g z.1.2) :=
      hg.comp (Primrec.snd.comp Primrec.fst)
    have h3 : Primrec (fun z : (ℕ × BitString) × ℕ =>
        decide (countHalts c z.1.1 z.2 = g z.1.2)) :=
      PrimrecPred.decide (PrimrecRel.comp Primrec.eq h1 h2)
    exact h3.to₂
  refine ⟨0, fun q =>
    (Nat.rfind (fun T => Part.some (decide (countHalts c q.1 T = g q.2)))).map natBits,
    ?_, ?_⟩
  · exact (Partrec.rfind hpred.to_comp.partrec₂).map
      (natBits_computable.comp Computable.snd).to₂
  · intro n
    simp only [Nat.sub_zero, hgspec n]
    rw [rfind_countHalts c n]
    simp only [Part.map_some]
    rw [show canonicalObject U c 3 n = natBits (maxHaltTimeNat c n) from rfl,
      maxHaltTime_eq_maxHaltingStage c n]

/-- From the number of halting programs of length at most `n` at parameter `n` one computes the
maximal halting time of the programs of length at most `n` at parameter `n - O(1)`. SUV
Theorem 15. -/
theorem haltingCount_reduces_maxTime (U : Map) (c : Code) : HubReduces U c 5 3 :=
  hubReduces_maxTime U c 5 decodeBits primrec_decodeBits (fun n => by
    simp only [canonicalObject, objHaltingCount, natBits, decodeBits_natBits])

/-- From the list of halting programs of length at most `n` at parameter `n` one computes the
maximal halting time of the programs of length at most `n` at parameter `n - O(1)`. SUV
Theorem 15. -/
theorem haltingList_reduces_maxTime (U : Map) (c : Code) : HubReduces U c 4 3 :=
  hubReduces_maxTime U c 4 (fun w => (decodeListCode w).length)
    (Primrec.list_length.comp decodeListCode_primrec) (fun n => by
      simp only [canonicalObject, objHaltingList, decodeListCode_listCode])

/-- From the maximal halting time of the programs of length at most `n` at parameter `n` one
computes the list of halting programs of length at most `n` at parameter `n - O(1)`. SUV
Theorem 15. -/
theorem maxTime_reduces_haltingList (U : Map) (c : Code) : HubReduces U c 3 4 := by
  have hfilter : Primrec (fun q : ℕ × BitString =>
      (boundedPrograms q.1).filter (fun p => haltsWithin c (decodeBits q.2) p)) := by
    refine list_filter_primrec (primrec_boundedPrograms.comp Primrec.fst) ?_
    exact (haltsWithin_primrec₂ c).comp
      (primrec_decodeBits.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  refine ⟨0, fun q => Part.some (listCode ((boundedPrograms q.1).filter
    (fun p => haltsWithin c (decodeBits q.2) p))), (listCode_primrec.comp hfilter).to_comp,
    fun n => ?_⟩
  simp only [Nat.sub_zero, canonicalObject, objMaxTime, objHaltingList, natBits,
    decodeBits_natBits, maxHaltTime_eq_maxHaltingStage c n]
  rw [filter_haltsWithin_eq_haltingProgramsBounded c n (maxHaltingStage c n) le_rfl]
/-- The numbers read off a list of strings are exactly those whose binary expansion
occurs in the list. -/
theorem mem_maxCanonList (L : List BitString) (x : ℕ) :
    x ∈ (L.filter (fun w => decide (Nat.bits (bitsToNat w) = w))).map bitsToNat ↔
      Nat.bits x ∈ L := by
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨w, ⟨hw, hcanon⟩, rfl⟩
    rwa [hcanon]
  · intro h
    exact ⟨Nat.bits x, ⟨h, by rw [bitsToNat_bits]⟩, bitsToNat_bits x⟩

/-- The largest number whose binary expansion occurs in the given list of strings. -/
def maxCanon (L : List BitString) : ℕ :=
  ((L.filter (fun w => decide (Nat.bits (bitsToNat w) = w))).map bitsToNat).foldr max 0

/-- Reading off the largest number coded in a list of strings is primitive recursive. -/
theorem maxCanon_primrec : Primrec maxCanon := by
  have hp : Primrec₂ (fun (_ : List BitString) (w : BitString) =>
      decide (Nat.bits (bitsToNat w) = w)) := by
    have h : Primrec (fun z : List BitString × BitString =>
        decide (Nat.bits (bitsToNat z.2) = z.2)) :=
      PrimrecPred.decide (PrimrecRel.comp Primrec.eq
        (primrec_natBits.comp (bitsToNat_primrec.comp Primrec.snd)) Primrec.snd)
    exact h.to₂
  have hfilter : Primrec (fun L : List BitString =>
      L.filter (fun w => decide (Nat.bits (bitsToNat w) = w))) :=
    list_filter_primrec Primrec.id hp
  have hmap : Primrec (fun L : List BitString =>
      (L.filter (fun w => decide (Nat.bits (bitsToNat w) = w))).map bitsToNat) :=
    Primrec.list_map hfilter (bitsToNat_primrec.comp Primrec.snd).to₂
  have hstep : Primrec₂ (fun (_ : List BitString) (p : ℕ × ℕ) => max p.1 p.2) := by
    have h : Primrec (fun z : List BitString × (ℕ × ℕ) => z.2.1 + (z.2.2 - z.2.1)) :=
      Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
    have h2 : Primrec (fun z : List BitString × (ℕ × ℕ) => max z.2.1 z.2.2) :=
      h.of_eq (fun z => by omega)
    exact h2.to₂
  exact (Primrec.list_foldr hmap (Primrec.const 0) hstep).of_eq (fun L => rfl)

/-- Dropping the complexity components of the complexity list leaves the completed
bounded output of the level. -/
theorem decode_objComplexityList (U : Map) (c : Code) (n : ℕ) :
    (decodeListCode (objComplexityList U c n)).map decodeFirst = completedBoundedOutput c n := by
  unfold objComplexityList
  rw [decodeListCode_listCode, List.map_map]
  refine Eq.trans (List.map_congr_left ?_) (List.map_id _)
  intro x _
  exact decodeFirst_pairCode x _

private theorem maxCanon_completed (c : Code) (m : ℕ) :
    maxCanon (completedBoundedOutput c m) = (busyBeaver c m).getD 0 := by
  have hmem : ∀ x : ℕ,
      x ∈ ((completedBoundedOutput c m).filter
        (fun w => decide (Nat.bits (bitsToNat w) = w))).map bitsToNat ↔
      x ∈ boundedNatOutputs c m := fun x => by
    rw [mem_maxCanonList, mem_boundedNatOutputs_iff_mem_completed]
  rcases Option.eq_none_or_eq_some (busyBeaver c m) with hn | ⟨b, hb⟩
  · rw [hn]
    have hempty : boundedNatOutputs c m = ∅ := (busyBeaver_eq_none_iff c m).mp hn
    have hnil : ((completedBoundedOutput c m).filter
        (fun w => decide (Nat.bits (bitsToNat w) = w))).map bitsToNat = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      have hx' := (hmem x).mp hx
      rw [hempty] at hx'
      simp at hx'
    unfold maxCanon
    rw [hnil]
    rfl
  · rw [hb]
    obtain ⟨hbmem, hbmax⟩ := (busyBeaver_some_iff c m b).mp hb
    unfold maxCanon
    simp only [Option.getD_some]
    exact le_antisymm (foldr_max_le_of_forall_mem (fun a ha => hbmax a ((hmem a).mp ha)))
      (le_foldr_max_of_mem ((hmem b).mpr hbmem))

/-- From the maximal halting time of the programs of length at most `n` at parameter `n` one
computes the busy-beaver value at parameter `n - O(1)`. SUV Theorem 15. -/
theorem maxTime_reduces_busyBeaver (U : Map) (c : Code) : HubReduces U c 3 2 := by
  have hstage : Primrec (fun q : ℕ × BitString =>
      boundedOutputStage c q.1 (decodeBits q.2)) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair Primrec.fst (primrec_decodeBits.comp Primrec.snd))
  refine ⟨0, fun q => Part.some (natBits (maxCanon
    (boundedOutputStage c q.1 (decodeBits q.2)))),
    (primrec_natBits.comp (maxCanon_primrec.comp hstage)).to_comp, fun n => ?_⟩
  simp only [Nat.sub_zero, canonicalObject, objMaxTime, objBusyBeaver, natBits,
    decodeBits_natBits, maxHaltTime_eq_maxHaltingStage c n]
  rw [show boundedOutputStage c n (maxHaltingStage c n) = completedBoundedOutput c n from rfl,
    maxCanon_completed c n]

private theorem rfind_map_eq {p : ℕ → Prop} [DecidablePred p] {f : ℕ → BitString}
    {v : BitString} (T : ℕ) (hT : p T) (hf : ∀ s, p s → f s = v) :
    (Nat.rfind (fun s => Part.some (decide (p s)))).map f = Part.some v := by
  have hex : ∃ s, p s := ⟨T, hT⟩
  have hmem : Nat.find hex ∈ Nat.rfind (fun s => Part.some (decide (p s))) := by
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · simp only [Part.mem_some_iff]
      symm
      rw [decide_eq_true_iff]
      exact Nat.find_spec hex
    · intro k hk
      simp only [Part.mem_some_iff]
      symm
      rw [decide_eq_false_iff_not]
      exact Nat.find_min hex hk
  rw [Part.eq_some_iff, Part.mem_map_iff]
  exact ⟨Nat.find hex, hmem, hf _ (Nat.find_spec hex)⟩

private theorem stage_eq_of_length (c : Code) (n T : ℕ)
    (h : (boundedOutputStage c n T).length = (completedBoundedOutput c n).length) :
    boundedOutputStage c n T = completedBoundedOutput c n :=
  boundedOutputStage_eq_completed_of_completion_le c n T
    (boundedOutputCompletionTime_le_complete_stage c n T h)

/-- From the number of strings of complexity at most `n` at parameter `n` one computes the
busy-beaver value at parameter `n - O(1)`. SUV Theorem 15. -/
theorem complexityCount_reduces_busyBeaver (U : Map) (c : Code) : HubReduces U c 1 2 := by
  have hstage : Primrec (fun z : (ℕ × BitString) × ℕ =>
      boundedOutputStage c z.1.1 z.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hpred : Primrec₂ (fun (q : ℕ × BitString) (T : ℕ) =>
      decide ((boundedOutputStage c q.1 T).length = decodeBits q.2)) := by
    have h1 : Primrec (fun z : (ℕ × BitString) × ℕ =>
        (boundedOutputStage c z.1.1 z.2).length) := Primrec.list_length.comp hstage
    have h2 : Primrec (fun z : (ℕ × BitString) × ℕ => decodeBits z.1.2) :=
      primrec_decodeBits.comp (Primrec.snd.comp Primrec.fst)
    exact (PrimrecPred.decide (PrimrecRel.comp Primrec.eq h1 h2)).to₂
  have hmapf : Computable₂ (fun (q : ℕ × BitString) (T : ℕ) =>
      natBits (maxCanon (boundedOutputStage c q.1 T))) :=
    ((primrec_natBits.comp (maxCanon_primrec.comp hstage)).to_comp).to₂
  refine ⟨0, fun q =>
    (Nat.rfind (fun T => Part.some
      (decide ((boundedOutputStage c q.1 T).length = decodeBits q.2)))).map
        (fun T => natBits (maxCanon (boundedOutputStage c q.1 T))),
    (Partrec.rfind hpred.to_comp.partrec₂).map hmapf, fun n => ?_⟩
  simp only [Nat.sub_zero, canonicalObject, objComplexityCount, objBusyBeaver, natBits,
    decodeBits_natBits]
  refine rfind_map_eq (maxHaltingStage c n) rfl ?_
  intro s hs
  rw [stage_eq_of_length c n s hs, maxCanon_completed c n]

/-- From the list of strings of complexity at most `n` at parameter `n` one computes the
busy-beaver value at parameter `n - O(1)`. SUV Theorem 15. -/
theorem complexityList_reduces_busyBeaver (U : Map) (c : Code) : HubReduces U c 0 2 := by
  have hcomp : Primrec (fun q : ℕ × BitString =>
      (decodeListCode q.2).map decodeFirst) :=
    Primrec.list_map (decodeListCode_primrec.comp Primrec.snd)
      (decodeFirst_primrec.comp Primrec.snd).to₂
  refine ⟨0, fun q => Part.some (natBits (maxCanon
    ((decodeListCode q.2).map decodeFirst))),
    (primrec_natBits.comp (maxCanon_primrec.comp hcomp)).to_comp, fun n => ?_⟩
  simp only [Nat.sub_zero, canonicalObject, objBusyBeaver]
  rw [decode_objComplexityList U c n, maxCanon_completed c n]

private theorem foldr_min_le {l : List ℕ} {d a : ℕ} (h : a ∈ l) :
    l.foldr min d ≤ a := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih h')

private theorem le_foldr_min {l : List ℕ} {d M : ℕ} (h : ∀ a ∈ l, M ≤ a) (hd : M ≤ d) :
    M ≤ l.foldr min d := by
  induction l with
  | nil => simpa using hd
  | cons b t ih =>
    simp only [List.foldr_cons]
    exact le_min (h b (List.mem_cons_self ..))
      (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- The minimal length of a program of length at most `n` that outputs `x`
within `T` steps (`n + 1` if there is none). -/
private def cValUpTo (c : Code) (n T : ℕ) (x : BitString) : ℕ :=
  (((boundedPrograms n).filter (fun p => decide (runOut c T p = some x))).map List.length).foldr
    min (n + 1)

private theorem runOut_primrec (c : Code) :
    Primrec₂ (fun (t : ℕ) (p : BitString) => runOut c t p) := by
  have h : Primrec (fun q : ℕ × BitString => runOut c q.1 q.2) := by
    refine Primrec.option_bind ?_ ?_
    · exact (evaln_primrec c).comp Primrec.fst
        (Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.const ([] : BitString))))
    · exact Primrec.decode.comp Primrec.snd
  exact h.to₂

private theorem cValUpTo_primrec (c : Code) :
    Primrec (fun q : (ℕ × ℕ) × BitString => cValUpTo c q.1.1 q.1.2 q.2) := by
  have hfilter : Primrec (fun q : (ℕ × ℕ) × BitString =>
      (boundedPrograms q.1.1).filter (fun p => decide (runOut c q.1.2 p = some q.2))) := by
    refine list_filter_primrec (primrec_boundedPrograms.comp (Primrec.fst.comp Primrec.fst)) ?_
    have hrun : Primrec (fun z : ((ℕ × ℕ) × BitString) × BitString =>
        runOut c z.1.1.2 z.2) :=
      (runOut_primrec c).comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd
    have hx : Primrec (fun z : ((ℕ × ℕ) × BitString) × BitString =>
        (some z.1.2 : Option BitString)) :=
      Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)
    exact (PrimrecPred.decide (PrimrecRel.comp Primrec.eq hrun hx)).to₂
  have hmap : Primrec (fun q : (ℕ × ℕ) × BitString =>
      ((boundedPrograms q.1.1).filter
        (fun p => decide (runOut c q.1.2 p = some q.2))).map List.length) :=
    Primrec.list_map hfilter (Primrec.list_length.comp Primrec.snd).to₂
  have hstep : Primrec₂ (fun (_ : (ℕ × ℕ) × BitString) (z : ℕ × ℕ) => min z.1 z.2) := by
    have h : Primrec (fun w : ((ℕ × ℕ) × BitString) × (ℕ × ℕ) => min w.2.1 w.2.2) :=
      Primrec.nat_min.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    exact h
  exact Primrec.list_foldr hmap
    (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)) hstep

/-- **Key lemma.** Past the completed halting stage for length-`n` programs, the
bounded search `cValUpTo` computes the true complexity of every string of
complexity at most `n`. -/
private theorem cValUpTo_eq (U : Map) (c : Code) (hc : IsCodeFor c U) (n T : ℕ)
    (hT : maxHaltingStage c n ≤ T) (x : BitString) (hx : plainK U x ≤ (n : ℕ∞)) :
    cValUpTo c n T x = cVal U x := by
  have hne : plainK U x ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hx
    exact ENat.natCast_ne_top n hx
  have hplain : plainK U x = ((cVal U x : ℕ) : ℕ∞) := (ENat.natCast_toNat hne).symm
  have hLn : cVal U x ≤ n := by
    have h2 : ((cVal U x : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := hplain ▸ hx
    exact_mod_cast h2
  -- (a) the search finds a program of length at most `cVal U x`
  obtain ⟨p, hplen, hprod⟩ := (condK_le_iff U x [] (cVal U x)).mp (le_of_eq hplain)
  have hplen' : p.length ≤ cVal U x := hplen
  have hpmem : p ∈ boundedPrograms n :=
    (mem_boundedPrograms_iff p n).mpr (le_trans hplen' hLn)
  obtain ⟨t, ht⟩ := runOut_complete hc hprod
  obtain ⟨a, ha, hadec⟩ : ∃ a, Code.evaln t c
      (Encodable.encode ((p, ([] : BitString)) : BitString × BitString)) = some a ∧
      (Encodable.decode a : Option BitString) = some x := by
    have h := ht
    unfold runOut at h
    rw [Option.bind_eq_some_iff] at h
    exact h
  have hhalt_t : haltsWithin c t p = true := by
    unfold haltsWithin
    rw [ha]
    rfl
  have hhaltT : haltsWithin c T p = true :=
    haltsWithin_mono c hT p ((halts_maxStage_iff c n hpmem).mpr ⟨t, hhalt_t⟩)
  obtain ⟨r, hr⟩ : ∃ r, Code.evaln T c
      (Encodable.encode ((p, ([] : BitString)) : BitString × BitString)) = some r := by
    unfold haltsWithin at hhaltT
    exact Option.isSome_iff_exists.mp hhaltT
  have har : a = r := by
    have h1 := Nat.Partrec.Code.evaln_mono (le_max_left t T) ha
    have h2 := Nat.Partrec.Code.evaln_mono (le_max_right t T) hr
    have h3 := h1.symm.trans h2
    exact Option.some.inj h3
  have hrunT : runOut c T p = some x := by
    unfold runOut
    rw [hr, ← har]
    exact hadec
  have hmemfilter : p ∈ (boundedPrograms n).filter
      (fun q => decide (runOut c T q = some x)) := by
    rw [List.mem_filter]
    exact ⟨hpmem, by simp [hrunT]⟩
  have hle : cValUpTo c n T x ≤ p.length :=
    foldr_min_le (List.mem_map_of_mem hmemfilter)
  -- (b) every program the search finds is at least as long as `cVal U x`
  have hge : cVal U x ≤ cValUpTo c n T x := by
    refine le_foldr_min ?_ (by omega)
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨q, hq, rfl⟩ := hb
    rw [List.mem_filter] at hq
    have hrunq : runOut c T q = some x := of_decide_eq_true hq.2
    have hprodq : produces U q [] x := runOut_sound hc hrunq
    have hqle : plainK U x ≤ ((q.length : ℕ) : ℕ∞) :=
      (condK_le_iff U x [] q.length).mpr ⟨q, le_rfl, hprodq⟩
    rw [hplain] at hqle
    exact_mod_cast hqle
  omega

private theorem pairMap_primrec (c : Code)
    {α : Type} [Primcodable α] {u : α → ℕ} {v : α → ℕ} (hu : Primrec u) (hv : Primrec v) :
    Primrec₂ (fun (a : α) (x : BitString) =>
      pairCode x (natBits (cValUpTo c (u a) (v a) x))) := by
  have hval : Primrec (fun z : α × BitString =>
      cValUpTo c (u z.1) (v z.1) z.2) :=
    (cValUpTo_primrec c).comp
      (Primrec.pair (Primrec.pair (hu.comp Primrec.fst) (hv.comp Primrec.fst)) Primrec.snd)
  have hbits : Primrec (fun z : α × BitString =>
      natBits (cValUpTo c (u z.1) (v z.1) z.2)) :=
    primrec_natBits.comp hval
  exact (pairCode_primrec.comp Primrec.snd hbits).to₂

/-- From the maximal halting time of the programs of length at most `n` at parameter `n` one
computes the list of strings of complexity at most `n` at parameter `n - O(1)`. SUV Theorem
15. -/
theorem maxTime_reduces_complexityList (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 3 0 := by
  have _hU := hU
  have hstage : Primrec (fun q : ℕ × BitString =>
      boundedOutputStage c q.1 (decodeBits q.2)) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair Primrec.fst (primrec_decodeBits.comp Primrec.snd))
  have hcomp : Computable (fun q : ℕ × BitString =>
      listCode ((boundedOutputStage c q.1 (decodeBits q.2)).map
        (fun x => pairCode x (natBits (cValUpTo c q.1 (decodeBits q.2) x))))) :=
    (listCode_primrec.comp (Primrec.list_map hstage
      (pairMap_primrec c Primrec.fst (primrec_decodeBits.comp Primrec.snd)))).to_comp
  refine ⟨0, fun q => Part.some (listCode ((boundedOutputStage c q.1 (decodeBits q.2)).map
    (fun x => pairCode x (natBits (cValUpTo c q.1 (decodeBits q.2) x))))), hcomp,
    fun n => ?_⟩
  dsimp only
  rw [Nat.sub_zero]
  have hobj : canonicalObject U c 3 n = natBits (maxHaltTimeNat c n) := rfl
  rw [hobj]
  have hdec : decodeBits (natBits (maxHaltTimeNat c n)) = maxHaltingStage c n := by
    unfold natBits
    rw [decodeBits_natBits, maxHaltTime_eq_maxHaltingStage]
  rw [hdec, boundedOutputStage_eq_completedBoundedOutput c n (maxHaltingStage c n) le_rfl]
  have hmap : (completedBoundedOutput c n).map
      (fun x => pairCode x (natBits (cValUpTo c n (maxHaltingStage c n) x)))
      = (completedBoundedOutput c n).map (fun x => pairCode x (natBits (cVal U x))) := by
    refine List.map_congr_left ?_
    intro x hxmem
    rw [cValUpTo_eq U c hc n (maxHaltingStage c n) le_rfl x
      ((mem_completedBoundedOutput_iff_plainK_le hc n x).mp hxmem)]
  rw [hmap]
  rfl

/-- From the maximal halting time of the programs of length at most `n` at parameter `n` one
computes the graph of the complexity function on the strings of length `n` at parameter `n -
O(1)`. SUV Theorem 15. -/
theorem maxTime_reduces_complexityGraph (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 3 7 := by
  obtain ⟨k, hk⟩ := plainK_le_length U hU
  have hall : Primrec (fun q : ℕ × BitString => allStrings (q.1 - k)) :=
    Kolmogorov.CodedFiniteDistribution.allStrings_primrec.comp
      (Primrec.nat_sub.comp Primrec.fst (Primrec.const k))
  have hbody : Primrec (fun q : ℕ × BitString =>
      listCode ((allStrings (q.1 - k)).map
        (fun x => pairCode x (natBits (cValUpTo c q.1 (decodeBits q.2) x))))) :=
    listCode_primrec.comp (Primrec.list_map hall
      (pairMap_primrec c Primrec.fst (primrec_decodeBits.comp Primrec.snd)))
  have hcond : Primrec (fun q : ℕ × BitString => decide (q.1 < k)) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.nat_lt Primrec.fst (Primrec.const k))
  have hcomp : Computable (fun q : ℕ × BitString =>
      bif decide (q.1 < k) then canonicalObject U c 7 0
      else listCode ((allStrings (q.1 - k)).map
        (fun x => pairCode x (natBits (cValUpTo c q.1 (decodeBits q.2) x))))) :=
    Computable.cond hcond.to_comp (Computable.const _) hbody.to_comp
  refine ⟨k, fun q => Part.some
    (bif decide (q.1 < k) then canonicalObject U c 7 0
     else listCode ((allStrings (q.1 - k)).map
       (fun x => pairCode x (natBits (cValUpTo c q.1 (decodeBits q.2) x))))),
    hcomp, fun n => ?_⟩
  dsimp only
  by_cases hn : n < k
  · rw [decide_eq_true hn]
    have h0 : n - k = 0 := by omega
    rw [h0]
    rfl
  · rw [decide_eq_false hn]
    simp only [not_lt] at hn
    have hdec : decodeBits (canonicalObject U c 3 n) = maxHaltingStage c n := by
      change decodeBits (natBits (maxHaltTimeNat c n)) = maxHaltingStage c n
      unfold natBits
      rw [decodeBits_natBits, maxHaltTime_eq_maxHaltingStage]
    rw [hdec]
    have hmap : (allStrings (n - k)).map
        (fun x => pairCode x (natBits (cValUpTo c n (maxHaltingStage c n) x)))
        = (allStrings (n - k)).map (fun x => pairCode x (natBits (cVal U x))) := by
      refine List.map_congr_left ?_
      intro x hxmem
      have hxlen : x.length = n - k := (mem_allStrings (n - k) x).mp hxmem
      have hxk : plainK U x ≤ (n : ℕ∞) := by
        have h1 : plainK U x ≤ ((x.length : ℕ) : ℕ∞) + (k : ℕ∞) := hk x
        rw [hxlen, ← Nat.cast_add] at h1
        have h2 : (n - k) + k = n := by omega
        rwa [h2] at h1
      rw [cValUpTo_eq U c hc n (maxHaltingStage c n) le_rfl x hxk]
    change Part.some _ = Part.some _
    rw [hmap]
    rfl

private theorem find?_congr {α : Type*} {p q : α → Bool} (h : ∀ a, p a = q a)
    (l : List α) : l.find? p = l.find? q := by
  have hpq : p = q := funext h
  rw [hpq]

/-- From the graph of the complexity function on the strings of length `n` at parameter `n` one
computes the lexicographically first incompressible string of length `n` at parameter `n -
O(1)`. SUV Theorem 15. -/
theorem complexityGraph_reduces_firstIncompressible (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 7 8 := by
  have _hc := hc
  obtain ⟨k, hk⟩ := plainK_le_length U hU
  have hfin : ∀ x : BitString, plainK U x ≠ ⊤ := by
    intro x hx
    have h1 : plainK U x ≤ ((x.length : ℕ) : ℕ∞) + (k : ℕ∞) := hk x
    rw [hx, top_le_iff, ← Nat.cast_add] at h1
    exact ENat.natCast_ne_top _ h1
  have hfind : Primrec (fun q : ℕ × BitString =>
      (decodeListCode q.2).find? (fun z => decide (q.1 ≤ decodeBits (decodeSecond z)))) := by
    refine list_find?_primrec (decodeListCode_primrec.comp Primrec.snd) ?_
    exact (PrimrecPred.decide (PrimrecRel.comp Primrec.nat_le
      (Primrec.fst.comp Primrec.fst)
      (primrec_decodeBits.comp (decodeSecond_primrec.comp Primrec.snd)))).to₂
  have hcomp : Computable (fun q : ℕ × BitString =>
      (((decodeListCode q.2).find?
        (fun z => decide (q.1 ≤ decodeBits (decodeSecond z)))).map decodeFirst).getD []) :=
    (Primrec.option_getD.comp
      (Primrec.option_map hfind (decodeFirst_primrec.comp Primrec.snd).to₂)
      (Primrec.const [])).to_comp
  refine ⟨0, fun q => Part.some
    ((((decodeListCode q.2).find?
      (fun z => decide (q.1 ≤ decodeBits (decodeSecond z)))).map decodeFirst).getD []),
    hcomp, fun n => ?_⟩
  dsimp only
  rw [Nat.sub_zero]
  have h7 : canonicalObject U c 7 n
      = listCode ((allStrings n).map (fun x => pairCode x (natBits (cVal U x)))) := rfl
  rw [h7, decodeListCode_listCode, List.find?_map, Option.map_map]
  have hid : (decodeFirst ∘ fun x : BitString => pairCode x (natBits (cVal U x))) = id := by
    funext x
    simp only [Function.comp_apply, decodeFirst_pairCode, id_eq]
  rw [hid, Option.map_id]
  have hpred : ∀ x : BitString,
      ((fun z => decide (n ≤ decodeBits (decodeSecond z))) ∘
        fun y : BitString => pairCode y (natBits (cVal U y))) x
      = decide ((n : ℕ∞) ≤ plainK U x) := by
    intro x
    simp only [Function.comp_apply, decodeSecond_pairCode]
    show decide (n ≤ decodeBits (natBits (cVal U x))) = _
    unfold natBits
    rw [decodeBits_natBits, decide_eq_decide]
    have hcast : ((cVal U x : ℕ) : ℕ∞) = plainK U x := ENat.natCast_toNat (hfin x)
    constructor
    · intro h
      have h2 : ((n : ℕ) : ℕ∞) ≤ ((cVal U x : ℕ) : ℕ∞) := by exact_mod_cast h
      rwa [hcast] at h2
    · intro h
      rw [← hcast] at h
      exact_mod_cast h
  rw [find?_congr hpred (allStrings n)]
  rfl
/-- Searching for a halting stage of a halting program returns its halting time. -/
theorem rfind_haltTime (c : Code) (p : BitString)
    (h : ∃ t, haltsWithin c t p = true) :
    Nat.rfind (fun s => Part.some (haltsWithin c s p)) = Part.some (haltTimeNat c p) := by
  rw [Part.eq_some_iff]
  refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
  · simp only [Part.mem_some_iff]
    exact (haltsWithin_haltTime c h).symm
  · intro s hs
    simp only [Part.mem_some_iff]
    by_cases hcon : haltsWithin c s p = true
    · have := haltTime_le_of_haltsWithin c hcon
      omega
    · exact ((Bool.not_eq_true _).mp hcon).symm

private theorem haltStage_partrec (c : Code) :
    Partrec (fun x : BitString =>
      (Nat.rfind (fun s => Part.some (haltsWithin c s x))).map Nat.bits) := by
  have hpred : Primrec₂ (fun (x : BitString) (s : ℕ) => haltsWithin c s x) :=
    (Primrec₂.comp (haltsWithin_primrec₂ c) Primrec.snd Primrec.fst).to₂
  exact (Partrec.rfind hpred.to_comp.partrec₂).map (natBits_computable.comp Computable.snd).to₂

/-- From the busy-beaver value at parameter `n` one computes the list of halting programs of
length at most `n` at parameter `n - O(1)`. SUV Theorem 15. -/
theorem busyBeaver_reduces_haltingList (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 2 4 := by
  obtain ⟨c_map, hmap⟩ := plainK_partrec_map_le U hU _ (haltStage_partrec c)
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
  have hcond : Primrec (fun q : ℕ × BitString => decide (q.1 < c_len + c_map + K0)) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.nat_lt Primrec.fst (Primrec.const _))
  have hfilter : Primrec (fun q : ℕ × BitString =>
      (boundedPrograms (q.1 - (c_len + c_map + K0))).filter
        (fun x => haltsWithin c (decodeBits q.2) x)) :=
    list_filter_primrec
      (primrec_boundedPrograms.comp
        (Primrec₂.comp Primrec.nat_sub Primrec.fst (Primrec.const _)))
      ((Primrec₂.comp (haltsWithin_primrec₂ c)
        (primrec_decodeBits.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂)
  have hA : Computable (fun q : ℕ × BitString =>
      bif decide (q.1 < c_len + c_map + K0) then canonicalObject U c 4 0
      else listCode ((boundedPrograms (q.1 - (c_len + c_map + K0))).filter
        (fun x => haltsWithin c (decodeBits q.2) x))) :=
    Computable.cond hcond.to_comp (Computable.const _)
      (listCode_primrec.comp hfilter).to_comp
  refine ⟨c_len + c_map + K0, fun q => Part.some
    (bif decide (q.1 < c_len + c_map + K0) then canonicalObject U c 4 0
     else listCode ((boundedPrograms (q.1 - (c_len + c_map + K0))).filter
       (fun x => haltsWithin c (decodeBits q.2) x))), hA, fun n => ?_⟩
  by_cases hn : n < c_len + c_map + K0
  · simp only [decide_eq_true hn, cond_true]
    rw [show n - (c_len + c_map + K0) = 0 by omega]
  · simp only [not_lt] at hn
    simp only [decide_eq_false (by omega : ¬ n < c_len + c_map + K0), cond_false]
    obtain ⟨b0, hb0⟩ := busyBeaver_isSome_of_nonempty c n (hK0 n (by omega))
    have hcanon2 : canonicalObject U c 2 n = natBits b0 := by
      change natBits ((busyBeaver c n).getD 0) = natBits b0
      rw [hb0]
      rfl
    rw [hcanon2]
    change Part.some (listCode ((boundedPrograms (n - (c_len + c_map + K0))).filter
      (fun x => haltsWithin c (decodeBits (natBits b0)) x)))
      = Part.some (listCode (haltingProgramsBounded c (n - (c_len + c_map + K0))))
    simp only [natBits, decodeBits_natBits]
    congr 2
    set m := n - (c_len + c_map + K0) with hm
    unfold haltingProgramsBounded
    refine List.filter_congr (fun x hx => ?_)
    rw [Bool.eq_iff_iff]
    constructor
    · intro h
      exact (halts_maxStage_iff c m hx).mpr ⟨b0, h⟩
    · intro h
      have hex : ∃ t, haltsWithin c t x = true := (halts_maxStage_iff c m hx).mp h
      have hspec : haltsWithin c (haltTimeNat c x) x = true := haltsWithin_haltTime c hex
      have hmem : Nat.bits (haltTimeNat c x) ∈
          (Nat.rfind (fun s => Part.some (haltsWithin c s x))).map Nat.bits := by
        rw [rfind_haltTime c x hex]
        simp
      have hxlen : x.length ≤ m := (mem_boundedPrograms_iff x m).mp hx
      have hK : plainKNat U (haltTimeNat c x) ≤ (n : ℕ∞) := by
        calc plainKNat U (haltTimeNat c x) = plainK U (Nat.bits (haltTimeNat c x)) := rfl
          _ ≤ plainK U x + (c_map : ℕ∞) := hmap x _ hmem
          _ ≤ ((x.length : ℕ∞) + (c_len : ℕ∞)) + (c_map : ℕ∞) := by gcongr; exact hlen x
          _ ≤ ((m : ℕ∞) + (c_len : ℕ∞)) + (c_map : ℕ∞) := by
              gcongr
          _ = ((m + c_len + c_map : ℕ) : ℕ∞) := by push_cast; ring
          _ ≤ (n : ℕ∞) := by exact_mod_cast (by omega : m + c_len + c_map ≤ n)
      have hmemb : haltTimeNat c x ∈ boundedNatOutputs c n :=
        (mem_boundedNatOutputs_iff_plainKNat_le hc n _).mpr hK
      have hle := ((busyBeaver_some_iff c n b0).mp hb0).2 _ hmemb
      exact haltsWithin_mono c hle x hspec

/-- A slowest halting program of level `n` halts at the maximal halting time of the
level. -/
theorem haltTime_argmax (c : Code) (n : ℕ) {q : BitString}
    (hq : List.argmax (haltTimeNat c) (haltingProgramsBounded c n) = some q) :
    haltTimeNat c q = maxHaltTimeNat c n := by
  have hmem : q ∈ haltingProgramsBounded c n := List.argmax_mem hq
  unfold maxHaltTimeNat
  refine le_antisymm (le_foldr_max_of_mem (List.mem_map_of_mem hmem)) ?_
  refine foldr_max_le_of_forall_mem ?_
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  exact List.le_of_mem_argmax hp hq

private theorem maxHaltTime_eq_zero (c : Code) (n : ℕ)
    (h : haltingProgramsBounded c n = []) : maxHaltTimeNat c n = 0 := by
  unfold maxHaltTimeNat
  rw [h]
  rfl

private theorem rfind_guard_const (f : ℕ → Bool) (hf : ∀ t, f t = true) :
    Nat.rfind (fun t => Part.some (f t)) = Part.some 0 := by
  rw [Part.eq_some_iff]
  refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
  · simp only [Part.mem_some_iff]
    exact (hf 0).symm
  · intro k hk
    exact absurd hk (Nat.not_lt_zero k)

private theorem rfind_guard_false (c : Code) (b : Bool) (p : BitString) (hb : b = false)
    (h : ∃ t, haltsWithin c t p = true) :
    Nat.rfind (fun t : ℕ => Part.some (bif b then true else haltsWithin c t p))
      = Part.some (haltTimeNat c p) := by
  subst hb
  exact rfind_haltTime c p h

private theorem partrec_guardedRfind (c : Code) (g : BitString → Bool) (hg : Primrec g) :
    Partrec (fun q : ℕ × BitString =>
      (Nat.rfind (fun t : ℕ =>
        Part.some (bif g q.2 then true else haltsWithin c t q.2))).map natBits) := by
  have h0 : Primrec (fun z : (ℕ × BitString) × ℕ =>
      bif g z.1.2 then true else haltsWithin c z.2 z.1.2) := by
    refine Primrec.cond (hg.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const true) ?_
    exact Primrec₂.comp (haltsWithin_primrec₂ c) Primrec.snd (Primrec.snd.comp Primrec.fst)
  exact (Partrec.rfind h0.to₂.to_comp.partrec₂).map
    (natBits_computable.comp Computable.snd).to₂

private theorem argmax_of_ne_nil (c : Code) (n : ℕ)
    (h : haltingProgramsBounded c n ≠ []) :
    ∃ q, List.argmax (haltTimeNat c) (haltingProgramsBounded c n) = some q := by
  rcases hopt : List.argmax (haltTimeNat c) (haltingProgramsBounded c n) with _ | q
  · exact absurd (List.argmax_eq_none.mp hopt) h
  · exact ⟨q, rfl⟩

/-- From the slowest halting program of length at most `n` at parameter `n` one computes the
maximal halting time of the programs of length at most `n` at parameter `n - O(1)`. SUV
Theorem 15. -/
theorem slowestProgram_reduces_maxTime (U : Map) (c : Code) : HubReduces U c 6 3 := by
  by_cases hnil : ∃ t, haltsWithin c t ([] : BitString) = true
  · refine ⟨0, _, partrec_guardedRfind c (fun _ => false) (Primrec.const false), ?_⟩
    intro n
    have hmem0 : ([] : BitString) ∈ haltingProgramsBounded c n :=
      (mem_haltingProgramsBounded_iff c n []).mpr
        ⟨(mem_boundedPrograms_iff [] n).mpr (by simp), hnil⟩
    have hne : haltingProgramsBounded c n ≠ [] := by
      intro h; rw [h] at hmem0; simp at hmem0
    obtain ⟨q, hq⟩ := argmax_of_ne_nil c n hne
    have hqmem : q ∈ haltingProgramsBounded c n := List.argmax_mem hq
    have hqex : ∃ t, haltsWithin c t q = true :=
      ((mem_haltingProgramsBounded_iff c n q).mp hqmem).2
    have hw : canonicalObject U c 6 n = q := by
      change (List.argmax (haltTimeNat c) (haltingProgramsBounded c n)).getD [] = q
      rw [hq]; rfl
    change (Nat.rfind (fun t : ℕ =>
        Part.some (haltsWithin c t (canonicalObject U c 6 n)))).map natBits
        = Part.some (canonicalObject U c 3 (n - 0))
    rw [hw, rfind_haltTime c q hqex, Part.map_some, haltTime_argmax c n hq,
      Nat.sub_zero]
    rfl
  · refine ⟨0, _, partrec_guardedRfind c (fun w => decide (w = ([] : BitString)))
      (PrimrecPred.decide (PrimrecRel.comp Primrec.eq Primrec.id
        (Primrec.const ([] : BitString)))), ?_⟩
    intro n
    have hnotmem : ([] : BitString) ∉ haltingProgramsBounded c n := fun h =>
      hnil ((mem_haltingProgramsBounded_iff c n []).mp h).2
    by_cases hcase : haltingProgramsBounded c n = []
    · have hw : canonicalObject U c 6 n = ([] : BitString) := by
        change (List.argmax (haltTimeNat c) (haltingProgramsBounded c n)).getD [] = []
        rw [List.argmax_eq_none.mpr hcase]; rfl
      have hconst : ∀ t : ℕ,
          (bif decide (canonicalObject U c 6 n = ([] : BitString)) then true
            else haltsWithin c t (canonicalObject U c 6 n)) = true := by
        intro t; rw [hw]; simp
      change (Nat.rfind (fun t : ℕ => Part.some
          (bif decide (canonicalObject U c 6 n = ([] : BitString)) then true
            else haltsWithin c t (canonicalObject U c 6 n)))).map natBits
          = Part.some (canonicalObject U c 3 (n - 0))
      rw [rfind_guard_const _ hconst, Part.map_some, Nat.sub_zero,
        show canonicalObject U c 3 n = natBits (maxHaltTimeNat c n) from rfl,
        maxHaltTime_eq_zero c n hcase]
    · obtain ⟨q, hq⟩ := argmax_of_ne_nil c n hcase
      have hqmem : q ∈ haltingProgramsBounded c n := List.argmax_mem hq
      have hqne : q ≠ ([] : BitString) := by rintro rfl; exact hnotmem hqmem
      have hqex : ∃ t, haltsWithin c t q = true :=
        ((mem_haltingProgramsBounded_iff c n q).mp hqmem).2
      have hw : canonicalObject U c 6 n = q := by
        change (List.argmax (haltTimeNat c) (haltingProgramsBounded c n)).getD [] = q
        rw [hq]; rfl
      have hdec : decide (q = ([] : BitString)) = false := by simp [hqne]
      change (Nat.rfind (fun t : ℕ => Part.some
          (bif decide (canonicalObject U c 6 n = ([] : BitString)) then true
            else haltsWithin c t (canonicalObject U c 6 n)))).map natBits
          = Part.some (canonicalObject U c 3 (n - 0))
      rw [hw, rfind_guard_false c _ q hdec hqex, Part.map_some,
        haltTime_argmax c n hq, Nat.sub_zero]
      rfl

end Kolmogorov
