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
import KolmogorovMathlib.Complexity.CanonicalObjects.HubEdges

/-!
# Effective ingredients of the canonical-object reductions

The primitive-recursive functions the reductions of SUV Theorem 15 are built from, with the
small facts that make them correct.

`haltTimeLe` is the bounded halting-time test (`haltTimeLe_eq`, `haltTimeLe_primrec`);
`argmaxNat` and `argAuxNat` are a primitive-recursive presentation of the search for a
maximising index, with the congruence and membership lemmas that let it replace `List.argmax`;
`graphToGamma_spec` shows the complexity graph of level `n` determines the lexicographically
first incompressible string of that length, and `head_length`, `le_cVal_iff_le_plainK` and
`find_congr` are the remaining bridges between the `ℕ`- and `ℕ∞`-valued complexities and
between equal predicates.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

private def haltTimeLe (c : Code) (T : ℕ) (p : BitString) : ℕ :=
  T + 1 - (List.range (T + 1)).countP (fun s => haltsWithin c s p)

private theorem countP_range_ge (h : ℕ) : ∀ T : ℕ,
    (List.range T).countP (fun s => decide (h ≤ s)) = T - h := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
    rw [List.range_succ, List.countP_append, ih, List.countP_cons, List.countP_nil]
    by_cases hT : h ≤ T
    · rw [if_pos (by simpa using hT)]
      omega
    · rw [if_neg (by simpa using hT)]
      omega

private theorem haltTimeLe_eq (c : Code) (T : ℕ) (p : BitString)
    (hT : haltsWithin c T p = true) : haltTimeLe c T p = haltTimeNat c p := by
  have hex : ∃ t, haltsWithin c t p = true := ⟨T, hT⟩
  have hle : haltTimeNat c p ≤ T := haltTime_le_of_haltsWithin c hT
  have hfun : (fun s => haltsWithin c s p) = (fun s => decide (haltTimeNat c p ≤ s)) := by
    funext s
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    exact ⟨fun hs => haltTime_le_of_haltsWithin c hs,
      fun hs => haltsWithin_mono c hs p (haltsWithin_haltTime c hex)⟩
  unfold haltTimeLe
  rw [hfun, countP_range_ge]
  omega

private theorem haltTimeLe_primrec {α : Type*} [Primcodable α] (c : Code)
    {T : α → ℕ} {p : α → BitString} (hT : Primrec T) (hp : Primrec p) :
    Primrec (fun a => haltTimeLe c (T a) (p a)) := by
  have hcount : Primrec (fun a =>
      (List.range (T a + 1)).countP (fun s => haltsWithin c s (p a))) := by
    refine list_countP_primrec (Primrec.list_range.comp (Primrec.succ.comp hT)) ?_
    exact (Primrec₂.comp (haltsWithin_primrec₂ c) Primrec.snd (hp.comp Primrec.fst)).to₂
  have hsub : Primrec (fun a =>
      T a + 1 - (List.range (T a + 1)).countP (fun s => haltsWithin c s (p a))) :=
    Primrec₂.comp Primrec.nat_sub (Primrec.succ.comp hT) hcount
  exact hsub.of_eq (fun a => rfl)

private def argAuxNat (f : BitString → ℕ) (a : Option BitString) (b : BitString) :
    Option BitString :=
  Option.casesOn a (some b) (fun cc => if f cc < f b then some b else some cc)

private def argmaxNat (f : BitString → ℕ) (l : List BitString) : Option BitString :=
  l.foldl (argAuxNat f) none

private theorem argmaxNat_eq (f : BitString → ℕ) (l : List BitString) :
    argmaxNat f l = List.argmax f l := rfl

private theorem argAuxNat_congr {f g : BitString → ℕ} (a : Option BitString)
    (b : BitString) (hb : f b = g b) (ha : ∀ x, a = some x → f x = g x) :
    argAuxNat f a b = argAuxNat g a b := by
  cases a with
  | none => rfl
  | some cc => simp only [argAuxNat, hb, ha cc rfl]

private theorem argAuxNat_mem {f : BitString → ℕ} {a : Option BitString} {b x : BitString}
    (hx : argAuxNat f a b = some x) : x = b ∨ a = some x := by
  cases a with
  | none => exact Or.inl (Option.some.inj hx).symm
  | some cc =>
    simp only [argAuxNat] at hx
    by_cases hlt : f cc < f b
    · rw [if_pos hlt] at hx
      exact Or.inl (Option.some.inj hx).symm
    · rw [if_neg hlt] at hx
      exact Or.inr hx

private theorem foldl_argAuxNat_congr {f g : BitString → ℕ} :
    ∀ (l : List BitString) (a : Option BitString), (∀ x ∈ l, f x = g x) →
      (∀ x, a = some x → f x = g x) →
      l.foldl (argAuxNat f) a = l.foldl (argAuxNat g) a := by
  intro l
  induction l with
  | nil => intro a _ _; rfl
  | cons b t ih =>
    intro a hl ha
    have hb : f b = g b := hl b (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    rw [argAuxNat_congr a b hb ha]
    refine ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) ?_
    intro x hx
    rcases argAuxNat_mem hx with rfl | hx'
    · exact hb
    · exact ha x hx'

private theorem argmax_congr {f g : BitString → ℕ} (l : List BitString)
    (h : ∀ x ∈ l, f x = g x) : List.argmax f l = List.argmax g l := by
  rw [← argmaxNat_eq, ← argmaxNat_eq]
  exact foldl_argAuxNat_congr l none h (fun x hx => by simp at hx)

/-- From the maximal halting time of the programs of length at most `n` at parameter `n` one
computes the slowest halting program of length at most `n` at parameter `n - O(1)`. SUV
Theorem 15. -/
theorem maxTime_reduces_slowestProgram (U : Map) (c : Code) : HubReduces U c 3 6 := by
  have hlist : Primrec (fun q : ℕ × BitString =>
      (boundedPrograms q.1).filter (fun p => haltsWithin c (decodeBits q.2) p)) := by
    refine list_filter_primrec (primrec_boundedPrograms.comp Primrec.fst) ?_
    exact (haltsWithin_primrec₂ c).comp
      (primrec_decodeBits.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hT : Primrec (fun v : ((ℕ × BitString) × (Option BitString × BitString)) × BitString =>
      decodeBits v.1.1.2) :=
    primrec_decodeBits.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hA : Primrec (fun v : ((ℕ × BitString) × (Option BitString × BitString)) × BitString =>
      haltTimeLe c (decodeBits v.1.1.2) v.2) :=
    haltTimeLe_primrec c hT Primrec.snd
  have hB : Primrec (fun v : ((ℕ × BitString) × (Option BitString × BitString)) × BitString =>
      haltTimeLe c (decodeBits v.1.1.2) v.1.2.2) :=
    haltTimeLe_primrec c hT (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hinner : Primrec₂ (fun (y : (ℕ × BitString) × (Option BitString × BitString))
      (cc : BitString) =>
      if haltTimeLe c (decodeBits y.1.2) cc
          < haltTimeLe c (decodeBits y.1.2) y.2.2
        then some y.2.2 else some cc) :=
    (Primrec.ite (PrimrecRel.comp Primrec.nat_lt hA hB)
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.option_some.comp Primrec.snd)).to₂
  have hstep : Primrec (fun y : (ℕ × BitString) × (Option BitString × BitString) =>
      argAuxNat (haltTimeLe c (decodeBits y.1.2)) y.2.1 y.2.2) := by
    unfold argAuxNat
    exact Primrec.option_casesOn (Primrec.fst.comp Primrec.snd)
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) hinner
  have hfold : Primrec (fun q : ℕ × BitString =>
      argmaxNat (haltTimeLe c (decodeBits q.2))
        ((boundedPrograms q.1).filter (fun p => haltsWithin c (decodeBits q.2) p))) :=
    (Primrec.list_foldl hlist (Primrec.const (none : Option BitString)) hstep.to₂).of_eq
      (fun q => rfl)
  refine ⟨0, fun q => Part.some ((argmaxNat (haltTimeLe c (decodeBits q.2))
      ((boundedPrograms q.1).filter (fun p => haltsWithin c (decodeBits q.2) p))).getD []),
    (Primrec₂.comp Primrec.option_getD hfold (Primrec.const ([] : BitString))).to_comp, ?_⟩
  intro n
  change Part.some ((argmaxNat (haltTimeLe c (decodeBits (canonicalObject U c 3 n)))
      ((boundedPrograms n).filter
        (fun p => haltsWithin c (decodeBits (canonicalObject U c 3 n)) p))).getD [])
    = Part.some (canonicalObject U c 6 (n - 0))
  have hdec : decodeBits (canonicalObject U c 3 n) = maxHaltingStage c n := by
    change decodeBits (natBits (maxHaltTimeNat c n)) = maxHaltingStage c n
    unfold natBits
    rw [decodeBits_natBits, maxHaltTime_eq_maxHaltingStage]
  have hcongr : ∀ p ∈ haltingProgramsBounded c n,
      haltTimeLe c (maxHaltingStage c n) p = haltTimeNat c p := by
    intro p hp
    refine haltTimeLe_eq c _ p ?_
    have hp' := hp
    unfold haltingProgramsBounded at hp'
    exact (List.mem_filter.mp hp').2
  rw [hdec,
    filter_haltsWithin_eq_haltingProgramsBounded c n (maxHaltingStage c n) le_rfl, argmaxNat_eq,
    argmax_congr _ hcongr, Nat.sub_zero]
  rfl
/-- `2 log j + A < j` for all large `j`. -/
private theorem two_bits_lt (A : ℕ) :
    ∃ M : ℕ, ∀ j : ℕ, M ≤ j → 2 * (Nat.bits j).length + A < j := by
  refine ⟨(A + 8) * (A + 8), fun k hk => ?_⟩
  have hbits : (Nat.bits k).length ≤ Nat.sqrt k + 2 := bits_length_le_sqrt_add_two k
  have h1 : Nat.sqrt k * Nat.sqrt k ≤ k := Nat.sqrt_le k
  have h2 : A + 8 ≤ Nat.sqrt k := by
    have := Nat.sqrt_le_sqrt hk
    rwa [Nat.sqrt_eq] at this
  have h3 : (A + 8) * Nat.sqrt k ≤ Nat.sqrt k * Nat.sqrt k :=
    Nat.mul_le_mul_right (Nat.sqrt k) h2
  nlinarith [Nat.sqrt k, hbits, h1, h2, h3]

/-- Boolean membership test for bit strings. -/
private def bitStringMemBool (x : BitString) (l : List BitString) : Bool :=
  l.foldr (fun y acc => (decide (y = x)) || acc) false

private theorem memBool_iff (x : BitString) (l : List BitString) :
    bitStringMemBool x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [bitStringMemBool]
  | cons a t ih =>
    simp only [bitStringMemBool, List.foldr_cons, Bool.or_eq_true, decide_eq_true_eq,
      List.mem_cons] at *
    constructor
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr (ih.mp h)
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr (ih.mpr h)

/-- Elements of `l` strictly before the first occurrence of `g`. -/
private def beforeFirstOccurrence (g : BitString) (l : List BitString) : List BitString :=
  l.foldr (fun a acc => bif decide (a = g) then [] else a :: acc) []

private theorem before_append {g : BitString} {l1 l2 : List BitString}
    (h : g ∉ l1) : beforeFirstOccurrence g (l1 ++ g :: l2) = l1 := by
  induction l1 with
  | nil => simp [beforeFirstOccurrence]
  | cons a t ih =>
    have ha : a ≠ g := fun hh => h (by simp [hh])
    have ht : g ∉ t := fun hh => h (List.mem_cons_of_mem _ hh)
    simp only [List.cons_append, beforeFirstOccurrence, List.foldr_cons] at *
    rw [show (decide (a = g)) = false from decide_eq_false ha]
    simp only [cond_false]
    rw [ih ht]

/-- First element of `l` that is not in `stage` (or `[]`). -/
private def firstNotIn (l stage : List BitString) : BitString :=
  l.foldr (fun a acc => bif bitStringMemBool a stage then acc else a) []

private theorem firstNotIn_eq {l1 l2 stage : List BitString} {a : BitString}
    (h1 : ∀ x ∈ l1, bitStringMemBool x stage = true)
    (ha : bitStringMemBool a stage = false) :
    firstNotIn (l1 ++ a :: l2) stage = a := by
  induction l1 with
  | nil => simp [firstNotIn, ha]
  | cons b t ih =>
    have hb : bitStringMemBool b stage = true := h1 b (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, bitStringMemBool x stage = true :=
      fun x hx => h1 x (List.mem_cons_of_mem _ hx)
    simp only [List.cons_append, firstNotIn, List.foldr_cons] at *
    rw [hb]
    simp only [cond_true]
    exact ih ht

private theorem memBool_primrec {α : Type} [Primcodable α]
    {f : α → BitString} {g : α → List BitString} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => bitStringMemBool (f a) (g a)) := by
  have h : Primrec₂ (fun (a : α) (z : BitString × Bool) =>
      (decide (z.1 = f a)) || z.2) :=
    (Primrec₂.comp (Primrec.dom_bool₂ (fun u v => u || v))
      (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
        (Primrec.fst.comp Primrec.snd) (hf.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hg (Primrec.const false) h

private theorem before_primrec {α : Type} [Primcodable α]
    {f : α → BitString} {g : α → List BitString} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => beforeFirstOccurrence (f a) (g a)) := by
  have h : Primrec₂ (fun (a : α) (z : BitString × List BitString) =>
      bif decide (z.1 = f a) then ([] : List BitString) else z.1 :: z.2) :=
    (Primrec.cond
      (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
        (Primrec.fst.comp Primrec.snd) (hf.comp Primrec.fst)))
      (Primrec.const ([] : List BitString))
      (Primrec₂.comp Primrec.list_cons (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂
  exact Primrec.list_foldr hg (Primrec.const ([] : List BitString)) h

private theorem firstNotIn_primrec {α : Type} [Primcodable α]
    {f g : α → List BitString} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => firstNotIn (f a) (g a)) := by
  have h : Primrec₂ (fun (a : α) (z : BitString × BitString) =>
      bif bitStringMemBool z.1 (g a) then z.2 else z.1) :=
    (Primrec.cond
      (memBool_primrec (Primrec.fst.comp Primrec.snd) (hg.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const ([] : BitString)) h

/-- The `find?` defining `objFirstIncompressible` succeeds, and the decomposition of
`allStrings n` around it. -/
private theorem gamma_decomp (U : Map) (n : ℕ) :
    ∃ l1 l2 : List BitString,
      allStrings n = l1 ++ objFirstIncompressible U n :: l2 ∧
      (n : ℕ∞) ≤ plainK U (objFirstIncompressible U n) ∧
      objFirstIncompressible U n ∉ l1 ∧
      ∀ x ∈ l1, plainK U x < (n : ℕ∞) := by
  classical
  set p : BitString → Bool := fun x => decide ((n : ℕ∞) ≤ plainK U x) with hp
  have hsome : ((allStrings n).find? p).isSome = true := by
    rw [List.find?_isSome]
    obtain ⟨s, hlen, hs⟩ := exists_incompressible_string U [] n
    refine ⟨s, (mem_allStrings n s).mpr hlen, ?_⟩
    simp only [hp]
    exact decide_eq_true (show (n : ℕ∞) ≤ plainK U s from hs)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
  have hgam : objFirstIncompressible U n = a := by
    change ((allStrings n).find? p).getD [] = a
    rw [ha]; rfl
  rw [List.find?_eq_some_iff_append] at ha
  obtain ⟨hpa, l1, l2, hsplit, hl1⟩ := ha
  have hl1lt : ∀ x ∈ l1, plainK U x < (n : ℕ∞) := by
    intro x hx
    have hx2 := hl1 x hx
    simp only [hp] at hx2
    have : ¬ ((n : ℕ∞) ≤ plainK U x) := by
      intro hcon
      rw [decide_eq_true hcon] at hx2
      exact absurd hx2 (by decide)
    exact not_le.mp this
  refine ⟨l1, l2, ?_, ?_, ?_, hl1lt⟩
  · rw [hgam]; exact hsplit
  · rw [hgam]; simpa [hp] using hpa
  · rw [hgam]
    intro hcon
    have := hl1lt a hcon
    have hpa2 : (n : ℕ∞) ≤ plainK U a := by simpa [hp] using hpa
    exact absurd hpa2 (not_le.mpr this)

private theorem rfind_spec (p : ℕ → Bool) (h : ∃ T, p T = true) :
    ∃ T0 : ℕ, p T0 = true ∧ Nat.rfind (fun T => Part.some (p T)) = Part.some T0 := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  rw [Part.eq_some_iff, Nat.mem_rfind]
  refine ⟨by simpa using Nat.find_spec h, ?_⟩
  intro m hm
  simp only [Part.mem_some_iff]
  have hm2 := Nat.find_min h hm
  rw [Bool.not_eq_true] at hm2
  exact hm2.symm

private theorem pre_lt (U : Map) (n : ℕ) :
    ∀ x ∈ beforeFirstOccurrence (objFirstIncompressible U n) (allStrings n),
      plainK U x < (n : ℕ∞) := by
  obtain ⟨l1, l2, hsplit, _, hnotmem, hlt⟩ := gamma_decomp U n
  intro x hx
  rw [hsplit, before_append hnotmem] at hx
  exact hlt x hx

private theorem plainK_le_pred {U : Map} {n : ℕ} (hn : 1 ≤ n) {x : BitString}
    (h : plainK U x < (n : ℕ∞)) : plainK U x ≤ ((n - 1 : ℕ) : ℕ∞) := by
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h)
  rw [← hj] at h ⊢
  have hjn : j < n := Nat.cast_lt.mp h
  exact Nat.cast_le.mpr (by omega : j ≤ n - 1)

private theorem gamma_not_mem {U : Map} {c : Code} (hc : IsCodeFor c U) {n : ℕ}
    (hn : 1 ≤ n) : objFirstIncompressible U n ∉ completedBoundedOutput c (n - 1) := by
  intro hmem
  have h1 := (mem_completedBoundedOutput_iff_plainK_le hc (n - 1) _).mp hmem
  obtain ⟨l1, l2, hsplit, hge, hnotmem, hlt⟩ := gamma_decomp U n
  have h2 : (n : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := le_trans hge h1
  have h3 : n ≤ n - 1 := by exact_mod_cast h2
  omega

/-- The search predicate: every string before `w` in `allStrings n` has already been
output by stage `T` of the `(n-1)`-bounded enumeration. -/
private def allEarlierEnumerated (c : Code) (q : ℕ × BitString) (T : ℕ) : Bool :=
  decide ((beforeFirstOccurrence q.2 (allStrings q.1)).countP
      (fun x => bitStringMemBool x (boundedOutputStage c (q.1 - 1) T)) =
    (beforeFirstOccurrence q.2 (allStrings q.1)).length)

private theorem pred_iff (c : Code) (q : ℕ × BitString) (T : ℕ) :
    allEarlierEnumerated c q T = true ↔
      ∀ x ∈ beforeFirstOccurrence q.2 (allStrings q.1), x ∈ boundedOutputStage c (q.1 - 1) T := by
  unfold allEarlierEnumerated
  rw [decide_eq_true_iff, List.countP_eq_length]
  exact ⟨fun h x hx => (memBool_iff x _).mp (h x hx),
    fun h x hx => (memBool_iff x _).mpr (h x hx)⟩

private theorem pred_primrec (c : Code) : Primrec₂ (allEarlierEnumerated c) := by
  have hbefore : Primrec (fun z : (ℕ × BitString) × ℕ =>
      beforeFirstOccurrence z.1.2 (allStrings z.1.1)) :=
    before_primrec (Primrec.snd.comp Primrec.fst)
      (allStrings_primrec.comp (Primrec.fst.comp Primrec.fst))
  have hstage : Primrec (fun z : (ℕ × BitString) × ℕ =>
      boundedOutputStage c (z.1.1 - 1) z.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair (Primrec₂.comp Primrec.nat_sub (Primrec.fst.comp Primrec.fst)
        (Primrec.const 1)) Primrec.snd)
  have hcount : Primrec (fun z : (ℕ × BitString) × ℕ =>
      (beforeFirstOccurrence z.1.2 (allStrings z.1.1)).countP
        (fun x => bitStringMemBool x (boundedOutputStage c (z.1.1 - 1) z.2))) :=
    list_countP_primrec hbefore
      (memBool_primrec Primrec.snd (hstage.comp Primrec.fst)).to₂
  exact (PrimrecPred.decide (PrimrecRel.comp Primrec.eq hcount
    (Primrec.list_length.comp hbefore))).to₂

/-- The compressor used in the key claim: from a code for `(e, α)` it runs `α` to its
halting time `B` and returns the first string of length `|α| + e` not yet enumerated at
stage `B` of the `(|α| + e - 1)`-bounded enumeration. -/
private def firstUnenumeratedCompressor (c : Code) (w : BitString) : Part BitString :=
  (Nat.rfind (fun s => Part.some (haltsWithin c s (decodeSecond w)))).map (fun B =>
    firstNotIn (allStrings ((decodeSecond w).length + decodeBits (decodeFirst w)))
      (boundedOutputStage c ((decodeSecond w).length + decodeBits (decodeFirst w) - 1) B))

private theorem firstUnenumeratedCompressor_partrec (c : Code) :
    Partrec (firstUnenumeratedCompressor c) := by
  have hpred : Primrec₂ (fun (w : BitString) (s : ℕ) => haltsWithin c s (decodeSecond w)) :=
    (Primrec₂.comp (haltsWithin_primrec₂ c) Primrec.snd
      (decodeSecond_primrec.comp Primrec.fst)).to₂
  have hn : Primrec (fun z : BitString × ℕ =>
      (decodeSecond z.1).length + decodeBits (decodeFirst z.1)) :=
    Primrec₂.comp Primrec.nat_add
      (Primrec.list_length.comp (decodeSecond_primrec.comp Primrec.fst))
      (primrec_decodeBits.comp (decodeFirst_primrec.comp Primrec.fst))
  have hg : Primrec (fun z : BitString × ℕ =>
      firstNotIn (allStrings ((decodeSecond z.1).length + decodeBits (decodeFirst z.1)))
        (boundedOutputStage c
          ((decodeSecond z.1).length + decodeBits (decodeFirst z.1) - 1) z.2)) :=
    firstNotIn_primrec (allStrings_primrec.comp hn)
      ((boundedOutputStage_primrec c).comp
        (Primrec.pair (Primrec₂.comp Primrec.nat_sub hn (Primrec.const 1)) Primrec.snd))
  exact (Partrec.rfind hpred.to_comp.partrec₂).map hg.to_comp.to₂

private theorem firstUnenumeratedCompressor_eval (c : Code) (e : ℕ) (a : BitString)
    (ha : ∃ t, haltsWithin c t a = true) :
    firstUnenumeratedCompressor c (pairCode (natBits e) a) =
      Part.some (firstNotIn (allStrings (a.length + e))
        (boundedOutputStage c (a.length + e - 1) (haltTimeNat c a))) := by
  unfold firstUnenumeratedCompressor
  rw [decodeFirst_pairCode, decodeSecond_pairCode]
  simp only [natBits, decodeBits_natBits]
  rw [rfind_haltTime c a ha]
  simp

private theorem foldr_max_attained {α : Type} (f : α → ℕ) :
    ∀ (l : List α), l ≠ [] → ∃ a ∈ l, f a = (l.map f).foldr max 0
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_cons_self .., by simp⟩
  | a :: b :: t, _ => by
      obtain ⟨d, hd, hdf⟩ := foldr_max_attained f (b :: t) (by simp)
      simp only [List.map_cons, List.foldr_cons] at *
      rcases le_total (f d) (f a) with h | h
      · refine ⟨a, List.mem_cons_self .., ?_⟩
        rw [← hdf]
        omega
      · refine ⟨d, List.mem_cons_of_mem _ hd, ?_⟩
        rw [← hdf] at *
        omega

private theorem pred_exists (U : Map) (c : Code) (hc : IsCodeFor c U) (n : ℕ) :
    ∃ T, allEarlierEnumerated c (n, objFirstIncompressible U n) T = true := by
  refine ⟨maxHaltingStage c (n - 1), ?_⟩
  rw [pred_iff]
  intro x hx
  have hlt : plainK U x < (n : ℕ∞) := pre_lt U n x hx
  change x ∈ completedBoundedOutput c (n - 1)
  rw [mem_completedBoundedOutput_iff_plainK_le hc]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd hlt (by simp)
  · exact plainK_le_pred hn hlt

/-- **The key claim.**  There is a constant `K` such that whenever every string
lexicographically before `γ_n` has been enumerated by stage `T` of the `(n-1)`-bounded
enumeration, `T` already exceeds the maximal halting stage at `n - K`. -/
private theorem maxHaltingStage_le_of_allEarlierEnumerated (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ n : ℕ, K ≤ n → ∀ T : ℕ,
      allEarlierEnumerated c (n, objFirstIncompressible U n) T = true →
      maxHaltingStage c (n - K) ≤ T := by
  obtain ⟨c_map, hmap⟩ :=
    plainK_partrec_map_le U hU (firstUnenumeratedCompressor c)
      (firstUnenumeratedCompressor_partrec c)
  obtain ⟨c_len, hlen⟩ := plainK_le_length U hU
  obtain ⟨M, hM⟩ := two_bits_lt (1 + c_len + c_map)
  refine ⟨M + 1, by omega, ?_⟩
  intro n hn T hT
  set m := n - (M + 1) with hm
  by_contra hcon
  push_neg at hcon
  have hmt : maxHaltTimeNat c m = maxHaltingStage c m := maxHaltTime_eq_maxHaltingStage c m
  have hne : haltingProgramsBounded c m ≠ [] := by
    intro h0
    have hz : maxHaltTimeNat c m = 0 := by unfold maxHaltTimeNat; rw [h0]; simp
    omega
  obtain ⟨a, ha_mem, ha_eq⟩ := foldr_max_attained (haltTimeNat c) _ hne
  have ha_ht : haltTimeNat c a = maxHaltTimeNat c m := ha_eq
  have haB : T ≤ haltTimeNat c a := by omega
  have ha_bd := (mem_haltingProgramsBounded_iff c m a).mp ha_mem
  have ha_len : a.length ≤ m := (mem_boundedPrograms_iff a m).mp ha_bd.1
  have ha_halts : ∃ t, haltsWithin c t a = true := ha_bd.2
  have hn1 : 1 ≤ n := by omega
  have hsum : a.length + ((m - a.length) + (M + 1)) = n := by omega
  obtain ⟨l1, l2, hsplit, hge, hnotmem, hltl1⟩ := gamma_decomp U n
  have hbefore : beforeFirstOccurrence (objFirstIncompressible U n) (allStrings n) = l1 := by
    rw [hsplit]; exact before_append hnotmem
  have hl1B : ∀ x ∈ l1,
      bitStringMemBool x (boundedOutputStage c (n - 1) (haltTimeNat c a)) = true := by
    intro x hx
    rw [memBool_iff]
    have hall := (pred_iff c (n, objFirstIncompressible U n) T).mp hT
    simp only at hall
    have hxT : x ∈ boundedOutputStage c (n - 1) T := hall x (by rw [hbefore]; exact hx)
    exact (boundedOutputStage_prefix_of_le c (n - 1) haB).subset hxT
  have hgamB : bitStringMemBool (objFirstIncompressible U n)
      (boundedOutputStage c (n - 1) (haltTimeNat c a)) = false := by
    by_contra hcon2
    rw [Bool.not_eq_false, memBool_iff] at hcon2
    exact gamma_not_mem hc hn1
      ((boundedOutputStage_prefix_completed c (n - 1) (haltTimeNat c a)).subset hcon2)
  have hfirst : firstNotIn (allStrings n) (boundedOutputStage c (n - 1) (haltTimeNat c a))
      = objFirstIncompressible U n := by
    rw [hsplit]
    exact firstNotIn_eq hl1B hgamB
  have hFeval : firstUnenumeratedCompressor c (pairCode (natBits ((m - a.length) + (M + 1))) a)
      = Part.some (objFirstIncompressible U n) := by
    rw [firstUnenumeratedCompressor_eval c _ a ha_halts, hsum, hfirst]
  have hmem : objFirstIncompressible U n ∈
      firstUnenumeratedCompressor c (pairCode (natBits ((m - a.length) + (M + 1))) a) := by
    rw [hFeval]; exact Part.mem_some _
  have h1 := hmap _ _ hmem
  have h2 := hlen (pairCode (natBits ((m - a.length) + (M + 1))) a)
  have hwlen : (pairCode (natBits ((m - a.length) + (M + 1))) a).length
      = 2 * (Nat.bits ((m - a.length) + (M + 1))).length + 1 + a.length := by
    rw [length_pairCode]
    simp only [natBits]
    omega
  have hfinal : (n : ℕ∞) ≤ ((2 * (Nat.bits ((m - a.length) + (M + 1))).length + 1
      + a.length + c_len + c_map : ℕ) : ℕ∞) := by
    calc (n : ℕ∞) ≤ plainK U (objFirstIncompressible U n) := hge
      _ ≤ plainK U (pairCode (natBits ((m - a.length) + (M + 1))) a) + (c_map : ℕ∞) := h1
      _ ≤ (((pairCode (natBits ((m - a.length) + (M + 1))) a).length : ℕ∞)
            + (c_len : ℕ∞)) + (c_map : ℕ∞) := by gcongr
      _ = ((2 * (Nat.bits ((m - a.length) + (M + 1))).length + 1
            + a.length + c_len + c_map : ℕ) : ℕ∞) := by rw [hwlen]; push_cast; ring
  have hnat : n ≤ 2 * (Nat.bits ((m - a.length) + (M + 1))).length + 1
      + a.length + c_len + c_map := Nat.cast_le.mp hfinal
  have hbig := hM ((m - a.length) + (M + 1)) (by omega)
  omega

/-- From the lexicographically first incompressible string of length `n` at parameter `n` one
computes the list of halting programs of length at most `n` at parameter `n - O(1)`. SUV
Theorem 15. -/
theorem firstIncompressible_reduces_haltingList (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 8 4 := by
  obtain ⟨K, hK1, hK⟩ := maxHaltingStage_le_of_allEarlierEnumerated U hU c hc
  have hg : Computable (fun z : (ℕ × BitString) × ℕ =>
      bif decide (z.1.1 < K) then canonicalObject U c 4 0
      else listCode ((boundedPrograms (z.1.1 - K)).filter
        (fun p => haltsWithin c z.2 p))) := by
    refine Computable.cond ?_ (Computable.const _) ?_
    · exact (PrimrecPred.decide (PrimrecRel.comp Primrec.nat_lt
        (Primrec.fst.comp Primrec.fst) (Primrec.const K))).to_comp
    · refine (listCode_primrec.comp (list_filter_primrec ?_ ?_)).to_comp
      · exact primrec_boundedPrograms.comp
          (Primrec₂.comp Primrec.nat_sub (Primrec.fst.comp Primrec.fst) (Primrec.const K))
      · exact (Primrec₂.comp (haltsWithin_primrec₂ c)
          (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  refine ⟨K, fun q => (Nat.rfind (fun T => Part.some (allEarlierEnumerated c q T))).map (fun T =>
    bif decide (q.1 < K) then canonicalObject U c 4 0
    else listCode ((boundedPrograms (q.1 - K)).filter (fun p => haltsWithin c T p))),
    ?_, ?_⟩
  · exact (Partrec.rfind (pred_primrec c).to_comp.partrec₂).map hg.to₂
  · intro n
    obtain ⟨T0, hT0, hrf⟩ := rfind_spec _ (pred_exists U c hc n)
    have hrf2 :
        Nat.rfind (fun T => Part.some (allEarlierEnumerated c (n, objFirstIncompressible U n) T))
        = Part.some T0 := hrf
    change ((Nat.rfind
        (fun T => Part.some (allEarlierEnumerated c (n, objFirstIncompressible U n) T))).map
      (fun T => bif decide (n < K) then canonicalObject U c 4 0
        else listCode ((boundedPrograms (n - K)).filter (fun p => haltsWithin c T p))))
      = Part.some (canonicalObject U c 4 (n - K))
    rw [hrf2, Part.map_some]
    by_cases hnk : n < K
    · rw [decide_eq_true hnk]
      simp only [cond_true]
      rw [show n - K = 0 by omega]
    · rw [decide_eq_false hnk]
      simp only [cond_false]
      push_neg at hnk
      rw [filter_haltsWithin_eq_haltingProgramsBounded c (n - K) T0 (hK n hnk T0 hT0)]
      rfl

/-- From the list of strings of complexity at most `n` at parameter `n` one computes the number of
strings of complexity at most `n` at parameter `n - O(1)`. SUV Theorem 15. -/
theorem complexityList_reduces_complexityCount (U : Map) (c : Code) : HubReduces U c 0 1 := by
  refine ⟨0, fun p => Part.some (natBits (decodeListCode p.2).length),
    listLengthCode_computable, fun n => ?_⟩
  simp only [Nat.sub_zero, canonicalObject, objComplexityList, objComplexityCount,
    decodeListCode_listCode, List.length_map]

/-- From the list of halting programs of length at most `n` at parameter `n` one computes the
number of halting programs of length at most `n` at parameter `n - O(1)`. SUV Theorem 15. -/
theorem haltingList_reduces_haltingCount (U : Map) (c : Code) : HubReduces U c 4 5 := by
  refine ⟨0, fun p => Part.some (natBits (decodeListCode p.2).length),
    listLengthCode_computable, fun n => ?_⟩
  simp only [Nat.sub_zero, canonicalObject, objHaltingList, objHaltingCount,
    decodeListCode_listCode]
/-- The canonical object the list of strings of complexity at most `n` reduces to the canonical
object the list of halting programs of length at most `n`: from the list of strings of complexity at
most `n` at parameter `n` one computes the list of halting programs of length at most `n` at
parameter `n - O(1)`. SUV Theorem 15. -/
theorem complexityList_reduces_haltingList (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 0 4 :=
  (complexityList_reduces_busyBeaver U c).trans' (busyBeaver_reduces_haltingList U hU c hc)

/-- The canonical object the number of strings of complexity at most `n` reduces to the canonical
object the list of halting programs of length at most `n`: from the number of strings of complexity
at most `n` at parameter `n` one computes the list of halting programs of length at most `n` at
parameter `n - O(1)`. SUV Theorem 15. -/
theorem complexityCount_reduces_haltingList (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 1 4 :=
  (complexityCount_reduces_busyBeaver U c).trans' (busyBeaver_reduces_haltingList U hU c hc)

/-- The canonical object the number of halting programs of length at most `n` reduces to the
canonical object the list of halting programs of length at most `n`: from the number of halting
programs of length at most `n` at parameter `n` one computes the list of halting programs of length
at most `n` at parameter `n - O(1)`. SUV Theorem 15. -/
theorem haltingCount_reduces_haltingList (U : Map) (c : Code) : HubReduces U c 5 4 :=
  (haltingCount_reduces_maxTime U c).trans' (maxTime_reduces_haltingList U c)

/-- The canonical object the list of halting programs of length at most `n` reduces to the canonical
object the list of strings of complexity at most `n`: from the list of halting programs of length at
most `n` at parameter `n` one computes the list of strings of complexity at most `n` at parameter
`n - O(1)`. SUV Theorem 15. -/
theorem haltingList_reduces_complexityList (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 4 0 :=
  (haltingList_reduces_maxTime U c).trans' (maxTime_reduces_complexityList U hU c hc)

/-- The canonical object the list of halting programs of length at most `n` reduces to the canonical
object the number of strings of complexity at most `n`: from the list of halting programs of length
at most `n` at parameter `n` one computes the number of strings of complexity at most `n` at
parameter `n - O(1)`. SUV Theorem 15. -/
theorem haltingList_reduces_complexityCount (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 4 1 :=
  (haltingList_reduces_complexityList U hU c hc).trans' (complexityList_reduces_complexityCount U c)

/-- The canonical object the list of halting programs of length at most `n` reduces to the canonical
object the busy-beaver value: from the list of halting programs of length at most `n` at parameter
`n` one computes the busy-beaver value at parameter `n - O(1)`. SUV Theorem 15. -/
theorem haltingList_reduces_busyBeaver (U : Map) (c : Code) : HubReduces U c 4 2 :=
  (haltingList_reduces_maxTime U c).trans' (maxTime_reduces_busyBeaver U c)

/-- The canonical object the list of halting programs of length at most `n` reduces to the canonical
object the graph of the complexity function on the strings of length `n`: from the list of halting
programs of length at most `n` at parameter `n` one computes the graph of the complexity function on
the strings of length `n` at parameter `n - O(1)`. SUV Theorem 15. -/
theorem haltingList_reduces_complexityGraph (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 4 7 :=
  (haltingList_reduces_maxTime U c).trans' (maxTime_reduces_complexityGraph U hU c hc)

/-- The canonical object the list of halting programs of length at most `n` reduces to the canonical
object the lexicographically first incompressible string of length `n`: from the list of halting
programs of length at most `n` at parameter `n` one computes the lexicographically first
incompressible string of length `n` at parameter `n - O(1)`. SUV Theorem 15. -/
theorem haltingList_reduces_firstIncompressible (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 4 8 :=
  (haltingList_reduces_complexityGraph U hU c hc).trans'
    (complexityGraph_reduces_firstIncompressible U hU c hc)

/-- The canonical object the slowest halting program of length at most `n` reduces to the canonical
object the list of halting programs of length at most `n`: from the slowest halting program of
length at most `n` at parameter `n` one computes the list of halting programs of length at most `n`
at parameter `n - O(1)`. SUV Theorem 15. -/
theorem slowestProgram_reduces_haltingList (U : Map) (c : Code) : HubReduces U c 6 4 :=
  (slowestProgram_reduces_maxTime U c).trans' (maxTime_reduces_haltingList U c)

/-- The canonical object the list of halting programs of length at most `n` reduces to the canonical
object the slowest halting program of length at most `n`: from the list of halting programs of
length at most `n` at parameter `n` one computes the slowest halting program of length at most `n`
at parameter `n - O(1)`. SUV Theorem 15. -/
theorem haltingList_reduces_slowestProgram (U : Map) (c : Code) : HubReduces U c 4 6 :=
  (haltingList_reduces_maxTime U c).trans' (maxTime_reduces_slowestProgram U c)

/-- The canonical object the graph of the complexity function on the strings of length `n` reduces
to the canonical object the list of halting programs of length at most `n`: from the graph of the
complexity function on the strings of length `n` at parameter `n` one computes the list of halting
programs of length at most `n` at parameter `n - O(1)`. SUV Theorem 15. -/
theorem complexityGraph_reduces_haltingList (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) : HubReduces U c 7 4 :=
  (complexityGraph_reduces_firstIncompressible U hU c hc).trans'
    (firstIncompressible_reduces_haltingList U hU c hc)

private theorem HubReduces.rfl' (U : Map) (c : Code) (i : ℕ) : HubReduces U c i i :=
  ⟨0, fun p => Part.some p.2, Computable.snd, fun n => by simp⟩

/-- Every canonical object reduces to the hub object, the list of halting programs. SUV Theorem
15. -/
theorem hub_in (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∀ i, i ≤ 8 → HubReduces U c i 4 := by
  intro i hi
  interval_cases i
  · exact complexityList_reduces_haltingList U hU c hc
  · exact complexityCount_reduces_haltingList U hU c hc
  · exact busyBeaver_reduces_haltingList U hU c hc
  · exact maxTime_reduces_haltingList U c
  · exact HubReduces.rfl' U c 4
  · exact haltingCount_reduces_haltingList U c
  · exact slowestProgram_reduces_haltingList U c
  · exact complexityGraph_reduces_haltingList U hU c hc
  · exact firstIncompressible_reduces_haltingList U hU c hc

/-- The hub object, the list of halting programs, reduces to every canonical object. SUV Theorem
15. -/
theorem hub_out (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∀ j, j ≤ 8 → HubReduces U c 4 j := by
  intro j hj
  interval_cases j
  · exact haltingList_reduces_complexityList U hU c hc
  · exact haltingList_reduces_complexityCount U hU c hc
  · exact haltingList_reduces_busyBeaver U c
  · exact haltingList_reduces_maxTime U c
  · exact HubReduces.rfl' U c 4
  · exact haltingList_reduces_haltingCount U c
  · exact haltingList_reduces_slowestProgram U c
  · exact haltingList_reduces_complexityGraph U hU c hc
  · exact haltingList_reduces_firstIncompressible U hU c hc
/-- An upper bound `n + k` on the complexity of a canonical object may be relaxed to any
larger constant. -/
theorem upper_mono {U : Map} {c : Code} {i k k' : ℕ} (h : k ≤ k')
    (H : ∀ n : ℕ, plainK U (canonicalObject U c i n) ≤ ((n + k : ℕ) : ℕ∞)) :
    ∀ n : ℕ, plainK U (canonicalObject U c i n) ≤ ((n + k' : ℕ) : ℕ∞) := fun n =>
  (H n).trans (by exact_mod_cast Nat.add_le_add_left h n)

/-- Object (b) at parameter `m` is reconstructible from the fixed-width Omega code, a
string of length `m + 1`; so every object that (b) reduces to has complexity `≤ n + O(1)`. -/
private theorem upper_of_red_1 (U : Map) (hU : isOptimalConditional U) (c : Code)
    (j : ℕ) (h : HubReduces U c 1 j) :
    ∃ k : ℕ, ∀ n : ℕ, plainK U (canonicalObject U c j n) ≤ ((n + k : ℕ) : ℕ∞) := by
  obtain ⟨kj, A, hA, hAeq⟩ := h
  obtain ⟨c_len, hlen⟩ := plainK_le_length U hU
  have hwidth : Computable (fun z : BitString => z.length - 1) :=
    (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)).to_comp
  have hcount : Computable (fun z : BitString => natBits (decodeFixedWidthNatCode z)) :=
    (primrec_natBits.comp decodeFixedWidthNatCode_primrec).to_comp
  have hF : Partrec (fun z : BitString =>
      A (z.length - 1, natBits (decodeFixedWidthNatCode z))) :=
    hA.comp (Computable.pair hwidth hcount)
  obtain ⟨C, hC⟩ := plainK_partrec_map_le U hU _ hF
  refine ⟨kj + 1 + c_len + C, fun n => ?_⟩
  set m := n + kj with hm
  have hlenm : (omegaFixedCode c m).length = m + 1 := omegaFixedCode_length c m
  have hdec : decodeFixedWidthNatCode (omegaFixedCode c m) = (completedBoundedOutput c m).length :=
    decode_omegaFixedCode c m
  have hmem : canonicalObject U c j n ∈
      A ((omegaFixedCode c m).length - 1,
        natBits (decodeFixedWidthNatCode (omegaFixedCode c m))) := by
    rw [hlenm, hdec, Nat.add_sub_cancel]
    have h1 : natBits (completedBoundedOutput c m).length = canonicalObject U c 1 m := rfl
    rw [h1, hAeq m]
    have h2 : m - kj = n := by omega
    rw [h2]
    exact Part.mem_some _
  have hK := hC (omegaFixedCode c m) (canonicalObject U c j n) hmem
  calc plainK U (canonicalObject U c j n)
      ≤ plainK U (omegaFixedCode c m) + (C : ℕ∞) := hK
    _ ≤ (((omegaFixedCode c m).length : ℕ∞) + (c_len : ℕ∞)) + (C : ℕ∞) := by
        gcongr
        exact hlen _
    _ = ((m + 1 + c_len + C : ℕ) : ℕ∞) := by rw [hlenm]; push_cast; ring
    _ = ((n + (kj + 1 + c_len + C) : ℕ) : ℕ∞) := by rw [hm]; push_cast; ring

private theorem hubReduces_complexityCount_le_eight (U : Map) (hU : isOptimalConditional U)
    (c : Code)
    (hc : IsCodeFor c U) : ∀ j, j ≤ 8 → HubReduces U c 1 j := by
  intro j hj
  exact (complexityCount_reduces_haltingList U hU c hc).trans' (hub_out U hU c hc j hj)

/-- All nine canonical objects have complexity at most `n + O(1)`. SUV Theorem 15. -/
theorem upper (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) :
    ∃ k : ℕ, ∀ i, i ≤ 8 → ∀ n : ℕ,
      plainK U (canonicalObject U c i n) ≤ ((n + k : ℕ) : ℕ∞) := by
  obtain ⟨k0, h0⟩ :=
    upper_of_red_1 U hU c 0 (hubReduces_complexityCount_le_eight U hU c hc 0 (by omega))
  obtain ⟨k1, h1⟩ :=
    upper_of_red_1 U hU c 1 (hubReduces_complexityCount_le_eight U hU c hc 1 (by omega))
  obtain ⟨k2, h2⟩ :=
    upper_of_red_1 U hU c 2 (hubReduces_complexityCount_le_eight U hU c hc 2 (by omega))
  obtain ⟨k3, h3⟩ :=
    upper_of_red_1 U hU c 3 (hubReduces_complexityCount_le_eight U hU c hc 3 (by omega))
  obtain ⟨k4, h4⟩ :=
    upper_of_red_1 U hU c 4 (hubReduces_complexityCount_le_eight U hU c hc 4 (by omega))
  obtain ⟨k5, h5⟩ :=
    upper_of_red_1 U hU c 5 (hubReduces_complexityCount_le_eight U hU c hc 5 (by omega))
  obtain ⟨k6, h6⟩ :=
    upper_of_red_1 U hU c 6 (hubReduces_complexityCount_le_eight U hU c hc 6 (by omega))
  obtain ⟨k7, h7⟩ :=
    upper_of_red_1 U hU c 7 (hubReduces_complexityCount_le_eight U hU c hc 7 (by omega))
  obtain ⟨k8, h8⟩ :=
    upper_of_red_1 U hU c 8 (hubReduces_complexityCount_le_eight U hU c hc 8 (by omega))
  refine ⟨k0 + k1 + k2 + k3 + k4 + k5 + k6 + k7 + k8, fun i hi => ?_⟩
  interval_cases i
  · exact upper_mono (by omega) h0
  · exact upper_mono (by omega) h1
  · exact upper_mono (by omega) h2
  · exact upper_mono (by omega) h3
  · exact upper_mono (by omega) h4
  · exact upper_mono (by omega) h5
  · exact upper_mono (by omega) h6
  · exact upper_mono (by omega) h7
  · exact upper_mono (by omega) h8
/-- A `find?` that succeeds returns an element satisfying the predicate. -/
private theorem find_getD_spec {p : BitString → Bool} {l : List BitString}
    {P : BitString → Prop} (hP : ∀ x, p x = true → P x)
    (hex : ∃ x ∈ l, p x = true) : P ((l.find? p).getD []) := by
  rcases hfind : l.find? p with _ | γ
  · exfalso
    rw [List.find?_eq_none] at hfind
    obtain ⟨x, hx, hpx⟩ := hex
    exact hfind x hx hpx
  · exact hP γ (List.find?_some hfind)

/-- The lexicographically first incompressible string of length `n` has complexity at least `n`.
The lexicographically first incompressible string of length `n` has complexity at least `n`. -/
theorem objFirstIncompressible_spec (U : Map) (n : ℕ) :
    (n : ℕ∞) ≤ plainK U (objFirstIncompressible U n) := by
  obtain ⟨s, hslen, hs⟩ := exists_incompressible_string U [] n
  have hsmem : s ∈ allStrings n := (mem_allStrings n s).mpr hslen
  unfold objFirstIncompressible
  refine find_getD_spec (P := fun z => (n : ℕ∞) ≤ plainK U z) ?_ ?_
  · intro x hx
    exact of_decide_eq_true hx
  · exact ⟨s, hsmem, decide_eq_true (show (n : ℕ∞) ≤ plainK U s from hs)⟩

/-- The lexicographically first incompressible string of length `n` has complexity at
least `n - O(1)`. -/
theorem lower_8 (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U) : ∃ k : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK U (canonicalObject U c 8 n) + (k : ℕ∞) := by
  have _hU := hU
  have _hc := hc
  refine ⟨0, fun n => ?_⟩
  simpa using objFirstIncompressible_spec U n

/-- Reads the lexicographically first incompressible string off the graph of the complexity
function on the strings of a given length. -/
def graphToGamma (w : BitString) : BitString :=
  (((decodeListCode w).find? (fun z =>
      decide ((decodeFirst ((decodeListCode w).headI)).length ≤
        decodeBits (decodeSecond z)))).map decodeFirst).getD []

private theorem allStrings_ne_nil (n : ℕ) : allStrings n ≠ [] := by
  refine List.ne_nil_of_length_pos ?_
  rw [length_allStrings]
  positivity

/-- The first entry of the complexity graph of level `n` records a string of length `n`. -/
theorem head_length (U : Map) (n : ℕ) :
    (decodeFirst (((allStrings n).map
        (fun x => pairCode x (natBits (cVal U x)))).headI)).length = n := by
  obtain ⟨x₀, rest, hcons⟩ := List.exists_cons_of_ne_nil (allStrings_ne_nil n)
  have hx₀ : x₀ ∈ allStrings n := by rw [hcons]; exact List.mem_cons_self ..
  rw [hcons]
  simp only [List.map_cons, List.headI_cons, decodeFirst_pairCode]
  exact (mem_allStrings n x₀).mp hx₀

/-- The natural-valued and `ℕ∞`-valued plain complexities agree on lower bounds. -/
theorem le_cVal_iff_le_plainK (U : Map) (hU : isOptimalConditional U) (n : ℕ) (x : BitString) :
    (n ≤ cVal U x) ↔ ((n : ℕ∞) ≤ plainK U x) := by
  obtain ⟨c_len, hlen⟩ := plainK_le_length U hU
  have hne : plainK U x ≠ ⊤ := by
    have h_top : ((x.length + c_len : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
    intro h_inf
    have h_le := hlen x
    rw [h_inf] at h_le
    exact h_top (top_le_iff.mp h_le)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have hcv : cVal U x = m := by
    unfold cVal
    rw [← hm]
    exact ENat.toNat_coe m
  rw [hcv, ← hm]
  exact Nat.cast_le.symm

/-- Searching a list with pointwise equal predicates gives the same result. -/
theorem find_congr {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.find?_cons, ha, ht]

/-- The complexity graph of level `n` determines the lexicographically first
incompressible string of length `n`. -/
theorem graphToGamma_spec (U : Map) (hU : isOptimalConditional U) (n : ℕ) :
    graphToGamma (objComplexityGraph U n) = objFirstIncompressible U n := by
  have hdec : decodeListCode (objComplexityGraph U n)
      = (allStrings n).map (fun x => pairCode x (natBits (cVal U x))) := by
    unfold objComplexityGraph
    rw [decodeListCode_listCode]
  have hcomp : ∀ o : Option BitString,
      o.map (decodeFirst ∘ (fun x => pairCode x (natBits (cVal U x)))) = o := by
    intro o
    cases o with
    | none => rfl
    | some x => simp only [Option.map_some, Function.comp_apply, decodeFirst_pairCode]
  unfold graphToGamma
  rw [hdec, head_length U n, List.find?_map, Option.map_map, hcomp]
  unfold objFirstIncompressible
  refine congrArg (fun o : Option BitString => o.getD []) ?_
  refine find_congr _ _ _ (fun x _ => ?_)
  change decide (n ≤ decodeBits (decodeSecond (pairCode x (natBits (cVal U x))))) = _
  simp only [decodeSecond_pairCode, natBits, decodeBits_natBits]
  exact decide_eq_decide.mpr (le_cVal_iff_le_plainK U hU n x)

end Kolmogorov
