import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.CommonInformation.ConditionalIndependence
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.ConditionalComplexity.Continuity
import KolmogorovMathlib.Complexity.KolmogorovLevin.LogarithmicGap

/-!
# How many short descriptions a string has

`condK_le_of_many_descriptions` (SUV Exercise 39): if `x` has `2 ^ k` descriptions of length
at most `n`, then `x` is cheap given `n` and `k` — the strings with many short descriptions
are few, and can be enumerated.  That enumeration is `stageQual` and `accumQual`, built from
`evalDAt` and the description count `descCountAt`.

`card_shortestDescriptions_le` (Exercise 40) is the companion: for an optimal decompressor
every string has only `O(1)` shortest descriptions.  `padBits`, with its round-trip lemmas, is
the fixed-width numeral the enumeration indices are written in.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
namespace ShortDescriptions

open Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- The output of the machine `c_D` on the program `q` if it halts within `t` steps. -/
def evalDAt (c_D : Code) (q : BitString) (t : ℕ) : Option BitString :=
  match Nat.Partrec.Code.evaln t c_D (Nat.pair (Encodable.encode q) 0) with
  | none => none
  | some m => Encodable.decode m

/-- The number of programs of length at most `n` that output `x` within `t` steps. -/
def descCountAt (c_D : Code) (n t : ℕ) (x : BitString) : ℕ :=
  ((boundedPrograms n).filter (fun q =>
    match evalDAt c_D q t with
    | none => false
    | some x' => decide (x' = x))).length

/-- The strings that by stage `t` already have at least `2 ^ k` descriptions of length at most
`n`, without repetitions. -/
def stageQual (c_D : Code) (k n t : ℕ) : List BitString :=
  let progs := (boundedPrograms n).filter (fun q =>
    match evalDAt c_D q t with
    | none => false
    | some x => decide (2 ^ k ≤ descCountAt c_D n t x))
  (progs.map (fun q => (evalDAt c_D q t).getD [])).eraseDups

/-- The strings with at least `2 ^ k` short descriptions, accumulated over all stages up to `t`
in order of first appearance. -/
def accumQual (c_D : Code) (k n : ℕ) : ℕ → List BitString
  | 0 => stageQual c_D k n 0
  | t + 1 => (accumQual c_D k n t ++ stageQual c_D k n (t + 1)).eraseDups

/-- The binary digits of `i`, padded with zeros on the right to width `m`. -/
def padBits (i m : ℕ) : BitString :=
  Nat.bits i ++ List.replicate (m - (Nat.bits i).length) false

/-- An all-zero string denotes the number zero. -/
lemma decodeBits_replicate_false (L : ℕ) : decodeBits (List.replicate L false) = 0 := by
  induction L with
  | zero => rfl
  | succ L ih =>
    dsimp [List.replicate, decodeBits]
    rw [ih]

/-- Padding a number with at most `m` binary digits to width `m` gives a string of length `m`. -/
lemma padBits_length (i m : ℕ) (hi : (Nat.bits i).length ≤ m) :
    (padBits i m).length = m := by
  dsimp [padBits]
  rw [List.length_append, List.length_replicate]
  omega

/-- Padding is inverted by decoding: `padBits i m` denotes `i`. -/
lemma padBits_decodeBits (i m : ℕ) : decodeBits (padBits i m) = i := by
  dsimp [padBits]
  rw [decodeBits_append_replicate_false, decodeBits_natBits]

/-- An all-zero string is read as the number zero. -/
lemma bitsToNat_replicate_false (L : ℕ) : bitsToNat (List.replicate L false) = 0 := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change 2 * bitsToNat (List.replicate L false) + 0 = 0
    rw [ih]

/-- Appending trailing zeros does not change the number a string is read as. -/
lemma bitsToNat_app_replicate_false (bs : List Bool) (L : ℕ) :
    bitsToNat (bs ++ List.replicate L false) = bitsToNat bs := by
  induction bs with
  | nil =>
    rw [List.nil_append]
    exact bitsToNat_replicate_false L
  | cons b bs ih =>
    cases b
    · change 2 * bitsToNat (bs ++ List.replicate L false) + 0 = 2 * bitsToNat bs + 0
      rw [ih]
    · change 2 * bitsToNat (bs ++ List.replicate L false) + 1 = 2 * bitsToNat bs + 1
      rw [ih]

/-- Reading `padBits i m` as a number gives `i` back. -/
lemma padBits_bitsToNat (i m : ℕ) : bitsToNat (padBits i m) = i := by
  dsimp [padBits]
  rw [bitsToNat_app_replicate_false, bitsToNat_bits]

/-- Running the machine `c_D` for a bounded number of steps is primitive recursive in the
program and the step bound. -/
theorem evalDAt_primrec (c_D : Code) : Primrec (fun p : BitString × ℕ => evalDAt c_D p.1 p.2) := by
  dsimp [evalDAt]
  have h_pair : Primrec (fun p : BitString × ℕ => Nat.pair (Encodable.encode p.1) 0) :=
    (Primrec₂.natPair.comp Primrec.encode (Primrec.const 0)).comp Primrec.fst
  have h_evaln : Primrec (fun p : BitString × ℕ =>
      Code.evaln p.2 c_D (Nat.pair (Encodable.encode p.1) 0)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair Primrec.snd (Primrec.const c_D)) h_pair)
  have h_dec : Primrec (fun m : Option ℕ =>
      m.bind (fun n => (Encodable.decode n : Option BitString))) :=
    Primrec.option_bind Primrec.id
      (Primrec.decode.comp (Primrec.snd (α := Option ℕ) (β := ℕ))).to₂
  exact (h_dec.comp h_evaln).of_eq (by
    intro p
    cases Code.evaln p.2 c_D (Nat.pair (Encodable.encode p.1) 0) <;> simp)

/-- The number of short descriptions found by stage `t` is primitive recursive in the length
bound, the stage and the string. -/
theorem descCountAt_primrec (c_D : Code) :
    Primrec (fun p : ((ℕ × ℕ) × BitString) => descCountAt c_D p.1.1 p.1.2 p.2) := by
  dsimp [descCountAt]
  have h_bp : Primrec (fun p : (ℕ × ℕ) × BitString => boundedPrograms p.1.1) :=
    primrec_boundedPrograms.comp (Primrec.fst.comp Primrec.fst)
  have h_ev : Primrec (fun p : ((ℕ × ℕ) × BitString) × BitString => evalDAt c_D p.2 p.1.1.2) :=
    (evalDAt_primrec c_D).comp
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have h_body : Primrec (fun p : ((ℕ × ℕ) × BitString) × BitString =>
      bif (evalDAt c_D p.2 p.1.1.2).isSome then
        decide ((evalDAt c_D p.2 p.1.1.2).getD [] = p.1.2)
      else false) := by
    have h_eq : Primrec (fun p : ((ℕ × ℕ) × BitString) × BitString =>
        decide ((evalDAt c_D p.2 p.1.1.2).getD [] = p.1.2)) :=
      (PrimrecPred.decide Primrec.eq).comp
        (Primrec.pair (Primrec.option_getD.comp h_ev (Primrec.const []))
          (Primrec.snd.comp Primrec.fst))
    exact Primrec.cond (Primrec.option_isSome.comp h_ev) h_eq (Primrec.const false)
  have h_cond : Primrec (fun p : ((ℕ × ℕ) × BitString) × BitString =>
      match evalDAt c_D p.2 p.1.1.2 with
      | none => false
      | some x' => decide (x' = p.1.2)) :=
    h_body.of_eq (by intro p; cases evalDAt c_D p.2 p.1.1.2 <;> simp)
  have h_filt : Primrec (fun p : (ℕ × ℕ) × BitString =>
      (boundedPrograms p.1.1).filter (fun q =>
        match evalDAt c_D q p.1.2 with
        | none => false
        | some x' => decide (x' = p.2))) :=
    list_filter_primrec h_bp h_cond.to₂
  exact Primrec.list_length.comp h_filt

/-- Decides whether the program `q` has produced, by stage `t`, a string with at least `2 ^ k`
descriptions of length at most `n`. -/
def checkQual (c_D : Code) (k n t : ℕ) (q : BitString) : Bool :=
  match evalDAt c_D q t with
  | none => false
  | some x => decide (2 ^ k ≤ descCountAt c_D n t x)

/-- The qualification test is primitive recursive in all its arguments. -/
theorem checkQual_primrec (c_D : Code) :
    Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString => checkQual c_D p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  dsimp [checkQual]
  have h_ev : Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString => evalDAt c_D p.2 p.1.2) :=
    (evalDAt_primrec c_D).comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
  have h_pow : Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString => 2 ^ p.1.1.1) :=
    Kolmogorov.primrec_two_pow_aux.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have h_getD : Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString => (evalDAt c_D p.2 p.1.2).getD []) :=
    Primrec.option_getD.comp h_ev (Primrec.const [])
  have h_cnt_arg : Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString =>
      ((p.1.1.2, p.1.2), (evalDAt c_D p.2 p.1.2).getD [])) :=
    Primrec.pair (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)) h_getD
  have h_cnt : Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString =>
      descCountAt c_D p.1.1.2 p.1.2 ((evalDAt c_D p.2 p.1.2).getD [])) :=
    (descCountAt_primrec c_D).comp h_cnt_arg
  have h_le : Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString =>
      decide (2 ^ p.1.1.1 ≤ descCountAt c_D p.1.1.2 p.1.2 ((evalDAt c_D p.2 p.1.2).getD []))) :=
    (PrimrecPred.decide Primrec.nat_le).comp (Primrec.pair h_pow h_cnt)
  have h_cond_body : Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString =>
      bif (evalDAt c_D p.2 p.1.2).isSome then
        decide (2 ^ p.1.1.1 ≤ descCountAt c_D p.1.1.2 p.1.2 ((evalDAt c_D p.2 p.1.2).getD []))
      else false) :=
    Primrec.cond (Primrec.option_isSome.comp h_ev) h_le (Primrec.const false)
  exact h_cond_body.of_eq (by intro p; cases evalDAt c_D p.2 p.1.2 <;> rfl)

/-- The stage-`t` list of qualifying strings is primitive recursive in the parameters. -/
theorem stageQual_primrec (c_D : Code) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => stageQual c_D p.1.1 p.1.2 p.2) := by
  dsimp [stageQual]
  have h_bp : Primrec (fun p : (ℕ × ℕ) × ℕ => boundedPrograms p.1.2) :=
    primrec_boundedPrograms.comp (Primrec.snd.comp Primrec.fst)
  have h_check : Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString =>
      checkQual c_D p.1.1.1 p.1.1.2 p.1.2 p.2) :=
    checkQual_primrec c_D
  have h_ev : Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString => evalDAt c_D p.2 p.1.2) :=
    (evalDAt_primrec c_D).comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
  have h_getD : Primrec (fun p : ((ℕ × ℕ) × ℕ) × BitString => (evalDAt c_D p.2 p.1.2).getD []) :=
    Primrec.option_getD.comp h_ev (Primrec.const [])
  have h_progs : Primrec (fun p : (ℕ × ℕ) × ℕ =>
      (boundedPrograms p.1.2).filter (fun q => checkQual c_D p.1.1 p.1.2 p.2 q)) :=
    list_filter_primrec h_bp h_check.to₂
  have h_map : Primrec (fun p : (ℕ × ℕ) × ℕ =>
      ((boundedPrograms p.1.2).filter (fun q =>
        checkQual c_D p.1.1 p.1.2 p.2 q)).map (fun q => (evalDAt c_D q p.2).getD [])) :=
    Primrec.list_map h_progs h_getD.to₂
  exact eraseDups_bitstring_primrec.comp h_map

/-- The accumulated list of qualifying strings is primitive recursive in the parameters. -/
theorem accumQual_primrec (c_D : Code) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => accumQual c_D p.1.1 p.1.2 p.2) := by
  have h_base : Primrec (fun p : (ℕ × ℕ) × ℕ => stageQual c_D p.1.1 p.1.2 0) :=
    (stageQual_primrec c_D).comp (Primrec.pair Primrec.fst (Primrec.const 0))
  have h_sq_step : Primrec (fun p : ((ℕ × ℕ) × ℕ) × (ℕ × List BitString) =>
      stageQual c_D p.1.1.1 p.1.1.2 (p.2.1 + 1)) :=
    (stageQual_primrec c_D).comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
  have h_app : Primrec (fun p : ((ℕ × ℕ) × ℕ) × (ℕ × List BitString) =>
      p.2.2 ++ stageQual c_D p.1.1.1 p.1.1.2 (p.2.1 + 1)) :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.snd) h_sq_step
  have h_step : Primrec (fun p : ((ℕ × ℕ) × ℕ) × (ℕ × List BitString) =>
      (p.2.2 ++ stageQual c_D p.1.1.1 p.1.1.2 (p.2.1 + 1)).eraseDups) :=
    eraseDups_bitstring_primrec.comp h_app
  have h_rec := Primrec.nat_rec' Primrec.snd h_base h_step.to₂
  refine h_rec.of_eq ?_
  intro p
  induction p.2 with
  | zero => rfl
  | succ t ih => simp [accumQual, ih]

/-- The accumulated list of qualifying strings is computable in the parameters. -/
theorem accumQual_computable (c_D : Code) :
    Computable (fun p : (ℕ × ℕ) × ℕ => accumQual c_D p.1.1 p.1.2 p.2) :=
  (accumQual_primrec c_D).to_comp

/-- The accumulated list of qualifying strings has no repetitions. -/
lemma accumQual_nodup (c_D : Code) (k n t : ℕ) : (accumQual c_D k n t).Nodup := by
  cases t
  · exact nodup_eraseDups_bitString _
  · exact nodup_eraseDups_bitString _

/-- Each accumulated stage is a prefix of the next, so the enumeration order is stable. -/
lemma accumQual_prefix (c_D : Code) (k n t : ℕ) :
    accumQual c_D k n t <+: accumQual c_D k n (t + 1) := by
  dsimp [accumQual]
  exact prefix_eraseDups_append_of_nodup _ _ (accumQual_nodup c_D k n t)

/-- The accumulated list at an earlier stage is a prefix of the one at a later stage. -/
lemma accumQual_le_of_le (c_D : Code) (k n t1 t2 : ℕ) (h : t1 ≤ t2) :
    accumQual c_D k n t1 <+: accumQual c_D k n t2 := by
  induction h with
  | refl => exact List.prefix_rfl
  | step h_le ih => exact ih.trans (accumQual_prefix c_D k n _)

/-- Everything qualifying at stage `t` is in the accumulated list at stage `t`. -/
lemma stageQual_subset_accumQual (c_D : Code) (k n t : ℕ) (x : BitString)
    (h : x ∈ stageQual c_D k n t) : x ∈ accumQual c_D k n t := by
  induction t with
  | zero => exact h
  | succ s ih =>
    dsimp [accumQual]
    rw [mem_eraseDups_bitString, List.mem_append]
    exact Or.inr h

/-- Counting descriptions: at most `2 ^ n / 2 ^ k` strings can have `2 ^ k` descriptions of
length at most `n` each, since the descriptions are disjoint sets of programs. -/
lemma accumQual_card_le (c_D : Code) (k n t : ℕ) :
    (accumQual c_D k n t).length * 2 ^ k ≤ (boundedPrograms n).length := by
  let L := accumQual c_D k n t
  let S := L.toFinset
  let progs := boundedPrograms n
  have h_nodup : L.Nodup := accumQual_nodup c_D k n t
  have h_card_S : S.card = L.length := List.toFinset_card_of_nodup h_nodup
  have h_qual : ∀ y ∈ S, 2 ^ k ≤ descCountAt c_D n t y := by
    intro y hy
    induction t with
    | zero =>
      change y ∈ (accumQual c_D k n 0).toFinset at hy
      rw [accumQual.eq_def] at hy
      dsimp [stageQual] at hy
      rw [List.mem_toFinset, mem_eraseDups_bitString, List.mem_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      rw [List.mem_filter] at hq
      cases h_ev : evalDAt c_D q 0 with
      | none =>
        exfalso
        rw [h_ev] at hq
        simp at hq
      | some x' =>
        rw [h_ev] at hq
        exact decide_eq_true_iff.mp hq.2
    | succ s ih =>
      change y ∈ (accumQual c_D k n (s + 1)).toFinset at hy
      rw [accumQual.eq_def] at hy
      rw [List.mem_toFinset, mem_eraseDups_bitString, List.mem_append] at hy
      cases hy with
      | inl h_old =>
        have h_old_le := ih (accumQual_nodup c_D k n s)
          (List.toFinset_card_of_nodup (accumQual_nodup c_D k n s))
          (List.mem_toFinset.mpr h_old)
        refine h_old_le.trans ?_
        dsimp [descCountAt]
        have h1 : ((boundedPrograms n).filter (fun q =>
            match evalDAt c_D q s with
            | none => false
            | some x' => decide (x' = y))).toFinset ⊆
            ((boundedPrograms n).filter (fun q =>
            match evalDAt c_D q (s + 1) with
            | none => false
            | some x' => decide (x' = y))).toFinset := by
          intro q hq
          rw [List.mem_toFinset, List.mem_filter] at hq ⊢
          obtain ⟨hq_bp, hq_eval⟩ := hq
          refine ⟨hq_bp, ?_⟩
          dsimp [evalDAt] at hq_eval ⊢
          cases h_evaln : Code.evaln s c_D (Nat.pair (Encodable.encode q) 0) with
          | none =>
            exfalso
            rw [h_evaln] at hq_eval
            dsimp at hq_eval
            cases hq_eval
          | some val =>
            have h_mono := Code.evaln_mono (Nat.le_succ s) (Option.mem_def.mpr h_evaln)
            rw [Option.mem_def.mp h_mono]
            rw [h_evaln] at hq_eval
            exact hq_eval
        have h2 := Finset.card_le_card h1
        rw [List.toFinset_card_of_nodup (List.Nodup.filter _ (boundedPrograms_nodup n)),
            List.toFinset_card_of_nodup (List.Nodup.filter _ (boundedPrograms_nodup n))] at h2
        exact h2
      | inr h_new =>
        dsimp [stageQual] at h_new
        rw [mem_eraseDups_bitString, List.mem_map] at h_new
        obtain ⟨q, hq, rfl⟩ := h_new
        rw [List.mem_filter] at hq
        cases h_ev : evalDAt c_D q (s + 1) with
        | none =>
          exfalso
          rw [h_ev] at hq
          simp at hq
        | some x' =>
          rw [h_ev] at hq
          exact decide_eq_true_iff.mp hq.2
  let f : BitString → Finset BitString := fun y =>
    ((boundedPrograms n).filter (fun q =>
      match evalDAt c_D q t with
      | none => false
      | some x' => decide (x' = y))).toFinset
  have h_f_card : ∀ y ∈ S, (f y).card = descCountAt c_D n t y := by
    intro y hy
    dsimp [f, descCountAt]
    exact List.toFinset_card_of_nodup (List.Nodup.filter _ (boundedPrograms_nodup n))
  have h_disj : ∀ y1 ∈ S, ∀ y2 ∈ S, y1 ≠ y2 → Disjoint (f y1) (f y2) := by
    intro y1 hy1 y2 hy2 hne
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    dsimp [f] at hq1 hq2
    rw [List.mem_toFinset, List.mem_filter] at hq1 hq2
    cases h_ev : evalDAt c_D q t with
    | none =>
      rw [h_ev] at hq1
      exact False.elim (by revert hq1; simp)
    | some x' =>
      rw [h_ev] at hq1 hq2
      have h1 : x' = y1 := by simpa using hq1.2
      have h2 : x' = y2 := by simpa using hq2.2
      subst h1 h2
      exact hne rfl
  have h_biUnion_sub : S.biUnion f ⊆ progs.toFinset := by
    intro q hq
    rw [Finset.mem_biUnion] at hq
    obtain ⟨y, hy, hqy⟩ := hq
    dsimp [f] at hqy
    rw [List.mem_toFinset, List.mem_filter] at hqy
    rw [List.mem_toFinset]
    exact hqy.1
  have h_sum_f : ∑ y ∈ S, (f y).card = (S.biUnion f).card := by
    rw [Finset.card_biUnion]
    intro y1 hy1 y2 hy2 hne
    exact h_disj y1 hy1 y2 hy2 hne
  have h_card_biUnion : (S.biUnion f).card ≤ progs.toFinset.card :=
    Finset.card_le_card h_biUnion_sub
  rw [List.toFinset_card_of_nodup (boundedPrograms_nodup n)] at h_card_biUnion
  have h_sum_ge : L.length * 2 ^ k ≤ ∑ y ∈ S, (f y).card := by
    have h_f_sum : ∑ y ∈ S, descCountAt c_D n t y = ∑ y ∈ S, (f y).card :=
      Finset.sum_congr rfl (fun y hy => (h_f_card y hy).symm)
    calc L.length * 2 ^ k = S.card * 2 ^ k := by rw [h_card_S]
      _ = ∑ y ∈ S, 2 ^ k := by simp [Finset.sum_const]
      _ ≤ ∑ y ∈ S, descCountAt c_D n t y :=
          Finset.sum_le_sum (fun y hy => h_qual y hy)
      _ = ∑ y ∈ S, (f y).card := h_f_sum
  exact h_sum_ge.trans (h_sum_f.symm ▸ h_card_biUnion)

/-- Decompressor that reads `k` from the condition and an index from the program, and outputs
the string at that index in the enumeration of the strings with `2 ^ k` short descriptions. -/
def D_sim (c_D : Code) : Map := fun p : BitString × BitString =>
  let k := decodeBits p.2
  let m := p.1.length - 1
  let n := m + k
  let idx := bitsToNat p.1
  (Nat.rfind (fun t => Part.some (decide (idx < (accumQual c_D k n t).length)))).bind
    (fun t => Part.some ((accumQual c_D k n t).getD idx []))

/-- The enumeration decompressor is a conditional decompressor. -/
theorem D_sim_isDecompressor (c_D : Code) : isDecompressor (D_sim c_D) := by
  dsimp [D_sim, isDecompressor]
  have h_k : Computable (fun p : BitString × BitString => decodeBits p.2) :=
    primrec_decodeBits.to_comp.comp Computable.snd
  have h_m : Computable (fun p : BitString × BitString => p.1.length - 1) :=
    (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)).to_comp.comp Computable.fst
  have h_pair_mk : Computable (fun p : BitString × BitString => (p.1.length - 1, decodeBits p.2)) :=
    Computable.pair h_m h_k
  have h_n : Computable (fun p : BitString × BitString => p.1.length - 1 + decodeBits p.2) :=
    Computable.comp Primrec.nat_add.to_comp h_pair_mk
  have h_idx : Computable (fun p : BitString × BitString => bitsToNat p.1) :=
    bitsToNat_primrec.to_comp.comp Computable.fst
  have h_acc : Computable (fun p : (BitString × BitString) × ℕ =>
      accumQual c_D (decodeBits p.1.2) (p.1.1.length - 1 + decodeBits p.1.2) p.2) :=
    (accumQual_computable c_D).comp
      (Computable.pair (Computable.pair (h_k.comp Computable.fst)
        (h_n.comp Computable.fst)) Computable.snd)
  have h_len : Computable (fun p : (BitString × BitString) × ℕ =>
      (accumQual c_D (decodeBits p.1.2) (p.1.1.length - 1 + decodeBits p.1.2) p.2).length) :=
    Computable.list_length.comp h_acc
  have h_idx' : Computable (fun p : (BitString × BitString) × ℕ => bitsToNat p.1.1) :=
    h_idx.comp Computable.fst
  have h_lt : Computable₂ (fun a b : ℕ => decide (a < b)) :=
    (PrimrecPred.decide Primrec.nat_lt).to_comp
  have h_check : Computable₂ (fun (p : BitString × BitString) (t : ℕ) =>
      decide (bitsToNat p.1 <
        (accumQual c_D (decodeBits p.2) (p.1.length - 1 + decodeBits p.2) t).length)) :=
    h_lt.comp h_idx' h_len
  have h_getD : Computable₂ (fun (l : List BitString) (n : ℕ) => l.getD n []) :=
    (Primrec.list_getD []).to_comp
  have h_post : Computable₂ (fun (p : BitString × BitString) (t : ℕ) =>
      (accumQual c_D (decodeBits p.2)
        (p.1.length - 1 + decodeBits p.2) t).getD (bitsToNat p.1) []) :=
    h_getD.comp h_acc h_idx'
  exact Partrec.bind (Partrec.rfind h_check.partrec₂) h_post.partrec₂

/-- Descriptions of length at most `n` are among the programs of length at most `n`. -/
lemma descriptionsLe_subset (D : Map) (x : BitString) (n : ℕ) :
    descriptionsLe D x n ⊆ (boundedPrograms n).toFinset := by
  intro p hp
  dsimp [descriptionsLe] at hp
  rw [Finset.mem_coe, List.mem_toFinset, mem_boundedPrograms_iff]
  exact hp.2

/-- A string with `2 ^ k` descriptions of length at most `n` forces `k ≤ n`. -/
lemma k_le_n_of_many_desc (D : Map) (n k : ℕ) (x : BitString)
    (_hfin : (descriptionsLe D x n).Finite)
    (hcard : 2 ^ k ≤ (descriptionsLe D x n).ncard) : k ≤ n := by
  by_contra hlt
  push Not at hlt
  have h1 : (descriptionsLe D x n).ncard ≤ ((boundedPrograms n).toFinset : Set BitString).ncard :=
    Set.ncard_le_ncard (descriptionsLe_subset D x n) (boundedPrograms n).toFinset.finite_toSet
  have h2 : ((boundedPrograms n).toFinset : Set BitString).ncard = (boundedPrograms n).length := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup (boundedPrograms_nodup n)]
  have h3 : (boundedPrograms n).length < 2 ^ (n + 1) := length_boundedPrograms_lt n
  have h4 : 2 ^ (n + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hlt
  omega

/-- A program producing `x` from `y` bounds the conditional complexity of `x` given `y` with
respect to that decompressor by its length. -/
lemma condK_le_of_produces (D : Map) (p y x : BitString) (hp : x ∈ D (p, y)) :
    condK D x y ≤ (p.length : ℕ∞) := by
  dsimp [condK]
  exact sInf_le ⟨p, hp, rfl⟩

end ShortDescriptions

/-- Finds a step bound at which all short descriptions of `x` have evaluated under machine code
`c_D`. -/
private lemma exists_step_evalDAt_eq (D : Map) (c_D : Code)
    (hc_D : c_D.eval = fun n => (Part.ofOption (Encodable.decode n)).bind
      (fun a => Part.map Encodable.encode (D a)))
    (n : ℕ) (x : BitString) (hfin : (descriptionsLe D x n).Finite) :
    ∃ maxStep : ℕ, ∀ p ∈ descriptionsLe D x n,
      ShortDescriptions.evalDAt c_D p maxStep = some x := by
  have h_eval_code : ∀ p ∈ descriptionsLe D x n, ∃ s,
      (Nat.Partrec.Code.evaln s c_D (Nat.pair (Encodable.encode p) 0)).isSome = true := by
    intro p hp
    have hp_prod : x ∈ D (p, []) := hp.1
    have h_enc_mem : Encodable.encode x ∈ Part.map Encodable.encode (D (p, [])) :=
      Part.mem_map Encodable.encode hp_prod
    have h_eval_eq_map : Code.eval c_D (Nat.pair (Encodable.encode p) 0) =
        Part.map Encodable.encode (D (p, [])) := by
      rw [hc_D]
      dsimp
      have h_dec : Encodable.decode (α := BitString × BitString)
          (Nat.pair (Encodable.encode p) 0) = some (p, []) :=
        Encodable.encodek (p, ([] : BitString))
      rw [h_dec]
      ext z
      simp
    have h_eval_mem : Encodable.encode x ∈ Code.eval c_D (Nat.pair (Encodable.encode p) 0) :=
      h_eval_eq_map.symm ▸ h_enc_mem
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp h_eval_mem
    exact ⟨s, Option.isSome_iff_exists.mpr ⟨Encodable.encode x, hs⟩⟩
  choose stepOf hstepOf using h_eval_code
  let step_fn : BitString → ℕ := fun p =>
    if hp : p ∈ hfin.toFinset then stepOf p (hfin.mem_toFinset.mp hp) else 0
  let maxStep := hfin.toFinset.sup step_fn
  refine ⟨maxStep, fun p hp => ?_⟩
  have hpS : p ∈ hfin.toFinset := hfin.mem_toFinset.mpr hp
  have h_le_sup : step_fn p ≤ maxStep := Finset.le_sup hpS
  have h_eq_step : step_fn p = stepOf p hp := dite_eq_left hpS
  have h_le : stepOf p hp ≤ maxStep := h_eq_step ▸ h_le_sup
  obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp (hstepOf p hp)
  have hmono := Nat.Partrec.Code.evaln_mono h_le (Option.mem_def.mp hval)
  have h_maxStep : (Nat.Partrec.Code.evaln maxStep c_D
      (Nat.pair (Encodable.encode p) 0)).isSome = true :=
    Option.isSome_iff_exists.mpr ⟨val, Option.mem_def.mpr hmono⟩
  dsimp [ShortDescriptions.evalDAt]
  obtain ⟨val', hval'⟩ := Option.isSome_iff_exists.mp h_maxStep
  rw [hval']
  have h_sound := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hval')
  have h_eval_eq_map : Code.eval c_D (Nat.pair (Encodable.encode p) 0) =
      Part.map Encodable.encode (D (p, [])) := by
    rw [hc_D]
    dsimp
    have h_dec : Encodable.decode (α := BitString × BitString)
        (Nat.pair (Encodable.encode p) 0) = some (p, []) :=
      Encodable.encodek (p, ([] : BitString))
    rw [h_dec]
    ext z
    simp
  have hp_prod : x ∈ D (p, []) := hp.1
  have h_enc_mem : Encodable.encode x ∈ Code.eval c_D (Nat.pair (Encodable.encode p) 0) := by
    rw [h_eval_eq_map]
    exact Part.mem_map Encodable.encode hp_prod
  have h_val_eq : val' = Encodable.encode x := Part.mem_unique h_sound h_enc_mem
  rw [h_val_eq]
  exact Encodable.encodek x

/-- A string with `2 ^ k` descriptions of length at most `n` eventually appears in `accumQual`. -/
private lemma mem_accumQual_of_evalDAt_eq (D : Map) (c_D : Code) (n k maxStep : ℕ)
    (x : BitString) (hfin : (descriptionsLe D x n).Finite)
    (hcard : 2 ^ k ≤ (descriptionsLe D x n).ncard)
    (h_eval_eq : ∀ p ∈ descriptionsLe D x n,
      ShortDescriptions.evalDAt c_D p maxStep = some x) :
    x ∈ ShortDescriptions.accumQual c_D k n maxStep := by
  have h_desc_cnt : 2 ^ k ≤ ShortDescriptions.descCountAt c_D n maxStep x := by
    dsimp [ShortDescriptions.descCountAt]
    have h_sub : hfin.toFinset ⊆ ((boundedPrograms n).filter (fun q =>
        match ShortDescriptions.evalDAt c_D q maxStep with
        | none => false
        | some x' => decide (x' = x))).toFinset := by
      intro p hp
      rw [hfin.mem_toFinset] at hp
      rw [List.mem_toFinset, List.mem_filter]
      refine ⟨List.mem_toFinset.mp (ShortDescriptions.descriptionsLe_subset D x n hp), ?_⟩
      have h_ev := h_eval_eq p hp
      rw [h_ev]
      simp
    have h_card_le : hfin.toFinset.card ≤ ((boundedPrograms n).filter (fun q =>
        match ShortDescriptions.evalDAt c_D q maxStep with
        | none => false
        | some x' => decide (x' = x))).toFinset.card := Finset.card_le_card h_sub
    rw [List.toFinset_card_of_nodup (List.Nodup.filter _ (boundedPrograms_nodup n))] at h_card_le
    rw [Set.ncard_eq_toFinset_card (descriptionsLe D x n) hfin] at hcard
    exact hcard.trans h_card_le
  have h_x_stage : x ∈ ShortDescriptions.stageQual c_D k n maxStep := by
    dsimp [ShortDescriptions.stageQual]
    rw [mem_eraseDups_bitString, List.mem_map]
    have h_len_pos : 0 < ((boundedPrograms n).filter (fun q =>
        match ShortDescriptions.evalDAt c_D q maxStep with
        | none => false
        | some x' => decide (x' = x))).length := by
      have h_pow_pos : 0 < 2 ^ k := Nat.two_pow_pos k
      exact h_desc_cnt.trans_lt' h_pow_pos
    obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos h_len_pos
    rw [List.mem_filter] at hq
    have hq_cond := hq.2
    cases h_ev : ShortDescriptions.evalDAt c_D q maxStep with
    | none => rw [h_ev] at hq_cond; contradiction
    | some x' =>
      rw [h_ev] at hq_cond
      have h_eq : x' = x := by simpa using hq_cond
      subst h_eq
      refine ⟨q, ?_, ?_⟩
      · rw [List.mem_filter]
        refine ⟨hq.1, ?_⟩
        change (match ShortDescriptions.evalDAt c_D q maxStep with
          | none => false
          | some x'' => decide (2 ^ k ≤ ShortDescriptions.descCountAt c_D n maxStep x'')) = true
        rw [h_ev]
        exact decide_eq_true h_desc_cnt
      · rw [h_ev]
        rfl
  exact ShortDescriptions.stageQual_subset_accumQual c_D k n maxStep x h_x_stage

/-- Reconstructs `x` via `D_sim` from its index in `accumQual`. -/
private lemma mem_D_sim_of_mem_accumQual (c_D : Code) (n k maxStep : ℕ) (x : BitString)
    (hkn : k ≤ n) (h_x_accum : x ∈ ShortDescriptions.accumQual c_D k n maxStep) :
    ∃ p : BitString, p.length = n - k + 1 ∧
      x ∈ ShortDescriptions.D_sim c_D (p, Nat.bits k) := by
  let m := n - k
  let L := ShortDescriptions.accumQual c_D k n maxStep
  let idx := L.idxOf x
  have h_idx_lt : idx < L.length := List.idxOf_lt_length_of_mem h_x_accum
  have h_L_len : L.length < 2 ^ (m + 1) := by
    have h_pow_eq : 2 ^ (n + 1) = 2 ^ (m + 1) * 2 ^ k := by
      dsimp [m]
      rw [← Nat.pow_add]
      congr 1
      omega
    have h_card_bound : L.length * 2 ^ k ≤ (boundedPrograms n).length :=
      ShortDescriptions.accumQual_card_le c_D k n maxStep
    have h_bp := length_boundedPrograms_lt n
    rw [h_pow_eq] at h_bp
    have h_mul : L.length * 2 ^ k < 2 ^ (m + 1) * 2 ^ k := h_card_bound.trans_lt h_bp
    exact Nat.lt_of_mul_lt_mul_right h_mul
  let p := ShortDescriptions.padBits idx (m + 1)
  have hp_len : p.length = m + 1 := by
    apply ShortDescriptions.padBits_length
    exact length_natBits_lt_pow (by omega : idx < 2 ^ (m + 1))
  have hp_m : p.length - 1 = m := by rw [hp_len]; omega
  have hp_nat : bitsToNat p = idx := ShortDescriptions.padBits_bitsToNat idx (m + 1)
  have h_get_x : L.getD idx [] = x := by
    rw [List.getD_eq_getElem L [] h_idx_lt,
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr h_x_accum)]
  let pred : ℕ →. Bool := fun t =>
    Part.some (decide (idx < (ShortDescriptions.accumQual c_D k n t).length))
  have h_rfind_dom : (Nat.rfind pred).Dom := by
    rw [Nat.rfind_dom]
    refine ⟨maxStep, ?_, fun _ => Part.some_dom _⟩
    rw [Part.mem_some_iff, eq_comm, decide_eq_true_iff]
    exact h_idx_lt
  set t_min := (Nat.rfind pred).get h_rfind_dom
  have ht_min_mem : t_min ∈ Nat.rfind pred := Part.get_mem h_rfind_dom
  have ht_min_spec := (Nat.mem_rfind.mp ht_min_mem).1
  rw [Part.mem_some_iff, eq_comm, decide_eq_true_iff] at ht_min_spec
  have ht_min_le : t_min ≤ maxStep := by
    by_contra! h_gt
    have h_lt_spec := (Nat.mem_rfind.mp ht_min_mem).2 (m := maxStep) h_gt
    rw [Part.mem_some_iff, eq_comm] at h_lt_spec
    rw [decide_eq_false_iff_not, not_lt] at h_lt_spec
    have h_lt_copy := h_idx_lt
    dsimp [L] at h_lt_copy
    omega
  have h_sub_t : ShortDescriptions.accumQual c_D k n t_min <+:
      ShortDescriptions.accumQual c_D k n maxStep :=
    ShortDescriptions.accumQual_le_of_le c_D k n t_min maxStep ht_min_le
  have h_get_t : (ShortDescriptions.accumQual c_D k n t_min).getD idx [] = x := by
    rw [List.getD_eq_getElem _ [] ht_min_spec]
    have h2 : (ShortDescriptions.accumQual c_D k n maxStep).getD idx [] =
        (ShortDescriptions.accumQual c_D k n maxStep)[idx] := List.getD_eq_getElem _ [] h_idx_lt
    rw [h2] at h_get_x
    rw [← h_get_x]
    exact h_sub_t.getElem ht_min_spec
  refine ⟨p, hp_len, ?_⟩
  dsimp [ShortDescriptions.D_sim]
  rw [decodeBits_natBits, hp_m, hp_nat]
  have h_mk : m + k = n := by dsimp [m]; omega
  rw [h_mk]
  rw [Part.mem_bind_iff]
  refine ⟨t_min, ht_min_mem, ?_⟩
  rw [Part.mem_some_iff]
  exact h_get_t.symm

/-- **Exercise 39.** Many short descriptions lower the conditional complexity:
`2 ^ k` descriptions of length at most `n` give `C(x | k) ≤ n - k + O(1)`. -/
theorem condK_le_of_many_descriptions (U : Map) (hU : isOptimalConditional U)
    (D : Map) (hD : isDecompressor D) :
    ∃ c : ℕ, ∀ (n k : ℕ) (x : BitString),
      (descriptionsLe D x n).Finite → 2 ^ k ≤ (descriptionsLe D x n).ncard →
      condK U x (Nat.bits k) ≤ ((n - k + c : ℕ) : ℕ∞) := by
  obtain ⟨c_D, hc_D⟩ := Nat.Partrec.Code.exists_code.mp hD
  obtain ⟨c_sim, hc_sim⟩ :=
    hU.2 (ShortDescriptions.D_sim c_D) (ShortDescriptions.D_sim_isDecompressor c_D)
  refine ⟨c_sim + 1, fun n k x hfin hcard => ?_⟩
  have hkn : k ≤ n := ShortDescriptions.k_le_n_of_many_desc D n k x hfin hcard
  obtain ⟨maxStep, h_eval_eq⟩ := exists_step_evalDAt_eq D c_D hc_D n x hfin
  have h_x_accum := mem_accumQual_of_evalDAt_eq D c_D n k maxStep x hfin hcard h_eval_eq
  obtain ⟨p, hp_len, h_prod_sim⟩ := mem_D_sim_of_mem_accumQual c_D n k maxStep x hkn h_x_accum
  have h_cond_sim := ShortDescriptions.condK_le_of_produces (ShortDescriptions.D_sim c_D) p
    (Nat.bits k) x h_prod_sim
  have h1 : condK (ShortDescriptions.D_sim c_D) x (Nat.bits k) + (c_sim : ℕ∞) ≤
      (p.length : ℕ∞) + (c_sim : ℕ∞) := by gcongr
  have h2 : condK U x (Nat.bits k) ≤ (p.length : ℕ∞) + (c_sim : ℕ∞) :=
    (hc_sim x (Nat.bits k)).trans h1
  rw [hp_len] at h2
  have h3 : ((n - k + 1 : ℕ) : ℕ∞) + (c_sim : ℕ∞) = ((n - k + (c_sim + 1) : ℕ) : ℕ∞) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  exact h2.trans_eq h3

private lemma log_pow_two_self (m : ℕ) : Nat.log 2 (2 ^ m) = m := by
  rw [Nat.log_eq_iff (Or.inr ⟨by decide, by positivity⟩)]
  exact ⟨le_rfl, Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self m)⟩

private lemma exp_gt_linear (C : ℕ) : 3 * C + 12 < 2 ^ (C + 5) := by
  induction C with
  | zero => decide
  | succ C ih =>
    have h1 : 2 ^ (C + 1 + 5) = 2 ^ (C + 5) * 2 := by
      have : C + 1 + 5 = (C + 5) + 1 := by omega
      rw [this, Nat.pow_succ]
    rw [h1]
    omega

/-- **Exercise 40.** For an optimal decompressor every string has only `O(1)`
shortest descriptions. -/
theorem card_shortestDescriptions_le (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x : BitString,
      (shortestDescriptions D x).Finite ∧ (shortestDescriptions D x).ncard ≤ c := by
  obtain ⟨c39, hc39⟩ := condK_le_of_many_descriptions D hD D hD.1
  obtain ⟨k26, hk26⟩ := plainK_sub_condK_le_two_mul_plainK D hD
  obtain ⟨cLit, hLit⟩ := plainK_le_length D hD
  set C := c39 + k26 + 2 * cLit
  set k := 2 ^ (C + 5)
  refine ⟨2 ^ k, fun x => ?_⟩
  have hsub : shortestDescriptions D x ⊆ descriptionsLe D x (cVal D x) := by
    intro p hp
    rw [shortestDescriptions, Set.mem_ofPred_eq] at hp
    rw [descriptionsLe, Set.mem_ofPred_eq]
    refine ⟨hp.1, ?_⟩
    have hlen : p.length = cVal D x := by
      rw [cVal, ← hp.2, ENat.toNat_natCast]
    omega
  have hfin_bounded : Set.Finite ((boundedPrograms (cVal D x)).toFinset : Set BitString) :=
    Finset.finite_toSet _
  have hfin_le : (descriptionsLe D x (cVal D x)).Finite :=
    hfin_bounded.subset (ShortDescriptions.descriptionsLe_subset D x (cVal D x))
  have hfin : (shortestDescriptions D x).Finite := hfin_le.subset hsub
  refine ⟨hfin, ?_⟩
  by_cases h_card : (shortestDescriptions D x).ncard ≤ 2 ^ k
  · exact h_card
  · push Not at h_card
    have h2k : 2 ^ k ≤ (shortestDescriptions D x).ncard := le_of_lt h_card
    have hcard_le : 2 ^ k ≤ (descriptionsLe D x (cVal D x)).ncard := by
      have h1 := Set.ncard_le_ncard hsub hfin_le
      exact h2k.trans h1
    have hcond := hc39 (cVal D x) k x hfin_le hcard_le
    have htop : plainK D x ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top (x.length + cLit)) (hLit x)
    have h_cVal_eq : (cVal D x : ℕ∞) = plainK D x := ENat.natCast_toNat htop
    have hkn : k ≤ cVal D x :=
      ShortDescriptions.k_le_n_of_many_desc D (cVal D x) k x hfin_le hcard_le
    have h_ex26 := (hk26 x (Nat.bits k)).2
    have h_cVal_bits : cVal D (Nat.bits k) ≤ (Nat.bits k).length + cLit := by
      have h_top_k : plainK D (Nat.bits k) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENat.natCast_ne_top ((Nat.bits k).length + cLit)) (hLit (Nat.bits k))
      have h_coe : (cVal D (Nat.bits k) : ℕ∞) = plainK D (Nat.bits k) := ENat.natCast_toNat h_top_k
      have h_le := hLit (Nat.bits k)
      rw [← h_coe] at h_le
      exact_mod_cast h_le
    have h_bits_len : (Nat.bits k).length ≤ C + 6 := by
      have h1 := length_natBits_le_log (2 ^ (C + 5))
      rw [log_pow_two_self (C + 5)] at h1
      exact h1
    have h_bound_2cVal : 2 * cVal D (Nat.bits k) + k26 ≤ 2 * C + 12 + 2 * cLit + k26 := by omega
    have h_arith1 : (cVal D x : ℕ∞) ≤
        ((cVal D x - k + c39 : ℕ) : ℕ∞) + ((2 * C + 12 + 2 * cLit + k26 : ℕ) : ℕ∞) := by
      calc (cVal D x : ℕ∞) = plainK D x := h_cVal_eq
        _ ≤ condK D x (Nat.bits k) + ((2 * cVal D (Nat.bits k) + k26 : ℕ) : ℕ∞) := h_ex26
        _ ≤ ((cVal D x - k + c39 : ℕ) : ℕ∞) + ((2 * C + 12 + 2 * cLit + k26 : ℕ) : ℕ∞) :=
          add_le_add hcond (by exact_mod_cast h_bound_2cVal)
    have h_nat_contra : cVal D x ≤ cVal D x - k + c39 + (2 * C + 12 + 2 * cLit + k26) := by
      exact_mod_cast h_arith1
    have h_k_le : k ≤ c39 + 2 * C + 12 + 2 * cLit + k26 := by omega
    dsimp [k] at h_k_le
    have h_exp := exp_gt_linear C
    dsimp [C] at h_exp h_k_le
    omega

end Kolmogorov
