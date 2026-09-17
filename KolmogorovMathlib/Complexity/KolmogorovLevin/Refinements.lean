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
import Mathlib.Data.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.ConditionalComplexity.Continuity

/-!
# The rectangle dichotomy

`rectangle_dichotomy` (SUV Exercise 36) is the combinatorial heart of the Kolmogorov–Levin
proof: for a set of pairs, either some `x` has many partners `y` — and then `x` is cheap given
the parameters — or the partners of each `x` are few, and then each pair is cheap given `x`.

Both branches are made effective by staged enumerations: `dichotomyEnum1` and
`dichotomyStage1` accumulate the strings `x` already known to have many partners,
`dichotomyEnum2` and `dichotomyStage2` the partners of a fixed `x`, and
`dichotomySnapshotY` is the finite snapshot they read; each is primitive recursive.
`condK_dichotomyD1_le` and `condK_dichotomyD2_le` are the two complexity bounds the branches
yield.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution


/-- Appending trailing zero bits does not change the number a bit string denotes. -/
lemma bitsToNat_append_replicate_false (bs : BitString) (m : ℕ) :
    bitsToNat (bs ++ List.replicate m false) = bitsToNat bs := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ', ← List.append_assoc, bitsToNat_append_single_false, ih]

/-- Padding a bit string to a fixed width with zeros does not change the number it denotes. -/
lemma bitsToNat_padTo (n : ℕ) (bs : BitString) :
    bitsToNat (padTo n bs) = bitsToNat bs :=
  bitsToNat_append_replicate_false bs (n - bs.length)

/-- Finite snapshot at stage `t` of `y` produced for `x` given `z` from programs of length `≤ B`. -/
def dichotomySnapshotY (c : Code) (z : BitString) (B : ℕ) (x : BitString) (t : ℕ) :
    List BitString :=
  ((conditionalOutputSnapshot c z B t).filterMap (fun u =>
    if decodeFirst u = x then some (decodeSecond u) else none)).eraseDups

/-- The strings `x` seen by stage `t` in the enumeration for condition `z = (k, l)` that already
have at least `2 ^ l` partners `y` with `(x, y)` enumerated below the bound `k + l - 1`. -/
def dichotomyEnum1 (c : Code) (z : BitString) (t : ℕ) : List BitString :=
  let k := decodeBits (decodeFirst z)
  let l := decodeBits (decodeSecond z)
  let B := k + l - 1
  ((conditionalOutputSnapshot c z B t).map decodeFirst).filter (fun x' =>
    decide (2 ^ l ≤ (dichotomySnapshotY c z B x' t).length))

/-- The duplicate-free accumulation of the first enumeration up to stage `t`. -/
def dichotomyStage1 (c : Code) (z : BitString) : ℕ → List BitString
  | 0 => (dichotomyEnum1 c z 0).eraseDups
  | t + 1 => (dichotomyStage1 c z t ++ dichotomyEnum1 c z (t + 1)).eraseDups

/-- The partners `y` of the fixed string `x` seen by stage `t` in the enumeration below the
bound `k + l - 1`, where the condition packs `x` together with `z = (k, l)`. -/
def dichotomyEnum2 (c : Code) (cond : BitString) (t : ℕ) : List BitString :=
  let x := decodeFirst cond
  let z := decodeSecond cond
  let k := decodeBits (decodeFirst z)
  let l := decodeBits (decodeSecond z)
  let B := k + l - 1
  (conditionalOutputSnapshot c z B t).filterMap (fun u =>
    if decodeFirst u = x then some (decodeSecond u) else none)

/-- The duplicate-free accumulation of the second enumeration up to stage `t`. -/
def dichotomyStage2 (c : Code) (cond : BitString) : ℕ → List BitString
  | 0 => (dichotomyEnum2 c cond 0).eraseDups
  | t + 1 => (dichotomyStage2 c cond t ++ dichotomyEnum2 c cond (t + 1)).eraseDups

/-- The stage-`t` snapshot of the second components paired with `x` is primitive recursive in
the condition, the length bound, the string `x` and the stage. -/
lemma dichotomySnapshotY_primrec (c : Code) :
    Primrec (fun q : ((BitString × ℕ × BitString) × ℕ) =>
      dichotomySnapshotY c q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  unfold dichotomySnapshotY
  have hsnap : Primrec (fun q : ((BitString × ℕ × BitString) × ℕ) =>
      conditionalOutputSnapshot c q.1.1 q.1.2.1 q.2) :=
    (conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  have h_cond_pred : Primrec (fun r : (((BitString × ℕ × BitString) × ℕ) × BitString) =>
      decide (decodeFirst r.2 = r.1.1.2.2)) :=
    (PrimrecPred.decide (Primrec.eq.comp (CodedFiniteDistribution.decodeFirst_primrec.comp
      Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
  have h_then : Primrec (fun r : (((BitString × ℕ × BitString) × ℕ) × BitString) =>
      some (decodeSecond r.2)) :=
    Primrec.option_some.comp (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.snd)
  have h_else : Primrec (fun _ : (((BitString × ℕ × BitString) × ℕ) × BitString) =>
      (none : Option BitString)) :=
    Primrec.const (none : Option BitString)
  have h_f : Primrec₂ (fun (q : (BitString × ℕ × BitString) × ℕ) (u : BitString) =>
      if decodeFirst u = q.1.2.2 then some (decodeSecond u) else none) :=
    (Primrec.cond h_cond_pred h_then h_else).to₂.of_eq (fun q u => by dsimp; split_ifs <;> simp_all)
  exact eraseDups_bitstring_primrec.comp (Primrec.listFilterMap hsnap h_f)

/-- The first staged enumeration (of the strings `x` with many partners `y`) is primitive
recursive in the condition and the stage. -/
lemma dichotomyEnum1_primrec (c : Code) :
    Primrec (fun p : BitString × ℕ => dichotomyEnum1 c p.1 p.2) := by
  unfold dichotomyEnum1
  have h_z : Primrec (fun p : BitString × ℕ => p.1) := Primrec.fst
  have h_t : Primrec (fun p : BitString × ℕ => p.2) := Primrec.snd
  have h_k : Primrec (fun p : BitString × ℕ => decodeBits (decodeFirst p.1)) :=
    primrec_decodeBits.comp (CodedFiniteDistribution.decodeFirst_primrec.comp h_z)
  have h_l : Primrec (fun p : BitString × ℕ => decodeBits (decodeSecond p.1)) :=
    primrec_decodeBits.comp (CodedFiniteDistribution.decodeSecond_primrec.comp h_z)
  have h_add : Primrec (fun p : BitString × ℕ =>
      decodeBits (decodeFirst p.1) + decodeBits (decodeSecond p.1)) :=
    Primrec.nat_add.comp h_k h_l
  have h_B : Primrec (fun p : BitString × ℕ =>
      decodeBits (decodeFirst p.1) + decodeBits (decodeSecond p.1) - 1) :=
    Primrec.nat_sub.comp h_add (Primrec.const 1)
  have h_snap : Primrec (fun p : BitString × ℕ =>
      conditionalOutputSnapshot c p.1
        (decodeBits (decodeFirst p.1) + decodeBits (decodeSecond p.1) - 1) p.2) :=
    (conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair h_z h_B) h_t)
  have h_map : Primrec (fun p : BitString × ℕ =>
      (conditionalOutputSnapshot c p.1
        (decodeBits (decodeFirst p.1) + decodeBits (decodeSecond p.1) - 1) p.2).map decodeFirst) :=
    Primrec.list_map h_snap (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.snd).to₂
  have h_arg_Y : Primrec (fun q : (BitString × ℕ) × BitString =>
      (((q.1.1, decodeBits (decodeFirst q.1.1) + decodeBits (decodeSecond q.1.1) - 1, q.2), q.1.2) :
        (BitString × ℕ × BitString) × ℕ)) :=
    Primrec.pair (Primrec.pair (h_z.comp Primrec.fst)
      (Primrec.pair (h_B.comp Primrec.fst) Primrec.snd)) (h_t.comp Primrec.fst)
  have h_snapY : Primrec (fun q : (BitString × ℕ) × BitString =>
      (dichotomySnapshotY c q.1.1
        (decodeBits (decodeFirst q.1.1) + decodeBits (decodeSecond q.1.1) - 1) q.2
            q.1.2).length) :=
    Primrec.list_length.comp ((dichotomySnapshotY_primrec c).comp h_arg_Y)
  have h_pow : Primrec (fun q : (BitString × ℕ) × BitString =>
      2 ^ decodeBits (decodeSecond q.1.1)) :=
    primrec_two_pow_aux.comp (h_l.comp Primrec.fst)
  have h_pred : Primrec (fun q : (BitString × ℕ) × BitString =>
      decide (2 ^ decodeBits (decodeSecond q.1.1) ≤
        (dichotomySnapshotY c q.1.1
          (decodeBits (decodeFirst q.1.1) + decodeBits (decodeSecond q.1.1) - 1) q.2
            q.1.2).length)) :=
    PrimrecPred.decide (Primrec.nat_le.comp h_pow h_snapY)
  exact list_filter_primrec h_map h_pred

/-- The accumulated first enumeration is computable in the condition and the stage. -/
lemma dichotomyStage1_computable (c : Code) :
    Computable (fun p : BitString × ℕ => dichotomyStage1 c p.1 p.2) := by
  have hEnum := dichotomyEnum1_primrec c
  have hbase : Primrec (fun p : BitString × ℕ => (dichotomyEnum1 c p.1 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      (hEnum.comp (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep : Primrec₂ (fun (p : BitString × ℕ) (z : ℕ × List BitString) =>
      (z.2 ++ dichotomyEnum1 c p.1 (z.1 + 1)).eraseDups) :=
    (eraseDups_bitstring_primrec.comp
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
        (hEnum.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))).to₂
  apply Primrec.to_comp
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  rintro ⟨z, t⟩
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [dichotomyStage1]
    rw [← ih]

/-- The second staged enumeration (of the partners `y` of a fixed `x`) is primitive recursive in
the condition and the stage. -/
lemma dichotomyEnum2_primrec (c : Code) :
    Primrec (fun p : BitString × ℕ => dichotomyEnum2 c p.1 p.2) := by
  unfold dichotomyEnum2
  have h_cond : Primrec (fun p : BitString × ℕ => p.1) := Primrec.fst
  have h_t : Primrec (fun p : BitString × ℕ => p.2) := Primrec.snd
  have h_z : Primrec (fun p : BitString × ℕ => decodeSecond p.1) :=
    CodedFiniteDistribution.decodeSecond_primrec.comp h_cond
  have h_k : Primrec (fun p : BitString × ℕ => decodeBits (decodeFirst (decodeSecond p.1))) :=
    primrec_decodeBits.comp (CodedFiniteDistribution.decodeFirst_primrec.comp h_z)
  have h_l : Primrec (fun p : BitString × ℕ => decodeBits (decodeSecond (decodeSecond p.1))) :=
    primrec_decodeBits.comp (CodedFiniteDistribution.decodeSecond_primrec.comp h_z)
  have h_add : Primrec (fun p : BitString × ℕ =>
      decodeBits (decodeFirst (decodeSecond p.1)) +
        decodeBits (decodeSecond (decodeSecond p.1))) :=
    Primrec.nat_add.comp h_k h_l
  have h_B : Primrec (fun p : BitString × ℕ =>
      decodeBits (decodeFirst (decodeSecond p.1)) +
        decodeBits (decodeSecond (decodeSecond p.1)) - 1) :=
    Primrec.nat_sub.comp h_add (Primrec.const 1)
  have h_snap : Primrec (fun p : BitString × ℕ =>
      conditionalOutputSnapshot c (decodeSecond p.1)
        (decodeBits (decodeFirst (decodeSecond p.1)) +
          decodeBits (decodeSecond (decodeSecond p.1)) - 1) p.2) :=
    (conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair h_z h_B) h_t)
  have h_cond_pred : Primrec (fun q : (BitString × ℕ) × BitString =>
      decide (decodeFirst q.2 = decodeFirst q.1.1)) :=
    (PrimrecPred.decide (Primrec.eq.comp (CodedFiniteDistribution.decodeFirst_primrec.comp
      Primrec.snd)
      (CodedFiniteDistribution.decodeFirst_primrec.comp (Primrec.fst.comp Primrec.fst))))
  have h_then : Primrec (fun q : (BitString × ℕ) × BitString =>
      some (decodeSecond q.2)) :=
    Primrec.option_some.comp (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.snd)
  have h_else : Primrec (fun _ : (BitString × ℕ) × BitString => (none : Option BitString)) :=
    Primrec.const (none : Option BitString)
  have h_f : Primrec₂ (fun (p : BitString × ℕ) (u : BitString) =>
      if decodeFirst u = decodeFirst p.1 then some (decodeSecond u) else none) :=
    (Primrec.cond h_cond_pred h_then h_else).to₂.of_eq (fun p u => by dsimp; split_ifs <;> simp_all)
  exact Primrec.listFilterMap h_snap h_f

/-- The accumulated second enumeration is computable in the condition and the stage. -/
lemma dichotomyStage2_computable (c : Code) :
    Computable (fun p : BitString × ℕ => dichotomyStage2 c p.1 p.2) := by
  have hEnum := dichotomyEnum2_primrec c
  have hbase : Primrec (fun p : BitString × ℕ => (dichotomyEnum2 c p.1 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      (hEnum.comp (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep : Primrec₂ (fun (p : BitString × ℕ) (z : ℕ × List BitString) =>
      (z.2 ++ dichotomyEnum2 c p.1 (z.1 + 1)).eraseDups) :=
    (eraseDups_bitstring_primrec.comp
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
        (hEnum.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))).to₂
  apply Primrec.to_comp
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  rintro ⟨cond, t⟩
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [dichotomyStage2]
    rw [← ih]

/-- The accumulated first enumeration has no repetitions. -/
lemma dichotomyStage1_nodup (c : Code) (z : BitString) (t : ℕ) :
    (dichotomyStage1 c z t).Nodup := by
  cases t <;> exact nodup_eraseDups_bitString _

/-- The accumulated second enumeration has no repetitions. -/
lemma dichotomyStage2_nodup (c : Code) (cond : BitString) (t : ℕ) :
    (dichotomyStage2 c cond t).Nodup := by
  cases t <;> exact nodup_eraseDups_bitString _

/-- Each stage of the first enumeration is a prefix of the next. -/
lemma dichotomyStage1_mono (c : Code) (z : BitString) (t : ℕ) :
    dichotomyStage1 c z t <+: dichotomyStage1 c z (t + 1) := by
  dsimp [dichotomyStage1]
  exact prefix_eraseDups_append_of_nodup _ _ (dichotomyStage1_nodup c z t)

/-- Each stage of the second enumeration is a prefix of the next. -/
lemma dichotomyStage2_mono (c : Code) (cond : BitString) (t : ℕ) :
    dichotomyStage2 c cond t <+: dichotomyStage2 c cond (t + 1) := by
  dsimp [dichotomyStage2]
  exact prefix_eraseDups_append_of_nodup _ _ (dichotomyStage2_nodup c cond t)

/-- The snapshot of partners of `x` grows with the stage. -/
lemma dichotomySnapshotY_mono (c : Code) (z : BitString) (B : ℕ) (x : BitString) {t1 t2 : ℕ}
    (ht : t1 ≤ t2) :
    (dichotomySnapshotY c z B x t1).length ≤ (dichotomySnapshotY c z B x t2).length := by
  have h_sub : ∀ y' ∈ dichotomySnapshotY c z B x t1, y' ∈ dichotomySnapshotY c z B x t2 := by
    intro y' hy'
    unfold dichotomySnapshotY at hy' ⊢
    rw [mem_eraseDups_bitString, List.mem_filterMap] at hy' ⊢
    obtain ⟨u, hu_snap, hu_eq⟩ := hy'
    refine ⟨u, ?_, hu_eq⟩
    unfold conditionalOutputSnapshot at hu_snap ⊢
    rw [List.mem_filterMap] at hu_snap ⊢
    obtain ⟨p0, hp0_mem, hp0_run⟩ := hu_snap
    exact ⟨p0, hp0_mem, conditionalRunOut_mono c ht hp0_run⟩
  have h_nodup : (dichotomySnapshotY c z B x t1).Nodup := by
    unfold dichotomySnapshotY; exact nodup_eraseDups_bitString _
  rw [← List.toFinset_card_of_nodup h_nodup]
  exact le_trans (Finset.card_le_card (fun y' hy' =>
    List.mem_toFinset.mpr (h_sub y' (List.mem_toFinset.mp hy')))) (List.toFinset_card_le _)

/-- Summing the indicator of equality with `a` over a duplicate-free list gives `1` if `a`
occurs in the list and `0` otherwise. -/
lemma sum_if_eq_mem {α : Type} [DecidableEq α] (S : List α) (hS : S.Nodup) (a : α) :
    (S.map (fun x => if a = x then 1 else 0)).sum = if a ∈ S then 1 else 0 := by
  induction S with
  | nil => simp
  | cons b S' ih =>
    rw [List.nodup_cons] at hS
    rw [List.map_cons, List.sum_cons, ih hS.2]
    by_cases hab : a = b
    · subst hab
      have h_notin : a ∉ S' := hS.1
      simp [h_notin]
    · simp [hab]

/-- Summing, over a duplicate-free list of values, the number of elements of `K` mapped to that
value is at most the length of `K`. -/
lemma sum_filter_length_le {α β : Type} [DecidableEq β] (S : List β) (hS : S.Nodup)
    (K : List α) (f : α → β) :
    (S.map (fun x => (K.filter (fun u => decide (f u = x))).length)).sum ≤ K.length := by
  induction K with
  | nil => simp
  | cons u K' ih =>
    rw [List.length_cons]
    have h_item : ∀ x, ((u :: K').filter (fun v => decide (f v = x))).length =
        (K'.filter (fun v => decide (f v = x))).length +
        if f u = x then 1 else 0 := by
      intro x
      rw [List.filter_cons]
      by_cases h : f u = x <;> simp [h]
    have h_eq : (fun x => ((u :: K').filter (fun v => decide (f v = x))).length) =
        (fun x => (K'.filter (fun v => decide (f v = x))).length + if f u = x then 1 else 0) := by
      ext x; exact h_item x
    rw [h_eq, List.sum_map_add]
    rw [sum_if_eq_mem S hS (f u)]
    split_ifs <;> omega

/-- Fewer than `2 ^ k` strings ever enter the first enumeration, since each of them consumes
`2 ^ l` of the at most `2 ^ (k + l)` enumerated pairs. -/
lemma dichotomy_card_bound (c : Code) (z : BitString) (k l t0 : ℕ)
    (hk : k = decodeBits (decodeFirst z)) (hl : l = decodeBits (decodeSecond z))
    (hkl : 0 < k + l) :
    (dichotomyStage1 c z t0).length < 2 ^ k := by
  let S : List BitString := dichotomyStage1 c z t0
  have hS_nodup : S.Nodup := dichotomyStage1_nodup c z t0
  have hB : k + l - 1 + 1 = k + l := by omega
  have hY_len : ∀ x' ∈ S, 2 ^ l ≤ (dichotomySnapshotY c z (k + l - 1) x' t0).length := by
    intro x' hx'
    induction t0 with
    | zero =>
      change x' ∈ (dichotomyEnum1 c z 0).eraseDups at hx'
      rw [mem_eraseDups_bitString] at hx'
      unfold dichotomyEnum1 at hx'
      rw [List.mem_filter] at hx'
      have hx'_cond := decide_eq_true_iff.mp hx'.2
      rwa [← hk, ← hl] at hx'_cond
    | succ t0' ih =>
      change x' ∈ (dichotomyStage1 c z t0' ++ dichotomyEnum1 c z (t0' + 1)).eraseDups at hx'
      rw [mem_eraseDups_bitString, List.mem_append] at hx'
      cases hx' with
      | inl h_prev =>
        have ih_prev := ih (dichotomyStage1_nodup c z t0') h_prev
        exact ih_prev.trans (dichotomySnapshotY_mono c z (k + l - 1) x' (by omega))
      | inr h_curr =>
        unfold dichotomyEnum1 at h_curr
        rw [List.mem_filter] at h_curr
        have h_curr_cond := decide_eq_true_iff.mp h_curr.2
        rwa [← hk, ← hl] at h_curr_cond
  let K : List BitString := conditionalOutputSnapshot c z (k + l - 1) t0
  have h_group_len : ∀ x' ∈ S,
      2 ^ l ≤ (K.filter (fun u => decide (decodeFirst u = x'))).length := by
    intro x' hx'
    have h1 := hY_len x' hx'
    unfold dichotomySnapshotY at h1
    let L0 : List BitString := K.filterMap (fun u =>
      if decodeFirst u = x' then some (decodeSecond u) else none)
    have h2 : L0.eraseDups.length ≤ L0.length := by
      have h_nodup := nodup_eraseDups_bitString L0
      rw [← List.toFinset_card_of_nodup h_nodup]
      have h_eq : L0.eraseDups.toFinset = L0.toFinset := by
        ext w; simp
      rw [h_eq]
      exact List.toFinset_card_le L0
    have h3 : L0.length ≤ (K.filter (fun u => decide (decodeFirst u = x'))).length := by
      have h_sub : L0 = (K.filter (fun u => decide (decodeFirst u = x'))).filterMap
          (fun u => if decodeFirst u = x' then some (decodeSecond u) else none) := by
        dsimp [L0]
        induction K with
        | nil => simp
        | cons u K' ih =>
          rw [List.filterMap_cons, List.filter_cons]
          by_cases h : decodeFirst u = x' <;> simp [h, ih]
      rw [h_sub]
      exact List.length_filterMap_le _ _
    exact h1.trans h2 |>.trans h3
  have h_sum_le : (S.map (fun x' =>
      (K.filter (fun u => decide (decodeFirst u = x'))).length)).sum ≤ K.length :=
    sum_filter_length_le S hS_nodup K decodeFirst
  have h_S_sum : S.length * 2 ^ l ≤
      (S.map (fun x' => (K.filter (fun u => decide (decodeFirst u = x'))).length)).sum := by
    revert hS_nodup h_group_len
    induction S with
    | nil => simp
    | cons a S' ih =>
      intro h_nodup h_group
      rw [List.nodup_cons] at h_nodup
      have h_a := h_group a (by simp)
      have ih' := ih h_nodup.2 (fun x' hx' => h_group x' (by simp [hx']))
      rw [List.length_cons, List.map_cons, List.sum_cons, add_mul, one_mul]
      omega
  have h_snap_len : S.length * 2 ^ l ≤ K.length := h_S_sum.trans h_sum_le
  have h_bp := length_boundedPrograms_lt (k + l - 1)
  have h_filter_le := List.length_filterMap_le (conditionalRunOut c t0 · z)
    (boundedPrograms (k + l - 1))
  have h_pow : 2 ^ (k + l - 1 + 1) = 2 ^ k * 2 ^ l := by
    rw [hB]
    exact pow_add 2 k l
  rw [h_pow] at h_bp
  have h_lt : S.length * 2 ^ l < 2 ^ k * 2 ^ l := by
    calc S.length * 2 ^ l ≤ K.length := h_snap_len
      _ ≤ (boundedPrograms (k + l - 1)).length := h_filter_le
      _ < 2 ^ k * 2 ^ l := h_bp
  exact Nat.lt_of_mul_lt_mul_right h_lt

/-- The snapshot of partners of `x` at the length bound `k + l - 1` is the duplicate-free second
enumeration run on the condition `pairCode x z`. -/
lemma dichotomySnapshotY_eq_enum2 (c : Code) (x z : BitString) (t : ℕ) :
    dichotomySnapshotY c z (decodeBits (decodeFirst z) + decodeBits (decodeSecond z) - 1) x t =
    (dichotomyEnum2 c (pairCode x z) t).eraseDups := by
  dsimp [dichotomySnapshotY, dichotomyEnum2]
  rw [decodeFirst_pairCode, decodeSecond_pairCode]

/-- Membership in the second enumeration persists to the next stage. -/
lemma dichotomyEnum2_mono (c : Code) (cond : BitString) (t : ℕ) {y' : BitString}
    (hy : y' ∈ dichotomyEnum2 c cond t) : y' ∈ dichotomyEnum2 c cond (t + 1) := by
  unfold dichotomyEnum2 at hy ⊢
  rw [List.mem_filterMap] at hy ⊢
  obtain ⟨u, hu_snap, hu_eq⟩ := hy
  refine ⟨u, ?_, hu_eq⟩
  unfold conditionalOutputSnapshot at hu_snap ⊢
  rw [List.mem_filterMap] at hu_snap ⊢
  obtain ⟨p, hp_mem, hp_run⟩ := hu_snap
  exact ⟨p, hp_mem, conditionalRunOut_mono c (Nat.le_succ t) hp_run⟩

/-- Every element of the accumulated second enumeration at stage `t` already occurs in the
stage-`t` enumeration itself. -/
lemma dichotomyStage2_mem_enum2 (c : Code) (cond : BitString) (t : ℕ) {y' : BitString}
    (hy : y' ∈ dichotomyStage2 c cond t) : y' ∈ dichotomyEnum2 c cond t := by
  induction t with
  | zero =>
    dsimp [dichotomyStage2] at hy
    exact mem_eraseDups_bitString.mp hy
  | succ t ih =>
    dsimp [dichotomyStage2] at hy
    rw [mem_eraseDups_bitString, List.mem_append] at hy
    cases hy with
    | inl h_prev => exact dichotomyEnum2_mono c cond t (ih h_prev)
    | inr h_curr => exact h_curr

/-- Every partner listed by the accumulated second enumeration for the condition `pairCode x z`
occurs in the snapshot of partners of `x`. -/
lemma dichotomyStage2_sub_snapshotY (c : Code) (x z : BitString) (t0 : ℕ) :
    ∀ y' ∈ dichotomyStage2 c (pairCode x z) t0,
      y' ∈ dichotomySnapshotY c z
        (decodeBits (decodeFirst z) + decodeBits (decodeSecond z) - 1) x t0 := by
  intro y' hy'
  have hy2 := dichotomyStage2_mem_enum2 c (pairCode x z) t0 hy'
  rw [dichotomySnapshotY_eq_enum2, mem_eraseDups_bitString]
  exact hy2

/-- The first field of the condition `pairCode (bits k) (bits l)` decodes to `k`. -/
lemma decodeFirst_z (k l : ℕ) :
    decodeBits (decodeFirst (pairCode (Nat.bits k) (Nat.bits l))) = k := by
  rw [decodeFirst_pairCode, decodeBits_natBits]

/-- The second field of the condition `pairCode (bits k) (bits l)` decodes to `l`. -/
lemma decodeSecond_z (k l : ℕ) :
    decodeBits (decodeSecond (pairCode (Nat.bits k) (Nat.bits l))) = l := by
  rw [decodeSecond_pairCode, decodeBits_natBits]

/-- The decompressor that reads its program as a fixed-length index into the accumulated first
enumeration for the condition. -/
def dichotomyD1 (c : Code) : Map :=
  fun pr => condFFixedLength (dichotomyStage1 c) pr.2 pr.1

/-- The decompressor that reads its program as a fixed-length index into the accumulated second
enumeration for the condition. -/
def dichotomyD2 (c : Code) : Map :=
  fun pr => condFFixedLength (dichotomyStage2 c) pr.2 pr.1

/-- The first decompressor of the dichotomy, which reads an index into the first enumeration,
is a conditional decompressor. -/
lemma dichotomyD1_decompressor (c : Code) : isDecompressor (dichotomyD1 c) :=
  condFFixedLength_partrec (dichotomyStage1 c) (dichotomyStage1_computable c)

/-- The second decompressor of the dichotomy, which reads an index into the second enumeration,
is a conditional decompressor. -/
lemma dichotomyD2_decompressor (c : Code) : isDecompressor (dichotomyD2 c) :=
  condFFixedLength_partrec (dichotomyStage2 c) (dichotomyStage2_computable c)

/-- On a program whose value is a legal index into the first enumeration, the first decompressor
outputs the string at that index. -/
lemma dichotomyD1_eval (c : Code) (z px : BitString) (t0 : ℕ)
    (hidx : bitsToNat px < (dichotomyStage1 c z t0).eraseDups.length) :
    (dichotomyStage1 c z t0).eraseDups.getD (bitsToNat px) [] ∈ dichotomyD1 c (px, z) :=
  condFFixedLength_eval (dichotomyStage1 c) (dichotomyStage1_mono c) z px t0 hidx

/-- Reformulation of the previous evaluation with the index named separately. -/
lemma dichotomyD1_getD_eval (c : Code) (z px : BitString) (t0 : ℕ) (idx : ℕ)
    (hpx : bitsToNat px = idx)
    (hidx : idx < (dichotomyStage1 c z t0).eraseDups.length) :
    (dichotomyStage1 c z t0).eraseDups.getD idx [] ∈ dichotomyD1 c (px, z) := by
  have h1 := dichotomyD1_eval c z px t0 (by rwa [hpx])
  rwa [hpx] at h1

/-- If the entry of the first enumeration at the index denoted by `px` is `x`, then the first
decompressor outputs `x` on the program `px` with condition `z`. -/
lemma dichotomyD1_elem_eval (c : Code) (z px x : BitString) (t0 : ℕ) (idx : ℕ)
    (hpx : bitsToNat px = idx)
    (hidx : idx < (dichotomyStage1 c z t0).eraseDups.length)
    (hget : (dichotomyStage1 c z t0).eraseDups.getD idx [] = x) :
    x ∈ dichotomyD1 c (px, z) := by
  have h1 := dichotomyD1_getD_eval c z px t0 idx hpx hidx
  rwa [hget] at h1

/-- On a program whose value is a legal index into the second enumeration, the second
decompressor outputs the string at that index. -/
lemma dichotomyD2_eval (c : Code) (cond py : BitString) (t0 : ℕ)
    (hidx : bitsToNat py < (dichotomyStage2 c cond t0).eraseDups.length) :
    (dichotomyStage2 c cond t0).eraseDups.getD (bitsToNat py) [] ∈ dichotomyD2 c (py, cond) :=
  condFFixedLength_eval (dichotomyStage2 c) (dichotomyStage2_mono c) cond py t0 hidx

/-- Reformulation of the previous evaluation with the index named separately. -/
lemma dichotomyD2_getD_eval (c : Code) (cond py : BitString) (t0 : ℕ) (idx : ℕ)
    (hpy : bitsToNat py = idx)
    (hidx : idx < (dichotomyStage2 c cond t0).eraseDups.length) :
    (dichotomyStage2 c cond t0).eraseDups.getD idx [] ∈ dichotomyD2 c (py, cond) := by
  have h1 := dichotomyD2_eval c cond py t0 (by rwa [hpy])
  rwa [hpy] at h1

/-- If the entry of the second enumeration at the index denoted by `py` is `y`, then the second
decompressor outputs `y` on the program `py` with condition `cond`. -/
lemma dichotomyD2_elem_eval (c : Code) (cond py y : BitString) (t0 : ℕ) (idx : ℕ)
    (hpy : bitsToNat py = idx)
    (hidx : idx < (dichotomyStage2 c cond t0).eraseDups.length)
    (hget : (dichotomyStage2 c cond t0).eraseDups.getD idx [] = y) :
    y ∈ dichotomyD2 c (py, cond) := by
  have h1 := dichotomyD2_getD_eval c cond py t0 idx hpy hidx
  rwa [hget] at h1

/-- A pair `⟨x, y⟩` in the output snapshot contributes its second component `y` to the snapshot
of partners of `x`. -/
lemma dichotomySnapshotY_mem (c : Code) (z : BitString) (B : ℕ) (x y : BitString) (t : ℕ)
    (h : pairCode x y ∈ conditionalOutputSnapshot c z B t) :
    y ∈ dichotomySnapshotY c z B x t := by
  unfold dichotomySnapshotY
  rw [mem_eraseDups_bitString, List.mem_filterMap]
  refine ⟨pairCode x y, h, ?_⟩
  rw [decodeFirst_pairCode, decodeSecond_pairCode, if_pos rfl]

/-- A string `x` with at least `2 ^ l` partners at stage `t` enters the first enumeration. -/
lemma dichotomyEnum1_mem (c : Code) (z : BitString) (k l : ℕ) (x y : BitString) (t : ℕ)
    (hk : decodeBits (decodeFirst z) = k)
    (hl : decodeBits (decodeSecond z) = l)
    (hp_snapshot : pairCode x y ∈ conditionalOutputSnapshot c z (k + l - 1) t)
    (h_case : 2 ^ l ≤ (dichotomySnapshotY c z (k + l - 1) x t).length) :
    x ∈ dichotomyEnum1 c z t := by
  unfold dichotomyEnum1
  rw [List.mem_filter, List.mem_map]
  have hp_snapshot' : pairCode x y ∈
      conditionalOutputSnapshot c z
        (decodeBits (decodeFirst z) + decodeBits (decodeSecond z) - 1) t := by
    rwa [hk, hl]
  refine ⟨⟨pairCode x y, hp_snapshot', decodeFirst_pairCode x y⟩, ?_⟩
  rw [hk, hl]
  exact decide_eq_true h_case

/-- A pair `⟨x, y⟩` in the output snapshot for the condition `z` puts `y` into the second
enumeration run on the condition `pairCode x z`. -/
lemma dichotomyEnum2_mem (c : Code) (x z y : BitString) (k l : ℕ) (t : ℕ)
    (hk : decodeBits (decodeFirst z) = k)
    (hl : decodeBits (decodeSecond z) = l)
    (hp_snapshot : pairCode x y ∈ conditionalOutputSnapshot c z (k + l - 1) t) :
    y ∈ dichotomyEnum2 c (pairCode x z) t := by
  unfold dichotomyEnum2
  rw [List.mem_filterMap]
  have hp_snapshot' : pairCode x y ∈
      conditionalOutputSnapshot c (decodeSecond (pairCode x z))
        (decodeBits (decodeFirst (decodeSecond (pairCode x z))) +
          decodeBits (decodeSecond (decodeSecond (pairCode x z))) - 1) t := by
    rw [decodeSecond_pairCode, hk, hl]
    exact hp_snapshot
  refine ⟨pairCode x y, hp_snapshot', ?_⟩
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, ite_true]

/-- If the pair `⟨x, y⟩` has conditional complexity strictly below `k + l` given `z`, then it has
a program of length at most `k + l - 1`. -/
lemma cCondPair_lt_imp_condK_le (U : Map) (x y z : BitString) (k l : ℕ)
    (hlt : cCondPair U x y z < ((k + l : ℕ) : ℕ∞)) :
    condK U (pairCode x y) z ≤ ((k + l - 1 : ℕ) : ℕ∞) := by
  dsimp [cCondPair] at hlt
  cases hK : condK U (pairCode x y) z with
  | top => rw [hK] at hlt; contradiction
  | coe n =>
    have h1 : n < k + l := by
      have hlt' := hlt
      rw [hK] at hlt'
      exact WithTop.coe_lt_coe.mp hlt'
    have h2 : n ≤ k + l - 1 := by omega
    exact_mod_cast h2

/-- Every string entering the first enumeration at stage `t` is in the accumulated list. -/
lemma dichotomyEnum1_sub_stage1 (c : Code) (z : BitString) (t : ℕ) {x : BitString}
    (hx : x ∈ dichotomyEnum1 c z t) : x ∈ dichotomyStage1 c z t := by
  cases t with
  | zero =>
    dsimp [dichotomyStage1]
    exact mem_eraseDups_bitString.mpr hx
  | succ t' =>
    dsimp [dichotomyStage1]
    exact mem_eraseDups_bitString.mpr (List.mem_append_right _ hx)

/-- Every partner entering the second enumeration at stage `t` is in the accumulated list. -/
lemma dichotomyEnum2_sub_stage2 (c : Code) (cond : BitString) (t : ℕ) {y : BitString}
    (hy : y ∈ dichotomyEnum2 c cond t) : y ∈ dichotomyStage2 c cond t := by
  cases t with
  | zero =>
    dsimp [dichotomyStage2]
    exact mem_eraseDups_bitString.mpr hy
  | succ t' =>
    dsimp [dichotomyStage2]
    exact mem_eraseDups_bitString.mpr (List.mem_append_right _ hy)

/-- A program on which the first decompressor outputs `x` bounds the complexity of `x` given `z`
with respect to that decompressor by its length. -/
lemma condK_dichotomyD1_le (c : Code) (x z px : BitString)
    (h_eval : x ∈ dichotomyD1 c (px, z)) :
    condK (dichotomyD1 c) x z ≤ (px.length : ℕ∞) :=
  sInf_le ⟨px, h_eval, rfl⟩

/-- A program on which the second decompressor outputs `y` bounds the complexity of `y` given
the condition with respect to that decompressor by its length. -/
lemma condK_dichotomyD2_le (c : Code) (y cond py : BitString)
    (h_eval : y ∈ dichotomyD2 c (py, cond)) :
    condK (dichotomyD2 c) y cond ≤ (py.length : ℕ∞) :=
  sInf_le ⟨py, h_eval, rfl⟩

/-- **Exercise 36.** The rectangle dichotomy behind the Kolmogorov–Levin proof. -/
theorem rectangle_dichotomy (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString) (k l : ℕ),
      cCondPair U x y (pairCode (Nat.bits k) (Nat.bits l)) < ((k + l : ℕ) : ℕ∞) →
        condK U x (pairCode (Nat.bits k) (Nat.bits l)) ≤ ((k + c : ℕ) : ℕ∞) ∨
        condK U y (pairCode x (pairCode (Nat.bits k) (Nat.bits l))) ≤ ((l + c : ℕ) : ℕ∞) := by
  obtain ⟨cU, hcU⟩ : ∃ c : Code, IsCodeFor c U := Nat.Partrec.Code.exists_code.mp hU.1
  obtain ⟨c1, hc1⟩ := hU.2 (dichotomyD1 cU) (dichotomyD1_decompressor cU)
  obtain ⟨c2, hc2⟩ := hU.2 (dichotomyD2 cU) (dichotomyD2_decompressor cU)
  refine ⟨max c1 c2, fun x y k l hlt => ?_⟩
  set z := pairCode (Nat.bits k) (Nat.bits l)
  dsimp [cCondPair] at hlt
  by_cases hkl : k + l = 0
  · have : ((k + l : ℕ) : ℕ∞) = (0 : ℕ∞) := by rw [hkl]; rfl
    rw [this] at hlt
    exact False.elim (not_lt_of_ge (bot_le) hlt)
  have hB : k + l - 1 + 1 = k + l := by omega
  have hlt_le := cCondPair_lt_imp_condK_le U x y z k l hlt
  obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U (pairCode x y) z (k + l - 1)).mp hlt_le
  obtain ⟨t0, ht0⟩ := conditionalRunOut_complete hcU hp_prod
  have hp_snapshot : pairCode x y ∈ conditionalOutputSnapshot cU z (k + l - 1) t0 :=
    mem_conditionalOutputSnapshot_of_run hp_len ht0
  have hy_snap := dichotomySnapshotY_mem cU z (k + l - 1) x y t0 hp_snapshot
  by_cases h_case : 2 ^ l ≤ (dichotomySnapshotY cU z (k + l - 1) x t0).length
  · left
    have hx_enum1 := dichotomyEnum1_mem cU z k l x y t0
      (decodeFirst_z k l) (decodeSecond_z k l) hp_snapshot h_case
    have hx_stage1 := dichotomyEnum1_sub_stage1 cU z t0 hx_enum1
    have hx_erase : x ∈ (dichotomyStage1 cU z t0).eraseDups :=
      mem_eraseDups_bitString.mpr hx_stage1
    set idx := (dichotomyStage1 cU z t0).eraseDups.idxOf x
    have hidx_lt_len : idx < (dichotomyStage1 cU z t0).eraseDups.length :=
      List.idxOf_lt_length_iff.mpr hx_erase
    have hidx_getD : (dichotomyStage1 cU z t0).eraseDups.getD idx [] = x := by
      rw [List.getD_eq_getElem (dichotomyStage1 cU z t0).eraseDups [] hidx_lt_len,
        List.getElem_idxOf hidx_lt_len]
    have h_card_bound : (dichotomyStage1 cU z t0).eraseDups.length < 2 ^ k := by
      have h_nodup := nodup_eraseDups_bitString (dichotomyStage1 cU z t0)
      have h_le : (dichotomyStage1 cU z t0).eraseDups.length ≤
          (dichotomyStage1 cU z t0).length := by
        rw [← List.toFinset_card_of_nodup h_nodup]
        have h_eq : (dichotomyStage1 cU z t0).eraseDups.toFinset =
            (dichotomyStage1 cU z t0).toFinset := by
          ext w; simp
        rw [h_eq]
        exact List.toFinset_card_le _
      have h_bound := dichotomy_card_bound cU z k l t0 (decodeFirst_z k l).symm
        (decodeSecond_z k l).symm (by omega)
      exact lt_of_le_of_lt h_le h_bound
    have hidx_lt_pow : idx < 2 ^ k := lt_trans hidx_lt_len h_card_bound
    set px := padTo k (Nat.bits idx)
    have hpx_len : px.length = k := length_padTo k (Nat.bits idx)
      (length_natBits_lt_pow hidx_lt_pow)
    have hpx_nat : bitsToNat px = idx := by
      rw [bitsToNat_padTo, bitsToNat_bits]
    have h_eval : x ∈ dichotomyD1 cU (px, z) :=
      dichotomyD1_elem_eval cU z px x t0 idx hpx_nat hidx_lt_len hidx_getD
    have h_le := condK_dichotomyD1_le cU x z px h_eval
    calc condK U x z ≤ condK (dichotomyD1 cU) x z + (c1 : ℕ∞) := hc1 x z
      _ ≤ (px.length : ℕ∞) + (c1 : ℕ∞) := by gcongr
      _ = ((k + c1 : ℕ) : ℕ∞) := by rw [hpx_len]; push_cast; rfl
      _ ≤ ((k + max c1 c2 : ℕ) : ℕ∞) := by gcongr; exact le_max_left c1 c2
  · right
    have h_snapshot_lt : (dichotomySnapshotY cU z (k + l - 1) x t0).length < 2 ^ l :=
      not_le.mp h_case
    have hy_enum2 := dichotomyEnum2_mem cU x z y k l t0
      (decodeFirst_z k l) (decodeSecond_z k l) hp_snapshot
    have hy_stage2 := dichotomyEnum2_sub_stage2 cU (pairCode x z) t0 hy_enum2
    have hy_erase : y ∈ (dichotomyStage2 cU (pairCode x z) t0).eraseDups :=
      mem_eraseDups_bitString.mpr hy_stage2
    set idx := (dichotomyStage2 cU (pairCode x z) t0).eraseDups.idxOf y
    have hidx_lt_len : idx < (dichotomyStage2 cU (pairCode x z) t0).eraseDups.length :=
      List.idxOf_lt_length_iff.mpr hy_erase
    have hidx_getD : (dichotomyStage2 cU (pairCode x z) t0).eraseDups.getD idx [] = y := by
      rw [List.getD_eq_getElem (dichotomyStage2 cU (pairCode x z) t0).eraseDups [] hidx_lt_len,
        List.getElem_idxOf hidx_lt_len]
    have h_sub := dichotomyStage2_sub_snapshotY cU x z t0
    have h_card_bound : (dichotomyStage2 cU (pairCode x z) t0).eraseDups.length < 2 ^ l := by
      have h1 : (dichotomyStage2 cU (pairCode x z) t0).eraseDups.length ≤
          (dichotomySnapshotY cU z (k + l - 1) x t0).length := by
        have h_nodup : (dichotomyStage2 cU (pairCode x z) t0).eraseDups.Nodup :=
          nodup_eraseDups_bitString _
        rw [← List.toFinset_card_of_nodup h_nodup]
        have h_kl_eq : decodeBits (decodeFirst z) +
            decodeBits (decodeSecond z) - 1 = k + l - 1 := by
          dsimp [z]
          rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
            decodeBits_natBits]
        exact le_trans (Finset.card_le_card (fun y' hy' =>
          List.mem_toFinset.mpr (h_kl_eq ▸ h_sub y' (mem_eraseDups_bitString.mp
            (List.mem_toFinset.mp hy')))))
            (List.toFinset_card_le _)
      exact lt_of_le_of_lt h1 h_snapshot_lt
    have hidx_lt_pow : idx < 2 ^ l := lt_trans hidx_lt_len h_card_bound
    set py := padTo l (Nat.bits idx)
    have hpy_len : py.length = l := length_padTo l (Nat.bits idx)
      (length_natBits_lt_pow hidx_lt_pow)
    have hpy_nat : bitsToNat py = idx := by
      rw [bitsToNat_padTo, bitsToNat_bits]
    have h_eval : y ∈ dichotomyD2 cU (py, pairCode x z) :=
      dichotomyD2_elem_eval cU (pairCode x z) py y t0 idx hpy_nat hidx_lt_len hidx_getD
    have h_le := condK_dichotomyD2_le cU y (pairCode x z) py h_eval
    calc condK U y (pairCode x z) ≤
        condK (dichotomyD2 cU) y (pairCode x z) + (c2 : ℕ∞) := hc2 y (pairCode x z)
      _ ≤ (py.length : ℕ∞) + (c2 : ℕ∞) := by gcongr
      _ = ((l + c2 : ℕ) : ℕ∞) := by rw [hpy_len]; push_cast; rfl
      _ ≤ ((l + max c1 c2 : ℕ) : ℕ∞) := by gcongr; exact le_max_right c1 c2

end Kolmogorov
