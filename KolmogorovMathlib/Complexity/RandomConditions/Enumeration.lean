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
import KolmogorovMathlib.Complexity.KolmogorovLevin.ShortDescriptions

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution

/-! ### Exercises 41–46: conditional complexity with random conditions -/

open Kolmogorov.CodedFiniteDistribution

/-- Double counting for a boolean relation on two finite sets: summing the row counts equals
summing the column counts. -/
lemma finset_card_double_count {α β : Type*}
    (S : Finset α) (Y : Finset β) (R : α → β → Bool) :
    S.sum (fun x => (Y.filter (fun y => R x y = true)).card) =
    Y.sum (fun y => (S.filter (fun x => R x y = true)).card) := by
  classical
  have h1 : ∀ x, (Y.filter (fun y => R x y = true)).card =
      Y.sum (fun y => if R x y = true then 1 else 0) := fun x => Finset.card_filter _ _
  have h2 : ∀ y, (S.filter (fun x => R x y = true)).card =
      S.sum (fun x => if R x y = true then 1 else 0) := fun y => Finset.card_filter _ _
  simp_rw [h1, h2]
  exact Finset.sum_comm

/-- Candidate outputs visible at stage `t`. -/
def randomCondCandidateList (c : Code) (n k t : ℕ) : List BitString :=
  ((allStrings n).flatMap (fun y => conditionalOutputSnapshot c y k t)).eraseDups

/-- Number of conditions `y` for which `x` is produced within stage `t`. -/
def randomCondCount (c : Code) (x : BitString) (n k t : ℕ) : ℕ :=
  ((allStrings n).filter (fun y => x ∈ conditionalOutputSnapshot c y k t)).length

/-- A candidate `x` is acceptable at stage `t` when it is produced for at least a `2 ^ (-l)`
fraction of the length-`n` conditions: `2 ^ n ≤ 2 ^ l * randomCondCount c x n k t`. -/
def randomCondAcceptable (c : Code) (x : BitString) (n l k t : ℕ) : Bool :=
  decide (2 ^ n ≤ 2 ^ l * randomCondCount c x n k t)

/-- Staged enumeration of acceptable outputs. -/
def randomCondStep (c : Code) (p : ℕ × ℕ × ℕ) (z : ℕ × List BitString) : List BitString :=
  z.2 ++ (randomCondCandidateList c p.1 p.2.2 (z.1 + 1)).filter
    (fun x => x ∉ z.2 ∧ randomCondAcceptable c x p.1 p.2.1 p.2.2 (z.1 + 1))

/-- The acceptable outputs enumerated by stage `t`, accumulated from the empty list. -/
def randomCondStage (c : Code) (n l k : ℕ) : ℕ → List BitString
  | 0 => []
  | t + 1 => randomCondStep c (n, l, k) (t, randomCondStage c n l k t)

/-- The stage-`t` enumeration with the parameters `n`, `l` read off the condition `z` and the
budget `k` read off the length of the program `p`. -/
def randomCondStageList (c : Code) (p z : BitString) (t : ℕ) : List BitString :=
  let n := bitsToNat (decodeFirst z)
  let l := bitsToNat (decodeSecond z)
  let k := p.length - l - 1
  randomCondStage c n l k t

/-- Halting test of the decompressor: the stage-`t` enumeration is already long enough to
contain the entry indexed by the program `p`. -/
def randomCondCheck (c : Code) (p z : BitString) (t : ℕ) : Bool :=
  let m := (allStrings p.length).findIdx (fun y => decide (y = p))
  decide (m < (randomCondStageList c p z t).length)

/-- Output of the decompressor: the entry of the stage-`t` enumeration indexed by the position of
`p` among the strings of its length. -/
def randomCondGet (c : Code) (p z : BitString) (t : ℕ) : BitString :=
  let m := (allStrings p.length).findIdx (fun y => decide (y = p))
  (randomCondStageList c p z t).getD m []

/-- The decompressor that searches for the first stage `t` passing `randomCondCheck` and then
returns `randomCondGet` at that stage. -/
def randomCondDecoder (c : Code) : Map := fun pz =>
  (Nat.rfind (fun t => Part.some (randomCondCheck c pz.1 pz.2 t))).bind
    (fun t => Part.some (randomCondGet c pz.1 pz.2 t))

/-- Searching a list for a given string by a decidable equality test is the same as taking its
index in the list. -/
lemma findIdx_decide_eq (l : List BitString) (p : BitString) :
    l.findIdx (fun y => decide (y = p)) = @List.idxOf BitString List.instBEq p l := by
  have h : (fun y : BitString => decide (y = p)) = (fun x => x == p) := by
    ext y
    cases h1 : y == p <;> cases h2 : decide (y = p) <;> try rfl
    · have hy : y = p := of_decide_eq_true h2
      have hbeq : (y == p) = true := beq_iff_eq.mpr hy
      rw [hbeq] at h1
      contradiction
    · have hy : y = p := beq_iff_eq.mp h1
      have hdec : decide (y = p) = true := decide_eq_true hy
      rw [hdec] at h2
      contradiction
  rw [h]
  rfl

/-- Lookups below the length of a prefix agree in the prefix and in the whole list. -/
lemma getD_eq_of_prefix_of_lt_length {α} {l1 l2 : List α} (h : l1 <+: l2) (k : ℕ) (d : α)
    (hk : k < l1.length) : l2.getD k d = l1.getD k d := by
  obtain ⟨r, rfl⟩ := h
  exact List.getD_append l1 r d k hk

/-- The stage enumeration of acceptable outputs has no repetitions. -/
theorem randomCondStage_nodup (c : Code) (n l k t : ℕ) :
    (randomCondStage c n l k t).Nodup := by
  induction t with
  | zero => exact List.nodup_nil
  | succ t ih =>
      unfold randomCondStage
      apply List.Nodup.append ih
      · apply List.Nodup.filter
        exact nodup_eraseDups_bitString _
      · intro x hx h_mem
        rw [List.mem_filter] at h_mem
        have h_and := of_decide_eq_true h_mem.2
        have h_not : x ∉ randomCondStage c n l k t := h_and.1
        exact h_not hx

private theorem randomCondStage_prefix (c : Code) (n l k t : ℕ) :
    randomCondStage c n l k t <+: randomCondStage c n l k (t + 1) :=
  ⟨_, rfl⟩

/-- The stage enumeration at an earlier stage is a prefix of the one at a later stage. -/
theorem randomCondStage_mono (c : Code) (n l k : ℕ) {t1 t2 : ℕ} (h : t1 ≤ t2) :
    randomCondStage c n l k t1 <+: randomCondStage c n l k t2 := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact List.IsPrefix.trans ih (randomCondStage_prefix c n l k _)

/-- A program producing `x` from `z` bounds the conditional complexity with respect to that
decompressor by its length. -/
lemma condK_le_of_produces {D : Map} {p z x : BitString} (h : produces D p z x) :
    condK D x z ≤ (p.length : ℕ∞) :=
  sInf_le ⟨p, h, rfl⟩

end Kolmogorov
