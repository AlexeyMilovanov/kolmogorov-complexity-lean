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
import KolmogorovMathlib.Complexity.IncompressibleStrings.Deficiency

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution
variable (Q : ℕ × ℕ × BitString → Bool)

-- The refutation of the `O(C n)`-only reading of Problem 59
-- (`information_conservation_Cn_only_exponent_false` and
-- `information_conservation_Cn_only_exponent_unprovable`) lives in
-- `KolmogorovCounterexamples/Problem59CnOnlyExponent.lean`.

/-! ### Exercise 59(a): the conditional version of Exercise 41 -/

/-- Candidate outputs visible at stage `t`, from the conditions `⟨r, x⟩` with `r` of length `n`. -/
def randomPairCandidateList (c : Code) (x : BitString) (n k t : ℕ) : List BitString :=
  ((allStrings n).flatMap (fun r => conditionalOutputSnapshot c (pairCode r x) k t)).eraseDups

/-- Number of conditions `r` of length `n` from which `y` is produced within stage `t`. -/
def randomPairCount (c : Code) (x y : BitString) (n k t : ℕ) : ℕ :=
  ((allStrings n).filter (fun r => y ∈ conditionalOutputSnapshot c (pairCode r x) k t)).length

/-- Acceptability predicate for candidate `y`. -/
def randomPairAcceptable (c : Code) (x y : BitString) (n l k t : ℕ) : Bool :=
  decide (2 ^ n ≤ 2 ^ l * randomPairCount c x y n k t)

/-- One step of the staged enumeration of acceptable outputs. -/
def randomPairStep (c : Code) (p : BitString × ℕ × ℕ × ℕ) (w : ℕ × List BitString) :
    List BitString :=
  w.2 ++ (randomPairCandidateList c p.1 p.2.1 p.2.2.2 (w.1 + 1)).filter
    (fun y => y ∉ w.2 ∧ randomPairAcceptable c p.1 y p.2.1 p.2.2.1 p.2.2.2 (w.1 + 1))

/-- Staged enumeration of acceptable outputs. -/
def randomPairStage (c : Code) (x : BitString) (n l k : ℕ) : ℕ → List BitString
  | 0 => []
  | t + 1 => randomPairStep c (x, n, l, k) (t, randomPairStage c x n l k t)

/-- The stage list, with all parameters recovered from the condition string `z` and
the program length. -/
def randomPairStageList (c : Code) (p z : BitString) (t : ℕ) : List BitString :=
  let n := bitsToNat (decodeFirst z)
  let l := bitsToNat (decodeFirst (decodeSecond z))
  let x := decodeSecond (decodeSecond z)
  let k := p.length - l - 1
  randomPairStage c x n l k t

/-- Halting test of `randomPairDecoder`: true once the stage-`t` enumeration of
acceptable outputs read off the condition `z` has produced more than `m` strings,
where `m` is the position of the program `p` among the strings of its length. -/
def randomPairCheck (c : Code) (p z : BitString) (t : ℕ) : Bool :=
  let m := (allStrings p.length).findIdx (fun y => decide (y = p))
  decide (m < (randomPairStageList c p z t).length)

/-- Output of `randomPairDecoder`: the entry of the stage-`t` enumeration of acceptable
outputs at the position of the program `p` among the strings of its length. -/
def randomPairGet (c : Code) (p z : BitString) (t : ℕ) : BitString :=
  let m := (allStrings p.length).findIdx (fun y => decide (y = p))
  (randomPairStageList c p z t).getD m []

/-- The decompressor that, on input `(p, z)`, searches for the first stage `t` at which the
enumeration of acceptable outputs is long enough and returns the entry at the position of `p`
among the strings of its length. -/
def randomPairDecoder (c : Code) : Map := fun pz =>
  (Nat.rfind (fun t => Part.some (randomPairCheck c pz.1 pz.2 t))).bind
    (fun t => Part.some (randomPairGet c pz.1 pz.2 t))

private theorem randomPairStage_nodup (c : Code) (x : BitString) (n l k t : ℕ) :
    (randomPairStage c x n l k t).Nodup := by
  induction t with
  | zero => exact List.nodup_nil
  | succ t ih =>
      unfold randomPairStage
      apply List.Nodup.append ih
      · apply List.Nodup.filter
        exact nodup_eraseDups_bitString _
      · intro y hy h_mem
        rw [List.mem_filter] at h_mem
        have h_and := of_decide_eq_true h_mem.2
        have h_not : y ∉ randomPairStage c x n l k t := h_and.1
        exact h_not hy

private theorem randomPairStage_prefix (c : Code) (x : BitString) (n l k t : ℕ) :
    randomPairStage c x n l k t <+: randomPairStage c x n l k (t + 1) :=
  ⟨_, rfl⟩

private theorem randomPairStage_mono (c : Code) (x : BitString) (n l k : ℕ) {t1 t2 : ℕ}
    (h : t1 ≤ t2) :
    randomPairStage c x n l k t1 <+: randomPairStage c x n l k t2 := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact List.IsPrefix.trans ih (randomPairStage_prefix c x n l k _)

private theorem randomPairStage_eventually_mem {c : Code} {U : Map} (hc : IsCodeFor c U)
    {x y : BitString} {n k l : ℕ}
    (h : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ l *
      (((allStrings n).filter
        (fun r => decide (condK U y (pairCode r x) ≤ (k : ℕ∞)))).length : ℝ)) :
    ∃ T, y ∈ randomPairStage c x n l k T := by
  have h_nat : 2 ^ n ≤
      2 ^ l * ((allStrings n).filter
        (fun r => decide (condK U y (pairCode r x) ≤ (k : ℕ∞)))).length := by
    have h_cast : (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by push_cast; rfl
    have h_cast2 : (2 : ℝ) ^ l = ((2 ^ l : ℕ) : ℝ) := by push_cast; rfl
    rw [h_cast, h_cast2, ← Nat.cast_mul] at h
    exact Nat.cast_le.mp h
  have h_run : ∀ r ∈ (allStrings n).filter
        (fun r => decide (condK U y (pairCode r x) ≤ (k : ℕ∞))),
      ∃ t_r p_r, p_r.length ≤ k ∧ conditionalRunOut c t_r p_r (pairCode r x) = some y := by
    intro r hr
    rw [List.mem_filter] at hr
    have h_cond : condK U y (pairCode r x) ≤ (k : ℕ∞) := by simpa using hr.2
    rw [condK_le_iff] at h_cond
    obtain ⟨p, hp_len, hp_prod⟩ := h_cond
    obtain ⟨t, ht⟩ := conditionalRunOut_complete hc hp_prod
    exact ⟨t, p, hp_len, ht⟩
  choose t_fn p_fn hp_len ht_run using h_run
  let Y := (allStrings n).filter (fun r => decide (condK U y (pairCode r x) ≤ (k : ℕ∞)))
  let T := (Y.map (fun r => if hr : r ∈ Y then t_fn r hr else 0)).sum + 1
  have hT_le : ∀ r (hr : r ∈ Y), t_fn r hr ≤ T := by
    intro r hr
    have : t_fn r hr ≤ (Y.map (fun r => if hr : r ∈ Y then t_fn r hr else 0)).sum := by
      have h_mem : t_fn r hr ∈ Y.map (fun r => if hr : r ∈ Y then t_fn r hr else 0) := by
        rw [List.mem_map]
        exact ⟨r, hr, by simp [hr]⟩
      exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ h_mem
    exact Nat.le_succ_of_le this
  have h_snap : ∀ r ∈ Y, y ∈ conditionalOutputSnapshot c (pairCode r x) k T := by
    intro r hr
    have h_run_r := ht_run r hr
    have h_mono := conditionalRunOut_mono c (hT_le r hr) h_run_r
    exact mem_conditionalOutputSnapshot_of_run (hp_len r hr) h_mono
  have h_count : Y.length ≤ randomPairCount c x y n k T := by
    unfold randomPairCount Y
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply list_countP_mono
    intro r hr h_cond
    have h_in_Y : r ∈ (allStrings n).filter
        (fun r => decide (condK U y (pairCode r x) ≤ (k : ℕ∞))) := by
      rw [List.mem_filter]
      exact ⟨hr, h_cond⟩
    simp only [decide_eq_true_eq]
    exact h_snap r h_in_Y
  have h_acc : randomPairAcceptable c x y n l k T = true := by
    unfold randomPairAcceptable
    apply decide_eq_true
    calc 2 ^ n ≤ 2 ^ l * Y.length := h_nat
      _ ≤ 2 ^ l * randomPairCount c x y n k T := Nat.mul_le_mul_left _ h_count
  have h_cand : y ∈ randomPairCandidateList c x n k T := by
    unfold randomPairCandidateList
    rw [mem_eraseDups_bitString, List.mem_flatMap]
    obtain ⟨r, hr_mem⟩ : ∃ r, r ∈ allStrings n ∧
        y ∈ conditionalOutputSnapshot c (pairCode r x) k T := by
      have h_nonempty : Y.length > 0 := by
        by_contra h_zero
        have : Y.length = 0 := Nat.le_zero.mp (not_lt.mp h_zero)
        rw [this, Nat.mul_zero] at h_nat
        have : 2 ^ n > 0 := Nat.two_pow_pos n
        omega
      obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos h_nonempty
      have hr_all := (List.mem_filter.mp hr).1
      exact ⟨r, hr_all, h_snap r hr⟩
    exact ⟨r, hr_mem.1, hr_mem.2⟩
  have hT_pos : T ≥ 1 := Nat.succ_le_succ (Nat.zero_le _)
  obtain ⟨t, ht_eq⟩ : ∃ t, T = t + 1 := ⟨T - 1, (Nat.sub_add_cancel hT_pos).symm⟩
  rw [ht_eq] at h_cand h_acc
  refine ⟨t + 1, ?_⟩
  unfold randomPairStage
  by_cases h_prev : y ∈ randomPairStage c x n l k t
  · exact List.mem_append_left _ h_prev
  · apply List.mem_append_right
    rw [List.mem_filter]
    exact ⟨h_cand, by simp [h_prev, h_acc]⟩

private theorem randomPairStage_length_bound (c : Code) (x : BitString)
    (n l k t : ℕ) : (randomPairStage c x n l k t).length < 2 ^ (k + l + 1) := by
  have h_acc : ∀ (t : ℕ) (y : BitString),
      y ∈ randomPairStage c x n l k t → 2 ^ n ≤ 2 ^ l * randomPairCount c x y n k t := by
    intro t
    induction t with
    | zero =>
        intro y hy
        simp [randomPairStage] at hy
    | succ t ih =>
        intro y hy
        change y ∈ randomPairStage c x n l k t ++
          (randomPairCandidateList c x n k (t + 1)).filter
            (fun y => y ∉ randomPairStage c x n l k t ∧
              randomPairAcceptable c x y n l k (t + 1)) at hy
        rw [List.mem_append] at hy
        cases hy with
        | inl hy_prev =>
            have h_mono : randomPairCount c x y n k t ≤ randomPairCount c x y n k (t + 1) := by
              unfold randomPairCount
              rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
              apply list_countP_mono
              intro r _ hr
              exact decide_eq_true
                (mem_conditionalOutputSnapshot_mono c (Nat.le_succ t) (of_decide_eq_true hr))
            calc 2 ^ n ≤ 2 ^ l * randomPairCount c x y n k t := ih y hy_prev
              _ ≤ 2 ^ l * randomPairCount c x y n k (t + 1) := Nat.mul_le_mul_left _ h_mono
        | inr hy_new =>
            rw [List.mem_filter] at hy_new
            have h_and := of_decide_eq_true hy_new.2
            have h_dec := h_and.2
            unfold randomPairAcceptable at h_dec
            exact of_decide_eq_true h_dec
  let S := (randomPairStage c x n l k t).toFinset
  let Y := (allStrings n).toFinset
  let R := fun (w r : BitString) => decide (w ∈ conditionalOutputSnapshot c (pairCode r x) k t)
  have hS_nodup : (randomPairStage c x n l k t).Nodup := randomPairStage_nodup c x n l k t
  have hS_card : S.card = (randomPairStage c x n l k t).length :=
    List.toFinset_card_of_nodup hS_nodup
  have hY_card : Y.card = 2 ^ n := by
    change (allStrings n).toFinset.card = 2 ^ n
    rw [List.toFinset_card_of_nodup (allStrings_nodup n), length_allStrings]
  have h_acc' : ∀ w ∈ S, 2 ^ n ≤ 2 ^ l * randomPairCount c x w n k t := by
    intro w hw
    rw [List.mem_toFinset] at hw
    exact h_acc t w hw
  have h_count_eq : ∀ w, randomPairCount c x w n k t = (Y.filter (fun r => R w r = true)).card := by
    intro w
    unfold randomPairCount R Y
    exact length_filter_eq_card_toFinset_filter (allStrings_nodup n) _
  have h_double := finset_card_double_count S Y R
  have h_each_y : ∀ r ∈ Y, (S.filter (fun w => R w r = true)).card ≤ 2 ^ (k + 1) - 1 := by
    intro r _
    have h_sub : (S.filter (fun w => R w r = true)) ⊆
        (conditionalOutputSnapshot c (pairCode r x) k t).toFinset := by
      intro w hw
      rw [Finset.mem_filter, List.mem_toFinset] at hw
      rw [List.mem_toFinset]
      exact of_decide_eq_true hw.2
    have h_le1 := Finset.card_le_card h_sub
    have h_le2 : (conditionalOutputSnapshot c (pairCode r x) k t).toFinset.card ≤
        (conditionalOutputSnapshot c (pairCode r x) k t).length := List.toFinset_card_le _
    have h_le3 : (conditionalOutputSnapshot c (pairCode r x) k t).length ≤
        (boundedPrograms k).length := List.length_filterMap_le _ _
    have h_lt := length_boundedPrograms_lt k
    omega
  have h_sum_y : Y.sum (fun r => (S.filter (fun w => R w r = true)).card) ≤
      2 ^ n * (2 ^ (k + 1) - 1) := by
    calc Y.sum (fun r => (S.filter (fun w => R w r = true)).card)
      _ ≤ Y.sum (fun _ => 2 ^ (k + 1) - 1) := Finset.sum_le_sum h_each_y
      _ = Y.card * (2 ^ (k + 1) - 1) := by simp [Finset.sum_const]
      _ = 2 ^ n * (2 ^ (k + 1) - 1) := by rw [hY_card]
  have h_sum_x : S.sum (fun w => randomPairCount c x w n k t) ≤
      2 ^ n * (2 ^ (k + 1) - 1) := by
    have h_eq_sum : S.sum (fun w => randomPairCount c x w n k t) =
        S.sum (fun w => (Y.filter (fun r => R w r = true)).card) := by
      refine Finset.sum_congr rfl (fun w _ => h_count_eq w)
    rw [h_eq_sum, h_double]
    exact h_sum_y
  have h_sum_acc : S.sum (fun _ => 2 ^ n) ≤
      S.sum (fun w => 2 ^ l * randomPairCount c x w n k t) := by
    apply Finset.sum_le_sum
    intro w hw
    exact h_acc' w hw
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h_sum_acc
  have h_bound : S.card * 2 ^ n ≤ 2 ^ n * (2 ^ l * (2 ^ (k + 1) - 1)) := by
    calc S.card * 2 ^ n
      _ ≤ 2 ^ l * S.sum (fun w => randomPairCount c x w n k t) := h_sum_acc
      _ ≤ 2 ^ l * (2 ^ n * (2 ^ (k + 1) - 1)) := Nat.mul_le_mul_left _ h_sum_x
      _ = 2 ^ n * (2 ^ l * (2 ^ (k + 1) - 1)) := by ring
  have h_bound' : 2 ^ n * S.card ≤ 2 ^ n * (2 ^ l * (2 ^ (k + 1) - 1)) := by
    rw [Nat.mul_comm]
    exact h_bound
  have h_pos : 0 < 2 ^ n := Nat.two_pow_pos n
  have h_card_le := Nat.le_of_mul_le_mul_left h_bound' h_pos
  rw [hS_card] at h_card_le
  have h_pow_sub : 2 ^ l * (2 ^ (k + 1) - 1) = 2 ^ (k + l + 1) - 2 ^ l := by
    have h1 : 2 ^ l * (2 ^ (k + 1) - 1) = 2 ^ l * 2 ^ (k + 1) - 2 ^ l * 1 :=
      Nat.mul_sub_left_distrib (2 ^ l) (2 ^ (k + 1)) 1
    have h2 : 2 ^ l * 2 ^ (k + 1) = 2 ^ (k + l + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h1, h2, mul_one]
  rw [h_pow_sub] at h_card_le
  have h_l_pos : 0 < 2 ^ l := Nat.two_pow_pos l
  have h_sub_lt : 2 ^ (k + l + 1) - 2 ^ l < 2 ^ (k + l + 1) := by
    have h_pos2 : 0 < 2 ^ (k + l + 1) := Nat.two_pow_pos _
    omega
  omega

/-! #### Primitive recursiveness of the Exercise 59(a) enumeration -/

private theorem randomPairCandidateList_primrec (c : Code) :
    Primrec (fun q : ((BitString × ℕ) × ℕ) × ℕ =>
      randomPairCandidateList c q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  have hx : Primrec (fun q : ((BitString × ℕ) × ℕ) × ℕ => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec (fun q : ((BitString × ℕ) × ℕ) × ℕ => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec (fun q : ((BitString × ℕ) × ℕ) × ℕ => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have ht : Primrec (fun q : ((BitString × ℕ) × ℕ) × ℕ => q.2) := Primrec.snd
  have hall : Primrec (fun q : ((BitString × ℕ) × ℕ) × ℕ => allStrings q.1.1.2) :=
    allStrings_primrec.comp hn
  have hcond : Primrec (fun q : (((BitString × ℕ) × ℕ) × ℕ) × BitString =>
      pairCode q.2 q.1.1.1.1) :=
    pairCode_primrec.comp Primrec.snd (hx.comp Primrec.fst)
  have hsnap : Primrec₂ (fun (q : ((BitString × ℕ) × ℕ) × ℕ) (r : BitString) =>
      conditionalOutputSnapshot c (pairCode r q.1.1.1) q.1.2 q.2) :=
    ((conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair hcond (hk.comp Primrec.fst)) (ht.comp Primrec.fst))).to₂
  have hflat : Primrec (fun q : ((BitString × ℕ) × ℕ) × ℕ =>
      (allStrings q.1.1.2).flatMap
        (fun r => conditionalOutputSnapshot c (pairCode r q.1.1.1) q.1.2 q.2)) :=
    Primrec.list_flatMap hall hsnap
  exact (eraseDups_bitstring_primrec.comp hflat).of_eq (fun _ => rfl)

/-- The number of strings `s` of length `r.1.2` for which `r.1.1.2` occurs in the
length-bounded output snapshot of the machine `c` on `pairCode s r.1.1.1`; the
uncurried form of `randomPairCount`, used to state its primitive recursiveness. -/
def randomPairCountFn (c : Code) (r : ((BitString × BitString) × ℕ) × (ℕ × ℕ)) : ℕ :=
  ((allStrings r.1.2).filter
    (fun s => decide (r.1.1.2 ∈
      conditionalOutputSnapshot c (pairCode s r.1.1.1) r.2.1 r.2.2))).length

private lemma randomPair_count_eq (c : Code) (r : ((BitString × BitString) × ℕ) × (ℕ × ℕ)) :
    randomPairCountFn c r = randomPairCount c r.1.1.1 r.1.1.2 r.1.2 r.2.1 r.2.2 := by
  rcases r with ⟨⟨⟨x, y⟩, n⟩, k, t⟩; rfl

private theorem randomPairCount_primrec (c : Code) :
    Primrec (fun r : ((BitString × BitString) × ℕ) × (ℕ × ℕ) =>
      randomPairCount c r.1.1.1 r.1.1.2 r.1.2 r.2.1 r.2.2) := by
  have hx : Primrec (fun r : ((BitString × BitString) × ℕ) × (ℕ × ℕ) => r.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hy : Primrec (fun r : ((BitString × BitString) × ℕ) × (ℕ × ℕ) => r.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec (fun r : ((BitString × BitString) × ℕ) × (ℕ × ℕ) => r.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hk : Primrec (fun r : ((BitString × BitString) × ℕ) × (ℕ × ℕ) => r.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun r : ((BitString × BitString) × ℕ) × (ℕ × ℕ) => r.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hall : Primrec (fun r : ((BitString × BitString) × ℕ) × (ℕ × ℕ) => allStrings r.1.2) :=
    allStrings_primrec.comp hn
  have hs_r : Primrec (fun r : (((BitString × BitString) × ℕ) × (ℕ × ℕ)) × BitString => r.2) :=
    Primrec.snd
  have hx_r : Primrec (fun r : (((BitString × BitString) × ℕ) × (ℕ × ℕ)) × BitString =>
      r.1.1.1.1) := hx.comp Primrec.fst
  have hy_r : Primrec (fun r : (((BitString × BitString) × ℕ) × (ℕ × ℕ)) × BitString =>
      r.1.1.1.2) := hy.comp Primrec.fst
  have hk_r : Primrec (fun r : (((BitString × BitString) × ℕ) × (ℕ × ℕ)) × BitString =>
      r.1.2.1) := hk.comp Primrec.fst
  have ht_r : Primrec (fun r : (((BitString × BitString) × ℕ) × (ℕ × ℕ)) × BitString =>
      r.1.2.2) := ht.comp Primrec.fst
  have hcond : Primrec (fun r : (((BitString × BitString) × ℕ) × (ℕ × ℕ)) × BitString =>
      pairCode r.2 r.1.1.1.1) := pairCode_primrec.comp hs_r hx_r
  have h_pair : Primrec (fun r : (((BitString × BitString) × ℕ) × (ℕ × ℕ)) × BitString =>
      ((pairCode r.2 r.1.1.1.1, r.1.1.1.2), (r.1.2.1, r.1.2.2))) :=
    Primrec.pair (Primrec.pair hcond hy_r) (Primrec.pair hk_r ht_r)
  have hmem : Primrec (fun r : (((BitString × BitString) × ℕ) × (ℕ × ℕ)) × BitString =>
      decide (r.1.1.1.2 ∈
        conditionalOutputSnapshot c (pairCode r.2 r.1.1.1.1) r.1.2.1 r.1.2.2)) :=
    (randomCondMemSnapshot_primrec c).comp h_pair
  have hfilter : Primrec (fun r : ((BitString × BitString) × ℕ) × (ℕ × ℕ) =>
      (allStrings r.1.2).filter
        (fun s => decide (r.1.1.2 ∈
          conditionalOutputSnapshot c (pairCode s r.1.1.1) r.2.1 r.2.2))) :=
    list_filter_primrec hall hmem.to₂
  have hcount : Primrec (fun r => randomPairCountFn c r) :=
    Primrec.list_length.comp hfilter
  exact hcount.of_eq (fun r => randomPair_count_eq c r)

/-- Argument type of the enumeration step: the parameters `(x, n, l, k)` together with
a stage number and the list enumerated so far, paired with a candidate string. -/
abbrev randomPairArgs := ((BitString × ℕ × ℕ × ℕ) × (ℕ × List BitString)) × BitString

private theorem randomPair_proj_pz : Primrec (fun (r : randomPairArgs) => r.1) := Primrec.fst
private theorem randomPair_proj_y : Primrec (fun (r : randomPairArgs) => r.2) := Primrec.snd
private theorem randomPair_proj_p : Primrec (fun (r : randomPairArgs) => r.1.1) := Primrec.fst.comp
    randomPair_proj_pz
private theorem randomPair_proj_x : Primrec (fun (r : randomPairArgs) => r.1.1.1) :=
  Primrec.fst.comp randomPair_proj_p
private theorem randomPair_proj_nlk : Primrec (fun (r : randomPairArgs) => r.1.1.2) :=
  Primrec.snd.comp randomPair_proj_p
private theorem randomPair_proj_n : Primrec (fun (r : randomPairArgs) => r.1.1.2.1) :=
  Primrec.fst.comp randomPair_proj_nlk
private theorem randomPair_proj_lk : Primrec (fun (r : randomPairArgs) => r.1.1.2.2) :=
  Primrec.snd.comp randomPair_proj_nlk
private theorem randomPair_proj_l : Primrec (fun (r : randomPairArgs) => r.1.1.2.2.1) :=
  Primrec.fst.comp randomPair_proj_lk
private theorem randomPair_proj_k : Primrec (fun (r : randomPairArgs) => r.1.1.2.2.2) :=
  Primrec.snd.comp randomPair_proj_lk
private theorem randomPair_proj_w : Primrec (fun (r : randomPairArgs) => r.1.2) := Primrec.snd.comp
    randomPair_proj_pz
private theorem randomPair_proj_w1 : Primrec (fun (r : randomPairArgs) => r.1.2.1) :=
  Primrec.fst.comp randomPair_proj_w
private theorem randomPair_proj_w2 : Primrec (fun (r : randomPairArgs) => r.1.2.2) :=
  Primrec.snd.comp randomPair_proj_w

private lemma randomPair_acceptable_eq (c : Code) (r : randomPairArgs) :
    decide (2 ^ r.1.1.2.1 ≤ 2 ^ r.1.1.2.2.1 *
      randomPairCount c r.1.1.1 r.2 r.1.1.2.1 r.1.1.2.2.2 (r.1.2.1 + 1)) =
    randomPairAcceptable c r.1.1.1 r.2 r.1.1.2.1 r.1.1.2.2.1 r.1.1.2.2.2 (r.1.2.1 + 1) := by
  rcases r with ⟨⟨⟨x, n, l, k⟩, w1, w2⟩, y⟩; rfl

private theorem randomPairAcceptable_cond_primrec (c : Code) :
    Primrec (fun r : randomPairArgs =>
      randomPairAcceptable c r.1.1.1 r.2 r.1.1.2.1 r.1.1.2.2.1 r.1.1.2.2.2 (r.1.2.1 + 1)) := by
  have ht : Primrec (fun (r : randomPairArgs) => r.1.2.1 + 1) :=
    Primrec.succ.comp randomPair_proj_w1
  have h_count_in : Primrec (fun (r : randomPairArgs) =>
      (((r.1.1.1, r.2), r.1.1.2.1), (r.1.1.2.2.2, r.1.2.1 + 1))) :=
    Primrec.pair (Primrec.pair (Primrec.pair randomPair_proj_x randomPair_proj_y) randomPair_proj_n)
      (Primrec.pair randomPair_proj_k ht)
  have hcount : Primrec (fun (r : randomPairArgs) =>
      randomPairCount c r.1.1.1 r.2 r.1.1.2.1 r.1.1.2.2.2 (r.1.2.1 + 1)) :=
    (randomPairCount_primrec c).comp h_count_in
  have hpow2n : Primrec (fun (r : randomPairArgs) => 2 ^ r.1.1.2.1) :=
    primrec_two_pow_aux.comp randomPair_proj_n
  have hpow2l : Primrec (fun (r : randomPairArgs) => 2 ^ r.1.1.2.2.1) :=
    primrec_two_pow_aux.comp randomPair_proj_l
  have hrhs : Primrec (fun (r : randomPairArgs) =>
      2 ^ r.1.1.2.2.1 * randomPairCount c r.1.1.1 r.2 r.1.1.2.1 r.1.1.2.2.2 (r.1.2.1 + 1)) :=
    Primrec.nat_mul.comp hpow2l hcount
  exact (PrimrecPred.decide (Primrec.nat_le.comp hpow2n hrhs)).of_eq
    (fun r => randomPair_acceptable_eq c r)

private lemma randomPair_not_mem_eq (r : randomPairArgs) :
    randomCondNotMem r.2 r.1.2.2 = decide (r.2 ∉ r.1.2.2) := by
  rcases r with ⟨⟨p, w1, w2⟩, y⟩; rfl

private theorem randomPairStep_not_mem_primrec :
    Primrec (fun r : randomPairArgs => decide (r.2 ∉ r.1.2.2) ) := by
  have h_arg : Primrec (fun (r : randomPairArgs) => (r.2, r.1.2.2)) :=
    Primrec.pair Primrec.snd randomPair_proj_w2
  have hcomp := randomCondNotMem_primrec.comp h_arg
  exact hcomp.of_eq (fun r => randomPair_not_mem_eq r)

private lemma randomPair_step_cond_eq (c : Code) (r : randomPairArgs) :
    (decide (r.2 ∉ r.1.2.2) &&
      randomPairAcceptable c r.1.1.1 r.2 r.1.1.2.1 r.1.1.2.2.1 r.1.1.2.2.2 (r.1.2.1 + 1)) =
    decide (r.2 ∉ r.1.2.2 ∧
      randomPairAcceptable c r.1.1.1 r.2 r.1.1.2.1 r.1.1.2.2.1 r.1.1.2.2.2 (r.1.2.1 + 1)) := by
  rcases r with ⟨⟨⟨x, n, l, k⟩, w1, w2⟩, y⟩
  by_cases h1 : y ∈ w2 <;> simp [h1]

private theorem randomPairStep_cond_primrec (c : Code) :
    Primrec (fun r : randomPairArgs => decide (r.2 ∉ r.1.2.2 ∧
      randomPairAcceptable c r.1.1.1 r.2 r.1.1.2.1 r.1.1.2.2.1 r.1.1.2.2.2 (r.1.2.1 + 1))) :=
  (Primrec.and.comp randomPairStep_not_mem_primrec (randomPairAcceptable_cond_primrec c)).of_eq
    (fun r => randomPair_step_cond_eq c r)

/-- Argument type of the enumeration step without the candidate string: the parameters
`(x, n, l, k)` together with a stage number and the list enumerated so far. -/
abbrev randomPairStepArgs := (BitString × ℕ × ℕ × ℕ) × (ℕ × List BitString)

private theorem randomPair_proj_s1 : Primrec (fun (r : randomPairStepArgs) => r.1) := Primrec.fst
private theorem randomPair_proj_s_x : Primrec (fun (r : randomPairStepArgs) => r.1.1) :=
  Primrec.fst.comp randomPair_proj_s1
private theorem randomPair_proj_s_nlk : Primrec (fun (r : randomPairStepArgs) => r.1.2) :=
  Primrec.snd.comp randomPair_proj_s1
private theorem randomPair_proj_s_n : Primrec (fun (r : randomPairStepArgs) => r.1.2.1) :=
  Primrec.fst.comp randomPair_proj_s_nlk
private theorem randomPair_proj_s_lk : Primrec (fun (r : randomPairStepArgs) => r.1.2.2) :=
  Primrec.snd.comp randomPair_proj_s_nlk
private theorem randomPair_proj_s_k : Primrec (fun (r : randomPairStepArgs) => r.1.2.2.2) :=
  Primrec.snd.comp randomPair_proj_s_lk
private theorem randomPair_proj_s2 : Primrec (fun (r : randomPairStepArgs) => r.2) := Primrec.snd
private theorem randomPair_proj_s_w1 : Primrec (fun (r : randomPairStepArgs) => r.2.1) :=
  Primrec.fst.comp randomPair_proj_s2
private theorem randomPair_proj_s_w2 : Primrec (fun (r : randomPairStepArgs) => r.2.2) :=
  Primrec.snd.comp randomPair_proj_s2

private theorem randomPairStep_cand_primrec (c : Code) :
    Primrec (fun r : randomPairStepArgs =>
      randomPairCandidateList c r.1.1 r.1.2.1 r.1.2.2.2 (r.2.1 + 1)) := by
  have ht : Primrec (fun r : randomPairStepArgs => r.2.1 + 1) :=
    Primrec.succ.comp randomPair_proj_s_w1
  have hin : Primrec (fun r : randomPairStepArgs => (((r.1.1, r.1.2.1), r.1.2.2.2), r.2.1 + 1)) :=
    Primrec.pair
      (Primrec.pair (Primrec.pair randomPair_proj_s_x randomPair_proj_s_n) randomPair_proj_s_k) ht
  exact (randomPairCandidateList_primrec c).comp hin

private theorem randomPairStep_primrec (c : Code) : Primrec₂ (randomPairStep c) := by
  have hcand := randomPairStep_cand_primrec c
  have h_and := randomPairStep_cond_primrec c
  have hfilt := list_filter_primrec hcand h_and.to₂
  exact Primrec.list_append.comp randomPair_proj_s_w2 hfilt

private lemma randomPair_stage_eq (c : Code) (p : BitString × ℕ × ℕ × ℕ) (t : ℕ) :
    Nat.rec [] (fun m IH => randomPairStep c p (m, IH)) t =
    randomPairStage c p.1 p.2.1 p.2.2.1 p.2.2.2 t := by
  rcases p with ⟨x, n, l, k⟩
  induction t with
  | zero => rfl
  | succ t ih =>
      dsimp
      rw [ih]
      rfl

private theorem randomPairStage_primrec (c : Code) :
    Primrec (fun q : (BitString × ℕ × ℕ × ℕ) × ℕ =>
      randomPairStage c q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) := by
  have hbase : Primrec (fun (_ : BitString × ℕ × ℕ × ℕ) => ([] : List BitString)) :=
    Primrec.const []
  have hrec := Primrec.nat_rec hbase (randomPairStep_primrec c)
  have hrec2 : Primrec₂ (fun (p : BitString × ℕ × ℕ × ℕ) (t : ℕ) =>
      randomPairStage c p.1 p.2.1 p.2.2.1 p.2.2.2 t) :=
    hrec.of_eq (fun p t => randomPair_stage_eq c p t)
  exact hrec2.of_eq (fun p t => rfl)

private theorem randomPairStageList_primrec (c : Code) :
    Primrec (fun pzt : (BitString × BitString) × ℕ =>
      randomPairStageList c pzt.1.1 pzt.1.2 pzt.2) := by
  unfold randomPairStageList
  have hz : Primrec (fun pzt : (BitString × BitString) × ℕ => pzt.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hz2 : Primrec (fun pzt : (BitString × BitString) × ℕ => decodeSecond pzt.1.2) :=
    decodeSecond_primrec.comp hz
  have hn : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      bitsToNat (decodeFirst pzt.1.2)) :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp hz)
  have hl : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      bitsToNat (decodeFirst (decodeSecond pzt.1.2))) :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp hz2)
  have hx : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      decodeSecond (decodeSecond pzt.1.2)) := decodeSecond_primrec.comp hz2
  have hk : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      pzt.1.1.length - bitsToNat (decodeFirst (decodeSecond pzt.1.2)) - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_sub.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)) hl)
      (Primrec.const 1)
  have ht : Primrec (fun pzt : (BitString × BitString) × ℕ => pzt.2) := Primrec.snd
  have hin : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      ((decodeSecond (decodeSecond pzt.1.2),
        bitsToNat (decodeFirst pzt.1.2),
        bitsToNat (decodeFirst (decodeSecond pzt.1.2)),
        pzt.1.1.length - bitsToNat (decodeFirst (decodeSecond pzt.1.2)) - 1), pzt.2)) :=
    Primrec.pair (Primrec.pair hx (Primrec.pair hn (Primrec.pair hl hk))) ht
  exact (randomPairStage_primrec c).comp hin

private theorem randomPairCheck_primrec (c : Code) :
    Primrec (fun pzt : (BitString × BitString) × ℕ =>
      randomPairCheck c pzt.1.1 pzt.1.2 pzt.2) := by
  unfold randomPairCheck
  have hp : Primrec (fun pzt : (BitString × BitString) × ℕ => pzt.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hall : Primrec (fun pzt : (BitString × BitString) × ℕ => allStrings pzt.1.1.length) :=
    allStrings_primrec.comp (Primrec.list_length.comp hp)
  have hpred : Primrec (fun pzt : ((BitString × BitString) × ℕ) × BitString =>
      decide (pzt.2 = pzt.1.1.1)) :=
    (PrimrecPred.decide Primrec.eq).comp (Primrec.pair Primrec.snd (hp.comp Primrec.fst))
  have hm : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      (allStrings pzt.1.1.length).findIdx (fun y => decide (y = pzt.1.1))) :=
    Primrec.list_findIdx hall hpred.to₂
  have hlen : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      (randomPairStageList c pzt.1.1 pzt.1.2 pzt.2).length) :=
    Primrec.list_length.comp (randomPairStageList_primrec c)
  exact PrimrecPred.decide (Primrec.nat_lt.comp hm hlen)

private theorem randomPairGet_primrec (c : Code) :
    Primrec (fun pzt : (BitString × BitString) × ℕ =>
      randomPairGet c pzt.1.1 pzt.1.2 pzt.2) := by
  unfold randomPairGet
  have hp : Primrec (fun pzt : (BitString × BitString) × ℕ => pzt.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hall : Primrec (fun pzt : (BitString × BitString) × ℕ => allStrings pzt.1.1.length) :=
    allStrings_primrec.comp (Primrec.list_length.comp hp)
  have hpred : Primrec (fun pzt : ((BitString × BitString) × ℕ) × BitString =>
      decide (pzt.2 = pzt.1.1.1)) :=
    (PrimrecPred.decide Primrec.eq).comp (Primrec.pair Primrec.snd (hp.comp Primrec.fst))
  have hm : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      (allStrings pzt.1.1.length).findIdx (fun y => decide (y = pzt.1.1))) :=
    Primrec.list_findIdx hall hpred.to₂
  have hstage : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      randomPairStageList c pzt.1.1 pzt.1.2 pzt.2) :=
    randomPairStageList_primrec c
  exact (Primrec.list_getD []).comp hstage hm

private theorem randomPairDecoder_isDecompressor (c : Code) :
    isDecompressor (randomPairDecoder c) := by
  unfold randomPairDecoder isDecompressor
  have hcheck : Partrec₂ (fun (pz : BitString × BitString) (t : ℕ) =>
      Part.some (randomPairCheck c pz.1 pz.2 t)) :=
    (Partrec.comp Partrec.some (randomPairCheck_primrec c).to_comp.partrec).to₂
  have hrfind : Partrec (fun pz : BitString × BitString =>
      Nat.rfind (fun t => Part.some (randomPairCheck c pz.1 pz.2 t))) :=
    Partrec.rfind hcheck
  have hget : Partrec (fun pzt : (BitString × BitString) × ℕ =>
      Part.some (randomPairGet c pzt.1.1 pzt.1.2 pzt.2)) :=
    Partrec.comp Partrec.some (randomPairGet_primrec c).to_comp.partrec
  exact Partrec.bind hrfind hget.to₂

/-- **Exercise 59(a).** If the probability that `C(y | ⟨r, x⟩) ≤ k` for a uniformly random
`n`-bit `r` is at least `2 ^ (-l)`, then `C(y | ⟨n, ⟨l, x⟩⟩) ≤ k + l + O(1)`. -/
theorem randomPair_probability_bound (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString) (n k l : ℕ),
      (2 : ℝ) ^ n ≤ (2 : ℝ) ^ l *
          (((allStrings n).filter
            (fun r => decide (condK U y (pairCode r x) ≤ (k : ℕ∞)))).length : ℝ) →
        condK U y (pairCode (Nat.bits n) (pairCode (Nat.bits l) x)) ≤ ((k + l + c : ℕ) : ℕ∞) := by
  obtain ⟨c_code, hc_code⟩ : ∃ c_code : Code, IsCodeFor c_code U :=
    Nat.Partrec.Code.exists_code.mp hU.1
  let D := randomPairDecoder c_code
  have hD : isDecompressor D := randomPairDecoder_isDecompressor c_code
  obtain ⟨c_opt, hc_opt⟩ := hU.2 D hD
  refine ⟨c_opt + 1, ?_⟩
  intro x y n k l h
  obtain ⟨T, hy_stage⟩ := randomPairStage_eventually_mem hc_code h
  let S := randomPairStage c_code x n l k T
  let m := S.idxOf y
  have hm_lt : m < S.length := List.idxOf_lt_length_of_mem hy_stage
  have hS_len := randomPairStage_length_bound c_code x n l k T
  have hm_lt_pow : m < (allStrings (k + l + 1)).length := by
    rw [length_allStrings]
    exact lt_trans hm_lt hS_len
  let p := (allStrings (k + l + 1)).getD m []
  have hp_eq : p = (allStrings (k + l + 1))[m] := by
    dsimp [p]
    rw [List.getD, List.getElem?_eq_getElem hm_lt_pow]
    rfl
  have hp_mem : p ∈ allStrings (k + l + 1) := by
    rw [hp_eq]
    exact List.getElem_mem hm_lt_pow
  have hp_len : p.length = k + l + 1 := (mem_allStrings (k + l + 1) p).mp hp_mem
  have hp_findIdx : (allStrings p.length).findIdx (fun w => decide (w = p)) = m := by
    rw [findIdx_decide_eq, hp_len, hp_eq]
    exact List.Nodup.idxOf_getElem (allStrings_nodup (k + l + 1)) m hm_lt_pow
  have hp_idx : (allStrings p.length).findIdx (fun w => decide (w = p)) = m := hp_findIdx
  let z := pairCode (Nat.bits n) (pairCode (Nat.bits l) x)
  have h_dec1 : decodeFirst z = Nat.bits n :=
    decodeFirst_pairCode (Nat.bits n) (pairCode (Nat.bits l) x)
  have h_dec2 : decodeSecond z = pairCode (Nat.bits l) x :=
    decodeSecond_pairCode (Nat.bits n) (pairCode (Nat.bits l) x)
  have h_b1 : bitsToNat (decodeFirst z) = n := by rw [h_dec1, bitsToNat_bits]
  have h_b2 : bitsToNat (decodeFirst (decodeSecond z)) = l := by
    rw [h_dec2, decodeFirst_pairCode, bitsToNat_bits]
  have h_b3 : decodeSecond (decodeSecond z) = x := by
    rw [h_dec2, decodeSecond_pairCode]
  have h_k : p.length - l - 1 = k := by rw [hp_len]; omega
  have h_prod : produces D p z y := by
    change y ∈ randomPairDecoder c_code (p, z)
    unfold randomPairDecoder randomPairGet randomPairCheck randomPairStageList
    dsimp only
    rw [h_b1, h_b2, h_b3, h_k, hp_idx]
    have h_dom : (Nat.rfind (fun t => Part.some (decide
        (m < (randomPairStage c_code x n l k t).length)))).Dom := by
      rw [Nat.rfind_dom]
      exact ⟨T, Part.mem_some_iff.mpr (decide_eq_true hm_lt).symm, fun _ => Part.some_dom _⟩
    obtain ⟨t0, ht0_mem⟩ := Part.dom_iff_mem.mp h_dom
    have ht0_le : t0 ≤ T := by
      by_contra h_lt
      have h_false := Nat.rfind_min ht0_mem (not_le.mp h_lt)
      have h_true : true ∈ Part.some (decide (m < (randomPairStage c_code x n l k T).length)) :=
        Part.mem_some_iff.mpr (decide_eq_true hm_lt).symm
      have h_eq := Part.mem_unique h_false h_true
      cases h_eq
    have ht0_eq : Nat.rfind (fun t => Part.some (decide
        (m < (randomPairStage c_code x n l k t).length))) = Part.some t0 :=
      Part.eq_some_iff.mpr ht0_mem
    rw [ht0_eq, Part.bind_some, Part.mem_some_iff]
    have ht0_spec := Nat.rfind_spec ht0_mem
    have ht0_lt : m < (randomPairStage c_code x n l k t0).length := by simpa using ht0_spec
    have h_prefix := randomPairStage_mono c_code x n l k ht0_le
    rw [← getD_eq_of_prefix_of_lt_length h_prefix m [] ht0_lt]
    rw [List.getD, List.getElem?_idxOf hy_stage]
    rfl
  have h_condD : condK D y z ≤ ((k + l + 1 : ℕ) : ℕ∞) := by
    have := condK_le_of_produces h_prod
    rw [hp_len] at this
    exact this
  have h_opt := hc_opt y z
  calc condK U y z ≤ condK D y z + (c_opt : ℕ∞) := h_opt
    _ ≤ ((k + l + 1 : ℕ) : ℕ∞) + (c_opt : ℕ∞) := by gcongr
    _ = ((k + l + (c_opt + 1) : ℕ) : ℕ∞) := by push_cast; ring

/-! ### Exercise 59: the two auxiliary transfer lemmas -/

/-- Decompressor for `condK_le_condK_pair_add_two_plainK`: the program is `pairCode qw py`,
where `qw` computes the extra condition `w` and `py` computes the answer from
`pairCode w x`. -/
def dropConditionDecompressor (U : Map) : Map :=
  fun p => (U (decodeFirst p.1, [])).bind (fun w => U (decodeSecond p.1, pairCode w p.2))

private theorem dropConditionDecompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (dropConditionDecompressor U) := by
  have h1 : Partrec (fun p : BitString × BitString => U (decodeFirst p.1, [])) := by
    have hp : Computable (fun p : BitString × BitString =>
        (decodeFirst p.1, ([] : BitString))) :=
      Computable.pair (decodeFirst_computable.comp Computable.fst) (Computable.const [])
    exact Partrec.comp hU hp
  have h2 : Partrec (fun q : (BitString × BitString) × BitString =>
      U (decodeSecond q.1.1, pairCode q.2 q.1.2)) := by
    have hpc : Computable (fun q : (BitString × BitString) × BitString =>
        pairCode q.2 q.1.2) :=
      Computable₂.comp pairCode_computable Computable.snd
        (Computable.snd.comp Computable.fst)
    have hp : Computable (fun q : (BitString × BitString) × BitString =>
        (decodeSecond q.1.1, pairCode q.2 q.1.2)) :=
      Computable.pair
        (decodeSecond_computable.comp (Computable.fst.comp Computable.fst)) hpc
    exact Partrec.comp hU hp
  exact Partrec.bind h1 h2

/-- **Dropping an extra condition.**  `C(y | x) ≤ C(y | ⟨w, x⟩) + 2 C(w) + O(1)`:
a self-delimiting shortest program for `w` is put in front of the conditional
program.  This is the relativized form of `plainK_sub_condK_le_two_mul_plainK`. -/
theorem condK_le_condK_pair_add_two_plainK (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ (y w x : BitString),
      condK U y x ≤ condK U y (pairCode w x) + ((2 * cVal U w + k : ℕ) : ℕ∞) := by
  have plainKNeTopAux : ∀ (U : Map), isOptimalConditional U → ∀ (y : BitString),
      plainK U y ≠ ⊤ := by
    intro U hU y h
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    have h_le := hc y
    rw [h] at h_le
    cases h_le
  have condKNeTopAux : ∀ (U : Map), isOptimalConditional U → ∀ (x y : BitString),
      condK U x y ≠ ⊤ := by
    intro U hU x y h
    obtain ⟨c, hc⟩ := condK_le_plainK U hU
    have h_le := hc x y
    have h_plain : plainK U x ≠ ⊤ := by
      obtain ⟨c', hc'⟩ := plainK_le_length U hU
      have h_le' := hc' x
      intro h'
      rw [h'] at h_le'
      cases h_le'
    have h_top_le : (⊤ : ℕ∞) ≤ plainK U x + (c : ℕ∞) := by
      calc (⊤ : ℕ∞) = condK U x y := h.symm
      _             ≤ plainK U x + (c : ℕ∞) := h_le
    have hc_ne : (c : ℕ∞) ≠ ⊤ := WithTop.coe_ne_top
    have hsum : plainK U x + (c : ℕ∞) ≠ ⊤ := WithTop.add_ne_top.mpr ⟨h_plain, hc_ne⟩
    exact hsum (top_unique h_top_le)
  let D := dropConditionDecompressor U
  have hD : isDecompressor D := dropConditionDecompressor_isDecompressor U hU.1
  obtain ⟨c2, hc2⟩ := hU.2 D hD
  refine ⟨c2 + 1, ?_⟩
  intro y w x
  have hw_top := plainKNeTopAux U hU w
  have hy_top := condKNeTopAux U hU y (pairCode w x)
  have h_eq_w : plainK U w = (cVal U w : ℕ∞) := (ENat.coe_toNat hw_top).symm
  have h_le_w : condK U w [] ≤ (cVal U w : ℕ∞) := by
    change plainK U w ≤ (cVal U w : ℕ∞)
    rw [h_eq_w]
  rw [condK_le_iff] at h_le_w
  obtain ⟨qw, hqw_len, hqw_prod⟩ := h_le_w
  change qw.length ≤ cVal U w at hqw_len
  have h_eq_y : condK U y (pairCode w x) = (condCVal U y (pairCode w x) : ℕ∞) :=
    (ENat.coe_toNat hy_top).symm
  have h_le_y : condK U y (pairCode w x) ≤ (condCVal U y (pairCode w x) : ℕ∞) := by
    rw [h_eq_y]
  rw [condK_le_iff] at h_le_y
  obtain ⟨py, hpy_len, hpy_prod⟩ := h_le_y
  change py.length ≤ condCVal U y (pairCode w x) at hpy_len
  have h_prod_D : produces D (pairCode qw py) x y := by
    dsimp [D, dropConditionDecompressor, produces]
    rw [decodeFirst_pairCode, decodeSecond_pairCode, Part.mem_bind_iff]
    exact ⟨w, hqw_prod, hpy_prod⟩
  have h_D_le : condK D y x ≤ ((pairCode qw py).length : ℕ∞) := by
    rw [condK_le_iff]
    exact ⟨pairCode qw py, le_rfl, h_prod_D⟩
  have h_len_bound : (pairCode qw py).length ≤
      2 * cVal U w + condCVal U y (pairCode w x) + 1 := by
    rw [length_pairCode]
    omega
  calc condK U y x ≤ condK D y x + (c2 : ℕ∞) := hc2 y x
    _ ≤ ((pairCode qw py).length : ℕ∞) + (c2 : ℕ∞) := by gcongr
    _ ≤ ((2 * cVal U w + condCVal U y (pairCode w x) + 1 : ℕ) : ℕ∞) + (c2 : ℕ∞) := by
        gcongr
    _ = ((condCVal U y (pairCode w x) : ℕ) : ℕ∞) +
          ((2 * cVal U w + (c2 + 1) : ℕ) : ℕ∞) := by
        push_cast
        ring
    _ = condK U y (pairCode w x) + ((2 * cVal U w + (c2 + 1) : ℕ) : ℕ∞) := by
        rw [h_eq_y]

/-- Decompressor for `relativized_conservation_compose`: run `f` on the decoded condition and feed
the result to `U`. -/
def relativizedConservationDecompressor (U : Map) (f : BitString × BitString →. BitString) : Map :=
  fun p => (f (decodeSecond p.2, decodeFirst p.2)).bind (fun v => U (p.1, v))

end Kolmogorov
