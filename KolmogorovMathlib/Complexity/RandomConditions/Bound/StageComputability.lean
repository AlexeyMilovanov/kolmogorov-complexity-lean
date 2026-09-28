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
import KolmogorovMathlib.Complexity.RandomConditions.Enumeration

/-!
# Effectiveness of the stage enumeration

The obligations behind the enumeration of `HeavyStringsEnumeration`.
`randomCondMemSnapshot_primrec` makes membership in the bounded-time output snapshot of a
fixed machine primitive recursive and `randomCondCountFn` counts the strings of a given length
in it; `mem_conditionalOutputSnapshot_mono` and `list_countP_mono` say both grow with the step
bound.

`T1` is the argument type of the enumeration step — the parameters `(n, l, k)` with the
condition data — and the `proj_*` lemmas project its fields primitive recursively, which is
what lets the step be assembled by combinators.
-/



namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-- Counting with a weaker predicate gives a larger count: if `p x` implies `q x` for every
element of `l`, then `l.countP p ≤ l.countP q`. -/
lemma list_countP_mono {α} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x → q x) :
    l.countP p ≤ l.countP q := by
  exact List.countP_mono_left h

/-- The bounded-time output snapshot only grows with the step bound: a string present after
`t1` steps is present after `t2 ≥ t1` steps. -/
lemma mem_conditionalOutputSnapshot_mono (c : Code) {y : BitString} {k t1 t2 : ℕ}
    (h : t1 ≤ t2) {x : BitString} (hx : x ∈ conditionalOutputSnapshot c y k t1) :
    x ∈ conditionalOutputSnapshot c y k t2 := by
  unfold conditionalOutputSnapshot at hx ⊢
  rw [List.mem_filterMap] at hx ⊢
  obtain ⟨p, hp, hrun⟩ := hx
  exact ⟨p, hp, conditionalRunOut_mono c h hrun⟩

/-- For a duplicate-free list, filtering and taking the length agrees with the cardinality of
the corresponding filtered finite set. -/
lemma length_filter_eq_card_toFinset_filter {α : Type*} [DecidableEq α] {L : List α}
    (hL : L.Nodup) (P : α → Bool) : (L.filter P).length =
    (L.toFinset.filter (fun x => P x = true)).card := by
  rw [← List.toFinset_card_of_nodup (List.Nodup.filter P hL), List.toFinset_filter]

/-- Membership of a string in the bounded-time output snapshot of a fixed machine is a
primitive recursive predicate of the condition, the string and the two bounds. -/
theorem randomCondMemSnapshot_primrec (c : Code) :
    Primrec (fun r : (BitString × BitString) × (ℕ × ℕ) =>
      decide (r.1.2 ∈ conditionalOutputSnapshot c r.1.1 r.2.1 r.2.2)) := by
  have hy : Primrec (fun r : (BitString × BitString) × (ℕ × ℕ) => r.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun r : (BitString × BitString) × (ℕ × ℕ) => r.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hk : Primrec (fun r : (BitString × BitString) × (ℕ × ℕ) => r.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun r : (BitString × BitString) × (ℕ × ℕ) => r.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hykt : Primrec (fun r : (BitString × BitString) × (ℕ × ℕ) =>
      ((r.1.1, r.2.1), r.2.2)) := Primrec.pair (Primrec.pair hy hk) ht
  have hsnap : Primrec (fun r : (BitString × BitString) × (ℕ × ℕ) =>
      conditionalOutputSnapshot c r.1.1 r.2.1 r.2.2) :=
    (conditionalOutputSnapshot_primrec c).comp hykt
  exact (bitString_mem_primrec.comp hx hsnap).of_eq (fun _ => rfl)

/-- The number of strings of a given length that occur in the bounded-time output snapshot of
the machine `c`; the uncurried form used to state primitive recursiveness of the count. -/
def randomCondCountFn (c : Code) (r : (BitString × ℕ) × (ℕ × ℕ)) : ℕ :=
  ((allStrings r.1.2).filter
    (fun y => decide (r.1.1 ∈ conditionalOutputSnapshot c y r.2.1 r.2.2))).length

/-- Argument type of the enumeration step: the parameters `(n, l, k)` and the condition data,
together with the stage number and the list enumerated so far, paired with a string. -/
abbrev T1 := ((ℕ × (ℕ × ℕ)) × (ℕ × List BitString)) × BitString

/-- The first component of an argument of type `T1` is a primitive recursive function of it. -/
theorem proj_pz_x : Primrec (fun (r : T1) => r.1) := Primrec.fst
/-- The candidate string of an argument of type `T1` is a primitive recursive function of it. -/
theorem proj_x : Primrec (fun (r : T1) => r.2) := Primrec.snd
/-- The parameter block of an argument of type `T1` is a primitive recursive function of it. -/
theorem proj_p : Primrec (fun (r : T1) => r.1.1) := Primrec.fst.comp proj_pz_x
/-- The length parameter `n` of an argument of type `T1` is primitive recursive in it. -/
theorem proj_n : Primrec (fun (r : T1) => r.1.1.1) := Primrec.fst.comp proj_p
/-- The pair `(l, k)` of an argument of type `T1` is primitive recursive in it. -/
theorem proj_lk : Primrec (fun (r : T1) => r.1.1.2) := Primrec.snd.comp proj_p
/-- The parameter `l` of an argument of type `T1` is primitive recursive in it. -/
theorem proj_l : Primrec (fun (r : T1) => r.1.1.2.1) := Primrec.fst.comp proj_lk
/-- The parameter `k` of an argument of type `T1` is primitive recursive in it. -/
theorem proj_k : Primrec (fun (r : T1) => r.1.1.2.2) := Primrec.snd.comp proj_lk
/-- The stage block of an argument of type `T1` is primitive recursive in it. -/
theorem proj_z : Primrec (fun (r : T1) => r.1.2) := Primrec.snd.comp proj_pz_x
/-- The stage number of an argument of type `T1` is primitive recursive in it. -/
theorem proj_z1 : Primrec (fun (r : T1) => r.1.2.1) := Primrec.fst.comp proj_z
/-- The list enumerated so far, in an argument of type `T1`, is primitive recursive in it. -/
theorem proj_z2 : Primrec (fun (r : T1) => r.1.2.2) := Primrec.snd.comp proj_z

/-- Decides that a string does not occur in a list. -/
def randomCondNotMem (x : BitString) (l : List BitString) : Bool := decide (x ∉ l)

/-- Non-membership of a string in a list of strings is primitive recursive. -/
theorem randomCondNotMem_primrec :
    Primrec (fun (p : BitString × List BitString) => randomCondNotMem p.1 p.2) :=
  (Primrec.not.comp bitString_mem_primrec).of_eq (fun _ => decide_not.symm)

/-- Argument type of the enumeration step without the candidate string: the parameters
`(n, l, k)` together with the stage number and the list enumerated so far. -/
abbrev StepP := (ℕ × (ℕ × ℕ)) × (ℕ × List BitString)

/-- The parameter block of an argument of type `StepP` is primitive recursive in it. -/
theorem proj_step_1 : Primrec (fun (r : StepP) => r.1) := Primrec.fst
/-- The parameter `n` of an argument of type `StepP` is primitive recursive in it. -/
theorem proj_step_1_1 : Primrec (fun (r : StepP) => r.1.1) := Primrec.fst.comp proj_step_1
/-- The pair `(l, k)` of an argument of type `StepP` is primitive recursive in it. -/
theorem proj_step_lk : Primrec (fun (r : StepP) => r.1.2) := Primrec.snd.comp proj_step_1
/-- The parameter `k` of an argument of type `StepP` is primitive recursive in it. -/
theorem proj_step_p122 : Primrec (fun r : StepP => r.1.2.2) := Primrec.snd.comp proj_step_lk
/-- The stage block of an argument of type `StepP` is primitive recursive in it. -/
theorem proj_step_2 : Primrec (fun (r : StepP) => r.2) := Primrec.snd
/-- The stage number of an argument of type `StepP` is primitive recursive in it. -/
theorem proj_step_z1 : Primrec (fun r : StepP => r.2.1) := Primrec.fst.comp proj_step_2
/-- The list enumerated so far, in an argument of type `StepP`, is primitive recursive in it. -/
theorem proj_step_z2 : Primrec (fun r : StepP => r.2.2) := Primrec.snd.comp proj_step_2

/-- Argument type of the stage function: the parameters `(n, l, k)` and the stage number. -/
abbrev StageP := (ℕ × (ℕ × ℕ)) × ℕ

private theorem randomCondStage_eventually_mem {c : Code} {U : Map} (hc : IsCodeFor c U)
    {x : BitString} {n k l : ℕ}
    (h : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ l *
      (((allStrings n).filter (fun y => decide (condK U x y ≤ (k : ℕ∞)))).length : ℝ)) :
    ∃ T, x ∈ randomCondStage c n l k T := by
  have h_nat : 2 ^ n ≤
      2 ^ l * ((allStrings n).filter (fun y => decide (condK U x y ≤ (k : ℕ∞)))).length := by
    have h_cast : (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by push_cast; rfl
    have h_cast2 : (2 : ℝ) ^ l = ((2 ^ l : ℕ) : ℝ) := by push_cast; rfl
    rw [h_cast, h_cast2, ← Nat.cast_mul] at h
    exact Nat.cast_le.mp h
  have h_run : ∀ y ∈ (allStrings n).filter (fun y => decide (condK U x y ≤ (k : ℕ∞))),
      ∃ t_y p_y, p_y.length ≤ k ∧ conditionalRunOut c t_y p_y y = some x := by
    intro y hy
    rw [List.mem_filter] at hy
    have h_cond : condK U x y ≤ (k : ℕ∞) := by simpa using hy.2
    rw [condK_le_iff] at h_cond
    obtain ⟨p, hp_len, hp_prod⟩ := h_cond
    obtain ⟨t, ht⟩ := conditionalRunOut_complete hc hp_prod
    exact ⟨t, p, hp_len, ht⟩
  choose t_fn p_fn hp_len ht_run using h_run
  let Y := (allStrings n).filter (fun y => decide (condK U x y ≤ (k : ℕ∞)))
  let T := (Y.map (fun y => if hy : y ∈ Y then t_fn y hy else 0)).sum + 1
  have hT_le : ∀ y (hy : y ∈ Y), t_fn y hy ≤ T := by
    intro y hy
    have : t_fn y hy ≤ (Y.map (fun y => if hy : y ∈ Y then t_fn y hy else 0)).sum := by
      have h_mem : t_fn y hy ∈ Y.map (fun y => if hy : y ∈ Y then t_fn y hy else 0) := by
        rw [List.mem_map]
        exact ⟨y, hy, by simp [hy]⟩
      exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ h_mem
    exact Nat.le_succ_of_le this
  have h_snap : ∀ y ∈ Y, x ∈ conditionalOutputSnapshot c y k T := by
    intro y hy
    have h_run_y := ht_run y hy
    have h_mono := conditionalRunOut_mono c (hT_le y hy) h_run_y
    exact mem_conditionalOutputSnapshot_of_run (hp_len y hy) h_mono
  have h_count : Y.length ≤ randomCondCount c x n k T := by
    unfold randomCondCount Y
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply list_countP_mono
    intro y hy h_cond
    have h_in_Y : y ∈ (allStrings n).filter (fun y => decide (condK U x y ≤ (k : ℕ∞))) := by
      rw [List.mem_filter]
      exact ⟨hy, h_cond⟩
    simp only [decide_eq_true_eq]
    exact h_snap y h_in_Y
  have h_acc : randomCondAcceptable c x n l k T = true := by
    unfold randomCondAcceptable
    apply decide_eq_true
    calc 2 ^ n ≤ 2 ^ l * Y.length := h_nat
      _ ≤ 2 ^ l * randomCondCount c x n k T := Nat.mul_le_mul_left _ h_count
  have h_cand : x ∈ randomCondCandidateList c n k T := by
    unfold randomCondCandidateList
    rw [mem_eraseDups_bitString, List.mem_flatMap]
    obtain ⟨y, hy_mem⟩ : ∃ y, y ∈ allStrings n ∧ x ∈ conditionalOutputSnapshot c y k T := by
      have h_nonempty : Y.length > 0 := by
        by_contra h_zero
        have : Y.length = 0 := Nat.le_zero.mp (not_lt.mp h_zero)
        rw [this, Nat.mul_zero] at h_nat
        have : 2 ^ n > 0 := Nat.two_pow_pos n
        omega
      obtain ⟨y, hy⟩ := List.exists_mem_of_length_pos h_nonempty
      have hy_all := (List.mem_filter.mp hy).1
      exact ⟨y, hy_all, h_snap y hy⟩
    exact ⟨y, hy_mem.1, hy_mem.2⟩
  have hT_pos : T ≥ 1 := Nat.succ_le_succ (Nat.zero_le _)
  obtain ⟨t, ht_eq⟩ : ∃ t, T = t + 1 := ⟨T - 1, (Nat.sub_add_cancel hT_pos).symm⟩
  rw [ht_eq] at h_cand h_acc
  refine ⟨t + 1, ?_⟩
  unfold randomCondStage
  by_cases h_prev : x ∈ randomCondStage c n l k t
  · exact List.mem_append_left _ h_prev
  · apply List.mem_append_right
    rw [List.mem_filter]
    exact ⟨h_cand, by simp [h_prev, h_acc]⟩

private theorem randomCondStage_length_bound (c : Code)
    (n l k t : ℕ) : (randomCondStage c n l k t).length < 2 ^ (k + l + 1) := by
  have h_acc : ∀ (t : ℕ) (x : BitString),
      x ∈ randomCondStage c n l k t → 2 ^ n ≤ 2 ^ l * randomCondCount c x n k t := by
    intro t
    induction t with
    | zero =>
        intro x hx
        simp [randomCondStage] at hx
    | succ t ih =>
        intro x hx
        change x ∈ randomCondStage c n l k t ++
          (randomCondCandidateList c n k (t + 1)).filter
            (fun x => x ∉ randomCondStage c n l k t ∧
              randomCondAcceptable c x n l k (t + 1)) at hx
        rw [List.mem_append] at hx
        cases hx with
        | inl hx_prev =>
            have h_mono : randomCondCount c x n k t ≤ randomCondCount c x n k (t + 1) := by
              unfold randomCondCount
              rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
              apply list_countP_mono
              intro y _ hy
              exact decide_eq_true
                (mem_conditionalOutputSnapshot_mono c (Nat.le_succ t) (of_decide_eq_true hy))
            calc 2 ^ n ≤ 2 ^ l * randomCondCount c x n k t := ih x hx_prev
              _ ≤ 2 ^ l * randomCondCount c x n k (t + 1) := Nat.mul_le_mul_left _ h_mono
        | inr hx_new =>
            rw [List.mem_filter] at hx_new
            have h_and := of_decide_eq_true hx_new.2
            have h_dec := h_and.2
            unfold randomCondAcceptable at h_dec
            exact of_decide_eq_true h_dec
  let S := (randomCondStage c n l k t).toFinset
  let Y := (allStrings n).toFinset
  let R := fun (x y : BitString) => decide (x ∈ conditionalOutputSnapshot c y k t)
  have hS_nodup : (randomCondStage c n l k t).Nodup := randomCondStage_nodup c n l k t
  have hS_card : S.card = (randomCondStage c n l k t).length :=
    List.toFinset_card_of_nodup hS_nodup
  have hY_card : Y.card = 2 ^ n := by
    change (allStrings n).toFinset.card = 2 ^ n
    rw [List.toFinset_card_of_nodup (allStrings_nodup n), length_allStrings]
  have h_acc' : ∀ x ∈ S, 2 ^ n ≤ 2 ^ l * randomCondCount c x n k t := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact h_acc t x hx
  have h_count_eq : ∀ x, randomCondCount c x n k t = (Y.filter (fun y => R x y = true)).card := by
    intro x
    unfold randomCondCount R Y
    exact length_filter_eq_card_toFinset_filter (allStrings_nodup n) _
  have h_double := finset_card_double_count S Y R
  have h_each_y : ∀ y ∈ Y, (S.filter (fun x => R x y = true)).card ≤ 2 ^ (k + 1) - 1 := by
    intro y _
    have h_sub : (S.filter (fun x => R x y = true)) ⊆
        (conditionalOutputSnapshot c y k t).toFinset := by
      intro x hx
      rw [Finset.mem_filter, List.mem_toFinset] at hx
      rw [List.mem_toFinset]
      exact of_decide_eq_true hx.2
    have h_le1 := Finset.card_le_card h_sub
    have h_le2 : (conditionalOutputSnapshot c y k t).toFinset.card ≤
        (conditionalOutputSnapshot c y k t).length := List.toFinset_card_le _
    have h_le3 : (conditionalOutputSnapshot c y k t).length ≤
        (boundedPrograms k).length := List.length_filterMap_le _ _
    have h_lt := length_boundedPrograms_lt k
    omega
  have h_sum_y : Y.sum (fun y => (S.filter (fun x => R x y = true)).card) ≤
      2 ^ n * (2 ^ (k + 1) - 1) := by
    calc Y.sum (fun y => (S.filter (fun x => R x y = true)).card)
      _ ≤ Y.sum (fun _ => 2 ^ (k + 1) - 1) := Finset.sum_le_sum h_each_y
      _ = Y.card * (2 ^ (k + 1) - 1) := by simp [Finset.sum_const]
      _ = 2 ^ n * (2 ^ (k + 1) - 1) := by rw [hY_card]
  have h_sum_x : S.sum (fun x => randomCondCount c x n k t) ≤
      2 ^ n * (2 ^ (k + 1) - 1) := by
    have h_eq_sum : S.sum (fun x => randomCondCount c x n k t) =
        S.sum (fun x => (Y.filter (fun y => R x y = true)).card) := by
      refine Finset.sum_congr rfl (fun x _ => h_count_eq x)
    rw [h_eq_sum, h_double]
    exact h_sum_y
  have h_sum_acc : S.sum (fun _ => 2 ^ n) ≤
      S.sum (fun x => 2 ^ l * randomCondCount c x n k t) := by
    apply Finset.sum_le_sum
    intro x hx
    exact h_acc' x hx
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h_sum_acc
  have h_bound : S.card * 2 ^ n ≤ 2 ^ n * (2 ^ l * (2 ^ (k + 1) - 1)) := by
    calc S.card * 2 ^ n
      _ ≤ 2 ^ l * S.sum (fun x => randomCondCount c x n k t) := h_sum_acc
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

private theorem randomCondCandidateList_primrec (c : Code) :
    Primrec (fun q : (ℕ × ℕ) × ℕ => randomCondCandidateList c q.1.1 q.1.2 q.2) := by
  have hn : Primrec (fun q : (ℕ × ℕ) × ℕ => q.1.1) := Primrec.fst.comp Primrec.fst
  have hk : Primrec (fun q : (ℕ × ℕ) × ℕ => q.1.2) := Primrec.snd.comp Primrec.fst
  have ht : Primrec (fun q : (ℕ × ℕ) × ℕ => q.2) := Primrec.snd
  have hall : Primrec (fun q : (ℕ × ℕ) × ℕ => allStrings q.1.1) := allStrings_primrec.comp hn
  have hsnap : Primrec₂ (fun (q : (ℕ × ℕ) × ℕ) (y : BitString) =>
      conditionalOutputSnapshot c y q.1.2 q.2) :=
    ((conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair Primrec.snd (hk.comp Primrec.fst)) (ht.comp Primrec.fst))).to₂
  have hflat : Primrec (fun q : (ℕ × ℕ) × ℕ =>
      (allStrings q.1.1).flatMap (fun y => conditionalOutputSnapshot c y q.1.2 q.2)) :=
    Primrec.list_flatMap hall hsnap
  exact (eraseDups_bitstring_primrec.comp hflat).of_eq (fun _ => rfl)

private lemma randomCond_count_eq (c : Code) (r : (BitString × ℕ) × (ℕ × ℕ)) :
    randomCondCountFn c r = randomCondCount c r.1.1 r.1.2 r.2.1 r.2.2 := by
  rcases r with ⟨⟨x, n⟩, k, t⟩; rfl

private theorem randomCondCount_primrec (c : Code) :
    Primrec (fun r : (BitString × ℕ) × (ℕ × ℕ) =>
      randomCondCount c r.1.1 r.1.2 r.2.1 r.2.2) := by
  have hx : Primrec (fun r : (BitString × ℕ) × (ℕ × ℕ) => r.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hn : Primrec (fun r : (BitString × ℕ) × (ℕ × ℕ) => r.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hk : Primrec (fun r : (BitString × ℕ) × (ℕ × ℕ) => r.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun r : (BitString × ℕ) × (ℕ × ℕ) => r.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hall : Primrec (fun r : (BitString × ℕ) × (ℕ × ℕ) => allStrings r.1.2) :=
    allStrings_primrec.comp hn
  have hy_r : Primrec (fun r : ((BitString × ℕ) × (ℕ × ℕ)) × BitString => r.2) :=
    Primrec.snd
  have hx_r : Primrec (fun r : ((BitString × ℕ) × (ℕ × ℕ)) × BitString => r.1.1.1) :=
    hx.comp Primrec.fst
  have hk_r : Primrec (fun r : ((BitString × ℕ) × (ℕ × ℕ)) × BitString => r.1.2.1) :=
    hk.comp Primrec.fst
  have ht_r : Primrec (fun r : ((BitString × ℕ) × (ℕ × ℕ)) × BitString => r.1.2.2) :=
    ht.comp Primrec.fst
  have h_pair : Primrec (fun r : ((BitString × ℕ) × (ℕ × ℕ)) × BitString =>
      ((r.2, r.1.1.1), (r.1.2.1, r.1.2.2))) :=
    Primrec.pair (Primrec.pair hy_r hx_r) (Primrec.pair hk_r ht_r)
  have hmem : Primrec (fun r : ((BitString × ℕ) × (ℕ × ℕ)) × BitString =>
      decide (r.1.1.1 ∈ conditionalOutputSnapshot c r.2 r.1.2.1 r.1.2.2)) :=
    (randomCondMemSnapshot_primrec c).comp h_pair
  have hfilter : Primrec (fun r : (BitString × ℕ) × (ℕ × ℕ) =>
      (allStrings r.1.2).filter
        (fun y => decide (r.1.1 ∈ conditionalOutputSnapshot c y r.2.1 r.2.2))) :=
    list_filter_primrec hall hmem.to₂
  have hcount : Primrec (fun r => randomCondCountFn c r) :=
    Primrec.list_length.comp hfilter
  exact hcount.of_eq (fun r => randomCond_count_eq c r)

private lemma randomCond_acceptable_eq (c : Code) (r : T1) :
    decide (2 ^ r.1.1.1 ≤ 2 ^ r.1.1.2.1 * randomCondCount c r.2 r.1.1.1 r.1.1.2.2 (r.1.2.1 + 1)) =
    randomCondAcceptable c r.2 r.1.1.1 r.1.1.2.1 r.1.1.2.2 (r.1.2.1 + 1) := by
  rcases r with ⟨⟨⟨n, l, k⟩, z1, z2⟩, x⟩; rfl

private theorem randomCondAcceptable_cond_primrec (c : Code) :
    Primrec (fun r : T1 =>
      randomCondAcceptable c r.2 r.1.1.1 r.1.1.2.1 r.1.1.2.2 (r.1.2.1 + 1)) := by
  have ht : Primrec (fun (r : T1) => r.1.2.1 + 1) := Primrec.succ.comp proj_z1
  have h_count_in : Primrec (fun (r : T1) => ((r.2, r.1.1.1), (r.1.1.2.2, r.1.2.1 + 1))) :=
    Primrec.pair (Primrec.pair proj_x proj_n) (Primrec.pair proj_k ht)
  have hcount : Primrec (fun (r : T1) =>
      randomCondCount c r.2 r.1.1.1 r.1.1.2.2 (r.1.2.1 + 1)) :=
    (randomCondCount_primrec c).comp h_count_in
  have hpow2n : Primrec (fun (r : T1) => 2 ^ r.1.1.1) := primrec_two_pow_aux.comp proj_n
  have hpow2l : Primrec (fun (r : T1) => 2 ^ r.1.1.2.1) := primrec_two_pow_aux.comp proj_l
  have hrhs : Primrec (fun (r : T1) =>
      2 ^ r.1.1.2.1 * randomCondCount c r.2 r.1.1.1 r.1.1.2.2 (r.1.2.1 + 1)) :=
    Primrec.nat_mul.comp hpow2l hcount
  exact (PrimrecPred.decide (Primrec.nat_le.comp hpow2n hrhs)).of_eq
    (fun r => randomCond_acceptable_eq c r)

private lemma randomCond_not_mem_eq (r : T1) :
    randomCondNotMem r.2 r.1.2.2 = decide (r.2 ∉ r.1.2.2) := by
  rcases r with ⟨⟨p, z1, z2⟩, x⟩; rfl

private theorem randomCondStep_not_mem_primrec : Primrec (fun r : T1 => decide (r.2 ∉ r.1.2.2) )
    := by
  have h_arg : Primrec (fun (r : T1) => (r.2, r.1.2.2)) := Primrec.pair Primrec.snd proj_z2
  have hcomp := randomCondNotMem_primrec.comp h_arg
  exact hcomp.of_eq (fun r => randomCond_not_mem_eq r)

private lemma randomCond_step_cond_eq (c : Code) (r : T1) :
    (decide (r.2 ∉ r.1.2.2) &&
      randomCondAcceptable c r.2 r.1.1.1 r.1.1.2.1 r.1.1.2.2 (r.1.2.1 + 1)) =
    decide (r.2 ∉ r.1.2.2 ∧
      randomCondAcceptable c r.2 r.1.1.1 r.1.1.2.1 r.1.1.2.2 (r.1.2.1 + 1)) := by
  rcases r with ⟨⟨⟨n, l, k⟩, z1, z2⟩, x⟩
  by_cases h1 : x ∈ z2 <;> simp [h1]

private theorem randomCondStep_cond_primrec (c : Code) :
    Primrec (fun r : T1 => decide (r.2 ∉ r.1.2.2 ∧
      randomCondAcceptable c r.2 r.1.1.1 r.1.1.2.1 r.1.1.2.2 (r.1.2.1 + 1))) :=
  (Primrec.and.comp (randomCondStep_not_mem_primrec) (randomCondAcceptable_cond_primrec c)).of_eq
    (fun r => randomCond_step_cond_eq c r)

private theorem randomCondStep_cand_primrec (c : Code) :
    Primrec (fun r : StepP => randomCondCandidateList c r.1.1 r.1.2.2 (r.2.1 + 1)) := by
  have ht : Primrec (fun r : StepP => r.2.1 + 1) := Primrec.succ.comp proj_step_z1
  have hnk : Primrec (fun r : StepP => ((r.1.1, r.1.2.2), r.2.1 + 1)) :=
    Primrec.pair (Primrec.pair proj_step_1_1 proj_step_p122) ht
  exact (randomCondCandidateList_primrec c).comp hnk

private theorem randomCondStep_primrec (c : Code) : Primrec₂ (randomCondStep c) := by
  have hcand := randomCondStep_cand_primrec c
  have h_and := randomCondStep_cond_primrec c
  have hfilt := list_filter_primrec hcand h_and.to₂
  exact Primrec.list_append.comp proj_step_z2 hfilt

private lemma randomCond_stage_eq (c : Code) (p : ℕ × (ℕ × ℕ)) (t : ℕ) :
    Nat.rec [] (fun m IH => randomCondStep c p (m, IH)) t =
    randomCondStage c p.1 p.2.1 p.2.2 t := by
  rcases p with ⟨n, l, k⟩
  induction t with
  | zero => rfl
  | succ t ih =>
      dsimp
      rw [ih]
      rfl

private theorem randomCondStage_primrec (c : Code) :
    Primrec (fun q : (ℕ × (ℕ × ℕ)) × ℕ => randomCondStage c q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have hbase : Primrec (fun (_ : ℕ × (ℕ × ℕ)) => ([] : List BitString)) := Primrec.const []
  have hrec := Primrec.nat_rec hbase (randomCondStep_primrec c)
  have hrec2 : Primrec₂ (fun (p : ℕ × (ℕ × ℕ)) (t : ℕ) =>
      randomCondStage c p.1 p.2.1 p.2.2 t) :=
    hrec.of_eq (fun p t => randomCond_stage_eq c p t)
  exact hrec2.of_eq (fun p t => rfl)

private theorem randomCondStageList_primrec (c : Code) :
    Primrec (fun pzt : (BitString × BitString) × ℕ =>
      randomCondStageList c pzt.1.1 pzt.1.2 pzt.2) := by
  unfold randomCondStageList
  have hn : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      bitsToNat (decodeFirst pzt.1.2)) :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp (Primrec.snd.comp Primrec.fst))
  have hl : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      bitsToNat (decodeSecond pzt.1.2)) :=
    bitsToNat_primrec.comp (decodeSecond_primrec.comp (Primrec.snd.comp Primrec.fst))
  have hk : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      pzt.1.1.length - bitsToNat (decodeSecond pzt.1.2) - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_sub.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)) hl)
      (Primrec.const 1)
  have ht : Primrec (fun pzt : (BitString × BitString) × ℕ => pzt.2) := Primrec.snd
  have hnlkt : Primrec (fun pzt : (BitString × BitString) × ℕ =>
      ((bitsToNat (decodeFirst pzt.1.2), bitsToNat (decodeSecond pzt.1.2),
        pzt.1.1.length - bitsToNat (decodeSecond pzt.1.2) - 1), pzt.2)) :=
    Primrec.pair (Primrec.pair hn (Primrec.pair hl hk)) ht
  exact (randomCondStage_primrec c).comp hnlkt

private theorem randomCondCheck_primrec (c : Code) :
    Primrec (fun pzt : (BitString × BitString) × ℕ =>
      randomCondCheck c pzt.1.1 pzt.1.2 pzt.2) := by
  unfold randomCondCheck
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
      (randomCondStageList c pzt.1.1 pzt.1.2 pzt.2).length) :=
    Primrec.list_length.comp (randomCondStageList_primrec c)
  exact PrimrecPred.decide (Primrec.nat_lt.comp hm hlen)

private theorem randomCondGet_primrec (c : Code) :
    Primrec (fun pzt : (BitString × BitString) × ℕ =>
      randomCondGet c pzt.1.1 pzt.1.2 pzt.2) := by
  unfold randomCondGet
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
      randomCondStageList c pzt.1.1 pzt.1.2 pzt.2) :=
    randomCondStageList_primrec c
  exact (Primrec.list_getD []).comp hstage hm

private theorem randomCondDecoder_isDecompressor (c : Code) : isDecompressor
    (randomCondDecoder c) := by
  unfold randomCondDecoder isDecompressor
  have hcheck : Partrec₂ (fun (pz : BitString × BitString) (t : ℕ) =>
      Part.some (randomCondCheck c pz.1 pz.2 t)) :=
    (Partrec.comp Partrec.some (randomCondCheck_primrec c).to_comp.partrec).to₂
  have hrfind : Partrec (fun pz : BitString × BitString =>
      Nat.rfind (fun t => Part.some (randomCondCheck c pz.1 pz.2 t))) :=
    Partrec.rfind hcheck
  have hget : Partrec (fun pzt : (BitString × BitString) × ℕ =>
      Part.some (randomCondGet c pzt.1.1 pzt.1.2 pzt.2)) :=
    Partrec.comp Partrec.some (randomCondGet_primrec c).to_comp.partrec
  exact Partrec.bind hrfind hget.to₂

/-- **Exercise 41.** If the probability that `C(x | y) ≤ k` for a uniformly random
`n`-bit `y` is at least `2 ^ (-l)`, then `C(x | n, l) ≤ k + l + O(1)`. -/
theorem condK_le_of_probability_condK_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n k l : ℕ),
      (2 : ℝ) ^ n ≤ (2 : ℝ) ^ l *
          (((allStrings n).filter (fun y => decide (condK U x y ≤ (k : ℕ∞)))).length : ℝ) →
        condK U x (pairCode (Nat.bits n) (Nat.bits l)) ≤ ((k + l + c : ℕ) : ℕ∞) := by
  obtain ⟨c_code, hc_code⟩ : ∃ c_code : Code, IsCodeFor c_code U :=
    Nat.Partrec.Code.exists_code.mp hU.1
  let D := randomCondDecoder c_code
  have hD : isDecompressor D := randomCondDecoder_isDecompressor c_code
  obtain ⟨c_opt, hc_opt⟩ := hU.2 D hD
  refine ⟨c_opt + 1, ?_⟩
  intro x n k l h
  obtain ⟨T, hx_stage⟩ := randomCondStage_eventually_mem hc_code h
  let S := randomCondStage c_code n l k T
  let m := S.idxOf x
  have hm_lt : m < S.length := List.idxOf_lt_length_of_mem hx_stage
  have hS_len := randomCondStage_length_bound c_code n l k T
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
  have hp_findIdx : (allStrings p.length).findIdx (fun y => decide (y = p)) = m := by
    rw [findIdx_decide_eq, hp_len, hp_eq]
    exact List.Nodup.idxOf_getElem (allStrings_nodup (k + l + 1)) m hm_lt_pow
  have hp_idx : (allStrings p.length).findIdx (fun y => decide (y = p)) = m := hp_findIdx
  let z := pairCode (Nat.bits n) (Nat.bits l)
  have h_dec1 : decodeFirst z = Nat.bits n := decodeFirst_pairCode (Nat.bits n) (Nat.bits l)
  have h_dec2 : decodeSecond z = Nat.bits l := decodeSecond_pairCode (Nat.bits n) (Nat.bits l)
  have h_b1 : bitsToNat (decodeFirst z) = n := by rw [h_dec1, bitsToNat_bits]
  have h_b2 : bitsToNat (decodeSecond z) = l := by rw [h_dec2, bitsToNat_bits]
  have h_k : p.length - l - 1 = k := by rw [hp_len]; omega
  have h_prod : produces D p z x := by
    change x ∈ randomCondDecoder c_code (p, z)
    unfold randomCondDecoder randomCondGet randomCondCheck randomCondStageList
    dsimp only
    rw [h_b1, h_b2, h_k, hp_idx]
    have h_dom : (Nat.rfind (fun t => Part.some (decide
        (m < (randomCondStage c_code n l k t).length)))).Dom := by
      rw [Nat.rfind_dom]
      exact ⟨T, Part.mem_some_iff.mpr (decide_eq_true hm_lt).symm, fun _ => Part.some_dom _⟩
    obtain ⟨t0, ht0_mem⟩ := Part.dom_iff_mem.mp h_dom
    have ht0_le : t0 ≤ T := by
      by_contra h_lt
      have h_false := Nat.rfind_min ht0_mem (not_le.mp h_lt)
      have h_true : true ∈ Part.some (decide (m < (randomCondStage c_code n l k T).length)) :=
        Part.mem_some_iff.mpr (decide_eq_true hm_lt).symm
      have h_eq := Part.mem_unique h_false h_true
      cases h_eq
    have ht0_eq : Nat.rfind (fun t => Part.some (decide
        (m < (randomCondStage c_code n l k t).length))) = Part.some t0 :=
      Part.eq_some_iff.mpr ht0_mem
    rw [ht0_eq, Part.bind_some, Part.mem_some_iff]
    have ht0_spec := Nat.rfind_spec ht0_mem
    have ht0_lt : m < (randomCondStage c_code n l k t0).length := by simpa using ht0_spec
    have h_prefix := randomCondStage_mono c_code n l k ht0_le
    rw [← getD_eq_of_prefix_of_lt_length h_prefix m [] ht0_lt]
    rw [List.getD, List.getElem?_idxOf hx_stage]
    rfl
  have h_condD : condK D x z ≤ ((k + l + 1 : ℕ) : ℕ∞) := by
    have := condK_le_of_produces h_prod
    rw [hp_len] at this
    exact this
  have h_opt := hc_opt x z
  calc condK U x z ≤ condK D x z + (c_opt : ℕ∞) := h_opt
    _ ≤ ((k + l + 1 : ℕ) : ℕ∞) + (c_opt : ℕ∞) := by gcongr
    _ = ((k + l + (c_opt + 1) : ℕ) : ℕ∞) := by push_cast; ring

/-! ### Running a code on a program with a condition -/

/-- Output of program `p` in context `y` within step budget `T`. -/
def runOutC (c : Code) (T : ℕ) (p y : BitString) : Option BitString :=
  (Code.evaln T c (Encodable.encode ((p, y) : BitString × BitString))).bind
    (fun r => (Encodable.decode r : Option BitString))

end Kolmogorov
