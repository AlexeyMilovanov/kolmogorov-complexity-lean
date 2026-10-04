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
import KolmogorovMathlib.Complexity.RandomConditions.Enumeration
import KolmogorovMathlib.Complexity.RandomConditions.Bound.StageComputability

/-!
# Strings that are simple given many conditions

A string is *heavy* at a stage when at least a `2 ^ (-s)` fraction of the length-`n`
conditions already produce it by a short program.  `heavyStringsEnum` enumerates the heavy
strings in order of first appearance, built from `hitAt` (some short program produces `x` from
`y` within the step budget), `countY` (how many conditions do), `candStage` and `isHeavyAt`.

`runOutC_sound`, `runOutC_complete` and `runOutC_mono` relate the bounded-step evaluation to
the machine it codes, and the `_primrec` lemmas make the whole enumeration primitive
recursive.  Counting its entries bounds the complexity of a heavy string, which is how a
random condition is shown not to help.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-- An output produced within the step budget is genuinely produced by the machine the code
computes: `runOutC c T p y = some w` implies `produces U p y w`. -/
lemma runOutC_sound {c : Code} {U : Map} (hc : IsCodeFor c U) {T : ℕ} {p y w : BitString}
    (h : runOutC c T p y = some w) : produces U p y w := by
  unfold runOutC at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨a, ha₁, ha₂⟩ := h
  have hev := Nat.Partrec.Code.evaln_sound ha₁
  unfold IsCodeFor at hc
  rw [hc] at hev
  simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.mem_map_iff] at hev
  obtain ⟨out, hout, henc⟩ := hev
  have : out = w := by
    have := congrArg (Encodable.decode (α := BitString)) henc
    rw [Encodable.encodek] at this
    rw [ha₂] at this
    exact (Option.some_inj.mp this)
  rwa [this] at hout

/-- Every output of the machine appears within some step budget: if `produces U p y out`, then
`runOutC c T p y = some out` for some `T`. -/
lemma runOutC_complete {c : Code} {U : Map} (hc : IsCodeFor c U) {p y out : BitString}
    (h : produces U p y out) : ∃ T, runOutC c T p y = some out := by
  have h_evaln : Encodable.encode out ∈ c.eval
      (Encodable.encode ((p, y) : BitString × BitString)) := by
    unfold IsCodeFor at hc
    rw [hc]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.mem_map_iff]
    exact ⟨out, h, rfl⟩
  obtain ⟨T, hT⟩ := Code.evaln_complete.mp h_evaln
  refine ⟨T, ?_⟩
  unfold runOutC
  rw [show Code.evaln T c (Encodable.encode ((p, y) : BitString × BitString))
      = some (Encodable.encode out) from hT]
  simp [Encodable.encodek]

/-- An output found within a step budget is still found with any larger budget. -/
lemma runOutC_mono (c : Code) {T T' : ℕ} (h : T ≤ T') {p y w : BitString}
    (hw : runOutC c T p y = some w) : runOutC c T' p y = some w := by
  unfold runOutC at hw ⊢
  rw [Option.bind_eq_some_iff] at hw
  obtain ⟨a, ha₁, ha₂⟩ := hw
  rw [show Code.evaln T' c (Encodable.encode ((p, y) : BitString × BitString)) = some a from
    Nat.Partrec.Code.evaln_mono h ha₁]
  exact ha₂

/-- Running a fixed code for a bounded number of steps is primitive recursive in the budget,
the program and the condition. -/
lemma runOutC_primrec (c : Code) :
    Primrec (fun q : (ℕ × BitString) × BitString => runOutC c q.1.1 q.1.2 q.2) := by
  unfold runOutC
  apply Primrec.option_bind
  · exact (evaln_primrec c).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.encode.comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  · exact Primrec.decode.comp Primrec.snd

/-! ### Stage-wise enumeration of the strings with many short conditional programs -/

/-- Some program of length at most `t` produces `x` from `y` within `T` steps. -/
def hitAt (c : Code) (t T : ℕ) (x y : BitString) : Bool :=
  decide (0 < (boundedPrograms t).countP (fun p => decide (runOutC c T p y = some x)))

/-- `hitAt c t T x y` holds exactly when some program of length at most `t` produces `x` from
the condition `y` within `T` steps. -/
lemma hitAt_iff (c : Code) (t T : ℕ) (x y : BitString) :
    hitAt c t T x y = true ↔ ∃ p ∈ boundedPrograms t, runOutC c T p y = some x := by
  unfold hitAt
  rw [decide_eq_true_eq, List.countP_pos_iff]
  constructor
  · rintro ⟨p, hp, hrun⟩
    exact ⟨p, hp, of_decide_eq_true hrun⟩
  · rintro ⟨p, hp, hrun⟩
    exact ⟨p, hp, decide_eq_true hrun⟩

/-- The number of conditions `y` of length `n` from which `x` is produced within `T`
steps by a program of length at most `t`. -/
def countY (c : Code) (n t T : ℕ) (x : BitString) : ℕ :=
  (allStrings n).countP (fun y => hitAt c t T x y)

/-- All strings produced within `T` steps from a length-`n` condition by a program of
length at most `t`, without repetitions. -/
def candStage (c : Code) (n t T : ℕ) : List BitString :=
  ((allStrings n).flatMap
    (fun y => (boundedPrograms t).filterMap (fun p => runOutC c T p y))).dedup

/-- `x` already has, at stage `T`, at least `2 ^ n / 2 ^ s` conditions producing it. -/
def isHeavyAt (c : Code) (n t s T : ℕ) (x : BitString) : Bool :=
  decide (2 ^ n ≤ countY c n t T x * 2 ^ s)

/-- The heavy strings, enumerated in order of first appearance. -/
def heavyStringsEnum (c : Code) (n t s : ℕ) : ℕ → List BitString
  | 0 => []
  | T + 1 => heavyStringsEnum c n t s T ++
      (candStage c n t (T + 1)).filter
        (fun x => isHeavyAt c n t s (T + 1) x && !(decide (x ∈ heavyStringsEnum c n t s T)))

/-- A hit found within `T` steps is still a hit within any larger step budget. -/
lemma hitAt_mono (c : Code) (t : ℕ) {T T' : ℕ} (h : T ≤ T') (x y : BitString) :
    hitAt c t T x y = true → hitAt c t T' x y = true := by
  rw [hitAt_iff, hitAt_iff]
  rintro ⟨p, hp, hrun⟩
  exact ⟨p, hp, runOutC_mono c h hrun⟩

/-- The number of conditions producing `x` within the step budget is monotone in the budget. -/
lemma countY_mono (c : Code) (n t : ℕ) {T T' : ℕ} (h : T ≤ T') (x : BitString) :
    countY c n t T x ≤ countY c n t T' x :=
  List.countP_mono_left (fun y _ hy => hitAt_mono c t h x y hy)

/-- A string that is heavy at stage `T` stays heavy at every later stage. -/
lemma isHeavyAt_mono (c : Code) (n t s : ℕ) {T T' : ℕ} (h : T ≤ T') (x : BitString) :
    isHeavyAt c n t s T x = true → isHeavyAt c n t s T' x = true := by
  unfold isHeavyAt
  simp only [decide_eq_true_eq]
  intro hx
  exact le_trans hx (Nat.mul_le_mul_right _ (countY_mono c n t h x))

/-- A string belongs to the stage-`T` candidate list exactly when some program of length at
most `t` produces it within `T` steps from some condition of length `n`. -/
lemma mem_candStage_iff (c : Code) (n t T : ℕ) (x : BitString) :
    x ∈ candStage c n t T ↔
      ∃ y ∈ allStrings n, ∃ p ∈ boundedPrograms t, runOutC c T p y = some x := by
  unfold candStage
  rw [List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨y, hy, hx⟩
    rw [List.mem_filterMap] at hx
    obtain ⟨p, hp, hrun⟩ := hx
    exact ⟨y, hy, p, hp, hrun⟩
  · rintro ⟨y, hy, p, hp, hrun⟩
    exact ⟨y, hy, List.mem_filterMap.mpr ⟨p, hp, hrun⟩⟩

/-- The stage-`T` candidate list has no repetitions. -/
lemma candStage_nodup (c : Code) (n t T : ℕ) : (candStage c n t T).Nodup :=
  List.nodup_dedup _

/-- The enumeration of heavy strings at stage `T` is a prefix of the one at stage `T + 1`. -/
lemma heavyEnum_prefix_succ (c : Code) (n t s T : ℕ) :
    heavyStringsEnum c n t s T <+: heavyStringsEnum c n t s (T + 1) := by
  rw [show heavyStringsEnum c n t s (T + 1) = heavyStringsEnum c n t s T ++ _ from rfl]
  exact List.prefix_append _ _

/-- The enumeration of heavy strings at stage `T` is a prefix of the one at any later stage. -/
lemma heavyEnum_prefix_of_le (c : Code) (n t s : ℕ) {T T' : ℕ} (h : T ≤ T') :
    heavyStringsEnum c n t s T <+: heavyStringsEnum c n t s T' := by
  induction T' with
  | zero => rw [Nat.le_zero.mp h]
  | succ T' ih =>
    rcases Nat.lt_or_ge T (T' + 1) with hlt | hge
    · exact (ih (by omega)).trans (heavyEnum_prefix_succ c n t s T')
    · rw [show T = T' + 1 by omega]

/-- The enumeration of heavy strings has no repetitions. -/
lemma heavyEnum_nodup (c : Code) (n t s T : ℕ) : (heavyStringsEnum c n t s T).Nodup := by
  induction T with
  | zero => exact List.nodup_nil
  | succ T ih =>
    rw [show heavyStringsEnum c n t s (T + 1) = heavyStringsEnum c n t s T ++
      (candStage c n t (T + 1)).filter
        (fun x => isHeavyAt c n t s (T + 1) x && !(decide (x ∈ heavyStringsEnum c n t s T)))
        from rfl]
    refine List.Nodup.append ih ((candStage_nodup c n t (T + 1)).filter _) ?_
    intro a ha hb
    rw [List.mem_filter] at hb
    have := hb.2
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this.2 ha

/-- Every string listed in the stage-`T` enumeration is heavy at stage `T`. -/
lemma mem_heavyEnum_isHeavyAt (c : Code) (n t s T : ℕ) {x : BitString}
    (hx : x ∈ heavyStringsEnum c n t s T) : isHeavyAt c n t s T x = true := by
  induction T with
  | zero => cases hx
  | succ T ih =>
    rw [show heavyStringsEnum c n t s (T + 1) = heavyStringsEnum c n t s T ++
      (candStage c n t (T + 1)).filter
        (fun x => isHeavyAt c n t s (T + 1) x && !(decide (x ∈ heavyStringsEnum c n t s T)))
        from rfl,
      List.mem_append] at hx
    rcases hx with hx | hx
    · exact isHeavyAt_mono c n t s (Nat.le_succ T) x (ih hx)
    · rw [List.mem_filter] at hx
      have := hx.2
      simp only [Bool.and_eq_true] at this
      exact this.1

/-- A candidate at stage `T` that is heavy at stage `T` occurs in the stage-`T` enumeration. -/
lemma mem_heavyEnum_of_cand (c : Code) (n t s T : ℕ) {x : BitString}
    (hcand : x ∈ candStage c n t T) (hheavy : isHeavyAt c n t s T x = true) :
    x ∈ heavyStringsEnum c n t s T := by
  cases T with
  | zero =>
    exfalso
    rw [mem_candStage_iff] at hcand
    obtain ⟨y, -, p, -, hrun⟩ := hcand
    unfold runOutC at hrun
    have he : Code.evaln 0 c (Encodable.encode ((p, y) : BitString × BitString)) = none := by
      rw [Option.eq_none_iff_forall_not_mem]
      intro z hz
      exact absurd (Nat.Partrec.Code.evaln_bound hz) (by omega)
    rw [he] at hrun
    simp at hrun
  | succ T =>
    by_cases hprev : x ∈ heavyStringsEnum c n t s T
    · exact (heavyEnum_prefix_succ c n t s T).subset hprev
    · rw [show heavyStringsEnum c n t s (T + 1) = heavyStringsEnum c n t s T ++
        (candStage c n t (T + 1)).filter
          (fun x => isHeavyAt c n t s (T + 1) x && !(decide (x ∈ heavyStringsEnum c n t s T)))
          from rfl,
        List.mem_append]
      refine Or.inr (List.mem_filter.mpr ⟨hcand, ?_⟩)
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨hheavy, hprev⟩

/-! ### The counting bound on the enumeration -/

/-- The sum of a pointwise sum of two functions over a list splits as the sum of the two sums. -/
lemma list_sum_map_add {α : Type} (M : List α) (g h : α → ℕ) :
    (M.map (fun b => g b + h b)).sum = (M.map g).sum + (M.map h).sum := by
  induction M with
  | nil => rfl
  | cons b M ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Summing the indicator of a decidable predicate over a list counts its satisfying elements. -/
lemma sum_map_ite_one_zero_eq_countP {β : Type} (M : List β) (q : β → Bool) :
    (M.map (fun b => if q b = true then 1 else 0)).sum = M.countP q := by
  induction M with
  | nil => rfl
  | cons b M ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases hb : q b
    · simp [hb]
      omega
    · simp [hb]

/-- Double counting for a boolean relation: summing the row counts over `L` equals summing the
column counts over `M`. -/
lemma sum_countP_swap {α β : Type} (L : List α) (M : List β) (f : α → β → Bool) :
    (L.map (fun a => M.countP (f a))).sum = (M.map (fun b => L.countP (fun a => f a b))).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih]
    have hfun : (fun b => (a :: L).countP (fun a' => f a' b))
        = (fun b => L.countP (fun a' => f a' b) + if f a b = true then 1 else 0) := by
      funext b
      rw [List.countP_cons]
    rw [hfun, list_sum_map_add, sum_map_ite_one_zero_eq_countP M (f a)]
    omega

/-- For a duplicate-free list of strings, at most one string per program of length at most `t`
is hit from a fixed condition, so the count is bounded by the number of such programs. -/
lemma countP_hit_le (c : Code) (t T : ℕ) (y : BitString) (L : List BitString) (hL : L.Nodup) :
    L.countP (fun x => hitAt c t T x y) ≤ (boundedPrograms t).length := by
  classical
  set g : BitString → BitString := fun x =>
    ((boundedPrograms t).find? (fun p => decide (runOutC c T p y = some x))).getD [] with hg
  set L' := L.filter (fun x => hitAt c t T x y) with hL'
  have hcount : L.countP (fun x => hitAt c t T x y) = L'.length := by
    rw [hL', List.countP_eq_length_filter]
  have hspec : ∀ x ∈ L', g x ∈ boundedPrograms t ∧ runOutC c T (g x) y = some x := by
    intro x hx
    rw [hL', List.mem_filter] at hx
    have hhit := (hitAt_iff c t T x y).mp hx.2
    obtain ⟨p0, hp0mem, hp0⟩ := hhit
    have hne : (boundedPrograms t).find? (fun p => decide (runOutC c T p y = some x)) ≠ none := by
      intro hnone
      rw [List.find?_eq_none] at hnone
      exact absurd (hnone p0 hp0mem) (by simp [hp0])
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hne
    have hmem : q ∈ boundedPrograms t := List.mem_of_find?_eq_some hq
    have hpred : runOutC c T q y = some x := by
      have := List.find?_some hq
      simpa using this
    rw [hg]
    simp only [hq, Option.getD_some]
    exact ⟨hmem, hpred⟩
  have hinj : ∀ x ∈ L', ∀ x' ∈ L', g x = g x' → x = x' := by
    intro x hx x' hx' hgg
    have h1 := (hspec x hx).2
    have h2 := (hspec x' hx').2
    rw [hgg, h2] at h1
    exact (Option.some_inj.mp h1).symm
  have hnodup : (L'.map g).Nodup := List.Nodup.map_on hinj (hL.filter _)
  have hsub : L'.map g ⊆ boundedPrograms t := by
    intro z hz
    rw [List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (hspec x hx).1
  have hlen := (List.subperm_of_subset hnodup hsub).length_le
  rw [List.length_map] at hlen
  omega

/-- The sum of a constant over a list is the length of the list times the constant. -/
lemma sum_map_const_nat {α : Type} (L : List α) (k : ℕ) :
    (L.map (fun _ => k)).sum = L.length * k := by
  induction L with
  | nil => simp
  | cons a M ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

/-- A constant right factor comes out of a sum over a list. -/
lemma sum_map_mul_right {α : Type} (L : List α) (g : α → ℕ) (k : ℕ) :
    (L.map (fun x => g x * k)).sum = (L.map g).sum * k := by
  induction L with
  | nil => simp
  | cons a M ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    ring

/-- At most `2 ^ (t + s + 1)` strings are heavy: each needs `2 ^ n / 2 ^ s` of the `2 ^ n`
conditions, and each condition serves at most `2 ^ (t + 1)` programs. -/
lemma heavyEnum_length_le (c : Code) (n t s T : ℕ) :
    (heavyStringsEnum c n t s T).length ≤ 2 ^ (t + s + 1) := by
  have hheavy : ∀ x ∈ heavyStringsEnum c n t s T, 2 ^ n ≤ countY c n t T x * 2 ^ s := by
    intro x hx
    have hh := mem_heavyEnum_isHeavyAt c n t s T hx
    unfold isHeavyAt at hh
    exact of_decide_eq_true hh
  have hsum1 : (heavyStringsEnum c n t s T).length * 2 ^ n
      ≤ ((heavyStringsEnum c n t s T).map (fun x => countY c n t T x * 2 ^ s)).sum := by
    rw [← sum_map_const_nat (heavyStringsEnum c n t s T) (2 ^ n)]
    exact List.sum_le_sum hheavy
  have hsum2 : ((heavyStringsEnum c n t s T).map (fun x => countY c n t T x)).sum
      ≤ 2 ^ n * (boundedPrograms t).length := by
    have hswap : ((heavyStringsEnum c n t s T).map (fun x => countY c n t T x)).sum
        = ((allStrings n).map
            (fun y => (heavyStringsEnum c n t s T).countP (fun x => hitAt c t T x y))).sum := by
      unfold countY
      exact sum_countP_swap (heavyStringsEnum c n t s T) (allStrings n) (fun x y => hitAt c t T x y)
    have hle : ((allStrings n).map
          (fun y => (heavyStringsEnum c n t s T).countP (fun x => hitAt c t T x y))).sum
        ≤ ((allStrings n).map (fun _ : BitString => (boundedPrograms t).length)).sum :=
      List.sum_le_sum
        (fun y _ => countP_hit_le c t T y (heavyStringsEnum c n t s T) (heavyEnum_nodup c n t s T))
    rw [hswap]
    refine hle.trans ?_
    rw [sum_map_const_nat, length_allStrings]
  have hbp : (boundedPrograms t).length < 2 ^ (t + 1) := length_boundedPrograms_lt t
  have hkey : (heavyStringsEnum c n t s T).length * 2 ^ n ≤ (2 ^ (t + 1) * 2 ^ s) * 2 ^ n := by
    refine hsum1.trans ?_
    rw [sum_map_mul_right]
    calc ((heavyStringsEnum c n t s T).map (fun x => countY c n t T x)).sum * 2 ^ s
        ≤ (2 ^ n * (boundedPrograms t).length) * 2 ^ s := Nat.mul_le_mul_right _ hsum2
      _ ≤ (2 ^ n * 2 ^ (t + 1)) * 2 ^ s :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hbp.le)
      _ = (2 ^ (t + 1) * 2 ^ s) * 2 ^ n := by ring
  have hfin : (heavyStringsEnum c n t s T).length ≤ 2 ^ (t + 1) * 2 ^ s :=
    Nat.le_of_mul_le_mul_right hkey (Nat.two_pow_pos n)
  calc (heavyStringsEnum c n t s T).length ≤ 2 ^ (t + 1) * 2 ^ s := hfin
    _ = 2 ^ (t + s + 1) := by rw [← pow_add]; ring_nf

/-! ### Computability of the stage enumeration -/

/-- A primitive recursive predicate has primitive recursive boolean decision function. -/
lemma primrec_decide_of_primrecPred {α : Type} [Primcodable α] {P : α → Prop}
    [DecidablePred P] (h : PrimrecPred P) : Primrec (fun a => decide (P a)) := by
  obtain ⟨_, h⟩ := h
  exact Primrec.of_eq h (fun a => by rw [decide_eq_decide])

/-- A predicate whose boolean decision function is primitive recursive is primitive recursive. -/
lemma primrecPred_of_primrec_decide {α : Type} [Primcodable α] {P : α → Prop}
    [inst : DecidablePred P] (h : Primrec (fun a => decide (P a))) : PrimrecPred P :=
  ⟨inst, h⟩

/-- Duplicate removal on a list of bit strings, written as a right fold, the form in which it
is transported to a primitive recursive function. -/
lemma dedup_eq_foldr (l : List BitString) :
    l.dedup = l.foldr (fun a r => if a ∈ r then r else a :: r) [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ← ih]
    by_cases h : a ∈ l.dedup
    · rw [ite_eq_left h, List.dedup_cons_of_mem (List.mem_dedup.mp h)]
    · rw [ite_eq_right h, List.dedup_cons_of_notMem (fun hh => h (List.mem_dedup.mpr hh))]

/-- The hit predicate of a fixed code is primitive recursive in the length bound, the step
budget, the string and the condition. -/
lemma hitAt_primrec (c : Code) :
    Primrec (fun q : (ℕ × ℕ) × BitString × BitString => hitAt c q.1.1 q.1.2 q.2.1 q.2.2) := by
  unfold hitAt
  have hrun : Primrec₂ (fun (q : (ℕ × ℕ) × BitString × BitString) (p : BitString) =>
      decide (runOutC c q.1.2 p q.2.2 = some q.2.1)) :=
    primrec_decide_of_primrecPred
      (Primrec.eq.comp
        ((runOutC_primrec c).comp (Primrec.pair
          (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
        (Primrec.option_some.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  have hcount := list_countP_primrec
    (primrec_boundedPrograms.comp (Primrec.fst.comp Primrec.fst)) hrun
  exact primrec_decide_of_primrecPred
    (Primrec.nat_lt.comp (Primrec.const 0) hcount)

/-- The number of conditions producing a string within the given bounds is primitive recursive. -/
lemma countY_primrec (c : Code) :
    Primrec (fun q : (ℕ × ℕ × ℕ) × BitString => countY c q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  unfold countY
  refine list_countP_primrec
    (allStrings_primrec.comp (Primrec.fst.comp Primrec.fst)) ?_
  exact (hitAt_primrec c).comp (Primrec.pair
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))

/-- The stage-`T` candidate list is a primitive recursive function of the parameters. -/
lemma candStage_primrec (c : Code) :
    Primrec (fun q : (ℕ × ℕ) × ℕ => candStage c q.1.1 q.1.2 q.2) := by
  unfold candStage
  refine dedup_primrec.comp ?_
  refine Primrec.list_flatMap
    (allStrings_primrec.comp (Primrec.fst.comp Primrec.fst)) ?_
  refine Primrec.listFilterMap
    (primrec_boundedPrograms.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) ?_
  exact (runOutC_primrec c).comp (Primrec.pair
    (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
    (Primrec.snd.comp Primrec.fst))

end Kolmogorov
