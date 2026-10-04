/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic

/-!
# From an effective cover to the prediction sequence (SUV Section 5.7.3, pp. 161–162)

This module builds the object behind the *reverse* direction of SUV Theorem 104, the
forward direction of Theorem 105 and the forward direction of Theorem 106: given an
effective cover of a non-random real `α` by rational intervals of total length at most
`ε`, it produces the computable sequence `hᵢ ≥ 0` of the prediction game, with
`∑ᵢ hᵢ ≤ ε` and `α ≤ aᵢ + hᵢ` for one `i`.

The construction is the source's ("we wait until the current approximation `aᵢ` gets
into some of the covering intervals, and we then predict that it will never go out of
this interval", p. 162), with the bookkeeping made explicit so that each covering
interval is charged **exactly once**: the interval of index `k` is charged at the single
step `i = k + j`, where `j` is the first index with `a j` inside that interval.  The
step `k + j` is computable from `(k, j)`, is at least `j` and at least `k`, and
determines the pair; that is all the argument needs.

Everything here is proved; the module renders no statement of the source.
-/

namespace Kolmogorov

open ENNReal

/-! ### The first index at which a `Bool` test fires -/

/-- `optFirst E p i` is the least `j ≤ i` with `E p j = true`, and `none` if there is
no such `j`.  Written in the shape `Computable.nat_rec` accepts, with `p` as the
recursion parameter. -/
def optFirst {α : Type} (E : α → ℕ → Bool) (p : α) : ℕ → Option ℕ
  | 0 => cond (E p 0) (some 0) none
  | i + 1 =>
      cond (optFirst E p i).isSome (optFirst E p i) (cond (E p (i + 1)) (some (i + 1)) none)

variable {α : Type}

/-- The complete description of `optFirst`: either the test never fired up to `i`, or
`optFirst` returns the least index at which it fired. -/
theorem optFirst_cases (E : α → ℕ → Bool) (p : α) (i : ℕ) :
    (optFirst E p i = none ∧ ∀ j, j ≤ i → E p j = false) ∨
      (∃ j, optFirst E p i = some j ∧ j ≤ i ∧ E p j = true ∧
        ∀ l, l < j → E p l = false) := by
  induction i with
  | zero =>
      cases h : E p 0 with
      | true =>
          refine Or.inr ⟨0, ?_, le_rfl, h, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
          simp only [optFirst, h, Bool.cond_true]
      | false =>
          refine Or.inl ⟨?_, fun j hj => ?_⟩
          · simp only [optFirst, h, Bool.cond_false]
          · rw [Nat.le_zero.mp hj]; exact h
  | succ i ih =>
      rcases ih with ⟨hnone, hall⟩ | ⟨j, hj, hjle, hjtrue, hjmin⟩
      · have hsome : (optFirst E p i).isSome = false := by rw [hnone]; rfl
        cases h : E p (i + 1) with
        | true =>
            refine Or.inr ⟨i + 1, ?_, le_rfl, h, fun l hl => hall l (Nat.lt_succ_iff.mp hl)⟩
            simp only [optFirst, hsome, Bool.cond_false, h, Bool.cond_true]
        | false =>
            refine Or.inl ⟨?_, fun m hm => ?_⟩
            · simp only [optFirst, hsome, Bool.cond_false, h, Bool.cond_false]
            · rcases Nat.eq_or_lt_of_le hm with heq | hlt
              · rw [heq]; exact h
              · exact hall m (Nat.lt_succ_iff.mp hlt)
      · refine Or.inr ⟨j, ?_, Nat.le_succ_of_le hjle, hjtrue, hjmin⟩
        simp only [optFirst, hj, Option.isSome_some, Bool.cond_true]

/-- The bounded first-hit search fails exactly when the test is false up to the bound. -/
theorem optFirst_eq_none_iff (E : α → ℕ → Bool) (p : α) (i : ℕ) :
    optFirst E p i = none ↔ ∀ j, j ≤ i → E p j = false := by
  rcases optFirst_cases E p i with ⟨h1, h2⟩ | ⟨j, hj, hjle, hjtrue, _⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · refine ⟨fun hc => absurd (hj.symm.trans hc) (by simp), fun hall => ?_⟩
    exact absurd (hall j hjle) (by rw [hjtrue]; simp)

/-- The index found by the bounded search is below the bound, fires the test, and is the least
such index. -/
theorem optFirst_spec {E : α → ℕ → Bool} {p : α} {i j : ℕ} (h : optFirst E p i = some j) :
    j ≤ i ∧ E p j = true ∧ ∀ l, l < j → E p l = false := by
  rcases optFirst_cases E p i with ⟨h1, _⟩ | ⟨j', hj', hjle, hjtrue, hjmin⟩
  · exact absurd (h.symm.trans h1) (by simp)
  · have hjj : j' = j := Option.some.inj (hj'.symm.trans h)
    subst hjj
    exact ⟨hjle, hjtrue, hjmin⟩

/-- Raising the bound does not change a successful bounded search. -/
theorem optFirst_stable {E : α → ℕ → Bool} {p : α} {i j : ℕ} (h : optFirst E p i = some j) :
    ∀ i', i ≤ i' → optFirst E p i' = some j := by
  intro i' hi'
  induction i', hi' using Nat.le_induction with
  | base => exact h
  | succ n _ ih => simp only [optFirst, ih, Option.isSome_some, Bool.cond_true]

/-- If the test has fired at some `j ≤ i`, then `optFirst` has an answer at `i`. -/
theorem optFirst_isSome_of {E : α → ℕ → Bool} {p : α} {i j : ℕ} (hj : j ≤ i)
    (h : E p j = true) : ∃ j', optFirst E p i = some j' := by
  rcases Option.eq_none_or_eq_some (optFirst E p i) with hn | ⟨j', hj'⟩
  · exact absurd ((optFirst_eq_none_iff E p i).mp hn j hj) (by rw [h]; simp)
  · exact ⟨j', hj'⟩

/-- The value of `optFirst` at its own firing index. -/
theorem optFirst_self {E : α → ℕ → Bool} {p : α} {j : ℕ} (h : E p j = true)
    (hmin : ∀ l, l < j → E p l = false) : optFirst E p j = some j := by
  obtain ⟨j', hj'⟩ := optFirst_isSome_of (le_refl j) h
  obtain ⟨hle, htrue, _⟩ := optFirst_spec hj'
  rcases Nat.lt_or_ge j' j with hlt | hge
  · exact absurd (hmin j' hlt) (by rw [htrue]; simp)
  · rwa [le_antisymm hle hge] at hj'

/-- The bounded first-hit search of a computable test is computable. -/
theorem computable_optFirst [Primcodable α] {E : α → ℕ → Bool} (hE : Computable₂ E) :
    Computable (fun q : α × ℕ => optFirst E q.1 q.2) := by
  have hbase : Computable (fun q : α × ℕ => cond (E q.1 0) (some 0 : Option ℕ) none) :=
    Computable.cond (hE.comp Computable.fst (Computable.const 0))
      (Computable.const (some 0)) (Computable.const none)
  have hstep : Computable₂ (fun (q : α × ℕ) (r : ℕ × Option ℕ) =>
      cond r.2.isSome r.2 (cond (E q.1 (r.1 + 1)) (some (r.1 + 1)) none)) := by
    have hIH : Computable (fun s : (α × ℕ) × ℕ × Option ℕ => s.2.2) :=
      Computable.snd.comp Computable.snd
    have hy : Computable (fun s : (α × ℕ) × ℕ × Option ℕ => s.2.1 + 1) :=
      Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)
    have hisSome : Computable (fun s : (α × ℕ) × ℕ × Option ℕ => s.2.2.isSome) :=
      Primrec.option_isSome.to_comp.comp hIH
    have hEy : Computable (fun s : (α × ℕ) × ℕ × Option ℕ => E s.1.1 (s.2.1 + 1)) :=
      hE.comp (Computable.fst.comp Computable.fst) hy
    exact Computable.cond hisSome hIH
      (Computable.cond hEy (Computable.option_some.comp hy) (Computable.const none))
  have hrec := Computable.nat_rec (σ := Option ℕ) Computable.snd hbase hstep
  refine hrec.of_eq (fun q => ?_)
  obtain ⟨p, n⟩ := q
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => Option ℕ)
      (cond (E p 0) (some 0) none)
      (fun y IH => cond IH.isSome IH (cond (E p (y + 1)) (some (y + 1)) none)) m)
      = optFirst E p m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        simp only [optFirst]
        exact congrArg
          (fun X : Option ℕ => cond X.isSome X (cond (E p (m + 1)) (some (m + 1)) none)) ih
  exact key n

/-- Reindexed form of `computable_optFirst`.  Stated in the *generic* setting, where
the test `E` is a variable, so that the definitional check never has to unfold the
concrete test (and, with it, the `Decidable` instance of `ℚ`). -/
theorem computable_optFirst_comp {β : Type} [Primcodable α] [Primcodable β]
    {E : α → ℕ → Bool} (hE : Computable₂ E) {u : β → α} {v : β → ℕ}
    (hu : Computable u) (hv : Computable v) :
    Computable (fun b : β => optFirst E (u b) (v b)) :=
  (computable_optFirst hE).comp (Computable.pair hu hv)

/-! ### Parameterised partial sums -/

/-- `∑_{k < n} u p k`, in the shape `Computable.nat_rec` accepts, with `p` as the
recursion parameter (so that the *diagonal* use, where the bound depends on `p`, is
computable). -/
def ratRangeSumP (u : α → ℕ → ℚ) (p : α) : ℕ → ℚ
  | 0 => 0
  | n + 1 => ratRangeSumP u p n + u p n

/-- The parameterised partial sum agrees with the sum over `Finset.range`. -/
theorem ratRangeSumP_eq (u : α → ℕ → ℚ) (p : α) (n : ℕ) :
    ratRangeSumP u p n = ∑ k ∈ Finset.range n, u p k := by
  induction n with
  | zero => simp [ratRangeSumP]
  | succ n ih => rw [ratRangeSumP, ih, Finset.sum_range_succ]

/-- Parameterised partial sums of a computable family are computable. -/
theorem computable_ratRangeSumP [Primcodable α] {u : α → ℕ → ℚ} (hu : Computable₂ u) :
    Computable (fun q : α × ℕ => ratRangeSumP u q.1 q.2) := by
  have hstep : Computable₂ (fun (q : α × ℕ) (r : ℕ × ℚ) => r.2 + u q.1 r.1) := by
    have h1 : Computable (fun s : (α × ℕ) × ℕ × ℚ => s.2.2) :=
      Computable.snd.comp Computable.snd
    have h2 : Computable (fun s : (α × ℕ) × ℕ × ℚ => u s.1.1 s.2.1) :=
      hu.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
    exact Computable₂.comp computable₂_ratAdd h1 h2
  have hrec := Computable.nat_rec (σ := ℚ) Computable.snd (Computable.const 0) hstep
  refine hrec.of_eq (fun q => ?_)
  obtain ⟨p, n⟩ := q
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) 0
      (fun y IH => IH + u p y) m) = ratRangeSumP u p m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        simp only [ratRangeSumP]
        exact congrArg (fun x : ℚ => x + u p m) ih
  exact key n

/-! ### Two small transfer lemmas -/

/-- A tsum over `ℕ` of a family supported on `[n, ∞)` is the tsum of its shift. -/
theorem tsum_shift_nat {T ψ : ℕ → ℝ≥0∞} (n : ℕ) (h1 : ∀ i, i < n → T i = 0)
    (h2 : ∀ m, T (m + n) = ψ m) : ∑' i, T i = ∑' m, ψ m := by
  have hinj : Function.Injective (fun m : ℕ => m + n) := add_left_injective n
  have hsupp : Function.support T ⊆ Set.range (fun m : ℕ => m + n) := by
    intro i hi
    rcases Nat.lt_or_ge i n with hlt | hge
    · exact absurd (h1 i hlt) hi
    · exact ⟨i - n, Nat.sub_add_cancel hge⟩
  rw [← hinj.tsum_eq hsupp]
  exact tsum_congr h2

/-- A strictly increasing rational sequence converging to `α` stays strictly below it. -/
theorem rat_lt_of_strictMono_tendsto {a : ℕ → ℚ} {α : ℝ} (hmono : StrictMono a)
    (hlim : Filter.Tendsto (fun n => ((a n : ℚ) : ℝ)) Filter.atTop (nhds α)) (i : ℕ) :
    ((a i : ℚ) : ℝ) < α := by
  have h1 : ((a i : ℚ) : ℝ) < ((a (i + 1) : ℚ) : ℝ) := by
    exact_mod_cast hmono (Nat.lt_succ_self i)
  have h2 : ((a (i + 1) : ℚ) : ℝ) ≤ α :=
    rat_le_of_monotone_tendsto hmono.monotone hlim (i + 1)
  linarith

/-! ### The prediction sequence read off a cover -/

section Cover

variable (cover : ℚ → ℕ → Option (ℚ × ℚ)) (a : ℕ → ℚ)

/-- The interval of index `p.2` of the cover for budget `p.1`, with `none` read as the
empty interval `(0, 0)`. -/
def covPair (p : ℚ × ℕ) : ℚ × ℚ := (cover p.1 p.2).getD (0, 0)

/-- `a j` lies strictly inside the interval `covPair cover p`. -/
def coverEnter (p : ℚ × ℕ) (j : ℕ) : Bool :=
  ratLtPair ((covPair cover p).1, a j) && ratLtPair (a j, (covPair cover p).2)

/-- The first index `j ≤ i` with `a j` strictly inside the interval `p = (ε, k)`. -/
def coverFirst (p : ℚ × ℕ) (i : ℕ) : Option ℕ := optFirst (coverEnter cover a) p i

/-- The charge that the covering interval `p = (ε, k)` puts on step `i`.  It is nonzero
only at the single step `i = k + j`, where `j` is the first index with `a j` inside the
interval, and it then equals the distance from `a j` to the right endpoint. -/
def coverCharge (p : ℚ × ℕ) (i : ℕ) : ℚ :=
  Option.casesOn (motive := fun _ => ℚ) (coverFirst cover a p i) 0
    (fun j => cond (p.2 + j == i) ((covPair cover p).2 - a j) 0)

/-- The prediction sequence for budget `ε`: the total charge of step `i`. -/
def coverH (ε : ℚ) (i : ℕ) : ℚ := ∑ k ∈ Finset.range (i + 1), coverCharge cover a (ε, k) i

/-- The search for the first step entering a covering interval fails exactly when no step up to
the bound enters it. -/
theorem coverFirst_eq_none_iff (p : ℚ × ℕ) (i : ℕ) :
    coverFirst cover a p i = none ↔ ∀ j, j ≤ i → coverEnter cover a p j = false :=
  optFirst_eq_none_iff _ _ _

/-- The step found is below the bound, enters the interval, and is the least such step. -/
theorem coverFirst_spec {p : ℚ × ℕ} {i j : ℕ} (h : coverFirst cover a p i = some j) :
    j ≤ i ∧ coverEnter cover a p j = true ∧ ∀ l, l < j → coverEnter cover a p l = false :=
  optFirst_spec h

/-- Raising the bound does not change a successful entry search. -/
theorem coverFirst_stable {p : ℚ × ℕ} {i j : ℕ} (h : coverFirst cover a p i = some j) :
    ∀ i', i ≤ i' → coverFirst cover a p i' = some j :=
  optFirst_stable h

/-- If some step up to the bound enters the interval, the entry search succeeds. -/
theorem coverFirst_isSome_of {p : ℚ × ℕ} {i j : ℕ} (hj : j ≤ i)
    (h : coverEnter cover a p j = true) : ∃ j', coverFirst cover a p i = some j' :=
  optFirst_isSome_of hj h

/-- The least entering step is found by the search run exactly to that step. -/
theorem coverFirst_self {p : ℚ × ℕ} {j : ℕ} (h : coverEnter cover a p j = true)
    (hmin : ∀ l, l < j → coverEnter cover a p l = false) :
    coverFirst cover a p j = some j :=
  optFirst_self h hmin

/-- A covering interval that has not been entered charges nothing. -/
theorem coverCharge_none {p : ℚ × ℕ} {i : ℕ} (h : coverFirst cover a p i = none) :
    coverCharge cover a p i = 0 := by rw [coverCharge, h]

/-- The charge of an entered interval is the distance from the approximation to the right
endpoint, and only at the step following the entry. -/
theorem coverCharge_some {p : ℚ × ℕ} {i j : ℕ} (h : coverFirst cover a p i = some j) :
    coverCharge cover a p i = cond (p.2 + j == i) ((covPair cover p).2 - a j) 0 := by
  rw [coverCharge, h]

/-- An entering step has its approximation strictly inside the interval. -/
theorem coverEnter_spec {p : ℚ × ℕ} {j : ℕ} (h : coverEnter cover a p j = true) :
    (covPair cover p).1 < a j ∧ a j < (covPair cover p).2 := by
  rw [coverEnter, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [ratLtPair, decide_eq_true_eq] at h1
  rw [ratLtPair, decide_eq_true_eq] at h2
  exact ⟨h1, h2⟩

/-- A cover slot that some `a j` enters is not the `none` slot. -/
theorem cover_eq_some_of_enter {p : ℚ × ℕ} {j : ℕ} (h : coverEnter cover a p j = true) :
    cover p.1 p.2 = some (covPair cover p) := by
  rcases Option.eq_none_or_eq_some (cover p.1 p.2) with hn | ⟨I, hI⟩
  · exfalso
    obtain ⟨h1, h2⟩ := coverEnter_spec cover a h
    rw [covPair, hn] at h1 h2
    exact absurd (h1.trans h2) (by simp)
  · have hpair : covPair cover p = I := by simp [covPair, hI]
    rw [hpair, hI]

/-- Charges are nonnegative. -/
theorem coverCharge_nonneg (p : ℚ × ℕ) (i : ℕ) : 0 ≤ coverCharge cover a p i := by
  rcases Option.eq_none_or_eq_some (coverFirst cover a p i) with hn | ⟨j, hj⟩
  · rw [coverCharge_none cover a hn]
  · rw [coverCharge_some cover a hj]
    obtain ⟨_, h2⟩ := coverEnter_spec cover a (coverFirst_spec cover a hj).2.1
    cases hb : (p.2 + j == i) with
    | false => rw [Bool.cond_false]
    | true => rw [Bool.cond_true]; linarith

/-- Interval `k` cannot charge a step `i < k`, because its charging step is `k + j`. -/
theorem coverCharge_eq_zero_of_lt {p : ℚ × ℕ} {i : ℕ} (h : i < p.2) :
    coverCharge cover a p i = 0 := by
  rcases Option.eq_none_or_eq_some (coverFirst cover a p i) with hn | ⟨j, hj⟩
  · exact coverCharge_none cover a hn
  · rw [coverCharge_some cover a hj,
      beq_eq_false_iff_ne.mpr (by omega : ¬ (p.2 + j = i)), Bool.cond_false]

/-- The prediction sequence is nonnegative. -/
theorem coverH_nonneg (ε : ℚ) (i : ℕ) : 0 ≤ coverH cover a ε i :=
  Finset.sum_nonneg (fun k _ => coverCharge_nonneg cover a (ε, k) i)

/-- Each covering interval is charged at most its own length, over all steps. -/
theorem tsum_ofReal_coverCharge_le (ε : ℚ) (k : ℕ) :
    (∑' i, ENNReal.ofReal ((coverCharge cover a (ε, k) i : ℚ) : ℝ))
      ≤ (cover ε k).elim 0 ratIntervalLength := by
  by_cases hfire : ∃ j, coverEnter cover a (ε, k) j = true
  · obtain ⟨j, hj⟩ := hfire
    obtain ⟨j0, hj0⟩ := coverFirst_isSome_of cover a (le_refl j) hj
    obtain ⟨hj0le, hj0true, hj0min⟩ := coverFirst_spec cover a hj0
    have hbase : coverFirst cover a (ε, k) j0 = some j0 :=
      coverFirst_self cover a hj0true hj0min
    have hval : ∀ i, coverCharge cover a (ε, k) i
        = if k + j0 = i then (covPair cover (ε, k)).2 - a j0 else 0 := by
      intro i
      rcases Nat.lt_or_ge i j0 with hlt | hge
      · have hnone : coverFirst cover a (ε, k) i = none :=
          (coverFirst_eq_none_iff cover a _ _).mpr
            (fun m hm => hj0min m (lt_of_le_of_lt hm hlt))
        rw [coverCharge_none cover a hnone, ite_eq_right (by omega : ¬ (k + j0 = i))]
      · rw [coverCharge_some cover a (coverFirst_stable cover a hbase i hge)]
        cases hb : (k + j0 == i) with
        | false => rw [Bool.cond_false, ite_eq_right (beq_eq_false_iff_ne.mp hb)]
        | true => rw [Bool.cond_true, ite_eq_left (beq_iff_eq.mp hb)]
    have hsingle : (∑' i, ENNReal.ofReal ((coverCharge cover a (ε, k) i : ℚ) : ℝ))
        = ENNReal.ofReal (((covPair cover (ε, k)).2 - a j0 : ℚ) : ℝ) := by
      refine (tsum_eq_single (k + j0) (fun i hi => ?_)).trans ?_
      · rw [hval i, ite_eq_right (fun hc => hi hc.symm)]
        simp
      · rw [hval (k + j0), ite_eq_left rfl]
    rw [hsingle, cover_eq_some_of_enter cover a hj0true]
    obtain ⟨h1, h2⟩ := coverEnter_spec cover a hj0true
    have h1R : (((covPair cover (ε, k)).1 : ℚ) : ℝ) < ((a j0 : ℚ) : ℝ) := by exact_mod_cast h1
    change ENNReal.ofReal (((covPair cover (ε, k)).2 - a j0 : ℚ) : ℝ)
      ≤ ratIntervalLength (covPair cover (ε, k))
    rw [ratIntervalLength]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith
  · push Not at hfire
    have hz : ∀ i, coverCharge cover a (ε, k) i = 0 := by
      intro i
      refine coverCharge_none cover a ((coverFirst_eq_none_iff cover a _ _).mpr ?_)
      intro m _
      simpa using hfire m
    simp [hz]

/-- The total charge over all steps is at most the total length of the cover. -/
theorem tsum_ofReal_coverH_le (ε : ℚ) :
    (∑' i, ENNReal.ofReal ((coverH cover a ε i : ℚ) : ℝ))
      ≤ ∑' k, (cover ε k).elim 0 ratIntervalLength := by
  have hstep : ∀ i, ENNReal.ofReal ((coverH cover a ε i : ℚ) : ℝ)
      = ∑' k, ENNReal.ofReal ((coverCharge cover a (ε, k) i : ℚ) : ℝ) := by
    intro i
    have hzero : ∀ k, k ∉ Finset.range (i + 1) →
        ENNReal.ofReal ((coverCharge cover a (ε, k) i : ℚ) : ℝ) = 0 := by
      intro k hk
      have hik : i < k := by
        have := Finset.mem_range.not.mp hk
        omega
      rw [coverCharge_eq_zero_of_lt cover a hik]
      simp
    have hcast : (((∑ k ∈ Finset.range (i + 1), coverCharge cover a (ε, k) i : ℚ)) : ℝ)
        = ∑ k ∈ Finset.range (i + 1), ((coverCharge cover a (ε, k) i : ℚ) : ℝ) := by
      push_cast
      ring
    rw [coverH, hcast, ENNReal.ofReal_sum_of_nonneg
      (fun k _ => by exact_mod_cast coverCharge_nonneg cover a (ε, k) i)]
    exact (tsum_eq_sum hzero).symm
  rw [tsum_congr hstep, ENNReal.tsum_comm]
  exact ENNReal.tsum_le_tsum (fun k => tsum_ofReal_coverCharge_le cover a ε k)

/-- One of the steps is charged enough to cover `α`, provided `α` lies inside one of the
intervals of the cover and the sequence `a` converges to `α` from below. -/
theorem exists_le_add_coverH {α : ℝ} (ε : ℚ) (hmono : Monotone a)
    (hle : ∀ i, ((a i : ℚ) : ℝ) ≤ α)
    (hlim : Filter.Tendsto (fun n => ((a n : ℚ) : ℝ)) Filter.atTop (nhds α))
    (hmem : α ∈ ⋃ i, (cover ε i).elim ∅ ratInterval) :
    ∃ i, α ≤ ((a i : ℚ) : ℝ) + ((coverH cover a ε i : ℚ) : ℝ) := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
  rcases Option.eq_none_or_eq_some (cover ε k) with hn | ⟨I, hI⟩
  · rw [hn] at hk; exact absurd hk (by simp)
  rw [hI] at hk
  have hkI : α ∈ Set.Ioo ((I.1 : ℚ) : ℝ) ((I.2 : ℚ) : ℝ) := hk
  have hIpair : covPair cover (ε, k) = I := by simp [covPair, hI]
  have hex : ∃ n, ((I.1 : ℚ) : ℝ) < ((a n : ℚ) : ℝ) := by
    by_contra hc
    push Not at hc
    have hle : α ≤ ((I.1 : ℚ) : ℝ) := le_of_tendsto' hlim hc
    linarith [hkI.1]
  obtain ⟨n, hn⟩ := hex
  have hent : coverEnter cover a (ε, k) n = true := by
    rw [coverEnter, hIpair, Bool.and_eq_true, ratLtPair, ratLtPair, decide_eq_true_eq,
      decide_eq_true_eq]
    refine ⟨by exact_mod_cast hn, ?_⟩
    have hlt2 : ((a n : ℚ) : ℝ) < ((I.2 : ℚ) : ℝ) := lt_of_le_of_lt (hle n) hkI.2
    exact_mod_cast hlt2
  obtain ⟨j0, hj0⟩ := coverFirst_isSome_of cover a (le_refl n) hent
  obtain ⟨hj0le, hj0true, hj0min⟩ := coverFirst_spec cover a hj0
  have hbase : coverFirst cover a (ε, k) j0 = some j0 :=
    coverFirst_self cover a hj0true hj0min
  refine ⟨k + j0, ?_⟩
  have hchg : coverCharge cover a (ε, k) (k + j0) = I.2 - a j0 := by
    rw [coverCharge_some cover a (coverFirst_stable cover a hbase (k + j0) (by omega)),
      hIpair]
    simp
  have hle : coverCharge cover a (ε, k) (k + j0) ≤ coverH cover a ε (k + j0) :=
    Finset.single_le_sum (f := fun k' => coverCharge cover a (ε, k') (k + j0))
      (fun k' _ => coverCharge_nonneg cover a (ε, k') (k + j0))
      (Finset.mem_range.mpr (by omega))
  have hleR : ((I.2 : ℚ) : ℝ) - ((a j0 : ℚ) : ℝ) ≤ ((coverH cover a ε (k + j0) : ℚ) : ℝ) := by
    have := hle
    rw [hchg] at this
    have hcast : (((I.2 - a j0 : ℚ)) : ℝ) = ((I.2 : ℚ) : ℝ) - ((a j0 : ℚ) : ℝ) := by
      push_cast; ring
    rw [← hcast]
    exact_mod_cast this
  have hamono : ((a j0 : ℚ) : ℝ) ≤ ((a (k + j0) : ℚ) : ℝ) := by
    exact_mod_cast hmono (by omega : j0 ≤ k + j0)
  linarith [hkI.2]

/-! ### The two-point membership test of SUV p. 164 -/

/-- The closed interval `[x, y]` sits strictly inside the interval `p` of the cover.
This is the test behind Theorem 109: the block `[r₀ + ⋯ + rᵢ₋₁, r₀ + ⋯ + rᵢ]` is
entirely covered by one of the intervals. -/
def coverInside (p : ℚ × ℕ) (x y : ℚ) : Bool :=
  ratLtPair ((covPair cover p).1, x) && ratLtPair (y, (covPair cover p).2)

/-- If the containment test fires, the closed interval `[x, y]` is strictly inside the covering
interval. -/
theorem coverInside_spec {p : ℚ × ℕ} {x y : ℚ} (h : coverInside cover p x y = true) :
    (covPair cover p).1 < x ∧ y < (covPair cover p).2 := by
  rw [coverInside, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [ratLtPair, decide_eq_true_eq] at h1
  rw [ratLtPair, decide_eq_true_eq] at h2
  exact ⟨h1, h2⟩

/-- Strict containment of `[x, y]` in the covering interval makes the test fire. -/
theorem coverInside_of {p : ℚ × ℕ} {x y : ℚ} (h1 : (covPair cover p).1 < x)
    (h2 : y < (covPair cover p).2) : coverInside cover p x y = true := by
  rw [coverInside, Bool.and_eq_true, ratLtPair, ratLtPair, decide_eq_true_eq,
    decide_eq_true_eq]
  exact ⟨h1, h2⟩

/-- A cover slot with a nonempty interval is not the `none` slot. -/
theorem cover_eq_some_of_lt {p : ℚ × ℕ}
    (h : (covPair cover p).1 < (covPair cover p).2) :
    cover p.1 p.2 = some (covPair cover p) := by
  rcases Option.eq_none_or_eq_some (cover p.1 p.2) with hn | ⟨I, hI⟩
  · exfalso
    rw [covPair, hn] at h
    exact absurd h (by simp)
  · have hpair : covPair cover p = I := by simp [covPair, hI]
    rw [hpair, hI]

/-! ### Computability of the prediction sequence -/

/-- Reading the interval of a cover, with `none` read as the degenerate pair, is computable. -/
theorem computable_covPair (hcov : Computable₂ cover) :
    Computable (fun p : ℚ × ℕ => covPair cover p) :=
  Computable.option_getD hcov (Computable.const (0, 0))

/-- The containment test is computable. -/
theorem computable_coverInside (hcov : Computable₂ cover) :
    Computable (fun t : (ℚ × ℕ) × ℚ × ℚ => coverInside cover t.1 t.2.1 t.2.2) := by
  have hp : Computable (fun t : (ℚ × ℕ) × ℚ × ℚ => covPair cover t.1) :=
    (computable_covPair cover hcov).comp Computable.fst
  have hx : Computable (fun t : (ℚ × ℕ) × ℚ × ℚ => t.2.1) :=
    Computable.fst.comp Computable.snd
  have hy : Computable (fun t : (ℚ × ℕ) × ℚ × ℚ => t.2.2) :=
    Computable.snd.comp Computable.snd
  have h1 : Computable (fun t : (ℚ × ℕ) × ℚ × ℚ =>
      ratLtPair ((covPair cover t.1).1, t.2.1)) :=
    computable_ratLtPair.comp (Computable.pair (Computable.fst.comp hp) hx)
  have h2 : Computable (fun t : (ℚ × ℕ) × ℚ × ℚ =>
      ratLtPair (t.2.2, (covPair cover t.1).2)) :=
    computable_ratLtPair.comp (Computable.pair hy (Computable.snd.comp hp))
  exact Primrec.and.to_comp.comp h1 h2

/-- Reindexed form of `computable_coverInside`, with the three inputs supplied by
computable functions.  Stated separately so that the definitional check never has to
unfold `coverInside` (and, with it, the `Decidable` instance of `ℚ`). -/
theorem computable_coverInside_comp {β : Type} [Primcodable β] (hcov : Computable₂ cover)
    {u : β → ℚ × ℕ} {x y : β → ℚ} (hu : Computable u) (hx : Computable x)
    (hy : Computable y) :
    Computable (fun b : β => coverInside cover (u b) (x b) (y b)) := by
  -- the composition is elaborated *without* an expected type, so that the higher-order
  -- unification never has to unfold `coverInside`
  have h := (computable_coverInside cover hcov).comp (Computable.pair hu (Computable.pair hx hy))
  exact h

/-- The entry test is computable in both arguments. -/
theorem computable_coverEnter (hcov : Computable₂ cover) (ha : Computable a) :
    Computable₂ (coverEnter cover a) := by
  have hp : Computable (fun r : (ℚ × ℕ) × ℕ => covPair cover r.1) :=
    (computable_covPair cover hcov).comp Computable.fst
  have haj : Computable (fun r : (ℚ × ℕ) × ℕ => a r.2) := ha.comp Computable.snd
  have h1 : Computable (fun r : (ℚ × ℕ) × ℕ =>
      ratLtPair ((covPair cover r.1).1, a r.2)) :=
    computable_ratLtPair.comp (Computable.pair (Computable.fst.comp hp) haj)
  have h2 : Computable (fun r : (ℚ × ℕ) × ℕ =>
      ratLtPair (a r.2, (covPair cover r.1).2)) :=
    computable_ratLtPair.comp (Computable.pair haj (Computable.snd.comp hp))
  exact Primrec.and.to_comp.comp h1 h2

/-- The charge of a covering interval at a step is computable. -/
theorem computable_coverCharge (hcov : Computable₂ cover) (ha : Computable a) :
    Computable (fun s : (ℚ × ℕ) × ℕ => coverCharge cover a (s.1.1, s.2) s.1.2) := by
  have hfirst : Computable (fun s : (ℚ × ℕ) × ℕ =>
      optFirst (coverEnter cover a) (s.1.1, s.2) s.1.2) :=
    computable_optFirst_comp (computable_coverEnter cover a hcov ha)
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
      (Computable.snd.comp Computable.fst)
  have hsome : Computable₂ (fun (s : (ℚ × ℕ) × ℕ) (j : ℕ) =>
      cond (s.2 + j == s.1.2) ((covPair cover (s.1.1, s.2)).2 - a j) 0) := by
    have hk : Computable (fun t : ((ℚ × ℕ) × ℕ) × ℕ => t.1.2) :=
      Computable.snd.comp Computable.fst
    have hj : Computable (fun t : ((ℚ × ℕ) × ℕ) × ℕ => t.2) := Computable.snd
    have hsum : Computable (fun t : ((ℚ × ℕ) × ℕ) × ℕ => t.1.2 + t.2) :=
      Primrec.nat_add.to_comp.comp hk hj
    have hi : Computable (fun t : ((ℚ × ℕ) × ℕ) × ℕ => t.1.1.2) :=
      Computable.snd.comp (Computable.fst.comp Computable.fst)
    have hbeq : Computable (fun t : ((ℚ × ℕ) × ℕ) × ℕ => (t.1.2 + t.2 == t.1.1.2)) :=
      Primrec.beq.to_comp.comp hsum hi
    have hpair : Computable (fun t : ((ℚ × ℕ) × ℕ) × ℕ => covPair cover (t.1.1.1, t.1.2)) :=
      (computable_covPair cover hcov).comp
        (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.fst)) hk)
    have hval : Computable (fun t : ((ℚ × ℕ) × ℕ) × ℕ =>
        (covPair cover (t.1.1.1, t.1.2)).2 - a t.2) :=
      Computable₂.comp computable₂_ratSub (Computable.snd.comp hpair) (ha.comp hj)
    exact Computable.cond hbeq hval (Computable.const 0)
  exact Computable.option_casesOn hfirst (Computable.const 0) hsome

/-- The prediction sequence is computable in the budget and the step. -/
theorem computable_coverH (hcov : Computable₂ cover) (ha : Computable a) :
    Computable₂ (coverH cover a) := by
  have hu : Computable₂ (fun (p : ℚ × ℕ) (k : ℕ) => coverCharge cover a (p.1, k) p.2) :=
    computable_coverCharge cover a hcov ha
  have hd : Computable (fun q : ℚ × ℕ => ((q.1, q.2), q.2 + 1)) :=
    Computable.pair Computable.id (Primrec.succ.to_comp.comp Computable.snd)
  refine ((computable_ratRangeSumP hu).comp hd).of_eq (fun q => ?_)
  rw [ratRangeSumP_eq, coverH]

end Cover

end Kolmogorov
