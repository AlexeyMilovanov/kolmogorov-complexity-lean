/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.PredictCover

/-!
# The shifted-interval process of SUV Section 5.7.4 (p. 164)

Given computable increasing rational approximations `a → α` and `b → β` and a positive
integer `c`, the source shifts the increments of `a/c` onto the `b`-axis:

  `i₀ = 0`,  `i_{k+1} =` the first `j` with `b_j > b_{i_k} + (a_{k+1} − a_k)/c`.

Two things can happen (p. 164–165).  If the process is **total**, then the map
`r ↦ a_k/c`, where `k` is the first index with `r < b_{i_k}`, is a reduction function
witnessing `α/c ≼₁ β`, because `(α − a_k)/c ≤ β − b_{i_k}`.  If it **stalls** at `k`,
then no `b_j` ever exceeds `b_{i_k} + (a_{k+1} − a_k)/c`, so `β` itself is caught in the
single interval `(b_{i_k}, b_{i_k} + (a_{k+1} − a_k)/c + padding)` — and the total length
of all the emitted intervals is at most `(α − a₀)/c + ε/2`, because each `k` emits at
most once and `∑ₖ (a_{k+1} − a_k)/c = (α − a₀)/c`.

Everything here is proved; the module renders no statement of the source.
-/

namespace Kolmogorov

open ENNReal

section Process

variable (as bs : ℕ → ℚ) (w : ℚ)

/-- The `k`-th shift amount `(a_{k+1} − a_k)/c`. -/
def shiftStep (k : ℕ) : ℚ := (as (k + 1) - as k) * w

/-- The test "the approximation `b` has passed the rational `x`". -/
def passTest (x : ℚ) (j : ℕ) : Bool := ratLtPair (x, bs j)

/-- The bounded search for the first index at which `b` passes `x`. -/
def firstPass (x : ℚ) (t : ℕ) : Option ℕ := optFirst (passTest bs) x t

/-- The process of SUV p. 164, run with search bound `t`. -/
def procIdx : ℕ → ℕ → Option ℕ :=
  fun k t =>
    Nat.rec (some 0)
      (fun j previous => previous.bind (fun i => firstPass bs (bs i + shiftStep as w j) t))
      k

/-- The step of the process at which an index is found for the *first* time. -/
def procFirst (k : ℕ) : ℕ → Option ℕ
  | 0 => procIdx as bs w k 0
  | t + 1 => cond (procIdx as bs w k t).isSome none (procIdx as bs w k (t + 1))

/-- The cover of SUV p. 165: the shifted interval attached to the step at which the
`k`-th index of the process is found. -/
def shiftCover (ε : ℚ) (n : ℕ) : Option (ℚ × ℚ) :=
  Option.casesOn (motive := fun _ => Option (ℚ × ℚ))
    (procFirst as bs w (Nat.unpair n).1 (Nat.unpair n).2) none
    (fun i => some (bs i, bs i + shiftStep as w (Nat.unpair n).1 + ratPad ε n))

end Process

/-! ### Basic properties of the process -/

variable {as bs : ℕ → ℚ} {w : ℚ}

/-- The pass test at `x` fires exactly when the approximation has exceeded `x`. -/
theorem passTest_iff {x : ℚ} {j : ℕ} : passTest bs x j = true ↔ x < bs j := by
  rw [passTest, ratLtPair, decide_eq_true_eq]

/-- An index returned by the bounded search does pass `x`. -/
theorem firstPass_spec {x : ℚ} {t j : ℕ} (h : firstPass bs x t = some j) : x < bs j :=
  passTest_iff.mp (optFirst_spec h).2.1

/-- When the bounded search fails up to `t`, no index up to `t` passes `x`. -/
theorem firstPass_none {x : ℚ} {t : ℕ} (h : firstPass bs x t = none) (j : ℕ) (hj : j ≤ t) :
    ¬ (x < bs j) := by
  have := (optFirst_eq_none_iff (passTest bs) x t).mp h j hj
  rw [passTest_iff.symm.not] at *
  simp_all

/-- Once the bounded search succeeds, increasing the bound does not change its value. -/
theorem firstPass_stable {x : ℚ} {t j : ℕ} (h : firstPass bs x t = some j) {t' : ℕ}
    (ht : t ≤ t') : firstPass bs x t' = some j := optFirst_stable h t' ht

/-- The process starts at index zero. -/
theorem procIdx_zero (t : ℕ) : procIdx as bs w 0 t = some 0 := rfl

/-- One step of the process searches for the first index at which the approximation exceeds the
current value shifted by the current increment. -/
theorem procIdx_succ (k t : ℕ) : procIdx as bs w (k + 1) t
    = (procIdx as bs w k t).bind (fun i => firstPass bs (bs i + shiftStep as w k) t) := rfl

/-- Once the process has found its `k`-th index within bound `t`, larger bounds return the same
index. -/
theorem procIdx_stable {k t i : ℕ} (h : procIdx as bs w k t = some i) {t' : ℕ} (ht : t ≤ t') :
    procIdx as bs w k t' = some i := by
  induction k generalizing i with
  | zero => rw [procIdx_zero] at h ⊢; exact h
  | succ k ih =>
      rw [procIdx_succ] at h ⊢
      rcases hp : procIdx as bs w k t with _ | i0
      · rw [hp] at h; exact absurd h (by simp)
      · rw [hp] at h
        rw [ih hp]
        exact firstPass_stable h ht

/-- The value found at step `k` really is a `b`-index that has passed the shifted
point of step `k − 1`. -/
theorem procIdx_succ_spec {k t i j : ℕ} (hi : procIdx as bs w k t = some i)
    (hj : procIdx as bs w (k + 1) t = some j) : bs i + shiftStep as w k < bs j := by
  rw [procIdx_succ, hi] at hj
  exact firstPass_spec hj

/-- If the process stalls at `k + 1`, no `b` ever passes the shifted point. -/
theorem le_of_procIdx_none {k t i : ℕ} (hi : procIdx as bs w k t = some i)
    (hnone : ∀ t', procIdx as bs w (k + 1) t' = none) (j : ℕ) :
    ¬ (bs i + shiftStep as w k < bs j) := by
  have ht : procIdx as bs w k (max t j) = some i := procIdx_stable hi (le_max_left t j)
  have h := hnone (max t j)
  rw [procIdx_succ, ht] at h
  exact firstPass_none h j (le_max_right t j)

/-- The step at which an index is found for the first time carries the same index as the process
itself. -/
theorem procFirst_some {k t i : ℕ} (h : procFirst as bs w k t = some i) :
    procIdx as bs w k t = some i := by
  cases t with
  | zero => exact h
  | succ t =>
      rw [procFirst] at h
      rcases hp : (procIdx as bs w k t).isSome with _ | _
      · rw [hp, Bool.cond_false] at h; exact h
      · rw [hp, Bool.cond_true] at h; exact absurd h (by simp)

/-- Each `k` is emitted at most once. -/
theorem procFirst_unique {k t t' i i' : ℕ} (h : procFirst as bs w k t = some i)
    (h' : procFirst as bs w k t' = some i') : t = t' := by
  by_contra hne
  rcases Nat.lt_or_ge t t' with hlt | hge
  · rcases t' with _ | t'
    · omega
    · rw [procFirst] at h'
      have hs : (procIdx as bs w k t').isSome = true := by
        rw [procIdx_stable (procFirst_some h) (by omega : t ≤ t')]
        rfl
      rw [hs, Bool.cond_true] at h'
      exact absurd h' (by simp)
  · have hlt : t' < t := by omega
    rcases t with _ | t
    · omega
    · rw [procFirst] at h
      have hs : (procIdx as bs w k t).isSome = true := by
        rw [procIdx_stable (procFirst_some h') (by omega : t' ≤ t)]
        rfl
      rw [hs, Bool.cond_true] at h
      exact absurd h (by simp)

/-- If the process ever reaches `k`, then some step emits it. -/
theorem exists_procFirst {k t i : ℕ} (h : procIdx as bs w k t = some i) :
    ∃ t' i', procFirst as bs w k t' = some i' := by
  induction t generalizing i with
  | zero => exact ⟨0, i, h⟩
  | succ t ih =>
      rcases hp : procIdx as bs w k t with _ | i0
      · refine ⟨t + 1, i, ?_⟩
        rw [procFirst, hp]
        exact h
      · exact ih hp

/-! ### Computability -/

/-- The pass test of a computable approximation is computable in both arguments. -/
theorem computable₂_passTest (hbs : Computable bs) : Computable₂ (passTest bs) := by
  have h := computable_ratLtPair.comp
    (Computable.pair (Computable.fst : Computable (fun q : ℚ × ℕ => q.1))
      (hbs.comp (Computable.snd : Computable (fun q : ℚ × ℕ => q.2))))
  exact h

/-- The bounded search is computable in the threshold and the bound. -/
theorem computable_firstPass (hbs : Computable bs) :
    Computable (fun q : ℚ × ℕ => firstPass bs q.1 q.2) :=
  computable_optFirst (computable₂_passTest hbs)

/-- The shift amounts of a computable approximation are computable. -/
theorem computable_shiftStep (has : Computable as) (w : ℚ) :
    Computable (shiftStep as w) := by
  have hsub := Computable₂.comp computable₂_ratSub (has.comp Primrec.succ.to_comp) has
  have h := Computable₂.comp computable₂_ratMul hsub (Computable.const w)
  exact h

/-- The process is computable in its step and its search bound. -/
theorem computable_procIdx (has : Computable as) (hbs : Computable bs) (w : ℚ) :
    Computable (fun q : ℕ × ℕ => procIdx as bs w q.1 q.2) := by
  have hstep : Computable₂ (fun (q : ℕ × ℕ) (r : ℕ × Option ℕ) =>
      r.2.bind (fun i => firstPass bs (bs i + shiftStep as w r.1) q.2)) := by
    have hg : Computable₂ (fun (z : (ℕ × ℕ) × ℕ × Option ℕ) (i : ℕ) =>
        firstPass bs (bs i + shiftStep as w z.2.1) z.1.2) := by
      have hx : Computable (fun v : ((ℕ × ℕ) × ℕ × Option ℕ) × ℕ =>
          bs v.2 + shiftStep as w v.1.2.1) :=
        Computable₂.comp computable₂_ratAdd (hbs.comp Computable.snd)
          ((computable_shiftStep has w).comp
            (Computable.fst.comp (Computable.snd.comp Computable.fst)))
      have ht : Computable (fun v : ((ℕ × ℕ) × ℕ × Option ℕ) × ℕ => v.1.1.2) :=
        Computable.snd.comp (Computable.fst.comp Computable.fst)
      have h := (computable_firstPass hbs).comp (Computable.pair hx ht)
      exact h
    have hIH : Computable (fun z : (ℕ × ℕ) × ℕ × Option ℕ => z.2.2) :=
      Computable.snd.comp Computable.snd
    have h := Computable.option_bind hIH hg
    exact h
  have hrec := Computable.nat_rec (σ := Option ℕ) Computable.fst
    (Computable.const (some 0)) hstep
  refine hrec.of_eq (fun q => ?_)
  obtain ⟨k, t⟩ := q
  have key : ∀ j : ℕ, (Nat.rec (motive := fun _ => Option ℕ) (some 0)
      (fun y IH => IH.bind (fun i => firstPass bs (bs i + shiftStep as w y) t)) j)
      = procIdx as bs w j t := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [procIdx_succ]
        exact congrArg (fun X : Option ℕ =>
          X.bind (fun i => firstPass bs (bs i + shiftStep as w j) t)) ih
  exact key k

/-- The first-appearance step of the process is computable. -/
theorem computable_procFirst (has : Computable as) (hbs : Computable bs) (w : ℚ) :
    Computable (fun q : ℕ × ℕ => procFirst as bs w q.1 q.2) := by
  have hp := computable_procIdx has hbs w
  have hbase : Computable (fun q : ℕ × ℕ => procIdx as bs w q.1 0) :=
    hp.comp (Computable.pair Computable.fst (Computable.const 0))
  have hstep : Computable₂ (fun (q : ℕ × ℕ) (t : ℕ) =>
      cond (procIdx as bs w q.1 t).isSome none (procIdx as bs w q.1 (t + 1))) := by
    have h1 := hp.comp (Computable.pair
      (Computable.fst.comp (Computable.fst : Computable (fun v : (ℕ × ℕ) × ℕ => v.1)))
      (Computable.snd : Computable (fun v : (ℕ × ℕ) × ℕ => v.2)))
    have h2 := hp.comp (Computable.pair
      (Computable.fst.comp (Computable.fst : Computable (fun v : (ℕ × ℕ) × ℕ => v.1)))
      (Primrec.succ.to_comp.comp (Computable.snd : Computable (fun v : (ℕ × ℕ) × ℕ => v.2))))
    have h := Computable.cond (Primrec.option_isSome.to_comp.comp h1)
      (Computable.const (none : Option ℕ)) h2
    exact h
  have h := Computable.nat_casesOn
    (Computable.snd : Computable (fun q : ℕ × ℕ => q.2)) hbase hstep
  refine h.of_eq (fun q => ?_)
  obtain ⟨k, t⟩ := q
  cases t with
  | zero => rfl
  | succ t => rfl

/-- The shifted-interval cover is computable in the budget and the index. -/
theorem computable₂_shiftCover (has : Computable as) (hbs : Computable bs) (w : ℚ) :
    Computable₂ (shiftCover as bs w) := by
  have hk : Computable (fun q : ℚ × ℕ => (Nat.unpair q.2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have ht : Computable (fun q : ℚ × ℕ => (Nat.unpair q.2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hfirst := (computable_procFirst has hbs w).comp (Computable.pair hk ht)
  have hsome : Computable₂ (fun (q : ℚ × ℕ) (i : ℕ) =>
      some (bs i, bs i + shiftStep as w (Nat.unpair q.2).1 + ratPad q.1 q.2)) := by
    have hbi : Computable (fun v : (ℚ × ℕ) × ℕ => bs v.2) := hbs.comp Computable.snd
    have hst : Computable (fun v : (ℚ × ℕ) × ℕ =>
        shiftStep as w (Nat.unpair v.1.2).1) :=
      (computable_shiftStep has w).comp (hk.comp Computable.fst)
    have hpad : Computable (fun v : (ℚ × ℕ) × ℕ => ratPad v.1.1 v.1.2) :=
      computable₂_ratPad.comp (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.fst)
    have hr : Computable (fun v : (ℚ × ℕ) × ℕ =>
        bs v.2 + shiftStep as w (Nat.unpair v.1.2).1 + ratPad v.1.1 v.1.2) :=
      Computable₂.comp computable₂_ratAdd
        (Computable₂.comp computable₂_ratAdd hbi hst) hpad
    exact Computable.option_some.comp (Computable.pair hbi hr)
  exact Computable.option_casesOn hfirst (Computable.const none) hsome

/-! ### The total length of the cover -/

/-- For a monotone approximation and a nonnegative scale, the shift amounts are nonnegative. -/
theorem shiftStep_nonneg (hmono : Monotone as) (w : ℚ) (hw : 0 ≤ w) (k : ℕ) :
    0 ≤ shiftStep as w k := by
  rw [shiftStep]
  refine mul_nonneg ?_ hw
  have := hmono (Nat.le_succ k)
  linarith

/-- The length of the interval emitted at index `n` is the shift amount of the corresponding step
together with its padding, and zero where nothing is emitted. -/
theorem shiftCover_length (hmono : Monotone as) {w : ℚ} (hw : 0 ≤ w) {ε : ℚ} (hε : 0 < ε)
    (n : ℕ) :
    (shiftCover as bs w ε n).elim 0 ratIntervalLength
      = Option.casesOn (motive := fun _ => ℝ≥0∞)
          (procFirst as bs w (Nat.unpair n).1 (Nat.unpair n).2) 0
          (fun _ => ENNReal.ofReal ((shiftStep as w (Nat.unpair n).1 : ℚ) : ℝ)
            + ENNReal.ofReal ((ratPad ε n : ℚ) : ℝ)) := by
  rw [shiftCover]
  rcases hf : procFirst as bs w (Nat.unpair n).1 (Nat.unpair n).2 with _ | i
  · rfl
  · change ratIntervalLength (bs i, bs i + shiftStep as w (Nat.unpair n).1 + ratPad ε n) = _
    rw [ratIntervalLength]
    have hval : ((bs i + shiftStep as w (Nat.unpair n).1 + ratPad ε n : ℚ) : ℝ)
        - ((bs i : ℚ) : ℝ)
        = ((shiftStep as w (Nat.unpair n).1 : ℚ) : ℝ) + ((ratPad ε n : ℚ) : ℝ) := by
      push_cast; ring
    rw [hval]
    exact ENNReal.ofReal_add (by exact_mod_cast shiftStep_nonneg hmono w hw _)
      (by exact_mod_cast (ratPad_pos hε n).le)

/-- The shifts telescope to `(α − a₀)·w`. -/
theorem tsum_shiftStep_le {α : ℝ} (a : LowerApprox α) {w : ℚ} (hw : 0 < w) :
    (∑' k, ENNReal.ofReal ((shiftStep a.seq w k : ℚ) : ℝ))
      ≤ ENNReal.ofReal ((α - ((a.seq 0 : ℚ) : ℝ)) * ((w : ℚ) : ℝ)) := by
  have hwR : (0 : ℝ) < ((w : ℚ) : ℝ) := by exact_mod_cast hw
  refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
  have hsum : ∀ n : ℕ, ∑ k ∈ Finset.range n, shiftStep a.seq w k
      = (a.seq n - a.seq 0) * w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, shiftStep]
        ring
  have hnn : ∀ k ∈ Finset.range n, (0 : ℝ) ≤ ((shiftStep a.seq w k : ℚ) : ℝ) :=
    fun k _ => by exact_mod_cast shiftStep_nonneg a.isStrictMono.monotone w hw.le k
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcast : ∑ k ∈ Finset.range n, ((shiftStep a.seq w k : ℚ) : ℝ)
      = (((a.seq n : ℚ) : ℝ) - ((a.seq 0 : ℚ) : ℝ)) * ((w : ℚ) : ℝ) := by
    have h1 : (((∑ k ∈ Finset.range n, shiftStep a.seq w k : ℚ)) : ℝ)
        = ∑ k ∈ Finset.range n, ((shiftStep a.seq w k : ℚ) : ℝ) := by push_cast; ring
    rw [← h1, hsum n]
    push_cast
    ring
  rw [hcast]
  have hle : ((a.seq n : ℚ) : ℝ) ≤ α := a.seq_le n
  gcongr

/-! ### The cover is small, and it catches `β` when the process stalls -/

/-- The shift charged at the index `n` (zero when nothing is emitted there). -/
noncomputable def shiftCharge (as bs : ℕ → ℚ) (w : ℚ) (n : ℕ) : ℝ≥0∞ :=
  Option.casesOn (motive := fun _ => ℝ≥0∞)
    (procFirst as bs w (Nat.unpair n).1 (Nat.unpair n).2) 0
    (fun _ => ENNReal.ofReal ((shiftStep as w (Nat.unpair n).1 : ℚ) : ℝ))

/-- Nothing is charged at an index where the process emits nothing. -/
theorem shiftCharge_none {n : ℕ}
    (h : procFirst as bs w (Nat.unpair n).1 (Nat.unpair n).2 = none) :
    shiftCharge as bs w n = 0 := by rw [shiftCharge, h]

/-- At an index where the process emits, the charge is the shift amount of that step. -/
theorem shiftCharge_some {n i : ℕ}
    (h : procFirst as bs w (Nat.unpair n).1 (Nat.unpair n).2 = some i) :
    shiftCharge as bs w n = ENNReal.ofReal ((shiftStep as w (Nat.unpair n).1 : ℚ) : ℝ) := by
  rw [shiftCharge, h]

/-- The total length of the shifted cover is at most `(α - a 0) * w + ε / 2`. -/
theorem tsum_length_shiftCover_le {α β : ℝ} (a : LowerApprox α) (b : LowerApprox β)
    {w : ℚ} (hw : 0 < w) {ε : ℚ} (hε : 0 < ε) :
    (∑' n, (shiftCover a.seq b.seq w ε n).elim 0 ratIntervalLength)
      ≤ ENNReal.ofReal ((α - ((a.seq 0 : ℚ) : ℝ)) * ((w : ℚ) : ℝ))
        + ENNReal.ofReal (((ε : ℚ) : ℝ) / 2) := by
  classical
  have hmono : Monotone a.seq := a.isStrictMono.monotone
  have hterm : ∀ n, (shiftCover a.seq b.seq w ε n).elim 0 ratIntervalLength
      ≤ shiftCharge a.seq b.seq w n + ENNReal.ofReal ((ratPad ε n : ℚ) : ℝ) := by
    intro n
    rw [shiftCover_length hmono hw.le hε n]
    rcases hf : procFirst a.seq b.seq w (Nat.unpair n).1 (Nat.unpair n).2 with _ | i
    · rw [shiftCharge_none hf]
      simp
    · rw [shiftCharge_some hf]
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_add, tsum_ofReal_ratPad hε]
  refine add_le_add ?_ le_rfl
  have hrow : ∀ n, shiftCharge a.seq b.seq w n
      = ∑' k, (if (Nat.unpair n).1 = k then shiftCharge a.seq b.seq w n else 0) := by
    intro n
    rw [tsum_eq_single (Nat.unpair n).1 (fun k hk => ite_eq_right (fun hc2 => hk hc2.symm)),
      ite_eq_left rfl]
  have hcol : ∀ k, (∑' n, (if (Nat.unpair n).1 = k then shiftCharge a.seq b.seq w n else 0))
      ≤ ENNReal.ofReal ((shiftStep a.seq w k : ℚ) : ℝ) := by
    intro k
    by_cases hex : ∃ n, (Nat.unpair n).1 = k ∧
        ∃ i, procFirst a.seq b.seq w (Nat.unpair n).1 (Nat.unpair n).2 = some i
    · obtain ⟨n0, hk0, i0, hi0⟩ := hex
      have huniq : ∀ n, (if (Nat.unpair n).1 = k then shiftCharge a.seq b.seq w n else 0) ≠ 0 →
          n = n0 := by
        intro n hn
        by_cases hk : (Nat.unpair n).1 = k
        · rcases hf : procFirst a.seq b.seq w (Nat.unpair n).1 (Nat.unpair n).2 with _ | i
          · rw [ite_eq_left hk, shiftCharge_none hf] at hn
            exact absurd rfl hn
          · have ht : (Nat.unpair n).2 = (Nat.unpair n0).2 :=
              procFirst_unique (k := k) (hk ▸ hf) (hk0 ▸ hi0)
            have hp : Nat.unpair n = Nat.unpair n0 := Prod.ext (hk.trans hk0.symm) ht
            have hq := congrArg (fun p : ℕ × ℕ => Nat.pair p.1 p.2) hp
            simpa [Nat.pair_unpair] using hq
        · rw [ite_eq_right hk] at hn
          exact absurd rfl hn
      rw [tsum_eq_single n0 (fun n hn => by
        by_contra hcon
        exact hn (huniq n hcon))]
      rw [ite_eq_left hk0, shiftCharge_some hi0, hk0]
    · push Not at hex
      have hz : ∀ n, (if (Nat.unpair n).1 = k then shiftCharge a.seq b.seq w n else 0) = 0 := by
        intro n
        by_cases hk : (Nat.unpair n).1 = k
        · rcases hf : procFirst a.seq b.seq w (Nat.unpair n).1 (Nat.unpair n).2 with _ | i
          · rw [ite_eq_left hk, shiftCharge_none hf]
          · exact absurd hf (hex n hk i)
        · rw [ite_eq_right hk]
      simp [hz]
  calc (∑' n, shiftCharge a.seq b.seq w n)
      = ∑' n, ∑' k, (if (Nat.unpair n).1 = k then shiftCharge a.seq b.seq w n else 0) :=
        tsum_congr hrow
    _ = ∑' k, ∑' n, (if (Nat.unpair n).1 = k then shiftCharge a.seq b.seq w n else 0) :=
        ENNReal.tsum_comm
    _ ≤ ∑' k, ENNReal.ofReal ((shiftStep a.seq w k : ℚ) : ℝ) := ENNReal.tsum_le_tsum hcol
    _ ≤ _ := tsum_shiftStep_le a hw

/-! ### Computability, uniformly in the scale -/

/-- The shift amounts are computable jointly in the scale and the step. -/
theorem computable_shiftStepP (has : Computable as) :
    Computable (fun q : ℚ × ℕ => shiftStep as q.1 q.2) := by
  have hsub : Computable (fun q : ℚ × ℕ => as (q.2 + 1) - as q.2) :=
    Computable₂.comp computable₂_ratSub
      (has.comp (Primrec.succ.to_comp.comp Computable.snd)) (has.comp Computable.snd)
  have h := Computable₂.comp computable₂_ratMul hsub Computable.fst
  exact h

attribute [irreducible] passTest firstPass shiftStep

/-- The process is computable jointly in the scale, the step and the search bound. -/
theorem computable_procIdxP (has : Computable as) (hbs : Computable bs) :
    Computable (fun q : ℚ × ℕ × ℕ => procIdx as bs q.1 q.2.1 q.2.2) := by
  have hstep : Computable₂ (fun (q : ℚ × ℕ × ℕ) (r : ℕ × Option ℕ) =>
      r.2.bind (fun i => firstPass bs (bs i + shiftStep as q.1 r.1) q.2.2)) := by
    have hg : Computable₂ (fun (z : (ℚ × ℕ × ℕ) × ℕ × Option ℕ) (i : ℕ) =>
        firstPass bs (bs i + shiftStep as z.1.1 z.2.1) z.1.2.2) := by
      have p1 : Computable (fun v : ((ℚ × ℕ × ℕ) × ℕ × Option ℕ) × ℕ => v.1.1.1) :=
        Computable.fst.comp (Computable.fst.comp Computable.fst)
      have p2 : Computable (fun v : ((ℚ × ℕ × ℕ) × ℕ × Option ℕ) × ℕ => v.1.2.1) :=
        Computable.fst.comp (Computable.snd.comp Computable.fst)
      have p3 : Computable (fun v : ((ℚ × ℕ × ℕ) × ℕ × Option ℕ) × ℕ => v.1.1.2.2) :=
        Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
      have pi : Computable (fun v : ((ℚ × ℕ × ℕ) × ℕ × Option ℕ) × ℕ => v.2) := Computable.snd
      have hst := (computable_shiftStepP has).comp (Computable.pair p1 p2)
      have hx := Computable₂.comp computable₂_ratAdd (hbs.comp pi) hst
      have h := (computable_firstPass hbs).comp (Computable.pair hx p3)
      exact h
    have hIH : Computable (fun z : (ℚ × ℕ × ℕ) × ℕ × Option ℕ => z.2.2) :=
      Computable.snd.comp Computable.snd
    have h := Computable.option_bind hIH hg
    exact h
  have hrec := Computable.nat_rec (σ := Option ℕ)
    (Computable.fst.comp Computable.snd) (Computable.const (some 0)) hstep
  refine hrec.of_eq (fun q => ?_)
  obtain ⟨v, k, t⟩ := q
  have key : ∀ j : ℕ, (Nat.rec (motive := fun _ => Option ℕ) (some 0)
      (fun y IH => IH.bind (fun i => firstPass bs (bs i + shiftStep as v y) t)) j)
      = procIdx as bs v j t := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [procIdx_succ]
        exact congrArg (fun X : Option ℕ =>
          X.bind (fun i => firstPass bs (bs i + shiftStep as v j) t)) ih
  exact key k

attribute [irreducible] procIdx

/-- The first-appearance step is computable jointly in the scale, the step and the bound. -/
theorem computable_procFirstP (has : Computable as) (hbs : Computable bs) :
    Computable (fun q : ℚ × ℕ × ℕ => procFirst as bs q.1 q.2.1 q.2.2) := by
  have hp := computable_procIdxP has hbs
  have hbase : Computable (fun q : ℚ × ℕ × ℕ => procIdx as bs q.1 q.2.1 0) :=
    hp.comp (Computable.pair Computable.fst
      (Computable.pair (Computable.fst.comp Computable.snd) (Computable.const 0)))
  have hstep : Computable₂ (fun (q : ℚ × ℕ × ℕ) (t : ℕ) =>
      cond (procIdx as bs q.1 q.2.1 t).isSome none (procIdx as bs q.1 q.2.1 (t + 1))) := by
    have hq1 : Computable (fun v : (ℚ × ℕ × ℕ) × ℕ => v.1.1) :=
      Computable.fst.comp Computable.fst
    have hq2 : Computable (fun v : (ℚ × ℕ × ℕ) × ℕ => v.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
    have h1 := hp.comp (Computable.pair hq1 (Computable.pair hq2 Computable.snd))
    have h2 := hp.comp (Computable.pair hq1
      (Computable.pair hq2 (Primrec.succ.to_comp.comp Computable.snd)))
    have h := Computable.cond (Primrec.option_isSome.to_comp.comp h1)
      (Computable.const (none : Option ℕ)) h2
    exact h
  have h := Computable.nat_casesOn
    (Computable.snd.comp (Computable.snd : Computable (fun q : ℚ × ℕ × ℕ => q.2))) hbase hstep
  refine h.of_eq (fun q => ?_)
  obtain ⟨v, k, t⟩ := q
  cases t with
  | zero => rfl
  | succ t => rfl

attribute [irreducible] procFirst

/-- The shifted cover is computable jointly in the scale, the budget and the index. -/
theorem computable_shiftCoverP (has : Computable as) (hbs : Computable bs) :
    Computable (fun q : (ℚ × ℚ) × ℕ => shiftCover as bs q.1.1 q.1.2 q.2) := by
  have hk : Computable (fun q : (ℚ × ℚ) × ℕ => (Nat.unpair q.2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have ht : Computable (fun q : (ℚ × ℚ) × ℕ => (Nat.unpair q.2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hfirst := (computable_procFirstP has hbs).comp
    (Computable.pair (Computable.fst.comp Computable.fst) (Computable.pair hk ht))
  have hsome : Computable₂ (fun (q : (ℚ × ℚ) × ℕ) (i : ℕ) =>
      some (bs i, bs i + shiftStep as q.1.1 (Nat.unpair q.2).1 + ratPad q.1.2 q.2)) := by
    have p1 : Computable (fun v : ((ℚ × ℚ) × ℕ) × ℕ => v.1.1.1) :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have p2 : Computable (fun v : ((ℚ × ℚ) × ℕ) × ℕ => v.1.1.2) :=
      Computable.snd.comp (Computable.fst.comp Computable.fst)
    have p3 : Computable (fun v : ((ℚ × ℚ) × ℕ) × ℕ => v.1.2) :=
      Computable.snd.comp Computable.fst
    have pi : Computable (fun v : ((ℚ × ℚ) × ℕ) × ℕ => v.2) := Computable.snd
    have pk : Computable (fun v : ((ℚ × ℚ) × ℕ) × ℕ => (Nat.unpair v.1.2).1) :=
      (Primrec.fst.comp Primrec.unpair).to_comp.comp p3
    have hbi := hbs.comp pi
    have hst := (computable_shiftStepP has).comp (Computable.pair p1 pk)
    have hpad := computable₂_ratPad.comp p2 p3
    have hr := Computable₂.comp computable₂_ratAdd
      (Computable₂.comp computable₂_ratAdd hbi hst) hpad
    have h := Computable.option_some.comp (Computable.pair hbi hr)
    exact h
  exact Computable.option_casesOn hfirst (Computable.const none) hsome

/-! ### The cover catches `β` when the process stalls -/

/-- If the process stalls after its `k`-th index, then `β` is caught by one of the emitted
intervals. -/
theorem mem_shiftCover_of_stall {α β : ℝ} (a : LowerApprox α) (b : LowerApprox β)
    {w ε : ℚ} (hε : 0 < ε) {k t i : ℕ}
    (hi : procIdx a.seq b.seq w k t = some i)
    (hnone : ∀ t', procIdx a.seq b.seq w (k + 1) t' = none) :
    β ∈ ⋃ n, (shiftCover a.seq b.seq w ε n).elim ∅ ratInterval := by
  obtain ⟨t', i', hf⟩ := exists_procFirst hi
  have hii : i' = i := by
    have h1 : procIdx a.seq b.seq w k (max t t') = some i :=
      procIdx_stable hi (le_max_left _ _)
    have h2 : procIdx a.seq b.seq w k (max t t') = some i' :=
      procIdx_stable (procFirst_some hf) (le_max_right _ _)
    exact Option.some.inj (h2.symm.trans h1)
  have hi' : procIdx a.seq b.seq w k t = some i' := by rw [hii]; exact hi
  refine Set.mem_iUnion.mpr ⟨Nat.pair k t', ?_⟩
  have hcov : shiftCover a.seq b.seq w ε (Nat.pair k t')
      = some (b.seq i', b.seq i' + shiftStep a.seq w k + ratPad ε (Nat.pair k t')) := by
    rw [shiftCover, Nat.unpair_pair, hf]
  rw [hcov]
  change β ∈ ratInterval (b.seq i', b.seq i' + shiftStep a.seq w k + ratPad ε (Nat.pair k t'))
  rw [ratInterval]
  refine Set.mem_Ioo.mpr ⟨b.seq_lt i', ?_⟩
  have hle : ∀ j, b.seq j ≤ b.seq i' + shiftStep a.seq w k :=
    fun j => not_lt.mp (le_of_procIdx_none hi' hnone j)
  have hβ : β ≤ ((b.seq i' + shiftStep a.seq w k : ℚ) : ℝ) := by
    refine le_of_tendsto' b.tendsto (fun j => ?_)
    exact_mod_cast hle j
  have hpad : (0 : ℝ) < ((ratPad ε (Nat.pair k t') : ℚ) : ℝ) := by
    exact_mod_cast ratPad_pos hε _
  push_cast at hβ ⊢
  linarith

/-! ### When the process is total -/

/-- A total process has a computable index function `J` returning its successive indices. -/
theorem exists_process_index {α β : ℝ} (a : LowerApprox α) (b : LowerApprox β) (w : ℚ)
    (has : Computable a.seq) (hbs : Computable b.seq)
    (htot : ∀ k, ∃ t i, procIdx a.seq b.seq w k t = some i) :
    ∃ J : ℕ → ℕ, Computable J ∧ ∀ k, ∃ t, procIdx a.seq b.seq w k t = some (J k) := by
  have hdom : ∀ k, (Nat.rfindOpt (fun t => procIdx a.seq b.seq w k t)).Dom := by
    intro k
    obtain ⟨t, i, h⟩ := htot k
    exact Nat.rfindOpt_dom.mpr ⟨t, i, Option.mem_def.mpr h⟩
  have hpartrec : Partrec (fun k => Nat.rfindOpt (fun t => procIdx a.seq b.seq w k t)) := by
    refine Partrec.rfindOpt ?_
    have h := (computable_procIdxP has hbs).comp
      (Computable.pair (Computable.const w)
        (Computable.pair (Computable.fst : Computable (fun q : ℕ × ℕ => q.1))
          (Computable.snd : Computable (fun q : ℕ × ℕ => q.2))))
    exact h
  refine ⟨fun k => (Nat.rfindOpt (fun t => procIdx a.seq b.seq w k t)).get (hdom k),
    computable_of_partrec_total hpartrec hdom, fun k => ?_⟩
  obtain ⟨t, ht⟩ := Nat.rfindOpt_spec (Part.get_mem (hdom k))
  exact ⟨t, Option.mem_def.mp ht⟩

/-- Successive indices of the process advance the approximation by more than the current shift
amount. -/
theorem process_index_lt {α β : ℝ} (a : LowerApprox α) (b : LowerApprox β) {w : ℚ}
    {J : ℕ → ℕ} (hJ : ∀ k, ∃ t, procIdx a.seq b.seq w k t = some (J k)) (k : ℕ) :
    b.seq (J k) + shiftStep a.seq w k < b.seq (J (k + 1)) := by
  obtain ⟨t1, h1⟩ := hJ k
  obtain ⟨t2, h2⟩ := hJ (k + 1)
  exact procIdx_succ_spec (procIdx_stable h1 (le_max_left t1 t2))
    (procIdx_stable h2 (le_max_right t1 t2))

/-! ### The scale attached to a budget, and the resulting effectively null set -/

/-- The scale used at budget `ε` when the increments of `a` sum to at most `K`. -/
def scaleOf (K : ℕ) (ε : ℚ) : ℚ := ε / (2 * (K : ℚ) + 2)

/-- The scale used at a positive budget is positive. -/
theorem scaleOf_pos (K : ℕ) {ε : ℚ} (hε : 0 < ε) : 0 < scaleOf K ε := by
  rw [scaleOf]
  have hD : (0 : ℚ) < 2 * (K : ℚ) + 2 := by positivity
  exact div_pos hε hD

/-- The scale is computable in the budget. -/
theorem computable_scaleOf (K : ℕ) : Computable (scaleOf K) :=
  computable_ratDivConst (c := 2 * (K : ℚ) + 2) (by positivity)

/-- The defining property of the scale: it shrinks `K` below `ε/2`. -/
theorem scaleOf_bound {K : ℕ} {ε : ℚ} (hε : 0 < ε) : (K : ℚ) * scaleOf K ε ≤ ε / 2 := by
  have hD : (0 : ℚ) < 2 * (K : ℚ) + 2 := by positivity
  have key : (K : ℚ) * (ε / (2 * (K : ℚ) + 2))
      = (ε / 2) * ((2 * (K : ℚ)) / (2 * (K : ℚ) + 2)) := by
    field_simp
  rw [scaleOf, key]
  have h1 : (2 * (K : ℚ)) / (2 * (K : ℚ) + 2) ≤ 1 := by
    rw [div_le_one hD]
    linarith
  have h2 : (0 : ℚ) ≤ (2 * (K : ℚ)) / (2 * (K : ℚ) + 2) := by positivity
  nlinarith [hε.le, h1, h2]

/-- If the process stalls at every budget, then `{β}` is an effectively null set of reals. -/
theorem isEffectivelyNullReal_singleton_of_stall {α β : ℝ} (a : LowerApprox α)
    (b : LowerApprox β) {K : ℕ} (hK : α - ((a.seq 0 : ℚ) : ℝ) ≤ (K : ℝ))
    (hstall : ∀ ε : ℚ, 0 < ε → ∃ k t i,
      procIdx a.seq b.seq (scaleOf K ε) k t = some i ∧
      ∀ t', procIdx a.seq b.seq (scaleOf K ε) (k + 1) t' = none) :
    IsEffectivelyNullReal {β} := by
  refine ⟨fun ε n => shiftCover a.seq b.seq (scaleOf K ε) ε n, ?_, fun ε hε => ⟨?_, ?_⟩⟩
  · have h := (computable_shiftCoverP a.isComputable b.isComputable).comp
      (Computable.pair
        (Computable.pair ((computable_scaleOf K).comp Computable.fst) Computable.fst)
        Computable.snd)
    exact h
  · rintro y hy
    have hyβ : y = β := hy
    subst hyβ
    obtain ⟨k, t, i, hi, hnone⟩ := hstall ε hε
    exact mem_shiftCover_of_stall a b hε hi hnone
  · refine le_trans (tsum_length_shiftCover_le a b (scaleOf_pos K hε) hε) ?_
    have hhalf : (α - ((a.seq 0 : ℚ) : ℝ)) * ((scaleOf K ε : ℚ) : ℝ)
        ≤ ((ε : ℚ) : ℝ) / 2 := by
      have h1 : (0 : ℝ) < ((scaleOf K ε : ℚ) : ℝ) := by exact_mod_cast scaleOf_pos K hε
      have h2 : (α - ((a.seq 0 : ℚ) : ℝ)) * ((scaleOf K ε : ℚ) : ℝ)
          ≤ (K : ℝ) * ((scaleOf K ε : ℚ) : ℝ) := mul_le_mul_of_nonneg_right hK h1.le
      have h3 : (K : ℝ) * ((scaleOf K ε : ℚ) : ℝ) ≤ ((ε : ℚ) : ℝ) / 2 := by
        have hq := scaleOf_bound (K := K) hε
        have hc : (((K : ℚ) * scaleOf K ε : ℚ) : ℝ) ≤ (((ε / 2 : ℚ)) : ℝ) := by
          exact_mod_cast hq
        push_cast at hc
        linarith
      linarith
    have hεR : (0 : ℝ) ≤ ((ε : ℚ) : ℝ) / 2 := by
      have : (0 : ℝ) < ((ε : ℚ) : ℝ) := by exact_mod_cast hε
      linarith
    calc ENNReal.ofReal ((α - ((a.seq 0 : ℚ) : ℝ)) * ((scaleOf K ε : ℚ) : ℝ))
          + ENNReal.ofReal (((ε : ℚ) : ℝ) / 2)
        ≤ ENNReal.ofReal (((ε : ℚ) : ℝ) / 2) + ENNReal.ofReal (((ε : ℚ) : ℝ) / 2) :=
          add_le_add (ENNReal.ofReal_le_ofReal hhalf) le_rfl
      _ = ENNReal.ofReal ((ε : ℚ) : ℝ) := by
          rw [← ENNReal.ofReal_add hεR hεR]
          congr 1
          ring

/-- If the process never stalls it is total. -/
theorem total_of_not_stall {α β : ℝ} (a : LowerApprox α) (b : LowerApprox β) {w : ℚ}
    (h : ∀ k t i, procIdx a.seq b.seq w k t = some i →
      ¬ (∀ t', procIdx a.seq b.seq w (k + 1) t' = none)) :
    ∀ k, ∃ t i, procIdx a.seq b.seq w k t = some i := by
  intro k
  induction k with
  | zero => exact ⟨0, 0, procIdx_zero 0⟩
  | succ k ih =>
      obtain ⟨t, i, hi⟩ := ih
      have hne := h k t i hi
      push Not at hne
      obtain ⟨t', ht'⟩ := hne
      rcases hv : procIdx a.seq b.seq w (k + 1) t' with _ | i'
      · exact absurd hv ht'
      · exact ⟨t', i', hv⟩

/-- The lower bound the totality of the process gives: the tail of the shifts sits below
the gap between `β` and the corresponding `b`-value. -/
theorem mul_sub_le_of_process {α β : ℝ} (a : LowerApprox α) (b : LowerApprox β) {w : ℚ}
    (_hw : 0 < w) {J : ℕ → ℕ} (hJ : ∀ k, ∃ t, procIdx a.seq b.seq w k t = some (J k))
    (k : ℕ) : ((w : ℚ) : ℝ) * (α - ((a.seq k : ℚ) : ℝ)) ≤ β - ((b.seq (J k) : ℚ) : ℝ) := by
  have hlt := process_index_lt a b hJ
  have hstep : ∀ m : ℕ, ((a.seq (k + m) : ℚ) : ℝ) * ((w : ℚ) : ℝ)
      ≤ ((b.seq (J (k + m)) : ℚ) : ℝ) - ((b.seq (J k) : ℚ) : ℝ)
        + ((a.seq k : ℚ) : ℝ) * ((w : ℚ) : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have h1 := hlt (k + m)
        have h2 : ((b.seq (J (k + m)) : ℚ) : ℝ)
            + (((a.seq (k + m + 1) - a.seq (k + m)) * w : ℚ) : ℝ)
            < ((b.seq (J (k + m + 1)) : ℚ) : ℝ) := by
          have := h1
          rw [shiftStep] at this
          exact_mod_cast this
        have h3 : ((k + (m + 1) : ℕ)) = k + m + 1 := by ring
        rw [h3]
        push_cast at h2 ⊢
        nlinarith [ih, h2]
  have hlim : ∀ m : ℕ, ((a.seq (k + m) : ℚ) : ℝ) * ((w : ℚ) : ℝ)
      ≤ β - ((b.seq (J k) : ℚ) : ℝ) + ((a.seq k : ℚ) : ℝ) * ((w : ℚ) : ℝ) := by
    intro m
    have h1 := hstep m
    have h2 : ((b.seq (J (k + m)) : ℚ) : ℝ) ≤ β := b.seq_le _
    linarith
  have htend : Filter.Tendsto (fun m => ((a.seq (k + m) : ℚ) : ℝ) * ((w : ℚ) : ℝ))
      Filter.atTop (nhds (α * ((w : ℚ) : ℝ))) := by
    have hshift : Filter.Tendsto (fun m : ℕ => k + m) Filter.atTop Filter.atTop := by
      simpa [Nat.add_comm] using Filter.tendsto_add_atTop_nat k
    have hsub : Filter.Tendsto (fun m => ((a.seq (k + m) : ℚ) : ℝ)) Filter.atTop (nhds α) :=
      a.tendsto.comp hshift
    exact hsub.mul_const _
  have hfin : α * ((w : ℚ) : ℝ)
      ≤ β - ((b.seq (J k) : ℚ) : ℝ) + ((a.seq k : ℚ) : ℝ) * ((w : ℚ) : ℝ) :=
    le_of_tendsto htend (Filter.Eventually.of_forall hlim)
  nlinarith [hfin]

/-- For a total process, the approximation along the process indices converges to `β`. -/
theorem tendsto_process_index {α β : ℝ} (a : LowerApprox α) (b : LowerApprox β) {w : ℚ}
    (hw : 0 < w) {J : ℕ → ℕ} (hJ : ∀ k, ∃ t, procIdx a.seq b.seq w k t = some (J k)) :
    Filter.Tendsto (fun k => ((b.seq (J k) : ℚ) : ℝ)) Filter.atTop (nhds β) := by
  have hlt := process_index_lt a b hJ
  have hmono : StrictMono J := by
    refine strictMono_nat_of_lt_succ (fun k => ?_)
    have h1 := hlt k
    have h2 : 0 < shiftStep a.seq w k := by
      rw [shiftStep]
      have h3 := a.isStrictMono (Nat.lt_succ_self k)
      have hsub : 0 < a.seq (k + 1) - a.seq k := by linarith
      exact mul_pos hsub hw
    have h3 : b.seq (J k) < b.seq (J (k + 1)) := by linarith
    exact b.isStrictMono.lt_iff_lt.mp h3
  exact b.tendsto.comp hmono.tendsto_atTop

end Kolmogorov
