/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import Mathlib.Computability.Halting

/-!
# Computable toolkit for SUV Section 5.7

This module collects the small, **fully proved** computability and analysis
facts that the `Ω` / Solovay cluster of SUV Section 5.7 (Shen–Uspensky–
Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness*, pp. 157–172)
needs over and over.  Nothing here renders a statement of the source; every
declaration is infrastructure.

* `invSucc` — the computable rational null sequence `n ↦ 1/(n+1)`, used for the
  "subtract a null sequence" normalisations of p. 158 (a non-decreasing
  approximation becomes a strictly increasing one).
* `ratRunMax` — the running maximum of a computable rational sequence, the
  standard way to turn an arbitrary computable approximation into a
  *non-decreasing* one (p. 158).
* `ratSearchPair` — the reduction function of p. 158: on input `r` search for the
  first stage `n` at which the approximation `b` of `β` passes `r`, and answer
  with the corresponding term `a n` of the approximation of `α`.  This is the
  partial computable object behind every `≼₁` witness in `Omega/Solovay.lean`.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The computable null sequence `1/(n+1)` -/

/-- The computable rational null sequence `n ↦ 1/(n+1)`. -/
def invSucc (n : ℕ) : ℚ := 1 / ((n : ℚ) + 1)

/-- The sequence `n ↦ 1 / (n + 1)` is computable. -/
theorem computable_invSucc : Computable invSucc := by
  refine computable_of_num_den (f := invSucc) (N := fun _ : ℕ => (1 : ℤ))
    (D := fun n : ℕ => n + 1) (Computable.const 1) (Primrec.succ.to_comp)
    (fun n => n.succ_pos) (fun n => ?_)
  simp only [invSucc]
  push_cast
  ring

/-- The sequence `n ↦ 1 / (n + 1)` is positive. -/
theorem invSucc_pos (n : ℕ) : 0 < invSucc n := by
  have : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  simpa [invSucc] using div_pos one_pos this

/-- The sequence `n ↦ 1 / (n + 1)` strictly decreases at every step. -/
theorem invSucc_succ_lt (n : ℕ) : invSucc (n + 1) < invSucc n := by
  have h0 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have h1 : ((n : ℚ) + 1) < ((n : ℚ) + 1 + 1) := by linarith
  have := one_div_lt_one_div_of_lt h0 h1
  simpa [invSucc] using this

/-- The sequence `n ↦ 1 / (n + 1)` is antitone. -/
theorem invSucc_antitone : Antitone invSucc :=
  antitone_nat_of_succ_le fun n => (invSucc_succ_lt n).le

/-- `1/(n+1) → 0` in `ℝ`. -/
theorem tendsto_invSucc :
    Filter.Tendsto (fun n : ℕ => ((invSucc n : ℚ) : ℝ)) Filter.atTop (nhds 0) := by
  have h : (fun n : ℕ => ((invSucc n : ℚ) : ℝ)) = fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    funext n; simp [invSucc]
  rw [h]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ### Computable maxima of rationals -/

/-- Strict comparison of a pair of rationals, packaged as a *named* `Bool`-valued
function.  Composing `Computable` facts through a named function keeps the
`Decidable (· < ·)` instance of `ℚ` opaque; unfolding it inside a unification
problem is what makes `Computable₂.comp` diverge here. -/
def ratLtPair (p : ℚ × ℚ) : Bool := decide (p.1 < p.2)

/-- Strict comparison of a pair of rationals is computable. -/
theorem computable_ratLtPair : Computable ratLtPair := computable₂_ratLt

/-- The maximum of two rationals is computable in both arguments. -/
theorem computable₂_ratMax : Computable₂ (fun a b : ℚ => max a b) :=
  (primrec₂_max_of_le ComputableReals.primrec_ratLe).to_comp

/-- The **running maximum** `max (f 0) … (f n)` of a rational sequence. -/
def ratRunMax (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => f 0
  | n + 1 => max (ratRunMax f n) (f (n + 1))

/-- The running maximum at zero is the first term. -/
@[simp] theorem ratRunMax_zero (f : ℕ → ℚ) : ratRunMax f 0 = f 0 := rfl

/-- One step of the running maximum takes the maximum with the next term. -/
@[simp] theorem ratRunMax_succ (f : ℕ → ℚ) (n : ℕ) :
    ratRunMax f (n + 1) = max (ratRunMax f n) (f (n + 1)) := rfl

/-- The running maximum of a computable rational sequence is computable. -/
theorem computable_ratRunMax {f : ℕ → ℚ} (hf : Computable f) : Computable (ratRunMax f) := by
  have hh : Computable₂ (fun (_ : ℕ) (p : ℕ × ℚ) => max p.2 (f (p.1 + 1))) := by
    have h1 : Computable (fun q : ℕ × ℕ × ℚ => q.2.2) := Computable.snd.comp Computable.snd
    have h2 : Computable (fun q : ℕ × ℕ × ℚ => f (q.2.1 + 1)) :=
      hf.comp (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
    exact Computable₂.comp computable₂_ratMax h1 h2
  have hrec := Computable.nat_rec (σ := ℚ) Computable.id (Computable.const (f 0)) hh
  refine hrec.of_eq (fun n => ?_)
  induction n with
  | zero => rfl
  | succ n ih => simpa using congrArg (fun x => max x (f (n + 1))) ih

/-- The running maximum is non-decreasing. -/
theorem monotone_ratRunMax (f : ℕ → ℚ) : Monotone (ratRunMax f) :=
  monotone_nat_of_le_succ fun n => by simp

/-- Every term is at most the running maximum at its index. -/
theorem le_ratRunMax (f : ℕ → ℚ) (n : ℕ) : f n ≤ ratRunMax f n := by
  cases n with
  | zero => simp
  | succ n => simp

/-- A bound valid for every term bounds the running maximum. -/
theorem ratRunMax_le {f : ℕ → ℚ} {c : ℚ} (h : ∀ k, f k ≤ c) (n : ℕ) : ratRunMax f n ≤ c := by
  induction n with
  | zero => simpa using h 0
  | succ n ih => simp only [ratRunMax_succ, max_le_iff]; exact ⟨ih, h (n + 1)⟩

/-- If a rational sequence stays below its real limit, its running maximum has the
same limit.  This is the standard "make an approximation non-decreasing" step. -/
theorem tendsto_ratRunMax {f : ℕ → ℚ} {L : ℝ}
    (hlim : Filter.Tendsto (fun n => ((f n : ℚ) : ℝ)) Filter.atTop (nhds L))
    (hle : ∀ n, ((f n : ℚ) : ℝ) ≤ L) :
    Filter.Tendsto (fun n => ((ratRunMax f n : ℚ) : ℝ)) Filter.atTop (nhds L) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
    (fun n => ?_) (fun n => ?_)
  · exact Rat.cast_le.mpr (le_ratRunMax f n)
  · induction n with
    | zero => simpa using hle 0
    | succ n ih =>
        rw [ratRunMax_succ]
        rcases max_cases (ratRunMax f n) (f (n + 1)) with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he]; exact ih
        · rw [he]; exact hle (n + 1)

/-! ### The `≼₁` search: first stage at which an approximation passes a rational -/

/-- **SUV p. 158, the reduction function.** Given approximations `a` of `α` and `b`
of `β`, the partial computable map sending a rational `r` to `a n`, where `n` is the
first stage with `r < b n`. -/
def ratSearchPair (a b : ℕ → ℚ) (r : ℚ) : Part ℚ :=
  Nat.rfindOpt (fun n => if r < b n then some (a n) else none)

/-- The reduction function built from two computable rational approximations is partial
recursive. -/
theorem partrec_ratSearchPair {a b : ℕ → ℚ} (ha : Computable a) (hb : Computable b) :
    Partrec (ratSearchPair a b) := by
  have hpair : Computable (fun p : ℚ × ℕ => ((p.1, b p.2) : ℚ × ℚ)) :=
    Computable.pair Computable.fst (hb.comp Computable.snd)
  have hlt : Computable (fun p : ℚ × ℕ => ratLtPair (p.1, b p.2)) :=
    computable_ratLtPair.comp hpair
  have hc : Computable (fun p : ℚ × ℕ =>
      cond (ratLtPair (p.1, b p.2)) (some (a p.2)) none) :=
    Computable.cond hlt (Computable.option_some.comp (ha.comp Computable.snd))
      (Computable.const none)
  have hc' : Computable₂ (fun (r : ℚ) (n : ℕ) => if r < b n then some (a n) else none) := by
    refine hc.of_eq (fun p => ?_)
    simp only [ratLtPair, Bool.cond_decide]
  exact Partrec.rfindOpt hc'

/-- A value of the reduction function at `r` is a term `a n` at a stage where `r < b n`. -/
theorem mem_ratSearchPair {a b : ℕ → ℚ} {r q : ℚ} (h : q ∈ ratSearchPair a b r) :
    ∃ n, r < b n ∧ q = a n := by
  rw [ratSearchPair] at h
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec h
  by_cases hb : r < b n
  · rw [if_pos hb] at hn
    exact ⟨n, hb, Eq.symm (by simpa using hn)⟩
  · rw [if_neg hb] at hn
    exact absurd hn (by simp)

/-- The reduction function converges at `r` as soon as some `b n` exceeds `r`. -/
theorem ratSearchPair_dom {a b : ℕ → ℚ} {r : ℚ} (h : ∃ n, r < b n) :
    (ratSearchPair a b r).Dom := by
  obtain ⟨n, hn⟩ := h
  rw [ratSearchPair]
  exact Nat.rfindOpt_dom.2 ⟨n, a n, by simp [hn]⟩

/-- The **index** version of `ratSearchPair`: the first stage `n` with `r < b n`. -/
def ratSearchIndex (b : ℕ → ℚ) (r : ℚ) : Part ℕ :=
  Nat.rfindOpt (fun n => if r < b n then some n else none)

/-- The stage-index search is partial recursive. -/
theorem partrec_ratSearchIndex {b : ℕ → ℚ} (hb : Computable b) :
    Partrec (ratSearchIndex b) := by
  have hpair : Computable (fun p : ℚ × ℕ => ((p.1, b p.2) : ℚ × ℚ)) :=
    Computable.pair Computable.fst (hb.comp Computable.snd)
  have hlt : Computable (fun p : ℚ × ℕ => ratLtPair (p.1, b p.2)) :=
    computable_ratLtPair.comp hpair
  have hc : Computable (fun p : ℚ × ℕ =>
      cond (ratLtPair (p.1, b p.2)) (some p.2) none) :=
    Computable.cond hlt (Computable.option_some.comp Computable.snd) (Computable.const none)
  have hc' : Computable₂ (fun (r : ℚ) (n : ℕ) => if r < b n then some n else none) := by
    refine hc.of_eq (fun p => ?_)
    simp only [ratLtPair, Bool.cond_decide]
  exact Partrec.rfindOpt hc'

/-- The stage returned by the index search does satisfy `r < b n`. -/
theorem mem_ratSearchIndex {b : ℕ → ℚ} {r : ℚ} {n : ℕ} (h : n ∈ ratSearchIndex b r) :
    r < b n := by
  rw [ratSearchIndex] at h
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec h
  by_cases hb : r < b k
  · rw [if_pos hb] at hk
    have hnk : n = k := Eq.symm (by simpa using hk)
    rwa [hnk]
  · rw [if_neg hb] at hk
    exact absurd hk (by simp)

/-- The index search converges at `r` as soon as some `b n` exceeds `r`. -/
theorem ratSearchIndex_dom {b : ℕ → ℚ} {r : ℚ} (h : ∃ n, r < b n) :
    (ratSearchIndex b r).Dom := by
  obtain ⟨n, hn⟩ := h
  rw [ratSearchIndex]
  exact Nat.rfindOpt_dom.2 ⟨n, n, by simp [hn]⟩

/-! ### Partial sums of a computable rational series -/

/-- `∑_{i < n} u i`, in the recursive shape `Computable.nat_rec` accepts. -/
def ratRangeSum (u : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => ratRangeSum u n + u n

/-- The recursively defined partial sum agrees with the sum over `Finset.range`. -/
theorem ratRangeSum_eq (u : ℕ → ℚ) (n : ℕ) :
    ratRangeSum u n = ∑ i ∈ Finset.range n, u i := by
  induction n with
  | zero => simp [ratRangeSum]
  | succ n ih => rw [ratRangeSum, ih, Finset.sum_range_succ]

/-- Partial sums of a computable rational sequence are computable. -/
theorem computable_ratRangeSum {u : ℕ → ℚ} (hu : Computable u) :
    Computable (ratRangeSum u) := by
  have hh : Computable₂ (fun (_ : ℕ) (p : ℕ × ℚ) => p.2 + u p.1) := by
    have h1 : Computable (fun q : ℕ × ℕ × ℚ => q.2.2) := Computable.snd.comp Computable.snd
    have h2 : Computable (fun q : ℕ × ℕ × ℚ => u q.2.1) :=
      hu.comp (Computable.fst.comp Computable.snd)
    exact Computable₂.comp computable₂_ratAdd h1 h2
  have hrec := Computable.nat_rec (σ := ℚ) Computable.id (Computable.const 0) hh
  refine hrec.of_eq (fun n => ?_)
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [ratRangeSum]
      exact congrArg (fun x => x + u n) ih

/-! ### Stage-parameterised natural partial sums -/

/-- `∑_{n < k} g s n`, in the recursive shape `Computable.nat_rec` accepts.  The stage
`s` is carried as the recursion *parameter*, so the diagonal `s ↦ natRangeSum g s s`
— the stage-`s` numerator of a diagonal sum of an `IsLSC` family — is computable. -/
def natRangeSum (g : ℕ → ℕ → ℕ) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => natRangeSum g s k + g s k

/-- The recursively defined stagewise partial sum agrees with the sum over `Finset.range`. -/
theorem natRangeSum_eq (g : ℕ → ℕ → ℕ) (s k : ℕ) :
    natRangeSum g s k = ∑ n ∈ Finset.range k, g s n := by
  induction k with
  | zero => simp [natRangeSum]
  | succ k ih => rw [natRangeSum, ih, Finset.sum_range_succ]

/-- The diagonal `s ↦ ∑_{n < s} g s n` of a computable family is computable. -/
theorem computable_natRangeSum_diag {g : ℕ → ℕ → ℕ}
    (hg : Computable (fun p : ℕ × ℕ => g p.1 p.2)) :
    Computable (fun s : ℕ => natRangeSum g s s) := by
  have hh : Computable₂ (fun (s : ℕ) (p : ℕ × ℕ) => p.2 + g s p.1) := by
    have h1 : Computable (fun q : ℕ × ℕ × ℕ => q.2.2) := Computable.snd.comp Computable.snd
    have h2 : Computable (fun q : ℕ × ℕ × ℕ => g q.1 q.2.1) :=
      hg.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
    exact Computable₂.comp (Primrec.nat_add.to_comp) h1 h2
  have hrec := Computable.nat_rec (σ := ℕ) Computable.id (Computable.const 0) hh
  refine hrec.of_eq (fun s => ?_)
  have key : ∀ k : ℕ, Nat.rec (motive := fun _ => ℕ) 0 (fun y IH => IH + g s y) k
      = natRangeSum g s k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [natRangeSum]
        exact congrArg (fun x => x + g s k) ih
  exact key s

/-- The minimum of two rationals is computable in both arguments. -/
theorem computable₂_ratMin : Computable₂ (fun a b : ℚ => min a b) :=
  (primrec₂_min_of_le ComputableReals.primrec_ratLe).to_comp

/-- A running maximum of terms all strictly below a real bound stays strictly below it. -/
theorem ratRunMax_lt_real {f : ℕ → ℚ} {c : ℝ} (h : ∀ k, ((f k : ℚ) : ℝ) < c) (n : ℕ) :
    ((ratRunMax f n : ℚ) : ℝ) < c := by
  induction n with
  | zero => simpa using h 0
  | succ n ih =>
      rw [ratRunMax_succ]
      rcases max_cases (ratRunMax f n) (f (n + 1)) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he]; exact ih
      · rw [he]; exact h (n + 1)

/-! ### Increments of a rational sequence -/

/-- The increments of a rational sequence: the series whose partial sums recover it.
This is the passage between "increasing approximation" and "series" of SUV p. 159. -/
def increments (c : ℕ → ℚ) : ℕ → ℚ
  | 0 => c 0
  | i + 1 => c (i + 1) - c i

/-- The zeroth increment of a sequence is its first value. -/
@[simp] theorem increments_zero (c : ℕ → ℚ) : increments c 0 = c 0 := rfl

/-- Later increments are the successive differences of the sequence. -/
@[simp] theorem increments_succ (c : ℕ → ℚ) (i : ℕ) :
    increments c (i + 1) = c (i + 1) - c i := rfl

/-- The increments telescope: the first `n + 1` of them sum to `c n`. -/
theorem sum_range_increments (c : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), increments c i = c n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, increments_succ]
      ring

/-- The increments of a computable sequence are computable. -/
theorem computable_increments {c : ℕ → ℚ} (hc : Computable c) : Computable (increments c) := by
  have hh : Computable₂ (fun (_ : ℕ) (j : ℕ) => c (j + 1) - c j) := by
    have h1 : Computable (fun q : ℕ × ℕ => c (q.2 + 1)) :=
      hc.comp (Primrec.succ.to_comp.comp Computable.snd)
    have h2 : Computable (fun q : ℕ × ℕ => c q.2) := hc.comp Computable.snd
    exact Computable₂.comp computable₂_ratSub h1 h2
  refine (Computable.nat_casesOn Computable.id (Computable.const (c 0)) hh).of_eq (fun n => ?_)
  cases n with
  | zero => rfl
  | succ n => rfl

/-! ### The capped approximation of SUV p. 159 -/

/-- `cappedApprox A v` follows the approximation `A` but is never allowed to grow by
more than `v` in one step.  This is the device that turns `α ≼₁ β` into a pair of series
with `uᵢ ≤ vᵢ` (SUV p. 159, "the reverse statement is also true"). -/
def cappedApprox (A v : ℕ → ℚ) : ℕ → ℚ
  | 0 => A 0
  | i + 1 => min (A (i + 1)) (cappedApprox A v i + v (i + 1))

/-- The capped approximation starts at the value of the approximation it follows. -/
@[simp] theorem cappedApprox_zero (A v : ℕ → ℚ) : cappedApprox A v 0 = A 0 := rfl

/-- One step of the capped approximation takes the smaller of the target value and the previous
value increased by the allowance. -/
@[simp] theorem cappedApprox_succ (A v : ℕ → ℚ) (i : ℕ) :
    cappedApprox A v (i + 1) = min (A (i + 1)) (cappedApprox A v i + v (i + 1)) := rfl

/-- The capped approximation never exceeds the approximation it follows. -/
theorem cappedApprox_le {A v : ℕ → ℚ} (i : ℕ) : cappedApprox A v i ≤ A i := by
  cases i with
  | zero => exact le_rfl
  | succ i => exact min_le_left _ _

/-- The capped approximation of computable data is computable. -/
theorem computable_cappedApprox {A v : ℕ → ℚ} (hA : Computable A) (hv : Computable v) :
    Computable (cappedApprox A v) := by
  have hh : Computable₂ (fun (_ : ℕ) (p : ℕ × ℚ) =>
      min (A (p.1 + 1)) (p.2 + v (p.1 + 1))) := by
    have hsucc : Computable (fun q : ℕ × ℕ × ℚ => q.2.1 + 1) :=
      Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)
    have h1 : Computable (fun q : ℕ × ℕ × ℚ => A (q.2.1 + 1)) := hA.comp hsucc
    have h2 : Computable (fun q : ℕ × ℕ × ℚ => q.2.2 + v (q.2.1 + 1)) :=
      Computable₂.comp computable₂_ratAdd (Computable.snd.comp Computable.snd) (hv.comp hsucc)
    exact Computable₂.comp computable₂_ratMin h1 h2
  have hrec := Computable.nat_rec (σ := ℚ) Computable.id (Computable.const (A 0)) hh
  refine hrec.of_eq (fun n => ?_)
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [cappedApprox_succ]
      exact congrArg (fun x => min (A (n + 1)) (x + v (n + 1))) ih

/-! ### Observed prefixes of a rational sequence -/

/-- The list `[a 0, …, a n]` of the first `n+1` values of a sequence — the history the
observer of SUV p. 161 has seen at step `n` — in the recursive shape
`Computable.nat_rec` accepts. -/
def listPrefix (a : ℕ → ℚ) : ℕ → List ℚ
  | 0 => [a 0]
  | n + 1 => listPrefix a n ++ [a (n + 1)]

/-- The history of a sequence up to `n` is the list of its values on `List.range (n + 1)`. -/
theorem listPrefix_eq (a : ℕ → ℚ) (n : ℕ) : listPrefix a n = (List.range (n + 1)).map a := by
  induction n with
  | zero => simp [listPrefix]
  | succ n ih =>
      rw [listPrefix, ih, List.range_succ (n := n + 1), List.map_append]
      rfl

/-- The history of a computable sequence is computable. -/
theorem computable_listPrefix {a : ℕ → ℚ} (ha : Computable a) : Computable (listPrefix a) := by
  have hh : Computable₂ (fun (_ : ℕ) (p : ℕ × List ℚ) => p.2 ++ [a (p.1 + 1)]) := by
    have h1 : Computable (fun q : ℕ × ℕ × List ℚ => q.2.2) := Computable.snd.comp Computable.snd
    have h3 : Computable (fun q : ℕ × ℕ × List ℚ => a (q.2.1 + 1)) :=
      ha.comp (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
    have h2 : Computable (fun q : ℕ × ℕ × List ℚ => [a (q.2.1 + 1)]) :=
      Computable₂.comp (Primrec.list_cons.to_comp) h3 (Computable.const [])
    exact Computable₂.comp (Primrec.list_append.to_comp) h1 h2
  have hrec := Computable.nat_rec (σ := List ℚ) Computable.id (Computable.const [a 0]) hh
  refine hrec.of_eq (fun n => ?_)
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [listPrefix]
      exact congrArg (fun x => x ++ [a (n + 1)]) ih

/-! ### Dyadic values -/

/-- The dyadic value of a finite sum of numerators is the sum of the dyadic values. -/
theorem dyadicValue_sum (f : ℕ → ℕ) (t s : ℕ) :
    dyadicValue (∑ n ∈ Finset.range t, f n) s
      = ∑ n ∈ Finset.range t, dyadicValue (f n) s := by
  simp only [dyadicValue, div_eq_mul_inv, ← Finset.sum_mul]
  congr 1
  push_cast
  rfl


/-- The dyadic value of the numerator `2 ^ s` at stage `s` is `1`. -/
theorem dyadicValue_two_pow_self (s : ℕ) : dyadicValue (2 ^ s) s = 1 :=
  dyadicValue_two_pow_eq_one s

/-- The dyadic value is monotone in its numerator. -/
theorem dyadicValue_le_of_le {a b s : ℕ} (h : a ≤ b) : dyadicValue a s ≤ dyadicValue b s :=
  dyadicValue_mono_num h s

/-- A dyadic value is finite. -/
theorem dyadicValue_ne_top (n s : ℕ) : dyadicValue n s ≠ ⊤ := (dyadicValue_lt_top n s).ne

/-- The real value of `dyadicValue n s` is `n / 2 ^ s`. -/
theorem toReal_dyadicValue (n s : ℕ) : (dyadicValue n s).toReal = (n : ℝ) / 2 ^ s := by
  rw [dyadicValue, ENNReal.toReal_div]
  simp

/-- The extended-nonnegative value of the real `n / 2 ^ s` is `dyadicValue n s`. -/
theorem ofReal_toReal_dyadicValue (n s : ℕ) :
    ENNReal.ofReal ((n : ℝ) / 2 ^ s) = dyadicValue n s := by
  rw [← toReal_dyadicValue, ENNReal.ofReal_toReal (dyadicValue_ne_top n s)]

/-- `ratDyadicFloor` of a nonnegative rational is the natural floor of `q · 2^s`. -/
theorem ratDyadicFloor_eq_natFloor {q : ℚ} (hq : 0 ≤ q) (s : ℕ) :
    ratDyadicFloor q s = ⌊q * ((2 ^ s : ℕ) : ℚ)⌋₊ := by
  set r : ℚ := q * ((2 ^ s : ℕ) : ℚ) with hrdef
  have hrnn : (0 : ℚ) ≤ r := by rw [hrdef]; positivity
  have hnum : 0 ≤ r.num := Rat.num_nonneg.2 hrnn
  have hN : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg hnum
  have hfl : (⌊r⌋₊ : ℤ) = r.num / (r.den : ℤ) := by
    rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.2 hrnn), Rat.floor_def']
  have hd : (r.num.toNat / r.den : ℕ) = ⌊r⌋₊ := by
    have h2 : ((r.num.toNat / r.den : ℕ) : ℤ) = (r.num.toNat : ℤ) / ((r.den : ℕ) : ℤ) :=
      Int.natCast_div _ _
    have h3 : ((r.num.toNat / r.den : ℕ) : ℤ) = ((⌊r⌋₊ : ℕ) : ℤ) := by
      rw [h2, hN, hfl]
    exact_mod_cast h3
  rw [ratDyadicFloor_eq, hd]

/-- Extracting a total computable function from an everywhere-defined partial
computable one. -/
theorem computable_of_partrec_total {α σ : Type} [Primcodable α] [Primcodable σ]
    {f : α →. σ} (hf : Partrec f) (hdom : ∀ a, (f a).Dom) :
    Computable (fun a => (f a).get (hdom a)) :=
  Partrec.of_eq hf (fun a => (Part.some_get (hdom a)).symm)

/-! ### Step-bounded evaluation of a partial computable rational function -/

/-- **Step-bounded evaluator.**  Every partial computable `p : ℚ →. ℚ` is the pointwise
limit of a `Computable₂` family `E : ℚ → ℕ → Option ℚ` monotone in the step count:
`Nat.Partrec.Code.exists_code` plus `evaln`.  This is what lets a *cover enumerator*
dovetail the reduction function of SUV p. 158, which is only partial. -/
theorem exists_stepEval_of_partrec {p : ℚ →. ℚ} (hp : Partrec p) :
    ∃ E : ℚ → ℕ → Option ℚ, Computable₂ E ∧
      (∀ (r : ℚ) (s t : ℕ) (q : ℚ), s ≤ t → E r s = some q → E r t = some q) ∧
      (∀ r q : ℚ, q ∈ p r ↔ ∃ s, E r s = some q) := by
  -- The `Encodable ℚ` instance must be the one `Partrec` itself uses
  -- (`Primcodable.toEncodable`), not the one instance search finds (`Rat.instEncodable`).
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  have hevalr : ∀ r : ℚ,
      Nat.Partrec.Code.eval c (@Encodable.encode ℚ Primcodable.toEncodable r)
        = Part.map (@Encodable.encode ℚ Primcodable.toEncodable) (p r) := by
    intro r
    simp only [hc]
    rw [@Encodable.encodek ℚ Primcodable.toEncodable]
    simp
  refine ⟨fun r s => (Nat.Partrec.Code.evaln s c
      (@Encodable.encode ℚ Primcodable.toEncodable r)).bind
    (fun m => @Encodable.decode ℚ Primcodable.toEncodable m), ?_, ?_, ?_⟩
  · have hsnd : Primrec (fun x : ℚ × ℕ => x.2) := Primrec.snd
    have hfst : Primrec (fun x : ℚ × ℕ => x.1) := Primrec.fst
    have h_prim := Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair hsnd (Primrec.const c)) (Primrec.encode.comp hfst))
    exact Computable.option_bind (Primrec.to_comp h_prim)
      (Computable.decode.comp Computable.snd)
  · intro r s t q hst h
    simp only at h ⊢
    rcases hev : Nat.Partrec.Code.evaln s c
        (@Encodable.encode ℚ Primcodable.toEncodable r) with _ | m
    · rw [hev] at h; simp at h
    · have hmono : Nat.Partrec.Code.evaln t c
          (@Encodable.encode ℚ Primcodable.toEncodable r) = some m :=
        Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hst (Option.mem_def.mpr hev))
      rw [hev] at h
      rw [hmono]
      exact h
  · intro r q
    simp only
    constructor
    · intro hq
      have hmem : (@Encodable.encode ℚ Primcodable.toEncodable q)
          ∈ Nat.Partrec.Code.eval c (@Encodable.encode ℚ Primcodable.toEncodable r) := by
        rw [hevalr r]
        exact Part.mem_map _ hq
      obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
      refine ⟨s, ?_⟩
      rw [Option.mem_def.mp hs]
      simp only [Option.bind]
      exact @Encodable.encodek ℚ Primcodable.toEncodable q
    · rintro ⟨s, hs⟩
      rcases hev : Nat.Partrec.Code.evaln s c
          (@Encodable.encode ℚ Primcodable.toEncodable r) with _ | m
      · rw [hev] at hs; simp at hs
      · rw [hev] at hs
        have hdec : (@Encodable.decode ℚ Primcodable.toEncodable m) = some q := hs
        have hmem : m ∈ Nat.Partrec.Code.eval c
            (@Encodable.encode ℚ Primcodable.toEncodable r) :=
          Nat.Partrec.Code.evaln_complete.mpr ⟨s, Option.mem_def.mpr hev⟩
        rw [hevalr r] at hmem
        obtain ⟨x, hx, hxm⟩ := (Part.mem_map_iff _).mp hmem
        have hxq : x = q := by
          have hd2 : (@Encodable.decode ℚ Primcodable.toEncodable
              (@Encodable.encode ℚ Primcodable.toEncodable x)) = some q := by
            rw [hxm]; exact hdec
          rw [@Encodable.encodek ℚ Primcodable.toEncodable] at hd2
          exact Option.some_injective _ hd2
        rwa [← hxq]

/-- The **first-convergence filter** of a step-bounded evaluator: `stepFirst E l s` is
`E l s` when the evaluation converges at step `s` *for the first time*, and `none`
otherwise.  It fires at most once (`stepFirst_unique`), which is what lets a dovetailed
enumeration of intervals keep the total length of the family it transports. -/
def stepFirst (E : ℚ → ℕ → Option ℚ) (l : ℚ) : ℕ → Option ℚ
  | 0 => E l 0
  | s + 1 => cond (E l s).isSome none (E l (s + 1))

/-- The first-convergence filter at step zero passes the evaluator's value through. -/
@[simp] theorem stepFirst_zero (E : ℚ → ℕ → Option ℚ) (l : ℚ) : stepFirst E l 0 = E l 0 := rfl

/-- At a later step the filter fires only if the evaluator had not yet converged. -/
@[simp] theorem stepFirst_succ (E : ℚ → ℕ → Option ℚ) (l : ℚ) (s : ℕ) :
    stepFirst E l (s + 1) = cond (E l s).isSome none (E l (s + 1)) := rfl

/-- A value passed by the filter is a value of the evaluator at the same step. -/
theorem stepFirst_le {E : ℚ → ℕ → Option ℚ} {l : ℚ} {s : ℕ} {q : ℚ}
    (h : stepFirst E l s = some q) : E l s = some q := by
  cases s with
  | zero => exact h
  | succ s =>
      rw [stepFirst_succ] at h
      cases hb : (E l s).isSome with
      | false => rwa [hb] at h
      | true => rw [hb] at h; exact absurd h (by simp)

/-- For a monotone evaluator, the filter is silent at every step after the first convergence. -/
theorem stepFirst_eq_none_of_lt {E : ℚ → ℕ → Option ℚ}
    (hmono : ∀ (r : ℚ) (s t : ℕ) (q : ℚ), s ≤ t → E r s = some q → E r t = some q)
    {l : ℚ} {s t : ℕ} {q : ℚ} (hst : s < t) (hs : E l s = some q) :
    stepFirst E l t = none := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have ht' : E l t' = some q := hmono l s t' q (by omega) hs
  rw [stepFirst_succ, ht']
  rfl

/-- For a monotone evaluator, the filter fires at most at one step. -/
theorem stepFirst_unique {E : ℚ → ℕ → Option ℚ}
    (hmono : ∀ (r : ℚ) (s t : ℕ) (q : ℚ), s ≤ t → E r s = some q → E r t = some q)
    {l : ℚ} {s t : ℕ} {q q' : ℚ}
    (hs : stepFirst E l s = some q) (ht : stepFirst E l t = some q') : s = t := by
  by_contra hne
  rcases Nat.lt_or_ge s t with hlt | hge
  · rw [stepFirst_eq_none_of_lt hmono hlt (stepFirst_le hs)] at ht
    exact absurd ht (by simp)
  · have hlt : t < s := lt_of_le_of_ne hge (fun hh => hne hh.symm)
    rw [stepFirst_eq_none_of_lt hmono hlt (stepFirst_le ht)] at hs
    exact absurd hs (by simp)

/-- For a monotone evaluator, every value the evaluator ever takes is passed by the filter at
some step. -/
theorem exists_stepFirst {E : ℚ → ℕ → Option ℚ}
    (hmono : ∀ (r : ℚ) (s t : ℕ) (q : ℚ), s ≤ t → E r s = some q → E r t = some q)
    {l q : ℚ} (h : ∃ s, E l s = some q) : ∃ s, stepFirst E l s = some q := by
  classical
  obtain ⟨s0, hs0⟩ := h
  have hex : ∃ s, (E l s).isSome = true := ⟨s0, by simp [hs0]⟩
  have hm : (E l (Nat.find hex)).isSome = true := Nat.find_spec hex
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp hm
  have h1 : E l (max (Nat.find hex) s0) = some q' :=
    hmono l _ _ q' (le_max_left _ _) hq'
  have h2 : E l (max (Nat.find hex) s0) = some q :=
    hmono l _ _ q (le_max_right _ _) hs0
  have hqq : q' = q := by
    rw [h1] at h2
    exact Option.some_injective _ h2
  subst hqq
  refine ⟨Nat.find hex, ?_⟩
  rcases hf : Nat.find hex with _ | m
  · rw [hf] at hq'; simpa using hq'
  · have hmin : ¬ (E l m).isSome = true := by
      have := Nat.find_min hex (m := m) (by omega)
      exact this
    have hnone : (E l m).isSome = false := by
      cases hb : (E l m).isSome with
      | false => rfl
      | true => exact absurd hb hmin
    rw [hf] at hq'
    rw [stepFirst_succ, hnone]
    exact hq'

/-- The first-convergence filter of a computable evaluator is computable. -/
theorem computable_stepFirst {E : ℚ → ℕ → Option ℚ} (hE : Computable₂ E) :
    Computable (fun x : ℚ × ℕ => stepFirst E x.1 x.2) := by
  have hE' : Computable (fun y : ℚ × ℕ => E y.1 y.2) := hE
  have hg : Computable (fun x : ℚ × ℕ => E x.1 0) :=
    hE'.comp (Computable.pair Computable.fst (Computable.const 0))
  have hA : Computable (fun y : (ℚ × ℕ) × ℕ => E y.1.1 y.2) :=
    hE'.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  have hB : Computable (fun y : (ℚ × ℕ) × ℕ => E y.1.1 (y.2 + 1)) :=
    hE'.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Primrec.succ.to_comp.comp Computable.snd))
  have hcond : Computable (fun y : (ℚ × ℕ) × ℕ => (E y.1.1 y.2).isSome) :=
    (Primrec.to_comp Primrec.option_isSome).comp hA
  have hh : Computable₂ (fun (x : ℚ × ℕ) (s : ℕ) =>
      cond (E x.1 s).isSome none (E x.1 (s + 1))) :=
    Computable.cond hcond (Computable.const none) hB
  refine (Computable.nat_casesOn Computable.snd hg hh).of_eq (fun x => ?_)
  obtain ⟨l, s⟩ := x
  cases s with
  | zero => rfl
  | succ s => rfl

/-! ### Passing a rational: a convergent rational sequence eventually exceeds
every rational strictly below its limit -/

/-- A rational strictly below the limit of a convergent rational sequence is exceeded by some
term. -/
theorem exists_rat_lt_of_tendsto {β : ℝ} {b : ℕ → ℚ}
    (hb : Filter.Tendsto (fun n => ((b n : ℚ) : ℝ)) Filter.atTop (nhds β))
    {r : ℚ} (hr : (r : ℝ) < β) : ∃ n, r < b n := by
  by_contra h
  push Not at h
  have hle : β ≤ (r : ℝ) := le_of_tendsto' hb (fun n => by exact_mod_cast h n)
  linarith

end Kolmogorov
