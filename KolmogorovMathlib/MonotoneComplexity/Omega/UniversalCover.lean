/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.LscBasic

/-!
# A universal enumeration of covers by rational intervals (SUV pp. 157–158)

This module builds the enumeration behind "the largest effectively null set of reals"
(SUV p. 157, the parenthetical of the definition of an ML-random real).

`covEnum : ℚ → ℕ → Option (ℚ × ℚ)` is one `Computable₂` family of rational intervals
such that

* for every rational `ε > 0` the total length of `covEnum ε` is at most `ε / 2`
  (`tsum_covLen_covEnum_le`), and
* every `Computable₂` cover `c` whose total length at budget `δ` is at most `δ` appears
  *in full* inside `covEnum ε`, at the sub-budget `δ = covBudget ε e` assigned to a code
  `e` of `c` (`exists_code_covEnum`).

The construction is the standard one: dovetail `Nat.Partrec.Code.evaln` over all codes,
give code `e` the budget `ε / 2 ^ (e + 2)`, keep only the *first* step at which a given
input converges (so that one output is emitted once), and truncate on-line — an interval
is emitted only when the total length emitted so far by the same code, together with the
new interval, still fits in that code's budget.  A genuine cover never triggers the
truncation, because its own total length is within its budget.

Everything here is proved; the module renders no statement of the source.
-/

namespace Kolmogorov

open ENNReal

/-! ### The budget split -/

/-- The budget `ε / 2 ^ (e + 2)` assigned to the code `e` at global budget `ε`.  It is
definitionally `ratPad ε e` of `Omega/Basic.lean`, whose total mass is `ε / 2`. -/
def covBudget (ε : ℚ) (e : ℕ) : ℚ := ε / 2 ^ (e + 2)

/-- The budget assigned to a code is positive when the global budget is. -/
theorem covBudget_pos {ε : ℚ} (hε : 0 < ε) (e : ℕ) : 0 < covBudget ε e := by
  rw [covBudget]; positivity

/-- The budget assigned to a code is nonnegative when the global budget is. -/
theorem covBudget_nonneg {ε : ℚ} (hε : 0 ≤ ε) (e : ℕ) : 0 ≤ covBudget ε e := by
  rw [covBudget]; positivity

/-- The budget split is computable in the global budget and the code. -/
theorem computable₂_covBudget : Computable₂ covBudget := by
  have hden : Computable (fun p : ℚ × ℕ => (1 : ℚ) / 2 ^ (p.2 + 2)) := by
    have hnat : Primrec (fun n : ℕ => 2 ^ (n + 2)) :=
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
        (Primrec.succ.comp Primrec.succ))
    refine computable_of_num_den (N := fun _ : ℚ × ℕ => (1 : ℤ))
      (D := fun p : ℚ × ℕ => 2 ^ (p.2 + 2)) (Computable.const 1)
      (hnat.to_comp.comp Computable.snd) (fun _ => by positivity) (fun p => ?_)
    push_cast
    ring
  refine (Computable₂.comp computable₂_ratMul Computable.fst hden).of_eq (fun p => ?_)
  rw [covBudget]
  ring

/-! ### The length of an optional rational interval -/

/-- The length of an optional interval, clipped at `0`. -/
def covLen (I : Option (ℚ × ℚ)) : ℚ :=
  Option.casesOn (motive := fun _ => ℚ) I 0 (fun J => max 0 (J.2 - J.1))

/-- A missing interval has length zero. -/
@[simp] theorem covLen_none : covLen none = 0 := rfl

/-- The length of a present interval is its width, clipped at zero. -/
@[simp] theorem covLen_some (J : ℚ × ℚ) : covLen (some J) = max 0 (J.2 - J.1) := rfl

/-- Interval lengths are nonnegative. -/
theorem covLen_nonneg (I : Option (ℚ × ℚ)) : 0 ≤ covLen I := by
  cases I with
  | none => exact le_rfl
  | some J => exact le_max_left _ _

/-- The length of an optional interval is computable. -/
theorem computable_covLen : Computable covLen := by
  have hsome : Computable₂ (fun (_ : Option (ℚ × ℚ)) (J : ℚ × ℚ) => max 0 (J.2 - J.1)) := by
    have hsub : Computable (fun z : Option (ℚ × ℚ) × (ℚ × ℚ) => z.2.2 - z.2.1) :=
      Computable₂.comp computable₂_ratSub (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.snd)
    exact Computable₂.comp computable₂_ratMax (Computable.const 0) hsub
  exact Computable.option_casesOn Computable.id (Computable.const 0) hsome

/-! ### Step-bounded evaluation of an arbitrary code -/

/-- The value produced by the code `p.1` on the input `(covBudget p.2 p.1, i)` within
`t` steps of `Nat.Partrec.Code.evaln`, decoded as an optional interval.  The outer
`Option` records convergence, the inner one is the cover's own value. -/
def codeVal (p : ℕ × ℚ) (i t : ℕ) : Option (Option (ℚ × ℚ)) :=
  (Nat.Partrec.Code.evaln t (Denumerable.ofNat Nat.Partrec.Code p.1)
      (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (covBudget p.2 p.1, i))).bind
    (fun v => @Encodable.decode (Option (ℚ × ℚ)) Primcodable.toEncodable v)

/-- The step-bounded value of a code on the budgeted input is computable. -/
theorem computable_codeVal :
    Computable (fun z : (ℕ × ℚ) × ℕ × ℕ => codeVal z.1 z.2.1 z.2.2) := by
  have hcode : Computable (fun z : (ℕ × ℚ) × ℕ × ℕ => Denumerable.ofNat Nat.Partrec.Code z.1.1) :=
    (Primrec.ofNat Nat.Partrec.Code).to_comp.comp (Computable.fst.comp Computable.fst)
  have hbud : Computable (fun z : (ℕ × ℚ) × ℕ × ℕ => covBudget z.1.2 z.1.1) :=
    Computable₂.comp computable₂_covBudget (Computable.snd.comp Computable.fst)
      (Computable.fst.comp Computable.fst)
  have hinp : Computable (fun z : (ℕ × ℚ) × ℕ × ℕ =>
      @Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (covBudget z.1.2 z.1.1, z.2.1)) :=
    Primrec.encode.to_comp.comp (Computable.pair hbud (Computable.fst.comp Computable.snd))
  have hstep : Computable (fun z : (ℕ × ℚ) × ℕ × ℕ => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hev : Computable (fun z : (ℕ × ℚ) × ℕ × ℕ =>
      Nat.Partrec.Code.evaln z.2.2 (Denumerable.ofNat Nat.Partrec.Code z.1.1)
        (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (covBudget z.1.2 z.1.1, z.2.1))) := by
    have h := Nat.Partrec.Code.primrec_evaln.to_comp.comp
      (Computable.pair (Computable.pair hstep hcode) hinp)
    exact h
  exact Computable.option_bind hev (Computable.decode.comp Computable.snd)

/-- Unfolding of the step-bounded value: run `evaln` on the encoded pair of the budget and the
index and decode the result. -/
theorem codeVal_def (p : ℕ × ℚ) (i t : ℕ) : codeVal p i t =
    (Nat.Partrec.Code.evaln t (Denumerable.ofNat Nat.Partrec.Code p.1)
        (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (covBudget p.2 p.1, i))).bind
      (fun v => @Encodable.decode (Option (ℚ × ℚ)) Primcodable.toEncodable v) := rfl

/- `codeVal` is made opaque from here on: every later definitional check would
otherwise unfold it down to the `Decidable` instance of `ℚ` and diverge. -/
attribute [irreducible] codeVal

/-- Flattening a nested option is computable. -/
theorem computable_optJoin {α : Type} [Primcodable α] :
    Computable (fun o : Option (Option α) => o.getD none) :=
  Computable.option_getD Computable.id (Computable.const none)

/-- The interval produced by the code, read as `none` when it has not converged. -/
def codeOut (p : ℕ × ℚ) (i t : ℕ) : Option (ℚ × ℚ) := (codeVal p i t).getD none

/-- Unfolding of the code output: a non-converged evaluation reads as `none`. -/
theorem codeOut_def (p : ℕ × ℚ) (i t : ℕ) : codeOut p i t = (codeVal p i t).getD none := rfl

/-- The code output is computable. -/
theorem computable_codeOut :
    Computable (fun z : (ℕ × ℚ) × ℕ × ℕ => codeOut z.1 z.2.1 z.2.2) := by
  have h := computable_optJoin.comp computable_codeVal
  exact h

/-- The output of the code at the *first* step at which it converges, and `none` at
every other step.  This makes each input contribute at most one emitted interval. -/
def codeFirst (p : ℕ × ℚ) (i t : ℕ) : Option (ℚ × ℚ) :=
  Nat.casesOn (motive := fun _ => Option (ℚ × ℚ)) t (codeOut p i 0)
    (fun t' => cond (codeVal p i t').isSome none (codeOut p i (t' + 1)))

/-- At step zero the first-convergence output is the code output. -/
@[simp] theorem codeFirst_zero (p : ℕ × ℚ) (i : ℕ) :
    codeFirst p i 0 = codeOut p i 0 := rfl

/-- At later steps the first-convergence output is silent once the code has already converged. -/
@[simp] theorem codeFirst_succ (p : ℕ × ℚ) (i t : ℕ) :
    codeFirst p i (t + 1)
      = cond (codeVal p i t).isSome none (codeOut p i (t + 1)) := rfl

/-- The first-convergence output is computable. -/
theorem computable_codeFirst :
    Computable (fun z : (ℕ × ℚ) × ℕ × ℕ => codeFirst z.1 z.2.1 z.2.2) := by
  have hz : Computable (fun z : (ℕ × ℚ) × ℕ × ℕ => (z.1, z.2.1, (0 : ℕ))) :=
    Computable.pair Computable.fst
      (Computable.pair (Computable.fst.comp Computable.snd) (Computable.const 0))
  have hbase := computable_codeOut.comp hz
  have hstep : Computable₂ (fun (z : (ℕ × ℚ) × ℕ × ℕ) (t' : ℕ) =>
      cond (codeVal z.1 z.2.1 t').isSome none (codeOut z.1 z.2.1 (t' + 1))) := by
    have hz1 : Computable (fun w : ((ℕ × ℚ) × ℕ × ℕ) × ℕ => (w.1.1, w.1.2.1, w.2)) :=
      Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
          Computable.snd)
    have hz2 : Computable (fun w : ((ℕ × ℚ) × ℕ × ℕ) × ℕ => (w.1.1, w.1.2.1, w.2 + 1)) :=
      Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
          (Primrec.succ.to_comp.comp Computable.snd))
    have hv1 := computable_codeVal.comp hz1
    have hv2 := computable_codeOut.comp hz2
    have h := Computable.cond (Primrec.option_isSome.to_comp.comp hv1)
      (Computable.const (none : Option (ℚ × ℚ))) hv2
    exact h
  have h := Computable.nat_casesOn
    (Computable.snd.comp Computable.snd : Computable (fun z : (ℕ × ℚ) × ℕ × ℕ => z.2.2))
    hbase hstep
  exact h

attribute [irreducible] codeFirst

/-! ### The truncated enumeration -/

/-- The candidate interval at the flat index `m = ⟨i, t⟩`. -/
def covCand (p : ℕ × ℚ) (m : ℕ) : Option (ℚ × ℚ) :=
  codeFirst p (Nat.unpair m).1 (Nat.unpair m).2

/-- The candidate interval at a flat index is computable. -/
theorem computable_covCand : Computable (fun z : (ℕ × ℚ) × ℕ => covCand z.1 z.2) := by
  have hz : Computable (fun z : (ℕ × ℚ) × ℕ => (z.1, (Nat.unpair z.2).1, (Nat.unpair z.2).2)) :=
    Computable.pair Computable.fst
      (Computable.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
  have h := computable_codeFirst.comp hz
  exact h

/-- The flat index is unpaired into an input index and a step count. -/
theorem covCand_def (p : ℕ × ℚ) (m : ℕ) :
    covCand p m = codeFirst p (Nat.unpair m).1 (Nat.unpair m).2 := rfl

attribute [irreducible] covCand

/-- The on-line truncation test: emitting the candidate at `m` would take the code
`p.1` over its budget. -/
def covOver (p : ℕ × ℚ) (m : ℕ) (acc : ℚ) : Bool :=
  ratLtPair (covBudget p.2 p.1, acc + covLen (covCand p m))

/-- The total length already emitted by the code `p.1` at flat indices `< m`. -/
def covAcc (p : ℕ × ℚ) : ℕ → ℚ
  | 0 => 0
  | m + 1 => covAcc p m + cond (covOver p m (covAcc p m)) 0 (covLen (covCand p m))

/-- The interval actually emitted by the code `p.1` at flat index `m`. -/
def covEmit (p : ℕ × ℚ) (m : ℕ) : Option (ℚ × ℚ) :=
  cond (covOver p m (covAcc p m)) none (covCand p m)

/-- **The universal cover.**  The index `n` decodes as a pair (code, flat index). -/
def covEnum (ε : ℚ) (n : ℕ) : Option (ℚ × ℚ) :=
  covEmit ((Nat.unpair n).1, ε) (Nat.unpair n).2

/-- An emitted interval has the length of the candidate, or zero when the truncation test fires. -/
theorem covLen_covEmit (p : ℕ × ℚ) (m : ℕ) :
    covLen (covEmit p m) = cond (covOver p m (covAcc p m)) 0 (covLen (covCand p m)) := by
  rw [covEmit]
  cases covOver p m (covAcc p m) with
  | false => rw [cond_false, cond_false]
  | true => rw [cond_true, cond_true, covLen_none]

/-- The accumulated length grows by the length of the interval emitted at the current index. -/
theorem covAcc_succ (p : ℕ × ℚ) (m : ℕ) :
    covAcc p (m + 1) = covAcc p m + covLen (covEmit p m) := by
  rw [covLen_covEmit, covAcc]

/-- The accumulated length is nonnegative. -/
theorem covAcc_nonneg (p : ℕ × ℚ) (m : ℕ) : 0 ≤ covAcc p m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
      rw [covAcc_succ]
      have := covLen_nonneg (covEmit p m)
      linarith

/-- The truncation keeps every code inside its own budget. -/
theorem covAcc_le (p : ℕ × ℚ) (hb : 0 ≤ covBudget p.2 p.1) (m : ℕ) :
    covAcc p m ≤ covBudget p.2 p.1 := by
  induction m with
  | zero => exact hb
  | succ m ih =>
      rw [covAcc]
      cases hc : covOver p m (covAcc p m) with
      | true => rw [cond_true, add_zero]; exact ih
      | false =>
          rw [cond_false]
          have h : ¬ (covBudget p.2 p.1 < covAcc p m + covLen (covCand p m)) := by
            rw [covOver, ratLtPair] at hc
            simpa using hc
          linarith [not_lt.mp h]

/-- The accumulated length at `M` is the sum of the lengths emitted at the indices below `M`. -/
theorem sum_range_covLen_covEmit (p : ℕ × ℚ) (M : ℕ) :
    ∑ m ∈ Finset.range M, covLen (covEmit p m) = covAcc p M := by
  induction M with
  | zero => simp [covAcc]
  | succ M ih => rw [Finset.sum_range_succ, ih, covAcc_succ]

/-- Every code stays inside its budget, in total. -/
theorem tsum_covLen_covEmit_le (p : ℕ × ℚ) (hb : 0 ≤ covBudget p.2 p.1) :
    (∑' m, ENNReal.ofReal ((covLen (covEmit p m) : ℚ) : ℝ))
      ≤ ENNReal.ofReal ((covBudget p.2 p.1 : ℚ) : ℝ) := by
  refine ENNReal.tsum_le_of_sum_range_le (fun M => ?_)
  have hnn : ∀ m ∈ Finset.range M, (0 : ℝ) ≤ ((covLen (covEmit p m) : ℚ) : ℝ) :=
    fun m _ => by exact_mod_cast covLen_nonneg (covEmit p m)
  have hcast : (((∑ m ∈ Finset.range M, covLen (covEmit p m) : ℚ)) : ℝ)
      = ∑ m ∈ Finset.range M, ((covLen (covEmit p m) : ℚ) : ℝ) := by push_cast; ring
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← hcast, sum_range_covLen_covEmit]
  refine ENNReal.ofReal_le_ofReal ?_
  exact_mod_cast covAcc_le p hb M

/-! ### Computability of the enumeration -/

/-- The on-line truncation test is computable. -/
theorem computable_covOver :
    Computable (fun w : ((ℕ × ℚ) × ℕ) × ℚ => covOver w.1.1 w.1.2 w.2) := by
  have hbud : Computable (fun w : ((ℕ × ℚ) × ℕ) × ℚ => covBudget w.1.1.2 w.1.1.1) :=
    Computable₂.comp computable₂_covBudget
      (Computable.snd.comp (Computable.fst.comp Computable.fst))
      (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hcand : Computable (fun w : ((ℕ × ℚ) × ℕ) × ℚ => covCand w.1.1 w.1.2) :=
    computable_covCand.comp Computable.fst
  have hsum : Computable (fun w : ((ℕ × ℚ) × ℕ) × ℚ =>
      w.2 + covLen (covCand w.1.1 w.1.2)) :=
    Computable₂.comp computable₂_ratAdd Computable.snd (computable_covLen.comp hcand)
  exact computable_ratLtPair.comp (Computable.pair hbud hsum)

/-- The truncation test compares the code's budget with the accumulated length plus the
candidate. -/
theorem covOver_def (p : ℕ × ℚ) (m : ℕ) (acc : ℚ) :
    covOver p m acc = ratLtPair (covBudget p.2 p.1, acc + covLen (covCand p m)) := rfl

/-- Nothing has been emitted before the first index. -/
theorem covAcc_zero (p : ℕ × ℚ) : covAcc p 0 = 0 := rfl

/-- Unfolding of one step of the accumulated length, before the truncation test is abbreviated. -/
theorem covAcc_succ_raw (p : ℕ × ℚ) (m : ℕ) :
    covAcc p (m + 1)
      = covAcc p m + cond (covOver p m (covAcc p m)) 0 (covLen (covCand p m)) := rfl

/-- Unfolding of the emitted interval: the candidate is dropped exactly when the truncation test
fires. -/
theorem covEmit_def (p : ℕ × ℚ) (m : ℕ) :
    covEmit p m = cond (covOver p m (covAcc p m)) none (covCand p m) := rfl

/-- Unfolding of the universal cover: the index is unpaired into a code and a flat index. -/
theorem covEnum_def (ε : ℚ) (n : ℕ) :
    covEnum ε n = covEmit ((Nat.unpair n).1, ε) (Nat.unpair n).2 := rfl

attribute [irreducible] covOver

/-- The accumulated length is computable. -/
theorem computable_covAcc : Computable (fun z : (ℕ × ℚ) × ℕ => covAcc z.1 z.2) := by
  have hw : Computable (fun s : ((ℕ × ℚ) × ℕ) × ℕ × ℚ => ((s.1.1, s.2.1), s.2.2)) :=
    Computable.pair
      (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  have hover := computable_covOver.comp hw
  have hw2 : Computable (fun s : ((ℕ × ℚ) × ℕ) × ℕ × ℚ => (s.1.1, s.2.1)) :=
    Computable.pair (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
  have hcand := computable_covLen.comp (computable_covCand.comp hw2)
  have hstep : Computable₂ (fun (z : (ℕ × ℚ) × ℕ) (r : ℕ × ℚ) =>
      r.2 + cond (covOver z.1 r.1 r.2) 0 (covLen (covCand z.1 r.1))) := by
    have h := Computable₂.comp computable₂_ratAdd
      (Computable.snd.comp Computable.snd :
        Computable (fun s : ((ℕ × ℚ) × ℕ) × ℕ × ℚ => s.2.2))
      (Computable.cond hover (Computable.const (0 : ℚ)) hcand)
    exact h
  have hrec := Computable.nat_rec (σ := ℚ) Computable.snd (Computable.const 0) hstep
  refine hrec.of_eq (fun z => ?_)
  obtain ⟨p, n⟩ := z
  have key : ∀ M : ℕ, (Nat.rec (motive := fun _ => ℚ) 0
      (fun y IH => IH + cond (covOver p y IH) 0 (covLen (covCand p y))) M) = covAcc p M := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih =>
        simp only [covAcc]
        exact congrArg (fun x : ℚ => x + cond (covOver p M x) 0 (covLen (covCand p M))) ih
  exact key n

attribute [irreducible] covAcc

/-- The emitted interval is computable. -/
theorem computable_covEmit : Computable (fun z : (ℕ × ℚ) × ℕ => covEmit z.1 z.2) := by
  have hover := computable_covOver.comp
    (Computable.pair (Computable.id : Computable (fun z : (ℕ × ℚ) × ℕ => z)) computable_covAcc)
  have h := Computable.cond hover (Computable.const (none : Option (ℚ × ℚ))) computable_covCand
  exact h

attribute [irreducible] covEmit

/-- The universal cover is computable in the budget and the index. -/
theorem computable₂_covEnum : Computable₂ covEnum := by
  have hz : Computable (fun q : ℚ × ℕ => (((Nat.unpair q.2).1, q.1), (Nat.unpair q.2).2)) :=
    Computable.pair
      (Computable.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
        Computable.fst)
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have h := computable_covEmit.comp hz
  exact h

/-! ### The total length of the universal cover -/

/-- The total length of the universal cover at budget `ε` is at most the sum of the budgets
assigned to the individual codes. -/
theorem tsum_covLen_covEnum_le {ε : ℚ} (hε : 0 < ε) :
    (∑' n, ENNReal.ofReal ((covLen (covEnum ε n) : ℚ) : ℝ))
      ≤ ∑' e, ENNReal.ofReal ((covBudget ε e : ℚ) : ℝ) := by
  have h1 : (∑' n, ENNReal.ofReal ((covLen (covEnum ε n) : ℚ) : ℝ))
      = ∑' q : ℕ × ℕ, ENNReal.ofReal ((covLen (covEmit (q.1, ε) q.2) : ℚ) : ℝ) := by
    refine (Equiv.tsum_eq Nat.pairEquiv
      (fun n => ENNReal.ofReal ((covLen (covEnum ε n) : ℚ) : ℝ))).symm.trans ?_
    refine tsum_congr (fun q => ?_)
    obtain ⟨a, b⟩ := q
    have hq : (Nat.pairEquiv (a, b)) = Nat.pair a b := rfl
    simp only [hq, covEnum, Nat.unpair_pair]
  rw [h1, ENNReal.tsum_prod']
  refine ENNReal.tsum_le_tsum (fun e => ?_)
  exact tsum_covLen_covEmit_le (e, ε) (covBudget_nonneg hε.le e)

/-- The budgets sum to `ε / 2`, so the universal cover fits in the global budget. -/
theorem tsum_ofReal_covBudget {ε : ℚ} (hε : 0 < ε) :
    (∑' e : ℕ, ENNReal.ofReal ((covBudget ε e : ℚ) : ℝ))
      = ENNReal.ofReal (((ε : ℚ) : ℝ) / 2) := by
  have hcast : ∀ e : ℕ, ((covBudget ε e : ℚ) : ℝ) = ((ε : ℚ) : ℝ) * ((1 : ℝ) / 2) ^ (e + 2) := by
    intro e
    rw [covBudget]
    push_cast
    rw [div_pow, one_pow]
    ring
  have hgeom : Summable (fun e : ℕ => ((1 : ℝ) / 2) ^ e) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : ∑' e : ℕ, ((1 : ℝ) / 2) ^ e = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hshift : ∀ e : ℕ, ((1 : ℝ) / 2) ^ (e + 2) = ((1 : ℝ) / 2) ^ e * ((1 : ℝ) / 4) := by
    intro e
    rw [pow_add]
    norm_num
  have hs2 : Summable (fun e : ℕ => ((ε : ℚ) : ℝ) * ((1 : ℝ) / 2) ^ (e + 2)) := by
    have h := (hgeom.mul_right ((1 : ℝ) / 4)).mul_left ((ε : ℚ) : ℝ)
    refine h.congr (fun e => ?_)
    rw [hshift e]
  have hval : ∑' e : ℕ, ((ε : ℚ) : ℝ) * ((1 : ℝ) / 2) ^ (e + 2) = ((ε : ℚ) : ℝ) / 2 := by
    rw [tsum_congr (fun e => by rw [hshift e]), tsum_mul_left, hgeom.tsum_mul_right, hsum]
    ring
  rw [tsum_congr (fun e => congrArg ENNReal.ofReal (hcast e)),
    ← ENNReal.ofReal_tsum_of_nonneg (fun e => by positivity) hs2, hval]

/-! ### Completeness of the enumeration -/

/-- Decoded value of `codeVal` matches the function evaluated by code `cd`. -/
private theorem codeVal_eq_some_of_eval {q : ℕ × ℚ} {cd : Nat.Partrec.Code} {B : ℚ}
    {c_B : ℕ → Option (ℚ × ℚ)} (hcd : Denumerable.ofNat Nat.Partrec.Code q.1 = cd)
    (hB : covBudget q.2 q.1 = B)
    (heval : ∀ i : ℕ, Nat.Partrec.Code.eval cd
      (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (B, i))
      = Part.some (@Encodable.encode (Option (ℚ × ℚ)) Primcodable.toEncodable (c_B i)))
    (i t : ℕ) (w : Option (ℚ × ℚ)) (hw : codeVal q i t = some w) : w = c_B i := by
  rw [codeVal_def, hB, hcd] at hw
  rcases hev : Nat.Partrec.Code.evaln t cd
      (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (B, i)) with _ | v
  · rw [hev] at hw; exact absurd hw (by simp)
  · rw [hev] at hw
    have hw' : (@Encodable.decode (Option (ℚ × ℚ)) Primcodable.toEncodable v) = some w := hw
    have hmem : v ∈ Nat.Partrec.Code.eval cd
        (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (B, i)) :=
      Nat.Partrec.Code.evaln_complete.mpr ⟨t, Option.mem_def.mpr hev⟩
    rw [heval i] at hmem
    rw [Part.mem_some_iff.mp hmem,
      @Encodable.encodek (Option (ℚ × ℚ)) Primcodable.toEncodable] at hw'
    exact (Option.some.inj hw').symm

/-- Monotonicity of `codeVal` once the underlying code evaluation converges. -/
private theorem codeVal_mono_of_evaln {q : ℕ × ℚ} {cd : Nat.Partrec.Code} {B : ℚ}
    (hcd : Denumerable.ofNat Nat.Partrec.Code q.1 = cd) (hB : covBudget q.2 q.1 = B)
    {i t t' : ℕ} (hte : t' ≤ t)
    (hev : (Nat.Partrec.Code.evaln t' cd
      (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (B, i))).isSome = true) :
    codeVal q i t = codeVal q i t' := by
  rcases hv : Nat.Partrec.Code.evaln t' cd
      (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (B, i)) with _ | v
  · rw [hv] at hev; exact absurd hev (by simp)
  · have hmono := Option.mem_def.mp
      (Nat.Partrec.Code.evaln_mono hte (Option.mem_def.mpr hv))
    rw [codeVal_def, hB, hcd, hmono, codeVal_def, hB, hcd, hv]

/-- `T` is the first-convergence schedule of the code `q` with values `c_B`: the code is
undefined at every step before `T i`, takes the value `c_B i` at step `T i`, and keeps that
value at every later step. -/
private def CodeFirstSchedule (q : ℕ × ℚ) (T : ℕ → ℕ) (c_B : ℕ → Option (ℚ × ℚ)) : Prop :=
  (∀ i t, t < T i → codeVal q i t = none) ∧
    (∀ i, codeVal q i (T i) = some (c_B i)) ∧
    (∀ i t, T i ≤ t → codeVal q i t = codeVal q i (T i))

/-- At the first convergence step `T i`, `codeFirst` yields `c_B i`. -/
private theorem codeFirst_at_first_step {q : ℕ × ℚ} {T : ℕ → ℕ} {c_B : ℕ → Option (ℚ × ℚ)}
    (hTval : ∀ i, codeVal q i (T i) = some (c_B i))
    (hTmin : ∀ i t, t < T i → codeVal q i t = none) (i : ℕ) :
    codeFirst q i (T i) = c_B i := by
  rcases hTi : T i with _ | t'
  · have hv : codeVal q i 0 = some (c_B i) := hTi ▸ hTval i
    rw [codeFirst_zero, codeOut_def, hv]
    rfl
  · have hv0 : codeVal q i t' = none := hTmin i t' (by omega)
    have hv : codeVal q i (t' + 1) = some (c_B i) := hTi ▸ hTval i
    rw [codeFirst_succ, hv0, Option.isSome_none, cond_false, codeOut_def, hv]
    rfl

/-- At steps other than `T i`, `codeFirst` yields `none`. -/
private theorem codeFirst_of_ne {q : ℕ × ℚ} {T : ℕ → ℕ} {c_B : ℕ → Option (ℚ × ℚ)}
    (hsched : CodeFirstSchedule q T c_B)
    {i t : ℕ} (ht : t ≠ T i) : codeFirst q i t = none := by
  obtain ⟨hTmin, hTval, hmonoVal⟩ := hsched
  have hTspec : ∀ i, (codeVal q i (T i)).isSome = true := by
    intro i; rw [hTval i]; rfl
  rcases Nat.lt_or_ge t (T i) with hlt | hge
  · rcases t with _ | t'
    · rw [codeFirst_zero, codeOut_def, hTmin i 0 hlt]
      rfl
    · rw [codeFirst_succ, hTmin i t' (by omega), Option.isSome_none, cond_false,
        codeOut_def, hTmin i (t' + 1) hlt]
      rfl
  · have hgt : T i < t := lt_of_le_of_ne hge (fun hcc => ht hcc.symm)
    rcases t with _ | t'
    · exact absurd hgt (Nat.not_lt_zero _)
    · rw [codeFirst_succ, hmonoVal i t' (by omega), hTspec i, cond_true]

/-- The candidate family of `q` is concentrated on the sparse index set of the pairs
`Nat.pair i (T i)`, where it takes the value `c_B i`; at every other index it is undefined. -/
private def CovCandSparse (q : ℕ × ℚ) (T : ℕ → ℕ) (c_B : ℕ → Option (ℚ × ℚ)) : Prop :=
  (∀ i, covCand q (Nat.pair i (T i)) = c_B i) ∧
    ∀ m, (∀ i, m ≠ Nat.pair i (T i)) → covCand q m = none

/-- The total candidate length is bounded by the budget when candidates are
concentrated on an injective sequence of indices with sum bounded by the budget. -/
private theorem tsum_covLen_covCand_le_of_sparse {q : ℕ × ℚ} {B : ℚ} (T : ℕ → ℕ)
    (c_B : ℕ → Option (ℚ × ℚ)) (hsparse : CovCandSparse q T c_B)
    (hlenB : (∑' i, ENNReal.ofReal ((covLen (c_B i) : ℚ) : ℝ)) ≤ ENNReal.ofReal ((B : ℚ) : ℝ)) :
    (∑' m, ENNReal.ofReal ((covLen (covCand q m) : ℚ) : ℝ)) ≤ ENNReal.ofReal ((B : ℚ) : ℝ) := by
  obtain ⟨hCandT, hCandNe⟩ := hsparse
  have hinj : Function.Injective (fun i => Nat.pair i (T i)) := by
    intro x y hxy
    have hxy' : Nat.pair x (T x) = Nat.pair y (T y) := hxy
    have h1 : (Nat.unpair (Nat.pair x (T x))).1 = (Nat.unpair (Nat.pair y (T y))).1 := by
      rw [hxy']
    rwa [Nat.unpair_pair, Nat.unpair_pair] at h1
  have hsupp : Function.support (fun m => ENNReal.ofReal ((covLen (covCand q m) : ℚ) : ℝ))
      ⊆ Set.range (fun i => Nat.pair i (T i)) := by
    intro m hm
    by_contra hcon
    have hz : covCand q m = none := hCandNe m (fun i hcc => hcon ⟨i, hcc.symm⟩)
    have hzero : ENNReal.ofReal ((covLen (covCand q m) : ℚ) : ℝ) = 0 := by rw [hz]; simp
    exact hm hzero
  rw [← hinj.tsum_eq hsupp, tsum_congr (fun i => by rw [hCandT i])]
  exact hlenB

/-- The finite range sum of candidate lengths is bounded by the budget if the tsum is. -/
private theorem sum_range_covLen_covCand_le {q : ℕ × ℚ} {B : ℚ} (hBpos : 0 < B)
    (hcandle : (∑' m, ENNReal.ofReal ((covLen (covCand q m) : ℚ) : ℝ))
      ≤ ENNReal.ofReal ((B : ℚ) : ℝ)) (M : ℕ) :
    ∑ m ∈ Finset.range M, covLen (covCand q m) ≤ B := by
  have hnn : ∀ m ∈ Finset.range M, (0 : ℝ) ≤ ((covLen (covCand q m) : ℚ) : ℝ) :=
    fun m _ => by exact_mod_cast covLen_nonneg (covCand q m)
  have hcast : (((∑ m ∈ Finset.range M, covLen (covCand q m) : ℚ)) : ℝ)
      = ∑ m ∈ Finset.range M, ((covLen (covCand q m) : ℚ) : ℝ) := by push_cast; ring
  have hle : ENNReal.ofReal (((∑ m ∈ Finset.range M, covLen (covCand q m) : ℚ)) : ℝ)
      ≤ ENNReal.ofReal ((B : ℚ) : ℝ) := by
    rw [hcast, ENNReal.ofReal_sum_of_nonneg hnn]
    exact le_trans (ENNReal.sum_le_tsum _) hcandle
  have hBR : (0 : ℝ) ≤ ((B : ℚ) : ℝ) := by exact_mod_cast hBpos.le
  have hq2 := (ENNReal.ofReal_le_ofReal_iff hBR).mp hle
  exact_mod_cast hq2

/-- If the sum of candidate lengths in every finite range is bounded by the budget,
the truncation test never fires and `covAcc` equals the sum of candidate lengths. -/
private theorem covOver_eq_false_of_sum_le (p : ℕ × ℚ)
    (hsumle : ∀ M : ℕ, ∑ m ∈ Finset.range M, covLen (covCand p m) ≤ covBudget p.2 p.1) (m : ℕ) :
    covOver p m (covAcc p m) = false ∧
      covAcc p m = ∑ m' ∈ Finset.range m, covLen (covCand p m') := by
  induction m with
  | zero =>
      have hacc0 : covAcc p 0 = ∑ m' ∈ Finset.range 0, covLen (covCand p m') := by
        rw [covAcc_zero, Finset.sum_range_zero]
      have hnf : covOver p 0 (covAcc p 0) = false := by
        rw [covOver_def, hacc0, Finset.sum_range_zero, ratLtPair, decide_eq_false_iff_not,
          not_lt, zero_add]
        have h1 := hsumle 1
        rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h1
        exact h1
      exact ⟨hnf, hacc0⟩
  | succ m ih =>
      obtain ⟨hnf_m, hacc_m⟩ := ih
      have hacc_succ : covAcc p (m + 1) = ∑ m' ∈ Finset.range (m + 1), covLen (covCand p m') := by
        rw [covAcc_succ_raw, hnf_m, cond_false, hacc_m, Finset.sum_range_succ]
      have hnf_succ : covOver p (m + 1) (covAcc p (m + 1)) = false := by
        rw [covOver_def, ratLtPair, decide_eq_false_iff_not, not_lt, hacc_succ]
        have h1 := hsumle (m + 2)
        rw [Finset.sum_range_succ] at h1
        exact h1
      exact ⟨hnf_succ, hacc_succ⟩

/-- **Every effective cover appears in full inside the universal enumeration.**  If `c`
is a `Computable₂` family of intervals whose total length at any budget it is run with is
at most that budget, then at every global budget `ε > 0` there is a sub-budget `δ > 0`
such that every interval of `c δ` is an interval of `covEnum ε`. -/
theorem exists_code_covEnum {c : ℚ → ℕ → Option (ℚ × ℚ)} (hc : Computable₂ c)
    (hlen : ∀ δ : ℚ, 0 < δ →
      (∑' i, ENNReal.ofReal ((covLen (c δ i) : ℚ) : ℝ)) ≤ ENNReal.ofReal ((δ : ℚ) : ℝ))
    {ε : ℚ} (hε : 0 < ε) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ i, ∃ n, covEnum ε n = c δ i := by
  classical
  obtain ⟨cd, hcd⟩ := Nat.Partrec.Code.exists_code.mp hc
  obtain ⟨e₀, hcode⟩ : ∃ e : ℕ, Denumerable.ofNat Nat.Partrec.Code e = cd :=
    ⟨Encodable.encode cd, Denumerable.ofNat_encode cd⟩
  set B : ℚ := covBudget ε e₀ with hB
  set q : ℕ × ℚ := (e₀, ε) with hq
  have hBpos : 0 < B := by rw [hB]; exact covBudget_pos hε e₀
  have hq1 : q.1 = e₀ := by rw [hq]
  have hqB : covBudget q.2 q.1 = B := by rw [hq, hB]
  have heval : ∀ i : ℕ, Nat.Partrec.Code.eval cd
      (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (B, i))
      = Part.some (@Encodable.encode (Option (ℚ × ℚ)) Primcodable.toEncodable (c B i)) := by
    intro i
    simp only [hcd]
    rw [@Encodable.encodek (ℚ × ℕ) Primcodable.toEncodable]
    simp
  have hconvSome : ∀ i : ℕ, ∃ t : ℕ, (codeVal q i t).isSome = true := by
    intro i
    have hmem : (@Encodable.encode (Option (ℚ × ℚ)) Primcodable.toEncodable (c B i))
        ∈ Nat.Partrec.Code.eval cd
          (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (B, i)) := by
      rw [heval i]; exact Part.mem_some _
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
    refine ⟨t, ?_⟩
    have hvv : codeVal q i t = some (c B i) := by
      rw [codeVal_def, hqB, hq1, hcode, Option.mem_def.mp ht]
      exact @Encodable.encodek (Option (ℚ × ℚ)) Primcodable.toEncodable _
    rw [hvv]
    rfl
  set T : ℕ → ℕ := fun i => Nat.find (hconvSome i) with hTdef
  have hTspec : ∀ i, (codeVal q i (T i)).isSome = true := fun i => Nat.find_spec (hconvSome i)
  have hTmin : ∀ i t, t < T i → codeVal q i t = none := by
    intro i t ht
    have hns := Nat.find_min (hconvSome i) ht
    rcases hv : codeVal q i t with _ | w
    · rfl
    · exact absurd (by rw [hv]; rfl : (codeVal q i t).isSome = true) hns
  have hTval : ∀ i, codeVal q i (T i) = some (c B i) := by
    intro i
    rcases hv : codeVal q i (T i) with _ | w
    · have hs := hTspec i; rw [hv] at hs; exact absurd hs (by simp)
    · rw [codeVal_eq_some_of_eval hcode hqB heval i (T i) w hv]
  have hmonoVal : ∀ i t, T i ≤ t → codeVal q i t = codeVal q i (T i) := fun i t hle => by
    rcases hev : Nat.Partrec.Code.evaln (T i) cd
        (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (B, i)) with _ | v
    · have h1 := hTspec i; rw [codeVal_def, hqB, hq1, hcode, hev] at h1; exact absurd h1 (by simp)
    · exact codeVal_mono_of_evaln hcode hqB hle (by rw [hev]; rfl)
  have hsched : CodeFirstSchedule q T (c B) := ⟨hTmin, hTval, hmonoVal⟩
  have hFirstT : ∀ i, codeFirst q i (T i) = c B i :=
    codeFirst_at_first_step hsched.2.1 hsched.1
  have hFirstNe : ∀ i t, t ≠ T i → codeFirst q i t = none := fun _ _ ht =>
    codeFirst_of_ne hsched ht
  have hCandT : ∀ i, covCand q (Nat.pair i (T i)) = c B i := by
    intro i
    rw [covCand_def, Nat.unpair_pair]
    exact hFirstT i
  have hCandNe : ∀ m, (∀ i, m ≠ Nat.pair i (T i)) → covCand q m = none := by
    intro m hm
    rw [covCand_def]
    refine hFirstNe _ _ (fun hcc => ?_)
    exact hm (Nat.unpair m).1 (by rw [← hcc, Nat.pair_unpair])
  have hcandle := tsum_covLen_covCand_le_of_sparse T (c B) ⟨hCandT, hCandNe⟩ (hlen B hBpos)
  have hsumle : ∀ M : ℕ, ∑ m ∈ Finset.range M, covLen (covCand q m) ≤ covBudget q.2 q.1 := by
    rw [hqB]
    exact sum_range_covLen_covCand_le hBpos hcandle
  have hnofire : ∀ m, covOver q m (covAcc q m) = false := fun m =>
    (covOver_eq_false_of_sum_le q hsumle m).1
  refine ⟨B, hBpos, fun i => ⟨Nat.pair e₀ (Nat.pair i (T i)), ?_⟩⟩
  have hqq : ((e₀ : ℕ), ε) = q := hq.symm
  rw [covEnum_def, Nat.unpair_pair, hqq, covEmit_def, hnofire (Nat.pair i (T i)), cond_false,
    hCandT i]

end Kolmogorov
