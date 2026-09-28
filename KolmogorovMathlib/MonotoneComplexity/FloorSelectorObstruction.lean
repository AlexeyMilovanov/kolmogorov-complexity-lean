import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasureEnumeration
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import KolmogorovMathlib.MonotoneComplexity.MeasureRepresentation

/-!
# The exact dyadic floor interface for computable measures is not attainable

`IsFloorComputableMeasure μ` (in `AlgorithmicRandomness/ComputableMeasure.lean`,
the historical floor-selector strengthening of the faithful two-sided
`IsComputableMeasure`) asks for a *computable dyadic floor selector*: a
computable `a : BitString → ℕ → ℕ` with

  `a x s / 2^s ≤ μ[x] ≤ a x s / 2^s + 1 / 2^s`   for all `x`, `s`.

This is strictly stronger than the two-sided ("Cauchy") notion `IsComputableENNReal`
used elsewhere in the project: the admissible `a x s` are the integers in the
half-open window `[2^s·μ[x] − 1, 2^s·μ[x]]`, which pins `a x s = ⌊2^s·μ[x]⌋`
whenever `2^s·μ[x] ∉ ℕ`.

This file shows that the representation statement

  *every exactly additive lower-semicomputable continuous semimeasure is the
  cylinder-mass function of a measure satisfying `IsFloorComputableMeasure`*

is **false**, by exhibiting an exactly additive lower-semicomputable continuous
semimeasure whose dyadic floors uniformly compute a separator of the computably
inseparable pair `{e : φ_e(e) = 0}`, `{e : φ_e(e) = 1}`.

The construction is a binary tree of masses
`hardTree x = ω(x) · 2^{-|x|}` where the weight `ω` equals `1` except below the
nodes `1^e 0`, whose two children carry the weights `1 ± δ_e` with

* `δ_e > 0` if `φ_e(e) = 0`,
* `δ_e < 0` if `φ_e(e) = 1`,
* `δ_e = 0` otherwise.

A floor selector evaluated at the node `1^e 0 0` with precision `s = e + 2` then
decides the sign of `δ_e`.
-/

namespace Kolmogorov

open scoped ENNReal
open MeasureTheory

/-! ### A computably inseparable diagonal pair -/

/-- Step-`t` evaluation of the `e`-th partial recursive function on input `e`. -/
def diagEvaln (e t : ℕ) : Option ℕ :=
  Nat.Partrec.Code.evaln t (Denumerable.ofNat Nat.Partrec.Code e) e

/-- `φ_e(e)` has been seen to converge to `0` within `t` steps. -/
def sawZero (e t : ℕ) : Bool := diagEvaln e t == some 0

/-- `φ_e(e)` has been seen to converge to `1` within `t` steps. -/
def sawOne (e t : ℕ) : Bool := diagEvaln e t == some 1

/-- The diagonal set `{e : φ_e(e) = 0}`. -/
def DiagZero (e : ℕ) : Prop := 0 ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval e

/-- The diagonal set `{e : φ_e(e) = 1}`. -/
def DiagOne (e : ℕ) : Prop := 1 ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval e

/-- The step-bounded diagonal evaluation is primitive recursive. -/
lemma primrec_diagEvaln : Primrec (fun p : ℕ × ℕ => diagEvaln p.1 p.2) :=
  Nat.Partrec.Code.primrec_evaln.comp
    ((Primrec.snd.pair ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.fst)).pair Primrec.fst)

/-- Having seen the diagonal value zero persists at later steps. -/
lemma sawZero_mono {e t t' : ℕ} (h : t ≤ t') (hs : sawZero e t = true) :
    sawZero e t' = true := by
  simp only [sawZero, beq_iff_eq] at hs ⊢
  exact Nat.Partrec.Code.evaln_mono h hs

/-- Having seen the diagonal value one persists at later steps. -/
lemma sawOne_mono {e t t' : ℕ} (h : t ≤ t') (hs : sawOne e t = true) : sawOne e t' = true := by
  simp only [sawOne, beq_iff_eq] at hs ⊢
  exact Nat.Partrec.Code.evaln_mono h hs

/-- The two diagonal observations exclude each other. -/
lemma not_sawZero_sawOne {e t t' : ℕ} (h0 : sawZero e t = true) (h1 : sawOne e t' = true) :
    False := by
  simp only [sawZero, sawOne, beq_iff_eq] at h0 h1
  have m0 : (0 : ℕ) ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval e :=
    Nat.Partrec.Code.evaln_sound h0
  have m1 : (1 : ℕ) ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval e :=
    Nat.Partrec.Code.evaln_sound h1
  exact absurd (Part.mem_unique m0 m1) (by norm_num)

/-- If the diagonal value is zero, it is seen to be zero at some step. -/
lemma exists_sawZero_of_diagZero {e : ℕ} (h : DiagZero e) : ∃ t, sawZero e t = true := by
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp h
  exact ⟨t, by simpa [sawZero, diagEvaln] using ht⟩

/-- If the diagonal value is one, it is seen to be one at some step. -/
lemma exists_sawOne_of_diagOne {e : ℕ} (h : DiagOne e) : ∃ t, sawOne e t = true := by
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp h
  exact ⟨t, by simpa [sawOne, diagEvaln] using ht⟩

/-- The diagonal pair `{e : φ_e(e) = 0}`, `{e : φ_e(e) = 1}` is computably inseparable. -/
theorem no_computable_diagonal_separator {S : ℕ → Bool} (hS : Computable S)
    (h0 : ∀ e, DiagZero e → S e = true) (h1 : ∀ e, DiagOne e → S e = false) : False := by
  have hcomp : Computable (fun e : ℕ => if S e then 1 else 0) :=
    (Computable.cond hS (Computable.const 1) (Computable.const 0)).of_eq
      (fun e => by cases h : S e <;> simp)
  have hg : Nat.Partrec (fun e : ℕ => (Part.some (if S e then 1 else 0) : Part ℕ)) := by
    rw [← Partrec.nat_iff]
    exact hcomp.partrec
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  have hoc : Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c) = c :=
    Denumerable.ofNat_encode c
  set e := Encodable.encode c with he
  by_cases hSe : S e = true
  · have hmem : DiagOne e := by
      unfold DiagOne
      rw [hoc, hc]; simp [hSe]
    have := h1 e hmem
    simp [hSe] at this
  · simp only [Bool.not_eq_true] at hSe
    have hmem : DiagZero e := by
      unfold DiagZero
      rw [hoc, hc]; simp [hSe]
    have := h0 e hmem
    simp [hSe] at this

/-! ### Stage numerators -/

/-- `sawNum v e k = ∑_{t < k} [φ_e(e) seen to be `v` within `t` steps] · 2^{k-1-t}`. -/
def sawNum (v e : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * sawNum v e k + (if diagEvaln e k == some v then 1 else 0)

/-- The observation numerator, written as a plain recursion on the number of steps. -/
lemma sawNum_eq_rec (v e k : ℕ) :
    sawNum v e k =
      Nat.rec 0 (fun n IH => 2 * IH + (if diagEvaln e n == some v then 1 else 0)) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [sawNum, ih]

/-- The observation numerator is primitive recursive. -/
lemma primrec_sawNum (v : ℕ) : Primrec (fun p : ℕ × ℕ => sawNum v p.1 p.2) := by
  have hbit : Primrec (fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
      if diagEvaln q.1.1 q.2.1 == some v then 1 else 0) := by
    have h1 : Primrec (fun q : (ℕ × ℕ) × (ℕ × ℕ) => diagEvaln q.1.1 q.2.1) :=
      primrec_diagEvaln.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
    have h2 : PrimrecPred
        (fun q : (ℕ × ℕ) × (ℕ × ℕ) => diagEvaln q.1.1 q.2.1 = some v) :=
      Primrec.eq.comp h1 (Primrec.const (some v))
    exact (Primrec.ite h2 (Primrec.const 1) (Primrec.const 0)).of_eq (by
      intro q; by_cases h : diagEvaln q.1.1 q.2.1 = some v <;> simp [h])
  have hmul : Primrec (fun q : (ℕ × ℕ) × (ℕ × ℕ) => 2 * q.2.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂ (fun (p : ℕ × ℕ) (q : ℕ × ℕ) =>
      2 * q.2 + (if diagEvaln p.1 q.1 == some v then 1 else 0)) :=
    Primrec.nat_add.comp hmul hbit
  have hrec := Primrec.nat_rec' (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ : ℕ × ℕ => (0 : ℕ))
    Primrec.snd (Primrec.const 0) hstep
  exact hrec.of_eq (fun p => (sawNum_eq_rec v p.1 p.2).symm)

/-- The observation numerator at precision `k` is below `2 ^ k`. -/
lemma sawNum_lt (v e k : ℕ) : sawNum v e k < 2 ^ k := by
  induction k with
  | zero => simp [sawNum]
  | succ k ih =>
    simp only [sawNum, pow_succ]
    split <;> omega

/-- The observation numerator at least doubles from one precision to the next. -/
lemma two_mul_sawNum_le (v e k : ℕ) : 2 * sawNum v e k ≤ sawNum v e (k + 1) := by
  simp only [sawNum]
  omega

/-- If the diagonal value is never observed, the numerator stays zero. -/
lemma sawNum_eq_zero_of_never {v e : ℕ} (h : ∀ t, diagEvaln e t ≠ some v) (k : ℕ) :
    sawNum v e k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [sawNum, ih]
    simp [h k]

/-- Two sightings after the first one make the numerator at least `2`. -/
lemma two_le_sawNum {v e t : ℕ} (ht : diagEvaln e t = some v) : 2 ≤ sawNum v e (t + 2) := by
  have h1 : 1 ≤ sawNum v e (t + 1) := by
    simp only [sawNum, ht]
    simp
  have h2 : 2 * sawNum v e (t + 1) ≤ sawNum v e (t + 2) := two_mul_sawNum_le v e (t + 1)
  omega

/-- Once a sighting has occurred at time `t`, the numerator grows geometrically. -/
lemma pow_le_sawNum {v e t : ℕ} (hmono : ∀ t', t ≤ t' → diagEvaln e t' = some v)
    (ht : diagEvaln e t = some v) {k : ℕ} (hk : t + 1 ≤ k) :
    2 ^ (k - t - 1) ≤ sawNum v e k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge (t + 1) (k + 1) with h | h
    · have hk' : t + 1 ≤ k := by omega
      have := ih hk'
      have hstep := two_mul_sawNum_le v e k
      have : 2 ^ (k + 1 - t - 1) = 2 * 2 ^ (k - t - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
    · have hkt : k = t := by omega
      subst hkt
      simp only [sawNum, ht]
      simp

/-! ### The perturbed weights -/

/-- Numerator (at denominator `2^{k+3}`) of the stage-`k` lower approximation to the
weight `1 + δ_e` of the node `1^e 0 0`. -/
def hardPlusNum (e k : ℕ) : ℕ := 2 ^ (k + 3) + sawNum 0 e k - sawNum 1 e k - 1

/-- Numerator (at denominator `2^{k+3}`) of the stage-`k` lower approximation to the
weight `1 - δ_e` of the node `1^e 0 1`. -/
def hardMinusNum (e k : ℕ) : ℕ := 2 ^ (k + 3) + sawNum 1 e k - sawNum 0 e k - 1

/-- The observation numerator at precision `k` is below `2 ^ (k + 3)`. -/
lemma sawNum_lt_pow_add_three (v e k : ℕ) : sawNum v e k < 2 ^ (k + 3) := by
  have h := sawNum_lt v e k
  have : (2 : ℕ) ^ k ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The two children numerators of a test node add up to `2 ^ (k + 4) - 2`, so the node is
exactly split. -/
lemma hardNum_add (e k : ℕ) :
    hardPlusNum e k + hardMinusNum e k + 2 = 2 ^ (k + 4) := by
  have h0 := sawNum_lt_pow_add_three 0 e k
  have h1 := sawNum_lt_pow_add_three 1 e k
  have hp : (2 : ℕ) ^ (k + 4) = 2 * 2 ^ (k + 3) := by ring
  simp only [hardPlusNum, hardMinusNum]
  omega

/-- The heavier child numerator at least doubles from one precision to the next. -/
lemma two_mul_hardPlusNum_le (e k : ℕ) :
    2 * hardPlusNum e k ≤ hardPlusNum e (k + 1) := by
  have h0 := sawNum_lt_pow_add_three 0 e k
  have h1 := sawNum_lt_pow_add_three 1 e k
  have e0 : sawNum 0 e (k + 1) = 2 * sawNum 0 e k + (if diagEvaln e k == some 0 then 1 else 0) :=
    rfl
  have e1 : sawNum 1 e (k + 1) = 2 * sawNum 1 e k + (if diagEvaln e k == some 1 then 1 else 0) :=
    rfl
  have hp : (2 : ℕ) ^ (k + 1 + 3) = 2 * 2 ^ (k + 3) := by ring
  simp only [hardPlusNum, e0, e1, hp]
  split <;> split <;> omega

/-- The lighter child numerator at least doubles from one precision to the next. -/
lemma two_mul_hardMinusNum_le (e k : ℕ) :
    2 * hardMinusNum e k ≤ hardMinusNum e (k + 1) := by
  have h0 := sawNum_lt_pow_add_three 0 e k
  have h1 := sawNum_lt_pow_add_three 1 e k
  have e0 : sawNum 0 e (k + 1) = 2 * sawNum 0 e k + (if diagEvaln e k == some 0 then 1 else 0) :=
    rfl
  have e1 : sawNum 1 e (k + 1) = 2 * sawNum 1 e k + (if diagEvaln e k == some 1 then 1 else 0) :=
    rfl
  have hp : (2 : ℕ) ^ (k + 1 + 3) = 2 * 2 ^ (k + 3) := by ring
  simp only [hardMinusNum, e0, e1, hp]
  split <;> split <;> omega

/-- The heavier child numerator grows by at most a factor two plus two. -/
lemma hardPlusNum_succ_le (e k : ℕ) :
    hardPlusNum e (k + 1) ≤ 2 * hardPlusNum e k + 2 := by
  have h0 := sawNum_lt_pow_add_three 0 e k
  have h1 := sawNum_lt_pow_add_three 1 e k
  have e0 : sawNum 0 e (k + 1) = 2 * sawNum 0 e k + (if diagEvaln e k == some 0 then 1 else 0) :=
    rfl
  have e1 : sawNum 1 e (k + 1) = 2 * sawNum 1 e k + (if diagEvaln e k == some 1 then 1 else 0) :=
    rfl
  have hp : (2 : ℕ) ^ (k + 1 + 3) = 2 * 2 ^ (k + 3) := by ring
  simp only [hardPlusNum, e0, e1, hp]
  split <;> split <;> omega

/-- The lighter child numerator grows by at most a factor two plus two. -/
lemma hardMinusNum_succ_le (e k : ℕ) :
    hardMinusNum e (k + 1) ≤ 2 * hardMinusNum e k + 2 := by
  have h0 := sawNum_lt_pow_add_three 0 e k
  have h1 := sawNum_lt_pow_add_three 1 e k
  have e0 : sawNum 0 e (k + 1) = 2 * sawNum 0 e k + (if diagEvaln e k == some 0 then 1 else 0) :=
    rfl
  have e1 : sawNum 1 e (k + 1) = 2 * sawNum 1 e k + (if diagEvaln e k == some 1 then 1 else 0) :=
    rfl
  have hp : (2 : ℕ) ^ (k + 1 + 3) = 2 * 2 ^ (k + 3) := by ring
  simp only [hardMinusNum, e0, e1, hp]
  split <;> split <;> omega

/-! ### The tree -/

/-- Number of leading `true` bits. -/
def leadOnes : BitString → ℕ
  | [] => 0
  | b :: t => if b then leadOnes t + 1 else 0

/-- The number of leading ones is at most the length of the string. -/
lemma leadOnes_le_length (x : BitString) : leadOnes x ≤ x.length := by
  induction x with
  | nil => simp [leadOnes]
  | cons b t ih =>
    simp only [leadOnes, List.length_cons]
    split <;> omega

/-- Appending a bit to a string of ones either extends the run or ends it. -/
lemma leadOnes_append_of_all_ones {x : BitString} (h : leadOnes x = x.length) (b : Bool) :
    leadOnes (x ++ [b]) = if b then x.length + 1 else x.length := by
  induction x with
  | nil => cases b <;> simp [leadOnes]
  | cons c t ih =>
    cases c
    · simp [leadOnes] at h
    · simp only [leadOnes, List.length_cons, if_true] at h ⊢
      have h' : leadOnes t = t.length := by omega
      rw [List.cons_append]
      simp only [leadOnes, if_true, ih h']
      cases b <;> simp

/-- Appending a bit past the first zero does not change the run of leading ones. -/
lemma leadOnes_append_of_not_all_ones {x : BitString} (h : leadOnes x < x.length) (b : Bool) :
    leadOnes (x ++ [b]) = leadOnes x := by
  induction x with
  | nil => simp [leadOnes] at h
  | cons c t ih =>
    cases c
    · simp [leadOnes]
    · simp only [leadOnes, List.length_cons, if_true] at h ⊢
      rw [List.cons_append]
      simp only [leadOnes, if_true, ih (by omega : leadOnes t < t.length)]

/-- Appending a bit does not change the earlier entries. -/
lemma getD_append_of_lt {x : BitString} {i : ℕ} (h : i < x.length) (b d : Bool) :
    (x ++ [b]).getD i d = x.getD i d := by
  simp only [List.getD, List.getElem?_append_left h]

/-- The stage-`s` numerator of the counterexample tree semimeasure. -/
def hardStage (s : ℕ) (x : BitString) : ℕ :=
  if x.length ≤ leadOnes x + 1 then
    (if x.length ≤ s then 2 ^ (s - x.length) else 0)
  else if s < x.length + 3 then 0
  else if x.getD (leadOnes x + 1) true = false then
    hardPlusNum (leadOnes x) (s - x.length - 3)
  else hardMinusNum (leadOnes x) (s - x.length - 3)

/-- The root of the counterexample tree carries the full stage mass `2 ^ s`. -/
lemma hardStage_nil (s : ℕ) : hardStage s [] = 2 ^ s := by
  simp [hardStage, leadOnes]

/-- The number of leading ones, written as a fold. -/
lemma leadOnes_eq_foldr (x : BitString) :
    leadOnes x = x.foldr (fun b ih => if b then ih + 1 else 0) 0 := by
  induction x with
  | nil => rfl
  | cons b t ih => simp only [leadOnes, List.foldr_cons, ih]

/-- The number of leading ones is primitive recursive. -/
lemma primrec_leadOnes : Primrec leadOnes := by
  have hstep : Primrec₂
      (fun (_ : BitString) (q : Bool × ℕ) => if q.1 then q.2 + 1 else 0) := by
    have := Primrec.cond (c := fun q : BitString × (Bool × ℕ) => q.2.1)
      (f := fun q : BitString × (Bool × ℕ) => q.2.2 + 1)
      (g := fun _ : BitString × (Bool × ℕ) => 0)
      (Primrec.fst.comp Primrec.snd) (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const 0)
    exact this.of_eq (fun q => by cases h : q.2.1 <;> simp [h])
  have hfold := Primrec.list_foldr (f := fun x : BitString => x) Primrec.id
    (Primrec.const 0) hstep
  exact hfold.of_eq (fun x => (leadOnes_eq_foldr x).symm)

/-- The heavier child numerator is primitive recursive. -/
lemma primrec_hardPlusNum : Primrec₂ hardPlusNum := by
  have hpow : Primrec (fun p : ℕ × ℕ => 2 ^ (p.2 + 3)) :=
    primrec_two_pow_aux.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 3))
  have h0 : Primrec (fun p : ℕ × ℕ => sawNum 0 p.1 p.2) := primrec_sawNum 0
  have h1 : Primrec (fun p : ℕ × ℕ => sawNum 1 p.1 p.2) := primrec_sawNum 1
  exact Primrec.nat_sub.comp
    (Primrec.nat_sub.comp (Primrec.nat_add.comp hpow h0) h1) (Primrec.const 1)

/-- The lighter child numerator is primitive recursive. -/
lemma primrec_hardMinusNum : Primrec₂ hardMinusNum := by
  have hpow : Primrec (fun p : ℕ × ℕ => 2 ^ (p.2 + 3)) :=
    primrec_two_pow_aux.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 3))
  have h0 : Primrec (fun p : ℕ × ℕ => sawNum 0 p.1 p.2) := primrec_sawNum 0
  have h1 : Primrec (fun p : ℕ × ℕ => sawNum 1 p.1 p.2) := primrec_sawNum 1
  exact Primrec.nat_sub.comp
    (Primrec.nat_sub.comp (Primrec.nat_add.comp hpow h1) h0) (Primrec.const 1)

private lemma primrec_hs_len : Primrec (fun p : ℕ × BitString => p.2.length) :=
  Primrec.list_length.comp Primrec.snd

private lemma primrec_hs_lead : Primrec (fun p : ℕ × BitString => leadOnes p.2) :=
  primrec_leadOnes.comp Primrec.snd

private lemma primrec_hs_plainVal : Primrec (fun p : ℕ × BitString =>
    if p.2.length ≤ p.1 then 2 ^ (p.1 - p.2.length) else 0) :=
  Primrec.ite (Primrec.nat_le.comp primrec_hs_len Primrec.fst)
    (primrec_two_pow_aux.comp (Primrec.nat_sub.comp Primrec.fst primrec_hs_len))
    (Primrec.const 0)

private lemma primrec_hs_k : Primrec (fun p : ℕ × BitString => p.1 - p.2.length - 3) :=
  Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.fst primrec_hs_len) (Primrec.const 3)

private lemma primrec_hs_plus : Primrec (fun p : ℕ × BitString =>
    hardPlusNum (leadOnes p.2) (p.1 - p.2.length - 3)) :=
  Primrec₂.comp primrec_hardPlusNum primrec_hs_lead primrec_hs_k

private lemma primrec_hs_minus : Primrec (fun p : ℕ × BitString =>
    hardMinusNum (leadOnes p.2) (p.1 - p.2.length - 3)) :=
  Primrec₂.comp primrec_hardMinusNum primrec_hs_lead primrec_hs_k

private lemma primrec_hs_getD : Primrec (fun p : ℕ × BitString =>
    p.2.getD (leadOnes p.2 + 1) true) :=
  (Primrec.list_getD true).comp Primrec.snd (Primrec.succ.comp primrec_hs_lead)

private lemma primrec_hs_branch : Primrec (fun p : ℕ × BitString =>
    if p.2.getD (leadOnes p.2 + 1) true = false then
      hardPlusNum (leadOnes p.2) (p.1 - p.2.length - 3)
    else hardMinusNum (leadOnes p.2) (p.1 - p.2.length - 3)) :=
  Primrec.ite (Primrec.eq.comp primrec_hs_getD (Primrec.const false))
    primrec_hs_plus primrec_hs_minus

private lemma primrec_hs_hardVal : Primrec (fun p : ℕ × BitString =>
    if p.1 < p.2.length + 3 then 0
    else if p.2.getD (leadOnes p.2 + 1) true = false then
      hardPlusNum (leadOnes p.2) (p.1 - p.2.length - 3)
    else hardMinusNum (leadOnes p.2) (p.1 - p.2.length - 3)) :=
  Primrec.ite
    (Primrec.nat_lt.comp Primrec.fst (Primrec.nat_add.comp primrec_hs_len (Primrec.const 3)))
    (Primrec.const 0) primrec_hs_branch

/-- The stage numerators of the counterexample tree are computable. -/
lemma computable_hardStage : Computable (fun p : ℕ × BitString => hardStage p.1 p.2) :=
  (Primrec.ite (Primrec.nat_le.comp primrec_hs_len (Primrec.succ.comp primrec_hs_lead))
    primrec_hs_plainVal primrec_hs_hardVal).to_comp

/-- Away from the test nodes the tree carries the uniform mass `2 ^ (s - |x|)`. -/
lemma hardStage_plain {x : BitString} (h : x.length ≤ leadOnes x + 1) (s : ℕ) :
    hardStage s x = if x.length ≤ s then 2 ^ (s - x.length) else 0 := by
  simp only [hardStage, h, if_true]

/-- Below a test node the tree carries the heavier or the lighter child numerator, according to
the bit following the run of ones. -/
lemma hardStage_hard {x : BitString} (h : leadOnes x + 1 < x.length) (s : ℕ) :
    hardStage s x =
      if s < x.length + 3 then 0
      else if x.getD (leadOnes x + 1) true = false then
        hardPlusNum (leadOnes x) (s - x.length - 3)
      else hardMinusNum (leadOnes x) (s - x.length - 3) := by
  have h' : ¬ (x.length ≤ leadOnes x + 1) := by omega
  simp only [hardStage, h', if_false]

/-- The stage numerators at least double from one stage to the next, so the dyadic masses
increase. -/
lemma hardStage_mono (s : ℕ) (x : BitString) :
    2 * hardStage s x ≤ hardStage (s + 1) x := by
  by_cases hplain : x.length ≤ leadOnes x + 1
  · rw [hardStage_plain hplain, hardStage_plain hplain]
    by_cases hs : x.length ≤ s
    · have hs' : x.length ≤ s + 1 := by omega
      have hk : s + 1 - x.length = (s - x.length) + 1 := by omega
      simp only [hs, hs', if_true, hk, pow_succ]
      omega
    · simp only [hs, if_false, Nat.mul_zero]
      exact Nat.zero_le _
  · have hlt : leadOnes x + 1 < x.length := by omega
    rw [hardStage_hard hlt, hardStage_hard hlt]
    by_cases h3 : s < x.length + 3
    · simp only [h3, if_true, Nat.mul_zero]
      exact Nat.zero_le _
    · have h3' : ¬ (s + 1 < x.length + 3) := by omega
      have hk : s + 1 - x.length - 3 = (s - x.length - 3) + 1 := by omega
      simp only [h3, h3', if_false, hk]
      by_cases hg : x.getD (leadOnes x + 1) true = false
      · simp only [hg, if_true]
        exact two_mul_hardPlusNum_le _ _
      · simp only [hg]
        exact two_mul_hardMinusNum_le _ _

/-- The bit appended to a string is the entry at its old length. -/
lemma getD_append_last (x : BitString) (b d : Bool) : (x ++ [b]).getD x.length d = b := by
  simp [List.getD]

/-- The stage numerators are supermultiplicative over the two children, so the limit is a
semimeasure. -/
lemma hardStage_coh (s : ℕ) (x : BitString) :
    hardStage s (x ++ [false]) + hardStage s (x ++ [true]) ≤ hardStage s x := by
  have hle := leadOnes_le_length x
  have hlenf : (x ++ [false]).length = x.length + 1 := by simp
  have hlent : (x ++ [true]).length = x.length + 1 := by simp
  rcases Nat.eq_or_lt_of_le hle with hall | hlt
  · -- `x` is a block of ones: both children are unperturbed
    have hf : leadOnes (x ++ [false]) = x.length := by
      rw [leadOnes_append_of_all_ones hall]; simp
    have ht : leadOnes (x ++ [true]) = x.length + 1 := by
      rw [leadOnes_append_of_all_ones hall]; simp
    rw [hardStage_plain (by omega), hardStage_plain (by omega),
      hardStage_plain (by omega : x.length ≤ leadOnes x + 1), hlenf, hlent]
    by_cases hs : x.length + 1 ≤ s
    · obtain ⟨k, rfl⟩ : ∃ k, s = x.length + 1 + k := ⟨s - x.length - 1, by omega⟩
      rw [if_pos (by omega : x.length + 1 ≤ x.length + 1 + k),
        if_pos (by omega : x.length ≤ x.length + 1 + k)]
      have e1 : x.length + 1 + k - (x.length + 1) = k := by omega
      have e2 : x.length + 1 + k - x.length = k + 1 := by omega
      rw [e1, e2, pow_succ]
      omega
    · rw [if_neg hs]
      exact Nat.zero_le _
  · -- appending does not change the leading block of ones
    have hf : leadOnes (x ++ [false]) = leadOnes x := leadOnes_append_of_not_all_ones hlt false
    have ht : leadOnes (x ++ [true]) = leadOnes x := leadOnes_append_of_not_all_ones hlt true
    rcases Nat.lt_or_ge (leadOnes x + 1) x.length with hhard | hplain
    · -- `x` is already a perturbed node; both children inherit its sign
      have hgf : (x ++ [false]).getD (leadOnes x + 1) true = x.getD (leadOnes x + 1) true :=
        getD_append_of_lt (by omega) _ _
      have hgt : (x ++ [true]).getD (leadOnes x + 1) true = x.getD (leadOnes x + 1) true :=
        getD_append_of_lt (by omega) _ _
      rw [hardStage_hard (by omega : leadOnes (x ++ [false]) + 1 < (x ++ [false]).length),
        hardStage_hard (by omega : leadOnes (x ++ [true]) + 1 < (x ++ [true]).length),
        hardStage_hard hhard, hf, ht, hgf, hgt, hlenf, hlent]
      by_cases h4 : s < x.length + 1 + 3
      · rw [if_pos h4]
        exact Nat.zero_le _
      · rw [if_neg h4, if_neg (by omega : ¬ s < x.length + 3)]
        have hk : s - x.length - 3 = (s - (x.length + 1) - 3) + 1 := by omega
        rw [hk]
        by_cases hg : x.getD (leadOnes x + 1) true = false
        · rw [if_pos hg, if_pos hg]
          have := two_mul_hardPlusNum_le (leadOnes x) (s - (x.length + 1) - 3)
          omega
        · rw [if_neg hg, if_neg hg]
          have := two_mul_hardMinusNum_le (leadOnes x) (s - (x.length + 1) - 3)
          omega
    · -- `x = 1^e 0`: the two children carry the two perturbed weights
      have hlen : x.length = leadOnes x + 1 := by omega
      have hgf : (x ++ [false]).getD (leadOnes x + 1) true = false := by
        rw [← hlen]; exact getD_append_last x false true
      have hgt : (x ++ [true]).getD (leadOnes x + 1) true = true := by
        rw [← hlen]; exact getD_append_last x true true
      rw [hardStage_hard (by omega : leadOnes (x ++ [false]) + 1 < (x ++ [false]).length),
        hardStage_hard (by omega : leadOnes (x ++ [true]) + 1 < (x ++ [true]).length),
        hardStage_plain (by omega), hf, ht, hgf, hgt, hlenf, hlent]
      by_cases h4 : s < x.length + 1 + 3
      · rw [if_pos h4, if_pos h4]
        exact Nat.zero_le _
      · rw [if_neg h4, if_neg h4, if_pos (by omega : x.length ≤ s),
          if_pos (rfl : false = false), if_neg (by simp : ¬ (true = false))]
        have hsum := hardNum_add (leadOnes x) (s - (x.length + 1) - 3)
        have hk : s - (x.length + 1) - 3 + 4 = s - x.length := by omega
        rw [hk] at hsum
        omega


/-- From stage `|x| + 4` on, the children numerators add up to the parent numerator
up to an error of `2`. -/
lemma hardStage_coh_close (s : ℕ) (x : BitString) (hs : x.length + 4 ≤ s) :
    hardStage s x ≤ hardStage s (x ++ [false]) + hardStage s (x ++ [true]) + 2 := by
  have hle := leadOnes_le_length x
  have hlenf : (x ++ [false]).length = x.length + 1 := by simp
  have hlent : (x ++ [true]).length = x.length + 1 := by simp
  rcases Nat.eq_or_lt_of_le hle with hall | hlt
  · have hf : leadOnes (x ++ [false]) = x.length := by
      rw [leadOnes_append_of_all_ones hall]; simp
    have ht : leadOnes (x ++ [true]) = x.length + 1 := by
      rw [leadOnes_append_of_all_ones hall]; simp
    rw [hardStage_plain (x := x) (by omega),
      hardStage_plain (x := x ++ [false]) (by omega),
      hardStage_plain (x := x ++ [true]) (by omega), hlenf, hlent]
    obtain ⟨k, rfl⟩ : ∃ k, s = x.length + 1 + k := ⟨s - x.length - 1, by omega⟩
    rw [if_pos (by omega : x.length + 1 ≤ x.length + 1 + k),
      if_pos (by omega : x.length ≤ x.length + 1 + k)]
    have e1 : x.length + 1 + k - (x.length + 1) = k := by omega
    have e2 : x.length + 1 + k - x.length = k + 1 := by omega
    rw [e1, e2, pow_succ]
    omega
  · have hf : leadOnes (x ++ [false]) = leadOnes x := leadOnes_append_of_not_all_ones hlt false
    have ht : leadOnes (x ++ [true]) = leadOnes x := leadOnes_append_of_not_all_ones hlt true
    rcases Nat.lt_or_ge (leadOnes x + 1) x.length with hhard | hplain
    · have hgf : (x ++ [false]).getD (leadOnes x + 1) true = x.getD (leadOnes x + 1) true :=
        getD_append_of_lt (by omega) _ _
      have hgt : (x ++ [true]).getD (leadOnes x + 1) true = x.getD (leadOnes x + 1) true :=
        getD_append_of_lt (by omega) _ _
      rw [hardStage_hard (by omega : leadOnes (x ++ [false]) + 1 < (x ++ [false]).length),
        hardStage_hard (by omega : leadOnes (x ++ [true]) + 1 < (x ++ [true]).length),
        hardStage_hard hhard, hf, ht, hgf, hgt, hlenf, hlent]
      simp only [if_neg (by omega : ¬ s < x.length + 1 + 3),
        if_neg (by omega : ¬ s < x.length + 3)]
      have hk : s - x.length - 3 = (s - (x.length + 1) - 3) + 1 := by omega
      rw [hk]
      by_cases hg : x.getD (leadOnes x + 1) true = false
      · simp only [if_pos hg]
        have := hardPlusNum_succ_le (leadOnes x) (s - (x.length + 1) - 3)
        omega
      · simp only [if_neg hg]
        have := hardMinusNum_succ_le (leadOnes x) (s - (x.length + 1) - 3)
        omega
    · have hlen : x.length = leadOnes x + 1 := by omega
      have hgf : (x ++ [false]).getD (leadOnes x + 1) true = false := by
        rw [← hlen]; exact getD_append_last x false true
      have hgt : (x ++ [true]).getD (leadOnes x + 1) true = true := by
        rw [← hlen]; exact getD_append_last x true true
      rw [hardStage_hard (by omega : leadOnes (x ++ [false]) + 1 < (x ++ [false]).length),
        hardStage_hard (by omega : leadOnes (x ++ [true]) + 1 < (x ++ [true]).length),
        hardStage_plain (x := x) (by omega), hf, ht, hgf, hgt, hlenf, hlent]
      simp only [if_neg (by omega : ¬ s < x.length + 1 + 3),
        if_pos (by omega : x.length ≤ s),
        if_neg (by simp : ¬ (true = false)), if_true]
      have hsum := hardNum_add (leadOnes x) (s - (x.length + 1) - 3)
      have hk : s - (x.length + 1) - 3 + 4 = s - x.length := by omega
      rw [hk] at hsum
      omega

/-- The counterexample tree semimeasure. -/
noncomputable def hardTree (x : BitString) : ℝ≥0∞ := ⨆ s, dyadicValue (hardStage s x) s

/-- The dyadic value with numerator two at precision `n + 1` is `2 ^ -n`. -/
lemma dyadicValue_two_succ (n : ℕ) : dyadicValue 2 (n + 1) = ((2 : ℝ≥0∞)⁻¹) ^ n := by
  rw [show (2 : ℕ) = 2 ^ 1 * 1 by norm_num, dyadicValue_two_pow_mul_add,
    dyadicValue_one_eq_inv_two_pow']

/-- For a fixed numerator, the dyadic value decreases as the precision grows. -/
lemma dyadicValue_antitone_stage (n : ℕ) {s t : ℕ} (h : s ≤ t) :
    dyadicValue n t ≤ dyadicValue n s := by
  unfold dyadicValue
  gcongr
  exact one_le_two

/-- A bound valid up to `2 ^ -t` for every large `t` is a bound. -/
lemma le_of_le_add_dyadicValue {x y : ℝ≥0∞} {N : ℕ}
    (h : ∀ t, N ≤ t → x ≤ y + dyadicValue 2 t) : x ≤ y := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (a := (ε : ℝ≥0∞))
    (by exact_mod_cast hε.ne')
  refine le_trans (h (max N (n + 1)) (le_max_left _ _)) ?_
  gcongr
  calc dyadicValue 2 (max N (n + 1)) ≤ dyadicValue 2 (n + 1) :=
        dyadicValue_antitone_stage 2 (le_max_right _ _)
    _ = ((2 : ℝ≥0∞)⁻¹) ^ n := dyadicValue_two_succ n
    _ ≤ (ε : ℝ≥0∞) := hn.le

/-- Doubling the numerator while raising the precision by one does not decrease the dyadic value. -/
lemma dyadicValue_step_le {n m s : ℕ} (h : 2 * n ≤ m) :
    dyadicValue n s ≤ dyadicValue m (s + 1) := by
  rw [← dyadicValue_two_mul_succ n s]
  exact dyadicValue_le _ _ _ h

/-- A numerator sequence that at least doubles at every step has non-decreasing dyadic values. -/
lemma dyadicValue_chain_mono {q : ℕ → ℕ} (h : ∀ s, 2 * q s ≤ q (s + 1))
    {s t : ℕ} (hst : s ≤ t) :
    dyadicValue (q s) s ≤ dyadicValue (q t) t := by
  induction hst with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (dyadicValue_step_le (h _))

/-- Two stagewise approximations whose numerators differ by at most `2` from some stage on
have the same limit. -/
lemma iSup_dyadicValue_eq_of_close {D q : ℕ → ℕ} {s₀ : ℕ}
    (hqmono : ∀ s, 2 * q s ≤ q (s + 1)) (hle : ∀ s, D s ≤ q s)
    (hclose : ∀ s, s₀ ≤ s → q s ≤ D s + 2) :
    ⨆ s, dyadicValue (D s) s = ⨆ s, dyadicValue (q s) s := by
  apply le_antisymm
  · exact iSup_mono (fun s => dyadicValue_le _ _ _ (hle s))
  · refine iSup_le (fun s => ?_)
    refine le_of_le_add_dyadicValue (N := max s s₀) (fun t ht => ?_)
    have h1 : dyadicValue (q s) s ≤ dyadicValue (q t) t :=
      dyadicValue_chain_mono hqmono (le_trans (le_max_left _ _) ht)
    have h2 : dyadicValue (q t) t ≤ dyadicValue (D t) t + dyadicValue 2 t := by
      rw [← dyadicValue_add]
      exact dyadicValue_le _ _ _ (hclose t (le_trans (le_max_right _ _) ht))
    refine h1.trans (h2.trans ?_)
    gcongr
    exact le_iSup (fun t => dyadicValue (D t) t) t

/-- The dyadic masses of the counterexample tree are non-decreasing in the stage. -/
lemma hardStage_dyadic_mono (s : ℕ) (x : BitString) :
    dyadicValue (hardStage s x) s ≤ dyadicValue (hardStage (s + 1) x) (s + 1) :=
  dyadicValue_step_le (hardStage_mono s x)

/-- The counterexample tree is a lower semicomputable continuous semimeasure. -/
theorem isLowerSemicomputableContinuousSemimeasure_hardTree :
    IsLowerSemicomputableContinuousSemimeasure hardTree :=
  isLowerSemicomputableContinuousSemimeasure_iSup_of_stage
    hardStage_nil hardStage_coh hardStage_dyadic_mono computable_hardStage

/-- The counterexample tree is exactly additive: each node carries the sum of its two children. -/
theorem hardTree_exact (x : BitString) :
    hardTree x = hardTree (x ++ [false]) + hardTree (x ++ [true]) := by
  have hsum : hardTree (x ++ [false]) + hardTree (x ++ [true])
      = ⨆ s, dyadicValue (hardStage s (x ++ [false]) + hardStage s (x ++ [true])) s := by
    rw [hardTree, hardTree, iSup_add_iSup_of_stage_mono hardStage_dyadic_mono x]
    exact iSup_congr (fun s => (dyadicValue_add _ _ _).symm)
  rw [hsum, hardTree]
  exact (iSup_dyadicValue_eq_of_close (s₀ := x.length + 4)
    (fun s => hardStage_mono s x) (fun s => hardStage_coh s x)
    (fun s hs => hardStage_coh_close s x hs)).symm

/-! ### The test nodes -/

/-- Scaling numerator and precision together leaves the dyadic value unchanged. -/
lemma dyadicValue_scale (n s d : ℕ) : dyadicValue n s = dyadicValue (n * 2 ^ d) (s + d) := by
  rw [mul_comm n (2 ^ d)]
  exact (dyadicValue_two_pow_mul_add n s d).symm

/-- At a fixed precision the dyadic value is strictly monotone in the numerator. -/
lemma dyadicValue_lt_of_lt {n m : ℕ} (s : ℕ) (h : n < m) :
    dyadicValue n s < dyadicValue m s := by
  unfold dyadicValue
  exact ENNReal.div_lt_div_right (by simp) (ENNReal.pow_ne_top (by simp)) (by exact_mod_cast h)

/-- The test node `1^e 0 0`. -/
def hardNode (e : ℕ) : BitString := List.replicate e true ++ [false, false]

/-- The string `1^e 0 y` has exactly `e` leading ones. -/
lemma leadOnes_replicate_append (e : ℕ) (y : BitString) :
    leadOnes (List.replicate e true ++ (false :: y)) = e := by
  induction e with
  | zero => simp [leadOnes]
  | succ e ih => simp [List.replicate_succ, leadOnes, ih]

/-- Entries past a block of leading ones are the entries of the tail. -/
lemma getD_replicate_append (e i : ℕ) (y : BitString) (d : Bool) :
    (List.replicate e true ++ y).getD (e + i) d = y.getD i d := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h : e + 1 + i = (e + i) + 1 := by omega
    rw [List.replicate_succ, List.cons_append, h, List.getD_cons_succ, ih]

/-- The test node of index `e` has length `e + 2`. -/
lemma hardNode_length (e : ℕ) : (hardNode e).length = e + 2 := by simp [hardNode]

/-- The test node of index `e` has `e` leading ones. -/
lemma leadOnes_hardNode (e : ℕ) : leadOnes (hardNode e) = e :=
  leadOnes_replicate_append e [false]

/-- The test node is the zero child of `1^e 0`. -/
lemma getD_hardNode (e : ℕ) : (hardNode e).getD (e + 1) true = false := by
  have h := getD_replicate_append e 1 [false, false] true
  simp [hardNode]

/-- At the test node the stage numerator is the heavier child numerator, shifted by `e + 5`. -/
lemma hardStage_hardNode (s e : ℕ) :
    hardStage s (hardNode e) = if s < e + 5 then 0 else hardPlusNum e (s - e - 5) := by
  rw [hardStage_hard (by rw [hardNode_length, leadOnes_hardNode]; omega) s,
    leadOnes_hardNode, hardNode_length, getD_hardNode]
  have h5 : e + 2 + 3 = e + 5 := by omega
  have hk : s - (e + 2) - 3 = s - e - 5 := by omega
  rw [h5, hk]
  simp only [if_true]

/-- If the diagonal value is zero, the mass of the test node exceeds `2 ^ -(e + 2)`. -/
theorem hardTree_hardNode_gt {e : ℕ} (h : DiagZero e) :
    dyadicValue 1 (e + 2) < hardTree (hardNode e) := by
  obtain ⟨t0, ht0⟩ := exists_sawZero_of_diagZero h
  have hz : diagEvaln e t0 = some 0 := by simpa [sawZero] using ht0
  have hone : ∀ t, diagEvaln e t ≠ some 1 := by
    intro t ht
    exact not_sawZero_sawOne ht0 (show sawOne e t = true by simp [sawOne, ht])
  have hO : sawNum 1 e (t0 + 2) = 0 := sawNum_eq_zero_of_never hone _
  have hZ : 2 ≤ sawNum 0 e (t0 + 2) := two_le_sawNum hz
  have hP : 2 ^ (t0 + 2 + 3) < hardPlusNum e (t0 + 2) := by
    have h0 := sawNum_lt_pow_add_three 0 e (t0 + 2)
    simp only [hardPlusNum, hO]
    omega
  have hstage : hardStage (t0 + 2 + e + 5) (hardNode e) = hardPlusNum e (t0 + 2) := by
    rw [hardStage_hardNode, if_neg (by omega)]
    congr 1
    omega
  have hscale : dyadicValue 1 (e + 2) = dyadicValue (2 ^ (t0 + 2 + 3)) (t0 + 2 + e + 5) := by
    rw [dyadicValue_scale 1 (e + 2) (t0 + 2 + 3), one_mul]
    congr 1
    omega
  calc dyadicValue 1 (e + 2) = dyadicValue (2 ^ (t0 + 2 + 3)) (t0 + 2 + e + 5) := hscale
    _ < dyadicValue (hardPlusNum e (t0 + 2)) (t0 + 2 + e + 5) := dyadicValue_lt_of_lt _ hP
    _ ≤ hardTree (hardNode e) := by
        rw [hardTree, ← hstage]
        exact le_iSup (fun s => dyadicValue (hardStage s (hardNode e)) s) (t0 + 2 + e + 5)

/-- If the diagonal value is one, the mass of the test node falls below `2 ^ -(e + 2)`. -/
theorem hardTree_hardNode_lt {e : ℕ} (h : DiagOne e) :
    hardTree (hardNode e) < dyadicValue 1 (e + 2) := by
  obtain ⟨t1, ht1⟩ := exists_sawOne_of_diagOne h
  have ho : diagEvaln e t1 = some 1 := by simpa [sawOne] using ht1
  have hzero : ∀ t, diagEvaln e t ≠ some 0 := by
    intro t ht
    exact not_sawZero_sawOne (show sawZero e t = true by simp [sawZero, ht]) ht1
  have hZ : ∀ k, sawNum 0 e k = 0 := sawNum_eq_zero_of_never hzero
  have hOmono : ∀ t', t1 ≤ t' → diagEvaln e t' = some 1 := by
    intro t' h'
    have := sawOne_mono h' ht1
    simpa [sawOne] using this
  have hbound : ∀ k, hardPlusNum e k * 2 ^ (t1 + 5) ≤ (2 ^ (t1 + 5) - 1) * 2 ^ (k + 3) := by
    intro k
    rcases Nat.lt_or_ge k (t1 + 1) with hk | hk
    · have hP : hardPlusNum e k ≤ 2 ^ (k + 3) - 1 := by
        simp only [hardPlusNum, hZ k]
        omega
      have hAB : (2 : ℕ) ^ (k + 3) ≤ 2 ^ (t1 + 5) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      calc hardPlusNum e k * 2 ^ (t1 + 5) ≤ (2 ^ (k + 3) - 1) * 2 ^ (t1 + 5) :=
            Nat.mul_le_mul_right _ hP
        _ = 2 ^ (k + 3) * 2 ^ (t1 + 5) - 2 ^ (t1 + 5) := by rw [Nat.sub_mul, one_mul]
        _ ≤ 2 ^ (k + 3) * 2 ^ (t1 + 5) - 2 ^ (k + 3) := Nat.sub_le_sub_left hAB _
        _ = (2 ^ (t1 + 5) - 1) * 2 ^ (k + 3) := by
            rw [Nat.sub_mul, one_mul, Nat.mul_comm]
    · have hC : 2 ^ (k - t1 - 1) ≤ sawNum 1 e k := pow_le_sawNum hOmono ho hk
      have hP : hardPlusNum e k ≤ 2 ^ (k + 3) - 2 ^ (k - t1 - 1) := by
        simp only [hardPlusNum, hZ k]
        omega
      have hCB : 2 ^ (k - t1 - 1) * 2 ^ (t1 + 5) = 2 * 2 ^ (k + 3) := by
        rw [← pow_add, ← pow_succ']
        congr 1
        omega
      calc hardPlusNum e k * 2 ^ (t1 + 5) ≤ (2 ^ (k + 3) - 2 ^ (k - t1 - 1)) * 2 ^ (t1 + 5) :=
            Nat.mul_le_mul_right _ hP
        _ = 2 ^ (k + 3) * 2 ^ (t1 + 5) - 2 ^ (k - t1 - 1) * 2 ^ (t1 + 5) := by rw [Nat.sub_mul]
        _ = 2 ^ (k + 3) * 2 ^ (t1 + 5) - 2 * 2 ^ (k + 3) := by rw [hCB]
        _ ≤ 2 ^ (k + 3) * 2 ^ (t1 + 5) - 2 ^ (k + 3) :=
            Nat.sub_le_sub_left (by omega) _
        _ = (2 ^ (t1 + 5) - 1) * 2 ^ (k + 3) := by
            rw [Nat.sub_mul, one_mul, Nat.mul_comm]
  have hterm : ∀ s, dyadicValue (hardStage s (hardNode e)) s
      ≤ dyadicValue (2 ^ (t1 + 5) - 1) (t1 + e + 7) := by
    intro s
    rw [hardStage_hardNode]
    by_cases hs : s < e + 5
    · rw [if_pos hs]
      simp [dyadicValue]
    · rw [if_neg hs]
      obtain ⟨k, rfl⟩ : ∃ k, s = k + e + 5 := ⟨s - e - 5, by omega⟩
      have hk : k + e + 5 - e - 5 = k := by omega
      rw [hk]
      have hL : dyadicValue (hardPlusNum e k) (k + e + 5)
          = dyadicValue (hardPlusNum e k * 2 ^ (t1 + 5)) (k + e + t1 + 10) := by
        rw [dyadicValue_scale (hardPlusNum e k) (k + e + 5) (t1 + 5)]
        congr 1
        omega
      have hR : dyadicValue (2 ^ (t1 + 5) - 1) (t1 + e + 7)
          = dyadicValue ((2 ^ (t1 + 5) - 1) * 2 ^ (k + 3)) (k + e + t1 + 10) := by
        rw [dyadicValue_scale (2 ^ (t1 + 5) - 1) (t1 + e + 7) (k + 3)]
        congr 1
        omega
      rw [hL, hR]
      exact dyadicValue_le _ _ _ (hbound k)
  have hlast : dyadicValue (2 ^ (t1 + 5) - 1) (t1 + e + 7) < dyadicValue 1 (e + 2) := by
    have hpos : 0 < (2 : ℕ) ^ (t1 + 5) := pow_pos (by norm_num) _
    have hscale : dyadicValue 1 (e + 2) = dyadicValue (2 ^ (t1 + 5)) (t1 + e + 7) := by
      rw [dyadicValue_scale 1 (e + 2) (t1 + 5), one_mul]
      congr 1
      omega
    rw [hscale]
    exact dyadicValue_lt_of_lt _ (by omega)
  exact lt_of_le_of_lt (iSup_le hterm) hlast

-- The refutation itself (`not_forall_exists_isFloorComputableMeasure_of_exact`)
-- lives in `KolmogorovCounterexamples/FloorComputableMeasure.lean`.

end Kolmogorov
