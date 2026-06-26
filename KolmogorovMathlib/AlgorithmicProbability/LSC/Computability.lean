import Mathlib
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple
import KolmogorovMathlib.AlgorithmicProbability.LSC.Defs
import KolmogorovMathlib.AlgorithmicProbability.LSC.Truncate

namespace Kolmogorov

open scoped ENNReal
open Computability

section Truncate

variable {approx : ℕ → BitString → BitString → ℕ}

lemma computable_range_sum {α : Type*} [Primcodable α]
    (g : α → ℕ → ℕ) (hg : Computable₂ g) (b : α → ℕ) (hb : Computable b) :
    Computable (fun a => ∑ t ∈ Finset.range (b a), g a t) :=
  Computability.computable_range_sum g hg b hb

/-- Compatibility alias for the reusable power helper. -/
lemma primrec_two_pow_aux : Primrec (fun n : ℕ => 2 ^ n) :=
  Computability.primrec_two_pow

lemma computable_two_mul : Computable (fun n : ℕ => 2 * n) :=
  Computability.computable_two_mul

/-
`evOut` is computable.
-/
lemma evOut_computable : Computable evOut := by
  unfold evOut
  have hdecode₂ : Computable (fun n : ℕ => Encodable.decode₂ BitString n) := by
    have hbranch : Computable₂ (fun (n : ℕ) (b : BitString) =>
        if Encodable.encode b = n then some b else none) := by
      have hpred : PrimrecPred (fun p : ℕ × BitString => Encodable.encode p.2 = p.1) :=
        Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst
      exact (Primrec.ite hpred
        (Primrec.option_some.comp Primrec.snd)
        (Primrec.const (none : Option BitString))).to_comp.to₂
    exact (Computable.option_bind (Computable.decode (α := BitString)) hbranch).of_eq (fun n => by
      unfold Encodable.decode₂
      cases h : (Encodable.decode n : Option BitString) <;> simp [Option.guard])
  exact hdecode₂.comp (Computable.fst.comp Computable.unpair)

/-- `evK` is computable. -/
lemma evK_computable : Computable evK := by
  unfold evK
  exact Computable.snd.comp Computable.unpair

/-- The increment numerator is computable in `(k, out, ctx)`. -/
lemma incNum_computable_f1 (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ => approx (q.2 + 1) q.1.2.1 q.1.2.2) := by
  have h_k_1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.2 + 1) := Computable.succ.comp Computable.snd
  have h_q1_2 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1.2) := Kolmogorov.Computability.comp_fst_snd Computable.id
  exact Computable.of_eq (hcomp.comp (Computable.pair h_k_1 h_q1_2)) (fun q => rfl)

lemma incNum_computable_f2 (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ => 2 * approx q.2 q.1.2.1 q.1.2.2) := by
  have h_q1_2 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1.2) := Kolmogorov.Computability.comp_fst_snd Computable.id
  have h_approx2 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => approx q.2 q.1.2.1 q.1.2.2) :=
    Computable.of_eq (hcomp.comp (Computable.pair Computable.snd h_q1_2)) (fun q => rfl)
  exact Computable.of_eq (computable_two_mul.comp h_approx2) (fun q => rfl)

lemma incNum_computable_step (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable₂ (fun (p : ℕ × BitString × BitString) (k : ℕ) => approx (k + 1) p.2.1 p.2.2 - 2 * approx k p.2.1 p.2.2) := by
  have h_sub : Computable (fun p : ℕ × ℕ => p.1 - p.2) := Primrec.nat_sub.to_comp
  exact Computable.of_eq (h_sub.comp (Computable.pair (incNum_computable_f1 approx hcomp) (incNum_computable_f2 approx hcomp))) (fun q => beta_pair (fun x y => x - y) _ _)

lemma incNum_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString × BitString => incNum approx p.1 p.2.1 p.2.2) := by
  have hg : Computable (fun p : ℕ × BitString × BitString => approx 0 p.2.1 p.2.2) :=
    hcomp.comp (Computable.pair (Computable.const 0) Computable.snd)
  exact Computable.of_eq
    (Kolmogorov.Computability.comp_nat_casesOn (Kolmogorov.Computability.comp_fst Computable.id) hg (incNum_computable_step approx hcomp))
    (fun p => incNum_eq_cases approx p)

/-- The event increment numerator is computable in `(t, ctx)`. -/
lemma evNum_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString => evNum approx p.1 p.2) := by
  have hf : Computable (fun p : ℕ × BitString => evOut p.1) := evOut_computable.comp Computable.fst
  have hg : Computable (fun p : ℕ × BitString => (0 : ℕ)) := Computable.const 0
  have hh : Computable₂ (fun (p : ℕ × BitString) (out : BitString) => incNum approx (evK p.1) out p.2) := by
    have h_q1 : Computable (fun q : (ℕ × BitString) × BitString => q.1) := Computable.fst
    have h_q1_1 : Computable (fun q : (ℕ × BitString) × BitString => q.1.1) := Computable.fst.comp h_q1
    have h_evK_q1_1 : Computable (fun q : (ℕ × BitString) × BitString => evK q.1.1) := evK_computable.comp h_q1_1
    have h_q2 : Computable (fun q : (ℕ × BitString) × BitString => q.2) := Computable.snd
    have h_q1_2 : Computable (fun q : (ℕ × BitString) × BitString => q.1.2) := Computable.snd.comp h_q1
    have h_inc_args : Computable (fun q : (ℕ × BitString) × BitString => (evK q.1.1, q.2, q.1.2)) :=
      Computable.pair h_evK_q1_1 (Computable.pair h_q2 h_q1_2)
    exact Computable.of_eq ((incNum_computable hcomp).comp h_inc_args) (fun q => beta_pair3 (incNum approx) (evK q.1.1) q.2 q.1.2)
  exact Computable.of_eq (f := fun p => Option.casesOn (evOut p.1) 0 (fun o => incNum approx (evK p.1) o p.2))
    (Computable.option_casesOn hf hg hh)
    (fun p => by
      cases h : evOut p.1 <;> simp [h, evNum_eq_none, evNum_eq_some])

/-- The cumulative numerator is computable in `(S, n, ctx)`. -/
-- The paired argument to `evNum_computable` contains nested product projections,
-- and Lean 4.31 spends most of its time normalizing the resulting `Partrec` witness.
lemma cumNumTerm_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun q : (ℕ × ℕ × BitString) × ℕ => cumNumTerm approx q.1 q.2) := by
  have h_q1 : Computable (fun q : (ℕ × ℕ × BitString) × ℕ => q.1) := Computable.fst
  have h_q2 : Computable (fun q : (ℕ × ℕ × BitString) × ℕ => q.2) := Computable.snd
  have h_q1_1 : Computable (fun q : (ℕ × ℕ × BitString) × ℕ => q.1.1) := Computable.fst.comp h_q1
  have h_q1_22 : Computable (fun q : (ℕ × ℕ × BitString) × ℕ => q.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp h_q1)
  have h_ev_args : Computable (fun q : (ℕ × ℕ × BitString) × ℕ => (q.2, q.1.2.2)) :=
    Computable.pair h_q2 h_q1_22
  have h_ev : Computable (fun q : (ℕ × ℕ × BitString) × ℕ => evNum approx q.2 q.1.2.2) :=
    Computable.of_eq ((evNum_computable hcomp).comp h_ev_args)
      (fun q => beta_pair (evNum approx) q.2 q.1.2.2)
  have h_evK_q2 : Computable (fun q : (ℕ × ℕ × BitString) × ℕ => evK q.2) :=
    evK_computable.comp h_q2
  have h_sub : Computable (fun q : (ℕ × ℕ × BitString) × ℕ => q.1.1 - evK q.2) :=
    Primrec.nat_sub.to_comp.comp h_q1_1 h_evK_q2
  have h_pow : Computable (fun q : (ℕ × ℕ × BitString) × ℕ => 2 ^ (q.1.1 - evK q.2)) :=
    primrec_two_pow.to_comp.comp h_sub
  have h_mul : Computable
      (fun q : (ℕ × ℕ × BitString) × ℕ =>
        evNum approx q.2 q.1.2.2 * 2 ^ (q.1.1 - evK q.2)) :=
    Computable.of_eq (Computable.comp Primrec.nat_mul.to_comp (Computable.pair h_ev h_pow))
      (fun q => beta_pair Nat.mul _ _)
  exact Computable.of_eq h_mul (fun q => cumNumTerm_eq_packed approx q)

-- `computable_range_sum` still expands a sizeable primitive-recursive recursor here.
lemma cumNum_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
  Computable (cumNumPacked approx) := by
  have h_g : Computable₂ (cumNumTerm approx) := cumNumTerm_computable hcomp
  have h_p21 : Computable (fun p : ℕ × ℕ × BitString => p.2.1) := Computable.fst.comp Computable.snd
  have h_computable : Computable (fun p : ℕ × ℕ × BitString => ∑ i ∈ Finset.range p.2.1, cumNumTerm approx p i) :=
    computable_range_sum (cumNumTerm approx) h_g (fun p : ℕ × ℕ × BitString => p.2.1) h_p21
  exact Computable.of_eq h_computable (fun p => (cumNumPacked_eq approx p).symm)

/-- The decision `evOut t = some out` is computable in `(t, out)`. -/
lemma evOutEq_decide_computable :
    Computable (fun p : ℕ × BitString => decide (evOut p.1 = some p.2)) := by
  have h_eq : PrimrecPred (fun q : Option BitString × BitString => q.1 = some q.2) :=
    Primrec.eq.comp Primrec.fst (Primrec.option_some.comp Primrec.snd)
  obtain ⟨_, h_eq⟩ := h_eq
  exact Computable.of_eq
    (h_eq.to_comp.comp (Computable.pair (evOut_computable.comp Computable.fst) Computable.snd))
    (fun p => by
      by_cases h : evOut p.1 = some p.2 <;> simp [h])

/-- The full stage-term (with the running-mass and output guards) is computable. -/
lemma decide_and_eq_cond {A B : Prop} [Decidable A] [Decidable B] :
  decide (A ∧ B) = cond (decide A) (decide B) false := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

lemma truncGTerm_computable_then_ev (approx : ℕ → BitString → BitString → ℕ)
      (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ => evNum approx q.2 q.1.2.2) := by
  have h_q2 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.2) := Computable.snd
  have h_q1_22 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1.2.2) :=
    Computable.of_eq (Computable.snd.comp (Kolmogorov.Computability.comp_fst_snd Computable.id)) (fun q => rfl)
  have h_arg_ev : Computable (fun q : (ℕ × BitString × BitString) × ℕ => (q.2, q.1.2.2)) := Computable.pair h_q2 h_q1_22
  exact Computable.of_eq ((evNum_computable hcomp).comp h_arg_ev) (fun q => rfl)

lemma truncGTerm_computable_then_pow (_approx : ℕ → BitString → BitString → ℕ) :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ => 2 ^ (q.1.1 - evK q.2)) := by
  have h_q2 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.2) := Computable.snd
  have h_q1_1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1.1) := Kolmogorov.Computability.comp_fst_fst Computable.id
  have h_evK_q2 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => evK q.2) := Computable.of_eq (evK_computable.comp h_q2) (fun q => rfl)
  have h_sub : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1.1 - evK q.2) :=
    Primrec.nat_sub.to_comp.comp h_q1_1 h_evK_q2
  exact Computable.of_eq (primrec_two_pow.to_comp.comp h_sub) (fun q => rfl)

lemma truncGTerm_computable_then (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
  Computable (fun q : (ℕ × BitString × BitString) × ℕ => evNum approx q.2 q.1.2.2 * 2 ^ (q.1.1 - evK q.2)) := by
  exact Primrec.nat_mul.to_comp.comp (truncGTerm_computable_then_ev approx hcomp) (truncGTerm_computable_then_pow approx)

lemma truncGTerm_computable_cond_A (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ => cumNum approx q.1.1 (q.2 + 1) q.1.2.2) := by
  have h_arg1_1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1) := Computable.fst
  have h_arg1_2_1 : Computable (fun p : ℕ × BitString × BitString => p.1) := Computable.fst
  have h_arg1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1.1) := h_arg1_2_1.comp h_arg1_1
  have h_arg2_1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.2) := Computable.snd
  have h_succ_q2 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.2 + 1) := Computable.succ.comp h_arg2_1
  have h_arg1_2_2 : Computable (fun p : ℕ × BitString × BitString => p.2) := Computable.snd
  have h_arg1_2_2_2 : Computable (fun p : BitString × BitString => p.2) := Computable.snd
  have h_arg1_2_2_2_q : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1.2.2) := h_arg1_2_2_2.comp (h_arg1_2_2.comp h_arg1_1)
  have h_cumNum_args1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => (q.2 + 1, q.1.2.2)) := Computable.pair h_succ_q2 h_arg1_2_2_2_q
  have h_cumNum_args2 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => (q.1.1, q.2 + 1, q.1.2.2)) := Computable.pair h_arg1 h_cumNum_args1
  exact Computable.of_eq ((cumNum_computable hcomp).comp h_cumNum_args2) (fun q => by unfold cumNumPacked; rfl)

lemma truncGTerm_computable_cond_B (d : ℕ) :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ => 2 ^ (d + q.1.1)) := by
  have h_arg1_1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1) := Computable.fst
  have h_arg1_2_1 : Computable (fun p : ℕ × BitString × BitString => p.1) := Computable.fst
  have h_arg1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1.1) := h_arg1_2_1.comp h_arg1_1
  have h_d : Computable (fun _ : (ℕ × BitString × BitString) × ℕ => d) := Computable.const d
  have h_add_d_q11 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => d + q.1.1) :=
    Primrec.nat_add.to_comp.comp h_d h_arg1
  exact primrec_two_pow.to_comp.comp h_add_d_q11

lemma truncGTerm_computable_cond_C1 (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) (d : ℕ) :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ => decide (cumNum approx q.1.1 (q.2 + 1) q.1.2.2 ≤ 2 ^ (d + q.1.1))) := by
  obtain ⟨_, hle⟩ := Primrec.nat_le
  exact Computable.of_eq (hle.to_comp.comp (Computable.pair (truncGTerm_computable_cond_A hcomp) (truncGTerm_computable_cond_B d)))
    (fun q => by simp)

lemma truncGTerm_computable_cond_C2 :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ => decide (evOut q.2 = some q.1.2.1)) := by
  have h_arg1_1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1) := Computable.fst
  have h_arg2_1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.2) := Computable.snd
  have h_arg1_2_2 : Computable (fun p : ℕ × BitString × BitString => p.2) := Computable.snd
  have h_arg1_2_2_1 : Computable (fun p : BitString × BitString => p.1) := Computable.fst
  have h_arg1_2_2_1_q : Computable (fun q : (ℕ × BitString × BitString) × ℕ => q.1.2.1) := h_arg1_2_2_1.comp (h_arg1_2_2.comp h_arg1_1)
  have h_c2_args : Computable (fun q : (ℕ × BitString × BitString) × ℕ => (q.2, q.1.2.1)) := Computable.pair h_arg2_1 h_arg1_2_2_1_q
  exact Computable.of_eq (evOutEq_decide_computable.comp h_c2_args) (fun q => by rfl)

lemma truncGTerm_computable_cond (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) (d : ℕ) :
  Computable (fun q : (ℕ × BitString × BitString) × ℕ => decide (cumNum approx q.1.1 (q.2 + 1) q.1.2.2 ≤ 2 ^ (d + q.1.1) ∧ evOut q.2 = some q.1.2.1)) := by
  have h_c1 := truncGTerm_computable_cond_C1 hcomp d
  have h_c2 := truncGTerm_computable_cond_C2
  exact Computable.of_eq (Computable.cond h_c1 h_c2 (Computable.const false)) (fun q => decide_and_eq_cond.symm)

lemma truncGTerm_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) (d : ℕ) :
  Computable (truncGTerm approx d) := by
  have h_cond := truncGTerm_computable_cond hcomp d
  have h_then := truncGTerm_computable_then approx hcomp
  exact Computable.of_eq (Computable.cond h_cond h_then (Computable.const 0))
    (fun q => truncGTerm_eq_cond approx d q)

/-
The stage-`S` numerator is computable in `(S, out, ctx)`.
-/
lemma truncGapprox_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) (d : ℕ) :
    Computable (fun p : ℕ × BitString × BitString => truncGapprox approx d p.1 p.2.1 p.2.2) := by
  have hg : Computable₂ (fun p t => truncGTerm approx d (p, t)) :=
    truncGTerm_computable hcomp d
  exact Computable.of_eq
    (computable_range_sum (fun p t => truncGTerm approx d (p, t)) hg (fun p : ℕ × BitString × BitString => p.1)
      Computable.fst)
    (fun p => (truncGapprox_eq approx d p).symm)

/-! ### Uniform (index-parameterized) computability of the dyadic numerators

The lemmas above establish computability of the numerator chain for a single fixed
approximation `approx`. The following *uniform* variants thread an extra leading
index coordinate `i : ℕ` through the chain, so that an entire jointly-computable
*family* `b : ℕ → ℕ → BitString → BitString → ℕ` of approximations yields a jointly
computable numerator family. These are needed for the lower-semicomputability of a
countable mixture of sanitized enumerations (see `UniversalSemimeasure`). Each
proof mirrors the corresponding fixed-`approx` lemma with `b i` substituted and `i`
carried as a `Computable.fst`-style coordinate. -/

-- Nested product projections in the uniform computability witness normalize slowly in Lean 4.31.
lemma incNum_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (incNumUniformPacked b) := by
  have h_p22 : Computable (fun p : ℕ × ℕ × BitString × BitString => p.2.2) := Computable.snd.comp Computable.snd
  have h_p221 : Computable (fun p : ℕ × ℕ × BitString × BitString => p.2.2.1) := Computable.fst.comp h_p22
  have h_p222 : Computable (fun p : ℕ × ℕ × BitString × BitString => p.2.2.2) := Computable.snd.comp h_p22
  have hg_args : Computable (fun p : ℕ × ℕ × BitString × BitString => (p.1, 0, p.2.2.1, p.2.2.2)) :=
    Computable.pair Computable.fst (Computable.pair (Computable.const 0) (Computable.pair h_p221 h_p222))
  have hg : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 0 p.2.2.1 p.2.2.2) :=
    Computable.of_eq (hb.comp hg_args) (fun p => beta_pair4 b p.1 0 p.2.2.1 p.2.2.2)
  have hh : Computable₂ (fun (p : ℕ × ℕ × BitString × BitString) (k : ℕ) => b p.1 (k + 1) p.2.2.1 p.2.2.2 - 2 * b p.1 k p.2.2.1 p.2.2.2) := by
    have h_sub_comp := Primrec.nat_sub.to_comp
    have h_sub : Computable (fun p : ℕ × ℕ => p.1 - p.2) := h_sub_comp
    have h_q1 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1) := Computable.fst
    have h_q2 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.2) := Computable.snd
    have h_succ_q2 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.2 + 1) := Computable.succ.comp h_q2
    have h_q1_1 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.1) := Computable.fst.comp h_q1
    have h_q1_221 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.2.2.1) := h_p221.comp h_q1
    have h_q1_222 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.2.2.2) := h_p222.comp h_q1
    have h_f1_args : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => (q.1.1, q.2 + 1, q.1.2.2.1, q.1.2.2.2)) :=
      Computable.pair h_q1_1 (Computable.pair h_succ_q2 (Computable.pair h_q1_221 h_q1_222))
    have h_f1 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => b q.1.1 (q.2 + 1) q.1.2.2.1 q.1.2.2.2) :=
      Computable.of_eq (hb.comp h_f1_args) (fun q => beta_pair4 b q.1.1 (q.2 + 1) q.1.2.2.1 q.1.2.2.2)
    have h_f2_args : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => (q.1.1, q.2, q.1.2.2.1, q.1.2.2.2)) :=
      Computable.pair h_q1_1 (Computable.pair h_q2 (Computable.pair h_q1_221 h_q1_222))
    have h_b2 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => b q.1.1 q.2 q.1.2.2.1 q.1.2.2.2) :=
      Computable.of_eq (hb.comp h_f2_args) (fun q => beta_pair4 b q.1.1 q.2 q.1.2.2.1 q.1.2.2.2)
    have h_f2 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => 2 * b q.1.1 q.2 q.1.2.2.1 q.1.2.2.2) := computable_two_mul.comp h_b2
    exact Computable.of_eq (h_sub.comp (Computable.pair h_f1 h_f2)) (fun q => beta_pair Nat.sub _ _)
  have h_p21 : Computable (fun p : ℕ × ℕ × BitString × BitString => p.2.1) := Computable.fst.comp Computable.snd
  exact Computable.of_eq (f := fun p => Nat.casesOn p.2.1 (b p.1 0 p.2.2.1 p.2.2.2) (fun k => b p.1 (k + 1) p.2.2.1 p.2.2.2 - 2 * b p.1 k p.2.2.1 p.2.2.2))
    (Computable.nat_casesOn h_p21 hg hh)
    (fun p => incNumUniformPacked_eq_cases b p)

-- Nested product projections in the uniform computability witness normalize slowly in Lean 4.31.
lemma evNum_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (evNumUniformPacked b) := by
  have h_p21 : Computable (fun p : ℕ × ℕ × BitString => p.2.1) := Computable.fst.comp Computable.snd
  have hf : Computable (fun p : ℕ × ℕ × BitString => evOut p.2.1) := evOut_computable.comp h_p21
  have hg : Computable (fun p : ℕ × ℕ × BitString => (0 : ℕ)) := Computable.const 0
  have hh : Computable₂ (fun (p : ℕ × ℕ × BitString) (out : BitString) => incNum (b p.1) (evK p.2.1) out p.2.2) := by
    have h_q1 : Computable (fun q : (ℕ × ℕ × BitString) × BitString => q.1) := Computable.fst
    have h_q1_1 : Computable (fun q : (ℕ × ℕ × BitString) × BitString => q.1.1) := Computable.fst.comp h_q1
    have h_q1_21 : Computable (fun q : (ℕ × ℕ × BitString) × BitString => q.1.2.1) := Computable.fst.comp (Computable.snd.comp h_q1)
    have h_evK : Computable (fun q : (ℕ × ℕ × BitString) × BitString => evK q.1.2.1) := evK_computable.comp h_q1_21
    have h_q2 : Computable (fun q : (ℕ × ℕ × BitString) × BitString => q.2) := Computable.snd
    have h_q1_22 : Computable (fun q : (ℕ × ℕ × BitString) × BitString => q.1.2.2) := Computable.snd.comp (Computable.snd.comp h_q1)
    have h_args : Computable (fun q : (ℕ × ℕ × BitString) × BitString => (q.1.1, evK q.1.2.1, q.2, q.1.2.2)) :=
      Computable.pair h_q1_1 (Computable.pair h_evK (Computable.pair h_q2 h_q1_22))
    have h_inc : Computable (fun q : (ℕ × ℕ × BitString) × BitString => incNum (b q.1.1) (evK q.1.2.1) q.2 q.1.2.2) :=
      Computable.of_eq ((incNum_computable_uniform b hb).comp h_args) (fun q => incNumUniformPacked_eq b (q.1.1, evK q.1.2.1, q.2, q.1.2.2))
    exact h_inc
  exact Computable.of_eq (f := fun p => Option.casesOn (evOut p.2.1) 0 (fun o => incNum (b p.1) (evK p.2.1) o p.2.2))
    (Computable.option_casesOn hf hg hh)
    (fun p => evNumUniformPacked_eq_cases b p)

lemma cumNumTermUniform_ev_computable (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => evNum (b q.1.1) q.2 q.1.2.2.2) := by
  have h_q1 : Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => q.1) := Computable.fst
  have h_q1_1 : Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => q.1.1) := Computable.fst.comp h_q1
  have h_q2 : Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => q.2) := Computable.snd
  have h_q1_222 : Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => q.1.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp h_q1))
  have h_f1_args : Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => (q.1.1, q.2, q.1.2.2.2)) :=
    Computable.pair h_q1_1 (Computable.pair h_q2 h_q1_222)
  exact Computable.of_eq ((evNum_computable_uniform b hb).comp h_f1_args)
    (fun q => evNumUniformPacked_eq b (q.1.1, q.2, q.1.2.2.2))

lemma cumNumTermUniform_pow_computable :
    Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => 2 ^ (q.1.2.1 - evK q.2)) := by
  have h_q1 : Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => q.1) := Computable.fst
  have h_q2 : Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => q.2) := Computable.snd
  have h_q1_21 : Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => q.1.2.1) := Computable.fst.comp (Computable.snd.comp h_q1)
  have h_evK_q2 : Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => evK q.2) := evK_computable.comp h_q2
  have h_sub : Computable (fun q : (ℕ × ℕ × ℕ × BitString) × ℕ => q.1.2.1 - evK q.2) :=
    Primrec.nat_sub.to_comp.comp h_q1_21 h_evK_q2
  exact primrec_two_pow.to_comp.comp h_sub

lemma cumNumTermUniform_computable (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable₂ (cumNumTermUniform b) := by
  have h_f1 := cumNumTermUniform_ev_computable b hb
  have h_f2 := cumNumTermUniform_pow_computable
  have h_mul := Computable.comp Primrec.nat_mul.to_comp (Computable.pair h_f1 h_f2)
  exact Computable.of_eq h_mul
    (fun q => Eq.trans (beta_pair Nat.mul _ _) (cumNumTermUniform_eq_packed b q))

lemma cumNum_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (cumNumUniformPacked b) := by
  have h_g : Computable₂ (cumNumTermUniform b) := cumNumTermUniform_computable b hb
  have h_computable : Computable (fun p : ℕ × ℕ × ℕ × BitString => ∑ i ∈ Finset.range p.2.2.1, cumNumTermUniform b p i) :=
    computable_range_sum (cumNumTermUniform b) h_g
      (fun p : ℕ × ℕ × ℕ × BitString => p.2.2.1)
      (Computable.fst.comp (Computable.snd.comp Computable.snd))
  exact Computable.of_eq h_computable (fun p => (cumNumUniformPacked_eq b p).symm)

-- Cache the packed `evNum` argument before forming the product witness below.
lemma truncGTerm_computable_uniform_then_ev (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => evNum (b q.1.1) q.2 q.1.2.2.2) := by
  have h_q1 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1) := Computable.fst
  have h_q2 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.2) := Computable.snd
  have h_q1_1 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.1) := Computable.fst.comp h_q1
  have h_q1_222 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp h_q1))
  have h_arg_ev : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => (q.1.1, q.2, q.1.2.2.2)) := Computable.pair h_q1_1 (Computable.pair h_q2 h_q1_222)
  exact Computable.of_eq ((evNum_computable_uniform b hb).comp h_arg_ev)
    (fun q => evNumUniformPacked_eq b (q.1.1, q.2, q.1.2.2.2))

-- The power side is independent of the approximation family.
lemma truncGTerm_computable_uniform_then_pow :
    Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => 2 ^ (q.1.2.1 - evK q.2)) := by
  have h_q1 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1) := Computable.fst
  have h_q2 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.2) := Computable.snd
  have h_q1_21 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.2.1) := Computable.fst.comp (Computable.snd.comp h_q1)
  have h_evK : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => evK q.2) := evK_computable.comp h_q2
  have h_sub : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.2.1 - evK q.2) :=
    Primrec.nat_sub.to_comp.comp h_q1_21 h_evK
  exact primrec_two_pow.to_comp.comp h_sub

-- The expensive uniform subproofs are named above, so this product witness stays small.
lemma truncGTerm_computable_uniform_then (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
  Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => evNum (b q.1.1) q.2 q.1.2.2.2 * 2 ^ (q.1.2.1 - evK q.2)) := by
  have h_ev := truncGTerm_computable_uniform_then_ev b hb
  have h_pow := truncGTerm_computable_uniform_then_pow
  exact Computable.of_eq (Computable.comp Primrec.nat_mul.to_comp (Computable.pair h_ev h_pow))
    (fun q => beta_pair Nat.mul _ _)

lemma truncGTerm_computable_uniform_cond_A (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => cumNum (b q.1.1) q.1.2.1 (q.2 + 1) q.1.2.2.2) := by
  have h_q1 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1) := Computable.fst
  have h_q2 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.2) := Computable.snd
  have h_q1_1 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.1) := Computable.fst.comp h_q1
  have h_q1_21 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.2.1) := Computable.fst.comp (Computable.snd.comp h_q1)
  have h_q1_222 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp h_q1))
  have h_succ_q2 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.2 + 1) := Computable.succ.comp h_q2
  have h_A_args : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => (q.1.1, q.1.2.1, q.2 + 1, q.1.2.2.2)) :=
    Computable.pair h_q1_1 (Computable.pair h_q1_21 (Computable.pair h_succ_q2 h_q1_222))
  exact Computable.of_eq ((cumNum_computable_uniform b hb).comp h_A_args) (fun q => by unfold cumNumUniformPacked; rfl)

lemma truncGTerm_computable_uniform_cond_B (d : ℕ) :
    Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => 2 ^ (d + q.1.2.1)) := by
  have h_q1 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1) := Computable.fst
  have h_q1_21 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.2.1) := Computable.fst.comp (Computable.snd.comp h_q1)
  have h_d : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => d) := Computable.const d
  have h_add_d : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => d + q.1.2.1) :=
    Primrec.nat_add.to_comp.comp h_d h_q1_21
  exact primrec_two_pow.to_comp.comp h_add_d

lemma truncGTerm_computable_uniform_cond_C1 (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) (d : ℕ) :
    Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => decide (cumNum (b q.1.1) q.1.2.1 (q.2 + 1) q.1.2.2.2 ≤ 2 ^ (d + q.1.2.1))) := by
  obtain ⟨_, hle⟩ := Primrec.nat_le
  exact Computable.of_eq (hle.to_comp.comp (Computable.pair (truncGTerm_computable_uniform_cond_A b hb) (truncGTerm_computable_uniform_cond_B d)))
    (fun q => by simp)

lemma truncGTerm_computable_uniform_cond_C2 :
    Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => decide (evOut q.2 = some q.1.2.2.1)) := by
  have h_q1 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1) := Computable.fst
  have h_q2 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.2) := Computable.snd
  have h_q1_221 : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => q.1.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp h_q1))
  have h_c2_args : Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => (q.2, q.1.2.2.1)) := Computable.pair h_q2 h_q1_221
  exact Computable.of_eq (evOutEq_decide_computable.comp h_c2_args) (fun q => by rfl)

lemma truncGTerm_computable_uniform_cond (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2))
    (d : ℕ) :
    Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => decide (cumNum (b q.1.1) q.1.2.1 (q.2 + 1) q.1.2.2.2 ≤ 2 ^ (d + q.1.2.1) ∧ evOut q.2 = some q.1.2.2.1)) := by
  have h_c1 := truncGTerm_computable_uniform_cond_C1 b hb d
  have h_c2 := truncGTerm_computable_uniform_cond_C2
  exact Computable.of_eq (Computable.cond h_c1 h_c2 (Computable.const false)) (fun q => decide_and_eq_cond.symm)

lemma truncGTerm_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2))
    (d : ℕ) :
    Computable (truncGTermUniform b d) := by
  have h_cond := truncGTerm_computable_uniform_cond b hb d
  have h_then := truncGTerm_computable_uniform_then b hb
  exact Computable.of_eq (Computable.cond h_cond h_then (Computable.const 0))
    (fun q => truncGTermUniform_eq_cond b d q)

lemma truncGapprox_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2))
    (d : ℕ) :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      truncGapprox (b p.1) d p.2.1 p.2.2.1 p.2.2.2) := by
  have hg : Computable₂ (fun p t => truncGTermUniform b d (p, t)) :=
    truncGTerm_computable_uniform b hb d
  exact Computable.of_eq
    (computable_range_sum (fun p t => truncGTermUniform b d (p, t)) hg
      (fun p : ℕ × ℕ × BitString × BitString => p.2.1)
      (Computable.fst.comp Computable.snd))
    (fun p => (truncGapproxUniform_eq b d p).symm)

end Truncate

/-- **Dynamic truncation of a lower-semicomputable function to a global mass bound.**

Given a lower-semicomputable `f` and a level `d`, there is a lower-semicomputable
`g` that is *globally* `2^{d}`-subnormalized (`∀ ctx, ∑_out g out ctx ≤ 2^{d}`) and
agrees with `f` on every context whose own `f`-mass already respects the bound
(`∑_out f out ctx ≤ 2^{d} → g = f` on that context).

The construction is the online truncation `truncG`: enumerate all dyadic
increments of `f` as a single `ℕ`-indexed stream, accept an increment iff the
running cumulative mass stays `≤ 2^{d}`, and read off the accepted mass per
output as the supremum of exact dyadic numerators over `2^S`. -/
theorem IsLSC.truncate {f : BitString → BitString → ℝ≥0∞} (hf : IsLSC f) (d : ℕ) :
    ∃ g : BitString → BitString → ℝ≥0∞, IsLSC g ∧
      (∀ ctx : BitString, (∑' out : BitString, g out ctx) ≤ (2 : ℝ≥0∞) ^ d) ∧
      (∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ (2 : ℝ≥0∞) ^ d →
        ∀ out : BitString, g out ctx = f out ctx) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hf
  refine ⟨truncG approx d, ⟨truncGapprox approx d, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro S out ctx; exact truncGapprox_mono d S out ctx
  · intro out ctx; rfl
  · exact truncGapprox_computable hcomp d
  · intro ctx; exact tsum_truncG_le d ctx
  · intro ctx hle out; exact truncG_eq_f_of_le hmono hsup d ctx hle out

end Kolmogorov
