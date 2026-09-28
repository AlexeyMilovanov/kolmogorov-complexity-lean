import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part01
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.MonotoneComplexity.Dimension.DeficiencySemimeasure
import KolmogorovMathlib.MonotoneComplexity.SimpleTreeApproximation
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.TwoStage
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Rat.Denumerable

/-!
# Applications of the Kraft-Chaitin theorem, part 2

Grouping a computable family of dyadic lower approximations: the a priori measure of a
computably grouped family equals the grouped a priori measure up to a constant factor
(`aprioriMeasure_computable_grouping`), together with the dyadic-value arithmetic
(`dyadicValue_sup`, `dyadicValue_sum_range_dim`, `dyadicValue_ite`) that the argument needs.

SUV Exercise 98, p. 110.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-- The dyadic value of a finite supremum of numerators is the supremum of their dyadic values. -/
lemma dyadicValue_sup (S : Finset ℕ) (v : ℕ → ℕ) (k : ℕ) :
    dyadicValue (S.sup v) k = S.sup (fun i => dyadicValue (v i) k) := by
  induction S using Finset.induction with
  | empty => dsimp [dyadicValue]; simp
  | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.sup_insert, ← ih, dyadicValue_max]

/-- The dyadic value commutes with a case distinction on the numerator. -/
lemma dyadicValue_ite (P : Prop) [Decidable P] (a b s : ℕ) :
    dyadicValue (if P then a else b) s = if P then dyadicValue a s else dyadicValue b s := by
  split_ifs <;> rfl

/-- A finite sum of suprema of monotone sequences in `ℝ≥0∞` is the supremum of the sums. -/
lemma ENNReal_sum_iSup {ι : Type*} (FinS : Finset ι) (g : ι → ℕ → ℝ≥0∞)
    (hg : ∀ i ∈ FinS, Monotone (g i)) :
    (∑ i ∈ FinS, ⨆ k : ℕ, g i k) = ⨆ k : ℕ, ∑ i ∈ FinS, g i k := by
  classical
  induction FinS using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have ih_apply := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      rw [ih_apply]
      have h_mono_sum : Monotone (fun k : ℕ => ∑ i ∈ s, g i k) := fun s1 s2 hss =>
        Finset.sum_le_sum (fun i hi => hg i (Finset.mem_insert_of_mem hi) hss)
      have h_mono_a : Monotone (g a) := hg a (Finset.mem_insert_self a _)
      have h_add : (⨆ k : ℕ, g a k) + (⨆ k : ℕ, ∑ i ∈ s, g i k) =
          ⨆ k : ℕ, (g a k + ∑ i ∈ s, g i k) :=
        @ENNReal.iSup_add_iSup_of_monotone ℕ _ _ (g a) (fun k => ∑ i ∈ s, g i k) h_mono_a h_mono_sum
      rw [h_add]
      simp_rw [Finset.sum_insert ha]

/-- The stage numerators of the second component of the pair decomposition, obtained from those of
`m` by the index shift `f`. -/
def approxM2 (approx_m : ℕ → BitString → BitString → ℕ) (f : ℕ → ℕ)
    (s : ℕ) (y : BitString) (_ : BitString) : ℕ :=
  (Finset.range (s + 1)).sup (fun n =>
    if y = natBits (f n) then approx_m s (natBits n) [] else 0)

/-- The body of the second-component approximation is computable. -/
lemma approx_m2_body_computable (f : ℕ → ℕ) (hf : Computable f)
    (approx_m : ℕ → BitString → BitString → ℕ)
    (hcomp_m : Computable (fun p : ℕ × BitString × BitString => approx_m p.1 p.2.1 p.2.2)) :
    Computable (fun p : (ℕ × BitString × BitString) × ℕ =>
      if p.1.2.1 = natBits (f p.2) then approx_m p.1.1 (natBits p.2) [] else 0) := by
  have h_s : Computable (fun p : (ℕ × BitString × BitString) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have h_y : Computable (fun p : (ℕ × BitString × BitString) × ℕ => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have h_n : Computable (fun p : (ℕ × BitString × BitString) × ℕ => p.2) :=
    Computable.snd
  have h_fn : Computable (fun p : (ℕ × BitString × BitString) × ℕ => natBits (f p.2)) :=
    natBits_computable.comp (hf.comp h_n)
  have h_bits : Computable (fun p : (ℕ × BitString × BitString) × ℕ => natBits p.2) :=
    natBits_computable.comp h_n
  have h_then : Computable (fun p : (ℕ × BitString × BitString) × ℕ =>
      approx_m p.1.1 (natBits p.2) []) := by
    convert hcomp_m.comp (h_s.pair (h_bits.pair (Computable.const []))) using 1
  have h_else : Computable (fun _ : (ℕ × BitString × BitString) × ℕ => (0 : ℕ)) :=
    Computable.const 0
  have h_cond : Computable (fun p : (ℕ × BitString × BitString) × ℕ =>
      decide (p.1.2.1 = natBits (f p.2))) := by
    convert bitstring_eq_decide_computable.comp (h_y.pair h_fn) using 1
  convert Computable.cond h_cond h_then h_else using 1
  funext p
  dsimp; split_ifs with h
  · rw [decide_eq_true h]; rfl
  · rw [decide_eq_false h]; rfl

/-- The second-component approximation is computable. -/
lemma approx_m2_computable (f : ℕ → ℕ) (hf : Computable f)
    (approx_m : ℕ → BitString → BitString → ℕ)
    (hcomp_m : Computable (fun p : ℕ × BitString × BitString => approx_m p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString × BitString => approxM2 approx_m f p.1 p.2.1 p.2.2) :=
  @computable_finset_range_sup (ℕ × BitString × BitString) _
    (fun p => p.1 + 1)
    (fun p n => if p.2.1 = natBits (f n) then approx_m p.1 (natBits n) [] else 0)
    (Computable.succ.comp Computable.fst)
    (approx_m2_body_computable f hf approx_m hcomp_m)

/-- The stage numerators of the first component of the pair decomposition, obtained from those of
`m` by the index shift `f`. -/
def approxM1 (approx_m : ℕ → BitString → BitString → ℕ) (f : ℕ → ℕ)
    (s : ℕ) (x : BitString) (_ : BitString) : ℕ :=
  (Finset.range (s + 1)).sup (fun n =>
    if x = natBits n then
      ∑ k ∈ Finset.Ico (f n) (f (n + 1)), approx_m s (natBits k) []
    else 0)

/-- The body of the first-component approximation is computable. -/
lemma approx_m1_body_computable (f : ℕ → ℕ) (hf : Computable f)
    (approx_m : ℕ → BitString → BitString → ℕ)
    (hcomp_m : Computable (fun p : ℕ × BitString × BitString => approx_m p.1 p.2.1 p.2.2)) :
    Computable (fun p : (ℕ × BitString × BitString) × ℕ =>
      if p.1.2.1 = natBits p.2 then
        ∑ k ∈ Finset.Ico (f p.2) (f (p.2 + 1)), approx_m p.1.1 (natBits k) []
      else 0) := by
  have h_x : Computable (fun p : (ℕ × BitString × BitString) × ℕ => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have h_n : Computable (fun p : (ℕ × BitString × BitString) × ℕ => p.2) :=
    Computable.snd
  have h_bits_n : Computable (fun p : (ℕ × BitString × BitString) × ℕ => natBits p.2) :=
    natBits_computable.comp h_n
  have h_sum_inner : Computable (fun p : (ℕ × BitString × BitString) × ℕ =>
      ∑ k ∈ Finset.Ico (f p.2) (f (p.2 + 1)), approx_m p.1.1 (natBits k) []) := by
    have h_rw : (fun p : (ℕ × BitString × BitString) × ℕ =>
        ∑ k ∈ Finset.Ico (f p.2) (f (p.2 + 1)),
          approx_m p.1.1 (natBits k) []) =
        (fun p : (ℕ × BitString × BitString) × ℕ =>
        ∑ i ∈ Finset.range (f (p.2 + 1) - f p.2),
          approx_m p.1.1 (natBits (f p.2 + i)) []) := by
      funext p
      exact Finset.sum_Ico_eq_sum_range
        (fun k => approx_m p.1.1 (natBits k) []) (f p.2) (f (p.2 + 1))
    rw [h_rw]
    have h_len : Computable
        (fun p : (ℕ × BitString × BitString) × ℕ => f (p.2 + 1) - f p.2) := by
      have h_f1 : Computable (fun p : (ℕ × BitString × BitString) × ℕ =>
          f (p.2 + 1)) :=
        hf.comp (Computable.succ.comp h_n)
      have h_f2 : Computable (fun p : (ℕ × BitString × BitString) × ℕ => f p.2) :=
        hf.comp h_n
      convert (Primrec.to_comp Primrec.nat_sub).comp (h_f1.pair h_f2) using 1
    have h_fbody : Computable₂ (fun (p : (ℕ × BitString × BitString) × ℕ) (i : ℕ) =>
        approx_m p.1.1 (natBits (f p.2 + i)) []) := by
      have h_s' : Computable (fun q : ((ℕ × BitString × BitString) × ℕ) × ℕ => q.1.1.1) :=
        Computable.fst.comp (Computable.fst.comp Computable.fst)
      have h_fp2 : Computable (fun q : ((ℕ × BitString × BitString) × ℕ) × ℕ => f q.1.2) :=
        hf.comp (Computable.snd.comp Computable.fst)
      have h_i : Computable (fun q : ((ℕ × BitString × BitString) × ℕ) × ℕ => q.2) :=
        Computable.snd
      have h_k : Computable (fun q : ((ℕ × BitString × BitString) × ℕ) × ℕ => f q.1.2 + q.2) := by
        convert (Primrec.to_comp Primrec.nat_add).comp (h_fp2.pair h_i) using 1
      have h_bits : Computable (fun q : ((ℕ × BitString × BitString) × ℕ) × ℕ =>
          natBits (f q.1.2 + q.2)) :=
        natBits_computable.comp h_k
      convert hcomp_m.comp (h_s'.pair (h_bits.pair (Computable.const []))) using 1
    exact @computable_range_sum ((ℕ × BitString × BitString) × ℕ) _
      (fun p i => approx_m p.1.1 (natBits (f p.2 + i)) [])
      h_fbody (fun p => f (p.2 + 1) - f p.2) h_len
  have h_else : Computable (fun _ : (ℕ × BitString × BitString) × ℕ => (0 : ℕ)) :=
    Computable.const 0
  have h_cond : Computable (fun p : (ℕ × BitString × BitString) × ℕ =>
      decide (p.1.2.1 = natBits p.2)) := by
    convert bitstring_eq_decide_computable.comp (h_x.pair h_bits_n) using 1
  convert Computable.cond h_cond h_sum_inner h_else using 1
  funext p
  dsimp; split_ifs with h
  · rw [decide_eq_true h]; rfl
  · rw [decide_eq_false h]; rfl

/-- The first-component approximation is computable. -/
lemma approx_m1_computable (f : ℕ → ℕ) (hf : Computable f)
    (approx_m : ℕ → BitString → BitString → ℕ)
    (hcomp_m : Computable (fun p : ℕ × BitString × BitString => approx_m p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString × BitString => approxM1 approx_m f p.1 p.2.1 p.2.2) :=
  @computable_finset_range_sup (ℕ × BitString × BitString) _
    (fun p => p.1 + 1)
    (fun p n => if p.2.1 = natBits n then
      ∑ k ∈ Finset.Ico (f n) (f (n + 1)), approx_m p.1 (natBits k) []
    else 0)
    (Computable.succ.comp Computable.fst)
    (approx_m1_body_computable f hf approx_m hcomp_m)

open Classical in
/-- The grouped indicator measure on `f n` indices is a semimeasure. -/
private lemma isSemimeasure_approxM2 (m : BitString → ℝ≥0∞) (hm : IsSemimeasure m)
    (f : ℕ → ℕ) (hmono : StrictMono f) :
    IsSemimeasure (fun y =>
      if h : ∃ n, y = natBits (f n) then m (natBits (Nat.find h)) else 0) := by
  classical
  change (∑' y : BitString,
    if h : ∃ n, y = natBits (f n) then m (natBits (Nat.find h)) else 0) ≤ 1
  have h_natToBits_inj : Function.Injective natBits := natBits_injective
  have h_m2_eq (y : BitString) : (if h : ∃ n, y = natBits (f n) then
      m (natBits (Nat.find h)) else 0) =
      ∑' n : ℕ, if y = natBits (f n) then m (natBits n) else 0 := by
    dsimp
    split_ifs with h
    · have h_spec := Nat.find_spec h
      symm
      rw [tsum_eq_single (Nat.find h)]
      · rw [if_pos h_spec]
      · intro b hb
        rw [if_neg]
        intro h_b
        have h_fn_eq : f b = f (Nat.find h) := h_natToBits_inj (h_b.symm.trans h_spec)
        have h_b_eq : b = Nat.find h := hmono.injective h_fn_eq
        exact hb h_b_eq
    · symm
      rw [ENNReal.tsum_eq_zero]
      intro n
      rw [if_neg]
      intro h_n
      exact h ⟨n, h_n⟩
  have h_sum1 : (∑' y : BitString, if h : ∃ n, y = natBits (f n) then
      m (natBits (Nat.find h)) else 0) = ∑' n : ℕ, m (natBits n) := by
    simp_rw [h_m2_eq]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun n => ?_)
    rw [tsum_eq_single (natBits (f n))]
    · rw [if_pos rfl]
    · intro b hb
      rw [if_neg hb]
  have h_sum2 : (∑' n : ℕ, m (natBits n)) ≤ ∑' x : BitString, m x :=
    ENNReal.tsum_comp_le_tsum_of_injective h_natToBits_inj (fun x => m x)
  calc (∑' y : BitString, if h : ∃ n, y = natBits (f n) then
        m (natBits (Nat.find h)) else 0)
    _ = ∑' n : ℕ, m (natBits n) := h_sum1
    _ ≤ ∑' x : BitString, m x := h_sum2
    _ ≤ 1 := hm

/-- Monotonicity of the stage approximations for `approxM2`. -/
private lemma approxM2_monotone (approx_m : ℕ → BitString → BitString → ℕ)
    (hmono_m : ∀ s x ctx, dyadicValue (approx_m s x ctx) s ≤
      dyadicValue (approx_m (s + 1) x ctx) (s + 1))
    (f : ℕ → ℕ) (s : ℕ) (y ctx : BitString) :
    (dyadicValue (approxM2 approx_m f s y ctx) s : ℝ≥0∞) ≤
      dyadicValue (approxM2 approx_m f (s + 1) y ctx) (s + 1) := by
  dsimp [approxM2]
  rw [dyadicValue_sup, dyadicValue_sup]
  have h_sub : Finset.range (s + 1) ⊆ Finset.range (s + 2) :=
    Finset.range_mono (Nat.le_succ (s + 1))
  refine le_trans (Finset.sup_mono (f := fun n => dyadicValue (if y = natBits (f n) then
    approx_m s (natBits n) [] else 0) s) h_sub) (Finset.sup_le (fun n hn => ?_))
  by_cases h_eq : y = natBits (f n)
  · rw [if_pos h_eq]
    refine le_trans (hmono_m s (natBits n) []) ?_
    refine le_trans ?_ (Finset.le_sup hn)
    rw [dyadicValue_ite, if_pos h_eq]
  · rw [if_neg h_eq, dyadicValue_zero]
    exact zero_le _

/-- The stage enumeration `approx_m` approximates the semimeasure `m` from below: its dyadic
values increase with the stage and their supremum is `m x`. -/
private def DyadicApproximates (approx_m : ℕ → BitString → BitString → ℕ)
    (m : BitString → ℝ≥0∞) : Prop :=
  (∀ s x ctx, dyadicValue (approx_m s x ctx) s ≤
      dyadicValue (approx_m (s + 1) x ctx) (s + 1)) ∧
    ∀ x ctx, (⨆ s, dyadicValue (approx_m s x ctx) s) = m x

open Classical in
/-- The supremum over stage approximations for `approxM2` equals the grouped indicator value. -/
private lemma approxM2_iSup (m : BitString → ℝ≥0∞)
    (approx_m : ℕ → BitString → BitString → ℕ)
    (happrox : DyadicApproximates approx_m m)
    (f : ℕ → ℕ) (hmono : StrictMono f) (y ctx : BitString) :
    (⨆ s, dyadicValue (approxM2 approx_m f s y ctx) s) =
      if h : ∃ n, y = natBits (f n) then m (natBits (Nat.find h)) else 0 := by
  classical
  obtain ⟨hmono_m, hsup_m⟩ := happrox
  have h_natToBits_inj : Function.Injective natBits := natBits_injective
  by_cases h : ∃ n, y = natBits (f n)
  · rw [dif_pos h]
    set n0 := Nat.find h
    have h_spec : y = natBits (f n0) := Nat.find_spec h
    rw [h_spec]
    change (⨆ s, dyadicValue (approxM2 approx_m f s (natBits (f n0)) ctx) s) = m (natBits n0)
    apply le_antisymm
    · refine iSup_le (fun s => ?_)
      dsimp [approxM2]
      rw [dyadicValue_sup]
      refine Finset.sup_le (fun n hn => ?_)
      by_cases h_m : natBits (f n0) = natBits (f n)
      · rw [dyadicValue_ite, if_pos h_m]
        have h_fn_eq : f n0 = f n := h_natToBits_inj h_m
        have h_n_eq : n = n0 := hmono.injective h_fn_eq.symm
        subst h_n_eq
        exact le_trans (le_iSup (fun s' => dyadicValue (approx_m s' (natBits n0) []) s') s)
          (le_of_eq (hsup_m (natBits n0) []))
      · rw [dyadicValue_ite, if_neg h_m, dyadicValue_zero]
        exact zero_le _
    · have h_in : n0 ∈ Finset.range (n0 + 1) := Finset.mem_range.mpr (Nat.lt_succ_self n0)
      have h_match : natBits (f n0) = natBits (f n0) := rfl
      rw [← hsup_m (natBits n0) []]
      refine iSup_le (fun s => ?_)
      by_cases hs : s ≤ n0
      · have h_mono := monotone_nat_of_le_succ (fun k => hmono_m k (natBits n0) []) hs
        refine le_trans h_mono ?_
        refine le_iSup_of_le n0 ?_
        dsimp [approxM2]
        rw [dyadicValue_sup]
        refine le_trans ?_ (Finset.le_sup h_in)
        rw [dyadicValue_ite, if_pos h_match]
      · have h_s0_le : n0 ≤ s := le_of_not_ge hs
        refine le_iSup_of_le s ?_
        dsimp [approxM2]
        rw [dyadicValue_sup]
        have h_in_s : n0 ∈ Finset.range (s + 1) :=
          Finset.mem_range.mpr (Nat.lt_succ_of_le h_s0_le)
        refine le_trans ?_ (Finset.le_sup h_in_s)
        rw [dyadicValue_ite, if_pos h_match]
  · rw [dif_neg h]
    apply le_antisymm
    · refine iSup_le (fun s => ?_)
      dsimp [approxM2]
      rw [dyadicValue_sup]
      refine Finset.sup_le (fun n _ => ?_)
      by_cases h_m : y = natBits (f n)
      · exfalso
        exact h ⟨n, h_m⟩
      · rw [dyadicValue_ite, if_neg h_m, dyadicValue_zero]
    · exact zero_le _

open Classical in
/-- The grouped interval sum measure `m1` is a semimeasure. -/
private lemma isSemimeasure_approxM1 (m : BitString → ℝ≥0∞) (hm : IsSemimeasure m)
    (f : ℕ → ℕ) (hmono : StrictMono f) :
    IsSemimeasure (fun x =>
      if h : ∃ n, x = natBits n then
        ∑' k : ℕ, if f (Nat.find h) ≤ k ∧ k < f (Nat.find h + 1) then m (natBits k) else 0
      else 0) := by
  classical
  set S : ℕ → ℝ≥0∞ := fun n =>
    ∑' k : ℕ, if f n ≤ k ∧ k < f (n + 1) then m (natBits k) else 0
  have h_natToBits_inj : Function.Injective natBits := natBits_injective
  change (∑' x : BitString, if h : ∃ n, x = natBits n then S (Nat.find h) else 0) ≤ 1
  have h_m1_eq (x : BitString) : (if h : ∃ n, x = natBits n then S (Nat.find h) else 0) =
      ∑' n : ℕ, if x = natBits n then S n else 0 := by
    dsimp
    split_ifs with h
    · have h_spec := Nat.find_spec h
      symm
      rw [tsum_eq_single (Nat.find h)]
      · rw [if_pos h_spec]
      · intro b hb
        rw [if_neg]
        intro h_b
        exact hb (h_natToBits_inj (h_b.symm.trans h_spec))
    · symm
      rw [ENNReal.tsum_eq_zero]
      intro n
      rw [if_neg]
      intro h_n
      exact h ⟨n, h_n⟩
  have h_sum1 : (∑' x : BitString, if h : ∃ n, x = natBits n then S (Nat.find h) else 0) =
      ∑' n : ℕ, S n := by
    simp_rw [h_m1_eq]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun n => ?_)
    rw [tsum_eq_single (natBits n)]
    · rw [if_pos rfl]
    · intro b hb
      rw [if_neg hb]
  have h_sum2 : (∑' n : ℕ, S n) ≤ ∑' k : ℕ, m (natBits k) := by
    dsimp [S]
    rw [ENNReal.tsum_comm]
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    by_cases h_ex : ∃ n, f n ≤ k ∧ k < f (n + 1)
    · obtain ⟨nk, hnk⟩ := h_ex
      rw [tsum_eq_single nk]
      · rw [if_pos hnk]
      · intro b hb
        rw [if_neg]
        intro hbk
        have h_eq_nk : b = nk := by
          rcases lt_trichotomy b nk with h1 | h1 | h1
          · have h_le : f (b + 1) ≤ f nk := hmono.monotone h1
            omega
          · exact h1
          · have h_le : f (nk + 1) ≤ f b := hmono.monotone h1
            omega
        exact hb h_eq_nk
    · have h_zero : (∑' a : ℕ, if f a ≤ k ∧ k < f (a + 1) then m (natBits k) else 0) = 0 := by
        rw [ENNReal.tsum_eq_zero]
        intro a
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact h_ex ⟨a, h1, h2⟩
      rw [h_zero]
      exact zero_le _
  have h_sum3 : (∑' k : ℕ, m (natBits k)) ≤ ∑' x : BitString, m x :=
    ENNReal.tsum_comp_le_tsum_of_injective h_natToBits_inj (fun x => m x)
  calc (∑' x : BitString, if h : ∃ n, x = natBits n then S (Nat.find h) else 0)
    _ = ∑' n : ℕ, S n := h_sum1
    _ ≤ ∑' k : ℕ, m (natBits k) := h_sum2
    _ ≤ ∑' x : BitString, m x := h_sum3
    _ ≤ 1 := hm

/-- Monotonicity of the stage approximations for `approxM1`. -/
private lemma approxM1_monotone (approx_m : ℕ → BitString → BitString → ℕ)
    (hmono_m : ∀ s x ctx, dyadicValue (approx_m s x ctx) s ≤
      dyadicValue (approx_m (s + 1) x ctx) (s + 1))
    (f : ℕ → ℕ) (s : ℕ) (x ctx : BitString) :
    (dyadicValue (approxM1 approx_m f s x ctx) s : ℝ≥0∞) ≤
      dyadicValue (approxM1 approx_m f (s + 1) x ctx) (s + 1) := by
  dsimp [approxM1]
  rw [dyadicValue_sup, dyadicValue_sup]
  have h_sub : Finset.range (s + 1) ⊆ Finset.range (s + 2) :=
    Finset.range_mono (Nat.le_succ (s + 1))
  refine le_trans (Finset.sup_mono (f := fun n => dyadicValue (if x = natBits n then
    ∑ k ∈ Finset.Ico (f n) (f (n + 1)), approx_m s (natBits k) [] else 0) s) h_sub)
    (Finset.sup_le (fun n hn => ?_))
  by_cases h_match : x = natBits n
  · rw [if_pos h_match, dyadicValue_sum_range_dim]
    refine le_trans (Finset.sum_le_sum (fun k _ => hmono_m s (natBits k) [])) ?_
    rw [← dyadicValue_sum_range_dim]
    refine le_trans ?_ (Finset.le_sup hn)
    rw [dyadicValue_ite, if_pos h_match]
  · rw [if_neg h_match, dyadicValue_zero]
    exact zero_le _

open Classical in
/-- The supremum over stage approximations for `approxM1` equals the grouped interval sum. -/
private lemma approxM1_iSup (m : BitString → ℝ≥0∞)
    (approx_m : ℕ → BitString → BitString → ℕ)
    (happrox : DyadicApproximates approx_m m)
    (f : ℕ → ℕ) (x ctx : BitString) :
    (⨆ s, dyadicValue (approxM1 approx_m f s x ctx) s) =
      if h : ∃ n, x = natBits n then
        ∑' k : ℕ, if f (Nat.find h) ≤ k ∧ k < f (Nat.find h + 1) then m (natBits k) else 0
      else 0 := by
  classical
  obtain ⟨hmono_m, hsup_m⟩ := happrox
  set S : ℕ → ℝ≥0∞ := fun n =>
    ∑' k : ℕ, if f n ≤ k ∧ k < f (n + 1) then m (natBits k) else 0
  have h_natToBits_inj : Function.Injective natBits := natBits_injective
  split_ifs with h
  · set n0 := Nat.find h
    have h_spec : x = natBits n0 := Nat.find_spec h
    rw [h_spec]
    change (⨆ s, dyadicValue (approxM1 approx_m f s (natBits n0) ctx) s) = S n0
    have h_in : n0 ∈ Finset.range (n0 + 1) := Finset.mem_range.mpr (Nat.lt_succ_self n0)
    have h_match : natBits n0 = natBits n0 := rfl
    have h_S_eq : S n0 = ∑ k ∈ Finset.Ico (f n0) (f (n0 + 1)), m (natBits k) := by
      dsimp [S]
      refine (tsum_eq_sum (s := Finset.Ico (f n0) (f (n0 + 1)))
        (f := fun k => if f n0 ≤ k ∧ k < f (n0 + 1) then
          m (natBits k) else 0) ?_).trans ?_
      · intro k hk
        have h_not : ¬ (f n0 ≤ k ∧ k < f (n0 + 1)) := by
          intro ⟨h1, h2⟩
          rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
          cases hk <;> omega
        dsimp only
        rw [if_neg h_not]
      · refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_Ico] at hk
        rw [if_pos hk]
    apply le_antisymm
    · refine iSup_le (fun s => ?_)
      dsimp [approxM1]
      rw [dyadicValue_sup]
      refine Finset.sup_le (fun n hn => ?_)
      by_cases h_m : natBits n0 = natBits n
      · rw [dyadicValue_ite, if_pos h_m]
        have h_n_eq : n = n0 := h_natToBits_inj h_m.symm
        subst h_n_eq
        rw [h_S_eq, dyadicValue_sum_range_dim]
        exact Finset.sum_le_sum (fun k _ => le_trans
          (le_iSup (fun s' => dyadicValue (approx_m s' (natBits k) []) s') s)
          (le_of_eq (hsup_m (natBits k) [])))
      · rw [dyadicValue_ite, if_neg h_m, dyadicValue_zero]
        exact zero_le _
    · rw [h_S_eq]
      have h_sum_sup : (∑ k ∈ Finset.Ico (f n0) (f (n0 + 1)),
          m (natBits k)) =
          ∑ k ∈ Finset.Ico (f n0) (f (n0 + 1)),
            ⨆ s, dyadicValue (approx_m s (natBits k) []) s := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hsup_m (natBits k) []]
      rw [h_sum_sup]
      rw [@ENNReal_sum_iSup ℕ (Finset.Ico (f n0) (f (n0 + 1)))
        (fun (i : ℕ) (k : ℕ) => dyadicValue (approx_m k (natBits i) []) k)
        (fun i _ => @monotone_nat_of_le_succ ℝ≥0∞ _
          (fun k => dyadicValue (approx_m k (natBits i) []) k)
          (fun k' => hmono_m k' (natBits i) []))]
      refine iSup_le (fun s => ?_)
      by_cases hs : s ≤ n0
      · have h_mono : (∑ k ∈ Finset.Ico (f n0) (f (n0 + 1)),
            dyadicValue (approx_m s (natBits k) []) s) ≤
            ∑ k ∈ Finset.Ico (f n0) (f (n0 + 1)),
              dyadicValue (approx_m n0 (natBits k) []) n0 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact monotone_nat_of_le_succ (fun k' => hmono_m k' (natBits k) []) hs
        refine le_trans h_mono ?_
        refine le_iSup_of_le n0 ?_
        dsimp [approxM1]
        rw [dyadicValue_sup]
        refine le_trans ?_ (Finset.le_sup h_in)
        rw [dyadicValue_ite, if_pos h_match, dyadicValue_sum_range_dim]
      · have h_s0_le : n0 ≤ s := le_of_not_ge hs
        have h_in_s : n0 ∈ Finset.range (s + 1) :=
          Finset.mem_range.mpr (Nat.lt_succ_of_le h_s0_le)
        refine le_iSup_of_le s ?_
        dsimp [approxM1]
        rw [dyadicValue_sup]
        refine le_trans ?_ (Finset.le_sup h_in_s)
        rw [dyadicValue_ite, if_pos h_match, dyadicValue_sum_range_dim]
  · apply le_antisymm
    · refine iSup_le (fun s => ?_)
      dsimp [approxM1]
      rw [dyadicValue_sup]
      refine Finset.sup_le (fun n _ => ?_)
      by_cases h_match : x = natBits n
      · exfalso
        exact h ⟨n, h_match⟩
      · rw [dyadicValue_ite, if_neg h_match, dyadicValue_zero]
    · exact zero_le _

open Classical in
/-- Derives the upper bound factor for grouped sum from universal semimeasure domination. -/
private lemma aprioriMeasure_computable_grouping_upper (m : BitString → ℝ≥0∞)
    (hm : IsUniversalSemimeasure m)
    (S : ℕ → ℝ≥0∞) (c0 : ℝ≥0∞) (hc0_pos : 0 < c0)
    (hc0 : ∀ x, c0 * (if h : ∃ n, x = natBits n then S (Nat.find h) else 0) ≤ m x) (n : ℕ) :
    S n ≤ c0⁻¹ * m (natBits n) := by
  classical
  have h_natToBits_inj : Function.Injective natBits := natBits_injective
  have h_dom := hc0 (natBits n)
  have h_exist : ∃ n0, natBits n = natBits n0 := ⟨n, rfl⟩
  rw [dif_pos h_exist] at h_dom
  have h_spec := Nat.find_spec h_exist
  have h_n_eq : Nat.find h_exist = n := h_natToBits_inj h_spec.symm
  rw [h_n_eq] at h_dom
  have hc0_ne_zero : c0 ≠ 0 := ne_of_gt hc0_pos
  change S n ≤ c0⁻¹ * m (natBits n)
  by_cases hc0_top : c0 = ⊤
  · subst hc0_top
    by_cases hS : S n = 0
    · rw [hS]
      exact zero_le _
    · have h_top_mul : (⊤ : ℝ≥0∞) * S n = ⊤ := ENNReal.top_mul hS
      rw [h_top_mul] at h_dom
      exfalso
      have h_m_top : m (natBits n) = ⊤ := top_unique h_dom
      have h_m_le1 : (∑' x : BitString, m x) ≤ 1 := hm.1.1
      have h_tsum_top : (∑' x : BitString, m x) = ⊤ :=
        ENNReal.tsum_eq_top_of_eq_top ⟨natBits n, h_m_top⟩
      rw [h_tsum_top] at h_m_le1
      exact ENNReal.top_ne_one (top_unique h_m_le1).symm
  · have h_le_div : S n ≤ m (natBits n) / c0 :=
      (ENNReal.le_div_iff_mul_le (Or.inl hc0_ne_zero) (Or.inl hc0_top)).mpr
        (by rwa [mul_comm] at h_dom)
    rwa [div_eq_mul_inv, mul_comm] at h_le_div

/-- **Exercise 102.** Grouping the a priori probability over the computable
intervals `[f n, f (n+1))` gives back `m(n)` up to a constant factor. -/
theorem aprioriMeasure_computable_grouping (m : BitString → ℝ≥0∞)
    (hm : IsUniversalSemimeasure m) (f : ℕ → ℕ) (hf : Computable f) (hmono : StrictMono f) :
    ∃ c₁ c₂ : ℝ≥0∞, 0 < c₁ ∧ c₂ ≠ ⊤ ∧ ∀ n : ℕ,
      c₁ * m (natBits n) ≤
          ∑' k : ℕ, (if f n ≤ k ∧ k < f (n + 1) then m (natBits k) else 0) ∧
        (∑' k : ℕ, (if f n ≤ k ∧ k < f (n + 1) then m (natBits k) else 0)) ≤
          c₂ * m (natBits n) := by
  classical
  obtain ⟨approx_m, hmono_m, hsup_m_raw, hcomp_m⟩ := hm.1.2
  have hsup_m (x : BitString) (ctx : BitString) :
      (⨆ s, dyadicValue (approx_m s x ctx) s) = m x := hsup_m_raw x ctx
  have h_natToBits_inj : Function.Injective natBits := natBits_injective
  set S : ℕ → ℝ≥0∞ := fun n =>
    ∑' k : ℕ, if f n ≤ k ∧ k < f (n + 1) then m (natBits k) else 0
  set m2 : BitString → ℝ≥0∞ := fun y =>
    if h : ∃ n, y = natBits (f n) then m (natBits (Nat.find h)) else 0
  have hm2_semi : IsSemimeasure m2 := isSemimeasure_approxM2 m hm.1.1 f hmono
  have hmono_m2 : ∀ s y ctx, (dyadicValue (approxM2 approx_m f s y ctx) s : ℝ≥0∞) ≤
      dyadicValue (approxM2 approx_m f (s + 1) y ctx) (s + 1) :=
    approxM2_monotone approx_m hmono_m f
  have hsup_m2 : ∀ y ctx, (⨆ s, dyadicValue (approxM2 approx_m f s y ctx) s) = m2 y :=
    approxM2_iSup m approx_m ⟨hmono_m, hsup_m⟩ f hmono
  have hcomp_m2 : Computable (fun p : ℕ × BitString × BitString =>
      approxM2 approx_m f p.1 p.2.1 p.2.2) :=
    approx_m2_computable f hf approx_m hcomp_m
  have hm2_lsc : IsLowerSemicomputableSemimeasure m2 :=
    ⟨hm2_semi, ⟨approxM2 approx_m f, hmono_m2, hsup_m2, hcomp_m2⟩⟩
  obtain ⟨c1, hc1_pos, hc1⟩ := hm.2 m2 hm2_lsc
  have h_lower (n : ℕ) : c1 * m (natBits n) ≤ S n := by
    have h_exist : ∃ n0, natBits (f n) = natBits (f n0) := ⟨n, rfl⟩
    have h_m2_val : m2 (natBits (f n)) = m (natBits n) := by
      dsimp [m2]
      rw [dif_pos h_exist]
      have h_find_spec := Nat.find_spec h_exist
      have h_f_eq : f (Nat.find h_exist) = f n := h_natToBits_inj h_find_spec.symm
      rw [hmono.injective h_f_eq]
    have h_dom := hc1 (natBits (f n))
    rw [h_m2_val] at h_dom
    have h_fn_in : f n ≤ f n ∧ f n < f (n + 1) := ⟨le_rfl, hmono (Nat.lt_succ_self n)⟩
    have h_single : m (natBits (f n)) ≤ S n := by
      have h_le := ENNReal.le_tsum (f := fun k =>
        if f n ≤ k ∧ k < f (n + 1) then m (natBits k) else 0) (f n)
      rw [if_pos h_fn_in] at h_le
      exact h_le
    exact le_trans h_dom h_single
  set m1 : BitString → ℝ≥0∞ := fun x =>
    if h : ∃ n, x = natBits n then S (Nat.find h) else 0
  have hm1_semi : IsSemimeasure m1 := isSemimeasure_approxM1 m hm.1.1 f hmono
  have hmono_m1 : ∀ s x ctx, (dyadicValue (approxM1 approx_m f s x ctx) s : ℝ≥0∞) ≤
      dyadicValue (approxM1 approx_m f (s + 1) x ctx) (s + 1) :=
    approxM1_monotone approx_m hmono_m f
  have hsup_m1 : ∀ x ctx, (⨆ s, dyadicValue (approxM1 approx_m f s x ctx) s) = m1 x :=
    approxM1_iSup m approx_m ⟨hmono_m, hsup_m⟩ f
  have hcomp_m1 : Computable (fun p : ℕ × BitString × BitString =>
      approxM1 approx_m f p.1 p.2.1 p.2.2) :=
    approx_m1_computable f hf approx_m hcomp_m
  have hm1_lsc : IsLowerSemicomputableSemimeasure m1 :=
    ⟨hm1_semi, ⟨approxM1 approx_m f, hmono_m1, hsup_m1, hcomp_m1⟩⟩
  obtain ⟨c0, hc0_pos, hc0⟩ := hm.2 m1 hm1_lsc
  use c1, c0⁻¹
  refine ⟨hc1_pos, ENNReal.inv_ne_top.mpr (ne_of_gt hc0_pos), fun n => ⟨h_lower n, ?_⟩⟩
  exact aprioriMeasure_computable_grouping_upper m hm S c0 hc0_pos hc0 n

end Kolmogorov

