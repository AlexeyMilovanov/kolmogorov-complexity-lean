import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.DyadicEnumeration
import KolmogorovMathlib.AlgorithmicRandomness.LSCConstruction
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.MonotoneComplexity.SimpleTreeApproximation

/-!
# Between suprema, monotone limits and sums

The three presentations of SUV Theorem 40 are shown equivalent to each other here.

`isLowerSemicomputableFun_of_isSupremum` closes the circle back to lower semicomputability;
its computability obligation is discharged by taking the enumeration of `DyadicEnumeration`
apart into the pieces `stageOf`, `stringOf`, `getA`, `getApprox`, `getB`, `getCond` and
proving each computable.

`isMonotoneLimit_of_isSupremum` replaces a supremum by the running maxima
`monotoneMaxApprox`, `isSupremum_of_isMonotoneLimit` is the converse, and
`isSum_of_isMonotoneLimit_proof` differences a monotone limit into the sum of the nonnegative
terms `monotoneTerm`.  The remaining implication, from a sum back to a monotone limit, and the
statement combining all of them, are in `Characterization`.
-/

namespace Kolmogorov
open MeasureTheory Topology
open scoped ENNReal NNReal

/-- The stage component of the packed argument of the enumeration. -/
def stageOf (p : ((ℤ × ℤ) × ℕ) × BitString) : ℕ := p.1.2.unpair.1
/-- The stage component of the packed argument is computable. -/
lemma comp_s : Computable stageOf :=
  @Computable.comp (((ℤ × ℤ) × ℕ) × BitString) ((ℤ × ℤ) × ℕ) ℕ _ _ _
    (fun p => p.2.unpair.1) Prod.fst
    (@Computable.comp ((ℤ × ℤ) × ℕ) ℕ ℕ _ _ _
      (fun i => i.unpair.1) Prod.snd (Primrec.fst.comp Primrec.unpair).to_comp
          (Computable.snd (α := ℤ × ℤ) (β := ℕ)))
    (Computable.fst (α := (ℤ × ℤ) × ℕ) (β := BitString))

/-- The string component of the packed argument of the enumeration. -/
def stringOf (p : ((ℤ × ℤ) × ℕ) × BitString) : BitString := p.2
/-- The string component of the packed argument is computable. -/
lemma comp_x : Computable stringOf := Computable.snd (α := (ℤ × ℤ) × ℕ) (β := BitString)

/-- The power `2^s` attached to the stage component of the packed argument. -/
def twoPowStage (p : ((ℤ × ℤ) × ℕ) × BitString) : ℤ := Int.ofNat (2^stageOf p)
/-- The power of two attached to the stage component is computable. -/
lemma comp_2_pow_s : Computable twoPowStage := by
  have h1 : Computable (fun s : ℕ => 2^s) := by
    have h_eq : (fun s : ℕ => 2^s) = (fun s => (bitStringsOfLength s).length) := by
      funext s
      exact (length_bitStringsOfLength s).symm
    rw [h_eq]
    exact Computable.comp Primrec.list_length.to_comp computable_bitStringsOfLength
  exact @Computable.comp (((ℤ × ℤ) × ℕ) × BitString) ℕ ℤ _ _ _
    (fun n => Int.ofNat n) (fun p => 2^stageOf p) comp_ofNat
    (@Computable.comp (((ℤ × ℤ) × ℕ) × BitString) ℕ ℕ _ _ _
      (fun s => 2^s) stageOf h1 comp_s)

/-- The left-hand side `q.num · 2^s` of the comparison performed by the enumeration. -/
def getA (p : ((ℤ × ℤ) × ℕ) × BitString) : ℤ := getQNum p * twoPowStage p
/-- The left-hand side of the enumeration's comparison is computable. -/
lemma comp_A : Computable getA :=
  @Computable.comp (((ℤ × ℤ) × ℕ) × BitString) (ℤ × ℤ) ℤ _ _ _
    (fun pair => pair.1 * pair.2) (fun p => (getQNum p, twoPowStage p))
    comp_mul_int (@Computable.pair (((ℤ × ℤ) × ℕ) × BitString) ℤ ℤ _ _ _ getQNum twoPowStage
        comp_q_num comp_2_pow_s)

/-- The approximation value at the stage and string of the packed argument, as an integer. -/
def getApprox (approx : ℕ → BitString → ℕ) (p : ((ℤ × ℤ) × ℕ) × BitString) : ℤ := Int.ofNat
    (approx (stageOf p) (stringOf p))
/-- The approximation value at the packed argument is computable. -/
lemma comp_approx {approx : ℕ → BitString → ℕ} (hcomp : Computable (fun p : ℕ × BitString =>
    approx p.1 p.2)) : Computable (getApprox approx) :=
  @Computable.comp (((ℤ × ℤ) × ℕ) × BitString) ℕ ℤ _ _ _
    (fun n => Int.ofNat n) (fun p => approx (stageOf p) (stringOf p))
    comp_ofNat
    (@Computable.comp (((ℤ × ℤ) × ℕ) × BitString) (ℕ × BitString) ℕ _ _ _
      (fun pair => approx pair.1 pair.2) (fun p => (stageOf p, stringOf p))
      hcomp (@Computable.pair (((ℤ × ℤ) × ℕ) × BitString) ℕ BitString _ _ _ stageOf stringOf comp_s
          comp_x))

/-- The right-hand side `approx · q.den` of the comparison performed by the enumeration. -/
def getB (approx : ℕ → BitString → ℕ) (p : ((ℤ × ℤ) × ℕ) × BitString) : ℤ := getApprox approx
    p * getQDen p
/-- The right-hand side of the enumeration's comparison is computable. -/
lemma comp_B {approx : ℕ → BitString → ℕ}
    (hcomp : Computable (fun p : ℕ × BitString => approx p.1 p.2)) : Computable (getB approx) :=
  @Computable.comp (((ℤ × ℤ) × ℕ) × BitString) (ℤ × ℤ) ℤ _ _ _
    (fun pair => pair.1 * pair.2) (fun p => (getApprox approx p, getQDen p))
    comp_mul_int (@Computable.pair (((ℤ × ℤ) × ℕ) × BitString) ℤ ℤ _ _ _ (getApprox approx)
        getQDen (comp_approx hcomp) comp_q_den)

/-- The comparison test performed by the enumeration at the packed argument. -/
def getCond (approx : ℕ → BitString → ℕ) (p : ((ℤ × ℤ) × ℕ) × BitString) : Bool := decide
    (getA p < getB approx p)
/-- The comparison test of the enumeration is computable. -/
lemma comp_cond {approx : ℕ → BitString → ℕ}
    (hcomp : Computable (fun p : ℕ × BitString => approx p.1 p.2)) : Computable (getCond approx) :=
  @Computable.comp (((ℤ × ℤ) × ℕ) × BitString) (ℤ × ℤ) Bool _ _ _
    (fun pair => decide (pair.1 < pair.2)) (fun p => (getA p, getB approx p))
    comp_decide_int_lt (@Computable.pair (((ℤ × ℤ) × ℕ) × BitString) ℤ ℤ _ _ _ getA (getB
        approx) comp_A (comp_B hcomp))

/-- The enumeration, taken with the numerator and denominator supplied separately as integers,
is computable. -/
lemma dyadicEnum_int_comp {approx : ℕ → BitString → ℕ}
    (hcomp : Computable (fun p : ℕ × BitString => approx p.1 p.2)) :
    Computable (fun p : (ℤ × ℤ) × ℕ =>
      Option.bind (bitStringsOfLength p.2.unpair.1)[p.2.unpair.2]? (fun x =>
        bif decide (p.1.1 * ((2^p.2.unpair.1 : ℕ) : ℤ) < (approx p.2.unpair.1 x : ℤ) * p.1.2)
        then some x else none
      )) := by
  have h_g : Computable₂ (fun (p : (ℤ × ℤ) × ℕ) (x : BitString) =>
      bif decide (p.1.1 * ((2^p.2.unpair.1 : ℕ) : ℤ) < (approx p.2.unpair.1 x : ℤ) * p.1.2) then
          some x else none) := by
    have : (fun (p : (ℤ × ℤ) × ℕ) (x : BitString) =>
      bif decide (p.1.1 * ((2^p.2.unpair.1 : ℕ) : ℤ) < (approx p.2.unpair.1 x : ℤ) * p.1.2) then
          some x else none) =
      (fun p x => bif getCond approx (p, x) then some x else none) := by
      funext p x
      rfl
    rw [this]
    exact Computable.cond (comp_cond hcomp) (Computable.option_some.comp Computable.snd)
        (Computable.const none)
  exact Computable.option_bind h_f_fast h_g

/-- The enumeration of the superlevel sets is computable in the rational and the index. -/
lemma dyadicEnum_comp {approx : ℕ → BitString → ℕ}
    (hcomp : Computable (fun p : ℕ × BitString => approx p.1 p.2)) :
    Computable (fun p : ℚ × ℕ => dyadicEnum approx p.1 p.2) := by
  have : (fun p : ℚ × ℕ => dyadicEnum approx p.1 p.2) = fun p =>
    (fun p : (ℤ × ℤ) × ℕ =>
      Option.bind (bitStringsOfLength p.2.unpair.1)[p.2.unpair.2]? (fun x =>
        bif decide (p.1.1 * ((2^p.2.unpair.1 : ℕ) : ℤ) < (approx p.2.unpair.1 x : ℤ) * p.1.2)
        then some x else none
      )) ((p.1.num, (p.1.den : ℤ)), p.2) := by
    funext p
    unfold dyadicEnum
    dsimp
    split
    next h =>
      have h_get : (bitStringsOfLength p.2.unpair.1)[p.2.unpair.2]? = some
          ((bitStringsOfLength p.2.unpair.1).get ⟨p.2.unpair.2, h⟩) := by
        exact List.getElem?_eq_getElem h
      rw [h_get]
      dsimp [Option.bind]
      split
      next h_lt =>
        rw [decide_eq_true h_lt]
        rfl
      next h_nlt =>
        rw [decide_eq_false h_nlt]
        rfl
    next h =>
      have h_get : (bitStringsOfLength p.2.unpair.1)[p.2.unpair.2]? = none := by
        exact List.getElem?_eq_none (by omega)
      rw [h_get]
      rfl
  rw [this]
  have h_base : Computable (fun p : ℚ × ℕ => ((p.1.num, (p.1.den : ℤ)), p.2)) :=
    @Computable.pair (ℚ × ℕ) (ℤ × ℤ) ℕ _ _ _
      (fun p => (p.1.num, (p.1.den : ℤ)))
      (fun p => p.2)
      (@Computable.pair (ℚ × ℕ) ℤ ℤ _ _ _
        (fun p => p.1.num)
        (fun p => (p.1.den : ℤ))
        (computable_ratNum.comp Computable.fst)
        (comp_ofNat.comp (computable_ratDen.comp Computable.fst)))
      Computable.snd
  exact Computable.comp (dyadicEnum_int_comp hcomp) h_base

/-- A supremum of computable basic functions is lower semicomputable. -/
lemma isLowerSemicomputableFun_of_isSupremum {f : CantorSeq → ℝ≥0∞}
    (hf : IsSupremumOfComputableBasicFunctions f) : IsLowerSemicomputableFun f := by
  rcases hf with ⟨approx, hcomp, hsup⟩
  use dyadicEnum approx
  constructor
  · exact dyadicEnum_comp hcomp
  · intro q
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Option.elim]
    by_cases hq : (q : ℝ) < 0
    · have hq_num : q.num < 0 := Rat.num_neg.mpr (by exact_mod_cast hq)
      have h_s : (cantorPrefix w 0).length = 0 := by simp
      have h_lt : q.num * ((2^0 : ℕ) : ℤ) < (approx 0 (cantorPrefix w 0) : ℤ) * q.den := by
        simp only [pow_zero, Nat.cast_one, mul_one]
        have h1 : 0 ≤ (approx 0 (cantorPrefix w 0) : ℤ) := by positivity
        have h2 : 0 < (q.den : ℤ) := by exact_mod_cast q.den_pos
        have h3 : 0 ≤ (approx 0 (cantorPrefix w 0) : ℤ) * q.den := mul_nonneg h1 (le_of_lt h2)
        omega
      have h_ex := (dyadicEnum_spec q 0 (cantorPrefix w 0) h_s).mp h_lt
      constructor
      · intro _
        rcases h_ex with ⟨i, hi⟩
        use i
        rw [hi]
        exact mem_cantorCylinder_cantorPrefix w 0
      · intro _
        exact Or.inl hq
    · push_neg at hq
      constructor
      · intro h
        cases h with
        | inl h_lt =>
          have h_false : False := by linarith
          contradiction
        | inr h_f =>
          rw [hsup w] at h_f
          have h_ex : ∃ s, ENNReal.ofReal (q : ℝ) < dyadicValue (approx s (cantorPrefix w s)) s
              := lt_iSup_iff.mp h_f
          rcases h_ex with ⟨s, hs⟩
          have h_s : (cantorPrefix w s).length = s := by simp
          have h_lt : q.num * ((2^s : ℕ) : ℤ) < (approx s (cantorPrefix w s) : ℤ) * q.den :=
              (bridge q (approx s (cantorPrefix w s)) s hq).mp hs
          have h_ex2 := (dyadicEnum_spec q s (cantorPrefix w s) h_s).mp h_lt
          rcases h_ex2 with ⟨i, hi⟩
          use i
          rw [hi]
          exact mem_cantorCylinder_cantorPrefix w s
      · intro h
        rcases h with ⟨i, hi⟩
        cases h_eq : dyadicEnum approx q i with
        | none =>
          rw [h_eq] at hi
          contradiction
        | some x =>
          rw [h_eq] at hi
          have h_lt := (dyadicEnum_spec q x.length x rfl).mpr ⟨i, h_eq⟩
          right
          rw [hsup w]
          have hx_eq : x = cantorPrefix w x.length :=
              (cantorPrefix_eq_of_mem_cantorCylinder rfl hi).symm
          have h_lt2 : ENNReal.ofReal (q : ℝ) < dyadicValue
              (approx x.length (cantorPrefix w x.length)) x.length := by
            rw [← hx_eq]
            exact (bridge q (approx x.length x) x.length hq).mpr h_lt
          exact h_lt2.trans_le
              (le_iSup (fun s => dyadicValue (approx s (cantorPrefix w s)) s) x.length)

/-- Extending a finite supremum by one more term. -/
lemma max_iSup_range_succ (f : ℕ → ℝ≥0∞) (s : ℕ) :
    max (⨆ t ∈ Finset.range (s + 1), f t) (f (s + 1)) = ⨆ t ∈ Finset.range (s + 1 + 1), f t := by
  apply le_antisymm
  · apply max_le
    · refine iSup_le fun t => iSup_le fun ht => ?_
      have : t ∈ Finset.range (s + 1 + 1) := by
        rw [Finset.mem_range] at ht ⊢
        omega
      exact le_iSup_of_le t (le_iSup_of_le this le_rfl)
    · have : s + 1 ∈ Finset.range (s + 1 + 1) := by
        rw [Finset.mem_range]
        omega
      exact le_iSup_of_le (s + 1) (le_iSup_of_le this le_rfl)
  · refine iSup_le fun t => iSup_le fun ht => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff, le_iff_lt_or_eq] at ht
    cases ht with
    | inl hlt =>
      have : t ∈ Finset.range (s + 1) := Finset.mem_range.mpr hlt
      exact le_max_of_le_left (le_iSup_of_le t (le_iSup_of_le this le_rfl))
    | inr heq =>
      rw [heq]
      exact le_max_right _ _

/-- The running maximum of the dyadic terms up to a stage, kept in numerator form. -/
def monotoneMaxApprox (term : ℕ → BitString → ℕ) : ℕ → BitString → ℕ
| 0, x => term 0 (x.take 0)
| s + 1, x => max (2 * monotoneMaxApprox term s x) (term (s + 1) (x.take (s + 1)))

/-- The running maximum of a computable family of dyadic terms is computable. -/
lemma monotoneMaxApprox_comp {term : ℕ → BitString → ℕ}
    (hcomp : Computable fun p : ℕ × BitString => term p.1 p.2) :
    Computable (fun p : ℕ × BitString => monotoneMaxApprox term p.1 p.2) := by
  have h_eq : (fun p : ℕ × BitString => monotoneMaxApprox term p.1 p.2) =
      fun p : ℕ × BitString => Nat.rec (term 0 (p.2.take 0))
          (fun y ih => max (2 * ih) (term (y + 1) (p.2.take (y + 1)))) p.1 := by
    funext p
    rcases p with ⟨s, x⟩
    induction s with
    | zero => rfl
    | succ s ih => dsimp [monotoneMaxApprox]; rw [ih]; rfl
  rw [h_eq]
  refine Computable.nat_rec (g := fun p : ℕ × BitString => term 0 (p.2.take 0))
    (h := fun (p : ℕ × BitString) (p2 : ℕ × ℕ) => max (2 * p2.2) (term (p2.1 + 1) (p.2.take
        (p2.1 + 1))))
    Computable.fst ?_ ?_
  · exact hcomp.comp (Computable.pair (Computable.const 0) (Computable₂.comp
      Primrec.list_take.to_comp Computable.snd (Computable.const 0)))
  · exact Computable₂.comp Primrec.nat_max.to_comp
      (Computable₂.comp Primrec.nat_mul.to_comp (Computable.const 2) (Computable.snd.comp
          Computable.snd))
      (hcomp.comp (Computable.pair
        (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
        (Computable₂.comp Primrec.list_take.to_comp
          (Computable.snd.comp Computable.fst)
          (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)))))

/-- The running maximum at stage `s` reads at most the first `s` bits of its argument. -/
lemma monotoneMaxApprox_take (term : ℕ → BitString → ℕ) (s : ℕ) :
    ∀ (x : BitString) (m : ℕ), s ≤ m →
      monotoneMaxApprox term s (x.take m) = monotoneMaxApprox term s x := by
  induction s with
  | zero =>
    intro x m h
    change term 0 (List.take 0 (x.take m)) = term 0 (x.take 0)
    rw [List.take_take, Nat.min_eq_left (by omega)]
  | succ s ih =>
    intro x m h
    change max (2 * monotoneMaxApprox term s (x.take m)) (term (s + 1) (List.take (s + 1) (x.take
        m))) = max (2 * monotoneMaxApprox term s x) (term (s + 1) (x.take (s + 1)))
    rw [ih x m (by omega), List.take_take, Nat.min_eq_left h]

/-- The dyadic values of the running maxima increase with the stage. -/
lemma approx_max_mono (term : ℕ → BitString → ℕ) (w : CantorSeq) (s : ℕ) :
    dyadicValue (monotoneMaxApprox term s (cantorPrefix w s)) s ≤ dyadicValue
        (monotoneMaxApprox term (s + 1) (cantorPrefix w (s + 1))) (s + 1) := by
  have h1 : monotoneMaxApprox term (s + 1) (cantorPrefix w (s + 1)) =
      max (2 * monotoneMaxApprox term s (cantorPrefix w (s + 1)))
          (term (s + 1) (cantorPrefix w (s + 1))) := by
    change max (2 * monotoneMaxApprox term s (cantorPrefix w (s + 1)))
        (term (s + 1) (List.take (s + 1) (cantorPrefix w (s + 1)))) = _
    rw [cantorPrefix_take w (s + 1) (s + 1) (by omega)]
  have h2 : monotoneMaxApprox term s (cantorPrefix w (s + 1)) = monotoneMaxApprox term s
      (cantorPrefix w s) := by
    have ht : cantorPrefix w s = (cantorPrefix w (s + 1)).take s := by
      exact (cantorPrefix_take w s (s + 1) (by omega)).symm
    rw [ht, monotoneMaxApprox_take term s (cantorPrefix w (s + 1)) s (by omega)]
  rw [h1, h2]
  have hd : dyadicValue (monotoneMaxApprox term s (cantorPrefix w s) * 2) (s + 1) = dyadicValue
      (monotoneMaxApprox term s (cantorPrefix w s)) s := by
    have h_pow : monotoneMaxApprox term s (cantorPrefix w s) * 2 ^ (s + 1 - s) =
        monotoneMaxApprox term s (cantorPrefix w s) * 2 := by
      have : s + 1 - s = 1 := by omega
      rw [this, pow_one]
    rw [← h_pow]
    exact dyadicValue_mul_two_pow_sub
      (monotoneMaxApprox term s (cantorPrefix w s)) (s + 1) s (by omega)
  rw [← hd, mul_comm (monotoneMaxApprox term s (cantorPrefix w s)) 2]
  unfold dyadicValue
  have hc1 : (2 ^ (s + 1) : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hc2 : (2 ^ (s + 1) : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
  have h_le : 2 * monotoneMaxApprox term s (cantorPrefix w s) ≤ max (2 * monotoneMaxApprox term s
      (cantorPrefix w s)) (term (s + 1) (cantorPrefix w (s + 1))) := le_max_left _ _
  exact (ENNReal.mul_le_mul_iff_left hc1 hc2).mpr (by exact_mod_cast h_le)

/-- The stage-`s` running maximum evaluates to the maximum of the first `s + 1` dyadic terms
along the sequence. -/
lemma approx_max_eq_sup (term : ℕ → BitString → ℕ) (w : CantorSeq) (s : ℕ) :
    dyadicValue (monotoneMaxApprox term s (cantorPrefix w s)) s = ⨆ t ∈ Finset.range (s + 1),
        dyadicValue (term t (cantorPrefix w t)) t := by
  induction s with
  | zero =>
    dsimp [monotoneMaxApprox]
    simp [cantorPrefix]
  | succ s ih =>
    have h1 : monotoneMaxApprox term (s + 1) (cantorPrefix w (s + 1)) =
        max (2 * monotoneMaxApprox term s (cantorPrefix w (s + 1)))
            (term (s + 1) (cantorPrefix w (s + 1))) := by
      change max (2 * monotoneMaxApprox term s (cantorPrefix w (s + 1)))
          (term (s + 1) (List.take (s + 1) (cantorPrefix w (s + 1)))) = _
      rw [cantorPrefix_take w (s + 1) (s + 1) (by omega)]
    have h2 : monotoneMaxApprox term s (cantorPrefix w (s + 1)) = monotoneMaxApprox term s
        (cantorPrefix w s) := by
      have ht : cantorPrefix w s = (cantorPrefix w (s + 1)).take s := by
        exact (cantorPrefix_take w s (s + 1) (by omega)).symm
      rw [ht, monotoneMaxApprox_take term s (cantorPrefix w (s + 1)) s (by omega)]
    rw [h1, h2]
    rw [dyadicValue_max]
    have hd : dyadicValue (monotoneMaxApprox term s (cantorPrefix w s) * 2) (s + 1) = dyadicValue
        (monotoneMaxApprox term s (cantorPrefix w s)) s := by
      have h_pow : monotoneMaxApprox term s (cantorPrefix w s) * 2 ^ (s + 1 - s) = monotoneMaxApprox
          term s (cantorPrefix w s) * 2 := by
        have : s + 1 - s = 1 := by omega
        rw [this, pow_one]
      rw [← h_pow]
      exact dyadicValue_mul_two_pow_sub (monotoneMaxApprox term s (cantorPrefix w s)) (s + 1) s
          (by omega)
    have hd2 : dyadicValue (2 * monotoneMaxApprox term s (cantorPrefix w s)) (s + 1) = dyadicValue
        (monotoneMaxApprox term s (cantorPrefix w s)) s := by
      rw [mul_comm]
      exact hd
    rw [hd2, ih]
    exact max_iSup_range_succ (fun t => dyadicValue (term t (cantorPrefix w t)) t) s

/-- The supremum of the finite partial suprema of a sequence is its supremum. -/
lemma isMonotoneLimit_of_isSupremum_proof_helper (f : ℕ → ℝ≥0∞) :
    (⨆ s, ⨆ t ∈ Finset.range (s + 1), f t) = ⨆ s, f s := by
  apply le_antisymm
  · refine iSup_le fun s => iSup_le fun t => iSup_le fun ht => ?_
    exact le_iSup_of_le t le_rfl
  · refine iSup_le fun s => ?_
    have ht : s ∈ Finset.range (s + 1) := by
      rw [Finset.mem_range]
      omega
    exact le_iSup_of_le s (le_iSup_of_le s (le_iSup_of_le ht le_rfl))

/-- A supremum of computable basic functions is a monotone limit of computable basic
functions. -/
lemma isMonotoneLimit_of_isSupremum {f : CantorSeq → ℝ≥0∞}
    (hf : IsSupremumOfComputableBasicFunctions f) : IsMonotoneLimitOfComputableBasicFunctions f
        := by
  rcases hf with ⟨term, hcomp, hsup⟩
  refine ⟨monotoneMaxApprox term, monotoneMaxApprox_comp hcomp,
    fun s w => approx_max_mono term w s, fun w => ?_⟩
  rw [hsup w]
  have ht : (⨆ s, dyadicValue (monotoneMaxApprox term s (cantorPrefix w s)) s) = ⨆ s, ⨆ t ∈
      Finset.range (s + 1), dyadicValue (term t (cantorPrefix w t)) t := by
    congr 1
    funext s
    exact approx_max_eq_sup term w s
  rw [ht]
  exact (isMonotoneLimit_of_isSupremum_proof_helper _).symm

/-- A monotone limit of computable basic functions is a supremum of computable basic
functions. -/
lemma isSupremum_of_isMonotoneLimit {f : CantorSeq → ℝ≥0∞}
    (hf : IsMonotoneLimitOfComputableBasicFunctions f) : IsSupremumOfComputableBasicFunctions f
        := by
  rcases hf with ⟨approx, hcomp, _, hsup⟩
  exact ⟨approx, hcomp, hsup⟩

/-- Dyadic values at a common denominator subtract by subtracting numerators. -/
lemma dyadicValue_sub_add (A B n : ℕ) (h : B ≤ A) :
    dyadicValue (A - B) n + dyadicValue B n = dyadicValue A n := by
  unfold dyadicValue
  rw [← ENNReal.add_div]
  congr 1
  rw [← Nat.cast_add, Nat.sub_add_cancel h]

/-- If the dyadic value of the approximation does not decrease from stage `s` to stage `s + 1`,
then its numerator at least doubles: `2 * approx s (cantorPrefix w s) ≤ approx (s + 1)
(cantorPrefix w (s + 1))`.  Only this implication is proved, at one fixed stage; the converse is
not claimed. -/
lemma approx_mono_nat (approx : ℕ → BitString → ℕ) (w : CantorSeq) (s : ℕ)
    (hmono : dyadicValue (approx s (cantorPrefix w s)) s ≤ dyadicValue (approx (s + 1)
        (cantorPrefix w (s + 1))) (s + 1)) :
    2 * approx s (cantorPrefix w s) ≤ approx (s + 1) (cantorPrefix w (s + 1)) := by
  have hd : dyadicValue (approx s (cantorPrefix w s) * 2) (s + 1) = dyadicValue
      (approx s (cantorPrefix w s)) s := by
    have h_pow : approx s (cantorPrefix w s) * 2 ^ (s + 1 - s) = approx s (cantorPrefix w s) * 2
        := by
      have : s + 1 - s = 1 := by omega
      rw [this, pow_one]
    rw [← h_pow]
    exact dyadicValue_mul_two_pow_sub (approx s (cantorPrefix w s)) (s + 1) s (by omega)
  rw [mul_comm]
  rw [← hd] at hmono
  unfold dyadicValue at hmono
  have hc1 : (2 ^ (s + 1) : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hc2 : (2 ^ (s + 1) : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
  have h_mul := (ENNReal.mul_le_mul_iff_left hc1 hc2).mp (by exact hmono)
  exact_mod_cast h_mul

/-- The successive differences of a monotone approximation, in numerator form; their dyadic
values are the terms of a series summing to the approximation. -/
def monotoneTerm (approx : ℕ → BitString → ℕ) : ℕ → BitString → ℕ
| 0, x => approx 0 (x.take 0)
| s + 1, x => approx (s + 1) (x.take (s + 1)) - 2 * approx s (x.take s)

/-- The successive differences of a computable approximation are computable. -/
lemma monotoneTerm_comp {approx : ℕ → BitString → ℕ}
    (hcomp : Computable fun p : ℕ × BitString => approx p.1 p.2) :
    Computable (fun p : ℕ × BitString => monotoneTerm approx p.1 p.2) := by
  have h_eq : (fun p : ℕ × BitString => monotoneTerm approx p.1 p.2) =
      fun p : ℕ × BitString => Nat.casesOn p.1 (approx 0 (p.2.take 0))
          (fun s => approx (s + 1) (p.2.take (s + 1)) - 2 * approx s (p.2.take s)) := by
    funext p
    rcases p with ⟨s, x⟩
    cases s with
    | zero => rfl
    | succ s => rfl
  rw [h_eq]
  refine Computable.nat_casesOn Computable.fst ?_ ?_
  · exact hcomp.comp (Computable.pair (Computable.const 0) (Computable₂.comp
      Primrec.list_take.to_comp Computable.snd (Computable.const 0)))
  · exact Computable₂.comp Primrec.nat_sub.to_comp
      (hcomp.comp (Computable.pair
        (Primrec.succ.to_comp.comp Computable.snd)
        (Computable₂.comp Primrec.list_take.to_comp (Computable.snd.comp Computable.fst)
            (Primrec.succ.to_comp.comp Computable.snd))))
      (Computable₂.comp Primrec.nat_mul.to_comp (Computable.const 2)
        (hcomp.comp (Computable.pair
          Computable.snd
          (Computable₂.comp Primrec.list_take.to_comp (Computable.snd.comp Computable.fst)
              Computable.snd))))

/-- The first `s + 1` difference terms sum to the stage-`s` value of the approximation. -/
lemma monotoneTerm_sum (approx : ℕ → BitString → ℕ)
    (hmono : ∀ w s, dyadicValue (approx s (cantorPrefix w s)) s ≤ dyadicValue (approx (s + 1)
        (cantorPrefix w (s + 1))) (s + 1))
    (w : CantorSeq) (s : ℕ) :
    ∑ i ∈ Finset.range (s + 1), dyadicValue (monotoneTerm approx i (cantorPrefix w i)) i =
        dyadicValue (approx s (cantorPrefix w s)) s := by
  induction s with
  | zero =>
    dsimp [monotoneTerm]
    simp [cantorPrefix]
  | succ s ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : monotoneTerm approx (s + 1) (cantorPrefix w (s + 1)) = approx (s + 1)
        (cantorPrefix w (s + 1)) - 2 * approx s (cantorPrefix w s) := by
      dsimp [monotoneTerm]
      have ht1 : (cantorPrefix w (s + 1)).take (s + 1) = cantorPrefix w (s + 1) :=
          List.take_of_length_le (by simp)
      rw [ht1, cantorPrefix_take w s (s + 1) (by omega)]
    rw [h1]
    have hd : dyadicValue (approx s (cantorPrefix w s) * 2) (s + 1) = dyadicValue
        (approx s (cantorPrefix w s)) s := by
      have h_pow : approx s (cantorPrefix w s) * 2 ^ (s + 1 - s) = approx s (cantorPrefix w s) *
          2 := by
        have : s + 1 - s = 1 := by omega
        rw [this, pow_one]
      rw [← h_pow]
      exact dyadicValue_mul_two_pow_sub (approx s (cantorPrefix w s)) (s + 1) s (by omega)
    rw [← hd, mul_comm (approx s (cantorPrefix w s)) 2]
    rw [add_comm]
    exact dyadicValue_sub_add (approx (s + 1) (cantorPrefix w (s + 1)))
        (2 * approx s (cantorPrefix w s)) (s + 1) (approx_mono_nat approx w s (hmono w s))

/-- A monotone limit of computable basic functions is a sum of computable nonnegative basic
functions. -/
lemma isSum_of_isMonotoneLimit_proof {f : CantorSeq → ℝ≥0∞}
    (hf : IsMonotoneLimitOfComputableBasicFunctions f) :
        IsSumOfComputableNonnegativeBasicFunctions f := by
  rcases hf with ⟨approx, hcomp, hmono, hsup⟩
  refine ⟨monotoneTerm approx, monotoneTerm_comp hcomp, fun w => ?_⟩
  rw [hsup w]
  have heq : ∀ s, ∑ i ∈ Finset.range (s + 1),
      dyadicValue (monotoneTerm approx i (cantorPrefix w i)) i =
      dyadicValue (approx s (cantorPrefix w s)) s :=
    monotoneTerm_sum approx (fun w s => hmono s w) w
  have ht : (∑' i, dyadicValue (monotoneTerm approx i (cantorPrefix w i)) i) = ⨆ s, ∑ i ∈
      Finset.range (s + 1), dyadicValue (monotoneTerm approx i (cantorPrefix w i)) i := by
    rw [ENNReal.tsum_eq_iSup_nat]
    apply le_antisymm
    · refine iSup_le fun s => ?_
      cases s with
      | zero => exact zero_le _
      | succ s => exact le_iSup_of_le s le_rfl
    · exact iSup_le fun s => le_iSup_of_le (s + 1) le_rfl
  rw [ht]
  simp_rw [heq]

end Kolmogorov
