import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.AlgorithmicRandomness.LSCConstruction
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# Superlevel sets of a lower-semicomputable function, enumerated

To pass between lower semicomputability and the basic-function presentations one has to
enumerate, effectively in a rational `q`, the cylinders on which the approximation already
exceeds `q`.  That enumeration is `dyadicEnum`, and `dyadicEnum_spec` says exactly which
strings it emits; `isSupremum_of_isLowerSemicomputableFun` is the implication it proves, from
lower semicomputability to a supremum of computable basic functions.

Around it: `bitStringsOfLength` with its computability and membership lemmas, the bridge
`bridge` turning `q < dyadicValue A s` into an integer cross-multiplication, and the coded
integer arithmetic (`intLtNat`, `intMulNat` and their `Primrec` lemmas) that makes that
comparison computable.
-/



namespace Kolmogorov

open MeasureTheory Topology
open scoped ENNReal NNReal

/-- Rescaling a numerator by `2^{s-t}` and reading it at denominator `s` gives the same value as
reading the original numerator at denominator `t`. -/
lemma dyadicValue_mul_two_pow_sub (n s t : ℕ) (h : t ≤ s) :
    dyadicValue (n * 2 ^ (s - t)) s = dyadicValue n t := by
  unfold dyadicValue
  push_cast
  have h3 : t + (s - t) = s := by omega
  nth_rw 2 [← h3]
  rw [pow_add]
  exact ENNReal.mul_div_mul_right ↑n (2^t) (ENNReal.pow_ne_zero (by norm_num) (s - t))
      (ENNReal.pow_ne_top (by norm_num))

/-- The list of all bit strings of a given length, built by prepending a bit to the strings one
shorter. -/
def bitStringsOfLength : ℕ → List BitString
  | 0 => [[]]
  | s + 1 => (bitStringsOfLength s).map (fun x => false :: x) ++
             (bitStringsOfLength s).map (fun x => true :: x)

/-- The enumeration of all bit strings of a given length is computable. -/
lemma computable_bitStringsOfLength : Computable bitStringsOfLength := by
  have h : bitStringsOfLength = fun s => Nat.rec [[]]
      (fun _ IH => IH.map (fun x => false :: x) ++ IH.map (fun x => true :: x)) s := by
    funext s
    induction s with
    | zero => rfl
    | succ s ih =>
      dsimp [bitStringsOfLength]
      rw [ih]
  rw [h]
  apply Primrec.to_comp
  apply Primrec.nat_rec₁
  apply Primrec.list_append.comp
  · apply Primrec.list_map Primrec₂.right
    apply Primrec.list_cons.comp (Primrec.const false) Primrec₂.right
  · apply Primrec.list_map Primrec₂.right
    apply Primrec.list_cons.comp (Primrec.const true) Primrec₂.right

/-- A point of the cylinder of `x` has `x` as its prefix of the corresponding length. -/
lemma cantorPrefix_eq_of_mem_cantorCylinder {s : ℕ} {x : BitString} {w : CantorSeq}
    (hx : x.length = s) (hw : w ∈ cantorCylinder x) : cantorPrefix w s = x := by
  subst hx
  apply List.ext_get
  · simp [cantorPrefix]
  · intro i h1 h2
    simp only [List.get_eq_getElem, cantorPrefix_getElem]
    have h : IsCantorPrefix x w := hw
    exact h i h2

/-- A lower semicomputable function is a supremum of computable basic functions. -/
lemma isSupremum_of_isLowerSemicomputableFun {f : CantorSeq → ℝ≥0∞}
    (hf : IsLowerSemicomputableFun f) : IsSupremumOfComputableBasicFunctions f := by
  rcases hf with ⟨enum, hcomp, hspec⟩
  exact ⟨lscApprox enum, lscComputable_approx hcomp, lscISup_approx_eq hspec⟩

/-- There are `2^s` bit strings of length `s`. -/
lemma length_bitStringsOfLength (s : ℕ) : (bitStringsOfLength s).length = 2 ^ s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [bitStringsOfLength, ih, pow_succ, mul_two]

/-- A member of the list of length-`s` strings has length `s`. -/
lemma length_of_mem_bitStringsOfLength {s : ℕ} {x : BitString}
    (h : x ∈ bitStringsOfLength s) : x.length = s := by
  revert x
  induction s with
  | zero =>
    intro x h
    simp only [bitStringsOfLength, List.mem_singleton] at h
    rw [h]
    rfl
  | succ s ih =>
    intro x h
    simp only [bitStringsOfLength, List.mem_append, List.mem_map] at h
    rcases h with ⟨y, hy, heq⟩ | ⟨y, hy, heq⟩ <;>
      · rw [← heq]
        simp [ih hy]

/-- Every bit string occurs in the list of strings of its own length. -/
lemma mem_bitStringsOfLength (x : BitString) : x ∈ bitStringsOfLength x.length := by
  induction x with
  | nil => simp [bitStringsOfLength]
  | cons b x ih => cases b <;> simp [bitStringsOfLength, ih]

/-- Membership in the list of length-`s` strings is exactly having length `s`. -/
lemma mem_bitStringsOfLength_iff {s : ℕ} {x : BitString} :
    x ∈ bitStringsOfLength s ↔ x.length = s := by
  constructor
  · exact length_of_mem_bitStringsOfLength
  · intro h; rw [← h]; exact mem_bitStringsOfLength x

/-- The enumeration of the cylinders on which the approximations already exceed the rational
threshold `q`, indexed by a pairing of the stage with a string of that length. -/
def dyadicEnum (approx : ℕ → BitString → ℕ) (q : ℚ) (i : ℕ) : Option BitString :=
  let s := i.unpair.1
  let k := i.unpair.2
  let lst := bitStringsOfLength s
  if h : k < lst.length then
    let x := lst.get ⟨k, h⟩
    let A : ℤ := q.num * (2^s : ℕ)
    let B : ℤ := (approx s x : ℤ) * q.den
    if A < B then
      some x
    else none
  else none

/-- A length-`s` string is emitted by the enumeration for `q` exactly when the stage-`s`
approximation on it exceeds `q`. -/
lemma dyadicEnum_spec {approx : ℕ → BitString → ℕ} (q : ℚ) (s : ℕ) (x : BitString)
    (hx : x.length = s) :
    q.num * ((2^s : ℕ) : ℤ) < (approx s x : ℤ) * q.den ↔
    ∃ i, dyadicEnum approx q i = some x := by
  constructor
  · intro hlt
    have h_lst : x ∈ bitStringsOfLength s := by rw [mem_bitStringsOfLength_iff]; exact hx
    rcases List.mem_iff_get.mp h_lst with ⟨k, h_get⟩
    use Nat.pair s k.1
    unfold dyadicEnum
    dsimp only
    rw [Nat.unpair_pair]
    rw [dif_pos k.2]
    have h_eq : (bitStringsOfLength s).get ⟨k.1, k.2⟩ = x := h_get
    rw [h_eq]
    rw [if_pos hlt]
  · intro h
    rcases h with ⟨i, hi⟩
    unfold dyadicEnum at hi
    dsimp at hi
    split at hi
    next h_k =>
      split at hi
      next h_lt =>
        injection hi with h_eq
        have h_len : ((bitStringsOfLength i.unpair.1).get ⟨i.unpair.2, h_k⟩).length = i.unpair.1
            := by
          rw [← mem_bitStringsOfLength_iff]
          exact List.get_mem ..
        have hx' := hx
        rw [← h_eq] at hx'
        change ((bitStringsOfLength i.unpair.1).get ⟨i.unpair.2, h_k⟩).length = s at hx'
        rw [h_len] at hx'
        have hs : i.unpair.1 = s := hx'
        subst hs
        rw [← h_eq]
        exact h_lt
      next => contradiction
    next => contradiction

/-- The dyadic value is the extended-real image of the real quotient `A / 2^s`. -/
lemma dyadicValue_eq_ofReal (A s : ℕ) : dyadicValue A s = ENNReal.ofReal
    ((A : ℝ) / ((2^s : ℕ) : ℝ)) := by
  unfold dyadicValue
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  · exact (ENNReal.ofReal_natCast A).symm
  · have : (2 : ℝ≥0∞)^s = ((2^s : ℕ) : ℝ≥0∞) := by norm_cast
    rw [this]
    exact (ENNReal.ofReal_natCast (2^s)).symm

/-- A nonnegative rational is strictly below a dyadic value exactly when the corresponding
integer cross-multiplication inequality holds. -/
lemma bridge (q : ℚ) (A s : ℕ) (hq : 0 ≤ (q : ℝ)) :
    ENNReal.ofReal (q : ℝ) < dyadicValue A s ↔ q.num * ((2^s : ℕ) : ℤ) < (A : ℤ) * q.den := by
  rw [dyadicValue_eq_ofReal]
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hq]
  have h1 : 0 < ((2^s : ℕ) : ℝ) := by positivity
  rw [lt_div_iff₀ h1]
  have h2 : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
  rw [Rat.cast_def q]
  rw [div_mul_eq_mul_div, div_lt_iff₀ h2]
  have eq1 : (q.num : ℝ) * ((2^s : ℕ) : ℝ) = ((q.num * ((2^s : ℕ) : ℤ) : ℤ) : ℝ) := by
      push_cast; rfl
  have eq2 : (A : ℝ) * (q.den : ℝ) = (((A : ℤ) * q.den : ℤ) : ℝ) := by push_cast; rfl
  rw [eq1, eq2]
  exact_mod_cast Iff.rfl

/-- The strict order of the integers, read through their codes as natural numbers. -/
def intLtNat (a b : ℕ) : Bool :=
  let is_neg_a := a % 2 == 1
  let is_neg_b := b % 2 == 1
  let val_a := a / 2
  let val_b := b / 2
  bif is_neg_a then
    bif is_neg_b then decide (val_b < val_a)
    else true
  else
    bif is_neg_b then false
    else decide (val_a < val_b)

/-- The coded integer comparison is primitive recursive. -/
lemma primrec_int_lt_nat : Primrec₂ intLtNat := by
  have h_is_neg_a : Primrec (fun p : ℕ × ℕ => p.1 % 2 == 1) :=
    Primrec.beq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 1)
  have h_is_neg_b : Primrec (fun p : ℕ × ℕ => p.2 % 2 == 1) :=
    Primrec.beq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1)
  have h_val_a : Primrec (fun p : ℕ × ℕ => p.1 / 2) :=
    Primrec.nat_div.comp Primrec.fst (Primrec.const 2)
  have h_val_b : Primrec (fun p : ℕ × ℕ => p.2 / 2) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have h_lt_1 : Primrec (fun p : ℕ × ℕ => decide (p.1 / 2 < p.2 / 2)) :=
    PrimrecPred.decide (Primrec.nat_lt.comp h_val_a h_val_b)
  have h_lt_2 : Primrec (fun p : ℕ × ℕ => decide (p.2 / 2 < p.1 / 2)) :=
    PrimrecPred.decide (Primrec.nat_lt.comp h_val_b h_val_a)
  exact Primrec.cond h_is_neg_a
    (Primrec.cond h_is_neg_b h_lt_2 (Primrec.const true))
    (Primrec.cond h_is_neg_b (Primrec.const false) h_lt_1)

/-- The coded comparison agrees with the order of the integers. -/
lemma int_lt_nat_eq (a b : ℤ) : intLtNat (Encodable.encode a) (Encodable.encode b) = decide
    (a < b) := by
  cases a with
  | ofNat n =>
    cases b with
    | ofNat m =>
      change intLtNat (2 * n) (2 * m) = decide ((n : ℤ) < (m : ℤ))
      have ha : ((2 * n) % 2 == 1) = false := by simp
      have hb : ((2 * m) % 2 == 1) = false := by simp
      have hca : (2 * n) / 2 = n := by omega
      have hcb : (2 * m) / 2 = m := by omega
      dsimp [intLtNat]
      simp only [ha, hb, hca, hcb]
      exact decide_eq_decide.mpr (by omega)
    | negSucc m =>
      change intLtNat (2 * n) (2 * m + 1) = decide ((n : ℤ) < -((m : ℤ) + 1))
      have ha : ((2 * n) % 2 == 1) = false := by simp
      have hb : ((2 * m + 1) % 2 == 1) = true := by simp [Nat.add_mod]
      dsimp [intLtNat]
      simp only [ha, hb]
      have : ¬((n : ℤ) < -((m : ℤ) + 1)) := by omega
      exact Eq.symm (decide_eq_false this)
  | negSucc n =>
    cases b with
    | ofNat m =>
      change intLtNat (2 * n + 1) (2 * m) = decide (-((n : ℤ) + 1) < (m : ℤ))
      have ha : ((2 * n + 1) % 2 == 1) = true := by simp [Nat.add_mod]
      have hb : ((2 * m) % 2 == 1) = false := by simp
      dsimp [intLtNat]
      simp only [ha, hb]
      have : -((n : ℤ) + 1) < (m : ℤ) := by omega
      exact Eq.symm (decide_eq_true this)
    | negSucc m =>
      change intLtNat (2 * n + 1) (2 * m + 1) = decide (-((n : ℤ) + 1) < -((m : ℤ) + 1))
      have ha : ((2 * n + 1) % 2 == 1) = true := by simp [Nat.add_mod]
      have hb : ((2 * m + 1) % 2 == 1) = true := by simp [Nat.add_mod]
      have hca : (2 * n + 1) / 2 = n := by omega
      have hcb : (2 * m + 1) / 2 = m := by omega
      dsimp [intLtNat]
      simp only [ha, hb, hca, hcb]
      exact decide_eq_decide.mpr (by omega)

/-- The order of the integers is computable as a boolean-valued function. -/
lemma comp_decide_int_lt : Computable (fun p : ℤ × ℤ => decide (p.1 < p.2)) := by
  have : (fun p : ℤ × ℤ => decide (p.1 < p.2)) = fun p => intLtNat (Encodable.encode p.1)
      (Encodable.encode p.2) := by
    funext p
    exact (int_lt_nat_eq p.1 p.2).symm
  rw [this]
  have h1 : Computable (fun (p : ℤ × ℤ) => Encodable.encode p.1) :=
    @Computable.comp (ℤ × ℤ) ℤ ℕ _ _ _ Encodable.encode Prod.fst Computable.encode
        (Computable.fst (α := ℤ) (β := ℤ))
  have h2 : Computable (fun (p : ℤ × ℤ) => Encodable.encode p.2) :=
    @Computable.comp (ℤ × ℤ) ℤ ℕ _ _ _ Encodable.encode Prod.snd Computable.encode
        (Computable.snd (α := ℤ) (β := ℤ))
  have hp : Computable (fun (p : ℤ × ℤ) => (Encodable.encode p.1, Encodable.encode p.2)) :=
    @Computable.pair (ℤ × ℤ) ℕ ℕ _ _ _ (fun p => Encodable.encode p.1)
        (fun p => Encodable.encode p.2) h1 h2
  exact @Computable.comp (ℤ × ℤ) (ℕ × ℕ) Bool _ _ _
    (fun (p : ℕ × ℕ) => intLtNat p.1 p.2)
    (fun (p : ℤ × ℤ) => (Encodable.encode p.1, Encodable.encode p.2))
    primrec_int_lt_nat.to_comp hp

/-- The inclusion of the naturals into the integers is computable. -/
lemma comp_ofNat : Computable (fun n : ℕ => Int.ofNat n) := by
  have h1 : Computable (fun n : ℕ => 2 * n) :=
    @Computable.comp ℕ (ℕ × ℕ) ℕ _ _ _ (fun p => p.1 * p.2) (fun n => (2, n))
      Primrec.nat_mul.to_comp (@Computable.pair ℕ ℕ ℕ _ _ _ (fun _ => 2) (fun n => n)
          (Computable.const 2) Computable.id)
  have h2 : Computable (fun n : ℕ => (Encodable.decode (2 * n) : Option ℤ)) :=
    @Computable.comp ℕ ℕ (Option ℤ) _ _ _ Encodable.decode (fun n => 2 * n) Computable.decode h1
  have h3 : Computable (fun n : ℕ => ((Encodable.decode (2 * n) : Option ℤ)).getD 0) :=
    Computable.option_getD h2 (Computable.const 0)
  have h_eq : (fun n : ℕ => ((Encodable.decode (2 * n) : Option ℤ)).getD 0) =
      (fun n => Int.ofNat n) := by
    funext n
    change ((Encodable.decode (Encodable.encode (Int.ofNat n)) : Option ℤ)).getD 0 = _
    rw [Encodable.encodek]
    rfl
  rwa [←h_eq]

/-- Multiplication of the integers, read through their codes as natural numbers. -/
def intMulNat (a b : ℕ) : ℕ :=
  let is_neg_a := a % 2 == 1
  let is_neg_b := b % 2 == 1
  let val_a := a / 2
  let val_b := b / 2
  bif is_neg_a then
    bif is_neg_b then
      2 * (val_a * val_b + val_a + val_b + 1)
    else
      bif val_b == 0 then 0
      else 2 * (val_a * val_b + val_b - 1) + 1
  else
    bif is_neg_b then
      bif val_a == 0 then 0
      else 2 * (val_a * val_b + val_a - 1) + 1
    else
      2 * (val_a * val_b)

/-- The coded integer multiplication is primitive recursive. -/
lemma primrec_int_mul_nat : Primrec₂ intMulNat := by
  have h_is_neg_a : Primrec (fun p : ℕ × ℕ => p.1 % 2 == 1) :=
    Primrec.beq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 1)
  have h_is_neg_b : Primrec (fun p : ℕ × ℕ => p.2 % 2 == 1) :=
    Primrec.beq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1)
  have h_val_a : Primrec (fun p : ℕ × ℕ => p.1 / 2) :=
    Primrec.nat_div.comp Primrec.fst (Primrec.const 2)
  have h_val_b : Primrec (fun p : ℕ × ℕ => p.2 / 2) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have h_val_prod : Primrec (fun p : ℕ × ℕ => (p.1 / 2) * (p.2 / 2)) :=
    Primrec.nat_mul.comp h_val_a h_val_b
  
  have h_pos_pos : Primrec (fun p : ℕ × ℕ => 2 * ((p.1 / 2) * (p.2 / 2))) :=
    Primrec.nat_mul.comp (Primrec.const 2) h_val_prod
    
  have h_pos_neg : Primrec (fun p : ℕ × ℕ => bif p.1 / 2 == 0 then 0 else 2 * ((p.1 / 2) * (p.2
      / 2) + p.1 / 2 - 1) + 1) :=
    Primrec.cond (Primrec.beq.comp h_val_a (Primrec.const 0))
      (Primrec.const 0)
      (Primrec.nat_add.comp 
        (Primrec.nat_mul.comp (Primrec.const 2) 
          (Primrec.nat_sub.comp 
            (Primrec.nat_add.comp h_val_prod h_val_a) 
            (Primrec.const 1)))
        (Primrec.const 1))
        
  have h_neg_pos : Primrec (fun p : ℕ × ℕ => bif p.2 / 2 == 0 then 0 else 2 * ((p.1 / 2) * (p.2
      / 2) + p.2 / 2 - 1) + 1) :=
    Primrec.cond (Primrec.beq.comp h_val_b (Primrec.const 0))
      (Primrec.const 0)
      (Primrec.nat_add.comp 
        (Primrec.nat_mul.comp (Primrec.const 2) 
          (Primrec.nat_sub.comp 
            (Primrec.nat_add.comp h_val_prod h_val_b) 
            (Primrec.const 1)))
        (Primrec.const 1))
        
  have h_neg_neg : Primrec (fun p : ℕ × ℕ => 2 * ((p.1 / 2) * (p.2 / 2) + p.1 / 2 + p.2 / 2 + 1)) :=
    Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp h_val_prod h_val_a)
          h_val_b)
        (Primrec.const 1))
        
  exact Primrec.cond h_is_neg_a
    (Primrec.cond h_is_neg_b h_neg_neg h_neg_pos)
    (Primrec.cond h_is_neg_b h_pos_neg h_pos_pos)

/-- The coded multiplication agrees with multiplication of the integers. -/
lemma int_mul_nat_eq (a b : ℤ) : intMulNat (Encodable.encode a) (Encodable.encode b) =
    Encodable.encode (a * b) := by
  cases a with
  | ofNat n =>
    cases b with
    | ofNat m =>
      change intMulNat (2 * n) (2 * m) = 2 * (n * m)
      dsimp only [intMulNat]
      have ha : ((2 * n) % 2 == 1) = false := by simp
      have hb : ((2 * m) % 2 == 1) = false := by simp
      have hca : (2 * n) / 2 = n := by omega
      have hcb : (2 * m) / 2 = m := by omega
      simp only [ha, hb, hca, hcb]
      rfl
    | negSucc m =>
      change intMulNat (2 * n) (2 * m + 1) = Encodable.encode (Int.ofNat n * Int.negSucc m)
      dsimp only [intMulNat]
      have ha : ((2 * n) % 2 == 1) = false := by simp
      have hb : ((2 * m + 1) % 2 == 1) = true := by simp [Nat.add_mod]
      have hca : (2 * n) / 2 = n := by omega
      have hcb : (2 * m + 1) / 2 = m := by omega
      simp only [ha, hb, hca, hcb]
      have h_prod_zero : ((n == 0) = true) ↔ (n = 0) := beq_iff_eq
      by_cases h : n = 0
      · rw [h_prod_zero.mpr h, h]
        have h_zero : Int.ofNat 0 * Int.negSucc m = 0 := by ring
        rw [h_zero]
        rfl
      · have : (n == 0) = false := by
          have : ¬(n == 0) = true := mt h_prod_zero.mp h
          exact eq_false_of_ne_true this
        rw [this]
        have eq_val : Int.ofNat n * Int.negSucc m = Int.negSucc (n * m + n - 1) := by
          change (n : ℤ) * -((m : ℤ) + 1) = -(((n * m + n - 1 : ℕ) : ℤ) + 1)
          have h2 : 1 ≤ n * m + n := by
            have : 0 < n := Nat.pos_of_ne_zero h
            omega
          have : (n * m + n : ℤ) = ((n * m + n - 1 : ℕ) : ℤ) + 1 := by
            have : (n * m + n : ℤ) - 1 = ((n * m + n - 1 : ℕ) : ℤ) := Eq.symm (Nat.cast_sub h2)
            linarith
          linarith
        rw [eq_val]
        change _ = 2 * (n * m + n - 1) + 1
        rfl
  | negSucc n =>
    cases b with
    | ofNat m =>
      change intMulNat (2 * n + 1) (2 * m) = Encodable.encode (Int.negSucc n * Int.ofNat m)
      dsimp only [intMulNat]
      have ha : ((2 * n + 1) % 2 == 1) = true := by simp [Nat.add_mod]
      have hb : ((2 * m) % 2 == 1) = false := by simp
      have hca : (2 * n + 1) / 2 = n := by omega
      have hcb : (2 * m) / 2 = m := by omega
      simp only [ha, hb, hca, hcb]
      have h_prod_zero : ((m == 0) = true) ↔ (m = 0) := beq_iff_eq
      by_cases h : m = 0
      · rw [h_prod_zero.mpr h, h]
        have h_zero : Int.negSucc n * Int.ofNat 0 = 0 := by ring
        rw [h_zero]
        rfl
      · have : (m == 0) = false := by
          have : ¬(m == 0) = true := mt h_prod_zero.mp h
          exact eq_false_of_ne_true this
        rw [this]
        have eq_val : Int.negSucc n * Int.ofNat m = Int.negSucc (n * m + m - 1) := by
          change -((n : ℤ) + 1) * (m : ℤ) = -(((n * m + m - 1 : ℕ) : ℤ) + 1)
          have h2 : 1 ≤ n * m + m := by
            have : 0 < m := Nat.pos_of_ne_zero h
            omega
          have : (n * m + m : ℤ) = ((n * m + m - 1 : ℕ) : ℤ) + 1 := by
            have : (n * m + m : ℤ) - 1 = ((n * m + m - 1 : ℕ) : ℤ) := Eq.symm (Nat.cast_sub h2)
            linarith
          linarith
        rw [eq_val]
        change _ = 2 * (n * m + m - 1) + 1
        rfl
    | negSucc m =>
      change intMulNat (2 * n + 1) (2 * m + 1) = 2 * ((n + 1) * (m + 1))
      dsimp only [intMulNat]
      have ha : ((2 * n + 1) % 2 == 1) = true := by simp [Nat.add_mod]
      have hb : ((2 * m + 1) % 2 == 1) = true := by simp [Nat.add_mod]
      have hca : (2 * n + 1) / 2 = n := by omega
      have hcb : (2 * m + 1) / 2 = m := by omega
      simp only [ha, hb, hca, hcb]
      have : n * m + n + m + 1 = (n + 1) * (m + 1) := by ring
      rw [this]
      rfl

/-- Multiplication of integers is computable. -/
lemma comp_mul_int : Computable (fun p : ℤ × ℤ => p.1 * p.2) := by
  have : (fun p : ℤ × ℤ => p.1 * p.2) = fun p =>
      (Encodable.decode (intMulNat (Encodable.encode p.1) (Encodable.encode p.2))).getD 0 := by
    funext p
    rw [int_mul_nat_eq]
    rw [Encodable.encodek]
    rfl
  rw [this]
  have h1 : Computable (fun (p : ℤ × ℤ) => Encodable.encode p.1) :=
    @Computable.comp (ℤ × ℤ) ℤ ℕ _ _ _ Encodable.encode Prod.fst Computable.encode
        (Computable.fst (α := ℤ) (β := ℤ))
  have h2 : Computable (fun (p : ℤ × ℤ) => Encodable.encode p.2) :=
    @Computable.comp (ℤ × ℤ) ℤ ℕ _ _ _ Encodable.encode Prod.snd Computable.encode
        (Computable.snd (α := ℤ) (β := ℤ))
  have hp : Computable (fun (p : ℤ × ℤ) => (Encodable.encode p.1, Encodable.encode p.2)) :=
    @Computable.pair (ℤ × ℤ) ℕ ℕ _ _ _ (fun p => Encodable.encode p.1)
        (fun p => Encodable.encode p.2) h1 h2
  have h_mul : Computable
      (fun p : ℤ × ℤ => intMulNat (Encodable.encode p.1) (Encodable.encode p.2)) :=
    @Computable.comp (ℤ × ℤ) (ℕ × ℕ) ℕ _ _ _
      (fun (p : ℕ × ℕ) => intMulNat p.1 p.2)
      (fun (p : ℤ × ℤ) => (Encodable.encode p.1, Encodable.encode p.2))
      primrec_int_mul_nat.to_comp hp
  have h_dec : Computable (fun p : ℤ × ℤ => (Encodable.decode (intMulNat (Encodable.encode
      p.1) (Encodable.encode p.2)) : Option ℤ)) :=
    @Computable.comp (ℤ × ℤ) ℕ (Option ℤ) _ _ _ Encodable.decode _ Computable.decode h_mul
  exact Computable.option_getD h_dec (Computable.const 0)

/-- Looking up the string of a given index among the strings of a given length is computable. -/
lemma h_f_fast : Computable
    (fun p : (ℤ × ℤ) × ℕ => (bitStringsOfLength p.2.unpair.1)[p.2.unpair.2]?) :=
  @Computable.comp ((ℤ × ℤ) × ℕ) (List BitString × ℕ) (Option BitString) _ _ _
    (fun p => p.1[p.2]?)
    (fun p => (bitStringsOfLength p.2.unpair.1, p.2.unpair.2))
    Primrec.list_getElem?.to_comp
    (@Computable.pair ((ℤ × ℤ) × ℕ) (List BitString) ℕ _ _ _
      (fun p => bitStringsOfLength p.2.unpair.1)
      (fun p => p.2.unpair.2)
      (@Computable.comp ((ℤ × ℤ) × ℕ) ℕ (List BitString) _ _ _
         bitStringsOfLength
         (fun p => p.2.unpair.1)
         computable_bitStringsOfLength
         (@Computable.comp ((ℤ × ℤ) × ℕ) ℕ ℕ _ _ _
           (fun s => s.unpair.1)
           (fun p => p.2)
           (Primrec.fst.comp Primrec.unpair).to_comp
           Computable.snd))
      (@Computable.comp ((ℤ × ℤ) × ℕ) ℕ ℕ _ _ _
         (fun s => s.unpair.2)
         (fun p => p.2)
         (Primrec.snd.comp Primrec.unpair).to_comp
         Computable.snd))

/-- The numerator component of the packed argument of the enumeration. -/
def getQNum (p : ((ℤ × ℤ) × ℕ) × BitString) : ℤ := p.1.1.1
/-- The numerator component of the packed argument is computable. -/
lemma comp_q_num : Computable getQNum :=
  @Computable.comp (((ℤ × ℤ) × ℕ) × BitString) ((ℤ × ℤ) × ℕ) ℤ _ _ _
    (fun p => p.1.1) Prod.fst
    (@Computable.comp ((ℤ × ℤ) × ℕ) (ℤ × ℤ) ℤ _ _ _
      Prod.fst Prod.fst (Computable.fst (α := ℤ) (β := ℤ)) (Computable.fst (α := ℤ × ℤ) (β := ℕ)))
    (Computable.fst (α := (ℤ × ℤ) × ℕ) (β := BitString))

/-- The denominator component of the packed argument of the enumeration. -/
def getQDen (p : ((ℤ × ℤ) × ℕ) × BitString) : ℤ := p.1.1.2
/-- The denominator component of the packed argument is computable. -/
lemma comp_q_den : Computable getQDen :=
  @Computable.comp (((ℤ × ℤ) × ℕ) × BitString) ((ℤ × ℤ) × ℕ) ℤ _ _ _
    (fun p => p.1.2) Prod.fst
    (@Computable.comp ((ℤ × ℤ) × ℕ) (ℤ × ℤ) ℤ _ _ _
      Prod.snd Prod.fst (Computable.snd (α := ℤ) (β := ℤ)) (Computable.fst (α := ℤ × ℤ) (β := ℕ)))
    (Computable.fst (α := (ℤ × ℤ) × ℕ) (β := BitString))

end Kolmogorov
