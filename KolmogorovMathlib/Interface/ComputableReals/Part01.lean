import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Rat.Denumerable
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import Mathlib.Data.Nat.Nth

/-!
# Computable rationals and lower semicomputable reals: the groundwork

Builds a computability-friendly encoding of rationals, including primitive-recursive integer
parts, gcd, rational arithmetic and search.

It then develops lower semicomputable reals: monotonisation of approximations, constructors,
the characterization by a computable nondecreasing rational sequence converging to the real,
and the first closure properties.
-/

open Encodable Denumerable

namespace Kolmogorov
namespace ComputableReals

attribute [local instance] Encodable.decidableRangeEncode

/-! ## Computability groundwork

### Integers -/

/-- The equivalence `ℤ ≃ ℕ ⊕ ℕ` sends `Int.ofNat n` to `Sum.inl n`. -/
lemma intEquivNatSumNat_ofNat (n : ℕ) :
    Equiv.intEquivNatSumNat (Int.ofNat n) = Sum.inl n := rfl

/-- The equivalence `ℤ ≃ ℕ ⊕ ℕ` sends `Int.negSucc n` to `Sum.inr n`. -/
lemma intEquivNatSumNat_negSucc (n : ℕ) :
    Equiv.intEquivNatSumNat (Int.negSucc n) = Sum.inr n := rfl

/-- The `Primcodable ℤ` code of an integer is the code of the corresponding element of
`ℕ ⊕ ℕ`; this is what makes the transfer below cost nothing. -/
lemma encode_intEquivNatSumNat (i : ℤ) :
    Encodable.encode (Equiv.intEquivNatSumNat i) = Encodable.encode i := by
  cases i <;> rfl

/-- Viewing an integer as an element of `ℕ ⊕ ℕ` is primitive recursive. -/
theorem primrec_intToSum : Primrec (fun i : ℤ => Equiv.intEquivNatSumNat i) :=
  Primrec.encode_iff.1 (Primrec.encode.of_eq fun i => (encode_intEquivNatSumNat i).symm)

/-- Reading an element of `ℕ ⊕ ℕ` as an integer is primitive recursive. -/
theorem primrec_sumToInt : Primrec (fun s : ℕ ⊕ ℕ => Equiv.intEquivNatSumNat.symm s) :=
  Primrec.encode_iff.1 (Primrec.encode.of_eq fun s => by
    rw [← encode_intEquivNatSumNat, Equiv.apply_symm_apply])

/-- The positive part `Int.toNat` is primitive recursive. -/
theorem primrec_intToNat : Primrec (fun i : ℤ => i.toNat) :=
  (Primrec.sumCasesOn primrec_intToSum Primrec.snd.to₂
    (Primrec.const 0).to₂).of_eq (fun i => by cases i <;> rfl)

/-- The negative part of an integer is primitive recursive. -/
theorem primrec_intNegToNat : Primrec (fun i : ℤ => (-i).toNat) :=
  (Primrec.sumCasesOn primrec_intToSum (Primrec.const 0).to₂
    (Primrec.succ.comp Primrec.snd).to₂).of_eq (fun i => by
      cases i with
      | ofNat n => change (0 : ℕ) = _; simp
      | negSucc n => change n.succ = _; omega)

/-- The integer difference of two naturals is primitive recursive. -/
theorem primrec_natSubInt : Primrec₂ (fun a b : ℕ => (a : ℤ) - b) := by
  have h : Primrec (fun p : ℕ × ℕ =>
      Equiv.intEquivNatSumNat.symm
        (if p.2 ≤ p.1 then Sum.inl (p.1 - p.2) else Sum.inr (p.2 - p.1 - 1))) :=
    primrec_sumToInt.comp (Primrec.ite (PrimrecRel.comp Primrec.nat_le Primrec.snd Primrec.fst)
      (Primrec.sumInl.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
      (Primrec.sumInr.comp (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1))))
  exact h.of_eq (fun p => by
    by_cases hle : p.2 ≤ p.1
    · simp only [hle, ite_eq_left]
      change ((p.1 - p.2 : ℕ) : ℤ) = _
      omega
    · simp only [hle, ite_eq_right, not_false_iff]
      change (Int.negSucc (p.2 - p.1 - 1)) = _
      omega)

/-- Every integer is the difference of its positive and negative parts. -/
lemma int_eq_toNat_sub (i : ℤ) : i = (i.toNat : ℤ) - ((-i).toNat : ℤ) := by omega

/-- `Int.natAbs` is primitive recursive. -/
theorem primrec_intNatAbs : Primrec (fun i : ℤ => i.natAbs) :=
  ((Primrec.nat_add.comp primrec_intToNat primrec_intNegToNat)).of_eq (fun i => by omega)

/-- The cast `ℕ → ℤ` is primitive recursive. -/
theorem primrec_natCastInt : Primrec (fun n : ℕ => (n : ℤ)) :=
  (primrec_natSubInt.comp Primrec.id (Primrec.const 0)).of_eq (fun n => by simp)

/-- Addition of integers is primitive recursive. -/
theorem primrec_intAdd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  have h := primrec_natSubInt.comp
    (Primrec.nat_add.comp (primrec_intToNat.comp Primrec.fst)
      (primrec_intToNat.comp Primrec.snd))
    (Primrec.nat_add.comp (primrec_intNegToNat.comp Primrec.fst)
      (primrec_intNegToNat.comp Primrec.snd))
  exact h.of_eq (fun p => by push_cast; omega)

/-- Multiplication of integers is primitive recursive. -/
theorem primrec_intMul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  have h := primrec_natSubInt.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (primrec_intToNat.comp Primrec.fst)
        (primrec_intToNat.comp Primrec.snd))
      (Primrec.nat_mul.comp (primrec_intNegToNat.comp Primrec.fst)
        (primrec_intNegToNat.comp Primrec.snd)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (primrec_intToNat.comp Primrec.fst)
        (primrec_intNegToNat.comp Primrec.snd))
      (Primrec.nat_mul.comp (primrec_intNegToNat.comp Primrec.fst)
        (primrec_intToNat.comp Primrec.snd)))
  refine h.of_eq (fun p => ?_)
  push_cast
  conv_rhs => rw [int_eq_toNat_sub p.1, int_eq_toNat_sub p.2]
  ring

/-- The order on `ℤ` is primitive recursive. -/
theorem primrec_intLe : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) := by
  have h := Primrec.nat_le.comp
    (Primrec.nat_add.comp (primrec_intToNat.comp Primrec.fst)
      (primrec_intNegToNat.comp Primrec.snd))
    (Primrec.nat_add.comp (primrec_intToNat.comp Primrec.snd)
      (primrec_intNegToNat.comp Primrec.fst))
  exact h.of_eq (fun p => by omega)

/-- Strict order on `ℤ` is primitive recursive. -/
theorem primrec_intLt : PrimrecRel ((· < ·) : ℤ → ℤ → Prop) :=
  PrimrecPred.of_eq (PrimrecPred.not (PrimrecRel.comp primrec_intLe Primrec.snd Primrec.fst))
    (fun p => by simp)

/-! ### Greatest common divisors -/

/-- One step of the Euclidean algorithm. -/
def gcdStep (p : ℕ × ℕ) : ℕ × ℕ := if p.2 = 0 then p else (p.2, p.1 % p.2)

/-- The Euclidean step is primitive recursive. -/
theorem primrec_gcdStep : Primrec gcdStep :=
  Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 0)) Primrec.id
    (Primrec.pair Primrec.snd (Primrec.nat_mod.comp Primrec.fst Primrec.snd))

/-- Iterating the Euclidean step more often than the second argument computes the gcd. -/
theorem gcdStep_iterate (n : ℕ) :
    ∀ x y : ℕ, y < n → (gcdStep^[n] (x, y)).1 = Nat.gcd x y := by
  induction n with
  | zero => intro x y h; omega
  | succ n ih =>
    intro x y h
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · have hfix : gcdStep (x, 0) = (x, 0) := by simp [gcdStep]
      rw [Function.iterate_fixed hfix]
      simp
    · rw [Function.iterate_succ_apply]
      have hstep : gcdStep (x, y) = (y, x % y) := by
        simp only [gcdStep]
        rw [ite_eq_right (by omega)]
      rw [hstep, ih y (x % y) (by have := Nat.mod_lt x hy; omega)]
      rw [Nat.gcd_comm y (x % y), ← Nat.gcd_rec, Nat.gcd_comm]

/-- `Nat.gcd` is primitive recursive (mathlib has no such lemma). -/
theorem primrec_natGcd : Primrec₂ Nat.gcd := by
  have h : Primrec (fun p : ℕ × ℕ => (gcdStep^[p.1 + p.2 + 1] p).1) :=
    Primrec.fst.comp (Primrec.nat_iterate
      (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd) (Primrec.const 1))
      Primrec.id (primrec_gcdStep.comp Primrec.snd).to₂)
  exact h.of_eq (fun p => gcdStep_iterate _ p.1 p.2 (by omega))

/-! ### The structural code of a rational -/

/-- The structural code of a rational number. -/
abbrev ratCode : ℚ → ℕ := @Encodable.encode ℚ Rat.instEncodable

/-- The structural code pairs the code of the numerator with the denominator. -/
theorem ratCode_eq (r : ℚ) : ratCode r = Nat.pair (Encodable.encode r.num) r.den := rfl

/-- The set of structural codes is infinite. -/
instance instInfiniteRangeRatCode : Infinite (Set.range ratCode) :=
  Infinite.of_injective _ (Equiv.ofInjective _ (@encode_injective ℚ _)).injective

/-- Test whether a natural number is the structural code of a rational. -/
def isCode (m : ℕ) : Bool :=
  decide (0 < m.unpair.2) &&
    decide (Nat.gcd (Denumerable.ofNat ℤ m.unpair.1).natAbs m.unpair.2 = 1)

/-- The code test is primitive recursive. -/
theorem primrec_isCode : Primrec isCode := by
  have h1 : Primrec (fun m : ℕ => decide (0 < m.unpair.2)) :=
    (PrimrecRel.comp Primrec.nat_lt (Primrec.const 0) (Primrec.snd.comp Primrec.unpair)).decide
  have h2 : Primrec (fun m : ℕ =>
      decide (Nat.gcd (Denumerable.ofNat ℤ m.unpair.1).natAbs m.unpair.2 = 1)) :=
    (PrimrecRel.comp Primrec.eq
      (primrec_natGcd.comp
        (primrec_intNatAbs.comp ((Primrec.ofNat ℤ).comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 1)).decide
  exact (Primrec.cond h1 h2 (Primrec.const false)).of_eq (fun m => by
    cases h : decide (0 < m.unpair.2) <;> simp [isCode, h])

/-- Structural codes pass the test. -/
theorem isCode_ratCode (r : ℚ) : isCode (ratCode r) = true := by
  simp only [isCode, ratCode_eq, Nat.unpair_pair, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨r.pos, ?_⟩
  rw [Denumerable.ofNat_encode]
  exact r.reduced

/-- Anything passing the test is a structural code. -/
theorem exists_ratCode {m : ℕ} (h : isCode m = true) : ∃ r : ℚ, ratCode r = m := by
  simp only [isCode, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hd, hc⟩ := h
  refine ⟨Rat.mk' (Denumerable.ofNat ℤ m.unpair.1) m.unpair.2 (by omega) hc, ?_⟩
  rw [ratCode_eq]
  change Nat.pair (Encodable.encode (Denumerable.ofNat ℤ m.unpair.1)) m.unpair.2 = m
  rw [Denumerable.encode_ofNat, Nat.pair_unpair]

/-- Membership in the range of the structural code is decided by `isCode`. -/
theorem mem_range_ratCode_iff (m : ℕ) : m ∈ Set.range ratCode ↔ isCode m = true := by
  constructor
  · rintro ⟨r, rfl⟩; exact isCode_ratCode r
  · intro h; exact exists_ratCode h

/-! ### Enumerating the structural codes -/

/-- Every `Nat.pair k 1` is a code: it stands for an integer over denominator `1`. -/
theorem isCode_pair_one (k : ℕ) : isCode (Nat.pair k 1) = true := by
  simp [isCode, Nat.unpair_pair]

/-- There are codes above every natural number. -/
theorem exists_isCode_gt (x : ℕ) : ∃ m, x < m ∧ isCode m = true :=
  ⟨Nat.pair (x + 1) 1, lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.left_le_pair _ _),
    isCode_pair_one _⟩

/-- One step of the linear scan looking for the next code. -/
def scanStep (st : ℕ × Bool) : ℕ × Bool := if st.2 then st else (st.1 + 1, isCode (st.1 + 1))

/-- The scan step is primitive recursive. -/
theorem primrec_scanStep : Primrec scanStep :=
  Primrec.ite (Primrec.primrecPred
      (Primrec.snd.of_eq (fun st : ℕ × Bool => by simp))) Primrec.id
    (Primrec.pair (Primrec.succ.comp Primrec.fst)
      (primrec_isCode.comp (Primrec.succ.comp Primrec.fst)))

/-- The scan started at `a` finds the least code in `[a, a + k]`. -/
theorem scanStep_iterate (k : ℕ) :
    ∀ a y : ℕ, isCode y = true → a ≤ y → y ≤ a + k →
      (∀ z, a ≤ z → z < y → isCode z = false) →
      (scanStep^[k] (a, isCode a)).1 = y := by
  induction k with
  | zero =>
    intro a y _ hay hya _
    simp only [Function.iterate_zero_apply]
    omega
  | succ k ih =>
    intro a y hy hay hya hmin
    rcases eq_or_lt_of_le hay with rfl | hlt
    · have hfix : scanStep (a, isCode a) = (a, isCode a) := by simp [scanStep, hy]
      rw [Function.iterate_fixed hfix]
    · have hfa : isCode a = false := hmin a le_rfl hlt
      rw [Function.iterate_succ_apply]
      have hstep : scanStep (a, isCode a) = (a + 1, isCode (a + 1)) := by simp [scanStep, hfa]
      rw [hstep]
      exact ih (a + 1) y hy (by omega) (by omega) (fun z hz1 hz2 => hmin z (by omega) hz2)

/-- The least code strictly larger than `x`. -/
def nextCode (x : ℕ) : ℕ := (scanStep^[Nat.pair (x + 1) 1] (x + 1, isCode (x + 1))).1

/-- `nextCode` is primitive recursive. -/
theorem primrec_nextCode : Primrec nextCode :=
  Primrec.fst.comp (Primrec.nat_iterate
    (Primrec₂.comp Primrec₂.natPair Primrec.succ (Primrec.const 1))
    (Primrec.pair Primrec.succ (primrec_isCode.comp Primrec.succ))
    (primrec_scanStep.comp Primrec.snd).to₂)

/-- `nextCode x` really is the least code above `x`. -/
theorem nextCode_spec (x : ℕ) :
    x < nextCode x ∧ isCode (nextCode x) = true ∧
      ∀ y, x < y → isCode y = true → nextCode x ≤ y := by
  classical
  have hex : ∃ m, x < m ∧ isCode m = true := exists_isCode_gt x
  obtain ⟨hfx, hfc⟩ : x < Nat.find hex ∧ isCode (Nat.find hex) = true := Nat.find_spec hex
  have hle : Nat.find hex ≤ Nat.pair (x + 1) 1 :=
    Nat.find_min' hex ⟨lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.left_le_pair _ _),
      isCode_pair_one _⟩
  have key : nextCode x = Nat.find hex := by
    refine scanStep_iterate _ (x + 1) _ hfc (by omega) (by omega) (fun z hz1 hz2 => ?_)
    have hz := Nat.find_min hex hz2
    rcases Bool.eq_false_or_eq_true (isCode z) with h | h
    · exact absurd ⟨by omega, h⟩ hz
    · exact h
  refine ⟨by omega, by rw [key]; exact hfc, fun y hxy hy => ?_⟩
  rw [key]
  exact Nat.find_min' hex ⟨hxy, hy⟩

/-- The increasing enumeration of all structural codes. -/
def unrank (n : ℕ) : ℕ := nextCode^[n] 1

/-- The enumeration of the codes is primitive recursive. -/
theorem primrec_unrank : Primrec unrank :=
  Primrec.nat_iterate Primrec.id (Primrec.const 1) (primrec_nextCode.comp Primrec.snd).to₂

/-- Recursion equation for the enumeration of the codes. -/
theorem unrank_succ (n : ℕ) : unrank (n + 1) = nextCode (unrank n) :=
  Function.iterate_succ_apply' _ _ _

/-- `1` is a code (it is the code of `0 = 0/1`). -/
theorem isCode_one : isCode 1 = true := by
  have h : Nat.pair 0 1 = 1 := rfl
  rw [← h]
  exact isCode_pair_one 0

/-- `0` is not a code: it would have denominator `0`. -/
theorem not_isCode_zero : isCode 0 = false := by
  simp [isCode, Nat.unpair_zero]

/-- The least structural code is `1`. -/
theorem coe_bot_eq_one : ((⊥ : Set.range ratCode) : ℕ) = 1 := by
  have h1 : ((⊥ : Set.range ratCode) : ℕ) ∈ Set.range ratCode := (⊥ : Set.range ratCode).2
  have hone : (1 : ℕ) ∈ Set.range ratCode := (mem_range_ratCode_iff 1).2 isCode_one
  have hle : ((⊥ : Set.range ratCode) : ℕ) ≤ 1 :=
    Subtype.coe_le_coe.2 (bot_le (a := (⟨1, hone⟩ : Set.range ratCode)))
  have hne : ((⊥ : Set.range ratCode) : ℕ) ≠ 0 := by
    intro h
    rw [h] at h1
    have h2 := (mem_range_ratCode_iff 0).1 h1
    rw [not_isCode_zero] at h2
    exact Bool.noConfusion h2
  omega

/-- `Nat.Subtype.succ` on the set of codes is `nextCode`. -/
theorem coe_succ_eq_nextCode (x : Set.range ratCode) :
    ((Nat.Subtype.succ x : Set.range ratCode) : ℕ) = nextCode (x : ℕ) := by
  obtain ⟨hlt, hcode, hmin⟩ := nextCode_spec (x : ℕ)
  have h1 : (x : ℕ) < ((Nat.Subtype.succ x : Set.range ratCode) : ℕ) := Nat.Subtype.lt_succ_self x
  have h2 : isCode ((Nat.Subtype.succ x : Set.range ratCode) : ℕ) = true :=
    (mem_range_ratCode_iff _).1 (Nat.Subtype.succ x).2
  have hmem : nextCode (x : ℕ) ∈ Set.range ratCode := (mem_range_ratCode_iff _).2 hcode
  have h3 : ((Nat.Subtype.succ x : Set.range ratCode) : ℕ) ≤ nextCode (x : ℕ) :=
    Subtype.coe_le_coe.2 (Nat.Subtype.succ_le_of_lt
      (show x < (⟨nextCode (x : ℕ), hmem⟩ : Set.range ratCode) from hlt))
  have h4 : nextCode (x : ℕ) ≤ ((Nat.Subtype.succ x : Set.range ratCode) : ℕ) := hmin _ h1 h2
  omega

/-- The mathlib enumeration of the code set agrees with `unrank`. -/
theorem coe_subtypeOfNat (n : ℕ) :
    ((Nat.Subtype.ofNat (Set.range ratCode) n : Set.range ratCode) : ℕ) = unrank n := by
  induction n with
  | zero => exact coe_bot_eq_one
  | succ n ih =>
    change ((Nat.Subtype.succ (Nat.Subtype.ofNat (Set.range ratCode) n) :
      Set.range ratCode) : ℕ) = _
    rw [coe_succ_eq_nextCode, ih, unrank_succ]

/-- **Key bridge.** The `Denumerable ℚ` enumeration, read through the structural code,
is the increasing enumeration of the codes. -/
theorem ratCode_ofNat (n : ℕ) : ratCode (Denumerable.ofNat ℚ n) = unrank n := by
  rw [← coe_subtypeOfNat n]
  change ratCode ((equivRangeEncode ℚ).symm (Nat.Subtype.ofNat (Set.range ratCode) n)) = _
  exact congrArg Subtype.val ((equivRangeEncode ℚ).apply_symm_apply _)

/-- The structural code is a primitive recursive function of a rational. -/
theorem primrec_ratCode : Primrec ratCode :=
  Primrec.ofNat_iff.2 (primrec_unrank.of_eq (fun n => (ratCode_ofNat n).symm))

/-- The numerator–denominator pair of a rational is a primitive recursive function of it.
This is the general statement behind `primrec_ratNum` and `primrec_ratDen`, which are its
two components. -/
theorem primrec_ratNumDen : Primrec (fun r : ℚ => (r.num, r.den)) :=
  (Primrec.pair
      ((Primrec.ofNat ℤ).comp (Primrec.fst.comp (Primrec.unpair.comp primrec_ratCode)))
      (Primrec.snd.comp (Primrec.unpair.comp primrec_ratCode))).of_eq (fun r => by
    rw [ratCode_eq, Nat.unpair_pair, Denumerable.ofNat_encode])

/-- Denominators are primitive recursive. -/
theorem primrec_ratDen : Primrec (fun r : ℚ => r.den) :=
  Primrec.snd.comp primrec_ratNumDen

/-- Numerators are primitive recursive. -/
theorem primrec_ratNum : Primrec (fun r : ℚ => r.num) :=
  Primrec.fst.comp primrec_ratNumDen

/-! ### Arithmetic on the rationals -/

/-- Clearing the denominator. -/
theorem rat_mul_den (r : ℚ) : r * (r.den : ℚ) = (r.num : ℚ) := by
  have h : ((r.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  calc r * (r.den : ℚ) = ((r.num : ℚ) / (r.den : ℚ)) * (r.den : ℚ) := by rw [Rat.num_div_den]
    _ = (r.num : ℚ) := div_mul_cancel₀ _ h

/-- Comparison of rationals by cross multiplication. -/
theorem ratLe_iff (a b : ℚ) : a ≤ b ↔ a.num * (b.den : ℤ) ≤ b.num * (a.den : ℤ) := by
  have ha : (0 : ℚ) < (a.den : ℚ) := by exact_mod_cast a.pos
  have hb : (0 : ℚ) < (b.den : ℚ) := by exact_mod_cast b.pos
  have hK : (0 : ℚ) < (a.den : ℚ) * (b.den : ℚ) := mul_pos ha hb
  have e1 : ((a.num * (b.den : ℤ) : ℤ) : ℚ) = a * ((a.den : ℚ) * (b.den : ℚ)) := by
    push_cast
    rw [← rat_mul_den a]; ring
  have e2 : ((b.num * (a.den : ℤ) : ℤ) : ℚ) = b * ((a.den : ℚ) * (b.den : ℚ)) := by
    push_cast
    rw [← rat_mul_den b]; ring
  rw [← Int.cast_le (R := ℚ), e1, e2]
  exact ⟨fun h => mul_le_mul_of_nonneg_right h hK.le, fun h => le_of_mul_le_mul_right h hK⟩

/-- Strict comparison of rationals by cross multiplication. -/
theorem ratLt_iff (a b : ℚ) : a < b ↔ a.num * (b.den : ℤ) < b.num * (a.den : ℤ) := by
  rw [← not_le, ← not_le, ratLe_iff b a]

/-- Recognising a sum of rationals by cross multiplication. -/
theorem ratAdd_iff (a b c : ℚ) :
    c = a + b ↔ c.num * ((a.den : ℤ) * (b.den : ℤ))
      = (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)) * (c.den : ℤ) := by
  have ha : (0 : ℚ) < (a.den : ℚ) := by exact_mod_cast a.pos
  have hb : (0 : ℚ) < (b.den : ℚ) := by exact_mod_cast b.pos
  have hc : (0 : ℚ) < (c.den : ℚ) := by exact_mod_cast c.pos
  have hK : ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) ≠ 0 := by positivity
  have e1 : ((c.num * ((a.den : ℤ) * (b.den : ℤ)) : ℤ) : ℚ)
      = c * ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) := by
    push_cast
    rw [← rat_mul_den c]; ring
  have e2 : (((a.num * (b.den : ℤ) + b.num * (a.den : ℤ)) * (c.den : ℤ) : ℤ) : ℚ)
      = (a + b) * ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) := by
    push_cast
    rw [← rat_mul_den a, ← rat_mul_den b]; ring
  rw [← Int.cast_inj (α := ℚ), e1, e2]
  exact (mul_left_inj' hK).symm

/-- Recognising the negation of a rational by cross multiplication. -/
theorem ratNeg_iff (a c : ℚ) : c = -a ↔ c.num * (a.den : ℤ) = -a.num * (c.den : ℤ) := by
  have ha : (0 : ℚ) < (a.den : ℚ) := by exact_mod_cast a.pos
  have hc : (0 : ℚ) < (c.den : ℚ) := by exact_mod_cast c.pos
  have hK : ((a.den : ℚ) * (c.den : ℚ)) ≠ 0 := by positivity
  have e1 : ((c.num * (a.den : ℤ) : ℤ) : ℚ) = c * ((a.den : ℚ) * (c.den : ℚ)) := by
    push_cast
    rw [← rat_mul_den c]; ring
  have e2 : ((-a.num * (c.den : ℤ) : ℤ) : ℚ) = (-a) * ((a.den : ℚ) * (c.den : ℚ)) := by
    push_cast
    rw [← rat_mul_den a]; ring
  rw [← Int.cast_inj (α := ℚ), e1, e2]
  exact (mul_left_inj' hK).symm

/-- The order on `ℚ` is primitive recursive. -/
theorem primrec_ratLe : PrimrecRel ((· ≤ ·) : ℚ → ℚ → Prop) :=
  PrimrecPred.of_eq
    (PrimrecRel.comp primrec_intLe
      (primrec_intMul.comp (primrec_ratNum.comp Primrec.fst)
        (primrec_natCastInt.comp (primrec_ratDen.comp Primrec.snd)))
      (primrec_intMul.comp (primrec_ratNum.comp Primrec.snd)
        (primrec_natCastInt.comp (primrec_ratDen.comp Primrec.fst))))
    (fun p => (ratLe_iff p.1 p.2).symm)

/-- The strict order on `ℚ` is primitive recursive. -/
theorem primrec_ratLt : PrimrecRel ((· < ·) : ℚ → ℚ → Prop) :=
  PrimrecPred.of_eq (PrimrecPred.not (PrimrecRel.comp primrec_ratLe Primrec.snd Primrec.fst))
    (fun p => by simp)

/-- `max` on `ℚ` is primitive recursive. -/
theorem primrec_ratMax : Primrec₂ (max : ℚ → ℚ → ℚ) :=
  primrec₂_max_of_le primrec_ratLe

/-- `min` on `ℚ` is primitive recursive. -/
theorem primrec_ratMin : Primrec₂ (min : ℚ → ℚ → ℚ) :=
  primrec₂_min_of_le primrec_ratLe

/-! ### Computing a rational by searching for it -/

/-- **Search principle.** If a computable test recognises the value of a function into a
denumerable type, then that function is computable: run the test along the standard
enumeration of the target. -/
theorem computable_of_verifier {α σ : Type*} [Primcodable α] [Denumerable σ] {f : α → σ}
    {p : α → σ → Bool} (hp : Computable₂ p) (hspec : ∀ a q, p a q = true ↔ q = f a) :
    Computable f := by
  have hinj : Function.Injective (Denumerable.ofNat σ) := (Denumerable.eqv σ).symm.injective
  have hcomp : Computable₂ (fun (a : α) (n : ℕ) => p a (Denumerable.ofNat σ n)) :=
    hp.comp Computable.fst ((Computable.ofNat σ).comp Computable.snd)
  have hrf : Partrec
      (fun a : α => Nat.rfind (fun n => (Part.some (p a (Denumerable.ofNat σ n))))) :=
    Partrec.rfind hcomp.partrec₂
  have hpart : Partrec (fun a : α =>
      Part.map (fun n : ℕ => Denumerable.ofNat σ n)
        (Nat.rfind (fun n => (Part.some (p a (Denumerable.ofNat σ n)))))) :=
    Partrec.map hrf ((Computable.ofNat σ).comp Computable.snd).to₂
  refine Partrec.of_eq_tot hpart (fun a => ?_)
  have h0 : Denumerable.ofNat σ ((Denumerable.eqv σ) (f a)) = f a :=
    (Denumerable.eqv σ).symm_apply_apply (f a)
  have hmem : (Denumerable.eqv σ) (f a) ∈
      Nat.rfind (fun n => (Part.some (p a (Denumerable.ofNat σ n)))) := by
    refine Nat.mem_rfind.2 ⟨?_, ?_⟩
    · have htrue : p a (Denumerable.ofNat σ ((Denumerable.eqv σ) (f a))) = true :=
        (hspec a _).2 h0
      rw [htrue]
      exact Part.mem_some _
    · intro m hm
      have hne : Denumerable.ofNat σ m ≠ f a := by
        intro hcon
        exact absurd (hinj (hcon.trans h0.symm)) (by omega)
      have hfalse : p a (Denumerable.ofNat σ m) = false := by
        rcases Bool.eq_false_or_eq_true (p a (Denumerable.ofNat σ m)) with h | h
        · exact absurd ((hspec a _).1 h) hne
        · exact h
      rw [hfalse]
      exact Part.mem_some _
  rw [← h0]
  exact Part.mem_map _ hmem

/-- Addition on `ℚ` is computable. -/
theorem computable_ratAdd : Computable₂ ((· + ·) : ℚ → ℚ → ℚ) := by
  have hnum : Primrec (fun z : (ℚ × ℚ) × ℚ => z.2.num) := primrec_ratNum.comp Primrec.snd
  have hden : Primrec (fun z : (ℚ × ℚ) × ℚ => ((z.2.den : ℤ))) :=
    primrec_natCastInt.comp (primrec_ratDen.comp Primrec.snd)
  have hn1 : Primrec (fun z : (ℚ × ℚ) × ℚ => z.1.1.num) :=
    primrec_ratNum.comp (Primrec.fst.comp Primrec.fst)
  have hn2 : Primrec (fun z : (ℚ × ℚ) × ℚ => z.1.2.num) :=
    primrec_ratNum.comp (Primrec.snd.comp Primrec.fst)
  have hd1 : Primrec (fun z : (ℚ × ℚ) × ℚ => ((z.1.1.den : ℤ))) :=
    primrec_natCastInt.comp (primrec_ratDen.comp (Primrec.fst.comp Primrec.fst))
  have hd2 : Primrec (fun z : (ℚ × ℚ) × ℚ => ((z.1.2.den : ℤ))) :=
    primrec_natCastInt.comp (primrec_ratDen.comp (Primrec.snd.comp Primrec.fst))
  have hver : Primrec (fun z : (ℚ × ℚ) × ℚ =>
      decide (z.2.num * ((z.1.1.den : ℤ) * (z.1.2.den : ℤ))
        = (z.1.1.num * (z.1.2.den : ℤ) + z.1.2.num * (z.1.1.den : ℤ)) * (z.2.den : ℤ))) :=
    (PrimrecRel.comp Primrec.eq
      (primrec_intMul.comp hnum (primrec_intMul.comp hd1 hd2))
      (primrec_intMul.comp
        (primrec_intAdd.comp (primrec_intMul.comp hn1 hd2) (primrec_intMul.comp hn2 hd1))
        hden)).decide
  refine computable_of_verifier (p := fun (ab : ℚ × ℚ) (c : ℚ) =>
    decide (c.num * ((ab.1.den : ℤ) * (ab.2.den : ℤ))
      = (ab.1.num * (ab.2.den : ℤ) + ab.2.num * (ab.1.den : ℤ)) * (c.den : ℤ)))
    hver.to_comp.to₂ (fun ab c => ?_)
  simpa using (ratAdd_iff ab.1 ab.2 c).symm


/-- Negation on `ℚ` is computable. -/
theorem computable_ratNeg : Computable (fun r : ℚ => -r) := by
  have hn1 : Primrec (fun z : ℚ × ℚ => z.1.num) := primrec_ratNum.comp Primrec.fst
  have hd1 : Primrec (fun z : ℚ × ℚ => ((z.1.den : ℤ))) :=
    primrec_natCastInt.comp (primrec_ratDen.comp Primrec.fst)
  have hn2 : Primrec (fun z : ℚ × ℚ => z.2.num) := primrec_ratNum.comp Primrec.snd
  have hd2 : Primrec (fun z : ℚ × ℚ => ((z.2.den : ℤ))) :=
    primrec_natCastInt.comp (primrec_ratDen.comp Primrec.snd)
  have hneg : Primrec (fun z : ℚ × ℚ => -z.1.num) :=
    (primrec_intMul.comp (Primrec.const (-1 : ℤ)) hn1).of_eq (fun z => by ring)
  have hver : Primrec (fun z : ℚ × ℚ =>
      decide (z.2.num * (z.1.den : ℤ) = -z.1.num * (z.2.den : ℤ))) :=
    (PrimrecRel.comp Primrec.eq (primrec_intMul.comp hn2 hd1)
      (primrec_intMul.comp hneg hd2)).decide
  refine computable_of_verifier
    (p := fun (a : ℚ) (c : ℚ) => decide (c.num * (a.den : ℤ) = -a.num * (c.den : ℤ)))
    hver.to_comp.to₂ (fun a c => ?_)
  simpa using (ratNeg_iff a c).symm

/-- Subtraction on `ℚ` is computable. -/
theorem computable_ratSub : Computable₂ ((· - ·) : ℚ → ℚ → ℚ) :=
  (computable_ratAdd.comp Computable.fst (computable_ratNeg.comp Computable.snd)).of_eq
    (fun p => (sub_eq_add_neg p.1 p.2).symm)

/-- The natural-number cast `ℕ → ℚ` is computable. -/
theorem computable_natCastRat : Computable (fun n : ℕ => (n : ℚ)) := by
  have hn : Primrec (fun z : ℕ × ℚ => z.2.num) := primrec_ratNum.comp Primrec.snd
  have hd : Primrec (fun z : ℕ × ℚ => ((z.2.den : ℤ))) :=
    primrec_natCastInt.comp (primrec_ratDen.comp Primrec.snd)
  have hc : Primrec (fun z : ℕ × ℚ => ((z.1 : ℤ))) := primrec_natCastInt.comp Primrec.fst
  have hver : Primrec (fun z : ℕ × ℚ =>
      decide (z.2.num = (z.1 : ℤ) * (z.2.den : ℤ))) :=
    (PrimrecRel.comp Primrec.eq hn (primrec_intMul.comp hc hd)).decide
  refine computable_of_verifier
    (p := fun (n : ℕ) (c : ℚ) => decide (c.num = (n : ℤ) * (c.den : ℤ)))
    hver.to_comp.to₂ (fun n c => ?_)
  have hden : (0 : ℚ) < (c.den : ℚ) := by exact_mod_cast c.pos
  have key : ((c.num : ℚ) = ((n : ℤ) : ℚ) * ((c.den : ℤ) : ℚ)) ↔ c = (n : ℚ) := by
    rw [← rat_mul_den c]
    push_cast
    constructor
    · intro h
      exact mul_right_cancel₀ (ne_of_gt hden) h
    · intro h
      rw [h]
  simp only [decide_eq_true_eq]
  rw [← key, ← Int.cast_inj (α := ℚ)]
  push_cast
  tauto

/-- The rationals `1 / (n + 1)` form a computable sequence. -/
theorem computable_invSucc : Computable (fun n : ℕ => (1 / ((n : ℚ) + 1) : ℚ)) := by
  have hn : Primrec (fun z : ℕ × ℚ => z.2.num) := primrec_ratNum.comp Primrec.snd
  have hd : Primrec (fun z : ℕ × ℚ => ((z.2.den : ℤ))) :=
    primrec_natCastInt.comp (primrec_ratDen.comp Primrec.snd)
  have hc : Primrec (fun z : ℕ × ℚ => ((z.1 : ℤ) + 1)) :=
    primrec_intAdd.comp (primrec_natCastInt.comp Primrec.fst) (Primrec.const 1)
  have hver : Primrec (fun z : ℕ × ℚ =>
      decide (z.2.num * ((z.1 : ℤ) + 1) = (z.2.den : ℤ))) :=
    (PrimrecRel.comp Primrec.eq (primrec_intMul.comp hn hc) hd).decide
  refine computable_of_verifier
    (p := fun (n : ℕ) (c : ℚ) => decide (c.num * ((n : ℤ) + 1) = (c.den : ℤ)))
    hver.to_comp.to₂ (fun n c => ?_)
  have hden : (0 : ℚ) < (c.den : ℚ) := by exact_mod_cast c.pos
  have hdne : ((c.den : ℚ)) ≠ 0 := ne_of_gt hden
  have hnpos : ((n : ℚ) + 1) ≠ 0 := by positivity
  simp only [decide_eq_true_eq]
  rw [← Int.cast_inj (α := ℚ)]
  push_cast
  rw [← rat_mul_den c]
  constructor
  · intro h
    have h2 : (c * ((n : ℚ) + 1)) * (c.den : ℚ) = 1 * (c.den : ℚ) := by
      rw [one_mul]
      calc (c * ((n : ℚ) + 1)) * (c.den : ℚ) = c * (c.den : ℚ) * ((n : ℚ) + 1) := by ring
        _ = (c.den : ℚ) := h
    exact (eq_div_iff hnpos).2 (mul_right_cancel₀ hdne h2)
  · intro h
    have h3 : c * ((n : ℚ) + 1) = 1 := (eq_div_iff hnpos).1 h
    calc c * (c.den : ℚ) * ((n : ℚ) + 1) = (c * ((n : ℚ) + 1)) * (c.den : ℚ) := by ring
      _ = 1 * (c.den : ℚ) := by rw [h3]
      _ = (c.den : ℚ) := one_mul _


/-! ## Lower semicomputable reals -/

/-- A real number is *lower semicomputable* if it is the limit of a computable
non-decreasing sequence of rationals.  This is definitionally the predicate
`Kolmogorov.IsLowerSemicomputableReal` of
`KolmogorovMathlib.MonotoneComplexity.Omega.Basic.Part01`. -/
def IsLowerSemicomputableReal (a : ℝ) : Prop :=
  ∃ q : ℕ → ℚ, Computable q ∧ Monotone q ∧
    Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds a)

/-- A real number is *computable* if a rational approximation with any prescribed positive
rational precision can be computed.  Definitionally the predicate
`Kolmogorov.IsComputableReal` of
`KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals`. -/
def IsComputableReal (a : ℝ) : Prop :=
  ∃ f : ℚ → ℚ, Computable f ∧ ∀ e : ℚ, 0 < e → |a - (f e : ℝ)| ≤ (e : ℝ)

/-- A sequence of reals is *lower semicomputable* (uniformly enumerable from below).
Definitionally the predicate `Kolmogorov.IsLowerSemicomputableSeq` of
`KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals`. -/
def IsLowerSemicomputableSeq (p : ℕ → ℝ) : Prop :=
  ∃ f : ℕ → ℕ → Option ℚ, Computable (fun z : ℕ × ℕ => f z.1 z.2) ∧
    (∀ i n, ∀ q ∈ f i n, ∃ q' ∈ f i (n + 1), q ≤ q') ∧
    (∀ i, IsLUB {r : ℝ | ∃ n q, f i n = some q ∧ (q : ℝ) = r} (p i))

/-- Unfolding lemma: transports results to any other copy of the definition. -/
theorem isLowerSemicomputableReal_iff (a : ℝ) :
    IsLowerSemicomputableReal a ↔ ∃ q : ℕ → ℚ, Computable q ∧ Monotone q ∧
      Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds a) := Iff.rfl

/-- Unfolding lemma: transports results to any other copy of the definition. -/
theorem isComputableReal_iff (a : ℝ) :
    IsComputableReal a ↔ ∃ f : ℚ → ℚ, Computable f ∧
      ∀ e : ℚ, 0 < e → |a - (f e : ℝ)| ≤ (e : ℝ) := Iff.rfl

/-- Unfolding lemma: transports results to any other copy of the definition. -/
theorem isLowerSemicomputableSeq_iff (p : ℕ → ℝ) :
    IsLowerSemicomputableSeq p ↔ ∃ f : ℕ → ℕ → Option ℚ,
      Computable (fun z : ℕ × ℕ => f z.1 z.2) ∧
      (∀ i n, ∀ q ∈ f i n, ∃ q' ∈ f i (n + 1), q ≤ q') ∧
      (∀ i, IsLUB {r : ℝ | ∃ n q, f i n = some q ∧ (q : ℝ) = r} (p i)) := Iff.rfl

/-! ### Monotonisation -/

/-- The running maximum `runningMax q n = max {q i | i ≤ n}` of a sequence of rationals. -/
def runningMax (q : ℕ → ℚ) : ℕ → ℚ
  | 0 => q 0
  | (n + 1) => max (runningMax q n) (q (n + 1))

/-- The running maximum at `0`. -/
@[simp] theorem runningMax_zero (q : ℕ → ℚ) : runningMax q 0 = q 0 := rfl

/-- Recursion equation for the running maximum. -/
@[simp] theorem runningMax_succ (q : ℕ → ℚ) (n : ℕ) :
    runningMax q (n + 1) = max (runningMax q n) (q (n + 1)) := rfl

/-- Casting a monotone rational sequence into `ℝ` keeps it monotone. -/
theorem monotone_ratCast {q : ℕ → ℚ} (hm : Monotone q) : Monotone (fun n => (q n : ℝ)) := by
  intro m n hmn
  change ((q m : ℚ) : ℝ) ≤ ((q n : ℚ) : ℝ)
  exact_mod_cast hm hmn

/-- The running maximum of a computable sequence of rationals is computable. -/
theorem computable_runningMax {q : ℕ → ℚ} (hq : Computable q) : Computable (runningMax q) := by
  have hstep : Computable₂ (fun (_ : ℕ) (z : ℕ × ℚ) => max z.2 (q (z.1 + 1))) :=
    (primrec_ratMax.to_comp.comp (Computable.snd.comp Computable.snd)
      (hq.comp ((Primrec.succ.to_comp).comp (Computable.fst.comp Computable.snd)))).to₂
  have h := Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ : ℕ => q 0)
    (h := fun (_ : ℕ) (z : ℕ × ℚ) => max z.2 (q (z.1 + 1)))
    Computable.id (Computable.const (q 0)) hstep
  refine h.of_eq (fun n => ?_)
  induction n with
  | zero => rfl
  | succ n ih => rw [runningMax_succ, ← ih]

/-- Each term is below the running maximum. -/
theorem le_runningMax (q : ℕ → ℚ) (n : ℕ) : q n ≤ runningMax q n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

/-- The running maximum is non-decreasing. -/
theorem monotone_runningMax (q : ℕ → ℚ) : Monotone (runningMax q) :=
  monotone_nat_of_le_succ (fun n => by rw [runningMax_succ]; exact le_max_left _ _)

/-- The running maximum is attained. -/
theorem exists_runningMax_eq (q : ℕ → ℚ) (n : ℕ) : ∃ i, i ≤ n ∧ runningMax q n = q i := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    obtain ⟨i, hi, hEq⟩ := ih
    rcases le_total (runningMax q n) (q (n + 1)) with hle | hle
    · exact ⟨n + 1, le_rfl, by rw [runningMax_succ, max_eq_right hle]⟩
    · exact ⟨i, hi.trans (Nat.le_succ n), by rw [runningMax_succ, max_eq_left hle, hEq]⟩

/-- The running maximum is bounded by any bound on the initial segment. -/
theorem runningMax_le {q : ℕ → ℚ} {b : ℚ} {n : ℕ} (h : ∀ i ≤ n, q i ≤ b) :
    runningMax q n ≤ b := by
  obtain ⟨i, hi, hEq⟩ := exists_runningMax_eq q n
  rw [hEq]
  exact h i hi

/-- Monotonisation does not change the supremum. -/
theorem isLUB_range_runningMax {q : ℕ → ℚ} {a : ℝ}
    (h : IsLUB (Set.range fun n => (q n : ℝ)) a) :
    IsLUB (Set.range fun n => ((runningMax q n : ℚ) : ℝ)) a := by
  constructor
  · rintro x ⟨n, rfl⟩
    obtain ⟨i, -, hEq⟩ := exists_runningMax_eq q n
    change ((runningMax q n : ℚ) : ℝ) ≤ a
    rw [hEq]
    exact h.1 ⟨i, rfl⟩
  · intro b hb
    refine h.2 ?_
    rintro x ⟨n, rfl⟩
    refine le_trans ?_ (hb ⟨n, rfl⟩)
    change ((q n : ℚ) : ℝ) ≤ ((runningMax q n : ℚ) : ℝ)
    exact_mod_cast le_runningMax q n

/-! ### Constructors -/

/-- **Workhorse constructor.** A real number that is the supremum of the values of a
computable sequence of rationals is lower semicomputable: monotonise by running maxima. -/
theorem isLowerSemicomputableReal_of_isLUB {q : ℕ → ℚ} (hq : Computable q) {a : ℝ}
    (h : IsLUB (Set.range fun n => (q n : ℝ)) a) : IsLowerSemicomputableReal a :=
  ⟨runningMax q, computable_runningMax hq, monotone_runningMax q,
    tendsto_atTop_isLUB (monotone_ratCast (monotone_runningMax q))
      (isLUB_range_runningMax h)⟩

/-- A computable monotone rational sequence with a limit gives a lower semicomputable real
(this is the definition, packaged as a constructor). -/
theorem isLowerSemicomputableReal_of_tendsto {q : ℕ → ℚ} (hq : Computable q) (hm : Monotone q)
    {a : ℝ} (h : Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds a)) :
    IsLowerSemicomputableReal a := ⟨q, hq, hm, h⟩

/-- A computable monotone bounded rational sequence has a lower semicomputable supremum. -/
theorem isLowerSemicomputableReal_of_monotone_isLUB {q : ℕ → ℚ} (hq : Computable q)
    (hm : Monotone q) {a : ℝ} (h : IsLUB (Set.range fun n => (q n : ℝ)) a) :
    IsLowerSemicomputableReal a :=
  ⟨q, hq, hm, tendsto_atTop_isLUB (monotone_ratCast hm) h⟩

/-- Every lower semicomputable real is the supremum of a computable non-decreasing sequence
of rational lower bounds. -/
theorem IsLowerSemicomputableReal.exists_seq {a : ℝ} (h : IsLowerSemicomputableReal a) :
    ∃ q : ℕ → ℚ, Computable q ∧ Monotone q ∧ (∀ n, (q n : ℝ) ≤ a) ∧
      IsLUB (Set.range fun n => (q n : ℝ)) a ∧
      Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds a) := by
  obtain ⟨q, hq, hm, ht⟩ := h
  have hcast : Monotone (fun n => (q n : ℝ)) := monotone_ratCast hm
  exact ⟨q, hq, hm, fun n => hcast.ge_of_tendsto ht n, isLUB_of_tendsto_atTop hcast ht, ht⟩

/-- **One-sided approximation from below.** -/
theorem IsLowerSemicomputableReal.exists_lower_approx {a : ℝ} (h : IsLowerSemicomputableReal a) :
    ∃ q : ℕ → ℚ, Computable q ∧ Monotone q ∧ (∀ n, (q n : ℝ) ≤ a) ∧
      ∀ ε : ℝ, 0 < ε → ∃ n, a - ε < (q n : ℝ) := by
  obtain ⟨q, hq, hm, ht⟩ := h
  have hcast : Monotone (fun n => (q n : ℝ)) := monotone_ratCast hm
  refine ⟨q, hq, hm, fun n => hcast.ge_of_tendsto ht n, fun ε hε => ?_⟩
  have hlt : a - ε < a := by linarith
  exact (ht.eventually_const_lt hlt).exists

/-- **One-sided approximation from above**, from lower semicomputability of `-a`. -/
theorem IsLowerSemicomputableReal.exists_upper_approx {a : ℝ}
    (h : IsLowerSemicomputableReal (-a)) :
    ∃ q : ℕ → ℚ, Computable q ∧ Antitone q ∧ (∀ n, a ≤ (q n : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ n, (q n : ℝ) < a + ε := by
  obtain ⟨p, hp, hm, hle, happrox⟩ := h.exists_lower_approx
  refine ⟨fun n => -p n, computable_ratNeg.comp hp, fun m n hmn => ?_, fun n => ?_, ?_⟩
  · exact neg_le_neg (hm hmn)
  · have := hle n
    push_cast
    linarith
  · intro ε hε
    obtain ⟨n, hn⟩ := happrox ε hε
    refine ⟨n, ?_⟩
    push_cast
    linarith

/-! ### The book's characterisation -/

/-- The index of a rational number in the standard computable enumeration of `ℚ`.  This is
`Encodable.encode` for the `Primcodable ℚ` instance, which is *not* the structural encoding
`Rat.instEncodable` used by `ratCode`. -/
def ratIndex (r : ℚ) : ℕ := @Encodable.encode ℚ (@Primcodable.toEncodable ℚ _) r

/-- The index of the `i`-th rational is `i`. -/
theorem ratIndex_ofNat (i : ℕ) : ratIndex (Denumerable.ofNat ℚ i) = i :=
  Denumerable.encode_ofNat i

/-- Decoding the index of a rational returns it. -/
theorem ofNat_ratIndex (r : ℚ) : Denumerable.ofNat ℚ (ratIndex r) = r :=
  Denumerable.ofNat_encode r

/-- Halting of a partial recursive function is witnessed by a bounded evaluation of any
code for it. -/
theorem dom_iff_exists_evaln {α : Type*} [Primcodable α] (G : α →. Unit)
    (c : Nat.Partrec.Code)
    (hc : c.eval = fun n => (Part.ofOption (Encodable.decode (α := α) n)).bind
      (fun x => Part.map Encodable.encode (G x))) (x : α) :
    (G x).Dom ↔ ∃ k, (Nat.Partrec.Code.evaln k c (Encodable.encode x)).isSome := by
  have h_eval : (c.eval (Encodable.encode x)).Dom ↔ (G x).Dom := by aesop
  convert h_eval.symm using 1
  simp only [Part.dom_iff_mem, Nat.Partrec.Code.evaln_complete]
  constructor
  · rintro ⟨k, hk⟩
    cases h : Nat.Partrec.Code.evaln k c (Encodable.encode x) <;> aesop
  · rintro ⟨y, k, hk⟩
    exact ⟨k, by aesop⟩

/-- **Forward direction of the book's characterisation.** If `a` is lower semicomputable
then the set of rationals below `a` is enumerable. -/
theorem isRE_rat_lt_of_isLowerSemicomputableReal {a : ℝ} (h : IsLowerSemicomputableReal a) :
    IsRE (fun r : ℚ => (r : ℝ) < a) := by
  obtain ⟨q, hq, -, hle, -, ht⟩ := h.exists_seq
  have hkey : ∀ r : ℚ, ((r : ℝ) < a ↔ ∃ n, decide (r < q n) = true) := by
    intro r
    constructor
    · intro hr
      obtain ⟨n, hn⟩ := (ht.eventually_const_lt hr).exists
      have hn' : r < q n := by exact_mod_cast hn
      exact ⟨n, by simpa using hn'⟩
    · rintro ⟨n, hn⟩
      have hn' : r < q n := by simpa using hn
      have hcast : ((r : ℚ) : ℝ) < ((q n : ℚ) : ℝ) := by exact_mod_cast hn'
      exact lt_of_lt_of_le hcast (hle n)
  have hdec : Computable₂ (fun (r : ℚ) (n : ℕ) => decide (r < q n)) :=
    ((PrimrecRel.decide primrec_ratLt).to_comp).comp Computable.fst (hq.comp Computable.snd)
  refine ⟨fun r => Part.map (fun _ => ())
      (Nat.rfind (fun n => (Part.some (decide (r < q n))))),
    Partrec.map (Partrec.rfind hdec.partrec₂) (Computable.const ()).to₂, fun r => ?_⟩
  change (Nat.rfind (show Nat →. Bool from fun n => Part.some (decide (r < q n)))).Dom ↔
    ((r : ℝ) < a)
  rw [Nat.rfind_dom, hkey r]
  simp_rw [Part.mem_some_iff]
  constructor
  · rintro ⟨n, hn, -⟩
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm, fun _ => trivial⟩

/-- **Backward direction of the book's characterisation.** If the set of rationals below `a`
is enumerable then `a` is lower semicomputable. -/
theorem isLowerSemicomputableReal_of_isRE_rat_lt {a : ℝ}
    (h : IsRE (fun r : ℚ => (r : ℝ) < a)) : IsLowerSemicomputableReal a := by
  obtain ⟨F, hF, hdom⟩ := h
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hF
  obtain ⟨r₀, hr₀⟩ := exists_rat_lt a
  have hcode : ∀ x : ℚ, ((x : ℝ) < a ↔
      ∃ k, (Nat.Partrec.Code.evaln k c (ratIndex x)).isSome) := by
    intro x
    exact ((hdom x).symm).trans (dom_iff_exists_evaln F c hc x)
  have hevaln : Primrec (fun p : ℕ × ℕ => Nat.Partrec.Code.evaln p.1 c p.2) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c)) Primrec.snd)
  have hfound : Primrec (fun k : ℕ =>
      (Nat.Partrec.Code.evaln (k.unpair.2 + 1) c k.unpair.1).isSome) :=
    Primrec.option_isSome.comp (hevaln.comp
      (Primrec.pair (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))
        (Primrec.fst.comp Primrec.unpair)))
  set g : ℕ → ℚ := fun k =>
    if (Nat.Partrec.Code.evaln (k.unpair.2 + 1) c k.unpair.1).isSome = true
      then Denumerable.ofNat ℚ k.unpair.1 else r₀ with hgdef
  have hgcomp : Computable g :=
    (Primrec.ite (Primrec.primrecPred (hfound.of_eq (fun k => by simp)))
      ((Primrec.ofNat ℚ).comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const r₀)).to_comp
  have hglt : ∀ k, ((g k : ℚ) : ℝ) < a := by
    intro k
    by_cases hk : (Nat.Partrec.Code.evaln (k.unpair.2 + 1) c k.unpair.1).isSome = true
    · have hgk : g k = Denumerable.ofNat ℚ k.unpair.1 := by
        rw [hgdef]; simp only [ite_eq_left hk]
      rw [hgk]
      refine (hcode _).2 ⟨k.unpair.2 + 1, ?_⟩
      rwa [ratIndex_ofNat]
    · have hgk : g k = r₀ := by rw [hgdef]; simp only [ite_eq_right hk]
      rw [hgk]
      exact hr₀
  have hgrange : ∀ r : ℚ, ((r : ℝ) < a) → ∃ k, g k = r := by
    intro r hr
    obtain ⟨k₀, hk₀⟩ := (hcode r).1 hr
    refine ⟨Nat.pair (ratIndex r) k₀, ?_⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk₀
    have hstep : (Nat.Partrec.Code.evaln (k₀ + 1) c (ratIndex r)).isSome = true :=
      Option.isSome_iff_exists.2 ⟨y, Option.mem_def.mp
        (Nat.Partrec.Code.evaln_mono (Nat.le_succ k₀) (Option.mem_def.mpr hy))⟩
    rw [hgdef]
    simp only [Nat.unpair_pair]
    rw [ite_eq_left hstep, ofNat_ratIndex]
  have hlub : IsLUB (Set.range fun k => ((g k : ℚ) : ℝ)) a := by
    constructor
    · rintro x ⟨k, rfl⟩
      change ((g k : ℚ) : ℝ) ≤ a
      exact (hglt k).le
    · intro b hb
      by_contra hcon
      push Not at hcon
      obtain ⟨r, hbr, hra⟩ := exists_rat_btwn hcon
      obtain ⟨k, hk⟩ := hgrange r hra
      have hmem : ((g k : ℚ) : ℝ) ≤ b := hb ⟨k, rfl⟩
      rw [hk] at hmem
      linarith
  exact isLowerSemicomputableReal_of_isLUB hgcomp hlub

/-- **The book's characterisation** (Shen–Uspensky–Vereshchagin, after Problem 95):
a real number is lower semicomputable if and only if the set of rational numbers less
than it is enumerable. -/
theorem isLowerSemicomputableReal_iff_isRE (a : ℝ) :
    IsLowerSemicomputableReal a ↔ IsRE (fun r : ℚ => (r : ℝ) < a) :=
  ⟨isRE_rat_lt_of_isLowerSemicomputableReal, isLowerSemicomputableReal_of_isRE_rat_lt⟩

/-! ### Closure properties -/

/-- A rational (cast to `ℝ`) is lower semicomputable. -/
theorem isLowerSemicomputableReal_ratCast (r : ℚ) : IsLowerSemicomputableReal (r : ℝ) :=
  ⟨fun _ => r, Computable.const r, monotone_const, tendsto_const_nhds⟩

/-- The supremum characterisation of a sequence of rational lower bounds. -/
theorem isLUB_of_le_of_tendsto {q : ℕ → ℚ} {a : ℝ} (hle : ∀ n, (q n : ℝ) ≤ a)
    (ht : Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds a)) :
    IsLUB (Set.range fun n => (q n : ℝ)) a :=
  ⟨by rintro x ⟨n, rfl⟩; exact hle n,
    fun b hb => le_of_tendsto ht (Filter.Eventually.of_forall (fun n => hb ⟨n, rfl⟩))⟩

/-- A real approached from below by a computable sequence of rationals is lower
semicomputable (the sequence need not be monotone). -/
theorem isLowerSemicomputableReal_of_tendsto_le {q : ℕ → ℚ} (hq : Computable q) {a : ℝ}
    (hle : ∀ n, (q n : ℝ) ≤ a)
    (ht : Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds a)) :
    IsLowerSemicomputableReal a :=
  isLowerSemicomputableReal_of_isLUB hq (isLUB_of_le_of_tendsto hle ht)

/-- A computable real is lower semicomputable. -/
theorem IsComputableReal.isLowerSemicomputableReal {a : ℝ} (h : IsComputableReal a) :
    IsLowerSemicomputableReal a := by
  obtain ⟨f, hf, hspec⟩ := h
  have hepos : ∀ n : ℕ, (0 : ℚ) < 1 / ((n : ℚ) + 1) := by
    intro n
    have hn : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    positivity
  have hecast : ∀ n : ℕ, ((1 / ((n : ℚ) + 1) : ℚ) : ℝ) = 1 / ((n : ℝ) + 1) := by
    intro n; push_cast; ring
  set q : ℕ → ℚ := fun n => f (1 / ((n : ℚ) + 1)) - 1 / ((n : ℚ) + 1) with hqdef
  have hq : Computable q :=
    computable_ratSub.comp (hf.comp computable_invSucc) computable_invSucc
  have hqcast : ∀ n : ℕ, ((q n : ℚ) : ℝ)
      = ((f (1 / ((n : ℚ) + 1)) : ℚ) : ℝ) - 1 / ((n : ℝ) + 1) := by
    intro n
    rw [hqdef]
    push_cast
    ring
  have hle : ∀ n, (q n : ℝ) ≤ a := by
    intro n
    have h1 := hspec _ (hepos n)
    have h2 : -((1 / ((n : ℚ) + 1) : ℚ) : ℝ) ≤ a - ((f (1 / ((n : ℚ) + 1)) : ℚ) : ℝ) :=
      neg_le_of_abs_le h1
    rw [hecast n] at h2
    rw [hqcast n]
    linarith
  have hge : ∀ n : ℕ, a - 2 * (1 / ((n : ℝ) + 1)) ≤ (q n : ℝ) := by
    intro n
    have h1 := hspec _ (hepos n)
    have h2 : a - ((f (1 / ((n : ℚ) + 1)) : ℚ) : ℝ) ≤ ((1 / ((n : ℚ) + 1) : ℚ) : ℝ) :=
      le_of_abs_le h1
    rw [hecast n] at h2
    rw [hqcast n]
    linarith
  have hinv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlow : Filter.Tendsto (fun n : ℕ => a - 2 * (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds a) := by
    have h2 := hinv.const_mul (2 : ℝ)
    have := (tendsto_const_nhds (x := a) (f := Filter.atTop (α := ℕ))).sub h2
    simpa using this
  have ht : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds a) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hge hle
  exact isLowerSemicomputableReal_of_tendsto_le hq hle ht

end ComputableReals
end Kolmogorov
