import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.Interface.ComputableReals.Part01
import Mathlib.Computability.Partrec
import Mathlib.Data.Rat.Denumerable
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Computability of rational arithmetic

`Mathlib` equips `ℤ` and `ℚ` with `Primcodable` structures (obtained from their
`Denumerable` instances), but it provides no lemmas showing that the arithmetic
operations on these types are computable.  This file supplies the missing
toolkit:

* `ComputableReals.primrec_natCastInt`, `Kolmogorov.primrec_intNeg`,
  `Kolmogorov.primrec_intAdd`, `Kolmogorov.primrec_intSub`,
  `Kolmogorov.primrec_intMul` : primitive recursiveness of integer arithmetic;
* `Kolmogorov.computable_ratNum`, `Kolmogorov.computable_ratDen` : the numerator
  and denominator of a rational number are computable;
* `Kolmogorov.computable_of_num_den` : a rational-valued function is computable
  as soon as it can be written as `N a / D a` for computable `N : α → ℤ` and
  `D : α → ℕ` with `D a ≠ 0`;
* `Kolmogorov.computable_ratAdd`, `Kolmogorov.computable_ratSub`,
  `Kolmogorov.computable_ratHalf` : computability of `+`, `-` and halving on `ℚ`.

The only delicate point is that the `Primcodable ℚ` instance does *not* encode a
rational by the pair (numerator, denominator); it encodes it by its index in the
increasing enumeration of the set of such pairs.  We therefore relate the two
encodings explicitly (`Kolmogorov.encode_eq_ratCount`) and invert the index map
by an unbounded search (`Kolmogorov.computable_ratCode`).
-/

open Encodable Denumerable ENNReal

namespace Kolmogorov

/-! ### Integer codes -/

/-- The standard encoding sends a nonnegative integer `n` to `2n`. -/
lemma int_encode_natCast (n : ℕ) : (encode ((n : ℤ)) : ℕ) = 2 * n := rfl

/-- The standard encoding sends the negative integer `-(n+1)` to `2n + 1`. -/
lemma int_encode_negSucc (n : ℕ) : (encode (Int.negSucc n) : ℕ) = 2 * n + 1 := rfl

/-- The standard encoding of an integer, in closed form. -/
lemma int_encode_eq (m : ℤ) :
    (encode m : ℕ) = if 0 ≤ m then 2 * m.toNat else 2 * m.natAbs - 1 := by
  rcases m with n | n
  · simpa using int_encode_natCast n
  · rw [int_encode_negSucc]
    simp
    omega

/-- The integer decoded from a natural number, in closed form. -/
lemma int_ofNat_eq (n : ℕ) :
    (ofNat ℤ n) = if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n / 2 : ℕ) : ℤ) + 1) := by
  have h : encode (if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n / 2 : ℕ) : ℤ) + 1)) = n := by
    by_cases h : n % 2 = 0
    · rw [if_pos h, int_encode_natCast]; omega
    · rw [if_neg h]
      have hneg : (-(((n / 2 : ℕ) : ℤ) + 1)) = Int.negSucc (n / 2) := by
        simp [Int.negSucc_eq]
      rw [hneg, int_encode_negSucc]; omega
  calc
    ofNat ℤ n = ofNat ℤ (encode (if n % 2 = 0 then ((n / 2 : ℕ) : ℤ)
      else -(((n / 2 : ℕ) : ℤ) + 1))) := congrArg (ofNat ℤ) h.symm
    _ = _ := Denumerable.ofNat_encode _

/-- The absolute value of the integer coded by `n` is `(n+1)/2`. -/
lemma int_natAbs_ofNat (n : ℕ) : (ofNat ℤ n).natAbs = (n + 1) / 2 := by
  rw [int_ofNat_eq]
  by_cases h : n % 2 = 0 <;> simp [h] <;> omega

/-- The absolute value of an integer read off from its code. -/
lemma int_natAbs_eq_encode (m : ℤ) : m.natAbs = ((encode m : ℕ) + 1) / 2 := by
  conv_lhs => rw [← Denumerable.ofNat_encode m]
  exact int_natAbs_ofNat _

/-- The truncation to `ℕ` of the integer coded by `n`. -/
lemma int_toNat_ofNat (n : ℕ) : (ofNat ℤ n).toNat = if n % 2 = 0 then n / 2 else 0 := by
  rw [int_ofNat_eq]
  by_cases h : n % 2 = 0 <;> simp [h] <;> omega

/-- Negating an integer flips the parity of its code. -/
lemma int_encode_neg (m : ℤ) :
    (encode (-m) : ℕ) =
      if (encode m : ℕ) % 2 = 0 then (encode m : ℕ) - 1 else (encode m : ℕ) + 1 := by
  rw [int_encode_eq m, int_encode_eq (-m)]
  by_cases h : (0 : ℤ) ≤ m
  · simp only [if_pos h]
    by_cases h0 : m = 0
    · subst h0; simp
    · rw [if_neg (by omega : ¬ ((0 : ℤ) ≤ -m)), if_pos (by omega : (2 * m.toNat) % 2 = 0)]
      omega
  · rw [if_neg h, if_pos (by omega : (0 : ℤ) ≤ -m),
      if_neg (by have : 1 ≤ m.natAbs := by omega
                 omega : ¬ ((2 * m.natAbs - 1) % 2 = 0))]
    omega

/-- The code of a difference of two natural numbers, in closed form. -/
lemma int_encode_subNat (a b : ℕ) :
    (encode ((a : ℤ) - (b : ℤ)) : ℕ) = if b ≤ a then 2 * (a - b) else 2 * (b - a) - 1 := by
  rw [int_encode_eq]
  by_cases h : b ≤ a
  · rw [if_pos (by omega : (0 : ℤ) ≤ (a : ℤ) - b), if_pos h]; omega
  · rw [if_neg (by omega : ¬ ((0 : ℤ) ≤ (a : ℤ) - b)), if_neg h]; omega

/-! ### Primitive recursiveness of integer arithmetic -/

/-- Negation of integers is primitive recursive. -/
lemma primrec_intNeg : Primrec (fun m : ℤ => -m) := by
  rw [← Primrec.encode_iff]
  refine (Primrec.ite (c := fun m : ℤ => (encode m : ℕ) % 2 = 0) ?_ ?_ ?_).of_eq
    fun m => (int_encode_neg m).symm
  · exact PrimrecRel.comp Primrec.eq
      (Primrec.nat_mod.comp Primrec.encode (Primrec.const 2)) (Primrec.const 0)
  · exact Primrec.nat_sub.comp Primrec.encode (Primrec.const 1)
  · exact Primrec.nat_add.comp Primrec.encode (Primrec.const 1)

/-- The difference of two natural numbers, taken in the integers, is primitive recursive. -/
lemma primrec_intSubNat : Primrec₂ (fun a b : ℕ => (a : ℤ) - (b : ℤ)) := by
  have h : Primrec (fun p : ℕ × ℕ => encode ((p.1 : ℤ) - (p.2 : ℤ))) := by
    refine (Primrec.ite (c := fun p : ℕ × ℕ => p.2 ≤ p.1) ?_ ?_ ?_).of_eq
      fun p => (int_encode_subNat p.1 p.2).symm
    · exact PrimrecRel.comp Primrec.nat_le Primrec.snd Primrec.fst
    · exact Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.fst Primrec.snd)
    · exact Primrec.nat_sub.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.snd Primrec.fst))
        (Primrec.const 1)
  exact Primrec.encode_iff.mp h

/-- Addition of integers is primitive recursive. -/
lemma primrec_intAdd : Primrec₂ (fun a b : ℤ => a + b) := by
  have h : Primrec (fun p : ℤ × ℤ => (p.1 + p.2)) := by
    have hpos : Primrec (fun p : ℤ × ℤ => p.1.toNat + p.2.toNat) :=
      Primrec.nat_add.comp (ComputableReals.primrec_intToNat.comp Primrec.fst)
        (ComputableReals.primrec_intToNat.comp Primrec.snd)
    have hneg : Primrec (fun p : ℤ × ℤ => (-p.1).toNat + (-p.2).toNat) :=
      Primrec.nat_add.comp (ComputableReals.primrec_intToNat.comp (primrec_intNeg.comp Primrec.fst))
        (ComputableReals.primrec_intToNat.comp (primrec_intNeg.comp Primrec.snd))
    exact (primrec_intSubNat.comp hpos hneg).of_eq fun p => by
      have h1 := ComputableReals.int_eq_toNat_sub p.1
      have h2 := ComputableReals.int_eq_toNat_sub p.2
      push_cast
      omega
  exact h

/-- Subtraction of integers is primitive recursive. -/
lemma primrec_intSub : Primrec₂ (fun a b : ℤ => a - b) := by
  have h : Primrec (fun p : ℤ × ℤ => p.1 - p.2) :=
    (primrec_intAdd.comp Primrec.fst (primrec_intNeg.comp Primrec.snd)).of_eq fun p => by ring
  exact h

/-- Multiplication of integers is primitive recursive. -/
lemma primrec_intMul : Primrec₂ (fun a b : ℤ => a * b) := by
  have h : Primrec (fun p : ℤ × ℤ => p.1 * p.2) := by
    have hp1 : Primrec (fun p : ℤ × ℤ => p.1.toNat) :=
      ComputableReals.primrec_intToNat.comp Primrec.fst
    have hp2 : Primrec (fun p : ℤ × ℤ => p.2.toNat) :=
      ComputableReals.primrec_intToNat.comp Primrec.snd
    have hn1 : Primrec (fun p : ℤ × ℤ => (-p.1).toNat) :=
      ComputableReals.primrec_intToNat.comp (primrec_intNeg.comp Primrec.fst)
    have hn2 : Primrec (fun p : ℤ × ℤ => (-p.2).toNat) :=
      ComputableReals.primrec_intToNat.comp (primrec_intNeg.comp Primrec.snd)
    have hpos : Primrec (fun p : ℤ × ℤ => p.1.toNat * p.2.toNat + (-p.1).toNat * (-p.2).toNat) :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp hp1 hp2) (Primrec.nat_mul.comp hn1 hn2)
    have hneg : Primrec (fun p : ℤ × ℤ => p.1.toNat * (-p.2).toNat + (-p.1).toNat * p.2.toNat) :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp hp1 hn2) (Primrec.nat_mul.comp hn1 hp2)
    refine (primrec_intSubNat.comp hpos hneg).of_eq fun p => ?_
    have h1 := ComputableReals.int_eq_toNat_sub p.1
    have h2 := ComputableReals.int_eq_toNat_sub p.2
    push_cast
    nlinarith [h1, h2]
  exact h

/-! ### Rational codes -/

/-- The concrete code of a rational number: the pair (code of numerator, denominator). -/
def ratCode (q : ℚ) : ℕ := Nat.pair (encode q.num) q.den

/-- The naturals which are concrete codes of rational numbers. -/
def IsRatCode (m : ℕ) : Prop :=
  0 < (Nat.unpair m).2 ∧ Nat.Coprime (((Nat.unpair m).1 + 1) / 2) (Nat.unpair m).2

instance : DecidablePred IsRatCode := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The rational number with a given concrete code (junk value `0` off the codes). -/
def ratOfCode (m : ℕ) : ℚ :=
  if IsRatCode m then mkRat (ofNat ℤ (Nat.unpair m).1) (Nat.unpair m).2 else 0

/-- The code of a rational is a valid rational code, i.e. a pairing of a numerator and a positive
denominator that are coprime. -/
lemma isRatCode_ratCode (q : ℚ) : IsRatCode (ratCode q) := by
  refine ⟨?_, ?_⟩ <;> rw [ratCode, Nat.unpair_pair]
  · exact q.pos
  · rw [← int_natAbs_eq_encode]
    exact q.reduced

/-- Decoding the code of a rational returns that rational. -/
lemma ratOfCode_ratCode (q : ℚ) : ratOfCode (ratCode q) = q := by
  rw [ratOfCode, if_pos (isRatCode_ratCode q), ratCode, Nat.unpair_pair,
    Denumerable.ofNat_encode]
  exact Rat.mkRat_num_den' q

/-- Encoding the rational decoded from a valid code returns that code. -/
lemma ratCode_ratOfCode {m : ℕ} (h : IsRatCode m) : ratCode (ratOfCode m) = m := by
  obtain ⟨hpos, hcop⟩ := h
  have hcop' : (ofNat ℤ (Nat.unpair m).1).natAbs.Coprime (Nat.unpair m).2 := by
    rwa [int_natAbs_ofNat]
  have hmk : mkRat (ofNat ℤ (Nat.unpair m).1) (Nat.unpair m).2 =
      ⟨ofNat ℤ (Nat.unpair m).1, (Nat.unpair m).2, by omega, hcop'⟩ :=
    (Rat.mk_eq_mkRat _ _ (by omega) hcop').symm
  rw [ratOfCode, if_pos ⟨hpos, hcop⟩, ratCode, hmk]
  change Nat.pair (encode (ofNat ℤ (Nat.unpair m).1)) (Nat.unpair m).2 = m
  rw [Denumerable.encode_ofNat, Nat.pair_unpair]

/-- The rational coding is injective. -/
lemma ratCode_injective : Function.Injective ratCode := by
  intro a b hab
  rw [← ratOfCode_ratCode a, ← ratOfCode_ratCode b, hab]

/-- A natural number is in the range of Mathlib's rational encoding exactly when it is a valid
rational code. -/
lemma mem_range_encodable_iff (m : ℕ) :
    m ∈ Set.range (@encode ℚ Rat.instEncodable) ↔ IsRatCode m := by
  constructor
  · rintro ⟨q, rfl⟩
    exact isRatCode_ratCode q
  · intro h
    exact ⟨ratOfCode m, ratCode_ratOfCode h⟩

/-- The number of concrete rational codes below `m`. -/
def ratCount (m : ℕ) : ℕ := ((List.range m).filter (fun k => decide (IsRatCode k))).length

/-- Mathlib's `Primcodable ℚ` encoding counts the valid rational codes below the code of the
rational. -/
lemma encode_eq_countP (q : ℚ) :
    (@encode ℚ (@Primcodable.toEncodable ℚ _) q) = (List.range (ratCode q)).countP
      (fun m => @decide (m ∈ Set.range (@encode ℚ Rat.instEncodable))
        (Encodable.decidableRangeEncode ℚ m)) := rfl

/-- Mathlib's `Primcodable ℚ` encoding is the counting function of the valid rational codes,
evaluated at the rational code. -/
lemma encode_eq_ratCount (q : ℚ) :
    (@encode ℚ (@Primcodable.toEncodable ℚ _) q) = ratCount (ratCode q) := by
  rw [encode_eq_countP, ratCount, ← List.countP_eq_length_filter]
  refine List.countP_congr ?_
  intro m _
  simpa using mem_range_encodable_iff m

/-- The index-based encoding of `ℚ` is inverted by counting concrete codes. -/
lemma ofNat_ratCount_ratCode (q : ℚ) : ofNat ℚ (ratCount (ratCode q)) = q := by
  rw [← encode_eq_ratCount q]
  exact Denumerable.ofNat_encode q


/-! ### Computability of the code maps -/

/-- Coprimality may be tested by a bounded search over the possible common divisors. -/
lemma coprime_iff_bounded {a b : ℕ} (hb : 0 < b) :
    Nat.Coprime a b ↔ ∀ k < b + 1, ¬ (a % k = 0 ∧ b % k = 0) ∨ k ≤ 1 := by
  constructor
  · intro h k _
    by_cases hk : a % k = 0 ∧ b % k = 0
    · right
      have hd : k ∣ Nat.gcd a b :=
        Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hk.1) (Nat.dvd_of_mod_eq_zero hk.2)
      rw [Nat.Coprime] at h
      rw [h] at hd
      exact Nat.le_of_dvd one_pos hd
    · exact Or.inl hk
  · intro h
    have hg2 : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
    have hpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_right a hb
    have hle : Nat.gcd a b ≤ b := Nat.le_of_dvd hb hg2
    have hmod : a % Nat.gcd a b = 0 ∧ b % Nat.gcd a b = 0 :=
      ⟨Nat.dvd_iff_mod_eq_zero.mp (Nat.gcd_dvd_left a b), Nat.dvd_iff_mod_eq_zero.mp hg2⟩
    rcases h (Nat.gcd a b) (by omega) with hcon | hle1
    · exact absurd hmod hcon
    · exact Nat.le_antisymm hle1 hpos

/-- Being a valid rational code is a primitive recursive predicate. -/
lemma primrecPred_isRatCode : PrimrecPred IsRatCode := by
  have hR : PrimrecRel (fun k m : ℕ =>
      ¬ ((((Nat.unpair m).1 + 1) / 2) % k = 0 ∧ (Nat.unpair m).2 % k = 0) ∨ k ≤ 1) := by
    have h1 : PrimrecPred (fun p : ℕ × ℕ => (((Nat.unpair p.2).1 + 1) / 2) % p.1 = 0) :=
      PrimrecRel.comp Primrec.eq
        (Primrec.nat_mod.comp
          (Primrec.nat_div.comp
            (Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
            (Primrec.const 2))
          Primrec.fst)
        (Primrec.const 0)
    have h2 : PrimrecPred (fun p : ℕ × ℕ => (Nat.unpair p.2).2 % p.1 = 0) :=
      PrimrecRel.comp Primrec.eq
        (Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst)
        (Primrec.const 0)
    have h3 : PrimrecPred (fun p : ℕ × ℕ => p.1 ≤ 1) :=
      PrimrecRel.comp Primrec.nat_le Primrec.fst (Primrec.const 1)
    exact PrimrecPred.or (PrimrecPred.not (PrimrecPred.and h1 h2)) h3
  have hall : PrimrecPred (fun m : ℕ => ∀ k < (Nat.unpair m).2 + 1,
      ¬ ((((Nat.unpair m).1 + 1) / 2) % k = 0 ∧ (Nat.unpair m).2 % k = 0) ∨ k ≤ 1) :=
    PrimrecRel.comp hR.forall_lt
      (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair)) Primrec.id
  have hpos : PrimrecPred (fun m : ℕ => 0 < (Nat.unpair m).2) :=
    PrimrecRel.comp Primrec.nat_lt (Primrec.const 0) (Primrec.snd.comp Primrec.unpair)
  refine (PrimrecPred.and hpos hall).of_eq fun m => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (coprime_iff_bounded h1).mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (coprime_iff_bounded h1).mp h2⟩

/-- The counting function of the valid rational codes is primitive recursive. -/
lemma primrec_ratCount : Primrec ratCount :=
  Primrec.list_length.comp ((Primrec.listFilter primrecPred_isRatCode).comp Primrec.list_range)

/-- The rational zero has code one. -/
lemma ratCode_zero : ratCode 0 = 1 := rfl

/-- Decoding a natural number as a rational, expressed through Mathlib's decoding and the
counting function. -/
lemma ratOfCode_eq_ofNat (m : ℕ) :
    ratOfCode m = ofNat ℚ (ratCount (if IsRatCode m then m else 1)) := by
  by_cases h : IsRatCode m
  · rw [if_pos h]
    conv_lhs => rw [← ofNat_ratCount_ratCode (ratOfCode m)]
    rw [ratCode_ratOfCode h]
  · rw [if_neg h, ratOfCode, if_neg h, ← ratCode_zero, ofNat_ratCount_ratCode]

/-- Decoding a natural number as a rational is computable. -/
lemma computable_ratOfCode : Computable ratOfCode := by
  have hite : Primrec (fun m : ℕ => if IsRatCode m then m else 1) :=
    Primrec.ite primrecPred_isRatCode Primrec.id (Primrec.const 1)
  exact ((Primrec.ofNat ℚ).comp (primrec_ratCount.comp hite)).to_comp.of_eq
    fun m => (ratOfCode_eq_ofNat m).symm

/-- Search function used to invert the concrete code map. -/
def ratSearch (q : ℚ) (m : ℕ) : Option ℕ :=
  bif (decide (IsRatCode m) &&
      decide (ratCount m = @encode ℚ (@Primcodable.toEncodable ℚ _) q)) then some m else none

/-- The search for the code of a rational is computable. -/
lemma computable₂_ratSearch : Computable₂ ratSearch := by
  have h1 : Computable (fun p : ℚ × ℕ => decide (IsRatCode p.2)) :=
    ((primrecPred_isRatCode.comp Primrec.snd).decide).to_comp
  have h2 : Computable (fun p : ℚ × ℕ =>
      decide (ratCount p.2 = @encode ℚ (@Primcodable.toEncodable ℚ _) p.1)) :=
    ((PrimrecRel.comp Primrec.eq (primrec_ratCount.comp Primrec.snd)
      (Primrec.encode.comp Primrec.fst)).decide).to_comp
  have h3 : Computable (fun p : ℚ × ℕ => (decide (IsRatCode p.2) &&
      decide (ratCount p.2 = @encode ℚ (@Primcodable.toEncodable ℚ _) p.1))) :=
    Computable₂.comp ((Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp) h1 h2
  exact Computable.cond h3 (Computable.option_some.comp Computable.snd) (Computable.const none)

/-- The search succeeds at exactly one natural number, the code of the rational. -/
lemma ratSearch_isSome_iff (q : ℚ) (m : ℕ) :
    (ratSearch q m).isSome = true ↔ m = ratCode q := by
  constructor
  · intro h
    by_cases h1 : IsRatCode m
    · by_cases h2 : ratCount m = @encode ℚ (@Primcodable.toEncodable ℚ _) q
      · have h3 : ratCount m = ratCount (ratCode q) := by rw [h2, encode_eq_ratCount]
        have h4 : ratOfCode m = q := by
          rw [ratOfCode_eq_ofNat, if_pos h1, h3, ofNat_ratCount_ratCode]
        rw [← h4, ratCode_ratOfCode h1]
      · rw [ratSearch] at h; simp [h1, h2] at h
    · rw [ratSearch] at h; simp [h1] at h
  · rintro rfl
    have h1 : IsRatCode (ratCode q) := isRatCode_ratCode q
    have h2 : ratCount (ratCode q) = @encode ℚ (@Primcodable.toEncodable ℚ _) q :=
      (encode_eq_ratCount q).symm
    simp [ratSearch, h1, h2]

/-- At the code of the rational the search returns that code. -/
lemma ratSearch_eq_some (q : ℚ) : ratSearch q (ratCode q) = some (ratCode q) := by
  have h1 : IsRatCode (ratCode q) := isRatCode_ratCode q
  have h2 : ratCount (ratCode q) = @encode ℚ (@Primcodable.toEncodable ℚ _) q :=
    (encode_eq_ratCount q).symm
  simp [ratSearch, h1, h2]

/-- The rational coding is computable. -/
lemma computable_ratCode : Computable ratCode := by
  refine Partrec.of_eq_tot (Partrec.rfindOpt computable₂_ratSearch) fun q => ?_
  rw [Nat.rfindOpt]
  refine Part.mem_bind_iff.mpr ⟨ratCode q, ?_, ?_⟩
  · change ratCode q ∈ Nat.rfind
      (show ℕ →. Bool from fun n => Part.some (ratSearch q n).isSome)
    rw [Nat.mem_rfind]
    constructor
    · simp [(ratSearch_isSome_iff q (ratCode q)).mpr rfl]
    · intro m hm
      have hns : ¬ ((ratSearch q m).isSome = true) := fun hh => by
        have := (ratSearch_isSome_iff q m).mp hh
        omega
      simp only [Bool.not_eq_true] at hns
      simp [hns]
  · simp [ratSearch_eq_some q]

/-! ### Numerator and denominator -/

/-- The numerator of a rational is read off from the first component of its code. -/
lemma num_eq_ofNat_unpair (q : ℚ) : q.num = ofNat ℤ (Nat.unpair (ratCode q)).1 := by
  rw [ratCode, Nat.unpair_pair, Denumerable.ofNat_encode]

/-- The denominator of a rational is the second component of its code. -/
lemma den_eq_unpair (q : ℚ) : q.den = (Nat.unpair (ratCode q)).2 := by
  rw [ratCode, Nat.unpair_pair]

/-- The numerator of a rational is a computable function of it. -/
lemma computable_ratNum : Computable (fun q : ℚ => q.num) :=
  (Primrec.fst.comp ComputableReals.primrec_ratNumDen).to_comp

/-- The denominator of a rational is a computable function of it. -/
lemma computable_ratDen : Computable (fun q : ℚ => q.den) :=
  (Primrec.snd.comp ComputableReals.primrec_ratNumDen).to_comp

/-! ### Building rationals from a numerator and a denominator -/

/-- A rational equals `N / D` exactly when the corresponding cross-multiplication of numerators
and denominators holds. -/
lemma rat_eq_div_iff {r : ℚ} {N : ℤ} {D : ℕ} (hD : 0 < D) :
    r = (N : ℚ) / (D : ℚ) ↔ r.num * (D : ℤ) = N * (r.den : ℤ) := by
  have hDQ : ((D : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hden : ((r.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hnum : (r.num : ℚ) = r * (r.den : ℚ) := (Rat.mul_den_eq_num r).symm
  have key : (r = (N : ℚ) / (D : ℚ)) ↔ ((r.num : ℚ) * (D : ℚ) = (N : ℚ) * (r.den : ℚ)) := by
    rw [eq_div_iff hDQ, hnum]
    constructor
    · intro h; rw [← h]; ring
    · intro h
      have h' : (r * (D : ℚ)) * (r.den : ℚ) = (N : ℚ) * (r.den : ℚ) := by linear_combination h
      exact mul_right_cancel₀ hden h'
  rw [key]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h


section Build

variable {α : Type*} [Primcodable α]

/-- Search function used to build a rational from a numerator and a denominator. -/
def ratBuild (N : α → ℤ) (D : α → ℕ) (a : α) (m : ℕ) : Option ℚ :=
  bif (decide (IsRatCode m) &&
      decide ((ratOfCode m).num * (D a : ℤ) = N a * ((ratOfCode m).den : ℤ)))
    then some (ratOfCode m) else none

/-- Building the rational `N / D` from computable data is computable. -/
lemma computable₂_ratBuild {N : α → ℤ} {D : α → ℕ} (hN : Computable N) (hD : Computable D) :
    Computable₂ (ratBuild N D) := by
  have h1 : Computable (fun p : α × ℕ => decide (IsRatCode p.2)) :=
    ((primrecPred_isRatCode.comp Primrec.snd).decide).to_comp
  have hr : Computable (fun p : α × ℕ => ratOfCode p.2) :=
    computable_ratOfCode.comp Computable.snd
  have hlhs : Computable (fun p : α × ℕ => (ratOfCode p.2).num * (D p.1 : ℤ)) :=
    Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp hr)
      (ComputableReals.primrec_natCastInt.to_comp.comp (hD.comp Computable.fst))
  have hrhs : Computable (fun p : α × ℕ => N p.1 * ((ratOfCode p.2).den : ℤ)) :=
    Computable₂.comp primrec_intMul.to_comp (hN.comp Computable.fst)
      (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp hr))
  have h2 : Computable (fun p : α × ℕ =>
      decide ((ratOfCode p.2).num * (D p.1 : ℤ) = N p.1 * ((ratOfCode p.2).den : ℤ))) :=
    Computable₂.comp (Primrec.eq (α := ℤ)).decide.to_comp hlhs hrhs
  have h3 : Computable (fun p : α × ℕ => (decide (IsRatCode p.2) &&
      decide ((ratOfCode p.2).num * (D p.1 : ℤ) = N p.1 * ((ratOfCode p.2).den : ℤ)))) :=
    Computable₂.comp ((Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp) h1 h2
  exact Computable.cond h3 (Computable.option_some.comp hr) (Computable.const none)

/-- A rational-valued function which can be written as a quotient of a computable
integer-valued numerator by a computable positive denominator is computable. -/
lemma computable_of_num_den {f : α → ℚ} {N : α → ℤ} {D : α → ℕ}
    (hN : Computable N) (hD : Computable D) (hDpos : ∀ a, 0 < D a)
    (hf : ∀ a, f a = (N a : ℚ) / (D a : ℚ)) : Computable f := by
  refine Partrec.of_eq_tot (Partrec.rfindOpt (computable₂_ratBuild hN hD)) fun a => ?_
  have hcross : (f a).num * (D a : ℤ) = N a * ((f a).den : ℤ) :=
    (rat_eq_div_iff (hDpos a)).mp (hf a)
  have hkey : ∀ m, (ratBuild N D a m).isSome = true ↔ m = ratCode (f a) := by
    intro m
    constructor
    · intro h
      by_cases h1 : IsRatCode m
      · by_cases h2 : (ratOfCode m).num * (D a : ℤ) = N a * ((ratOfCode m).den : ℤ)
        · have h3 : ratOfCode m = f a := by
            rw [hf a]
            exact (rat_eq_div_iff (hDpos a)).mpr h2
          rw [← h3, ratCode_ratOfCode h1]
        · rw [ratBuild] at h; simp [h1, h2] at h
      · rw [ratBuild] at h; simp [h1] at h
    · rintro rfl
      simp [ratBuild, isRatCode_ratCode (f a), ratOfCode_ratCode, hcross]
  have hval : ratBuild N D a (ratCode (f a)) = some (f a) := by
    simp [ratBuild, isRatCode_ratCode (f a), ratOfCode_ratCode, hcross]
  rw [Nat.rfindOpt]
  refine Part.mem_bind_iff.mpr ⟨ratCode (f a), ?_, ?_⟩
  · change ratCode (f a) ∈ Nat.rfind
      (show ℕ →. Bool from fun n => Part.some (ratBuild N D a n).isSome)
    rw [Nat.mem_rfind]
    constructor
    · simp [(hkey (ratCode (f a))).mpr rfl]
    · intro m hm
      have hns : ¬ ((ratBuild N D a m).isSome = true) := fun hh => by
        have := (hkey m).mp hh
        omega
      simp only [Bool.not_eq_true] at hns
      simp [hns]
  · simp [hval]

end Build

/-! ### Computability of rational arithmetic -/

/-- Halving a rational is computable. -/
lemma computable_ratHalf : Computable (fun ε : ℚ => ε / 2) := by
  refine computable_of_num_den (N := fun ε : ℚ => ε.num) (D := fun ε : ℚ => 2 * ε.den)
    computable_ratNum
    ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.comp computable_ratDen)
    (fun ε => Nat.mul_pos (by norm_num) ε.pos) (fun ε => ?_)
  have hnum : (ε.num : ℚ) = ε * (ε.den : ℚ) := (Rat.mul_den_eq_num ε).symm
  have hden : ((ε.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr ε.den_nz
  push_cast
  rw [hnum]
  field_simp

/-- Subtraction of rationals is computable. -/
lemma computable₂_ratSub : Computable₂ (fun a b : ℚ => a - b) := by
  have hnum : Computable
      (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ) - p.2.num * (p.1.den : ℤ)) :=
    Computable₂.comp primrec_intSub.to_comp
      (Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp Computable.fst)
        (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp Computable.snd)))
      (Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp Computable.snd)
        (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp Computable.fst)))
  have hden : Computable (fun p : ℚ × ℚ => p.1.den * p.2.den) :=
    Computable₂.comp Primrec.nat_mul.to_comp (computable_ratDen.comp Computable.fst)
      (computable_ratDen.comp Computable.snd)
  refine computable_of_num_den (f := fun p : ℚ × ℚ => p.1 - p.2) hnum hden
    (fun p => Nat.mul_pos p.1.pos p.2.pos) (fun p => ?_)
  have h1 : (p.1.num : ℚ) = p.1 * (p.1.den : ℚ) := (Rat.mul_den_eq_num p.1).symm
  have h2 : (p.2.num : ℚ) = p.2 * (p.2.den : ℚ) := (Rat.mul_den_eq_num p.2).symm
  have hd1 : ((p.1.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.1.den_nz
  have hd2 : ((p.2.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.2.den_nz
  push_cast
  rw [h1, h2]
  field_simp

/-- Addition of rationals is computable. -/
lemma computable₂_ratAdd : Computable₂ (fun a b : ℚ => a + b) := by
  have hnum : Computable
      (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ)) :=
    Computable₂.comp primrec_intAdd.to_comp
      (Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp Computable.fst)
        (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp Computable.snd)))
      (Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp Computable.snd)
        (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp Computable.fst)))
  have hden : Computable (fun p : ℚ × ℚ => p.1.den * p.2.den) :=
    Computable₂.comp Primrec.nat_mul.to_comp (computable_ratDen.comp Computable.fst)
      (computable_ratDen.comp Computable.snd)
  refine computable_of_num_den (f := fun p : ℚ × ℚ => p.1 + p.2) hnum hden
    (fun p => Nat.mul_pos p.1.pos p.2.pos) (fun p => ?_)
  have h1 : (p.1.num : ℚ) = p.1 * (p.1.den : ℚ) := (Rat.mul_den_eq_num p.1).symm
  have h2 : (p.2.num : ℚ) = p.2 * (p.2.den : ℚ) := (Rat.mul_den_eq_num p.2).symm
  have hd1 : ((p.1.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.1.den_nz
  have hd2 : ((p.2.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.2.den_nz
  push_cast
  rw [h1, h2]
  field_simp

/-- Multiplication of rationals is computable. -/
lemma computable₂_ratMul : Computable₂ (fun a b : ℚ => a * b) := by
  have hnum : Computable (fun p : ℚ × ℚ => p.1.num * p.2.num) :=
    Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp Computable.fst)
      (computable_ratNum.comp Computable.snd)
  have hden : Computable (fun p : ℚ × ℚ => p.1.den * p.2.den) :=
    Computable₂.comp Primrec.nat_mul.to_comp (computable_ratDen.comp Computable.fst)
      (computable_ratDen.comp Computable.snd)
  refine computable_of_num_den (f := fun p : ℚ × ℚ => p.1 * p.2) hnum hden
    (fun p => Nat.mul_pos p.1.pos p.2.pos) (fun p => ?_)
  have h1 : (p.1.num : ℚ) = p.1 * (p.1.den : ℚ) := (Rat.mul_den_eq_num p.1).symm
  have h2 : (p.2.num : ℚ) = p.2 * (p.2.den : ℚ) := (Rat.mul_den_eq_num p.2).symm
  have hd1 : ((p.1.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.1.den_nz
  have hd2 : ((p.2.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.2.den_nz
  push_cast
  rw [h1, h2]
  field_simp

/-- Deciding `q ≤ 1` on the rationals is computable. -/
lemma computable_ratLeOne : Computable (fun q : ℚ => decide (q ≤ 1)) := by
  have hkey : ∀ q : ℚ, (q ≤ 1) ↔ (q.num.toNat ≤ q.den) := by
    intro q
    have hd : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.pos
    rw [show (q ≤ 1) ↔ ((q.num : ℚ) / (q.den : ℚ) ≤ 1) by rw [Rat.num_div_den],
      div_le_one hd]
    constructor
    · intro h
      have h' : q.num ≤ (q.den : ℤ) := by exact_mod_cast h
      omega
    · intro h
      have h' : q.num ≤ (q.den : ℤ) := by omega
      exact_mod_cast h'
  have hcomp : Computable (fun q : ℚ => decide (q.num.toNat ≤ q.den)) :=
    Computable₂.comp (Primrec.nat_le.comp Primrec.fst Primrec.snd).decide.to₂.to_comp
      (ComputableReals.primrec_intToNat.to_comp.comp computable_ratNum) computable_ratDen
  exact hcomp.of_eq (fun q => by simp [hkey q])

/-- The numerator of the largest dyadic rational with denominator `2^s` not exceeding `q`. -/
def ratDyadicFloor (q : ℚ) (s : ℕ) : ℕ :=
  if 0 ≤ q then (q * (2 ^ s : ℕ)).num.toNat / (q * (2 ^ s : ℕ)).den else 0
 
/-- The dyadic floor, computed from the numerator and denominator of `q · 2^s`. -/
lemma ratDyadicFloor_eq (q : ℚ) (s : ℕ) : ratDyadicFloor q s = (q * (2 ^ s : ℕ)).num.toNat / (q
  * (2 ^ s : ℕ)).den := by
  unfold ratDyadicFloor
  split_ifs with h
  · rfl
  · have h1 : (q * (2 ^ s : ℕ)).num < 0 := by
      push Not at h
      have hpos : (0 : ℚ) < (2 ^ s : ℕ) := by norm_cast; exact Nat.two_pow_pos s
      have : q * (2 ^ s : ℕ) < 0 := by exact mul_neg_of_neg_of_pos h hpos
      exact Rat.num_neg.mpr this
    have h2 : (q * (2 ^ s : ℕ)).num.toNat = 0 := Int.toNat_of_nonpos (le_of_lt h1)
    rw [h2]
    simp

/-- Exponentiation of natural numbers is primitive recursive in both arguments. -/
lemma nat_pow_primrec₂ : Primrec₂ (fun (a b : ℕ) => a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow

/-- The map `s ↦ 2^s` on the naturals is computable. -/
lemma comp_pow : Computable (fun s : ℕ => (2 ^ s : ℕ)) :=
  (nat_pow_primrec₂.comp (Primrec.const 2) Primrec.id).to_comp

/-- The inclusion of the naturals into the rationals is computable. -/
lemma computable_nat_to_rat : Computable (fun (n : ℕ) => (n : ℚ)) := by
  have h_num : Computable (fun n : ℕ => (n : ℤ)) := ComputableReals.primrec_natCastInt.to_comp
  have h_den : Computable (fun _ : ℕ => (1 : ℕ)) := Computable.const 1
  exact (computable_of_num_den h_num h_den (fun _ => by norm_num) (fun n =>
    by simp)).of_eq fun _ => rfl

/-- The dyadic floor is computable in the rational and the precision. -/
lemma computable_ratDyadicFloor : Computable₂ ratDyadicFloor := by
  have h_pow_rat : Computable (fun s : ℕ => ((2 ^ s : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp comp_pow
  have h_mul : Computable (fun p : ℚ × ℕ => p.1 * ((2 ^ p.2 : ℕ) : ℚ)) :=
    Computable₂.comp computable₂_ratMul Computable.fst (h_pow_rat.comp Computable.snd)
  have h_num : Computable (fun p : ℚ × ℕ => (p.1 * ((2 ^ p.2 : ℕ) : ℚ)).num.toNat) :=
    ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp h_mul)
  have h_den : Computable (fun p : ℚ × ℕ => (p.1 * ((2 ^ p.2 : ℕ) : ℚ)).den) :=
    computable_ratDen.comp h_mul
  have h_div : Computable (fun p : ℚ × ℕ =>
    (p.1 * ((2 ^ p.2 : ℕ) : ℚ)).num.toNat / (p.1 * ((2 ^ p.2 : ℕ) : ℚ)).den) :=
    Computable₂.comp Primrec.nat_div.to_comp h_num h_den
  exact h_div.of_eq fun p => (ratDyadicFloor_eq p.1 p.2).symm

/-- The dyadic floor is the natural-number floor of `q · 2^s`. -/
lemma ratDyadicFloor_eq_floor (q : ℚ) (s : ℕ) :
    ratDyadicFloor q s = ⌊q * (2 ^ s : ℕ)⌋₊ := by
  unfold ratDyadicFloor
  split_ifs with h
  · have hpos : 0 ≤ q * (2 ^ s : ℕ) := mul_nonneg h (by norm_cast; exact Nat.zero_le _)
    have hz : ((q * (2 ^ s : ℕ)).num.toNat / (q * (2 ^ s : ℕ)).den : ℤ) = ⌊q * (2 ^ s : ℕ)⌋ := by
      have h1 : ⌊q * (2 ^ s : ℕ)⌋ = (q * (2 ^ s : ℕ)).num / (q * (2 ^ s : ℕ)).den := Rat.floor_def _
      rw [h1]
      rw [← Int.toNat_of_nonneg (Rat.num_nonneg.mpr hpos)]
      exact_mod_cast rfl
    have h_toNat : ⌊q * (2 ^ s : ℕ)⌋ = (⌊q * (2 ^ s : ℕ)⌋.toNat : ℤ) := by
      have : 0 ≤ ⌊q * (2 ^ s : ℕ)⌋ := Int.floor_nonneg.mpr hpos
      exact (Int.toNat_of_nonneg this).symm
    rw [h_toNat] at hz
    have hf : ⌊q * (2 ^ s : ℕ)⌋.toNat = ⌊q * (2 ^ s : ℕ)⌋₊ := rfl
    rw [← hf]
    exact_mod_cast hz
  · have hneg : q * (2 ^ s : ℕ) < 0 := by
      push Not at h
      exact mul_neg_of_neg_of_pos h (by norm_cast; exact Nat.two_pow_pos s)
    have hz : q * (2 ^ s : ℕ) ≤ 0 := le_of_lt hneg
    exact (Nat.floor_of_nonpos hz).symm

/-- At a fixed precision the dyadic floor is monotone in the rational. -/
lemma ratDyadicFloor_mono {q1 q2 : ℚ} (h : q1 ≤ q2) (s : ℕ) :
    ratDyadicFloor q1 s ≤ ratDyadicFloor q2 s := by
  rw [ratDyadicFloor_eq_floor q1 s, ratDyadicFloor_eq_floor q2 s]
  have : q1 * (2 ^ s : ℕ) ≤ q2 * (2 ^ s : ℕ) := by
    exact mul_le_mul_of_nonneg_right h (by norm_cast; exact Nat.zero_le _)
  exact Nat.floor_mono this

/-- Along a monotone sequence of rationals, the dyadic floors taken at increasing precision have
the same supremum as the sequence itself. -/
lemma iSup_ratDyadicFloor_of_monotone {f : ℕ → ℚ} (hf : Monotone f) :
    (⨆ s, (ratDyadicFloor (f s) s : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s) = ⨆ s, ENNReal.ofReal (f s : ℝ) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    rw [ratDyadicFloor_eq_floor]
    have h1 : (⌊f s * (2 ^ s : ℕ)⌋₊ : ℝ≥0∞) = ENNReal.ofReal (⌊f s * (2 ^ s : ℕ)⌋₊ : ℝ) := by
      exact (ENNReal.ofReal_natCast _).symm
    rw [h1]
    have h2 : ((2 : ℝ≥0∞) ^ s) = ENNReal.ofReal ((2 : ℝ) ^ s) := by
      have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
      rw [this, ← ENNReal.ofReal_pow (by norm_num)]
    rw [h2]
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    refine le_trans ?_ (le_iSup (fun s => ENNReal.ofReal (f s : ℝ)) s)
    by_cases hpos : 0 ≤ f s
    · apply ENNReal.ofReal_le_ofReal
      have h3 : (⌊f s * (2 ^ s : ℕ)⌋₊ : ℚ) ≤ f s * (2 ^ s : ℕ) := Nat.floor_le (by positivity)
      have h4 : (⌊f s * (2 ^ s : ℕ)⌋₊ : ℝ) ≤ (f s : ℝ) * (2 : ℝ) ^ s := by
        have hcast : (((f s * (2 ^ s : ℕ) : ℚ) : ℝ)) = (f s : ℝ) * (2 : ℝ) ^ s := by push_cast; rfl
        rw [← hcast]
        exact_mod_cast h3
      have hp2 : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
      exact (div_le_iff₀ hp2).mpr h4
    · have hz2 : ⌊f s * (2 ^ s : ℕ)⌋₊ = 0 := by
        have : f s * (2 ^ s : ℕ) ≤ 0 := by
          have hneg : f s < 0 := not_le.mp hpos
          have hp : (0 : ℚ) < (2 ^ s : ℕ) := by norm_cast; exact Nat.two_pow_pos s
          exact le_of_lt (mul_neg_of_neg_of_pos hneg hp)
        exact Nat.floor_of_nonpos this
      rw [hz2]
      simp
  · apply iSup_le
    intro s
    by_cases hpos : 0 ≤ f s
    · apply ENNReal.le_of_forall_pos_le_add
      intro ε hε htop
      have : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < (ε : ℝ) := by
        apply exists_pow_lt_of_lt_one (by exact_mod_cast hε) (by norm_num)
      rcases this with ⟨n, hn⟩
      let t := max s n
      have ht1 : s ≤ t := le_max_left s n
      have ht2 : n ≤ t := le_max_right s n
      have h1 : (1 / 2 : ℝ) ^ t ≤ (1 / 2 : ℝ) ^ n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) ht2
      have h2 : (1 / 2 : ℝ) ^ t < (ε : ℝ) := lt_of_le_of_lt h1 hn
      have h_f : (f s : ℝ) ≤ (f t : ℝ) := by
        have : f s ≤ f t := hf ht1
        exact_mod_cast this
      have ht_pos : (0 : ℝ) < 2 ^ t := by positivity
      have h_floor : (f t : ℝ) * 2 ^ t - 1 < (⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ) := by
        have := Nat.sub_one_lt_floor (f t * (2 ^ t : ℕ) : ℚ)
        exact_mod_cast this
      have h_div : (f t : ℝ) - 1 / 2 ^ t < (⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ) / 2 ^ t := by
        have : ((f t : ℝ) * 2 ^ t - 1) / 2 ^ t < (⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ) / 2 ^ t :=
          div_lt_div_of_pos_right h_floor ht_pos
        have h_left : ((f t : ℝ) * 2 ^ t - 1) / 2 ^ t = (f t : ℝ) - 1 / 2 ^ t :=
          by rw [sub_div, mul_div_cancel_right₀ _ (by positivity)]
        rwa [h_left] at this
      have h_div2 : (f s : ℝ) < (⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ) / 2 ^ t + (ε : ℝ) := by
        have h3 : 1 / (2 : ℝ) ^ t = (1 / 2 : ℝ) ^ t := by rw [div_pow, one_pow]
        linarith [h_f, h_div, h2, h3]
      have h_div3 : ENNReal.ofReal (f s : ℝ) ≤ ENNReal.ofReal ((⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ) / 2 ^ t
        + (ε : ℝ)) := ENNReal.ofReal_le_ofReal (le_of_lt h_div2)
      have h_div4 : ENNReal.ofReal ((⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ) / 2 ^ t + (ε : ℝ))
        = ENNReal.ofReal ((⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ) / 2 ^ t) + ENNReal.ofReal (ε : ℝ) := by
        have h_pos1 : 0 ≤ (⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ) / 2 ^ t := by positivity
        have h_pos2 : 0 ≤ (ε : ℝ) := by exact_mod_cast le_of_lt hε
        exact ENNReal.ofReal_add h_pos1 h_pos2
      rw [h_div4] at h_div3
      have h_div5 : ENNReal.ofReal ((⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ) / 2 ^ t)
        = (ratDyadicFloor (f t) t : ℝ≥0∞) / (2 : ℝ≥0∞) ^ t := by
        rw [ratDyadicFloor_eq_floor]
        have h_num : ENNReal.ofReal (⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ) = (⌊f t * (2 ^ t : ℕ)⌋₊ : ℝ≥0∞) :=
          ENNReal.ofReal_natCast _
        have h_den : ENNReal.ofReal (2 ^ t : ℝ) = (2 : ℝ≥0∞) ^ t := by
          have : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
          rw [← this]
          have hpos2 : 0 ≤ (2 : ℝ) := by norm_num
          exact ENNReal.ofReal_pow hpos2 t
        have hy_pos : (0 : ℝ) < 2 ^ t := by positivity
        rw [ENNReal.ofReal_div_of_pos hy_pos, h_num, h_den]
      rw [h_div5] at h_div3
      have h_div6 : (ratDyadicFloor (f t) t : ℝ≥0∞) / (2 : ℝ≥0∞) ^ t ≤ ⨆ s,
        (ratDyadicFloor (f s) s : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s :=
        le_iSup (fun s => (ratDyadicFloor (f s) s : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s) t
      have h_div7 : ENNReal.ofReal ((ε : ℝ)) = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
      rw [h_div7] at h_div3
      exact le_trans h_div3 (add_le_add h_div6 (le_refl _))
    · have : (f s : ℝ) < 0 := by exact_mod_cast not_le.mp hpos
      rw [ENNReal.ofReal_of_nonpos (le_of_lt this)]
      exact bot_le

/-- Increasing the rational and the precision together does not decrease the dyadic value of the
floor. -/
lemma dyadicValue_ratDyadicFloor_mono_of_le {q1 q2 : ℚ} (h : q1 ≤ q2) (s : ℕ) :
    dyadicValue (ratDyadicFloor q1 s) s ≤ dyadicValue (ratDyadicFloor q2 (s + 1)) (s + 1) := by
  have key : 2 * ratDyadicFloor q1 s ≤ ratDyadicFloor q2 (s + 1) := by
    by_cases hq : 0 ≤ q1
    · refine le_trans ?_ (ratDyadicFloor_mono h (s + 1))
      rw [ratDyadicFloor_eq_floor, ratDyadicFloor_eq_floor]
      apply Nat.le_floor
      have hle : ((⌊q1 * (2 ^ s : ℕ)⌋₊ : ℚ)) ≤ q1 * (2 ^ s : ℕ) :=
        Nat.floor_le (by positivity)
      push_cast at hle ⊢
      have hp : (2 : ℚ) ^ (s + 1) = 2 * 2 ^ s := by ring
      rw [hp]
      linarith [hle]
    · have hz : ratDyadicFloor q1 s = 0 := by
        unfold ratDyadicFloor; simp [hq]
      simp [hz]
  have hstep : dyadicValue (ratDyadicFloor q1 s) s
      = dyadicValue (2 * ratDyadicFloor q1 s) (s + 1) := by
    unfold dyadicValue
    rw [pow_succ']
    push_cast
    rw [ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
  rw [hstep]
  unfold dyadicValue
  gcongr

/-- A stagewise nondecreasing rational sequence has nondecreasing dyadic-floor
approximations. -/
lemma dyadicValue_ratDyadicFloor_monotone {f : ℕ → ℚ} (hf : ∀ s, f s ≤ f (s + 1)) :
    Monotone (fun s => dyadicValue (ratDyadicFloor (f s) s) s) :=
  monotone_nat_of_le_succ fun s => dyadicValue_ratDyadicFloor_mono_of_le (hf s) s

/-- The dyadic values of the floors of a monotone rational sequence have the same supremum as the
sequence. -/
lemma iSup_dyadicValue_ratDyadicFloor {f : ℕ → ℚ} (hf : Monotone f) :
    (⨆ s, dyadicValue (ratDyadicFloor (f s) s) s) = ⨆ s, ENNReal.ofReal (f s : ℝ) := by
  have : (⨆ s, dyadicValue (ratDyadicFloor (f s) s) s) = ⨆ s,
    (ratDyadicFloor (f s) s : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s := rfl
  rw [this]
  exact iSup_ratDyadicFloor_of_monotone hf

end Kolmogorov
