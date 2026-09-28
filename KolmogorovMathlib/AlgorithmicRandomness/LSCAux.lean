import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.Prefix.TwoStage
import Mathlib.Data.List.GetD

/-!
# Auxiliary tools for the characterizations of lower semicomputable functions

This file collects the elementary computability and dyadic-arithmetic tools used
in `LSCCharacterizations.lean` to prove the equivalence of the several standard
descriptions of a lower semicomputable function on Cantor space.

* bounded search operators `lscBMax`, `lscBExists` (primitive recursion over a
  computable family), together with their computability;
* computability of dyadic rationals, of `List.take` and of the prefix test on
  bit strings;
* the dictionary between `dyadicValue` and rational comparisons.
-/

namespace Kolmogorov

open Encodable Denumerable

/-! ### Elementary computability helpers -/

/-- The minimum of two naturals is primitive recursive. -/
lemma lscPrimrec_natMin : Primrec₂ (fun a b : ℕ => min a b) :=
  primrec₂_min_of_le Primrec.nat_le

/-- The maximum of two naturals is primitive recursive. -/
lemma lscPrimrec_natMax : Primrec₂ (fun a b : ℕ => max a b) :=
  primrec₂_max_of_le Primrec.nat_le

/-- Boolean prefix test on bit strings. -/
def lscIsPrefixB (y x : BitString) : Bool := decide (x.take y.length = y)

/-- The boolean prefix test is correct: it returns `true` exactly when `y` is a prefix of `x`. -/
lemma lscIsPrefixB_iff (y x : BitString) : lscIsPrefixB y x = true ↔ y <+: x := by
  rw [lscIsPrefixB, decide_eq_true_iff, List.prefix_iff_eq_take]
  exact eq_comm

/-- The boolean prefix test is primitive recursive in both arguments. -/
lemma lscPrimrec₂_isPrefixB : Primrec₂ lscIsPrefixB := by
  have h : Primrec (fun p : BitString × BitString => decide (p.2.take p.1.length = p.1)) :=
    Primrec₂.comp (f := fun (a b : BitString) => decide (a = b))
      (Primrec.eq (α := BitString)).decide
      (Primrec₂.comp (f := fun (l : BitString) (n : ℕ) => l.take n) primrec_list_take
        Primrec.snd (Primrec.list_length.comp Primrec.fst))
      Primrec.fst
  exact h

/-- The dyadic rational `n / 2 ^ s` is a computable function of `(n, s)`. -/
lemma lscComputable_dyadicRat : Computable (fun p : ℕ × ℕ => (p.1 : ℚ) / 2 ^ p.2) := by
  have hpow : Primrec (fun p : ℕ × ℕ => 2 ^ p.2) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.snd
  refine computable_of_num_den (N := fun p : ℕ × ℕ => (p.1 : ℤ)) (D := fun p : ℕ × ℕ => 2 ^ p.2)
    (ComputableReals.primrec_natCastInt.to_comp.comp Computable.fst) hpow.to_comp
    (fun _ => by positivity) (fun _ => by push_cast; ring)

/-! ### Bounded search -/

/-- Bounded maximum `max_{k < n} F k`, with value `0` when `n = 0`. -/
def lscBMax (F : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec 0 (fun y IH => max IH (F y)) n

/-- The bounded maximum over the empty range is zero. -/
@[simp] lemma lscBMax_zero (F : ℕ → ℕ) : lscBMax F 0 = 0 := rfl

/-- The bounded maximum over `n + 1` values extends the one over `n` values by `F n`. -/
@[simp] lemma lscBMax_succ (F : ℕ → ℕ) (n : ℕ) :
    lscBMax F (n + 1) = max (lscBMax F n) (F n) := rfl

/-- Each value below the bound is dominated by the bounded maximum. -/
lemma lscLe_bMax (F : ℕ → ℕ) {k n : ℕ} (h : k < n) : F k ≤ lscBMax F n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · exact le_trans (ih h') (le_max_left _ _)
    · exact le_max_right _ _

/-- The bounded maximum is either zero or attained at some index below the bound. -/
lemma lscBMax_spec (F : ℕ → ℕ) (n : ℕ) :
    lscBMax F n = 0 ∨ ∃ k < n, F k = lscBMax F n := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [lscBMax_succ]
    rcases le_total (F n) (lscBMax F n) with h | h
    · rw [max_eq_left h]
      rcases ih with h0 | ⟨k, hk, hkv⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k, by omega, hkv⟩
    · rw [max_eq_right h]
      exact Or.inr ⟨n, by omega, rfl⟩

/-- The bounded maximum of a computable family is computable. -/
lemma lscComputable_bMax {α : Type*} [Primcodable α] {F : α → ℕ → ℕ} {N : α → ℕ}
    (hF : Computable₂ F) (hN : Computable N) : Computable (fun a => lscBMax (F a) (N a)) := by
  have hstep : Computable₂ (fun (a : α) (p : ℕ × ℕ) => max p.2 (F a p.1)) :=
    Computable₂.comp (f := fun a b : ℕ => max a b) lscPrimrec_natMax.to_comp
      (Computable.snd.comp Computable.snd)
      (Computable₂.comp hF Computable.fst (Computable.fst.comp Computable.snd))
  exact Computable.nat_rec hN (Computable.const 0) hstep

/-- Bounded existential `∃ k < n, G k`. -/
def lscBExists (G : ℕ → Bool) (n : ℕ) : Bool := Nat.rec false (fun y IH => IH || G y) n

/-- The bounded existential test succeeds exactly when some index below the bound passes. -/
lemma lscBExists_iff (G : ℕ → Bool) (n : ℕ) :
    lscBExists G n = true ↔ ∃ k < n, G k = true := by
  induction n with
  | zero => simp [lscBExists]
  | succ n ih =>
    have hstep : lscBExists G (n + 1) = (lscBExists G n || G n) := rfl
    rw [hstep, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, hkv⟩ | h)
      · exact ⟨k, by omega, hkv⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨k, hk, hkv⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h' | rfl
      · exact Or.inl ⟨k, h', hkv⟩
      · exact Or.inr hkv

/-- The bounded existential test over a computable predicate is computable. -/
lemma lscComputable_bExists {α : Type*} [Primcodable α] {G : α → ℕ → Bool} {N : α → ℕ}
    (hG : Computable₂ G) (hN : Computable N) : Computable (fun a => lscBExists (G a) (N a)) := by
  have hstep : Computable₂ (fun (a : α) (p : ℕ × Bool) => (p.2 || G a p.1)) :=
    Computable₂.comp (f := fun a b : Bool => a || b)
      (Primrec.dom_bool₂ (fun a b : Bool => a || b)).to_comp
      (Computable.snd.comp Computable.snd)
      (Computable₂.comp hG Computable.fst (Computable.fst.comp Computable.snd))
  exact Computable.nat_rec hN (Computable.const false) hstep

/-! ### Dyadic values -/

/-- The dyadic value `dyadicValue n s` is the extended-real image of the rational `n / 2^s`. -/
lemma lscDyadicValue_eq_ofReal (n s : ℕ) :
    dyadicValue n s = ENNReal.ofReal ((((n : ℚ) / 2 ^ s : ℚ)) : ℝ) := by
  have hcast : ((((n : ℚ) / 2 ^ s : ℚ)) : ℝ) = (n : ℝ) / 2 ^ s := by push_cast; ring
  rw [hcast, dyadicValue, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- Dyadic rationals of the form `n / 2^s` with `n` a natural number are nonnegative. -/
lemma lscDyadicRat_nonneg (n s : ℕ) : (0 : ℝ) ≤ (((n : ℚ) / 2 ^ s : ℚ) : ℝ) := by
  have : (0 : ℚ) ≤ (n : ℚ) / 2 ^ s := by positivity
  exact_mod_cast this

/-- A nonnegative rational is below a dyadic value exactly when it is below the corresponding
dyadic rational. -/
lemma lscOfReal_lt_dyadicValue_iff {q : ℚ} (hq : 0 ≤ q) (n s : ℕ) :
    ENNReal.ofReal (q : ℝ) < dyadicValue n s ↔ q < (n : ℚ) / 2 ^ s := by
  rw [lscDyadicValue_eq_ofReal,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by exact_mod_cast hq)]
  exact_mod_cast Iff.rfl

/-- At a common denominator, dyadic values compare exactly as their numerators do. -/
lemma lscDyadicValue_le_iff (n m s : ℕ) : dyadicValue n s ≤ dyadicValue m s ↔ n ≤ m := by
  have hp : (0 : ℚ) < 2 ^ s := by positivity
  rw [lscDyadicValue_eq_ofReal, lscDyadicValue_eq_ofReal,
    ENNReal.ofReal_le_ofReal_iff (lscDyadicRat_nonneg m s)]
  constructor
  · intro h
    have h' : (n : ℚ) / 2 ^ s ≤ (m : ℚ) / 2 ^ s := by exact_mod_cast h
    have h2 : (n : ℚ) ≤ (m : ℚ) := by
      calc (n : ℚ) = ((n : ℚ) / 2 ^ s) * 2 ^ s := by field_simp
        _ ≤ ((m : ℚ) / 2 ^ s) * 2 ^ s := by gcongr
        _ = (m : ℚ) := by field_simp
    exact_mod_cast h2
  · intro h
    have h' : (n : ℚ) / 2 ^ s ≤ (m : ℚ) / 2 ^ s := by gcongr
    exact_mod_cast h'

/-- At a fixed denominator, dyadic values are monotone in the numerator. -/
lemma lscDyadicValue_mono {n m : ℕ} (s : ℕ) (h : n ≤ m) : dyadicValue n s ≤ dyadicValue m s :=
  (lscDyadicValue_le_iff n m s).2 h

end Kolmogorov
