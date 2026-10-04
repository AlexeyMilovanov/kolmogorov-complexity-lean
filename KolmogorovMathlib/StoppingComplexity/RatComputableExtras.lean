/-
Copyright (c) 2026 Maintainers of KolmogorovMathlib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maintainers
-/
import KolmogorovMathlib.Interface.ComputableReals.Part01

/-!
# Primitive recursive floor and ceiling of rationals

The natural-number floor `⌊q⌋₊` and ceiling `⌈q⌉₊` of a rational number are primitive recursive.
The floor is the quotient `q.num.toNat / q.den` of the numerator by the denominator
(`natFloor_rat_eq_num_toNat_div_den`), and the ceiling is the floor plus one exactly when `q`
exceeds its floor (`natCeil_rat_eq_ite`), a comparison of integers `q.num ≤ ⌊q⌋₊ · q.den`
(`rat_le_natCast_iff`). The library's rational arithmetic (`RatComputable`,
`ComputableReals`) has no floor or ceiling of a general rational; LEM-EFF-02 needs both, since
the marker bound `M_j` and the coarse count `N` of a round of the stopping-allocation game are a
floor and a ceiling of rationals.

Blueprint 02 LEM-EFF-02 (uniform computability of the strategy).
-/

namespace Kolmogorov

/-- The natural-number floor of a rational is the quotient of its numerator by its denominator,
`⌊q⌋₊ = q.num.toNat / q.den` (both sides vanish when `q` is negative). -/
theorem natFloor_rat_eq_num_toNat_div_den (q : ℚ) : ⌊q⌋₊ = q.num.toNat / q.den := by
  rcases le_or_gt 0 q with hq | hq
  · have hnum : ((q.num.toNat : ℤ) : ℚ) = (q.num : ℚ) := by
      rw [Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)]
    have hq' : (q.num.toNat : ℚ) / (q.den : ℚ) = q := by
      rw [Int.cast_natCast] at hnum
      rw [hnum, Rat.num_div_den]
    conv_lhs => rw [← hq']
    exact Rat.natFloor_natCast_div_natCast _ _
  · rw [Nat.floor_of_nonpos hq.le, Int.toNat_of_nonpos (Rat.num_neg.2 hq).le, Nat.zero_div]

/-- A rational is at most a natural number `n` exactly when its numerator is at most
`n · q.den`, a comparison of integers. -/
theorem rat_le_natCast_iff (q : ℚ) (n : ℕ) : q ≤ n ↔ q.num ≤ (n : ℤ) * q.den := by
  rw [ComputableReals.ratLe_iff]
  simp

/-- The natural-number ceiling of a rational is its floor, plus one exactly when the rational
exceeds its floor. -/
theorem natCeil_rat_eq_ite (q : ℚ) : ⌈q⌉₊ = if q ≤ ⌊q⌋₊ then ⌊q⌋₊ else ⌊q⌋₊ + 1 := by
  split_ifs with h
  · exact le_antisymm (Nat.ceil_le.2 h) (Nat.floor_le_ceil q)
  · exact le_antisymm (Nat.ceil_le_floor_add_one q) (Nat.lt_ceil.2 (not_le.1 h))

/-- The natural-number floor `q ↦ ⌊q⌋₊` of a rational is primitive recursive. -/
theorem primrec_rat_natFloor : Primrec fun q : ℚ => ⌊q⌋₊ :=
  (Primrec.nat_div.comp (ComputableReals.primrec_intToNat.comp ComputableReals.primrec_ratNum)
    ComputableReals.primrec_ratDen).of_eq fun q => (natFloor_rat_eq_num_toNat_div_den q).symm

/-- The natural-number ceiling `q ↦ ⌈q⌉₊` of a rational is primitive recursive. -/
theorem primrec_rat_natCeil : Primrec fun q : ℚ => ⌈q⌉₊ := by
  have hle : PrimrecPred fun q : ℚ => q.num ≤ (⌊q⌋₊ : ℤ) * q.den :=
    ComputableReals.primrec_intLe.comp ComputableReals.primrec_ratNum
      (ComputableReals.primrec_intMul.comp
        (ComputableReals.primrec_natCastInt.comp primrec_rat_natFloor)
        (ComputableReals.primrec_natCastInt.comp ComputableReals.primrec_ratDen))
  refine (Primrec.ite hle primrec_rat_natFloor (Primrec.succ.comp primrec_rat_natFloor)).of_eq
    fun q => ?_
  rw [natCeil_rat_eq_ite q]
  simp only [rat_le_natCast_iff, Nat.succ_eq_add_one]

end Kolmogorov
