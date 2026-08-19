import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rel
import KolmogorovMathlib.CommonInformation.RectangleCover
import KolmogorovMathlib.CommonInformation.NoFourCycleDensity
import KolmogorovMathlib.CommonInformation.WorstCaseCounting

namespace Kolmogorov

variable {α β : Type*}

private lemma muchnikThreshold_cover_exponent_sum_lt
    (n : Nat) (hn : 14 ≤ n) :
    2 ^ (muchnikThreshold n + muchnikThreshold n + 1) +
      2 ^ (muchnikThreshold n + muchnikThreshold n +
        (muchnikThreshold n + 1) / 2 + 1) <
      2 ^ (3 * n) := by
  let t := muchnikThreshold n
  have he1 : t + t + 1 ≤ 3 * n - 2 := by
    by_cases hn19 : 19 ≤ n
    · have ht10 : 10 * t ≤ 11 * n + 9 := by
        dsimp [t, muchnikThreshold]
        omega
      omega
    · dsimp [t]
      interval_cases n <;> norm_num [muchnikThreshold] at *
  have he2 : t + t + (t + 1) / 2 + 1 ≤ 3 * n - 1 := by
    by_cases hn19 : 19 ≤ n
    · have ht10 : 10 * t ≤ 11 * n + 9 := by
        dsimp [t, muchnikThreshold]
        omega
      have hh : 2 * ((t + 1) / 2) ≤ t + 1 := by omega
      omega
    · dsimp [t]
      interval_cases n <;> norm_num [muchnikThreshold] at *
  have hm : 2 ≤ 3 * n := by omega
  have hp1 : 2 ^ (t + t + 1) ≤ 2 ^ (3 * n - 2) :=
    Nat.pow_le_pow_right (by omega) he1
  have hp2 : 2 ^ (t + t + (t + 1) / 2 + 1) ≤ 2 ^ (3 * n - 1) :=
    Nat.pow_le_pow_right (by omega) he2
  calc
    2 ^ (muchnikThreshold n + muchnikThreshold n + 1) +
          2 ^ (muchnikThreshold n + muchnikThreshold n +
            (muchnikThreshold n + 1) / 2 + 1)
        ≤ 2 ^ (3 * n - 2) + 2 ^ (3 * n - 1) := by
          simpa [t] using Nat.add_le_add hp1 hp2
    _ = 3 * 2 ^ (3 * n - 2) := by
      have heq : 3 * n - 1 = (3 * n - 2) + 1 := by omega
      rw [heq, pow_succ]
      ring
    _ < 4 * 2 ^ (3 * n - 2) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ = 2 ^ (3 * n) := by
      have heq : 3 * n = (3 * n - 2) + 2 := by omega
      rw [heq, pow_add]
      norm_num
      ring

open Classical in
lemma muchnikThreshold_rectangleFamilyEdges_card_lt
    (n : Nat) (r : α → β → Prop) {𝓡 : Finset (CombinatorialRectangle α β)} :
  14 ≤ n →
  NoFourCycle r →
  𝓡.card ≤ 2 ^ muchnikThreshold n →
  (∀ R ∈ 𝓡,
    R.1.card ≤ 2 ^ muchnikThreshold n ∧
    R.2.card ≤ 2 ^ muchnikThreshold n) →
  (rectangleFamilyEdges r 𝓡).card < 2 ^ (3 * n) := by
  intro hn hfour hcard hrect
  have hbound := noFourCycle_rectangleFamilyEdges_card_le_pow
    r hfour hcard hrect
  exact hbound.trans_lt (muchnikThreshold_cover_exponent_sum_lt n hn)

lemma incidence_weighted_bound_of_left_order
    {n α β γ : Nat}
    (_hβγ : β ≤ γ)
    (hS : 3 * n ≤ α + γ / 2 + max (γ / 2) β)
    (hx : 2 * n ≤ α + β)
    (hy : 2 * n ≤ α + γ)
    (_hxy : 3 * n ≤ α + β + γ) :
    8 * n ≤ 3 * α + 2 * β + 2 * γ := by
  by_cases hβhalf : β ≤ γ / 2
  · rw [max_eq_left hβhalf] at hS
    omega
  · rw [max_eq_right (by omega)] at hS
    omega

lemma incidence_weighted_bound_of_right_order
    {n α β γ : Nat}
    (_hγβ : γ ≤ β)
    (hS : 3 * n ≤ α + β / 2 + max (β / 2) γ)
    (hx : 2 * n ≤ α + β)
    (hy : 2 * n ≤ α + γ)
    (_hxy : 3 * n ≤ α + β + γ) :
    8 * n ≤ 3 * α + 2 * β + 2 * γ := by
  by_cases hγhalf : γ ≤ β / 2
  · rw [max_eq_left hγhalf] at hS
    omega
  · rw [max_eq_right (by omega)] at hS
    omega

lemma incidence_weighted_bound
    {n α β γ : Nat}
    (hLeft : β ≤ γ →
      3 * n ≤ α + γ / 2 + max (γ / 2) β)
    (hRight : γ ≤ β →
      3 * n ≤ α + β / 2 + max (β / 2) γ)
    (hx : 2 * n ≤ α + β)
    (hy : 2 * n ≤ α + γ)
    (hxy : 3 * n ≤ α + β + γ) :
    8 * n ≤ 3 * α + 2 * β + 2 * γ := by
  rcases le_total β γ with hβγ | hγβ
  · exact incidence_weighted_bound_of_left_order hβγ (hLeft hβγ) hx hy hxy
  · exact incidence_weighted_bound_of_right_order hγβ (hRight hγβ) hx hy hxy

lemma theorem_227_arithmetic
    (n kz kxz kyz d kx kzx e ky kzy : Nat)
    (hEnvelope :
      8 * n ≤
        3 * (kz + 1 + d) +
        2 * (kxz + 1 + d) +
        2 * (kyz + 1 + d))
    (hBalX : kz + kxz ≤ kx + kzx + e)
    (hBalY : kz + kyz ≤ ky + kzy + e)
    (hKx : kx ≤ 2 * n + d)
    (hKy : ky ≤ 2 * n + d) :
    kz ≤ 2 * kzx + 2 * kzy + 4 * e + 11 * d + 7 := by
  omega

end Kolmogorov
