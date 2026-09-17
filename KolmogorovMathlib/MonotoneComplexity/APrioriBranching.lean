import KolmogorovMathlib.MonotoneComplexity.APrioriMinimality
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Branching below the a priori probability

Descending a binary tree along light children. At every node of a continuous tree semimeasure
one of the two children carries at most half of the node's mass
(`exists_bool_child_mass_le_half`), so iterating the choice produces the *halving descent*
`hardKAPrefix x n`: an extension of `x` by `n` bits whose universal a priori mass has dropped by
a factor `2 ^ (-n)` (`exists_extension_mass_le_invTwoPow`). Taking logarithms turns this into the
growth statements for a priori complexity: `KA_child_ge_add_one`, `exists_extension_KA_ge`, and
the infinite form `exists_cantorSeq_KA_prefix_ge`, whose stated version
`exists_cantorSeq_KA_prefix_ge_length` gives an infinite sequence all of whose prefixes have a
priori complexity at least their length.

Source: SUV, Problem 128.
-/

open ENNReal
namespace Kolmogorov

/-- Every node of a continuous tree semimeasure has a child carrying at most half of its mass. -/
lemma exists_bool_child_mass_le_half {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (x : BitString) :
    ∃ b : Bool, a (x ++ [b]) ≤ a x / 2 := by
  by_contra! h
  have h1 := h false
  have h2 := h true
  have h_sum : a x / 2 + a x / 2 < a (x ++ [false]) + a (x ++ [true]) := ENNReal.add_lt_add h1 h2
  have h_half : a x / 2 + a x / 2 = a x := ENNReal.add_halves (a x)
  rw [h_half] at h_sum
  have h3 := ha.2 x
  exact lt_irrefl _ (lt_of_lt_of_le h_sum h3)

/-- The extension of `x` by `n` bits obtained by repeatedly stepping into a child of at most half
the
universal a priori mass. -/
noncomputable def hardKAPrefix (x : BitString) : ℕ → BitString
  | 0 => x
  | n + 1 =>
    let curr := hardKAPrefix x n
    curr ++ [Classical.choose (exists_bool_child_mass_le_half
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1 curr)]

/-- One step of the halving descent appends the chosen light child. -/
lemma hardKAPrefix_succ (x : BitString) (n : ℕ) :
    hardKAPrefix x (n + 1) = hardKAPrefix x n ++
      [Classical.choose (exists_bool_child_mass_le_half
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
      (hardKAPrefix x n))] := rfl

/-- After `n` steps the halving descent has appended exactly `n` bits to `x`. -/
lemma hardKAPrefix_length (x : BitString) (n : ℕ) :
    (hardKAPrefix x n).length = x.length + n := by
  induction n with
  | zero => simp [hardKAPrefix]
  | succ n ih =>
    simp [hardKAPrefix_succ, ih]
    omega

/-- Earlier stages of the halving descent are prefixes of later ones. -/
lemma hardKAPrefix_prefix (x : BitString) (n m : ℕ) (h : n ≤ m) :
    hardKAPrefix x n <+: hardKAPrefix x m := by
  induction m generalizing n with
  | zero =>
    have : n = 0 := by omega
    simp [this]
  | succ m ih =>
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact List.prefix_refl _
    · have := ih n (by omega)
      rw [hardKAPrefix_succ]
      exact List.IsPrefix.trans this (List.prefix_append _ _)

/-- The stages of the halving descent agree bit by bit wherever both are defined. -/
lemma hardKAPrefix_getElem (x : BitString) (n m : ℕ) (h_le : n ≤ m) (i : ℕ)
    (h1 : i < (hardKAPrefix x n).length) (h2 : i < (hardKAPrefix x m).length) :
    (hardKAPrefix x n)[i]'h1 = (hardKAPrefix x m)[i]'h2 := by
  have ⟨l, hl⟩ := hardKAPrefix_prefix x n m h_le
  revert h2
  rw [← hl]
  intro h2
  rw [List.getElem_append]
  rw [dif_pos h1]

/-- The infinite sequence whose prefixes are the stages of the halving descent started at `x`. -/
noncomputable def hardKASeq (x : BitString) : CantorSeq :=
  fun i => (hardKAPrefix x (i + 1))[i]'(by
    have := hardKAPrefix_length x (i + 1)
    omega)

/-- The prefix of `hardKASeq x` of length `|x| + n` is the `n`-th stage of the halving descent. -/
lemma cantorPrefix_hardKASeq (x : BitString) (n : ℕ) :
    cantorPrefix (hardKASeq x) (x.length + n) = hardKAPrefix x n := by
  apply List.ext_getElem
  · simp [cantorPrefix, hardKAPrefix_length]
  · intro i h1 h2
    simp only [cantorPrefix_getElem]
    have h_len : i < (hardKAPrefix x (i + 1)).length := by
      have := hardKAPrefix_length x (i + 1)
      omega
    have h_eq : (hardKAPrefix x (i + 1))[i]'h_len = (hardKAPrefix x (max (i + 1) n))[i]'(by
        have := hardKAPrefix_length x (max (i + 1) n)
        omega) := by
      apply hardKAPrefix_getElem _ _ _ (le_max_left _ _)
    have h_eq2 : (hardKAPrefix x n)[i]'h2 = (hardKAPrefix x (max (i + 1) n))[i]'(by
        have := hardKAPrefix_length x (max (i + 1) n)
        omega) := by
      apply hardKAPrefix_getElem _ _ _ (le_max_right _ _)
    exact h_eq.trans h_eq2.symm

/-- A string whose universal a priori mass is at most `2 ^ (-n)` times that of `x` has a priori
complexity at least `KA x + n`. -/
lemma KA_add_nat_le_of_universal_mass_le (x z : BitString) (n : ℕ)
    (h : universalContinuousSemimeasure z ≤ universalContinuousSemimeasure x / 2 ^ n) :
    KA x + (n : ℝ) ≤ KA z := by
  have h_ne_top := universalContinuousSemimeasure_ne_top z
  have h_pos := universalContinuousSemimeasure_pos z
  have h_x_pos := universalContinuousSemimeasure_pos x
  have h_x_ne_top := universalContinuousSemimeasure_ne_top x
  have h_x_pos_real : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos h_x_pos.ne' h_x_ne_top
  have h_y_pos_real : 0 < (universalContinuousSemimeasure z).toReal :=
    ENNReal.toReal_pos h_pos.ne' h_ne_top
  unfold KA
  have h_le_real : (universalContinuousSemimeasure z).toReal ≤
      (universalContinuousSemimeasure x).toReal / 2 ^ n := by
    have h1 : (universalContinuousSemimeasure x / 2 ^ n).toReal =
        (universalContinuousSemimeasure x).toReal / 2 ^ n := by
      change (universalContinuousSemimeasure x * (2 ^ n)⁻¹).toReal =
        (universalContinuousSemimeasure x).toReal / 2 ^ n
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
      change _ * ((2 : ℝ)^n)⁻¹ = _
      rw [div_eq_mul_inv]
    rw [← h1]
    have hp_ne_top : universalContinuousSemimeasure x / 2 ^ n ≠ ⊤ := by
      change universalContinuousSemimeasure x * (2^n)⁻¹ ≠ ⊤
      apply ENNReal.mul_ne_top h_x_ne_top (by simp)
    exact ENNReal.toReal_mono hp_ne_top h
  have hd : 0 < (universalContinuousSemimeasure x).toReal / 2^n := by positivity
  have h_log := (Real.logb_le_logb (b:=2) (by norm_num) h_y_pos_real hd).mpr h_le_real
  have h_div : Real.logb 2 ((universalContinuousSemimeasure x).toReal / 2 ^ n) =
      Real.logb 2 (universalContinuousSemimeasure x).toReal - Real.logb 2 (2 ^ n) := by
    unfold Real.logb
    rw [Real.log_div h_x_pos_real.ne' (by positivity)]
    ring
  rw [h_div] at h_log
  have hr : Real.logb 2 (2 ^ n) = n := by
    unfold Real.logb
    rw [Real.log_pow]
    have hz : Real.log 2 ≠ 0 := by positivity
    exact mul_div_cancel_right₀ _ hz
  rw [hr] at h_log
  linarith

/-- After `n` halving steps the universal a priori mass has dropped by a factor of at least `2 ^ n`.
-/
lemma hardKAPrefix_mass_le (x : BitString) (n : ℕ) :
    universalContinuousSemimeasure (hardKAPrefix x n) ≤ universalContinuousSemimeasure x / 2^n := by
  induction n with
  | zero =>
    simp [hardKAPrefix]
  | succ n ih =>
    rw [hardKAPrefix_succ]
    have hb := Classical.choose_spec (exists_bool_child_mass_le_half
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
      (hardKAPrefix x n))
    have h1 : universalContinuousSemimeasure (hardKAPrefix x n) / 2 ≤
        (universalContinuousSemimeasure x / 2^n) / 2 := by
      gcongr
    have h2 : (universalContinuousSemimeasure x / 2^n) / 2 =
        universalContinuousSemimeasure x / 2^(n + 1) := by
      change universalContinuousSemimeasure x * (2^n)⁻¹ * 2⁻¹ =
        universalContinuousSemimeasure x * (2^(n + 1))⁻¹
      have hp1 : (2 : ℝ≥0∞) ^ n ≠ 0 := by simp
      have hp2 : (2 : ℝ≥0∞) ≠ 0 := by simp
      rw [mul_assoc, ← ENNReal.mul_inv (Or.inl hp1) (Or.inr hp2)]
      have : (2 : ℝ≥0∞) ^ n * 2 = 2 ^ (n + 1) := (pow_succ _ _).symm
      rw [this]
    rw [← h2]
    exact le_trans hb h1

/-- Every string has an extension by `n` bits whose universal a priori mass is at most `2 ^ (-n)`
times its own. -/
lemma exists_extension_mass_le_invTwoPow (x : BitString) (n : ℕ) :
    ∃ y : BitString, x <+: y ∧ y.length = x.length + n ∧
      universalContinuousSemimeasure y ≤ universalContinuousSemimeasure x / 2^n := by
  use hardKAPrefix x n
  refine ⟨hardKAPrefix_prefix x 0 n (by omega), ?_, hardKAPrefix_mass_le x n⟩
  exact hardKAPrefix_length x n

/-- Every string has a child whose a priori complexity exceeds its own by at least one bit. -/
lemma KA_child_ge_add_one (x : BitString) :
    ∃ b : Bool, KA x + 1 ≤ KA (x ++ [b]) := by
  have ⟨b, hb⟩ := exists_bool_child_mass_le_half
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1 x
  use b
  have := KA_add_nat_le_of_universal_mass_le x (x ++ [b]) 1 (by
    have h : (2 : ℝ≥0∞) ^ 1 = 2 := by norm_num
    rw [h]
    exact hb)
  push_cast at this
  exact this

/-- Every string has an extension by `n` bits whose a priori complexity is at least `KA x + n`. -/
lemma exists_extension_KA_ge (x : BitString) (n : ℕ) :
    ∃ y : BitString, x <+: y ∧ y.length = x.length + n ∧ KA x + (n : ℝ) ≤ KA y := by
  use hardKAPrefix x n
  refine ⟨hardKAPrefix_prefix x 0 n (by omega), hardKAPrefix_length x n, ?_⟩
  exact KA_add_nat_le_of_universal_mass_le x (hardKAPrefix x n) n (hardKAPrefix_mass_le x n)

/-- Every string extends to an infinite sequence along which the a priori complexity of the prefixes
grows at least one bit per position. -/
lemma exists_cantorSeq_KA_prefix_ge (x : BitString) :
    ∃ w : CantorSeq, cantorPrefix w x.length = x ∧
      ∀ n : ℕ, KA x + (n : ℝ) ≤ KA (cantorPrefix w (x.length + n)) := by
  use hardKASeq x
  constructor
  · have := cantorPrefix_hardKASeq x 0
    simp only [hardKAPrefix] at this
    exact this
  · intro n
    rw [cantorPrefix_hardKASeq x n]
    have h_mass := hardKAPrefix_mass_le x n
    exact KA_add_nat_le_of_universal_mass_le x (hardKAPrefix x n) n h_mass

/-- `KA` of the empty string is `0`, because `a([]) = 1` for a continuous tree
semimeasure and `KA` is `-log₂ a` without rounding. -/
lemma KA_nil : KA [] = 0 := by
  unfold KA
  rw [universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.1]
  simp

/-- Problem 128, third part (literal form): there is an infinite binary sequence
`w` such that `KA(x) ≥ l(x)` for every prefix `x` of `w`. Here every prefix of
`w` is `cantorPrefix w n` for some `n`, and its length is `n`, so the bound reads
`(n : ℝ) ≤ KA (cantorPrefix w n)`. This is the `x = []` instance of
`exists_cantorSeq_KA_prefix_ge` together with `KA_nil`. -/
lemma exists_cantorSeq_KA_prefix_ge_length :
    ∃ w : CantorSeq, ∀ n : ℕ, (n : ℝ) ≤ KA (cantorPrefix w n) := by
  obtain ⟨w, -, hw⟩ := exists_cantorSeq_KA_prefix_ge []
  refine ⟨w, fun n => ?_⟩
  have h := hw n
  rw [KA_nil] at h
  simpa using h

end Kolmogorov
