import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionShift

namespace Kolmogorov

open scoped ENNReal

/-- Two log-slacks at the same visible budget combine by adding their constants. -/
theorem logSlack_add_const (c c' n : Nat) :
    logSlack c n + logSlack c' n = logSlack (c + c') n := by
  unfold logSlack; ring

/-
A linear reparametrisation of the visible budget can be absorbed into the
slack constant: for fixed `a, b`, the slack `logSlack c (a*M+b)` is dominated by
a single `logSlack C M` with a larger constant `C`.
-/
theorem logSlack_linear_bound (c a b : Nat) :
    ∃ C : Nat, ∀ M : Nat, logSlack c (a * M + b) ≤ logSlack C M := by
  refine ⟨ c * ( Nat.log 2 a + Nat.log 2 b + 2 ) + c, fun M => ?_ ⟩ ; unfold logSlack ; ring_nf;
  -- Use the length bound: `(Nat.bits (a*M+b)).length ≤ (Nat.bits M).length + L`.
  have h_length_bound : (a * M + b).bits.length ≤ M.bits.length + (Nat.log 2 a + Nat.log 2 b + 2) := by
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide [ Nat.size_eq_bits_len ];
    · rw [ Nat.size_le ];
      exact lt_of_lt_of_le ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ( Nat.pow_le_pow_right ( by decide ) ( by linarith ) );
    · refine Nat.le_of_lt_succ ( Nat.lt_succ_of_le ( Nat.le_trans ( Nat.size_le.mpr ?_ ) ( Nat.add_le_add_left ( Nat.le_succ _ ) _ ) ) );
      rw [ pow_add ];
      nlinarith [ Nat.lt_pow_of_log_lt one_lt_two ( by linarith : Nat.log 2 a < Nat.log 2 a + 1 ), Nat.lt_size_self M, Nat.lt_size_self a ];
    · rw [ Nat.size_le ];
      have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) a
      have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) b
      have := Nat.lt_size_self M
      norm_num at *;
      ring_nf at *;
      nlinarith [ Nat.zero_le ( a * M ), Nat.zero_le ( b * M ), Nat.zero_le ( a * b ), Nat.zero_le ( a * 2 ^ M.size ), Nat.zero_le ( b * 2 ^ M.size ), Nat.zero_le ( a * 2 ^ Nat.log 2 b ), Nat.zero_le ( b * 2 ^ Nat.log 2 b ), Nat.zero_le ( 2 ^ M.size * 2 ^ Nat.log 2 a ), Nat.zero_le ( 2 ^ M.size * 2 ^ Nat.log 2 b ), Nat.zero_le ( 2 ^ Nat.log 2 a * 2 ^ Nat.log 2 b ) ];
  nlinarith [ Nat.zero_le ( c * M.bits.length ), Nat.zero_le ( c * Nat.log 2 a ), Nat.zero_le ( c * Nat.log 2 b ) ]

/-
Visible-parameter linear bound for the internal description parameters.
When `j0 + i ≤ KPPlain U x + delta` (the tight dyadic-bracket bound coming from
`setOptimalityCardBound`), the internal budget `n + i + j0` is linearly bounded
by the visible budget `n + delta + d`, using `KPPlain U x ≤ length + O(log length)`.
-/
theorem visible_param_linear_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ b : Nat, ∀ (x : BitString) (n i j0 delta d : Nat),
      x.length = n →
      ((j0 : ENat) + i ≤ KPPlain U x + delta) →
      n + i + j0 ≤ 4 * (n + delta + d) + b := by
  -- By `KPPlain_le_length_add_log U hU`, obtain `cK` with `∀ x, KPPlain U x ≤ length + 2*log(length) + cK`, then use `b := cK`.
  have ⟨cK, hK⟩ := KPPlain_le_length_add_log U hU;
  use cK
  intro x n i j0 delta d hn hbound
  have hsize : (Nat.bits n).length ≤ n := by
    have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
    simpa [Nat.size_eq_bits_len] using h
  have key : ((j0 + i : ℕ) : ENat) ≤ ((n + 2 * (Nat.bits n).length + cK + delta : ℕ) : ENat) := by
    calc ((j0 + i : ℕ) : ENat)
        = (j0 : ENat) + i := by push_cast; ring
      _ ≤ KPPlain U x + delta := hbound
      _ ≤ ((n + 2 * (Nat.bits n).length + cK : ℕ) : ENat) + (delta : ENat) := by
          gcongr
          have h := hK x
          rw [hn] at h
          refine h.trans_eq ?_
          push_cast; ring
      _ = ((n + 2 * (Nat.bits n).length + cK + delta : ℕ) : ENat) := by push_cast; ring
  have keyn : j0 + i ≤ n + 2 * (Nat.bits n).length + cK + delta := by exact_mod_cast key
  omega

end Kolmogorov
