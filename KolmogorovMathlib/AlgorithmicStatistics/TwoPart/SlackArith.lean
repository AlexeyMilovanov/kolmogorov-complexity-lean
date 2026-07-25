import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionShift
import Mathlib.Data.Nat.Log

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
  have h_length_bound : (a * M + b).bits.length ≤
      M.bits.length + (Nat.log 2 a + Nat.log 2 b + 2) := by
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · rw [ha, hb]
        have h_0_M_0 : 0 * M + 0 = 0 := by ring
        rw [h_0_M_0]
        exact Nat.zero_le _
      · rw [ha]
        have h_0_M_b : 0 * M + b = b := by ring
        rw [h_0_M_b]
        have h_log : Nat.log 2 0 = 0 := rfl
        rw [h_log]
        have h1 : b.size ≤ M.bits.length + (0 + Nat.log 2 b + 2) := by
          refine Nat.size_le.mpr (lt_of_lt_of_le
            (Nat.lt_pow_succ_log_self (by decide) b)
            (Nat.pow_le_pow_right (by decide) (by omega)))
        simpa [← Nat.size_eq_bits_len] using h1
    · by_cases hb : b = 0
      · rw [hb]
        have h_a_M_0 : a * M + 0 = a * M := by ring
        rw [h_a_M_0]
        have h_log_0 : Nat.log 2 0 = 0 := rfl
        rw [h_log_0]
        have h1 : (a * M).size ≤ M.bits.length + (Nat.log 2 a + 0 + 2) := by
          refine Nat.le_of_lt_succ (Nat.lt_succ_of_le
            (Nat.le_trans (Nat.size_le.mpr ?_) (Nat.add_le_add_left (Nat.le_succ _) _)))
          rw [ pow_add ]
          have hM : M < 2 ^ M.bits.length := by
            simpa [← Nat.size_eq_bits_len] using Nat.lt_size_self M
          nlinarith [Nat.lt_pow_of_log_lt one_lt_two
            (by omega : Nat.log 2 a < Nat.log 2 a + 1), hM, Nat.lt_size_self a]
        simpa [← Nat.size_eq_bits_len] using h1
      · have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) a
        have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) b
        have hM : M < 2 ^ M.bits.length := by simpa [←Nat.size_eq_bits_len] using Nat.lt_size_self M
        have h1 : (a * M + b).size ≤ M.bits.length + (Nat.log 2 a + Nat.log 2 b + 2) := by
          refine Nat.size_le.mpr ?_
          norm_num at *; ring_nf at *
          nlinarith [Nat.zero_le (a * M), Nat.zero_le (b * M), Nat.zero_le (a * b),
            Nat.zero_le (a * 2 ^ M.bits.length), Nat.zero_le (b * 2 ^ M.bits.length),
            Nat.zero_le (a * 2 ^ Nat.log 2 b), Nat.zero_le (b * 2 ^ Nat.log 2 b),
            Nat.zero_le (2 ^ M.bits.length * 2 ^ Nat.log 2 a),
            Nat.zero_le (2 ^ M.bits.length * 2 ^ Nat.log 2 b),
            Nat.zero_le (2 ^ Nat.log 2 a * 2 ^ Nat.log 2 b)]
        simpa [← Nat.size_eq_bits_len] using h1
  nlinarith [Nat.zero_le (c * M.bits.length), Nat.zero_le (c * Nat.log 2 a),
    Nat.zero_le (c * Nat.log 2 b)]

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
  -- By `KPPlain_le_length_add_log U hU`, obtain `cK` with `∀ x, KPPlain U x ≤ length +
  --   2*log(length) + cK`, then use `b := cK`.
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

/-
A log-slack is dominated by the identity plus a constant: since
`logSlack cc m = cc*(bits m).length + cc` and `(bits m).length` grows only
logarithmically, `cc*(bits m).length` is eventually below `m`, so there is a single
additive constant `b` with `logSlack cc m ≤ m + b` for all `m`.
-/
theorem logSlack_le_add_const (cc : Nat) : ∃ b : Nat, ∀ m : Nat, logSlack cc m ≤ m + b := by
  -- By definition of `logSlack`, we have `logSlack cc m = cc * (Nat.bits m).length + cc`.
  unfold logSlack;
  use cc * 2 ^ ( cc + 2 ) + cc;
  intro m
  by_cases hm : m < 2 ^ (cc + 2);
  · nlinarith [ show m.bits.length ≤ 2 ^ ( cc + 2 ) by
                  have h_bits_len : ∀ m : ℕ, m < 2 ^ (cc + 2) → (m.bits.length ≤ cc + 2) := by
                    intro m hm
                    have h1 := (@Nat.size_le m (cc + 2)).mpr hm
                    simpa [← Nat.size_eq_bits_len] using h1
                  exact le_trans (h_bits_len m hm) (by
                    exact Nat.recOn cc (by norm_num) fun n ihn => by
                      norm_num [Nat.pow_succ'] at *
                      linarith) ];
  · have h_log : cc * (Nat.log 2 m + 1) ≤ m := by
      have h_log_growth : ∀ d : Nat, cc * ((cc + 2 + d) + 1) ≤ 2 ^ (cc + 2 + d) := by
        intro d
        induction d with
        | zero =>
          rcases cc with ( _ | _ | cc )
          · norm_num
          · norm_num
          · exact Nat.recOn cc (by norm_num) fun n ihn => by
              norm_num [Nat.pow_succ'] at ihn ⊢
              nlinarith
        | succ d ih =>
          have h_rw : cc + 2 + (d + 1) = (cc + 2 + d) + 1 := by omega
          rw [h_rw, Nat.pow_succ, mul_two]
          have h1 : cc ≤ 2 ^ (cc + 2 + d) := by
            have h_lt : cc + 2 + d < 2 ^ (cc + 2 + d) := Nat.lt_pow_self one_lt_two
            omega
          nlinarith
      have h_pow_pos : 0 < 2 ^ (cc + 2) := by positivity
      have h_m_pos : 0 < m := lt_of_lt_of_le h_pow_pos (by omega)
      have h_bound : cc + 2 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by decide) (by omega)
      have hk : cc * (Nat.log 2 m + 1) ≤ 2 ^ (Nat.log 2 m) := by
        have h_k_eq : Nat.log 2 m = cc + 2 + (Nat.log 2 m - (cc + 2)) := by omega
        rw [h_k_eq]
        exact h_log_growth (Nat.log 2 m - (cc + 2))
      exact le_trans hk ( Nat.pow_le_of_le_log (by omega) ( Nat.le_refl _ ) )
    have h_log_bits : (Nat.bits m).length ≤ Nat.log 2 m + 1 := by
      have h1 := (@Nat.size_le m (Nat.log 2 m + 1)).mpr
        (show m < 2 ^ (Nat.log 2 m + 1) from Nat.lt_pow_succ_log_self (by decide) m)
      simpa [← Nat.size_eq_bits_len] using h1
    nlinarith [ Nat.zero_le ( cc * 2 ^ ( cc + 2 ) ), Nat.zero_le ( cc * ( Nat.log 2 m + 1 ) ) ]

/-
**Level-slack folding.**  If the level `k` is bounded by the visible budget as
`k ≤ n + beta + logSlack c_lb n` (the shape produced by the level bound), then a
log-slack `logSlack cc k` at that level is dominated by a single log-slack at the
visible budget `n + alpha + beta`, at the cost of a larger constant `C`.  This keeps
the logarithmic tightness (unlike `logSlack_le_add_const`).  Proof: `logSlack c_lb n ≤ n + b`
(`logSlack_le_add_const`), so `k ≤ 2*(n+alpha+beta) + b`; then `logSlack_linear_bound`
and monotonicity of `logSlack` in its argument (`logSlack_mono_right`) fold it.
-/
/-- Slacks at *different* visible budgets combine at the joint budget: the
standard move for merging bounds coming from two sub-arguments. -/
theorem logSlack_add_logSlack_le (c c' n m : Nat) :
    logSlack c n + logSlack c' m ≤ logSlack (c + c') (n + m) :=
  calc logSlack c n + logSlack c' m
      ≤ logSlack c (n + m) + logSlack c' (n + m) :=
        Nat.add_le_add (logSlack_mono_right c (Nat.le_add_right n m))
          (logSlack_mono_right c' (Nat.le_add_left m n))
    _ = logSlack (c + c') (n + m) := logSlack_add_const c c' (n + m)

/-- An additive `O(1)` constant folds into the slack constant. -/
theorem logSlack_add_nat_le (c k n : Nat) :
    logSlack c n + k ≤ logSlack (c + k) n := by
  unfold logSlack
  nlinarith [Nat.zero_le (k * (Nat.bits n).length)]

theorem logSlack_fold_level (cc c_lb : Nat) :
    ∃ C : Nat, ∀ (n alpha beta k : Nat),
      k ≤ n + beta + logSlack c_lb n →
      logSlack cc k ≤ logSlack C (n + alpha + beta) := by
  obtain ⟨b, hb⟩ := logSlack_le_add_const c_lb
  obtain ⟨C, hC⟩ := logSlack_linear_bound cc 2 b
  refine ⟨C, fun n alpha beta k hk => ?_⟩
  have hk' : k ≤ 2 * (n + alpha + beta) + b := by linarith [hb n]
  exact le_trans (logSlack_mono_right cc hk') (hC (n + alpha + beta))

lemma polynomialOverhead_bits_le_logSlack (C d : ℕ) (hC : 0 < C) :
  ∃ c_over : ℕ, ∀ n, (Nat.bits (C * (n + 1) ^ d)).length ≤ logSlack c_over n := by
  refine ⟨Nat.size C + d, fun n => ?_⟩
  have hCsize : 0 < Nat.size C := Nat.size_pos.mpr hC
  have hn : n + 1 ≤ 2 ^ Nat.size n := Nat.succ_le_iff.mpr (Nat.lt_size_self n)
  have hpow : (n + 1) ^ d ≤ (2 ^ Nat.size n) ^ d :=
    Nat.pow_le_pow_left hn d
  have hlt : C * (n + 1) ^ d < 2 ^ (Nat.size C + Nat.size n * d) := by
    calc
      C * (n + 1) ^ d < 2 ^ Nat.size C * (n + 1) ^ d :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self C) (pow_pos (by omega) d)
      _ ≤ 2 ^ Nat.size C * (2 ^ Nat.size n) ^ d :=
        Nat.mul_le_mul_left _ hpow
      _ = 2 ^ (Nat.size C + Nat.size n * d) := by
        rw [← pow_mul, pow_add]
  have hsize : Nat.size (C * (n + 1) ^ d) ≤ Nat.size C + Nat.size n * d :=
    Nat.size_le.mpr hlt
  unfold logSlack
  simp only [Nat.size_eq_bits_len]
  exact hsize.trans (by
    nlinarith [Nat.zero_le (Nat.size C * Nat.size n), Nat.zero_le d, hCsize])

end Kolmogorov
