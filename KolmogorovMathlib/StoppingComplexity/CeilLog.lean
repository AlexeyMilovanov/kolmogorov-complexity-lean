import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec

/-!
# Computable ceiling logarithms and the discount `F`

Blueprint 04 §2 ("Computable ceiling logarithms without real-number decisions").
The ceiling logarithm `L n = min {k | n ≤ 2 ^ k}` is Mathlib's `Nat.clog 2`
(items `04-DEF-L`, `04-L-PROPS`; the specification (L1) is `Nat.clog_le_iff_le_pow`,
monotonicity is `Nat.clog_mono_right`, `n ≤ 2 ^ L n` is `Nat.le_pow_clog`).  On top of
it we define the discount

  `F n = L (max 16 n) + L (L (L (max 16 n)))`

(item `04-DEF-F`), state its computability and monotonicity, the iterated-ceiling
identity, the shift bound `F (n + a) ≤ F n + 2 a` (`04-F-SHIFT`), the doubling bound
(`04-F-DOUBLE`) and the single comparison with the real iterated logarithm used by
Theorem E (`04-F-REAL`).  Everything except the last lemma is integer arithmetic.
-/

namespace Kolmogorov

/-- For `n ≥ 2` the ceiling logarithm is one more than the floor logarithm of `n - 1`:
`L n = ⌊log₂ (n - 1)⌋ + 1`. -/
private theorem clogTwo_eq_log_pred_add_one {n : ℕ} (hn : 2 ≤ n) :
    Nat.clog 2 n = Nat.log 2 (n - 1) + 1 := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
    have h : n - 1 < 2 ^ (Nat.log 2 (n - 1) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) (n - 1)
    omega
  · rw [Nat.add_one_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)]
    have h := Nat.pow_log_le_self 2 (x := n - 1) (by omega)
    omega

/-- The ceiling logarithm `L = Nat.clog 2` is primitive recursive: it is `0` for `n ≤ 1` and
`⌊log₂ (n - 1)⌋ + 1` otherwise.  Blueprint 04 Definition L (`04-DEF-L`). -/
theorem primrec_clogTwo : Primrec fun n : ℕ => Nat.clog 2 n := by
  have h : Primrec fun n : ℕ => if n ≤ 1 then 0 else Nat.log 2 (n - 1) + 1 :=
    Primrec.ite (Primrec.nat_le.comp Primrec.id (Primrec.const 1)) (Primrec.const 0)
      (Primrec.nat_add.comp
        (primrec_natLogTwo.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
        (Primrec.const 1))
  refine h.of_eq fun n => ?_
  split_ifs with hn
  · exact (Nat.clog_of_right_le_one hn 2).symm
  · exact (clogTwo_eq_log_pred_add_one (by omega)).symm

/-- The ceiling logarithm `L = Nat.clog 2` is a computable function of `n` (bounded search
through `k = 0, …, n`, or via `Nat.log 2`).  Blueprint 04 Definition L (`04-DEF-L`). -/
theorem clogTwo_computable : Computable fun n : ℕ => Nat.clog 2 n := by
  exact primrec_clogTwo.to_comp

/-- For `n ≥ 1`, the first power of two at least `n` is at most `2 n`:
`2 ^ L n ≤ 2 n`.  Blueprint 04 Lemma L-properties (2), second half (`04-L-PROPS`). -/
theorem clogTwo_pow_le_two_mul {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  rcases h : Nat.clog 2 n with _ | k
  · simp only [pow_zero]
    omega
  · have hlt : 2 ^ k < n := (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by omega)
    rw [pow_succ]
    omega

/-- One step never raises the ceiling logarithm by more than one:
`L (n + 1) ≤ L n + 1`.  Blueprint 04 Lemma L-properties (3) (`04-L-PROPS`). -/
theorem clogTwo_succ_le (n : ℕ) : Nat.clog 2 (n + 1) ≤ Nat.clog 2 n + 1 := by
  rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2), pow_succ]
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) n
  have h2 := Nat.two_pow_pos (Nat.clog 2 n)
  omega

/-- Multiplying by `2 ^ a` shifts the ceiling logarithm by exactly `a` when `n ≥ 1`:
`L (2 ^ a * n) = a + L n`.  Blueprint 04 Lemma L-properties (4) (`04-L-PROPS`). -/
theorem clogTwo_two_pow_mul {n : ℕ} (hn : 1 ≤ n) (a : ℕ) :
    Nat.clog 2 (2 ^ a * n) = a + Nat.clog 2 n := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : 2 ^ (a + 1) * n = 2 * (2 ^ a * n) := by ring
    have hpos : 1 ≤ 2 ^ a * n := Nat.mul_pos (Nat.two_pow_pos a) hn
    generalize hm : 2 ^ a * n = m at ih hpos e
    rw [e, Nat.clog_of_two_le (by norm_num) (by omega)]
    have hdiv : (2 * m + 2 - 1) / 2 = m := by omega
    rw [hdiv, ih]
    ring

/-- For `j ≥ 1`, `L (j + 1) ≤ j` (since `j + 1 ≤ 2 ^ j`).
Blueprint 04 Lemma L-properties (5) (`04-L-PROPS`). -/
theorem clogTwo_succ_le_self {j : ℕ} (hj : 1 ≤ j) : Nat.clog 2 (j + 1) ≤ j := by
  rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ k _ ih =>
    rw [pow_succ]
    omega

/-- The discount `F n = L (max 16 n) + L (L (L (max 16 n)))` with `L = Nat.clog 2`: for
`n ≥ 16` it equals `⌈log₂ n⌉ + ⌈log₂ log₂ log₂ n⌉`, computed by integer arithmetic only.
Blueprint 04 Definition F (`04-DEF-F`). -/
def discountF (n : ℕ) : ℕ :=
  Nat.clog 2 (max 16 n) + Nat.clog 2 (Nat.clog 2 (Nat.clog 2 (max 16 n)))

/-- The discount `F` is a total computable function (the seventh of the items that must not be
packaged as a hypothesis: computability of the rounded iterated logarithm is a theorem).
Blueprint 04 Definition F (`04-DEF-F`). -/
theorem discountF_computable : Computable discountF := by
  have hN : Primrec fun n : ℕ => max 16 n := Primrec.nat_max.comp (Primrec.const 16) Primrec.id
  have hL := primrec_clogTwo
  exact (Primrec.nat_add.comp (hL.comp hN) (hL.comp (hL.comp (hL.comp hN)))).to_comp.of_eq
    fun _ => rfl

/-- The discount `F` is nondecreasing.  Blueprint 04 Definition F (`04-DEF-F`). -/
theorem discountF_mono : Monotone discountF := by
  intro a b h
  have hN : max 16 a ≤ max 16 b := max_le_max le_rfl h
  exact add_le_add (Nat.clog_mono_right 2 hN)
    (Nat.clog_mono_right 2 (Nat.clog_mono_right 2 (Nat.clog_mono_right 2 hN)))

/-- The iterated-ceiling identity: `L (L (L n)) ≤ k ↔ n ≤ 2 ^ 2 ^ 2 ^ k`, three applications of
(L1).  The blueprint's identity is unconditional, so no `16 ≤ n` hypothesis is carried
(deviation from the `items.tsv` sketch).  Blueprint 04 Definition F, iterated-ceiling identity
(`04-DEF-F`). -/
theorem clogTwo_iter_three_le_iff (n k : ℕ) :
    Nat.clog 2 (Nat.clog 2 (Nat.clog 2 n)) ≤ k ↔ n ≤ 2 ^ 2 ^ 2 ^ k := by
  rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2), Nat.clog_le_iff_le_pow (by norm_num : 1 < 2),
    Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]

/-- The ceiling logarithm moves by at most one along a step of at most one:
`x ≤ y + 1` implies `L x ≤ L y + 1` (monotonicity and L-properties (3)). -/
private theorem clogTwo_le_succ_of_le_succ {x y : ℕ} (h : x ≤ y + 1) :
    Nat.clog 2 x ≤ Nat.clog 2 y + 1 :=
  (Nat.clog_mono_right 2 h).trans (clogTwo_succ_le y)

/-- One step of the argument raises `F` by at most two: `F (n + 1) ≤ F n + 2`, since each of
`L (N n)` and `L (L (L (N n)))` rises by at most one. -/
private theorem discountF_succ_le (n : ℕ) : discountF (n + 1) ≤ discountF n + 2 := by
  have h0 : max 16 (n + 1) ≤ max 16 n + 1 :=
    max_le (by omega) (Nat.add_le_add_right (le_max_right 16 n) 1)
  have h1 := clogTwo_le_succ_of_le_succ h0
  have h3 := clogTwo_le_succ_of_le_succ (clogTwo_le_succ_of_le_succ h1)
  unfold discountF
  omega

/-- F-shift with the explicit constant `D_a = 2 a`: for all naturals `n, a`,
`F (n + a) ≤ F n + 2 a`.  Blueprint 04 Lemma F-shift (`04-F-SHIFT`). -/
theorem discountF_add_le (n a : ℕ) : discountF (n + a) ≤ discountF n + 2 * a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h := discountF_succ_le (n + a)
    rw [← add_assoc]
    omega

/-- F-double: if `16 ≤ x ≤ y ≤ 2 x` then `F y ≤ F x + 2`.
Blueprint 04 Lemma F-double (`04-F-DOUBLE`). -/
theorem discountF_le_of_le_two_mul {x y : ℕ} (h16 : 16 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 * x) :
    discountF y ≤ discountF x + 2 := by
  have hx : max 16 x = x := max_eq_right h16
  have hy' : max 16 y = y := max_eq_right (h16.trans hxy)
  have h1 : Nat.clog 2 y ≤ Nat.clog 2 x + 1 := by
    have h2 := clogTwo_two_pow_mul (n := x) (by omega) 1
    have h3 : Nat.clog 2 y ≤ Nat.clog 2 (2 ^ 1 * x) := Nat.clog_mono_right 2 (by omega)
    omega
  have h3 := clogTwo_le_succ_of_le_succ (clogTwo_le_succ_of_le_succ h1)
  unfold discountF
  rw [hx, hy']
  omega

/-- The real binary logarithm of a natural number is at most its ceiling logarithm,
`log₂ m ≤ L m` (both sides vanish at `m = 0`). -/
private theorem logb_le_clogTwo (m : ℕ) : Real.logb 2 m ≤ Nat.clog 2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hle : (m : ℝ) ≤ 2 ^ Nat.clog 2 m := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) m
    calc Real.logb 2 m ≤ Real.logb 2 (2 ^ Nat.clog 2 m) :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hm) hle
      _ = Nat.clog 2 m := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- `F` dominates the real iterated logarithm: for `n ≥ 16`,
`log₂ n + log₂ log₂ log₂ n ≤ F n` (three applications of `log₂ x ≤ L x`).  Used once, in
Theorem E.  Blueprint 04 Definition F, comparison with the real logarithm (`04-F-REAL`). -/
theorem logb_add_logb_logb_logb_le_discountF {n : ℕ} (h : 16 ≤ n) :
    Real.logb 2 n + Real.logb 2 (Real.logb 2 (Real.logb 2 n)) ≤ discountF n := by
  have hN : max 16 n = n := max_eq_right h
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast h
  have ha : 1 < Real.logb 2 n :=
    calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ < Real.logb 2 n := Real.logb_lt_logb (by norm_num) (by norm_num) (by linarith)
  have hb : 0 < Real.logb 2 (Real.logb 2 n) := Real.logb_pos (by norm_num) ha
  have h1 := logb_le_clogTwo n
  have h2 : Real.logb 2 (Real.logb 2 n) ≤ Nat.clog 2 (Nat.clog 2 n) :=
    (Real.logb_le_logb_of_le (by norm_num) (by linarith) h1).trans (logb_le_clogTwo _)
  have h3 : Real.logb 2 (Real.logb 2 (Real.logb 2 n)) ≤
      Nat.clog 2 (Nat.clog 2 (Nat.clog 2 n)) :=
    (Real.logb_le_logb_of_le (by norm_num) hb h2).trans (logb_le_clogTwo _)
  unfold discountF
  rw [hN]
  push_cast
  linarith

end Kolmogorov
