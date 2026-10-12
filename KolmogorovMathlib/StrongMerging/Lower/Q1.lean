import KolmogorovMathlib.StrongMerging.Lower.Assembly
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The negative answer to the formal Question 1

Blueprint nodes L40 (`strongMinimumProfile`), L41 (`stableProfileWindow`) and L42
(`q1FormalCounterexample`) of the formalization of `sublinear-merging.tex` (main text: section
"A consequence for robust minimal strong statistics", Corollary `cor:q1-negative`, tex lines
2103-2240; appendix paragraphs "L40" to "L42", lines 5070-5150).

* **L40.**  `strongProfile V x t` is the attained minimum of `C(F)` over the strong-only
  admissible class at tolerance `t`: `t`-strong, `t`-sufficient models `F ∋ x`
  (`ProfileAdmissible`).  It is a noncomputable `sInf` of natural values; it is attained and
  antitone in `t` whenever the class is nonempty.
* **L41.**  Along the window `t_i = t₀ + i w`, `i < J`, some drop `d_i = f(t_i) - f(t_{i+1})`
  satisfies `J d_i ≤ f(t₀)`; a minimizer at `t_i` is strong-only robustly minimal (the shared S00
  predicate `StrongRobustMin`) at tolerance `t_i + s` for every `s ≤ w`, with gap `d_i + 1`.
* **L42.**  With `E = m²` in the sharp theorem (`exists_strong_pair_without_common_model'`) the
  selected minimizer is far, in total conditional complexity, from one of the two original stars:
  `exists_strongRobustMin_seq_unbounded_ratio'` and `not_exists_strongRobustMin_total_bound'`,
  verbatim the frozen statements of `StrongMerging.Statements`.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset Filter

/-! ### L40: the strong minimum profile -/

/-- The strong-only admissible class at tolerance `t`: `F` is `t`-strong and `t`-sufficient for
`x` (sufficiency includes `x ∈ F`). -/
def ProfileAdmissible (V : Map) (x : BitString) (t : ℝ) (F : Finset BitString) : Prop :=
  IsStrongModel x F t ∧ IsSufficientModel V x F t

/-- Admissibility is monotone in the tolerance. -/
theorem ProfileAdmissible.mono {V : Map} {x : BitString} {t t' : ℝ} {F : Finset BitString}
    (h : ProfileAdmissible V x t F) (htt' : t ≤ t') : ProfileAdmissible V x t' F :=
  ⟨le_trans h.1 htt', h.2.1, by linarith [h.2.2]⟩

/-- **The strong minimum profile** (node L40): `f(t) = min {C(F) : F admissible at t}`, the
infimum of the natural values `(plainK V (code F)).toNat = C(F)`; it is `0` for an empty class
(a default never used). -/
noncomputable def strongProfile (V : Map) (x : BitString) (t : ℝ) : ℕ :=
  sInf {k : ℕ | ∃ F : Finset BitString, ProfileAdmissible V x t F ∧
    (plainK V (canonicalFiniteSetCode F)).toNat = k}

/-- **Attainment** (node L40): a nonempty admissible class has a member of complexity exactly
`f(t)`. -/
theorem exists_strongProfile_eq {V : Map} {x : BitString} {t : ℝ} {F₀ : Finset BitString}
    (h : ProfileAdmissible V x t F₀) :
    ∃ F : Finset BitString, ProfileAdmissible V x t F ∧ setC V F = strongProfile V x t := by
  have hne : {k : ℕ | ∃ F : Finset BitString, ProfileAdmissible V x t F ∧
      (plainK V (canonicalFiniteSetCode F)).toNat = k}.Nonempty := ⟨_, F₀, h, rfl⟩
  obtain ⟨F, hF, hk⟩ := Nat.sInf_mem hne
  exact ⟨F, hF, by rw [strongProfile, ← hk]; rfl⟩

/-- **Minimality** (node L40): every admissible model has complexity at least `f(t)`. -/
theorem strongProfile_le {V : Map} {x : BitString} {t : ℝ} {F : Finset BitString}
    (h : ProfileAdmissible V x t F) : (strongProfile V x t : ℝ) ≤ setC V F := by
  have : strongProfile V x t ≤ (plainK V (canonicalFiniteSetCode F)).toNat :=
    Nat.sInf_le ⟨F, h, rfl⟩
  unfold setC plainC
  exact_mod_cast this

/-- **Monotonicity** (node L40): if the class at `t` is nonempty and `t ≤ t'` then
`f(t') ≤ f(t)`. -/
theorem strongProfile_antitone {V : Map} {x : BitString} {t t' : ℝ} {F₀ : Finset BitString}
    (h : ProfileAdmissible V x t F₀) (htt' : t ≤ t') :
    strongProfile V x t' ≤ strongProfile V x t := by
  obtain ⟨F, hF, hFeq⟩ := exists_strongProfile_eq h
  have h' := strongProfile_le (hF.mono htt')
  rw [hFeq] at h'
  exact_mod_cast h'

/-- **Node L40, `strongMinimumProfile`.**  For a string `x` whose strong-only admissible class at
tolerance `t` is nonempty: the profile value `f(t)` is attained, every admissible model has
complexity at least `f(t)`, and `f` is antitone from `t` on. -/
theorem strongMinimumProfile (V : Map) (x : BitString) (t : ℝ) (F₀ : Finset BitString)
    (h : ProfileAdmissible V x t F₀) :
    (∃ F : Finset BitString, ProfileAdmissible V x t F ∧ setC V F = strongProfile V x t) ∧
      (∀ F : Finset BitString, ProfileAdmissible V x t F → (strongProfile V x t : ℝ) ≤ setC V F) ∧
      ∀ t' : ℝ, t ≤ t' → strongProfile V x t' ≤ strongProfile V x t :=
  ⟨exists_strongProfile_eq h, fun _ hF => strongProfile_le hF,
    fun _ ht => strongProfile_antitone h ht⟩

/-! ### L41: a stable window -/

/-- **A small drop exists** (integer averaging): for an antitone `f : ℕ → ℕ` and `J ≥ 1` some
`i < J` has `J (f i - f (i + 1)) ≤ f 0`.

Proof sketch: the drops telescope, `∑_{i<J} (f i - f (i + 1)) = f 0 - f J ≤ f 0`
(`Finset.sum_range_tsub` for antitone `f`, or induction on `J`); if every drop had
`J (f i - f (i + 1)) > f 0`, summing over `i < J` would give `J (f 0 - f J) > J f 0`.
Reference: tex 2186-2190 ("Choose `i < J` for which the integer drop is at most
`(n + c₀)/J`"), blueprint L41 ("integer form of averaging"). -/
theorem exists_small_drop (f : ℕ → ℕ) (hf : Antitone f) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ i < J, J * (f i - f (i + 1)) ≤ f 0 := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have htel : ∀ n, ∑ i ∈ range n, (f i - f (i + 1)) = f 0 - f n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      have h1 : f (n + 1) ≤ f n := hf (Nat.le_succ n)
      have h2 : f n ≤ f 0 := hf (Nat.zero_le n)
      omega
  have hsum : J * f 0 < ∑ i ∈ range J, J * (f i - f (i + 1)) := by
    calc J * f 0 = ∑ _i ∈ range J, f 0 := by simp
      _ < ∑ i ∈ range J, J * (f i - f (i + 1)) :=
        sum_lt_sum_of_nonempty ⟨0, by simp; omega⟩ fun i hi => h i (mem_range.1 hi)
  rw [← mul_sum, htel] at hsum
  have : J * (f 0 - f J) ≤ J * f 0 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  omega

/-- **Node L41, `stableProfileWindow`.**  Let `F₀` be admissible at `t₀`, let `w, J` be naturals
with `J ≥ 1`, and let `s ≤ w`.  Then for some `i < J` there are a model `F` admissible at
`t_i = t₀ + i w` and a natural drop `d` with `J d ≤ f(t₀)` such that `F` is strong-only robustly
minimal (S00) at tolerance `t_i + s` with gap `d + 1`: every `(t_i + s)`-strong,
`(t_i + s)`-sufficient `F'` has `C(F) < C(F') + d + 1`. -/
theorem stableProfileWindow (V : Map) (x : BitString) (t₀ : ℝ) (F₀ : Finset BitString)
    (hF₀ : ProfileAdmissible V x t₀ F₀) (w J : ℕ) (hJ : 1 ≤ J) (s : ℝ) (hs : s ≤ w) :
    ∃ i < J, ∃ (F : Finset BitString) (dr : ℕ), ProfileAdmissible V x (t₀ + i * w) F ∧
      J * dr ≤ strongProfile V x t₀ ∧ StrongRobustMin V x F (t₀ + i * w + s) (dr + 1) := by
  set f : ℕ → ℕ := fun k => strongProfile V x (t₀ + k * w) with hf
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hadm : ∀ k : ℕ, ProfileAdmissible V x (t₀ + k * w) F₀ := fun k =>
    hF₀.mono (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hanti : Antitone f := by
    intro k l hkl
    have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
    exact strongProfile_antitone (hadm k) (by nlinarith)
  obtain ⟨i, hi, hdrop⟩ := exists_small_drop f hanti hJ
  obtain ⟨F, hF, hFeq⟩ := exists_strongProfile_eq (hadm i)
  have hf0 : f 0 = strongProfile V x t₀ := by simp [hf]
  refine ⟨i, hi, F, f i - f (i + 1), hF, hf0 ▸ hdrop, fun F' hs' hsuff' => ?_⟩
  have hadm' : ProfileAdmissible V x (t₀ + ((i + 1 : ℕ) : ℝ) * w) F' :=
    ProfileAdmissible.mono (⟨hs', hsuff'⟩ : ProfileAdmissible V x _ F') (by push_cast; linarith)
  have hlow := strongProfile_le hadm'
  have hle : f (i + 1) ≤ f i := hanti (Nat.le_succ i)
  have hsub : ((f i - f (i + 1) : ℕ) : ℝ) = (f i : ℝ) - f (i + 1) := by
    rw [Nat.cast_sub hle]
  have hFi : setC V F = f i := hFeq
  have hFi1 : (f (i + 1) : ℝ) ≤ setC V F' := hlow
  push_cast [hsub]
  linarith

/-! ### L42: the formal counterexample -/

/-- The logarithm `L = log₂ n` of the length `n = 2M`. -/
noncomputable def q1Log (M : ℕ) : ℝ :=
  Real.logb 2 ((2 * M : ℕ) : ℝ)

/-- The window step `w = ⌈c_min L⌉ + 1`. -/
noncomputable def q1Width (cmin : ℝ) (M : ℕ) : ℕ :=
  ⌈cmin * q1Log M⌉₊ + 1

/-- The window length `J = ⌊√(n / L)⌋`. -/
noncomputable def q1Count (M : ℕ) : ℕ :=
  ⌊Real.sqrt (((2 * M : ℕ) : ℝ) / q1Log M)⌋₊

/-- The scale `√(n L)` of the parameters, `n = 2M`. -/
noncomputable def q1Scale (M : ℕ) : ℝ :=
  Real.sqrt (((2 * M : ℕ) : ℝ) * q1Log M)

/-- Basic facts on `L = log₂ (2M)` for `M ≥ 1`: `1 ≤ L ≤ 2M`, `L - 1 ≤ m`. -/
theorem q1Log_facts {M : ℕ} (hM : 1 ≤ M) :
    1 ≤ q1Log M ∧ q1Log M ≤ ((2 * M : ℕ) : ℝ) ∧ q1Log M - 1 ≤ headerLog M := by
  have h2M : (2 : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * M)
  refine ⟨?_, ?_, ?_⟩
  · unfold q1Log
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]
    exact h2M
  · unfold q1Log
    rw [Real.logb_le_iff_le_rpow one_lt_two (by linarith), Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self).le
  · unfold q1Log
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have e : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
    rw [e, Real.logb_mul (by norm_num) hM0.ne', Real.logb_self_eq_one one_lt_two]
    have h1 : Real.logb 2 (M : ℝ) ≤ Real.logb 2 ((M : ℝ) + 2) :=
      Real.logb_le_logb_of_le one_lt_two hM0 (by linarith)
    have h2 : ((M + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (headerLog M : ℕ) := by
      have := Nat.le_pow_clog one_lt_two (M + 2)
      unfold headerLog
      exact_mod_cast this
    have h3 : Real.logb 2 ((M : ℝ) + 2) ≤ headerLog M := by
      rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity), Real.rpow_natCast]
      push_cast at h2
      exact h2
    linarith

/-- The merger budget at `E = m²` is at least `(m √M - 1) / 10⁶ - 1`. -/
theorem mergerBudget_sq_ge (M : ℕ) :
    ((headerLog M : ℝ) * Real.sqrt M - 1) / 10 ^ 6 - 1 ≤ mergerBudget M (headerLog M ^ 2) := by
  have hr : Real.sqrt ((M * headerLog M ^ 2 : ℕ) : ℝ) < (Nat.sqrt (M * headerLog M ^ 2) : ℝ) + 1 :=
    Real.real_sqrt_lt_nat_sqrt_succ
  have hsq : Real.sqrt ((M * headerLog M ^ 2 : ℕ) : ℝ) = (headerLog M : ℝ) * Real.sqrt M := by
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _), mul_comm]
  have hT : (Nat.sqrt (M * headerLog M ^ 2) : ℝ) <
      10 ^ 6 * ((mergerBudget M (headerLog M ^ 2) : ℝ) + 1) := by
    have h := Nat.lt_mul_div_succ (Nat.sqrt (M * headerLog M ^ 2)) (show 0 < 10 ^ 6 by positivity)
    have h' : (Nat.sqrt (M * headerLog M ^ 2) : ℝ) <
        ((10 ^ 6 * (Nat.sqrt (M * headerLog M ^ 2) / 10 ^ 6 + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [mergerBudget]
    push_cast at h' ⊢
    linarith
  rw [hsq] at hr
  rw [div_sub_one (by norm_num), div_le_iff₀ (by norm_num)]
  linarith

/-- Polylogarithms are eventually small: for every `C`, eventually `C L⁴ ≤ M`, `L = log₂ (2M)`. -/
theorem q1Log_pow_le (C : ℝ) : ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M → C * q1Log M ^ 4 ≤ M := by
  have hc : (0 : ℝ) < 1 / (64 * (|C| + 1)) := by positivity
  have ho := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound hc
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp ho
  refine ⟨⌈x₀⌉₊ + 1, fun M hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hx : x₀ ≤ 2 * (M : ℝ) := by
    have h1 : x₀ ≤ (⌈x₀⌉₊ : ℝ) := Nat.le_ceil x₀
    have h2 : ((⌈x₀⌉₊ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM
    push_cast at h2
    linarith
  have h := hx₀ (2 * M) hx
  have hlogpos : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by linarith)
  have h' : Real.log (2 * (M : ℝ)) ^ 4 ≤ 1 / (64 * (|C| + 1)) * (2 * M) := by
    simp only [Real.norm_eq_abs, id] at h
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.log (2 * (M : ℝ)) ^ 4),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (M : ℝ))] at h
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hL : q1Log M = Real.log (2 * (M : ℝ)) / Real.log 2 := by
    unfold q1Log
    push_cast
    rfl
  have hL0 : 0 ≤ q1Log M := by
    rw [hL]
    positivity
  have hLle : q1Log M ≤ 2 * Real.log (2 * (M : ℝ)) := by
    rw [hL, div_le_iff₀ (by linarith)]
    nlinarith
  calc C * q1Log M ^ 4 ≤ (|C| + 1) * (2 * Real.log (2 * (M : ℝ))) ^ 4 :=
        mul_le_mul (by linarith [le_abs_self C]) (pow_le_pow_left₀ hL0 hLle 4)
          (by positivity) (by positivity)
    _ = 16 * (|C| + 1) * Real.log (2 * (M : ℝ)) ^ 4 := by ring
    _ ≤ 16 * (|C| + 1) * (1 / (64 * (|C| + 1)) * (2 * M)) := by gcongr
    _ = M / 2 := by field_simp; ring
    _ ≤ M := by linarith

/-- The header is at most `L + 1` for `M ≥ 2`. -/
theorem headerLog_le_q1Log {M : ℕ} (hM : 2 ≤ M) : (headerLog M : ℝ) ≤ q1Log M + 1 := by
  have h1 := clog_le_logb_add_one (M + 2)
  have h2 : Real.logb 2 ((M + 2 : ℕ) : ℝ) ≤ q1Log M := by
    unfold q1Log
    exact Real.logb_le_logb_of_le one_lt_two (by positivity)
      (by exact_mod_cast (by omega : M + 2 ≤ 2 * M))
  have h3 : (headerLog M : ℝ) = (Nat.clog 2 (M + 2) : ℝ) := rfl
  linarith

/-- The window-length scale: `√(2M / L) · L = √(2 M L)` and `√(2M/L) ≤ √(2ML)` for `L ≥ 1`. -/
theorem q1_sqrt_div_facts {M : ℕ} (hL1 : 1 ≤ q1Log M) :
    Real.sqrt (((2 * M : ℕ) : ℝ) / q1Log M) * q1Log M = q1Scale M ∧
      Real.sqrt (((2 * M : ℕ) : ℝ) / q1Log M) ≤ q1Scale M := by
  have hL0 : 0 ≤ q1Log M := by linarith
  have hn : (0 : ℝ) ≤ ((2 * M : ℕ) : ℝ) := Nat.cast_nonneg _
  have hLne : q1Log M ≠ 0 := by positivity
  have e : Real.sqrt (((2 * M : ℕ) : ℝ) / q1Log M) * q1Log M = q1Scale M := by
    unfold q1Scale
    calc Real.sqrt (((2 * M : ℕ) : ℝ) / q1Log M) * q1Log M =
          Real.sqrt (((2 * M : ℕ) : ℝ) / q1Log M) * Real.sqrt (q1Log M ^ 2) := by
          rw [Real.sqrt_sq hL0]
      _ = Real.sqrt (((2 * M : ℕ) : ℝ) / q1Log M * q1Log M ^ 2) :=
          (Real.sqrt_mul (div_nonneg hn hL0) _).symm
      _ = Real.sqrt (((2 * M : ℕ) : ℝ) * q1Log M) := by
          congr 1
          field_simp
  refine ⟨e, ?_⟩
  rw [← e]
  have := Real.sqrt_nonneg (((2 * M : ℕ) : ℝ) / q1Log M)
  nlinarith

/-- **The window is nonempty** (L42): eventually `J = ⌊√(n / L)⌋ ≥ 1`, with `n = 2M`,
`L = log₂ n`.

Proof sketch: `n / L ≥ 1` as soon as `log₂ (2M) ≤ 2M` and `M ≥ 1` (`Real.logb_le_self`-type
bound, or `Real.log_le_sub_one_of_pos`), so `√(n / L) ≥ 1` and `Nat.le_floor`.
Reference: tex 2172-2176 ("For all large `n`, `J ≥ 1`"), blueprint L41. -/
theorem q1_count_pos : ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M → 1 ≤ q1Count M := by
  refine ⟨1, fun M hM => ?_⟩
  unfold q1Count
  apply Nat.le_floor
  have hLpos : 0 < q1Log M :=
    Real.logb_pos one_lt_two (by exact_mod_cast (by omega : 1 < 2 * M))
  have hLle : q1Log M ≤ ((2 * M : ℕ) : ℝ) := by
    unfold q1Log
    rw [Real.logb_le_iff_le_rpow one_lt_two (by exact_mod_cast (by omega : 0 < 2 * M)),
      Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self).le
  rw [Nat.cast_one, Real.one_le_sqrt, le_div_iff₀ hLpos]
  linarith

/-- **The window stays below the scale** (L42): for `c_min ≥ 0`, eventually
`t_J = 32 m² + J w ≤ (c_min + 4) √(n L)`, with `m = ⌈log₂ (M + 2)⌉`, `w = ⌈c_min L⌉ + 1`.

Proof sketch: `J w ≤ √(n/L) (c_min L + 2) = c_min √(nL) + 2 √(n/L) ≤ (c_min + 2) √(nL)` for
`L ≥ 1` (`Nat.floor_le`, `Nat.ceil_lt_add_one`); `m ≤ L + 1` for `M ≥ 2`
(`clog_le_logb_add_one`, `Real.logb_le_logb_of_le`) and `32 (L + 1)² ≤ √(nL)` eventually
(polylogarithmic versus `√n`, e.g. via `Real.isLittleO_log_rpow_atTop`).
Reference: tex 2191-2196 (`t_i ≤ e₀ + J w = O(√(n log n))`), blueprint L41-L42. -/
theorem q1_window_scale (cmin : ℝ) (hcmin : 0 ≤ cmin) :
    ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
      ((32 * headerLog M ^ 2 + q1Count M * q1Width cmin M : ℕ) : ℝ) ≤
        (cmin + 4) * q1Scale M := by
  obtain ⟨M₀, hM₀⟩ := q1Log_pow_le 4096
  refine ⟨max M₀ 2, fun M hM => ?_⟩
  have hM2 : 2 ≤ M := le_of_max_le_right hM
  obtain ⟨hL1, hL2, -⟩ := q1Log_facts (by omega : 1 ≤ M)
  have hmL := headerLog_le_q1Log hM2
  have hpoly := hM₀ M (le_of_max_le_left hM)
  obtain ⟨hJS, hJle⟩ := q1_sqrt_div_facts hL1
  set L := q1Log M with hL
  set S := q1Scale M with hS
  set r := Real.sqrt (((2 * M : ℕ) : ℝ) / L) with hr
  have hJ : (q1Count M : ℝ) ≤ r := Nat.floor_le (Real.sqrt_nonneg _)
  have hw : (q1Width cmin M : ℝ) ≤ cmin * L + 2 := by
    unfold q1Width
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ cmin * L)
    push_cast
    linarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hJw : (q1Count M : ℝ) * q1Width cmin M ≤ cmin * S + 2 * S := by
    have h1 : (q1Count M : ℝ) * q1Width cmin M ≤ r * (cmin * L + 2) :=
      mul_le_mul hJ hw (Nat.cast_nonneg _) hr0
    nlinarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hS64 : 64 * L ^ 2 ≤ S := by
    rw [hS, q1Scale, ← hL]
    apply Real.le_sqrt_of_sq_le
    push_cast
    nlinarith
  have hm2 : (headerLog M : ℝ) ^ 2 ≤ 4 * L ^ 2 := by
    have : (0 : ℝ) ≤ headerLog M := Nat.cast_nonneg _
    nlinarith
  push_cast
  nlinarith

/-- **The drop gap stays below the scale** (L42): for `c_min ≥ 0` and a constant `b`,
eventually `(n + b + 32 m²) / J + 1 ≤ (c_min + 4) √(n L)`.

Proof sketch: `J ≥ √(n/L) - 1 ≥ √(n/L) / 2` eventually (`Nat.lt_floor_add_one`), so the left
side is at most `2 (n + b + 32 m²) √(L / n) + 1 = 2 √(nL) + o(√(nL)) ≤ 3 √(nL)` eventually.
Reference: tex 2196-2198 (`δ' ≤ (n + c₀)/J + 1 = O(√(n log n))`), blueprint L41-L42. -/
theorem q1_window_drop (cmin : ℝ) (hcmin : 0 ≤ cmin) (b : ℕ) :
    ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
      ((2 * M + b + 32 * headerLog M ^ 2 : ℕ) : ℝ) / q1Count M + 1 ≤ (cmin + 4) * q1Scale M := by
  obtain ⟨M₀, hM₀⟩ := q1Log_pow_le 256
  refine ⟨max (max M₀ (2 * b)) 2, fun M hM => ?_⟩
  have hM2 : 2 ≤ M := le_of_max_le_right hM
  have hMM₀ : M₀ ≤ M := le_trans (le_max_left _ _) (le_of_max_le_left hM)
  have hMb : 2 * b ≤ M := le_trans (le_max_right _ _) (le_of_max_le_left hM)
  obtain ⟨hL1, hL2, -⟩ := q1Log_facts (by omega : 1 ≤ M)
  have hmL := headerLog_le_q1Log hM2
  have hpoly := hM₀ M hMM₀
  obtain ⟨hJS, hJle⟩ := q1_sqrt_div_facts hL1
  set L := q1Log M with hL
  set S := q1Scale M with hS
  set r := Real.sqrt (((2 * M : ℕ) : ℝ) / L) with hr
  set m : ℝ := (headerLog M : ℝ) with hm
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hb : (2 : ℝ) * b ≤ M := by exact_mod_cast hMb
  have hL0 : 0 < L := by linarith
  have hn : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
  have hrr : r * r = 2 * (M : ℝ) / L := by
    rw [hr, Real.mul_self_sqrt (div_nonneg (by positivity) hL0.le), hn]
  have hrS : r * S = 2 * (M : ℝ) := by
    rw [← hJS]
    have : r * (r * L) = r * r * L := by ring
    rw [this, hrr]
    field_simp
  have hL4 : L ≤ L ^ 4 := by
    have h1 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
    calc L = L * 1 := (mul_one _).symm
      _ ≤ L * L ^ 3 := mul_le_mul_of_nonneg_left h1 hL0.le
      _ = L ^ 4 := by ring
  have hL24 : L ^ 2 ≤ L ^ 4 := by
    have h1 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
    calc L ^ 2 = L ^ 2 * 1 := (mul_one _).symm
      _ ≤ L ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = L ^ 4 := by ring
  -- `r ≥ 2`
  have hr2 : 2 ≤ r := by
    rw [hr, Real.le_sqrt (by norm_num) (div_nonneg (by positivity) hL0.le), hn,
      le_div_iff₀ hL0]
    nlinarith
  have hJ : r - 1 < (q1Count M : ℝ) := by
    have := Nat.lt_floor_add_one r
    unfold q1Count
    linarith
  have hJpos : 0 < (q1Count M : ℝ) := by linarith
  have hJr : r / 2 ≤ (q1Count M : ℝ) := by linarith
  have hm2 : m ^ 2 ≤ 4 * L ^ 2 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  set N : ℝ := ((2 * M + b + 32 * headerLog M ^ 2 : ℕ) : ℝ) with hNdef
  have hN : N ≤ 2 * M + b + 128 * L ^ 2 := by
    rw [hNdef]
    push_cast
    rw [← hm]
    linarith
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hS1 : 1 ≤ S := by linarith
  have hr0 : 0 < r := by linarith
  -- `N / J ≤ 2 N / r ≤ 3 S`
  have h1 : N / q1Count M ≤ 2 * N / r := by
    rw [div_le_div_iff₀ hJpos hr0]
    nlinarith
  have h2 : 2 * N ≤ 3 * S * r := by
    have : 128 * L ^ 2 ≤ (M : ℝ) / 2 := by nlinarith
    nlinarith
  have h3 : 2 * N / r ≤ 3 * S := by
    rw [div_le_iff₀ hr0]
    linarith
  nlinarith

/-- **The window stays below the merger budget** (L42): for `c_min ≥ 0`, eventually
`32 m² + J w ≤ T = ⌊⌊√(M m²)⌋ / 10⁶⌋`.

Proof sketch: by `q1_window_scale`-type estimates the left side is at most `(c_min + 3) √(nL)`,
while `T ≥ m √M / 10⁶ - 2` (`Nat.sqrt` floor, `mergerBudget_eq_floor`) and `m ≥ L - 1`; the
quotient `(L - 1) √M / (10⁶ (c_min + 3) √(2 M L)) → ∞` because `L → ∞`.
Reference: tex 2200-2203 ("In particular, `t_i < T` for all sufficiently large `n`"),
blueprint L42. -/
theorem q1_window_budget (cmin : ℝ) (hcmin : 0 ≤ cmin) :
    ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
      32 * headerLog M ^ 2 + q1Count M * q1Width cmin M ≤ mergerBudget M (headerLog M ^ 2) := by
  obtain ⟨M₀, hM₀⟩ := q1Log_pow_le ((520 * 10 ^ 6) ^ 2)
  have h2M : Tendsto (fun M : ℕ => ((2 * M : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun M => show M ≤ 2 * M by omega) tendsto_id)
  have hLt : Tendsto q1Log atTop atTop := (Real.tendsto_logb_atTop one_lt_two).comp h2M
  set B : ℝ := 8 * 10 ^ 6 * (cmin + 2) with hB
  obtain ⟨M₂, hM₂⟩ := eventually_atTop.mp (hLt.eventually (eventually_ge_atTop (B ^ 2 + 4)))
  refine ⟨max (max M₀ M₂) 2, fun M hM => ?_⟩
  have hM2 : 2 ≤ M := le_of_max_le_right hM
  have hMM₀ : M₀ ≤ M := le_trans (le_max_left _ _) (le_of_max_le_left hM)
  have hMM₂ : M₂ ≤ M := le_trans (le_max_right _ _) (le_of_max_le_left hM)
  obtain ⟨hL1, hL2, hLm⟩ := q1Log_facts (by omega : 1 ≤ M)
  have hmL := headerLog_le_q1Log hM2
  have hpoly := hM₀ M hMM₀
  have hLbig := hM₂ M hMM₂
  have hT := mergerBudget_sq_ge M
  obtain ⟨hJS, hJle⟩ := q1_sqrt_div_facts hL1
  set L := q1Log M with hL
  set S := q1Scale M with hS
  set r := Real.sqrt (((2 * M : ℕ) : ℝ) / L) with hr
  set m : ℝ := (headerLog M : ℝ) with hm
  have hJ : (q1Count M : ℝ) ≤ r := Nat.floor_le (Real.sqrt_nonneg _)
  have hw : (q1Width cmin M : ℝ) ≤ cmin * L + 2 := by
    unfold q1Width
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ cmin * L)
    push_cast
    linarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hJw : (q1Count M : ℝ) * q1Width cmin M ≤ (cmin + 2) * S := by
    have h1 : (q1Count M : ℝ) * q1Width cmin M ≤ r * (cmin * L + 2) :=
      mul_le_mul hJ hw (Nat.cast_nonneg _) hr0
    nlinarith
  have hm2 : m ^ 2 ≤ 4 * L ^ 2 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  -- `S = √2 √M √L`, with `t = √M` and `s = √L`
  set t := Real.sqrt (M : ℝ) with ht
  set s := Real.sqrt L with hsdef
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have ht1 : 1 ≤ t := by
    rw [ht, Real.le_sqrt (by norm_num) (by positivity)]
    simpa using hM1
  have htt : t * t = M := Real.mul_self_sqrt (by positivity)
  have hss : s * s = L := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hSst : S ≤ 2 * t * s := by
    have e : S = Real.sqrt 2 * t * s := by
      rw [hS, q1Scale, ← hL, ht, hsdef]
      push_cast
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
    have h2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    rw [e]
    have : 0 ≤ t * s := by positivity
    nlinarith
  have hsB : B ≤ s := by
    rw [hsdef, Real.le_sqrt (by positivity) (by linarith)]
    linarith
  -- the three estimates
  have hB0 : 0 ≤ B := by positivity
  have e1 : (cmin + 2) * S ≤ L * t / (4 * 10 ^ 6) := by
    have h1 : (cmin + 2) * S ≤ (cmin + 2) * (2 * t * s) :=
      mul_le_mul_of_nonneg_left hSst (by linarith)
    have h2 : (cmin + 2) * (2 * t * s) = B * t * s / (4 * 10 ^ 6) := by rw [hB]; ring
    have h3 : B * (t * s) ≤ s * (t * s) := mul_le_mul_of_nonneg_right hsB (by positivity)
    rw [← hss]
    have h4 : B * t * s / (4 * 10 ^ 6) ≤ s * s * t / (4 * 10 ^ 6) := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith
    linarith
  have hL21 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
  have hL23 : L ^ 2 ≤ L ^ 3 := by
    calc L ^ 2 = L ^ 2 * 1 := (mul_one _).symm
      _ ≤ L ^ 2 * L := mul_le_mul_of_nonneg_left hL1 (by positivity)
      _ = L ^ 3 := by ring
  have e2 : 128 * L ^ 2 + 2 ≤ L * t / (4 * 10 ^ 6) := by
    have h2 : 520 * 10 ^ 6 * L ^ 2 ≤ t := by
      rw [ht, Real.le_sqrt (by positivity) (by positivity)]
      calc (520 * 10 ^ 6 * L ^ 2 : ℝ) ^ 2 = (520 * 10 ^ 6) ^ 2 * L ^ 4 := by ring
        _ ≤ (M : ℝ) := hpoly
    have h3 : L * (520 * 10 ^ 6 * L ^ 2) ≤ L * t := mul_le_mul_of_nonneg_left h2 (by linarith)
    rw [le_div_iff₀ (by norm_num)]
    have h5 : L * (520 * 10 ^ 6 * L ^ 2) = 520 * 10 ^ 6 * L ^ 3 := by ring
    linarith
  have hB16 : 16 * 10 ^ 6 ≤ B := by
    rw [hB]
    nlinarith
  have hBsq : (16 * 10 ^ 6 : ℝ) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (by norm_num) hB16 2
  have e3 : L * t / (2 * 10 ^ 6) ≤ (m * t - 1) / 10 ^ 6 - 1 := by
    have h1 : (L - 1) * t ≤ m * t := mul_le_mul_of_nonneg_right hLm (by linarith)
    have hL2big : 2 * 10 ^ 6 + 2 ≤ L - 2 := by nlinarith
    have h2 : (L - 2) * 1 ≤ (L - 2) * t := mul_le_mul_of_nonneg_left ht1 (by linarith)
    rw [div_sub_one (by norm_num), div_le_div_iff₀ (by norm_num) (by norm_num)]
    have e4 : (L - 1) * t = L * t - t := by ring
    have e5 : (L - 2) * t = L * t - 2 * t := by ring
    linarith
  have hfinal : (32 : ℝ) * m ^ 2 + (q1Count M : ℝ) * q1Width cmin M ≤
      mergerBudget M (headerLog M ^ 2) := by
    have : L * t / (4 * 10 ^ 6) + L * t / (4 * 10 ^ 6) = L * t / (2 * 10 ^ 6) := by ring
    linarith
  rw [hm] at hfinal
  exact_mod_cast hfinal

/-- **The window parameters** (L42): the conjunction of `q1_count_pos`, `q1_window_scale`,
`q1_window_drop` and `q1_window_budget` beyond one common cutoff. -/
theorem q1_window (cmin : ℝ) (hcmin : 0 ≤ cmin) (b : ℕ) :
    ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M → 1 ≤ q1Count M ∧
      ((32 * headerLog M ^ 2 + q1Count M * q1Width cmin M : ℕ) : ℝ) ≤ (cmin + 4) * q1Scale M ∧
      ((2 * M + b + 32 * headerLog M ^ 2 : ℕ) : ℝ) / q1Count M + 1 ≤ (cmin + 4) * q1Scale M ∧
      32 * headerLog M ^ 2 + q1Count M * q1Width cmin M ≤ mergerBudget M (headerLog M ^ 2) := by
  obtain ⟨M₁, h₁⟩ := q1_count_pos
  obtain ⟨M₂, h₂⟩ := q1_window_scale cmin hcmin
  obtain ⟨M₃, h₃⟩ := q1_window_drop cmin hcmin b
  obtain ⟨M₄, h₄⟩ := q1_window_budget cmin hcmin
  refine ⟨max (max M₁ M₂) (max M₃ M₄), fun M hM => ⟨h₁ M ?_, h₂ M ?_, h₃ M ?_, h₄ M ?_⟩⟩ <;>
    omega

/-- **The ratio diverges** (L42): for `K > 0`,
`T / (2 K √(n L) + L) → ∞` as `M → ∞`, with `T = ⌊⌊√(M m²)⌋ / 10⁶⌋`, `n = 2M`, `L = log₂ n`.

Proof sketch: `T ≥ √M m / (2 · 10⁶) - 1` and `m ≥ log₂ (M + 2) ≥ L - 1`, while
`2K √(nL) + L ≤ 3K √(2 M L)` eventually; so the ratio is at least `√L / (c K) - o(1)`, and
`L → ∞` (`Real.tendsto_logb_atTop`); conclude with `Filter.tendsto_atTop_mono`.
Reference: tex 2219-2228 ("`Θ(√n log n) / O(√(n log n)) → ∞`"). -/
theorem q1_ratio_tendsto (K : ℝ) (hK : 0 < K) :
    Tendsto (fun M : ℕ => (mergerBudget M (headerLog M ^ 2) : ℝ) /
      (2 * K * q1Scale M + q1Log M)) atTop atTop := by
  set c₁ : ℝ := 10 ^ 6 * (2 * K + 1) * Real.sqrt 2 with hc₁
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hc₁pos : 0 < c₁ := by positivity
  have h2M : Tendsto (fun M : ℕ => ((2 * M : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun M => show M ≤ 2 * M by omega) tendsto_id)
  have hL : Tendsto q1Log atTop atTop := (Real.tendsto_logb_atTop one_lt_two).comp h2M
  have hsL : Tendsto (fun M : ℕ => Real.sqrt (q1Log M)) atTop atTop := by
    have := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hL
    refine this.congr' ?_
    filter_upwards [hL.eventually (eventually_ge_atTop 0)] with M hM
    simp [Function.comp, Real.sqrt_eq_rpow]
  have hg : Tendsto (fun M : ℕ => (Real.sqrt (q1Log M) - 1) / c₁ - 1) atTop atTop := by
    have h1 := tendsto_atTop_add_const_right atTop (-1) hsL
    have h2 := h1.atTop_div_const hc₁pos
    have h3 := tendsto_atTop_add_const_right atTop (-1) h2
    simpa [sub_eq_add_neg] using h3
  refine tendsto_atTop_mono' atTop ?_ hg
  filter_upwards [eventually_ge_atTop 1] with M hM
  obtain ⟨hL1, hL2, hLm⟩ := q1Log_facts hM
  have hT := mergerBudget_sq_ge M
  set L := q1Log M with hLdef
  set m : ℝ := (headerLog M : ℝ) with hm
  set T : ℝ := (mergerBudget M (headerLog M ^ 2) : ℝ) with hTdef
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hsM : 1 ≤ Real.sqrt (M : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    simpa using hM1
  have hsL1 : 1 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    simpa using hL1
  have hsLsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
  have hS : q1Scale M = Real.sqrt 2 * Real.sqrt M * Real.sqrt L := by
    unfold q1Scale
    rw [← hLdef]
    push_cast
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  have hLS : L ≤ q1Scale M := by
    rw [hS]
    have h1 : Real.sqrt L ≤ Real.sqrt 2 * Real.sqrt M := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by push_cast at hL2; linarith)
    nlinarith [Real.sqrt_nonneg L]
  set D := 2 * K * q1Scale M + L with hD
  have hDpos : 0 < D := by
    have : 0 ≤ q1Scale M := Real.sqrt_nonneg _
    rw [hD]
    nlinarith
  have hDle : D ≤ (2 * K + 1) * (Real.sqrt 2 * Real.sqrt M * Real.sqrt L) := by
    rw [hD, ← hS]
    nlinarith
  have hP : 0 < Real.sqrt 2 * Real.sqrt M * Real.sqrt L := by positivity
  -- the ratio bound
  rw [le_div_iff₀ hDpos]
  set P := (2 * K + 1) * (Real.sqrt 2 * Real.sqrt M * Real.sqrt L) with hPdef
  have hs2' : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hK1 : (1 : ℝ) ≤ 2 * K + 1 := by linarith
  have a2 : (1.4 : ℝ) ≤ (2 * K + 1) * Real.sqrt 2 := by nlinarith
  have a3 : (1.4 : ℝ) ≤ (2 * K + 1) * Real.sqrt 2 * Real.sqrt M := by nlinarith
  have a4 : (1.4 : ℝ) ≤ P := by
    rw [hPdef]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (2 * K + 1) * Real.sqrt 2 * Real.sqrt M)
      (by linarith : (0 : ℝ) ≤ Real.sqrt L - 1)]
  have hPc : P / c₁ = Real.sqrt M * Real.sqrt L / 10 ^ 6 := by
    rw [hPdef, hc₁]
    field_simp
  have h1 : (Real.sqrt L - 1) * Real.sqrt L * Real.sqrt M ≤ m * Real.sqrt M := by
    have e : (Real.sqrt L - 1) * Real.sqrt L = L - Real.sqrt L := by
      rw [sub_mul, hsLsq, one_mul]
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hLm (Real.sqrt_nonneg (M : ℝ)), Real.sqrt_nonneg (M : ℝ)]
  have key : ((Real.sqrt L - 1) / c₁ - 1) * P ≤ (m * Real.sqrt M - 1) / 10 ^ 6 - 1 := by
    have e : ((Real.sqrt L - 1) / c₁ - 1) * P = (Real.sqrt L - 1) * (P / c₁) - P := by
      field_simp
    rw [e, hPc]
    have e2 : (Real.sqrt L - 1) * (Real.sqrt M * Real.sqrt L / 10 ^ 6) =
        (Real.sqrt L - 1) * Real.sqrt L * Real.sqrt M / 10 ^ 6 := by ring
    rw [e2]
    have : (Real.sqrt L - 1) * Real.sqrt L * Real.sqrt M / 10 ^ 6 ≤ m * Real.sqrt M / 10 ^ 6 :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have e3 : (m * Real.sqrt M - 1) / 10 ^ 6 = m * Real.sqrt M / 10 ^ 6 - 1 / 10 ^ 6 := by ring
    rw [e3]
    linarith
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  by_cases hg0 : 0 ≤ (Real.sqrt L - 1) / c₁ - 1
  · calc ((Real.sqrt L - 1) / c₁ - 1) * D ≤ ((Real.sqrt L - 1) / c₁ - 1) * P :=
          mul_le_mul_of_nonneg_left hDle hg0
      _ ≤ (m * Real.sqrt M - 1) / 10 ^ 6 - 1 := key
      _ ≤ T := hT
  · have : ((Real.sqrt L - 1) / c₁ - 1) * D ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hDpos.le
    linarith

/-- The logarithm `L = log₂ (2M)` is nonnegative. -/
theorem q1Log_nonneg (M : ℕ) : 0 ≤ q1Log M := by
  unfold q1Log
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h
    simp
  · exact Real.logb_nonneg one_lt_two (by exact_mod_cast (by omega : 1 ≤ 2 * M))

/-- **Node L42, `q1FormalCounterexample`, one dimension.**  For an optimal plain machine `V` and
`c_min ≥ 0` there are `K > 0`, a cutoff `M₁` and a function `g → ∞` such that for every
`M ≥ M₁` with `2048 ∣ M` there are a string `x` of length `n = 2M`, models `A, B` and reals
`ε, δ` with: `A, B` both `ε`-strong and `ε`-sufficient; `ε, δ ≤ K √(n log₂ n)`, `δ ≥ 1`; `A`
strong-only robustly minimal at tolerance `ε + c_min log₂ n` with gap `δ`; and
`CT(A | B) / (ε + δ + log₂ n) ≥ g M`.  The model `A` is the profile minimizer of L41 and `B` an
original star of the sharp theorem with `CT(A | B) > T`; the other star need not be close and
no minimality of `B` is claimed (this is not Question 2). -/
theorem q1FormalCounterexample (V : Map) (hV : isOptimalConditional V) (cmin : ℝ)
    (hcmin : 0 ≤ cmin) :
    ∃ (K : ℝ) (M₁ : ℕ) (g : ℕ → ℝ), 0 < K ∧ Tendsto g atTop atTop ∧
      ∀ M : ℕ, M₁ ≤ M → 2048 ∣ M → ∃ (x : BitString) (A B : Finset BitString) (ε δ : ℝ),
        x.length = 2 * M ∧
        (IsStrongModel x A ε ∧ IsSufficientModel V x A ε ∧
          IsStrongModel x B ε ∧ IsSufficientModel V x B ε) ∧
        (ε ≤ K * Real.sqrt (x.length * Real.logb 2 x.length) ∧
          δ ≤ K * Real.sqrt (x.length * Real.logb 2 x.length) ∧ 1 ≤ δ) ∧
        StrongRobustMin V x A (ε + cmin * Real.logb 2 x.length) δ ∧
        g M ≤ setTotalC A B / (ε + δ + Real.logb 2 x.length) := by
  obtain ⟨lam, cpt, M₀, hlam, h37⟩ := exists_strong_pair_without_common_model' V hV
  obtain ⟨blit, hblit⟩ := plainC_le_length_add V hV
  -- L42 (tex 2153-2158): `E = m²` is eventually admissible
  obtain ⟨Ma, hMa⟩ := headerLog_eventually lam cpt
  obtain ⟨Mw, hMw⟩ := q1_window cmin hcmin blit
  have hK : 0 < cmin + 4 := by linarith
  refine ⟨cmin + 4, max M₀ (max Ma Mw), _, hK, q1_ratio_tendsto (cmin + 4) hK,
    fun M hM hdiv => ?_⟩
  have hM0 : M₀ ≤ M := le_of_max_le_left hM
  have hMa' : Ma ≤ M := le_trans (le_max_left _ _) (le_of_max_le_right hM)
  have hMw' : Mw ≤ M := le_trans (le_max_right _ _) (le_of_max_le_right hM)
  obtain ⟨hadm1, hadm2, hcpt⟩ := hMa M hMa'
  obtain ⟨hJ, htJ, hdrop, htT⟩ := hMw M hMw'
  set m := headerLog M with hm
  set E := m ^ 2 with hE
  obtain ⟨x, A₀, B₀, hx, hptA, hptB, hsA, hsB, -, hno⟩ := h37 M hM0 hdiv E hadm1 hadm2
  set T := mergerBudget M E with hT
  set t₀ : ℝ := ((32 * E : ℕ) : ℝ) with ht₀
  set L := Real.logb 2 (x.length : ℝ) with hL
  have hLq : L = q1Log M := by rw [hL, hx]; rfl
  have hL0 : 0 ≤ L := hLq ▸ q1Log_nonneg M
  have hcpt' : (cpt : ℝ) ≤ t₀ := by rw [ht₀]; exact_mod_cast hcpt
  have hadmA₀ : ProfileAdmissible V x t₀ A₀ :=
    ⟨le_trans hptA hcpt', hsA.1, by rw [ht₀]; push_cast; exact hsA.2⟩
  have hadmB₀ : ProfileAdmissible V x t₀ B₀ :=
    ⟨le_trans hptB hcpt', hsB.1, by rw [ht₀]; push_cast; exact hsB.2⟩
  -- L41 along the window
  set w := q1Width cmin M with hw
  set J := q1Count M with hJdef
  have hs : cmin * L ≤ (w : ℝ) := by
    rw [hw, q1Width, hLq]
    push_cast
    linarith [Nat.le_ceil (cmin * q1Log M)]
  obtain ⟨i, hi, F, dr, hF, hJdr, hmin⟩ :=
    stableProfileWindow V x t₀ A₀ hadmA₀ w J hJ (cmin * L) hs
  set ε : ℝ := t₀ + i * w with hε
  -- the bounds on `ε` and `δ = dr + 1`
  have hiJ : (i : ℝ) * w ≤ J * w := by
    have : (i : ℝ) ≤ J := by exact_mod_cast hi.le
    nlinarith [(Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
  have htJ' : t₀ + (J : ℝ) * w ≤ (cmin + 4) * q1Scale M := by
    rw [ht₀]
    push_cast at htJ ⊢
    linarith
  have hscale : q1Scale M = Real.sqrt (x.length * Real.logb 2 x.length) := by
    rw [q1Scale, hx]
    rfl
  have hprof : (strongProfile V x t₀ : ℝ) ≤ 2 * M + blit + 32 * E := by
    have h1 := strongProfile_le hadmA₀
    have h2 := hsA.2
    have h3 := hblit x
    have h4 : 0 ≤ Real.logb 2 A₀.card :=
      Real.logb_nonneg one_lt_two (by exact_mod_cast card_pos.2 ⟨x, hsA.1⟩)
    rw [hx] at h3
    push_cast at h2 h3 ⊢
    linarith
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hdr : (dr : ℝ) + 1 ≤ (cmin + 4) * q1Scale M := by
    have h1 : (J : ℝ) * dr ≤ strongProfile V x t₀ := by exact_mod_cast hJdr
    have h2 : (dr : ℝ) ≤ (2 * M + blit + 32 * E) / J := by
      rw [le_div_iff₀ hJpos]
      linarith
    push_cast at hdrop
    linarith
  -- one original star is far from the minimizer
  have htT' : ε ≤ T := by
    have : ((32 * E + J * w : ℕ) : ℝ) ≤ T := by exact_mod_cast htT
    push_cast at this
    rw [hε, ht₀]
    push_cast
    linarith
  have hfar : T < setTotalC F A₀ ∨ T < setTotalC F B₀ := by
    by_contra hclose
    simp only [not_or, not_lt] at hclose
    apply hno F hF.2.1
    exact ⟨by linarith [hF.2.2], hclose.1, hclose.2⟩
  have hδ1 : (1 : ℝ) ≤ dr + 1 := by linarith [(Nat.cast_nonneg dr : (0 : ℝ) ≤ dr)]
  have hε0 : 0 ≤ ε := le_trans (totalC_nonneg _ _) hF.1
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  -- the ratio bound, common to both choices of the far star
  have hratio : ∀ B : Finset BitString, (T : ℝ) < setTotalC F B →
      (T : ℝ) / (2 * (cmin + 4) * q1Scale M + q1Log M) ≤
        setTotalC F B / (ε + (dr + 1) + Real.logb 2 x.length) := by
    intro B hB
    have hden : 0 < ε + (dr + 1) + Real.logb 2 x.length := by linarith
    have hden' : ε + (dr + 1) + Real.logb 2 x.length ≤
        2 * (cmin + 4) * q1Scale M + q1Log M := by
      rw [← hLq]
      linarith
    calc (T : ℝ) / (2 * (cmin + 4) * q1Scale M + q1Log M)
        ≤ T / (ε + (dr + 1) + Real.logb 2 x.length) :=
          div_le_div_of_nonneg_left hT0 hden hden'
      _ ≤ setTotalC F B / (ε + (dr + 1) + Real.logb 2 x.length) :=
          div_le_div_of_nonneg_right hB.le hden.le
  have hBadm : ∀ B : Finset BitString, ProfileAdmissible V x t₀ B →
      IsStrongModel x B ε ∧ IsSufficientModel V x B ε := fun B hB => by
    have h := hB.mono (show t₀ ≤ ε by
      rw [hε]
      nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg w : (0 : ℝ) ≤ w)])
    exact ⟨h.1, h.2⟩
  have hεK : ε ≤ (cmin + 4) * Real.sqrt (x.length * Real.logb 2 x.length) := by
    rw [← hscale]
    linarith
  have hδK : (dr : ℝ) + 1 ≤ (cmin + 4) * Real.sqrt (x.length * Real.logb 2 x.length) := by
    rw [← hscale]
    exact hdr
  rcases hfar with hfarA | hfarB
  · exact ⟨x, F, A₀, ε, dr + 1, hx, ⟨hF.1, hF.2, hBadm A₀ hadmA₀⟩, ⟨hεK, hδK, hδ1⟩,
      by rw [hε]; exact hmin, hratio A₀ hfarA⟩
  · exact ⟨x, F, B₀, ε, dr + 1, hx, ⟨hF.1, hF.2, hBadm B₀ hadmB₀⟩, ⟨hεK, hδK, hδ1⟩,
      by rw [hε]; exact hmin, hratio B₀ hfarB⟩

/-- **The formal Question 1, sequence form** (node L42): verbatim the frozen statement
`exists_strongRobustMin_seq_unbounded_ratio` of `StrongMerging.Statements`. -/
theorem exists_strongRobustMin_seq_unbounded_ratio' (V : Map) (hV : isOptimalConditional V)
    (cmin : ℝ) (hcmin : 0 ≤ cmin) :
    ∃ (x : ℕ → BitString) (A B : ℕ → Finset BitString) (ε δ : ℕ → ℝ) (K : ℝ),
      Tendsto (fun j => (x j).length) atTop atTop ∧
      (∀ j, IsStrongModel (x j) (A j) (ε j) ∧ IsSufficientModel V (x j) (A j) (ε j) ∧
        IsStrongModel (x j) (B j) (ε j) ∧ IsSufficientModel V (x j) (B j) (ε j)) ∧
      (∀ j, ε j ≤ K * Real.sqrt ((x j).length * Real.logb 2 (x j).length) ∧
        δ j ≤ K * Real.sqrt ((x j).length * Real.logb 2 (x j).length) ∧ 1 ≤ δ j) ∧
      (∀ j, StrongRobustMin V (x j) (A j) (ε j + cmin * Real.logb 2 (x j).length) (δ j)) ∧
      Tendsto (fun j => setTotalC (A j) (B j) / (ε j + δ j + Real.logb 2 (x j).length))
        atTop atTop := by
  obtain ⟨K, M₁, g, -, hg, hinst⟩ := q1FormalCounterexample V hV cmin hcmin
  have hMj : ∀ j : ℕ, M₁ ≤ 2048 * (j + M₁) ∧ 2048 ∣ 2048 * (j + M₁) :=
    fun j => ⟨by omega, dvd_mul_right _ _⟩
  choose x A B ε δ hx hmod hpar hmin hrat using
    fun j => hinst (2048 * (j + M₁)) (hMj j).1 (hMj j).2
  have hM : Tendsto (fun j : ℕ => 2048 * (j + M₁)) atTop atTop :=
    tendsto_atTop_mono (fun j => show j ≤ 2048 * (j + M₁) by omega) tendsto_id
  refine ⟨x, A, B, ε, δ, K, ?_, hmod, hpar, hmin, ?_⟩
  · have : (fun j => (x j).length) = fun j => 2 * (2048 * (j + M₁)) := funext hx
    rw [this]
    exact tendsto_atTop_mono (fun j => by omega) hM
  · exact tendsto_atTop_mono hrat (hg.comp hM)

/-- **The formal Question 1 has a negative answer** (node L42, concluding sentence of
`cor:q1-negative`): verbatim the frozen statement `not_exists_strongRobustMin_total_bound` of
`StrongMerging.Statements`. -/
theorem not_exists_strongRobustMin_total_bound' (V : Map) (hV : isOptimalConditional V) :
    ¬ ∃ cmin Kout c₀ : ℝ, 0 ≤ cmin ∧ 0 ≤ Kout ∧
      ∀ (ε δ : ℝ) (x : BitString) (A B : Finset BitString), 0 ≤ ε → 1 ≤ δ → 2 ≤ x.length →
      IsStrongModel x A ε → IsSufficientModel V x A ε →
      IsStrongModel x B ε → IsSufficientModel V x B ε →
      StrongRobustMin V x A (ε + cmin * Real.logb 2 x.length) δ →
        setTotalC A B ≤ Kout * (ε + δ + Real.logb 2 x.length) + c₀ := by
  rintro ⟨cmin, Kout, c₀, hcmin, hKout, hbound⟩
  obtain ⟨x, A, B, ε, δ, K, hlen, hmod, hpar, hmin, hratio⟩ :=
    exists_strongRobustMin_seq_unbounded_ratio' V hV cmin hcmin
  have h1 := hlen.eventually (eventually_ge_atTop 2)
  have h2 := hratio.eventually (eventually_gt_atTop (Kout + |c₀| + 1))
  obtain ⟨j, hj1, hj2⟩ := (h1.and h2).exists
  have hε : 0 ≤ ε j := le_trans (totalC_nonneg _ _) (hmod j).1
  have hδ : 1 ≤ δ j := (hpar j).2.2
  have hL : 0 ≤ Real.logb 2 (x j).length :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast le_trans one_le_two hj1)
  have hden : 0 < ε j + δ j + Real.logb 2 (x j).length := by linarith
  have hb := hbound (ε j) (δ j) (x j) (A j) (B j) hε hδ hj1 (hmod j).1 (hmod j).2.1
    (hmod j).2.2.1 (hmod j).2.2.2 (hmin j)
  rw [lt_div_iff₀ hden] at hj2
  nlinarith [abs_nonneg c₀, le_abs_self c₀]

end Kolmogorov.StrongMerging.Lower
