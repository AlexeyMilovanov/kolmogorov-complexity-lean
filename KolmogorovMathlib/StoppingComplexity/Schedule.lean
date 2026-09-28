import KolmogorovMathlib.StoppingComplexity.Game
import KolmogorovMathlib.StoppingComplexity.CeilLog

/-!
# The common increasing schedule and its exact budget estimates

Blueprint 04 §3 ("The common increasing schedule and exact budget estimates") together with
the schedule inequality R1 and the divergence predicate DIV of §4.  The exponents are

  `E_0 = 16`,  `g_i = 2 L (i + 1) + 3`,  `E_j = 16 + Σ_{i=1}^{j} g_i`

(item `04-SCHED`), and for a nondecreasing discount `f` and an additive parameter `c` the
variable schedule `δ_j = E_j + f (E_j) + c` is packaged as a `GameSchedule` (Interface
GAME-VARIABLE).  We state the growth facts S1–S2 (`04-S1`, `04-S2`), the dyadic-loss sums S3
(`04-S3`), the budget bounds B1 (`04-B1`), the schedule inequality `SatisfiesR1` (`04-DEF-R1`),
the threshold bound T1 (`04-T1`), and the partial sums `discountSums` with the predicate
`HasDivergentSums` (`04-DEF-DIV`), which both `Divergence` and `AdmissibleDiscount` use.
All sums are finite rational sums; no real number appears.
-/

namespace Kolmogorov

/-- The step `g_i = 2 L (i + 1) + 3` of the common schedule (`L = Nat.clog 2`).
Blueprint 04 Definition SCHEDULE (`04-SCHED`). -/
def stepSize (i : ℕ) : ℕ := 2 * Nat.clog 2 (i + 1) + 3

/-- The exponents `E_0 = 16`, `E_j = E_{j-1} + g_j`, i.e. `E_j = 16 + Σ_{i=1}^{j} g_i`.
Blueprint 04 Definition SCHEDULE (`04-SCHED`). -/
def expSchedule : ℕ → ℕ
  | 0 => 16
  | j + 1 => expSchedule j + stepSize (j + 1)

/-- The variable schedule of Interface GAME-VARIABLE for the discount `f`, the additive
parameter `c` and the horizon `R`: Alice exponents `E_0 < … < E_R` from `expSchedule` and Bob
depths `δ_j = E_j + f (E_j) + c`.  Blueprint 04 Definition SCHEDULE / Interface GAME-VARIABLE
(`04-SCHED`). -/
def variableSchedule (f : ℕ → ℕ) (c R : ℕ) : GameSchedule :=
  ⟨(List.range (R + 1)).map expSchedule,
    (List.range (R + 1)).map fun j => expSchedule j + f (expSchedule j) + c⟩

/-- Every step after the first is at least five (`L (j + 2) ≥ 1`), so `E_j + 5 ≤ E_{j+1}`. -/
private theorem expSchedule_add_five_le (j : ℕ) : expSchedule j + 5 ≤ expSchedule (j + 1) := by
  have h := Nat.clog_pos (b := 2) (n := j + 1 + 1) (by norm_num) (by omega)
  simp only [expSchedule, stepSize]
  omega

/-- The top level of the variable schedule is its horizon `R`. -/
private theorem variableSchedule_R (f : ℕ → ℕ) (c R : ℕ) : (variableSchedule f c R).R = R := by
  simp [GameSchedule.R, variableSchedule]

/-- Up to the horizon, the exponents of the variable schedule are the common exponents `E_j`. -/
private theorem variableSchedule_exp {f : ℕ → ℕ} {c R j : ℕ} (hj : j ≤ R) :
    (variableSchedule f c R).exp j = expSchedule j := by
  simp [GameSchedule.exp, variableSchedule, Nat.lt_succ_of_le hj]

/-- Up to the horizon, the depths of the variable schedule are `δ_j = E_j + f (E_j) + c`. -/
private theorem variableSchedule_depth {f : ℕ → ℕ} {c R j : ℕ} (hj : j ≤ R) :
    (variableSchedule f c R).depth j = expSchedule j + f (expSchedule j) + c := by
  simp [GameSchedule.depth, variableSchedule, Nat.lt_succ_of_le hj]

/-- For a nondecreasing `f` the variable schedule is a valid game schedule: equal lengths,
strictly increasing exponents and depths, `E_0 ≥ 1`.  Blueprint 04 Definition SCHEDULE /
Interface GAME-VARIABLE (`04-SCHED`). -/
theorem variableSchedule_isValid {f : ℕ → ℕ} (hf : Monotone f) (c R : ℕ) :
    (variableSchedule f c R).IsValid := by
  have hE : StrictMono expSchedule :=
    strictMono_nat_of_lt_succ fun j => by have := expSchedule_add_five_le j; omega
  refine ⟨by simp [variableSchedule], by simp [variableSchedule], ?_, ?_, ?_⟩
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp fun h => hE h)
  · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp fun h => ?_)
    have h1 := hE h
    have h2 := hf h1.le
    omega
  · rw [variableSchedule_exp (Nat.zero_le R)]
    simp [expSchedule]

/-- The exponent schedule `j ↦ E_j` is primitive recursive (a primitive recursion whose step
adds `g_{j+1} = 2 L (j + 2) + 3`). -/
private theorem primrec_expSchedule : Primrec expSchedule := by
  have hstep : Primrec stepSize :=
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (primrec_clogTwo.comp Primrec.succ)) (Primrec.const 3)).of_eq fun _ => rfl
  have hg : Primrec₂ fun (j e : ℕ) => e + stepSize (j + 1) :=
    (Primrec.nat_add.comp Primrec.snd (hstep.comp (Primrec.succ.comp Primrec.fst))).to₂
  refine (Primrec.nat_rec₁ 16 hg).of_eq fun j => ?_
  induction j with
  | zero => rfl
  | succ j ih => rw [expSchedule, ← ih]

/-- The variable schedule is a computable function of `(c, R)` whenever `f` is computable
(uniformity "in the finite rational data and a program for `f`").  Blueprint 04 Definition
SCHEDULE / Interface GAME-VARIABLE (`04-SCHED`). -/
theorem variableSchedule_computable {f : ℕ → ℕ} (hf : Computable f) :
    Computable fun a : ℕ × ℕ => variableSchedule f a.1 a.2 := by
  have hE := primrec_expSchedule.to_comp
  have hrange : Computable fun a : ℕ × ℕ => List.range (a.2 + 1) :=
    Primrec.list_range.to_comp.comp (Computable.succ.comp Computable.snd)
  have hexps : Computable fun a : ℕ × ℕ => (List.range (a.2 + 1)).map expSchedule :=
    Computable.list_map hrange (hE.comp Computable.snd).to₂
  have hdepth : Computable fun p : (ℕ × ℕ) × ℕ =>
      expSchedule p.2 + f (expSchedule p.2) + p.1.1 :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp (hE.comp Computable.snd) (hf.comp (hE.comp Computable.snd)))
      (Computable.fst.comp Computable.fst)
  have hdepths : Computable fun a : ℕ × ℕ =>
      (List.range (a.2 + 1)).map fun j => expSchedule j + f (expSchedule j) + a.1 :=
    Computable.list_map hrange hdepth.to₂
  exact ((Primrec.of_equiv_symm (e := GameSchedule.equivProd)).to_comp.comp
    (hexps.pair hdepths)).of_eq fun _ => rfl

/-- S1, growth: `E_j ≥ 16 + 5 j` (each step is at least `5`).
Blueprint 04 (S1) (`04-S1`). -/
theorem expSchedule_ge (j : ℕ) : 16 + 5 * j ≤ expSchedule j := by
  induction j with
  | zero => simp [expSchedule]
  | succ j ih =>
    have := expSchedule_add_five_le j
    omega

/-- S1, strict increase: `E_j > E_{j-1}`, i.e. `expSchedule` is strictly monotone.
Blueprint 04 (S1) (`04-S1`). -/
theorem expSchedule_strictMono : StrictMono expSchedule :=
  strictMono_nat_of_lt_succ fun j => by have := expSchedule_add_five_le j; omega

/-- S2, first half: `g_j ≤ E_{j-1}` for every `j ≥ 1` (from L5 and S1).
Blueprint 04 (S2) (`04-S2`). -/
theorem stepSize_le_expSchedule_pred {j : ℕ} (hj : 1 ≤ j) : stepSize j ≤ expSchedule (j - 1) := by
  have h1 := clogTwo_succ_le_self hj
  have h2 := expSchedule_ge (j - 1)
  unfold stepSize
  omega

/-- S2, second half: `E_j ≤ 2 E_{j-1}` for every `j ≥ 1`.
Blueprint 04 (S2) (`04-S2`). -/
theorem expSchedule_le_two_mul_pred {j : ℕ} (hj : 1 ≤ j) :
    expSchedule j ≤ 2 * expSchedule (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have h := stepSize_le_expSchedule_pred hj
  simp only [Nat.add_sub_cancel] at h ⊢
  rw [expSchedule]
  omega

/-- Closed form of the first dyadic loss: with `K = L (R + 1)` and `x = 2^{-K}`,
`Σ_{i=1}^{R} 2^{-g_i} = 1/16 - (3/16) x + ((R + 1)/8) x²`.  The summands are constant on the
dyadic blocks `2^{k-1} < i + 1 ≤ 2^k`, which is what makes the closed form exact. -/
private theorem sum_stepSize_loss_eq (R : ℕ) :
    ∑ i ∈ Finset.Icc 1 R, (1 / 2 : ℚ) ^ stepSize i =
      1 / 16 - 3 / 16 * (1 / 2) ^ Nat.clog 2 (R + 1) +
        (R + 1) / 8 * ((1 / 2) ^ Nat.clog 2 (R + 1)) ^ 2 := by
  induction R with
  | zero => norm_num
  | succ R ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hstep : (1 / 2 : ℚ) ^ stepSize (R + 1) =
        1 / 8 * ((1 / 2) ^ Nat.clog 2 (R + 1 + 1)) ^ 2 := by
      rw [stepSize]
      ring
    rw [hstep]
    have hmono : Nat.clog 2 (R + 1) ≤ Nat.clog 2 (R + 1 + 1) := Nat.clog_mono_right 2 (by omega)
    rcases Nat.lt_or_ge (Nat.clog 2 (R + 1)) (Nat.clog 2 (R + 1 + 1)) with hlt | hge
    · have hpow : 2 ^ Nat.clog 2 (R + 1) = R + 1 :=
        (Nat.clog_lt_clog_succ_iff (by norm_num)).mp hlt
      have hsucc : Nat.clog 2 (R + 1 + 1) = Nat.clog 2 (R + 1) + 1 :=
        le_antisymm (clogTwo_succ_le _) hlt
      rw [hsucc]
      have hx : ((R : ℚ) + 1) * (1 / 2) ^ Nat.clog 2 (R + 1) = 1 := by
        have h2 : ((2 : ℚ) ^ Nat.clog 2 (R + 1)) = (R : ℚ) + 1 := by exact_mod_cast hpow
        rw [← h2, ← mul_pow]
        norm_num
      push_cast
      linear_combination (3 / 32 * (1 / 2 : ℚ) ^ Nat.clog 2 (R + 1)) * hx
    · rw [le_antisymm hge hmono]
      push_cast
      ring

/-- S-dyadic-loss, first bound: `Σ_{i=1}^{R} 2^{-g_i} ≤ 1 / 16` for every finite `R`
(dyadic grouping by `k = L (i + 1)`).  Blueprint 04 Lemma S-dyadic-loss (S3) (`04-S3`). -/
theorem sum_stepSize_loss_le (R : ℕ) :
    ∑ i ∈ Finset.Icc 1 R, (1 / 2 : ℚ) ^ stepSize i ≤ 1 / 16 := by
  rw [sum_stepSize_loss_eq]
  have hR : ((R : ℚ) + 1) ≤ 2 ^ Nat.clog 2 (R + 1) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) (R + 1)
  have hx : (0 : ℚ) < (1 / 2) ^ Nat.clog 2 (R + 1) := by positivity
  have hx1 : ((R : ℚ) + 1) * (1 / 2) ^ Nat.clog 2 (R + 1) ≤ 1 := by
    calc ((R : ℚ) + 1) * (1 / 2) ^ Nat.clog 2 (R + 1)
        ≤ 2 ^ Nat.clog 2 (R + 1) * (1 / 2) ^ Nat.clog 2 (R + 1) :=
          mul_le_mul_of_nonneg_right hR hx.le
      _ = 1 := by rw [← mul_pow]; norm_num
  have hx2 := mul_le_mul_of_nonneg_right hx1 hx.le
  nlinarith

/-- S-dyadic-loss, second bound: `Σ_{i=1}^{R} 2^{-E_i} ≤ 1 / 65536` for every finite `R`
(from `E_i ≥ 16 + i`).  Blueprint 04 Lemma S-dyadic-loss (S3) (`04-S3`). -/
theorem sum_expSchedule_loss_le (R : ℕ) :
    ∑ i ∈ Finset.Icc 1 R, (1 / 2 : ℚ) ^ expSchedule i ≤ 1 / 65536 := by
  have key : ∀ R : ℕ, ∑ i ∈ Finset.Icc 1 R, (1 / 2 : ℚ) ^ expSchedule i ≤
      1 / 65536 * (1 - (1 / 2) ^ R) := by
    intro R
    induction R with
    | zero => simp
    | succ R ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hE : 16 + (R + 1) ≤ expSchedule (R + 1) := by
        have := expSchedule_ge (R + 1)
        omega
      have h1 : (1 / 2 : ℚ) ^ expSchedule (R + 1) ≤ (1 / 2) ^ (16 + (R + 1)) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hE
      have h2 : (1 / 2 : ℚ) ^ (16 + (R + 1)) = 1 / 65536 * ((1 / 2) ^ R * (1 / 2)) := by ring
      rw [pow_succ]
      linarith
  have h0 : (0 : ℚ) ≤ (1 / 2) ^ R := by positivity
  have := key R
  linarith

/-- The loss factor `1 / L_i = 2^{-(δ_i - δ_{i-1})}` of the variable schedule is at most
`2^{-g_i}`, because `γ_i = g_i + f (E_i) - f (E_{i-1}) ≥ g_i` for a nondecreasing `f`. -/
private theorem variableSchedule_inv_ratio_le {f : ℕ → ℕ} (hf : Monotone f) {c R k : ℕ}
    (hk : k < R) :
    1 / ((variableSchedule f c R).ratio (k + 1) : ℚ) ≤ (1 / 2) ^ stepSize (k + 1) := by
  have hd := variableSchedule_depth (f := f) (c := c) (j := k + 1) hk
  have hd' := variableSchedule_depth (f := f) (c := c) hk.le
  have hmono : f (expSchedule k) ≤ f (expSchedule (k + 1)) :=
    hf (expSchedule_strictMono.monotone (by omega))
  have hE : expSchedule (k + 1) = expSchedule k + stepSize (k + 1) := rfl
  have hge : stepSize (k + 1) ≤
      (variableSchedule f c R).depth (k + 1) - (variableSchedule f c R).depth (k + 1 - 1) := by
    rw [Nat.add_sub_cancel, hd, hd']
    omega
  rw [GameSchedule.ratio]
  push_cast
  rw [← one_div_pow]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hge

/-- B-budget: for a nondecreasing `f`, every backwards budget of the variable schedule
satisfies `7 / 8 ≤ B_j ≤ 1` and `B_j - 2^{-E_j} ≥ 3 / 4` for all `j ≤ R`; in particular
`B_0 ≥ 2^{-E_0}`.  Blueprint 04 Lemma B-budget (B1) (`04-B1`). -/
theorem variableSchedule_budget_bounds {f : ℕ → ℕ} (hf : Monotone f) {c R j : ℕ} (hj : j ≤ R) :
    7 / 8 ≤ (variableSchedule f c R).budget j ∧ (variableSchedule f c R).budget j ≤ 1 ∧
      3 / 4 ≤ (variableSchedule f c R).budget j - (variableSchedule f c R).weight j := by
  set S := variableSchedule f c R with hS
  have hSR : S.R = R := variableSchedule_R f c R
  have hw : ∀ k, k ≤ R → S.weight k = (1 / 2) ^ expSchedule k := fun k hk => by
    rw [hS, GameSchedule.weight, variableSchedule_exp hk, requestWeight]
  -- Backwards induction: `B_k ≤ 1` and `B_k ≥ 1 - Σ_{i=k+1}^{R} (2^{-g_i} + 2^{-E_i})`.
  have key : ∀ d k, k + d = R → S.budget k ≤ 1 ∧
      1 - (∑ i ∈ Finset.Icc 1 R, (1 / 2 : ℚ) ^ stepSize i -
          ∑ i ∈ Finset.Icc 1 k, (1 / 2 : ℚ) ^ stepSize i) -
        (∑ i ∈ Finset.Icc 1 R, (1 / 2 : ℚ) ^ expSchedule i -
          ∑ i ∈ Finset.Icc 1 k, (1 / 2 : ℚ) ^ expSchedule i) ≤ S.budget k := by
    intro d
    induction d with
    | zero =>
      intro k hk
      have hkR : k = R := by omega
      have h1 : S.budget R = 1 := by
        have := S.budget_R
        rwa [hSR] at this
      rw [hkR, h1]
      exact ⟨le_rfl, by linarith⟩
    | succ d ih =>
      intro k hk
      obtain ⟨ih1, ih2⟩ := ih (k + 1) (by omega)
      have hkR : k < R := by omega
      have hrec := S.budget_eq_of_lt (j := k) (hSR ▸ hkR)
      have hα : 1 / (S.ratio (k + 1) : ℚ) ≤ (1 / 2) ^ stepSize (k + 1) :=
        variableSchedule_inv_ratio_le hf hkR
      have hα0 : (0 : ℚ) ≤ 1 / (S.ratio (k + 1) : ℚ) := by positivity
      have hs1 : (1 / 2 : ℚ) ^ stepSize (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hβ := hw (k + 1) (by omega)
      have hβ0 : (0 : ℚ) ≤ (1 / 2) ^ expSchedule (k + 1) := by positivity
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)] at ih2
      rw [hrec, hβ]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr (hα.trans hs1)) (sub_nonneg.mpr ih1)]
      · nlinarith [mul_nonneg hα0 (sub_nonneg.mpr ih1)]
  obtain ⟨h1, h2⟩ := key (R - j) j (by omega)
  have hA := sum_stepSize_loss_le R
  have hC := sum_expSchedule_loss_le R
  have hA0 : (0 : ℚ) ≤ ∑ i ∈ Finset.Icc 1 j, (1 / 2 : ℚ) ^ stepSize i := by positivity
  have hC0 : (0 : ℚ) ≤ ∑ i ∈ Finset.Icc 1 j, (1 / 2 : ℚ) ^ expSchedule i := by positivity
  have hwj : S.weight j ≤ 1 / 65536 := by
    rw [hw j hj]
    calc (1 / 2 : ℚ) ^ expSchedule j ≤ (1 / 2) ^ 16 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by have := expSchedule_ge j; omega)
      _ = 1 / 65536 := by norm_num
  exact ⟨by linarith, h1, by linarith⟩

/-- The schedule inequality R1 for a discount `f`: `f (E_i) ≤ f (E_{i-1}) + E_{i-1} - 1` for
every `i ≥ 1`, written without natural subtraction as `f (E_i) + 1 ≤ f (E_{i-1}) + E_{i-1}`
(equivalent since `E_{i-1} ≥ 16`).  Blueprint 04 Lemma T-threshold, hypothesis (R1)
(`04-DEF-R1`). -/
def SatisfiesR1 (f : ℕ → ℕ) : Prop :=
  ∀ i, 1 ≤ i → f (expSchedule i) + 1 ≤ f (expSchedule (i - 1)) + expSchedule (i - 1)

/-- T-threshold: under MONO and R1, every threshold increment of the variable schedule satisfies
the uniform estimate `t_i ≥ (1 / 4) · 2^{-c} · 2^{-f (E_i)}` (hence `t_i ≥ 0`) for `1 ≤ i ≤ R`.
Blueprint 04 Lemma T-threshold (T1) (`04-T1`). -/
theorem variableSchedule_threshold_ge {f : ℕ → ℕ} (hf : Monotone f) (hR1 : SatisfiesR1 f)
    {c R i : ℕ} (hi : 1 ≤ i) (hiR : i ≤ R) :
    (1 / 4 : ℚ) * (1 / 2) ^ c * (1 / 2) ^ f (expSchedule i) ≤
      (variableSchedule f c R).threshold i := by
  obtain ⟨-, -, hB⟩ := variableSchedule_budget_bounds (c := c) hf hiR
  have hw : (variableSchedule f c R).weight i = (1 / 2) ^ expSchedule i := by
    rw [GameSchedule.weight, variableSchedule_exp hiR, requestWeight]
  have hs : (variableSchedule f c R).fineLength i =
      (1 / 2) ^ expSchedule i * ((1 / 2) ^ c * (1 / 2) ^ f (expSchedule i)) := by
    rw [GameSchedule.fineLength, variableSchedule_depth hiR]
    ring
  have hh : (variableSchedule f c R).coarseLength i ≤
      1 / 2 * ((1 / 2) ^ c * (1 / 2) ^ f (expSchedule i)) := by
    rw [GameSchedule.coarseLength, variableSchedule_depth (by omega : i - 1 ≤ R)]
    have h := hR1 i hi
    calc (1 / 2 : ℚ) ^ (expSchedule (i - 1) + f (expSchedule (i - 1)) + c)
        ≤ (1 / 2) ^ (f (expSchedule i) + 1 + c) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 * ((1 / 2) ^ c * (1 / 2) ^ f (expSchedule i)) := by ring
  have hQ : (0 : ℚ) ≤ (1 / 2) ^ c * (1 / 2) ^ f (expSchedule i) := by positivity
  have hq : (variableSchedule f c R).fineLength i / (variableSchedule f c R).weight i =
      (1 / 2) ^ c * (1 / 2) ^ f (expSchedule i) := by
    rw [hs, hw, mul_div_cancel_left₀ _ (by positivity)]
  rw [GameSchedule.threshold, hq]
  nlinarith [mul_le_mul_of_nonneg_right hB hQ]

/-- The rational partial sums `S_R = Σ_{i=1}^{R} 2^{-f (E_i)}` of a discount `f` along the common
schedule.  Defined here (not in `Divergence` or `AdmissibleDiscount`) so that DIV for `F` and the
round search see one definition.  Blueprint 04 Definition admissible-discount, DIV
(`04-DEF-DIV`). -/
def discountSums (f : ℕ → ℕ) (R : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 R, (1 / 2 : ℚ) ^ f (expSchedule i)

/-- DIV: the partial sums `S_R` of `f` are unbounded — for every natural `Q` some `R` has
`S_R ≥ Q`.  Blueprint 04 Definition admissible-discount, DIV (`04-DEF-DIV`). -/
def HasDivergentSums (f : ℕ → ℕ) : Prop :=
  ∀ Q : ℕ, ∃ R, (Q : ℚ) ≤ discountSums f R

end Kolmogorov
