/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.StoppingComplexity.PathBudget
import KolmogorovMathlib.StoppingComplexity.DyadicCells
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayTestComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame

/-!
# The generalized finite stopping-allocation game

Blueprint part 02, §1 (DEF-01, DEF-03, DEF-04), §5 (PARAM-GAME, LEM-GAME-01) and §7
(LEM-CONTEXT). A `GameSchedule` is the finite data `E_0 < … < E_R` (Alice exponents) and
`δ_0 < … < δ_R` (Bob depths); the rational budgets `B_j`, thresholds `t_j`, `Ψ_j` and the
sharp variants of COR-GAME-SHARP are defined from it by exact rational arithmetic
(PARAM-GAME). A local history is a list of answered requests with their dyadic cells; Bob's
legal answers (DEF-03), the histories reachable by a strategy against legal answers, and the
winning predicate with its four clauses — freshness, allowed exponent, load *including the
pending request* and the request bound (DEF-04) — are defined here. `embedStrategy` plays a
local strategy inside a fresh subtree, mapping the real answers through a cell translation
(LEM-CONTEXT).
-/

namespace Kolmogorov

/-! ### Schedules and their rational parameters (DEF-03, PARAM-GAME) -/

/-- The finite schedule of the game: the Alice exponents `E_0 < … < E_R` and the Bob depths
`δ_0 < … < δ_R`, as two lists (so that the strategy is computable in the schedule).
Blueprint 02 DEF-03. -/
structure GameSchedule where
  /-- The exponents `E_0, …, E_R`. -/
  exps : List ℕ
  /-- The depths `δ_0, …, δ_R`. -/
  depths : List ℕ

/-- A schedule is a pair of lists. Blueprint 02 DEF-03. -/
def GameSchedule.equivProd : GameSchedule ≃ List ℕ × List ℕ where
  toFun S := (S.exps, S.depths)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro S; cases S; rfl
  right_inv := by intro p; cases p; rfl

/-- Schedules are `Primcodable` through the pair of lists. Blueprint 02 DEF-03. -/
instance : Primcodable GameSchedule := Primcodable.ofEquiv _ GameSchedule.equivProd

namespace GameSchedule

/-- The top level `R` of a schedule (`0` for an empty exponent list). Blueprint 02 DEF-03. -/
def R (S : GameSchedule) : ℕ := S.exps.length - 1

/-- The exponent `E_j` (`0` out of range). Blueprint 02 DEF-03. -/
def exp (S : GameSchedule) (j : ℕ) : ℕ := S.exps.getD j 0

/-- The depth `δ_j` (`0` out of range). Blueprint 02 DEF-03. -/
def depth (S : GameSchedule) (j : ℕ) : ℕ := S.depths.getD j 0

/-- A valid schedule: the two lists have the same positive length, both are strictly
increasing (`List.Pairwise (· < ·)`), and `E_0 ≥ 1`. Blueprint 02 DEF-03. -/
def IsValid (S : GameSchedule) : Prop :=
  S.exps.length = S.depths.length ∧ 0 < S.exps.length ∧ S.exps.Pairwise (· < ·) ∧
    S.depths.Pairwise (· < ·) ∧ 1 ≤ S.exp 0

/-- The Bob depth `δ_i` prescribed for the Alice exponent `n = E_i` (junk when `n` is not an
exponent of the schedule). Blueprint 02 DEF-03. -/
def depthOfExp (S : GameSchedule) (n : ℕ) : ℕ := S.depth (S.exps.idxOf n)

/-- For a valid schedule, the depth prescribed for the exponent `E_j` is `δ_j`.
Blueprint 02 DEF-03. -/
theorem depthOfExp_exp {S : GameSchedule} (hS : S.IsValid) {j : ℕ} (hj : j < S.exps.length) :
    S.depthOfExp (S.exp j) = S.depth j := by
  have hnodup : S.exps.Nodup := hS.2.2.1.imp ne_of_lt
  unfold depthOfExp exp
  rw [List.getD_eq_getElem _ _ hj, List.Nodup.idxOf_getElem hnodup j hj]

/-- The exponents of a valid schedule increase along the list: `E_i ≤ E_k` for `i ≤ k` in
range. Blueprint 02 DEF-03. -/
private theorem exp_le_exp {S : GameSchedule} (hS : S.IsValid) {i k : ℕ} (hik : i ≤ k)
    (hk : k < S.exps.length) : S.exp i ≤ S.exp k := by
  unfold exp
  rw [List.getD_eq_getElem _ _ (lt_of_le_of_lt hik hk), List.getD_eq_getElem _ _ hk]
  rcases hik.lt_or_eq with h | rfl
  · exact (List.pairwise_iff_getElem.1 hS.2.2.1 i k (lt_of_le_of_lt hik hk) hk h).le
  · exact le_rfl

/-- The request weight `w_j = 2^{-E_j}`. Blueprint 02 PARAM-GAME. -/
def weight (S : GameSchedule) (j : ℕ) : ℚ := requestWeight (S.exp j)

/-- The fine Bob cell length `s_j = 2^{-δ_j}`. Blueprint 02 §3 / PARAM-GAME. -/
def fineLength (S : GameSchedule) (j : ℕ) : ℚ := (1 / 2 : ℚ) ^ S.depth j

/-- The coarse Bob cell length `h_j = 2^{-δ_{j-1}}` (for `j ≥ 1`). Blueprint 02 §3. -/
def coarseLength (S : GameSchedule) (j : ℕ) : ℚ := (1 / 2 : ℚ) ^ S.depth (j - 1)

/-- The ratio `L_j = 2^{δ_j - δ_{j-1}}` (for `j ≥ 1`; under `IsValid` the exponent is a
genuine difference). Blueprint 02 §3 / PARAM-GAME. -/
def ratio (S : GameSchedule) (j : ℕ) : ℕ := 2 ^ (S.depth j - S.depth (j - 1))

/-- The downward budget recursion, indexed by `R - j`: `budgetAux 0 = B_R = 1` and
`budgetAux (k + 1) = B_{R-k-1} = B_{R-k} (1 - 1/L_{R-k}) - w_{R-k}`.
Blueprint 02 PARAM-GAME. -/
def budgetAux (S : GameSchedule) : ℕ → ℚ
  | 0 => 1
  | k + 1 => S.budgetAux k * (1 - 1 / (S.ratio (S.R - k) : ℚ)) - S.weight (S.R - k)

/-- The rational budget `B_j` of level `j`: `B_R = 1`, `B_{j-1} = B_j (1 - 1/L_j) - w_j`.
Blueprint 02 PARAM-GAME. -/
def budget (S : GameSchedule) (j : ℕ) : ℚ := S.budgetAux (S.R - j)

/-- The source threshold `t_j = (B_j - w_j) · (s_j / w_j) - h_j`, with `2^{E_j - δ_j}` read
as the rational ratio `s_j / w_j`. Blueprint 02 PARAM-GAME. -/
def threshold (S : GameSchedule) (j : ℕ) : ℚ :=
  (S.budget j - S.weight j) * (S.fineLength j / S.weight j) - S.coarseLength j

/-- `Ψ_j = Σ_{i=1}^{j} t_i` (`Ψ_0 = 0`). Blueprint 02 PARAM-GAME. -/
def psi (S : GameSchedule) (j : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 j, S.threshold i

/-- The sharp threshold `t♯_j = B_j · (s_j / w_j) - s_{j-1}` of COR-GAME-SHARP.
Blueprint 02 COR-GAME-SHARP. -/
def thresholdSharp (S : GameSchedule) (j : ℕ) : ℚ :=
  S.budget j * (S.fineLength j / S.weight j) - S.fineLength (j - 1)

/-- `Ψ♯_j = Σ_{i=1}^{j} t♯_i`. Blueprint 02 COR-GAME-SHARP. -/
def psiSharp (S : GameSchedule) (j : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 j, S.thresholdSharp i

/-- The PARAM-GAME hypotheses: a valid schedule with `w_0 ≤ B_0` and all source thresholds
`t_j`, `1 ≤ j ≤ R`, nonnegative. Blueprint 02 PARAM-GAME. -/
def IsAdmissible (S : GameSchedule) : Prop :=
  S.IsValid ∧ S.weight 0 ≤ S.budget 0 ∧ ∀ j, 1 ≤ j → j ≤ S.R → 0 ≤ S.threshold j

/-- The top budget is `B_R = 1`. Blueprint 02 PARAM-GAME. -/
theorem budget_R (S : GameSchedule) : S.budget S.R = 1 := by
  simp [budget, budgetAux]

/-- The budget recurrence `B_j = B_{j+1} (1 - 1/L_{j+1}) - w_{j+1}` for `j < R`.
Blueprint 02 PARAM-GAME. -/
theorem budget_eq_of_lt (S : GameSchedule) {j : ℕ} (hj : j < S.R) :
    S.budget j = S.budget (j + 1) * (1 - 1 / (S.ratio (j + 1) : ℚ)) - S.weight (j + 1) := by
  unfold budget
  obtain ⟨k, hk⟩ : ∃ k, S.R - j = k + 1 := ⟨S.R - j - 1, by omega⟩
  rw [hk, budgetAux, show S.R - k = j + 1 by omega, show S.R - (j + 1) = k by omega]

/-- The weights `w_j = 2^{-E_j}` are positive. Blueprint 02 PARAM-GAME. -/
private theorem weight_pos (S : GameSchedule) (j : ℕ) : 0 < S.weight j := by
  unfold weight requestWeight
  positivity

/-- One step of the forward recurrence of LEM-GAME-01: below the top level, a positive
budget `B_j` is at most `B_{j+1}`, which is positive as well (`B_{j+1} (1 - 1/L_{j+1}) =
B_j + w_{j+1} > 0` with `0 ≤ 1 - 1/L_{j+1} ≤ 1`). Blueprint 02 LEM-GAME-01. -/
private theorem budget_le_budget_succ {S : GameSchedule} {j : ℕ} (hj : j < S.R)
    (hpos : 0 < S.budget j) : 0 < S.budget (j + 1) ∧ S.budget j ≤ S.budget (j + 1) := by
  have hrec := S.budget_eq_of_lt hj
  have hL : (1 : ℚ) ≤ (S.ratio (j + 1) : ℚ) := by
    unfold ratio
    exact_mod_cast Nat.one_le_two_pow
  have hinv : 0 ≤ 1 / (S.ratio (j + 1) : ℚ) := by positivity
  have hinv1 : 1 / (S.ratio (j + 1) : ℚ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hL
  have hw := S.weight_pos (j + 1)
  set c := 1 - 1 / (S.ratio (j + 1) : ℚ)
  have hc0 : 0 ≤ c := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hBc : 0 < S.budget (j + 1) * c := by linarith
  have hB : 0 < S.budget (j + 1) := by
    by_contra hneg
    have : S.budget (j + 1) * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hc0
    linarith
  exact ⟨hB, by nlinarith⟩

/-- Budget positivity and monotonicity: for an admissible schedule and every `i ≤ R`,
`w_i ≤ w_0 ≤ B_0 ≤ B_i ≤ 1` (forward recurrence `B_j = (B_{j-1} + w_j) / (1 - 1/L_j)`).
Blueprint 02 LEM-GAME-01. -/
theorem budget_bounds {S : GameSchedule} (hS : S.IsAdmissible) {i : ℕ} (hi : i ≤ S.R) :
    S.weight i ≤ S.weight 0 ∧ S.weight 0 ≤ S.budget 0 ∧ S.budget 0 ≤ S.budget i ∧
      S.budget i ≤ 1 := by
  obtain ⟨hV, hw0, -⟩ := hS
  have hlen := hV.2.1
  have hup : ∀ i, i ≤ S.R → 0 < S.budget i ∧ S.budget 0 ≤ S.budget i := by
    intro i hi
    induction i with
    | zero => exact ⟨lt_of_lt_of_le (S.weight_pos 0) hw0, le_rfl⟩
    | succ i ih =>
      obtain ⟨hpos, h0⟩ := ih (by omega)
      obtain ⟨hpos', hle⟩ := budget_le_budget_succ (by omega : i < S.R) hpos
      exact ⟨hpos', h0.trans hle⟩
  have hdown : ∀ d, d ≤ S.R → S.budget (S.R - d) ≤ 1 := by
    intro d hd
    induction d with
    | zero => simp [budget_R]
    | succ d ih =>
      have hle := (budget_le_budget_succ (by omega : S.R - (d + 1) < S.R)
        (hup _ (by omega)).1).2
      rw [show S.R - (d + 1) + 1 = S.R - d by omega] at hle
      exact hle.trans (ih (by omega))
  refine ⟨?_, hw0, (hup i hi).2, ?_⟩
  · unfold weight requestWeight
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (exp_le_exp hV (Nat.zero_le i) (by unfold R at hi; omega))
  · have hle := hdown (S.R - i) (by omega)
    rwa [show S.R - (S.R - i) = i by omega] at hle

/-- `Ψ_0 = 0`. Blueprint 02 PARAM-GAME. -/
theorem psi_zero (S : GameSchedule) : S.psi 0 = 0 := by
  simp [psi]

/-- `Ψ_{j+1} = Ψ_j + t_{j+1}`. Blueprint 02 PARAM-GAME. -/
theorem psi_succ (S : GameSchedule) (j : ℕ) : S.psi (j + 1) = S.psi j + S.threshold (j + 1) := by
  unfold psi
  exact Finset.sum_Icc_succ_top (by omega) _

/-- For an admissible schedule the partial sums `Ψ_j`, `j ≤ R`, are nonnegative.
Blueprint 02 PARAM-GAME. -/
theorem psi_nonneg {S : GameSchedule} (hS : S.IsAdmissible) {j : ℕ} (hj : j ≤ S.R) :
    0 ≤ S.psi j :=
  Finset.sum_nonneg fun i hi =>
    hS.2.2 i (Finset.mem_Icc.1 hi).1 ((Finset.mem_Icc.1 hi).2.trans hj)

/-- The exponent list of a schedule is primitive recursive. Blueprint 02 PARAM-GAME. -/
private theorem primrec_exps : Primrec GameSchedule.exps :=
  (Primrec.fst.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl

/-- The depth list of a schedule is primitive recursive. Blueprint 02 PARAM-GAME. -/
private theorem primrec_depths : Primrec GameSchedule.depths :=
  (Primrec.snd.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl

/-- The top level `R` is primitive recursive in the schedule. Blueprint 02 PARAM-GAME. -/
private theorem primrec_R : Primrec GameSchedule.R :=
  (Primrec.nat_sub.comp (Primrec.list_length.comp primrec_exps) (Primrec.const 1)).of_eq
    fun _ => rfl

/-- The exponent `E_j` is primitive recursive in the schedule and the level.
Blueprint 02 PARAM-GAME. -/
private theorem primrec_exp : Primrec₂ GameSchedule.exp :=
  ((Primrec.list_getD 0).comp (primrec_exps.comp Primrec.fst) Primrec.snd).of_eq fun _ => rfl

/-- The depth `δ_j` is primitive recursive in the schedule and the level.
Blueprint 02 PARAM-GAME. -/
private theorem primrec_depth : Primrec₂ GameSchedule.depth :=
  ((Primrec.list_getD 0).comp (primrec_depths.comp Primrec.fst) Primrec.snd).of_eq fun _ => rfl

/-- The downward budget recursion as a `Nat.rec`, with the division by `L_{R-k}` written as
the power `(1/2)^{δ_{R-k} - δ_{R-k-1}}` (the form in which the budgets are computed; ℚ has no
computable division in the library). Blueprint 02 PARAM-GAME. -/
private theorem budgetAux_eq_rec (S : GameSchedule) (k : ℕ) :
    S.budgetAux k = Nat.rec (motive := fun _ => ℚ) 1 (fun k b => b * (1 - (1 / 2 : ℚ) ^
      (S.depth (S.R - k) - S.depth (S.R - k - 1))) - (1 / 2 : ℚ) ^ S.exp (S.R - k)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hL : (1 : ℚ) / (S.ratio (S.R - k) : ℚ) =
        (1 / 2 : ℚ) ^ (S.depth (S.R - k) - S.depth (S.R - k - 1)) := by
      rw [ratio, Nat.cast_pow, Nat.cast_ofNat, one_div_pow]
    rw [budgetAux, ih, hL]
    rfl

/-- `s_j / w_j = 2^{-δ_j} · 2^{E_j}`: the ratio of the fine cell length and the weight as a
product (the form in which the thresholds are computed). Blueprint 02 PARAM-GAME. -/
private theorem fineLength_div_weight (S : GameSchedule) (j : ℕ) :
    S.fineLength j / S.weight j = (1 / 2 : ℚ) ^ S.depth j * ((2 ^ S.exp j : ℕ) : ℚ) := by
  unfold fineLength weight requestWeight
  rw [div_eq_iff (by positivity), Nat.cast_pow, Nat.cast_ofNat, mul_assoc, ← mul_pow]
  norm_num

/-- The partial sums `Σ_{i=1}^{j} f(a, i)` of a computable rational sequence are computable in
`(a, j)`. Blueprint 02 PARAM-GAME. -/
private theorem computable_sum_Icc_one {α : Type*} [Primcodable α] {f : α → ℕ → ℚ}
    (hf : Computable₂ f) : Computable fun a : α × ℕ => ∑ i ∈ Finset.Icc 1 a.2, f a.1 i := by
  have hstep : Computable₂ fun (a : α × ℕ) (p : ℕ × ℚ) => p.2 + f a.1 (p.1 + 1) :=
    (computable₂_ratAdd.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))).of_eq fun _ => rfl
  refine (Computable.nat_rec Computable.snd (Computable.const (0 : ℚ)) hstep).of_eq
    fun a => ?_
  obtain ⟨a, j⟩ := a
  dsimp only
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    exact congrArg (· + f a (j + 1)) ih

/-- The budgets are computable in the schedule and the level. Blueprint 02 PARAM-GAME. -/
theorem computable_budget : Computable fun a : GameSchedule × ℕ => a.1.budget a.2 := by
  have hRk : Primrec fun q : (GameSchedule × ℕ) × (ℕ × ℚ) => q.1.1.R - q.2.1 :=
    (Primrec.nat_sub.comp (primrec_R.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)).of_eq fun _ => rfl
  have hm : Primrec fun q : (GameSchedule × ℕ) × (ℕ × ℚ) =>
      q.1.1.depth (q.1.1.R - q.2.1) - q.1.1.depth (q.1.1.R - q.2.1 - 1) :=
    (Primrec.nat_sub.comp (primrec_depth.comp (Primrec.fst.comp Primrec.fst) hRk)
      (primrec_depth.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.nat_sub.comp hRk (Primrec.const 1)))).of_eq fun _ => rfl
  have he : Primrec fun q : (GameSchedule × ℕ) × (ℕ × ℚ) => q.1.1.exp (q.1.1.R - q.2.1) :=
    (primrec_exp.comp (Primrec.fst.comp Primrec.fst) hRk).of_eq fun _ => rfl
  have hstep : Computable₂ fun (a : GameSchedule × ℕ) (p : ℕ × ℚ) =>
      p.2 * (1 - (1 / 2 : ℚ) ^ (a.1.depth (a.1.R - p.1) - a.1.depth (a.1.R - p.1 - 1))) -
        (1 / 2 : ℚ) ^ a.1.exp (a.1.R - p.1) :=
    (computable₂_ratSub.comp (computable₂_ratMul.comp (Computable.snd.comp Computable.snd)
      (computable₂_ratSub.comp (Computable.const 1) (computable_half_pow.comp hm.to_comp)))
      (computable_half_pow.comp he.to_comp)).of_eq fun _ => rfl
  have hk : Computable fun a : GameSchedule × ℕ => a.1.R - a.2 :=
    (Primrec.nat_sub.comp (primrec_R.comp Primrec.fst) Primrec.snd).to_comp
  exact (Computable.nat_rec hk (Computable.const (1 : ℚ)) hstep).of_eq fun a => by
    rw [budget, budgetAux_eq_rec]

/-- The thresholds are computable in the schedule and the level. Blueprint 02 PARAM-GAME. -/
theorem computable_threshold : Computable fun a : GameSchedule × ℕ => a.1.threshold a.2 := by
  have hw : Computable fun a : GameSchedule × ℕ => (1 / 2 : ℚ) ^ a.1.exp a.2 :=
    (computable_half_pow.comp primrec_exp.to_comp).of_eq fun _ => rfl
  have hs : Computable fun a : GameSchedule × ℕ =>
      (1 / 2 : ℚ) ^ a.1.depth a.2 * ((2 ^ a.1.exp a.2 : ℕ) : ℚ) :=
    (computable₂_ratMul.comp (computable_half_pow.comp primrec_depth.to_comp)
      (computable_nat_to_rat.comp (comp_pow.comp primrec_exp.to_comp))).of_eq fun _ => rfl
  have hh : Computable fun a : GameSchedule × ℕ => (1 / 2 : ℚ) ^ a.1.depth (a.2 - 1) :=
    (computable_half_pow.comp (primrec_depth.comp Primrec.fst
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))).to_comp).of_eq fun _ => rfl
  exact (computable₂_ratSub.comp (computable₂_ratMul.comp
    (computable₂_ratSub.comp computable_budget hw) hs) hh).of_eq fun a => by
      rw [threshold, fineLength_div_weight]
      rfl

/-- The partial sums `Ψ_j` are computable in the schedule and the level.
Blueprint 02 PARAM-GAME. -/
theorem computable_psi : Computable fun a : GameSchedule × ℕ => a.1.psi a.2 :=
  (computable_sum_Icc_one (f := GameSchedule.threshold) computable_threshold).of_eq
    fun _ => rfl

/-- The sharp partial sums `Ψ♯_j` are computable in the schedule and the level.
Blueprint 02 COR-GAME-SHARP. -/
theorem computable_psiSharp : Computable fun a : GameSchedule × ℕ => a.1.psiSharp a.2 := by
  have hs : Computable fun a : GameSchedule × ℕ =>
      (1 / 2 : ℚ) ^ a.1.depth a.2 * ((2 ^ a.1.exp a.2 : ℕ) : ℚ) :=
    (computable₂_ratMul.comp (computable_half_pow.comp primrec_depth.to_comp)
      (computable_nat_to_rat.comp (comp_pow.comp primrec_exp.to_comp))).of_eq fun _ => rfl
  have hh : Computable fun a : GameSchedule × ℕ => (1 / 2 : ℚ) ^ a.1.depth (a.2 - 1) :=
    (computable_half_pow.comp (primrec_depth.comp Primrec.fst
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))).to_comp).of_eq fun _ => rfl
  have hsharp : Computable₂ GameSchedule.thresholdSharp :=
    (computable₂_ratSub.comp (computable₂_ratMul.comp computable_budget hs) hh).of_eq
      fun a => by
        rw [thresholdSharp, fineLength_div_weight]
        rfl
  exact (computable_sum_Icc_one hsharp).of_eq fun _ => rfl

end GameSchedule

/-! ### Histories, legal answers and reachable histories (DEF-01, DEF-03, DEF-04) -/

/-- A local history: the answered requests in order, each with Bob's cell. The pending request
is appended by the caller when loads and freshness are checked. Blueprint 02 DEF-01. -/
abbrev LocalHistory := List (Request × DyadicCell)

/-- A local strategy: the next request as a total function of the history.
Blueprint 02 DEF-01 / DEF-04. -/
abbrev LocalStrategy := LocalHistory → Request

/-- The requests of a history, in order. Blueprint 02 DEF-01. -/
def requestsOf (h : LocalHistory) : List Request := h.map Prod.fst

/-- A legal Bob answer `a` to the request `r` after the history `h` in the game of capacity
`U`: the cell has the depth prescribed for the exponent of `r`, lies in `[0, U)`, and is
disjoint from the answers at distinct requested vertices comparable with the vertex of `r`
(incomparable vertices impose no constraint). Blueprint 02 DEF-03. -/
def LegalAnswer (S : GameSchedule) (U : ℚ) (h : LocalHistory) (r : Request) (a : DyadicCell) :
    Prop :=
  a.1 = S.depthOfExp r.2 ∧ CellInCapacity U a ∧
    ∀ e ∈ h, IsComparable e.1.1 r.1 → e.1.1 ≠ r.1 → CellsDisjoint e.2 a

/-- Legality of an answer is decidable (finite rational checks). Blueprint 02 DEF-03. -/
instance instDecidableLegalAnswer (S : GameSchedule) (U : ℚ) (h : LocalHistory) (r : Request)
    (a : DyadicCell) : Decidable (LegalAnswer S U h r a) := by
  unfold LegalAnswer; infer_instance

/-- A request is allowed at level `j` when its exponent is one of `E_0, …, E_j`.
Blueprint 02 DEF-03 / THEOREM-GAME ("using only exponents `E_0, …, E_j`"). -/
def RequestAllowed (S : GameSchedule) (j : ℕ) (r : Request) : Prop := r.2 ∈ S.exps.take (j + 1)

/-- DEF-01's `n ≥ 1` for the allowed requests of a valid schedule (`E_0 ≥ 1` and the
exponents increase). Blueprint 02 DEF-01 / DEF-03. -/
theorem GameSchedule.one_le_of_requestAllowed {S : GameSchedule} {j : ℕ} {r : Request}
    (hS : S.IsValid) (h : RequestAllowed S j r) : 1 ≤ r.2 := by
  obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.1 (List.mem_of_mem_take h)
  have hle := GameSchedule.exp_le_exp hS (Nat.zero_le k) hk
  have h0 := hS.2.2.2.2
  unfold GameSchedule.exp at hle h0
  rw [List.getD_eq_getElem _ _ hk, hkr] at hle
  omega

/-- An exponent allowed at level `j ≤ R` is at most `E_j`. Blueprint 02 DEF-03. -/
theorem GameSchedule.le_exp_of_requestAllowed {S : GameSchedule} {j : ℕ} {r : Request}
    (hS : S.IsValid) (hj : j ≤ S.R) (h : RequestAllowed S j r) : r.2 ≤ S.exp j := by
  obtain ⟨k, hk, hkr⟩ := List.mem_take_iff_getElem.1 h
  have hjl : j < S.exps.length := by
    have := hS.2.1
    unfold GameSchedule.R at hj
    omega
  have hle := GameSchedule.exp_le_exp hS (show k ≤ j by omega) hjl
  unfold GameSchedule.exp at hle
  rw [List.getD_eq_getElem _ _ (by omega), hkr] at hle
  exact hle

/-- The histories reachable by playing `σ` against legal answers on top of a fixed prior
history `H₀` (legality is judged against `H₀ ++ h`). Blueprint 02 DEF-04. -/
inductive ReachableFrom (S : GameSchedule) (U : ℚ) (σ : LocalStrategy) (H₀ : LocalHistory) :
    LocalHistory → Prop
  /-- The empty continuation is reachable. -/
  | nil : ReachableFrom S U σ H₀ []
  /-- Answering the current request legally extends a reachable history. -/
  | snoc {h : LocalHistory} {a : DyadicCell} (hh : ReachableFrom S U σ H₀ h)
      (ha : LegalAnswer S U (H₀ ++ h) (σ h) a) : ReachableFrom S U σ H₀ (h ++ [(σ h, a)])

/-- The histories reachable by `σ` from the empty history. Blueprint 02 DEF-04. -/
abbrev Reachable (S : GameSchedule) (U : ℚ) (σ : LocalStrategy) : LocalHistory → Prop :=
  ReachableFrom S U σ []

/-- The precise winning endpoint on top of a prior history `H₀`: at every reachable history
the next request is fresh (its vertex was never requested), uses an exponent among
`E_0, …, E_j`, keeps every path load — *including the pending request* — at most `B`, and is
at most the `T`-th request (so no legal history answers `T` requests).
Blueprint 02 DEF-04 (items 2–4; computability, item 1, is a separate statement). -/
def IsWinningLocalStrategyFrom (S : GameSchedule) (j : ℕ) (U B : ℚ) (T : ℕ)
    (H₀ : LocalHistory) (σ : LocalStrategy) : Prop :=
  ∀ h, ReachableFrom S U σ H₀ h →
    (σ h).1 ∉ (requestsOf (H₀ ++ h)).map Prod.fst ∧ RequestAllowed S j (σ h) ∧
      HasBudget (requestsOf (H₀ ++ h) ++ [σ h]) B ∧ h.length + 1 ≤ T

/-- The winning endpoint from the empty history. Blueprint 02 DEF-04. -/
abbrev IsWinningLocalStrategy (S : GameSchedule) (j : ℕ) (U B : ℚ) (T : ℕ)
    (σ : LocalStrategy) : Prop :=
  IsWinningLocalStrategyFrom S j U B T [] σ

/-! ### Context embedding (LEM-CONTEXT) -/

/-- The virtual history seen by a local strategy played below the root `u`: vertices relative
to `u` and answers mapped through the cell translation `Φ`. Blueprint 02 LEM-CONTEXT. -/
def virtualHistory (u : BitString) (Φ : DyadicCell → DyadicCell) (h : LocalHistory) :
    LocalHistory :=
  h.map fun e => ((e.1.1.drop u.length, e.1.2), Φ e.2)

/-- Play `σ` in local coordinates below `u`: the real request is `u ++ x` when the virtual
request is `x`, and the real answers reach `σ` through `Φ`. Blueprint 02 LEM-CONTEXT. -/
def embedStrategy (u : BitString) (Φ : DyadicCell → DyadicCell) (σ : LocalStrategy) :
    LocalStrategy :=
  fun h => let r := σ (virtualHistory u Φ h); (u ++ r.1, r.2)

/-- The virtual play follows the real one: answering the embedded request with `c` extends
the virtual history by `σ`'s own request answered with `Φ c`. Blueprint 02 LEM-CONTEXT. -/
theorem virtualHistory_snoc (u : BitString) (Φ : DyadicCell → DyadicCell) (σ : LocalStrategy)
    (h : LocalHistory) (c : DyadicCell) :
    virtualHistory u Φ (h ++ [(embedStrategy u Φ σ h, c)]) =
      virtualHistory u Φ h ++ [(σ (virtualHistory u Φ h), Φ c)] := by
  simp [virtualHistory, embedStrategy]

/-- Every request of an embedded play lies below the root: the real requests are the virtual
ones translated by `u` (concatenation `x ↦ u ++ x`). Blueprint 02 LEM-CONTEXT. -/
private theorem requestsOf_eq_translateRequests {S : GameSchedule} {U : ℚ} {u : BitString}
    {Φ : DyadicCell → DyadicCell} {σ : LocalStrategy} {H₀ h : LocalHistory}
    (hh : ReachableFrom S U (embedStrategy u Φ σ) H₀ h) :
    requestsOf h = translateRequests u (requestsOf (virtualHistory u Φ h)) := by
  induction hh with
  | nil => rfl
  | @snoc h a hh ha ih =>
    rw [virtualHistory_snoc]
    simp only [requestsOf, translateRequests, List.map_append, List.map_cons,
      List.map_nil] at ih ⊢
    rw [ih]
    rfl

/-- The response map preserves legal play: the virtual history of a reachable embedded
history is reachable for `σ` in the virtual game of capacity `U'`. Blueprint 02 LEM-CONTEXT
(used again by the termination bound LEM-EFF-01). -/
theorem reachable_virtualHistory_of_embed {S : GameSchedule} {j : ℕ} {U U' B : ℚ} {T : ℕ}
    {σ : LocalStrategy} {u : BitString} {Φ : DyadicCell → DyadicCell} {H₀ : LocalHistory}
    (hσ : IsWinningLocalStrategy S j U' B T σ)
    (hΦ : ∀ h r c, ReachableFrom S U (embedStrategy u Φ σ) H₀ h → RequestAllowed S j r →
      LegalAnswer S U (H₀ ++ h) (u ++ r.1, r.2) c →
        LegalAnswer S U' (virtualHistory u Φ h) r (Φ c))
    {h : LocalHistory} (hh : ReachableFrom S U (embedStrategy u Φ σ) H₀ h) :
    Reachable S U' σ (virtualHistory u Φ h) := by
  induction hh with
  | nil => exact ReachableFrom.nil
  | @snoc h a hh ha ih =>
    rw [virtualHistory_snoc]
    exact ReachableFrom.snoc ih (hΦ _ _ _ hh (hσ _ ih).2.1 ha)

/-- Loads add along the old ancestor chain and the new local requests: a history `A₀` with
load at most `a` on the words through `u` and at most `B'` everywhere, extended by the
translation below `u` of a local history of budget `B`, has budget `B'` when `a + B ≤ B'`.
Blueprint 01 F2.3 / 02 LEM-CONTEXT. -/
private theorem hasBudget_append_translateRequests {A₀ A : List Request} {u : BitString}
    {a B B' : ℚ} (hload : ∀ v, u <+: v → load A₀ v ≤ a) (hA₀ : HasBudget A₀ B')
    (hA : HasBudget A B) (hab : a + B ≤ B') : HasBudget (A₀ ++ translateRequests u A) B' := by
  intro v
  rw [load_append]
  by_cases hv : u <+: v
  · rw [load_translateRequests_of_prefix u A hv]
    linarith [hload v hv, hA (v.drop u.length)]
  · rw [load_translateRequests_of_not_prefix u A hv]
    linarith [hA₀ v]

/-- A request below a fresh root is new: if `x` is not a local vertex, then `u ++ x` is
neither an old vertex (freshness of `u`) nor a translated local vertex (concatenation with
`u` is injective). Blueprint 01 F2.3 / 02 LEM-CONTEXT. -/
private theorem append_not_mem_map_fst {A₀ A : List Request} {u x : BitString}
    (hfresh : IsFreshRoot A₀ u) (hx : x ∉ A.map Prod.fst) :
    u ++ x ∉ (A₀ ++ translateRequests u A).map Prod.fst := by
  simp only [List.map_append, List.mem_append, not_or]
  refine ⟨fun hmem => ?_, fun hmem => ?_⟩
  · obtain ⟨r, hr, hrx⟩ := List.mem_map.1 hmem
    exact hfresh r hr (by rw [hrx]; exact List.prefix_append u x)
  · obtain ⟨r, hr, hrx⟩ := List.mem_map.1 hmem
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact hx (List.mem_map.2 ⟨r', hr', List.append_cancel_left hrx⟩)

/-- Simulating a fresh local subtree. If `σ` wins the local game of capacity `U'` with budget
`B` and request bound `T`; `Φ` maps every legal real answer (in capacity `U`, after a
reachable history of the embedded play) to a request allowed at level `j` below `u` to a
legal virtual answer; `u` is a fresh root of the prior history `H₀`; `H₀` has load at most `a`
on every path through `u` and is within the budget `B'` everywhere, with `a + B ≤ B'`; then
the embedded strategy wins from `H₀` with budget `B'` and the same request bound. The text's
third hypothesis (old requests off the ancestor chain are incomparable with the subtree)
follows from `hfresh` and is not a binder; the conclusion's budget is a `B' ≥ a + B` that
also bounds `H₀` on the paths outside `u`, which the embedding leaves unchanged.
Blueprint 02 LEM-CONTEXT. -/
theorem embedStrategy_winning {S : GameSchedule} {j : ℕ} {U U' B B' a : ℚ} {T : ℕ}
    {σ : LocalStrategy} {u : BitString} {Φ : DyadicCell → DyadicCell} {H₀ : LocalHistory}
    (hσ : IsWinningLocalStrategy S j U' B T σ)
    (hΦ : ∀ h r c, ReachableFrom S U (embedStrategy u Φ σ) H₀ h → RequestAllowed S j r →
      LegalAnswer S U (H₀ ++ h) (u ++ r.1, r.2) c →
        LegalAnswer S U' (virtualHistory u Φ h) r (Φ c))
    (hfresh : IsFreshRoot (requestsOf H₀) u)
    (hload : ∀ v, u <+: v → load (requestsOf H₀) v ≤ a)
    (hH₀ : HasBudget (requestsOf H₀) B') (hab : a + B ≤ B') :
    IsWinningLocalStrategyFrom S j U B' T H₀ (embedStrategy u Φ σ) := by
  intro h hh
  obtain ⟨hnew, hallowed, hbudget, hlen⟩ := hσ _ (reachable_virtualHistory_of_embed hσ hΦ hh)
  have hreqs : requestsOf (H₀ ++ h) =
      requestsOf H₀ ++ translateRequests u (requestsOf (virtualHistory u Φ h)) := by
    rw [← requestsOf_eq_translateRequests hh]
    simp only [requestsOf, List.map_append]
  refine ⟨?_, hallowed, ?_, ?_⟩
  · rw [hreqs]
    exact append_not_mem_map_fst hfresh hnew
  · have hlast : translateRequests u (requestsOf (virtualHistory u Φ h)) ++
        [embedStrategy u Φ σ h] = translateRequests u
          (requestsOf (virtualHistory u Φ h) ++ [σ (virtualHistory u Φ h)]) := by
      simp [translateRequests, embedStrategy]
    rw [hreqs, List.append_assoc, hlast]
    exact hasBudget_append_translateRequests hload hH₀ hbudget hab
  · rw [virtualHistory, List.length_map] at hlen
    exact hlen

end Kolmogorov
