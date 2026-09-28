import KolmogorovMathlib.StoppingComplexity.Schedule
import KolmogorovMathlib.StoppingComplexity.WordGame
import KolmogorovMathlib.StoppingComplexity.StrategyComputable
import KolmogorovMathlib.Foundation.UnboundedSearch

/-!
# Admissible discounts and the variable-discount word family

Blueprint 04 §4 (Definition admissible-discount, Lemma choose-rounds) and the instantiated
Interface GAME-VARIABLE of 04 §1.

An *admissible discount* `f : ℕ → ℕ` is a total computable nondecreasing function satisfying
the schedule inequality R1, the bounded-shift condition SHIFT and the divergence condition DIV
on the rational partial sums `S_R = Σ_{i=1}^R 2^{-f(E_i)}` along the common schedule
`E_j = expSchedule j` (item `04-DEF-ADMISSIBLE`; `discountSums` and `HasDivergentSums` live in
`Schedule`). For such an `f` and every tag `c` the horizon `roundCount f _ c` is the first `R`
with `S_R ≥ 4·2^c`: the search is total by DIV and a computable function of `c`
(`04-CHOOSE-ROUNDS`). With that horizon the variable schedule `variableSchedule f c R` (depths
`δ_j = E_j + f(E_j) + c`) satisfies every hypothesis of THEOREM-GAME at capacity `U = 1`, and
the padded shadow (LEM-SHADOW with `cap = 0`) of the concrete strategy `localStrategy` is the
uniformly computable family `variableWordFamily f hf`, winning `G_{f+c}` for every `c`
(`04-GAME-VARIABLE`, `04-VARIABLE-FAMILY-WIN`, `04-VARIABLE-FAMILY-COMP`). Nothing here assumes
a winning strategy: the game theorem is applied to one closed definition.

The optional series-form sufficient condition for DIV (04 §4, SER, item `04-SER`) is parked by
owner decision and not coded.
-/

namespace Kolmogorov

/-- Condition SHIFT of an admissible discount: for every shift `a` there is a natural `D` (the
blueprint's `D_a`) with `f (n + a) ≤ f n + D` for every natural `n`. The constants need not be
computable in `a`. Blueprint 04 Definition admissible-discount, SHIFT (`04-DEF-ADMISSIBLE`). -/
def HasBoundedShift (f : ℕ → ℕ) : Prop := ∀ a : ℕ, ∃ D : ℕ, ∀ n : ℕ, f (n + a) ≤ f n + D

/-- An admissible discount: a total computable `f : ℕ → ℕ` that is nondecreasing (MONO),
satisfies the schedule inequality R1 (`SatisfiesR1`), has bounded shifts (SHIFT,
`HasBoundedShift`) and divergent partial sums `Σ_{i=1}^R 2^{-f(E_i)}` along the common schedule
(DIV, `HasDivergentSums`). The five conditions are bundled so that the endpoint statements
about an arbitrary `f` carry one hypothesis. Blueprint 04 Definition admissible-discount
(`04-DEF-ADMISSIBLE`). -/
structure IsAdmissibleDiscount (f : ℕ → ℕ) : Prop where
  /-- `f` is a total computable function (04 §4: "a fixed total computable function"). -/
  computable : Computable f
  /-- MONO: `f` is nondecreasing. -/
  mono : Monotone f
  /-- R1: `f (E_i) + 1 ≤ f (E_{i-1}) + E_{i-1}` for every `i ≥ 1`. -/
  r1 : SatisfiesR1 f
  /-- SHIFT: for every `a` some `D_a` bounds `f (n + a) - f n`. -/
  shift : HasBoundedShift f
  /-- DIV: the partial sums `Σ_{i=1}^R 2^{-f(E_i)}` are unbounded. -/
  div : HasDivergentSums f

/-- The horizon `R(c)` of choose-rounds: the first `R` with `Σ_{i=1}^R 2^{-f(E_i)} ≥ 4·2^c`
(condition R-search), found by sequential search over exact rational comparisons. The search
succeeds because DIV supplies a witness; the divergence proof `hdiv` is an argument of the
definition (`Nat.find`), and computability of `c ↦ R(c)` is the theorem `roundCount_computable`.
Blueprint 04 Lemma choose-rounds (`04-CHOOSE-ROUNDS`). -/
def roundCount (f : ℕ → ℕ) (hdiv : HasDivergentSums f) (c : ℕ) : ℕ :=
  Nat.find (show ∃ R, (4 * 2 ^ c : ℚ) ≤ discountSums f R by exact_mod_cast hdiv (4 * 2 ^ c))

/-- choose-rounds, the search condition at the horizon: for every tag `c`, the partial sum
`Σ_{i=1}^R 2^{-f(E_i)}` at `R = roundCount f hdiv c` is at least `4·2^c`.
Blueprint 04 Lemma choose-rounds, (R-search) (`04-CHOOSE-ROUNDS`). -/
theorem roundCount_spec {f : ℕ → ℕ} (hdiv : HasDivergentSums f) (c : ℕ) :
    (4 * 2 ^ c : ℚ) ≤ discountSums f (roundCount f hdiv c) := by
  unfold roundCount
  exact Nat.find_spec (show ∃ R, (4 * 2 ^ c : ℚ) ≤ discountSums f R by
    exact_mod_cast hdiv (4 * 2 ^ c))

/-- The partial sums `S_R = Σ_{i=1}^R 2^{-f(E_i)}` of a computable discount are a computable
function of `R`: a primitive recursion over `R` whose step adds `2^{-f(E_{R+1})}`, the exponents
`E_i` being themselves a primitive recursion whose step adds `g_{i+1} = 2 L (i + 2) + 3`.
Blueprint 04 Lemma choose-rounds ("each partial sum is an exact rational number"). -/
private theorem discountSums_computable {f : ℕ → ℕ} (hf : Computable f) :
    Computable (discountSums f) := by
  have hE : Computable expSchedule := by
    have hstep : Primrec stepSize :=
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (primrec_clogTwo.comp Primrec.succ)) (Primrec.const 3)).of_eq fun _ => rfl
    have hg : Primrec₂ fun (j e : ℕ) => e + stepSize (j + 1) :=
      (Primrec.nat_add.comp Primrec.snd (hstep.comp (Primrec.succ.comp Primrec.fst))).to₂
    refine (Primrec.nat_rec₁ 16 hg).to_comp.of_eq fun j => ?_
    induction j with
    | zero => rfl
    | succ j ih => rw [expSchedule, ← ih]
  have hstep : Computable₂ fun (_ : ℕ) (p : ℕ × ℚ) =>
      p.2 + (1 / 2 : ℚ) ^ f (expSchedule (p.1 + 1)) :=
    (computable₂_ratAdd.comp (Computable.snd.comp Computable.snd)
      (computable_half_pow.comp (hf.comp (hE.comp
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))))).to₂
  refine (Computable.nat_rec Computable.id (Computable.const (0 : ℚ)) hstep).of_eq fun R => ?_
  dsimp only [id]
  induction R with
  | zero => simp [discountSums]
  | succ R ih =>
    have h1 : discountSums f (R + 1) =
        discountSums f R + (1 / 2 : ℚ) ^ f (expSchedule (R + 1)) :=
      Finset.sum_Icc_succ_top (by omega) _
    rw [h1, ← ih]

/-- choose-rounds, computability: for a computable `f` with divergent partial sums the horizon
`c ↦ roundCount f hdiv c` is a total computable function (unbounded search over the decidable
rational test `4·2^c ≤ S_R`; no convergence rate is assumed).
Blueprint 04 Lemma choose-rounds ("computes a total function `R(c)`") (`04-CHOOSE-ROUNDS`). -/
theorem roundCount_computable {f : ℕ → ℕ} (hf : Computable f) (hdiv : HasDivergentSums f) :
    Computable (roundCount f hdiv) := by
  have hbound : Computable fun c : ℕ => (4 * 2 ^ c : ℚ) :=
    (computable_nat_to_rat.comp (Primrec.nat_mul.to_comp.comp (Computable.const 4)
      comp_pow)).of_eq fun c => by push_cast; rfl
  have hP : Computable fun p : ℕ × ℕ => decide ((4 * 2 ^ p.1 : ℚ) ≤ discountSums f p.2) :=
    computable_ratLe.comp (hbound.comp Computable.fst)
      ((discountSums_computable hf).comp Computable.snd)
  exact Computable.natFind (P := fun c R => (4 * 2 ^ c : ℚ) ≤ discountSums f R) hP
    fun c => by exact_mod_cast hdiv (4 * 2 ^ c)

/-- The parameters of GAME-VARIABLE: for an admissible discount `f` and every tag `c`, the
variable schedule `S` with horizon `R = roundCount f hf.div c` satisfies all hypotheses of
THEOREM-GAME at capacity `U = 1` — `S` is admissible (valid, `w_0 ≤ B_0` and all source
thresholds `t_j ≥ 0`, by B1 and T1) and `Ψ_R ≥ (1/4)·2^{-c}·Σ_{i=1}^R 2^{-f(E_i)} ≥ 1` by T1 and
the choice of the horizon. The horizon is chosen before, and independently of, the budgets.
Blueprint 04 Lemma choose-rounds (second part) and Interface GAME-VARIABLE
(`04-GAME-VARIABLE`). -/
theorem variableSchedule_isAdmissible_of_roundCount {f : ℕ → ℕ} (hf : IsAdmissibleDiscount f)
    (c : ℕ) :
    (variableSchedule f c (roundCount f hf.div c)).IsAdmissible ∧
      1 ≤ (variableSchedule f c (roundCount f hf.div c)).psi
        (variableSchedule f c (roundCount f hf.div c)).R := by
  set R := roundCount f hf.div c with hRdef
  have hSR : (variableSchedule f c R).R = R := by simp [GameSchedule.R, variableSchedule]
  have hB0 := (variableSchedule_budget_bounds (c := c) hf.mono (Nat.zero_le R)).2.2
  refine ⟨⟨variableSchedule_isValid hf.mono c R, by linarith, fun j hj hjR => ?_⟩, ?_⟩
  · rw [hSR] at hjR
    have ht := variableSchedule_threshold_ge hf.mono hf.r1 (c := c) hj hjR
    have h0 : (0 : ℚ) ≤ (1 / 4 : ℚ) * (1 / 2) ^ c * (1 / 2) ^ f (expSchedule j) := by positivity
    linarith
  · rw [hSR, GameSchedule.psi]
    have hsum : (1 / 4 : ℚ) * (1 / 2) ^ c * discountSums f R ≤
        ∑ i ∈ Finset.Icc 1 R, (variableSchedule f c R).threshold i := by
      rw [discountSums, Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => variableSchedule_threshold_ge hf.mono hf.r1
        (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2
    have hspec := mul_le_mul_of_nonneg_left (roundCount_spec hf.div c)
      (by positivity : (0 : ℚ) ≤ 1 / 4 * (1 / 2) ^ c)
    have h1 : (1 / 4 : ℚ) * (1 / 2) ^ c * (4 * 2 ^ c) = 1 := by
      rw [show (1 / 4 : ℚ) * (1 / 2) ^ c * (4 * 2 ^ c) = (1 / 2) ^ c * 2 ^ c by ring, ← mul_pow]
      norm_num
    rw [← hRdef] at hspec
    linarith

/-- The variable-discount word family: for the tag `c`, the concrete strategy
`localStrategy S S.R 1` of the schedule `S = variableSchedule f c (roundCount f hf.div c)`
(exponents `E_j`, depths `δ_j = E_j + f(E_j) + c`, capacity `U = 1`) played in the word game
`G_{f+c}` through the padding translation of LEM-SHADOW with `cap = 0` (a reply of at most
`n + f(n) + c` bits is padded with zeros to a depth-`δ` cell of `[0, 1)`).
Blueprint 04 Interface GAME-VARIABLE, instantiated (`04-GAME-VARIABLE`). -/
def variableWordFamily (f : ℕ → ℕ) (hf : IsAdmissibleDiscount f) (c : ℕ) : WordStrategy :=
  wordStrategyOfLocal 0 (variableSchedule f c (roundCount f hf.div c)).depthOfExp
    (localStrategy (variableSchedule f c (roundCount f hf.div c))
      (variableSchedule f c (roundCount f hf.div c)).R 1)

/-- On the exponents of the variable schedule the prescribed Bob depth is
`δ(n) = n + f(n) + c`: the exponent `n = E_j` sits at position `j` of the (strictly increasing)
exponent list, and `δ_j = E_j + f(E_j) + c`. Blueprint 04 Interface GAME-VARIABLE
(`δ_j = E_j + f(E_j) + c`). -/
private theorem depthOfExp_variableSchedule {f : ℕ → ℕ} (hf : Monotone f) {c R n : ℕ}
    (hn : n ∈ (variableSchedule f c R).exps) :
    (variableSchedule f c R).depthOfExp n = n + f n + c := by
  have hn' : n ∈ (List.range (R + 1)).map expSchedule := hn
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hn'
  have hjR : j < R + 1 := List.mem_range.1 hj
  have hlen : j < (variableSchedule f c R).exps.length := by simp [variableSchedule, hjR]
  have hexp : (variableSchedule f c R).exp j = expSchedule j := by
    simp [GameSchedule.exp, variableSchedule, hjR]
  have hdepth : (variableSchedule f c R).depth j = expSchedule j + f (expSchedule j) + c := by
    simp [GameSchedule.depth, variableSchedule, hjR]
  rw [← hexp, GameSchedule.depthOfExp_exp (variableSchedule_isValid hf c R) hlen, hdepth, hexp]

/-- The variable-discount family wins `G_{f+c}` uniformly in the tag: for an admissible `f`
and every `c`, `variableWordFamily f hf c` is a winning word strategy for the reply bound
`b c n = n + f n + c` within the request bound `T_R` of its schedule — every request has a
positive exponent and a fresh vertex, every path load including the pending request is at most
one, and no legal history answers `T_R` requests. The game theorem is applied (THEOREM-GAME
through `variableSchedule_isAdmissible_of_roundCount`, then LEM-SHADOW with
`hS := variableSchedule_isValid`), not assumed.
Blueprint 04 Interface GAME-VARIABLE ("a finite computable Alice strategy winning `G_{f+c}`")
(`04-VARIABLE-FAMILY-WIN`). -/
theorem variableWordFamily_winning {f : ℕ → ℕ} (hf : IsAdmissibleDiscount f) :
    IsWinningWordFamily (fun c n => n + f n + c) (variableWordFamily f hf) fun c =>
      (variableSchedule f c (roundCount f hf.div c)).requestBound
        (variableSchedule f c (roundCount f hf.div c)).R := by
  intro c
  obtain ⟨hA, hψ⟩ := variableSchedule_isAdmissible_of_roundCount hf c
  set R := roundCount f hf.div c with hRdef
  set S := variableSchedule f c R with hS
  have hwin := localStrategy_winning S hA le_rfl zero_le_one
    ⟨2 ^ S.depth S.R, by push_cast; ring⟩ hψ
  have hwin' : IsWinningLocalStrategy S S.R (2 ^ 0) 1 (S.requestBound S.R)
      (localStrategy S S.R 1) := by
    rw [pow_zero]
    rwa [GameSchedule.budget_R] at hwin
  exact wordStrategyOfLocal_winning hA.1 hwin' fun n hn => by
    rw [depthOfExp_variableSchedule hf.mono hn, Nat.add_zero]

/-- The variable-discount family is computable uniformly in the tag and the history: one
algorithm computes `(c, h) ↦ variableWordFamily f hf c h`, composed of the horizon search
(`roundCount_computable`), the schedule (`variableSchedule_computable`), the strategy
(LEM-EFF-02) and the padding translation.
Blueprint 04 Interface GAME-VARIABLE ("uniform in the finite rational data and a program for
`f`") and 03 §6 item 1 (`04-VARIABLE-FAMILY-COMP`). -/
theorem variableWordFamily_computable {f : ℕ → ℕ} (hf : IsAdmissibleDiscount f) :
    Computable fun a : ℕ × WordHistory => variableWordFamily f hf a.1 a.2 := by
  suffices key : ∀ r : ℕ → ℕ, Computable r → Computable fun a : ℕ × WordHistory =>
      wordStrategyOfLocal 0 (variableSchedule f a.1 (r a.1)).depthOfExp
        (localStrategy (variableSchedule f a.1 (r a.1)) (variableSchedule f a.1 (r a.1)).R 1)
        a.2 from key (roundCount f hf.div) (roundCount_computable hf.computable hf.div)
  -- the horizon is abstracted to a computable `r`, so that no unifier step unfolds its search
  intro r hr
  have hV := (variableSchedule_computable hf.computable).comp (Computable.id.pair hr)
  have hVR : Computable fun c : ℕ => (variableSchedule f c (r c)).R :=
    hr.of_eq fun c => by simp [GameSchedule.R, variableSchedule]
  have h := wordStrategyOfLocal_computable.comp ((Computable.const 0).pair
    ((hV.comp Computable.fst).pair ((hVR.comp Computable.fst).pair
      ((Computable.const (1 : ℚ)).pair Computable.snd))))
  exact h

end Kolmogorov
