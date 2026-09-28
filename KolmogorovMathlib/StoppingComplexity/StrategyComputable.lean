import KolmogorovMathlib.StoppingComplexity.Strategy
import KolmogorovMathlib.StoppingComplexity.RatComputableExtras

/-!
# Computability of the strategy (LEM-EFF-02)

Blueprint part 02, §6, LEM-EFF-02: uniform computability of the strategy without a hidden
choice oracle. Every piece of the replay of `Strategy` is data-valued (`MarkerState`,
`StrategyLevelState` are `Primcodable`), so computability is assembled bottom-up from the
repository's `Primrec`/`Computable` combinators: one marker step, the replay of a marker
phase (a fold over the history), the residual region (a filtered range), one level of the
replay, the fold over the levels, and finally the strategy itself, uniformly in the schedule,
the level, the capacity and the history.
-/

namespace Kolmogorov

/-- The coarse cell of an answer is primitive recursive in the schedule, the level and the
answer: the ancestor of depth `δ_{j-1}` of the cell `(d, i)` is `(δ_{j-1}, i / 2^{d - δ_{j-1}})`.
Blueprint 02 LEM-EFF-02. -/
private theorem primrec_coarseCellOf :
    Primrec fun a : (GameSchedule × ℕ) × DyadicCell => coarseCellOf a.1.1 a.1.2 a.2 := by
  have hdepths : Primrec GameSchedule.depths :=
    (Primrec.snd.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  have hD : Primrec fun a : (GameSchedule × ℕ) × DyadicCell => a.1.1.depth (a.1.2 - 1) :=
    ((Primrec.list_getD 0).comp (hdepths.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1))).of_eq
      fun _ => rfl
  exact (hD.pair (Primrec.nat_div.comp (Primrec.snd.comp Primrec.snd)
    (nat_pow_primrec₂.comp (Primrec.const 2)
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) hD)))).of_eq fun _ => rfl

/-- Whether a cell is one of the marked coarse cells of a marker state is primitive recursive
in the schedule, the level, the state and the cell: a `List.any` over the coarse cells of the
markers. Blueprint 02 LEM-EFF-02. -/
private theorem primrec_mem_markedCoarseCells :
    Primrec fun a : ((GameSchedule × ℕ) × MarkerState) × DyadicCell =>
      decide (a.2 ∈ markedCoarseCells a.1.1.1 a.1.1.2 a.1.2) := by
  have hmarkers : Primrec MarkerState.markers :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := MarkerState.equivProd)))).of_eq
      fun _ => rfl
  have hg : Primrec fun p : (((GameSchedule × ℕ) × MarkerState) × DyadicCell) ×
      (BitString × DyadicCell) => (p.1.1.1, p.2.2) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.snd)
  have hl : Primrec fun a : ((GameSchedule × ℕ) × MarkerState) × DyadicCell => a.1.2.markers :=
    hmarkers.comp (Primrec.snd.comp Primrec.fst)
  have hcells := Primrec.list_map hl (primrec_coarseCellOf.comp hg).to₂
  have hq : Primrec₂ fun (a : ((GameSchedule × ℕ) × MarkerState) × DyadicCell)
      (b : DyadicCell) => decide (b = a.2) :=
    primrec_decideEq.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  have hp : Primrec fun a : ((GameSchedule × ℕ) × MarkerState) × DyadicCell =>
      (markedCoarseCells a.1.1.1 a.1.1.2 a.1.2).any (fun b => decide (b = a.2)) :=
    (list_any_primrec hcells hq).of_eq fun _ => rfl
  have hany : ∀ (l : List DyadicCell) (x : DyadicCell),
      l.any (fun b => decide (b = x)) = decide (x ∈ l) := by
    intro l x
    rw [Bool.eq_iff_iff]
    simp
  exact hp.of_eq fun _ => hany _ _

/-- The chain request of a marker state is primitive recursive in the schedule, the level and
the state: `(u_k 0^{r_k - t + 1}, E_j)` with `r_k = k (L_j - 1) + 1` and
`L_j = 2^{δ_j - δ_{j-1}}`. Blueprint 02 LEM-EFF-02. -/
private theorem primrec_markerRequest :
    Primrec fun a : (GameSchedule × ℕ) × MarkerState => markerRequest a.1.1 a.1.2 a.2 := by
  have hexps : Primrec GameSchedule.exps :=
    (Primrec.fst.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  have hdepths : Primrec GameSchedule.depths :=
    (Primrec.snd.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  have hroot : Primrec MarkerState.root :=
    (Primrec.fst.comp (Primrec.of_equiv (e := MarkerState.equivProd))).of_eq fun _ => rfl
  have hstage : Primrec MarkerState.stage :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := MarkerState.equivProd))))).of_eq fun _ => rfl
  have hpos : Primrec MarkerState.chainPos :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := MarkerState.equivProd))))).of_eq fun _ => rfl
  have hS : Primrec fun a : (GameSchedule × ℕ) × MarkerState => a.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hj : Primrec fun a : (GameSchedule × ℕ) × MarkerState => a.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hL : Primrec fun a : (GameSchedule × ℕ) × MarkerState => a.1.1.ratio a.1.2 :=
    (nat_pow_primrec₂.comp (Primrec.const 2) (Primrec.nat_sub.comp
      ((Primrec.list_getD 0).comp (hdepths.comp hS) hj)
      ((Primrec.list_getD 0).comp (hdepths.comp hS)
        (Primrec.nat_sub.comp hj (Primrec.const 1))))).of_eq fun _ => rfl
  have hr : Primrec fun a : (GameSchedule × ℕ) × MarkerState =>
      markerChainLength (a.1.1.ratio a.1.2) a.2.stage :=
    (Primrec.succ.comp (Primrec.nat_mul.comp (hstage.comp Primrec.snd)
      (Primrec.nat_sub.comp hL (Primrec.const 1)))).of_eq fun _ => rfl
  have hv : Primrec fun a : (GameSchedule × ℕ) × MarkerState =>
      chainVertex a.2.root (markerChainLength (a.1.1.ratio a.1.2) a.2.stage) a.2.chainPos :=
    (Primrec.list_append.comp (hroot.comp Primrec.snd) (Primrec.list_replicate.comp
      (Primrec.succ.comp (Primrec.nat_sub.comp hr (hpos.comp Primrec.snd)))
      (Primrec.const false))).of_eq fun _ => rfl
  exact (hv.pair ((Primrec.list_getD 0).comp (hexps.comp hS) hj)).of_eq fun _ => rfl

/-- One marker step is computable, uniformly in the schedule, the level, the state and the
answer. Blueprint 02 LEM-EFF-02. -/
theorem markerStep_computable :
    Computable fun a : GameSchedule × ℕ × MarkerState × DyadicCell =>
      markerStep a.1 a.2.1 a.2.2.1 a.2.2.2 := by
  have hroot : Primrec MarkerState.root :=
    (Primrec.fst.comp (Primrec.of_equiv (e := MarkerState.equivProd))).of_eq fun _ => rfl
  have hmarkers : Primrec MarkerState.markers :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := MarkerState.equivProd)))).of_eq
      fun _ => rfl
  have hstage : Primrec MarkerState.stage :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := MarkerState.equivProd))))).of_eq fun _ => rfl
  have hpos : Primrec MarkerState.chainPos :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := MarkerState.equivProd))))).of_eq fun _ => rfl
  have hSj : Primrec fun a : GameSchedule × ℕ × MarkerState × DyadicCell => (a.1, a.2.1) :=
    Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
  have hst : Primrec fun a : GameSchedule × ℕ × MarkerState × DyadicCell => a.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec fun a : GameSchedule × ℕ × MarkerState × DyadicCell => a.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hcell := primrec_coarseCellOf.comp (hSj.pair ha)
  have hdec := primrec_mem_markedCoarseCells.comp ((hSj.pair hst).pair hcell)
  have hmem : PrimrecPred fun a : GameSchedule × ℕ × MarkerState × DyadicCell =>
      coarseCellOf a.1 a.2.1 a.2.2.2 ∈ markedCoarseCells a.1 a.2.1 a.2.2.1 :=
    Primrec.primrecPred (hdec.of_eq fun _ => rfl)
  have hv := Primrec.fst.comp (primrec_markerRequest.comp (hSj.pair hst))
  have hsame : Primrec fun a : GameSchedule × ℕ × MarkerState × DyadicCell =>
      (⟨a.2.2.1.root, a.2.2.1.markers, a.2.2.1.stage, a.2.2.1.chainPos + 1⟩ : MarkerState) :=
    ((Primrec.of_equiv_symm (e := MarkerState.equivProd)).comp ((hroot.comp hst).pair
      ((hmarkers.comp hst).pair ((hstage.comp hst).pair
        (Primrec.succ.comp (hpos.comp hst)))))).of_eq fun _ => rfl
  have hnew : Primrec fun a : GameSchedule × ℕ × MarkerState × DyadicCell =>
      (⟨(markerRequest a.1 a.2.1 a.2.2.1).1 ++ [true],
        a.2.2.1.markers ++ [((markerRequest a.1 a.2.1 a.2.2.1).1, a.2.2.2)],
        a.2.2.1.stage + 1, 1⟩ : MarkerState) :=
    ((Primrec.of_equiv_symm (e := MarkerState.equivProd)).comp
      ((Primrec.list_concat.comp hv (Primrec.const true)).pair
        ((Primrec.list_concat.comp (hmarkers.comp hst) (hv.pair ha)).pair
          ((Primrec.succ.comp (hstage.comp hst)).pair (Primrec.const 1))))).of_eq fun _ => rfl
  exact (Primrec.ite hmem hsame hnew).to_comp.of_eq fun _ => rfl

/-- The marker bound `M_j = ⌊(B_j - w_j) / (L_j w_j)⌋ + 1` is computable in the schedule and the
level: with `w_j = 2^{-E_j}` and `L_j = 2^γ` the quotient is the product
`(B_j - w_j) · 2^{E_j} · 2^{-γ}` of computable rationals. Blueprint 02 LEM-EFF-02. -/
private theorem markerBound_computable :
    Computable fun a : GameSchedule × ℕ => a.1.markerBound a.2 := by
  have hexps : Primrec GameSchedule.exps :=
    (Primrec.fst.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  have hdepths : Primrec GameSchedule.depths :=
    (Primrec.snd.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  have hE : Primrec fun a : GameSchedule × ℕ => a.1.exp a.2 :=
    ((Primrec.list_getD 0).comp (hexps.comp Primrec.fst) Primrec.snd).of_eq fun _ => rfl
  have hγ : Primrec fun a : GameSchedule × ℕ => a.1.depth a.2 - a.1.depth (a.2 - 1) :=
    (Primrec.nat_sub.comp ((Primrec.list_getD 0).comp (hdepths.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD 0).comp (hdepths.comp Primrec.fst)
        (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))).of_eq fun _ => rfl
  have hw : Computable fun a : GameSchedule × ℕ => (1 / 2 : ℚ) ^ a.1.exp a.2 :=
    computable_half_pow.comp hE.to_comp
  have hq : Computable fun a : GameSchedule × ℕ =>
      (a.1.budget a.2 - (1 / 2 : ℚ) ^ a.1.exp a.2) * ((2 ^ a.1.exp a.2 : ℕ) : ℚ) *
        (1 / 2 : ℚ) ^ (a.1.depth a.2 - a.1.depth (a.2 - 1)) :=
    computable₂_ratMul.comp (computable₂_ratMul.comp
      (computable₂_ratSub.comp GameSchedule.computable_budget hw)
      (computable_nat_to_rat.comp (comp_pow.comp hE.to_comp)))
      (computable_half_pow.comp hγ.to_comp)
  refine (Primrec.succ.to_comp.comp (primrec_rat_natFloor.to_comp.comp hq)).of_eq fun a => ?_
  have hrat : ∀ (B : ℚ) (E γ : ℕ), (B - (1 / 2 : ℚ) ^ E) * ((2 ^ E : ℕ) : ℚ) * (1 / 2 : ℚ) ^ γ =
      (B - (1 / 2 : ℚ) ^ E) / (((2 ^ γ : ℕ) : ℚ) * (1 / 2 : ℚ) ^ E) := by
    intro B E γ
    push_cast
    simp only [one_div_pow]
    field_simp
  simp only [GameSchedule.markerBound, markerCount, GameSchedule.weight, requestWeight,
    GameSchedule.ratio, hrat, Nat.succ_eq_add_one]

/-- The number of marker stages `m = min ⌈U / h_j⌉ M_j` is computable in the schedule, the level
and the capacity: `U / h_j = U · 2^{δ_{j-1}}`, a ceiling of a computable rational, and the marker
bound. Blueprint 02 LEM-EFF-02. -/
private theorem stages_computable :
    Computable fun a : GameSchedule × ℕ × ℚ => a.1.stages a.2.1 a.2.2 := by
  have hdepths : Primrec GameSchedule.depths :=
    (Primrec.snd.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  have hd : Primrec fun a : GameSchedule × ℕ × ℚ => a.1.depth (a.2.1 - 1) :=
    ((Primrec.list_getD 0).comp (hdepths.comp Primrec.fst)
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))).of_eq
      fun _ => rfl
  have hcoarse : Computable fun a : GameSchedule × ℕ × ℚ =>
      ⌈a.2.2 * ((2 ^ a.1.depth (a.2.1 - 1) : ℕ) : ℚ)⌉₊ :=
    primrec_rat_natCeil.to_comp.comp (computable₂_ratMul.comp
      (Computable.snd.comp Computable.snd) (computable_nat_to_rat.comp (comp_pow.comp hd.to_comp)))
  refine (Primrec.nat_min.to_comp.comp hcoarse (markerBound_computable.comp
    (Computable.fst.pair (Computable.fst.comp Computable.snd)))).of_eq fun a => ?_
  have hdiv : ∀ (U : ℚ) (d : ℕ), U * ((2 ^ d : ℕ) : ℚ) = U / (1 / 2 : ℚ) ^ d := by
    intro U d
    push_cast
    rw [one_div_pow, div_div_eq_mul_div, div_one]
  simp only [GameSchedule.stages, stageCount, coarseCount, GameSchedule.coarseLength, hdiv,
    GameSchedule.markerBound]

/-- The replay of a marker phase is computable. Blueprint 02 LEM-EFF-02. -/
theorem replayMarkerPhase_computable :
    Computable fun a : GameSchedule × ℕ × ℚ × LocalHistory =>
      replayMarkerPhase a.1 a.2.1 a.2.2.1 a.2.2.2 := by
  have hstage : Primrec MarkerState.stage :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := MarkerState.equivProd))))).of_eq fun _ => rfl
  have h1 : Computable fun y : (GameSchedule × ℕ × ℚ × LocalHistory) ×
      ((MarkerState × LocalHistory) × (Request × DyadicCell)) => y.2.1.1.stage :=
    hstage.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.snd))
  have hlevel : Computable fun y : (GameSchedule × ℕ × ℚ × LocalHistory) ×
      ((MarkerState × LocalHistory) × (Request × DyadicCell)) => (y.1.1, y.1.2.1, y.1.2.2.1) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))))
  have h2 := stages_computable.comp hlevel
  have hc := Primrec.nat_lt.decide.to_comp.comp h1 h2
  have hargs : Computable fun y : (GameSchedule × ℕ × ℚ × LocalHistory) ×
      ((MarkerState × LocalHistory) × (Request × DyadicCell)) =>
      (y.1.1, y.1.2.1, y.2.1.1, y.2.2.2) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        ((Computable.fst.comp (Computable.fst.comp Computable.snd)).pair
          (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have hmark := (markerStep_computable.comp hargs).pair
    (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have htail : Computable fun y : (GameSchedule × ℕ × ℚ × LocalHistory) ×
      ((MarkerState × LocalHistory) × (Request × DyadicCell)) =>
      (y.2.1.1, y.2.1.2 ++ [y.2.2]) :=
    (Computable.fst.comp (Computable.fst.comp Computable.snd)).pair
      (Primrec.list_concat.to_comp.comp
        (Computable.snd.comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd))
  refine (Computable.list_foldl (Computable.snd.comp (Computable.snd.comp Computable.snd))
    (Computable.const (initialMarkerState, ([] : LocalHistory)))
    (Computable.cond hc hmark htail).to₂).of_eq fun a => ?_
  simp only [replayMarkerPhase, Bool.cond_decide]

/-- Containment of the depth-`D` cell `(D, i)` in `[0, U)` is decidable by a computable
comparison of rationals, `(i + 1) · 2^{-D} ≤ U`, uniformly in `(U, D)` and `i`.
Blueprint 02 LEM-EFF-02. -/
private theorem computable_cellInCapacity :
    Computable₂ fun (a : ℚ × ℕ) (i : ℕ) => decide (CellInCapacity a.1 (a.2, i)) := by
  have hr := computable₂_ratMul.comp
    (computable_nat_to_rat.comp (Computable.succ.comp (Computable.snd (α := ℚ × ℕ) (β := ℕ))))
    (computable_half_pow.comp (Computable.snd.comp (Computable.fst (α := ℚ × ℕ) (β := ℕ))))
  refine (computable_ratLe.comp hr (Computable.fst.comp Computable.fst)).of_eq fun p => ?_
  simp only [CellInCapacity, cellRight, one_div_pow, Nat.cast_succ, mul_one_div]

/-- The residual region of a marker state is computable. Blueprint 02 LEM-EFF-02. -/
theorem residualCells_computable :
    Computable fun a : GameSchedule × ℕ × ℚ × MarkerState =>
      residualCells a.1 a.2.1 a.2.2.1 a.2.2.2 := by
  have hdepths : Primrec GameSchedule.depths :=
    (Primrec.snd.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  have hD : Primrec fun a : GameSchedule × ℕ × ℚ × MarkerState => a.1.depth (a.2.1 - 1) :=
    ((Primrec.list_getD 0).comp (hdepths.comp Primrec.fst)
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))).of_eq
      fun _ => rfl
  have hU : Computable fun a : GameSchedule × ℕ × ℚ × MarkerState => a.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hN := primrec_rat_natCeil.to_comp.comp (computable₂_ratMul.comp hU
    (computable_nat_to_rat.comp (comp_pow.comp hD.to_comp)))
  have hUD : Computable fun p : (GameSchedule × ℕ × ℚ × MarkerState) × ℕ =>
      (p.1.2.2.1, p.1.1.depth (p.1.2.1 - 1)) :=
    (hU.comp Computable.fst).pair (hD.to_comp.comp Computable.fst)
  have hcap := computable_cellInCapacity.comp hUD Computable.snd
  have hargs : Primrec fun p : (GameSchedule × ℕ × ℚ × MarkerState) × ℕ =>
      (((p.1.1, p.1.2.1), p.1.2.2.2), (p.1.1.depth (p.1.2.1 - 1), p.2)) :=
    (((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair
      ((hD.comp Primrec.fst).pair Primrec.snd)
  have hmem := (primrec_mem_markedCoarseCells.comp hargs).to_comp
  refine (computable_list_filter (Primrec.list_range.to_comp.comp hN)
    (Primrec.and.to_comp.comp hcap (Primrec.not.to_comp.comp hmem)).to₂).of_eq fun a => ?_
  have hdiv : ∀ (U : ℚ) (d : ℕ), U * ((2 ^ d : ℕ) : ℚ) = U / (1 / 2 : ℚ) ^ d := by
    intro U d
    push_cast
    rw [one_div_pow, div_div_eq_mul_div, div_one]
  simp only [residualCells, coarseCount, GameSchedule.coarseLength, hdiv]

/-- One level of the replay is computable. Blueprint 02 LEM-EFF-02. -/
theorem strategyLevelStep_computable :
    Computable fun a : GameSchedule × ℕ × StrategyLevelState =>
      strategyLevelStep a.1 a.2.1 a.2.2 := by
  have hcap : Primrec StrategyLevelState.capacity :=
    (Primrec.fst.comp (Primrec.of_equiv (e := StrategyLevelState.equivProd))).of_eq fun _ => rfl
  have hroot : Primrec StrategyLevelState.root :=
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := StrategyLevelState.equivProd)))).of_eq fun _ => rfl
  have htail : Primrec StrategyLevelState.tail :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := StrategyLevelState.equivProd))))).of_eq fun _ => rfl
  have hpending : Primrec StrategyLevelState.pending :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := StrategyLevelState.equivProd))))).of_eq fun _ => rfl
  have hstage : Primrec MarkerState.stage :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := MarkerState.equivProd))))).of_eq fun _ => rfl
  have hmroot : Primrec MarkerState.root :=
    (Primrec.fst.comp (Primrec.of_equiv (e := MarkerState.equivProd))).of_eq fun _ => rfl
  have hexps : Primrec GameSchedule.exps :=
    (Primrec.fst.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  have hdepths : Primrec GameSchedule.depths :=
    (Primrec.snd.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  have hS : Computable fun a : GameSchedule × ℕ × StrategyLevelState => a.1 := Computable.fst
  have hj : Computable fun a : GameSchedule × ℕ × StrategyLevelState => a.2.1 :=
    Computable.fst.comp Computable.snd
  have hst : Computable fun a : GameSchedule × ℕ × StrategyLevelState => a.2.2 :=
    Computable.snd.comp Computable.snd
  have hU : Computable fun a : GameSchedule × ℕ × StrategyLevelState => a.2.2.capacity :=
    hcap.to_comp.comp hst
  have hr : Computable fun a : GameSchedule × ℕ × StrategyLevelState => a.2.2.root :=
    hroot.to_comp.comp hst
  have hmr := replayMarkerPhase_computable.comp
    (hS.pair (hj.pair (hU.pair (htail.to_comp.comp hst))))
  have hmr1 := Computable.fst.comp hmr
  have hc := Primrec.nat_lt.decide.to_comp.comp (hstage.to_comp.comp hmr1)
    (stages_computable.comp (hS.pair (hj.pair hU)))
  have hreq := primrec_markerRequest.to_comp.comp ((hS.pair hj).pair hmr1)
  have hexp : Computable fun a : GameSchedule × ℕ × StrategyLevelState => a.1.exp a.2.1 :=
    ((Primrec.list_getD 0).to_comp.comp (hexps.to_comp.comp hS) hj).of_eq fun _ => rfl
  have hpend := (Primrec.of_equiv_symm (e := StrategyLevelState.equivProd)).to_comp.comp
    (hU.pair (hr.pair ((htail.to_comp.comp hst).pair (Computable.option_some.comp
      ((Primrec.list_append.to_comp.comp hr (Computable.fst.comp hreq)).pair hexp)))))
  have hD : Computable fun a : GameSchedule × ℕ × StrategyLevelState => a.1.depth (a.2.1 - 1) :=
    ((Primrec.list_getD 0).to_comp.comp (hdepths.to_comp.comp hS)
      (Primrec.nat_sub.to_comp.comp hj (Computable.const 1))).of_eq fun _ => rfl
  have hF := residualCells_computable.comp (hS.pair (hj.pair (hU.pair hmr1)))
  have hcapF := computable₂_ratMul.comp (computable_nat_to_rat.comp
    (Primrec.list_length.to_comp.comp hF)) (computable_half_pow.comp hD)
  have hroot' := Primrec.list_append.to_comp.comp hr (hmroot.to_comp.comp hmr1)
  have hΦ := primrec_repackMap.to_comp.comp
    (((hD.comp Computable.fst).pair (hF.comp Computable.fst)).pair
      (Computable.snd.comp (Computable.snd (α := GameSchedule × ℕ × StrategyLevelState)
        (β := Request × DyadicCell))))
  have hdrop := Primrec.list_drop.to_comp.comp
    (Computable.fst.comp (Computable.fst.comp (Computable.snd
      (α := GameSchedule × ℕ × StrategyLevelState) (β := Request × DyadicCell))))
    (Primrec.list_length.to_comp.comp ((hmroot.to_comp.comp hmr1).comp Computable.fst))
  have hentry := (hdrop.pair (Computable.snd.comp (Computable.fst.comp Computable.snd))).pair hΦ
  have hvirt := Computable.list_map (Computable.snd.comp hmr) hentry.to₂
  have hnext := (Primrec.of_equiv_symm (e := StrategyLevelState.equivProd)).to_comp.comp
    (hcapF.pair (hroot'.pair (hvirt.pair (Computable.const (none : Option Request)))))
  have hnone := Computable.cond hc hpend hnext
  refine (Computable.option_casesOn (hpending.to_comp.comp hst) hnone
    (hst.comp Computable.fst).to₂).of_eq fun a => ?_
  obtain ⟨S, j, U, r, t, p⟩ := a
  cases p with
  | some _ => rfl
  | none =>
    simp only [strategyLevelStep, Bool.cond_decide, residualCapacity, packedCapacity,
      virtualHistory, one_div_pow, mul_one_div]
    rfl

/-- The replay of all levels is computable (a fold over `(List.range j).reverse`).
Blueprint 02 LEM-EFF-02. -/
theorem strategyLevelRun_computable :
    Computable fun a : GameSchedule × ℕ × ℚ × LocalHistory =>
      strategyLevelRun a.1 a.2.1 a.2.2.1 a.2.2.2 := by
  have hl : Computable fun a : GameSchedule × ℕ × ℚ × LocalHistory => (List.range a.2.1).reverse :=
    (Primrec.list_reverse.comp (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd))).to_comp
  have hinit := (Primrec.of_equiv_symm (e := StrategyLevelState.equivProd)).to_comp.comp
    ((Computable.fst.comp (Computable.snd.comp (Computable.snd
      (α := GameSchedule) (β := ℕ × ℚ × LocalHistory)))).pair
      ((Computable.const ([] : BitString)).pair
        ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair
          (Computable.const (none : Option Request)))))
  have hstep := strategyLevelStep_computable.comp
    ((Computable.fst.comp (Computable.fst (α := GameSchedule × ℕ × ℚ × LocalHistory)
      (β := StrategyLevelState × ℕ))).pair
      ((Computable.succ.comp (Computable.snd.comp Computable.snd)).pair
        (Computable.fst.comp Computable.snd)))
  exact (Computable.list_foldl hl hinit hstep.to₂).of_eq fun _ => rfl

/-- **LEM-EFF-02.** The strategy is computable, uniformly in the schedule, the level, the
capacity and the history: there is one algorithm that, given the finite data of the game and
a history, outputs the next request. Blueprint 02 LEM-EFF-02. -/
theorem localStrategy_computable :
    Computable fun a : GameSchedule × ℕ × ℚ × LocalHistory =>
      localStrategy a.1 a.2.1 a.2.2.1 a.2.2.2 := by
  have hpending : Primrec StrategyLevelState.pending :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := StrategyLevelState.equivProd))))).of_eq fun _ => rfl
  have hroot : Primrec StrategyLevelState.root :=
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := StrategyLevelState.equivProd)))).of_eq fun _ => rfl
  have hexp0 : Primrec fun S : GameSchedule => S.exp 0 :=
    ((Primrec.list_getD 0).comp ((Primrec.fst.comp
      (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl)
      (Primrec.const 0)).of_eq fun _ => rfl
  refine (Computable.option_casesOn (hpending.to_comp.comp strategyLevelRun_computable)
    ((hroot.to_comp.comp strategyLevelRun_computable).pair (hexp0.to_comp.comp Computable.fst))
    Computable.snd.to₂).of_eq fun a => ?_
  unfold localStrategy
  split <;> simp_all

end Kolmogorov
