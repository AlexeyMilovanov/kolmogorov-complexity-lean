import KolmogorovMathlib.StoppingComplexity.MarkerRound

/-!
# The finite-state strategy for the recursive game and its termination bounds

Blueprint part 02, §5 (the full recursive theorem: THEOREM-GAME, PARAM-GAME, COR-GAME-SHARP)
and §6 (LEM-EFF-01, the explicit termination bounds). The strategy of level `j` is a
*finite-state replay* (blueprint 05, recommendation 3: "encode a strategy by a finite state
machine"): a `StrategyLevelState` carries the capacity of the current level, the real
coordinate root of the current local game, the still unconsumed answers in local coordinates
and, once the replay stopped inside a marker phase, the pending chain request. `strategyLevelStep`
replays one level (the marker phase of `MarkerRound`, then the repacking of the residual region
into the next level), `strategyLevelRun` folds the levels `j, j - 1, …, 1`, and `localStrategy`
answers the pending chain request or, when every level completed, requests the final root with
the exponent `E_0`. The recursion equation `localStrategy_succ_eq_embed` identifies this object
with the blueprint's recursive description (marker phase, then `embedStrategy` on the residual
game), which is what THEOREM-GAME's induction uses. The bounds `M_j`, `T_j`, `H_j` of LEM-EFF-01
are explicit natural numbers. Computability (LEM-EFF-02) is in `StrategyComputable`.
-/

namespace Kolmogorov

/-! ### The replay state and the strategy (02-STRATEGY-DEF) -/

/-- The replay state carried from one level to the next: the capacity `U` of the current
level, the real-coordinate root `u` of the current local game, the unconsumed answers `tail`
in local coordinates (vertices relative to the root, cells mapped through the repacking maps
of the outer levels), and `pending = some r` once the replay stopped inside a marker phase
whose chain request `r` (real coordinates) is unanswered; later levels are then skipped.
Blueprint 02 §5–6 and 05 (recommendation 3). -/
structure StrategyLevelState where
  /-- The capacity of the current level. -/
  capacity : ℚ
  /-- The real-coordinate root of the current local game. -/
  root : BitString
  /-- The unconsumed answers, in the coordinates of the current local game. -/
  tail : LocalHistory
  /-- The pending chain request, if the replay stopped inside a marker phase. -/
  pending : Option Request

/-- The replay state as a product, for its `Primcodable` instance. Blueprint 02 §6. -/
def StrategyLevelState.equivProd :
    StrategyLevelState ≃ ℚ × BitString × LocalHistory × Option Request where
  toFun st := (st.capacity, st.root, st.tail, st.pending)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable StrategyLevelState := Primcodable.ofEquiv _ StrategyLevelState.equivProd

/-- One level `j ≥ 1` of the replay. If a chain request is already pending nothing happens.
Otherwise the marker phase of level `j` is replayed in the current capacity over the unconsumed
tail: if the tail ran out inside the phase, the current chain request (translated to real
coordinates) becomes pending; if the phase completed with final local root `u` and residual
region `F`, the replay continues in the residual capacity, below the root `u`, with the rest of
the tail translated into the subtree coordinates through the repacking map of `F`. Malformed
histories are simply replayed (legality is never inspected). Blueprint 02 §5 and LEM-CONTEXT. -/
def strategyLevelStep (S : GameSchedule) (j : ℕ) (st : StrategyLevelState) :
    StrategyLevelState :=
  match st.pending with
  | some _ => st
  | none =>
    let mr := replayMarkerPhase S j st.capacity st.tail
    if mr.1.stage < S.stages j st.capacity then
      { st with pending := some (st.root ++ (markerRequest S j mr.1).1, S.exp j) }
    else
      { capacity := residualCapacity S j st.capacity mr.1
        root := st.root ++ mr.1.root
        tail := virtualHistory mr.1.root
          (repackMap (S.depth (j - 1)) (residualCells S j st.capacity mr.1)) mr.2
        pending := none }

/-- The replay of the levels `j, j - 1, …, 1`, in this order, from the initial state of
capacity `U`, root `[]` and tail `h`; at level `0` it is the initial state itself.
Blueprint 02 §5. -/
def strategyLevelRun (S : GameSchedule) (j : ℕ) (U : ℚ) (h : LocalHistory) :
    StrategyLevelState :=
  (List.range j).reverse.foldl (fun st i => strategyLevelStep S (i + 1) st) ⟨U, [], h, none⟩

/-- **The strategy of level `j` in capacity `U`** (02-STRATEGY-DEF): replay the levels; if the
replay stopped inside a marker phase, answer its pending chain request, otherwise request the
final root with the exponent `E_0`. At level `0` this is the constant request `([], E_0)`.
THEOREM-GAME, LEM-EFF-01, LEM-EFF-02 and the word families of parts 03–04 all refer to exactly
this object. Blueprint 02 §5. -/
def localStrategy (S : GameSchedule) (j : ℕ) (U : ℚ) : LocalStrategy := fun h =>
  match (strategyLevelRun S j U h).pending with
  | some r => r
  | none => ((strategyLevelRun S j U h).root, S.exp 0)

/-- The replay state seen from the real root `u`: the root and a pending chain request are
translated by `u` (concatenation `x ↦ u ++ x`), the capacity and the tail are unchanged.
Blueprint 02 LEM-CONTEXT. -/
private def StrategyLevelState.translate (u : BitString) (st : StrategyLevelState) :
    StrategyLevelState :=
  { st with root := u ++ st.root, pending := st.pending.map fun r => (u ++ r.1, r.2) }

/-- One level of the replay commutes with the translation of the real root by `u`: the step
reads only the capacity and the tail, and only ever appends to the root.
Blueprint 02 §5 and LEM-CONTEXT. -/
private theorem strategyLevelStep_translate (S : GameSchedule) (k : ℕ) (u : BitString)
    (st : StrategyLevelState) :
    strategyLevelStep S k (st.translate u) = (strategyLevelStep S k st).translate u := by
  rcases st with ⟨c, root, t, _ | _⟩
  · simp only [strategyLevelStep, StrategyLevelState.translate]
    split_ifs <;> simp
  · rfl

/-- The replay of any sequence of levels commutes with the translation of the real root by `u`
(`strategyLevelStep_translate`, level by level). Blueprint 02 §5 and LEM-CONTEXT. -/
private theorem foldl_strategyLevelStep_translate (S : GameSchedule) (u : BitString)
    (l : List ℕ) (st : StrategyLevelState) :
    l.foldl (fun st i => strategyLevelStep S (i + 1) st) (st.translate u) =
      (l.foldl (fun st i => strategyLevelStep S (i + 1) st) st).translate u := by
  induction l generalizing st with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, strategyLevelStep_translate, ih]

/-- Once a chain request is pending, the replay of the remaining levels changes nothing.
Blueprint 02 §5. -/
private theorem foldl_strategyLevelStep_pending (S : GameSchedule) (l : List ℕ) (c : ℚ)
    (root : BitString) (t : LocalHistory) (r : Request) :
    l.foldl (fun st i => strategyLevelStep S (i + 1) st) ⟨c, root, t, some r⟩ =
      ⟨c, root, t, some r⟩ := by
  induction l with
  | nil => rfl
  | cons i l ih => exact ih

/-- The recursion equation of the replay: the replay of the levels `j + 1, j, …, 1` starts with
the marker phase of level `j + 1`; while that phase is incomplete its chain request stays
pending, and once it is complete the result is the replay of the levels `j, …, 1` in the
residual capacity on the unconsumed tail (translated through the repacking map), seen from the
final root. Blueprint 02 §5 and LEM-CONTEXT. -/
private theorem strategyLevelRun_succ (S : GameSchedule) (j : ℕ) (U : ℚ) (h : LocalHistory) :
    strategyLevelRun S (j + 1) U h =
      if (replayMarkerPhase S (j + 1) U h).1.stage < S.stages (j + 1) U then
        ⟨U, [], h, some (markerRequest S (j + 1) (replayMarkerPhase S (j + 1) U h).1)⟩
      else
        (strategyLevelRun S j (residualCapacity S (j + 1) U (replayMarkerPhase S (j + 1) U h).1)
          (virtualHistory (replayMarkerPhase S (j + 1) U h).1.root
            (repackMap (S.depth j)
              (residualCells S (j + 1) U (replayMarkerPhase S (j + 1) U h).1))
            (replayMarkerPhase S (j + 1) U h).2)).translate
          (replayMarkerPhase S (j + 1) U h).1.root := by
  have hfirst : strategyLevelRun S (j + 1) U h =
      (List.range j).reverse.foldl (fun st i => strategyLevelStep S (i + 1) st)
        (strategyLevelStep S (j + 1) ⟨U, [], h, none⟩) := by
    simp only [strategyLevelRun, List.range_succ, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.foldl_cons]
  rw [hfirst, strategyLevelStep]
  dsimp only
  split_ifs
  · exact foldl_strategyLevelStep_pending S _ _ _ _ _
  · rw [strategyLevelRun, ← foldl_strategyLevelStep_translate]
    simp [StrategyLevelState.translate]

/-- The recursion equation of the strategy, used by THEOREM-GAME's induction: at level
`j + 1` the strategy is the marker phase of level `j + 1` and, once that phase is complete
with final root `u` and residual region `F`, the strategy of level `j` in the residual
capacity, embedded below `u` through the repacking map of `F`
(`embedStrategy`, LEM-CONTEXT), on the unconsumed tail. Blueprint 02 §5. -/
theorem localStrategy_succ_eq_embed (S : GameSchedule) (j : ℕ) (U : ℚ) (h : LocalHistory) :
    localStrategy S (j + 1) U h =
      if (replayMarkerPhase S (j + 1) U h).1.stage < S.stages (j + 1) U then
        markerRequest S (j + 1) (replayMarkerPhase S (j + 1) U h).1
      else
        embedStrategy (replayMarkerPhase S (j + 1) U h).1.root
          (repackMap (S.depth j)
            (residualCells S (j + 1) U (replayMarkerPhase S (j + 1) U h).1))
          (localStrategy S j (residualCapacity S (j + 1) U (replayMarkerPhase S (j + 1) U h).1))
          (replayMarkerPhase S (j + 1) U h).2 := by
  dsimp only [localStrategy, embedStrategy]
  rw [strategyLevelRun_succ]
  split_ifs
  · rfl
  · generalize strategyLevelRun S j _ _ = R
    rcases R with ⟨c, root, t, _ | r⟩ <;> rfl

/-! ### Termination bounds (LEM-EFF-01) -/

/-- The marker bound `M_j = ⌊(B_j - w_j) / (L_j w_j)⌋ + 1` of level `j`.
Blueprint 02 LEM-EFF-01. -/
def GameSchedule.markerBound (S : GameSchedule) (j : ℕ) : ℕ :=
  markerCount (S.budget j) (S.weight j) (S.ratio j)

/-- The request bound `T_j`: `T_0 = 1` and
`T_j = M_j + (L_j - 1) M_j (M_j - 1) / 2 + T_{j-1}` (the product `M_j (M_j - 1)` is even, so the
division is exact). Blueprint 02 LEM-EFF-01. -/
def GameSchedule.requestBound (S : GameSchedule) : ℕ → ℕ
  | 0 => 1
  | j + 1 =>
    S.markerBound (j + 1) +
      (S.ratio (j + 1) - 1) * (S.markerBound (j + 1) * (S.markerBound (j + 1) - 1) / 2) +
        S.requestBound j

/-- The height bound `H_j`: `H_0 = 0` and
`H_j = 2 M_j + (L_j - 1) M_j (M_j - 1) / 2 + H_{j-1}`. Blueprint 02 LEM-EFF-01. -/
def GameSchedule.heightBound (S : GameSchedule) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
    2 * S.markerBound (j + 1) +
      (S.ratio (j + 1) - 1) * (S.markerBound (j + 1) * (S.markerBound (j + 1) - 1) / 2) +
        S.heightBound j

/-! ### The recursive theorem (THEOREM-GAME, COR-GAME-SHARP) -/

/-! ### The replay of a reachable history (THEOREM-GAME, LEM-EFF-01) -/

/-- The depths of a valid schedule increase along the list: `δ_i ≤ δ_k` for `i ≤ k` in range.
Blueprint 02 DEF-03. -/
private theorem depth_le_depth {S : GameSchedule} (hS : S.IsValid) {i k : ℕ} (hik : i ≤ k)
    (hk : k < S.depths.length) : S.depth i ≤ S.depth k := by
  unfold GameSchedule.depth
  rw [List.getD_eq_getElem _ _ (lt_of_le_of_lt hik hk), List.getD_eq_getElem _ _ hk]
  rcases hik.lt_or_eq with h | rfl
  · exact (List.pairwise_iff_getElem.1 hS.2.2.2.1 i k (lt_of_le_of_lt hik hk) hk h).le
  · exact le_rfl

/-- The exponent `E_i`, `i ≤ j`, is allowed at level `j`. Blueprint 02 DEF-03. -/
private theorem exp_mem_take {S : GameSchedule} (hS : S.IsValid) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ S.R) : S.exp i ∈ S.exps.take (j + 1) := by
  have hlen := hS.2.1
  unfold GameSchedule.R at hj
  unfold GameSchedule.exp
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.mem_take_iff_getElem.2 ⟨i, by simp only [lt_min_iff]; omega, rfl⟩

/-- An answer to a request allowed at level `j ≤ R` has depth at most `δ_j`.
Blueprint 02 DEF-03. -/
private theorem depthOfExp_le_of_requestAllowed {S : GameSchedule} (hS : S.IsValid) {j : ℕ}
    (hj : j ≤ S.R) {r : Request} (hr : RequestAllowed S j r) : S.depthOfExp r.2 ≤ S.depth j := by
  obtain ⟨k, hk, hkr⟩ := List.mem_take_iff_getElem.1 hr
  have hlen := hS.2.1
  have hdl := hS.1
  unfold GameSchedule.R at hj
  have hk' : k < S.exps.length := lt_of_lt_of_le hk (min_le_right _ _)
  have hkj : k ≤ j := by
    have := lt_of_lt_of_le hk (min_le_left _ _)
    omega
  have hr2 : r.2 = S.exp k := by
    unfold GameSchedule.exp
    rw [List.getD_eq_getElem _ _ hk']
    exact hkr.symm
  rw [hr2, GameSchedule.depthOfExp_exp hS hk']
  exact depth_le_depth hS hkj (by omega)

/-- Every request of the strategy of level `j ≤ R` uses one of the exponents `E_0, …, E_j`, on
every history (the pending chain requests of levels `1, …, j` and the final request `E_0`).
Blueprint 02 THEOREM-GAME ("using only exponents `E_0, …, E_j`"). -/
private theorem localStrategy_requestAllowed {S : GameSchedule} (hS : S.IsValid) {j : ℕ}
    (hj : j ≤ S.R) (U : ℚ) (h : LocalHistory) : RequestAllowed S j (localStrategy S j U h) := by
  induction j generalizing U h with
  | zero => exact exp_mem_take hS le_rfl hj
  | succ j ih =>
    rw [localStrategy_succ_eq_embed]
    split_ifs
    · exact exp_mem_take hS le_rfl hj
    · exact List.take_subset_take_left _ (by omega) (ih (by omega) _ _)

/-- The replay of the marker phase over a history extended by one answer: while the stage is
below `m` the answer is fed to `markerStep`, afterwards it is appended to the tail.
Blueprint 02 DEF-ROUND-01. -/
private theorem replayMarkerPhase_append_singleton (S : GameSchedule) (j : ℕ) (U : ℚ)
    (h : LocalHistory) (e : Request × DyadicCell) :
    replayMarkerPhase S j U (h ++ [e]) =
      if (replayMarkerPhase S j U h).1.stage < S.stages j U then
        (markerStep S j (replayMarkerPhase S j U h).1 e.2, (replayMarkerPhase S j U h).2)
      else ((replayMarkerPhase S j U h).1, (replayMarkerPhase S j U h).2 ++ [e]) := by
  simp only [replayMarkerPhase, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The strengthened replay invariant of the marker phase of level `j + 1` (DEF-ROUND-01 with
the counts of LEM-EFF-01): the part `h₁` of a history consumed by the marker phase, the replay
state `st` and the unconsumed tail satisfy the stage invariant; `h₁` has at most
`Σ_{k < stage} r_k + t - 1` answers and the root at most `Σ_{k < stage} (r_k + 1)` letters; before
the phase completes nothing is left over, and after it completes the chain position is `1` and
the tail is a legal continuation of the level-`j` strategy embedded below the final root.
Blueprint 02 DEF-ROUND-01, THEOREM-GAME and LEM-EFF-01. -/
private structure MarkerPhaseSplit (S : GameSchedule) (j : ℕ) (U : ℚ) (h₁ tail : LocalHistory)
    (st : MarkerState) : Prop where
  /-- The stage invariant at the consumed part. -/
  inv : MarkerStageInvariant S (j + 1) U h₁ st
  /-- The number of answers consumed by the marker phase. -/
  length_le : h₁.length + 1 ≤
    ∑ k ∈ Finset.range st.stage, markerChainLength (S.ratio (j + 1)) k + st.chainPos
  /-- The length of the active root. -/
  root_length_le : st.root.length ≤
    ∑ k ∈ Finset.range st.stage, (markerChainLength (S.ratio (j + 1)) k + 1)
  /-- Before the phase completes the tail is empty. -/
  tail_nil : st.stage < S.stages (j + 1) U → tail = []
  /-- After the phase completes the tail is played by the embedded strategy of level `j`. -/
  complete : S.stages (j + 1) U ≤ st.stage → st.chainPos = 1 ∧
    ReachableFrom S U (embedStrategy st.root (repackMap (S.depth j) (residualCells S (j + 1) U st))
      (localStrategy S j (residualCapacity S (j + 1) U st))) h₁ tail

/-- Every history reachable by the strategy of level `j + 1` splits as `h₁ ++ tail` along the
replay of its marker phase, with the strengthened replay invariant (induction on the history:
each marker-phase answer is a legal answer to the current chain request, LEM-ROUND-03, and after
the phase the strategy is the embedded strategy of level `j` by `localStrategy_succ_eq_embed`).
Blueprint 02 THEOREM-GAME and LEM-EFF-01. -/
private theorem exists_markerPhaseSplit {S : GameSchedule} (hS : S.IsValid) {j : ℕ}
    (hjR : j + 1 ≤ S.R) (hw : S.weight (j + 1) ≤ S.budget (j + 1)) {U : ℚ} {h : LocalHistory}
    (hh : Reachable S U (localStrategy S (j + 1) U) h) :
    ∃ h₁, h = h₁ ++ (replayMarkerPhase S (j + 1) U h).2 ∧
      MarkerPhaseSplit S j U h₁ (replayMarkerPhase S (j + 1) U h).2
        (replayMarkerPhase S (j + 1) U h).1 := by
  induction hh with
  | nil =>
    refine ⟨[], rfl, markerStageInvariant_initial S (j + 1) U, le_rfl, le_rfl,
      fun _ => rfl, fun _ => ⟨rfl, ReachableFrom.nil⟩⟩
  | @snoc h a _ ha ih =>
    obtain ⟨h₁, heq, hsp⟩ := ih
    have hσ := localStrategy_succ_eq_embed S j U h
    rw [replayMarkerPhase_append_singleton]
    rw [List.nil_append] at ha
    generalize replayMarkerPhase S (j + 1) U h = p at heq hsp hσ ⊢
    obtain ⟨st, tail⟩ := p
    dsimp only at heq hsp hσ ⊢
    subst heq
    by_cases hk : st.stage < S.stages (j + 1) U
    · rw [if_pos hk] at hσ ⊢
      have htail := hsp.tail_nil hk
      subst htail
      rw [hσ] at ha ⊢
      rw [List.append_nil] at ha ⊢
      have htr := chain_forces_new_coarse hS (by omega) hjR hsp.inv
      have hlen := hsp.length_le
      have hroot := hsp.root_length_le
      refine ⟨h₁ ++ [(markerRequest S (j + 1) st, a)], by simp,
        markerStep_invariant_of_valid hS hw (by omega) hjR hsp.inv hk ha, ?_, ?_,
        fun _ => rfl, fun hm => ⟨?_, ReachableFrom.nil⟩⟩
      · unfold markerStep
        split_ifs
        · simp only [List.length_append, List.length_singleton]
          omega
        · simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
          omega
      · unfold markerStep
        split_ifs
        · exact hroot
        · simp only [markerRequest, chainVertex, List.length_append, List.length_replicate,
            List.length_singleton, Finset.sum_range_succ]
          have := hsp.inv.one_le_chainPos
          omega
      · unfold markerStep at hm ⊢
        split_ifs at hm ⊢
        · exact absurd hm (not_le.2 hk)
        · rfl
    · rw [if_neg hk] at hσ ⊢
      rw [hσ] at ha ⊢
      refine ⟨h₁, by simp, hsp.inv, hsp.length_le, hsp.root_length_le,
        fun hk' => absurd hk' hk, fun hm => ⟨(hsp.complete hm).1, ?_⟩⟩
      exact (hsp.complete hm).2.snoc ha

/-- The entries of a history reachable by an embedded strategy whose requests are allowed at
level `j` lie below the root, use allowed exponents and were answered legally with respect to
the prior history. Blueprint 02 LEM-CONTEXT. -/
private theorem mem_of_reachableFrom_embed {S : GameSchedule} {j : ℕ} {U : ℚ} {u : BitString}
    {Φ : DyadicCell → DyadicCell} {σ : LocalStrategy} {H₀ h : LocalHistory}
    (hσ : ∀ h', RequestAllowed S j (σ h'))
    (hh : ReachableFrom S U (embedStrategy u Φ σ) H₀ h) :
    ∀ e ∈ h, u <+: e.1.1 ∧ RequestAllowed S j e.1 ∧ LegalAnswer S U H₀ e.1 e.2 := by
  induction hh with
  | nil => simp
  | @snoc h a _ ha ih =>
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact ih e he
    · rw [List.mem_singleton.1 he]
      exact ⟨List.prefix_append _ _, hσ _, ha.1, ha.2.1,
        fun e' he' => ha.2.2 e' (List.mem_append_left _ he')⟩

/-- The repacking map sends legal real answers to legal virtual answers (LEM-ROUND-05 with
LEM-REPACK-03): after a complete marker phase of level `j + 1`, a legal answer to an embedded
request allowed at level `j` is clean, so its image under `Φ` has the prescribed depth, lies in
the residual capacity and is disjoint from the images of the earlier (clean) answers at
comparable vertices. This is the hypothesis `hΦ` of LEM-CONTEXT.
Blueprint 02 LEM-ROUND-05, LEM-REPACK-03 and THEOREM-GAME. -/
private theorem repackMap_legalAnswer {S : GameSchedule} (hS : S.IsValid) {j : ℕ}
    (hjR : j + 1 ≤ S.R) {U : ℚ} {H₀ h : LocalHistory} {st : MarkerState} {r : Request}
    {c : DyadicCell} (hinv : MarkerStageInvariant S (j + 1) U H₀ st)
    (hh : ReachableFrom S U (embedStrategy st.root
      (repackMap (S.depth j) (residualCells S (j + 1) U st))
      (localStrategy S j (residualCapacity S (j + 1) U st))) H₀ h)
    (hr : RequestAllowed S j r) (hc : LegalAnswer S U (H₀ ++ h) (st.root ++ r.1, r.2) c) :
    LegalAnswer S (residualCapacity S (j + 1) U st)
      (virtualHistory st.root (repackMap (S.depth j) (residualCells S (j + 1) U st)) h) r
      (repackMap (S.depth j) (residualCells S (j + 1) U st) c) := by
  have hsub := mem_of_reachableFrom_embed
    (localStrategy_requestAllowed hS (by omega) (residualCapacity S (j + 1) U st)) hh
  have hclean : ∀ {x : BitString} {n : ℕ} {a : DyadicCell}, st.root <+: x →
      RequestAllowed S j (x, n) → LegalAnswer S U H₀ (x, n) a →
        IsClean (S.depth j) (residualCells S (j + 1) U st) a := fun hx hr' ha =>
    recursive_answer_isClean hS (by omega) hjR hinv hx
      (ha.1 ▸ depthOfExp_le_of_requestAllowed hS (by omega) hr') ha
  have hc₀ : LegalAnswer S U H₀ (st.root ++ r.1, r.2) c :=
    ⟨hc.1, hc.2.1, fun e he => hc.2.2 e (List.mem_append_left _ he)⟩
  have hcc := hclean (List.prefix_append _ _) hr hc₀
  refine ⟨by rw [repackMap_depth]; exact hc.1, repackMap_inCapacity hcc, ?_⟩
  intro e he hcomp hne
  obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
  obtain ⟨⟨x, hx⟩, hallow, hlegal⟩ := hsub e₀ he₀
  have hdrop : e₀.1.1.drop st.root.length = x := by rw [← hx, List.drop_left]
  dsimp only at hcomp hne ⊢
  rw [hdrop] at hcomp hne
  have hcomp' : IsComparable e₀.1.1 (st.root ++ r.1) := by
    rw [← hx]
    exact hcomp.imp (List.prefix_append_right_inj _).2 (List.prefix_append_right_inj _).2
  have hne' : e₀.1.1 ≠ st.root ++ r.1 := by
    rw [← hx]
    exact fun h' => hne (List.append_cancel_left h')
  have hdisj := hc.2.2 e₀ (List.mem_append_right _ he₀) hcomp' hne'
  have he₀c := hclean (x := e₀.1.1) (n := e₀.1.2) ⟨x, hx⟩ hallow hlegal
  exact (cellsDisjoint_repackMap_iff he₀c hcc).2 hdisj

/-- LEM-GAME-01 for a valid schedule with `w_0 ≤ B_0` (the source thresholds are not needed):
`w_i ≤ B_i` for every `i ≤ R`, by the forward recurrence `B_{i+1} (1 - 1/L_{i+1}) = B_i + w_{i+1}`.
Blueprint 02 LEM-GAME-01. -/
private theorem weight_le_budget_of_valid {S : GameSchedule} (hw0 : S.weight 0 ≤ S.budget 0)
    {i : ℕ} (hi : i ≤ S.R) : S.weight i ≤ S.budget i := by
  induction i with
  | zero => exact hw0
  | succ i ih =>
    have hrec := S.budget_eq_of_lt (by omega : i < S.R)
    have hwi := ih (by omega)
    have hL : (1 : ℚ) ≤ S.ratio (i + 1) := by exact_mod_cast Nat.one_le_two_pow
    have hinv0 : 0 ≤ 1 / (S.ratio (i + 1) : ℚ) := by positivity
    have hinv1 : 1 / (S.ratio (i + 1) : ℚ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hL
    have hwpos : 0 < S.weight i := by
      unfold GameSchedule.weight requestWeight
      positivity
    have hwpos' : 0 < S.weight (i + 1) := by
      unfold GameSchedule.weight requestWeight
      positivity
    set c := 1 - 1 / (S.ratio (i + 1) : ℚ)
    have hc0 : 0 ≤ c := by linarith
    have hc1 : c ≤ 1 := by linarith
    have hB : 0 < S.budget (i + 1) := by
      by_contra hneg
      have := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hc0
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hc1 hB.le]

/-- The marker load and the next budget fit: `k w_{j+1} + B_j ≤ B_{j+1}` for `k ≤ M_{j+1}`
(`M w ≤ (B - w)/L + w` and `B_j = B_{j+1} (1 - 1/L) - w_{j+1}`, so the sum is at most
`B_{j+1} - w/L`). Blueprint 02 THEOREM-GAME. -/
private theorem markerLoad_add_budget_le {S : GameSchedule} {j k : ℕ} (hjR : j + 1 ≤ S.R)
    (hw : S.weight (j + 1) ≤ S.budget (j + 1)) (hk : k ≤ S.markerBound (j + 1)) :
    (k : ℚ) * S.weight (j + 1) + S.budget j ≤ S.budget (j + 1) := by
  have hM := markerCount_mul_weight_le (S.ratio (j + 1)) hw
  have hrec := S.budget_eq_of_lt (by omega : j < S.R)
  have hwpos : 0 < S.weight (j + 1) := by
    unfold GameSchedule.weight requestWeight
    positivity
  have hL : (0 : ℚ) < S.ratio (j + 1) := by exact_mod_cast Nat.two_pow_pos _
  have hk' : (k : ℚ) * S.weight (j + 1) ≤ (S.markerBound (j + 1) : ℚ) * S.weight (j + 1) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hwpos.le
  have key : (S.budget (j + 1) - S.weight (j + 1)) / S.ratio (j + 1) + S.weight (j + 1) +
      (S.budget (j + 1) * (1 - 1 / (S.ratio (j + 1) : ℚ)) - S.weight (j + 1)) =
        S.budget (j + 1) - S.weight (j + 1) / S.ratio (j + 1) := by
    field_simp
    ring
  have hpos : 0 ≤ S.weight (j + 1) / S.ratio (j + 1) := by positivity
  unfold GameSchedule.markerBound at hk'
  linarith

/-- The chain lengths of the stages `k < M` add up to `P = M + (L - 1) M (M - 1) / 2`.
Blueprint 02 LEM-EFF-01. -/
private theorem sum_range_markerChainLength (L M : ℕ) :
    ∑ k ∈ Finset.range M, markerChainLength L k = M + (L - 1) * (M * (M - 1) / 2) := by
  simp only [markerChainLength, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one, ← Finset.sum_mul, Finset.sum_range_id]
  ring

/-- The residual capacity after a complete marker phase of level `j + 1` satisfies the
hypotheses of the level-`j` game (LEM-ROUND-06): it is nonnegative, lies on the fine grid of
level `j`, and is at most `Σ_{i=1}^{j} t_i` — it is `0` when all `N` coarse cells are marked,
and `U' < U - t_{j+1} ≤ Σ_{i=1}^{j} t_i` when `M_{j+1}` markers were placed.
Blueprint 02 LEM-ROUND-06 and THEOREM-GAME. -/
private theorem residualCapacity_bounds {S : GameSchedule} (hS : S.IsValid) (t : ℕ → ℚ)
    (hloss : ∀ i U H st, 1 ≤ i → i ≤ S.R → MarkerStageInvariant S i U H st →
      (∃ A : ℕ, U / S.fineLength i = A) → st.stage = S.markerBound i →
        residualCapacity S i U st < U - t i)
    {j : ℕ} (hjR : j + 1 ≤ S.R) (ht : ∀ i, 1 ≤ i → i ≤ j + 1 → 0 ≤ t i) {U : ℚ}
    (hgrid : ∃ A : ℕ, U * 2 ^ S.depth (j + 1) = A) (hψ : U ≤ ∑ i ∈ Finset.Icc 1 (j + 1), t i)
    {H : LocalHistory} {st : MarkerState} (hinv : MarkerStageInvariant S (j + 1) U H st)
    (hk : S.stages (j + 1) U ≤ st.stage) :
    0 ≤ residualCapacity S (j + 1) U st ∧
      (∃ A : ℕ, residualCapacity S (j + 1) U st * 2 ^ S.depth j = A) ∧
        residualCapacity S (j + 1) U st ≤ ∑ i ∈ Finset.Icc 1 j, t i := by
  refine ⟨by unfold residualCapacity packedCapacity; positivity,
    ⟨(residualCells S (j + 1) U st).length, by
      unfold residualCapacity packedCapacity
      rw [Nat.add_sub_cancel, div_mul_cancel₀ _ (by positivity)]⟩, ?_⟩
  by_cases hN : st.stage = coarseCount U (S.coarseLength (j + 1))
  · rw [residualCapacity_eq_zero_of_all_marked hS (by omega) hjR hinv hN]
    exact Finset.sum_nonneg fun i hi =>
      ht i (Finset.mem_Icc.1 hi).1 ((Finset.mem_Icc.1 hi).2.trans (Nat.le_succ j))
  · have hst : st.stage = S.markerBound (j + 1) := by
      have hle := hinv.stage_le
      unfold GameSchedule.stages stageCount at hle hk
      unfold GameSchedule.markerBound
      rcases min_choice (coarseCount U (S.coarseLength (j + 1)))
        (markerCount (S.budget (j + 1)) (S.weight (j + 1)) (S.ratio (j + 1))) with h' | h'
      · rw [h'] at hle hk
        exact absurd (le_antisymm hle hk) hN
      · rw [h'] at hle hk
        exact le_antisymm hle hk
    have hgridU : ∃ A : ℕ, U / S.fineLength (j + 1) = A := by
      obtain ⟨A, hA⟩ := hgrid
      refine ⟨A, ?_⟩
      rw [← hA]
      unfold GameSchedule.fineLength
      rw [one_div_pow, div_div_eq_mul_div, div_one]
    have hlt := hloss (j + 1) U H st (by omega) hjR hinv hgridU hst
    rw [Finset.sum_Icc_succ_top (by omega)] at hψ
    linarith

/-- **THEOREM-GAME for general thresholds** (the common core of THEOREM-GAME and
COR-GAME-SHARP): for a valid schedule with `w_0 ≤ B_0` and thresholds `t_i ≥ 0` such that every
complete marker phase with `M_i` markers loses capacity `U' < U - t_i`, the strategy of level
`j ≤ R` wins the local game of every capacity `0 ≤ U ≤ Σ_{i=1}^{j} t_i` on the fine grid. Induction
on `j`: the marker phase (LEM-ROUND-03/04) and then LEM-CONTEXT with the repacking map
(LEM-ROUND-05, LEM-REPACK-03) and the residual capacity (LEM-ROUND-06).
Blueprint 02 THEOREM-GAME. -/
private theorem localStrategy_winning_of_thresholds (S : GameSchedule) (hS : S.IsValid)
    (hw0 : S.weight 0 ≤ S.budget 0) (t : ℕ → ℚ)
    (hloss : ∀ i U H st, 1 ≤ i → i ≤ S.R → MarkerStageInvariant S i U H st →
      (∃ A : ℕ, U / S.fineLength i = A) → st.stage = S.markerBound i →
        residualCapacity S i U st < U - t i)
    {j : ℕ} (hj : j ≤ S.R) (ht : ∀ i, 1 ≤ i → i ≤ j → 0 ≤ t i) {U : ℚ} (hU : 0 ≤ U)
    (hgrid : ∃ A : ℕ, U * 2 ^ S.depth j = A) (hψ : U ≤ ∑ i ∈ Finset.Icc 1 j, t i) :
    IsWinningLocalStrategy S j U (S.budget j) (S.requestBound j) (localStrategy S j U) := by
  induction j generalizing U with
  | zero =>
    have hU0 : U = 0 := le_antisymm (by simpa using hψ) hU
    subst hU0
    intro h hh
    have hnil : h = [] := by
      cases hh with
      | nil => rfl
      | @snoc _ c _ ha =>
        exfalso
        have hpos : 0 < cellRight c := by
          unfold cellRight
          positivity
        exact absurd ha.2.1 (not_le.2 hpos)
    subst hnil
    have h0 : localStrategy S 0 0 [] = ([], S.exp 0) := rfl
    refine ⟨by simp [requestsOf], localStrategy_requestAllowed hS hj 0 [], ?_, le_rfl⟩
    intro v
    rw [h0]
    simp only [requestsOf, List.append_nil, List.map_nil, List.nil_append]
    rw [load_cons, if_pos (List.nil_prefix)]
    simpa [load] using hw0
  | succ j ih =>
    intro h hh
    have hjR : j + 1 ≤ S.R := hj
    have hw := weight_le_budget_of_valid hw0 hj
    obtain ⟨h₁, heq, hsp⟩ := exists_markerPhaseSplit hS hjR hw hh
    have hσ := localStrategy_succ_eq_embed S j U h
    generalize replayMarkerPhase S (j + 1) U h = p at heq hsp hσ
    obtain ⟨st, tail⟩ := p
    dsimp only at heq hsp hσ
    subst heq
    have hM : st.stage ≤ S.markerBound (j + 1) :=
      hsp.inv.stage_le.trans (min_le_right _ _)
    have hsumM : ∑ k ∈ Finset.range st.stage, markerChainLength (S.ratio (j + 1)) k ≤
        ∑ k ∈ Finset.range (S.markerBound (j + 1)), markerChainLength (S.ratio (j + 1)) k :=
      Finset.sum_le_sum_of_subset (Finset.range_mono hM)
    have hP := sum_range_markerChainLength (S.ratio (j + 1)) (S.markerBound (j + 1))
    by_cases hk : st.stage < S.stages (j + 1) U
    · rw [if_pos hk] at hσ
      have htail := hsp.tail_nil hk
      subst htail
      rw [hσ, List.append_nil]
      have htr := chain_forces_new_coarse hS (by omega) hjR hsp.inv
      have hlen := hsp.length_le
      have hM' : st.stage + 1 ≤ S.markerBound (j + 1) :=
        lt_of_lt_of_le hk (min_le_right _ _)
      have hsum1 : ∑ k ∈ Finset.range (st.stage + 1), markerChainLength (S.ratio (j + 1)) k ≤
          ∑ k ∈ Finset.range (S.markerBound (j + 1)), markerChainLength (S.ratio (j + 1)) k :=
        Finset.sum_le_sum_of_subset (Finset.range_mono hM')
      rw [Finset.sum_range_succ] at hsum1
      refine ⟨markerRequest_fresh hsp.inv htr, exp_mem_take hS le_rfl hj,
        markerPhase_load_le_of_valid hS hw (by omega) hjR hsp.inv hk, ?_⟩
      simp only [GameSchedule.requestBound]
      omega
    · rw [if_neg hk] at hσ
      rw [hσ]
      obtain ⟨hpos, hreach⟩ := hsp.complete (not_lt.1 hk)
      obtain ⟨hU', hgrid', hψ'⟩ :=
        residualCapacity_bounds hS t hloss hjR ht hgrid hψ hsp.inv (not_lt.1 hk)
      have hwin := embedStrategy_winning (a := (st.stage : ℚ) * S.weight (j + 1))
        (ih (by omega) (fun i hi1 hij => ht i hi1 (hij.trans (Nat.le_succ j))) hU' hgrid' hψ')
        (fun _ _ _ hh' hr hc => repackMap_legalAnswer hS hjR hsp.inv hh' hr hc)
        (fun r hr hpre => ?_)
        (fun v hv => le_of_eq (markerPhase_load_root_eq hsp.inv hpos hv))
        (fun v => ?_) (markerLoad_add_budget_le hjR hw hM) tail hreach
      · obtain ⟨hnew, hallowed, hbudget, hlen⟩ := hwin
        refine ⟨hnew, List.take_subset_take_left _ (by omega) hallowed, hbudget, ?_⟩
        have hlen₁ := hsp.length_le
        rw [hpos] at hlen₁
        simp only [GameSchedule.requestBound, List.length_append]
        omega
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
        rcases hsp.inv.request_cases e he with hm | ⟨t', ht1, ht', -⟩ | hinc
        · obtain ⟨m, hm', hme⟩ := List.mem_map.1 hm
          obtain ⟨hp, hne⟩ := hsp.inv.marker_prefix m hm'
          rw [← hme] at hpre
          exact hne (hp.eq_of_length (le_antisymm hp.length_le hpre.length_le))
        · omega
        · exact (hinc []).2 (by simpa using hpre)
      · by_cases hv : st.root <+: v
        · rw [markerPhase_load_root_eq hsp.inv hpos hv]
          have hBj : 0 ≤ S.budget j := by
            have := weight_le_budget_of_valid hw0 (by omega : j ≤ S.R)
            have hwj : 0 < S.weight j := by
              unfold GameSchedule.weight requestWeight
              positivity
            linarith
          linarith [markerLoad_add_budget_le hjR hw hM]
        · exact hsp.inv.exited_load v hv

/-- The capacity loss of a complete marker phase with `M_i` markers in the form used by
THEOREM-GAME: `U' < U - t_i` for the source threshold `t_i = (B_i - w_i)(s_i / w_i) - h_i`
(LEM-ROUND-06, the weaker source inequality). Blueprint 02 LEM-ROUND-06 and THEOREM-GAME. -/
private theorem residualCapacity_lt_sub_threshold {S : GameSchedule} (hS : S.IsAdmissible)
    {i : ℕ} {U : ℚ} {H : LocalHistory} {st : MarkerState} (hi1 : 1 ≤ i) (hiR : i ≤ S.R)
    (hinv : MarkerStageInvariant S i U H st) (hgrid : ∃ A : ℕ, U / S.fineLength i = A)
    (hM : st.stage = S.markerBound i) : residualCapacity S i U st < U - S.threshold i := by
  have := residualCapacity_lt_source hS hi1 hiR hinv hgrid hM
  unfold GameSchedule.threshold
  linarith

/-- **THEOREM-GAME** (source: T3c Theorem A′). For an admissible schedule, every level
`j ≤ R` and every capacity `U ≥ 0` on the fine grid of level `j` (`U 2^{δ_j}` integral) with
`U ≤ Ψ_j`, the strategy of level `j` wins the local game of capacity `U`: at every reachable
history the next request is fresh, uses only the exponents `E_0, …, E_j`, keeps every path
load — including the pending request — at most `B_j`, and no legal history answers `T_j`
requests. Blueprint 02 §5 THEOREM-GAME. -/
theorem localStrategy_winning (S : GameSchedule) (hS : S.IsAdmissible) {j : ℕ} (hj : j ≤ S.R)
    {U : ℚ} (hU : 0 ≤ U) (hgrid : ∃ A : ℕ, U * 2 ^ S.depth j = A) (hψ : U ≤ S.psi j) :
    IsWinningLocalStrategy S j U (S.budget j) (S.requestBound j) (localStrategy S j U) := by
  exact localStrategy_winning_of_thresholds S hS.1 hS.2.1 S.threshold
    (fun _ _ _ _ hi1 hiR hinv hgrid hM =>
      residualCapacity_lt_sub_threshold hS hi1 hiR hinv hgrid hM)
    hj (fun i hi1 hij => hS.2.2 i hi1 (hij.trans hj)) hU hgrid hψ

/-- `h_i = L_i s_i`: the coarse length is the ratio times the fine length (validity gives
`δ_{i-1} ≤ δ_i`). Blueprint 02 §3. -/
private theorem coarseLength_eq_ratio_mul {S : GameSchedule} (hS : S.IsValid) {i : ℕ}
    (hi1 : 1 ≤ i) (hiR : i ≤ S.R) : S.coarseLength i = (S.ratio i : ℚ) * S.fineLength i := by
  have hlen := hS.2.1
  have hdl := hS.1
  unfold GameSchedule.R at hiR
  have hle : S.depth (i - 1) ≤ S.depth i := depth_le_depth hS (by omega) (by omega)
  obtain ⟨e, he⟩ : ∃ e, S.depth i = S.depth (i - 1) + e := ⟨_, (Nat.add_sub_cancel' hle).symm⟩
  unfold GameSchedule.coarseLength GameSchedule.ratio GameSchedule.fineLength
  rw [he, Nat.add_sub_cancel_left, pow_add, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  rw [← mul_pow]
  norm_num

/-- LEM-ROUND-06, sharp form, for a valid schedule (none of the PARAM-GAME inequalities is
needed): after a complete marker phase with `M_i` markers on the fine grid,
`U' ≤ (N - M) h < (U + h - s) - (B_i - w_i) s / w_i = U - t♯_i`, with the sharp threshold
`t♯_i = B_i (s_i / w_i) - s_{i-1}` and `h_i = s_{i-1}`.
Blueprint 02 LEM-ROUND-06 and COR-GAME-SHARP. -/
private theorem residualCapacity_lt_sub_thresholdSharp {S : GameSchedule} (hS : S.IsValid)
    {i : ℕ} {U : ℚ} {H : LocalHistory} {st : MarkerState} (hi1 : 1 ≤ i) (hiR : i ≤ S.R)
    (hinv : MarkerStageInvariant S i U H st) (hgrid : ∃ A : ℕ, U / S.fineLength i = A)
    (hM : st.stage = S.markerBound i) : residualCapacity S i U st < U - S.thresholdSharp i := by
  have hle := residualCapacity_le_unmarked hS hi1 hiR hinv
  have hMN : st.stage ≤ coarseCount U (S.coarseLength i) :=
    hinv.stage_le.trans (min_le_left _ _)
  have hhs := coarseLength_eq_ratio_mul hS hi1 hiR
  have hs : 0 < S.fineLength i := by
    unfold GameSchedule.fineLength
    positivity
  have hw : 0 < S.weight i := by
    unfold GameSchedule.weight requestWeight
    positivity
  have hL : 1 ≤ S.ratio i := Nat.one_le_two_pow
  have hN := coarseCount_mul_coarse_le hs hL hgrid
  have hMh := markerCount_mul_coarse_gt (B := S.budget i) hw hs (by omega : 0 < S.ratio i)
  rw [hM] at hle hMN
  unfold GameSchedule.markerBound at hle hMN
  rw [hhs] at hle hMN
  rw [Nat.cast_sub hMN, sub_mul] at hle
  have key : (S.budget i - S.weight i) * S.fineLength i / S.weight i =
      S.budget i * (S.fineLength i / S.weight i) - S.fineLength i := by
    field_simp
  have hcf : S.fineLength (i - 1) = (S.ratio i : ℚ) * S.fineLength i := hhs
  unfold GameSchedule.thresholdSharp
  linarith

/-- **COR-GAME-SHARP** (optional stronger thresholds): the conclusion of THEOREM-GAME under
the sharp thresholds `Ψ♯_j = ∑_{i ≤ j} (B_i s_i / w_i - s_{i-1})`, provided each sharp threshold
up to `j` is non-negative; of PARAM-GAME only the validity of the schedule and `w_0 ≤ B_0` are
assumed (the source thresholds need not be non-negative). Blueprint 02 §5 COR-GAME-SHARP. -/
theorem localStrategy_winning_sharp (S : GameSchedule) (hS : S.IsValid)
    (hw : S.weight 0 ≤ S.budget 0) {j : ℕ}
    (hj : j ≤ S.R) (hsharp : ∀ i, 1 ≤ i → i ≤ j → 0 ≤ S.thresholdSharp i)
    {U : ℚ} (hU : 0 ≤ U) (hgrid : ∃ A : ℕ, U * 2 ^ S.depth j = A) (hψ : U ≤ S.psiSharp j) :
    IsWinningLocalStrategy S j U (S.budget j) (S.requestBound j) (localStrategy S j U) := by
  exact localStrategy_winning_of_thresholds S hS hw S.thresholdSharp
    (fun _ _ _ _ hi1 hiR hinv hgrid hM =>
      residualCapacity_lt_sub_thresholdSharp hS hi1 hiR hinv hgrid hM)
    hj hsharp hU hgrid hψ

/-- **LEM-EFF-01**, the height bound: along every reachable history of the winning play of
level `j`, the requested vertex has length at most `H_j`. Blueprint 02 §6 LEM-EFF-01. -/
theorem localStrategy_length_le (S : GameSchedule) (hS : S.IsAdmissible) {j : ℕ} (hj : j ≤ S.R)
    {U : ℚ} (hU : 0 ≤ U) (hgrid : ∃ A : ℕ, U * 2 ^ S.depth j = A) (hψ : U ≤ S.psi j) :
    ∀ h, Reachable S U (localStrategy S j U) h →
      (localStrategy S j U h).1.length ≤ S.heightBound j := by
  induction j generalizing U with
  | zero =>
    intro _ _
    exact le_of_eq rfl
  | succ j ih =>
    intro h hh
    have hw := weight_le_budget_of_valid hS.2.1 hj
    obtain ⟨h₁, heq, hsp⟩ := exists_markerPhaseSplit hS.1 hj hw hh
    have hσ := localStrategy_succ_eq_embed S j U h
    generalize replayMarkerPhase S (j + 1) U h = p at heq hsp hσ
    obtain ⟨st, tail⟩ := p
    dsimp only at heq hsp hσ
    subst heq
    have hM : st.stage ≤ S.markerBound (j + 1) := hsp.inv.stage_le.trans (min_le_right _ _)
    have hroot := hsp.root_length_le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      mul_one] at hroot
    have hP := sum_range_markerChainLength (S.ratio (j + 1)) (S.markerBound (j + 1))
    have hH : S.heightBound (j + 1) = 2 * S.markerBound (j + 1) + (S.ratio (j + 1) - 1) *
        (S.markerBound (j + 1) * (S.markerBound (j + 1) - 1) / 2) + S.heightBound j := rfl
    by_cases hk : st.stage < S.stages (j + 1) U
    · rw [if_pos hk] at hσ
      rw [hσ]
      have hM' : st.stage + 1 ≤ S.markerBound (j + 1) := lt_of_lt_of_le hk (min_le_right _ _)
      have hsum1 : ∑ k ∈ Finset.range (st.stage + 1), markerChainLength (S.ratio (j + 1)) k ≤
          ∑ k ∈ Finset.range (S.markerBound (j + 1)), markerChainLength (S.ratio (j + 1)) k :=
        Finset.sum_le_sum_of_subset (Finset.range_mono hM')
      rw [Finset.sum_range_succ] at hsum1
      have ht1 := hsp.inv.one_le_chainPos
      have hr1 : 1 ≤ markerChainLength (S.ratio (j + 1)) st.stage := Nat.le_add_left _ _
      simp only [markerRequest, chainVertex, List.length_append, List.length_replicate]
      omega
    · rw [if_neg hk] at hσ
      rw [hσ]
      obtain ⟨-, hreach⟩ := hsp.complete (not_lt.1 hk)
      obtain ⟨hU', hgrid', hψ'⟩ := residualCapacity_bounds hS.1 S.threshold
        (fun _ _ _ _ hi1 hiR hinv hgrid hM =>
          residualCapacity_lt_sub_threshold hS hi1 hiR hinv hgrid hM)
        hj (fun i hi1 hij => hS.2.2 i hi1 (hij.trans hj)) hgrid hψ hsp.inv (not_lt.1 hk)
      have hvr := reachable_virtualHistory_of_embed
        (localStrategy_winning S hS (by omega : j ≤ S.R) hU' hgrid' hψ')
        (fun _ _ _ hh' hr hc => repackMap_legalAnswer hS.1 hj hsp.inv hh' hr hc) hreach
      have hIH := ih (by omega) hU' hgrid' hψ' _ hvr
      have hsumM : ∑ k ∈ Finset.range st.stage, markerChainLength (S.ratio (j + 1)) k ≤
          ∑ k ∈ Finset.range (S.markerBound (j + 1)), markerChainLength (S.ratio (j + 1)) k :=
        Finset.sum_le_sum_of_subset (Finset.range_mono hM)
      simp only [embedStrategy, List.length_append]
      omega

/-- Along the replay of the levels, a pending chain request extends the real root of the
current local game (`strategyLevelStep` sets `pending := root ++ _` and leaves the root, and
once a request is pending the later levels change nothing). Blueprint 02 LEM-EFF-01. -/
private theorem strategyLevelRun_root_prefix (S : GameSchedule) (j : ℕ) (U : ℚ)
    (h : LocalHistory) {r : Request} (hr : (strategyLevelRun S j U h).pending = some r) :
    (strategyLevelRun S j U h).root <+: r.1 := by
  unfold strategyLevelRun at hr ⊢
  suffices key : ∀ (l : List ℕ) (st : StrategyLevelState),
      (∀ r, st.pending = some r → st.root <+: r.1) → ∀ r,
        (l.foldl (fun st i => strategyLevelStep S (i + 1) st) st).pending = some r →
          (l.foldl (fun st i => strategyLevelStep S (i + 1) st) st).root <+: r.1 from
    key _ _ (fun _ h' => by simp at h') r hr
  intro l
  induction l with
  | nil => exact fun st hst => hst
  | cons i l ih =>
    intro st hst
    refine ih _ fun r' hr' => ?_
    unfold strategyLevelStep at hr' ⊢
    rcases hp : st.pending with _ | _
    · simp only [hp] at hr' ⊢
      split_ifs at hr' ⊢
      simp only [Option.some.injEq] at hr'
      rw [← hr']
      exact List.prefix_append _ _
    · simp only [hp] at hr' ⊢
      exact hst r' (hp.trans hr')

/-- **LEM-EFF-01**, the active-root bound: along every reachable history of the winning play of
level `j`, the real root of the current local game (the `root` of the replay state) has length
at most `H_j`. The active root of a pending marker phase extends this root and is a prefix of the
pending chain request, so it is bounded by `localStrategy_length_le`.
Blueprint 02 §6 LEM-EFF-01. -/
theorem strategyLevelRun_root_length_le (S : GameSchedule) (hS : S.IsAdmissible) {j : ℕ}
    (hj : j ≤ S.R) {U : ℚ} (hU : 0 ≤ U) (hgrid : ∃ A : ℕ, U * 2 ^ S.depth j = A)
    (hψ : U ≤ S.psi j) :
    ∀ h, Reachable S U (localStrategy S j U) h →
      (strategyLevelRun S j U h).root.length ≤ S.heightBound j := by
  intro h hh
  have hlen := localStrategy_length_le S hS hj hU hgrid hψ h hh
  unfold localStrategy at hlen
  rcases hp : (strategyLevelRun S j U h).pending with _ | r
  · rw [hp] at hlen
    exact hlen
  · rw [hp] at hlen
    exact (strategyLevelRun_root_prefix S j U h hp).length_le.trans hlen

end Kolmogorov
