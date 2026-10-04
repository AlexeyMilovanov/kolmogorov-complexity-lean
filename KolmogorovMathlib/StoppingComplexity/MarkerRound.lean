/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.StoppingComplexity.CellCounting
import KolmogorovMathlib.StoppingComplexity.LegalHistory
import KolmogorovMathlib.StoppingComplexity.Repacking

/-!
# One round of the game: markers, chains and the residual space

Blueprint part 02, §3 (ROUND-PARAMS, LEM-ROUND-01, DEF-ROUND-01, LEM-ROUND-02, LEM-ROUND-03,
LEM-ROUND-04) and §4 (RESIDUAL, LEM-ROUND-05, LEM-ROUND-06). At a level `j ≥ 1` with weight
`w = w_j`, fine length `s = s_j`, coarse length `h = h_j = L s` and budget `B = B_j`, the round
parameters are `M = ⌊(B - w)/(L w)⌋ + 1`, `N = ⌈U/h⌉` and `m = min N M` (rational ratio, never a
truncated exponent). The marker phase is a finite-state replay: a `MarkerState` records the
active root, the markers placed so far, the stage `k` and the position `t` on the current
deepest-first zero chain; `markerStep` processes one Bob answer and `replayMarkerPhase` replays
a history. `MarkerStageInvariant` is the stage invariant of DEF-ROUND-01, stated for every chain
position so that it is preserved by every step (LEM-ROUND-03); the chain-position bound
`chain_forces_new_coarse` is LEM-ROUND-02, the load bounds including the pending request are
LEM-ROUND-04, and the residual region `F`, its capacity `U' = |F| h`, the cleanness of the
recursive answers (LEM-ROUND-05) and the capacity loss with the explicit cancellation
(LEM-ROUND-06) close the round.
-/

namespace Kolmogorov

/-! ### Round parameters (ROUND-PARAMS, LEM-ROUND-01) -/

/-- The marker count `M = ⌊(B - w) / (L w)⌋ + 1`, with the rational ratio (the source's
`⌊(B - 2^{-E_j}) 2^{E_j - γ}⌋ + 1` without a truncated exponent). Blueprint 02 §3. -/
def markerCount (B w : ℚ) (L : ℕ) : ℕ := ⌊(B - w) / (L * w)⌋₊ + 1

/-- The number `N = ⌈U / h⌉` of coarse cells meeting `[0, U)`. Blueprint 02 §3. -/
def coarseCount (U h : ℚ) : ℕ := ⌈U / h⌉₊

/-- The number of marker stages `m = min N M`. Blueprint 02 §3. -/
def stageCount (U h B w : ℚ) (L : ℕ) : ℕ := min (coarseCount U h) (markerCount B w L)

/-- The chain length `r = k (L - 1) + 1` of stage `k`. Blueprint 02 LEM-ROUND-02. -/
def markerChainLength (L k : ℕ) : ℕ := k * (L - 1) + 1

/-- The chain vertex `v_t = u_k 0^{r - t + 1}`, `1 ≤ t ≤ r`, of the deepest-first chain below
the active root. Blueprint 02 LEM-ROUND-02. -/
def chainVertex (root : BitString) (r t : ℕ) : BitString := root ++ List.replicate (r - t + 1) false

/-- The number of marker stages of level `j` in capacity `U`, read off the schedule:
`min ⌈U / h_j⌉ (⌊(B_j - w_j)/(L_j w_j)⌋ + 1)`. Blueprint 02 §3. -/
def GameSchedule.stages (S : GameSchedule) (j : ℕ) (U : ℚ) : ℕ :=
  stageCount U (S.coarseLength j) (S.budget j) (S.weight j) (S.ratio j)

/-- `M ≥ 1`. Blueprint 02 LEM-ROUND-01. -/
theorem markerCount_pos (B w : ℚ) (L : ℕ) : 1 ≤ markerCount B w L := by
  unfold markerCount
  omega

/-- `(M - 1) L w + w ≤ B` when `w ≤ B` (the hypothesis `B ≤ 1` of the text is not needed).
Blueprint 02 LEM-ROUND-01. -/
theorem markerCount_pred_load_le {B w : ℚ} (L : ℕ) (hw : w ≤ B) :
    ((markerCount B w L - 1 : ℕ) : ℚ) * L * w + w ≤ B := by
  unfold markerCount
  have h_add_sub : ⌊(B - w) / (L * w)⌋₊ + 1 - 1 = ⌊(B - w) / (L * w)⌋₊ := by
    exact Nat.add_sub_cancel ⌊(B - w) / (L * w)⌋₊ 1
  rw [h_add_sub]
  by_cases hLw : 0 < (L : ℚ) * w
  · have h_floor : (⌊(B - w) / (L * w)⌋₊ : ℚ) ≤ (B - w) / (L * w) := by
      apply Nat.floor_le
      apply div_nonneg
      · linarith
      · exact le_of_lt hLw
    have h_mul : (⌊(B - w) / (L * w)⌋₊ : ℚ) * ((L : ℚ) * w) ≤
      ((B - w) / (L * w)) * ((L : ℚ) * w) := by
      exact mul_le_mul_of_nonneg_right h_floor (le_of_lt hLw)
    have h_div_mul : ((B - w) / (L * w)) * ((L : ℚ) * w) = B - w := by
      exact div_mul_cancel₀ (B - w) (ne_of_gt hLw)
    rw [h_div_mul] at h_mul
    linarith
  · push Not at hLw
    have h_nonpos : (B - w) / (L * w) ≤ 0 := by
      apply div_nonpos_of_nonneg_of_nonpos
      · linarith
      · exact hLw
    have h_floor_zero : ⌊(B - w) / (L * w)⌋₊ = 0 := by
      exact Nat.floor_of_nonpos h_nonpos
    rw [h_floor_zero]
    simp only [CharP.cast_eq_zero, zero_mul, zero_add, ge_iff_le]
    exact hw

/-- `M w ≤ (B - w) / L + w` when `w ≤ B`. Blueprint 02 LEM-ROUND-01. -/
theorem markerCount_mul_weight_le {B w : ℚ} (L : ℕ) (hw : w ≤ B) :
    (markerCount B w L : ℚ) * w ≤ (B - w) / L + w := by
  unfold markerCount
  push_cast
  by_cases hLw : 0 < (L : ℚ) * w
  · have hw_pos : 0 < w := pos_of_mul_pos_right hLw (Nat.cast_nonneg L)
    have h_floor : (⌊(B - w) / (L * w)⌋₊ : ℚ) ≤ (B - w) / (L * w) := by
      apply Nat.floor_le
      apply div_nonneg
      · linarith
      · exact le_of_lt hLw
    have h_mul : (⌊(B - w) / (L * w)⌋₊ : ℚ) * w ≤ ((B - w) / (L * w)) * w := by
      exact mul_le_mul_of_nonneg_right h_floor (le_of_lt hw_pos)
    have h_rw : ((B - w) / (L * w)) * w = (B - w) / L := by
      calc ((B - w) / (L * w)) * w = (B - w) / ((L : ℚ) * w) * w := by rfl
        _ = (B - w) / (L : ℚ) / w * w := by rw [div_mul_eq_div_div]
        _ = (B - w) / L := div_mul_cancel₀ _ (ne_of_gt hw_pos)
    rw [h_rw] at h_mul
    linarith
  · push Not at hLw
    have h_nonpos : (B - w) / (L * w) ≤ 0 := by
      apply div_nonpos_of_nonneg_of_nonpos
      · linarith
      · exact hLw
    have h_floor_zero : ⌊(B - w) / (L * w)⌋₊ = 0 := by
      exact Nat.floor_of_nonpos h_nonpos
    rw [h_floor_zero]
    simp
    by_cases hL : L = 0
    · subst hL
      simp
    · have hL_pos : 0 < (L : ℚ) := by
        exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hL)
      have hw_nonpos : w ≤ 0 := nonpos_of_mul_nonpos_right hLw hL_pos
      have h_div_nonneg : 0 ≤ (B - w) / L := by
        apply div_nonneg
        · linarith
        · exact le_of_lt hL_pos
      linarith

/-- `M h > (B - w) s / w` for `h = L s`, with `w, s > 0` and `L ≥ 1` (positivity of the
schedule parameters, automatic for `w = 2^{-E}`, `s = 2^{-δ}`, `L = 2^γ`).
Blueprint 02 LEM-ROUND-01. -/
theorem markerCount_mul_coarse_gt {B w s : ℚ} {L : ℕ} (hw : 0 < w) (hs : 0 < s) (hL : 0 < L) :
    (B - w) * s / w < (markerCount B w L : ℚ) * (L * s) := by
  unfold markerCount
  have _ := hw
  have h_lt : (B - w) / (L * w) < ((⌊(B - w) / (L * w)⌋₊ + 1 : ℕ) : ℚ) := by
    have := Nat.lt_floor_add_one ((B - w) / ((L : ℚ) * w))
    exact_mod_cast this
  have hLs_pos : 0 < (L : ℚ) * s := by
    exact mul_pos (Nat.cast_pos.mpr hL) hs
  have h_mul : ((B - w) / ((L : ℚ) * w)) * ((L : ℚ) * s) <
      ((⌊(B - w) / (L * w)⌋₊ + 1 : ℕ) : ℚ) * ((L : ℚ) * s) := by
    exact mul_lt_mul_of_pos_right h_lt hLs_pos
  have h_rw : ((B - w) / ((L : ℚ) * w)) * ((L : ℚ) * s) = (B - w) * s / w := by
    calc ((B - w) / ((L : ℚ) * w)) * ((L : ℚ) * s) =
        ((B - w) / ((L : ℚ) * w)) * (L : ℚ) * s := by rw [mul_assoc]
      _ = (B - w) / (L : ℚ) / w * (L : ℚ) * s := by rw [div_mul_eq_div_div]
      _ = (B - w) / w / (L : ℚ) * (L : ℚ) * s := by rw [div_right_comm]
      _ = (B - w) / w * s := by rw [div_mul_cancel₀ _ (ne_of_gt (Nat.cast_pos.mpr hL))]
      _ = (B - w) * s / w := by rw [div_mul_eq_mul_div]
  rwa [h_rw] at h_mul

/-- `N h ≤ U + h - s` for `h = L s` when `U / s` is a natural number (the fine-grid condition;
valid at `U = 0`). Blueprint 02 LEM-ROUND-01. -/
theorem coarseCount_mul_coarse_le {U s : ℚ} {L : ℕ} (hs : 0 < s) (hL : 1 ≤ L)
    (hgrid : ∃ A : ℕ, U / s = A) :
    (coarseCount U (L * s) : ℚ) * (L * s) ≤ U + L * s - s := by
  unfold coarseCount
  rcases hgrid with ⟨A, hA⟩
  have hU : U = A * s := by
    calc U = (U / s) * s := by rw [div_mul_cancel₀ _ (ne_of_gt hs)]
      _ = A * s := by rw [hA]
  have h_arg : U / ((L : ℚ) * s) = A / (L : ℚ) := by
    calc U / ((L : ℚ) * s) = (A * s) / ((L : ℚ) * s) := by rw [hU]
      _ = A / (L : ℚ) := by rw [mul_div_mul_right (A : ℚ) (L : ℚ) (ne_of_gt hs)]
  rw [h_arg]
  have h_ceil : (⌈(A : ℚ) / (L : ℚ)⌉₊ : ℚ) * L ≤ (A : ℚ) + L - 1 := by
    have h_ceil_lt2 : (⌈(A : ℚ) / L⌉₊ : ℚ) < (A : ℚ) / L + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hL_pos : (0 : ℚ) < L := by exact Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_one hL)
    have h_mul : (⌈(A : ℚ) / L⌉₊ : ℚ) * L < ((A : ℚ) / L + 1) * L :=
      mul_lt_mul_of_pos_right h_ceil_lt2 hL_pos
    have h_rw : ((A : ℚ) / L + 1) * L = A + L := by
      calc ((A : ℚ) / L + 1) * L = (A : ℚ) / L * L + L := by rw [add_mul, one_mul]
        _ = A + L := by rw [div_mul_cancel₀ _ (ne_of_gt hL_pos)]
    rw [h_rw] at h_mul
    have h_mul_nat : ⌈(A : ℚ) / L⌉₊ * L < A + L := by exact_mod_cast h_mul
    have h_le_sub_one : ⌈(A : ℚ) / L⌉₊ * L ≤ A + L - 1 := Nat.le_sub_one_of_lt h_mul_nat
    have h_cast : ((⌈(A : ℚ) / L⌉₊ * L : ℕ) : ℚ) ≤ ((A + L - 1 : ℕ) : ℚ) := by
      exact_mod_cast h_le_sub_one
    have h_cast2 : ((A + L - 1 : ℕ) : ℚ) = (A : ℚ) + L - 1 := by
      rw [Nat.cast_sub (le_trans hL (Nat.le_add_left L A))]
      push_cast
      rfl
    calc (⌈(A : ℚ) / (L : ℚ)⌉₊ : ℚ) * L = ((⌈(A : ℚ) / L⌉₊ * L : ℕ) : ℚ) := by push_cast; rfl
      _ ≤ ((A + L - 1 : ℕ) : ℚ) := h_cast
      _ = (A : ℚ) + L - 1 := h_cast2
  have h_mul_s : (⌈(A : ℚ) / L⌉₊ : ℚ) * (L * s) ≤ ((A : ℚ) + L - 1) * s := by
    calc (⌈(A : ℚ) / L⌉₊ : ℚ) * ((L : ℚ) * s) = (⌈(A : ℚ) / L⌉₊ : ℚ) * L * s := by rw [mul_assoc]
      _ ≤ ((A : ℚ) + L - 1) * s := mul_le_mul_of_nonneg_right h_ceil (le_of_lt hs)
  have h_rw2 : ((A : ℚ) + L - 1) * s = U + L * s - s := by
    calc ((A : ℚ) + L - 1) * s = ((A : ℚ) + L) * s - 1 * s := by rw [sub_mul]
      _ = (A : ℚ) * s + (L : ℚ) * s - 1 * s := by rw [add_mul]
      _ = U + L * s - s := by rw [← hU, one_mul]
  rwa [h_rw2] at h_mul_s

/-! ### The marker phase as a finite-state replay (DEF-ROUND-01) -/

/-- The replay state of the marker phase: the active root `u_k`, the markers placed so far
(vertex and Bob cell), the stage `k` and the position `t` on the current chain.
Blueprint 02 DEF-ROUND-01. -/
structure MarkerState where
  /-- The active root `u_k`. -/
  root : BitString
  /-- The markers `(vertex, Bob cell)` placed so far. -/
  markers : List (BitString × DyadicCell)
  /-- The stage `k`. -/
  stage : ℕ
  /-- The position `t ≥ 1` on the current deepest-first chain. -/
  chainPos : ℕ

/-- A marker state is a tuple. Blueprint 02 DEF-ROUND-01. -/
def MarkerState.equivProd : MarkerState ≃ BitString × List (BitString × DyadicCell) × ℕ × ℕ where
  toFun st := (st.root, st.markers, st.stage, st.chainPos)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := by intro st; cases st; rfl
  right_inv := by intro p; rfl

/-- Marker states are `Primcodable` through the tuple. Blueprint 02 DEF-ROUND-01. -/
instance : Primcodable MarkerState := Primcodable.ofEquiv _ MarkerState.equivProd

/-- The initial state: local root `[]`, no markers, stage `0`, chain position `1`.
Blueprint 02 DEF-ROUND-01. -/
def initialMarkerState : MarkerState := ⟨[], [], 0, 1⟩

/-- The current chain request `(v_t, E_j)` of a state. Blueprint 02 LEM-ROUND-02. -/
def markerRequest (S : GameSchedule) (j : ℕ) (st : MarkerState) : Request :=
  (chainVertex st.root (markerChainLength (S.ratio j) st.stage) st.chainPos, S.exp j)

/-- The coarse (depth `δ_{j-1}`) cell containing a Bob cell of level `j`.
Blueprint 02 §3. -/
def coarseCellOf (S : GameSchedule) (j : ℕ) (a : DyadicCell) : DyadicCell :=
  cellAncestor a (S.depth (j - 1))

/-- The coarse cells marked so far. Blueprint 02 DEF-ROUND-01. -/
def markedCoarseCells (S : GameSchedule) (j : ℕ) (st : MarkerState) : List DyadicCell :=
  st.markers.map fun e => coarseCellOf S j e.2

/-- Process Bob's answer `a` to the current chain request: an answer in a new coarse cell
becomes a marker at `v_t`, the root advances to `v_t 1`, the stage increases and the chain
restarts at `t = 1`; otherwise the chain advances to `t + 1`. Blueprint 02 LEM-ROUND-03. -/
def markerStep (S : GameSchedule) (j : ℕ) (st : MarkerState) (a : DyadicCell) : MarkerState :=
  if coarseCellOf S j a ∈ markedCoarseCells S j st then
    ⟨st.root, st.markers, st.stage, st.chainPos + 1⟩
  else
    ⟨(markerRequest S j st).1 ++ [true], st.markers ++ [((markerRequest S j st).1, a)],
      st.stage + 1, 1⟩

/-- Replay the marker phase of level `j` in capacity `U` over a history: while the stage is
below `m`, feed each answer to `markerStep`; afterwards collect the answers in the unconsumed
tail. Legality is never inspected (off-protocol histories are simply replayed).
Blueprint 02 DEF-ROUND-01 / LEM-EFF-02. -/
def replayMarkerPhase (S : GameSchedule) (j : ℕ) (U : ℚ) (h : LocalHistory) :
    MarkerState × LocalHistory :=
  h.foldl
    (fun p e =>
      if p.1.stage < S.stages j U then (markerStep S j p.1 e.2, p.2) else (p.1, p.2 ++ [e]))
    (initialMarkerState, [])

/-- The stage invariant of the marker phase, stated at every chain position: the stage is
at most `m`; the chain position is `≥ 1`; the `k` markers are strict ancestors of the active
root, requested with exponent `E_j` and answered in `k` distinct coarse cells; the chain
vertices `v_1, …, v_{t-1}` of the current stage were requested with exponent `E_j` and
answered inside marked coarse cells; every request of `H` is a marker, a current chain vertex,
or incomparable with the whole active subtree (so at a stage start, `t = 1`, the active
subtree is undeclared and the only requests on a path through the root are the markers); the
answers of `H` are legal in shape and pairwise disjoint at distinct comparable vertices, no
vertex is requested twice; and every path leaving the active subtree carries load at most
`B_j`. Blueprint 02 DEF-ROUND-01. -/
structure MarkerStageInvariant (S : GameSchedule) (j : ℕ) (U : ℚ) (H : LocalHistory)
    (st : MarkerState) : Prop where
  /-- `k ≤ m`. -/
  stage_le : st.stage ≤ S.stages j U
  /-- `t ≥ 1`. -/
  one_le_chainPos : 1 ≤ st.chainPos
  /-- There are exactly `k` markers. -/
  markers_length : st.markers.length = st.stage
  /-- Markers are strict ancestors of the active root. -/
  marker_prefix : ∀ e ∈ st.markers, e.1 <+: st.root ∧ e.1 ≠ st.root
  /-- Markers were requested with exponent `E_j` and answered by the recorded cell. -/
  marker_mem : ∀ e ∈ st.markers, ((e.1, S.exp j), e.2) ∈ H
  /-- The marked coarse cells are distinct. -/
  markedCoarse_nodup : (markedCoarseCells S j st).Nodup
  /-- The chain vertices `v_1, …, v_{t-1}` were requested with `E_j` and answered inside
  marked coarse cells. -/
  chain_mem : ∀ t, 1 ≤ t → t < st.chainPos →
    ∃ a, ((chainVertex st.root (markerChainLength (S.ratio j) st.stage) t, S.exp j), a) ∈ H ∧
      coarseCellOf S j a ∈ markedCoarseCells S j st
  /-- Every request is a marker, a current chain vertex, or incomparable with the active
  subtree. -/
  request_cases : ∀ e ∈ H, e.1.1 ∈ st.markers.map Prod.fst ∨
    (∃ t, 1 ≤ t ∧ t < st.chainPos ∧
      e.1.1 = chainVertex st.root (markerChainLength (S.ratio j) st.stage) t) ∨
    ∀ x, IsIncomparable e.1.1 (st.root ++ x)
  /-- Answers have the prescribed depth and lie in `[0, U)`. -/
  answers_legal : ∀ e ∈ H, e.2.1 = S.depthOfExp e.1.2 ∧ CellInCapacity U e.2
  /-- Answers at distinct comparable vertices are disjoint. -/
  answers_disjoint : ∀ e ∈ H, ∀ e' ∈ H, IsComparable e.1.1 e'.1.1 → e.1.1 ≠ e'.1.1 →
    CellsDisjoint e.2 e'.2
  /-- A vertex is requested at most once. -/
  vertices_nodup : ((requestsOf H).map Prod.fst).Nodup
  /-- Paths leaving the active subtree carry load at most `B_j`. -/
  exited_load : ∀ v, ¬ st.root <+: v → load (requestsOf H) v ≤ S.budget j

/-- A fresh initial root satisfies the invariant: the empty history and the initial state.
Blueprint 02 DEF-ROUND-01. -/
theorem markerStageInvariant_initial (S : GameSchedule) (j : ℕ) (U : ℚ) :
    MarkerStageInvariant S j U [] initialMarkerState := by
  constructor
  · exact Nat.zero_le _
  · exact Nat.le_refl 1
  · rfl
  · intro e he; cases he
  · intro e he; cases he
  · exact List.nodup_nil
  · intro t ht1 hlt; revert hlt; unfold initialMarkerState; intro hlt; change t < 1 at hlt; omega
  · intro e he; cases he
  · intro e he; cases he
  · intro e he _ _ _ _; cases he
  · exact List.nodup_nil
  · intro v hv
    exact False.elim (hv (List.nil_prefix))

/-- A vertex is requested at most once: two entries of the history at the same vertex are
equal. Blueprint 02 DEF-01. -/
private theorem eq_of_mem_of_vertex_eq {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hinv : MarkerStageInvariant S j U H st) {e e' : Request × DyadicCell}
    (he : e ∈ H) (he' : e' ∈ H) (h : e.1.1 = e'.1.1) : e = e' := by
  have hH : (H.map fun e => e.1.1).Nodup := by
    simpa [requestsOf, List.map_map, Function.comp_def] using hinv.vertices_nodup
  exact List.inj_on_of_nodup_map hH he he' h

/-- The marker vertices are pairwise distinct: the markers have distinct coarse cells, and a
vertex is requested at most once. Blueprint 02 DEF-ROUND-01. -/
private theorem markers_map_fst_nodup {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hinv : MarkerStageInvariant S j U H st) :
    (st.markers.map Prod.fst).Nodup := by
  have hnd : st.markers.Nodup := List.Nodup.of_map _ hinv.markedCoarse_nodup
  refine hnd.map_on fun m hm m' hm' h => ?_
  have := eq_of_mem_of_vertex_eq hinv (hinv.marker_mem m hm) (hinv.marker_mem m' hm') h
  exact Prod.ext h (Prod.ext_iff.1 this).2

/-- The history entries at prefixes of the first chain vertex `v_1 = u_k 0^r` are markers and
chain entries: their exponent is `E_j` and their answers lie in marked coarse cells.
Blueprint 02 LEM-ROUND-02. -/
private theorem exp_eq_and_coarse_mem_of_prefix {S : GameSchedule} {j : ℕ} {U : ℚ}
    {H : LocalHistory} {st : MarkerState} (hinv : MarkerStageInvariant S j U H st)
    {e : Request × DyadicCell} (he : e ∈ H)
    (hev : e.1.1 <+: chainVertex st.root (markerChainLength (S.ratio j) st.stage) 1) :
    e.1.2 = S.exp j ∧ coarseCellOf S j e.2 ∈ markedCoarseCells S j st := by
  rcases hinv.request_cases e he with hm | ⟨t, ht1, ht, heq⟩ | hinc
  · obtain ⟨m, hm, hme⟩ := List.mem_map.1 hm
    have := eq_of_mem_of_vertex_eq hinv (hinv.marker_mem m hm) he hme
    rw [← this]
    exact ⟨rfl, List.mem_map_of_mem hm⟩
  · obtain ⟨a, ha, hac⟩ := hinv.chain_mem t ht1 ht
    have := eq_of_mem_of_vertex_eq hinv ha he heq.symm
    rw [← this]
    exact ⟨rfl, hac⟩
  · exact absurd hev (hinc _).1

/-- The chain vertices `v_t = u_k 0^(r - t + 1)`, `1 ≤ t ≤ r`, are pairwise distinct (their zero
tails have distinct lengths). Blueprint 02 LEM-ROUND-02. -/
private theorem chainVertex_nodup (root : BitString) (r : ℕ) :
    ((List.range r).map fun i => chainVertex root r (i + 1)).Nodup := by
  refine List.nodup_range.map_on fun i hi i' hi' h => ?_
  have hl := congrArg List.length h
  simp only [chainVertex, List.length_append, List.length_replicate] at hl
  rw [List.mem_range] at hi hi'
  omega

/-- Deepest-first chain forces a new coarse cell: under the invariant at stage `k`, the chain
position never exceeds `r = k (L - 1) + 1`, because the `k` markers and the `t - 1` chain
answers are pairwise disjoint fine cells inside `k` marked coarse cells of `L` fine positions
each (`k + t - 1 ≤ k L`). Hence if Bob answers all `r` chain requests, one of the answers lies
in an unmarked coarse cell. Blueprint 02 LEM-ROUND-02. -/
theorem chain_forces_new_coarse {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hS : S.IsValid) (hj1 : 1 ≤ j) (hjR : j ≤ S.R)
    (hinv : MarkerStageInvariant S j U H st) :
    st.chainPos ≤ markerChainLength (S.ratio j) st.stage := by
  have _ := hj1
  by_contra hlt
  push Not at hlt
  set r := markerChainLength (S.ratio j) st.stage with hr
  have hjl : j < S.exps.length := by
    have := hS.2.1
    unfold GameSchedule.R at hjR
    omega
  -- the history entries at prefixes of `v_1`
  set P := H.filter fun e => decide (e.1.1 <+: chainVertex st.root r 1)
  have hPH : ∀ e ∈ P, e ∈ H ∧ e.1.1 <+: chainVertex st.root r 1 := fun e he => by
    simpa [P] using he
  have hvert : (H.map fun e => e.1.1).Nodup := by
    simpa [requestsOf, List.map_map, Function.comp_def] using hinv.vertices_nodup
  have hPv : (P.map fun e => e.1.1).Nodup := hvert.sublist (List.filter_sublist.map _)
  -- lower bound: the `k` marker vertices and the `r` chain vertices are vertices of `P`
  have hlow : st.stage + r ≤ P.length := by
    have hW : (st.markers.map Prod.fst ++
        (List.range r).map fun i => chainVertex st.root r (i + 1)).Nodup := by
      refine (markers_map_fst_nodup hinv).append (chainVertex_nodup st.root r) ?_
      intro x hx hx'
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i, -, hi⟩ := List.mem_map.1 hx'
      obtain ⟨hpre, hne⟩ := hinv.marker_prefix m hm
      have h1 := congrArg List.length hi
      have h2 : m.1.length ≠ st.root.length := fun h => hne (hpre.eq_of_length h)
      have h3 := hpre.length_le
      simp only [chainVertex, List.length_append, List.length_replicate] at h1
      omega
    have hsub : (st.markers.map Prod.fst ++
        (List.range r).map fun i => chainVertex st.root r (i + 1)) ⊆ P.map fun e => e.1.1 := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
        refine List.mem_map.2 ⟨((m.1, S.exp j), m.2), ?_, rfl⟩
        refine List.mem_filter.2 ⟨hinv.marker_mem m hm, decide_eq_true ?_⟩
        exact (hinv.marker_prefix m hm).1.trans (List.prefix_append _ _)
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        rw [List.mem_range] at hi
        obtain ⟨a, ha, -⟩ := hinv.chain_mem (i + 1) (by omega) (by omega)
        refine List.mem_map.2 ⟨_, List.mem_filter.2 ⟨ha, decide_eq_true ?_⟩, rfl⟩
        refine ⟨List.replicate (i + 1 - 1) false, ?_⟩
        simp only [chainVertex, List.append_assoc, ← List.replicate_add]
        congr 2
        omega
    have := (hW.subperm hsub).length_le
    simpa [hinv.markers_length] using this
  -- upper bound: the answers of `P` are distinct fine cells in the `k` marked coarse cells
  have hup : P.length ≤ st.stage * S.ratio j := by
    have hdisj : (P.map Prod.snd).Pairwise CellsDisjoint := by
      rw [List.pairwise_map]
      refine (List.pairwise_map.1 hPv).imp_of_mem fun {e e'} he he' hne => ?_
      obtain ⟨he1, he2⟩ := hPH e he
      obtain ⟨he1', he2'⟩ := hPH e' he'
      exact hinv.answers_disjoint e he1 e' he1' (isComparable_of_prefix_of_prefix he2 he2') hne
    have hnd : (P.map Prod.snd).Nodup := by
      refine hdisj.imp fun {c c'} h => ?_
      rintro rfl
      exact not_cellsDisjoint_self c h
    have hcount := length_le_mul_of_cellAncestor_mem (a := S.depth (j - 1)) (b := S.depth j)
      (K := markedCoarseCells S j st) hnd (fun c hc => ?_) (fun c hc => ?_)
    · simpa [markedCoarseCells, hinv.markers_length, GameSchedule.ratio] using hcount
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
      obtain ⟨he1, he2⟩ := hPH e he
      rw [(hinv.answers_legal e he1).1, (exp_eq_and_coarse_mem_of_prefix hinv he1 he2).1]
      exact GameSchedule.depthOfExp_exp hS hjl
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
      obtain ⟨he1, he2⟩ := hPH e he
      exact (exp_eq_and_coarse_mem_of_prefix hinv he1 he2).2
  have hL : 1 ≤ S.ratio j := Nat.one_le_two_pow
  have h1 : r = st.stage * S.ratio j - st.stage + 1 := by
    rw [hr, markerChainLength, Nat.mul_sub_one]
  have h2 := Nat.le_mul_of_pos_right st.stage hL
  omega

/-- Load of the history on a path through the active root, before the pending request: the
requests of `H` at prefixes of such a path are the `k` markers and the `t - 1` chain vertices
already answered, all with exponent `E_j` (incomparable requests are never prefixes of the
path), so the load is at most `(k + t - 1) w_j`. Blueprint 02 LEM-ROUND-04. -/
theorem markerPhase_load_history_le {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hinv : MarkerStageInvariant S j U H st) {v : BitString}
    (hv : st.root <+: v) :
    load (requestsOf H) v ≤ ((st.stage + (st.chainPos - 1) : ℕ) : ℚ) * S.weight j := by
  have hexp : ∀ r ∈ requestsOf H, ∀ x a, ((x, S.exp j), a) ∈ H → r.1 = x → r.2 = S.exp j :=
    fun r hr x a hxa hx => by
      rw [List.inj_on_of_nodup_map hinv.vertices_nodup hr
        (List.mem_map_of_mem (f := Prod.fst) hxa) hx]
  have hV : ∀ r ∈ requestsOf H, r.1 <+: v → r.1 ∈ st.markers.map Prod.fst ++
      (List.range (st.chainPos - 1)).map
        (fun i => chainVertex st.root (markerChainLength (S.ratio j) st.stage) (i + 1)) ∧
      r.2 = S.exp j := by
    intro r hr hrv
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
    rcases hinv.request_cases e he with hm | ⟨t, ht1, ht, heq⟩ | hinc
    · obtain ⟨m, hm', hme⟩ := List.mem_map.1 hm
      exact ⟨List.mem_append_left _ hm, hexp _ hr _ _ (hinv.marker_mem m hm') hme.symm⟩
    · obtain ⟨a, ha, -⟩ := hinv.chain_mem t ht1 ht
      refine ⟨List.mem_append_right _ (List.mem_map.2 ⟨t - 1, List.mem_range.2 (by omega), ?_⟩),
        hexp _ hr _ _ ha heq⟩
      rw [heq, Nat.sub_add_cancel ht1]
    · exfalso
      rcases isComparable_of_prefix_of_prefix hrv hv with h | h
      · exact (hinc []).1 (by simpa using h)
      · exact (hinc []).2 (by simpa using h)
  refine (load_le_length_mul_requestWeight hinv.vertices_nodup hV).trans (le_of_eq ?_)
  simp [hinv.markers_length, GameSchedule.weight]

/-- The chain vertices visited before `v_t` lie below `v_t 0`: for `t' < t ≤ r` the zero tail
of `v_{t'}` is longer than that of `v_t`. Blueprint 02 LEM-ROUND-03. -/
private theorem chainVertex_append_false_prefix (root : BitString) {r t t' : ℕ} (ht : t' < t)
    (htr : t ≤ r) : chainVertex root r t ++ [false] <+: chainVertex root r t' := by
  refine ⟨List.replicate (t - t' - 1) false, ?_⟩
  unfold chainVertex
  rw [show [false] = List.replicate 1 false from rfl, List.append_assoc, List.append_assoc,
    ← List.replicate_add, ← List.replicate_add]
  congr 2
  omega

/-- The current chain request is fresh: under the stage invariant with `t ≤ r`, its vertex `v_t`
was never requested (the markers are strict ancestors of the active root, the earlier chain
vertices have longer zero tails, every other request is incomparable with the active subtree).
Blueprint 02 LEM-ROUND-03. -/
theorem markerRequest_fresh {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hinv : MarkerStageInvariant S j U H st)
    (htr : st.chainPos ≤ markerChainLength (S.ratio j) st.stage) :
    (markerRequest S j st).1 ∉ (requestsOf H).map Prod.fst := by
  simp only [requestsOf, List.map_map, List.mem_map, Function.comp_apply, not_exists, not_and]
  intro e he hev
  have hlen : (markerRequest S j st).1.length =
      st.root.length + (markerChainLength (S.ratio j) st.stage - st.chainPos + 1) := by
    simp [markerRequest, chainVertex]
  rcases hinv.request_cases e he with hm | ⟨t, -, ht, heq⟩ | hinc
  · obtain ⟨m, hm, hme⟩ := List.mem_map.1 hm
    obtain ⟨hpre, hne⟩ := hinv.marker_prefix m hm
    have h1 := hpre.length_le
    have h2 : m.1.length ≠ st.root.length := fun h => hne (hpre.eq_of_length h)
    have h3 : m.1.length = (markerRequest S j st).1.length := by rw [hme, hev]
    omega
  · have h3 := congrArg List.length (heq.symm.trans hev)
    rw [hlen] at h3
    simp only [chainVertex, List.length_append, List.length_replicate] at h3
    omega
  · exact (hinc _).ne hev

/-- LEM-ROUND-04 for a valid schedule with `w_j ≤ B_j` (all that the bound uses of the
PARAM-GAME hypotheses): at a stage `k < m` every path carries load at most `B_j` from the history
together with the pending chain request — at most `(k + t) w ≤ (k L + 1) w ≤ ((M - 1) L + 1) w ≤
B_j` through the active root, the invariant's bound on the paths leaving it.
Blueprint 02 LEM-ROUND-04. -/
theorem markerPhase_load_le_of_valid {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hS : S.IsValid) (hw : S.weight j ≤ S.budget j) (hj1 : 1 ≤ j)
    (hjR : j ≤ S.R) (hinv : MarkerStageInvariant S j U H st) (hk : st.stage < S.stages j U) :
    HasBudget (requestsOf H ++ [markerRequest S j st]) (S.budget j) := by
  have htr := chain_forces_new_coarse hS hj1 hjR hinv
  have hw0 : 0 < S.weight j := by
    unfold GameSchedule.weight requestWeight
    positivity
  intro v
  rw [load_append]
  by_cases hroot : st.root <+: v
  · have hL : 1 ≤ S.ratio j := Nat.one_le_two_pow
    have hM : st.stage ≤ markerCount (S.budget j) (S.weight j) (S.ratio j) - 1 := by
      unfold GameSchedule.stages stageCount at hk
      have := min_le_right (coarseCount U (S.coarseLength j))
        (markerCount (S.budget j) (S.weight j) (S.ratio j))
      omega
    have hcount : st.stage + (st.chainPos - 1) ≤
        (markerCount (S.budget j) (S.weight j) (S.ratio j) - 1) * S.ratio j := by
      have h1 : st.chainPos ≤ st.stage * (S.ratio j - 1) + 1 := htr
      have h2 := Nat.le_mul_of_pos_right st.stage hL
      have h3 := Nat.mul_le_mul_right (S.ratio j) hM
      rw [Nat.mul_sub_one] at h1
      omega
    have hcount' : ((st.stage + (st.chainPos - 1) : ℕ) : ℚ) ≤
        ((markerCount (S.budget j) (S.weight j) (S.ratio j) - 1 : ℕ) : ℚ) * S.ratio j := by
      exact_mod_cast hcount
    have hq : load [markerRequest S j st] v ≤ S.weight j := by
      have h0 : load [] v = 0 := by simp [load]
      rw [load_cons, h0, add_zero]
      split_ifs
      · exact le_rfl
      · exact hw0.le
    linarith [markerPhase_load_history_le hinv hroot, markerCount_pred_load_le (S.ratio j) hw,
      mul_le_mul_of_nonneg_right hcount' hw0.le]
  · have hnp : ¬ (markerRequest S j st).1 <+: v :=
      fun h => hroot ((List.prefix_append _ _).trans h)
    have h0 : load [markerRequest S j st] v = 0 := by simp [load, hnp]
    linarith [hinv.exited_load v hroot]

/-- LEM-ROUND-03 for a valid schedule with `w_j ≤ B_j` (all that the step uses of the PARAM-GAME
hypotheses): a legal answer to the current chain request at a stage `k < m` preserves the stage
invariant. An answer in a marked coarse cell advances the chain; an answer in a new coarse cell
becomes a marker, the chain vertices already visited lie below `v_t 0`, the new root `v_t 1` is
fresh, and a path leaving the new root carries at most `(k + t) w ≤ (k L + 1) w ≤ B_j`.
Blueprint 02 LEM-ROUND-03. -/
theorem markerStep_invariant_of_valid {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} {a : DyadicCell} (hS : S.IsValid) (hw : S.weight j ≤ S.budget j)
    (hj1 : 1 ≤ j) (hjR : j ≤ S.R) (hinv : MarkerStageInvariant S j U H st)
    (hk : st.stage < S.stages j U) (ha : LegalAnswer S U H (markerRequest S j st) a) :
    MarkerStageInvariant S j U (H ++ [(markerRequest S j st, a)]) (markerStep S j st a) := by
  have htr := chain_forces_new_coarse hS hj1 hjR hinv
  have hvroot : st.root <+: (markerRequest S j st).1 := List.prefix_append _ _
  have hreqs : requestsOf (H ++ [(markerRequest S j st, a)]) =
      requestsOf H ++ [markerRequest S j st] := by simp [requestsOf]
  have hlegal : ∀ e ∈ H ++ [(markerRequest S j st, a)],
      e.2.1 = S.depthOfExp e.1.2 ∧ CellInCapacity U e.2 := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hinv.answers_legal e he
    · rw [List.mem_singleton.1 he]
      exact ⟨ha.1, ha.2.1⟩
  have hnodup : ((requestsOf (H ++ [(markerRequest S j st, a)])).map Prod.fst).Nodup := by
    rw [hreqs, List.map_append]
    exact hinv.vertices_nodup.append (List.nodup_singleton _)
      (List.disjoint_singleton.2 (markerRequest_fresh hinv htr))
  have hexit : ∀ v, ¬ st.root <+: v →
      load (requestsOf (H ++ [(markerRequest S j st, a)])) v ≤ S.budget j := fun v _ => by
    rw [hreqs]
    exact markerPhase_load_le_of_valid hS hw hj1 hjR hinv hk v
  unfold markerStep
  split_ifs with hc
  · refine ⟨hinv.stage_le, Nat.le_add_left _ _, hinv.markers_length, hinv.marker_prefix,
      fun e he => List.mem_append_left _ (hinv.marker_mem e he), hinv.markedCoarse_nodup,
      ?_, ?_, hlegal, answers_disjoint_append hinv.answers_disjoint ha, hnodup, hexit⟩
    · intro t ht1 ht
      rcases (Nat.lt_succ_iff.1 ht).lt_or_eq with ht | rfl
      · obtain ⟨a', ha', hc'⟩ := hinv.chain_mem t ht1 ht
        exact ⟨a', List.mem_append_left _ ha', hc'⟩
      · exact ⟨a, List.mem_append_right _ (List.mem_singleton_self _), hc⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · rcases hinv.request_cases e he with h | ⟨t, ht1, ht, heq⟩ | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨t, ht1, Nat.lt_succ_of_lt ht, heq⟩)
        · exact Or.inr (Or.inr h)
      · rw [List.mem_singleton.1 he]
        exact Or.inr (Or.inl ⟨st.chainPos, hinv.one_le_chainPos, Nat.lt_succ_self _, rfl⟩)
  · refine ⟨by simp only; omega, le_rfl, by simp [hinv.markers_length], ?_, ?_, ?_,
      fun t ht1 ht => absurd (lt_of_le_of_lt ht1 ht) (lt_irrefl 1), ?_, hlegal,
      answers_disjoint_append hinv.answers_disjoint ha, hnodup, ?_⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · obtain ⟨hp, hne⟩ := hinv.marker_prefix e he
        refine ⟨hp.trans (hvroot.trans (List.prefix_append _ _)), fun heq => ?_⟩
        have h1 := congrArg List.length heq
        have h2 := hp.length_le
        have h3 := hvroot.length_le
        simp only [List.length_append, List.length_singleton] at h1
        omega
      · rw [List.mem_singleton.1 he]
        exact ⟨List.prefix_append _ _, fun h => by simp at h⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact List.mem_append_left _ (hinv.marker_mem e he)
      · rw [List.mem_singleton.1 he]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    · simp only [markedCoarseCells, List.map_append, List.map_singleton]
      exact hinv.markedCoarse_nodup.append (List.nodup_singleton _)
        (List.disjoint_singleton.2 hc)
    · intro e he
      rcases List.mem_append.1 he with he | he
      · rcases hinv.request_cases e he with h | ⟨t, -, ht, heq⟩ | h
        · exact Or.inl (by rw [List.map_append]; exact List.mem_append_left _ h)
        · refine Or.inr (Or.inr fun x => ?_)
          rw [heq]
          exact isIncomparable_of_zero_one_subtrees
            (chainVertex_append_false_prefix st.root ht htr) (List.prefix_append _ _)
        · refine Or.inr (Or.inr fun x => ?_)
          have := h (List.replicate (markerChainLength (S.ratio j) st.stage - st.chainPos + 1)
            false ++ [true] ++ x)
          simpa [markerRequest, chainVertex, List.append_assoc] using this
      · rw [List.mem_singleton.1 he]
        exact Or.inl (by simp)
    · intro v _
      rw [hreqs]
      exact markerPhase_load_le_of_valid hS hw hj1 hjR hinv hk v

/-- Advancing the active root preserves freshness: a legal answer to the current chain request
of a state satisfying the invariant at a stage `k < m` yields a state satisfying the invariant
for the extended history (a new marker moves the root to `v_t 1`, below which nothing was
requested; the dropped chain vertices lie below `v_t 0`; requests are never removed from `H`).
Blueprint 02 LEM-ROUND-03. -/
theorem markerStep_invariant {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} {a : DyadicCell} (hS : S.IsAdmissible) (hj1 : 1 ≤ j) (hjR : j ≤ S.R)
    (hinv : MarkerStageInvariant S j U H st) (hk : st.stage < S.stages j U)
    (ha : LegalAnswer S U H (markerRequest S j st) a) :
    MarkerStageInvariant S j U (H ++ [(markerRequest S j st, a)]) (markerStep S j st a) := by
  obtain ⟨h1, h2, h3, -⟩ := GameSchedule.budget_bounds hS hjR
  exact markerStep_invariant_of_valid hS.1 (h1.trans (h2.trans h3)) hj1 hjR hinv hk ha

/-- Load on a path through the active root, with the pending chain request: at stage `k` it is
at most `(k + r) w = (k L + 1) w`. Blueprint 02 LEM-ROUND-04. -/
theorem markerPhase_load_root_le {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hS : S.IsValid) (hj1 : 1 ≤ j) (hjR : j ≤ S.R)
    (hinv : MarkerStageInvariant S j U H st) {v : BitString} (hv : st.root <+: v) :
    load (requestsOf H ++ [markerRequest S j st]) v ≤
      ((st.stage * S.ratio j + 1 : ℕ) : ℚ) * S.weight j := by
  have htr := chain_forces_new_coarse hS hj1 hjR hinv
  have hw0 : 0 < S.weight j := by
    unfold GameSchedule.weight requestWeight
    positivity
  have hL : 1 ≤ S.ratio j := Nat.one_le_two_pow
  have hcount : st.stage + (st.chainPos - 1) + 1 ≤ st.stage * S.ratio j + 1 := by
    have h1 : st.chainPos ≤ st.stage * (S.ratio j - 1) + 1 := htr
    have h2 := Nat.le_mul_of_pos_right st.stage hL
    have h3 := hinv.one_le_chainPos
    rw [Nat.mul_sub_one] at h1
    omega
  have hcount' : ((st.stage + (st.chainPos - 1) : ℕ) : ℚ) + 1 ≤
      ((st.stage * S.ratio j + 1 : ℕ) : ℚ) := by
    exact_mod_cast hcount
  have hq : load [markerRequest S j st] v ≤ S.weight j := by
    have h0 : load [] v = 0 := by simp [load]
    rw [load_cons, h0, add_zero]
    split_ifs
    · exact le_rfl
    · exact hw0.le
  rw [load_append]
  nlinarith [markerPhase_load_history_le hinv hv, mul_le_mul_of_nonneg_right hcount' hw0.le]

/-- Legality at every phase-1 prefix, including failure: at a stage `k < m` every path carries
load at most `B_j` from the history together with the pending (possibly unanswerable) chain
request — `(k L + 1) w ≤ ((M - 1) L + 1) w ≤ B` through the active root, the earlier bound on
the exited paths. Blueprint 02 LEM-ROUND-04. -/
theorem markerPhase_load_le {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hS : S.IsAdmissible) (hj1 : 1 ≤ j) (hjR : j ≤ S.R)
    (hinv : MarkerStageInvariant S j U H st) (hk : st.stage < S.stages j U) :
    HasBudget (requestsOf H ++ [markerRequest S j st]) (S.budget j) := by
  obtain ⟨h1, h2, h3, -⟩ := GameSchedule.budget_bounds hS hjR
  exact markerPhase_load_le_of_valid hS.1 (h1.trans (h2.trans h3)) hj1 hjR hinv hk

/-- At a stage start (chain position `1`, in particular after the phase completes) a path
through the active root carries exactly the marker load `k w`. Blueprint 02 LEM-ROUND-04. -/
theorem markerPhase_load_root_eq {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hinv : MarkerStageInvariant S j U H st) (hpos : st.chainPos = 1)
    {v : BitString} (hv : st.root <+: v) :
    load (requestsOf H) v = (st.stage : ℚ) * S.weight j := by
  have hmem : ∀ r, r ∈ (requestsOf H).filter (fun r => decide (r.1 <+: v)) ↔
      r ∈ st.markers.map fun m => (m.1, S.exp j) := by
    intro r
    simp only [List.mem_filter, decide_eq_true_eq, requestsOf, List.mem_map]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hev⟩
      rcases hinv.request_cases e he with hm | ⟨t, ht1, ht, -⟩ | hinc
      · obtain ⟨m, hm, hme⟩ := List.mem_map.1 hm
        exact ⟨m, hm, congrArg Prod.fst (eq_of_mem_of_vertex_eq hinv (hinv.marker_mem m hm) he hme)⟩
      · omega
      · obtain ⟨x, rfl⟩ := hv
        exact absurd hev (hinc x).1
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨((m.1, S.exp j), m.2), hinv.marker_mem m hm, rfl⟩,
        (hinv.marker_prefix m hm).1.trans hv⟩
  have hnd1 : ((requestsOf H).filter fun r => decide (r.1 <+: v)).Nodup :=
    (List.Nodup.of_map Prod.fst hinv.vertices_nodup).filter _
  have hnd2 : (st.markers.map fun m => (m.1, S.exp j)).Nodup := by
    refine List.Nodup.of_map Prod.fst ?_
    simpa [List.map_map, Function.comp_def] using markers_map_fst_nodup hinv
  have hperm := (List.perm_ext_iff_of_nodup hnd1 hnd2).2 hmem
  unfold load
  rw [(hperm.map _).sum_eq]
  simp [List.map_map, Function.comp_def, hinv.markers_length, GameSchedule.weight]

/-! ### The residual space (RESIDUAL, LEM-ROUND-05, LEM-ROUND-06) -/

/-- The residual region `F`: the indices of the unmarked coarse (depth `δ_{j-1}`) cells wholly
contained in `[0, U)`; a partial right-boundary cell is excluded. Blueprint 02 §4. -/
def residualCells (S : GameSchedule) (j : ℕ) (U : ℚ) (st : MarkerState) : List ℕ :=
  (List.range (coarseCount U (S.coarseLength j))).filter fun i =>
    decide (CellInCapacity U (S.depth (j - 1), i)) &&
      !decide ((S.depth (j - 1), i) ∈ markedCoarseCells S j st)

/-- The residual capacity `U' = |F| h`. Blueprint 02 §4. -/
def residualCapacity (S : GameSchedule) (j : ℕ) (U : ℚ) (st : MarkerState) : ℚ :=
  packedCapacity (S.depth (j - 1)) (residualCells S j U st)

/-- The residual region lists each index once. Blueprint 02 §4. -/
theorem residualCells_nodup (S : GameSchedule) (j : ℕ) (U : ℚ) (st : MarkerState) :
    (residualCells S j U st).Nodup := by
  unfold residualCells
  exact List.Nodup.filter _ (List.nodup_range)

/-- Every recursive answer is clean: a legal answer, of depth at most `δ_{j-1}`, to a request
below the active root is a union of cells of `F` (it is disjoint from the marker answers,
whose vertices are its ancestors, hence meets no marked coarse cell by laminarity, and its
coarse cells lie in `[0, U)`). Blueprint 02 LEM-ROUND-05. -/
theorem recursive_answer_isClean {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hS : S.IsValid) (hj1 : 1 ≤ j) (hjR : j ≤ S.R)
    (hinv : MarkerStageInvariant S j U H st) {x : BitString} {n : ℕ} {a : DyadicCell}
    (hx : st.root <+: x) (hd : a.1 ≤ S.depth (j - 1)) (ha : LegalAnswer S U H (x, n) a) :
    IsClean (S.depth (j - 1)) (residualCells S j U st) a := by
  have hjl : j < S.exps.length := by
    have := hS.2.1
    unfold GameSchedule.R at hjR
    omega
  have hδ := GameSchedule.depth_pred_lt_depth hS hj1 hjR
  refine ⟨hd, fun i hi => ?_⟩
  have hsub := cellSubset_descendant hd hi
  have hcap := cellInCapacity_of_cellSubset hsub ha.2.1
  unfold residualCells
  rw [List.mem_filter, List.mem_range]
  refine ⟨index_lt_ceil_of_cellLeft_lt ((cellLeft_lt_cellRight _).trans_le hcap), ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  refine ⟨hcap, fun hmarked => ?_⟩
  obtain ⟨m, hm, hmc⟩ := List.mem_map.1 hmarked
  have hm2 : m.2.1 = S.depth j := by
    rw [(hinv.answers_legal _ (hinv.marker_mem m hm)).1]
    exact GameSchedule.depthOfExp_exp hS hjl
  have hmsub : CellSubset m.2 (coarseCellOf S j m.2) :=
    cellSubset_cellAncestor m.2 (by rw [hm2]; exact hδ.le)
  rw [hmc] at hmsub
  have hma : CellSubset m.2 a := ⟨hsub.1.trans hmsub.1, hmsub.2.trans hsub.2⟩
  obtain ⟨hpre, hne⟩ := hinv.marker_prefix m hm
  have hne' : m.1 ≠ x := by
    rintro rfl
    exact hne (hpre.eq_of_length (le_antisymm hpre.length_le hx.length_le))
  have hdisj := ha.2.2 _ (hinv.marker_mem m hm) (Or.inl (hpre.trans hx)) hne'
  exact not_cellsDisjoint_self m.2 (cellsDisjoint_of_cellSubset_left hma (Or.symm hdisj))

/-- `U' ≤ (N - k) h`: the residual region is a subset of the unmarked cells among the `N`
coarse cells meeting `[0, U)`. Blueprint 02 LEM-ROUND-06 (first inequality). -/
theorem residualCapacity_le_unmarked {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hS : S.IsValid) (hj1 : 1 ≤ j) (hjR : j ≤ S.R)
    (hinv : MarkerStageInvariant S j U H st) :
    residualCapacity S j U st ≤
      ((coarseCount U (S.coarseLength j) - st.stage : ℕ) : ℚ) * S.coarseLength j := by
  have hjl : j < S.exps.length := by
    have := hS.2.1
    unfold GameSchedule.R at hjR
    omega
  have hδ := GameSchedule.depth_pred_lt_depth hS hj1 hjR
  have hdepth : ∀ c ∈ markedCoarseCells S j st, c.1 = S.depth (j - 1) := by
    intro c hc
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hc
    rfl
  have hKnd : ((markedCoarseCells S j st).map Prod.snd).Nodup :=
    hinv.markedCoarse_nodup.map_on fun c hc c' hc' h =>
      Prod.ext ((hdepth c hc).trans (hdepth c' hc').symm) h
  have hK : ∀ i ∈ (markedCoarseCells S j st).map Prod.snd,
      i < coarseCount U (S.coarseLength j) := by
    intro i hi
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
    have hlegal := hinv.answers_legal _ (hinv.marker_mem m hm)
    have hm2 : m.2.1 = S.depth j := by
      rw [hlegal.1]
      exact GameSchedule.depthOfExp_exp hS hjl
    have hmsub : CellSubset m.2 (coarseCellOf S j m.2) :=
      cellSubset_cellAncestor m.2 (by rw [hm2]; exact hδ.le)
    exact index_lt_ceil_of_cellLeft_lt
      (hmsub.1.trans_lt ((cellLeft_lt_cellRight _).trans_le hlegal.2))
  have hFK : ∀ i ∈ residualCells S j U st,
      i ∉ (markedCoarseCells S j st).map Prod.snd := by
    intro i hi hiK
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hiK
    unfold residualCells at hi
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at hi
    exact hi.2.2 (by rw [← hdepth c hc]; exact hc)
  have hlen : (residualCells S j U st).length + st.stage ≤ coarseCount U (S.coarseLength j) := by
    have hnd := (residualCells_nodup S j U st).append hKnd fun i hF hK' => hFK i hF hK'
    have hsub : residualCells S j U st ++ (markedCoarseCells S j st).map Prod.snd ⊆
        List.range (coarseCount U (S.coarseLength j)) := by
      intro i hi
      rw [List.mem_range]
      rcases List.mem_append.1 hi with hi | hi
      · unfold residualCells at hi
        exact List.mem_range.1 (List.mem_filter.1 hi).1
      · exact hK i hi
    have := (hnd.subperm hsub).length_le
    simpa [markedCoarseCells, hinv.markers_length] using this
  have hcast : ((residualCells S j U st).length : ℚ) ≤
      ((coarseCount U (S.coarseLength j) - st.stage : ℕ) : ℚ) := by
    exact_mod_cast (by omega : (residualCells S j U st).length ≤
      coarseCount U (S.coarseLength j) - st.stage)
  unfold residualCapacity packedCapacity
  rw [div_eq_mul_one_div, ← one_div_pow]
  exact mul_le_mul_of_nonneg_right hcast (by positivity)

/-- If all `N` coarse cells meeting `[0, U)` are marked (`k = N`), the residual capacity is
`0`. Blueprint 02 LEM-ROUND-06. -/
theorem residualCapacity_eq_zero_of_all_marked {S : GameSchedule} {j : ℕ} {U : ℚ}
    {H : LocalHistory} {st : MarkerState} (hS : S.IsValid) (hj1 : 1 ≤ j) (hjR : j ≤ S.R)
    (hinv : MarkerStageInvariant S j U H st)
    (hN : st.stage = coarseCount U (S.coarseLength j)) : residualCapacity S j U st = 0 := by
    have h_le := residualCapacity_le_unmarked hS hj1 hjR hinv
    rw [hN, Nat.sub_self, Nat.cast_zero, zero_mul] at h_le
    have h_nonneg : 0 ≤ residualCapacity S j U st := by
      unfold residualCapacity packedCapacity
      have h1 : (0 : ℚ) ≤ ((residualCells S j U st).length : ℚ) := by positivity
      have h2 : (0 : ℚ) < 2 ^ S.depth (j - 1) := by positivity
      exact div_nonneg h1 h2.le
    exact le_antisymm h_le h_nonneg


/-- Capacity loss with the cancellation made explicit: if the phase placed `M` markers and
`U / s_j` is a natural number, then `U' < U - B_j (s_j / w_j) + h_j` (from
`U' ≤ (N - M) h < (U + h - s) - (B - w) s / w`). Blueprint 02 LEM-ROUND-06. -/
theorem residualCapacity_lt {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hS : S.IsAdmissible) (hj1 : 1 ≤ j) (hjR : j ≤ S.R)
    (hinv : MarkerStageInvariant S j U H st) (hgrid : ∃ A : ℕ, U / S.fineLength j = A)
    (hM : st.stage = markerCount (S.budget j) (S.weight j) (S.ratio j)) :
    residualCapacity S j U st <
      U - S.budget j * (S.fineLength j / S.weight j) + S.coarseLength j := by
  have hle := residualCapacity_le_unmarked hS.1 hj1 hjR hinv
  have hMN : st.stage ≤ coarseCount U (S.coarseLength j) :=
    hinv.stage_le.trans (min_le_left _ _)
  have hhs := GameSchedule.coarseLength_eq_ratio_mul_fineLength hS.1 hj1 hjR
  have hs : 0 < S.fineLength j := by
    unfold GameSchedule.fineLength
    positivity
  have hw : 0 < S.weight j := by
    unfold GameSchedule.weight requestWeight
    positivity
  have hL : 1 ≤ S.ratio j := Nat.one_le_two_pow
  have hN := coarseCount_mul_coarse_le hs hL hgrid
  have hMh := markerCount_mul_coarse_gt (B := S.budget j) hw hs (by omega : 0 < S.ratio j)
  rw [hM] at hle hMN
  rw [hhs] at hle hMN
  rw [Nat.cast_sub hMN, sub_mul] at hle
  have key : (S.budget j - S.weight j) * S.fineLength j / S.weight j =
      S.budget j * (S.fineLength j / S.weight j) - S.fineLength j := by
    field_simp
  rw [hhs]
  linarith

/-- The weaker source inequality `U' < U - (B_j - w_j) (s_j / w_j) + h_j`, the one used by
THEOREM-GAME. Blueprint 02 LEM-ROUND-06. -/
theorem residualCapacity_lt_source {S : GameSchedule} {j : ℕ} {U : ℚ} {H : LocalHistory}
    {st : MarkerState} (hS : S.IsAdmissible) (hj1 : 1 ≤ j) (hjR : j ≤ S.R)
    (hinv : MarkerStageInvariant S j U H st) (hgrid : ∃ A : ℕ, U / S.fineLength j = A)
    (hM : st.stage = markerCount (S.budget j) (S.weight j) (S.ratio j)) :
    residualCapacity S j U st <
      U - (S.budget j - S.weight j) * (S.fineLength j / S.weight j) + S.coarseLength j := by
  have H_lt := residualCapacity_lt hS hj1 hjR hinv hgrid hM
  have hw : (0 : ℚ) < S.weight j := by
    unfold GameSchedule.weight requestWeight; positivity
  calc
    residualCapacity S j U st < U - S.budget j * (S.fineLength j / S.weight j) + S.coarseLength j :=
      H_lt
    _ = U - (S.budget j - S.weight j) * (S.fineLength j / S.weight j)
        + S.coarseLength j - S.weight j * (S.fineLength j / S.weight j) := by ring
    _ = U - (S.budget j - S.weight j) * (S.fineLength j / S.weight j)
        + S.coarseLength j - S.fineLength j := by rw [mul_div_cancel₀ _ (ne_of_gt hw)]
    _ ≤ U - (S.budget j - S.weight j) * (S.fineLength j / S.weight j) + S.coarseLength j := by
      have hs : 0 ≤ S.fineLength j := by unfold GameSchedule.fineLength; positivity
      linarith

/-- `U' / h_j = |F|` is a natural number: the next-level grid condition holds exactly.
Blueprint 02 LEM-ROUND-06. -/
theorem residualCapacity_grid (S : GameSchedule) (j : ℕ) (U : ℚ) (st : MarkerState) :
    ∃ A : ℕ, residualCapacity S j U st / S.coarseLength j = A := by
  refine ⟨(residualCells S j U st).length, ?_⟩
  unfold residualCapacity packedCapacity GameSchedule.coarseLength
  have hd : (2 : ℚ) ^ S.depth (j - 1) ≠ 0 := by positivity
  set F : ℚ := ((residualCells S j U st).length : ℚ)
  calc
    (F / 2 ^ S.depth (j - 1)) / (1 / 2) ^ S.depth (j - 1)
      = (F / 2 ^ S.depth (j - 1)) / (2⁻¹) ^ S.depth (j - 1) := by rw [one_div]
    _ = (F / 2 ^ S.depth (j - 1)) / (2 ^ S.depth (j - 1))⁻¹ := by rw [inv_pow]
    _ = (F / 2 ^ S.depth (j - 1)) * 2 ^ S.depth (j - 1) := by rw [div_inv_eq_mul]
    _ = F := by rw [div_mul_cancel₀ _ hd]

end Kolmogorov
