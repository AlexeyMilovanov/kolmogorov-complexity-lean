import KolmogorovMathlib.MonotoneComplexity.GacsDayEndgameComputability
import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame

/-!
# Lifting a family strategy to a winning client of the Gács–Day game

The controller step: a strategy that plays legally on a family of parallel trees, requests only
inside the tree and always leaves some request unserved is a uniform winning strategy for the
game. `isUniformWinningStrategy_of_familyController` is the statement for a fixed budget and
`isUniformWinningStrategy_of_familyController_budget` its version under a dynamic budget, whose
extra ingredient is `requestCoherent_clientMoveLift_of_totalRootRequest`.
`allocationAvoidsUnavailable_truncAlloc_chain` supplies the avoidance side. The client actually
used is `grayRoundRobinStrategy`: the stage-`k` family winner run on `grayRoundCount d` parallel
trees, with `computable_grayRoundCount` for the computability of the count.

Source: SUV Theorem 88.
-/

namespace Kolmogorov

/-- A family strategy that plays legally, requests only inside the tree and always leaves an
unserved request lifts to a uniform winning strategy one level higher. -/
theorem isUniformWinningStrategy_of_familyController
    {h b n B d : ℕ} {alpha r : ℚ}
    {σf : ClientFamilyStrategy}
    (hnB : n ≤ B) (hbB : b ≤ B)
    (hr0 : 0 ≤ r) (hcap : r ≤ 1 / (d : ℚ)) (hsum : (n : ℚ) * alpha ≤ r)
    (hplay : ∀ sm : ℕ → FamilyServerMove, familyServerPlayLegal n b [] sm →
      familyClientPlayLegal n b alpha (playClientFamily [] n σf sm))
    (hrange : FamilyRangeSupported n b [] σf)
    (hunserved : ∀ sm : ℕ → FamilyServerMove, familyServerPlayLegal n b [] sm →
      familyClientWinsUnserved n h b (playClientFamily [] n σf sm) sm) :
    IsUniformWinningStrategy (h + 1) B d (liftFamilyStrategy n r σf) := by
  constructor
  · intro sm hsm
    have hfam := familyServerPlayLegal_below_of_le n b B hnB hbB sm hsm
    have hclient := hplay _ hfam
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t
      rw [playClient_liftFamilyStrategy]
      refine requestCoherent_clientMoveLift n b B d hnB hbB alpha r hr0 hcap hsum _
        (fun i hi => hclient.1 t i hi) ?_
      intro i hi x c hc
      obtain ⟨hist, hhist⟩ :=
        playClientFamily_eq_strategy_apply [] n σf (familyServerMovesBelow n sm) t
      rw [hhist]
      exact hrange hist x c hc i hi
    · intro t x
      rw [playClient_liftFamilyStrategy, playClient_liftFamilyStrategy]
      exact getReq_clientMoveLift_mono n r r _ _ le_rfl (fun i hi y => hclient.2 t i hi y) x
    · refine clientWinsUnserved_of_familyClientWinsUnserved n h b B hnB hbB _ _ sm ?_
        (hunserved _ hfam)
      intro t i hi x
      rw [playClient_liftFamilyStrategy, getReq_clientMoveLift_cons n r _ hi x]
  · intro hist x i hBi
    unfold liftFamilyStrategy
    cases x with
    | nil => exact getReq_clientMoveLift_cons_of_ge n r _ (le_trans hnB hBi) []
    | cons j y =>
      by_cases hj : j < n
      · change getReq (clientMoveLift n r _) (j :: (y ++ [i])) = 0
        rw [getReq_clientMoveLift_cons n r _ hj]
        obtain ⟨hist', hhist⟩ :=
          playClientFamily_eq_strategy_apply [] n σf
            (familyServerMovesBelow n (fun s => hist.2.getD s [])) hist.2.length
        rw [show getFamilyReq _ j (y ++ [i]) = getReq (familyClientMoveAt _ j) (y ++ [i]) from rfl,
          hhist]
        exact hrange hist' y i (le_trans hbB hBi) j hj
      · change getReq (clientMoveLift n r _) (j :: (y ++ [i])) = 0
        exact getReq_clientMoveLift_cons_of_ge n r _ (Nat.le_of_not_lt hj) _

/-- **Coherence of a lifted family move under a dynamic budget.** Only the
request the family actually makes at its roots has to fit under the root
request `r` of the big tree. The static hypothesis `n * alpha ≤ r` of
`requestCoherent_clientMoveLift` is the special case in which every tree of the
family is charged its cap; the sequential endgame cannot afford that, because
it opens far more rounds than the budget would allow if each of them asked for
its full cap. -/
lemma requestCoherent_clientMoveLift_of_totalRootRequest
    (n b B d : ℕ) (hnB : n ≤ B) (hbB : b ≤ B) (alpha r : ℚ)
    (hr0 : 0 ≤ r) (hcap : r ≤ 1 / (d : ℚ)) (fcm : FamilyClientMove)
    (hsum : totalRootRequest n fcm ≤ r)
    (hcoh : ∀ i, i < n → requestCoherentCap b alpha (familyClientMoveAt fcm i))
    (hrange : ∀ i, i < n → ∀ (x : GacsDayNode) (c : ℕ), b ≤ c →
      getReq (familyClientMoveAt fcm i) (x ++ [c]) = 0) :
    requestCoherent B d (clientMoveLift n r fcm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    cases y with
    | nil => rw [getReq_clientMoveLift_root]; exact hr0
    | cons i x =>
      by_cases hi : i < n
      · rw [getReq_clientMoveLift_cons n r fcm hi x]; exact (hcoh i hi).1 x
      · rw [getReq_clientMoveLift_cons_of_ge n r fcm (Nat.le_of_not_lt hi) x]
  · rw [getReq_clientMoveLift_root]; exact hcap
  · intro y
    cases y with
    | nil =>
      rw [getReq_clientMoveLift_root, ge_iff_le]
      have hzero : ∀ c, n ≤ c → getReq (clientMoveLift n r fcm) (([] : GacsDayNode) ++ [c]) = 0 :=
        fun c hc => getReq_clientMoveLift_cons_of_ge n r fcm hc []
      rw [sum_fin_eq_sum_fin_of_vanishing n B hnB
        (fun c => getReq (clientMoveLift n r fcm) (([] : GacsDayNode) ++ [c])) hzero]
      refine le_trans (le_of_eq ?_) hsum
      refine Finset.sum_congr rfl fun c _ => ?_
      exact getReq_clientMoveLift_cons n r fcm c.isLt []
    | cons i x =>
      by_cases hi : i < n
      · rw [getReq_clientMoveLift_cons n r fcm hi x, ge_iff_le]
        have hzero : ∀ c, b ≤ c → getReq (clientMoveLift n r fcm) ((i :: x) ++ [c]) = 0 := by
          intro c hc
          change getReq (clientMoveLift n r fcm) (i :: (x ++ [c])) = 0
          rw [getReq_clientMoveLift_cons n r fcm hi (x ++ [c])]
          exact hrange i hi x c hc
        rw [sum_fin_eq_sum_fin_of_vanishing b B hbB
          (fun c => getReq (clientMoveLift n r fcm) ((i :: x) ++ [c])) hzero]
        have hcongr : ∀ c : Fin b, getReq (clientMoveLift n r fcm) ((i :: x) ++ [c.val])
            = getReq (familyClientMoveAt fcm i) (x ++ [c.val]) := by
          intro c
          change getReq (clientMoveLift n r fcm) (i :: (x ++ [c.val])) = _
          rw [getReq_clientMoveLift_cons n r fcm hi (x ++ [c.val])]
          rfl
        rw [Finset.sum_congr rfl (fun c _ => hcongr c)]
        exact (hcoh i hi).2.2 x
      · rw [getReq_clientMoveLift_cons_of_ge n r fcm (Nat.le_of_not_lt hi) x, ge_iff_le]
        have hzero : ∀ c : Fin B, getReq (clientMoveLift n r fcm) ((i :: x) ++ [c.val]) = 0 := by
          intro c
          change getReq (clientMoveLift n r fcm) (i :: (x ++ [c.val])) = 0
          exact getReq_clientMoveLift_cons_of_ge n r fcm (Nat.le_of_not_lt hi) (x ++ [c.val])
        rw [Finset.sum_congr rfl (fun c _ => hzero c)]
        simp

/-- **The controller lift under a dynamic budget.** Same conclusion as
`isUniformWinningStrategy_of_familyController`, but the root of the big tree
only has to pay for the request the family actually makes at each time. This is
the form the sequential endgame needs: it opens one round per tree of the
family and there are many more trees than `1 / (d * alpha)`, so the static
bound `n * alpha ≤ r` is unavailable, while the accumulated request of the
rounds is kept below the dangerous level by the controller itself. -/
theorem isUniformWinningStrategy_of_familyController_budget
    {h b n B d : ℕ} {alpha r : ℚ}
    {σf : ClientFamilyStrategy}
    (hnB : n ≤ B) (hbB : b ≤ B)
    (hr0 : 0 ≤ r) (hcap : r ≤ 1 / (d : ℚ))
    (hplay : ∀ sm : ℕ → FamilyServerMove, familyServerPlayLegal n b [] sm →
      familyClientPlayLegal n b alpha (playClientFamily [] n σf sm))
    (hbudget : ∀ sm : ℕ → FamilyServerMove, familyServerPlayLegal n b [] sm →
      ∀ t, totalRootRequest n (playClientFamily [] n σf sm t) ≤ r)
    (hrange : FamilyRangeSupported n b [] σf)
    (hunserved : ∀ sm : ℕ → FamilyServerMove, familyServerPlayLegal n b [] sm →
      familyClientWinsUnserved n h b (playClientFamily [] n σf sm) sm) :
    IsUniformWinningStrategy (h + 1) B d (liftFamilyStrategy n r σf) := by
  constructor
  · intro sm hsm
    have hfam := familyServerPlayLegal_below_of_le n b B hnB hbB sm hsm
    have hclient := hplay _ hfam
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t
      rw [playClient_liftFamilyStrategy]
      refine requestCoherent_clientMoveLift_of_totalRootRequest n b B d hnB hbB alpha r hr0 hcap
        _ (hbudget _ hfam t) (fun i hi => hclient.1 t i hi) ?_
      intro i hi x c hc
      obtain ⟨hist, hhist⟩ :=
        playClientFamily_eq_strategy_apply [] n σf (familyServerMovesBelow n sm) t
      rw [hhist]
      exact hrange hist x c hc i hi
    · intro t x
      rw [playClient_liftFamilyStrategy, playClient_liftFamilyStrategy]
      exact getReq_clientMoveLift_mono n r r _ _ le_rfl (fun i hi y => hclient.2 t i hi y) x
    · refine clientWinsUnserved_of_familyClientWinsUnserved n h b B hnB hbB _ _ sm ?_
        (hunserved _ hfam)
      intro t i hi x
      rw [playClient_liftFamilyStrategy, getReq_clientMoveLift_cons n r _ hi x]
  · intro hist x i hBi
    unfold liftFamilyStrategy
    cases x with
    | nil => exact getReq_clientMoveLift_cons_of_ge n r _ (le_trans hnB hBi) []
    | cons j y =>
      by_cases hj : j < n
      · change getReq (clientMoveLift n r _) (j :: (y ++ [i])) = 0
        rw [getReq_clientMoveLift_cons n r _ hj]
        obtain ⟨hist', hhist⟩ :=
          playClientFamily_eq_strategy_apply [] n σf
            (familyServerMovesBelow n (fun s => hist.2.getD s [])) hist.2.length
        rw [show getFamilyReq _ j (y ++ [i]) = getReq (familyClientMoveAt _ j) (y ++ [i]) from rfl,
          hhist]
        exact hrange hist' y i (le_trans hbB hBi) j hj
      · change getReq (clientMoveLift n r _) (j :: (y ++ [i])) = 0
        exact getReq_clientMoveLift_cons_of_ge n r _ (Nat.le_of_not_lt hj) _

/-- A truncated allocation incomparable with every stage set avoids the whole chain of gray
allocations collected so far. -/
theorem allocationAvoidsUnavailable_truncAlloc_chain
    {N eps delta : ℕ} {S : ℕ → Finset BitString} {U : ℕ → Finset BitString}
    {alloc : Allocation} {A : ℕ → Allocation}
    (heps : eps ≤ delta)
    (hA : ∀ j < N, ∀ a ∈ A j, a ∈ newGrayCells eps delta (S j) (U j))
    (hdisj : ∀ j < N, ∀ c ∈ alloc, ∀ s ∈ S j, ¬ (c <+: s ∨ s <+: c)) :
    allocationAvoidsUnavailable ((List.range N).flatMap A) (truncAlloc eps alloc) := by
  intro c hc a ha hcomp
  simp only [List.mem_flatMap, List.mem_range] at ha
  rcases ha with ⟨j, hj, ha⟩
  exact allocationAvoidsUnavailable_truncAlloc heps (fun _ h => hA j hj _ h) (hdisj j hj)
    c hc a ha hcomp

/-- The endgame client: the stage-`k` family winner, run on `grayRoundCount d`
parallel trees at request scale and gray scale both equal to `2 ^ (-a)`.

This definition is only the engine for one family round; the source endgame
must sequence such rounds while extending the unavailable allocation. It is
not an unconditional win and does not use an exact-root measure barrier.
The remaining arguments are kept so that all endgame parameters stay visible
at the call site. -/
def grayRoundRobinStrategy (_d k a _e : ℕ) (_deltaDepth _branching : ℕ → ℕ → ℕ → ℕ)
    (σ : UniformFamilyStrategyScheme) : ClientFamilyStrategy :=
  σ k a a

/-- The number of parallel trees of the endgame family. -/
def grayRoundCount (d : ℕ) : ℕ := 64 * d

/-- The gray round count is computable. -/
theorem computable_grayRoundCount : Computable grayRoundCount := by
  change Computable (fun d => 64 * d)
  exact Primrec.to_comp (Primrec.nat_mul.comp (Primrec.const 64) Primrec.id)

end Kolmogorov
