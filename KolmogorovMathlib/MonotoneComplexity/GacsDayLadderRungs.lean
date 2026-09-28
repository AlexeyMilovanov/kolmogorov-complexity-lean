import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayRefine
import KolmogorovMathlib.MonotoneComplexity.GacsDaySubtreeEmbedding
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwo.ArithmeticRequests
import KolmogorovMathlib.MonotoneComplexity.GacsDayWitnessForcing

/-!
# The proved rungs of the ladder, at an arbitrary branching factor

`GrayRung` (in `GacsDayLadderStep`) is the shape the ladder of SUV pp. 142-144
consumes: at stage `k` the strategy scheme must win the family game at
amplification `1 + k / 2`, on trees of height `2 * k` and branching
`ladderBranching B a e = max (2 ^ (e - a)) B`, with fine scale `2 ^ (-(e + L))`.

The two proved stages above the base case, `grayFamilyGameSpec_halfStep`
(`kappa = 3 / 2`) and `grayFamilyGameSpec_stageTwo` (`kappa = 2`), are stated at
branching exactly `2`, so neither of them fits that shape yet: the ladder always
runs at branching at least `2 ^ (e - a)` at the root.

This file removes the restriction once and for all, by the general observation
that **a winning family strategy stays winning when the tree gets wider**
(`grayFamilyGameSpec_mono_branching`). Widening the tree

* strengthens the server's legality constraints, so a wider legal play is a
  narrower legal play (`familyServerPlayLegal_mono_branching`);
* weakens the client's default win, since a node with digits `< b` also has
  digits `< b'`;
* leaves the client's coherence inequality unchanged, because
  `FamilyRangeSupported` makes every extra son carry request `0`.

The rungs `grayRung_one` and `grayRung_two` are then immediate, and are the
first two rungs of `GrayRung` above `grayRung_zero`.
-/

namespace Kolmogorov

/-- A legal family server play on a wider tree is a legal family server play on
a narrower one: the coherence conditions of the narrow tree are instances of
those of the wide tree. -/
theorem familyServerPlayLegal_mono_branching {n b b' : ℕ} (hbb : b ≤ b') {A : Allocation}
    {sm : ℕ → FamilyServerMove} (hsm : familyServerPlayLegal n b' A sm) :
    familyServerPlayLegal n b A sm :=
  ⟨fun i hi => serverPlayLegal_mono_branching hbb (hsm.1 i hi), hsm.2.1, hsm.2.2⟩

/-- The client's default win transfers to a wider tree. -/
theorem familyClientWinsUnserved_mono_branching {n h b b' : ℕ} (hbb : b ≤ b')
    {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (hwin : familyClientWinsUnserved n h b cm sm) :
    familyClientWinsUnserved n h b' cm sm := by
  obtain ⟨i, hi, T, x, hlen, hdig, hfail⟩ := hwin
  exact ⟨i, hi, T, x, hlen, fun d hd => lt_of_lt_of_le (hdig d hd) hbb, hfail⟩

/-- Winning with positive unserved mass at branching `b` still wins at any larger branching. -/
theorem familyClientWinsUnservedPositive_mono_branching {n h b b' : ℕ} (hbb : b ≤ b')
    {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (H : familyClientWinsUnservedPositive n h b cm sm) :
    familyClientWinsUnservedPositive n h b' cm sm := by
  obtain ⟨i, hi, T, x, hlen, hdig, hfail, hpos⟩ := H
  exact ⟨i, hi, T, x, hlen, fun a ha => lt_of_lt_of_le (hdig a ha) hbb, hfail, hpos⟩

/-- **Widening the tree preserves a winning family strategy.** Every field of
`GrayFamilyGameSpec` transfers from branching `b` to any branching `b' ≥ b`.

The only field that is not a direct consequence of the corresponding field at
`b` is the coherence inequality inside `legal`, whose sum runs over the sons:
the extra sons `b, ..., b' - 1` all carry request `0` by `range_supported`. -/
theorem grayFamilyGameSpec_mono_branching {kappa alpha beta : ℚ}
    {epsDepth deltaDepth h b b' n : ℕ} (hbb : b ≤ b') {A : Allocation}
    {σ : ClientFamilyStrategy}
    (H : GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n A σ) :
    GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b' n A σ := by
  classical
  have hzero : ∀ (hist : FamilyGameHistory) (x : GacsDayNode) (i : ℕ), b ≤ i →
      ∀ j, j < n → getReq (familyClientMoveAt (σ A n hist) j) (x ++ [i]) = 0 :=
    fun hist x i hi j hj => H.range_supported hist x i hi j hj
  refine ⟨H.nonempty, H.kappa_ge_one, H.alpha_pos, H.beta_nonneg, H.scales, ?_, ?_, ?_, ?_,
    (fun hist x i hi j hj => hzero hist x i (le_trans hbb hi) j hj), H.tree_supported⟩
  · -- legal
    intro sm hsm
    have hsmb := familyServerPlayLegal_mono_branching hbb hsm
    obtain ⟨hcap, hmono⟩ := H.legal sm hsmb
    refine ⟨fun t i hi => ?_, hmono⟩
    obtain ⟨hnonneg, hroot, hsum⟩ := hcap t i hi
    refine ⟨hnonneg, hroot, fun x => ?_⟩
    obtain ⟨hist, hhist⟩ := playClientFamily_eq_strategy_apply A n σ sm t
    set req := familyClientMoveAt (playClientFamily A n σ sm t) i with hreq
    have hvanish : ∀ c ∈ Finset.range b', c ∉ Finset.range b →
        getReq req (x ++ [c]) = 0 := by
      intro c _ hc
      simp only [Finset.mem_range, not_lt] at hc
      rw [hreq, hhist]
      exact hzero hist x c hc i hi
    have hsub : Finset.range b ⊆ Finset.range b' := by
      intro c hc
      simp only [Finset.mem_range] at hc ⊢
      omega
    have hsplit : ∑ c : Fin b', getReq req (x ++ [c.val])
        = ∑ c : Fin b, getReq req (x ++ [c.val]) := by
      rw [Fin.sum_univ_eq_sum_range (fun c => getReq req (x ++ [c])) b',
        Fin.sum_univ_eq_sum_range (fun c => getReq req (x ++ [c])) b,
        Finset.sum_subset hsub hvanish]
    rw [ge_iff_le, hsplit]
    exact hsum x
  · -- minimum_request
    intro sm hsm
    exact H.minimum_request sm (familyServerPlayLegal_mono_branching hbb hsm)
  · -- wins
    intro sm hsm
    rcases H.wins sm (familyServerPlayLegal_mono_branching hbb hsm) with hwin | hgoal
    · exact Or.inl (familyClientWinsUnserved_mono_branching hbb hwin)
    · exact Or.inr hgoal
  · -- wins_positively
    intro sm hsm
    rcases H.wins_positively sm (familyServerPlayLegal_mono_branching hbb hsm) with hwin | hgoal
    · exact Or.inl (familyClientWinsUnservedPositive_mono_branching hbb hwin)
    · exact Or.inr hgoal

/-- **First amplification stage at an arbitrary branching factor.** The static
two-child split of `GacsDayHalfAmplification` wins the family game with
amplification `3 / 2` on trees of any branching factor `b ≥ 2`, not only on the
binary tree. -/
theorem grayFamilyGameSpec_halfStep_branching (b a e : ℕ) (hb : 2 ≤ b) (hae : a ≤ e)
    (n : ℕ) (hn : 1 ≤ n) (A : Allocation) :
    GrayFamilyGameSpec (halfAmplification 1) (dyadicScale a) ((3 / 4 : ℚ) * dyadicScale a)
      e (e + 3) 2 b n A (halfStepFamilyStrategy a (e + 3)) :=
  grayFamilyGameSpec_mono_branching hb (grayFamilyGameSpec_halfStep a e hae n hn A)

/-- **Second amplification stage at an arbitrary branching factor.** The
probe-and-raise strategy of `GacsDayStageTwo` wins the family game with
amplification `2` on trees of any branching factor `b ≥ 2`. -/
theorem grayFamilyGameSpec_stageTwo_branching (b a e : ℕ) (hb : 2 ≤ b) (hae : a ≤ e)
    (n : ℕ) (hn : 1 ≤ n) (A : Allocation) :
    GrayFamilyGameSpec (halfAmplification 2) (dyadicScale a) ((3 / 4 : ℚ) * dyadicScale a)
      e (e + 3) 4 b n A (stageTwoFamilyStrategy a (e + 3)) :=
  grayFamilyGameSpec_mono_branching hb (grayFamilyGameSpec_stageTwo a e hae n hn A)

/-- A rung stays a rung when the deep branching factor grows. -/
theorem grayRung_mono_branching {k L B B' : ℕ} (hBB : B ≤ B') {sigma : FamilyStrategyScheme}
    (H : GrayRung k L B sigma) : GrayRung k L B' sigma := by
  intro a e ha hae n A hn
  exact grayFamilyGameSpec_mono_branching
    (max_le_max (le_refl (2 * 2 ^ (e - a))) hBB) (H a e ha hae n A hn)

/-- A rung stays a rung when the depth loss grows, i.e. when the fine scale of
the game gets finer. -/
theorem grayRung_mono_loss {k L L' B : ℕ} (hLL : L ≤ L') {sigma : FamilyStrategyScheme}
    (H : GrayRung k L B sigma) : GrayRung k L' B sigma := by
  intro a e ha hae n A hn
  exact grayFamilyGameSpec_mono_deltaDepth (by omega) (H a e ha hae n A hn)

/-- **The stage-`1` rung of the ladder.** The static two-child split is a rung
of `GrayRung` at every deep branching factor `B ≥ 2`, with depth loss `3`. -/
theorem grayRung_one (B : ℕ) (hB : 2 ≤ B) :
    GrayRung 1 3 B (fun a e => halfStepFamilyStrategy a (e + 3)) := by
  intro a e _ha hae n A hn
  exact grayFamilyGameSpec_halfStep_branching (ladderBranching B a e) a e
    (two_le_ladderBranching hB a e) hae n hn A

/-- **The stage-`2` rung of the ladder.** The probe-and-raise strategy is a rung
of `GrayRung` at every deep branching factor `B ≥ 2`, with depth loss `3`. -/
theorem grayRung_two (B : ℕ) (hB : 2 ≤ B) :
    GrayRung 2 3 B (fun a e => stageTwoFamilyStrategy a (e + 3)) := by
  intro a e _ha hae n A hn
  exact grayFamilyGameSpec_stageTwo_branching (ladderBranching B a e) a e
    (two_le_ladderBranching hB a e) hae n hn A

end Kolmogorov
