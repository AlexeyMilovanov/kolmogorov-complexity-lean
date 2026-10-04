import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailPointwise
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFibre
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafD
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.EntrySupport

/-!
# The tail displays a coherent move

`grayTail_output_coherentCap` is the field of the tail specification asserting that the displayed
outer move is request coherent and respects the root cap. It is assembled from coherence of every
round the run freezes (`grayTailFrozenCoherent_stateAt`), of the current move
(`grayTailCurrentMove_requestCoherentCap`) and hence of all output entries
(`grayTailOutputEntries_requestCoherentCap`, with nonnegativity from
`grayTailOutputEntries_nonneg`). The monotonicity lemmas `grayTailSonRequest_mono`,
`grayTailRootRequest_mono`, `grayTailEntryMove_mono_append` and the bound
`grayTailThreshold_le_eps` are the arithmetic behind those statements.
-/

namespace Kolmogorov
open scoped BigOperators

/-- Against a legal server play, every round a tail run freezes carries a request coherent move. -/
lemma grayTailFrozenCoherent_stateAt
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (sm : ℕ → FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t : ℕ) :
    GrayTailFrozenCoherent q e
      (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen := by
  induction t with
  | zero =>
      intro p hp
      simp [grayTailInitialState] at hp
  | succ t ih =>
      rw [grayTailStateAt_succ]
      set b := grayTailBranch q L a e
      have hcert := grayTailCertified_stateAt (n := n) (b := b) q L a e sigma A sm t
      have htrace := grayTailTrace_stateAt (n := n) (b := b) q L a e sigma A sm t
      have hhist := grayTailHistoryOK_stateAt (n := n) (b := b) q L a e sigma A sm t
      set st := grayTailStateAt (n := n) (b := b) q L a e sigma A sm t
      rw [grayTailStep_eq]
      dsimp only
      split_ifs with hdone hgoal
      · exact ih
      · intro p hp j hj
        rcases List.mem_append.mp hp with hp | hp
        · exact ih p hp j hj
        · simp only [List.mem_singleton] at hp
          subst hp
          have hb : grayTailBaseBranch q L ≤ b := le_max_right _ _
          have hcount : st.frozen.length < grayTailRoundCount q := by
            by_contra h
            push Not at h
            have hdone' :=
              grayTail_done_of_roundCount_stateAt_core (q := q) (L := L) (a := a) (e := e) (sigma :=
                                                                                             sigma)
              (A := A) (sm := sm) (t := t) h
            change st.done = true at hdone'
            rw [hdone'] at hdone
            simp at hdone
          have hlocal := grayTailFutureServer_legal hcert hcount hsm
          have hspec := grayTailRound_gameSpec ha hae hB hRung hcert hdone hb
          have hlegal := hspec.weak.legal (grayTailFutureServer q L e st sm) hlocal
          have hcurr := grayTailCurrentMove_eq_futurePlay q L e sigma hhist htrace
          dsimp only
          rw [congrArg (fun m => familyClientMoveAt m j) hcurr]
          exact hlegal.1 st.history.2.length j hj
      · exact ih

/-- Against a legal server play, the current move (if any) satisfies request coherent cap. -/
private lemma grayTailCurrentMove_requestCoherentCap
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hrun : GrayTailRunLegal n q L a e B sigma A sm)
    (t j : ℕ)
    (hj : j < (grayTailBranchStateAt n q L a e sigma A sm t).slots.length) :
    requestCoherentCap (grayTailBranch q L a e) (dyadicScale (grayCallDepth q e))
      (familyClientMoveAt
        (if (grayTailBranchStateAt n q L a e sigma A sm t).done
         then []
         else grayTailCurrentMove q L e sigma
          (grayTailBranchStateAt n q L a e sigma A sm t)) j) := by
  obtain ⟨ha, hae, hB, hRung, hsm⟩ := hrun
  let b := grayTailBranch q L a e
  let st : GrayTailState n b :=
    grayTailStateAt (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
  have hsm' : familyServerPlayLegal n b A sm := by
    simpa [b] using hsm
  by_cases hdone : st.done
  · rw [hdone]
    simp [requestCoherentCap, familyClientMoveAt, getReq,
      (dyadicScale_pos (grayCallDepth q e)).le]
  · have hdone_eq : st.done = false := Bool.eq_false_of_not_eq_true hdone
    rw [hdone_eq]
    have hactive : (st.done || st.slots.isEmpty) ≠ true := by
      rw [hdone_eq]
      simp only [Bool.false_or]
      intro hempty
      have hlen : st.slots.length = 0 :=
        List.isEmpty_iff_length_eq_zero.mp hempty
      change j < st.slots.length at hj
      omega
    have hcert := grayTailCertified_stateAt
      (n := n) (b := b) q L a e sigma A sm t
    have hhist := grayTailHistoryOK_stateAt
      (n := n) (b := b) q L a e sigma A sm t
    have htrace := grayTailTrace_stateAt
      (n := n) (b := b) q L a e sigma A sm t
    have hcount : st.frozen.length < grayTailRoundCount q := by
      by_contra h
      push Not at h
      have hdone' := grayTail_done_of_roundCount_stateAt_core
        (q := q) (L := L) (a := a) (e := e) (sigma := sigma)
        (A := A) (sm := sm) (t := t) h
      change st.done = true at hdone'
      exact hdone hdone'
    have hb : grayTailBaseBranch q L ≤ b := by
      exact le_max_right _ _
    have hlocal := grayTailFutureServer_legal hcert hcount hsm'
    have hspec := grayTailRound_gameSpec
      ha hae hB hRung hcert hactive hb
    have hlegal := hspec.weak.legal
      (grayTailFutureServer q L e st sm) hlocal
    have hcurr := grayTailCurrentMove_eq_futurePlay
      q L e sigma hhist htrace
    simp only [Bool.false_eq_true, ite_false]
    rw [congrArg (fun m => familyClientMoveAt m j) hcurr]
    exact hlegal.1 st.history.2.length j hj

/-- All output entries of a gray tail state satisfy request coherent cap. -/
private lemma grayTailOutputEntries_requestCoherentCap
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (sm : ℕ → FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t : ℕ) :
    ∀ pr ∈ grayTailOutputEntries q L e sigma
      (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t),
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayCallDepth q e)) pr.2 := by
  let b := grayTailBranch q L a e
  let st : GrayTailState n b :=
    grayTailStateAt (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
  have hcoh : GrayTailFrozenCoherent q e st.frozen := by
    simpa [st, b] using
      (grayTailFrozenCoherent_stateAt ha hae hB hRung sm hsm t)
  have hcurrent :
      ∀ j < st.slots.length,
        requestCoherentCap b (dyadicScale (grayCallDepth q e))
          (familyClientMoveAt
            (if st.done then [] else grayTailCurrentMove q L e sigma st) j) := by
    intro j hj
    exact grayTailCurrentMove_requestCoherentCap ⟨ha, hae, hB, hRung, hsm⟩ t j hj
  intro pr hpr
  change pr ∈ grayTailEntries st.frozen st.slots
    (if st.done then [] else grayTailCurrentMove q L e sigma st) at hpr
  rw [grayTailEntries, List.mem_append] at hpr
  rcases hpr with hpr | hpr
  · rw [grayTailFrozenEntries, List.mem_flatMap] at hpr
    obtain ⟨p, hp, hpr⟩ := hpr
    rw [grayTailSlotEntries, List.mem_ofFn] at hpr
    obtain ⟨j, hj⟩ := hpr
    subst hj
    exact hcoh p hp j.val j.isLt
  · rw [grayTailSlotEntries, List.mem_ofFn] at hpr
    obtain ⟨j, hj⟩ := hpr
    subst hj
    exact hcurrent j.val j.isLt

/-- **Child E5e.**  Coherence and the root cap of the displayed outer move.

Every displayed request is nonnegative, the root request is at most
`dyadicScale a`, and every node carries the demand of its children.  This is
pure outer bookkeeping of `grayTailOutput`: the son requests are either a
`grayTailSonBase` (a sum of already displayed recursive root requests) or the
raised value `dyadicScale e`, at most `2 ^ (e - a)` sons are used, and
`2 ^ (e - a) * dyadicScale e = dyadicScale a`; the terminal root floor
`grayTailTargetFloor q a` is itself below `dyadicScale a`. -/
theorem grayTail_output_coherentCap
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (sm : ℕ → FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t i : ℕ) (hi : i < n) :
    requestCoherentCap (grayTailBranch q L a e) (dyadicScale a)
      (familyClientMoveAt
        (playClientFamily A n (grayTailStrategy q L a e sigma) sm t) i) := by
  let b := grayTailBranch q L a e
  let st : GrayTailState n b :=
    grayTailStateAt (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
  let entries := grayTailOutputEntries q L e sigma st
  let thresh := dyadicScale e - dyadicScale e / (6 * halfAmplification q)
  let eps := dyadicScale e
  have hplay :
      playClientFamily A n (grayTailStrategy q L a e sigma) sm t =
        grayTailOutput q L a e sigma st := by
    simpa [st, b] using
      (playClientFamily_grayTailStrategy q L a e n sigma A sm t)
  have hentries_coh :
      ∀ pr ∈ entries,
        requestCoherentCap b (dyadicScale (grayCallDepth q e)) pr.2 :=
    grayTailOutputEntries_requestCoherentCap ha hae hB hRung sm hsm t
  have hentries_nonneg : ∀ pr ∈ entries, ∀ x, 0 ≤ getReq pr.2 x := by
    intro pr hpr x
    exact (hentries_coh pr hpr).1 x
  have hentries_child :
      ∀ pr ∈ entries, ∀ x,
        getReq pr.2 x ≥ ∑ c : Fin b, getReq pr.2 (x ++ [c.val]) := by
    intro pr hpr x
    exact (hentries_coh pr hpr).2.2 x
  have hson_nonneg (c : Fin b) :
      0 ≤ grayTailSonRequest thresh eps entries ⟨i, hi⟩ c := by
    unfold grayTailSonRequest
    dsimp only
    split_ifs
    · exact (dyadicScale_pos e).le
    · exact grayTailSonBase_nonneg_global
        (fun pr hpr => hentries_nonneg pr hpr [])
  have hbase_cap (c : Fin b) :
      grayTailSonBase entries ⟨i, hi⟩ c ≤ eps := by
    simpa [st, entries, b, eps] using
      (grayTailSonBase_le_dyadicScale
        (q := q) (L := L) (a := a) (e := e) (t := t)
        (sigma := sigma) (A := A) (sm := sm)
        ha hae hB hRung hsm ⟨i, hi⟩ c)
  have hbase_le_son (c : Fin b) :
      grayTailSonBase entries ⟨i, hi⟩ c ≤
        grayTailSonRequest thresh eps entries ⟨i, hi⟩ c := by
    unfold grayTailSonRequest
    dsimp only
    split_ifs
    · exact hbase_cap c
    · exact le_rfl
  have hsum_le :
      (∑ c : Fin b, grayTailSonRequest thresh eps entries ⟨i, hi⟩ c) ≤
        dyadicScale a := by
    simpa [st, entries, b, thresh, eps] using
      (sum_grayTailSonRequest_le_dyadicScale
        (q := q) (L := L) (a := a) (e := e) (t := t)
        (sigma := sigma) (A := A) (sm := sm) hae ⟨i, hi⟩)
  have hmove :
      familyClientMoveAt
          (playClientFamily A n (grayTailStrategy q L a e sigma) sm t) i =
        graftTwoLevel
          (grayTailRootRequest st.done (grayTailTargetFloor q a)
            thresh eps entries ⟨i, hi⟩)
          b
          (fun c => if hc : c < b then
            grayTailSonRequest thresh eps entries ⟨i, hi⟩ ⟨c, hc⟩ else 0)
          (fun c c' => if hc : c < b then if hc' : c' < b then
            grayTailEntryMove entries (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩)
            else [] else []) := by
    rw [hplay]
    exact familyClientMoveAt_grayTailOutput st hi
  rw [hmove]
  refine requestCoherentCap_graftTwoLevel
    ?hroot0 ?hcap ?hson0 ?hsum ?hsonsum ?hpos ?hchild
  · unfold grayTailRootRequest
    split_ifs
    · exact (grayTailTargetFloor_nonneg q a).trans (le_max_right _ _)
    · exact Finset.sum_nonneg fun c _ => hson_nonneg c
  · unfold grayTailRootRequest
    split_ifs
    · exact max_le hsum_le (grayTailTargetFloor_le q a)
    · exact hsum_le
  · intro c hc
    rw [dite_eq_left hc]
    exact hson_nonneg ⟨c, hc⟩
  · have hsum_eq :
        (∑ c : Fin b, if hc : c.val < b then
          grayTailSonRequest thresh eps entries ⟨i, hi⟩ ⟨c.val, hc⟩ else 0) =
          ∑ c : Fin b, grayTailSonRequest thresh eps entries ⟨i, hi⟩ c := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dite_eq_left c.isLt]
    rw [hsum_eq]
    unfold grayTailRootRequest
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  · intro c hc
    rw [dite_eq_left hc]
    have hsum := (sum_grayTailEntryMove_root_le_grayTailSonBase
      entries hentries_nonneg ⟨i, hi⟩ ⟨c, hc⟩).trans
        (hbase_le_son ⟨c, hc⟩)
    refine le_trans (le_of_eq ?_) hsum
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [dite_eq_left hc, dite_eq_left c'.isLt]
  · intro c hc c' hc' x
    rw [dite_eq_left hc, dite_eq_left hc']
    exact grayTailEntryMove_nonneg entries hentries_nonneg
      (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩) x
  · intro c hc c' hc' x
    rw [dite_eq_left hc, dite_eq_left hc']
    exact grayTailEntryMove_child_le entries hentries_child
      (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩) x
/-- The son request is monotone in the son base, as long as the threshold does not exceed the
scale. -/
lemma grayTailSonRequest_mono {n b : ℕ} {threshold eps : ℚ}
    (htheps : threshold ≤ eps)
    {entries1 entries2 : List (GrayTailSlot n b × ClientMove)}
    (i : Fin n) (c : Fin b)
    (hbase : grayTailSonBase entries1 i c ≤ grayTailSonBase entries2 i c) :
    grayTailSonRequest threshold eps entries1 i c ≤
      grayTailSonRequest threshold eps entries2 i c := by
  change (if threshold < grayTailSonBase entries1 i c then eps
    else grayTailSonBase entries1 i c) ≤
      (if threshold < grayTailSonBase entries2 i c then eps
      else grayTailSonBase entries2 i c)
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso
    have h2' := not_lt.mp h2
    linarith
  · exact le_trans (not_lt.mp h1) htheps
  · exact hbase

/-- The root request is monotone in the son requests and in the finished flag. -/
lemma grayTailRootRequest_mono {n b : ℕ} {done1 done2 : Bool}
    {targetFloor threshold eps : ℚ}
    {entries1 entries2 : List (GrayTailSlot n b × ClientMove)}
    (i : Fin n)
    (hdone : done1 = true → done2 = true)
    (hson : ∀ c : Fin b,
      grayTailSonRequest threshold eps entries1 i c ≤
        grayTailSonRequest threshold eps entries2 i c) :
    grayTailRootRequest done1 targetFloor threshold eps entries1 i ≤
      grayTailRootRequest done2 targetFloor threshold eps entries2 i := by
  unfold grayTailRootRequest
  have hsum : ∑ c : Fin b, grayTailSonRequest threshold eps entries1 i c ≤
      ∑ c : Fin b, grayTailSonRequest threshold eps entries2 i c :=
    Finset.sum_le_sum fun c _ => hson c
  by_cases hd1 : done1
  · have hd2 : done2 = true := hdone hd1
    simp only [hd1, hd2, ↓reduceIte]
    exact max_le_max hsum le_rfl
  · simp only [hd1, Bool.false_eq_true, ↓reduceIte]
    by_cases hd2 : done2
    · simp only [hd2, ↓reduceIte]
      exact le_trans hsum (le_max_left _ _)
    · simp only [hd2, Bool.false_eq_true, ↓reduceIte]
      exact hsum

/-- Appending nonnegative entries only increases the move assembled for a slot. -/
lemma grayTailEntryMove_mono_append {n b : ℕ}
    (entries newEntries : List (GrayTailSlot n b × ClientMove))
    (hnonneg : ∀ pr ∈ newEntries, ∀ x, 0 ≤ getReq pr.2 x)
    (slot : GrayTailSlot n b) (y : GacsDayNode) :
    getReq (grayTailEntryMove entries slot) y ≤
      getReq (grayTailEntryMove (entries ++ newEntries) slot) y := by
  unfold grayTailEntryMove
  rw [List.find?_append]
  cases hfind : entries.find? (fun p => decide (p.1 = slot)) with
  | some pr =>
      simp
  | none =>
      simp only [Option.none_or]
      cases hnew : newEntries.find? (fun p => decide (p.1 = slot)) with
      | none =>
          simp
      | some pr =>
          have hmem : pr ∈ newEntries := List.mem_of_find?_eq_some hnew
          exact hnonneg pr hmem y

/-- The service threshold of the tail is at most `dyadicScale e`. -/
lemma grayTailThreshold_le_eps (q e : ℕ) :
    grayTailThreshold q e ≤ dyadicScale e := by
  have hpos : 0 ≤ dyadicScale e / (6 * halfAmplification q) := by
    exact div_nonneg (dyadicScale_pos e).le
      (mul_nonneg (by norm_num) (halfAmplification_pos q).le)
  unfold grayTailThreshold
  linarith

/-- If the frozen moves and the current move are nonnegative, so is every displayed entry. -/
lemma grayTailOutputEntries_nonneg {n b q L e : ℕ} {sigma : FamilyStrategyScheme}
    {st : GrayTailState n b}
    (hfrozen : ∀ p ∈ st.frozen, ∀ j < p.slots.length, ∀ x,
      0 ≤ getReq (familyClientMoveAt p.move j) x)
    (hcur : ∀ j < st.slots.length, ∀ x,
      0
        ≤ getReq (familyClientMoveAt (if st.done then [] else grayTailCurrentMove q L e
                                       sigma st) j) x)
    (pr : GrayTailSlot n b × ClientMove)
    (hpr : pr ∈ grayTailOutputEntries q L e sigma st) (x : GacsDayNode) :
    0 ≤ getReq pr.2 x := by
  unfold grayTailOutputEntries at hpr
  rw [grayTailEntries, List.mem_append] at hpr
  rcases hpr with hpr | hpr
  · rw [grayTailFrozenEntries, List.mem_flatMap] at hpr
    obtain ⟨p, hp, hpr⟩ := hpr
    rw [grayTailSlotEntries, List.mem_ofFn] at hpr
    obtain ⟨j, hj⟩ := hpr
    subst hj
    exact hfrozen p hp j.val j.isLt x
  · rw [grayTailSlotEntries, List.mem_ofFn] at hpr
    obtain ⟨j, hj⟩ := hpr
    subst hj
    exact hcur j.val j.isLt x

end Kolmogorov
