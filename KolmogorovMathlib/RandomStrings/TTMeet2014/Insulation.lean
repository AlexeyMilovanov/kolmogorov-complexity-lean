/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Structure

/-!
# Insulation of the boards (§4.2, §4.3 of the paper)

"Games for lower-priority requirements do not alter the game boards of games for higher-priority
requirements."  All proved here:

* `insul_rsAt`: while `R_m` has not acted since the last visit of `R_i` (`m < i`), every string on
  the board of `R_m` has length at most `c`, for `ε_i = 2 ^ (-c)`.  This is the choice of `c` in
  Case 1.
* `move_insulated`: a move never touches the board of a higher-priority requirement.
* `ours_eq_between`: between two consecutive visits of `R_i` with no reset at the second one, no
  string on the board of `R_i` is compressed by us: lower priorities miss it, and a move of a higher
  priority would force a reset.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

/-- The fields of the schedule are not changed by the cases of a stage. -/
def Frozen (r rs : ReqState) : Prop := r.lastActed = rs.lastActed ∧ r.lastVisit = rs.lastVisit

/-- The first part of Case 2 keeps the fields of the schedule, whether it ends the visit or returns
an agreed value. -/
theorem examineTop_frozen {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState} :
    (∀ r, examineTop I st i t c rs = .inl r → Frozen r.1 rs) ∧
      ∀ r, examineTop I st i t c rs = .inr r → Frozen r.1 rs := by
  constructor
  · intro r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · split at hr
      · cases hr
        exact ⟨rfl, rfl⟩
      · split at hr
        · cases hr
          exact ⟨rfl, rfl⟩
        · cases hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
          exact ⟨rfl, rfl⟩
        · cases hr
          exact ⟨rfl, rfl⟩
  · intro r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
        · cases hr
          exact ⟨rfl, rfl⟩
    · split at hr
      · cases hr
        exact ⟨rfl, rfl⟩
      · split at hr
        · cases hr
        · cases hr

/-- Case 2 keeps the fields of the schedule. -/
theorem caseTwo_frozen {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState} :
    Frozen (caseTwo I st i t c rs).1 rs := by
  have hex := examineTop_frozen (I := I) (st := st) (i := i) (t := t) (c := c) (rs := rs)
  unfold caseTwo
  dsimp only
  split
  · rename_i r hr
    exact hex.1 r hr
  · rename_i rs₁ σ hr
    have h₁ := hex.2 _ hr
    dsimp only at h₁
    split
    · exact h₁
    · split
      · exact h₁
      · split
        · exact h₁
        · split
          · exact h₁
          · split
            · exact h₁
            · exact h₁

/-- Case 3 keeps the fields of the schedule. -/
theorem caseThree_frozen {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState} {pl : Play} :
    Frozen (caseThree I st i t c rs pl).1 rs := by
  unfold caseThree
  dsimp only
  split_ifs
  · exact ⟨rfl, rfl⟩
  · split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- Case 1 keeps the fields of the schedule. -/
theorem caseOne_frozen {st : ConState} {i t : ℕ} : Frozen (caseOne st i t).1 (st.req i) := by
  unfold caseOne
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- The case distinction of a stage keeps the fields of the schedule of the requirement visited;
only `step` sets them. -/
theorem stepCore_frozen (I : Input) (st : ConState) :
    Frozen (stepCore I st).1 (st.req (Nat.unpair st.stage).1) := by
  unfold stepCore
  dsimp only
  split
  · exact caseOne_frozen
  · split
    · exact ⟨rfl, rfl⟩
    · split
      · exact caseTwo_frozen
      · exact caseThree_frozen

/-- The last action is at most the current stage. -/
theorem lastActed_le (I : Input) (s i : ℕ) : (rsAt I s i).lastActed ≤ s := by
  induction s with
  | zero => exact le_rfl
  | succ s ih =>
    by_cases hi : i = (Nat.unpair s).1
    · subst hi
      rw [rsAt_succ_self]
      dsimp only
      split_ifs
      · exact le_rfl
      · have hf := (stepCore_frozen I (stateAt I s)).1
        rw [stage_stateAt] at hf
        rw [hf]
        exact ih.trans (Nat.le_succ s)
    · rw [rsAt_succ_of_ne I hi]
      omega

/-- The last action is monotone. -/
theorem lastActed_succ (I : Input) (s i : ℕ) :
    (rsAt I s i).lastActed ≤ (rsAt I (s + 1) i).lastActed := by
  by_cases hi : i = (Nat.unpair s).1
  · subst hi
    rw [rsAt_succ_self]
    dsimp only
    split_ifs
    · exact (lastActed_le I s _).trans (Nat.le_succ s)
    · have hf := (stepCore_frozen I (stateAt I s)).1
      rw [stage_stateAt] at hf
      rw [hf]
      rfl
  · rw [rsAt_succ_of_ne I hi]

/-- The last action is monotone in the stage. -/
theorem lastActed_mono (I : Input) (i : ℕ) {s s' : ℕ} (h : s ≤ s') :
    (rsAt I s i).lastActed ≤ (rsAt I s' i).lastActed := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (lastActed_succ I _ i)

/-- Adding a table is an action. -/
theorem caseTwo_acted_of_tables {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState}
    (h : ReqWF i t rs) (hc : rs.c = some c)
    (hgrow : (caseTwo I st i t c rs).1.tables ≠ rs.tables) : (caseTwo I st i t c rs).2 = true := by
  obtain ⟨hl, hr⟩ := examineTop_spec (I := I) (st := st) h hc
  unfold caseTwo at hgrow ⊢
  dsimp only at hgrow ⊢
  split at hgrow
  · rename_i r hex
    exact absurd (hl r hex).1 hgrow
  · rename_i rs₁ σ hex
    obtain ⟨ht, -, -, -, -⟩ := hr _ hex
    dsimp only at ht
    split at hgrow
    · exact absurd ht hgrow
    · split_ifs at hgrow ⊢ with hx
      · exact absurd ht hgrow
      · split at hgrow
        · exact absurd ht hgrow
        · rename_i tbl htbl
          generalize topOutcome (arenaOf c (rs.tables ++ [tbl]))
            (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
            (levelBudget (rs.tables ++ [tbl]) 0) = v at hgrow ⊢
          cases v with
          | principal σ' => rfl
          | split j k S =>
            dsimp only at hgrow ⊢
            split at hgrow
            · rfl
            · exact absurd ht hgrow
          | meet S T =>
            dsimp only at hgrow ⊢
            split at hgrow
            · rfl
            · exact absurd ht hgrow
          | stuck =>
            dsimp only at hgrow ⊢
            split at hgrow
            · rfl
            · exact absurd ht hgrow

/-- Adding a table is an action, at the level of a stage. -/
theorem stepCore_acted_of_tables {I : Input} {st : ConState}
    (h : ReqWF (Nat.unpair st.stage).1 (st.stage + 1) (st.req (Nat.unpair st.stage).1))
    (hne : (stepCore I st).1.tables ≠ (st.req (Nat.unpair st.stage).1).tables) :
    (stepCore I st).2.2.2 = true := by
  unfold stepCore at hne ⊢
  dsimp only at hne ⊢
  cases hr : mustReset I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2 (st.stage + 1) with
  | true => simp
  | false =>
    simp only [hr, Bool.false_eq_true, ite_false] at hne ⊢
    cases hc : (st.req (Nat.unpair st.stage).1).c with
    | none =>
      simp only [hc] at hne
      exact absurd rfl hne
    | some c =>
      simp only [hc] at hne ⊢
      cases hp : (st.req (Nat.unpair st.stage).1).play with
      | none =>
        simp only [hp] at hne ⊢
        exact caseTwo_acted_of_tables h hc hne
      | some pl =>
        simp only [hp] at hne
        exact absurd (caseThree_spec h hp).1 hne

/-- A move of ours is an action. -/
theorem caseThree_acted_of_new {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState} {pl : Play}
    {j : Fin 3} {τ : Str} (hτ : τ ∈ (caseThree I st i t c rs pl).2.1 j) (hτ' : τ ∉ st.ours j) :
    (caseThree I st i t c rs pl).2.2 = true := by
  have hfold : ∀ moves : List (BoardGame × Finset Str),
      τ ∈ moves.foldr (fun q acc => if q.1.board = j then q.2 ∪ acc else acc) (st.ours j) →
        ∃ q ∈ moves, τ ∈ q.2 := by
    intro moves
    induction moves with
    | nil => exact fun h => absurd h hτ'
    | cons q moves ih =>
      simp only [List.foldr_cons]
      split_ifs
      · intro h
        rcases mem_union.1 h with h | h
        · exact ⟨q, List.mem_cons_self, h⟩
        · obtain ⟨q', hq', h'⟩ := ih h
          exact ⟨q', List.mem_cons_of_mem _ hq', h'⟩
      · intro h
        obtain ⟨q', hq', h'⟩ := ih h
        exact ⟨q', List.mem_cons_of_mem _ hq', h'⟩
  unfold caseThree at hτ ⊢
  dsimp only at hτ ⊢
  split_ifs at hτ ⊢ with hl hE
  · obtain ⟨q, hq, h'⟩ := hfold _ hτ
    rw [List.any_eq_true]
    exact ⟨q, hq, decide_eq_true ⟨τ, h'⟩⟩
  · split at hτ
    · split at hτ
      · exact absurd hτ hτ'
      · exact absurd hτ hτ'
    · exact absurd hτ hτ'
  · split at hτ
    · exact absurd hτ hτ'
    · exact absurd hτ hτ'

/-- A new string at a stage: Case 3 with no reset, on the board of the scheduled requirement, longer
than `c`, and an action. -/
theorem new_string_spec (I : Input) {j : Fin 3} {s : ℕ} {τ : Str} (h : τ ∈ oursAt I j (s + 1))
    (hτ : τ ∉ oursAt I j s) :
    mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) = false ∧
      (∃ c, (rsAt I s (Nat.unpair s).1).c = some c ∧ c < τ.length) ∧
      τ ∈ boardOf (rsAt I s (Nat.unpair s).1).tables ∧
      (rsAt I (s + 1) (Nat.unpair s).1).lastActed = s + 1 := by
  change τ ∈ (stepCore I (stateAt I s)).2.1 j at h
  have hτ' : τ ∉ (stateAt I s).ours j := hτ
  have hact : (stepCore I (stateAt I s)).2.2.2 = true → (rsAt I (s + 1) (Nat.unpair s).1).lastActed
      = s + 1 := by
    intro htrue
    rw [rsAt_succ_self]
    simp [htrue]
  have hst := stage_stateAt I s
  unfold stepCore at h hact
  dsimp only at h hact
  rw [hst] at h hact
  cases hr : mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) with
  | true =>
    simp only [hr, ite_true] at h
    exact absurd h hτ'
  | false =>
    simp only [hr, Bool.false_eq_true, ite_false] at h hact
    cases hc : ((stateAt I s).req (Nat.unpair s).1).c with
    | none =>
      simp only [hc] at h
      exact absurd h hτ'
    | some c =>
      simp only [hc] at h hact
      cases hp : ((stateAt I s).req (Nat.unpair s).1).play with
      | none =>
        simp only [hp] at h
        exact absurd h hτ'
      | some pl =>
        simp only [hp] at h hact
        obtain ⟨g, hg, hmove⟩ := caseThree_new_string h hτ'
        have hw := reqWF_rsAt I s (Nat.unpair s).1
        obtain ⟨c', hc', ha, hgl⟩ := hw.play pl hp
        have hcc : c' = c := by
          have h1 : (rsAt I s (Nat.unpair s).1).c = some c := hc
          rw [h1] at hc'
          exact (Option.some.inj hc').symm
        subst hcc
        obtain ⟨hsub, hcost⟩ := respond_legal pl.arena g
          ((stateAt I s).positionList I pl.arena (s + 1) g.board)
          (g.oppLimit - oppSpend I pl.arena pl.start (s + 1)) (g.ourLimit - g.spent)
        have hboard : τ ∈ pl.arena.board := by
          have := hsub hmove
          simp only [List.mem_toFinset, ConState.positionList, List.mem_filter] at this
          exact List.mem_toFinset.2 this.1
        have hlen : τ.length ≤ maxLen (rsAt I s (Nat.unpair s).1).tables := by
          refine length_le_maxLen ?_
          have := Arena.mem_board.1 hboard
          rw [ha] at this
          exact this
        have hweight : pl.arena.w τ ≤ cost pl.arena.w (respond pl.arena g
            ((stateAt I s).positionList I pl.arena (s + 1) g.board)
            (g.oppLimit - oppSpend I pl.arena pl.start (s + 1)) (g.ourLimit - g.spent)) :=
          Finset.single_le_sum (f := pl.arena.w) (fun _ _ => Nat.zero_le _) hmove
        have hbudget : pl.arena.w τ ≤ levelBudget (rsAt I s (Nat.unpair s).1).tables 0 :=
          hweight.trans (hcost.trans ((Nat.sub_le _ _).trans (hgl g hg)))
        rw [ha] at hbudget
        refine ⟨rfl, ⟨c', hc', length_gt_of_weight_le hlen hbudget⟩, ?_, ?_⟩
        · rw [ha] at hboard
          obtain ⟨tt, ht, hq⟩ := Arena.mem_board.1 hboard
          exact Arena.mem_board.2 ⟨tt, ht, hq⟩
        · exact hact (caseThree_acted_of_new h hτ')

/-- The tables of the enumeration are found among the tables defined at a stage. -/
theorem mem_tablesUpTo {i s n : ℕ} {l : List TTable} (h : tablesUpTo i s n = some l) :
    ∀ tt ∈ l, ∃ k, tableAt i k s = some tt := by
  induction n generalizing l with
  | zero =>
    have : l = [] := by
      simp only [tablesUpTo, Option.some.injEq] at h
      exact h.symm
    subst this
    simp
  | succ n ih =>
    simp only [tablesUpTo, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨l', hl', tt', ht', rfl⟩ := h
    intro tt htt
    rcases List.mem_append.1 htt with h1 | h1
    · exact ih hl' tt h1
    · rw [List.mem_singleton.1 h1]
      exact ⟨n, ht'⟩

/-- A string on the board of `R_m`, for `m < i`, is below the new `c` of `R_i`. -/
theorem length_le_newC {st : ConState} {i m t : ℕ} (hm : m < i) {tables : List TTable}
    (hwf : tablesUpTo m t tables.length = some tables) {z : Str} (hz : z ∈ boardOf tables) :
    z.length ≤ newC st i t := by
  obtain ⟨tt, htt, hq⟩ := Arena.mem_board.1 hz
  obtain ⟨k, hk⟩ := mem_tablesUpTo hwf tt htt
  have hkt : k < t := by
    by_contra hle
    rw [tableAt_eq_none_of_le (not_lt.1 hle)] at hk
    cases hk
  have hmem : z ∈ definedStrings i t := by
    simp only [definedStrings, List.mem_flatMap, List.mem_range]
    refine ⟨m, hm, k, hkt, ?_⟩
    rw [hk]
    exact hq
  have := length_le_foldr_max hmem
  unfold newC
  exact this.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The invariant of insulation. -/
def Insul (I : Input) (s i : ℕ) : Prop :=
  ∀ c, (rsAt I s i).c = some c → ∀ m < i, (rsAt I s m).lastActed ≤ (rsAt I s i).lastVisit →
    ∀ z ∈ boardOf (rsAt I s m).tables, z.length ≤ c

/-- **The invariant of insulation.**  While `R_m` has not acted since the last visit of `R_i`, the
board of `R_m` is below `c`. -/
theorem insul_rsAt (I : Input) : ∀ s i, Insul I s i := by
  intro s
  induction s with
  | zero =>
    intro i c hc
    cases hc
  | succ s ih =>
    intro i c hc m hm hact z hz
    have hw := fun i' => (reqWF_rsAt I s i').mono (Nat.le_succ s)
    by_cases hi : i = (Nat.unpair s).1
    · -- `R_i` is visited.
      have hmne : m ≠ (Nat.unpair s).1 := by omega
      rw [rsAt_succ_of_ne I hmne] at hact hz
      subst hi
      rw [rsAt_succ_self] at hc
      change (stepCore I (stateAt I s)).1.c = some c at hc
      cases hr : mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) with
      | true =>
        have hreset : stepCore I (stateAt I s) =
            ((caseOne (stateAt I s) (Nat.unpair s).1 (s + 1)).1, (stateAt I s).ours,
              (caseOne (stateAt I s) (Nat.unpair s).1 (s + 1)).2, true) := by
          unfold stepCore
          dsimp only
          rw [stage_stateAt, hr]
          rfl
        rw [hreset] at hc
        rw [(caseOne_spec (hw (Nat.unpair s).1)).2.2.2.1] at hc
        cases hc
        exact length_le_newC hm (hw m).tables hz
      | false =>
        have hr' : mustReset I (stateAt I s) (Nat.unpair (stateAt I s).stage).1
            (Nat.unpair (stateAt I s).stage).2 ((stateAt I s).stage + 1) = false := by
          rw [stage_stateAt]
          exact hr
        rw [stepCore_c_of_no_reset hr', stage_stateAt] at hc
        simp only [mustReset, Bool.or_eq_false_iff, List.any_eq_false, List.mem_range] at hr
        have hnot := hr.2 m hm
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hnot
        exact ih _ c hc m hm (not_lt.1 hnot.1) z hz
    · have hc' : (rsAt I s i).c = some c := by
        rwa [rsAt_succ_of_ne I hi] at hc
      rw [rsAt_succ_of_ne I hi] at hact
      by_cases hmi : m = (Nat.unpair s).1
      · -- `R_m` is visited.
        have hsame : (rsAt I (s + 1) m).tables = (rsAt I s m).tables := by
          by_contra hne
          have hne' : (stepCore I (stateAt I s)).1.tables ≠ (rsAt I s m).tables := by
            intro heq
            apply hne
            subst hmi
            rw [rsAt_succ_self]
            exact heq
          -- Adding a table is an action, later than the last visit of `R_i`.
          have hacted : (rsAt I (s + 1) m).lastActed = s + 1 := by
            subst hmi
            rw [rsAt_succ_self]
            have htrue : (stepCore I (stateAt I s)).2.2.2 = true :=
              stepCore_acted_of_tables (by rw [stage_stateAt]; exact hw _)
                (by rw [stage_stateAt]; exact hne')
            simp [htrue]
          have := lastVisit_le I s i
          omega
        rw [hsame] at hz
        have hmono := lastActed_succ I s m
        exact ih i c hc' m hm (hmono.trans hact) z hz
      · rw [rsAt_succ_of_ne I hmi] at hact hz
        exact ih i c hc' m hm hact z hz

/-- **A move never touches the board of a higher-priority requirement.** -/
theorem move_insulated (I : Input) {j : Fin 3} {s m : ℕ} {τ : Str} (hτ : τ ∈ oursAt I j (s + 1))
    (hτ' : τ ∉ oursAt I j s) (hm : m < (Nat.unpair s).1) :
    τ ∉ boardOf (rsAt I s m).tables := by
  obtain ⟨hr, ⟨c, hc, hlt⟩, -, -⟩ := new_string_spec I hτ hτ'
  simp only [mustReset, Bool.or_eq_false_iff, List.any_eq_false, List.mem_range] at hr
  have hnot := hr.2 m hm
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hnot
  intro hz
  have := insul_rsAt I s _ c hc m hm (not_lt.1 hnot.1) τ hz
  omega

/-- **Between two consecutive visits of `R_i`, with no reset at the second one, we do not compress
any string on the board of `R_i`.** -/
theorem ours_eq_between (I : Input) {i s s' : ℕ} (hlt : s < s')
    (hbetween : ∀ s'', s < s'' → s'' < s' → (Nat.unpair s'').1 ≠ i)
    (hvisit : (Nat.unpair s).1 = i)
    (hno : mustReset I (stateAt I s') i (Nat.unpair s').2 (s' + 1) = false) (j : Fin 3) {z : Str}
    (hz : z ∈ boardOf (rsAt I (s + 1) i).tables) (hzs : z ∈ oursAt I j s') :
    z ∈ oursAt I j (s + 1) := by
  by_contra hnot
  -- The first stage at which `z` is compressed.
  classical
  have hex : ∃ u, z ∈ oursAt I j u := ⟨s', hzs⟩
  let u := Nat.find hex
  have hu : z ∈ oursAt I j u := Nat.find_spec hex
  have hu0 : u ≠ 0 := by
    intro h0
    rw [show u = 0 from h0] at hu
    exact absurd hu (by simp [oursAt, stateAt])
  obtain ⟨u', huu⟩ := Nat.exists_eq_succ_of_ne_zero hu0
  have hu' : z ∉ oursAt I j u' := Nat.find_min hex (show u' < u by omega)
  have hu1 : z ∈ oursAt I j (u' + 1) := by
    have : u = u' + 1 := huu
    rw [← this]
    exact hu
  have hge : s + 1 ≤ u' := by
    by_contra hcon
    exact hnot (oursAt_mono I j (show u' + 1 ≤ s + 1 by omega) hu1)
  have hle : u' < s' := by
    have : u ≤ s' := Nat.find_min' hex hzs
    omega
  have hmover : (Nat.unpair u').1 ≠ i := hbetween u' (by omega) hle
  have hconst : rsAt I u' i = rsAt I (s + 1) i := rsAt_const I hge fun s'' h1 h2 =>
    hbetween s'' (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hmover with hlow | hhigh
  · -- A higher-priority move is an action, which would force a reset.
    obtain ⟨-, -, -, hact⟩ := new_string_spec I hu1 hu'
    have hmono := lastActed_mono I (Nat.unpair u').1 (show u' + 1 ≤ s' by omega)
    have hvis : (rsAt I s' i).lastVisit = s + 1 := by
      rw [rsAt_const I (show s + 1 ≤ s' by omega) fun s'' h1 h2 => hbetween s'' (by omega) h2]
      have := lastVisit_self I s
      rwa [hvisit] at this
    simp only [mustReset, Bool.or_eq_false_iff, List.any_eq_false, List.mem_range] at hno
    have hnot' := hno.2 _ hlow
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hnot'
    have h1 : ¬ ((stateAt I s').req i).lastVisit <
        ((stateAt I s').req (Nat.unpair u').1).lastActed :=
      hnot'.1
    have h2 : ((stateAt I s').req i).lastVisit = s + 1 := hvis
    have h3 : u' + 1 ≤ ((stateAt I s').req (Nat.unpair u').1).lastActed := by
      rw [hact] at hmono
      exact hmono
    omega
  · -- A lower-priority move misses the board.
    refine move_insulated I hu1 hu' hhigh ?_
    rw [hconst]
    exact hz

end Kolmogorov.RandomStrings.TTMeet
