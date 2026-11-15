/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Construction
import Mathlib.Tactic.FinCases

/-!
# The structure of the run

Facts about the stage transition which involve no game-theoretic content, all proved here:

* `reqWF_rsAt`: at every stage the examined tables are the actual tables of the enumeration, an
  agreed value has the right length, the arena of a play is the current one, our budgets are at most
  `ε`, and `c ≥ i + 7`.
* `tables_prefix`: the examined tables only grow, as initial segments, by at most one per stage.
* `length_ge_of_mem_oursAt`: every string we compress has length at least `8`.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

/-- The hypotheses on the stage data. -/
structure Input.Valid (I : Input) : Prop where
  /-- The opponent's approximation is computable. -/
  opp_computable : Computable fun p : ℕ × Str => I.opp p.1 p.2
  /-- The approximation of `X` is computable. -/
  X_computable : Computable fun p : ℕ × Str => I.X p.1 p.2
  /-- Compressed strings stay compressed. -/
  opp_mono : ∀ {s s' : ℕ} {τ : Str}, s ≤ s' → I.opp s τ = true → I.opp s' τ = true
  /-- The opponent's total spending, in true measure, is at most `1/32`. -/
  opp_budget : ∀ S : Finset Str, (∀ τ ∈ S, ∃ s, I.opp s τ = true) → trueCost S ≤ 1 / 32

/-- The state of the requirement `i` after `s` stages. -/
def rsAt (I : Input) (s i : ℕ) : ReqState := (stateAt I s).req i

/-- A move of a strategy is a subset of the position within budget, unconditionally. -/
theorem respond_legal (ar : Arena) (g : BoardGame) (La : List Str) (a b : ℕ) :
    respond ar g La a b ⊆ La.toFinset ∧ cost ar.w (respond ar g La a b) ≤ b := by
  unfold respond
  dsimp only
  cases hf : (La.sublists.map List.toFinset).find? (fun p =>
      decide (cost ar.w p ≤ b) &&
        (if p = ∅ then decide (ar.value La.toFinset ∈ g.target) &&
            decide (ar.Forces g.target La.toFinset a b)
         else decide (ar.Forces g.target (La.toFinset \ p) a (b - cost ar.w p)))) with
  | none => simp
  | some p =>
    simp only [Option.getD_some]
    have hmem := List.mem_of_find?_eq_some hf
    have hok := List.find?_some hf
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hmem
    refine ⟨fun z hz => ?_, ?_⟩
    · exact List.mem_toFinset.2 ((List.mem_sublists.1 hl).subset (List.mem_toFinset.1 hz))
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      exact hok.1

/-- Closing a window keeps the tables. -/
@[simp] theorem closeEpoch_tables (rs : ReqState) (i c stop t : ℕ) (f : Bool) :
    (rs.closeEpoch i c stop t f).tables = rs.tables := rfl
/-- Closing a window keeps the agreed value. -/
@[simp] theorem closeEpoch_baseline (rs : ReqState) (i c stop t : ℕ) (f : Bool) :
    (rs.closeEpoch i c stop t f).baseline = rs.baseline := rfl
/-- Closing a window keeps the games in progress. -/
@[simp] theorem closeEpoch_play (rs : ReqState) (i c stop t : ℕ) (f : Bool) :
    (rs.closeEpoch i c stop t f).play = rs.play := rfl
/-- Closing a window keeps `c`. -/
@[simp] theorem closeEpoch_c (rs : ReqState) (i c stop t : ℕ) (f : Bool) :
    (rs.closeEpoch i c stop t f).c = rs.c := rfl

/-- A principal verdict names a vector of the right length. -/
theorem topOutcome_principal {ar : Arena} {A : Fin 3 → Finset Str} {E : ℕ} {σ : List Bool}
    (h : topOutcome ar A E = .principal σ) : σ.length = ar.tables.length := by
  unfold topOutcome at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i σ' hσ'
        cases h
        exact mem_allVec.1 (List.mem_of_find?_eq_some hσ')
      · cases h

/-- The balanced games are on the given arena, with the given budget for us. -/
theorem balancedPlay_spec {ar : Arena} {t E : ℕ} {v : TopOutcome} {pl : Play}
    (h : balancedPlay ar t E v = some pl) : pl.arena = ar ∧ ∀ g ∈ pl.games, g.ourLimit = E := by
  unfold balancedPlay at h
  split at h
  · cases h
    refine ⟨rfl, fun g hg => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> rfl
  · cases h
    refine ⟨rfl, fun g hg => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> rfl
  · cases h

/-- The budget of every level of the stack is at most the budget `ε` of level `0`. -/
theorem levelBudget_le_zero (tables : List TTable) (ℓ : ℕ) :
    levelBudget tables ℓ ≤ levelBudget tables 0 := by
  unfold levelBudget
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The well-formedness of the state of a requirement at stage `t`. -/
structure ReqWF (i t : ℕ) (rs : ReqState) : Prop where
  /-- The examined tables are the actual tables of the enumeration, converged by stage `t`. -/
  tables : tablesUpTo i t rs.tables.length = some rs.tables
  /-- An agreed value has the right length. -/
  baseline : ∀ bl, rs.baseline = some bl → bl.σ.length = rs.tables.length
  /-- A play is on the current arena, and our budgets are at most `ε`. -/
  play : ∀ pl, rs.play = some pl → ∃ c, rs.c = some c ∧ pl.arena = arenaOf c rs.tables ∧
    ∀ g ∈ pl.games, g.ourLimit ≤ levelBudget rs.tables 0
  /-- The floor of `c`. -/
  floor : ∀ c, rs.c = some c → i + 7 ≤ c

/-- Well-formedness at stage `t` implies well-formedness at every later stage. -/
theorem ReqWF.mono {i t t' : ℕ} {rs : ReqState} (h : ReqWF i t rs) (ht : t ≤ t') : ReqWF i t' rs :=
  ⟨tablesUpTo_mono ht h.tables, h.baseline, h.play, h.floor⟩

/-- **Case 1** keeps the tables and well-formedness. -/
theorem caseOne_spec {st : ConState} {i t : ℕ} (h : ReqWF i t (st.req i)) :
    (caseOne st i t).1.tables = (st.req i).tables ∧ (caseOne st i t).1.play = none ∧
      (caseOne st i t).1.baseline = none ∧ (caseOne st i t).1.c = some (newC st i t) ∧
      ReqWF i t (caseOne st i t).1 := by
  have htab : (caseOne st i t).1.tables = (st.req i).tables := by
    unfold caseOne
    dsimp only
    split <;> rfl
  have hc : (caseOne st i t).1.c = some (newC st i t) := by
    unfold caseOne
    dsimp only
  have hp : (caseOne st i t).1.play = none := by
    unfold caseOne
    dsimp only
  have hb : (caseOne st i t).1.baseline = none := by
    unfold caseOne
    dsimp only
  refine ⟨htab, hp, hb, hc, ?_, ?_, ?_, ?_⟩
  · rw [htab]
    exact h.tables
  · intro bl hbl
    rw [hb] at hbl
    cases hbl
  · intro pl hpl
    rw [hp] at hpl
    cases hpl
  · intro c hcc
    rw [hc] at hcc
    cases hcc
    exact le_max_left _ _

/-- The first part of Case 2. -/
theorem examineTop_spec {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState}
    (h : ReqWF i t rs) (hc : rs.c = some c) :
    (∀ r, examineTop I st i t c rs = .inl r → r.1.tables = rs.tables ∧ ReqWF i t r.1) ∧
      ∀ r, examineTop I st i t c rs = .inr r →
        r.1.tables = rs.tables ∧ r.1.c = rs.c ∧ r.1.play = rs.play ∧
          r.1.baseline = some ⟨r.2, fun _ => t⟩ ∧ r.2.length = rs.tables.length := by
  have hE : ∀ pl : Play, pl.arena = arenaOf c rs.tables →
      (∀ g ∈ pl.games, g.ourLimit ≤ levelBudget rs.tables 0) →
        ∀ rs' : ReqState, rs'.tables = rs.tables → rs'.c = rs.c → rs'.baseline = rs.baseline →
          rs'.play = some pl → ReqWF i t rs' := by
    intro pl ha hg rs' ht hc' hb hp
    refine ⟨by rw [ht]; exact h.tables, ?_, ?_, ?_⟩
    · intro bl hbl
      rw [ht]
      exact h.baseline bl (hb ▸ hbl)
    · intro pl' hpl'
      rw [hp] at hpl'
      cases hpl'
      exact ⟨c, hc' ▸ hc, ht ▸ ha, ht ▸ hg⟩
    · intro c' hc''
      exact h.floor c' (hc' ▸ hc'')
  constructor
  · intro r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · split at hr
      · cases hr
        exact ⟨rfl, ⟨h.tables, fun bl hbl => (by cases hbl), h.play, h.floor⟩⟩
      · split at hr
        · cases hr
          refine ⟨rfl, hE _ rfl ?_ _ rfl rfl rfl rfl⟩
          intro g hg
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> exact le_rfl
        · cases hr
    · split at hr
      · cases hr
      · split at hr
        · rename_i pl hpl
          cases hr
          obtain ⟨ha, hg⟩ := balancedPlay_spec hpl
          refine ⟨rfl, hE pl ha (fun g hg' => (hg g hg').le) _ rfl rfl rfl rfl⟩
        · cases hr
          exact ⟨rfl, h⟩
  · intro r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · rename_i bl hbl
      split at hr
      · cases hr
      · split at hr
        · cases hr
        · cases hr
          exact ⟨rfl, rfl, rfl, rfl, h.baseline bl hbl⟩
    · split at hr
      · rename_i σ hσ
        cases hr
        refine ⟨rfl, rfl, rfl, rfl, ?_⟩
        exact topOutcome_principal hσ
      · split at hr
        · cases hr
        · cases hr

/-- **Case 2** keeps the tables, or adds a table of the enumeration. -/
theorem caseTwo_spec {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState}
    (h : ReqWF i t rs) (hc : rs.c = some c) (hnp : rs.play = none) :
    ReqWF i t (caseTwo I st i t c rs).1 ∧
      ((caseTwo I st i t c rs).1.tables = rs.tables ∨
        ∃ tbl, (caseTwo I st i t c rs).1.tables = rs.tables ++ [tbl] ∧
          tableAt i rs.tables.length t = some tbl) := by
  obtain ⟨hl, hr⟩ := examineTop_spec (I := I) (st := st) h hc
  unfold caseTwo
  dsimp only
  split
  · rename_i r hex
    obtain ⟨ht, hw⟩ := hl r hex
    exact ⟨hw, Or.inl ht⟩
  · rename_i rs₁ σ hex
    obtain ⟨ht, hc₁, hp₁, hb₁, hσ⟩ := hr _ hex
    dsimp only at ht hc₁ hp₁ hb₁ hσ
    have hw₁ : ReqWF i t rs₁ := by
      refine ⟨by rw [ht]; exact h.tables, ?_, ?_, ?_⟩
      · intro bl hbl
        rw [hb₁] at hbl
        cases hbl
        rw [ht]
        exact hσ
      · intro pl hpl
        rw [hp₁] at hpl
        obtain ⟨c', hc', ha, hg⟩ := h.play pl hpl
        exact ⟨c', hc₁ ▸ hc', ht ▸ ha, ht ▸ hg⟩
      · intro c' hc'
        exact h.floor c' (hc₁ ▸ hc')
    split
    · rename_i ℓ j _
      dsimp only
      refine ⟨⟨hw₁.tables, hw₁.baseline, ?_, hw₁.floor⟩, Or.inl ht⟩
      intro pl hpl
      cases hpl
      refine ⟨c, hc₁ ▸ hc, by rw [ht], ?_⟩
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rw [ht]
      rcases hg with rfl | rfl <;> exact levelBudget_le_zero _ _
    · split
      · exact ⟨hw₁, Or.inl ht⟩
      · split
        · exact ⟨hw₁, Or.inl ht⟩
        · rename_i tbl htbl
          have htab : tablesUpTo i t (rs.tables ++ [tbl]).length = some (rs.tables ++ [tbl]) := by
            rw [List.length_append, List.length_singleton]
            simp only [tablesUpTo, Option.pure_def, Option.bind_eq_bind, h.tables,
              Option.bind_some, htbl]
          split
          · rename_i σ' hσ'
            refine ⟨⟨htab, ?_, ?_, hw₁.floor⟩, Or.inr ⟨tbl, rfl, htbl⟩⟩
            · intro bl hbl
              cases hbl
              exact topOutcome_principal hσ'
            · intro pl hpl
              change rs₁.play = some pl at hpl
              rw [hp₁, hnp] at hpl
              cases hpl
          · split
            · rename_i pl hpl
              obtain ⟨ha, hg⟩ := balancedPlay_spec hpl
              refine ⟨⟨htab, fun bl hbl => (by cases hbl), ?_, hw₁.floor⟩,
                Or.inr ⟨tbl, rfl, htbl⟩⟩
              intro pl' hpl'
              cases hpl'
              exact ⟨c, hc₁ ▸ hc, ha, fun g hg' => (hg g hg').le⟩
            · exact ⟨hw₁, Or.inl ht⟩

/-- **Case 3** keeps the tables, and well-formedness. -/
theorem caseThree_spec {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState} {pl : Play}
    (h : ReqWF i t rs) (hp : rs.play = some pl) :
    (caseThree I st i t c rs pl).1.tables = rs.tables ∧
        ReqWF i t (caseThree I st i t c rs pl).1 := by
  obtain ⟨c', hc', ha, hg⟩ := h.play pl hp
  have hplt : pl.arena.tables = rs.tables := by rw [ha]; rfl
  have hstop : ∀ rs' : ReqState, rs'.tables = rs.tables → rs'.c = rs.c → rs'.play = none →
      rs'.baseline = none → ReqWF i t rs' := by
    intro rs' ht hc'' hp' hb'
    refine ⟨by rw [ht]; exact h.tables, ?_, ?_, ?_⟩
    · intro bl hbl
      rw [hb'] at hbl
      cases hbl
    · intro pl' hpl'
      rw [hp'] at hpl'
      cases hpl'
    · intro c'' hc'''
      exact h.floor c'' (hc'' ▸ hc''')
  unfold caseThree
  dsimp only
  split_ifs with hl hE
  · refine ⟨rfl, ⟨h.tables, h.baseline, ?_, h.floor⟩⟩
    intro pl' hpl'
    cases hpl'
    refine ⟨c', hc', ha, fun g hg' => ?_⟩
    simp only [List.mem_map] at hg'
    obtain ⟨q, hq, rfl⟩ := hg'
    obtain ⟨g₀, hg₀, rfl⟩ := hq
    exact hg g₀ hg₀
  · split
    · split
      · refine ⟨rfl, ⟨h.tables, h.baseline, ?_, h.floor⟩⟩
        intro pl' hpl'
        cases hpl'
        refine ⟨c', hc', ha, fun g hg' => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rw [← hplt]
        rcases hg' with rfl | rfl <;> exact le_rfl
      · refine ⟨rfl, ⟨h.tables, ?_, ?_, h.floor⟩⟩
        · intro bl' hbl'
          obtain ⟨bl, hbl, rfl⟩ := Option.map_eq_some_iff.1 hbl'
          exact h.baseline bl hbl
        · intro pl' hpl'
          cases hpl'
    · exact ⟨rfl, hstop _ rfl rfl rfl rfl⟩
  · split
    · exact ⟨rfl, hstop _ rfl rfl rfl rfl⟩
    · exact ⟨rfl, hstop _ rfl rfl rfl rfl⟩

/-- **A stage** keeps well-formedness, and the tables grow by at most one table of the
enumeration. -/
theorem stepCore_spec (I : Input) (st : ConState) (h : ReqWF (Nat.unpair st.stage).1 (st.stage + 1)
    (st.req (Nat.unpair st.stage).1)) :
    ReqWF (Nat.unpair st.stage).1 (st.stage + 1) (stepCore I st).1 ∧
      ((stepCore I st).1.tables = (st.req (Nat.unpair st.stage).1).tables ∨
        ∃ tbl, (stepCore I st).1.tables = (st.req (Nat.unpair st.stage).1).tables ++ [tbl] ∧
          tableAt (Nat.unpair st.stage).1 (st.req (Nat.unpair st.stage).1).tables.length
            (st.stage + 1) = some tbl) := by
  unfold stepCore
  dsimp only
  split
  · obtain ⟨ht, -, -, -, hw⟩ := caseOne_spec h
    exact ⟨hw, Or.inl ht⟩
  · split
    · exact ⟨h, Or.inl rfl⟩
    · rename_i c hc
      split
      · rename_i hnp
        exact caseTwo_spec h hc hnp
      · rename_i pl hp
        obtain ⟨ht, hw⟩ := caseThree_spec h hp
        exact ⟨hw, Or.inl ht⟩

/-- The other requirements are not touched by a stage. -/
theorem step_req_ne (I : Input) (st : ConState) {i : ℕ} (hi : i ≠ (Nat.unpair st.stage).1) :
    (step I st).req i = st.req i := by
  change Function.update _ _ _ i = _
  rw [Function.update_of_ne hi]

/-- The scheduled requirement after a stage. -/
theorem step_req_eq (I : Input) (st : ConState) :
    (step I st).req (Nat.unpair st.stage).1 =
      { (stepCore I st).1 with
        lastVisit := st.stage + 1
        lastActed := if (stepCore I st).2.2.2 ||
            pendingHit I (st.req (Nat.unpair st.stage).1) (st.stage + 1) then st.stage + 1
          else (stepCore I st).1.lastActed } := by
  change Function.update _ _ _ _ = _
  rw [Function.update_self]

/-- `stateAt` records the stage. -/
@[simp] theorem stage_stateAt (I : Input) (s : ℕ) : (stateAt I s).stage = s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change (stateAt I s).stage + 1 = s + 1
    rw [ih]

/-- Stage `s + 1` does not change the requirements other than `(Nat.unpair s).1`. -/
theorem rsAt_succ_of_ne (I : Input) {s i : ℕ} (hi : i ≠ (Nat.unpair s).1) :
    rsAt I (s + 1) i = rsAt I s i := by
  change (step I (stateAt I s)).req i = _
  rw [step_req_ne]
  · rfl
  · rwa [stage_stateAt]

/-- **Well-formedness of the run.** -/
theorem reqWF_rsAt (I : Input) : ∀ s i, ReqWF i s (rsAt I s i) := by
  intro s
  induction s with
  | zero =>
    intro i
    refine ⟨rfl, fun bl hbl => ?_, fun pl hpl => ?_, fun c hc => ?_⟩ <;> cases ‹_ = some _›
  | succ s ih =>
    intro i
    by_cases hi : i = (Nat.unpair s).1
    · subst hi
      have hst := stage_stateAt I s
      have hspec := stepCore_spec I (stateAt I s) (by
        rw [hst]
        exact (ih _).mono (Nat.le_succ s))
      rw [hst] at hspec
      have : rsAt I (s + 1) (Nat.unpair s).1 =
          { (stepCore I (stateAt I s)).1 with
            lastVisit := s + 1
            lastActed := if (stepCore I (stateAt I s)).2.2.2 ||
                pendingHit I ((stateAt I s).req (Nat.unpair s).1) (s + 1) then s + 1
              else (stepCore I (stateAt I s)).1.lastActed } := by
        have := step_req_eq I (stateAt I s)
        rw [hst] at this
        exact this
      rw [this]
      exact ⟨hspec.1.tables, hspec.1.baseline, hspec.1.play, hspec.1.floor⟩
    · rw [rsAt_succ_of_ne I hi]
      exact (ih i).mono (Nat.le_succ s)

/-- The scheduled requirement after a stage. -/
theorem rsAt_succ_self (I : Input) (s : ℕ) :
    rsAt I (s + 1) (Nat.unpair s).1 =
      { (stepCore I (stateAt I s)).1 with
        lastVisit := s + 1
        lastActed := if (stepCore I (stateAt I s)).2.2.2 ||
            pendingHit I (rsAt I s (Nat.unpair s).1) (s + 1) then s + 1
          else (stepCore I (stateAt I s)).1.lastActed } := by
  have := step_req_eq I (stateAt I s)
  rw [stage_stateAt] at this
  exact this

/-- If a game is running and still is after a stage, the tables did not change. -/
theorem tables_eq_of_play (I : Input) {s i : ℕ} {pl : Play} (h : (rsAt I s i).play = some pl)
    (h' : ∃ pl', (rsAt I (s + 1) i).play = some pl') :
    (rsAt I (s + 1) i).tables = (rsAt I s i).tables := by
  by_cases hi : i = (Nat.unpair s).1
  · subst hi
    obtain ⟨pl', hpl'⟩ := h'
    rw [rsAt_succ_self] at hpl' ⊢
    change (stepCore I (stateAt I s)).1.play = some pl' at hpl'
    change (stepCore I (stateAt I s)).1.tables = _
    have hw := (reqWF_rsAt I s (Nat.unpair s).1).mono (Nat.le_succ s)
    unfold stepCore at hpl' ⊢
    dsimp only at hpl' ⊢
    rw [stage_stateAt] at hpl' ⊢
    split at hpl'
    · obtain ⟨-, hp, -⟩ := caseOne_spec hw
      rw [hp] at hpl'
      cases hpl'
    · rename_i hreset
      rw [ite_eq_right hreset]
      split at hpl'
      · rfl
      · split at hpl'
        · rename_i hnone
          have : (rsAt I s (Nat.unpair s).1).play = none := hnone
          rw [h] at this
          cases this
        · rename_i pl₀ hp₀
          exact (caseThree_spec hw hp₀).1
  · rw [rsAt_succ_of_ne I hi]

/-- The examined tables grow as initial segments. -/
theorem tables_step (I : Input) (s i : ℕ) :
    (rsAt I (s + 1) i).tables = (rsAt I s i).tables ∨
      ∃ tbl, (rsAt I (s + 1) i).tables = (rsAt I s i).tables ++ [tbl] := by
  by_cases hi : i = (Nat.unpair s).1
  · subst hi
    have hst := stage_stateAt I s
    have hspec := stepCore_spec I (stateAt I s) (by
      rw [hst]
      exact (reqWF_rsAt I s _).mono (Nat.le_succ s))
    rw [hst] at hspec
    have hstep : (rsAt I (s + 1) (Nat.unpair s).1).tables =
        (stepCore I (stateAt I s)).1.tables := by
      have := step_req_eq I (stateAt I s)
      rw [hst] at this
      change ((step I (stateAt I s)).req (Nat.unpair s).1).tables = _
      rw [this]
    rw [hstep]
    rcases hspec.2 with h | ⟨tbl, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨tbl, h⟩
  · rw [rsAt_succ_of_ne I hi]
    exact Or.inl rfl

/-- The examined tables grow as initial segments. -/
theorem tables_prefix (I : Input) {s s' : ℕ} (i : ℕ) (h : s ≤ s') :
    (rsAt I s i).tables <+: (rsAt I s' i).tables := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    rcases tables_step I _ i with h' | ⟨tbl, h'⟩
    · rw [h']
      exact ih
    · rw [h']
      exact ih.trans (List.prefix_append _ _)

/-- A new string in Case 3 comes from a strategy. -/
theorem caseThree_new_string {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState} {pl : Play}
    {j : Fin 3} {τ : Str} (hτ : τ ∈ (caseThree I st i t c rs pl).2.1 j) (hτ' : τ ∉ st.ours j) :
    ∃ g ∈ pl.games, τ ∈ respond pl.arena g (st.positionList I pl.arena t g.board)
      (g.oppLimit - oppSpend I pl.arena pl.start t) (g.ourLimit - g.spent) := by
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
  unfold caseThree at hτ
  dsimp only at hτ
  split_ifs at hτ with hl hE
  · obtain ⟨q, hq, h'⟩ := hfold _ hτ
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hq
    exact ⟨g, hg, h'⟩
  · split at hτ
    · split at hτ
      · exact absurd hτ hτ'
      · exact absurd hτ hτ'
    · exact absurd hτ hτ'
  · split at hτ
    · exact absurd hτ hτ'
    · exact absurd hτ hτ'

/-! ### The verdict of an examination -/

/-- Every set of vectors of length `n` is listed by `subsetsOf n`. -/
theorem mem_subsetsOf {n : ℕ} {S : Finset (List Bool)} (hS : S ⊆ vectors n) :
    S ∈ subsetsOf n := by
  classical
  refine List.mem_map.2 ⟨(allVec n).filter fun z => decide (z ∈ S),
    List.mem_sublists.2 List.filter_sublist, ?_⟩
  ext z
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.1 (hS h), h⟩⟩

/-- A principal verdict: `{σ}` is winning on all boards.  This uses that no split was found, and
determinacy. -/
theorem topOutcome_principal_forces {ar : Arena} {A : Fin 3 → Finset Str} {E : ℕ} {σ : List Bool}
    (h : topOutcome ar A E = .principal σ) (j : Fin 3) : ar.Forces {σ} (A j) E E := by
  have hlen := topOutcome_principal h
  unfold topOutcome at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hsplit
    split at h
    · cases h
    · split at h
      · rename_i σ' hσ'
        cases h
        have h0 : ar.Forces {σ} (A 0) E E := by
          have := List.find?_some hσ'
          exact of_decide_eq_true this
        by_cases hj : j = 0
        · subst hj
          exact h0
        · rcases forces_or_compl (w := ar.w) (Arena.value_mem_vectors ar) {σ} (A j) E with h' | h'
          · exact h'
          · exfalso
            have hmem : ((((0 : Fin 3), j), ({σ} : Finset (List Bool))) :
                (Fin 3 × Fin 3) × Finset (List Bool)) ∈
                (allBoards.product allBoards).product (subsetsOf ar.tables.length) := by
              refine List.pair_mem_product.2 ⟨List.pair_mem_product.2 ⟨?_, ?_⟩, mem_subsetsOf ?_⟩
              · simp [allBoards]
              · fin_cases j <;> simp [allBoards]
              · exact singleton_subset_iff.2 (mem_vectors.2 hlen)
            have hno := List.find?_eq_none.1 hsplit _ hmem
            apply hno
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨⟨fun hj0 => hj hj0.symm, h0⟩, h'⟩
      · cases h

/-- The agreed value of the first part of Case 2 is winning on all boards. -/
theorem examineTop_forces {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState}
    {r : ReqState × List Bool} (hr : examineTop I st i t c rs = .inr r) (j : Fin 3) :
    (arenaOf c rs.tables).Forces {r.2} (st.position I (arenaOf c rs.tables) t j)
      (levelBudget rs.tables 0) (levelBudget rs.tables 0) := by
  unfold examineTop at hr
  dsimp only at hr
  split at hr
  · rename_i bl hbl
    split at hr
    · cases hr
    · split at hr
      · cases hr
      · rename_i hfind
        cases hr
        rcases forces_or_compl (w := (arenaOf c rs.tables).w)
            (Arena.value_mem_vectors (arenaOf c rs.tables)) {bl.σ}
            (st.position I (arenaOf c rs.tables) t j) (levelBudget rs.tables 0) with h' | h'
        · exact h'
        · exfalso
          have hj : j ∈ allBoards := by
            fin_cases j <;> simp [allBoards]
          have hno := List.find?_eq_none.1 hfind j hj
          exact hno (decide_eq_true h')
  · split at hr
    · rename_i σ hσ
      cases hr
      exact topOutcome_principal_forces hσ j
    · split at hr
      · cases hr
      · cases hr

/-- The position restricted to a smaller board is the position on it. -/
theorem position_inter_board (I : Input) (st : ConState) (c : ℕ) (tables more : List TTable)
    (t : ℕ) (j : Fin 3) :
    st.position I (arenaOf c (tables ++ more)) t j ∩ (arenaOf c tables).board =
      st.position I (arenaOf c tables) t j := by
  ext z
  simp only [ConState.position, ConState.positionList, mem_inter, List.mem_toFinset,
    List.mem_filter]
  have hsub : z ∈ (arenaOf c tables).boardList → z ∈ (arenaOf c (tables ++ more)).boardList := by
    intro hz
    have h1 : z ∈ (arenaOf c tables).board := List.mem_toFinset.2 hz
    obtain ⟨tt, ht, hq⟩ := Arena.mem_board.1 h1
    have h2 : z ∈ (arenaOf c (tables ++ more)).board :=
      Arena.mem_board.2 ⟨tt, List.mem_append_left _ ht, hq⟩
    exact List.mem_toFinset.1 h2
  constructor
  · rintro ⟨⟨-, ha⟩, hb⟩
    exact ⟨List.mem_toFinset.1 hb, ha⟩
  · rintro ⟨hb, ha⟩
    exact ⟨⟨hsub hb, ha⟩, List.mem_toFinset.2 hb⟩

/-- A generator of the longer game extends a generator of the shorter one. -/
theorem take_eq_of_forces {c : ℕ} {tables more : List TTable} {A : Finset Str} {σ σ' : List Bool}
    (hσ : σ.length = tables.length) (hσ' : σ'.length = tables.length + more.length)
    (h : (arenaOf c tables).Forces {σ} (A ∩ (arenaOf c tables).board)
      (levelBudget tables 0) (levelBudget tables 0))
    (h' : (arenaOf c (tables ++ more)).Forces {σ'} A
      (levelBudget (tables ++ more) 0) (levelBudget (tables ++ more) 0)) :
    σ'.take tables.length = σ := by
  by_contra hne
  have htake := generator_take hσ' h'
  have hsub : ({σ} : Finset (List Bool)) ⊆ vectors tables.length \ {σ'.take tables.length} := by
    refine singleton_subset_iff.2 (mem_sdiff.2 ⟨mem_vectors.2 hσ, fun hmem => hne ?_⟩)
    exact (mem_singleton.1 hmem).symm
  exact not_forces_and_compl (D := vectors tables.length) htake (Forces.mono h hsub)

/-- **Comparison with `X_t`.**  When Case 2 adds a bit, the old bits of the new agreed value are
those of `X_t`. -/
theorem caseTwo_extension {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState}
    (h : ReqWF i t rs) (hc : rs.c = some c)
    (hgrow : (caseTwo I st i t c rs).1.tables ≠ rs.tables) {bl : Baseline}
    (hbl : (caseTwo I st i t c rs).1.baseline = some bl) :
    xPrefix I t rs.tables.length = bl.σ.take rs.tables.length := by
  obtain ⟨hl, hr⟩ := examineTop_spec (I := I) (st := st) h hc
  unfold caseTwo at hgrow hbl
  dsimp only at hgrow hbl
  split at hgrow
  · rename_i r hex
    exact absurd (hl r hex).1 hgrow
  · rename_i rs₁ σ hex
    obtain ⟨ht, -, -, -, hσ⟩ := hr _ hex
    dsimp only at ht hσ
    have hforces := examineTop_forces hex 0
    dsimp only at hforces
    rw [hex] at hbl
    dsimp only at hbl
    split at hgrow
    · exact absurd ht hgrow
    · rename_i hstack
      rw [hstack] at hbl
      dsimp only at hbl
      split_ifs at hgrow hbl with hx
      · exact absurd ht hgrow
      · split at hgrow
        · exact absurd ht hgrow
        · rename_i tbl htbl
          rw [htbl] at hbl
          dsimp only at hbl
          generalize hv : topOutcome (arenaOf c (rs.tables ++ [tbl]))
            (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
            (levelBudget (rs.tables ++ [tbl]) 0) = v at hgrow hbl
          cases v with
          | principal σ' =>
            dsimp only at hbl
            cases hbl
            have hlen := topOutcome_principal hv
            have hforces' := topOutcome_principal_forces hv 0
            have hx' : σ = xPrefix I t rs.tables.length := not_not.1 hx
            rw [← hx']
            refine (take_eq_of_forces hσ ?_ ?_ hforces').symm
            · simpa [arenaOf] using hlen
            · rw [position_inter_board]
              exact hforces
          | split j k S =>
            dsimp only at hgrow hbl
            split at hgrow
            · rename_i pl hpl
              rw [hpl] at hbl
              cases hbl
            · exact absurd ht hgrow
          | meet S T =>
            dsimp only at hgrow hbl
            split at hgrow
            · rename_i pl hpl
              rw [hpl] at hbl
              cases hbl
            · exact absurd ht hgrow
          | stuck =>
            dsimp only at hgrow hbl
            split at hgrow
            · rename_i pl hpl
              rw [hpl] at hbl
              cases hbl
            · exact absurd ht hgrow

/-- When a stage adds a bit, the old bits of the new agreed value are those of `X_t`. -/
theorem stepCore_extension {I : Input} {st : ConState}
    (h : ReqWF (Nat.unpair st.stage).1 (st.stage + 1) (st.req (Nat.unpair st.stage).1))
    (hgrow : (st.req (Nat.unpair st.stage).1).tables.length < (stepCore I st).1.tables.length)
    {bl : Baseline} (hbl : (stepCore I st).1.baseline = some bl) :
    xPrefix I (st.stage + 1) (st.req (Nat.unpair st.stage).1).tables.length =
      bl.σ.take (st.req (Nat.unpair st.stage).1).tables.length := by
  unfold stepCore at hgrow hbl
  dsimp only at hgrow hbl
  cases hr : mustReset I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2 (st.stage + 1) with
  | true =>
    simp only [hr, ite_true] at hgrow
    rw [(caseOne_spec h).1] at hgrow
    exact absurd hgrow (lt_irrefl _)
  | false =>
    simp only [hr, Bool.false_eq_true, ite_false] at hgrow hbl
    cases hc : (st.req (Nat.unpair st.stage).1).c with
    | none =>
      simp only [hc] at hgrow
      exact absurd hgrow (lt_irrefl _)
    | some c =>
      simp only [hc] at hgrow hbl
      cases hp : (st.req (Nat.unpair st.stage).1).play with
      | none =>
        simp only [hp] at hgrow hbl
        exact caseTwo_extension h hc (fun heq => by
          rw [heq] at hgrow
          exact absurd hgrow (lt_irrefl _)) hbl
      | some pl =>
        simp only [hp] at hgrow
        rw [(caseThree_spec h hp).1] at hgrow
        exact absurd hgrow (lt_irrefl _)

/-- Every requirement has infinitely many stages. -/
theorem exists_stage_ge (i s₀ : ℕ) : ∃ s ≥ s₀, (Nat.unpair s).1 = i := by
  refine ⟨Nat.pair i (s₀ + 1), ?_, by simp⟩
  have := Nat.right_le_pair i (s₀ + 1)
  omega

/-- The strings already compressed stay compressed under Case 3. -/
theorem caseThree_ours_superset (I : Input) (st : ConState) (i t c : ℕ) (rs : ReqState) (pl : Play)
    (j : Fin 3) : st.ours j ⊆ (caseThree I st i t c rs pl).2.1 j := by
  have hfold : ∀ moves : List (BoardGame × Finset Str),
      st.ours j ⊆ moves.foldr (fun q acc => if q.1.board = j then q.2 ∪ acc else acc)
          (st.ours j) := by
    intro moves
    induction moves with
    | nil => exact Subset.refl _
    | cons q moves ih =>
      simp only [List.foldr_cons]
      split_ifs
      · exact ih.trans subset_union_right
      · exact ih
  unfold caseThree
  dsimp only
  split_ifs with h h'
  · exact hfold _
  · split
    · split
      · exact Subset.refl _
      · exact Subset.refl _
    · exact Subset.refl _
  · split <;> exact Subset.refl _

/-- The strings already compressed stay compressed under a stage. -/
theorem step_ours_superset (I : Input) (st : ConState) (j : Fin 3) :
    st.ours j ⊆ (step I st).ours j := by
  change st.ours j ⊆ (stepCore I st).2.1 j
  unfold stepCore
  dsimp only
  split
  · exact Subset.refl _
  · split
    · exact Subset.refl _
    · split
      · exact Subset.refl _
      · exact caseThree_ours_superset I st _ _ _ _ _ j

/-- `oursAt` is monotone. -/
theorem oursAt_mono (I : Input) (j : Fin 3) {s s' : ℕ} (h : s ≤ s') :
    oursAt I j s ⊆ oursAt I j s' := by
  induction h with
  | refl => exact Subset.refl _
  | step _ ih => exact ih.trans (step_ours_superset I _ j)

/-- The last visit is at most the current stage. -/
theorem lastVisit_le (I : Input) (s i : ℕ) : (rsAt I s i).lastVisit ≤ s := by
  induction s with
  | zero => exact le_rfl
  | succ s ih =>
    by_cases hi : i = (Nat.unpair s).1
    · subst hi
      rw [rsAt_succ_self]
    · rw [rsAt_succ_of_ne I hi]
      omega

/-- The last visit is monotone. -/
theorem lastVisit_mono (I : Input) (i : ℕ) {s s' : ℕ} (h : s ≤ s') :
    (rsAt I s i).lastVisit ≤ (rsAt I s' i).lastVisit := by
  induction h with
  | refl => exact le_rfl
  | step hle ih =>
    rename_i s''
    by_cases hi : i = (Nat.unpair s'').1
    · subst hi
      rw [rsAt_succ_self]
      exact ih.trans ((lastVisit_le I s'' _).trans (Nat.le_succ _))
    · rw [rsAt_succ_of_ne I hi]
      exact ih

/-- The last action is monotone. -/
theorem lastVisit_self (I : Input) (s : ℕ) :
    (rsAt I (s + 1) (Nat.unpair s).1).lastVisit = s + 1 := by
  rw [rsAt_succ_self]

/-- The requirement is unchanged while it is not visited. -/
theorem rsAt_const (I : Input) {i s u : ℕ} (hsu : s ≤ u)
    (h : ∀ s'', s ≤ s'' → s'' < u → (Nat.unpair s'').1 ≠ i) : rsAt I u i = rsAt I s i := by
  induction u, hsu using Nat.le_induction with
  | base => rfl
  | succ u hle ih =>
    rw [rsAt_succ_of_ne I (Ne.symm (h u hle (Nat.lt_succ_self u))),
      ih fun s'' h1 h2 => h s'' h1 (by omega)]

/-- A hit is an action of the requirement at its own stage. -/
theorem lastActed_of_hit (I : Input) {s : ℕ}
    (h : pendingHit I (rsAt I s (Nat.unpair s).1) (s + 1) = true) :
    (rsAt I (s + 1) (Nat.unpair s).1).lastActed = s + 1 := by
  rw [rsAt_succ_self]
  simp [h]

/-- Case 2 keeps `c`. -/
theorem caseTwo_c {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState} :
    (caseTwo I st i t c rs).1.c = rs.c := by
  have hex : (∀ r, examineTop I st i t c rs = .inl r → r.1.c = rs.c) ∧
      ∀ r, examineTop I st i t c rs = .inr r → r.1.c = rs.c := by
    constructor
    · intro r hr
      unfold examineTop at hr
      dsimp only at hr
      split at hr
      · split at hr
        · cases hr
          rfl
        · split at hr
          · cases hr
            rfl
          · cases hr
      · split at hr
        · cases hr
        · split at hr
          · cases hr
            rfl
          · cases hr
            rfl
    · intro r hr
      unfold examineTop at hr
      dsimp only at hr
      split at hr
      · split at hr
        · cases hr
        · split at hr
          · cases hr
          · cases hr
            rfl
      · split at hr
        · cases hr
          rfl
        · split at hr
          · cases hr
          · cases hr
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

/-- Case 3 keeps `c`. -/
theorem caseThree_c {I : Input} {st : ConState} {i t c : ℕ} {rs : ReqState} {pl : Play} :
    (caseThree I st i t c rs pl).1.c = rs.c := by
  unfold caseThree
  dsimp only
  split_ifs
  · rfl
  · split
    · split <;> rfl
    · rfl
  · split <;> rfl

/-- Without a reset, a stage keeps `c`. -/
theorem stepCore_c_of_no_reset {I : Input} {st : ConState}
    (h : mustReset I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2 (st.stage + 1) = false) :
    (stepCore I st).1.c = (st.req (Nat.unpair st.stage).1).c := by
  unfold stepCore
  dsimp only
  rw [h]
  simp only [Bool.false_eq_true, ite_false]
  split
  · rfl
  · split
    · exact caseTwo_c
    · exact caseThree_c

/-- After a visit, `c` is defined. -/
theorem c_isSome_after_visit (I : Input) (s : ℕ) :
    (rsAt I (s + 1) (Nat.unpair s).1).c.isSome = true := by
  rw [rsAt_succ_self]
  change (stepCore I (stateAt I s)).1.c.isSome = true
  have hw := (reqWF_rsAt I s (Nat.unpair s).1).mono (Nat.le_succ s)
  cases hr : mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) with
  | true =>
    unfold stepCore
    dsimp only
    rw [stage_stateAt, hr]
    simp only [ite_true]
    rw [(caseOne_spec hw).2.2.2.1]
    rfl
  | false =>
    have hst := stage_stateAt I s
    have hr' : mustReset I (stateAt I s) (Nat.unpair (stateAt I s).stage).1
        (Nat.unpair (stateAt I s).stage).2 ((stateAt I s).stage + 1) = false := by
      rw [hst]
      exact hr
    rw [stepCore_c_of_no_reset hr', hst]
    simp only [mustReset, Bool.or_eq_false_iff] at hr
    have h2 := hr.1.2
    change (rsAt I s (Nat.unpair s).1).c.isNone = false at h2
    cases hc : (rsAt I s (Nat.unpair s).1).c with
    | none =>
      rw [hc] at h2
      cases h2
    | some c =>
      exact (congrArg Option.isSome hc).trans rfl

/-- **Every string we compress has length at least `8`.** -/
theorem length_ge_of_mem_oursAt (I : Input) {j : Fin 3} {s : ℕ} {τ : Str}
    (h : τ ∈ oursAt I j s) : 8 ≤ τ.length := by
  induction s with
  | zero =>
    exact absurd h (by simp [oursAt, stateAt])
  | succ s ih =>
    by_cases hτ : τ ∈ oursAt I j s
    · exact ih hτ
    · change τ ∈ (stepCore I (stateAt I s)).2.1 j at h
      have hτ' : τ ∉ (stateAt I s).ours j := hτ
      unfold stepCore at h
      dsimp only at h
      split at h
      · exact absurd h hτ'
      · split at h
        · exact absurd h hτ'
        · rename_i c hc
          split at h
          · exact absurd h hτ'
          · rename_i pl hp
            obtain ⟨g, hg, hmove⟩ := caseThree_new_string h hτ'
            have hst := stage_stateAt I s
            rw [hst] at hc hp
            have hw := reqWF_rsAt I s (Nat.unpair s).1
            obtain ⟨c', hc', ha, hgl⟩ := hw.play pl hp
            obtain ⟨hsub, hcost⟩ := respond_legal pl.arena g _ _ _
            have hboard : τ ∈ pl.arena.board := by
              have := hsub hmove
              simp only [List.mem_toFinset, ConState.positionList, List.mem_filter] at this
              exact List.mem_toFinset.2 this.1
            have hlen : τ.length ≤ maxLen (rsAt I s (Nat.unpair s).1).tables := by
              refine length_le_maxLen ?_
              have := Arena.mem_board.1 hboard
              rw [ha] at this
              exact this
            have hweight : pl.arena.w τ ≤ cost pl.arena.w (respond pl.arena g _ _ _) :=
              Finset.single_le_sum (f := pl.arena.w) (fun _ _ => Nat.zero_le _) hmove
            have hbudget : pl.arena.w τ ≤ levelBudget (rsAt I s (Nat.unpair s).1).tables 0 :=
              hweight.trans (hcost.trans ((Nat.sub_le _ _).trans (hgl g hg)))
            rw [ha] at hbudget
            have hgt := length_gt_of_weight_le hlen hbudget
            have hfloor := hw.floor c' hc'
            omega

end Kolmogorov.RandomStrings.TTMeet
