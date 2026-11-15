/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Resettling

/-!
# Lemma 4.3 when the number of examined bits is bounded

With boundedly many bits, the board is eventually fixed, the opponent eventually stops moving on it,
and after that a new game cannot be cheated.  Hence (with `ε_i` settled):

* `stopsActing_of_bounded`: `R_i` stops acting;
* `satisfied_of_bounded`: if no game runs forever, then at late visits the stack agrees on a value
  which by the zero game is the final outcome, and no new bit is examined: either the next table
  never converges, or the outcome differs from `X`.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

variable {I : Input}

/-- The examined tables are eventually constant, if bounded. -/
theorem exists_tables_const {i N : ℕ} (hN : ∀ s, (rsAt I s i).tables.length ≤ N) (s₀ : ℕ) :
    ∃ S ≥ s₀, ∀ s ≥ S, (rsAt I s i).tables = (rsAt I S i).tables := by
  obtain ⟨S, hS, h⟩ := exists_stable_of_antitone
    (fun s => Finset.range (N - (rsAt I s i).tables.length)) (fun {t t'} ht => by
      have := (tables_prefix I i ht).length_le
      exact Finset.range_subset_range.2 (by omega)) s₀
  refine ⟨S, hS, fun s hs => ?_⟩
  have h1 := h s hs
  have h2 : N - (rsAt I s i).tables.length = N - (rsAt I S i).tables.length := by
    have := congrArg Finset.card h1
    simpa using this
  have h3 := hN s
  have h4 := hN S
  exact ((tables_prefix I i hs).eq_of_length (by omega)).symm

/-- The opponent is eventually silent on a finite board. -/
theorem exists_opp_silent (hI : I.Valid) (B : Finset Str) (s₀ : ℕ) :
    ∃ S ≥ s₀, ∀ t ≥ S, ∀ τ ∈ B, I.opp t τ = I.opp S τ := by
  classical
  obtain ⟨S, hS, h⟩ := exists_stable_of_antitone (fun t => B.filter fun τ => I.opp t τ = false)
    (fun {t t'} ht τ hτ => by
      obtain ⟨hb, ho⟩ := mem_filter.1 hτ
      refine mem_filter.2 ⟨hb, ?_⟩
      cases ho' : I.opp t τ with
      | false => rfl
      | true =>
        have := hI.opp_mono ht ho'
        rw [ho] at this
        cases this) s₀
  refine ⟨S, hS, fun t ht τ hτ => ?_⟩
  have h1 := h t ht
  have h2 : (I.opp t τ = false) ↔ (I.opp S τ = false) := by
    have ha := Finset.ext_iff.1 h1 τ
    simp only [mem_filter, hτ, true_and] at ha
    exact ha
  cases ht' : I.opp t τ <;> cases hS' : I.opp S τ <;> simp_all

/-- A silent opponent spends nothing. -/
theorem oppSpend_eq_zero {ar : Arena} {S t₀ t : ℕ}
    (hsilent : ∀ t ≥ S, ∀ τ ∈ ar.board, I.opp t τ = I.opp S τ) (ht₀ : S ≤ t₀) (ht : t₀ ≤ t) :
    oppSpend I ar t₀ t = 0 := by
  unfold oppSpend
  have : ar.board.filter (fun τ => I.opp t τ && !(I.opp t₀ τ)) = ∅ := by
    refine filter_eq_empty_iff.2 fun τ hτ => ?_
    rw [hsilent t (ht₀.trans ht) τ hτ, hsilent t₀ ht₀ τ hτ]
    cases I.opp S τ <;> simp
  rw [this]
  rfl

/-- A hit is impossible with the opponent silent. -/
theorem pendingHit_false {rs : ReqState} {S t : ℕ}
    (hsilent : ∀ t ≥ S, ∀ τ ∈ boardOf rs.tables, I.opp t τ = I.opp S τ) (hv : S ≤ rs.lastVisit)
    (ht : rs.lastVisit ≤ t) : pendingHit I rs t = false := by
  rw [pendingHit, decide_eq_false_iff_not, not_nonempty_iff_eq_empty]
  refine filter_eq_empty_iff.2 fun τ hτ => ?_
  rw [hsilent t (hv.trans ht) τ hτ, hsilent rs.lastVisit hv τ hτ]
  cases I.opp S τ <;> simp

/-- A play started when the opponent is silent runs forever. -/
theorem permanent_of_quiet {i s₀ s₃ c S : ℕ} {pl : Play} {T : List TTable} (hno : NoReset I i s₀)
    (hs : s₀ ≤ s₃) (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c) (hSs : S ≤ s₃)
    (hT : ∀ s ≥ S, (rsAt I s i).tables = T)
    (hsilent : ∀ t ≥ S, ∀ τ ∈ (arenaOf c T).board, I.opp t τ = I.opp S τ)
    (hp : (rsAt I s₃ i).play = some pl) (hstart : S ≤ pl.start) (hstart' : pl.start ≤ s₃) :
    Permanent I i := by
  refine permanent_of_limit hno hs hc hp fun s hle _ pl' h1 h2 h3 _ => ?_
  have ha := arena_of_play (hc s (hs.trans hle)) h1
  rw [hT s (hSs.trans hle)] at ha
  rw [ha, h2, oppSpend_eq_zero hsilent hstart (by omega)]
  exact Nat.zero_le _

/-- A play started in Case 2 starts now. -/
theorem caseTwo_play_start {st : ConState} {i t c : ℕ} {rs : ReqState} (hw : ReqWF i t rs)
    (hc : rs.c = some c) (hnp : rs.play = none) {pl : Play}
    (h : (caseTwo I st i t c rs).1.play = some pl) : pl.start = t := by
  obtain ⟨-, hspec⟩ := examineTop_spec (I := I) (st := st) hw hc
  unfold caseTwo at h
  dsimp only at h
  split at h
  · rename_i r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · split at hr
      · cases hr
        rw [hnp] at h
        cases h
      · split at hr
        · cases hr
          cases h
          rfl
        · cases hr
    · split at hr
      · cases hr
      · split at hr
        · rename_i pl' hpl'
          cases hr
          cases h
          exact (balancedPlay_inv hpl').1
        · cases hr
          rw [hnp] at h
          cases h
  · rename_i rs₁ σ hex
    obtain ⟨-, -, hp₁, -, -⟩ := hspec _ hex
    dsimp only at hp₁
    have hp₁' : rs₁.play = none := hp₁.trans hnp
    split at h
    · cases h
      rfl
    · split at h
      · rw [hp₁'] at h
        cases h
      · split at h
        · rw [hp₁'] at h
          cases h
        · rename_i tbl htbl
          generalize hv : topOutcome (arenaOf c (rs.tables ++ [tbl]))
            (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
            (levelBudget (rs.tables ++ [tbl]) 0) = v at h
          cases v with
          | principal σ' =>
            rw [show _ = rs₁.play from rfl, hp₁'] at h
            cases h
          | split j k S =>
            dsimp only at h
            split at h
            · rename_i pl' hpl'
              rw [← hv] at hpl'
              cases h
              exact (balancedPlay_inv hpl').1
            · rw [hp₁'] at h
              cases h
          | meet S T =>
            dsimp only at h
            split at h
            · rename_i pl' hpl'
              rw [← hv] at hpl'
              cases h
              exact (balancedPlay_inv hpl').1
            · rw [hp₁'] at h
              cases h
          | stuck => exact absurd hv (topOutcome_ne_stuck _ _ _)

/-- A visit in Case 2 that starts no game and adds no table: the agreement is dropped, or the stack
agrees and no new bit can be examined. -/
theorem caseTwo_quiet_visit {st : ConState} {i t c : ℕ} {rs : ReqState} (hw : ReqWF i t rs)
    (hc : rs.c = some c)
    (hplay : (caseTwo I st i t c rs).1.play = none)
    (htab : (caseTwo I st i t c rs).1.tables = rs.tables) :
    ((caseTwo I st i t c rs).1.baseline = none ∧ rs.baseline ≠ none ∧
        (caseTwo I st i t c rs).2 = false) ∨
      ∃ r, examineTop I st i t c rs = .inr r ∧
        firstStackSplit (arenaOf c rs.tables) (st.position I (arenaOf c rs.tables) t) r.2 = none ∧
        (caseTwo I st i t c rs).2 = false ∧
        ¬ (r.2 = xPrefix I t rs.tables.length ∧ ∃ tbl, tableAt i rs.tables.length t =
            some tbl) := by
  obtain ⟨-, hspec⟩ := examineTop_spec (I := I) (st := st) hw hc
  unfold caseTwo at hplay htab ⊢
  dsimp only at hplay htab ⊢
  split at hplay
  · rename_i r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · rename_i bl hbl
      have hne : rs.baseline ≠ none := by rw [hbl]; simp
      split at hr
      · cases hr
        exact Or.inl ⟨rfl, hne, rfl⟩
      · split at hr
        · cases hr
          cases hplay
        · cases hr
    · split at hr
      · cases hr
      · rename_i hnot
        split at hr
        · cases hr
          cases hplay
        · rename_i hb
          exfalso
          generalize hv : topOutcome (arenaOf c rs.tables)
            (st.position I (arenaOf c rs.tables) t) (levelBudget rs.tables 0) = v at hnot hb
          cases v with
          | principal σ => exact hnot σ rfl
          | split j k S => simp [balancedPlay] at hb
          | meet S T => simp [balancedPlay] at hb
          | stuck => exact topOutcome_ne_stuck _ _ _ hv
  · rename_i rs₁ σ hex
    refine Or.inr ⟨(rs₁, σ), hex, ?_⟩
    obtain ⟨ht, -, -, -, -⟩ := hspec _ hex
    dsimp only at ht
    rw [hex] at htab
    dsimp only at htab
    split at hplay
    · cases hplay
    · rename_i hstack
      rw [hstack] at htab
      dsimp only at htab
      refine ⟨hstack, ?_⟩
      split_ifs at hplay htab ⊢ with hx
      · exact ⟨rfl, fun h => hx h.1⟩
      · have hx' : σ = xPrefix I t rs.tables.length := not_not.1 hx
        split at hplay
        · rename_i htbl
          refine ⟨rfl, fun h => ?_⟩
          obtain ⟨-, tbl, h'⟩ := h
          rw [htbl] at h'
          cases h'
        · rename_i tbl htbl
          exfalso
          rw [htbl] at htab
          dsimp only at htab
          generalize hv : topOutcome (arenaOf c (rs.tables ++ [tbl]))
            (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
            (levelBudget (rs.tables ++ [tbl]) 0) = v at hplay htab
          cases v with
          | principal σ' =>
            have := congrArg List.length htab
            simp at this
          | split j k S =>
            dsimp only at hplay
            split at hplay
            · cases hplay
            · rename_i hb
              simp [balancedPlay] at hb
          | meet S T =>
            dsimp only at hplay
            split at hplay
            · cases hplay
            · rename_i hb
              simp [balancedPlay] at hb
          | stuck => exact topOutcome_ne_stuck _ _ _ hv

/-- The tables of the enumeration, by index. -/
theorem tablesUpTo_getElem {i s n : ℕ} {l : List TTable} (h : tablesUpTo i s n = some l) :
    l.length = n ∧ ∀ k (hk : k < l.length), tableAt i k s = some l[k] := by
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
    obtain ⟨l', hl', tt, ht, rfl⟩ := h
    obtain ⟨hlen, hget⟩ := ih hl'
    refine ⟨by simp [hlen], fun k hk => ?_⟩
    rcases Nat.lt_or_ge k l'.length with hlt | hge
    · rw [List.getElem_append_left hlt]
      exact hget k hlt
    · have hk' : k = n := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst hk'
      rw [List.getElem_append_right hge]
      simp [hlen, ht]

/-- Between two stages a position before the move lies between the two stable values. -/
theorem position_before_move (hI : I.Valid) {ar : Arena} {s s₁ : ℕ} {j : Fin 3} (hs : s₁ ≤ s)
    (hstable : ∀ t ≥ s₁, (stateAt I t).position I ar t j = (stateAt I s₁).position I ar s₁ j) :
    (stateAt I s).position I ar (s + 1) j = (stateAt I s₁).position I ar s₁ j := by
  refine Finset.Subset.antisymm ?_ ?_
  · rw [← hstable s hs]
    intro z hz
    obtain ⟨hb, ho, hn⟩ := mem_position.1 hz
    refine mem_position.2 ⟨hb, ?_, hn⟩
    cases ho' : I.opp s z with
    | false => rfl
    | true =>
      have := hI.opp_mono (Nat.le_succ s) ho'
      rw [ho] at this
      cases this
  · rw [← hstable (s + 1) (by omega)]
    intro z hz
    obtain ⟨hb, ho, hn⟩ := mem_position.1 hz
    exact mem_position.2 ⟨hb, ho, fun hmem => hn (oursAt_mono I j (Nat.le_succ s) hmem)⟩

/-- If no game runs forever and the opponent is silent, there is eventually no play at all. -/
theorem eventually_no_play {i s₀ c S : ℕ} {T : List TTable} (hno : NoReset I i s₀)
    (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c) (hS : s₀ ≤ S) (hT : ∀ s ≥ S, (rsAt I s i).tables = T)
    (hsilent : ∀ t ≥ S, ∀ τ ∈ (arenaOf c T).board, I.opp t τ = I.opp S τ)
    (hnp : ¬ Permanent I i) : ∃ s₅ ≥ S, ∀ s ≥ s₅, (rsAt I s i).play = none := by
  have hnone : ∃ s ≥ S, (rsAt I s i).play = none := by
    cases hp : (rsAt I S i).play with
    | none => exact ⟨S, le_rfl, hp⟩
    | some pl =>
      obtain ⟨s', hs', hn, -⟩ := exists_no_play hno hS hc hp hnp
      exact ⟨s', hs', hn⟩
  obtain ⟨s₅, hs₅, hp₅⟩ := hnone
  refine ⟨s₅, hs₅, fun s hs => ?_⟩
  induction s, hs using Nat.le_induction with
  | base => exact hp₅
  | succ s hle ih =>
    by_cases hi : i = (Nat.unpair s).1
    · subst hi
      have hs₀ := hS.trans (hs₅.trans hle)
      have hst := stage_stateAt I s
      have hcs := hc s hs₀
      have hcore := stepCore_eq_two (I := I) (st := stateAt I s) (c := c)
        (by rw [hst]; exact hno s hs₀ rfl) (by rw [hst]; exact hcs) (by rw [hst]; exact ih)
      rw [hst] at hcore
      have hf1 : (rsAt I (s + 1) (Nat.unpair s).1).play = (stepCore I (stateAt I s)).1.play := by
        rw [rsAt_succ_self]
      rw [hf1, hcore]
      dsimp only
      cases hcase : (caseTwo I (stateAt I s) (Nat.unpair s).1 (s + 1) c
          (rsAt I s (Nat.unpair s).1)).1.play with
      | none => exact hcase
      | some pl =>
        exfalso
        have hw := (reqWF_rsAt I s (Nat.unpair s).1).mono (Nat.le_succ s)
        have hstart := caseTwo_play_start hw hcs ih hcase
        refine hnp (permanent_of_quiet hno (show s₀ ≤ s + 1 by omega) hc
          (show S ≤ s + 1 by have := hs₅.trans hle; omega)
          hT hsilent (pl := pl) ?_ ?_ ?_)
        · rw [hf1, hcore]
          exact hcase
        · rw [hstart]
          have := hs₅.trans hle
          omega
        · rw [hstart]
    · rw [rsAt_succ_of_ne I hi]
      exact ih

/-- **Lemma 4.3, stopping.**  With boundedly many bits, the board is eventually fixed, the opponent
eventually stops moving on it, and then a new game cannot be cheated.  So `R_i` stops acting. -/
theorem stopsActing_of_bounded (hI : I.Valid) {i s₀ c N : ℕ} (hno : NoReset I i s₀)
    (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c) (hN : ∀ s, (rsAt I s i).tables.length ≤ N) :
    StopsActing I i := by
  obtain ⟨S₁, hS₁, hT₁⟩ := exists_tables_const hN s₀
  set T := (rsAt I S₁ i).tables with hTdef
  obtain ⟨S, hS, hsil⟩ := exists_opp_silent hI (arenaOf c T).board S₁
  have hs₀S : s₀ ≤ S := hS₁.trans hS
  have hT : ∀ s ≥ S, (rsAt I s i).tables = T := fun s hs => hT₁ s (hS.trans hs)
  -- It suffices that from some visit on, no visit is an action.
  suffices hlate : ∃ V ≥ S, ∀ s ≥ V, (Nat.unpair s).1 = i →
      (stepCore I (stateAt I s)).2.2.2 = false by
    obtain ⟨V, hVS, hV⟩ := hlate
    obtain ⟨v, hv, hvi, -⟩ := exists_next_visit I i V
    refine ⟨v + 1, fun s => ?_⟩
    rcases Nat.lt_or_ge s (v + 1) with hlt | hge
    · exact (lastActed_le I s i).trans hlt.le
    · induction s, hge using Nat.le_induction with
      | base => exact lastActed_le I _ i
      | succ s hle ih =>
        by_cases hi : i = (Nat.unpair s).1
        · subst hi
          rw [rsAt_succ_self]
          have hfalse := hV s (by omega) rfl
          have hvis : S ≤ (rsAt I s (Nat.unpair s).1).lastVisit := by
            have h1 := lastVisit_mono I (Nat.unpair s).1 hle
            have h2 := lastVisit_self I v
            rw [hvi] at h2
            rw [h2] at h1
            omega
          have hhit : pendingHit I (rsAt I s (Nat.unpair s).1) (s + 1) = false := by
            refine pendingHit_false (S := S) (fun t ht τ hτ => hsil t ht τ ?_) hvis
              ((lastVisit_le I s _).trans (Nat.le_succ s))
            rw [hT s (by omega)] at hτ
            exact mem_boardOf_iff.1 hτ
          simp only [hfalse, hhit, Bool.or_false, Bool.false_eq_true, ite_false]
          have hf := (stepCore_frozen I (stateAt I s)).1
          rw [stage_stateAt] at hf
          rw [hf]
          exact ih
        · rw [rsAt_succ_of_ne I hi]
          exact ih
  by_cases hperm : Permanent I i
  · -- A game runs forever: its moves stop.
    obtain ⟨s_p, start, hp⟩ := hperm
    obtain ⟨V, hV, hstable⟩ := exists_stable_position hI (arenaOf c T) (max S s_p)
    have hVS : S ≤ V := (le_max_left _ _).trans hV
    have hVp : s_p ≤ V := (le_max_right _ _).trans hV
    refine ⟨V, hVS, fun s hs hsi => ?_⟩
    subst hsi
    obtain ⟨pl, hpl, hst⟩ := hp s (by omega)
    obtain ⟨pl', hpl', hst'⟩ := hp (s + 1) (by omega)
    obtain ⟨hres, hl⟩ := visit_of_permanent hI hpl hpl' (by rw [hst, hst'])
    have hcs := hc s (by omega)
    have ha := arena_of_play hcs hpl
    rw [hT s (by omega)] at ha
    have hstable' : ∀ t ≥ V, ∀ j, (stateAt I t).position I pl.arena t j =
        (stateAt I V).position I pl.arena V j := by
      rw [ha]
      exact hstable
    have hst₀ := stage_stateAt I s
    have hcore := stepCore_eq_three (I := I) (st := stateAt I s) (c := c) (pl := pl)
      (by rw [hst₀]; exact hres) (by rw [hst₀]; exact hcs) (by rw [hst₀]; exact hpl)
    rw [hst₀] at hcore
    rw [hcore]
    dsimp only
    unfold caseThree
    dsimp only
    rw [ite_eq_left hl]
    dsimp only
    rw [List.any_eq_false]
    intro q hq
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hq
    have hem := (target_of_stable hI hs hstable' hres hpl hl hg).1
    dsimp only
    rw [hem]
    simp
  · -- No game runs forever: there is eventually no play, and no action.
    obtain ⟨s₅, hs₅, hnone⟩ := eventually_no_play hno hc hs₀S hT hsil hperm
    refine ⟨s₅, hs₅, fun s hs hsi => ?_⟩
    subst hsi
    have hs₀' : s₀ ≤ s := hs₀S.trans (hs₅.trans hs)
    have hcs := hc s hs₀'
    have hst₀ := stage_stateAt I s
    have hcore := stepCore_eq_two (I := I) (st := stateAt I s) (c := c)
      (by rw [hst₀]; exact hno s hs₀' rfl) (by rw [hst₀]; exact hcs)
      (by rw [hst₀]; exact hnone s hs)
    rw [hst₀] at hcore
    rw [hcore]
    dsimp only
    have hw := (reqWF_rsAt I s (Nat.unpair s).1).mono (Nat.le_succ s)
    have hf1 : (rsAt I (s + 1) (Nat.unpair s).1).play = (stepCore I (stateAt I s)).1.play := by
      rw [rsAt_succ_self]
    have hf2 : (rsAt I (s + 1) (Nat.unpair s).1).tables = (stepCore I (stateAt I s)).1.tables := by
      rw [rsAt_succ_self]
    have hplay := hnone (s + 1) (by omega)
    rw [hf1, hcore] at hplay
    have htab : (caseTwo I (stateAt I s) (Nat.unpair s).1 (s + 1) c
        (rsAt I s (Nat.unpair s).1)).1.tables = (rsAt I s (Nat.unpair s).1).tables := by
      have h1 := hT (s + 1) (by have := hs₅.trans hs; omega)
      rw [hf2, hcore] at h1
      rw [hT s (hs₅.trans hs)]
      exact h1
    rcases caseTwo_quiet_visit hw hcs hplay htab with ⟨-, -, h⟩ | ⟨r, -, -, h, -⟩
    · exact h
    · exact h

/-- **Lemma 4.3, satisfaction.**  With boundedly many bits and no game running forever, at late
visits all levels of the stack agree on `σ`, which by the zero game is the current outcome on every
board, hence the final outcome.  Since no new bit is examined, either the next table never converges
(`Ψ_i` is not total) or `X_t ↾ n ≠ σ` at late `t`, hence `X ↾ n ≠ σ`. -/
theorem satisfied_of_bounded (hI : I.Valid) {X : Set Str} (hX : Approximates I X) {i s₀ c N : ℕ}
    (hno : NoReset I i s₀) (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c)
    (hN : ∀ s, (rsAt I s i).tables.length ≤ N) (hnp : ¬ Permanent I i) :
    ¬ IsTotalGen i ∨ ∃ k s t j,
        tableAt i k s = some t ∧ ¬ (strOf k ∈ X ↔ t.Accepts (finalR I j)) := by
  classical
  by_cases htot : IsTotalGen i
  swap
  · exact Or.inl htot
  refine Or.inr ?_
  obtain ⟨S₁, hS₁, hT₁⟩ := exists_tables_const hN s₀
  set T := (rsAt I S₁ i).tables with hTdef
  obtain ⟨S, hS, hsil⟩ := exists_opp_silent hI (arenaOf c T).board S₁
  have hs₀S : s₀ ≤ S := hS₁.trans hS
  have hT : ∀ s ≥ S, (rsAt I s i).tables = T := fun s hs => hT₁ s (hS.trans hs)
  obtain ⟨s₅, hs₅, hnone⟩ := eventually_no_play hno hc hs₀S hT hsil hnp
  obtain ⟨s₆, hs₆, hstable⟩ := exists_stable_position hI (arenaOf c T) s₅
  -- The next table, and the approximation of `X` on the bits below it.
  obtain ⟨s_n, t_n, htn⟩ := htot T.length
  have hXall : ∀ n : ℕ, ∃ s_x, ∀ s ≥ s_x, ∀ k < n, (I.X s (strOf k) = true ↔ strOf k ∈ X) := by
    intro n
    induction n with
    | zero => exact ⟨0, fun _ _ k hk => absurd hk (by omega)⟩
    | succ n ih =>
      obtain ⟨s_a, ha⟩ := ih
      obtain ⟨s_b, hb⟩ := hX (strOf n)
      refine ⟨max s_a s_b, fun s hs k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hlt | rfl
      · exact ha s ((le_max_left _ _).trans hs) k hlt
      · exact hb s ((le_max_right _ _).trans hs)
  obtain ⟨s_x, hs_x⟩ := hXall T.length
  set L := max s₆ (max s_n s_x) with hL
  have hL₆ : s₆ ≤ L := le_max_left _ _
  have hLn : s_n ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLx : s_x ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  -- The analysis of a late visit.
  have hvisit : ∀ v ≥ L, (Nat.unpair v).1 = i →
      ((rsAt I (v + 1) i).baseline = none ∧ (rsAt I v i).baseline ≠ none) ∨
        ∃ r, examineTop I (stateAt I v) i (v + 1) c (rsAt I v i) = .inr r ∧
          firstStackSplit (arenaOf c (rsAt I v i).tables)
            ((stateAt I v).position I (arenaOf c (rsAt I v i).tables) (v + 1)) r.2 = none ∧
          ¬ (r.2 = xPrefix I (v + 1) (rsAt I v i).tables.length ∧
            ∃ tbl, tableAt i (rsAt I v i).tables.length (v + 1) = some tbl) := by
    intro v hv hvi
    subst hvi
    have hSv : S ≤ v := (hs₅.trans hs₆).trans (hL₆.trans hv)
    have hs₀v : s₀ ≤ v := hs₀S.trans hSv
    have hcs := hc v hs₀v
    have hst₀ := stage_stateAt I v
    have hnonev : (rsAt I v (Nat.unpair v).1).play = none := hnone v (hs₆.trans (hL₆.trans hv))
    have hcore := stepCore_eq_two (I := I) (st := stateAt I v) (c := c)
      (by rw [hst₀]; exact hno v hs₀v rfl) (by rw [hst₀]; exact hcs) (by rw [hst₀]; exact hnonev)
    rw [hst₀] at hcore
    have hw := (reqWF_rsAt I v (Nat.unpair v).1).mono (Nat.le_succ v)
    have hf1 : (rsAt I (v + 1) (Nat.unpair v).1).play = (stepCore I (stateAt I v)).1.play := by
      rw [rsAt_succ_self]
    have hf2 : (rsAt I (v + 1) (Nat.unpair v).1).tables = (stepCore I (stateAt I v)).1.tables := by
      rw [rsAt_succ_self]
    have hf3 : (rsAt I (v + 1) (Nat.unpair v).1).baseline =
        (stepCore I (stateAt I v)).1.baseline := by
      rw [rsAt_succ_self]
    have hplay := hnone (v + 1) (by have := hs₆.trans (hL₆.trans hv); omega)
    rw [hf1, hcore] at hplay
    have htab : (caseTwo I (stateAt I v) (Nat.unpair v).1 (v + 1) c
        (rsAt I v (Nat.unpair v).1)).1.tables = (rsAt I v (Nat.unpair v).1).tables := by
      have h1 := hT (v + 1) (by omega)
      rw [hf2, hcore] at h1
      rw [hT v hSv]
      exact h1
    rcases caseTwo_quiet_visit hw hcs hplay htab with ⟨h1, h2, -⟩ | ⟨r, h1, h2, -, h3⟩
    · refine Or.inl ⟨?_, h2⟩
      rw [hf3, hcore]
      exact h1
    · exact Or.inr ⟨r, h1, h2, h3⟩
  -- A late visit where the examination succeeds.
  have hgood : ∃ v ≥ L, (Nat.unpair v).1 = i ∧
      ∃ r, examineTop I (stateAt I v) i (v + 1) c (rsAt I v i) = .inr r ∧
        firstStackSplit (arenaOf c (rsAt I v i).tables)
          ((stateAt I v).position I (arenaOf c (rsAt I v i).tables) (v + 1)) r.2 = none ∧
        ¬ (r.2 = xPrefix I (v + 1) (rsAt I v i).tables.length ∧
          ∃ tbl, tableAt i (rsAt I v i).tables.length (v + 1) = some tbl) := by
    obtain ⟨v, hv, hvi, -⟩ := exists_next_visit I i L
    rcases hvisit v hv hvi with ⟨hb, -⟩ | h
    · obtain ⟨v', hv', hvi', hsame⟩ := exists_next_visit I i (v + 1)
      rcases hvisit v' (by omega) hvi' with ⟨-, hb'⟩ | h'
      · exact absurd (by rw [hsame]; exact hb) hb'
      · exact ⟨v', by omega, hvi', h'⟩
    · exact ⟨v, hv, hvi, h⟩
  obtain ⟨v, hv, hvi, r, hex, hstack, hnotX⟩ := hgood
  have hSv : S ≤ v := (hs₅.trans hs₆).trans (hL₆.trans hv)
  have htabv := hT v hSv
  rw [htabv] at hstack hnotX
  have hf : ∀ j, (arenaOf c T).Forces {r.2} ((stateAt I v).position I (arenaOf c T) (v + 1) j)
      (levelBudget T 0) (levelBudget T 0) := by
    intro j
    have := examineTop_forces hex j
    rwa [htabv] at this
  -- By the zero game, the agreed value is the current outcome.
  have hzero : ∀ j, (arenaOf c T).value ((stateAt I v).position I (arenaOf c T) (v + 1) j) =
      r.2 := by
    intro j
    refine (forces_zero_level (fun z hz => (mem_position.1 hz).1)).1 ?_
    rcases Nat.eq_zero_or_pos (maxLen T) with h0 | hpos
    · rw [h0]
      exact hf j
    · have := firstStackSplit_none hstack j (r := maxLen T - 1) (by
        change maxLen T - 1 < maxLen T
        omega)
      rw [show maxLen T - 1 + 1 = maxLen T by omega] at this
      exact this
  have hstab0 : ∀ t ≥ s₆, (stateAt I t).position I (arenaOf c T) t 0 =
      (stateAt I s₆).position I (arenaOf c T) s₆ 0 := fun t ht => hstable t ht 0
  have hposv : (stateAt I v).position I (arenaOf c T) (v + 1) 0 =
      (stateAt I s₆).position I (arenaOf c T) s₆ 0 :=
    position_before_move hI (hL₆.trans hv) hstab0
  have hσ : r.2 = (arenaOf c T).value ((stateAt I s₆).position I (arenaOf c T) s₆ 0) := by
    rw [← hposv]
    exact (hzero 0).symm
  -- The next table has converged, so the agreed value differs from `X_t`.
  have htn' : tableAt i T.length (v + 1) = some t_n :=
    tableAt_mono (show s_n ≤ v + 1 by have := hLn.trans hv; omega) htn
  have hne : r.2 ≠ xPrefix I (v + 1) T.length := fun h => hnotX ⟨h, t_n, htn'⟩
  -- A bit where they differ.
  have hgetall := tablesUpTo_getElem (tables_spec I v i)
  rw [htabv] at hgetall
  obtain ⟨-, hget⟩ := hgetall
  have hexk : ∃ k, ∃ hk : k < T.length,
      ¬ (I.X (v + 1) (strOf k) = T[k].evalB (chi (finalR I 0))) := by
    by_contra hall
    apply hne
    rw [hσ]
    have hvalue : (arenaOf c T).value ((stateAt I s₆).position I (arenaOf c T) s₆ 0) =
        T.map fun t => t.evalB fun z =>
          decide (z ∈ (stateAt I s₆).position I (arenaOf c T) s₆ 0) := rfl
    rw [hvalue]
    apply List.ext_getElem
    · simp [xPrefix]
    · intro k h1 h2
      have hk : k < T.length := by simpa [xPrefix] using h2
      have hval := value_stable_eq hI hstab0 (tt := T[k]) (List.getElem_mem hk)
      simp only [xPrefix, List.getElem_map, List.getElem_range]
      rw [hval]
      by_contra hbad
      exact hall ⟨k, hk, fun heq => hbad heq.symm⟩
  obtain ⟨k, hk, hdiff⟩ := hexk
  refine ⟨k, v, T[k], 0, hget k hk, fun hiff => hdiff ?_⟩
  have hxk := hs_x (v + 1) (by have := hLx.trans hv; omega) k hk
  rw [Bool.eq_iff_iff, hxk, hiff]
  rfl

end Kolmogorov.RandomStrings.TTMeet
