/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.LatePlay
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-!
# Resettling agreement, and the stability of the agreed value (Lemma 4.3)

The opponent's spending is summable, so from some stage on it is at most `ε_i` (`opp_tail`,
`oppSpend_le_of_tail`).  After such a stage:

* a balanced game cannot be cheated, so it runs forever (`permanent_of_balanced`);
* `exists_protected_or_permanent`: either a game runs forever, or all three boards get based after
  the stage, because at most two games started before the stage can be in the way;
* `agreed_nested`: **if no game runs forever, an agreed value is never dropped and only grows.**
  This is the step that the printed Case 2 does not support (`ParityExample.lean`).
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

variable {I : Input}

/-- Finitely many strings compressed by the opponent are compressed at one stage. -/
theorem exists_stage_all_opp (hI : I.Valid) (S : Finset Str) (hS : ∀ τ ∈ S, ∃ s, I.opp s τ = true) :
    ∃ s₁, ∀ τ ∈ S, I.opp s₁ τ = true := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S _ ih =>
    obtain ⟨s, hs⟩ := ih fun τ hτ => hS τ (mem_insert_of_mem hτ)
    obtain ⟨s', hs'⟩ := hS a (mem_insert_self a S)
    refine ⟨max s s', fun τ hτ => ?_⟩
    rcases mem_insert.1 hτ with rfl | h
    · exact hI.opp_mono (le_max_right _ _) hs'
    · exact hI.opp_mono (le_max_left _ _) (hs τ h)

/-- The opponent's tail: from some stage on the opponent spends less than `δ`. -/
theorem opp_tail (hI : I.Valid) {δ : ℚ} (hδ : 0 < δ) :
    ∃ s₁, ∀ S : Finset Str, (∀ τ ∈ S, (∃ s, I.opp s τ = true) ∧ I.opp s₁ τ = false) →
      trueCost S ≤ δ := by
  classical
  by_contra hcon
  have hstep : ∀ s₁, ∃ S : Finset Str, (∀ τ ∈ S, (∃ s, I.opp s τ = true) ∧ I.opp s₁ τ = false) ∧
      δ < trueCost S := by
    intro s₁
    by_contra hno
    exact hcon ⟨s₁, fun S hS => not_lt.1 fun hlt => hno ⟨S, hS, hlt⟩⟩
  have hgrow : ∀ n : ℕ, ∃ S : Finset Str, (∀ τ ∈ S, ∃ s, I.opp s τ = true) ∧
      (n : ℚ) * δ ≤ trueCost S := by
    intro n
    induction n with
    | zero => exact ⟨∅, by simp, by simp [trueCost]⟩
    | succ n ih =>
      obtain ⟨S, hS, hc⟩ := ih
      obtain ⟨s₁, hs₁⟩ := exists_stage_all_opp hI S hS
      obtain ⟨S', hS', hc'⟩ := hstep s₁
      refine ⟨S ∪ S', ?_, ?_⟩
      · intro τ hτ
        rcases mem_union.1 hτ with h | h
        · exact hS τ h
        · exact (hS' τ h).1
      · have hdisj : Disjoint S S' := by
          refine disjoint_left.2 fun τ h h' => ?_
          have h1 := hs₁ τ h
          have h2 := (hS' τ h').2
          simp [h1] at h2
        have : trueCost (S ∪ S') = trueCost S + trueCost S' := sum_union hdisj
        rw [this]
        push_cast
        linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 / 32) / δ)
  obtain ⟨S, hS, hc⟩ := hgrow n
  have h1 := hI.opp_budget S hS
  rw [div_lt_iff₀ hδ] at hn
  linarith

/-- The tail bound is monotone in the stage. -/
theorem tail_mono (hI : I.Valid) {δ : ℚ} {s₁ s₁' : ℕ} (hs : s₁ ≤ s₁')
    (h : ∀ S : Finset Str, (∀ τ ∈ S, (∃ s, I.opp s τ = true) ∧ I.opp s₁ τ = false) →
      trueCost S ≤ δ) :
    ∀ S : Finset Str, (∀ τ ∈ S, (∃ s, I.opp s τ = true) ∧ I.opp s₁' τ = false) →
      trueCost S ≤ δ := by
  intro S hS
  refine h S fun τ hτ => ⟨(hS τ hτ).1, ?_⟩
  cases ho : I.opp s₁ τ with
  | false => rfl
  | true =>
    have := hI.opp_mono hs ho
    rw [(hS τ hτ).2] at this
    cases this

/-- Units and true measure on a board. -/
theorem cost_eq_trueCost {c : ℕ} {tables : List TTable} {S : Finset Str}
    (hS : S ⊆ (arenaOf c tables).board) :
    ((cost (arenaOf c tables).w S : ℕ) : ℚ) = trueCost S * 2 ^ (c + maxLen tables + 1) := by
  unfold cost trueCost
  push_cast
  rw [Finset.sum_mul]
  refine sum_congr rfl fun τ hτ => ?_
  have hlen : τ.length ≤ maxLen tables := length_le_maxLen (Arena.mem_board.1 (hS hτ))
  exact unitWeight_eq_realCost (N := c + maxLen tables + 1) (by omega)

/-- **After the tail stage the opponent spends at most `ε`, in the units of any arena.** -/
theorem oppSpend_le_of_tail (hI : I.Valid) {c s₁ t₀ t : ℕ} {tables : List TTable}
    (htail : ∀ S : Finset Str, (∀ τ ∈ S, (∃ s, I.opp s τ = true) ∧ I.opp s₁ τ = false) →
      trueCost S ≤ 1 / 2 ^ c) (hs : s₁ ≤ t₀) :
    oppSpend I (arenaOf c tables) t₀ t ≤ levelBudget tables 0 := by
  have hS := htail ((arenaOf c tables).board.filter fun τ => I.opp t τ && !(I.opp t₀ τ))
    fun τ hτ => by
      have h := (mem_filter.1 hτ).2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      refine ⟨⟨t, h.1⟩, ?_⟩
      cases ho : I.opp s₁ τ with
      | false => rfl
      | true =>
        have := hI.opp_mono hs ho
        rw [h.2] at this
        cases this
  have hq := cost_eq_trueCost (S := (arenaOf c tables).board.filter
    fun τ => I.opp t τ && !(I.opp t₀ τ)) (filter_subset _ _)
  have hle : ((oppSpend I (arenaOf c tables) t₀ t : ℕ) : ℚ) ≤
      ((levelBudget tables 0 : ℕ) : ℚ) := by
    unfold oppSpend
    rw [hq]
    have h2 : (0 : ℚ) < 2 ^ (c + maxLen tables + 1) := by positivity
    calc _ ≤ (1 / 2 ^ c : ℚ) * 2 ^ (c + maxLen tables + 1) :=
          mul_le_mul_of_nonneg_right hS h2.le
      _ = ((levelBudget tables 0 : ℕ) : ℚ) := by
          unfold levelBudget
          push_cast
          rw [show c + maxLen tables + 1 = c + (maxLen tables + 1) by ring, pow_add]
          field_simp
  exact_mod_cast hle

/-- If `a ≤ E` and `a` is at most the opponent's limit in every game of `l`, then `a` is at most the
minimum of `E` and of these limits. -/
theorem le_foldr_min {a E : ℕ} {l : List BoardGame} (hE : a ≤ E) (h : ∀ g ∈ l, a ≤ g.oppLimit) :
    a ≤ l.foldr (fun g n => min g.oppLimit n) E := by
  induction l with
  | nil => exact hE
  | cons g l ih =>
    exact le_min (h g List.mem_cons_self) (ih fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

/-- The next visit of a requirement. -/
theorem exists_next_visit (I : Input) (i s : ℕ) :
    ∃ v ≥ s, (Nat.unpair v).1 = i ∧ rsAt I v i = rsAt I s i := by
  classical
  have hex : ∃ u, s ≤ u ∧ (Nat.unpair u).1 = i := by
    obtain ⟨u, hu, hui⟩ := exists_stage_ge i s
    exact ⟨u, hu, hui⟩
  have hu := Nat.find_spec hex
  refine ⟨Nat.find hex, hu.1, hu.2, rsAt_const I hu.1 fun s'' h1 h2 h3 =>
    Nat.find_min hex h2 ⟨h1, h3⟩⟩

/-- **A play within the limit at all later visits runs forever.** -/
theorem permanent_of_limit {i s₀ s₃ c : ℕ} {pl : Play} (hno : NoReset I i s₀) (hs : s₀ ≤ s₃)
    (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c) (hp : (rsAt I s₃ i).play = some pl)
    (hlim : ∀ s ≥ s₃, (Nat.unpair s).1 = i → ∀ pl', (rsAt I s i).play = some pl' →
      pl'.start = pl.start → pl'.arena = pl.arena → pl'.kind = pl.kind →
      oppSpend I pl'.arena pl'.start (s + 1) ≤
        pl'.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl'.arena.tables 0)) :
    Permanent I i := by
  refine ⟨s₃, pl.start, fun s hs₃ => ?_⟩
  suffices h : ∃ pl', (rsAt I s i).play = some pl' ∧ pl'.start = pl.start ∧ pl'.arena = pl.arena ∧
      pl'.kind = pl.kind by
    obtain ⟨pl', h1, h2, -, -⟩ := h
    exact ⟨pl', h1, h2⟩
  induction s, hs₃ using Nat.le_induction with
  | base => exact ⟨pl, hp, rfl, rfl, rfl⟩
  | succ s hle ih =>
    obtain ⟨pl', h1, h2, h3, h4⟩ := ih
    by_cases hi : i = (Nat.unpair s).1
    · subst hi
      have hl := hlim s hle rfl pl' h1 h2 h3 h4
      exact ⟨_, play_after_limit (hno s (hs.trans hle) rfl) (hc s (hs.trans hle)) h1 hl, h2, h3, h4⟩
    · rw [rsAt_succ_of_ne I hi]
      exact ⟨pl', h1, h2, h3, h4⟩

/-- The arena of a play, in a stage with settled `c`. -/
theorem arena_of_play {i s c : ℕ} {pl : Play} (hc : (rsAt I s i).c = some c)
    (hp : (rsAt I s i).play = some pl) : pl.arena = arenaOf c (rsAt I s i).tables := by
  obtain ⟨c', hc', ha, -⟩ := (reqWF_rsAt I s i).play pl hp
  rw [hc] at hc'
  cases hc'
  exact ha

/-- **A balanced game started after the tail stage cannot be cheated, so it runs forever.** -/
theorem permanent_of_balanced (hI : I.Valid) {i s₀ s₃ c s₁ : ℕ} {pl : Play} (hno : NoReset I i s₀)
    (hs : s₀ ≤ s₃) (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c) (hp : (rsAt I s₃ i).play = some pl)
    (hk : pl.kind = .balanced) (hstart : s₁ ≤ pl.start)
    (htail : ∀ S : Finset Str, (∀ τ ∈ S, (∃ s, I.opp s τ = true) ∧ I.opp s₁ τ = false) →
      trueCost S ≤ 1 / 2 ^ c) : Permanent I i := by
  refine permanent_of_limit hno hs hc hp fun s hle _ pl' h1 h2 _ h4 => ?_
  have hcs := hc s (hs.trans hle)
  have ha := arena_of_play hcs h1
  have hE : oppSpend I pl'.arena pl'.start (s + 1) ≤ levelBudget pl'.arena.tables 0 := by
    rw [ha]
    exact oppSpend_le_of_tail hI htail (by rw [h2]; exact hstart)
  obtain ⟨-, hlim⟩ := (run_invariant hI s i).balancedNone pl' h1 (h4.trans hk)
  exact le_foldr_min hE fun g hg => by
    rw [hlim g hg]
    exact hE

/-! ### The outcome of an examination -/

/-- The examination never gets stuck, by the principal ultrafilter. -/
theorem topOutcome_ne_stuck (ar : Arena) (A : Fin 3 → Finset Str) (E : ℕ) :
    topOutcome ar A E ≠ .stuck := by
  intro h
  unfold topOutcome at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hmeet
      split at h
      · cases h
      · rename_i hgen
        have hclosed : ∀ S T, S ⊆ vectors ar.tables.length → T ⊆ vectors ar.tables.length →
            TTMeet.Forces ar.w ar.value S (A 0) E E → TTMeet.Forces ar.w ar.value T (A 0) E E →
            TTMeet.Forces ar.w ar.value (S ∩ T) (A 0) E E := by
          intro S T hS hT hFS hFT
          by_contra hno
          apply List.find?_eq_none.1 hmeet (S, T)
            (List.pair_mem_product.2 ⟨mem_subsetsOf hS, mem_subsetsOf hT⟩)
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
            decide_eq_false_iff_not]
          exact ⟨⟨hFS, hFT⟩, hno⟩
        obtain ⟨σ, hσ, hF, -⟩ := exists_generator (Arena.value_mem_vectors ar) hclosed
        exact List.find?_eq_none.1 hgen σ (List.mem_toFinset.1 hσ)
          (decide_eq_true (show ar.Forces _ _ _ _ from hF))

/-- When Case 2 agrees on a value with an existing agreement, it is the old value. -/
theorem examineTop_inr_of_baseline {st : ConState} {i t c : ℕ} {rs : ReqState} {bl : Baseline}
    (hbl : rs.baseline = some bl) {r : ReqState × List Bool}
    (hr : examineTop I st i t c rs = .inr r) : r.2 = bl.σ := by
  unfold examineTop at hr
  dsimp only at hr
  split at hr
  · rename_i bl' hbl'
    rw [hbl] at hbl'
    cases hbl'
    split at hr
    · cases hr
    · split at hr
      · cases hr
      · cases hr
        rfl
  · rename_i hn
    rw [hbl] at hn
    cases hn

/-- The possible outcomes of a visit in Case 2. -/
theorem caseTwo_outcome {st : ConState} {i t c : ℕ} {rs : ReqState} (hw : ReqWF i t rs)
    (hc : rs.c = some c) (hnp : rs.play = none) :
    (∃ σ, (caseTwo I st i t c rs).1.baseline = some ⟨σ, fun _ => t⟩) ∨
      ((caseTwo I st i t c rs).1.play = none ∧ (caseTwo I st i t c rs).1.baseline = none ∧
        rs.baseline ≠ none) ∨
      (∃ pl, (caseTwo I st i t c rs).1.play = some pl ∧ pl.start = t ∧ pl.kind = .balanced) ∨
      (∃ pl, (caseTwo I st i t c rs).1.play = some pl ∧ pl.start = t ∧ pl.kind = .unbalanced ∧
        rs.baseline ≠ none) := by
  obtain ⟨-, hspec⟩ := examineTop_spec (I := I) (st := st) hw hc
  unfold caseTwo
  dsimp only
  split
  · rename_i r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · rename_i bl hbl
      have hne : rs.baseline ≠ none := by rw [hbl]; simp
      split at hr
      · cases hr
        exact Or.inr (Or.inl ⟨hnp, rfl, hne⟩)
      · split at hr
        · cases hr
          exact Or.inr (Or.inr (Or.inr ⟨_, rfl, rfl, rfl, hne⟩))
        · cases hr
    · split at hr
      · cases hr
      · rename_i hnot
        split at hr
        · rename_i pl hpl
          cases hr
          obtain ⟨h1, -, h3, -⟩ := balancedPlay_inv hpl
          exact Or.inr (Or.inr (Or.inl ⟨pl, rfl, h1, h3⟩))
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
    obtain ⟨ht, hc₁, hp₁, hb₁, -⟩ := hspec _ hex
    dsimp only at ht hc₁ hp₁ hb₁
    split
    · exact Or.inl ⟨σ, hb₁⟩
    · split
      · exact Or.inl ⟨σ, hb₁⟩
      · split
        · exact Or.inl ⟨σ, hb₁⟩
        · rename_i tbl htbl
          generalize hv : topOutcome (arenaOf c (rs.tables ++ [tbl]))
            (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
            (levelBudget (rs.tables ++ [tbl]) 0) = v
          cases v with
          | principal σ' => exact Or.inl ⟨σ', rfl⟩
          | split j k S =>
            dsimp only
            split
            · rename_i pl hpl
              rw [← hv] at hpl
              obtain ⟨h1, -, h3, -⟩ := balancedPlay_inv hpl
              exact Or.inr (Or.inr (Or.inl ⟨pl, rfl, h1, h3⟩))
            · exact Or.inl ⟨σ, hb₁⟩
          | meet S T =>
            dsimp only
            split
            · rename_i pl hpl
              rw [← hv] at hpl
              obtain ⟨h1, -, h3, -⟩ := balancedPlay_inv hpl
              exact Or.inr (Or.inr (Or.inl ⟨pl, rfl, h1, h3⟩))
            · exact Or.inl ⟨σ, hb₁⟩
          | stuck => exact absurd hv (topOutcome_ne_stuck _ _ _)

/-- A visit in Case 2, with an agreement that is not dropped: the agreement grows, or a balanced
game starts on a new bit. -/
theorem caseTwo_baseline_step {st : ConState} {i t c : ℕ} {rs : ReqState} {bl : Baseline}
    (hw : ReqWF i t rs) (hc : rs.c = some c) (hbl : rs.baseline = some bl)
    (hnodrop : ∀ j, oppSpend I (arenaOf c rs.tables) (bl.base j) t ≤ levelBudget rs.tables 0) :
    (∃ bl', (caseTwo I st i t c rs).1.baseline = some bl' ∧ bl.σ <+: bl'.σ ∧
        ∀ j, bl'.base j = bl.base j ∨ bl'.base j = t) ∨
      (∃ pl, (caseTwo I st i t c rs).1.play = some pl ∧ pl.start = t ∧ pl.kind = .balanced) := by
  obtain ⟨-, hspec⟩ := examineTop_spec (I := I) (st := st) hw hc
  unfold caseTwo
  dsimp only
  split
  · rename_i r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · rename_i bl' hbl'
      rw [hbl] at hbl'
      cases hbl'
      split at hr
      · rename_i hdrop
        exfalso
        obtain ⟨j, -, hj⟩ := List.any_eq_true.1 hdrop
        exact absurd (hnodrop j) (not_le.2 (of_decide_eq_true hj))
      · split at hr
        · cases hr
          exact Or.inl ⟨bl, hbl, List.prefix_refl _, fun j => Or.inl rfl⟩
        · cases hr
    · rename_i hn
      rw [hbl] at hn
      cases hn
  · rename_i rs₁ σ hex
    obtain ⟨ht, hc₁, hp₁, hb₁, hσ⟩ := hspec _ hex
    dsimp only at ht hc₁ hp₁ hb₁ hσ
    have hσeq : σ = bl.σ := examineTop_inr_of_baseline hbl hex
    have hleft : (rs₁.baseline = some ⟨σ, fun _ => t⟩) →
        ∃ bl', rs₁.baseline = some bl' ∧ bl.σ <+: bl'.σ ∧
          ∀ j, bl'.base j = bl.base j ∨ bl'.base j = t := fun h =>
      ⟨⟨σ, fun _ => t⟩, h, by rw [hσeq], fun _ => Or.inr rfl⟩
    have hforces := examineTop_forces hex 0
    dsimp only at hforces
    split
    · exact Or.inl (hleft hb₁)
    · split
      · exact Or.inl (hleft hb₁)
      · split
        · exact Or.inl (hleft hb₁)
        · rename_i tbl htbl
          generalize hv : topOutcome (arenaOf c (rs.tables ++ [tbl]))
            (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
            (levelBudget (rs.tables ++ [tbl]) 0) = v
          cases v with
          | principal σ' =>
            refine Or.inl ⟨⟨σ', fun _ => t⟩, rfl, ?_, fun _ => Or.inr rfl⟩
            have hlen := topOutcome_principal hv
            have hforces' := topOutcome_principal_forces hv 0
            have htake := take_eq_of_forces hσ (by simpa [arenaOf] using hlen)
              (by
                rw [position_inter_board]
                exact hforces) hforces'
            rw [← hσeq, ← htake]
            exact List.take_prefix _ _
          | split j k S =>
            dsimp only
            split
            · rename_i pl hpl
              rw [← hv] at hpl
              obtain ⟨h1, -, h3, -⟩ := balancedPlay_inv hpl
              exact Or.inr ⟨pl, rfl, h1, h3⟩
            · exact Or.inl (hleft hb₁)
          | meet S T =>
            dsimp only
            split
            · rename_i pl hpl
              rw [← hv] at hpl
              obtain ⟨h1, -, h3, -⟩ := balancedPlay_inv hpl
              exact Or.inr ⟨pl, rfl, h1, h3⟩
            · exact Or.inl (hleft hb₁)
          | stuck => exact absurd hv (topOutcome_ne_stuck _ _ _)

/-- A visit in Case 3 keeps the agreement, unless the opponent has spent too much. -/
theorem caseThree_baseline {st : ConState} {i t c : ℕ} {rs : ReqState} {pl : Play} {bl : Baseline}
    (hbl : rs.baseline = some bl)
    (h : oppSpend I pl.arena pl.start t ≤
        pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0) ∨
      ∃ σ b, pl.kind = .stacked σ b ∧ oppSpend I pl.arena pl.start t ≤
          levelBudget pl.arena.tables 0) :
    ∃ bl', (caseThree I st i t c rs pl).1.baseline = some bl' ∧ bl'.σ = bl.σ ∧
      ∀ j, bl'.base j = bl.base j ∨ bl'.base j = t := by
  unfold caseThree
  dsimp only
  by_cases hl : oppSpend I pl.arena pl.start t ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)
  · rw [ite_eq_left hl]
    exact ⟨bl, hbl, rfl, fun _ => Or.inl rfl⟩
  · rw [ite_eq_right hl]
    obtain ⟨σ, b, hk, hE⟩ := h.resolve_left hl
    rw [hk]
    dsimp only
    rw [ite_eq_left hE]
    split
    · exact ⟨bl, hbl, rfl, fun _ => Or.inl rfl⟩
    · refine ⟨⟨bl.σ, fun j => if j = b then bl.base j else t⟩, ?_, rfl, fun j => ?_⟩
      · change rs.baseline.map _ = _
        rw [hbl]
        rfl
      · by_cases hj : j = b
        · exact Or.inl (by simp [hj])
        · exact Or.inr (by simp [hj])

/-- What a play can turn into when the opponent exceeds the limit. -/
theorem change_spec {s c : ℕ} {pl : Play}
    (hres : mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) = false)
    (hc : (rsAt I s (Nat.unpair s).1).c = some c)
    (hp : (rsAt I s (Nat.unpair s).1).play = some pl)
    (hl : ¬ oppSpend I pl.arena pl.start (s + 1) ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)) :
    ((rsAt I (s + 1) (Nat.unpair s).1).play = none ∧
        ((rsAt I (s + 1) (Nat.unpair s).1).baseline = none ∨ ∃ σ b, pl.kind = .stacked σ b)) ∨
      ∃ pl', (rsAt I (s + 1) (Nat.unpair s).1).play = some pl' ∧ pl'.start = s + 1 ∧
        pl'.kind = .unbalanced := by
  have hst := stage_stateAt I s
  have hcore := stepCore_eq_three (I := I) (st := stateAt I s) (c := c) (pl := pl)
    (by rw [hst]; exact hres) (by rw [hst]; exact hc) (by rw [hst]; exact hp)
  rw [hst] at hcore
  have hf1 : (rsAt I (s + 1) (Nat.unpair s).1).play = (stepCore I (stateAt I s)).1.play := by
    rw [rsAt_succ_self]
  have hf2 : (rsAt I (s + 1) (Nat.unpair s).1).baseline =
      (stepCore I (stateAt I s)).1.baseline := by
    rw [rsAt_succ_self]
  rw [hf1, hf2, hcore]
  dsimp only
  unfold caseThree
  dsimp only
  rw [ite_eq_right hl]
  split
  · rename_i σ b hk
    split_ifs
    · split
      · exact Or.inr ⟨_, rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, Or.inr ⟨σ, b, hk⟩⟩
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
  · exact Or.inl ⟨rfl, Or.inl rfl⟩

/-- `change_spec` for a named requirement. -/
theorem change_spec_of {i s c : ℕ} {pl : Play} (hi : (Nat.unpair s).1 = i)
    (hres : mustReset I (stateAt I s) i (Nat.unpair s).2 (s + 1) = false)
    (hc : (rsAt I s i).c = some c) (hp : (rsAt I s i).play = some pl)
    (hl : ¬ oppSpend I pl.arena pl.start (s + 1) ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)) :
    ((rsAt I (s + 1) i).play = none ∧
        ((rsAt I (s + 1) i).baseline = none ∨ ∃ σ b, pl.kind = .stacked σ b)) ∨
      ∃ pl', (rsAt I (s + 1) i).play = some pl' ∧ pl'.start = s + 1 ∧ pl'.kind = .unbalanced := by
  subst hi
  exact change_spec hres hc hp hl

/-- An unbalanced game that exceeds its limit ends with no play and no agreement. -/
theorem unbalanced_exceed {i s c : ℕ} {pl : Play} (hi : (Nat.unpair s).1 = i)
    (hres : mustReset I (stateAt I s) i (Nat.unpair s).2 (s + 1) = false)
    (hc : (rsAt I s i).c = some c) (hp : (rsAt I s i).play = some pl)
    (hk : pl.kind = .unbalanced)
    (hl : ¬ oppSpend I pl.arena pl.start (s + 1) ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)) :
    (rsAt I (s + 1) i).play = none ∧ (rsAt I (s + 1) i).baseline = none := by
  subst hi
  have hst := stage_stateAt I s
  have hcore := stepCore_eq_three (I := I) (st := stateAt I s) (c := c) (pl := pl)
    (by rw [hst]; exact hres) (by rw [hst]; exact hc) (by rw [hst]; exact hp)
  rw [hst] at hcore
  have hf1 : (rsAt I (s + 1) (Nat.unpair s).1).play = (stepCore I (stateAt I s)).1.play := by
    rw [rsAt_succ_self]
  have hf2 : (rsAt I (s + 1) (Nat.unpair s).1).baseline =
      (stepCore I (stateAt I s)).1.baseline := by
    rw [rsAt_succ_self]
  rw [hf1, hf2, hcore]
  dsimp only
  unfold caseThree
  dsimp only
  rw [ite_eq_right hl, hk]
  exact ⟨rfl, rfl⟩

/-- If no game runs forever, some later visit exceeds the limit of a running play. -/
theorem exists_exceed {i s₀ s c : ℕ} {pl : Play} (hno : NoReset I i s₀) (hs : s₀ ≤ s)
    (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c) (hp : (rsAt I s i).play = some pl)
    (hnp : ¬ Permanent I i) :
    ∃ u ≥ s, (Nat.unpair u).1 = i ∧ ∃ pl', (rsAt I u i).play = some pl' ∧ pl'.kind = pl.kind ∧
      ¬ oppSpend I pl'.arena pl'.start (u + 1) ≤
        pl'.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl'.arena.tables 0) := by
  by_contra hcon
  refine hnp (permanent_of_limit hno hs hc hp fun s' hle hi pl' h1 _ _ h4 => ?_)
  by_contra hbad
  exact hcon ⟨s', hle, hi, pl', h1, h4, hbad⟩

/-- If no game runs forever, a running play is eventually replaced by no play. -/
theorem exists_no_play {i s₀ s c : ℕ} {pl : Play} (hno : NoReset I i s₀) (hs : s₀ ≤ s)
    (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c) (hp : (rsAt I s i).play = some pl)
    (hnp : ¬ Permanent I i) :
    ∃ s' ≥ s, (rsAt I s' i).play = none ∧
      (pl.kind = .unbalanced → (rsAt I s' i).baseline = none) := by
  obtain ⟨u, hu, hui, pl', h1, h2, h3⟩ := exists_exceed hno hs hc hp hnp
  have hs₀u := hs.trans hu
  rcases change_spec_of (hui) (hno u hs₀u hui) (hc u hs₀u) h1 h3 with
    ⟨hn, hb⟩ | ⟨pl'', hsome, hst, hk⟩
  · refine ⟨u + 1, by omega, hn, fun hunb => ?_⟩
    rcases hb with hb | ⟨σ, b, hk⟩
    · exact hb
    · rw [h2, hunb] at hk
      cases hk
  · -- An unbalanced game: it can only end with no play and no agreement.
    obtain ⟨v, hv, hvi, pl₃, h4, h5, h6⟩ :=
      exists_exceed hno (show s₀ ≤ u + 1 by omega) hc hsome hnp
    rw [hk] at h5
    obtain ⟨hn', hb'⟩ := unbalanced_exceed hvi (hno v (by omega) hvi) (hc v (by omega)) h4 h5 h6
    exact ⟨v + 1, by omega, hn', fun _ => hb'⟩

/-- A stage from which the agreement of `R_i` is protected against the opponent's remaining
spending: the opponent's tail from `s₁` is at most `ε_i`, and all the base stages are at least
`s₁`. -/
def Protected (I : Input) (i c s₂ : ℕ) : Prop :=
  ∃ s₁ bl, (∀ S : Finset Str, (∀ τ ∈ S, (∃ s, I.opp s τ = true) ∧ I.opp s₁ τ = false) →
      trueCost S ≤ 1 / 2 ^ c) ∧
    (rsAt I s₂ i).baseline = some bl ∧ ∀ j, s₁ ≤ bl.base j

/-- **Lemma 4.3, resettling agreement.**  With `ε_i` settled, either some game of `R_i` runs
forever, or at a late stage all three boards are based after the tail stage.  At most a few games
that started before the tail stage can be in the way. -/
theorem exists_protected_or_permanent (hI : I.Valid) {i s₀ c : ℕ} (hno : NoReset I i s₀)
    (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c) :
    Permanent I i ∨ ∃ s₂ ≥ s₀, Protected I i c s₂ := by
  obtain ⟨s₁, ht⟩ := opp_tail hI (δ := 1 / 2 ^ c) (by positivity)
  set S := max s₀ s₁ with hS
  have htail := tail_mono hI (le_max_right s₀ s₁) ht
  have hs₀S : s₀ ≤ S := le_max_left _ _
  by_cases hperm : Permanent I i
  · exact Or.inl hperm
  refine Or.inr ?_
  -- The step at a visit with no play.
  have hvisit : ∀ v ≥ S, (Nat.unpair v).1 = i → (rsAt I v i).play = none →
      (∃ s₂ ≥ s₀, Protected I i c s₂) ∨
        ((rsAt I (v + 1) i).play = none ∧ (rsAt I (v + 1) i).baseline = none ∧
          (rsAt I v i).baseline ≠ none) ∨
        (∃ pl, (rsAt I (v + 1) i).play = some pl ∧ pl.kind = .unbalanced ∧
          (rsAt I v i).baseline ≠ none) := by
    intro v hv hvi hp
    subst hvi
    have hst := stage_stateAt I v
    have hcv := hc v (hs₀S.trans hv)
    have hres := hno v (hs₀S.trans hv) rfl
    have hw := (reqWF_rsAt I v (Nat.unpair v).1).mono (Nat.le_succ v)
    have hcore := stepCore_eq_two (I := I) (st := stateAt I v) (c := c)
      (by rw [hst]; exact hres) (by rw [hst]; exact hcv) (by rw [hst]; exact hp)
    rw [hst] at hcore
    have hf1 : (rsAt I (v + 1) (Nat.unpair v).1).play = (stepCore I (stateAt I v)).1.play := by
      rw [rsAt_succ_self]
    have hf2 : (rsAt I (v + 1) (Nat.unpair v).1).baseline =
        (stepCore I (stateAt I v)).1.baseline := by
      rw [rsAt_succ_self]
    rw [hf1, hf2, hcore]
    dsimp only
    rcases caseTwo_outcome (I := I) (st := stateAt I v) hw hcv hp with
      ⟨σ, hb⟩ | ⟨h1, h2, h3⟩ | ⟨pl, h1, h2, h3⟩ | ⟨pl, h1, -, h3, h4⟩
    · refine Or.inl ⟨v + 1, by have := hs₀S.trans hv; omega, s₁, ⟨σ, fun _ => v + 1⟩, ht, ?_,
        fun _ => ?_⟩
      · rw [hf2, hcore]
        exact hb
      · have := (le_max_right s₀ s₁).trans hv
        change s₁ ≤ v + 1
        omega
    · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
    · exfalso
      refine hperm (permanent_of_balanced hI hno (show s₀ ≤ v + 1 by
        have := hs₀S.trans hv
        omega) hc (pl := pl) ?_ h3 (s₁ := s₁) ?_ ht)
      · rw [hf1, hcore]
        exact h1
      · rw [h2]
        have := (le_max_right s₀ s₁).trans hv
        omega
    · exact Or.inr (Or.inr ⟨pl, h1, h3, h4⟩)
  -- With no play and no agreement, the next visit gives a protected stage.
  have hkey : ∀ s ≥ S, (rsAt I s i).play = none → (rsAt I s i).baseline = none →
      ∃ s₂ ≥ s₀, Protected I i c s₂ := by
    intro s hs hp hb
    obtain ⟨v, hv, hvi, hsame⟩ := exists_next_visit I i s
    have hp' : (rsAt I v i).play = none := by rw [hsame]; exact hp
    have hb' : (rsAt I v i).baseline = none := by rw [hsame]; exact hb
    rcases hvisit v (hs.trans hv) hvi hp' with h | ⟨-, -, h⟩ | ⟨-, -, -, h⟩
    · exact h
    · exact absurd hb' h
    · exact absurd hb' h
  -- A stage with no play.
  have hnone : ∃ s ≥ S, (rsAt I s i).play = none := by
    cases hp : (rsAt I S i).play with
    | none => exact ⟨S, le_rfl, hp⟩
    | some pl =>
      obtain ⟨s', hs', hn, -⟩ := exists_no_play hno hs₀S hc hp hperm
      exact ⟨s', hs', hn⟩
  obtain ⟨s, hs, hp⟩ := hnone
  obtain ⟨v, hv, hvi, hsame⟩ := exists_next_visit I i s
  have hp' : (rsAt I v i).play = none := by rw [hsame]; exact hp
  rcases hvisit v (hs.trans hv) hvi hp' with h | ⟨h1, h2, -⟩ | ⟨pl, h1, h2, -⟩
  · exact h
  · exact hkey (v + 1) (by have := hs.trans hv; omega) h1 h2
  · obtain ⟨s', hs', hn, hb⟩ := exists_no_play hno
      (show s₀ ≤ v + 1 by have := hs₀S.trans (hs.trans hv); omega) hc h1 hperm
    exact hkey s' (by have := hs.trans hv; omega) hn (hb h2)

/-- **Lemma 4.3, the agreed value is stable.**  This is the heart of the proof, and the step that
fails for the printed Case 2 (`ParityExample.lean`).  After a protected stage a balanced or
unbalanced game cannot be cheated, so it would run forever.  If no game runs forever, an agreed
value is never dropped and only grows: a conflict with it starts an uncheatable game, and a new bit
extends it (`generator_take`, `not_forces_and_compl`). -/
theorem agreed_nested (hI : I.Valid) {i s₀ c s₂ : ℕ} (hno : NoReset I i s₀)
    (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c) (hs₂ : s₀ ≤ s₂) (hp : Protected I i c s₂)
    (hnp : ¬ Permanent I i) :
    (∀ s ≥ s₂, (rsAt I s i).baseline.isSome = true) ∧
      ∀ s s' bl bl', s₂ ≤ s → s ≤ s' → (rsAt I s i).baseline = some bl →
        (rsAt I s' i).baseline = some bl' → bl.σ <+: bl'.σ := by
  obtain ⟨s₁, bl₀, htail, hbl₀, hbase₀⟩ := hp
  -- One stage.
  have hstep : ∀ s ≥ s₂, ∀ bl, (rsAt I s i).baseline = some bl → (∀ j, s₁ ≤ bl.base j) →
      ∃ bl', (rsAt I (s + 1) i).baseline = some bl' ∧ bl.σ <+: bl'.σ ∧ ∀ j, s₁ ≤ bl'.base j := by
    intro s hs bl hbl hbase
    by_cases hi : i = (Nat.unpair s).1
    · subst hi
      have hs₀ := hs₂.trans hs
      have hst := stage_stateAt I s
      have hcs := hc s hs₀
      have hres := hno s hs₀ rfl
      have hwf := reqWF_rsAt I s (Nat.unpair s).1
      have hw := hwf.mono (Nat.le_succ s)
      have hinv := run_invariant hI s (Nat.unpair s).1
      have hle : s₁ ≤ s + 1 := by
        have h1 := hbase 0
        have h2 := hinv.baseLe bl hbl 0
        have h3 := lastVisit_le I s (Nat.unpair s).1
        omega
      have hf2 : (rsAt I (s + 1) (Nat.unpair s).1).baseline =
          (stepCore I (stateAt I s)).1.baseline := by
        rw [rsAt_succ_self]
      have hf1 : (rsAt I (s + 1) (Nat.unpair s).1).play = (stepCore I (stateAt I s)).1.play := by
        rw [rsAt_succ_self]
      cases hpl : (rsAt I s (Nat.unpair s).1).play with
      | none =>
        have hcore := stepCore_eq_two (I := I) (st := stateAt I s) (c := c)
          (by rw [hst]; exact hres) (by rw [hst]; exact hcs) (by rw [hst]; exact hpl)
        rw [hst] at hcore
        rw [hf2, hcore]
        dsimp only
        rcases caseTwo_baseline_step (I := I) (st := stateAt I s) hw hcs hbl
            (fun j => oppSpend_le_of_tail hI htail (hbase j)) with
          ⟨bl', hb', hpre, hbase'⟩ | ⟨pl, h1, h2, h3⟩
        · refine ⟨bl', hb', hpre, fun j => ?_⟩
          rcases hbase' j with h | h
          · rw [h]
            exact hbase j
          · rw [h]
            exact hle
        · exfalso
          refine hnp (permanent_of_balanced hI hno (show s₀ ≤ s + 1 by omega) hc (pl := pl) ?_ h3
            (s₁ := s₁) ?_ htail)
          · rw [hf1, hcore]
            exact h1
          · rw [h2]
            exact hle
      | some pl =>
        have hcore := stepCore_eq_three (I := I) (st := stateAt I s) (c := c) (pl := pl)
          (by rw [hst]; exact hres) (by rw [hst]; exact hcs) (by rw [hst]; exact hpl)
        rw [hst] at hcore
        rw [hf2, hcore]
        dsimp only
        have ha := arena_of_play hcs hpl
        have hcond : oppSpend I pl.arena pl.start (s + 1) ≤
            pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0) ∨
            ∃ σ b, pl.kind = .stacked σ b ∧
              oppSpend I pl.arena pl.start (s + 1) ≤ levelBudget pl.arena.tables 0 := by
          cases hk : pl.kind with
          | balanced =>
            obtain ⟨hb, -⟩ := hinv.balancedNone pl hpl hk
            rw [hbl] at hb
            cases hb
          | stacked σ b =>
            obtain ⟨⟨bl', hbl', -, hb'⟩, -, -⟩ := hinv.stacked pl σ b hpl hk
            rw [hbl] at hbl'
            cases hbl'
            refine Or.inr ⟨σ, b, rfl, ?_⟩
            rw [ha]
            exact oppSpend_le_of_tail hI htail (by rw [← hb']; exact hbase b)
          | unbalanced =>
            obtain ⟨bl', hbl', hk0, hlim⟩ := hinv.unbalancedLim pl hpl hk
            rw [hbl] at hbl'
            cases hbl'
            refine Or.inl (le_foldr_min ?_ fun g hg => ?_)
            · rw [ha]
              exact oppSpend_le_of_tail hI htail ((hbase 0).trans (hk0 0))
            · rcases hlim g hg with h | ⟨k, h⟩
              · rw [h, ha]
                exact oppSpend_le_of_tail hI htail ((hbase 0).trans (hk0 0))
              · rw [h]
                have hadd := oppSpend_add hI pl.arena (hk0 k)
                  (show pl.start ≤ s + 1 by
                    have h1 := hinv.startLe pl hpl
                    have h2 := lastVisit_le I s (Nat.unpair s).1
                    omega)
                have hb : oppSpend I pl.arena (bl.base k) (s + 1) ≤
                    levelBudget pl.arena.tables 0 := by
                  rw [ha]
                  exact oppSpend_le_of_tail hI htail (hbase k)
                omega
        obtain ⟨bl', hb', hσ, hbase'⟩ := caseThree_baseline (I := I) (st := stateAt I s)
          (i := (Nat.unpair s).1) (t := s + 1) (c := c) hbl hcond
        refine ⟨bl', hb', by rw [hσ], fun j => ?_⟩
        rcases hbase' j with h | h
        · rw [h]
          exact hbase j
        · rw [h]
          exact hle
    · rw [rsAt_succ_of_ne I hi]
      exact ⟨bl, hbl, List.prefix_refl _, hbase⟩
  -- The induction.
  have hall : ∀ s ≥ s₂, ∃ bl, (rsAt I s i).baseline = some bl ∧ ∀ j, s₁ ≤ bl.base j := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact ⟨bl₀, hbl₀, hbase₀⟩
    | succ s hle ih =>
      obtain ⟨bl, hbl, hbase⟩ := ih
      obtain ⟨bl', h1, -, h3⟩ := hstep s hle bl hbl hbase
      exact ⟨bl', h1, h3⟩
  refine ⟨fun s hs => ?_, fun s s' bl bl' hs hss' hbl hbl' => ?_⟩
  · obtain ⟨bl, hbl, -⟩ := hall s hs
    rw [hbl]
    rfl
  · have hsame : ∀ s' ≥ s, ∀ bl', (rsAt I s' i).baseline = some bl' → bl.σ <+: bl'.σ := by
      intro s' hss'
      induction s', hss' using Nat.le_induction with
      | base =>
        intro bl' h
        rw [hbl] at h
        cases h
        exact List.prefix_refl _
      | succ s' hle ih =>
        intro bl' h
        obtain ⟨bl₁, hbl₁, hbase₁⟩ := hall s' (hs.trans hle)
        obtain ⟨bl₂, h1, h2, -⟩ := hstep s' (hs.trans hle) bl₁ hbl₁ hbase₁
        rw [h] at h1
        cases h1
        exact (ih bl₁ hbl₁).trans h2
    exact hsame s' hss' bl' hbl'

end Kolmogorov.RandomStrings.TTMeet
