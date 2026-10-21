/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.Mirror

/-!
# Claim 2, second layer: helper lemmas for the live-game invariants

The four invariants of the live games hold at the beginning of every stage for every live game
of every requirement.  This module collects the helper lemmas: bounds on `hval`, the transfer of
safety through `gameOf`, the reply specification, and the charging predicate `LGood`.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-! ### Claim 2, second layer: invariants of the live games

The four invariants below hold at the beginning of every stage, for every requirement `e` and
every live game `g = (x, X, m, st)` of `e` (they are proved together by induction on the stages;
`live_playSets_disjoint` is used in the step of `live_game_safe`). -/

/-! #### Helper lemmas for the live-game invariants

The four invariants are proved together (`LGInv`, `lg_stage_liveInv`) by induction on the stages;
inside a stage, by induction along the fold over the requirements (`LGMid`). -/

section

omit [Family]

/-- The conditional target complexity is bounded by the original value plus `3`. -/
theorem CState.lg_Hstar_le_Fstar (σ : CState) (x : BitString) :
    σ.Hstar x ≤ ((σ.Fstar x + 3 : ℕ) : ℕ∞) := by
  unfold CState.Hstar
  refine (min_le_right _ _).trans ?_
  push_cast; exact le_rfl

/-- The numeric value `hval` agrees with the extended-natural upper bound `Hstar`. -/
theorem CState.lg_hval_coe (σ : CState) (x : BitString) : (σ.hval x : ℕ∞) = σ.Hstar x :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top _) (σ.lg_Hstar_le_Fstar x))

/-- The target value `hval` is bounded by the current original value `Fstar` plus `3`. -/
theorem CState.lg_hval_le_Fstar (σ : CState) (x : BitString) : σ.hval x ≤ σ.Fstar x + 3 := by
  have h := σ.lg_Hstar_le_Fstar x
  rw [← σ.lg_hval_coe x] at h
  exact_mod_cast h

/-- The target value `hval` is at least `3`. -/
theorem CState.lg_three_le_hval (σ : CState) (x : BitString) : 3 ≤ σ.hval x := by
  have h : ((3 : ℕ) : ℕ∞) ≤ σ.Hstar x := by
    unfold CState.Hstar
    refine le_min ?_ ?_
    · exact le_add_left (by exact_mod_cast ((by norm_num : (3 : ℕ) ≤ 5)))
    · exact le_add_self
  rw [← σ.lg_hval_coe x] at h
  exact_mod_cast h

/-- Decreasing `Kstar` and `Fstar` decreases `hval`. -/
theorem CState.lg_hval_le_hval {σ σ' : CState} (x : BitString) (hK : σ'.Kstar x ≤ σ.Kstar x)
    (hF : σ'.Fstar x ≤ σ.Fstar x) : σ'.hval x ≤ σ.hval x := by
  have h : σ'.Hstar x ≤ σ.Hstar x := by
    unfold CState.Hstar
    exact min_le_min (add_le_add hK le_rfl) (add_le_add (Nat.cast_le.2 hF) le_rfl)
  rw [← σ.lg_hval_coe x, ← σ'.lg_hval_coe x] at h
  exact_mod_cast h

/-- Applying flips does not change the target complexity of an unmodified string. -/
theorem lg_applyFlips_hval_of_not_mem (T : Finset BitString) (σ : CState) (z : BitString)
    (hz : z ∉ T) : (applyFlips T σ).hval z = σ.hval z := by
  simp [CState.hval, CState.Hstar, applyFlips, hz]

/-- The target complexity of a flipped string drops to slightly below its length. -/
theorem lg_applyFlips_hval_le_length (T : Finset BitString) (σ : CState) (z : BitString)
    (hz : z ∈ T) : (applyFlips T σ).hval z ≤ z.length - 4 + 3 := by
  have h := (applyFlips T σ).lg_hval_le_Fstar z
  have h2 : (applyFlips T σ).Fstar z ≤ z.length - 4 := by
    change (if z ∈ T then min (σ.Fstar z) (z.length - 4) else σ.Fstar z) ≤ z.length - 4
    rw [ite_eq_left hz]; exact min_le_right _ _
  omega

/-- Applying flips never increases the target complexity `hval`. -/
theorem lg_applyFlips_hval_le (T : Finset BitString) (σ : CState) (z : BitString) :
    (applyFlips T σ).hval z ≤ σ.hval z :=
  CState.lg_hval_le_hval z le_rfl (applyFlips_Fstar_le T σ z)

/-- Emulating `K` does not increase the target complexity `hval`. -/
theorem lg_updateK_hval_le (enumK : ℕ → BitString × ℕ) (t : ℕ) (σ : CState) (z : BitString) :
    (updateK enumK t σ).hval z ≤ σ.hval z := by
  refine CState.lg_hval_le_hval z ?_ le_rfl
  change Function.update σ.Kstar (enumK t).1 (min (σ.Kstar (enumK t).1) ((enumK t).2 : ℕ∞)) z ≤
    σ.Kstar z
  by_cases hz : z = (enumK t).1
  · subst hz; rw [Function.update_self]; exact min_le_left _ _
  · rw [Function.update_of_ne hz]

/-- Storing a game record does not change the target complexity `hval`. -/
theorem lg_setGame_hval (e : ℕ) (g : BitString × Finset BitString × ℕ × GState) (σ : CState) :
    (setGame e g σ).hval = σ.hval := rfl

/-- Injuring a requirement does not change the target complexity `hval`. -/
theorem lg_injure_hval (e : ℕ) (σ : CState) : (injure e σ).hval = σ.hval := rfl

/-- Destroying a requirement does not change the target complexity `hval`. -/
theorem lg_destroy_hval (e : ℕ) (σ : CState) : (destroy e σ).hval = σ.hval := rfl

/-- Strings of length `≤ 3` cost at least `1/8` to flip when the values are `≥ 3`. -/
theorem lg_four_le_length_of_flipCost (d : GameData) (z : BitString) (h3 : 3 ≤ d.h₀ z)
    (hc : flipCost d z < 1 / 8) : 4 ≤ z.length := by
  rcases Nat.lt_or_ge z.length 4 with hlt | hge
  · exfalso
    have h1 : (2 : ℝ)⁻¹ ^ 2 ≤ (2 : ℝ)⁻¹ ^ (z.length - 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (2 : ℝ)⁻¹ ^ d.h₀ z ≤ (2 : ℝ)⁻¹ ^ 3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h3
    have h4 : (2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ d.h₀ z ≤ flipCost d z := le_max_right _ _
    norm_num at h1 h2
    linarith
  · exact hge

/-- A single flip costs at most the whole move. -/
theorem lg_flipCost_le_moveCost (d : GameData) (S S' : Finset BitString) (z : BitString)
    (hz : z ∈ S' \ S) : flipCost d z ≤ moveCost d S S' :=
  Finset.single_le_sum (f := flipCost d) (fun y _ => flipCost_nonneg d y) hz

end

/-- Transfer of safety between two values `h` (old) and `h' ≤ h` (new) of the same game, when the
randomness of the queried strings outside `S₀ ⊆ st.S` is the same, the mover's score grows by the
potential, and the other score does not grow. -/
theorem lg_safeFor_gameOf_transfer {A : Set BitString}
    (c : OTMCode) (k : ℕ) (x : BitString) (h h' : BitString → ℕ) (ε : ℝ)
    (X S₀ : Finset BitString) (hle : ∀ z ∈ X, h' z ≤ h z)
    (hrand : ∀ z ∈ qsetF c k x, z ∉ S₀ →
      (z.length ≤ h z ↔ z.length ≤ h' z))
    (st st' : GState) (hsafe : SafeFor (gameOfF A c k x h ε X) (!st.yesTurn) st)
    (h0 : S₀ ⊆ st.S) (hSX : st.S ⊆ X) (hS : st'.S = st.S) (hT : st'.yesTurn = st.yesTurn)
    (hK : st.moverScore + ∑ z ∈ X \ st.S, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) ≤
      st'.moverScore)
    (hO : if st.yesTurn then st'.scoreN ≤ st.scoreN else st'.scoreY ≤ st.scoreY) :
    SafeFor (gameOfF A c k x h' ε X) (!st'.yesTurn) st' := by
  classical
  have hc0 : ∀ z ∈ (gameOfF A c k x h ε X).X,
      flipCost (gameOfF A c k x h' ε X) z ≤ flipCost (gameOfF A c k x h ε X) z := by
    intro z hz
    have hp : (2 : ℝ)⁻¹ ^ h z ≤ (2 : ℝ)⁻¹ ^ h' z :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hle z hz)
    change max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ h' z) ≤
      max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ h z)
    exact max_le_max le_rfl (by linarith)
  have hc1 : ∀ z ∈ (gameOfF A c k x h ε X).X, flipCost (gameOfF A c k x h ε X) z ≤
      flipCost (gameOfF A c k x h' ε X) z + ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) := by
    intro z hz
    have hp : (2 : ℝ)⁻¹ ^ h z ≤ (2 : ℝ)⁻¹ ^ h' z :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hle z hz)
    change max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ h z) ≤
      max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ h' z) + ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z)
    have m1 := le_max_left (0 : ℝ) ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ h' z)
    have m2 := le_max_right (0 : ℝ) ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ h' z)
    exact max_le (by linarith) (by linarith)
  have hout : ∀ S, S₀ ⊆ S → S ⊆ (gameOfF A c k x h ε X).X →
      (gameOfF A c k x h' ε X).outcome S = (gameOfF A c k x h ε X).outcome S := by
    intro S hS0 _
    by_cases hΦ : Family.Φ c k x
    · rw [gameOfF_of_Φ A _ _ _ hΦ, gameOfF_of_Φ A _ _ _ hΦ]
      simp only [gameOfT]
      refine decide_eq_decide.2
        (clockedAcceptsT_iff_of_agree c (Family.clk k x.length) _ _ x fun z hz => ?_)
      simp only [oracleOf, Set.mem_ofPred_eq]
      by_cases hzS : z ∈ S
      · simp [hzS]
      · have := hrand z (by rw [qsetF_of_Φ hΦ]; exact hz) (fun hz0 => hzS (hS0 hz0))
        tauto
    · rw [gameOfF_outcome_of_not A _ _ _ hΦ, gameOfF_outcome_of_not A _ _ _ hΦ]
  unfold SafeFor at hsafe ⊢
  rw [hT]
  cases hy : st.yesTurn with
  | false =>
    rw [hy] at hsafe hO
    simp only [Bool.not_false, ↓reduceIte] at hsafe ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hO
    simp only [GState.moverScore, hy, hT, Bool.false_eq_true, ↓reduceIte] at hK
    exact safeYes_transfer (gameOfF A c k x h ε X) (gameOfF A c k x h' ε X) rfl rfl
      (fun z => (2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) hc0 hc1 S₀ hout st hsafe st' hy h0 hSX hS
      hT hO hK
  | true =>
    rw [hy] at hsafe hO
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsafe ⊢
    simp only [↓reduceIte] at hO
    simp only [GState.moverScore, hy, hT, ↓reduceIte] at hK
    exact safeNo_transfer (gameOfF A c k x h ε X) h' (gameOfF A c k x h' ε X).outcome
      (fun z => (2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) hc0 hc1 S₀ hout st hsafe st' hy h0 hSX hS
      hT hK hO

omit [Family] in
/-- If there is a safe legal reply, `ourReply` computes one. -/
theorem lg_ourReply_spec (d : GameData) (we : Bool) (st : GState)
    (h : ∃ r, LegalMove d st r ∧ SafeFor d we (applyMove d st r)) :
    LegalMove d st (ourReply d we st) ∧ SafeFor d we (applyMove d st (ourReply d we st)) := by
  classical
  obtain ⟨r, hr⟩ := h
  have hex : ∃ k : ℕ, LegalMove d st
      (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.S) ∧
      SafeFor d we (applyMove d st
        (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.S)) :=
    ⟨Encodable.encode r.toList, by
      rw [Encodable.encodek]
      simp only [Option.map_some, Option.getD_some, Finset.toList_toFinset]
      exact hr⟩
  unfold ourReply
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

omit [Family] in
/-- A safe position answers every legal non-passing opponent move. -/
theorem SafeFor.lg_reply {d : GameData} {we : Bool} {st : GState} (h : SafeFor d we st)
    {S' : Finset BitString} (hL : LegalMove d st S') (hne : S' ≠ st.S) :
    ∃ r, LegalMove d (applyMove d st S') r ∧ SafeFor d we (applyMove d (applyMove d st S') r) := by
  unfold SafeFor at h ⊢
  cases we with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases h with
    | intro _ reply _ hlegal hsafe => exact ⟨reply S', hlegal S' hL hne, hsafe S' hL hne⟩
  | true =>
    simp only [↓reduceIte] at h ⊢
    cases h with
    | intro _ reply _ hlegal hsafe => exact ⟨reply S', hlegal S' hL hne, hsafe S' hL hne⟩

/-- The strings of the guarded game of the record `g` of requirement `e` (`qsetF`). -/
noncomputable def lgQ (γ : ℕ → OTMCode × ℕ) (e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) : Finset BitString :=
  qsetF (γ e).1 (γ e).2 g.1

/-- A live game record in good shape for the current values `h`. -/
structure LGood (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (h : BitString → ℕ) (e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) : Prop where
  side : g.2.2.2.yesTurn = false ↔ g.1 ∉ A
  SX : g.2.2.2.S ⊆ g.2.1
  XQ : g.2.1 ⊆ lgQ γ e g
  nonrand : ∀ z ∈ g.2.2.2.S, h z < z.length
  scY : 0 ≤ g.2.2.2.scoreY
  scN : 0 ≤ g.2.2.2.scoreN
  m7 : 7 ≤ g.2.2.1
  safe : SafeFor (gameOfF A (γ e).1 (γ e).2 g.1 h ((2 : ℝ)⁻¹ ^ g.2.2.1) g.2.1) (!g.2.2.2.yesTurn)
    g.2.2.2

/-- Good shape only depends on the values on the queried strings. -/
theorem LGood.of_eq {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {h h' : BitString → ℕ} {e : ℕ}
    {g : BitString × Finset BitString × ℕ × GState} (hg : LGood A γ h e g)
    (heq : ∀ z ∈ lgQ γ e g, h' z = h z) : LGood A γ h' e g := by
  refine ⟨hg.side, hg.SX, hg.XQ, fun z hz => ?_, hg.scY, hg.scN, hg.m7, ?_⟩
  · rw [heq z (hg.XQ (hg.SX hz))]; exact hg.nonrand z hz
  · refine lg_safeFor_gameOf_transfer (γ e).1 (γ e).2 g.1 h h' _ g.2.1 g.2.2.2.S
      (fun z hz => (heq z (hg.XQ hz)).le) (fun z hz _ => by rw [heq z hz]) g.2.2.2 g.2.2.2
      hg.safe subset_rfl hg.SX rfl rfl ?_ ?_
    · have : ∑ z ∈ g.2.1 \ g.2.2.2.S, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) = 0 :=
        Finset.sum_eq_zero fun z hz => by rw [heq z (hg.XQ (Finset.mem_sdiff.1 hz).1)]; ring
      rw [this, add_zero]
    · split_ifs <;> exact le_rfl

omit [Family] in
/-- Reducing complexity by updating `h` from `h` to `h'` yields a non-negative potential
difference. -/
theorem lg_two_inv_pow_sub_nonneg {h h' : BitString → ℕ} (z : BitString) (hle : h' z ≤ h z) :
    0 ≤ (2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z := by
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) hle
  linarith

/-- A charge of `K` by its real cost on the play set keeps the game in good shape for the new
values, if the randomness of the queried strings outside the flipped set does not change. -/
theorem LGood.charge {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {h h' : BitString → ℕ} {e : ℕ}
    {g : BitString × Finset BitString × ℕ × GState} (hg : LGood A γ h e g) (hle : ∀ z, h' z ≤ h z)
    (hrand : ∀ z ∈ lgQ γ e g, z ∉ g.2.2.2.S → (z.length ≤ h z ↔ z.length ≤ h' z)) :
    LGood A γ h' e (g.1, g.2.1, g.2.2.1,
      g.2.2.2.charge (∑ z ∈ g.2.1, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z))) := by
  have hδ : ∀ z, 0 ≤ (2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z := fun z =>
    lg_two_inv_pow_sub_nonneg z (hle z)
  obtain ⟨x, X, m, S, y, n, t⟩ := g
  have hsub : ∑ z ∈ X \ S, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) ≤
      ∑ z ∈ X, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun z _ _ => hδ z)
  have hc0 : 0 ≤ ∑ z ∈ X, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) :=
    Finset.sum_nonneg fun z _ => hδ z
  have hnr : ∀ z ∈ S, h' z < z.length := fun z hz => lt_of_le_of_lt (hle z) (hg.nonrand z hz)
  cases t with
  | false =>
    refine ⟨hg.side, hg.SX, hg.XQ, hnr, hg.scY, ?_, hg.m7, ?_⟩
    · change 0 ≤ n + _
      have := hg.scN; dsimp only at this; linarith
    · refine lg_safeFor_gameOf_transfer _ _ x h h' _ X S (fun z _ => hle z) hrand ⟨S, y, n, false⟩
        _ hg.safe subset_rfl hg.SX rfl rfl ?_ ?_
      · change n + _ ≤ n + _
        linarith
      · change y ≤ y
        exact le_rfl
  | true =>
    refine ⟨hg.side, hg.SX, hg.XQ, hnr, ?_, hg.scN, hg.m7, ?_⟩
    · change 0 ≤ y + _
      have := hg.scY; dsimp only at this; linarith
    · refine lg_safeFor_gameOf_transfer _ _ x h h' _ X S (fun z _ => hle z) hrand ⟨S, y, n, true⟩
        _ hg.safe subset_rfl hg.SX rfl rfl ?_ ?_
      · change y + _ ≤ y + _
        linarith
      · change n ≤ n
        exact le_rfl

section

omit [Family]

/-- A move by NO adds its cost to the NO score and passes the turn. -/
theorem lg_applyMove_false (d : GameData) (S : Finset BitString) (y n : ℝ) (T : Finset BitString) :
    applyMove d ⟨S, y, n, false⟩ T = ⟨T, y, n + moveCost d S T, true⟩ := rfl

/-- A move by YES adds its cost to the YES score and passes the turn. -/
theorem lg_applyMove_true (d : GameData) (S : Finset BitString) (y n : ℝ) (T : Finset BitString) :
    applyMove d ⟨S, y, n, true⟩ T = ⟨T, y + moveCost d S T, n, false⟩ := rfl

/-- `K`'s move during NO's turn adds its charge `c` to NO's score. -/
theorem lg_kMove_false (S : Finset BitString) (y n c : ℝ) (T : Finset BitString) :
    GState.kMove ⟨S, y, n, false⟩ T c = ⟨T, y, n + c, true⟩ := rfl

/-- `K`'s move during YES's turn adds its charge `c` to YES's score. -/
theorem lg_kMove_true (S : Finset BitString) (y n c : ℝ) (T : Finset BitString) :
    GState.kMove ⟨S, y, n, true⟩ T c = ⟨T, y + c, n, false⟩ := rfl

end

/-- A non-cheating flip move of `K` (all new strings non-random for the new values `h'`), charged
with its real cost, has a legal answer after which we are safe in the game with the new values. -/
theorem lg_move_reply {A : Set BitString}
    {c : OTMCode} {k : ℕ} {x : BitString} {h h' : BitString → ℕ} {ε : ℝ} {X : Finset BitString}
    (hle : ∀ z, h' z ≤ h z)
    (st : GState) (hsafe : SafeFor (gameOfF A c k x h ε X) (!st.yesTurn) st)
    (S' : Finset BitString) (h1 : st.S ⊆ S') (h2 : S' ⊆ X) (hne : S' ≠ st.S)
    (hflip : ∀ z ∈ S' \ st.S, h' z < z.length)
    (hrand : ∀ z ∈ qsetF c k x, z ∉ S' →
      (z.length ≤ h z ↔ z.length ≤ h' z))
    (hcheat : st.moverScore + ∑ z ∈ X, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) ≤ ε) :
    ∃ r, LegalMove (gameOfF A c k x h' ε X)
        (st.kMove S' (∑ z ∈ X, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z))) r ∧
      SafeFor (gameOfF A c k x h' ε X) (!st.yesTurn)
        (applyMove (gameOfF A c k x h' ε X)
          (st.kMove S' (∑ z ∈ X, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z))) r) := by
  have hδ : ∀ z, 0 ≤ (2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z := fun z =>
    lg_two_inv_pow_sub_nonneg z (hle z)
  have hfc : ∀ z ∈ S' \ st.S, flipCost (gameOfF A c k x h ε X) z ≤
      (2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z := by
    intro z hz
    have hlt := hflip z hz
    have hp : (2 : ℝ)⁻¹ ^ (z.length - 1) ≤ (2 : ℝ)⁻¹ ^ h' z :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    change max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ h z) ≤ _
    exact max_le (hδ z) (by linarith)
  have hmc : moveCost (gameOfF A c k x h ε X) st.S S' ≤
      ∑ z ∈ S' \ st.S, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) :=
    Finset.sum_le_sum hfc
  have hsplit := potential_split X st.S S' (fun z => (2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z)
    (fun z _ => hδ z) h1 h2
  have hsub : ∑ z ∈ X \ st.S, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) ≤
      ∑ z ∈ X, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun z _ _ => hδ z)
  have hpos : 0 ≤ ∑ z ∈ X \ S', ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) :=
    Finset.sum_nonneg fun z _ => hδ z
  have hc0 : ∀ z ∈ (gameOfF A c k x h ε X).X,
      flipCost (gameOfF A c k x h' ε X) z ≤ flipCost (gameOfF A c k x h ε X) z := by
    intro z _
    have hp : (2 : ℝ)⁻¹ ^ h z ≤ (2 : ℝ)⁻¹ ^ h' z :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hle z)
    change max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ h' z) ≤
      max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ h z)
    exact max_le_max le_rfl (by linarith)
  obtain ⟨S, y, n, t⟩ := st
  cases t with
  | false =>
    have hc' : n + ∑ z ∈ X, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) ≤ ε := hcheat
    have hL0 : LegalMove (gameOfF A c k x h ε X) ⟨S, y, n, false⟩ S' :=
      ⟨h1, h2, by change n + moveCost (gameOfF A c k x h ε X) S S' ≤ ε
                  dsimp only at hmc hsplit hsub; linarith⟩
    obtain ⟨r, ⟨r1, r2, r3⟩, hrs⟩ := hsafe.lg_reply hL0 hne
    rw [lg_applyMove_false] at r1 r3 hrs
    rw [lg_applyMove_true] at hrs
    change S' ⊆ r at r1
    change y + moveCost (gameOfF A c k x h ε X) S' r ≤ ε at r3
    have hmono := potential_mono X S' r (fun z => (2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z)
      (fun z _ => hδ z) r1
    have hcr := moveCost_le_moveCost (gameOfF A c k x h ε X) (gameOfF A c k x h' ε X) hc0 S' r r2
    rw [lg_kMove_false]
    refine ⟨r, ⟨r1, r2, by change y + moveCost (gameOfF A c k x h' ε X) S' r ≤ ε; linarith⟩, ?_⟩
    rw [lg_applyMove_true]
    refine lg_safeFor_gameOf_transfer c k x h h' ε X S' (fun z _ => hle z) hrand
      ⟨r, y + moveCost (gameOfF A c k x h ε X) S' r,
        n + moveCost (gameOfF A c k x h ε X) S S', false⟩
      ⟨r, y + moveCost (gameOfF A c k x h' ε X) S' r,
        n + ∑ z ∈ X, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z), false⟩
      hrs r1 r2 rfl rfl ?_ ?_
    · change n + moveCost (gameOfF A c k x h ε X) S S' + _ ≤ n + _
      dsimp only at hmc hsplit hsub hmono; linarith
    · change y + moveCost (gameOfF A c k x h' ε X) S' r ≤ y + moveCost (gameOfF A c k x h ε X) S' r
      linarith
  | true =>
    have hc' : y + ∑ z ∈ X, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z) ≤ ε := hcheat
    have hL0 : LegalMove (gameOfF A c k x h ε X) ⟨S, y, n, true⟩ S' :=
      ⟨h1, h2, by change y + moveCost (gameOfF A c k x h ε X) S S' ≤ ε
                  dsimp only at hmc hsplit hsub; linarith⟩
    obtain ⟨r, ⟨r1, r2, r3⟩, hrs⟩ := hsafe.lg_reply hL0 hne
    rw [lg_applyMove_true] at r1 r3 hrs
    rw [lg_applyMove_false] at hrs
    change S' ⊆ r at r1
    change n + moveCost (gameOfF A c k x h ε X) S' r ≤ ε at r3
    have hmono := potential_mono X S' r (fun z => (2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z)
      (fun z _ => hδ z) r1
    have hcr := moveCost_le_moveCost (gameOfF A c k x h ε X) (gameOfF A c k x h' ε X) hc0 S' r r2
    rw [lg_kMove_true]
    refine ⟨r, ⟨r1, r2, by change n + moveCost (gameOfF A c k x h' ε X) S' r ≤ ε; linarith⟩, ?_⟩
    rw [lg_applyMove_false]
    refine lg_safeFor_gameOf_transfer c k x h h' ε X S' (fun z _ => hle z) hrand
      ⟨r, y + moveCost (gameOfF A c k x h ε X) S S',
        n + moveCost (gameOfF A c k x h ε X) S' r, true⟩
      ⟨r, y + ∑ z ∈ X, ((2 : ℝ)⁻¹ ^ h' z - (2 : ℝ)⁻¹ ^ h z),
        n + moveCost (gameOfF A c k x h' ε X) S' r, true⟩
      hrs r1 r2 rfl rfl ?_ ?_
    · change y + moveCost (gameOfF A c k x h ε X) S S' + _ ≤ y + _
      dsimp only at hmc hsplit hsub hmono; linarith
    · change n + moveCost (gameOfF A c k x h' ε X) S' r ≤ n + moveCost (gameOfF A c k x h ε X) S' r
      linarith

/-- After our (legal, safe) reply and our flips, the stored game is in good shape. -/
theorem lg_goodGame_after_reply {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {e : ℕ} {x : BitString}
    {X : Finset BitString} {m : ℕ} {h h'' : BitString → ℕ} {st₁ : GState} {R : Finset BitString}
    (hL : LegalMove (gameOfF A (γ e).1 (γ e).2 x h ((2 : ℝ)⁻¹ ^ m) X) st₁ R)
    (hS : SafeFor (gameOfF A (γ e).1 (γ e).2 x h ((2 : ℝ)⁻¹ ^ m) X) st₁.yesTurn
      (applyMove (gameOfF A (γ e).1 (γ e).2 x h ((2 : ℝ)⁻¹ ^ m) X) st₁ R))
    (hside : st₁.yesTurn = true ↔ x ∉ A)
    (hXQ : X ⊆ qsetF (γ e).1 (γ e).2 x)
    (hnr : ∀ z ∈ st₁.S, h z < z.length)
    (hY : 0 ≤ st₁.scoreY) (hN : 0 ≤ st₁.scoreN) (hm : 7 ≤ m)
    (h3 : ∀ z, 3 ≤ h z)
    (hle : ∀ z, h'' z ≤ h z) (heq : ∀ z, z ∉ R \ st₁.S → h'' z = h z)
    (hflip : ∀ z ∈ R \ st₁.S, h'' z ≤ z.length - 4 + 3) :
    LGood A γ h'' e
      (x, X, m, applyMove (gameOfF A (γ e).1 (γ e).2 x h ((2 : ℝ)⁻¹ ^ m) X) st₁ R) := by
  obtain ⟨h1, h2, h3'⟩ := hL
  have hmc0 := moveCost_nonneg (gameOfF A (γ e).1 (γ e).2 x h ((2 : ℝ)⁻¹ ^ m) X) st₁.S R
  have hε : (2 : ℝ)⁻¹ ^ m < 1 / 8 := by
    calc (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ 7 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ < 1 / 8 := by norm_num
  have hmc : moveCost (gameOfF A (γ e).1 (γ e).2 x h ((2 : ℝ)⁻¹ ^ m) X) st₁.S R ≤
      (2 : ℝ)⁻¹ ^ m := by
    change (if st₁.yesTurn then _ ≤ (2 : ℝ)⁻¹ ^ m else _ ≤ (2 : ℝ)⁻¹ ^ m) at h3'
    split_ifs at h3' <;> linarith
  have hturn : (!(applyMove (gameOfF A (γ e).1 (γ e).2 x h ((2 : ℝ)⁻¹ ^ m) X) st₁ R).yesTurn) =
      st₁.yesTurn := by
    simp [applyMove]
  refine ⟨?_, h2, hXQ, ?_, ?_, ?_, hm, ?_⟩
  · change (!st₁.yesTurn) = false ↔ x ∉ A
    rw [← hside]; cases st₁.yesTurn <;> simp
  · intro z hz
    change z ∈ R at hz
    by_cases hzS : z ∈ st₁.S
    · exact lt_of_le_of_lt (hle z) (hnr z hzS)
    · have hzT : z ∈ R \ st₁.S := Finset.mem_sdiff.2 ⟨hz, hzS⟩
      have hfc := lg_flipCost_le_moveCost (gameOfF A (γ e).1 (γ e).2 x h ((2 : ℝ)⁻¹ ^ m) X)
        st₁.S R z hzT
      have h4 := lg_four_le_length_of_flipCost
        (gameOfF A (γ e).1 (γ e).2 x h ((2 : ℝ)⁻¹ ^ m) X) z (h3 z) (by linarith)
      have := hflip z hzT
      omega
  · change 0 ≤ (if st₁.yesTurn then st₁.scoreY + _ else st₁.scoreY)
    split_ifs <;> linarith
  · change 0 ≤ (if st₁.yesTurn then st₁.scoreN else st₁.scoreN + _)
    split_ifs <;> linarith
  · refine lg_safeFor_gameOf_transfer (γ e).1 (γ e).2 x h h'' _ X R (fun z _ => hle z)
      (fun z _ hz => by rw [heq z (fun hz' => hz (Finset.mem_sdiff.1 hz').1)]) _ _
      (by rw [hturn]; exact hS) subset_rfl h2 rfl rfl ?_ ?_
    · have : ∑ z ∈ X \ R, ((2 : ℝ)⁻¹ ^ h'' z - (2 : ℝ)⁻¹ ^ h z) = 0 :=
        Finset.sum_eq_zero fun z hz => by
          rw [heq z (fun hz' => (Finset.mem_sdiff.1 hz).2 (Finset.mem_sdiff.1 hz').1)]; ring
      change _ + ∑ z ∈ X \ R, ((2 : ℝ)⁻¹ ^ h'' z - (2 : ℝ)⁻¹ ^ h z) ≤ _
      rw [this, add_zero]
    · split_ifs <;> exact le_rfl

end Kolmogorov.RandomStrings
