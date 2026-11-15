/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Tauto

/-!
# Finite weighted deletion games (§4.1.1 and §4.1.2 of the paper)

A position is a finite set `A` of alive strings together with the two budgets.  Each player deletes
any subset of the alive strings, paying its total weight.  The opponent moves first, a move may be
empty (a pass), and the play ends when both players pass in a row.  Deletion is irreversible, so
nonempty moves strictly shrink `A`.

`Wins w T A a b`: *moving second, with budget `b`, we can force the final position into `T`, against
an opponent with budget `a`*.  This is the paper's `G(a, b)` with the target as a parameter.

The double-pass rule is faithful to the real construction, where the opponent may always move
later: `Wins` at a position quantifies over all opponent moves, so it stays available after a
double pass (see `wins_iff`).

## Results (all proved here)

* `wins_iff` (the recursive equation), `Wins.mono_budget`, `Wins.mono_target`.
* `firstWins_of_wins`, `firstWins_of_move`, `wins_of_firstWins`: moving second is exactly as good as
  moving first with the same budgets.  This is the paper's remark that "turn order is not
  important".
* `wins_or_compl` and `not_wins_and_compl`: symmetric determinacy, with its real hypothesis (equal
  budgets).  `G(a, a)` forces exactly one of `T`, `¬T`.
* `Wins.after_opponent` (**bishop lemma**, §4.1.2): if we have not answered, a winning position for
  `G(a, b)` stays winning for `G(a - λ, b)` after unanswered opponent moves of total weight `λ`.
* `Wins.pass_response`: the answer to a pass, the only way a strategy moves when the opponent is
  silent.
* `wins_zero_game`: a budget below every weight gives the zero game, decided by the current
  position.
* `wins_restrict_iff`: strings the target ignores do not matter (used for compatibility of the
  `n`-bit and `(n+1)`-bit games).
* `wins_scale_iff`: only the ratio of weights and budgets matters, so the choice of unit is
  harmless.

Weights are natural numbers: the construction measures everything in units of `2 ^ (-N)`, so that
the game is a finite object (see `Construction.lean`).
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

variable {α : Type*} [DecidableEq α]

/-- The total weight of a set of strings. -/
def cost (w : α → ℕ) (m : Finset α) : ℕ := ∑ τ ∈ m, w τ

omit [DecidableEq α] in
/-- The cost is monotone under inclusion. -/
theorem cost_mono (w : α → ℕ) {m m' : Finset α} (h : m ⊆ m') : cost w m ≤ cost w m' :=
  Finset.sum_le_sum_of_subset h

omit [DecidableEq α] in
/-- The empty move costs nothing. -/
@[simp] theorem cost_empty (w : α → ℕ) : cost w (∅ : Finset α) = 0 := rfl

/-- The game value with fuel, by recursion on the number of remaining nonempty moves.  See
`Wins`. -/
def WinsF (w : α → ℕ) (T : Finset α → Prop) : ℕ → Finset α → ℕ → ℕ → Prop
  | 0, A, _, _ => T A
  | n + 1, A, a, b =>
    ∀ m ∈ A.powerset, cost w m ≤ a → ∃ p ∈ (A \ m).powerset, cost w p ≤ b ∧
      if m = ∅ ∧ p = ∅ then T A else WinsF w T n ((A \ m) \ p) (a - cost w m) (b - cost w p)

/-- `G(a, b)` at the position `A` with target `T`: moving second with budget `b` against budget `a`,
we can force the final position into `T`. -/
def Wins (w : α → ℕ) (T : Finset α → Prop) (A : Finset α) (a b : ℕ) : Prop :=
  WinsF w T A.card A a b

/-- The value of the game is decidable, by exhausting the finitely many plays.  This instance is
what the stage construction runs.  Its effectivity in the sense of `Computable` is proved
separately (`forces_computable` in `Verification.lean`, from `Effectivity/GameTable.lean`). -/
instance decidableWinsF (w : α → ℕ) (T : Finset α → Prop) [DecidablePred T] :
    (n : ℕ) → (A : Finset α) → (a b : ℕ) → Decidable (WinsF w T n A a b)
  | 0, A, _, _ => inferInstanceAs (Decidable (T A))
  | n + 1, A, a, b => by
    have := decidableWinsF w T n
    change Decidable (∀ m ∈ A.powerset, cost w m ≤ a → ∃ p ∈ (A \ m).powerset, cost w p ≤ b ∧
      if m = ∅ ∧ p = ∅ then T A else WinsF w T n ((A \ m) \ p) (a - cost w m) (b - cost w p))
    infer_instance

instance decidableWins (w : α → ℕ) (T : Finset α → Prop) [DecidablePred T] (A : Finset α)
    (a b : ℕ) : Decidable (Wins w T A a b) :=
  decidableWinsF w T A.card A a b

/-- A round with a nonempty move shrinks the position: if `m ⊆ A`, `p ⊆ A \ m` and `m`, `p` are not
both empty, then `(A \ m) \ p` has fewer elements than `A`.  This drives the inductions on the size
of a position. -/
theorem card_sdiff_sdiff_lt {A m p : Finset α} (hm : m ⊆ A) (hp : p ⊆ A \ m)
    (h : ¬(m = ∅ ∧ p = ∅)) : ((A \ m) \ p).card < A.card := by
  have hsub : (A \ m) \ p ⊆ A := fun x hx => (mem_sdiff.1 (mem_sdiff.1 hx).1).1
  refine card_lt_card ⟨hsub, fun hsup => h ?_⟩
  constructor
  · refine eq_empty_of_forall_notMem fun x hx => ?_
    exact (mem_sdiff.1 (mem_sdiff.1 (hsup (hm hx))).1).2 hx
  · refine eq_empty_of_forall_notMem fun x hx => ?_
    have hxA := (mem_sdiff.1 (hp hx)).1
    exact (mem_sdiff.1 (hsup hxA)).2 hx

/-- On the empty position nobody can move: with any fuel, the game value is the target at `∅`. -/
theorem winsF_empty (w : α → ℕ) (T : Finset α → Prop) (a b : ℕ) :
    ∀ n, WinsF w T n ∅ a b ↔ T ∅
  | 0 => Iff.rfl
  | n + 1 => by
    constructor
    · intro h
      obtain ⟨p, hp, -, hT⟩ := h ∅ (by simp) (by simp)
      have hp0 : p = ∅ := by simpa using hp
      subst hp0
      simpa using hT
    · intro hT m hm _
      have hm0 : m = ∅ := by simpa using hm
      subst hm0
      exact ⟨∅, by simp, by simp, by simpa using hT⟩

/-- Fuel beyond the size of the position does not matter. -/
theorem winsF_fuel (w : α → ℕ) (T : Finset α → Prop) :
    ∀ (n n' : ℕ) (A : Finset α) (a b : ℕ), A.card ≤ n → A.card ≤ n' →
      (WinsF w T n A a b ↔ WinsF w T n' A a b) := by
  intro n
  induction n with
  | zero =>
    intro n' A a b h _
    have : A = ∅ := card_eq_zero.1 (by omega)
    subst this
    rw [winsF_empty, winsF_empty]
  | succ k ih =>
    intro n' A a b h h'
    cases n' with
    | zero =>
      have : A = ∅ := card_eq_zero.1 (by omega)
      subst this
      rw [winsF_empty, winsF_empty]
    | succ k' =>
      simp only [WinsF]
      refine forall₂_congr fun m hm => imp_congr_right fun _ => exists_congr fun p =>
        and_congr_right fun hp => and_congr_right fun _ => ?_
      split_ifs with hz
      · rfl
      · have := card_sdiff_sdiff_lt (mem_powerset.1 hm) (mem_powerset.1 hp) hz
        exact ih k' _ _ _ (by omega) (by omega)

/-- **The recursive equation of the game.** -/
theorem wins_iff {w : α → ℕ} {T : Finset α → Prop} {A : Finset α} {a b : ℕ} :
    Wins w T A a b ↔ ∀ m, m ⊆ A → cost w m ≤ a → ∃ p, p ⊆ A \ m ∧ cost w p ≤ b ∧
      if m = ∅ ∧ p = ∅ then T A else Wins w T ((A \ m) \ p) (a - cost w m) (b - cost w p) := by
  rw [Wins, winsF_fuel w T A.card (A.card + 1) A a b le_rfl (by omega)]
  simp only [WinsF, mem_powerset]
  refine forall₂_congr fun m hm => imp_congr_right fun _ => exists_congr fun p =>
    and_congr_right fun hp => and_congr_right fun _ => ?_
  split_ifs with hz
  · rfl
  · have := card_sdiff_sdiff_lt hm hp hz
    exact winsF_fuel w T _ _ _ _ _ (by omega) le_rfl

/-- More budget for us, less for the opponent. -/
theorem Wins.mono_budget {w : α → ℕ} {T : Finset α → Prop} {A : Finset α} {a b a' b' : ℕ}
    (h : Wins w T A a b) (ha : a' ≤ a) (hb : b ≤ b') : Wins w T A a' b' := by
  induction hn : A.card using Nat.strong_induction_on generalizing A a b a' b' with
  | _ n ih =>
    rw [wins_iff] at h ⊢
    intro m hm hc
    obtain ⟨p, hp, hcp, hif⟩ := h m hm (hc.trans ha)
    refine ⟨p, hp, hcp.trans hb, ?_⟩
    split_ifs at hif ⊢ with hz
    · exact hif
    · have := card_sdiff_sdiff_lt hm hp hz
      exact ih _ (by omega) hif (Nat.sub_le_sub_right ha _) (Nat.sub_le_sub_right hb _) rfl

/-- A bigger target is easier. -/
theorem Wins.mono_target {w : α → ℕ} {T T' : Finset α → Prop} {A : Finset α} {a b : ℕ}
    (h : Wins w T A a b) (hT : ∀ B, T B → T' B) : Wins w T' A a b := by
  induction hn : A.card using Nat.strong_induction_on generalizing A a b with
  | _ n ih =>
    rw [wins_iff] at h ⊢
    intro m hm hc
    obtain ⟨p, hp, hcp, hif⟩ := h m hm hc
    refine ⟨p, hp, hcp, ?_⟩
    split_ifs at hif ⊢ with hz
    · exact hT _ hif
    · have := card_sdiff_sdiff_lt hm hp hz
      exact ih _ (by omega) hif rfl

/-- The answer to a pass. -/
theorem Wins.pass_response {w : α → ℕ} {T : Finset α → Prop} {A : Finset α} {a b : ℕ}
    (h : Wins w T A a b) :
    ∃ p, p ⊆ A ∧ cost w p ≤ b ∧ ((p = ∅ ∧ T A) ∨ (p ≠ ∅ ∧ Wins w T (A \ p) a (b - cost w p))) := by
  obtain ⟨p, hp, hc, hif⟩ := wins_iff.1 h ∅ (empty_subset _) (by simp)
  have hpA : p ⊆ A := by simpa using hp
  refine ⟨p, hpA, hc, ?_⟩
  by_cases hp0 : p = ∅
  · subst hp0
    exact Or.inl ⟨rfl, by simpa using hif⟩
  · refine Or.inr ⟨hp0, ?_⟩
    simpa [hp0] using hif

/-! ### Moving first -/

/-- Moving first with budget `mine` against budget `opp`, we can force `T`: the opponent, moving
second, cannot force the complement. -/
def FirstWins (w : α → ℕ) (T : Finset α → Prop) (A : Finset α) (mine opp : ℕ) : Prop :=
  ¬ Wins w (fun B => ¬ T B) A mine opp

/-- The recursive equation for moving first. -/
theorem firstWins_iff {w : α → ℕ} {T : Finset α → Prop} {A : Finset α} {mine opp : ℕ} :
    FirstWins w T A mine opp ↔ ∃ p, p ⊆ A ∧ cost w p ≤ mine ∧ ∀ q, q ⊆ A \ p → cost w q ≤ opp →
      if p = ∅ ∧ q =
          ∅ then T A else FirstWins w T ((A \ p) \ q) (mine - cost w p) (opp - cost w q) := by
  unfold FirstWins
  rw [wins_iff]
  constructor
  · intro h
    by_contra hcon
    refine h fun m hm hc => ?_
    by_contra hno
    refine hcon ⟨m, hm, hc, fun q hq hcq => ?_⟩
    by_contra hbad
    refine hno ⟨q, hq, hcq, ?_⟩
    split_ifs at hbad ⊢ with hz
    · exact hbad
    · exact not_not.1 hbad
  · rintro ⟨p, hp, hc, hall⟩ hw
    obtain ⟨q, hq, hcq, hif⟩ := hw p hp hc
    have := hall q hq hcq
    split_ifs at this hif with hz
    · exact hif this
    · exact this hif

/-- First with a nonempty move: if after our move `p` we win moving second, we win moving first. -/
theorem firstWins_of_move {w : α → ℕ} {T : Finset α → Prop} :
    ∀ (n : ℕ) (A : Finset α), A.card = n → ∀ (mine opp : ℕ),
      (∀ p, p ⊆ A → p ≠ ∅ → cost w p ≤ mine → Wins w T (A \ p) opp (mine - cost w p) →
        FirstWins w T A mine opp) ∧
      (Wins w T A opp mine → FirstWins w T A mine opp) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA mine opp
    have hmove : ∀ p, p ⊆ A → p ≠ ∅ → cost w p ≤ mine →
        Wins w T (A \ p) opp (mine - cost w p) → FirstWins w T A mine opp := by
      intro p hp hp0 hcp hw
      refine firstWins_iff.2 ⟨p, hp, hcp, fun q hq hcq => ?_⟩
      have hne : ¬(p = ∅ ∧ q = ∅) := fun h => hp0 h.1
      rw [ite_eq_right hne]
      have hcard : ((A \ p) \ q).card < n := hA ▸ card_sdiff_sdiff_lt hp hq hne
      by_cases hq0 : q = ∅
      · subst hq0
        have h1 : (A \ p).card < n := by simpa using hcard
        simpa using (ih _ h1 (A \ p) rfl (mine - cost w p) opp).2 hw
      · obtain ⟨r, hr, hcr, hif⟩ := wins_iff.1 hw q hq hcq
        have hne' : ¬(q = ∅ ∧ r = ∅) := fun h => hq0 h.1
        rw [ite_eq_right hne'] at hif
        by_cases hr0 : r = ∅
        · subst hr0
          simp only [sdiff_empty, cost_empty, Nat.sub_zero] at hif
          exact (ih _ hcard ((A \ p) \ q) rfl (mine - cost w p) (opp - cost w q)).2 hif
        · exact (ih _ hcard ((A \ p) \ q) rfl (mine - cost w p) (opp - cost w q)).1 r hr hr0 hcr hif
    refine ⟨hmove, fun hw => ?_⟩
    obtain ⟨p₀, hp₀, hc₀, hif₀⟩ := wins_iff.1 hw ∅ (empty_subset _) (by simp)
    have hp₀A : p₀ ⊆ A := by simpa using hp₀
    by_cases hp0 : p₀ = ∅
    · subst hp0
      have hTA : T A := by simpa using hif₀
      refine firstWins_iff.2 ⟨∅, empty_subset _, by simp, fun q hq hcq => ?_⟩
      by_cases hq0 : q = ∅
      · subst hq0
        simpa using hTA
      · have hne : ¬((∅ : Finset α) = ∅ ∧ q = ∅) := fun h => hq0 h.2
        rw [ite_eq_right hne]
        have hqA : q ⊆ A := by simpa using hq
        obtain ⟨r, hr, hcr, hif⟩ := wins_iff.1 hw q hqA hcq
        have hne' : ¬(q = ∅ ∧ r = ∅) := fun h => hq0 h.1
        rw [ite_eq_right hne'] at hif
        have hcard : (A \ q).card < n := by
          have := card_sdiff_sdiff_lt hqA (empty_subset _) (fun h => hq0 h.1)
          simpa [hA] using this
        simp only [sdiff_empty, cost_empty, Nat.sub_zero]
        by_cases hr0 : r = ∅
        · subst hr0
          simp only [sdiff_empty, cost_empty, Nat.sub_zero] at hif
          exact (ih _ hcard (A \ q) rfl mine (opp - cost w q)).2 hif
        · exact (ih _ hcard (A \ q) rfl mine (opp - cost w q)).1 r hr hr0 hcr hif
    · have hne : ¬((∅ : Finset α) = ∅ ∧ p₀ = ∅) := fun h => hp0 h.2
      rw [ite_eq_right hne] at hif₀
      simp only [sdiff_empty, cost_empty, Nat.sub_zero] at hif₀
      exact hmove p₀ hp₀A hp0 hc₀ hif₀

/-- Moving second implies moving first. -/
theorem firstWins_of_wins {w : α → ℕ} {T : Finset α → Prop} {A : Finset α} {mine opp : ℕ}
    (h : Wins w T A opp mine) : FirstWins w T A mine opp :=
  (firstWins_of_move _ A rfl mine opp).2 h

/-- **Tempo.**  Moving first implies moving second: treat the opponent's first move as the reply to
our first move, and play both of our moves in one. -/
theorem wins_of_firstWins {w : α → ℕ} {T : Finset α → Prop} {A : Finset α} {mine opp : ℕ}
    (h : FirstWins w T A mine opp) : Wins w T A opp mine := by
  induction hn : A.card using Nat.strong_induction_on generalizing A mine opp with
  | _ n ih =>
    obtain ⟨p, hp, hcp, hall⟩ := firstWins_iff.1 h
    refine wins_iff.2 fun m hm hcm => ?_
    have hqsub : m \ p ⊆ A \ p := sdiff_subset_sdiff hm (Subset.refl _)
    have hcq : cost w (m \ p) ≤ cost w m := cost_mono w sdiff_subset
    have hcr : cost w (p \ m) ≤ cost w p := cost_mono w sdiff_subset
    have hrsub : p \ m ⊆ A \ m := sdiff_subset_sdiff hp (Subset.refl _)
    have hstep := hall (m \ p) hqsub (hcq.trans hcm)
    refine ⟨p \ m, hrsub, hcr.trans hcp, ?_⟩
    by_cases hz : p = ∅ ∧ m \ p = ∅
    · obtain ⟨hp0, hq0⟩ := hz
      subst hp0
      have hm0 : m = ∅ := by simpa using hq0
      subst hm0
      simpa using hstep
    · rw [ite_eq_right hz] at hstep
      have hne : ¬(m = ∅ ∧ p \ m = ∅) := by
        rintro ⟨hm0, hr0⟩
        subst hm0
        exact hz ⟨by simpa using hr0, by simp⟩
      rw [ite_eq_right hne]
      have hset : (A \ m) \ (p \ m) = (A \ p) \ (m \ p) := by
        ext x
        simp only [mem_sdiff]
        tauto
      rw [hset]
      have hcard := card_sdiff_sdiff_lt hp hqsub hz
      have hw := ih _ (by omega) hstep rfl
      exact hw.mono_budget (Nat.sub_le_sub_left hcq _) (Nat.sub_le_sub_left hcr _)

/-! ### Symmetric determinacy -/

/-- **Symmetric determinacy.**  In a symmetric game we can force `T` or its complement.  The equal
budgets are essential: tempo swaps the roles, and only equal budgets return the same game. -/
theorem wins_or_compl (w : α → ℕ) (T : Finset α → Prop) (A : Finset α) (a : ℕ) :
    Wins w T A a a ∨ Wins w (fun B => ¬ T B) A a a := by
  classical
  by_cases h : Wins w T A a a
  · exact Or.inl h
  · refine Or.inr (wins_of_firstWins ?_)
    unfold FirstWins
    simpa only [not_not] using h

/-- In a symmetric game we cannot force both `T` and its complement. -/
theorem not_wins_and_compl {w : α → ℕ} {T : Finset α → Prop} {A : Finset α} {a : ℕ}
    (h : Wins w T A a a) : ¬ Wins w (fun B => ¬ T B) A a a :=
  firstWins_of_wins h

/-! ### The bishop lemma -/

/-- **Bishop lemma (§4.1.2).**  While we do not answer, all the opponent's moves count as one first
move: after unanswered moves `m` of weight `λ`, a position winning for `G(a, b)` is winning for
`G(a - λ, b)`, for the same target. -/
theorem Wins.after_opponent {w : α → ℕ} {T : Finset α → Prop} {A m : Finset α} {a b : ℕ}
    (h : Wins w T A a b) (hm : m ⊆ A) (hc : cost w m ≤ a) :
    Wins w T (A \ m) (a - cost w m) b := by
  by_cases hm0 : m = ∅
  · subst hm0
    simpa using h
  obtain ⟨p, hp, hcp, hif⟩ := wins_iff.1 h m hm hc
  have hne : ¬(m = ∅ ∧ p = ∅) := fun h => hm0 h.1
  rw [ite_eq_right hne] at hif
  by_cases hp0 : p = ∅
  · subst hp0
    simpa using hif
  · exact wins_of_firstWins
      ((firstWins_of_move _ (A \ m) rfl b (a - cost w m)).1 p hp hp0 hcp hif)

/-! ### The zero game -/

omit [DecidableEq α] in
/-- If every string of `A` weighs more than `a`, a move in `A` costing at most `a` is empty. -/
theorem eq_empty_of_cost_le {w : α → ℕ} {A m : Finset α} {a : ℕ} (hsmall : ∀ τ ∈ A, a < w τ)
    (hm : m ⊆ A) (hc : cost w m ≤ a) : m = ∅ := by
  refine eq_empty_of_forall_notMem fun τ hτ => ?_
  have h1 : w τ ≤ cost w m := Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _) hτ
  have h2 := hsmall τ (hm hτ)
  omega

/-- **The zero game.**  If both budgets are below every weight on the board, nobody can move and the
game is decided by the current position. -/
theorem wins_zero_game {w : α → ℕ} {T : Finset α → Prop} {A : Finset α} {a b : ℕ}
    (ha : ∀ τ ∈ A, a < w τ) (hb : ∀ τ ∈ A, b < w τ) : Wins w T A a b ↔ T A := by
  constructor
  · intro h
    obtain ⟨p, hp, hc, hif⟩ := wins_iff.1 h ∅ (empty_subset _) (by simp)
    have hp0 : p = ∅ := eq_empty_of_cost_le hb (by simpa using hp) hc
    subst hp0
    simpa using hif
  · intro hT
    refine wins_iff.2 fun m hm hc => ?_
    have hm0 : m = ∅ := eq_empty_of_cost_le ha hm hc
    subst hm0
    exact ⟨∅, empty_subset _, by simp, by simpa using hT⟩

/-! ### Strings the target ignores -/

/-- One direction of `wins_restrict_iff`, by simulation. -/
theorem wins_of_wins_inter {w : α → ℕ} {T : Finset α → Prop} {A Q : Finset α} {a b : ℕ}
    (h : Wins w T (A ∩ Q) a b) : Wins w (fun B => T (B ∩ Q)) A a b := by
  induction hn : A.card using Nat.strong_induction_on generalizing A a b with
  | _ n ih =>
    refine wins_iff.2 fun m hm hc => ?_
    have hm₀ : m ∩ Q ⊆ A ∩ Q := inter_subset_inter_right hm
    have hcm₀ : cost w (m ∩ Q) ≤ cost w m := cost_mono w inter_subset_left
    obtain ⟨p, hp, hcp, hif⟩ := wins_iff.1 h (m ∩ Q) hm₀ (hcm₀.trans hc)
    have hpQ : p ⊆ Q := fun x hx => (mem_inter.1 (mem_sdiff.1 (hp hx)).1).2
    have hpA : p ⊆ A \ m := by
      intro x hx
      have hx' := mem_sdiff.1 (hp hx)
      refine mem_sdiff.2 ⟨(mem_inter.1 hx'.1).1, fun hxm => hx'.2 ?_⟩
      exact mem_inter.2 ⟨hxm, hpQ hx⟩
    refine ⟨p, hpA, hcp, ?_⟩
    by_cases hz : m = ∅ ∧ p = ∅
    · obtain ⟨hm0, hp0⟩ := hz
      subst hm0 hp0
      simpa using hif
    · rw [ite_eq_right hz]
      have hcard := card_sdiff_sdiff_lt hm hpA hz
      have hset : ((A \ m) \ p) ∩ Q = ((A ∩ Q) \ (m ∩ Q)) \ p := by
        ext x
        simp only [mem_inter, mem_sdiff]
        tauto
      refine ih _ (by omega) ?_ rfl
      rw [hset]
      by_cases hz' : m ∩ Q = ∅ ∧ p = ∅
      · obtain ⟨hm0, hp0⟩ := hz'
        subst hp0
        rw [hm0]
        simpa using h.mono_budget (Nat.sub_le a (cost w m)) le_rfl
      · rw [ite_eq_right hz'] at hif
        exact hif.mono_budget (Nat.sub_le_sub_left hcm₀ _) le_rfl

/-- **Strings the target ignores do not matter.**  If the target depends only on `B ∩ Q`, the game
on `A` has the value of the game on `A ∩ Q`.  The direction not given by simulation goes through
determinacy with the roles exchanged. -/
theorem wins_restrict_iff {w : α → ℕ} {T : Finset α → Prop} {A Q : Finset α} {a b : ℕ} :
    Wins w (fun B => T (B ∩ Q)) A a b ↔ Wins w T (A ∩ Q) a b := by
  classical
  refine ⟨fun h => ?_, wins_of_wins_inter⟩
  by_contra hno
  have h1 : Wins w (fun B => ¬ T B) (A ∩ Q) b a := by
    refine wins_of_firstWins ?_
    unfold FirstWins
    simpa only [not_not] using hno
  have h2 : Wins w (fun B => ¬ T (B ∩ Q)) A b a := wins_of_wins_inter h1
  exact firstWins_of_wins h2 (by simpa only [not_not] using h)

/-- Equivalent targets give the same game. -/
theorem wins_congr_target {w : α → ℕ} {T T' : Finset α → Prop} {A : Finset α} {a b : ℕ}
    (h : ∀ B, T B ↔ T' B) : Wins w T A a b ↔ Wins w T' A a b :=
  ⟨fun hw => hw.mono_target fun B hB => (h B).1 hB, fun hw => hw.mono_target fun B hB => (h B).2 hB⟩

/-- Weights matter only on the board. -/
theorem wins_congr_weight {w w' : α → ℕ} {T : Finset α → Prop} {A : Finset α} {a b : ℕ}
    (h : ∀ τ ∈ A, w τ = w' τ) : Wins w T A a b ↔ Wins w' T A a b := by
  have hcost : ∀ {B m : Finset α}, B ⊆ A → m ⊆ B → cost w m = cost w' m := fun hB hm =>
    Finset.sum_congr rfl fun τ hτ => h τ (hB (hm hτ))
  induction hn : A.card using Nat.strong_induction_on generalizing A a b with
  | _ n ih =>
    rw [wins_iff, wins_iff]
    refine forall₂_congr fun m hm => ?_
    rw [hcost (Subset.refl A) hm]
    refine imp_congr_right fun _ => exists_congr fun p => and_congr_right fun hp => ?_
    have hpA : p ⊆ A := hp.trans sdiff_subset
    rw [hcost (Subset.refl A) hpA]
    refine and_congr_right fun _ => ?_
    split_ifs with hz
    · rfl
    · have hcard := card_sdiff_sdiff_lt hm hp hz
      have hsub : (A \ m) \ p ⊆ A := sdiff_subset.trans sdiff_subset
      exact ih _ (by omega) (fun τ hτ => h τ (hsub hτ))
        (fun hB hm' => hcost (hB.trans hsub) hm') rfl

/-! ### Change of unit -/

/-- Only the ratio of weights and budgets matters. -/
theorem wins_scale_iff {w : α → ℕ} {T : Finset α → Prop} {A : Finset α} {a b k : ℕ} (hk : 0 < k) :
    Wins (fun τ => k * w τ) T A (k * a) (k * b) ↔ Wins w T A a b := by
  have hcost : ∀ m : Finset α, cost (fun τ => k * w τ) m = k * cost w m := by
    intro m
    simp [cost, Finset.mul_sum]
  have hle : ∀ m : Finset α, ∀ c, k * cost w m ≤ k * c ↔ cost w m ≤ c := fun m c =>
    Nat.mul_le_mul_left_iff hk
  induction hn : A.card using Nat.strong_induction_on generalizing A a b with
  | _ n ih =>
    rw [wins_iff, wins_iff]
    refine forall₂_congr fun m hm => ?_
    rw [hcost, hle]
    refine imp_congr_right fun _ => exists_congr fun p => and_congr_right fun hp => ?_
    rw [hcost, hle]
    refine and_congr_right fun _ => ?_
    split_ifs with hz
    · rfl
    · have := card_sdiff_sdiff_lt hm hp hz
      rw [← Nat.mul_sub, ← Nat.mul_sub]
      exact ih _ (by omega) rfl

end Kolmogorov.RandomStrings.TTMeet
