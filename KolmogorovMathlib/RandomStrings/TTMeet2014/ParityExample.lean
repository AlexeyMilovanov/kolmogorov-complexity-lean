/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Game

/-!
# Why the agreed value can change with no game in progress

This module records, with proofs, the game-theoretic core of the issue with Case 2 of the paper
described in `docs/random_strings_tt_meet_2014.md`, section 3.

Take a table computing the parity of the alive strings on a board of equal weights.  In a symmetric
game the second player can mirror each opponent move, so the forced value is the *current* parity
(`parity_forced`), at every budget, on every board with the same position, down to the zero game.
So all levels of the stack agree on the current parity, no split appears and no game is started.
One opponent move then flips the current parity on all three boards at once, and the symmetric value
flips with it (`symmetric_value_flips`), although we have not done anything.

The bishop lemma still applies: with the opponent's budget reduced by what was spent, the old value
is winning (the third component).  This asymmetric game is what the repaired Case 2 plays against
the new symmetric value.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

variable {α : Type*} [DecidableEq α]

/-- Unit weights. -/
abbrev unitW (_ : α) : ℕ := 1

omit [DecidableEq α] in
/-- With unit weights, the cost of a move is its number of strings. -/
theorem cost_unitW (m : Finset α) : cost unitW m = m.card := by
  simp [cost]

/-- **Mirroring.**  With unit weights, enough strings and at least the opponent's budget, the second
player forces the current parity, by answering every odd move with the deletion of one more
string. -/
theorem parity_forced {A : Finset α} {a b : ℕ} (hab : a ≤ b) (hcard : a + b ≤ A.card) :
    Wins unitW (fun B => B.card % 2 = A.card % 2) A a b := by
  suffices h : ∀ (n : ℕ) (A : Finset α), A.card = n → ∀ (a b r : ℕ), a ≤ b → a + b ≤ A.card →
      A.card % 2 = r → Wins unitW (fun B => B.card % 2 = r) A a b from
    h _ A rfl a b _ hab hcard rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA a b r hab hcard hr
    refine wins_iff.2 fun m hm hc => ?_
    rw [cost_unitW] at hc
    have hcm : (A \ m).card = A.card - m.card := card_sdiff_of_subset hm
    have hmle : m.card ≤ A.card := card_le_card hm
    by_cases hodd : m.card % 2 = 0
    · -- Even: pass.
      refine ⟨∅, empty_subset _, by simp, ?_⟩
      by_cases hm0 : m = ∅
      · subst hm0
        simpa using hr
      · have hne : ¬(m = ∅ ∧ (∅ : Finset α) = ∅) := fun h => hm0 h.1
        rw [ite_eq_right hne]
        simp only [sdiff_empty, cost_empty, Nat.sub_zero, cost_unitW]
        have hlt : (A \ m).card < n := by
          have : 0 < m.card := card_pos.2 (nonempty_iff_ne_empty.2 hm0)
          omega
        exact ih _ hlt _ rfl _ _ _ (by omega) (by omega) (by omega)
    · -- Odd: delete one more string.
      have hpos : 0 < m.card := by omega
      have hb : 0 < b := by omega
      have hne : (A \ m).Nonempty := by
        rw [← card_pos]
        omega
      obtain ⟨τ, hτ⟩ := hne
      refine ⟨{τ}, singleton_subset_iff.2 hτ, ?_, ?_⟩
      · rw [cost_unitW, card_singleton]
        omega
      · have hz : ¬(m = ∅ ∧ ({τ} : Finset α) = ∅) := fun h =>
          singleton_ne_empty τ h.2
        rw [ite_eq_right hz]
        simp only [cost_unitW, card_singleton]
        have hcard' : ((A \ m) \ {τ}).card = A.card - m.card - 1 := by
          rw [card_sdiff_of_subset (singleton_subset_iff.2 hτ), hcm, card_singleton]
        exact ih _ (by omega) _ rfl _ _ _ (by omega) (by omega) (by omega)

/-- **The symmetric value flips by one unanswered opponent move.**  Before the move, parity `p` is
forced at the budgets `(E, E)`.  After deleting one string with no answer:

1. the old parity is not forced at `(E, E)` any more, the new parity is;
2. the old parity is still forced at `(E - 1, E)` (the bishop lemma).

Since the opponent's moves are common to all boards, this happens on all boards at once when they
hold the same position. -/
theorem symmetric_value_flips {A : Finset α} {τ : α} (hτ : τ ∈ A) {E : ℕ} (hE : 1 ≤ E)
    (hcard : 2 * E + 1 ≤ A.card) :
    Wins unitW (fun B => B.card % 2 = A.card % 2) A E E ∧
      Wins unitW (fun B => B.card % 2 = (A \ {τ}).card % 2) (A \ {τ}) E E ∧
      ¬ Wins unitW (fun B => B.card % 2 = A.card % 2) (A \ {τ}) E E ∧
      Wins unitW (fun B => B.card % 2 = A.card % 2) (A \ {τ}) (E - 1) E := by
  have hc : (A \ {τ}).card = A.card - 1 := by
    rw [card_sdiff_of_subset (singleton_subset_iff.2 hτ), card_singleton]
  have hold := parity_forced (A := A) (a := E) (b := E) le_rfl (by omega)
  have hnew := parity_forced (A := A \ {τ}) (a := E) (b := E) le_rfl (by omega)
  refine ⟨hold, hnew, fun hbad => ?_, ?_⟩
  · refine not_wins_and_compl hnew (hbad.mono_target fun B hB hB' => ?_)
    rw [hB] at hB'
    omega
  · have := hold.after_opponent (m := {τ}) (singleton_subset_iff.2 hτ) (by
      rw [cost_unitW, card_singleton]
      omega)
    rwa [cost_unitW, card_singleton] at this

end Kolmogorov.RandomStrings.TTMeet
