/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Baseline

/-!
# Adaptive polynomial-time reductions are truth-table reductions

The existing class `PolyTimeOracle B` (`P^B`) is adaptive: the machine halts in polynomial time on
the actual oracle `B`, and may behave arbitrarily on other answers.  `ttReducible_of_polyTimeOracle`
turns it into a total computable table generator by unrolling all finite answer branches:

* the clock of the machine on the actual `B` bounds each branch, by `exists_clocked_of_polyTime`;
* the table queries `queryListCode m e x`, all strings that can be asked within the clock under
  *some* oracle;
* a row accepts iff the clocked machine accepts on the finite oracle of the row.  A fictitious
  branch that does not halt within the clock is rejected by default (`clockedOutcome`).

The converse is not claimed, and neither is any equality of classes: this is one inclusion, and
`P^B` is not the same class as `PolyTimeTT B`.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Kolmogorov

/-- The clause recording that the oracle agrees with the finite oracle `L` on the list `Q`. -/
def branchClause (Q L : List BitString) : Clause := Q.map fun z => (z, memStr z L)

/-- The table of the clocked coded machine `(decodeCode m, e)` on `x`. -/
def unrolledTable (m e : ℕ) (x : BitString) : TTable :=
  (allSub (queryListCode m e x)).flatMap fun L =>
    bif clockedOutcome m e L x then [branchClause (queryListCode m e x) L] else []

/-- The generator of `unrolledTable` is primitive recursive. -/
theorem unrolledTable_primrec (m e : ℕ) : Primrec (unrolledTable m e) := by
  have hQ : Primrec fun x : BitString => queryListCode m e x := by
    -- elaborate without the expected type: unifying against the tuple form unfolds `queryListCode`
    have h :=
      queryListCode_primrec.comp ((Primrec.const m).pair ((Primrec.const e).pair Primrec.id))
    exact h
  have hclause : Primrec fun r : (BitString × List BitString) × BitString =>
      (r.2, memStr r.2 r.1.2) :=
    Primrec.snd.pair (memStr_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
  have hbranch : Primrec fun r : BitString × List BitString =>
      branchClause (queryListCode m e r.1) r.2 :=
    Primrec.list_map (hQ.comp Primrec.fst) hclause.to₂
  have hout : Primrec fun r : BitString × List BitString => clockedOutcome m e r.2 r.1 := by
    have h := clockedOutcome_primrec.comp ((Primrec.const m).pair ((Primrec.const e).pair
      (Primrec.snd.pair Primrec.fst)))
    exact h
  have hinner : Primrec fun r : BitString × List BitString =>
      bif clockedOutcome m e r.2 r.1 then [branchClause (queryListCode m e r.1) r.2] else [] :=
    Primrec.cond hout (Primrec.list_cons.comp hbranch (Primrec.const [])) (Primrec.const [])
  exact Primrec.list_flatMap (allSub_primrec.comp hQ) hinner.to₂

/-- A branch clause holds iff the oracle agrees with the finite oracle on the list. -/
theorem holds_branchClause (Q L : List BitString) (B : Set BitString) :
    (branchClause Q L).holds (chi B) = true ↔ ∀ z ∈ Q, (z ∈ B ↔ z ∈ L) := by
  rw [Clause.holds_eq_true]
  simp only [branchClause, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun z _ => ?_
  rw [Bool.eq_iff_iff, chi_eq_true, memStr_iff]

/-- The table computes the clocked verdict on any oracle `B`: it is correct for the actual oracle,
and it needs no halting assumption for the other branches. -/
theorem unrolledTable_accepts (m e : ℕ) (x : BitString) (B : Set BitString) :
    (unrolledTable m e x).Accepts B ↔ ClockedAccepts (decodeCode m) e B x := by
  classical
  rw [TTable.Accepts, TTable.evalB_eq_true]
  simp only [unrolledTable, List.mem_flatMap]
  constructor
  · rintro ⟨c, ⟨L, -, hc⟩, hholds⟩
    cases hout : clockedOutcome m e L x
    · simp [hout] at hc
    · simp only [hout, Bool.cond_true, List.mem_singleton] at hc
      subst hc
      exact (clockedAccepts_iff_clockedOutcome m e x B L
        ((holds_branchClause _ _ _).1 hholds)).2 hout
  · intro h
    obtain ⟨L, hL, hLT⟩ := exists_allSub (queryListCode m e x)
      ((queryListCode m e x).toFinset.filter fun z => z ∈ B)
      fun z hz => List.mem_toFinset.1 (Finset.mem_filter.1 hz).1
    have hag : ∀ z ∈ queryListCode m e x, (z ∈ B ↔ z ∈ L) := by
      intro z hz
      rw [← List.mem_toFinset (l := L), hLT, Finset.mem_filter]
      exact ⟨fun hB => ⟨List.mem_toFinset.2 hz, hB⟩, fun h' => h'.2⟩
    have hout := (clockedAccepts_iff_clockedOutcome m e x B L hag).1 h
    refine ⟨branchClause (queryListCode m e x) L, ⟨L, hL, ?_⟩, (holds_branchClause _ _ _).2 hag⟩
    simp [hout]

/-- **The bridge.**  `P^B` is contained in the sets tt-reducible to `B`. -/
theorem ttReducible_of_polyTimeOracle {A B : Set BitString} (h : A ∈ PolyTimeOracle B) :
    TTReducible A B := by
  obtain ⟨c, e, hce⟩ := exists_clocked_of_polyTime B A h
  obtain ⟨m, rfl⟩ := decodeCode_surjective c
  exact ⟨unrolledTable m e, (unrolledTable_primrec m e).to_comp, fun x =>
    (hce x).trans (unrolledTable_accepts m e x B).symm⟩

end Kolmogorov.RandomStrings.TTMeet
