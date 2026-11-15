/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.RunInvariants

/-!
# The final oracles and the requirements

The final oracles `finalR I j` are defined here, from the limits of the stage data.  They are not
used by the stage transition.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

/-- `X_s` converges to `X`. -/
def Approximates (I : Input) (X : Set Str) : Prop :=
  ∀ x, ∃ s₀, ∀ s ≥ s₀, (I.X s x = true ↔ x ∈ X)

/-- The strings compressed by us on board `j`, over the whole construction. -/
def finalOurs (I : Input) (j : Fin 3) : Set Str := {τ | ∃ s, τ ∈ oursAt I j s}

/-- **The final oracle** on board `j`.  It is a limit, and it is not available to the
construction. -/
def finalR (I : Input) (j : Fin 3) : Set Str :=
  {τ | (∀ s, I.opp s τ = false) ∧ τ ∉ finalOurs I j}

/-- The requirement `R_i` stops acting: the last action of Remark 4.2 is bounded. -/
def StopsActing (I : Input) (i : ℕ) : Prop := ∃ s₀, ∀ s, (rsAt I s i).lastActed ≤ s₀

/-- **The requirement `R_i` is satisfied**: `¬ (Ψ_i^{R₀} = Ψ_i^{R₁} = Ψ_i^{R₂} = X)`, in the three
ways listed in §4 of the paper: `Ψ_i` is not a total reduction, or (i) two boards disagree, or (ii)
the value differs from `X`. -/
def ReqSatisfied (I : Input) (X : Set Str) (i : ℕ) : Prop :=
  ¬ IsTotalGen i ∨
    (∃ k s t j j', tableAt i k s = some t ∧ ¬ (t.Accepts (finalR I j) ↔ t.Accepts (finalR I j'))) ∨
    (∃ k s t j, tableAt i k s = some t ∧ ¬ (strOf k ∈ X ↔ t.Accepts (finalR I j)))

/-- From stage `s₀` on, Case 1 does not apply to `R_i`. -/
def NoReset (I : Input) (i s₀ : ℕ) : Prop :=
  ∀ s ≥ s₀, (Nat.unpair s).1 = i → mustReset I (stateAt I s) i (Nat.unpair s).2 (s + 1) = false

/-- A game of `R_i` runs forever from some stage on. -/
def Permanent (I : Input) (i : ℕ) : Prop :=
  ∃ s₀ start, ∀ s ≥ s₀, ∃ pl, (rsAt I s i).play = some pl ∧ pl.start = start

/-- The number of examined bits of `R_i` is unbounded. -/
def Unbounded (I : Input) (i : ℕ) : Prop := ∀ N, ∃ s, N ≤ (rsAt I s i).tables.length

/-- Finitely many strings of `finalOurs` are compressed at one stage. -/
theorem exists_stage_of_subset_finalOurs (I : Input) (j : Fin 3) (S : Finset Str)
    (h : ∀ τ ∈ S, τ ∈ finalOurs I j) : ∃ s, S ⊆ oursAt I j s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, empty_subset _⟩
  | insert a S _ ih =>
    obtain ⟨s, hs⟩ := ih fun τ hτ => h τ (mem_insert_of_mem hτ)
    obtain ⟨s', hs'⟩ := h a (mem_insert_self a S)
    refine ⟨max s s', insert_subset ?_ (hs.trans (oursAt_mono I j (le_max_left _ _)))⟩
    exact oursAt_mono I j (le_max_right _ _) hs'

section Structure

variable (I : Input)

/-- The examined tables are the actual tables of the enumeration. -/
theorem tables_spec (s i : ℕ) :
    tablesUpTo i s (rsAt I s i).tables.length = some (rsAt I s i).tables :=
  (reqWF_rsAt I s i).tables

/-- An agreed value is a vector of the current length. -/
theorem baseline_length {s i : ℕ} {bl : Baseline} (h : (rsAt I s i).baseline = some bl) :
    bl.σ.length = (rsAt I s i).tables.length :=
  (reqWF_rsAt I s i).baseline bl h

/-- While a game runs without a reset, no bit is added. -/
theorem tables_const_of_permanent {i : ℕ} (h : Permanent I i) :
    ∃ s₀, ∀ s ≥ s₀, (rsAt I s i).tables = (rsAt I s₀ i).tables := by
  obtain ⟨s₀, start, hs⟩ := h
  refine ⟨s₀, fun s hs₀ => ?_⟩
  induction s, hs₀ using Nat.le_induction with
  | base => rfl
  | succ s hle ih =>
    obtain ⟨pl, hpl, -⟩ := hs s hle
    obtain ⟨pl', hpl', -⟩ := hs (s + 1) (by omega)
    rw [tables_eq_of_play I hpl ⟨pl', hpl'⟩, ih]

end Structure

end Kolmogorov.RandomStrings.TTMeet
