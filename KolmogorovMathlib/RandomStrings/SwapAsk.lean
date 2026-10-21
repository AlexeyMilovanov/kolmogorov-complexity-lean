/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Game

/-!
# Swapping the answers of the oracle

The oracle `oracleOf T.fn K` of a position `K` of the game `G_{e,x}` is the *complement* of a
finite set: `oracleOf T.fn K = {z | z ∈ K ∪ T.bad}ᶜ` (`oracleOf_table`), where `T.bad` are the
strings made non-random by the table.  The existing simulations of clocked machines take a listed
oracle; the code transformation `OTMCode.swapAsk` (exchange the two branches of every `ask`)
turns a complemented oracle into a listed one: the runs correspond configuration by configuration
(`OTMCode.run_swapAsk`, through the explicit conversion `OTMCode.swapConfig`, since
`Config c.toOTM` and `Config c.swapAsk.toOTM` are different types), with the same asks, queries
and clocked verdicts (`askedAt_swapAsk`, `queries_swapAsk`, `clockedAccepts_swapAsk`).
-/

namespace Kolmogorov.RandomStrings

/-- Exchange the two branches of an `ask`. -/
def Act.swapAsk {Q : Type} : Act Q → Act Q
  | .step q a m => .step q a m
  | .push q b => .push q b
  | .ask q₁ q₂ => .ask q₂ q₁

/-- The machine `c` with the two branches of every `ask` exchanged. -/
def OTMCode.swapAsk (c : OTMCode) : OTMCode :=
  { c with δ := fun q a => (c.δ q a).swapAsk }

/-- A configuration of `c` as a configuration of `c.swapAsk` (the same states `Fin c.k`). -/
def OTMCode.swapConfig (c : OTMCode) (cf : Config c.toOTM) : Config c.swapAsk.toOTM :=
  ⟨cf.q, cf.tape, cf.head, cf.buf⟩

/-- The configuration `c.swapConfig cf` is halted if and only if `cf` is halted. -/
theorem OTMCode.halted_swapAsk_iff (c : OTMCode) (cf : Config c.toOTM) :
    Halted c.swapAsk.toOTM (c.swapConfig cf) ↔ Halted c.toOTM cf := Iff.rfl

/-- The transition function of `c.swapAsk` at `c.swapConfig cf` corresponds to
the transition function of `c` at `cf` with the branches of `ask` exchanged. -/
theorem OTMCode.swapAsk_δ (c : OTMCode) (cf : Config c.toOTM) :
    c.swapAsk.toOTM.δ (c.swapConfig cf).q ((c.swapConfig cf).tape (c.swapConfig cf).head) =
      (c.toOTM.δ cf.q (cf.tape cf.head)).swapAsk := rfl

/-- One step of `c.swapAsk` with the complemented oracle is the step of `c`. -/
theorem OTMCode.step_swapAsk (c : OTMCode) (B : Set BitString) (cf : Config c.toOTM) :
    step c.swapAsk.toOTM Bᶜ (c.swapConfig cf) = c.swapConfig (step c.toOTM B cf) := by
  by_cases hc : Halted c.toOTM cf
  · rw [step_of_halted _ _ _ hc, step_of_halted _ _ _ ((c.halted_swapAsk_iff cf).2 hc)]
  · have hc' : ¬ Halted c.swapAsk.toOTM (c.swapConfig cf) :=
      fun h => hc ((c.halted_swapAsk_iff cf).1 h)
    unfold step
    rw [ite_eq_right hc, ite_eq_right hc', OTMCode.swapAsk_δ]
    cases c.toOTM.δ cf.q (cf.tape cf.head) with
    | step q' a m => rfl
    | push q' b => rfl
    | ask qyes qno =>
      by_cases hb : cf.buf ∈ B <;> simp [hb, Act.swapAsk, OTMCode.swapConfig]

/-- **The runs correspond:** `c.swapAsk` with the oracle `Bᶜ` runs as `c` with the oracle `B`. -/
theorem OTMCode.run_swapAsk (c : OTMCode) (B : Set BitString) (x : BitString) (t : ℕ) :
    run c.swapAsk.toOTM Bᶜ x t = c.swapConfig (run c.toOTM B x t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run, run, ih, OTMCode.step_swapAsk]

/-- The same, for a complemented oracle on the side of `c`. -/
theorem OTMCode.run_swapAsk' (c : OTMCode) (B : Set BitString) (x : BitString) (t : ℕ) :
    run c.swapAsk.toOTM B x t = c.swapConfig (run c.toOTM Bᶜ x t) := by
  rw [← OTMCode.run_swapAsk, compl_compl]

/-- The machine `c.swapAsk` asks the same oracle questions as `c` at the corresponding
configuration. -/
theorem OTMCode.askedAt_swapAsk (c : OTMCode) (cf : Config c.toOTM) :
    askedAt c.swapAsk.toOTM (c.swapConfig cf) = askedAt c.toOTM cf := by
  unfold askedAt
  by_cases hc : Halted c.toOTM cf
  · rw [ite_eq_left hc, ite_eq_left ((c.halted_swapAsk_iff cf).2 hc)]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((c.halted_swapAsk_iff cf).1 h)),
      OTMCode.swapAsk_δ]
    cases c.toOTM.δ cf.q (cf.tape cf.head) <;> rfl

/-- The same queries. -/
theorem OTMCode.queries_swapAsk (c : OTMCode) (B : Set BitString) (x : BitString) (t : ℕ) :
    queries c.swapAsk.toOTM Bᶜ x t = queries c.toOTM B x t := by
  unfold queries
  refine Finset.biUnion_congr rfl fun s _ => ?_
  rw [OTMCode.run_swapAsk, OTMCode.askedAt_swapAsk]

/-- The same clocked verdicts. -/
theorem OTMCode.clockedAccepts_swapAsk (c : OTMCode) (e : ℕ) (B : Set BitString) (x : BitString) :
    ClockedAccepts c.swapAsk e Bᶜ x ↔ ClockedAccepts c e B x := by
  unfold ClockedAccepts
  simp only [OTMCode.run_swapAsk]
  exact Iff.rfl

/-! ### The oracle of a position of `G_{e,x}` is the complement of a finite set -/

/-- The strings made non-random by the table: `|z| ≤ T.fn z` fails exactly on them
(`Table.le_fn_iff`; outside the table, `|z| ≤ 2|z| + 6` always holds). -/
def Table.bad (T : Table) : Finset BitString := T.dom.filter fun z => T.value z < z.length

/-- The length of a string `z` is at most `T.fn z` if and only if `z` is not in `T.bad`. -/
theorem Table.le_fn_iff (T : Table) (z : BitString) : z.length ≤ T.fn z ↔ z ∉ T.bad := by
  unfold Table.fn Table.bad
  by_cases h : z ∈ T.dom
  · simp [h]
  · simp only [h, ite_false, Finset.mem_filter, false_and, not_false_eq_true, iff_true]
    omega

/-- `oracleOf T.fn K = {z | z ∈ K ∪ T.bad}ᶜ`. -/
theorem oracleOf_table (T : Table) (K : Finset BitString) :
    oracleOf T.fn K = {z | z ∈ K ∪ T.bad}ᶜ := by
  ext z
  simp only [oracleOf, Set.mem_ofPred_eq, Set.mem_compl_iff, Finset.mem_union, T.le_fn_iff]
  tauto

/-- **The run of a position through a listed oracle:** the run of `c` with the oracle of the
position `K` is the run of `c.swapAsk` with the listed oracle `K ∪ T.bad`. -/
theorem OTMCode.run_oracleOf_table (c : OTMCode) (T : Table) (K : Finset BitString)
    (x : BitString) (t : ℕ) :
    run c.swapAsk.toOTM {z | z ∈ K ∪ T.bad} x t =
      c.swapConfig (run c.toOTM (oracleOf T.fn K) x t) := by
  rw [oracleOf_table, OTMCode.run_swapAsk']

/-- The queries made by `c` with the oracle of position `K` are the same as the queries
made by `c.swapAsk` with the listed oracle `K ∪ T.bad`. -/
theorem OTMCode.queries_oracleOf_table (c : OTMCode) (T : Table) (K : Finset BitString)
    (x : BitString) (t : ℕ) :
    queries c.toOTM (oracleOf T.fn K) x t =
      queries c.swapAsk.toOTM {z | z ∈ K ∪ T.bad} x t := by
  rw [oracleOf_table, ← OTMCode.queries_swapAsk, compl_compl]

/-- The clocked acceptance of `c` with the oracle of position `K` is equivalent to the clocked
acceptance of `c.swapAsk` with the listed oracle `K ∪ T.bad`. -/
theorem OTMCode.clockedAccepts_oracleOf_table (c : OTMCode) (e : ℕ) (T : Table)
    (K : Finset BitString) (x : BitString) :
    ClockedAccepts c e (oracleOf T.fn K) x ↔
      ClockedAccepts c.swapAsk e {z | z ∈ K ∪ T.bad} x := by
  rw [oracleOf_table, ← OTMCode.clockedAccepts_swapAsk, compl_compl]

end Kolmogorov.RandomStrings
