/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Conditional
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective
import KolmogorovMathlib.RandomStrings.Plain.Construction.Referees
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability

/-!
# The permanent allocation graph of the fighter simulation

The state `fighterState P d tick` records every successful allocation in `allocated`, the
permanent graph of the constructed machine.  This module proves that each permanent allocation
is a description of its output by the constructed machine `fighterU P d`, of length one more
than its input (`simple_of_mem_fighterState_allocated`): by
`output_mem_fighterG_of_mem_allocated` its output is an actual output of the first-allocation
search on its input, which the directive branch of the machine reproduces.

The graph only grows with the tick (`fighterState_allocated_subset_of_le`, in
`Effective.LiveInvariants`), and the snapshot of an active phase is contained in the current
graph (`fighterState_initialAllocations_subset_allocated`, in
`Stability.PhaseSeparationAllocationGrowth`).

The fact is used by `Diagonal.FundedFrames` (fulfilled payoffs are simple).
-/

namespace Kolmogorov.Milovanov

/-- A permanent allocation is a description of its output by the constructed machine,
of length one more than its input. -/
theorem simple_of_mem_fighterState_allocated (P : FighterParams) (d tick : ℕ) (hd : 1 ≤ d)
    (a : AllocatedDirective) (ha : a ∈ (fighterState P d tick).allocated) :
    Simple (fighterU P d) a.output (a.input.length + 1) := by
  have hg := output_mem_fighterG_of_mem_allocated P d tick hd a ha
  apply (simple_iff_exists_program _ _ _).mpr
  refine ⟨true :: a.input, by simp only [List.length_cons, le_refl], ?_⟩
  have hdir := constructed_machine_directive P.B d hd (fighterG P d) a.input []
  simp only [produces, fighterU, hdir]
  exact hg

end Kolmogorov.Milovanov
