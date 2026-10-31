/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.VirtualOutput
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.VirtualStabilization
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.FundedFrames
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.SimulationState
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.SimulationEvents
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.OracleAgreement
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.PolynomialCounting

/-!
# Eventual oracle agreement and the counting diagonal

This aggregator imports the `Construction/Diagonal/` directory, which carries out the final
diagonal argument against the constructed decompressor `fighterU`. It compares two oracles
for the phase started by the true marker of a late level: the *virtual* oracle, read from the
live counters of the phase, and the *actual* oracle, the cumulative complexity oracle of the
constructed machine. It then shows that no referee of the abstract family computes the
cumulative count with the constructed oracle.

* `VirtualOutput`, `VirtualStabilization`, `LiveCounters`: virtual and actual answers, live
  counters, and the stabilization of the virtual oracle.
* `AllocationGraph`, `AllocationProvenance`, `PayoffReceipts`,
  `FundedFrames`, `SimulationState`, `SimulationEvents`: the permanent allocation graph, the
  origin of allocated directives, and the cases (initial positive, new simulation
  description, new payoff) in which an actual positive appears.
* `OracleAgreement`: eventual agreement of the virtual and the actual oracle
  (blueprint node `constr:agreement`).
* `PolynomialCounting`: `constructed_oracle_defeats_polynomial_counting`
  (blueprint node `constr:diagonal`), which `Plain.Main` instantiates with the native referees.

Virtual answers read the named true-marker phase's live counters. The frozen semantic
limit is identified with their eventual value by a theorem, never by a definition that
assumes stabilization. Actual answers use the literal normalization of the conditional
machine. The final diagonal takes any member of the abstract family, so its native consumer
need not select a late level or supply any of the true-marker stability conclusions as
hypotheses.
-/
