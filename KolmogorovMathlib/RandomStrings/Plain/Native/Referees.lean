/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Native.Referees.EffectiveInterface
import KolmogorovMathlib.RandomStrings.Plain.Native.Referees.ClockedDecider

/-!
# Native counting referees and their infinitely repeated family

This aggregator imports `Native/Referees/EffectiveInterface.lean` (the effective native
referee) and `Native/Referees/ClockedDecider.lean` (the family of all tuples, and the
correctness of the referee for a clocked decider of the halting language). `Plain.Main`
combines the family with the diagonal of `Construction.Diagonal`: a polynomial-time reduction
of the halting language to the cumulative oracle would give a clocked decider, hence a
referee of the family that computes the cumulative count, which the constructed machine
defeats.

A tuple contains an OTM, its clock exponent, a literal search index, and an oracle
flag. Its universal finite table is read in a fixed order by a `QueryTree`.
Leaves run binary search using Boolean finite-table simulations. Construction time
and tree size are unrestricted; only target lengths have polynomial bounds.

OTM codes have finite transition functions rather than a `Primcodable` instance.
Uniform computability is therefore stated using their existing numerical encoding
and decoding, together with the postfix encoding of query trees.
-/
