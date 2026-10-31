/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice.PastFuture
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice.Decompositions
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice.SquareRoot

/-!
# Two-scale extension prices

This aggregator imports `ExtensionPrice/PastFuture.lean` (past extension counts and future
decoding), `ExtensionPrice/Decompositions.lean` (two volume decompositions) and
`ExtensionPrice/SquareRoot.lean` (structural volume estimates). Together they define the
algorithm that prices a candidate program by its extensions at two scales and prove it sound
and complete (`extension_price_sound_complete`). The price is the quantity the fighter
construction compares against when it allocates directives, and `Plain.Main` selects its
price constants from the existential statement proved here.

Past counts read distinct extension indices from the emitted snapshot at a verified
candidate tick. Price computation is total on all records, using zero for malformed
records and small scales. Its constants are explicit inputs, never extracted from
existential proofs. Correctness uses one common structural-volume constant and the
true marker, a sufficiently large tower parameter, and the prescribed input ranges.
-/
