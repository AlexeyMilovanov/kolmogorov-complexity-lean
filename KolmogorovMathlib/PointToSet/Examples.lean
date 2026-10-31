/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Examples.MiddleThirds
import KolmogorovMathlib.PointToSet.Examples.MiddleThirdsUpper
import KolmogorovMathlib.PointToSet.Examples.MiddleThirdsPointwise

/-!
# Complex digit sequences and the middle-thirds Cantor set

This directory is the running example of the point-to-set principles: the middle-thirds Cantor
set, both of whose classical dimensions equal `log 2 / log 3`. It is an application of the
static point-to-set principle and is not used by the main theorems. The bound on digit
sequences uses the relative prefix complexity and binary prefixes. The Cantor presentation
decodes finite binary words, appends zeros, and maps the digits to zero and two in base three;
its density and completeness are proved as part of its definition.

* `Examples.MiddleThirds`: the Cantor set as a presentation of a complete metric space, binary
  sequences of maximal prefix complexity, and the Hausdorff dimension of the set.
* `Examples.MiddleThirdsUpper`: the specified-radius packing dimension of the set.
* `Examples.MiddleThirdsPointwise`: the lower and upper static point dimensions of its points,
  whose suprema over the set equal `log 2 / log 3` for every oracle.
-/
