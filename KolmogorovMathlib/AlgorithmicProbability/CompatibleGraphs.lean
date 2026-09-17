/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs.Basic
import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs.APrioriMarginals

/-!
# Compatible graphs and continuous maps on the Cantor space

A *compatible graph* is a monotone, consistent set of pairs (finite input prefix,
finite output prefix).  The main results are that every compatible graph is the
graph of a unique continuous map on the space of bit sequences
(`existsUnique_continuousMap_of_compatibleGraph`) and that this correspondence is a
bijection (`continuousMap_graph_bijection`).

The rest of the file develops the *leftmost allocation* used by the constructive
Kraft-Chaitin argument: `leftValue` reads a finite string as the left endpoint of the
dyadic interval it names, and the lemmas about it establish that the greedy leftmost
allocator never overlaps a previously allocated interval.

SUV Theorem 43, p. 105.
-/
