/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Geometry.InfiniteEntropy.FiniteAlphabetSubsystems
import KolmogorovMathlib.PointToSet.Geometry.InfiniteEntropy.NoBowenRoot

/-!
# Finite subsystems and the infinite-entropy conformal example

This directory supplies the example showing that the Bowen equation for conformal systems can
fail to have a real root when the entropy is infinite. It is not used by the main theorems; it
delimits their hypotheses.

* `InfiniteEntropy.FiniteAlphabetSubsystems`: pressure and cylinder covers of the subsystems
  of the Baire full shift with finitely many symbols. They are subsets of the full shift, so
  all pressure covers use ambient centers in that same space.
* `InfiniteEntropy.NoBowenRoot`: the Hausdorff dimension of each finite-alphabet subsystem is
  computed from these covers; letting the alphabet grow, the full Baire shift is uniformly
  conformal with constant potential one and uniform positive averages, but has infinite
  pressure, entropy, Hausdorff dimension and packing dimension, so that the pressure functions
  have no real zero.
-/
