/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.LSC.Computability
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin.Request

/-!
# Compatibility imports for the Kraft-Chaitin core

The former monolithic `KraftChaitinCore` file has been split into lower
semicomputable truncation/computability modules and the abstract Kraft-Chaitin
request realization engine. This file preserves the old import path while the
downstream tree migrates to the split modules.
-/
