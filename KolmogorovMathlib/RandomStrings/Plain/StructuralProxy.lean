/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.StructuralProxy.Towers
import KolmogorovMathlib.RandomStrings.Plain.StructuralProxy.Symmetry

/-!
# Tower parameters and the bounded structural proxy

This aggregator imports `StructuralProxy/Towers.lean` (towers, the finite crossing and the
total structural proxy) and `StructuralProxy/Symmetry.lean` (its symmetry properties). The
proxy is a total computable function that, from a candidate record, returns the last
crossing index of the tables of conditional complexities at a tower scale, so that the
construction never has to evaluate an uncomputable complexity. It builds on the
extension counts of `Plain.ExtensionDensity` and the markers of `Plain.Markers`, and the
extension prices of `Plain.ExtensionPrice` are computed from it.

The proxy scans a finite interval using only the frozen candidate prefix minima.
Its crossing set contains zero even for false candidates. Malformed records return
the empty word. Exact complexities occur only in propositions with natural witnesses;
no semantic complexity or marker is evaluated by an algorithm.
-/
