/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity.Bounds
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity.Density
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity.Relaxed

/-!
# Extension density at exponential scales

This aggregator imports `ExtensionDensity/Bounds.lean` (extension counts and dyadic crossing
descriptions), `ExtensionDensity/Density.lean` (strict density) and
`ExtensionDensity/Relaxed.lean` (relaxed density and computable projections). They bound the
number of extensions of a string at dyadic scales, from below by a crossing decoder and from
above by conditional coding. The results feed the structural proxy of `Plain.StructuralProxy`
and the volume estimates of `Plain.ExtensionPrice`.

Extensions literally use `pairCode y s`. Their semantic cardinalities use `Set.ncard`;
finiteness follows from the frozen description-count bound. All volume comparisons
cast these cardinalities to rationals, and every dyadic exponent is an integer.
The information-gap constant is shared by the strict and relaxed density estimates.
-/
