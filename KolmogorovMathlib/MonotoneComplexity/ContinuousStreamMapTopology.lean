/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.MonotoneComplexity.StreamTopology

/-!
# Topological characterisation of continuous stream maps

`IsContinuousStreamMap` (monotonicity together with the least-upper-bound condition
along infinite inputs, as in SUV §5.4) coincides with topological continuity for the
prefix-cone topology on `BitStream` defined in `StreamTopology.lean`.
-/

namespace Kolmogorov

/-- A map `f : BitStream → BitStream` is continuous for the prefix-cone topology
if and only if it is a continuous stream map in the sense of SUV §5.4. -/
theorem continuous_iff_isContinuousStreamMap (f : BitStream → BitStream) :
    Continuous f ↔ IsContinuousStreamMap f := by
  constructor
  · intro hf
    constructor
    · intro s t hst
      rw [BitStream.le_iff_forall_finite_le]
      intro y hy
      have hopen : IsOpen (f ⁻¹' bitStreamCylinder y) :=
        (isOpen_bitStreamCylinder y).preimage hf
      rw [isOpen_bitStream_iff] at hopen
      cases s with
      | finite x =>
        have hx : BitStream.finite x ∈ f ⁻¹' bitStreamCylinder y := hy
        exact hopen.1 x hx hst
      | infinite w =>
        cases t with
        | finite z => exact absurd hst (BitStream.not_infinite_le_finite)
        | infinite v =>
          obtain rfl : w = v := hst
          exact hy
    · intro w y hy
      rw [BitStream.le_iff_forall_finite_le]
      intro u hu
      have hopen : IsOpen (f ⁻¹' bitStreamCylinder u) :=
        (isOpen_bitStreamCylinder u).preimage hf
      rw [isOpen_bitStream_iff] at hopen
      obtain ⟨n, hn⟩ := hopen.2 w hu
      exact le_trans hn (hy n)
  · intro hf
    rw [continuous_generateFrom_iff]
    rintro _ ⟨y, rfl⟩
    rw [isOpen_bitStream_iff]
    constructor
    · intro x hx s hs
      exact le_trans hx (hf.1 hs)
    · intro w hw
      exact (continuousStreamMap_finite_le_infinite_iff f hf w y).1 hw

end Kolmogorov
