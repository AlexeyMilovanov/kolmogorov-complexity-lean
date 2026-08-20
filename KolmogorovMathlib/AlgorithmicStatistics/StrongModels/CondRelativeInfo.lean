import KolmogorovMathlib.Prefix.ConditionalSymmetry

/-!
# Removing relatively-simple information from a condition

`KP_cond_remove_short_info` (in `Prefix.ConditionalSymmetry`) says that dropping
a component `z` from the condition of a conditional prefix complexity costs at
most the *unconditional* complexity `KPPlain U z` of that component.  For the
charged bookkeeping used by the strong-model transports one needs the sharper,
*relativized* form: the charge is only the complexity of `z` **given `y`**,
which can be far smaller than `KPPlain U z`.

`KP_cond_remove_relative_info` proves that form.  It is the same two-stage
decoding argument: from `y` we first decode `z` (using a program of length
`KP U z y`), assemble the condition `pairCode y z`, then decode `x` from it, and
finally project the produced pair onto its second component.
-/

namespace Kolmogorov

/-- **Removing relatively-simple info `z` from the condition.** Dropping `z`
from the condition costs at most the complexity of `z` *given `y`*, up to an
additive constant. -/
theorem KP_cond_remove_relative_info (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y z : BitString,
      KP U x y ≤ KP U x (pairCode y z) + KP U z y + (c : ENat) := by
  let ctx : BitString → BitString → Nat → BitString := fun r z _ => pairCode r z
  have hctx : Computable (fun p : (BitString × BitString) × ℕ => ctx p.1.1 p.1.2 p.2) :=
    pairCode_computable.comp
      (Computable.pair (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.fst))
  have hD_decomp := condTwoStagePairBuilder_isDecompressor hU.isDecompressor hU.isPrefixMachine hctx
  have hD_prefix := condTwoStagePairBuilder_isPrefixMachine (ctx := ctx) hU.isPrefixMachine
  let D := condTwoStagePairBuilder U ctx
  have hD : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c_inv, hc_inv⟩ := hU.invariance hD
  obtain ⟨c_map, hc_map⟩ := KP_map_le U hU decodeSecond decodeSecond_computable
  refine ⟨c_inv + c_map, ?_⟩
  intro x y z
  by_cases hpx : KP U x (pairCode y z) = ⊤
  · rw [hpx]; simp
  by_cases hpz : KP U z y = ⊤
  · rw [hpz]; simp
  obtain ⟨q, hq, hqlen⟩ := exists_program_of_KP_ne_top (M := U) (x := x) (y := pairCode y z) hpx
  obtain ⟨p, hp, hplen⟩ := exists_program_of_KP_ne_top (M := U) (x := z) (y := y) hpz
  have h_bound :=
    KP_condTwoStagePairBuilder_le_of_produces (U := U) (ctx := ctx) hU.isPrefixMachine hp hq
  have h_bound2 : KP D (pairCode z x) y ≤ KP U z y + KP U x (pairCode y z) := by
    calc KP D (pairCode z x) y ≤ ((p.length + q.length : Nat) : ENat) := h_bound
      _ = (p.length : ENat) + (q.length : ENat) := by norm_cast
      _ = KP U z y + KP U x (pairCode y z) := by rw [hplen, hqlen]
  have h_extract : KP U x y ≤ KP D (pairCode z x) y + c_inv + c_map := by
    calc KP U x y = KP U (decodeSecond (pairCode z x)) y := by rw [decodeSecond_pairCode]
      _ ≤ KP U (pairCode z x) y + c_map := hc_map (pairCode z x) y
      _ ≤ KP D (pairCode z x) y + c_inv + c_map := by gcongr; exact hc_inv (pairCode z x) y
  calc KP U x y ≤ KP D (pairCode z x) y + c_inv + c_map := h_extract
    _ ≤ KP U z y + KP U x (pairCode y z) + c_inv + c_map := by gcongr
    _ = KP U x (pairCode y z) + KP U z y + ((c_inv + c_map : ℕ) : ENat) := by
      lift (KP U x (pairCode y z)) to ℕ using hpx with kpx
      lift (KP U z y) to ℕ using hpz with kpz
      push_cast
      ring_nf

end Kolmogorov
