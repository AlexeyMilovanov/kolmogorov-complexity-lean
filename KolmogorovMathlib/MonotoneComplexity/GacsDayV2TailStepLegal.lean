import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Monotonicity

/-!
# The pinned tail step, unconditional

With the outer legality field discharged (`grayChargedLegalV2_of_rung`:
coherence half `GacsDayV2OuterCoherence`, monotone half
`GacsDayV2OuterMonotonicity`) and the anchored exit datum of v14 retired
(proof document v15.1: plain reserves, validity at the call's anchor, the
raised-service wait), the V2 pinned tail step
`pinnedChargedRung_tail_step_of_legal` needs no named obligation.
-/

namespace Kolmogorov

/-- **The pinned tail step** (blueprint A4): from the pinned rung at `q ≥ 3`
to the pinned rung at `q + 1` for the V2 block controller. -/
theorem pinnedChargedRung_tail_step
    {q : Nat} {sigma : FamilyStrategyScheme} (hq : 3 <= q)
    (hRung : PinnedChargedRung 4 q sigma) :
    PinnedChargedRung 4 (q + 1)
      (fun a e => grayChargedStrategyV2 q (grayFootprint q) a e sigma) :=
  pinnedChargedRung_tail_step_of_legal hq hRung
    (fun _a _n _A ha _ => grayChargedLegalV2_of_rung ha hRung)

end Kolmogorov
