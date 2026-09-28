import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Coherence.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Coherence.Graft
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Minimum
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RequestWindow

/-!
# The coherence field of the V2 charged outer strategy

Port of `grayCharged_output_coherentCap` (`GacsDayChargedCoherence`) to
the V2 block controller: at every time, every root of the outer move
displayed by `grayChargedStrategyV2` is `requestCoherentCap`-capped at the
outer scale `dyadicScale a` — the first conjunct of `familyClientPlayLegal`.

Every sub-move the controller displays is a play of the pinned child rung
against a legal local server (`grayChargedBlockRound_gameSpecV2`,
`grayChargedSpendRound_gameSpecV2`), and the rung's `.weak.legal` gives the
per-root coherence of the current move at the round's anchor scale
(`grayTailRoundEps q L e r`, resp. `grayChargedSpendEps a L e pass`), both
dominated by the spend scale `dyadicScale (grayChargedSpendAlphaDepth a)`.
The invariant "every frozen round's move is coherent at the spend scale" is
carried along the certified run; the generic V1 graft lemmas
(`grayChargedEntryMove_nonneg`, `grayChargedEntryMove_child_le`,
`sum_grayChargedEntryMove_root_le_sonBase`) transfer the entry coherence to
the grafted outer move.  The two remaining root-side facts are the source
son-base cap (the advantage prefix is capped by `dyadicScale e` through the
wide-block multiplicity keystone, and the spend rounds only occupy spare
sons) and the root cap `≤ dyadicScale a` (advantage: source mass; spend: the
V2 request window plus the pinned per-pass increment `≤ α/8`; done: the
window).
-/
