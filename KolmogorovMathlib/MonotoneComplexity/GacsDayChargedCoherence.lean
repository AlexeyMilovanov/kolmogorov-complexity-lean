import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.LegalOuterMoves
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.RootIncrements
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.OutputCoherence
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedOuterSupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRequestWindow
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTerminationSupport

/-!
# Coherence of the charged strategy

Group of the coherence statements for the charged Gács–Day client: everything asserting that the
moves the charged run makes and displays are legal request assignments obeying the tree
discipline and the scale caps. Its parts are `LegalOuterMoves` (the play seen by a recursive
call, and the current and spend moves, are legal and request coherent), `RootIncrements` (the
amount a round adds at the root of a client stays below the spend scale, giving
`grayCharged_display_root_cap`) and `OutputCoherence` (the displayed move is request coherent for
every client, `grayCharged_output_coherentCap`), together with the support, request-window and
termination modules they rest on.
-/
