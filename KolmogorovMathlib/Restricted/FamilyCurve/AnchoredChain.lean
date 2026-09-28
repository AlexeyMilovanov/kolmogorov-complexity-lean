import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredChain.PrefixRuns
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredChain.VersionExponent
import KolmogorovMathlib.Restricted.FamilyCurve.RunChain
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredRun
import KolmogorovMathlib.Restricted.FamilyCurve.RunBounds

/-!
# The anchored run as an event-indexed chain

The anchored effective run processes its bad stream batch by batch; each batch
is a contiguous block of stream events.  This module re-indexes the run by
single events (`restrictedEventPrefixRun`), identifies the batch boundaries
with the chronological run, and packages the decoded per-event states as a
`RestrictedRunChain`, so that the version-count bound of `RunChain` applies to
the actual anchored construction.
-/
