import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun.StateCoding
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun.Computability
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun.Part02
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun.Part03
import KolmogorovMathlib.Restricted.FamilyCurve.RunCoding
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRebuild
import KolmogorovMathlib.Restricted.FamilyCurve.CoupledRun
import KolmogorovMathlib.Restricted.FamilyCurve.BadStream

/-!
# Partial-recursive chronological sampled run

The family cover selector is a partial-recursive search.  Consequently the
honest executable interface is a `Part BitString`: validity hypotheses prove
termination, rather than a noncomputable default being substituted when a
search diverges.

A coded state contains the current root live pool and the `N + 1` current
model codes.  All deeper live pools are reconstructed by successive
intersection.  On a bad event the executor finds the least failed density
edge, retains the prefix through that edge, and invokes the effective suffix
rebuild only on the strict suffix.
-/
