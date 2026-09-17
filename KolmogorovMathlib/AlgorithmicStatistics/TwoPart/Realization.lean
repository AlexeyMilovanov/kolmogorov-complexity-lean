import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.Part01
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.TemporalBadSets
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.FinalWindow
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.Computability
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.ProfileExistence
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.ProfileExistenceTail
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.Antistochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots


/-!
# Section 3: profile / curve realization (`stat-any-curve`)

This module states the Section 3 realization theorem of the algorithmic-statistics
article (Theorem `stat-any-curve`, attributed to Vereshchagin–Vitányi): every
admissible boundary curve is, up to logarithmic precision, the boundary of the
description profile `P_x` of some string `x`.

The curve is modelled by a function `h : ℕ → ℕ` (`h i = t_i` = admissible log-size
at complexity budget `i`).  `ProfileCurve` collects the article's admissibility
conditions: the boundary connects `(0, n)` to `(kx, 0)`, decreases with slope at
least `-1` (`t_0 > t_1 > … > t_k`), and stays above the sufficiency line
`i + j ≥ kx` (all up to logarithmic slack).

The construction is decomposed into named components:

* Gate E1 (`curveCode`, `KPPlain_curveCode_le`): *removed* — the claim that a
  faithful whole-curve encoding costs only `O(log n)` is false (a generic
  admissible curve has `~n` bits of information) and it was unused; see the
  comment where it stood.  The true incremental content lives in Gate E2's
  `realizingFamily_setComplexity_le`.
* Temporal greedy windows replace the informal nested family of "good" sets `A_i`:
  each held window has size `≤ 2^{h i}` and complexity `≤ i + O(log n)`.
* The constructed string is the lexicographically first length-`n` string that avoids
  all "bad" `(i, h i)`-descriptions; temporal stabilization puts it in every coded
  window.
* Gate F (`realization_upper`): membership in every coded window gives the *upper* half of
  the profile — an `(i + O(log n), h i + O(log n))`-description for every `i`.
* Gate H0 (`exists_string_with_profile`): the main theorem, assembled here from
  Gates F and E3.
-/
