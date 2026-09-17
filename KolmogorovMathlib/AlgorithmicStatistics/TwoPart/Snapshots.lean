import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Snapshot
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.RichChunks
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Part02
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Part03
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Part04
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions

/-!
# Snapshots of the description enumeration: the group

At any stage one can list the two-part descriptions of a given shape discovered so far; that
list is a *snapshot*, and it is what makes the improving-description arguments effective.
`Snapshots.Snapshot` defines it, `Snapshots.RichChunks` selects the rich descriptions and
groups the half-rich ones into chunks, `Snapshots.Part02` and `Snapshots.Part03` prove those
chunks sound and count them, and `Snapshots.Part04` derives the size form of the improving
description.
-/
