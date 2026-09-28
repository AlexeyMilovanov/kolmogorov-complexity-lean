import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow.StepFold
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow.CountInvariants
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow.Part02
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Greedy running-window version count (Vereshchagin–Vitányi core)

This module isolates the purely combinatorial heart of the Vereshchagin–Vitányi
finite greedy-window construction used for the Section 3 arbitrary-curve
realization theorem (`stat-any-curve`).

We model the finite deletion process abstractly, over an arbitrary finite ground
set `G : Finset α`.  A *running window* of size `W` is maintained: as deletions
`d₀, d₁, …` arrive (each merged into the accumulated `deleted` set), whenever the
current window is fully deleted it is *refreshed* to a fresh block
`first (G \ deleted)` of the still-undeleted elements, and a refresh counter is
incremented.

The key quantitative fact (`fold_count_mul_le` / `fold_count_le`) is that, as long
as there is always room for a full window (final `deleted.card + W ≤ G.card`), the
number of refreshes is at most `deleted.card / W`.  This is exactly the
"version count" bound: successive refreshed windows are pairwise disjoint blocks of
`W` freshly-deleted elements, so `count · W ≤ deleted.card`.

The `first` window selector is kept abstract (any function returning a size-`min W`
sub-block); the concrete Section 3 instance sorts length-`n` strings by a canonical
`ℕ` encoding.
-/
