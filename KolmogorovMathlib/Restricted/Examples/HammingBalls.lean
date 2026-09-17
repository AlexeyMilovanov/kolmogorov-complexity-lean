import KolmogorovMathlib.Restricted.Examples.HammingBalls.Part01
import KolmogorovMathlib.Restricted.Examples.HammingBalls.Part02
import KolmogorovMathlib.Restricted.Family
import KolmogorovMathlib.Restricted.GreedyCover
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Logic.Equiv.Fintype

/-!
# Hamming balls as a description family

Group of the Hamming-ball example: `Part01` develops the Hamming distance and the volume and
covering degree of spheres and balls, `Part02` assembles the description family and its covering
overhead. The family machinery and the greedy cover imported alongside are what the overhead
bound is stated against.
-/
