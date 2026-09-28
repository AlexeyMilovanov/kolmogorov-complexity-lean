import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwo.ServerProbes
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwo.ArithmeticRequests
import KolmogorovMathlib.MonotoneComplexity.GacsDayHalfAmplification

/-!
# The second amplification stage: `kappa = 2`

`grayFamilyGameSpec_halfStep` (in `GacsDayHalfAmplification`) wins the family
game with amplification `3 / 2` by a *static* request tree: the client asks
`2 ^ (-a)` at the root and the two unequal halves `2 ^ (-a-1) ± 2 ^ (-D)` at the
two root children, and the rounding-up built into `Serves` forces the server to
allocate two incompatible cylinders of masses `2 ^ (-a)` and `2 ^ (-a-1)`.

Static request trees cannot do better than that by much: if `forced x` denotes
the mass a subtree rooted at `x` forces, then `forced x` is at most the larger of
the rounded-up request at `x` and the sum of the forced masses of the children,
and rounding up multiplies a request by less than `2`, so a static request tree
never forces more than `2` times the root request. Amplification `2` therefore
needs a client that *reacts* to the server.

This file proves stage `2` of the family ladder, `kappa = 2`, with such a
reactive strategy. The client plays in two phases.

* **Probe.** It asks `2 ^ (-a)` at the root and `2 ^ (-a-1) - 2 ^ (-D)` at both
  root children. Those two children requests are each served by a cylinder of
  mass `2 ^ (-a-1)`, and the root request by a cylinder `R` of mass `2 ^ (-a)`.
* **Raise.** As soon as the server has served all three requests (at the first
  such time, which the client reads off the history), the client raises *one*
  child request to `2 ^ (-a-1) + 2 ^ (-D)`, keeping the total request at the
  root exactly `2 ^ (-a)`. The raised request now needs a cylinder of mass
  `2 ^ (-a)`, i.e. a cylinder as large as `R` itself. The client raises the
  child whose *sibling* cylinder is prefix-comparable with `R`, so the sibling
  blocks `R`: the new cylinder must be incompatible with `R`, and the two
  together carry gray mass `2 * 2 ^ (-a)`.

If no sibling cylinder is comparable with `R`, the three probe cylinders `R`,
`c₀`, `c₁` are already pairwise incompatible and carry
`2 ^ (-a) + 2 ^ (-a-1) + 2 ^ (-a-1) = 2 * 2 ^ (-a)` by themselves; and if `R` is
strictly shorter than `a` it carries `2 * 2 ^ (-a)` on its own. So every legal
server either leaves a request permanently unserved or grays twice the total
root request.
-/
