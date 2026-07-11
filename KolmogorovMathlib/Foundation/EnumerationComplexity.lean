import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile

/-!
# M0: complexity via computable enumerations — DRAFT statements

Plan reference: `PLAN_RESTRICTED_TYPE.md`, milestone M0. This file is owned by
the `M0_enumeration_complexity` proof-loop section.

The single most-used informal step of VS40 §6: *"the selected set can be
described by its ordinal number in an enumeration, so its complexity is
≤ log₂(index) + O(1)"*. The same move exists ad hoc in
`TwoPart/GapCounting.lean` (`candidateCodes`, `appearanceListCodes`,
`indexSelectorFn`, `code_mem_appearanceListCodes`) — the intended proof route
GENERALIZES that machinery; read it before proving anything here, and prefer
re-pointing it to this file over duplicating.

Statement status: DRAFT until the first strategic freeze. The constants are
per-enumeration (the enumeration is a fixed computable object, matching the
`KPPlain_map_le` style of the repo); a conditional variant carries the
context `y`.
-/

namespace Kolmogorov

/-- A staged computable enumeration of bitstrings: `enum t` is the finite
list produced within `t` steps, prefix-monotone in `t` (repetitions allowed;
distinctness is handled by `distinctAt`). -/
structure StagedEnumeration where
  enum : ℕ → List BitString
  computable : Computable enum
  mono : ∀ t, enum t <+: enum (t + 1)

namespace StagedEnumeration

/-- The distinct enumerated strings at stage `t`, in order of first
appearance. -/
def distinctAt (E : StagedEnumeration) (t : ℕ) : List BitString :=
  (E.enum t).eraseDups

/-- Stability: once an element has an index in `distinctAt`, later stages
preserve that index (prefix-monotonicity survives `eraseDups`). -/
theorem distinctAt_mono (E : StagedEnumeration) (t : ℕ) :
    E.distinctAt t <+: E.distinctAt (t + 1) := by
  sorry

/-- **M0 core (plain form).** The `k`-th distinct enumerated string has
prefix complexity at most `2·|bits k| + O(1)`; the constant depends only on
the enumeration `E` and the machine `U`. -/
theorem KPPlain_le_log_index_of_enumeration (U : Map)
    (hU : IsOptimalPrefixConditional U) (E : StagedEnumeration) :
    ∃ c : ℕ, ∀ (t k : ℕ),
      k < (E.distinctAt t).length →
      KPPlain U ((E.distinctAt t).getD k []) ≤
        2 * (Nat.bits k).length + (c : ENat) := by
  sorry

/-- **M0 core (conditional form).** Same bound for enumerations whose stage
lists depend computably on a context `y`; the index bound holds given `y`. -/
theorem KP_le_log_index_of_cond_enumeration (U : Map)
    (hU : IsOptimalPrefixConditional U)
    (enum : BitString → ℕ → List BitString)
    (henum : Computable fun p : BitString × ℕ => enum p.1 p.2)
    (hmono : ∀ y t, enum y t <+: enum y (t + 1)) :
    ∃ c : ℕ, ∀ (y : BitString) (t k : ℕ),
      k < ((enum y t).eraseDups).length →
      KP U (((enum y t).eraseDups).getD k []) y ≤
        2 * (Nat.bits k).length + (c : ENat) := by
  sorry

/-- **M0 for set codes.** If the enumeration produces canonical uniform codes
of finite sets, the `k`-th distinct enumerated set has `setComplexity` at
most `2·|bits k| + O(1)`. (Bridge form used by the restricted-family theory;
derive from `KPPlain_le_log_index_of_enumeration`.) -/
theorem setComplexity_le_log_index_of_enumeration (U : Map)
    (hU : IsOptimalPrefixConditional U) (E : StagedEnumeration) :
    ∃ c : ℕ, ∀ (t k : ℕ) (S : Finset BitString) (hS : S.Nonempty),
      k < (E.distinctAt t).length →
      (E.distinctAt t).getD k [] = (codedUniformOn S hS).code →
      setComplexity U S hS ≤ 2 * (Nat.bits k).length + (c : ENat) := by
  sorry

end StagedEnumeration

end Kolmogorov
