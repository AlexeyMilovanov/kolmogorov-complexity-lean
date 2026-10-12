import KolmogorovMathlib.StrongMerging.Coding.Encodings
import KolmogorovMathlib.StrongMerging.Coding.Programs
import KolmogorovMathlib.StrongMerging.Coding.Chain
import KolmogorovMathlib.StrongMerging.Coding.Information

/-!
# Strong merging: the coding foundation (cluster A_CODING)

The coding layer shared by the upper hierarchy, the reservoir game and the lower-bound assembly
of the strong-merging note `sublinear-merging.tex`.  All statements use the exact shared
definitions of `StrongMerging.Basic` (U00, S00, S01): one optimal plain machine `V`, the
canonical total interpreter `universalDecompressor`, the canonical model code
`canonicalFiniteSetCode`, real binary logarithms.

* `Coding.Encodings`: U01 `upperFiniteEncodings`, L01 `Lower.cubeModelEncoding`.
* `Coding.Programs`: `condC`; U02 `upperLiteralAndHeaders` (literal, conversions, finite indices,
  packets, realization of fixed decoders through S01); L03 `Lower.totalCodingInterface`;
  L04 `Lower.boundedEvaluationInterface`.
* `Coding.Chain`: `pairC`, `mutualInfo`; U03 `upperComplexityChain_lower`,
  `upperComplexityChain_upper`, `upperSubmodularity`; L02 `Lower.plainCodingInterface`.
* `Coding.Information`: U04 `upperTypicality`, `upperJointBound`; U05 `upperCommonInformation`,
  `upperCommonInformation_total`; U06 `upperMassTransfer_info`, `upperMassTransfer`.

## L43: the uniform constant ledger

Every coding statement of this layer has the form `∃ c : ℕ, ∀ instance, …`: the constant is
quantified after the machine `V` (and, for `condC_le_of_decoder` and `totalC_le_of_decoder`,
after the fixed decoder `D`) and before every instance parameter (strings, models, budgets,
lengths).  No statement has the form `∀ instance, ∃ c`.  Consumers must keep this order:

1. fix `V` (with `isOptimalConditional V`) and `T₀ = universalDecompressor` (S01);
2. fix each decoder `D` of an algorithm family, with its numeric fields as inputs read from a
   packet (`numPacket`, `pointPacket`), and obtain its constant from `totalC_le_of_decoder`;
3. obtain the coding constants of U02–U06 (each an explicit `∃ c`);
4. choose self-referential constants (a header constant `C₁` paying for its own header, the
   hierarchy step `c₂ > u₀ + u₁ + u₂ ⌈log₂ (c₂ + 2)⌉ + 2`) by `exists_const_gt_header`;
5. only then choose theorem cutoffs (`λ`, `M₀`) and quantify over instances.

Distinct Lean names keep the overloaded manuscript letters apart (blueprint symbol ledgers):
`plainMachine` = `V`, `totalMachine` = `universalDecompressor`, `headerLog` = `m`/`ℓ(n)`,
`baseBudget` = `H`, `rootScale` = `√(n H)`, `mergerBudget` = `T` of the lower bound; the
coding constants here are local existentials (`blit`, `btyp`, `bsize`, `bjoint`, …) and never
reuse the lower proof's radius or game parameters.
-/

namespace Kolmogorov.StrongMerging

/-- **Self-referential constant choice** (node L43, and the upper ledger's choice of the hierarchy
step `c₂`): for fixed `a, b` some constant `c` dominates `a + b ⌈log₂ (c + 2)⌉`.  This is how a
constant that must pay for its own header (`C₁` of the peeling decoder, `c₂` of the hierarchy) is
chosen after the constants it dominates, with no circularity.

Reference: appendix "Upper-specific symbol ledger" (`c₂`) and lower blueprint L43 (`C₁`). -/
theorem exists_const_gt_header (a b : ℕ) : ∃ c : ℕ, a + b * headerLog c < c := by
  have key : ∀ m : ℕ, 6 ≤ m → m * m + m + 2 < 2 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have hmm : m ≤ m * m := Nat.le_mul_self m
      rw [pow_succ]
      nlinarith
  have hk := key (a + b + 6) (by omega)
  refine ⟨2 ^ (a + b + 6) - 2, ?_⟩
  have hlog : headerLog (2 ^ (a + b + 6) - 2) = a + b + 6 := by
    unfold headerLog
    rw [Nat.sub_add_cancel (by omega)]
    exact Nat.clog_pow 2 _ one_lt_two
  rw [hlog]
  have hb : b * (a + b + 6) ≤ (a + b + 6) * (a + b + 6) :=
    Nat.mul_le_mul_right _ (by omega)
  generalize 2 ^ (a + b + 6) = P at hk ⊢
  generalize (a + b + 6) * (a + b + 6) = Q at hk hb
  omega

end Kolmogorov.StrongMerging
