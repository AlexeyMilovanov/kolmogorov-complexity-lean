import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerHardRegime
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FullCube
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2

/-!
# Shrinking the residual slack of the budgeted plain corner to `log (min beta l(x))`

`BudgetedPlainProfileCornerStatement V U` (`BudgetedNoiseTransport.lean`) is the
remaining input of `prop:upward`.  The proved §3 chain
(`budgeted_stochasticity_to_plain_corner_add_logSlack_beta`) establishes it up to
one residual additive term `logSlack c beta`, and
`budgeted_stochasticity_to_plain_corner_of_beta_le_pow`
(`BudgetedCornerHardRegime.lean`) absorbs that residual whenever `beta` is
polynomially bounded by the visible budget.

This module shows that the residual is in fact governed by the *minimum* of the
deficiency parameter and the length of `x`:

* `budgeted_plain_corner_of_length_le_beta` — as soon as `l(x) ≤ beta` the full
  cube `{0,1}^{l(x)}` already realizes the corner, with slack `O(log l(x))` and
  *no* stochasticity hypothesis at all: its plain set complexity is `O(log l(x))`
  (`plainSetComplexity_fullCube_le_logSlack`) and its size coordinate `l(x)` is
  already covered by `beta`;
* `budgeted_stochasticity_to_plain_corner_add_logSlack_min` — combining that with
  the §3 chain in the complementary regime `beta < l(x)` (where the residual
  `logSlack c beta` is itself the `min`) gives the corner for *every* `beta` with
  residual `logSlack c (min beta l(x))`;
* `budgeted_stochasticity_to_plain_corner_length_scale` — the same statement with
  the slack folded into `logSlack c (baseBudget + l(x))`, i.e. with the
  deficiency parameter eliminated from the slack altogether;
* `budgeted_stochasticity_to_plain_corner_of_min_le_pow` and its two special
  cases `..._of_length_le_pow` / `..._of_length_or_beta_le_pow` — the exact
  budget-scale corner whenever `min beta l(x)` is polynomially bounded by the
  budget;
* `plainSetComplexity_fullCube_le_KPPlain_natCode` and
  `budgeted_plain_corner_of_simple_length` — the cube gate sharpened from
  `O(log l(x))` to `K(l(x)) + O(1)`, giving the exact budget-scale corner for
  arbitrarily long strings, provided only that `l(x) ≤ beta` and that the length
  itself is of complexity at most `alpha`;
* `budgetedPlainCorner_of_hard_regime_superpoly` — the resulting case split,
  reducing the full corner statement to its remaining regime.

So the alternative research direction of the corner is narrowed once more: only strings whose
length *and* whose deficiency parameter are simultaneously superpolynomial in the
complexity budget, and whose length is either larger than `beta` or too complex
to name inside `alpha`, remain.  No frozen interface is edited, and nothing below
assumes an open statement.
-/

namespace Kolmogorov

open CodedFiniteDistribution

/-- **The full cube as a plain description profile.**  Every `x` lies in the
canonical length-`l(x)` cube, whose ordinary plain set complexity is
`O(log l(x))` and whose size coordinate is exactly `l(x)`. -/
theorem inPlainDescriptionProfile_fullCube (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString,
      InPlainDescriptionProfile V x (logSlack c x.length) x.length := by
  obtain ⟨c, hc⟩ := plainSetComplexity_fullCube_le_logSlack V hV
  refine ⟨c, fun x => ?_⟩
  refine ⟨stringsOfLength x.length, ⟨x, (memStringsOfLength _ _).mpr rfl⟩,
    (memStringsOfLength _ _).mpr rfl, hc x.length, ?_⟩
  rw [cardStringsOfLength]

/-- **A sharp complexity gate for the full cube.**  The ordinary plain set
complexity of the length-`n` cube is bounded by the prefix complexity of `n`
itself, not merely by `O(log n)`: the cube is computed from (a code for) `n` by a
fixed algorithm.

This refines `plainSetComplexity_fullCube_le_logSlack`, which is the special case
obtained from `KPPlain_natCode_le_log`. -/
theorem plainSetComplexity_fullCube_le_KPPlain_natCode
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ,
      plainSetComplexity V (stringsOfLength n) (codedStringsOfLength_nonempty n)
        ≤ KPPlain U (natCode n) + (c : ENat) := by
  obtain ⟨c₁, hc₁⟩ := KPPlain_map_le U hU
    (fun w => canonicalUniformCodeOfList
      (canonicalFinsetList (stringsOfLength (decodeNatCode w)))) (by
        convert canonicalUniformCodeOfList_computable.comp
          (_ : Computable fun w => canonicalFinsetList (stringsOfLength (decodeNatCode w)))
          using 1
        convert canonicalFinsetList_toFinset_primrec.comp
          (allStrings_primrec.comp decodeNatCode_primrec) |>.to_comp using 1)
  obtain ⟨cBridge, hcBridge⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  refine ⟨c₁ + cBridge, fun n => ?_⟩
  have hcode : canonicalUniformCodeOfList (canonicalFinsetList (stringsOfLength n))
      = (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).code :=
    canonicalUniformCodeOfList_canonicalFinsetList _ (codedStringsOfLength_nonempty n)
  have hmap := hc₁ (natCode n)
  rw [decodeNatCode_natCode, hcode] at hmap
  unfold plainSetComplexity
  calc plainK V (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).code
      ≤ KPPlain U (codedUniformOn (stringsOfLength n)
          (codedStringsOfLength_nonempty n)).code + (cBridge : ENat) := hcBridge _
    _ ≤ (KPPlain U (natCode n) + (c₁ : ENat)) + (cBridge : ENat) := by gcongr
    _ = KPPlain U (natCode n) + ((c₁ + cBridge : ℕ) : ENat) := by push_cast; ring

/-- **The budgeted plain corner in the regime `l(x) ≤ C(x) + beta`.**  No
stochasticity hypothesis is needed: the full cube at the length of `x` is a model
with complexity `O(log l(x))` and size coordinate `l(x)`, which the two-part
budget `kx + beta` already covers, so both corner inequalities hold with the slack
`logSlack c l(x)`.

This is exactly the regime the `beta`-restricted §3 corner cannot reach, and it
covers arbitrarily large deficiency parameters. -/
theorem budgeted_plain_corner_of_length_le_beta (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (kx alpha beta : ℕ),
      x.length ≤ kx + beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c x.length ∧
        i + j ≤ kx + beta + logSlack c x.length := by
  obtain ⟨c, hc⟩ := inPlainDescriptionProfile_fullCube V hV
  refine ⟨c, fun x kx alpha beta hlen => ?_⟩
  exact ⟨logSlack c x.length, x.length, hc x, by omega, by omega⟩

/-- The prefix complexity of the length of `x` is bounded by the prefix
complexity of `x`: the length is computed from the string. -/
theorem KPPlain_natCode_length_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, KPPlain U (natCode x.length) ≤ KPPlain U x + (c : ENat) :=
  KPPlain_map_le U hU (fun w => natCode w.length)
    (natCode_computable.comp Computable.list_length)

/-- **The budgeted plain corner for strings of simple length.**  If the length of
`x` is of prefix complexity at most `alpha`, and either the length or the length
plus that complexity fits the two-part budget, then the corner holds with the
budget-scale slack `logSlack c baseBudget` — with *no* bound on the length of
`x`, which may be arbitrarily larger than any power of the budget.

The model is again the full cube at the length of `x`, but its complexity is now
measured by the sharp gate `plainSetComplexity_fullCube_le_KPPlain_natCode`
(cost `K(l(x)) + O(1)`) rather than by `O(log l(x))`.  The two-part sum stays
budget-scale because `K(l(x)) ≤ K(x) ≤ C(x) + O(log C(x))` always holds, whatever
`alpha` is. -/
theorem budgeted_plain_corner_of_simple_length
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta m : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      (x.length ≤ beta ∨ x.length + m ≤ kx + beta) →
      KPPlain U (natCode x.length) ≤ (m : ENat) →
      m ≤ alpha →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨cG, hG⟩ := plainSetComplexity_fullCube_le_KPPlain_natCode V U hV hU
  obtain ⟨cLen, hLen⟩ := KPPlain_natCode_length_le U hU
  obtain ⟨cKP, hKP⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨2 + cG + cKP + cBits + cLen, fun x kx baseBudget alpha beta m hkx hkxN hlen hm hma => ?_⟩
  set c := 2 + cG + cKP + cBits + cLen with hc
  set q := kx + 2 * (Nat.bits kx).length + cKP + cBits + cLen with hq
  -- The complexity of the length of `x` is at most `C(x) + O(log C(x))`.
  have hqE : KPPlain U (natCode x.length) ≤ ((q : ℕ) : ENat) := by
    calc KPPlain U (natCode x.length) ≤ KPPlain U x + (cLen : ENat) := hLen x
      _ ≤ ((kx : ENat) + KPPlain U (Nat.bits kx) + (cKP : ENat)) + (cLen : ENat) := by
          gcongr
          exact hKP x kx hkx
      _ ≤ ((kx : ENat) + ((2 * (Nat.bits kx).length + cBits : ℕ) : ENat) + (cKP : ENat))
            + (cLen : ENat) := by
          gcongr
          exact hBits (Nat.bits kx)
      _ = ((q : ℕ) : ENat) := by rw [hq]; push_cast; ring
  -- Both complexity bounds for the cube.
  have hgate := hG x.length
  have hb1 : plainSetComplexity V (stringsOfLength x.length)
      (codedStringsOfLength_nonempty x.length) ≤ ((m + cG : ℕ) : ENat) := by
    refine hgate.trans ?_
    push_cast
    gcongr
  have hb2 : plainSetComplexity V (stringsOfLength x.length)
      (codedStringsOfLength_nonempty x.length) ≤ ((q + cG : ℕ) : ENat) := by
    refine hgate.trans ?_
    push_cast
    gcongr
  set i := min (m + cG) (q + cG) with hi
  have hbi : plainSetComplexity V (stringsOfLength x.length)
      (codedStringsOfLength_nonempty x.length) ≤ ((i : ℕ) : ENat) := by
    rcases le_total (m + cG) (q + cG) with h | h
    · rw [hi, min_eq_left h]; exact hb1
    · rw [hi, min_eq_right h]; exact hb2
  have hprof : InPlainDescriptionProfile V x i x.length :=
    ⟨stringsOfLength x.length, ⟨x, (memStringsOfLength _ _).mpr rfl⟩,
      (memStringsOfLength _ _).mpr rfl, hbi, by rw [cardStringsOfLength]⟩
  -- Slack bookkeeping.
  have hbits : 2 * (Nat.bits kx).length ≤ logSlack 2 baseBudget := by
    have h1 : 2 * (Nat.bits kx).length ≤ logSlack 2 kx := by unfold logSlack; omega
    exact h1.trans (logSlack_mono_right 2 hkxN)
  have hfold : logSlack 2 baseBudget + (cG + cKP + cBits + cLen) ≤ logSlack c baseBudget := by
    calc logSlack 2 baseBudget + (cG + cKP + cBits + cLen)
        ≤ logSlack (2 + (cG + cKP + cBits + cLen)) baseBudget := logSlack_add_nat_le _ _ _
      _ ≤ logSlack c baseBudget := logSlack_mono_left (by omega) _
  have hcG : cG ≤ logSlack c baseBudget := by
    have : c ≤ logSlack c baseBudget := by unfold logSlack; omega
    omega
  have hi1 : i ≤ m + cG := min_le_left _ _
  have hi2 : i ≤ q + cG := min_le_right _ _
  rcases hlen with hlen | hlen
  · exact ⟨i, x.length, hprof, by omega, by omega⟩
  · exact ⟨i, x.length, hprof, by omega, by omega⟩

/-- **The residual slack of the budgeted plain corner is `O(log (min beta l(x)))`.**
For *every* stochasticity witness — no restriction on `alpha`, on `beta` or on the
length — the corner holds with

* `i ≤ alpha + logSlack c baseBudget + logSlack c (min beta l(x))`,
* `i + j ≤ C(x) + beta + logSlack c baseBudget + logSlack c (min beta l(x))`.

This sharpens `budgeted_stochasticity_to_plain_corner_add_logSlack_beta`, whose
residual is `logSlack c beta`: if `beta ≤ l(x)` the two agree, and if
`l(x) < beta` the full cube (`budgeted_plain_corner_of_length_le_beta`) realizes
the corner outright with residual `logSlack c l(x)`. -/
theorem budgeted_stochasticity_to_plain_corner_add_logSlack_min
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget + logSlack c (min beta x.length) ∧
        i + j ≤ kx + beta + logSlack c baseBudget + logSlack c (min beta x.length) := by
  obtain ⟨cCube, hCube⟩ := budgeted_plain_corner_of_length_le_beta V hV
  obtain ⟨cChain, hChain⟩ :=
    budgeted_stochasticity_to_plain_corner_add_logSlack_beta V U hV hU
  refine ⟨max cCube cChain, fun x kx baseBudget alpha beta hkx hkxB hstoch => ?_⟩
  set c := max cCube cChain with hc
  rcases le_or_gt x.length beta with hlen | hlen
  · -- Long strings: the full cube is already a corner model.
    obtain ⟨i, j, hprof, hi, hij⟩ := hCube x kx alpha beta (by omega)
    have hmin : min beta x.length = x.length := min_eq_right hlen
    have hslack : logSlack cCube x.length ≤ logSlack c (min beta x.length) := by
      rw [hmin]
      exact logSlack_mono_left (le_max_left _ _) _
    exact ⟨i, j, hprof, by omega, by omega⟩
  · -- Short strings: the §3 chain's residual `logSlack c beta` is the minimum.
    obtain ⟨i, j, hprof, hi, hij⟩ := hChain x kx baseBudget alpha beta hkx hkxB hstoch
    have hmin : min beta x.length = beta := min_eq_left hlen.le
    have hslackB : logSlack cChain baseBudget ≤ logSlack c baseBudget :=
      logSlack_mono_left (le_max_right _ _) _
    have hslack : logSlack cChain beta ≤ logSlack c (min beta x.length) := by
      rw [hmin]
      exact logSlack_mono_left (le_max_right _ _) _
    exact ⟨i, j, hprof, by omega, by omega⟩

/-- **The budgeted plain corner with a length-scale slack.**  For every
stochasticity witness the corner holds with the slack
`logSlack c (baseBudget + l(x))`; the deficiency parameter has disappeared from
the slack entirely.  Immediate from
`budgeted_stochasticity_to_plain_corner_add_logSlack_min`. -/
theorem budgeted_stochasticity_to_plain_corner_length_scale
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c (baseBudget + x.length) ∧
        i + j ≤ kx + beta + logSlack c (baseBudget + x.length) := by
  obtain ⟨c, hc⟩ := budgeted_stochasticity_to_plain_corner_add_logSlack_min V U hV hU
  refine ⟨2 * c, fun x kx baseBudget alpha beta hkx hkxB hstoch => ?_⟩
  obtain ⟨i, j, hprof, hi, hij⟩ := hc x kx baseBudget alpha beta hkx hkxB hstoch
  have hB : logSlack c baseBudget ≤ logSlack c (baseBudget + x.length) :=
    logSlack_mono_right c (Nat.le_add_right _ _)
  have hL : logSlack c (min beta x.length) ≤ logSlack c (baseBudget + x.length) :=
    logSlack_mono_right c ((min_le_right _ _).trans (Nat.le_add_left _ _))
  have hfold : logSlack c (baseBudget + x.length) + logSlack c (baseBudget + x.length)
      = logSlack (2 * c) (baseBudget + x.length) := by
    rw [logSlack_add_const]
    ring_nf
  exact ⟨i, j, hprof, by omega, by omega⟩

/-- **The exact budget-scale corner whenever `min beta l(x)` is polynomial.**  If
either the deficiency parameter or the length of `x` is bounded by a fixed power
of the visible complexity budget, the budgeted plain corner holds with the slack
`logSlack c baseBudget`.

Together with the two proved regimes of `budgetedPlainCorner_of_hard_regime` this
leaves open only the doubly superpolynomial regime: `beta` *and* `l(x)` both
larger than every fixed power of `baseBudget`. -/
theorem budgeted_stochasticity_to_plain_corner_of_min_le_pow
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : ℕ) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      min beta x.length ≤ baseBudget ^ k →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨cMin, hMin⟩ := budgeted_stochasticity_to_plain_corner_add_logSlack_min V U hV hU
  obtain ⟨cPow, hPow⟩ := logSlack_le_of_le_pow cMin k
  refine ⟨cMin + cPow, fun x kx baseBudget alpha beta hkx hkxB hmin hstoch => ?_⟩
  obtain ⟨i, j, hprof, hi, hij⟩ := hMin x kx baseBudget alpha beta hkx hkxB hstoch
  have hres : logSlack cMin (min beta x.length) ≤ logSlack cPow baseBudget :=
    hPow baseBudget (min beta x.length) hmin
  have hfold : logSlack cMin baseBudget + logSlack cPow baseBudget
      = logSlack (cMin + cPow) baseBudget := logSlack_add_const _ _ _
  exact ⟨i, j, hprof, by omega, by omega⟩

/-- **The exact budget-scale corner for polynomially long strings**, with no
restriction whatsoever on the deficiency parameter. -/
theorem budgeted_stochasticity_to_plain_corner_of_length_le_pow
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : ℕ) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      x.length ≤ baseBudget ^ k →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨c, hc⟩ := budgeted_stochasticity_to_plain_corner_of_min_le_pow V U hV hU k
  exact ⟨c, fun x kx baseBudget alpha beta hkx hkxB hlen hstoch =>
    hc x kx baseBudget alpha beta hkx hkxB ((min_le_right _ _).trans hlen) hstoch⟩

/-- **The corner on the union of the two polynomial regimes.**  For a fixed
exponent `k`, the exact budget-scale plain corner holds whenever *either* the
length of `x` *or* the deficiency parameter `beta` is bounded by
`baseBudget ^ k`. -/
theorem budgeted_stochasticity_to_plain_corner_of_length_or_beta_le_pow
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : ℕ) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      (x.length ≤ baseBudget ^ k ∨ beta ≤ baseBudget ^ k) →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨c, hc⟩ := budgeted_stochasticity_to_plain_corner_of_min_le_pow V U hV hU k
  refine ⟨c, fun x kx baseBudget alpha beta hkx hkxB hcase hstoch => ?_⟩
  refine hc x kx baseBudget alpha beta hkx hkxB ?_ hstoch
  rcases hcase with hlen | hbeta
  · exact (min_le_right _ _).trans hlen
  · exact (min_le_left _ _).trans hbeta

/-- **The budgeted plain corner reduces to its doubly superpolynomial regime.**
A sharpening of `budgetedPlainCorner_of_hard_regime`: for any fixed exponent `k`,
the full `BudgetedPlainProfileCornerStatement V U` follows from the corner in the
regime

```text
alpha < kx ≤ baseBudget,   baseBudget ^ k < beta,   baseBudget ^ k < l(x),
```

together with the further restriction that the length of `x` is *not* simple: for
every bound `m ≤ alpha` on `K(l(x))` one has `beta < l(x)` and
`kx + beta < l(x) + m`.  Indeed the regime `kx ≤ alpha` is
`budgeted_plain_corner_of_kx_le_alpha`, the regime `min beta l(x) ≤ baseBudget ^ k`
is `budgeted_stochasticity_to_plain_corner_of_min_le_pow`, and the simple-length
regime is `budgeted_plain_corner_of_simple_length`.

Nothing here assumes the open regime; `hHard` is a faithful statement of what is
still missing, delimited on the deficiency axis, the length axis, and the
complexity of the length. -/
theorem budgetedPlainCorner_of_hard_regime_superpoly
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : ℕ)
    (hHard : ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      alpha < kx →
      baseBudget ^ k < beta →
      baseBudget ^ k < x.length →
      (∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) → m ≤ alpha →
        beta < x.length ∧ kx + beta < x.length + m) →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget) :
    BudgetedPlainProfileCornerStatement V U := by
  obtain ⟨cA, hA⟩ := budgeted_plain_corner_of_kx_le_alpha V hV
  obtain ⟨cM, hM⟩ := budgeted_stochasticity_to_plain_corner_of_min_le_pow V U hV hU k
  obtain ⟨cS, hS⟩ := budgeted_plain_corner_of_simple_length V U hV hU
  obtain ⟨cH, hH⟩ := hHard
  refine ⟨max (max cA cM) (max cS cH), fun x kx baseBudget alpha beta hkx hkxN hstoch => ?_⟩
  set c := max (max cA cM) (max cS cH) with hc
  have hcA : logSlack cA baseBudget ≤ logSlack c baseBudget :=
    logSlack_mono_left (le_trans (le_max_left cA cM) (le_max_left _ _)) baseBudget
  have hcM : logSlack cM baseBudget ≤ logSlack c baseBudget :=
    logSlack_mono_left (le_trans (le_max_right cA cM) (le_max_left _ _)) baseBudget
  have hcS : logSlack cS baseBudget ≤ logSlack c baseBudget :=
    logSlack_mono_left (le_trans (le_max_left cS cH) (le_max_right _ _)) baseBudget
  have hcH : logSlack cH baseBudget ≤ logSlack c baseBudget :=
    logSlack_mono_left (le_trans (le_max_right cS cH) (le_max_right _ _)) baseBudget
  by_cases hka : kx ≤ alpha
  · obtain ⟨i, j, hprof, hi, hij⟩ := hA x kx baseBudget alpha beta hkx hka
    exact ⟨i, j, hprof, by omega, by omega⟩
  · push_neg at hka
    by_cases hmin : min beta x.length ≤ baseBudget ^ k
    · obtain ⟨i, j, hprof, hi, hij⟩ := hM x kx baseBudget alpha beta hkx hkxN hmin hstoch
      exact ⟨i, j, hprof, by omega, by omega⟩
    · push_neg at hmin
      have hbeta : baseBudget ^ k < beta := lt_of_lt_of_le hmin (min_le_left _ _)
      have hlen : baseBudget ^ k < x.length := lt_of_lt_of_le hmin (min_le_right _ _)
      by_cases hsimple : ∃ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) ∧ m ≤ alpha ∧
          (x.length ≤ beta ∨ x.length + m ≤ kx + beta)
      · obtain ⟨m, hm, hma, hcase⟩ := hsimple
        obtain ⟨i, j, hprof, hi, hij⟩ :=
          hS x kx baseBudget alpha beta m hkx hkxN hcase hm hma
        exact ⟨i, j, hprof, by omega, by omega⟩
      · have hnot : ∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) → m ≤ alpha →
            beta < x.length ∧ kx + beta < x.length + m := by
          intro m hm hma
          have hno : ¬(x.length ≤ beta ∨ x.length + m ≤ kx + beta) := fun h =>
            hsimple ⟨m, hm, hma, h⟩
          push_neg at hno
          exact ⟨hno.1, hno.2⟩
        obtain ⟨i, j, hprof, hi, hij⟩ :=
          hH x kx baseBudget alpha beta hkx hkxN hka hbeta hlen hnot hstoch
        exact ⟨i, j, hprof, by omega, by omega⟩

end Kolmogorov
