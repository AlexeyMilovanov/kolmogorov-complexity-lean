# Source → Lean coverage map

Maintenance rule: **every PR that formalizes, retires, or renames a
paper-facing result must update this file.** Agents: consult this map
*before* formalizing anything — if a row exists, build on the named
theorems instead of re-deriving them.

Sources:

- **SUV** — Shen, Uspensky, Vereshchagin, *Kolmogorov Complexity and
  Algorithmic Randomness* (scan + OCR + theorem index in
  `~/kolmogorov-complexity-literature/SUV-work/`).
- **VS40** — Vereshchagin, Shen, *Algorithmic statistics: forty years
  later* (arXiv:1607.08077, source in
  `~/kolmogorov-complexity-literature/algorithmic-statistics/`).
- **KR** — Kritchman, Raz, *The surprise examination paradox and the
  second incompleteness theorem* (arXiv:1011.4974).

Status legend: ✅ formalized · 🟡 partial · ❌ not started · ➖ out of scope for now.

## Active S9 interface decision

The public Lemma omp and Theorem uppest use m_P_eps P k_P (3 * epsilon) c while L(P, epsilon) retains radius epsilon. This pays the missing 2 * epsilon endpoint loss in the published proof. The exact-radius LemmaOmpExactRadiusStatement is retained for research but is not a completion obligation. This decision supersedes older exact-radius iteration notes below.

## Section 7 current status (iteration 112)

All Lean sources are `sorry`-free.  The former standalone, `sorry`-backed draft
`inPlainDescriptionProfile_fst_of_pair_model_budgeted` has been retired rather
than treated as proved.  Its exact coordinates are preserved by the provably
unsatisfiable research interface `BudgetedPairProjectionStatement`, and its worker
module is now imported by the Section 7 aggregate.  The current public-endpoint
state is:

- S0–S3, S5, S6, S7, S8, and S9 public endpoints are all proved unconditionally (`prop_add_noise`, `thm_step_wise`, `thm_separation`, `thm_hereditary`, `prop_min_hereditary`, `lemma_lch`, `t1_strange_string`, `t3`, `lemma_4`, `thm_card`, `lemma_omp` (at authorized `3 * epsilon` radius), and `thm_uppest`).
- **S4 is now complete: `prop_upward` is unconditional.** `UpwardOrdinalNoiseBetaRegime.lean` (proved, sorry-free, kernel axioms `propext`/`Classical.choice`/`Quot.sound` only) adds `strongModelOrdinalNoiseTransport_of_n_le_beta`, the complementary regime `n ≤ beta` of the consumer-shaped ordinal transport: strongness makes `x` and the canonical model-code/ordinal pair totally equivalent up to `epsilon`, so the image `B` of the full cube `{0,1}^n` under the corresponding total program contains the pair, has at most `2 ^ n` elements and plain complexity `epsilon + O(log n)` (`strongModelPairImage_exists`, `plainK_codedUniformOn_image_le`); the uniform distribution on `B` is then a model of complexity `epsilon + O(log n)` and optimality deficiency at most `n + epsilon + O(log n)`, which fits the radius as soon as `n ≤ beta`. Together with the proved regime `beta ≤ n + epsilon + logSlack cBudget n` this exhausts all deficiency budgets, giving the unconditional `strongModelOrdinalNoiseTransport` and hence `prop_upward` (both in `UpwardOrdinalNoiseBetaRegime.lean`). The following historical bullets describe the earlier, strictly more general budgeted-transport lane, whose large-`beta` corner remains open but is no longer needed for the source endpoint.
- (Historical, superseded by the bullet above.) `prop_upward` remains conditional: `PropUpwardStatement` is represented by `propUpward_of_budgetedRandomNoiseTransport` and `propUpward_of_budgetedPlainCorner`, while no unconditional `prop_upward` declaration exists. `budgetedRandomNoiseTransport_of_beta_le` proves the transport branch `beta ≤ baseBudget`; the large-`beta` regime remains active and open. `BudgetedPlainProfileCornerStatement` is retained only as a sufficient research/reduction interface and must not be assumed to complete the source claim.
- Iteration 112 adds the consumer-sized research interface `StrongModelOrdinalNoiseTransportStatement U T` in `UpwardOrdinalNoiseTransport.lean`. `propUpward_of_strongModelOrdinalNoiseTransport` proves that this exact canonical model-code/ordinal transport suffices for `PropUpwardStatement U T`, while `strongModelOrdinalNoiseTransport_of_budgetedRandomNoiseTransport` certifies that it follows from the older, strictly more general budgeted interface. The unconditional theorem `strongModelOrdinalNoiseTransport_of_beta_le` discharges its `beta ≤ n + epsilon + logSlack cBudget n` regime. `deficiency_not_le_pred_of_beta_minimal` closes the first Pareto-minimality diagnostic: at a beta-minimal stochasticity coordinate, no probability model of complexity at most `alpha` can witness deficiency `beta - 1` (unless `beta = 0`). The interface itself is not assumed or proved in the remaining large-`beta` regime, so this is a narrowing and partial discharge, not an unconditional `prop_upward`.
- `budgetedPlainCorner_of_hard_regime` (`BudgetedCornerHardRegime.lean`, proved, sorry-free) collapses the open part of `BudgetedPlainProfileCornerStatement V U` to the single regime `alpha < kx ≤ baseBudget < beta`: it assembles the full corner from the two proved leaves `budgeted_plain_corner_of_kx_le_alpha` (regime `kx ≤ alpha`) and `budgeted_stochasticity_to_plain_corner_of_beta_le` (regime `beta ≤ baseBudget`) plus an explicit `hHard` hypothesis for that single remaining regime. Since the corner trivially implies each regime, `hHard` is exactly equivalent to the open corner (given the two proved leaves). This is a reduction only; `hHard` is not assumed to hold. The residual `log beta` charge in the superpolynomial-`beta` sub-regime is the genuine active crux.
- `logSlack_le_of_le_pow` and `budgeted_stochasticity_to_plain_corner_of_beta_le_pow` prove the hard corner whenever `beta ≤ baseBudget ^ k` for any fixed `k`. Thus only the regime not controlled by a fixed polynomial budget remains in this reduction lane.
- `BudgetedCornerLengthScale.lean` (proved, sorry-free) removes the deficiency parameter from the residual slack. `budgeted_plain_corner_of_length_le_beta` proves the corner outright, with no stochasticity hypothesis, whenever `l(x) ≤ kx + beta`: the full cube at the length of `x` is then already a corner model. Combining this with the §3 chain gives `budgeted_stochasticity_to_plain_corner_add_logSlack_min`, whose residual is `logSlack c (min beta l(x))` instead of `logSlack c beta`, and hence `budgeted_stochasticity_to_plain_corner_length_scale` (slack `logSlack c (baseBudget + l(x))`, no `beta`), `budgeted_stochasticity_to_plain_corner_of_min_le_pow`, `..._of_length_le_pow` and `..._of_length_or_beta_le_pow`: the exact budget-scale corner holds as soon as *either* `beta` or `l(x)` is bounded by a fixed power of `baseBudget`.
- `plainSetComplexity_fullCube_le_KPPlain_natCode` sharpens the cube gate from `O(log l(x))` to `K(l(x)) + O(1)`, and `budgeted_plain_corner_of_simple_length` uses it to prove the exact budget-scale corner for arbitrarily long strings: it suffices that `K(l(x)) ≤ m ≤ alpha` for some `m` with `l(x) ≤ beta` or `l(x) + m ≤ kx + beta`.
- `budgetedPlainCorner_of_hard_regime_superpoly` assembles these into the sharpest current reduction: for any fixed `k`, the full `BudgetedPlainProfileCornerStatement V U` follows from the corner in the regime `alpha < kx ≤ baseBudget`, `baseBudget ^ k < beta`, `baseBudget ^ k < l(x)`, plus the failure of the simple-length condition (`beta < l(x)` and `kx + beta < l(x) + m` for every bound `m ≤ alpha` on `K(l(x))`). As before this is a reduction only; the hypothesis is not assumed to hold.

- Iteration 112 (continued) adds `UpwardOrdinalNoiseTransportPow.lean` (proved, sorry-free). `budgetedRandomNoiseTransport_of_beta_le_pow` repeats the assembly of `budgetedRandomNoiseTransport_of_beta_le` with the budget-scale corner supplied by `budgeted_stochasticity_to_plain_corner_of_beta_le_pow`, and `strongModelOrdinalNoiseTransport_of_beta_le_pow` upgrades the consumer-shaped ordinal transport from the linear regime `beta <= n + epsilon + logSlack cBudget n` to `beta <= (n + epsilon + logSlack cBudget n) ^ k` for every fixed exponent `k`. The residual obstruction is now only the regime where `beta` exceeds every fixed power of the model-code budget. In `BudgetedCornerMinimalWitness.lean`, `levelSet_level_lower_of_beta_minimal` (with the `ENNReal` scale helper `two_inv_pow_le_two_pow_mul_two_inv_pow`) completes the tight-level diagnostic: at a coordinate where the deficiency cannot be lowered to `beta - 1`, a model giving `z` mass at least `2⁻¹ ^ k` forces `KP(z | P.code) + beta <= k + 1`.
- Iteration 113 adds `UpwardOrdinalNoiseRegimes.lean` (proved, sorry-free). Since the consumer transport radius `c * epsilon + logSlack c n` is independent of `(alpha, beta)`, `strongModelOrdinalNoiseTransport_of_witness_beta_le_pow` widens the discharged region along the witness axis: whenever *some* stochasticity witness `(a, b)` below `(alpha, beta)` for the model code has `b <= (n + epsilon + logSlack cBudget n) ^ k`, the polynomial-regime transport `strongModelOrdinalNoiseTransport_of_beta_le_pow` for `(a, b)` transfers upward to `(alpha, beta)` by `isStochastic_mono`. Feeding this the Pareto-minimal witness from `exists_pareto_minimal_stochastic_witness` yields the unconditional theorem `strongModelOrdinalNoiseTransport_dichotomy`: for every fixed exponent `k` and every stochasticity witness of the model code, either the ordinal pair is already stochastic at the source-scale radius, or a Pareto-minimal witness below it satisfies `baseBudget ^ k < b`. This pins the residual of this consumer lane, for each chosen `k`, to the Pareto-minimal above-fixed-power model-code case, now as a *proved dichotomy* rather than an assumed interface. It does not assert that one witness is simultaneously above every polynomial. Nothing here is assumed and no unconditional `prop_upward` is manufactured.
- Iteration 113 (continued) adds `UpwardOrdinalNoiseAlphaRegime.lean` (proved, sorry-free), which widens the discharged region along the orthogonal *complexity* axis. `strongModelOrdinalNoiseTransport_of_alpha_ge` proves the consumer transport conclusion unconditionally, for every `beta` and with no stochasticity hypothesis at all, whenever `2 * (n + epsilon + logSlack cBudget n) <= alpha`: the ordinal pair `pairCode (codedUniformOn A hA).code (strongModelOrdinalBits A x)` has plain complexity at most `2 * baseBudget + O(log baseBudget)` (`plainK_strongModelCode_le`, `finiteSetLogCard_le_length_add_deficiency_log`, `plainK_pair_le_plainK_add_length_budget`), so its own Dirac model (`isStochastic_dirac_of_plainK`) already fits the complexity budget with deficiency `0`, and the leftover logarithms are absorbed by `upward_ordinal_noise_radius_absorb`. Combining this with `strongModelOrdinalNoiseTransport_dichotomy` gives `strongModelOrdinalNoiseTransport_trichotomy`: for each fixed exponent `k`, every stochasticity witness of the model code either already yields transport at the source-scale radius, or lies in the *small-alpha, large-beta* corner `alpha < 2 * (n + epsilon + logSlack cAlpha n)` together with a Pareto-minimal sub-witness with `(n + epsilon + logSlack cBudget n) ^ k < b`. As before the second branch only describes the residual case; no transport is asserted there and no unconditional `prop_upward` is manufactured.
- Iteration 114 adds `WidthChargedNoiseTransport.lean` and `UpwardOrdinalNoiseWidthRegimes.lean` (both proved, sorry-free), widening the discharged region along a third, *width-slack* axis. `KP_fst_cond_le_pair_cond_pair_width` (L1) removes the known short model-width code `natCode m` from the condition at cost `logSlack c m`; `pairUniformExtension_stochasticity_width_charged` (L2) feeds it into `pairUniformExtension_stochasticity_of_condition_bound` to obtain, with **no** hypothesis on `beta`, purity, or `l(a)`, `IsStochastic U (pairCode a u) (alpha + logSlack c m) (beta + m + logSlack c m + c)` — the coupling of a model code to its ordinal index is paid for by exactly `m = log #A` of deficiency. `strongModelOrdinalNoiseTransport_of_width_slack` (L3) instantiates L2 at the consumer ordinal data (`upward_ordinal_noise_radius_absorb` collapses the logarithms into `c * epsilon + logSlack c n`), proving the consumer transport unconditionally whenever *some* stochasticity sub-witness `(a, b)` below `(alpha, beta)` for the model code satisfies `b + finiteSetLogCard A + logSlack c n <= beta`. Feeding this the Pareto-minimal witness gives `strongModelOrdinalNoiseTransport_width_dichotomy` (transport, or a Pareto-minimal witness in the *near-Pareto width sliver* `beta < b + finiteSetLogCard A + logSlack c n`), and combining with `strongModelOrdinalNoiseTransport_trichotomy` gives `strongModelOrdinalNoiseTransport_width_trichotomy`: for each fixed exponent `k` the residual of the whole consumer lane is pinned to the *intersection* — a Pareto-minimal witness with small complexity `alpha < 2 * (n + epsilon + logSlack cAlpha n)`, superpolynomial deficiency `(n + epsilon + logSlack cBudget n) ^ k < b`, and a near-Pareto width sliver `beta < b + finiteSetLogCard A + logSlack c n`. This is strictly smaller than the residual of either previous dichotomy. As before every disjunct's second branch only describes the residual case; nothing is assumed and no unconditional `prop_upward` is manufactured.
- Iteration 115 adds three reusable infrastructure lemmas for the purity-charged route, all proved and sorry-free. `RadiusMonotone.lean` factors the charged-radius bookkeeping that had been inlined in the regime files: `logSlack_radius_mono` (`c' <= c -> c' * epsilon + logSlack c' n <= c * epsilon + logSlack c n`) and `isStochastic_radius_mono`, which lifts stochasticity at a smaller charged radius to a larger one; `UpwardOrdinalNoiseAlphaRegime.lean` and `UpwardOrdinalNoiseWidthRegimes.lean` now use them instead of local `hradius` blocks. `CondRelativeInfo.lean` proves `KP_cond_remove_relative_info`, the relativized strengthening of `KP_cond_remove_short_info`: dropping `z` from a condition costs only `KP U z y` (the complexity of `z` *given* `y`) rather than the unconditional `KPPlain U z`, by the same two-stage conditional decoding argument. `PurityChargedArithmetic.lean` proves `purity_charged_arithmetic_absorb`, the pure `Nat`/`logSlack` bookkeeping that folds the purity-charged overhead `cExt * (eps + rho + logSlack cBound m + logSlack cBound k_a + logSlack cNat m + cNat + cCond) + logSlack cExt m + cExt` into a single charged shape `C * eps + C * rho + logSlack C B`, together with the supporting bound `length_natBits_programWitness_le` on the binary length of a program-length witness. No frozen statement is touched and no unconditional `prop_upward` is manufactured.
- Iteration 106 adds `BudgetedCornerSharpProfile.lean` (proved, sorry-free). `isOptimalSetStochastic_imp_profile_sharp` converts an optimal finite-set stochasticity witness into a description-profile point with **no** logarithmic slack at all (`i ≤ alpha` and `i + j = K(x) + beta` exactly): unlike `isOptimalSetStochastic_imp_profile` the size coordinate is left free, so no description shift and hence no address has to be encoded. `budgeted_plain_corner_of_isOptimalSetStochastic` derives from it, unconditionally, the exact budget-scale plain corner for every *optimal-set* witness, with slack only `logSlack c kx` (no `l(x)`, no `beta`). Consequently `budgetedPlainCorner_of_optimalSetConversion_budget` reduces the whole open corner to a single statement — the source's optimal-set conversion (Theorem 3) with its logarithmic loss measured against `K(x)` alone instead of `K(x) + alpha + beta`. Both are reductions only; neither hypothesis is assumed anywhere.

- Iteration 10 rewrites `PropUpwardFrontier.lean` to expose `BudgetedWitnessPurityStatement` as the sole remaining obligation for `prop_upward`. By combining the transport bounds with the purity hypothesis, `propUpward_of_budgetedWitnessPurity` frames the mathematical crux exactly around whether the frozen `O(ε + log l(x))` radius is achievable over arbitrary witnesses of the model code, raising an explicit interface question for human review.
- Iteration 109 adds `LemmaUpwardCruxStatement.lean` (stub-free research interface, no `sorry`/`axiom`). `LemmaUpwardCruxStatement U` names, as a standalone `def`, the exact `α,β`-independent optimal-set conversion hypothesis `hConv` of `propUpward_of_optimalSetConversion_budget` (slack `logSlack c p` measured against `K(x) = p` alone), analogous to S9's research-only `LemmaOmpExactRadiusStatement`. It is consumed only as a hypothesis of that frontier wrapper and is **never** discharged; naming it is a pure refactor that leaves the frontier unchanged — the single open `prop_upward` obligation whose truth is unestablished in the superpolynomial-`beta` regime.
- Iteration 109 also adds `LemmaUpwardCruxReduction.lean` (proved, sorry-free). It narrows the upward crux to a proper sub-regime, by four reductions. (i) `isOptimalSetStochastic_singleton_of_KPPlain` proves that the canonical singleton `{x}` is an optimal set model of complexity `K(x) + O(1)`, discharging the regime `K(x) <= alpha`. (ii) For any fixed exponent `k`, the polynomial regime `beta <= K(x) ^ k` is discharged by the proved `stochasticity_to_optimal_set_budget`, whose charge `logSlack c (K(x)+alpha+beta)` folds there into a single `logSlack C (K(x))` via `logSlack_linear_bound` and `logSlack_le_of_le_pow`. (iii) `setComplexity_fullCube_le_KPPlain_natCode` (the prefix-level cube gate at the complexity scale) and `isOptimalSetStochastic_fullCube_of_simple_length` discharge the simple-length regime, where `l(x) + m <= K(x) + beta` for some bound `m <= alpha` on `K(l(x))`. (iv) `exists_pareto_minimal_stochastic_witness` lets one pass to a Pareto-minimal witness for free. Hence `lemmaUpwardCrux_of_hardRegime` derives the full `LemmaUpwardCruxStatement U` from the strictly weaker `LemmaUpwardCruxHardRegimeStatement U k` — the same conversion restricted to Pareto-minimal witnesses with `alpha < K(x)`, `K(x) ^ k < beta` and a non-simple length — and `propUpward_of_hardRegimeCrux` exposes that restricted hypothesis as the sole remaining obligation for `prop_upward`. This is a reduction only: the hard-regime statement is never assumed to hold and is not discharged.
- Iteration 110 adds `LemmaUpwardCruxSlackRegime.lean` (proved, sorry-free). It sharpens both discharged boundaries of iteration 109 by a logarithmic margin: for *every* margin constant `w`, `lemmaUpwardCrux_of_hardRegime_slack` derives the full `LemmaUpwardCruxStatement U` from `LemmaUpwardCruxHardRegimeSlackStatement U k w`, i.e. the conversion restricted to Pareto-minimal witnesses with `alpha + logSlack w K(x) < K(x)`, `K(x) ^ k < beta`, and `K(x) + beta < l(x) + m` for every bound `m <= alpha + logSlack w K(x)` on `K(l(x))`. The extra margin is affordable because the conclusion's own `logSlack c K(x)` absorbs both the singleton gate constant and the cube gate constant (`logSlack_add_const_le`). `lemmaUpwardCruxHardRegimeSlackStatement_of_hardRegimeStatement` certifies formally that the new regime is a sub-regime of the iteration-109 one, and `propUpward_of_hardRegimeCrux_slack` re-exposes it as the sole remaining obligation for `prop_upward`. As before this is a reduction only; the hard-regime statement is never assumed and is not discharged.

Iteration 103 adds `BudgetedAddNoisePolySize.lean` (proved, sorry-free), which
confines the open size-coordinate regime of `BudgetedPairProjectionStatement`
to superpolynomial `j`; see the low-branch list below.

`BudgetedAddNoiseGainRegime.lean` (proved, sorry-free) adds the orthogonal
*gain* axis of the same compression input.
`inPlainDescriptionProfile_of_small_condK_gain` is a slack-free leaf: whenever
the claimed compression gain `g` is bounded by the available slack `s`, the
given model `H` itself already witnesses the description-profile point
`(iH - g + s, j1 + s)`, so no compression has to be performed and no optimality
hypothesis is needed.  Combining it with the intrinsic-size regime
`budgetedConditionalCompression_of_card_le_pow` gives
`budgetedConditionalCompression_of_card_le_pow_or_small_gain`: for every fixed
exponent `k` and margin `w`, the body of
`BudgetedConditionalCompressionStatement` holds for every model that is either
polynomially small in the budget (`|H| <= 2 ^ budget ^ k`) or carries at most
`logSlack w budget` bits of information about `x`.  The residual is thus
confined to models that are simultaneously superpolynomially large in the
complexity budget and informative about the string they describe.  This is a
partial discharge only: the disjunction is proved for each model satisfying it,
it is not claimed for all models, and nothing here discharges
`BudgetedConditionalCompressionStatement` or the frozen
`BudgetedPairProjectionStatement`.

The S9 interface repair at radius `3 * epsilon` is complete.  The unconditional
`prop_add_noise` and `rem_add_noise` proofs are kernel-checked.  Their direct
length-scale route uses heavy truncation, finite-set symmetry, a conditional
rank index, and `exists_description_smaller_complexity_of_many_logSlack` in
`RemAddNoiseLowBranch.lean`.  The distinct-truncation route is also connected
to that complexity-drop theorem by
`inDescriptionProfile_of_noise_information_gain` in
`AddNoiseMultiplicity.lean`; it is a proved provenance theorem, not an open
dependency of the public endpoints.

The budget-scale charged-heavy route now contains the following proved pieces:
`chargedHeavyNoiseCandidates` and `chargedHeavyNoiseCandidatesRaw` with their
structural soundness; the computable, duplicate-free, append-only appearance
enumeration `chargedHeavyAppearanceCodes_spec`; the length-free rank bounds
`condK_chargedHeavyCandidate_of_card_lt_pow` and
`condK_chargedHeavyCandidateRaw_of_card_lt_pow`; the prefix set-complexity and
multiplicity packages `manyIJDescriptions_of_chargedHeavyNoiseCandidates` and
`manyIJDescriptions_of_chargedHeavyNoiseCandidatesRaw`; and the independent
charge-cancellation arithmetic `addNoise_charge_cancels`.
`ChargedHeavyNoiseGain.lean` now supplies the missing rank-plus-suffix decoder
and proves
`chargedHeavyNoiseCandidatesRaw_card_lower_of_information_gain`: exact
conditional information gain from the true heavy truncation, together with
conditional randomness of the noise, forces the required raw-candidate
cardinality with no `x.length` term. The arbitrary size coordinate is charged
explicitly by `2 * (Nat.bits j).length`; all other overhead is
`logSlack c baseBudget + logSlack c noiseLen`.
That cardinality bound is now packaged directly as
`manyIJDescriptions_of_chargedHeavy_information_gain`, which turns an exact
charged information gain into
`ManyIJDescriptions U x (i + logSlack c |y|) (j - threshold + 1) k` with
`k = gain - epsilon - (2 * (Nat.bits j).length + logSlack c baseBudget +
logSlack c |y|)`.
Iteration 100 also proves
`inDescriptionProfile_of_charged_many_length_free`, which composes a genuinely
charge-balanced `ManyIJDescriptions` witness with the length-free
complexity-drop theorem and `addNoise_charge_cancels`.

The budgeted low branch is now decomposed as follows.  Every declaration is
`sorry`-free; the proposition-valued research targets below are deliberately
not asserted (`BudgetedAddNoiseLowBranch.lean`):

- `inPlainDescriptionProfile_fst_of_heavy_fibre_budgeted` — proved: the
  heavy-fibre case, where the fibre of the pair model over `x` is at least
  `l(y)` long.  Its whole slack is `O(log l(y))`.
- `inPlainDescriptionProfile_of_condK_compression_size_scale` — proved: a model
  `H` of `x` can be replaced by one whose complexity drops by the full
  conditional complexity `C([H] | x)`, with slack `O(log (C(H) + log #H))`.
- `BudgetedConditionalCompressionStatement` — the same compression with the
  slack measured against a complexity budget only. This is only a research
  reduction and the existing charged producer does not discharge it. It is
  *not* assumed anywhere unconditionally.
- `BudgetedPairProjectionStatement` — the exact pair-projection conclusion,
  retained as an unproved proposition rather than an unconditional theorem.
- `BudgetedPairProjectionManyStatement` and `budgetedPairProjection_of_many` —
  the exact consumer-shaped direct route: a producer must return a genuine
  `ManyIJDescriptions` witness together with the two inequalities that absorb
  the length-free complexity-drop and prefix-to-plain bridge costs.  The final
  bounds contain neither `j` nor `x.length`.
- `budgetedChargedHeavyAppearanceCodes_computable`, `_mono`, `_sound`, and
  `_complete`, together with
  `mem_pooledChargedHeavyNoiseCandidates_of_heavy_fibre` — proved pooled,
  append-only enumeration infrastructure over all stratum codes.  The
  complexity coordinate is clamped to `baseBudget`, the threshold to the noise
  length, and the size coordinate is deliberately left raw.  Thus its external
  parameters are `baseBudget` and the noise length, while it still covers
  `baseBudget < j` without making `j` an advice field.
- `budgetedChargedHeavyGainDecoder_partrec`,
  `mem_budgetedChargedHeavyGainDecoder`, and
  `budgetedChargedHeavyGainProgram_length_slack` — proved computability,
  correctness, and the budget/noise-scale program-length bound for the
  all-size rank-plus-suffix decoder.  Its packed program carries the noise
  length, base budget, and rank width, but no `j`.  The remaining direct-route
  cardinality contradiction is
  `exists_budgetedChargedHeavyAppearanceCodes_many_of_information_gain`: it
  proves that exact information gain forces a stage containing exponentially
  many distinct pooled truncation codes with slack depending only on the
  complexity budget and noise length.  The remaining direct-route leaf is the
  weighted fixed-stratum conversion of those pooled truncations into
  `BudgetedPairProjectionManyStatement`.
- `pooledChargedHeavyNoiseCandidates_setComplexity_le`,
  `manyIJDescriptions_of_pooled_family`,
  `manyIJDescriptions_of_pooled_family_of_gap`, and
  `manyIJDescriptions_of_budgetedChargedHeavyAppearanceCodes`
  (`BudgetedChargedHeavyNoiseMultiplicity.lean`, proved, sorry-free) — the
  combinatorial half of that conversion.  Every pooled candidate, from whatever
  stratum and however large that stratum's raw size coordinate, is a
  description of `x` of prefix set complexity at most
  `baseBudget + logSlack c noiseLen`; hence any collection of pooled candidates
  of cardinality at least `2 ^ k` whose members have at most `2 ^ J` elements —
  a condition readable off the strata alone, by the size/threshold gap — is a
  `ManyIJDescriptions U x (baseBudget + logSlack c noiseLen) J k` certificate,
  and the same holds for the size-filtered sublist of the codes listed at any
  finite stage of the pooled enumeration.  So the complexity coordinate of the
  pooled route is already budget scale and free of `j`; only the size
  coordinate still has to be supplied by the caller.  These are packaging
  lemmas for the pooled family, not steps of the unconditional `prop:upward`
  chain: the pair-projection consumer of this lane is refuted at the end of
  `BudgetedPairProjectionMany.lean`.
- `budgetedChargedHeavyNoiseCandidatesRaw_card_lower_of_information_gain` —
  proved budget-scale cardinality bound in the already bounded branch
  `j ≤ baseBudget`, by absorbing the old explicit bit-length charge into
  `logSlack _ baseBudget`.
- `inPlainDescriptionProfile_fst_of_pair_model_budgeted_core` and
  `..._of_conditionalCompression` — proved: the full reduction of the frozen
  target to that statement (heavy-fibre split, finite-set symmetry of
  information for the heavy truncation, the fibre lower bound from conditional
  randomness of `y`, and the final chunking, all at the budget scale).
- `inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le` — proved
  unconditionally: the branch in the regime `j ≤ baseBudget`, where the
  size-scale compression is already budget-scale.

- `inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le_pow`
  (`BudgetedAddNoisePolySize.lean`, proved, sorry-free) removes every
  polynomially large size coordinate from that residual regime: for each fixed
  `k` the exact budget-scale conclusion holds whenever
  `j ≤ (baseBudget + l(y)) ^ k`.  It applies the proved small-size branch at
  the enlarged budget `max baseBudget j` and folds the resulting logarithmic
  slack back into `baseBudget` and `l(y)` via `logSlack_max_le_of_le_pow`.
  The same folding gives `budgetedConditionalCompression_of_size_le_pow`: the
  body of `BudgetedConditionalCompressionStatement` holds whenever the log-size
  of the compressed model is at most `budget ^ k`.

Hence only the regime where the size coordinate `j` is *superpolynomially*
larger than the complexity budget keeps `BudgetedPairProjectionStatement`
unproved; that is exactly the residual `log j` charge of the multiplicity
family.
This reverse ordinary-profile projection is not itself the forward
`BudgetedRandomNoiseTransportStatement`; the forward stochasticity bridge and
the unconditional `prop_upward` remain separate obligations.

### Iteration 114: the pair-projection Many lane is unsatisfiable (dead end, not an interface problem)

The `def`s `BudgetedPairProjectionStatement` and `BudgetedPairProjectionManyStatement`
(`BudgetedAddNoiseLowBranch.lean`) are **provably unsatisfiable**, so the mandated
"weighted fixed-stratum conversion of the pooled truncations into
`BudgetedPairProjectionManyStatement`" targets a false proposition and cannot be
completed on this lane.  Diagnosis: their only complexity premise is
`i ≤ baseBudget`; they carry **no** bound on `plainK V x` (nor on `x.length`).
Take `x` incompressible of length `n ≫ baseBudget` and `y = []` (so the randomness
premise is vacuous); the full cube of `pairCode x []` is an `(O(log n), 2n)`-plain
description with `i = O(log n) ≤ baseBudget`.  Any `ManyIJDescriptions U x I J K`
certificate gives a two-part code of `x`, so `I + J ≥ KP(x) - O(log) ≳ n`; hence the
third inequality of `BudgetedPairProjectionManyStatement`
(`I - K + logSlack cDrop (I+J) + cBridge ≤ i + epsilon + logSlack c baseBudget + logSlack c y.length`,
consumed at `budgetedPairProjection_of_many` around line 544) forces
`logSlack cDrop (I+J) ≈ cDrop·log n ≤ [bounded independently of n]`, impossible.
The COVERAGE claim above that "the final bounds contain neither `j` nor `x.length`"
is literally true of the *displayed* terms but misleading: `logSlack cDrop (I+J)`
is an **implicit** `Ω(log x.length)` charge.  The residual regime is therefore not
"superpolynomial `j`" but *unbounded `l(x)`*.

This is **not** an `INTERFACE_PROBLEM`.  The two frozen statements are unaffected:
`BudgetedRandomNoiseTransportStatement` (`UpwardConditional.lean:25`) carries the
premise `plainK V x ≤ baseBudget`, which bounds the relevant `i + j` by
`baseBudget + l(y) + O(log)` and makes `logSlack cDrop (I+J)` absorbable into
`logSlack c baseBudget + logSlack c l(y)` via the existing `logSlack_add_le`.  The
sound repair for this lane is to thread that model-size bound (`i + j ≤
baseBudget + l(y) + O(log)`, or `plainK V x ≤ baseBudget`) through the projection
`def`s; as they stand they are honest, never-asserted research reductions that are
simply too strong.  The lane also does not by itself feed `prop_upward` (see the
paragraph above and `BudgetedAddNoiseLowBranch.lean:49-52`).

### Iteration 114: live corner route — ball models

The unconditional `prop_upward` route runs through the corner
`BudgetedPlainProfileCornerStatement` (`prop_upward ←
BudgetedRandomNoiseTransportStatement ← BudgetedPlainProfileCornerStatement`), whose
open part is the hard regime `alpha < kx ≤ baseBudget`, superpolynomial `beta` and
`l(x)`, with the simple-length gate failing.  `BudgetedCornerBallModels.lean` adds
two unconditional leaves toward the *rounded-length* widening of that gate:

- `budgeted_plain_corner_of_ball_length` (proved, sorry-free): the exact
  budget-scale plain corner from a ball model `stringsOfLengthLe n` at any free
  radius `n ≥ l(x)` with simple address `K(n) ≤ m ≤ alpha` and `n + 1 + m ≤ kx +
  beta`.  The `n := l(x)` instance is a ball analogue of
  `budgeted_plain_corner_of_simple_length`; the free `n` lets one round up to a
  radius of far smaller address complexity.
- `exists_rounded_multiple` (proved, sorry-free): the pure-`Nat` rounding
  primitive — for any `l, t` the ceiling multiple `q·2^t` of `2^t` above `l`
  satisfies `l ≤ q·2^t < l + 2^t` and `q ≤ l/2^t + 1`.

The `BudgetedCornerRoundedLength.lean` root (proved, sorry-free) now assembles the
rounded-length corner honestly.  Its leaves:

- `KPPlain_natCode_mul_pow_two_le` (proved): `K(natCode (q·2^t)) ≤ K(natCode q) +
  K(natCode t) + O(1)`, the address-splitting bound.
- `budgeted_plain_corner_of_rounded_multiple` (proved): feeds an explicit `(q,t,m)`
  into `budgeted_plain_corner_of_ball_length` with `n := q·2^t`.
- `length_le_roundedMultiple` (proved): the witness-explicit `l ≤ ⌈l/2^t⌉·2^t`.
- `budgeted_plain_corner_of_rounded_length` (proved): the ceiling specialisation —
  fix `t`, round `l(x)` up to `n = ⌈l(x)/2^t⌉·2^t`, and produce the corner *given*
  the two-part budget hypothesis `n + 1 + m ≤ kx + beta` (with `K(⌈l(x)/2^t⌉) +
  K(t) + O(1) ≤ m ≤ alpha`).
- `budgeted_plain_corner_of_rounded_length_log` (proved): the same with the abstract
  `K(natCode ·)` bounds discharged via `K(natCode n) ≤ 2·|bits n| + O(1)`, so the two
  side conditions become purely arithmetic in `t` and `l(x)`.

**Correction (retired false leaf).**  Iteration 5 removed a `sorry`-backed leaf
`rounded_length_radius_fits_budget` that claimed to *derive* the existence of a good
`(n,m)` from an `alpha`-only condition (roughly "`alpha ≳ 2·log(l(x)/S)` at
`t = log₂(S/2)`").  That statement is **mathematically FALSE**: when the two-part
slack `S = kx + beta - l(x)` is small (e.g. `S = 2 ⇒ t = 0 ⇒ n = l(x)`) but `l(x)`
is large, `n + 1 + m ≤ kx + beta` forces `m ≤ 1` while `m ≥ K(natCode l(x)) ≈
2·log l(x)`, so no witness exists regardless of `alpha`.  The earlier COVERAGE claim
that this "lowers the `alpha` demand to `≈ 2·log(l(x)/S)`" is therefore only correct
*when `S` is large enough to absorb `2^t + K(q) + K(t) + O(1)`*; the corner genuinely
fails for small `S`.  The honest theorems above encode this as a *sufficient
condition* (the caller must exhibit a budget-fitting `t`), not an `alpha`-only gate.

**Wiring status (wired, conditional).**  Iteration 5 wired the rounded-length corner
into the hard regime as `budgetedPlainCorner_of_hard_regime_rounded_minimal_tight`
(`LemmaUpwardCruxRoundedRegime.lean`).  It reduces `BudgetedPlainProfileCornerStatement`
to a hard-regime hypothesis `hHard` that *additionally* assumes the **failure** of the
rounded-length gate for every exponent `t` (`∀ t, alpha < address(t) ∨ kx + beta <
radius(t) + address(t)`, at the `Classical.choose` constant
`roundedCornerLogConstant = c` of `budgeted_plain_corner_of_rounded_length_log`); the
rounded-gate-**success** case is discharged directly by that log-explicit corner.  It is
exposed as `propUpward_of_corner_hard_regime_rounded` in `PropUpwardFrontier.lean`.  This
is a strict *narrowing* of the earlier `..._superpoly_minimal_tight` residual — the
rounded-gate-success sub-regime is now closed — but it is **conditional**: `hHard` is
never discharged, so no unconditional `prop_upward` is produced.

**Correction (iteration 5 final review — second retired false leaf).**  The intermediate
draft additionally introduced a `sorry`-backed leaf `exists_rounded_corner_exponent`
(one standalone copy in a scratch `TempExponent.lean` with a forbidden broad
`import Mathlib`, one in `LemmaUpwardCruxRoundedRegime.lean`) asserting the existence of
a good `t` with `2^t + 2·|bits ⌈l/2^t⌉| + 2·|bits t| + c ≤ min S alpha` whenever
`S, alpha ≥ c·|bits l| + c`.  That statement is **mathematically FALSE** — at `l = 0`,
`|bits 0| = 0` makes the hypotheses `c ≤ S`, `c ≤ alpha`; taking `S = alpha = c` gives
`min S alpha = c`, yet `2^t ≥ 1` forces the left side above `c` for every `t` and every
constant `c` — and it is also mis-shaped: it charges the radius term `2^t` to `alpha`,
whereas the genuine consumer charges `2^t` (inside the radius `⌈l/2^t⌉·2^t ≈ l + 2^t`)
to the **two-part** budget `kx + beta` and only the address to `alpha`.  Both copies were
removed (the scratch file deleted); the leaf was dead (consumed by nothing, since the
hard-regime wrapper uses the gate *failure* directly), so removal changes no proved
result.  The corrected *two-budget* existence statement is recorded as an Aristotle leaf.

## SUV book

| Chapter / § | Status | Lean home | Key theorems |
|---|---|---|---|
| 1.1 Plain complexity: definition, invariance | ✅ | `Core/Basic.lean`, `Core/UniversalDecompressor.lean`, `Core/Invariance.lean` | `condK`, `plainK`, `isOptimalConditional`, `existsIsOptimalConditional` |
| 1.1 Incompressibility / counting | ✅ | `Complexity/Incompressibility.lean` | `existsIncompressibleString`, `cardCompressibleWordsLt`, `existsComplexString` |
| 1.2 Algorithmic properties (non-computability, semicomputability) | ✅ | `Complexity/Uncomputability.lean`, `Complexity/Properties.lean` | `notComputablePlainKNat`, `noComputableUnboundedLowerBound`, `condKLeIsRe`, `plainKGtIsCore` |
| 2.1 Complexity of pairs (plain) | 🟡 | `Prefix/Properties.lean` (via prefix bridges) | `plainK_pair_le_KPPair`, `plainK_pair_le_KPPlain_add_KPPlain` — no standalone plain-pair theory |
| 2.2 Conditional complexity | ✅ | `Core/Basic.lean`, `Complexity/Properties.lean` | `condK`, `condKSelf`, `condKLePlainK`, `condKComp` |
| 2.3 **Symmetry of information, plain (Kolmogorov–Levin, O(log))** | ✅ | `AlgorithmicStatistics/StrongModels/PlainSymmetry.lean` | `KP_le_condK_of_logSlack_budget`, `plainK_add_condK_symmetry`, `condK_reverse_of_plain_complexity_gap` |
| 2.3 **Symmetry of information, plain (Kolmogorov–Levin, O(log))** | ✅ | `CommonInformation/PlainSymmetry.lean` | `pairPlainK_chain_lower_values`, `pairPlainK_chain_upper_values`, `pairPlainK_symmetryOfInformation_values` |
| 3 Martin-Löf randomness | ➖ | — | infinite sequences; deferred |
| 4.1–4.2 Semimeasures on ℕ, maximal semimeasure | ✅ | `AlgorithmicProbability/Semimeasure.lean`, `UniversalSemimeasure.lean` | `IsSemimeasure`, `IsUniversalSemimeasure`, `exists_universalSemimeasure` |
| 4.3–4.4 Prefix machines | ✅ | `Prefix/Basic.lean`, `Prefix/Machine.lean`, `Prefix/Optimal.lean`, `Prefix/OptimalExistence.lean` | `IsPrefixMachine`, `KP`, `IsOptimalPrefixConditional`, `exists_isOptimalPrefixConditional` |
| 4.5 Coding theorem `K = −log m + O(1)` | ✅ | `AlgorithmicProbability/Coding.lean`, `ConditionalCoding.lean`, `KraftChaitin*.lean` | `universalSemimeasure_equiv_prefixComplexity`, `complexityWeight_KP_le_aprioriMeasure` |
| 4.5 Kraft inequality + converse | ✅ | `Prefix/Kraft.lean`, `Prefix/KraftConverse.lean`, `Prefix/CountableKraft.lean` | `finset_kraft_progWeight_le_one`, `exists_prefixFree_code_of_kraft_le_one` |
| 4.6 Properties of prefix complexity | ✅ | `Prefix/Properties.lean`, `Prefix/CountingBound.lean`, `Prefix/TotalCountingBound.lean` | assorted |
| 4.7 Conditional prefix complexity, pairs, SOI | ✅ | `Prefix/Symmetry.lean`, `Prefix/ConditionalSymmetry.lean`, `Prefix/CondTwoStage.lean`, `Prefix/KPPairSwap.lean` | `KPPair_symmetryOfInformation_staged`, `KPCondPair_symmetryOfInformation_staged` |
| 5 Monotone complexity | ➖ | — | deferred |
| 6 General scheme for complexities | ❌ | — | |
| 7 Shannon entropy ↔ complexity | ❌ | — | **recommended next** (SUV track) |
| 8 Applications | ❌ | — | |
| 9 Frequency/game randomness | ➖ | — | deferred |
| 10 Inequalities for entropy/complexity/size | ❌ | — | after ch. 7 |
| 11 Common information | ❌ | — | |
| 11 Common information | ✅ | `CommonInformation/Definitions.lean`, `PlainCoding.lean`, `PlainSymmetry.lean`, `Splitting.lean`, `Intermediate.lean`, `Nested.lean`, `Basic.lean`, `Interfaces.lean`, `OverlapGeometry.lean`, `SharedDescription.lean`, `SharedDescriptionLengths.lean`, `OverlapExtraction.lean`, `Counting.lean`, `ConditionalCounting.lean`, `WorstCaseCounting.lean`, `CompactAdvice.lean`, `WorstCaseRegionBounds.lean`, `WorstCaseRegionCounting.lean`, `WorstCaseRegionAdvice.lean`, `WorstCaseRegionStages.lean`, `WorstCaseRegionSearch.lean`, `WorstCaseRegionSelector.lean`, `WorstCaseRegion.lean`, `WorstCaseSelector.lean`, `WorstCase.lean`, `CommonWitnessCoding.lean`, `RegionEnvelopes.lean`, `RegionLower.lean`, `RegionConsequences.lean`, `RectangleCover.lean`, `NoFourCycleDensity.lean`, `IncidenceCoverArithmetic.lean`, `AffineIncidence.lean`, `ConcreteField.lean`, `IncidenceCodecs.lean`, `IncidenceRegion.lean`, `IncidenceConsequences.lean`, `QuadraticIncidenceClasses.lean`, `IncidenceRectangleCapacity.lean`, `IncidenceCapacityCover.lean`, `IncidenceRegionUniformity.lean`, `Relativized.lean`, `ConditionalIndependence.lean`, `FiniteQuadruple.lean`, `ConditionalIndependenceChains.lean`, `FixedFrequency.lean`, `FixedHistogram.lean`, `FixedHistogramCoding.lean`, `TypeBounds.lean`, `FixedHistogramRank.lean`, `ChainHistogram.lean`, `FixedHistogramProjectionParams.lean`, `ChainWitness.lean`, `ChainFibre.lean`, `MaximalSampleFibre.lean`, `ChainSample.lean`, `ChainNonextractabilityEngine.lean`, `ChainNonextractability.lean`, `GacsKornerSupport.lean` | exact plain values and shortest programs; plain SOI; Theorem 221: `exists_incompressibleRepresentation`; Exercise 305: `exists_split_incompressible_halves`; Exercise 306: `exists_intermediate_split_conditionalComplexity`; Theorem 222: `exists_nested_incompressibleRepresentations`; C3 interfaces: `MutualInformationWithin`, `ExtractableCommonInformationWithin`, `CommonInformationRegion`, `OverlapRepresentationWithin`, `RawSharedDescriptionWithin`, `commonInformationRegion_upward_closed`, `nearLength_decodable_is_equivalent_incompressible`; C3 overlap geometry: `literalOverlap`(`_length`,`_factorization`,`_eq_prefix_drop`,`_eq_suffix_take`), `resizeToLength`(`_length`,`_take_original_append_drop`), `overlap_gap_lengths`, `normalized_overlap_gap_lengths`, `normalizedSharedComponentLengths_close`, `normalizedSharedTargetLengths_close`, `sharedDescriptionLengths_close`, `normalizedSharedDescription_shape`; C3 plain decoder leaves: `condK_slice_le`, `condK_trans_visible_le`, `plainK_threeBlock_le`, `condK_output_given_splitIndexed_reverseConcat_le`, `condK_output_given_splitIndexed_forwardConcat_le`, `condK_output_given_resized_reverseConcat_le`, `condK_output_given_resized_forwardConcat_le`, `resizeToLength_equivalent`, `condK_pair_from_prefix_suffix_le`, `condK_pair_from_prefix_suffix_visible_le`; C3 raw-length layer: `extractable_chain_length_close`, `extractable_chain_length_close_visible`, `exists_rawSharedDescription_of_extractableCommonInformation`; C3 budget folding: `commonInformationSlack_mono_right`, `commonInformationSlack_threeD_fold`, `commonInformationSlack_pairCombine_fold`, `commonInformationSlack_nested_fold`; **C3 / Exercise 307 COMPLETE**: overlap ⟹ extractable common string is `overlapRepresentation_yields_extractableCommonInformation` and its `_log` corollary; extractable common string ⟹ exact-length overlap representation is `normalize_rawSharedBlockRepresentation`, `exists_overlapRepresentation_of_extractableCommonInformation`, `exists_overlapRepresentation_of_extractableCommonInformation_log`; C4 counting foundation: `card_conditionallyCompressiblePairs_lt`, `card_commonWitnessPairsLe_lt`, `card_fixedLengthPairs_lowLeft_lt`, `card_fixedLengthPairs_lowRight_lt`, `card_fixedLengthPairs_lowPair_lt`, `mem_compressibleWords_iff`, `mem_commonWitnessPairsLe_iff`; C4 conditional enumerator semantics: `commonWitnessPairsStage_prefix`, `mem_commonWitnessPairsStage_eventually_iff`; C4 positive-`n` Muchnik survivor: `muchnikThreshold`, `muchnik_lt_threshold_iff`, `IsMuchnikSurvivor`, `exists_muchnikSurvivor`; C4 compact two-parameter advice (`CompactAdvice.lean`, the decisive `2τ`-exponent relation for the `3n+O(log n)` upper bound, distinct from the `3τ` common-witness relation): `conditionalDescriptionPairsLe`, `mem_conditionalDescriptionPairsLe_iff`, `card_conditionalDescriptionPairsLe_lt` (exponent `α+β+2`), `conditionalDescriptionPairsStage` (`_nodup`, `_prefix`, `_prefix_of_le`, `_primrec`, `_computable`), `mem_conditionalDescriptionPairsStage_eventually_iff`, generic `exists_stage_toFinset_eq`, `complete_stage_persists`, `exists_conditionalDescriptionPairsStage_complete`; C4 simultaneous-region finite interfaces (`WorstCaseRegionBounds.lean`): `muchnikRegionMargin`, `muchnikAdmissibleTriples`, `muchnikConditionalBounds`, `IsMuchnikRegionSurvivor`, exact membership and projection lemmas, nodup and polynomial length bounds, `two_mul_muchnikRegion_cubic_lt`, and primitive-recursive generation; C4 simultaneous-region semantic counting (`WorstCaseRegionCounting.lean`): `muchnikRegionBadPairs`, exact membership/nonmembership, `card_muchnikRegionBadPairs_lt`, and `exists_muchnikRegionSurvivor`; C4 simultaneous-region compact advice (`WorstCaseRegionAdvice.lean`): `muchnikRegionConditionalAdvice`, `muchnikRegionAdviceCount`, `muchnikRegionConditionalAdvice_sum_lt`, and `muchnikRegionAdviceCount_lt`; C4 simultaneous-region stage results: `muchnikRegionMergedStageCount_computable`, `muchnikRegionConditionalStages_exact_of_sum`, `muchnikRegionMergedStage_exact_of_total`, `exists_muchnikRegionMergedStageCount_eq`; C4 simultaneous-region finite search (`WorstCaseRegionSearch.lean`): `muchnikRegionSharedWitnessAtStage` (`_eq_true_iff`, `_primrec`, `_complete_iff`), `muchnikRegionBadAtStage` (`_primrec`, `_false_iff`), `exists_fixedLengthPairCode_not_regionBad`, `muchnikRegionFindAtStage_spec`; C4 region selector (`WorstCaseRegionSelector.lean`): `muchnikRegionSelectorGoodAtStage`, `muchnikRegionSelector_partrec`, `muchnikRegionSelector_spec`; C4 selector base (`WorstCaseSelector.lean`): `muchnikThreshold_primrec`, `fixedLengthPairCodes` (`mem_fixedLengthPairCodes_iff`, `_primrec`), `muchnikAdviceCount`, `muchnikAdviceCount_lt`, `muchnik_advice_length_le`, `mutualInformation_nat_bounds`, `muchnikMergedStageCount` (`_computable`), `muchnikMergedStage_exact_of_total`, `exists_muchnikMergedStageCount_eq`, `muchnikBadAtStage` (`_primrec`, `_false_iff`), `muchnikFindAtStage_spec`, `muchnikSelector`, `muchnikSelector_partrec`, `muchnikSelector_spec`; C4 selector bounds and **Theorem 224 COMPLETE** (`WorstCaseRegion.lean`): `muchnikRegion_selector_input_length_le`, `muchnikRegion_obstruction_mono_margin`, `muchnikRegionSelector_pairPlainK_upper`, `theorem_224_muchnik_worst_case_region` (exact finite plain-complexity values, one uniform `logSlack`, subtraction-free mutual information, and all three obstruction faces); **C4 / Theorem 223 COMPLETE** in `WorstCase.lean`: `theorem_223_muchnik_nonextractability` (exact finite plain-complexity values, `logSlack` bounds, subtraction-free mutual information, and strict `1.1n` obstruction); **C4 / Theorem 225 COMPLETE**: `theorem_225_common_information_universal_lower`, `theorem_225_common_information_profile_upper`, `theorem_225_common_information_lower_envelope_achieved`, `theorem_225_common_information_upper_envelope_achieved`; **C4 / Theorem 226 COMPLETE**: `plainK_conditional_balance_values`, `theorem_226_slack_folding`, `theorem_226_minimal_region_nonextractability`; **Exercise 308 COMPLETE**: `exercise_308_small_common_string_nonextractability`, `exercise_308_coefficient_two_sharp`; C5 rectangle-cover foundation: `CombinatorialRectangle`, `rectangleFamilyEdges`, `RectangleFamilyCovers`, `NoFourCycle`, `card_rectangleFamilyEdges_le_sum`, `card_of_rectangleFamilyCovers_le_sum`, `card_interedges_le_card_right_add_choose_two_left`; C5 abstract affine incidence graph: `AffineIncidence.Point`, `AffineIncidence.Line`, `AffineIncidence.Incident`, `AffineIncidence.incidentEdges`, `AffineIncidence.line_eq_of_two_distinct_incident_points`, `AffineIncidence.incidentPointEquiv`, `AffineIncidence.incidentEdgeEquiv`, `AffineIncidence.point_card`, `AffineIncidence.line_card`, `AffineIncidence.incidentEdges_card`, `AffineIncidence.noFourCycle`; **C5 / Theorem 227 COMPLETE**: region containment (`IncidenceRegion.lean`) is `theorem_227_incidence_region_containment`; the exact-value assembly (`IncidenceConsequences.lean`) is `theorem_227_weighted_profile_values`, `theorem_227_incidence_nonextractability_core`, and the public source-strength endpoint `theorem_227_incidence_nonextractability`, with the marginal profile derived internally from Exercise 309 and final error `logSlack C n`; C5 Exercise 311 combinatorial core (`QuadraticIncidenceClasses.lean`): `QuadraticIncidence.incidenceClass`, `incidenceClass_points_card_le`/`incidenceClass_lines_card_le`/`incidenceClass_card_le` (the `q²`,`q²`,`q³` bounds), `exists_incidenceClass_containing_edge`, `quadraticRectangleFamily_covers`, with the effective GF(q²) codec and the `(1.5n,n,n)` region witness now supplied by `QuadraticModel.lean`, `QuadraticIncidenceDecoders.lean`, `QuadraticEdgeDecoders.lean`, `QuadraticClassDecoders.lean` and `QuadraticIncidenceCodecs.lean` (**Exercise 311 COMPLETE**); C5 Exercise 312 finite covering core (`AffineIncidence.lean`): `incidentEdge_transitive`, `rectangle_image_side_cards`, and `interedges_image_card_eq` prove affine homogeneity; `incidentEdges_card_le_family_card_mul` is the necessity estimate; `shearRectangle_cover_multiplicity` and `exists_polynomial_shear_cover` prove the polynomial-factor sufficiency estimate, and `exists_shear_cover_card_between` / `exists_shear_cover_card_le_mul_log` package the two-sided estimate and log-factor optimality; **C5 / Exercise 312 COMPLETE**: `IncidenceRectangleCapacity.lean` defines `concreteIncidenceCapacity` and proves `incidence_region_capacity_necessary`; `IncidenceCapacityCover.lean` constructs the primitive-recursive shear cover; `IncidenceRegionUniformity.lean` proves the cover and endpoint selectors, the executable list-length and exponent-clamp bounds, `incidence_capacity_sufficient`, `exercise_312_incidence_region_criterion`, and `exercise_312_incidence_region_uniformity` with one uniform `logSlack C n`; **C6 / Exercise 313 COMPLETE** (`Relativized.lean`): `relativizedMap`, `condK_relativizedMap`, `isDecompressor_relativizedMap`, `isOptimalConditional_relativizedMap`, the union-bound counting core `exists_incident_uncompressible_uncovered`, `exists_incidentEdge_highComplexity_and_uncovered`, `region_excluded_of_uncovered`, and the public `exercise_313_relativized_obstruction` (unconditional `2n`/`2n`/`3n`/`I=n` profile with the symmetric `1.1n` threshold excluded from `CommonInformationRegion (relativizedMap V u) x y`); **C7 / Theorem 228 COMPLETE** (`ConditionalIndependence.lean`): `condK_pairCode_chain_lower_values`, `condK_pairCode_chain_upper_values`, and `condK_pairCode_symmetryOfInformation_values` give uniform plain conditional symmetry; `condK_pairCode_submodularity_values` and `base_conditional_mutualInformation_inequality` prove the relativized Problem-296 inequality; the public `theorem_228_conditional_independence_bound` is sorry-free and states SUV Theorem 228 in exact subtraction-free values form. **Exercise 314 COMPLETE** (`FiniteQuadruple.lean`): the finite joint-distribution interface `QuadDist` with its marginal/agreement probabilities, the division-free `CondIndepGivenGamma`/`CondIndepGivenDelta`/`GammaDeltaIndep`/`AlphaBetaIndep` predicates, the explicit couplings `highWeight`/`lowWeight` (`highDist`, `lowDist`) with their verified marginals, conditional independence and agreement probabilities, and the public `exercise_314_conditionally_independent_uniform_pair` (every `c ∈ [3/8, 5/8]` is realized by uniform conditionally independent bits) together with `exercise_314_not_independent` and the `c = 5/8` corollary `theorem_217_conditionally_independent_not_independent` (SUV Theorem 217). **C7 / Exercise 315 COMPLETE** (`ConditionalIndependenceChains.lean`): the chain interface `ChainDist` over `Fin (2k+2) → Bool`, coordinate maps `chainAlphaIdx`/`chainBetaIdx`, division-free `CondIndepCoords`/`IndepCoords`, and the full chain predicate `IsIndep315Chain`; `base_chain` proves `c ∈ [3/8, 5/8]`; the explicit kernel construction `extend_independence_chain` maps `c` to `(c²+1)/2` while preserving every old link; `iterate_reaches` and `extend_independence_chain_iterate` prove the high range; `invert_chain` proves the low range; and the public `exercise_315_conditional_independence_chains` proves the full source claim for every `c ∈ (0,1)`. Exercise 315 is **pure finite probability — it does NOT need the Section 7 bridge**. Exercise 316 uses the exact fixed-histogram method-of-types path below, avoiding a general Section 7 entropy theorem. **Fixed-frequency counting core** (`FixedFrequency.lean`, first step toward Exercise 316): the explicit duplicate-free enumeration `fixedWeightList` with `mem_fixedWeightList` and `length_fixedWeightList`, the finite set `fixedWeightStrings` with `card_fixedWeightStrings` (`= n.choose k`), the general finite pigeonhole `exists_mem_condK_gt_of_card_le`, and the fixed-frequency incompressibility theorems `exists_fixedWeight_condK_gt` / `exists_fixedWeight_plainK_gt` (counting / lower-bound half); the matching **enumeration (upper-bound) half** `condK_fixedWeight_le_size_choose` (via the computable filtered enumeration `fixedWeightFiltered`, `length_fixedWeightFiltered = n.choose k`, and the partial-recursive fixed-width-index decoder `fixedWeightDecoder`/`fixedWeightDecoder_isDecompressor`), which charges a length-`n` weight-`k` string at most `Nat.size (n.choose k) + O(1) = log₂(n.choose k) + O(1)` bits given `n, k`. Together these pin the conditional complexity of a maximally complex binary fixed-frequency string to `Nat.size (n.choose k) ± O(1)`; the plain decoder `fixedWeightPlainDecoder`, `plainK_fixedWeight_le_size_choose_add_params`, and its folded corollary `plainK_fixedWeight_le_size_choose_add_length` add self-delimiting binary parameter codes with only `O(log n)` overhead. **Fixed-histogram (multinomial) enumeration** (`FixedHistogram.lean`): the word enumeration `allWords` (`mem_allWords`, `allWords_nodup`), the fixed-histogram family `fixedHistogramWords` over any alphabet `Fin m` with `mem_fixedHistogramWords`, `fixedHistogramWords_nodup`, and the exact count `length_fixedHistogramWords = Nat.multinomial Finset.univ f` (proved through the recursive enumeration `histWords` and the new `Nat.multinomial` recurrences `sum_mul_multinomial_update_pred` and `multinomial_eq_sum_update_pred`), plus the four-letter forms `multinomial_univ_four_choose` and `length_fixedHistogramWords_four`. The four-letter dictionary and the counting half are in `FixedHistogramCoding.lean`: `letterFirst`/`letterSecond`, `wordFirst`/`wordSecond` with `word_eq_of_components`, the marginal identities `count_true_wordFirst`/`count_true_wordSecond`, the injective code `fourWordPairCode`, and the multinomial incompressibility theorems `exists_fixedHistogram_condK_gt`/`exists_fixedHistogram_plainK_gt`. **Exercise 316 bridge:** `TypeBounds.lean` proves the exact method-of-types inequalities, `FixedHistogramRank.lean` proves the multinomial rank/plain/lift decoders, `ChainHistogram.lean` constructs exact rational-atom histograms and proves the per-link/top multinomial type-log defects, and `ConditionalIndependence.lean` proves the value-form doubling recurrence `iterated_conditional_independence_bound_values`. No Chapter 7 entropy theorem is needed for these exact cancellations. The fixed-histogram coordinate-projection complexity assembly is now supplied by `FixedHistogramProjectionParams.lean` (`condK_fixedHistogramWord_given_projection_le_add_params`), the rational-atom denominator is now propagated along one chain extension by `ChainDist.RationalAtoms.extendChainDist`, and the finite Gács–Körner support-block criterion is `supportBlock_iff_exists_nontrivial_bool_commonFunction` together with the support-graph criterion `exists_nontrivial_bool_commonFunction_iff_not_supportReach` and the bridge `supportBlock_iff_not_supportReach` (`GacsKornerSupport.lean`). **Exercise 316 COMPLETE**: the explicit `exercise_316_nonextractability` assembly uses one denominator-32 rational chain and one maximal sample, and all of its former leaves (the arity-two/three fibre lower profiles, the abstract iterated chain inequality, and the concrete bottom-type gap) are now proved. |
| 11.4 Exercise 316 bridge | ✅ | `CommonInformation/TypeBounds.lean`, `CommonInformation/FixedHistogramRank.lean`, `CommonInformation/ChainHistogram.lean`, `CommonInformation/ConditionalIndependence.lean`, `CommonInformation/FixedHistogramProjectionParams.lean`, `CommonInformation/ChainWitness.lean`, `CommonInformation/ChainFibre.lean`, `CommonInformation/MaximalSampleFibre.lean`, `CommonInformation/ChainSample.lean`, `CommonInformation/ChainNonextractabilityEngine.lean`, `CommonInformation/ChainNonextractability.lean`, `CommonInformation/GacsKornerSupport.lean` | sorry-free exact method-of-types core: `multinomial_marginals_le_of_product_form`, `multinomial_fiber_factorization`; sorry-free rank/plain/lift decoders: `fixedHistogramRankDecoder_isDecompressor`, `fixedHistogramRankDecoder_recovers`, `condK_fixedHistogramWord_le_size_multinomial`, `fixedHistogramPlainDecoder_isDecompressor`, `fixedHistogramPlainDecoder_recovers`, `plainK_fixedHistogramWord_le_size_multinomial_add_params`, `length_fixedHistogramFiberWords`, `fixedHistogramLiftDecoder_isDecompressor`, `fixedHistogramLiftDecoder_recovers`; exact rational-atom histogram and type-log layer: `ChainDist.RationalAtoms`, `chainHistogram`, `chainHistogram_total`, `chainHistogram_condIndep_product_form`, `chainHistogram_indep_product_form`, `chain_link_mutualInformation_defect`, `chain_top_mutualInformation_defect`; arithmetic iteration: `chain_error_recurrence`, `iterated_conditional_independence_bound_values`; rational-atom transfer along one chain extension: `chainStepKernel_rationalAtom`, `ChainDist.RationalAtoms.extendChainDist`; histogram-in-the-program fibre bound: `condK_fixedHistogramWord_given_projection_le_add_params`; explicit dependent rational witness and exact bottom counts: `exists_fiveEighths_rationalAtom_chain`, `fiveEighths_bottom_histogram1`, `fiveEighths_bottom_histogram2`; one full-type maximizer and aligned projection counts: `exists_maximal_chainSample`, `IsMaximalChainSample.length_eq`, `chainWordAt_count`, `chainWordAt_pair_count`, `chainWordAt_triple_count`; the single-coordinate two-sided profile is complete and sorry-free: the rank-decoding upper half is `chain_single_projection_plainK_upper`, the fibre-incompressibility lower half is `chain_single_projection_plainK_lower_at` / `chain_single_projection_plainK_lower`, and the exact-value assembly is `chain_single_projection_complexity_close`; the rank-decoding upper halves for arities two and three are now `chain_pair_projection_plainK_upper` and `chain_triple_projection_plainK_upper`, using the computable canonical-pair recoders `plainK_pairCode_two_boolProjections_le` and `plainK_pairCode_three_boolProjections_le`. The same-sample fibre lower bounds `chain_pair_projection_plainK_lower` and `chain_triple_projection_plainK_lower` are proved from the abstract fibre-incompressibility tool `maximalSample_projection_typeLog_le` (`MaximalSampleFibre.lean`), completing the exact-value assemblies `chain_pair_projection_complexity_close` and `chain_triple_projection_complexity_close`. `ChainNonextractabilityEngine.lean` supplies the per-link and top complexity steps (`chain_link_condK_step`, `chain_top_condK_step`, `large_complexity_case`, `plainK_le_cond_add_of_value`, `histogramTypeLog_pair_le`/`_triple_le`) that discharge the abstract recurrence `chain_sample_iterated_nonextractability`, and the concrete bottom-type gap `fiveEighths_bottom_typeLog_gap` is proved from `fiveEighths_joint_multinomial_le` and `balanced_binary_typeLog_lower`. `exercise_316_nonextractability` is an exact public assembly using one concrete denominator-32 chain and one maximal sample, and is now sorry-free. The finite Gács–Körner criterion is separately `supportBlock_iff_exists_nontrivial_bool_commonFunction`, now complemented by the support-graph form `SupportLink`/`SupportReach`, `commonFunction_eq_of_supportReach`, `exists_nontrivial_bool_commonFunction_iff_not_supportReach`, and `supportBlock_iff_not_supportReach`. |
| 11.3 incidence coding and Exercise 309 | ✅ | `CommonInformation/IncidenceCoding.lean`, `CommonInformation/IncidenceProfile.lean` | `concreteIncidentPairCodes` (`_mem_iff`, `_nodup`, `_length`, `_primrec`), `concreteIncidentPairFromEdgeCode` (`_edge`, `_primrec`), `concreteLineFromPointCode` (`_incident`, `_primrec`), `concretePointFromLineCode` (`_incident`, `_primrec`), `plainK_concreteIncidentPair_le`, `condK_concreteLine_given_point_le`, `condK_concretePoint_given_line_le`; **Exercise 309 COMPLETE**: `exists_highComplexity_concreteIncidentEdge`, `exercise_309_incident_edge_profile` |
| 11.3 Exercise 311 quadratic-extension incidence classes and codecs | ✅ | `CommonInformation/QuadraticIncidenceClasses.lean`, `CommonInformation/QuadraticModel.lean`, `CommonInformation/QuadraticIncidenceDecoders.lean`, `CommonInformation/QuadraticEdgeDecoders.lean`, `CommonInformation/QuadraticClassDecoders.lean`, `CommonInformation/QuadraticIncidenceCodecs.lean` | combinatorial core over a quadratic extension `F/G`: `incidenceClass_lines_card_le`, `incidenceClass_points_card_le`, `incidenceClass_card_le`, `exists_incidenceClass_containing_edge`, `quadraticRectangleFamily_covers`; concrete `GaloisField` basis and cardinality layer: `concreteQuadraticBasis_zero`, `quadraticFieldCode_length`, `quadraticPointCode_length`, `quadraticLineCode_length`, the three code-injectivity theorems, `quadraticIncidentPairCodes_card`, and `exists_highComplexity_quadraticIncidentEdge`; the computable quadratic model `QuadraticModel.lean` (`quadCoeffA`, `quadCoeffB`, `quadGen`, `concreteQuadraticBasis`, `quadMk_mul`), the primitive recursive decoders of `QuadraticIncidenceDecoders.lean`/`QuadraticEdgeDecoders.lean`/`QuadraticClassDecoders.lean`, and hence the now-proved `quadraticIncident_coding_bounds` and `quadraticIncidenceClass_region_witness`; the public source-strength wrapper `exercise_311_region_witness` is sorry-free |
| 11.3 incidence witness rectangles and effective selector | ✅ | `CommonInformation/IncidenceWitnessRectangles.lean`, `CommonInformation/IncidenceWitnessSelector.lean` | valid-code semantics `concreteIncidentCodeRel_iff_exists_edge`, no-four-cycle transport, exact rectangle semantics, both asymmetric bounds `card_incidentCommonWitnessPairsLe_bound1` / `_bound2`, and the strict linear-gap theorem `muchnikThreshold_incidentCommonWitness_card_lt_gap`; effective staged rank coding `incidentCommonWitnessPairsStage_computable`, `mem_incidentCommonWitnessPairsStage_eventually_iff`, `incidentCommonWitnessRankSelector_partrec`, `incidentCommonWitnessRankSelector_recovers`, `pairPlainK_incidentCommonWitness_le`; **Exercise 310 COMPLETE**: `exercise_310_every_highComplexity_incident_edge`, `exists_incidence_muchnik_counterexample` |
| 12 Multisource (Muchnik) | ❌ | — | |
| 14 / algorithmic statistics | — | see VS40 below | |

C4 continuation now proves both the semantic simultaneous bad-union/survivor
layer in `CommonInformation/WorstCaseRegionCounting.lean` and the sharp compact
indexed advice bound in `CommonInformation/WorstCaseRegionAdvice.lean`.
`CommonInformation/WorstCaseRegionStages.lean` freezes the next exact
interfaces and already proves `map_sum_pointwise_eq_of_le_and_sum_eq`,
`muchnikRegionMergedStageCount_computable`, `muchnikRegionConditionalStages_exact_of_sum`,
simultaneous completion, and merged-total recovery.
`CommonInformation/WorstCaseRegionSearch.lean` proves the executable
identical-witness scan, full bad-candidate predicate, and finite survivor
search. `CommonInformation/WorstCaseRegionSelector.lean` proves the
partial-recursive region selector required by Theorem 224, including
termination and certified survivor recovery from the projected advice count.
`CommonInformation/WorstCaseRegion.lean` proves the selector input-length
bound, monotonicity of the three obstruction margins, and the uniform
positive-`n` pair-complexity packaging
`muchnikRegionSelector_pairPlainK_upper`; it then packages these into the
public `theorem_224_muchnik_worst_case_region`, including the zero case and one
uniform logarithmic constant.
`CommonInformation/CommonWitnessCoding.lean` supplies the coefficient-one
plain coding layer needed next: its two- and three-program encodings contain
each raw program once, their parsers are partial recursive, and
`plainK_le_commonWitness_values` /
`pairPlainK_le_commonWitness_values` derive the exact finite-value bounds from
genuine minimizing programs.
`CommonInformation/RegionEnvelopes.lean` now freezes the exact
`CommonInformationUpperEnvelope`, `CommonInformationThreeFaceEnvelope`, and
`CommonInformationLowerEnvelope` sets, proves their relevant upward-closure
properties, proves the universal upper containment
`theorem_225_common_information_universal_upper`, and converts Theorem 224's
pointwise obstruction into
`theorem_224_common_information_threeFace_containment`.  This is the initial
upper/obstruction-envelope portion of Theorem 225.
The same file now also proves coordinate-inflation composition,
`theorem_225_conditional_values_close` (deriving both conditional profile
coordinates from the `2n,2n,3n` plain profile through plain symmetry of
information and an explicit pair-order swap), and the exact merger
`commonInformationTripleInflate_mem_lowerEnvelope`.  It also proves the first
constructive prefix decoder,
`condK_output_given_plainProgramPrefix_le`, together with the exact two-prefix
and anchored decoder theorems
`condK_outputs_given_combined_plainProgramPrefixes_le`, and
`condK_outputs_given_plain_and_conditionalProgramPrefix_le`.  These are the
source's shortest-description prefix/combination witnesses; none assumes a
common-information-region witness.  The same file also bounds the plain
complexity of the combined visible prefixes and proves the missing
coefficient-one prefix-completion/transitivity decoder
`condK_output_given_plainProgramPrefix_then_conditionalProgram_le`.  The next
frontier is now isolated in `CommonInformation/RegionLower.lean`: the exact
finite arithmetic case cover
`commonInformationLowerEnvelope_prefix_case_cover` and the combined/anchored
program-to-region witnesses are proved.  The single-prefix transitive witness
and the constructive universal lower inclusion
`theorem_225_common_information_universal_lower` are proved.  The same file
also proves the uniform profile-normalized upper containment
`theorem_225_common_information_profile_upper` and combines it with Theorem
224 to prove both containment directions for the lower-envelope extremizer in
`theorem_225_common_information_lower_envelope_achieved`.  The exact
overlapping-factor arithmetic split is proved by
`commonInformationUpperEnvelope_overlap_case_cover`.  The profile construction
`exists_incompressibleOverlapPairProfile` now splits a genuinely incompressible
`3n`-bit string and reconstructs it from each marginal and the overlapping
pair.  The direct material decoders
`condK_insert_visible_context_le` and
`condK_overlapFactors_given_materialPrefixes_le` prove
`commonInformationRegion_contains_overlapMaterialProfiles`.  Consequently
`theorem_225_common_information_upper_envelope_achieved` is proved and SUV
Theorem 225 is complete in both extremal directions.  The next file,
`CommonInformation/RegionConsequences.lean`, proves the exact finite weighted
polyhedral inequality `commonInformationLowerEnvelope_weighted_bound`, the
plain symmetry-of-information transport
`plainK_conditional_balance_values`, and the public
`theorem_226_minimal_region_nonextractability`.  It also completes Exercise
308 with the small-`C(z)` coefficient-one inequality
`exercise_308_small_common_string_nonextractability` and the sharpness witness
`exercise_308_coefficient_two_sharp`. `CommonInformation/RectangleCover.lean`
begins C5 with exact rectangle-family coverage semantics and the coarse
no-four-cycle bound `card_interedges_le_card_right_add_choose_two_left`.
`CommonInformation/AffineIncidence.lean` supplies the nonvertical affine graph
`AffineIncidence.incidentEdges`, its exact per-line count
`AffineIncidence.incident_points_card`, the exact total count
`AffineIncidence.incidentEdges_card`, and `AffineIncidence.noFourCycle`.
`CommonInformation/NoFourCycleDensity.lean` proves the sampled power bounds
`noFourCycle_interedges_card_le_pow` in both orientations and the sound family
specialization
`noFourCycle_rectangleFamilyEdges_card_le_pow_of_noFourCycle`.
`CommonInformation/IncidenceCoverArithmetic.lean` proves the exact
`muchnikThreshold_rectangleFamilyEdges_card_lt` exponent specialization.
`CommonInformation/ConcreteField.lean` supplies the executable bounded search
`concretePrime`, its primitive-recursive/computable proofs and exact Bertrand
window specification, and the concrete field/incident-edge cardinality bounds.
The repaired public declaration
`noFourCycle_rectangleFamilyEdges_card_le_pow` explicitly requires the
mathematically necessary `NoFourCycle r` hypothesis. The exact fixed-width
residue, point, line, and incident-edge encodings, their lengths, round trips,
and injectivity are in `CommonInformation/IncidenceCodecs.lean`. Its explicit
incident-edge code-pair list now has exact membership, nodup, length
`concretePrime n ^ 3`, and uniform primitive-recursive/computable generation.
`CommonInformation/IncidenceCoding.lean` adds the uniform raw decoders from a
compact incident-edge code and from either endpoint plus one field-coordinate
program. The public bounds `plainK_concreteIncidentPair_le`,
`condK_concreteLine_given_point_le`, and
`condK_concretePoint_given_line_le` charge respectively `3 * (n + 1)` and
`n + 1` bits plus uniform constants; each decoder infers the varying field
width from its input rather than receiving `n` as advice.
`CommonInformation/IncidenceProfile.lean` proves the positive-`n`
high-complexity-edge existence lemma and **completes Exercise 309**: every
incident edge whose joint plain complexity is at least `3 * n - O(log n)` has
both marginal complexities within `O(log n)` of `2 * n`, joint complexity
within `O(log n)` of `3 * n`, and subtraction-free mutual information within
`O(log n)` of `n`. `CommonInformation/IncidenceWitnessRectangles.lean`
transports the no-four-cycle property through the valid point/line codecs,
identifies bounded common-witness pairs exactly with the corresponding
rectangle-family edges, retains both asymmetric arbitrary-parameter density
bounds, and proves the strict bound below `2 ^ (3 * n - n / 8)` at the Muchnik
threshold for `64 ≤ n`.
`CommonInformation/IncidenceWitnessSelector.lean` filters the computable
common-witness stages by valid incidence codes, ranks only the resulting
prefix-monotone staged list, and reconstructs a covered edge from the four
binary parameters plus one raw fixed-width rank.  The generic theorem
`pairPlainK_incidentCommonWitness_le` charges that rank exactly once.  Together
with the linear cardinality gap it proves **Exercise 310** for every sufficiently
large high-complexity incidence edge; `exists_incidence_muchnik_counterexample`
records the resulting explicit point/line code lengths and profile.
`CommonInformation/IncidenceRegion.lean` and
`CommonInformation/IncidenceConsequences.lean` complete **Theorem 227**: the
Figure-37 envelope feeds the existing weighted arithmetic and a small/large
`C(z)` split to obtain the uniform `O(log n)` endpoint.
`CommonInformation/QuadraticIncidenceClasses.lean` proves the **Exercise 311**
combinatorial core over a quadratic extension `F` of `G` with a two-element
basis `b : Basis (Fin 2) G F`, `b 0 = 1`: the `(r,t,s)`-keyed `incidenceClass`,
the three counting bounds `incidenceClass_points_card_le`,
`incidenceClass_lines_card_le`, `incidenceClass_card_le` (`|G|²`, `|G|²`,
`|G|³`), the covering statements `exists_incidenceClass_containing_edge` and
`quadraticRectangleFamily_covers`.
`CommonInformation/QuadraticModel.lean` presents the quadratic extension
computably: `quadIndex`/`quadCoeffA`/`quadCoeffB` search primitively recursively
for an irreducible monic quadratic `X² + A·X + B` over `ConcreteField m`,
`quadGen` is one of its roots, and `concreteQuadraticBasis m = (1, quadGen m)`
is the resulting basis of `ConcreteQuadraticField m = GF(q²)`, with
`quadMk`, `quadMk_add`, `quadMk_mul` giving the coordinate arithmetic.
`CommonInformation/QuadraticIncidenceDecoders.lean` and
`CommonInformation/QuadraticEdgeDecoders.lean` build the fixed-width codes
`quadraticFieldCode`/`quadraticPointCode`/`quadraticLineCode` (exact lengths and
injectivity) and the *primitive recursive* decoders `quadPointFromLineCode`,
`quadLineFromPointCode`, `quadIncidentPairFromEdgeCode`, yielding
`pairPlainK_quadraticIncident_le` (`6(m+1) + O(1)`),
`condK_quadraticPoint_given_line_le` and `condK_quadraticLine_given_point_le`
(`2(m+1) + O(1)` each).
`CommonInformation/QuadraticClassDecoders.lean` codes the class key
`(r, t, s)` of an incident pair in `3(m+1)` bits (`quadClassKeyOf`) and supplies
the primitive recursive decoders `quadClassPointFromKey`,
`quadClassLineFromKey`, giving `condK_quadraticPoint_given_classKey_le` and
`condK_quadraticLine_given_classKey_le`.
`CommonInformation/QuadraticIncidenceCodecs.lean` supplies the exact
encoded-edge cardinality `concretePrime m ^ 6`, the counting selector
`exists_highComplexity_quadraticIncidentEdge`, and now proves both former DRAFT
leaves: `quadraticIncident_coding_bounds` (from the edge decoders) and
`quadraticIncidenceClass_region_witness` (from the class-key decoders).  The
public wrapper `exercise_311_region_witness` therefore holds unconditionally,
stating the source endpoint for every high-complexity incident edge with
explicit `logSlack` inflation.
The `AffineIncidence.lean` file now also
proves the **Exercise 312** affine-homogeneity core: the shear equivalences
`pointShearEquiv`/`lineShearEquiv`, their incidence preservation
`pointShear_lineShear_incident_iff`, transitivity of the shear action on
incident edges `incidentEdge_shear_transitive`/`incidentEdge_transitive`, side-cardinality preservation
`rectangle_image_side_cards`, and incident-edge-count invariance under the
action `interedges_image_card_eq`.  The necessity estimate is
`incidentEdges_card_le_family_card_mul`, and
`exists_image_rectangle_covering_edge` transports a rectangle containing one
edge to any other edge while preserving both side sizes and its edge count.
The sufficiency half of Exercise 312 is now proved as well:
`shearRectangle` translates a rectangle by an affine shear,
`shearRectangle_cover_multiplicity` shows that every incident edge is covered by
exactly `|edges of R|` of the `|F|³` shear translates of `R`, and
`exists_polynomial_shear_cover` combines this with `greedy_cover_indexed`
(imported from the `Restricted` layer, settling the earlier module-boundary
question) to produce a family `𝓡` of translates of `R` that covers every
incident edge, consists of rectangles congruent to `R` (same side sizes, same
incident-edge count), and satisfies
`|𝓡| · |edges of R| ≤ |E| · (log₂ |E| + 1)`.  The two halves are combined in
`exists_shear_cover_card_between` (the same family also satisfies the necessity
bound `|E| ≤ |𝓡| · |edges of R|`) and in `exists_shear_cover_card_le_mul_log`,
which shows that no cover by rectangles of comparable density beats the
homogeneous shear cover by more than the factor `log₂ |E| + 1`.  With the computable quadratic
model and the two decoder files, **Exercise 311 is now sorry-free**, including
the uniform executable GF(q²) arithmetic, the class-key decoding, and the
`(1.5n,n,n)` region witness.
`CommonInformation/IncidenceRectangleCapacity.lean` supplies the sorry-free
capacity/necessity half of **Exercise 312**: `concreteIncidenceCapacity` is the
exact maximum over bounded concrete rectangles, with monotonicity and clamping;
`card_incidentCommonWitnessPairsLe_le_pow_mul_capacity` is the witness-family
counting bound; and `incidence_region_capacity_necessary` gives the uniform
`logSlack` necessary capacity criterion for every high-complexity incident edge.
`CommonInformation/IncidenceCapacityCode.lean` and
`CommonInformation/IncidenceShearCode.lean` add the bitstring-level counterpart
of that search, and `CommonInformation/IncidenceCapacityCover.lean` now closes
the computable maximizing-rectangle/shear-cover layer.  Bounded rectangles are
enumerated as pairs of sublists of the explicit list of all point codes, their
incident-edge counts are read off the explicit list of incident code pairs, and
`codeCapacityRectangleCode` selects a capacity-maximizing rectangle, giving
`incidenceCapacityRectangle_spec` (exact capacity equality) and the certificate
`incidenceCapacityRectangleCode_primrec`.  The affine shears are implemented
directly on fixed-width codes (`codePointShear`, `codeLineShear`,
`codeShearRectangleCode`, `codeShearRectangleCodes`, `codeShearCoverList`), and
`computableGreedyCover_map` transports the exhaustive subcover search from the
geometric side to the code side along the edge encoding.  Consequently
`incidenceCapacityShearCover_covers`, `incidenceCapacityShearCover_member_spec`,
`incidenceCapacityShearCover_card_mul_le` and
`incidenceCapacityShearCover_primrec` are all sorry-free; the supporting
generic certificates `nat_log2_primrec` and `computableGreedyCover_primrec` are
proved along the way. `CommonInformation/IncidenceRegionUniformity.lean`
completes **Exercise 312**.  Its explicit cover/member and point/line selectors
are partial recursive; `concreteIncidenceCapacity_pow_clamp` removes dependence
on oversized conditional coordinates; and
`incidenceCapacityShearCoverCode_length_mul_le` bounds the executable cover
list, not merely its deduplicated finset.  The effective theorem
`incidence_capacity_sufficient` is proved from those decoders and the capacity
criterion.  The public endpoints `exercise_312_incidence_region_criterion`
(two-directional capacity criterion) and
`exercise_312_incidence_region_uniformity` (the exact `O(log n)`-precision
equality of `C(x,y)` across all high-complexity incident edges) are therefore
sorry-free.  C5 is complete.
`CommonInformation/Relativized.lean` completes **C6 / Exercise 313**, the
condition-`u` analogue of the oracle remark on p. 361.  The relativized
decompressor `relativizedMap V u (p,y) := V (p, pairCode y u)` models
`C(· | u)`; `condK_relativizedMap` identifies `condK (relativizedMap V u) x y =
condK V x (pairCode y u)`, and `isDecompressor_relativizedMap` /
`isOptimalConditional_relativizedMap` certify it is a genuine optimal
decompressor (so its region is a genuine relativized region).  The mathematical
heart is the union bound `exists_incident_uncompressible_uncovered` (a generic
counting core over an abstract covered set) and its specialization
`exists_incidentEdge_highComplexity_and_uncovered`: among the
`concretePrime n ^ 3 > 2^{3n}` incident edges, at most `2^{3n-1}` are
`u`-covered (the no-4-cycle density bound
`muchnikThreshold_incidentCommonWitness_card_lt_gap`, valid for the arbitrary map
`relativizedMap V u`) and at most `2^{3n-1}` are unconditionally compressible, so
a good edge survives.  Gluing with the unconditional `exercise_309` profile and
the region → covered-pair bridge `region_excluded_of_uncovered` gives the public
`exercise_313_relativized_obstruction`: for every `u`, an incident pair `(x,y)`
of unconditional complexity `2n`, pair complexity `3n`, and
`MutualInformationWithin V x y n` such that the symmetric `1.1n` threshold is not
in `CommonInformationRegion (relativizedMap V u) x y` — the same strength as the
non-relativized `exists_incidence_muchnik_counterexample`.
`CommonInformation/ConditionalIndependence.lean` **completes Theorem 228**: the
public `theorem_228_conditional_independence_bound` (exact subtraction-free
values form) is fully proved from `condK_condPair_left_le` and the now-proved
relativized Problem-296 inequality
`base_conditional_mutualInformation_inequality`.  Its infrastructure includes
uniform plain conditional symmetry of information
`condK_pairCode_symmetryOfInformation_values` and the explicit submodularity
lemma `condK_pairCode_submodularity_values`.
**Exercise 314 is complete** (`FiniteQuadruple.lean`).  **Exercise 315 is
complete** (`ConditionalIndependenceChains.lean`): `base_chain` proves the base
range, `extend_independence_chain` gives the explicit `c ↦ (c²+1)/2`
distribution extension, `iterate_reaches` and `extend_independence_chain_iterate`
handle the high range, and `invert_chain` handles the low range.  Exercise
315 is pure finite probability and does **not** need the Section 7 bridge.
**Exercise 316 is complete** in `MaximalSampleFibre.lean`, `ChainSample.lean`,
`ChainNonextractabilityEngine.lean`, and `ChainNonextractability.lean`: the same
maximal full-chain sample supplies its one-, two-, and three-coordinate
profiles, the abstract chain recurrence has coefficient exactly `2 ^ k`, and
the concrete denominator-32 wrapper proves both the `N / 32` mutual-information
gap and non-extractability for the same bottom pair.  The fixed-frequency core
supporting that endpoint includes the proved counting lower bound
(`exists_fixedWeight_condK_gt`) and enumeration upper bound
(`condK_fixedWeight_le_size_choose`) for the binary case, pinning a maximally
complex fixed-frequency string's conditional
complexity to `Nat.size (n.choose k) ± O(1)`.  The plain decoder
`fixedWeightPlainDecoder` and bound
`plainK_fixedWeight_le_size_choose_add_params` now add binary parameter codes;
`plainK_fixedWeight_le_size_choose_add_length` folds their cost to `O(log n)`.
`TypeBounds.lean` now proves the exact natural-number method-of-types core,
including `multinomial_marginals_le_of_product_form` and
`multinomial_fiber_factorization`; this removes the previously claimed need
for a Chapter-7 entropy theorem.  `FixedHistogramRank.lean` is the current
decoder layer and is now sorry-free: its injective finite-word code, fibre
enumeration semantics, maximality theorem, the primitive recursiveness and
exact recovery of the rank, plain and lift decoders
(`fixedHistogramRankDecoder_isDecompressor`, `fixedHistogramRankDecoder_recovers`,
`fixedHistogramPlainDecoder_isDecompressor`, `fixedHistogramPlainDecoder_recovers`,
`fixedHistogramLiftDecoder_isDecompressor`, `fixedHistogramLiftDecoder_recovers`),
the exact fibre cardinality `length_fixedHistogramFiberWords`, and the
complexity bounds `condK_fixedHistogramWord_le_size_multinomial` and
`plainK_fixedHistogramWord_le_size_multinomial_add_params` are all proved.

## VS40 survey

| Section | Status | Lean home | Key theorems |
|---|---|---|---|
| §1 Statistical models | ✅ | `AlgorithmicStatistics/Basic.lean`, `FiniteSetModel.lean`, `CodedFiniteDistribution.lean`, `NormalizedCodedFiniteDistribution.lean` | model/`codedUniformOn` infrastructure |
| §2.1 Prefix complexity, a priori probability, randomness deficiency | ✅ | `AlgorithmicStatistics/Deficiency.lean`, `DeficiencyTest.lean` | `DeficiencyLe` (multiplicative form) |
| §2.2 Definition of stochasticity | ✅ | `AlgorithmicStatistics/Stochasticity.lean` | `IsStochastic`, monotonicity lemmas |
| §2.3 Stochasticity conservation | ✅ | `AlgorithmicStatistics/Conservation.lean`, `Selector.lean` | |
| §2.4 Non-stochastic objects | ✅ | `AlgorithmicStatistics/NonStochastic.lean` | |
| §3.1 Optimality deficiency, two-part descriptions | ✅ | `TwoPart/Basic.lean`, `OptimalityDeficiency.lean`, `DescriptionShift.lean` | `InDescriptionProfile`, `OptimalityDeficiencyLe` |
| §3.2 Optimality vs randomness deficiencies (Thm 4/5 chain) | ✅ | `TwoPart/Deficiencies.lean`, `GapCounting.lean`, `DescriptionSnapshot.lean`, `PaperTheorems.lean` | `deficiencies_theorem_tight_thm`, `stochasticity_to_optimal_set_thm`, `optimal_stochasticity_imp_profile_thm` |
| §3.3 Complexity/size trade-off; profile realization (`stat-any-curve`) | ✅ | `TwoPart/Profile.lean`, `CurveRealization.lean`, `GreedyWindow.lean`, `ProfileRealization.lean` | `structureFunction_admissible`, `ProfileCurve`, `exists_string_with_profile`; improving descriptions: `improving_descriptions_complexity_thm`, `improving_descriptions_size_thm` |
| §4 Bounded complexity lists | ✅ | `AlgorithmicStatistics/BoundedComplexityLists/` | B0: `boundedOutputStage_computable`, `mem_completedBoundedOutput_iff_plainK_le`, `suffixCountIncluding_eq_tailAfter_add_one`; B1: `prop_omegas`, `plainK_omegaFixedCode_lower`, `plainK_omegaFixedCode_upper`; B2: `prop_busy_beavers`; B3: `prop_enumeration_tail`; B4: `prop_omega_equivalence`; B5: `prop_pos_def`, `prop_tail_monotonicity`; B6: `tail_characterization`, `setComplexity_completedDyadicBlock_le` (shared coding core), `inDescriptionProfile_of_suffixCoordinate`; B7 infrastructure: `standardBlock`, `standardBlockTail`, `standardBlock_end_add_tail`, `standardBlockTail_eq_length_drop_block_end`, `standardBlock_eq_completedDyadicBlock`, `completedDyadicBlockSelector_recovers_standardBlock`, `plainK_standardBlock_upper`, `setComplexity_standardBlock_upper`, `standardBlockFromMemberSelector_partrec`, `standardBlockFromMemberSelector_recovers`, `standardBlockFromOmegaPrefixSelector_recovers`, `omegaPrefixFromStandardBlockSelector_recovers`, `standardBlock_omegaPrefix_equiv`, `standardBlock_plainK_index_close`, `standardBlock_plainK_index_close_plain`, `omegaFixedCode_close_logSlack`, `lengthFilterUniformCode_computable`, `lengthFilterUniformCodeSelector_recovers`, `setComplexity_lengthFilteredModel_le`; B7 proved endpoints: `prop_std_pos` (uniform plain/prefix complexity and positive-tail bounds), `chopped_standard_blocks` (concrete chopped-block `IsIJDescription` witness), `prop_better_std` (genuine standard block with conditional simplicity relative to the original model), `standard_description_simple_given_x`, `prop_std_omega` (both plain conditional directions, including nearby indices above or below `m-j`); B8 proved infrastructure and endpoints: `prop_information_rare`, `isStochastic_singleton_length`, `stochastic_of_standardBlock_at_plainK`, `KP_mutual_symm_le` (safe additive prefix mutual-information symmetry), `omegaPrefixFromMemberSelector_recovers`, `KP_omegaPrefix_given_standardBlock_member`, `KP_standardBlock_given_omegaPrefix`, `KPPlain_omegaPrefix_lower_of_standardBlock`, `KP_information_of_standardBlock_additive`, `KP_cond_partrec_map_le`, `KP_cond_partrec_advice_map_le`, `KP_cond_change_of_condK_le`, `KP_omegaPrefix_condition_transport`, `prop_dilemma`, and `prop_nonstochastic_counting_improved`. |
| §5 Computational/logical depth | ➖ | — | needs resource-bounded computability |
| §6 Descriptions of restricted type | 🟡 | `Foundation/EnumerationComplexity.lean`, `Restricted/Family.lean`, `Restricted/BasicProfile.lean`, `Restricted/GreedyCover.lean`, `Restricted/Selection.lean`, `Restricted/EffectiveSelection.lean`, `Restricted/Improving.lean`, `Restricted/DeficiencyEquiv.lean`, `Restricted/Examples/Cylinders.lean`, `Restricted/Examples/Masks.lean`, `Restricted/Examples/HammingBalls.lean`, `Restricted/HammingGap.lean`, `Restricted/FamilyCurve.lean`, `Restricted/FamilyCurve/Basic.lean`, `Restricted/FamilyCurve/Selector.lean`, `Restricted/FamilyCurve/EffectiveRebuild.lean`, `Restricted/FamilyCurve/BadStream.lean`, `Restricted/FamilyCurve/CoupledRun.lean`, `Restricted/FamilyCurve/RunCoding.lean`, `Restricted/FamilyCurve/EffectiveRun.lean`, `Restricted/FamilyCurve/EffectiveRunSemantics.lean`, `Restricted/FamilyCurve/AnchoredRun.lean`, `Restricted/FamilyCurve/RunBounds.lean` | `StagedEnumeration.KPPlain_le_log_index_of_enumeration`, `StagedEnumeration.KP_le_log_index_of_cond_enumeration`, `StagedEnumeration.KP_le_fixed_length_index_of_cond_enumeration`, `StagedEnumeration.setComplexity_le_log_index_of_enumeration`, `DescriptionFamily.HasPolynomialOverhead`, `DescriptionFamily.overhead_bits_le_logSlack`, `fullFamily_hasPolynomialOverhead`, `cylinderFamily_hasPolynomialOverhead`, `maskFamily_hasPolynomialOverhead`, `hammingFamily_hasPolynomialOverhead`, `inDescriptionProfileIn_fullFamily_iff`, `DescriptionFamily.singleton_mem`, `inDescriptionProfileIn_fullCube_of_optimal` (M2 a1), `inDescriptionProfileIn_singleton_of_optimal` (M2 a2), `exists_family_cover`, `exists_cover_codes_in_stage` (enumeration-stage refinement of the cover: a good cover whose codes all lie in a single `enum T`), `inDescriptionProfileIn_cover_shift` (M2 a3 — proved via `Restricted/CoverSearch.lean`), `greedy_cover`, `greedy_cover_indexed`, `selectionStrategy_length_bound`, `selectionStrategy_covers` (proved finite-stage indexed greedy selection), `familyStageModelCodesList_mono`, `familyMarkedCodeStream_computable`, `familyMarkedCodeStream_mono`, `familyMarkedCodeStream_sound`, `exists_markedStream_rank`, `ManyIJDescriptionsIn`, `manyIJDescriptionsIn_fullFamily_iff`, `inDescriptionProfileIn_improving_size`, `exists_familyComplexityRefinedSet`, `inDescriptionProfileIn_improving_complexity`, `restricted_improving_descriptions_conditional` (M5 draft), `restricted_stochasticity_to_optimal_set_thm` (M5 draft), `restricted_stochasticity_to_optimal_set_uniform` (M5 draft), `cylinderFamily` (M3 draft), `maskFamily` (M3 draft), `hammingFamily` (M3 draft), `prop_hamming_gap` (M6 draft), `restrictedCurveGrid_height_le_target_add_mesh`, `restrictedCurveGrid_mesh_le_sqrtSlack`, `restrictedCurveGrid_code_length_le_sqrt`, `KPPlain_restrictedCurveGridCode_le`, `exists_encoded_restricted_curve_grid`, `decode_restrictedCurveGridCode_sample_eq`, `restrictedSampledBadCodeStream_mono`, `restrictedSampledBadCodeStream_computable_uniform`, `restrictedSampledBadCodeStream_sound`, `restrictedSampledBadCodeStream_catches_violation`, `cover_argmax_intersection_bound`, `restrictedCoverValidBool_computable`, `restrictedMaxIntersectionCoverSelector_partrec`, `restrictedMaxIntersectionCoverSelector_spec`, `restrictedEffectiveRebuildStep_spec`, `restrictedEffectiveRebuildSuffix_partrec`, `restrictedEffectiveRebuildSuffix_decodes_density` (M7 effective suffix), `restrictedEffectiveSampledInitialState`, `restrictedEffectiveSampledRun`, `restrictedEffectiveSampledRun_partrec_uniform`, `restrictedSampledNewBadBatch_append`, `restrictedEffectiveLiveCodesAfterDelete_decode`, `restrictedEffectiveDensityFailsBool_iff`, `restrictedEffectiveFirstFailedScale_spec`, `restrictedEffectiveSampledRunStep_terminates`, `restrictedEffectiveSampledRun_step_spec`, `restrictedSampledBadBatchAt_decode_sound`, `restrictedEffectiveSampledRunProcess_spec`, `restrictedEffectiveSampledRun_processed_disjoint`, `restrictedEffectiveSampledRun_spec`, `restrictedAnchoredTarget`, `restrictedEffectiveAnchoredSizes`, `restrictedEffectiveAnchoredSampledRun`, `restrictedAnchoredRun_sample_getD`, `RestrictedSampledRunState.dropAnchor`, `restricted_rebuild_suffix`, `restrictedSampledRun_step_preserves`, `restrictedSampledRun_deleted_fresh`, `restrictedSampledRun_invariants`, `restricted_large_bad_appearances_le`, `restricted_small_bad_deleted_volume_le`, `restricted_rebuilds_charged_to_deleted_volume`, `restrictedSampledRun_rebuild_count_le`, `restrictedSampledRun_version_code_complexity`, `restrictedSampledRun_root_antitone`, `restrictedSampledRun_stabilizes`, `restrictedProfileBadSet_card_le`, `restrictedAnchoredProcessedBadUnion_card_le`, `restrictedCurveGrid_bad_volume_padding`, `exists_restricted_anchored_structural_output`, `RestrictedSampledOutputCore`, `RestrictedSampledOutput`, `restrictedCurveGridPredecessor_spec`, `RestrictedSampledOutput.toCoupledOutput`, `exists_restricted_sampled_output_core` (M7 version-coding leaf), `RestrictedCoupledOutput`, `exists_restricted_coupled_output`, `RestrictedScaleState` (M7 draft), `exists_restricted_scale_state` (M7 draft), `prop_family_curve` (M7 draft) |
| §7 Strong models | 🟡 | `AlgorithmicStatistics/StrongModels/` (including `TotalComplexity.lean`, `TotalReduction.lean`, `Partition.lean`, `StrongProfile.lean`, `AnyCurve.lean`, `Properties.lean`, `AddNoise.lean`, `SufficientStatistic.lean`, `StrongSufficientStatistic.lean`, `Separation.lean`, the `T1*.lean` worker files through `T1.lean`, `T3.lean`, `T3Boundary.lean`, `T3BoundaryReplay.lean`, `T3RunComplexity.lean`, and `T3Profile.lean`) | **S0–S3, S5–S9:** All listed public endpoints are proved and sorry-free (`prop_add_noise`, `thm_step_wise`, `thm_separation`, `thm_hereditary`, `prop_min_hereditary`, `lemma_lch`, `t1_strange_string`, `t3`, `lemma_4`, `thm_card`, `lemma_omp` at `3 * epsilon`, `thm_uppest`). **S4:** `prop_upward` is proved unconditionally in `UpwardOrdinalNoiseBetaRegime.lean` (`prop_upward`, via the unconditional `strongModelOrdinalNoiseTransport`, whose two regimes are `beta ≤ n + epsilon + logSlack cBudget n` and the full-cube branch `n ≤ beta`); the strictly more general budgeted-transport lane keeps its large-`beta` corner open, but it is no longer needed for the source endpoint. The unconditional proof of `rem_add_noise` is complete, and `prop_add_noise` is now derived from it (`propAddNoise_of_remAddNoise`) by translating witnesses to profile corners via length-scale Section 3 bridges; its multiplicity provenance is the heavy-truncation/symmetry/rank reverse inclusion `inPlainDescriptionProfile_fst_of_pair_model` (`RemAddNoiseLowBranch.lean`) feeding `exists_description_smaller_complexity_of_many_logSlack` (as detailed above). The separate `inDescriptionProfile_of_noise_information_gain` (`AddNoiseMultiplicity.lean`) is a standalone distinct-truncation provenance theorem, not on the endpoint path. |
| §7 Strong models | ❌ | — | needs total conditional complexity |

Internal M7 sampled-run combinatorics live in
`Restricted/FamilyCurve/SampledRun.lean`: `restricted_min_failed_scale_prefix_safe`
and `restricted_rebuild_suffix_terminal_nonempty` are proved.  Fresh deletion
blocks are now proved pairwise disjoint and feed
`restricted_self_rebuilds_charged_to_deleted_volume`.  The extensional
least-failed-scale transition and its finite-batch chronological recursion are
proved in `Restricted/FamilyCurve/CoupledRun.lean`, including fresh deletion and
the doubled post-rebuild density margin.  The effective decoder is now lifted
through finite batches and chronological time; connecting the anchored result
to final-state survival and bounded version ordinals remains open in
`exists_restricted_sampled_output_core`.  That leaf receives the exact encoded
grid together with its proved complexity budget; grid existence and the uniform
mesh estimate are no longer part of the obligation.
The static interpolation
from the `N + 1` sampled sets to every `i ≤ k` is now proved by
`RestrictedSampledOutput.toCoupledOutput`; in particular, the open construction
no longer ranges its version accounting over all `k + 1` coordinates.
`RunCoding.lean` now proves
the concrete finite charging bridge, binary version-code bound, root
antitonicity, eventual root stabilization, persistence of processed deletions
(`restrictedSampledRun_processed_bad_disjoint`), and survivor extraction from a
nonempty stabilized root (`restrictedSampledRun_exists_persistent_survivor`).
The extensional chronological run still makes no claim that all of its choices
form a computable version stream.  `EffectiveRebuild.lean` now supplies the
missing uniform partial-recursive suffix iterator and proves that its decoded
steps satisfy the same family-membership, size, live-intersection, and density
contract.  The computable maximum-intersection cover selector also has the proved coding leaf
`restrictedMaxIntersectionCoverSelector_KPPlain_le`, bounding the selected
cover-member code complexity by the selector-input complexity plus a uniform
constant.

`EffectiveRun.lean` keeps that partiality explicit: malformed inputs may
diverge instead of being assigned a noncomputable default.  Its coded update
deletes the new event, finds the least failed density edge, retains the safe
model prefix, and rebuilds only the strict suffix.  The false claim that every
new bad-code batch is empty has been replaced by the proved exact append
identity `restrictedSampledNewBadBatch_append`.  The former draft name
`restrictedEffectiveSampledRun_computable_uniform` is superseded by the honest
partial-recursive statement `restrictedEffectiveSampledRun_partrec_uniform`;
that statement and the decoded one-step correctness theorem
`restrictedEffectiveSampledRun_step_spec` are proved.

The sampled bad-event enumeration in `Restricted/FamilyCurve/BadStream.lean`
is prefix-stable and computable uniformly from the encoded grid.  Its catching
lemma now explicitly requires both `IsCodeFor c U` and strict decrease of the
target curve; these hypotheses are necessary to connect snapshot complexity to
`U` and to compare unsampled target heights with sampled grid heights.

`Restricted/FamilyCurve/RunBounds.lean` proves the concrete interval-wise
length bound for the sampled bad-code stream and its eventual stabilization
(`restrictedSampledBadCodeStream_length_le` and
`restrictedSampledBadCodeStream_stabilizes`).  It identifies the recursive
processed union with the chronological stream, proves the sound interval-wise
cardinality estimate `restrictedAnchoredProcessedBadUnion_card_le`, absorbs
that estimate into the balanced ambient cube with
`restrictedCurveGrid_bad_volume_padding`, and packages the complete nonempty
survivor/avoidance phase in `exists_restricted_anchored_structural_output`.
The stream's actual square-root subtraction is kept separate from the final
profile slack, avoiding a nested `sqrtSlack`.  `VersionDecoder.lean` now proves
partial recursiveness of the fixed-code event trace, actual-model change trace,
and version decoder, with all grid parameters recovered from the encoded grid.
The remaining core obligation is replay correctness for the terminal sampled
model, bounding its actual change ordinal by `RestrictedRunChain.rebuildSteps`,
and the final plain-complexity arithmetic for the self-delimiting decoder
bundle.
`EffectiveRun.lean` now also
proves the uniform partial-recursiveness of the chronological executor and the
decoded initial-state specification.  Its deletion trace now decodes exactly,
the executable density test is proved equivalent to the extensional predicate,
the first-failed-scale search has its least-index specification, and the
effective suffix search is proved to terminate.  Assembling the retained prefix
and rebuilt suffix into the decoded next-state invariants, and proving the
least-failed-edge transition contract, are now complete.

`EffectiveRunSemantics.lean` proves the finite-batch and chronological lifting.
Its public theorem is tied to an actual `RestrictedCurveGrid`; an earlier draft
incorrectly quantified an unrelated exponent function and omitted the initial
top-size bound.  `AnchoredRun.lean` starts the next M7 step by inserting the
fixed ambient cube at run level zero and shifting sampled level `s` to level
`s+1`.  Target/size alignment, monotonicity, code lookup, and sampled-state
projection, the effective initializer, and the exact finite-time root invariant
are proved.

## Other formalized results (outside the two sources)

| Result | Lean home | Key theorems |
|---|---|---|
| Chaitin incompleteness (abstract formal system) | `Complexity/Chaitin.lean`, `ChaitinCorollaries.lean` | `chaitinBound`, `chaitinIncompleteness` |
| Second incompleteness, Kritchman–Raz style (KR) | `Complexity/SecondIncompleteness.lean`, `SecondIncompletenessCorollaries.lean` | `secondIncompleteness` |
| Bundled paper-facing interface | `Interface/StandardMachine.lean` | `StandardMachine` + wrappers |
| List/tuple encoding API | `Encoding/Tuples.lean`, `Encoding/TuplesComplexity.lean` | `listCode`, `decodeListCode_listCode`, `listCode_injective`, `listCode_primrec`, `KPPlain_listCode_le`, `KP_component_listCode_le` |
| Primrec toolkit | `Foundation/PrimrecExtras.lean` | `Primrec.list_take/drop/takeWhile/replicate`, `Primrec.nat_iterate'`, `primrec_auto` — add new general `Primrec` lemmas HERE |

## Known gaps / debts

- **Plain symmetry of information** (SUV §2.3, `C(x,y) = C(x) + C(y|x) + O(log)`): not formalized; only prefix-staged versions and one-directional plain↔prefix bridges exist.
- ~~Chain-rule refactor~~ **done**: `KP_le_prefixComplexityContext_add_logSlack`
  is now a direct corollary of `KP_cond_remove_short_info`; the rest of
  `GapCounting`/`DescriptionShift` already sits on the pair/SOI primitives.
- `AdmissibleCurve` in `TwoPart/Profile.lean` is intentionally kept as a
  *documented false start* (`AdmissibleCurve_unsatisfiable`); do not build on it —
  use `structureFunction_admissible` / `ProfileCurve`.
