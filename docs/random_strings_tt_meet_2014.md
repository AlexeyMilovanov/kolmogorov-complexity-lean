# Random strings and tt-degrees: Theorem 4.1 of Cai, Downey, Epstein, Lempp, Miller

A formalization of Theorem 4.1 of M. Cai, R. G. Downey, R. Epstein, S. Lempp, J. S. Miller,
*Random strings and truth-table degrees of Turing complete c.e. sets*, Logical Methods in Computer
Science 10(3:15), 2014, arXiv:1408.5636.  The Lean sources are in
`KolmogorovMathlib/RandomStrings/TTMeet2014/`, with the aggregator
`KolmogorovMathlib/RandomStrings/TTMeet2014.lean`; all declarations are in the namespace
`Kolmogorov.RandomStrings.TTMeet`.

The proof is complete.  The development contains no `sorry`, `axiom`, `admit` or `native_decide`,
and its main theorems depend only on `propext`, `Classical.choice` and `Quot.sound` (section 9).

## 1. What is formalized

Theorem 4.1 of the paper: *for every noncomputable set `X` there is a universal prefix-free machine
`U` such that `X` is not truth-table reducible to `R_{K_U} = {x : K_U(x) ≥ |x|}`*.  Equivalently, the
sets that are tt-reducible to `R_{K_U}` for every universal `U` are exactly the computable sets.

The proof of Theorem 4.1 in Section 4 of the paper is formalized in full: the finite games of §4.1
(determinacy, the bishop lemma, winning sets and their generators, the stack of games), the stage
construction of §4.2 and §4.3, Lemma 4.3 (every requirement is eventually satisfied), Lemma 4.4 (we
stay within our measure), Posner's trick, the `Δ⁰₂` approximation of `X`, and the realization of each
of the three game boards as the set of random strings of an optimal machine.  Two corollaries are
derived: `computablePred_of_forall_polyTime`, for the adaptive class `P^{R_U}` (Conjecture 1.3 of the
paper, in its deterministic form), through the inclusion of `P^B` in tt; and, with the theorem of
Allender, Friedman and Gasarch already in the library, `mem_EXPSPACE_of_forall_polyTime`.

Not asserted: the intersection for Turing reducibility, the converse for adaptive `P^{R_U}`, or any
equality of resource classes.  The construction differs from the printed one in a few places, listed
in sections 3 and 4; one of them repairs a gap in the printed proof of Lemma 4.3.

## 2. Main statements

From `Main.lean` (`BitString` is `List Bool`; `Map` is the library's type of conditional machines,
`Machine` that of unconditional ones):

```lean
theorem theorem_4_1 (X : Set BitString) (hX : ¬ ComputablePred fun x => x ∈ X) :
    ∃ U : Map, IsOptimalPrefixConditional U ∧ ¬ TTReducible X (prefixRandom U)

theorem theorem_4_1_unconditional (X : Set BitString) (hX : ¬ ComputablePred fun x => x ∈ X) :
    ∃ U : Machine, IsUniversalMachine U ∧ ¬ TTReducible X (randomOf U)

theorem ttMeet_iff_computable (X : Set BitString) :
    (∀ U : Map, IsOptimalPrefixConditional U → TTReducible X (prefixRandom U)) ↔
      ComputablePred fun x => x ∈ X
```

| Lean | Content |
| --- | --- |
| `theorem_4_1` | the theorem for optimal conditional machines, with `R_U = prefixRandom U` |
| `theorem_4_1_unconditional` | the theorem for the paper's unconditional universal machines, with `R_U = randomOf U` |
| `ttMeet_iff_computable` | `X ≤_tt R_U` for every optimal `U` iff `X` is computable |
| `computablePred_of_forall_polyTime` | `X ∈ P^{R_U}` for every optimal `U` implies that `X` is computable |
| `mem_EXPSPACE_of_forall_polyTime` | the same hypothesis gives `X ∈ EXPSPACE`, with the AFG theorem |
| `exists_three_machines` | for a noncomputable `X ≤_tt R_V`, three optimal machines with no common reduction of `X` |
| `no_common_reduction` | no single computable table generator reduces `X` to all three final oracles |
| `lemma_4_3` | Lemma 4.3: every requirement `R_i` eventually stops acting and is satisfied |
| `lemma_4_4` | Lemma 4.4: what we compress on each board costs at most `3/32` |

**How the statements relate to the paper.**

* `TTReducible X R` (`TruthTable.lean`) is the classical unbounded tt-reducibility: a *total
  computable* generator of finite truth tables whose tables evaluate correctly on `R`.  It is not
  the polynomial-time class `PolyTimeTT` of `RandomStrings/TT.lean`.
* `prefixRandom U = {x | |x| ≤ KPPlain U x}`, with the threshold taken in `ℕ∞`, is the paper's
  `R_{K_U}`; `randomOf U` is the same set for an unconditional machine, with `KM U`.
* **"Universal" means additively optimal.**  `IsOptimalPrefixConditional U` (for conditional
  machines) and `IsUniversalMachine U` (for unconditional ones) ask that `U` be prefix-free and that
  its complexity be minimal, up to an additive constant, among all prefix-free machines: the sense in
  which the paper compares `K_U` and `K_V`.  `OptimalBridge.lean` shows that the conditional and the
  unconditional formulations give the same family of random sets
  (`exists_optimal_iff_exists_universal`).
* **The syntactic form of the paper's `U_j` is not reproduced.**  The paper's machines satisfy
  `U_j (000 σ) = V (σ)`.  The machines here come from the library's exact realization
  `K_{U'} = min (K_V + 5, F + 3)` (`exists_isOptimalPrefixConditional_min_toNat`), which prescribes the
  complexity but not a syntactic form.  So `theorem_4_1` provides an optimal `U`, not one of a
  prescribed syntactic form: under a stricter, compiler-prefix reading of "universal", it says less
  than the paper's construction gives.  Equivalently, the hypothesis of `ttMeet_iff_computable`
  ranges over all optimal machines.  Neither direction of `OptimalBridge.lean` uses a syntactic
  property such as `U (0^e 1 σ) = M_e (σ)`.
* **Quantifiers.**  As in the paper, the reduction may depend on `U`: `TTReducible` is an
  existential inside the `∀ U`.

| Paper | Lean |
| --- | --- |
| given `X` noncomputable, there is a universal `U` | `theorem_4_1`: `∀ X, ¬ ComputablePred X → ∃ U, …` |
| for each `U` its own reduction | `∀ U, … → TTReducible X (prefixRandom U)`, with `∃ g` inside `∀ U` |
| three machines `U_j`, depending on `X` | `exists_three_machines` (with `V`, and `X_s` from `exists_approx_of_tt`) |
| Posner: a single `Ψ_i` for all three | `posner_combine`, then `no_common_reduction` |
| `¬(Ψ_i^{R₀} = Ψ_i^{R₁} = Ψ_i^{R₂} = X)` for all `i` | `ReqSatisfied`, for all indices of the listing |
| the listing contains non-total reductions | `tableAt`, `IsTotalGen`, `exists_index` |
| `X` noncomputable is used only at the end | `lemma_4_3` needs it only through `computablePred_of_agreed` |

`posner_combine` handles coincidences among the three oracles by guards on a finite list of
distinguishing queries; this is why it needs all three reductions to compute the same `X`.

The construction receives the opponent's moves and `X_s` as stage data (`Input`).  `stateAt` is an
ordinary computable definition: nothing in `Construction.lean` is `noncomputable`, and every search
is over an explicit finite list.  The final oracles `finalR` are limits, defined in
`Requirements.lean`, and the stage transition cannot read them.  `chi` (`TruthTable.lean`) is the
only classical oracle, and the construction does not use it.

## 3. The gap in the printed proof of Lemma 4.3, and the repair

**The claim in question.**  §4.1.2 says that after stage `s₁`, "any time … that the values of the
games `G(ε₀, ε₀)` agree, this value will always be the same", and the proof of Lemma 4.3 concludes
that "we need only find the first such `σ` after stage `s₁` to know that `σ` is an initial segment of
`X`".  The printed justification treats intermediate-level cheating during a game (the knight and
bishop argument).

**The gap.**  Opponent moves between two examinations, with no game in progress, are not treated.
An opponent move is common to all three boards, and each symmetric game starts afresh with a full
opponent's budget.  So the agreed value can change on all boards at once, while they still agree
with each other.

**What is machine-checked** (`ParityExample.lean`).  For a table computing the parity of a set of
equal-weight strings, with enough strings, the second player forces the current parity by
mirroring (`parity_forced`).  `symmetric_value_flips`: one unanswered opponent move makes the old
parity not forced at `(E, E)`, makes the new parity forced at `(E, E)`, and leaves the old parity
forced at `(E - 1, E)`.

**A sketch of a failure of the printed construction (not machine-checked).**

1. Let `Ψ` compute, for each bit `x`, the parity of the alive strings of length `ℓ_x`, with `ℓ_x`
   growing fast enough that `∑_x 2 ^ (-ℓ_x)` is small.  All levels of the stack then force the
   current parity vector, on every board that holds it.  So as long as the boards hold the same
   position, no split, no failed intersection and no stack split appears, and the printed Case 2
   starts no game.
2. Choose `V` from a universal `V₀` of small measure and a KC set `W` which, for each `x`, mirrors the
   compressions of `V₀` at length `ℓ_x`, and adds one more string when `x` enters `∅'`.  The cost of
   mirroring is covered by the measure of `V₀`.  In the limit the parity at `ℓ_x` is `∅'(x)`.
3. Take `X = ∅'`, a limit-correct approximation `X_s`, and a listing with `Ψ_0 = Ψ`.  Then `R_0`
   passes every bit at a late enough stage, acts infinitely often, starts no game, and `Ψ^{R_j} = X`
   for all `j`.  All lower-priority requirements stay in Case 1, so nobody moves.  The conclusion of
   Lemma 4.3 fails for this `V` and this listing, and the first `σ` after `s₁` is not an initial
   segment of `X`.

This reading of the printed proof has not been confirmed with the authors, and steps 2 and 3 are
only sketched.  If the printed construction has a mechanism that this reading misses, the repair
below is unnecessary but still valid.  **Nothing here casts doubt on Theorem 4.1**, which is proved
here with the repaired construction.

**The repair** (`examineTop`, `Baseline` in `Construction.lean`).  The agreed `σ` is remembered with
a base stage per board.  While we make no move on a board, the bishop lemma gives `{σ}` winning at
`(ε - λ, ε)`, where `λ` is the opponent's spending since the base stage (`baseline_invariant`).  If at
a later visit `{σ}ᶜ` wins the symmetric game on a board `j`, that game is played against `{σ}` at
`(ε - λ, ε)` on another board.  This is the move of Case 3b, applied at every visit.  After a stage
where the opponent's remaining spending is at most `ε`, such a game cannot be cheated, so it wins
permanently, and otherwise `σ` really is stable (`agreed_nested`).  In the parity example, the game
on the second board flips the bit back and then mirrors, while the first board keeps the new value,
so the boards disagree unless the opponent overspends.

The accounting survives: the opponent's spending is charged over the whole window since the base
stage, and the windows are disjoint (section 4).  The invariants of the agreement and of the games
along the run (`run_invariant`), the stability of the agreed value (`agreed_nested`), and the
accounting of the repaired games (`examineTop_inl_spend`, `epoch_spent_le`) are all proved, so for
the construction in `Construction.lean` this part of the argument is machine-checked.  The sketch
above would only add that the printed construction, without the repair, fails.

## 4. Other deviations from the printed construction

**Faithful restructurings.**

1. **Bits are never reset** (`ReqState.tables`), and grow by at most one per visit.  The paper
   restarts from one bit at each visit and notes that the repetition is unnecessary.
   `forces_lift_iff` shows that shorter games bring nothing new.
2. **Tables** are clause lists, and `ofRows`/`evalB_ofRows` embed the paper's rows.  One index
   replaces the pair `⟨i_f, i_g⟩`.  Bit `k` names `strOf k`, a computable surjection `ℕ → Str`, and
   `tableAt_eq_none_of_le` bounds the bits defined at a stage.
3. **After Case 3c** the construction goes to the next visit, instead of to Case 2 at the same
   stage.
4. **Opponent first, and passing.**  The paper gives the opponent the first move and has no explicit
   end of play.  In `Wins` the play ends on a double pass; since `Wins` quantifies over all opponent
   moves at the position, the strategy stays valid if the opponent moves again later.  `respond` is
   positional.
5. **`TopOutcome.stuck`** exists only to make `topOutcome` total; `topOutcome_ne_stuck` shows that it
   does not occur.

**Double counting.**  The proof of Lemma 4.4 claims that an opponent move is counted in one game per
board, because a move in an `R_i`-game is an action of `R_i` and resets lower priorities.  Under the
printed schedule, with one requirement per stage, a lower-priority requirement can be visited between
the move and the next `R_i`-stage.  It would then see a cheat (the string costs more than its `ε`) and
charge the move too, and `R_i` charges it later.  **Repair:** `pendingHit` counts the move as an
action at once, for the lower-priority test.  This also applies when `R_m` only holds an agreement,
since the baseline window may charge the move later.  `charged_disjoint_of_lt` proves that this
suffices, and `charged_pairwise_disjoint` is the result.

**The opponent's measure.**  The paper's "measure used by the opponent" is ambiguous between the
weight of the opponent's requests and the cost of their effect on a given board, and the claim that
the opponent's actions on the three game boards are identical holds for the former only: a string we
already deleted on one board costs the opponent nothing there.  `oppSpend` counts each string of the
board once, at the cost `2 ^ (1 - |τ|)`, whatever its status on the boards.  This is at most the
opponent's true weight, and it bounds the actual cost on each board, so the game budgets are
respected.

**Constants.**  The cost of a move is the paper's.  Budgets are scaled, because the library realizes
`min (K_V + 5, F + 3)` rather than `min (K_V + 3, A_j)`:

| Quantity | Paper | Here |
| --- | --- | --- |
| opponent's total | `1/8` | `1/32` (`opp_budget`) |
| our allowance | `7/8` | `3/32` (`lemma_4_4`); `8 · 3/32 + 1/4 ≤ 1` in the Kraft sum of `F` (`realizingF_kraft`) |
| lost measure | `1/4` | `1/16` |
| useful and wasted | `1/4` | at most `1/64` (`sum_pow_le_of_nodup`) |
| floor of `c` | `c ≥ i + 4` | `c ≥ i + 7` (`newC`) |

**Windows.**  The paper's "useful", "wasted" and "lost" measure are organized by ghost data
(`Epoch`), which no decision reads.  A window ending in a reset closes at the last visit before the
reset, so moves first seen by the reset are not charged to it.  A window holds at most a stacked play
followed by an unbalanced one, or one balanced play.  If the opponent exceeds the limit of a
non-stacked play, the opponent has spent more than `ε` in the window, while we have spent at most
`2 ε`.  If the opponent exceeds the level `ε_ℓ` of a stacked play, we have spent at most
`ε_{ℓ-1} = 2 ε_ℓ` (`SpendInvAt`).  This is the factor `2` of the paper.

## 5. Source map

Page numbers are those of the LMCS PDF.

| Paper | Pages | Lean |
| --- | --- | --- |
| §1.1 `K_U`, `R_{K_U}` | 3–4 | `prefixRandom`, `KM`, `randomOf` |
| §1.1 tt-reductions, listing `Ψ_i`, stages | 4 | `TTable`, `ofRows`, `TTReducible`, `tableAt`, `exists_index`, `tablesUpTo` |
| Theorem 4.1 | 16 | `theorem_4_1`, `ttMeet_iff_computable` |
| §4 requirements `R_i`, Posner's trick | 16 | `ReqSatisfied`, `posner_combine` |
| §4 `Δ⁰₂` reduction | 16 | `exists_approx_of_tt`, `approximation_of_tt` |
| §4 coding `U_j (000 σ) = V (σ)`, opponent and "we" | 16–17 | `OppCompresses`, `exists_machine_of_board` |
| §4.1.1 game `G(ε, δ)`, determinacy, stack, zero game | 17–18 | `Wins`, `wins_or_compl`, `levelBudget`, `firstStackSplit`, `zero_level`, `wins_zero_game` |
| §4.1.2 knight and bishop | 18–19 | `Wins.after_opponent`, `caseThree`, `baseline_invariant` |
| §4.1.3 winning sets, ultrafilter, compatibility | 19–20 | `Forces`, `families_eq_of_no_split`, `exists_generator`, `forces_lift_iff`, `generator_take`, `topOutcome` |
| §4.2 multiple requirements | 20 | `mustReset`, `pendingHit`, `move_insulated` |
| §4.3 stage, KC sets | 20 | `step`, `stateAt`, `exists_machine_of_board` |
| §4.3 Case 1 | 20–21 | `caseOne`, `newC` |
| §4.3 Case 2 | 21 | `caseTwo`, `examineTop` |
| §4.3 Case 3a, 3b, 3c | 21–22 | `caseThree`, `respond`, `respond_spec` |
| Remark 4.2 | 22 | `ReqState.lastActed`, `step` |
| Lemma 4.3 | 22–23 | `lemma_4_3`, `eps_settles`, `opp_tail`, `agreed_nested`, `agreed_value_correct`, `computablePred_of_agreed`, `stopsActing_of_bounded`, `satisfied_of_bounded` |
| Lemma 4.4 | 23 | `lemma_4_4`, `ours_cost_le_epochs`, `spend_invariant`, `epoch_spent_le`, `charged_disjoint_of_lt`, `charged_pairwise_disjoint`, `final_c_nodup` |

## 6. Library API used

| Library declaration | Use |
| --- | --- |
| `Kolmogorov.BitString`, `Map`, `KP`, `KPPlain` | statements |
| `IsOptimalPrefixConditional`, `exists_isOptimalPrefixConditional` | statements, choice of `V` |
| `RandomStrings.prefixRandom` | the oracle, threshold `\|x\| ≤ K_U(x)` in `ℕ∞` |
| `exists_isOptimalPrefixConditional_min_toNat` | exact realization `K_{U'} = min (K_V + 5, F + 3)` |
| `IsEntropyFun`, `IsKraftFun`, `HasREOvergraph` | the hypotheses of the realization |
| `KPPlain_toNat_kraft`, `REPred_KPPlain_toNat_le`, `KPPlain_ne_top_of_isOptimalPrefixConditional` | opponent's budget and enumeration, `ℕ∞` handling |
| `RandomStrings.PolyTimeOracle`, `exists_clocked_of_polyTime`, `queryListCode`, `clockedOutcome`, `allSub`, `decodeCode_surjective` | the bridge from `P^B` |
| `dec_inter_polyTime_prefixRandom_subset_EXPSPACE` | the `EXPSPACE` corollary |

**Exactness of the realization.**  The realization is an equality of `K_{U'}`, so
`prefixRandom U_j = finalR I j` (`exists_machine_of_board`).  The set of compressed strings is exactly
the opponent's plus ours, and no unintended game move can occur.  `length_le_realizingF_iff` handles
short strings: a string we compress has length at least `8` (`length_ge_of_mem_oursAt`), so `|x| - 4`
is a true subtraction, and the empty string is never touched.  For an optimal machine
`KPPlain U x ≠ ⊤`, which reduces the `ℕ∞` threshold to `ℕ`.

**Layering.**  Every module below `Baseline.lean`, the effectivity layer included, depends on
Mathlib only, with `Str := List Bool` (definitionally `Kolmogorov.BitString`).  `Baseline.lean` is
the boundary: it imports the library modules `RandomStrings.PrefixForm` and `RandomStrings.Effective`,
and only `Adaptive`, `OptimalBridge` and `Main` are above it.

## 7. Module map

In import order: each module imports only modules listed before it.

| Module | Content |
| --- | --- |
| `Game.lean` | finite weighted deletion games `Wins`: recursion, symmetric determinacy, bishop lemma, zero game, scaling |
| `TruthTable.lean` | finite truth tables `TTable`, unbounded `TTReducible`, the effective listing `tableAt`, `strOf` |
| `Approximation.lean` | monotone stage enumerations of co-c.e. oracles; `X ≤_tt R` gives a computable approximation of `X` |
| `Posner.lean` | Posner's trick: three per-oracle reductions combine into one (`posner_combine`) |
| `ParityExample.lean` | the parity game behind the gap in the printed Case 2 (`parity_forced`, `symmetric_value_flips`) |
| `WinningSets.lean` | winning sets of the `n`-bit game, generators, units and arenas, compatibility (`forces_lift_iff`) |
| `Construction.lean` | the stage construction `step`/`stateAt` with the repaired Case 2, as computable definitions |
| `Structure.lean` | structure of the run without game content: well-formedness, growth of tables, string lengths |
| `Insulation.lean` | lower-priority moves never touch higher-priority boards (`move_insulated`) |
| `GameInvariants.lean` | evolution of positions between visits, verdicts of an examination, the stack of games |
| `RunInvariants.lean` | the visit invariant of the games and the agreement, by induction over the run (`run_invariant`) |
| `Requirements.lean` | the final oracles `finalR` and the requirements `ReqSatisfied` |
| `LatePlay.lean` | late visits: Case 2 or 3 without reset, current games, stable positions and their final oracles |
| `Resettling.lean` | the opponent's tail, resettling of the agreement, stability of the agreed value (`agreed_nested`) |
| `Bounded.lean` | Lemma 4.3 when the number of examined bits is bounded |
| `Effectivity/GameTable.lean` | the value of a game is computable: tabulation over the finite box of states |
| `Effectivity/StateTwin.lean` | the list twin of the construction state, its tracking relation, computability of the run |
| `Verification.lean` | Lemma 4.3 (`lemma_4_3`, `no_common_reduction`) and the effectivity theorems it uses |
| `Accounting.lean` | Lemma 4.4: windows, charged measure, no double counting (`lemma_4_4`) |
| `Realization.lean` | the entropy function `realizingF` of a board: its Kraft sum and its c.e. overgraph |
| `Baseline.lean` | the boundary module: imports the library API used by the last three modules |
| `Adaptive.lean` | adaptive polynomial-time reductions are tt-reductions (`ttReducible_of_polyTimeOracle`) |
| `OptimalBridge.lean` | optimal conditional and universal unconditional machines give the same random sets |
| `Main.lean` | the three machines, `theorem_4_1`, `ttMeet_iff_computable` and the corollaries |

The aggregator `TTMeet2014.lean` imports `Main`, `ParityExample` and the two effectivity modules.

## 8. The effectivity layer

`Construction.lean` is computable in Lean's sense, which excludes hidden choice, but Mathlib's
`Computable` needs `Primcodable` data, and `ConState` has none: its fields are finite sets,
functions on all requirements, and rational ghost fields.  The effectivity layer therefore works
with list data, in two Mathlib-only modules whose results enter `Verification.lean` as
`forces_computable`, `oursB_computable` and `agreedBit_computable`.  `realizingF_re` uses
`oursB_computable`; `computablePred_of_agreed`, hence `lemma_4_3`, uses `agreedBit_computable`.

**`Effectivity/GameTable.lean`: tabulation of the game value.**  The recursion of `decidableWinsF`
changes its parameters, so its value is tabulated over the finite box of states (`box`: every
sublist of the starting position, every pair of budgets below the starting budgets), level by level,
with `lookupT` reading the table.  One level of the game is factored into `replyT` (our replies) and
`moveT` (the opponent's moves), with `removeL` and `afterState` for the position after a move;
`levelT` is the only evaluator, with the double-pass rule and the budget subtraction of `Wins`.
`replyT_spec`, `moveT_spec`, `levelT_spec`, `tab_spec` and `forcesL_eq` prove that it agrees with
`Arena.Forces`; `tab_eq_nat_rec` identifies the table recursion with `Nat.rec`, which gives
`forcesL_primrec`.  The arena is encoded as `List TTable × ℕ` (`arenaEquiv`), and list membership is
decided through `List.idxOf`.  The interface used by `StateTwin.lean` consists of six declarations:
`costU`, `valueL`, `forcesB`, `valueL_eq`, `costU_eq` and `forcesB_computable`.

**`Effectivity/StateTwin.lean`: a list twin of the construction state.**  `ConStateL`, `ReqStateL`,
`PlayL` and `BoardGameL` keep every field that `step` reads and erase the ghost accounting fields.
Finite sets become lists, and the family of requirements, of which only those below the stage have
been visited, becomes a padded list: `reqL` reads a missing entry as the default state, and
`setReq` pads with default states before an update.  Each of these structures, as well as `Arena`,
`PlayKind` and `Baseline`, has an explicit equivalence with a product or option type, a `Primcodable`
instance through it, and primitive recursive projections and constructors.  `stepL` mirrors `step`
branch by branch; the larger routines are split into named continuations (`examineVerdictL`,
`extensionVerdictL`, `caseTwoAgreeL`, `movesL`, `advanceGamesL`, `mergeMovesL`, `caseThreeBishopL`,
`finishStepL`) that follow the original case order and search order and add no decision of their
own.

`Tracks stL st` says that the two states are at the same stage, that the lists represent the finite
sets of the original (`(stL.ours j).toFinset = st.ours j`), and that every requirement, stored or
default, satisfies `TracksReq`: equal exponent, tables, baseline, last visit and last action, and
equal play after interpreting the list targets (`PlayL.toPlay`).  It needs no well-formedness
assumption.  The tracking lemmas follow the branches of `Construction.lean`, including the baseline
repair, the `lastActed` updates, and the ghost-only `closeEpoch` updates (`tracksReq_closeEpoch`);
they give `stepL_tracks` and, by induction, `stateAtL_tracks`.  Since no decision reads the ghost
data, erasing it is a simulation.

Costs of lists are computed by `costU` on a deduplicated list (`costU_dedup`).  Raw `costU` counts
multiplicity (at scale `0` the list holding the empty string twice costs `4`, its finite set `2`), so
the identity without `Nodup` would be false and is not asserted; with deduplication, no `Nodup`
invariant on the stored lists is needed.

The import closure of the module has `Primrec.list_map` and `Primrec.list_foldr` but no `Computable`
analogues for computable, not primitive recursive, functions, so the module proves its own:
`computable_list_foldr`, by iterating a total list state, then `computable_list_map`,
`computable_list_filter`, `computable_list_any` and `computable_list_find`, together with currying
over finite domains.  The twin step is `Computable` under `Input.Valid` (`stepL_computable`), it is
iterated by `Nat.rec` (`stateAtL`, `stateAtL_computable`), and `oursBL_eq`, `agreedBitL_eq` read the
outputs off the tracked state.  This gives `oursB_computable'` and `agreedBit_computable'`.  The
internal declarations live in the namespace `StateTwin`.

## 9. How to verify

Build the development from the repository root, with the toolchain of `lean-toolchain`:

```sh
lake build KolmogorovMathlib.RandomStrings.TTMeet2014
```

Then check the axioms of the main theorems with a scratch file outside the library, for example
`/tmp/axioms.lean`, run by `lake env lean /tmp/axioms.lean`:

```lean
import KolmogorovMathlib.RandomStrings.TTMeet2014

open Kolmogorov.RandomStrings.TTMeet

#print axioms theorem_4_1
#print axioms theorem_4_1_unconditional
#print axioms exists_three_machines
#print axioms no_common_reduction
#print axioms lemma_4_3
#print axioms computablePred_of_agreed
#print axioms realizingF_re
```

Each of the seven commands reports `depends on axioms: [propext, Classical.choice, Quot.sound]`.
`scripts/audit.sh` checks, among other things, that the tree contains no `sorry`, `axiom`, `admit`,
`native_decide` or `implemented_by`, and its axiom sweep checks that every public theorem of the
library depends only on these three axioms.

## 10. Proof structure

The main results, in the order in which they are proved:

| Lean | Content | Module |
| --- | --- | --- |
| `wins_or_compl`, `Wins.after_opponent` | symmetric determinacy, bishop lemma | `Game` |
| `exists_generator`, `forces_lift_iff` | winning sets form a principal ultrafilter; compatibility | `WinningSets` |
| `reqWF_rsAt`, `tables_prefix`, `length_ge_of_mem_oursAt` | the structure of the run | `Structure` |
| `move_insulated`, `ours_eq_between` | no move touches a higher-priority board | `Insulation` |
| `position_between_visits` | the position changes only by the opponent between visits | `GameInvariants` |
| `run_invariant`, `baseline_invariant`, `game_invariant` | invariants of the agreement and the games | `RunInvariants` |
| `tables_spec`, `baseline_length`, `tables_const_of_permanent` | the requirement data along the run | `Requirements` |
| `opp_tail` | the opponent's tail is small | `Resettling` |
| `exists_protected_or_permanent` | agreement resettles after the tail stage | `Resettling` |
| `agreed_nested` | **the agreed value is stable** | `Resettling` |
| `stopsActing_of_bounded`, `satisfied_of_bounded` | `R_i` stops acting; satisfaction via the zero game | `Bounded` |
| `forcesB_computable` | the value of a game is computable | `Effectivity/GameTable` |
| `stateAtL_tracks`, `oursB_computable'`, `agreedBit_computable'` | the run is computable | `Effectivity/StateTwin` |
| `permanent_disagreement` | a game that never stops wins | `Verification` |
| `eps_settles` | `ε_i` settles | `Verification` |
| `extension_matches`, `agreed_value_correct` | a new bit agrees with `X_t`; the agreed value converges to `X` | `Verification` |
| `computablePred_of_agreed` | `X` is computable if a requirement extends its agreement forever | `Verification` |
| `lemma_4_3`, `no_common_reduction` | Lemma 4.3 and its use | `Verification` |
| `ours_cost_le_epochs` | all our spending is recorded in windows | `Accounting` |
| `finals_invariant`, `final_c_nodup` | distinct values of `c` | `Accounting` |
| `winInv`, `charged_disjoint_of_lt`, `charged_pairwise_disjoint` | **no double counting** | `Accounting` |
| `spend_invariant`, `epoch_spent_le` | spending at most twice the charged measure, plus `ε` | `Accounting` |
| `lemma_4_4` | Lemma 4.4 | `Accounting` |
| `realizingF_kraft`, `realizingF_re` | the Kraft sum of `F`; the overgraph of `F` is c.e. | `Realization` |
| `exists_machine_of_board`, `exists_three_machines` | the boards are random sets of optimal machines | `Main` |
| `theorem_4_1`, `ttMeet_iff_computable` | Theorem 4.1 | `Main` |
