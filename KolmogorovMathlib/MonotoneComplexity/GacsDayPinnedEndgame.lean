import KolmogorovMathlib.MonotoneComplexity.GacsDayEndgameController
import KolmogorovMathlib.MonotoneComplexity.GacsDayEndgameLift
import KolmogorovMathlib.MonotoneComplexity.GacsDayEndgameScale
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2BaseRung
import KolmogorovMathlib.MonotoneComplexity.GacsDayPinnedEndgameProp11
import KolmogorovMathlib.MonotoneComplexity.GacsDayPinnedEndgameEnvelope

/-!
# Stage E3′ — the single-call pinned endgame

`GacsDayGameStatement` is discharged by **one** call of the stage-`k` pinned
strategy, at

| symbol | value |
|---|---|
| `k` | `32 * d` (so `kappa = halfAmplification k = 1 + 16 * d`) |
| `a` | `grayEndgameA d = Nat.size (4 * d)`, with `4 * d < 2 ^ a ≤ 8 * d` |
| `alpha` | `dyadicScale a` |
| `n` | `1` (a singleton family — Day's Proposition 11 verbatim) |
| `A` | `[]` (nothing is unavailable: there is nothing earlier) |
| `e` | `a + 8 * grayFootprint (k - 1) + 3` (the pinned call depth) |
| `h` | `2 * k = 64 * d` |
| `C` | `129` |

There are no rounds, no schedule, no truncation, no accumulation and no
unavailable set, so the whole scheduled-endgame apparatus is bypassed:

* the *charged* gray outcome is **impossible** here, because the charge pins the
  single root request into `[alpha/2, alpha]` and
  `kappa * (alpha / 2) = (1 + 16 * d) / (2 * 2 ^ a) > 1` while the gray mass is
  at most one (`familyClientWinsUnserved_of_charged_window`, Prop 11);
* hence `ChargedGrayFamilyGameSpec.wins_charged` collapses to the unserved
  outcome, and the frozen win condition `clientWinsUnserved` places **no** lower
  bound on the request, so no `hbig` transfer obligation arises;
* the static budget `1 * alpha = 2 ^ (-a) < 1 / (4 * d) ≤ 1 / d` holds outright,
  which is why the *static* lift `isUniformWinningStrategy_of_familyController`
  is the right one (the hard-coded `gacsDayGameStatement_of_endgameController`
  fixes the family size `64 * d` and cannot host this call);
* legality, range support and the certificate are read at the call's own anchor
  `a` and nowhere else, so there is no cross-round scale obligation.

## Main results

* `gacsDayGameStatement_of_singleCall` — the generic single-call extraction.
* `PinnedGrayUniformInductionStatement` — the pinned replacement for
  `GrayFamilyUniformInductionStatement`.
* `gacsDayGameStatement_of_pinnedUniform` — Stage E3′ proper.
* `gacsDayGameStatement_of_canonicalPinned` — the unconditional corollary, via
  the committed canonical pinned ladder of `GacsDayV2BaseRung`.
-/

namespace Kolmogorov

/-! ### The generic single-call extraction -/

/-- **The single-call extraction.**  One family game of `nfun d` trees played
under the STATIC budget `nfun d * alpha d ≤ 1 / d` discharges
`GacsDayGameStatement`.  This is the sibling of
`gacsDayGameStatement_of_familyController`, but with the family size, the
height and the branching free parameters and with the static lift
`isUniformWinningStrategy_of_familyController` in place of the dynamic-budget
one. -/
theorem gacsDayGameStatement_of_singleCall
    (C : ℕ) (hgt bfun nfun : ℕ → ℕ) (alpha : ℕ → ℚ)
    (ctrl : ℕ → ClientFamilyStrategy)
    (hcomp : Computable₂ (fun d => liftFamilyStrategy (nfun d) (1 / (d : ℚ)) (ctrl d)))
    (hheight : ∀ d, 1 ≤ d → hgt d + 1 ≤ C * d)
    (hn : ∀ d, 1 ≤ d → nfun d ≤ 2 ^ ((C * d) ^ (C * d)))
    (hb : ∀ d, 1 ≤ d → bfun d ≤ 2 ^ ((C * d) ^ (C * d)))
    (hsum : ∀ d, 1 ≤ d → (nfun d : ℚ) * alpha d ≤ 1 / (d : ℚ))
    (hplay : ∀ d, 1 ≤ d → ∀ sm, familyServerPlayLegal (nfun d) (bfun d) [] sm →
      familyClientPlayLegal (nfun d) (bfun d) (alpha d)
        (playClientFamily [] (nfun d) (ctrl d) sm))
    (hrange : ∀ d, 1 ≤ d → FamilyRangeSupported (nfun d) (bfun d) [] (ctrl d))
    (hunserved : ∀ d, 1 ≤ d → ∀ sm, familyServerPlayLegal (nfun d) (bfun d) [] sm →
      familyClientWinsUnserved (nfun d) (hgt d) (bfun d)
        (playClientFamily [] (nfun d) (ctrl d) sm) sm) :
    GacsDayGameStatement := by
  refine ⟨C, fun d => liftFamilyStrategy (nfun d) (1 / (d : ℚ)) (ctrl d), hcomp, ?_⟩
  intro d hd
  have hr0 : (0 : ℚ) ≤ 1 / (d : ℚ) := by positivity
  have hwin :=
    isUniformWinningStrategy_of_familyController (h := hgt d) (b := bfun d) (n := nfun d)
      (B := 2 ^ ((C * d) ^ (C * d))) (d := d) (alpha := alpha d) (r := 1 / (d : ℚ))
      (σf := ctrl d) (hn d hd) (hb d hd) hr0 le_rfl (hsum d hd) (hplay d hd) (hrange d hd)
      (hunserved d hd)
  exact isUniformWinningStrategy_mono_height (hheight d hd) hwin

/-! ### The endgame parameters of the single call -/

/-- The endgame stage `32 * d`, whose half amplification `halfAmplification (32 * d) = 1 + 16 * d`
dominates `2 * 2 ^ a` for the endgame anchor `a`. -/
def pinnedEndgameK (d : ℕ) : ℕ := 32 * d

/-- The endgame anchor, unchanged from the scheduled route: `4 * d < 2 ^ a ≤ 8 * d`. -/
def pinnedEndgameA (d : ℕ) : ℕ := grayEndgameA d

/-- The pinned call depth `grayEndgameA d + 8 * grayFootprint (32 * d - 1) + 3` of the stage-`32 *
d` rung at the endgame anchor. -/
def pinnedEndgameE (d : ℕ) : ℕ :=
  grayEndgameA d + 8 * grayFootprint (32 * d - 1) + 3

/-- The pinned branching `ladderBranching (grayTailBaseBranch (32 * d - 1) (grayFootprint (32 * d -
1))) (grayEndgameA d) (pinnedEndgameE d)` of the single endgame call. -/
def pinnedEndgameB (d : ℕ) : ℕ :=
  ladderBranching (grayTailBaseBranch (32 * d - 1) (grayFootprint (32 * d - 1)))
    (grayEndgameA d) (pinnedEndgameE d)

/-- The pinned height of the single call, `2 * k = 64 * d`. -/
def pinnedEndgameH (d : ℕ) : ℕ := 2 * (32 * d)

/-- The request scale `dyadicScale (grayEndgameA d)` of the single call of the pinned
endgame. -/
def pinnedEndgameAlpha (d : ℕ) : ℚ := dyadicScale (grayEndgameA d)

/-- The pinned endgame stage `pinnedEndgameK` is computable. -/
lemma computable_pinnedEndgame_k : Computable pinnedEndgameK := by
  change Computable (fun d => 32 * d)
  exact Primrec.to_comp (Primrec.nat_mul.comp (Primrec.const 32) Primrec.id)

/-- The pinned endgame coarse scale `pinnedEndgameA` is computable. -/
lemma computable_pinnedEndgame_a : Computable pinnedEndgameA := computable_grayEndgame_a

/-- The pinned endgame fine scale `pinnedEndgameE` is computable. -/
lemma computable_pinnedEndgame_e : Computable pinnedEndgameE := by
  have hfp : Computable (fun d : ℕ => 8 * grayFootprint (32 * d - 1) + 3) :=
    Primrec.to_comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 8)
          (primrec_grayFootprint.comp
            (Primrec.nat_sub.comp
              (Primrec.nat_mul.comp (Primrec.const 32) Primrec.id) (Primrec.const 1))))
        (Primrec.const 3))
  have hadd : Computable (fun p : ℕ × ℕ => p.1 + p.2) := Primrec.nat_add.to_comp
  have := hadd.comp (Computable.pair computable_grayEndgame_a hfp)
  exact this.of_eq (fun d => by simp [pinnedEndgameE, Nat.add_assoc])

/-! ### The endgame arithmetic -/

/-- **Day's `f * 2 ^ (-r-1) ≥ 1` at the single-call parameters.**  With
`kappa = 1 + 16 * d` and `2 ^ a ≤ 8 * d`, the amplification applied to the
*guaranteed* root request `alpha / 2` already exceeds total mass one, which is
the hypothesis of Proposition 11. -/
theorem singleCall_window (d : ℕ) (hd : 1 ≤ d) :
    1 < halfAmplification (32 * d) *
      (((1 : ℕ) : ℚ) * (dyadicScale (grayEndgameA d) / 2)) := by
  rw [Nat.cast_one]
  have hb := (grayEndgame_a_bounds hd).2
  have hpow : ((2 : ℚ)) ^ grayEndgameA d ≤ 8 * (d : ℚ) := by exact_mod_cast hb
  have hpos : (0 : ℚ) < (2 : ℚ) ^ grayEndgameA d := by positivity
  have hd1 : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hds : dyadicScale (grayEndgameA d) = 1 / (2 : ℚ) ^ grayEndgameA d := by
    rw [dyadicScale, div_pow, one_pow]
  rw [hds, halfAmplification]
  push_cast
  have hgoal : (1 + 32 * (d : ℚ) / 2) * (1 * (1 / (2 : ℚ) ^ grayEndgameA d / 2))
      = (1 + 16 * (d : ℚ)) / (2 * (2 : ℚ) ^ grayEndgameA d) := by
    field_simp
    ring
  rw [hgoal, lt_div_iff₀ (by positivity)]
  nlinarith [hpow, hpos, hd1]

/-- **The static budget of the single call.**  One tree at scale `2 ^ (-a)` with
`4 * d < 2 ^ a` fits under `1 / d` outright — no sequencing is needed. -/
theorem singleCall_budget (d : ℕ) (hd : 1 ≤ d) :
    ((1 : ℕ) : ℚ) * dyadicScale (grayEndgameA d) ≤ 1 / (d : ℚ) := by
  have hb := (grayEndgame_a_bounds hd).1
  have hpow : 4 * (d : ℚ) < ((2 : ℚ)) ^ grayEndgameA d := by exact_mod_cast hb
  have hd1 : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hds : dyadicScale (grayEndgameA d) = 1 / (2 : ℚ) ^ grayEndgameA d := by
    rw [dyadicScale, div_pow, one_pow]
  rw [hds, Nat.cast_one, one_mul]
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  linarith

/-! ### Stage E3′ -/

/-- There is a computable uniform family strategy scheme `σ` such that `σ k` is a `PinnedChargedRung
4 k` for every stage `k ≥ 3`. This is the pinned replacement for
`GrayFamilyUniformInductionStatement`: it carries no constant, no envelope fields and no case
split on `epsDepth ≠ alphaDepth`. -/
def PinnedGrayUniformInductionStatement : Prop :=
  ∃ σ : UniformFamilyStrategyScheme,
    UniformFamilyStrategySchemeComputable σ ∧
    ∀ k, 3 ≤ k → PinnedChargedRung 4 k (σ k)

/-- **Stage E3′.**  The pinned uniform induction discharges the Gács–Day game
statement through a single call of its stage-`32 * d` rung at `n = 1`,
`A = []`, anchor `grayEndgameA d`. -/
theorem gacsDayGameStatement_of_pinnedUniform
    (H : PinnedGrayUniformInductionStatement) : GacsDayGameStatement := by
  obtain ⟨σ, hσ, hrung⟩ := H
  -- the single controller: one evaluation of the scheme at the endgame parameters
  set ctrl : ℕ → ClientFamilyStrategy :=
    fun d => σ (pinnedEndgameK d) (pinnedEndgameA d) (pinnedEndgameE d) with hctrl
  -- the one spec instance the whole endgame rests on
  have S : ∀ d, 1 ≤ d →
      ChargedGrayFamilyGameSpec 4 (halfAmplification (32 * d))
        (dyadicScale (grayEndgameA d)) ((3 / 4 : ℚ) * dyadicScale (grayEndgameA d))
        (grayEndgameA d) (grayEndgameA d + grayFootprint (32 * d))
        (2 * (32 * d)) (pinnedEndgameB d) 1 [] (ctrl d) := by
    intro d hd
    exact hrung (32 * d) (by omega) (grayEndgameA d) (one_le_grayEndgame_a hd) 1 [] le_rfl
  refine gacsDayGameStatement_of_singleCall 129 pinnedEndgameH pinnedEndgameB
    (fun _ => 1) pinnedEndgameAlpha ctrl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact computable₂_liftFamilyStrategy_scheme pinnedEndgameK pinnedEndgameA
      pinnedEndgameE (fun _ => 1) (fun d => 1 / (d : ℚ)) σ computable_pinnedEndgame_k
      computable_pinnedEndgame_a computable_pinnedEndgame_e (Computable.const 1)
      computable_one_div_d hσ
  · intro d hd
    exact pinnedEndgame_height_le hd
  · intro d _
    exact Nat.one_le_two_pow
  · intro d hd
    exact pinnedEndgame_branch_le hd (grayEndgameA d)
  · intro d hd
    exact singleCall_budget d hd
  · intro d hd
    exact (S d hd).weak.legal
  · intro d hd
    exact (S d hd).weak.range_supported
  · intro d hd sm hsm
    exact familyClientWinsUnserved_of_charged_window (S d hd) (singleCall_window d hd) sm hsm

/-- **The unconditional corollary.**  The committed canonical pinned ladder of
`GacsDayV2BaseRung` satisfies `PinnedGrayUniformInductionStatement`, so the
Gács–Day game statement holds outright. -/
theorem gacsDayGameStatement_of_canonicalPinned : GacsDayGameStatement :=
  gacsDayGameStatement_of_pinnedUniform
    ⟨canonicalPinnedScheme, canonicalPinnedScheme_computable, pinnedChargedRung_canonicalPinned⟩

end Kolmogorov
