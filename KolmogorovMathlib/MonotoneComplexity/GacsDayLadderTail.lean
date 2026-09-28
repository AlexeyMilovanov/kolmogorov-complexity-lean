import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderRungs
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCode
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwoComputable

/-!
# Discharging the first two steps of the ladder

`grayLadderStep_components` (in `GacsDayLadderStepClosure`) asks for a
transformer of strategy schemes that performs Day's half-step at *every* stage
`k`. The first two of those steps are already available in kernel-checked form:

* `k = 0 -> 1` is the static two-child split of `GacsDayHalfAmplification`,
  whose rung is `grayRung_one`;
* `k = 1 -> 2` is the probe-and-raise strategy of `GacsDayStageTwo`, whose rung
  is `grayRung_two`.

Both are computable (`computable_halfStepFamilyScheme`,
`computable_stageTwoFamilyScheme`), hence have codes, and both have depth loss
`3`, which is below the loss `c * (k + 1) ^ 2 * L + c * (k + 1)` the recurrence
of SUV p. 143 allows as soon as `c ≥ 3`. Neither of them looks at the scheme it
is handed, so they can simply be patched into any transformer.

`grayLadderStep_components_of_tail` performs that patch: a transformer that only
does Day's half-step from stage `2` on already yields the full
`grayLadderStep_components`. The remaining mathematics is therefore the
*tail* of the ladder, `k + 2 -> k + 3`.
-/

namespace Kolmogorov

/-- A transformer patched at the two proved stages: stage `0 -> 1` is the static
two-child split, stage `1 -> 2` is the probe-and-raise strategy, and every later
stage is left to `F`. -/
def ladderPatchScheme (F : ℕ → FamilyStrategyScheme → FamilyStrategyScheme) :
    ℕ → FamilyStrategyScheme → FamilyStrategyScheme
  | 0, _ => fun a e => halfStepFamilyStrategy a (e + 3)
  | 1, _ => fun a e => stageTwoFamilyStrategy a (e + 3)
  | (k + 2), sigma => F (k + 2) sigma

/-- The code transformer patched at the two proved stages. -/
def ladderPatchCode (c1 c2 : Nat.Partrec.Code)
    (G : ℕ → Nat.Partrec.Code → Nat.Partrec.Code) :
    ℕ → Nat.Partrec.Code → Nat.Partrec.Code :=
  fun k code =>
    bif decide (k = 0) then c1 else bif decide (k = 1) then c2 else G k code

/-- The patched ladder uses the first given code at stage `0`. -/
@[simp] lemma ladderPatchCode_zero (c1 c2 : Nat.Partrec.Code)
    (G : ℕ → Nat.Partrec.Code → Nat.Partrec.Code) (code : Nat.Partrec.Code) :
    ladderPatchCode c1 c2 G 0 code = c1 := by simp [ladderPatchCode]

/-- The patched ladder uses the second given code at stage `1`. -/
@[simp] lemma ladderPatchCode_one (c1 c2 : Nat.Partrec.Code)
    (G : ℕ → Nat.Partrec.Code → Nat.Partrec.Code) (code : Nat.Partrec.Code) :
    ladderPatchCode c1 c2 G 1 code = c2 := by simp [ladderPatchCode]

/-- From stage `2` on, the patched ladder follows the transformer `G`. -/
@[simp] lemma ladderPatchCode_add_two (c1 c2 : Nat.Partrec.Code)
    (G : ℕ → Nat.Partrec.Code → Nat.Partrec.Code) (k : ℕ) (code : Nat.Partrec.Code) :
    ladderPatchCode c1 c2 G (k + 2) code = G (k + 2) code := by
  simp [ladderPatchCode]

/-- Patching two constant codes preserves computability of the transformer. -/
theorem computable₂_ladderPatchCode (c1 c2 : Nat.Partrec.Code)
    {G : ℕ → Nat.Partrec.Code → Nat.Partrec.Code} (hG : Computable₂ G) :
    Computable₂ (ladderPatchCode c1 c2 G) := by
  have h0 : Computable (fun p : ℕ × Nat.Partrec.Code => decide (p.1 = 0)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp Computable.fst (Computable.const 0)
  have h1 : Computable (fun p : ℕ × Nat.Partrec.Code => decide (p.1 = 1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp Computable.fst (Computable.const 1)
  exact Computable.cond h0 (Computable.const c1)
    (Computable.cond h1 (Computable.const c2) hG)

/-- **The first two rungs are free.** A transformer that performs Day's
half-step only from stage `2` on, together with a code transformer for it,
already provides the full `grayLadderStep_components` data. -/
theorem grayLadderStep_components_of_tail
    (F : ℕ → FamilyStrategyScheme → FamilyStrategyScheme)
    (G : ℕ → Nat.Partrec.Code → Nat.Partrec.Code) (c : ℕ) (hc : 3 ≤ c)
    (hG : Computable₂ G)
    (hGcode : ∀ (k : ℕ) (code : Nat.Partrec.Code) (sigma : FamilyStrategyScheme),
      CodeComputesScheme code sigma → CodeComputesScheme (G k code) (F k sigma))
    (hRung : ∀ (k L B : ℕ) (sigma : FamilyStrategyScheme),
      B ≤ max 2 (c * (k + 3) * 2 ^ L) → GrayRung (k + 2) L B sigma →
      GrayRung (k + 3) (c * (k + 3) ^ 2 * L + c * (k + 3))
        (max 2 (c * (k + 3) *
          2 ^ (c * (k + 3) ^ 2 * L + c * (k + 3)))) (F (k + 2) sigma)) :
    ∃ (F' : ℕ → FamilyStrategyScheme → FamilyStrategyScheme)
      (G' : ℕ → Nat.Partrec.Code → Nat.Partrec.Code) (c' : ℕ),
    2 ≤ c' ∧ Computable₂ G' ∧
    (∀ (k : ℕ) (code : Nat.Partrec.Code) (sigma : FamilyStrategyScheme),
      CodeComputesScheme code sigma → CodeComputesScheme (G' k code) (F' k sigma)) ∧
    (∀ k L B sigma, B ≤ max 2 (c' * (k + 1) * 2 ^ L) → GrayRung k L B sigma →
      GrayRung (k + 1) (c' * (k + 1) ^ 2 * L + c' * (k + 1))
        (max 2 (c' * (k + 1) *
          2 ^ (c' * (k + 1) ^ 2 * L + c' * (k + 1)))) (F' k sigma)) := by
  obtain ⟨c1, hc1⟩ :=
    exists_code_of_familyStrategySchemeComputable computable_halfStepFamilyScheme
  obtain ⟨c2, hc2⟩ :=
    exists_code_of_familyStrategySchemeComputable computable_stageTwoFamilyScheme
  refine ⟨ladderPatchScheme F, ladderPatchCode c1 c2 G, c, by omega,
    computable₂_ladderPatchCode c1 c2 hG, ?_, ?_⟩
  · intro k code sigma hcode
    match k with
    | 0 => simpa [ladderPatchScheme] using hc1
    | 1 => simpa [ladderPatchScheme] using hc2
    | (k + 2) => simpa [ladderPatchScheme] using hGcode (k + 2) code sigma hcode
  · intro k L B sigma hB hk
    match k with
    | 0 =>
      have hone : GrayRung 1 3
          (max 2 (c * (0 + 1) * 2 ^ (c * (0 + 1) ^ 2 * L + c * (0 + 1))))
          (fun a e => halfStepFamilyStrategy a (e + 3)) :=
        grayRung_one _ (le_max_left _ _)
      have hloss : 3 ≤ c * (0 + 1) ^ 2 * L + c * (0 + 1) := by
        have : c ≤ c * (0 + 1) ^ 2 * L + c * (0 + 1) := by nlinarith [Nat.zero_le (c * L)]
        omega
      exact grayRung_mono_loss hloss hone
    | 1 =>
      have htwo : GrayRung 2 3
          (max 2 (c * (1 + 1) * 2 ^ (c * (1 + 1) ^ 2 * L + c * (1 + 1))))
          (fun a e => stageTwoFamilyStrategy a (e + 3)) :=
        grayRung_two _ (le_max_left _ _)
      have hloss : 3 ≤ c * (1 + 1) ^ 2 * L + c * (1 + 1) := by
        have : 2 * c ≤ c * (1 + 1) ^ 2 * L + c * (1 + 1) := by nlinarith [Nat.zero_le (c * L)]
        omega
      exact grayRung_mono_loss hloss htwo
    | (k + 2) => exact hRung k L B sigma hB hk

/-- **The recurrence only has to be met with room to spare.** A construction
that achieves depth loss `L'` and deep branching `B'` at stage `k + 3`, both
below what the recurrence of SUV p. 143 allows, meets the recurrence exactly:
a rung stays a rung when the fine scale gets finer (`grayRung_mono_loss`) and
when the tree gets wider (`grayRung_mono_branching`). -/
theorem grayRung_step_of_le {c k L B' L' : ℕ} {sigma : FamilyStrategyScheme}
    (hL : L' ≤ c * (k + 3) ^ 2 * L + c * (k + 3))
    (hB : B' ≤ max 2 (c * (k + 3) *
      2 ^ (c * (k + 3) ^ 2 * L + c * (k + 3))))
    (H : GrayRung (k + 3) L' B' sigma) :
    GrayRung (k + 3) (c * (k + 3) ^ 2 * L + c * (k + 3))
      (max 2 (c * (k + 3) *
        2 ^ (c * (k + 3) ^ 2 * L + c * (k + 3)))) sigma :=
  grayRung_mono_branching hB (grayRung_mono_loss hL H)

end Kolmogorov
