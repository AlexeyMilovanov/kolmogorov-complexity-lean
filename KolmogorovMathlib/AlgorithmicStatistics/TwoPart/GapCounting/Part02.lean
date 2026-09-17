import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting.GapBounds
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting.IndexSelector

/-!
# Counting descriptions: the statement

`manyIJDescriptions_of_realizedSetOptimalityGap`: a string realizing an optimality gap has
many `(i, j)`-descriptions.  This is the endpoint of the gap-counting argument, assembled from
the bounds of `GapBounds` and the enumeration of `IndexSelector`;
`gapCounting_slack_arithmetic` absorbs its two slack terms into one.
-/

namespace Kolmogorov

open CodedFiniteDistribution
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- The two slack terms of the gap-counting argument are absorbed into a single logarithmic
slack in `n + delta + d`. -/
theorem gapCounting_slack_arithmetic (U : Map) (hU : IsOptimalPrefixConditional U) (c1 c2 : ℕ) :
    ∃ c_out : ℕ, ∀ (n delta d i j_min : ℕ) (x : BitString) (code : BitString),
      x.length = n →
      (i : ENat) ≤ KPPlain U x + (delta : ENat) →
      (j_min : ENat) ≤ KP U x code + (d : ENat) →
      logSlack c2 (n + i + j_min) + logSlack c1 (n + delta + d) <
        logSlack c_out (n + delta + d) := by
  obtain ⟨cKP, hKP⟩ := Kolmogorov.KP_le_KPPlain U hU
  obtain ⟨c0, hPlain⟩ := Kolmogorov.KPPlain_le_length_add_log U hU
  use 9*c2 + c1 + c2*(2*c0 + cKP + 9) + c2 + c1 + 1
  intro n delta d i j_min x code hx hi hj;
  -- Let `W := L (n + delta + d)`. Using `length_natBits_mono` (monotone in argument) and
  --   `length_natBits_add_le` repeatedly, plus `L k ≤ k` and `L k ≤ W` whenever `k ≤ n + delta +
  --   d`:
  set W := (Nat.bits (n + delta + d)).length
  have hW : (Nat.bits n).length ≤ W ∧ (Nat.bits delta).length ≤ W ∧ (Nat.bits d).length ≤ W := by
    exact ⟨length_natBits_mono (by linarith), length_natBits_mono (by linarith),
      length_natBits_mono (by linarith)⟩
  have hL_i : (Nat.bits i).length ≤ 4*W + c0 + 3 := by
    have hL_i : (Nat.bits i).length ≤
        (Nat.bits (n + 2 * (Nat.bits n).length + c0 + delta)).length := by
      refine length_natBits_mono ?_;
      convert hi.trans _;
      rotate_left;
      · exact ↑ ( n + 2 * n.bits.length + c0 + delta );
      · aesop;
      · norm_cast;
    have hL_i : (Nat.bits (n + 2 * (Nat.bits n).length + c0 + delta)).length ≤ (Nat.bits n).length +
        (Nat.bits (2 * (Nat.bits n).length)).length + (Nat.bits c0).length + (Nat.bits delta).length
        + 3 := by
      have hL_i : ∀ a b : ℕ, (Nat.bits (a + b)).length ≤ (Nat.bits a).length + (Nat.bits b).length +
          1 := by
        intros a b
        have hL_i : (Nat.bits (a + b)).length ≤ (Nat.bits a).length + (Nat.bits b).length + 1 := by
          have := length_natBits_add_le a b
          exact this
        exact hL_i;
      grind;
    have hL_i : (Nat.bits (2 * (Nat.bits n).length)).length ≤ 2 * (Nat.bits n).length :=
      length_natBits_le _
    linarith [length_natBits_le c0]
  have hL_j_min : (Nat.bits j_min).length ≤ 4*W + c0 + cKP + 4 := by
    have hL_j_min : (Nat.bits j_min).length ≤
        (Nat.bits (n + 2 * (Nat.bits n).length + c0 + cKP + d)).length := by
      refine length_natBits_mono ?_
      have hbound :
          KP U x code + (d : ENat) ≤
            ((n + 2 * n.bits.length + c0 + cKP + d : ℕ) : ENat) := by
        calc
          KP U x code + (d : ENat)
              ≤ (KPPlain U x + (cKP : ENat)) + (d : ENat) :=
                add_le_add (hKP x code) le_rfl
          _ ≤ ((x.length : ENat) + 2 * (x.length.bits.length : ENat) +
                  (c0 : ENat) + (cKP : ENat)) + (d : ENat) :=
                add_le_add (add_le_add (hPlain x) le_rfl) le_rfl
          _ = ((n + 2 * n.bits.length + c0 + cKP + d : ℕ) : ENat) := by
                rw [hx]
                norm_cast
      exact ENat.natCast_le_natCast.mp (hj.trans hbound)
    have hL_j_min : (Nat.bits (n + 2 * (Nat.bits n).length + c0 + cKP + d)).length ≤
        (Nat.bits n).length + (Nat.bits (2 * (Nat.bits n).length)).length + (Nat.bits c0).length +
        (Nat.bits cKP).length + (Nat.bits d).length + 4 := by
      have hL_j_min : ∀ a b : ℕ, (Nat.bits (a + b)).length ≤ (Nat.bits a).length +
          (Nat.bits b).length + 1 := by
        intros a b
        have hL_j_min : (Nat.bits (a + b)).length ≤
            (Nat.bits a).length + (Nat.bits b).length + 1 := by
          have := length_natBits_add_le a b
          exact this
        generalize_proofs at *;
        exact hL_j_min
      generalize_proofs at *;
      grind +ring;
    have hL_j_min : (Nat.bits (2 * (Nat.bits n).length)).length ≤ 2 * (Nat.bits n).length :=
      length_natBits_le _
    have hL_j_min : (Nat.bits c0).length ≤ c0 ∧ (Nat.bits cKP).length ≤ cKP :=
      ⟨length_natBits_le c0, length_natBits_le cKP⟩
    linarith
  have hL_sum : (Nat.bits (n + i + j_min)).length ≤ 9*W + (2*c0 + cKP + 9) := by
    have hL_sum : (Nat.bits (n + i + j_min)).length ≤
        (Nat.bits (n + i)).length + (Nat.bits j_min).length + 1 :=
      length_natBits_add_le (n + i) j_min
    linarith [ length_natBits_add_le n i ]
  simp_all +decide [ logSlack ];
  nlinarith only [ hL_sum, hW, show 0 ≤ c2 * ( 2 * c0 + cKP + 9 ) by positivity ]

/-
The tight gap-counting bridge: realized deficiency gap implies many descriptions.
From `RealizedSetOptimalityGap U A hA x delta i j kx`, `DeficiencyLe U (codedUniformOn A hA) x d`,
`d ≤ delta`, derive `ManyIJDescriptions U x i j (delta - d - slack)`
up to the log-slack already in the theorem.
-/
theorem manyIJDescriptions_of_realizedSetOptimalityGap (U : Map) (hU : IsOptimalPrefixConditional U)
    :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n delta d i j kx c_soi : ℕ),
      x.length = n →
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ slack : ℕ, slack ≤ logSlack c (n + delta + d) ∧
        ManyIJDescriptions U x i j (delta - d - slack) := by
  rcases gap_lowerBound_conditional_setComplexity_tight U hU with ⟨c1, hc1⟩
  rcases description_count_of_conditional_complexity_gap U hU with ⟨c2, hc2⟩
  rcases gapCounting_slack_arithmetic U hU c1 c2 with ⟨c3, hc3⟩
  refine ⟨c3, fun A hA x n delta d i j kx c_soi hn h_realized hdef_cond hd => ?_⟩
  have hxA := h_realized.1
  have hi := h_realized.2.1
  have hj := h_realized.2.2.1
  have hj_lower := h_realized.2.2.2.1
  have hkx := h_realized.2.2.2.2.1
  have hdelta_eq := h_realized.2.2.2.2.2
  have hi_bound : (i : ENat) ≤ KPPlain U x + (delta : ENat) := by
    have hkx_eq : KPPlain U x = (kx : ENat) := hkx.symm
    rw [hkx_eq]
    norm_cast
    omega
  rcases card_le_of_deficiency hxA hdef_cond with ⟨j_opt, hj_opt, hj_bound⟩
  have h_gap := hc1 A hA x n delta d i j kx c_soi hn
    ⟨hxA, hi, hj, hj_lower, hkx, hdelta_eq⟩ hdef_cond hd
  have hj_min : A.card ≤ 2 ^ min j j_opt := by
    by_cases hle : j ≤ j_opt
    · rw [Nat.min_eq_left hle]
      exact hj
    · rw [Nat.min_eq_right (le_of_not_ge hle)]
      exact hj_opt
  clear hdelta_eq
  set slack := logSlack c3 (n + delta + d)
  use slack
  refine ⟨le_refl slack, ?_⟩
  by_cases h_zero : delta - d ≤ slack
  · rw [Nat.sub_eq_zero_of_le h_zero]
    exact manyIJDescriptions_zero U A hA x i j hxA hi hj
  · -- We derive `ManyIJDescriptions` by contradiction using the slack bound:
    -- combining the conditional lower bound (`hc1`), the description-count upper
    -- bound (`hc2`), and the slack arithmetic (`hc3`).
    contrapose! h_zero
    have := hc2 A hA x n i (Min.min j j_opt) (delta - d - slack) kx hn hxA hi hj_min hkx
    simp_all only [tsub_le_iff_right, ge_iff_le, Nat.sub_sub]
    have := hc3 n delta d i (Min.min j j_opt) x (codedUniformOn A hA).code hn hi_bound
      (le_trans (mod_cast min_le_right _ _) hj_bound)
    simp_all only [logSlack]
    rename_i h
    specialize h (fun h => h_zero <| h.mono_j <| min_le_left _ _)
    simp_all only [slack]
    contrapose! h_gap
    simp_all only [logSlack]
    refine lt_of_le_of_lt (add_le_add_three h le_rfl le_rfl) ?_
    norm_cast
    omega

end Kolmogorov
