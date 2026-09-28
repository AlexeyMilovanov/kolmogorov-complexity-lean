import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.EnumerationTail
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaPrefix.Part01

/-!
# Finite Omegas at two levels are equivalent

`prop_omega_equivalence` (VS40 Proposition `prop:omega-equivalence`): for `k ≤ m`, the fixed
finite Omega code `Ω_k` and the first `k` bits of `Ω_m` determine each other up to logarithmic
slack.  The direction proved here is `condK_omegaPrefix_le_of_omegaCode`: given `Ω_k`, the
high `k` bits of `Ω_m` are cheap.  The other direction comes from `OmegaPrefix/Part01`.
-/

namespace Kolmogorov
open Nat.Partrec (Code)

/-- **Reverse half of finite Omega equivalence.**  Given `Ω_k`, the first `k`
bits of `Ω_m` have plain conditional complexity `O(log m)`, uniformly for
`k ≤ m`.  The proof uses the executable reverse selector and charges only its
fixed-width quotient offset. -/
theorem condK_omegaPrefix_le_of_omegaCode
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m k : ℕ, k ≤ m →
      condK V ((omegaFixedCode c m).take k)
        (omegaFixedCode c k) ≤ (logSlack C m : ENat) := by
  obtain ⟨Ctail, htail⟩ :=
    omegaPrefix_stage_offset_upper_bound V hV c hc
  obtain ⟨Cmap, hmap⟩ :=
    condK_partrec_cond_map_le V hV
      (omegaPrefixReverseSelector c)
      (omegaPrefixReverseSelector_partrec c)
  let C := Ctail + Cmap + 3
  refine ⟨C, fun m k hk => ?_⟩
  let divisor := 2 ^ (m + 1 - k)
  let stageLength :=
    (boundedOutputStage c m
      (boundedOutputCompletionTime c k)).length
  let offset :=
    omegaCount c m / divisor - stageLength / divisor
  let offsetWidth := logSlack Ctail m + 2
  have hoffsetLe :
      offset ≤ 2 ^ logSlack Ctail m + 1 := by
    simpa [offset, divisor, stageLength] using htail m k hk
  have hoffset :
      offset < 2 ^ offsetWidth := by
    dsimp [offsetWidth]
    rw [show logSlack Ctail m + 2 =
      logSlack Ctail m + 1 + 1 by omega, pow_succ, pow_succ]
    have hpow : 0 < 2 ^ logSlack Ctail m := by positivity
    nlinarith
  have hselector :
      (omegaFixedCode c m).take k ∈
        omegaPrefixReverseSelector c (omegaFixedCode c k)
          (omegaPrefixReverseAdvice m offset offsetWidth) := by
    simpa [offset, divisor, stageLength] using
      omegaPrefixReverseSelector_intended_input c m k offsetWidth hk
  have hadviceLength :
      (omegaPrefixReverseAdvice m offset offsetWidth).length =
        2 * (Nat.bits m).length + offsetWidth + 1 :=
    omegaPrefixReverseAdvice_length hoffset
  have hbudget :
      (omegaPrefixReverseAdvice m offset offsetWidth).length + Cmap ≤
        logSlack C m := by
    rw [hadviceLength]
    dsimp [offsetWidth, C, logSlack]
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le Ctail, Nat.zero_le Cmap]
  calc
    condK V ((omegaFixedCode c m).take k)
        (omegaFixedCode c k) ≤
      ((omegaPrefixReverseAdvice m offset offsetWidth).length : ENat) +
        (Cmap : ENat) :=
      hmap _ _ _ hselector
    _ = (((omegaPrefixReverseAdvice m offset offsetWidth).length +
        Cmap : ℕ) : ENat) := by
      rw [Nat.cast_add]
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast hbudget

/-- **VS40 Proposition `prop:omega-equivalence`.**  For `k ≤ m`, the fixed
finite Omega code `Ω_k` and the literal first `k` high bits `(Ω_m)_k` determine
each other with `O(log m)` plain conditional advice. -/
theorem prop_omega_equivalence
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m k : ℕ, k ≤ m →
      condK V (omegaFixedCode c k)
          ((omegaFixedCode c m).take k) ≤
            (logSlack C m : ENat) ∧
      condK V ((omegaFixedCode c m).take k)
          (omegaFixedCode c k) ≤
            (logSlack C m : ENat) := by
  obtain ⟨Cforward, hforward⟩ :=
    condK_omegaCode_le_of_omegaPrefix V hV c hc
  obtain ⟨Creverse, hreverse⟩ :=
    condK_omegaPrefix_le_of_omegaCode V hV c hc
  let C := max Cforward Creverse
  refine ⟨C, fun m k hk => ⟨?_, ?_⟩⟩
  · exact (hforward m k hk).trans (by
      exact_mod_cast logSlack_mono_left
        (le_max_left Cforward Creverse) m)
  · exact (hreverse m k hk).trans (by
      exact_mod_cast logSlack_mono_left
        (le_max_right Cforward Creverse) m)

end Kolmogorov
