import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasureSanitizer
import KolmogorovMathlib.MonotoneComplexity.UniformTreeSanitizer
import KolmogorovMathlib.MonotoneComplexity.SimpleTreeApproximation
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure

/-!
# The standard enumeration of lower semicomputable continuous semimeasures

`treeLSCEnum i` is the `i`-th lower semicomputable continuous tree semimeasure: the `i`-th
computable stage approximation, passed through the sanitiser so that the result always satisfies
the axioms. Every member of the enumeration really is one
(`treeLSCEnum_isLowerSemicomputableContinuousSemimeasure`), the approximations behind it are
computable uniformly in the index (`treeLSCEnumApprox_uniform_computable`), and the enumeration
is complete (`treeLSCEnum_complete`) because on an honest approximation the sanitiser changes
nothing (`rootBudgetOK_of_honest`, `treeSanitize_eq_simpleApprox_of_honest`,
`treeLSCEnum_eq_of_iSup_eq`). The limit machinery is
`iSup_add_iSup_of_stage_mono` and
`isLowerSemicomputableContinuousSemimeasure_iSup_of_stage`.
-/

namespace Kolmogorov
open scoped ENNReal

/-- For stage-monotone approximations the sum of the two children's limits is the limit of the
stage-wise sums. -/
theorem iSup_add_iSup_of_stage_mono {q : ℕ → BitString → ℕ}
    (hmono : ∀ s x, dyadicValue (q s x) s ≤ dyadicValue (q (s + 1) x) (s + 1)) (x : BitString) :
    (⨆ s, dyadicValue (q s (x ++ [false])) s) + (⨆ s, dyadicValue (q s (x ++ [true])) s) =
      ⨆ s, dyadicValue (q s (x ++ [false])) s + dyadicValue (q s (x ++ [true])) s := by
  exact ENNReal.iSup_add_iSup_of_monotone (fun s1 s2 hs => by
    induction hs with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono _ _)
  ) (fun s1 s2 hs => by
    induction hs with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono _ _)
  )

/-- A computable, stage-monotone family of integer approximations that is normalised at the root and
respects the child inequality at each stage has as its limit a lower semicomputable continuous
semimeasure. -/
theorem isLowerSemicomputableContinuousSemimeasure_iSup_of_stage
    {q : ℕ → BitString → ℕ} (hroot : ∀ s, q s [] = 2 ^ s)
    (hcoh : ∀ s x, q s (x ++ [false]) + q s (x ++ [true]) ≤ q s x)
    (hmono : ∀ s x, dyadicValue (q s x) s ≤ dyadicValue (q (s + 1) x) (s + 1))
    (hcomp : Computable (fun p : ℕ × BitString => q p.1 p.2)) :
    IsLowerSemicomputableContinuousSemimeasure (fun x => ⨆ s, dyadicValue (q s x) s) := by
  constructor
  · constructor
    · simp_rw [hroot]
      have h1 : ∀ s, dyadicValue (2 ^ s) s = 1 := fun s => dyadicValue_two_pow_self s
      simp_rw [h1]
      exact iSup_const
    · intro x
      have h_le : ∀ s, dyadicValue (q s (x ++ [false])) s
          + dyadicValue (q s (x ++ [true])) s ≤ dyadicValue (q s x) s := by
        intro s
        rw [← dyadicValue_add]
        exact dyadicValue_le _ _ _ (hcoh s x)
      rw [iSup_add_iSup_of_stage_mono hmono]
      exact iSup_mono h_le
  · use fun s x _ => q s x
    refine ⟨fun s out _ => hmono s out, fun x _ => rfl, ?_⟩
    exact hcomp.comp (Computable.fst.pair (Computable.fst.comp Computable.snd))

/-- The `i`-th continuous semimeasure of the standard enumeration, obtained by sanitising the `i`-th
partial computable approximation into a monotone one. -/
noncomputable def treeLSCEnum (i : ℕ) : BitString → ℝ≥0∞ :=
  fun x => ⨆ s, dyadicValue (treeSanitize (fun s out _ => makeMono (approxEnum i) s out []) s x) s

/-- The staged approximations behind the enumeration are computable uniformly in the index, the
stage
and the string. -/
theorem treeLSCEnumApprox_uniform_computable :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      treeSanitize (fun s out _ => makeMono (approxEnum p.1) s out []) p.2.1 p.2.2.1) := by
  have hproj : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      (p.1, p.2.1, p.2.2.1, ([] : BitString))) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair (Computable.const [])))
  have hproj2 : Computable (fun p : ℕ × ℕ × BitString × BitString => (p.1, p.2.1, p.2.2.1)) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hb := (makeMono_computable_uniform (fun i => approxEnum i) approxEnum_computable).comp hproj
  have hmain := computable_treeSanitize_uniform
    (fun i s out _ => makeMono (approxEnum i) s out []) hb
  exact (hmain.comp hproj2).of_eq (fun _ => rfl)

/-- Every member of the enumeration is a lower semicomputable continuous semimeasure. -/
theorem treeLSCEnum_isLowerSemicomputableContinuousSemimeasure (i : ℕ) :
    IsLowerSemicomputableContinuousSemimeasure (treeLSCEnum i) := by
  apply isLowerSemicomputableContinuousSemimeasure_iSup_of_stage
  · exact fun s => treeSanitize_root _ s
  · exact fun s x => treeSanitize_coherent _ s x
  · exact fun s x => treeSanitize_stage_mono _ (fun s out _ => makeMono_mono _ s out []) s x
  · refine computable_treeSanitize _ ?_
    have h : Computable (fun p : ℕ × BitString × BitString =>
        makeMono (approxEnum i) p.1 p.2.1 p.2.2) :=
      makeMono_computable (approxEnum i)
        (approxEnum_computable.comp
          ((Computable.const i).pair (Computable.fst.pair Computable.snd)))
    exact h.comp (Computable.fst.pair
      ((Computable.fst.comp Computable.snd).pair (Computable.const [])))

/-- An approximation converging to a genuine continuous tree semimeasure never exceeds its root
budget, so the sanitiser never has to cut it. -/
lemma rootBudgetOK_of_honest (a : BitString → ℝ≥0∞)
    (approx : ℕ → BitString → BitString → ℕ)
    (h_sup : ∀ x ctx, ⨆ s, dyadicValue (approx s x ctx) s = a x)
    (ha : IsContinuousTreeSemimeasure a) (s : ℕ) :
    rootBudgetOK approx s := by
  have h := simpleApprox_coherent a approx h_sup ha s []
  rw [simpleApprox_root] at h
  simpa [rootBudgetOK] using h

/-- On an approximation converging to a genuine continuous tree semimeasure the sanitiser acts as
the
identity. -/
lemma treeSanitize_eq_simpleApprox_of_honest (a : BitString → ℝ≥0∞)
    (approx : ℕ → BitString → BitString → ℕ)
    (h_sup : ∀ x ctx, ⨆ s, dyadicValue (approx s x ctx) s = a x)
    (ha : IsContinuousTreeSemimeasure a) (s : ℕ) (x : BitString) :
    treeSanitize approx s x = simpleApprox approx s x := by
  have hfz : freezeStage approx s = s :=
    (freezeStage_self_iff approx s).mpr
      fun t _ => rootBudgetOK_of_honest a approx h_sup ha t
  simp [treeSanitize, hfz]

/-- If the sanitiser leaves a converging monotone approximation unchanged then its limit is the
semimeasure being approximated. -/
lemma treeLSCEnum_eq_of_iSup_eq (a : BitString → ℝ≥0∞)
    (approx : ℕ → BitString → BitString → ℕ)
    (hmono : ∀ s out ctx,
      dyadicValue (approx s out ctx) s ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (h_sup : ∀ x ctx, ⨆ s, dyadicValue (approx s x ctx) s = a x)
    (ha : IsContinuousTreeSemimeasure a)
    (h_eq : ∀ s x, treeSanitize approx s x = simpleApprox approx s x) :
    (fun x => ⨆ s, dyadicValue (treeSanitize approx s x) s) = a := by
  ext x
  have h1 : ⨆ s, dyadicValue (treeSanitize approx s x) s
      = ⨆ s, dyadicValue (simpleApprox approx s x) s := by
    congr 1
    ext s
    rw [h_eq]
  rw [h1]
  exact iSup_simpleApprox_eq a approx hmono h_sup ha x

/-- Every lower semicomputable continuous semimeasure occurs in the enumeration. -/
theorem treeLSCEnum_complete {a : BitString → ℝ≥0∞}
    (ha : IsLowerSemicomputableContinuousSemimeasure a) : ∃ i, treeLSCEnum i = a := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := ha.2
  obtain ⟨i, hi⟩ := exists_approxEnum approx hcomp
  use i
  let monoApprox : ℕ → BitString → BitString → ℕ := fun s out _ => makeMono (approxEnum i) s out []
  have hmonoStep : ∀ s out ctx,
      dyadicValue (monoApprox s out ctx) s
        ≤ dyadicValue (monoApprox (s + 1) out ctx) (s + 1) := by
    intro s out ctx
    exact makeMono_mono _ _ _ _
  have hsupApprox : ∀ x ctx, ⨆ s, dyadicValue (monoApprox s x ctx) s = a x := by
    intro x ctx
    have h_mono_eq : ⨆ s, dyadicValue (makeMono (approxEnum i) s x []) s
        = ⨆ s, dyadicValue (approxEnum i s x []) s :=
      iSup_makeMono_eq_iSup _ _ _
    rw [h_mono_eq]
    have hi_eq : ⨆ s, dyadicValue (approxEnum i s x []) s
        = ⨆ s, dyadicValue (approx s x []) s := hi x []
    rw [hi_eq]
    exact hsup x []
  apply treeLSCEnum_eq_of_iSup_eq a monoApprox hmonoStep hsupApprox ha.1
  intro s x
  apply treeSanitize_eq_simpleApprox_of_honest a monoApprox hsupApprox ha.1

end Kolmogorov
