import KolmogorovMathlib.MonotoneComplexity.Omega.Solovay.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic
import KolmogorovMathlib.MonotoneComplexity.Omega.LscEnum
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaComplete
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaFromComplete
import KolmogorovMathlib.MonotoneComplexity.Omega.ShiftedProcess
import KolmogorovMathlib.MonotoneComplexity.Omega.LeftmostRandom

/-!
# Solovay completeness equals randomness for lower semicomputable reals

`isSolovayComplete_iff_isMartinLofRandomReal`: a lower semicomputable real is Solovay complete
exactly when it is Martin-Löf random. One direction is
`isMartinLofRandomReal_of_lowerSemicomputable_isSolovayComplete`, the other
`isSolovayComplete_of_isMartinLofRandomReal`, whose key step
`not_isMartinLofRandomReal_of_not_isSolovayComplete` shows that failure of completeness produces
a cover. Also here: every `Ω`-number lies in `(0, 1)` (`IsOmegaNumber.mem_Ioo`), the range the
theorem needs, and `isMartinLofRandomReal_add_of_left`, randomness of a sum of lower
semicomputable reals when one summand is random.

Source: SUV §5.7.2 and §5.7.4, pp. 160–165, Theorems 110 and 111.
-/

namespace Kolmogorov

open ComputableReals
open MeasureTheory ENNReal

/-- **SUV p. 160.** Every `Ω`-number lies in `(0,1)`, which is the range in which
Theorem 103 characterises them as the Solovay complete lower semicomputable reals. -/
theorem IsOmegaNumber.mem_Ioo {α : ℝ} (h : IsOmegaNumber α) : α ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨m, hm, rfl⟩ := h
  exact omegaReal_mem_Ioo hm

/-- **SUV Section 5.7.2, Remark (p. 161).** If `α` and `β` are lower semicomputable
reals and at least one of them is random, then `α + β` is random too. -/
theorem isMartinLofRandomReal_add_of_left {α β : ℝ}
    (hα : IsLowerSemicomputableReal α) (hβ : IsLowerSemicomputableReal β)
    (hrand : IsMartinLofRandomReal α) : IsMartinLofRandomReal (α + β) := by
  refine isMartinLofRandomReal_of_solovayDominates hα (hα.add hβ) ?_ hrand
  refine solovayDominates_of_isLowerSemicomputableReal_sub hα ?_
  have heq : α + β - α = β := by ring
  rw [heq]
  exact hβ

/-! ### Section 5.7.4 and Theorem 110 -/

/-- **SUV Section 5.7.4 (p. 165), the key step.** If `β` is not Solovay complete
then `β` is not ML-random: choosing `α` with `α ⋠ β` makes the second alternative of
the shifted-interval process impossible, so the observer wins and produces covers of
`β` of arbitrarily small measure. -/
theorem not_isMartinLofRandomReal_of_not_isSolovayComplete {β : ℝ}
    (hβ : IsLowerSemicomputableReal β) (h : ¬ IsSolovayComplete β) :
    ¬ IsMartinLofRandomReal β := by
  classical
  have hex : ∃ α, IsLowerSemicomputableReal α ∧ ¬ SolovayReducible α β := by
    by_contra hcon
    push_neg at hcon
    exact h ⟨hβ, hcon⟩
  obtain ⟨α, hα, hnr⟩ := hex
  obtain ⟨a⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hα
  obtain ⟨b⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hβ
  obtain ⟨K, hK⟩ := exists_nat_ge (α - ((a.seq 0 : ℚ) : ℝ))
  intro hrand
  refine hrand {β} (isEffectivelyNullReal_singleton_of_stall a b hK ?_) rfl
  intro ε hε
  by_contra hcon
  push_neg at hcon
  -- the process is total, so `α` does reduce to `β` after all
  have hwpos : 0 < scaleOf K ε := scaleOf_pos K hε
  have htot : ∀ k, ∃ t i, procIdx a.seq b.seq (scaleOf K ε) k t = some i := by
    refine total_of_not_stall a b (fun k t i hi hall => ?_)
    obtain ⟨t', ht'⟩ := hcon k t i hi
    exact ht' (hall t')
  obtain ⟨J, hJc, hJ⟩ :=
    exists_process_index a b (scaleOf K ε) a.isComputable b.isComputable htot
  have hkey := mul_sub_le_of_process a b hwpos hJ
  have hbJ := tendsto_process_index a b hwpos hJ
  have hwR : (0 : ℝ) < ((scaleOf K ε : ℚ) : ℝ) := by exact_mod_cast hwpos
  -- the reduction function of SUV p. 158
  have hdom : SolovayDominates (((scaleOf K ε : ℚ) : ℝ) * α) β := by
    refine ⟨ratSearchPair (fun k => a.seq k * scaleOf K ε) (fun k => b.seq (J k)), ?_, ?_⟩
    · exact partrec_ratSearchPair
        (Computable₂.comp computable₂_ratMul a.isComputable (Computable.const (scaleOf K ε)))
        (b.isComputable.comp hJc)
    · intro r hr
      have hdomr : (ratSearchPair (fun k => a.seq k * scaleOf K ε)
          (fun k => b.seq (J k)) r).Dom :=
        ratSearchPair_dom (exists_rat_lt_of_tendsto hbJ hr)
      obtain ⟨n, hn, hq⟩ := mem_ratSearchPair (Part.get_mem hdomr)
      refine ⟨_, Part.get_mem hdomr, ?_, ?_⟩
      · rw [hq]
        have h1 : ((a.seq n : ℚ) : ℝ) < α := a.seq_lt n
        push_cast
        nlinarith [hwR, h1]
      · rw [hq]
        have h1 := hkey n
        have h2 : ((r : ℚ) : ℝ) < ((b.seq (J n) : ℚ) : ℝ) := by exact_mod_cast hn
        push_cast
        nlinarith [h1, h2]
  -- scale back: `α ≼_{1/w} β`
  have hscaled := hdom.rat_mul (c := (scaleOf K ε)⁻¹) (by positivity)
  have hcast : (((scaleOf K ε)⁻¹ : ℚ) : ℝ) * (((scaleOf K ε : ℚ) : ℝ) * α) = α := by
    have hne : ((scaleOf K ε : ℚ) : ℝ) ≠ 0 := ne_of_gt hwR
    push_cast
    field_simp
  rw [hcast] at hscaled
  exact hnr ((solovayReducible_iff_exists_rat hβ).mpr
    ⟨(scaleOf K ε)⁻¹, by positivity, hscaled⟩)

/-- A Solovay complete lower semicomputable real is ML-random.  SUV Theorem 110 (Section 5.7, p.
165), forward direction. -/
theorem isMartinLofRandomReal_of_lowerSemicomputable_isSolovayComplete {β : ℝ}
    (_hβ : IsLowerSemicomputableReal β) (h : IsSolovayComplete β) :
    IsMartinLofRandomReal β :=
  isMartinLofRandomReal_of_isSolovayComplete h

/-- An ML-random lower semicomputable real is Solovay complete.  SUV Theorem 110 (Section 5.7,
p. 165), reverse direction. -/
theorem isSolovayComplete_of_isMartinLofRandomReal {β : ℝ}
    (hβ : IsLowerSemicomputableReal β) (h : IsMartinLofRandomReal β) :
    IsSolovayComplete β := by
  by_contra hc
  exact not_isMartinLofRandomReal_of_not_isSolovayComplete hβ hc h

/-- A lower semicomputable real is Solovay complete if and only if it is ML-random.  SUV Theorem
110 (Section 5.7, p. 165). -/
theorem isSolovayComplete_iff_isMartinLofRandomReal {β : ℝ} (hβ : IsLowerSemicomputableReal β) :
    IsSolovayComplete β ↔ IsMartinLofRandomReal β :=
  ⟨isMartinLofRandomReal_of_lowerSemicomputable_isSolovayComplete hβ,
    isSolovayComplete_of_isMartinLofRandomReal hβ⟩

end Kolmogorov
