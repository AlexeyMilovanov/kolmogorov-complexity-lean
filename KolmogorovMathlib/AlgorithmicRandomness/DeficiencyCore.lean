import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveReal
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore

/-!
# The deficiency of a Martin-Löf test

`mlDeficiency U w` is the least level `n` of the test `U` that no longer covers `w`, and `⊤`
when every level does.  `IsMaximalMLDeficiencyTest` names a test whose deficiency dominates
that of every other test up to one additive constant, and `exists_maximal_mlDeficiency` builds
one for any computable measure, by the usual effective mixture of all tests.

`isEffectivelyNull_iff_exists_uniformlyEffectiveOpen_bound` is the reformulation of effective
nullity used in that proof: a set is effectively null exactly when a uniformly effectively
open family with the right measure bounds contains it.
-/






namespace Kolmogorov

open MeasureTheory Topology
open scoped ENNReal NNReal

-- Theorem 38
/-- A set is effectively null exactly when it is contained in the intersection of a uniformly
effectively open antitone sequence whose `n`-th term has measure at most `2^{-n}`. -/
theorem isEffectivelyNull_iff_exists_uniformlyEffectiveOpen_bound {μ : Measure CantorSeq}
    {A : Set CantorSeq} :
    IsEffectivelyNull μ A ↔
    ∃ U : ℕ → Set CantorSeq, IsUniformlyEffectiveOpen U ∧
      Antitone U ∧ A ⊆ (⋂ n, U n) ∧ ∀ n, μ (U n) ≤ dyadicValue 1 n := by
  constructor
  · intro h
    -- Decreasing-family refinement: replace the level `U n` by the tail union
    -- `⋃ k, U (n + k + 1)`, which is automatically antitone, still contains the
    -- intersection, and has measure at most `∑_{m > n} 2⁻ᵐ = 2⁻ⁿ`.
    obtain ⟨U, ⟨f, hf, hUeq⟩, hA, hbound⟩ := h
    set W : ℕ → Set CantorSeq := fun p => U (Nat.unpair p).2 with hWdef
    have hWopen : IsUniformlyEffectiveOpen W := by
      refine ⟨fun p i => f (Nat.unpair p).2 i, ?_, fun p => hUeq _⟩
      exact hf.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).to_comp
        Computable.snd
    have hWbound : ∀ k n, μ (W (Nat.pair k n)) ≤ dyadicValue 1 n := by
      intro k n
      simp only [hWdef, Nat.unpair_pair]
      exact hbound n
    refine ⟨fun n => ⋃ k, W (Nat.pair k (n + k + 1)),
      isUniformlyEffectiveOpen_shifted_iUnion hWopen, ?_, ?_,
      fun n => measure_shifted_iUnion_le hWbound n⟩
    · intro m n hmn x hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
      refine Set.mem_iUnion.2 ⟨(n - m) + k, ?_⟩
      simp only [hWdef, Nat.unpair_pair] at hk ⊢
      have heq : m + (n - m + k) + 1 = n + k + 1 := by omega
      rw [heq]
      exact hk
    · intro x hx
      refine Set.mem_iInter.2 fun n => Set.mem_iUnion.2 ⟨0, ?_⟩
      simp only [hWdef, Nat.unpair_pair]
      exact Set.mem_iInter.1 (hA hx) (n + 0 + 1)
  · rintro ⟨U, hU, -, hA, hbound⟩
    exact ⟨U, hU, hA, hbound⟩

-- Theorem 39
/-- The randomness deficiency of `w` with respect to the test `U`: the least `n` with
`w ∉ U n`, and `⊤` when `w` lies in every level of the test. -/
noncomputable def mlDeficiency (U : ℕ → Set CantorSeq) (w : CantorSeq) : ENat :=
  ⨆ (n : ℕ) (_ : w ∈ U n), (n : ENat)

/-- A Martin-Löf test whose deficiency dominates the deficiency of every other
test up to one additive constant, uniform in the sequence. -/
def IsMaximalMLDeficiencyTest (μ : Measure CantorSeq)
    (U : ℕ → Set CantorSeq) : Prop :=
  IsMartinLofTest μ U ∧
    ∀ V, IsMartinLofTest μ V →
      ∃ c : ℕ, ∀ w, mlDeficiency V w ≤ mlDeficiency U w + (c : ENat)

/-- Every computable measure admits a Martin-Löf test whose deficiency function dominates that
of all other tests up to an additive constant. -/
theorem exists_maximal_mlDeficiency {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) :
    ∃ U : ℕ → Set CantorSeq, IsMaximalMLDeficiencyTest μ U := by
  obtain ⟨a, hacomp, ha⟩ := hμ
  refine ⟨universalTest a, ⟨isUniformlyEffectiveOpen_universalTest hacomp,
    fun n => measure_universalTest_le ha n⟩, ?_⟩
  intro V hV
  obtain ⟨⟨h, hh, hVeq⟩, hVbound⟩ := hV
  have hh' : Computable₂ (fun m i => h (m + 1) i) :=
    hh.comp (Primrec.succ.comp Primrec.fst).to_comp Computable.snd
  obtain ⟨c, hc⟩ := exists_code_candEnum hh'
  refine ⟨c + 3, fun w => ?_⟩
  unfold mlDeficiency
  refine iSup_le fun n => iSup_le fun hwn => ?_
  by_cases hle : n ≤ c + 3
  · exact le_trans (WithTop.coe_le_coe.mpr hle) le_add_self
  · push_neg at hle
    have hsub : V n ⊆ universalTest a (n - c - 3) := by
      intro x hx
      refine Set.mem_iUnion.2 ⟨c, ?_⟩
      have hm : n - c - 3 + c + 3 = n := by omega
      have hlevel : (Nat.unpair (Nat.pair c (n - c - 3 + c + 1))).2 = n - c - 3 + c + 1 := by
        rw [Nat.unpair_pair]
      have hcand : (⋃ s, coverSet (candEnum (Nat.pair c (n - c - 3 + c + 1))) s)
          = V (n - c - 3 + c + 3) := by
        rw [hc (n - c - 3 + c + 1)]
        have heq_idx : n - c - 3 + c + 1 + 1 + 1 = n - c - 3 + c + 3 := by omega
        rw [heq_idx, hVeq (n - c - 3 + c + 3)]
        refine Set.iUnion_congr fun i => ?_
        rw [coverSet]
      have hsmall : μ (⋃ s, coverSet (candEnum (Nat.pair c (n - c - 3 + c + 1))) s)
          ≤ (2 : ℝ≥0∞)⁻¹ ^ ((Nat.unpair (Nat.pair c (n - c - 3 + c + 1))).2 + 2) := by
        rw [hcand, hlevel]
        have h_pow : (n - c - 3 + c + 1 + 2) = n - c - 3 + c + 3 := by omega
        rw [h_pow]
        have hv := hVbound (n - c - 3 + c + 3)
        have h_dv : dyadicValue 1 (n - c - 3 + c + 3) = (2 : ℝ≥0∞)⁻¹ ^ (n - c - 3 + c + 3) := by
          unfold dyadicValue
          rw [div_eq_mul_inv, Nat.cast_one, one_mul, ← ENNReal.inv_pow]
        rwa [h_dv] at hv
      have heq : univSet a (Nat.pair c (n - c - 3 + c + 1)) =
          ⋃ s, coverSet (candEnum (Nat.pair c (n - c - 3 + c + 1))) s :=
        univSet_eq_of_measure_le ha hsmall
      rw [heq, hcand, hm]
      exact hx
    have h1 : ((n - c - 3 : ℕ) : ENat) ≤ ⨆ (m : ℕ) (_ : w ∈ universalTest a m), (m : ENat) :=
      le_iSup_of_le (n - c - 3) (le_iSup_of_le (hsub hwn) le_rfl)
    have h2 : (n : ENat) = ((n - c - 3 : ℕ) : ENat) + (c + 3 : ℕ) := by
      rw [← ENat.coe_add]
      congr 1
      omega
    rw [h2]
    exact add_le_add h1 le_rfl


end Kolmogorov
