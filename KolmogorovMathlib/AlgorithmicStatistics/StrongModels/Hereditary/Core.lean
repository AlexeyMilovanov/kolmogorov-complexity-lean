import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LchLemma
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PropMinHereditary
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Budget
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Part02.Steps

/-!
# The hereditary family of a plain description point

This module assembles the steps of the hereditary construction into its core: for a normal
string `x` with a minimal sufficient strong set model `A`, every point `(i, j)` of the plain
description profile of the code of `A` carries a family `F` of set-codes which is a strong
model of that code and stays inside one hereditary slack (`hereditary_family_core`,
`hereditary_family_from_plain_point`).  The degenerate branches -- a point cheap enough for the
singleton family, and the regime outside the small-sufficiency condition -- are handled by
`hereditary_singleton_family` and `hereditary_fallback_budget`.  The main result is
`lemma_hereditary_strong_approximation`: every plain description point of the code of `A` lies
within one hereditary slack of a strong description point of it.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- The genuinely nontrivial branch of the hereditary construction: a plain description
point `(i, j)` of the code of a minimal sufficient strong model `A` of a normal string `x`
lies within one hereditary slack of a family `F` of set-codes containing the code of `A`,
which is a strong model of that code.  The two displayed inequalities are exactly the
hypotheses needed to invoke `lemma_lch`; the final strict inequality excludes the singleton
fallback. -/
private lemma hereditary_family_core
    (V T : Map) (hV : isOptimalConditional V) (hT : IsOptimalTotalConditional T) :
    ∃ cKappa cOut : Nat,
      ∀ x n A (hA : A.Nonempty) epsilon delta,
        x.length = n →
        IsMinimalModel V x A hA delta (logSlack cKappa n) →
        IsSufficientStatistic V x A hA epsilon →
        IsStrongSetModel T x A hA epsilon →
        IsNormalString V T x epsilon epsilon →
        ∀ i j,
        epsilon ≤ n →
        epsilon * 2 < Nat.sqrt n →
        ((i + hereditarySlack cOut delta epsilon n : Nat) : ENat) <
          plainSetComplexity V A hA →
        InPlainDescriptionProfile V (codedUniformOn A hA).code i j →
        ∃ F, ∃ hF : F.Nonempty,
          (codedUniformOn A hA).code ∈ F ∧
          IsStrongSetModel T (codedUniformOn A hA).code F hF
            (hereditarySlack cOut delta epsilon n) ∧
          plainSetComplexity V F hF ≤ (i + hereditarySlack cOut delta epsilon n : ENat) ∧
          plainSetComplexity V F hF + (finiteSetLogCard F : ENat) ≤
            ((i + j + hereditarySlack cOut delta epsilon n : Nat) : ENat) := by
  obtain ⟨cKappa, cStep, hStep⟩ := hereditary_core_lch_model V T hV hT
  obtain ⟨cFamStep, hFamStep⟩ := hereditary_core_family_from_model V T hV hT cStep
  refine ⟨cKappa, cStep + (cFamStep + cFamStep), ?_⟩
  intro x n A hA epsilon delta hn hMin hSuffA hStrong hNorm i j
    heps_le heps_sqrt h_i_lt h_prof
  -- The three budgets add up, because the hereditary slack is linear in its constant.
  have hSsum : hereditarySlack (cStep + (cFamStep + cFamStep)) delta epsilon n =
      hereditarySlack cStep delta epsilon n +
        (hereditarySlack cFamStep delta epsilon n +
          hereditarySlack cFamStep delta epsilon n) := by
    rw [hereditarySlack_add_c, hereditarySlack_add_c]
  have h_i_lt_step :
      ((i + hereditarySlack cStep delta epsilon n : Nat) : ENat) <
        plainSetComplexity V A hA := by
    refine lt_of_le_of_lt ?_ h_i_lt
    exact_mod_cast (show i + hereditarySlack cStep delta epsilon n ≤
      i + hereditarySlack (cStep + (cFamStep + cFamStep)) delta epsilon n by omega)
  -- Step one: the lifted LCH model of the profile point.
  obtain ⟨M, hM, hxM, hMstrong, hMcond, hMcomp, hMsum⟩ :=
    hStep x n A hA epsilon delta i j hn hMin hSuffA hNorm heps_le heps_sqrt
      h_i_lt_step h_prof
  have hMA : plainSetComplexity V M hM ≤ plainSetComplexity V A hA + (delta : ENat) :=
    (hMcomp.trans h_i_lt_step.le).trans (le_add_right le_rfl)
  -- Step two: the hereditary family built from that model.
  obtain ⟨F, hF, hAF, hFstrong, hFcomp, hFcard⟩ :=
    hFamStep x n A hA M hM epsilon delta hn heps_sqrt hxM hSuffA hStrong hMstrong hMA hMcond
  -- Numeric form of the two remaining complexity bounds.
  obtain ⟨fComp, hfVal⟩ := exists_plainSetComplexity_eq_coe V hV F hF
  obtain ⟨mComp, hmVal⟩ := exists_plainSetComplexity_eq_coe V hV M hM
  have hmCompNat : mComp ≤ i + hereditarySlack cStep delta epsilon n := by
    rw [hmVal] at hMcomp; exact_mod_cast hMcomp
  have hmSumNat : mComp + finiteSetLogCard M ≤
      i + j + finiteSetLogCard A + hereditarySlack cStep delta epsilon n := by
    rw [hmVal] at hMsum; exact_mod_cast hMsum
  have hfCompNat : fComp ≤ mComp + hereditarySlack cFamStep delta epsilon n := by
    rw [hfVal, hmVal] at hFcomp; exact_mod_cast hFcomp
  refine ⟨F, hF, hAF, hFstrong.mono (by omega), ?_, ?_⟩
  · rw [hfVal]
    exact_mod_cast (show fComp ≤
      i + hereditarySlack (cStep + (cFamStep + cFamStep)) delta epsilon n by omega)
  · rw [hfVal]
    exact_mod_cast (show fComp + finiteSetLogCard F ≤
      i + j + hereditarySlack (cStep + (cFamStep + cFamStep)) delta epsilon n by omega)


private lemma hereditary_min_shift_bound
    (i n delta epsilon cBound cCore : Nat)
    (S : Nat) (F : Finset BitString)
    (hInteresting : ((i + hereditarySlack cCore delta epsilon n : Nat) : ENat)
      < (n + delta + logSlack cBound n : Nat))
    (hBoundSlack : logSlack cBound n + hereditarySlack cCore delta epsilon n ≤ S) :
    min (i + S) (finiteSetLogCard F) ≤ n + delta + 2 * S := by
  -- `hInteresting` + `hABound` give `i + hereditarySlack cCore ≤ n + delta + logSlack cBound n`,
  -- and `logSlack cBound n ≤ S` (from `hBoundSlack`), so `i ≤ n + delta + S`; hence
  -- `min (i+S) (log #F) ≤ i + S ≤ n + delta + 2*S`.  (The `i+S ≤ n+delta+S` bound is
  -- FALSE in general: `i < C(A)` only up to the `O(log n)` slack `logSlack cBound n`.)
  have h1 : i + hereditarySlack cCore delta epsilon n ≤ n + delta + logSlack cBound n := by
    exact_mod_cast (le_of_lt (ENat.coe_lt_coe.mp hInteresting))
  have h2 : min (i + S) (finiteSetLogCard F) ≤ i + S := Nat.min_le_left _ _
  omega


/-- **The singleton fallback family.**  When the plain set complexity of the code of a model is
already inside the output budget, the singleton family of that code is a strong set model of it
of zero log-cardinality and meets the two complexity bounds of the hereditary conclusion. -/
private lemma hereditary_singleton_family (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cSing : Nat, ∀ (A : Finset BitString) (hA : A.Nonempty) (b i j s : Nat),
      plainSetComplexity V A hA ≤ (b : ENat) → b + cSing ≤ i + s → cSing ≤ s →
      ∃ F, ∃ hF : F.Nonempty,
        (codedUniformOn A hA).code ∈ F ∧
        IsStrongSetModel T (codedUniformOn A hA).code F hF s ∧
        plainSetComplexity V F hF ≤ ((i + s : Nat) : ENat) ∧
        plainSetComplexity V F hF + (finiteSetLogCard F : ENat) ≤ ((i + j + s : Nat) : ENat) ∧
        finiteSetLogCard F = 0 := by
  obtain ⟨cSing, hSingletonPlain⟩ := plainSetComplexity_singleton_le_plainK V hV
  obtain ⟨cSingletonStrong, hSingletonStrong⟩ := singleton_isStrongSetModel T hT
  refine ⟨cSing + cSingletonStrong, ?_⟩
  intro A hA b i j s hb hbs hs
  let y := (codedUniformOn A hA).code
  let F : Finset BitString := {y}
  let hF : F.Nonempty := Finset.singleton_nonempty y
  have hCard : finiteSetLogCard F = 0 := finiteSetLogCard_singleton y
  have hComp : plainSetComplexity V F hF ≤ ((i + s : Nat) : ENat) := by
    calc
      plainSetComplexity V F hF ≤ plainK V y + (cSing : ENat) := hSingletonPlain y
      _ = plainSetComplexity V A hA + (cSing : ENat) := rfl
      _ ≤ (b : ENat) + (cSing : ENat) := by gcongr
      _ ≤ ((i + s : Nat) : ENat) := by
          exact_mod_cast (show b + cSing ≤ i + s by omega)
  refine ⟨F, hF, by simp [F, y], (hSingletonStrong y).mono (by omega), hComp, ?_, hCard⟩
  simpa [F] using hComp.trans (by exact_mod_cast (show i + s ≤ i + j + s by omega))

/-- **The fallback budget.**  Outside the regime where the sufficiency parameter is small
against the square root of the length, the whole plain bound `n + delta + logSlack cBound n`
and one further constant already fit inside the hereditary slack. -/
private lemma hereditary_fallback_budget (n delta epsilon i cBound cSing cOut : Nat)
    (hLch : epsilon ≤ n → Nat.sqrt n ≤ epsilon * 2)
    (hc : cBound + cSing + 2 ≤ cOut) :
    n + delta + logSlack cBound n + cSing ≤ i + hereditarySlack cOut delta epsilon n := by
  have hcOne : 1 ≤ cOut := by omega
  have hcTwo : 2 ≤ cOut := by omega
  have hcBound : cBound + 2 ≤ cOut := by omega
  have hcConst : cBound + cSing ≤ cOut := by omega
  have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
  have hDeltaMul : delta ≤ cOut * delta :=
    Nat.le_mul_of_pos_left delta hcOne
  have hVariable :
      n + cBound * (Nat.bits n).length ≤
        cOut * (epsilon + (Nat.bits n).length) * Nat.sqrt n := by
    by_cases hn0 : n = 0
    · rw [hn0] at hBits ⊢
      have hBitsZero : (Nat.bits 0).length = 0 := by omega
      rw [hBitsZero]
      simp
    · have hsqrt : 1 ≤ Nat.sqrt n :=
        (Nat.sqrt_pos.2 (Nat.zero_lt_of_ne_zero hn0))
      have hBitsSqrt : (Nat.bits n).length ≤
          (Nat.bits n).length * Nat.sqrt n :=
        Nat.le_mul_of_pos_right _ hsqrt
      by_cases hEpsLe : epsilon ≤ n
      · have hSqrtLe : Nat.sqrt n ≤ 2 * epsilon :=
          by simpa [Nat.mul_comm] using hLch hEpsLe
        have hnSqrt : n ≤ Nat.sqrt n * Nat.sqrt n + 2 * Nat.sqrt n := by
          have h := Nat.lt_succ_sqrt n
          nlinarith
        have hSquare : Nat.sqrt n * Nat.sqrt n ≤
            2 * epsilon * Nat.sqrt n :=
          Nat.mul_le_mul_right (Nat.sqrt n) hSqrtLe
        have hBitsPos : 1 ≤ (Nat.bits n).length := by
          simpa [Nat.size_eq_bits_len] using
            Nat.size_pos.mpr (Nat.zero_lt_of_ne_zero hn0)
        have hSqrtBits : Nat.sqrt n ≤
            (Nat.bits n).length * Nat.sqrt n :=
          Nat.le_mul_of_pos_left _ hBitsPos
        calc
          n + cBound * (Nat.bits n).length
              ≤ (Nat.sqrt n * Nat.sqrt n + 2 * Nat.sqrt n) +
                cBound * (Nat.bits n).length :=
                  Nat.add_le_add_right hnSqrt _
          _ ≤ (2 * epsilon * Nat.sqrt n + 2 * Nat.sqrt n) +
                cBound * (Nat.bits n).length := by
                  exact Nat.add_le_add
                    (Nat.add_le_add hSquare le_rfl) le_rfl
          _ ≤ (2 * epsilon * Nat.sqrt n +
                2 * ((Nat.bits n).length * Nat.sqrt n)) +
                cBound * ((Nat.bits n).length * Nat.sqrt n) := by
                  exact Nat.add_le_add
                    (Nat.add_le_add le_rfl
                      (Nat.mul_le_mul_left 2 hSqrtBits))
                    (Nat.mul_le_mul_left cBound hBitsSqrt)
          _ = 2 * (epsilon * Nat.sqrt n) +
                (cBound + 2) * ((Nat.bits n).length * Nat.sqrt n) := by
                  ring
          _ ≤ cOut * (epsilon * Nat.sqrt n) +
                cOut * ((Nat.bits n).length * Nat.sqrt n) := by
                  exact Nat.add_le_add
                    (Nat.mul_le_mul_right _ hcTwo)
                    (Nat.mul_le_mul_right _ hcBound)
          _ = cOut * (epsilon + (Nat.bits n).length) * Nat.sqrt n := by
                ring
      · have hneps : n < epsilon := Nat.lt_of_not_ge hEpsLe
        have hEpsSqrt : epsilon ≤ epsilon * Nat.sqrt n :=
          Nat.le_mul_of_pos_right _ hsqrt
        calc
          n + cBound * (Nat.bits n).length
              ≤ epsilon + cBound * (Nat.bits n).length := by omega
          _ ≤ epsilon * Nat.sqrt n +
                cBound * ((Nat.bits n).length * Nat.sqrt n) := by
                  gcongr
          _ ≤ cOut * (epsilon * Nat.sqrt n) +
                cOut * ((Nat.bits n).length * Nat.sqrt n) := by
                  exact Nat.add_le_add
                    (Nat.le_mul_of_pos_left _ hcOne)
                    (Nat.mul_le_mul_right _ (by omega : cBound ≤ cOut))
          _ = cOut * (epsilon + (Nat.bits n).length) * Nat.sqrt n := by
                ring
  unfold hereditarySlack logSlack
  calc
    n + delta + (cBound * (Nat.bits n).length + cBound) + cSing
        = delta + (n + cBound * (Nat.bits n).length) +
            (cBound + cSing) := by ring
    _ ≤ cOut * delta +
          cOut * (epsilon + (Nat.bits n).length) * Nat.sqrt n + cOut := by
          gcongr
    _ ≤ i + (cOut * delta +
          cOut * (epsilon + (Nat.bits n).length) * Nat.sqrt n + cOut) := by
          omega

private lemma hereditary_family_from_plain_point
    (V T : Map) (hV : isOptimalConditional V) (hT : IsOptimalTotalConditional T) :
    ∃ cKappa cOut : Nat,
      ∀ x n A (hA : A.Nonempty) epsilon delta,
        x.length = n →
        IsMinimalModel V x A hA delta (logSlack cKappa n) →
        IsSufficientStatistic V x A hA epsilon →
        IsStrongSetModel T x A hA epsilon →
        IsNormalString V T x epsilon epsilon →
        ∀ i j, InPlainDescriptionProfile V (codedUniformOn A hA).code i j →
        ∃ F, ∃ hF : F.Nonempty,
          (codedUniformOn A hA).code ∈ F ∧
          IsStrongSetModel T (codedUniformOn A hA).code F hF
            (hereditarySlack cOut delta epsilon n) ∧
          plainSetComplexity V F hF ≤ (i + hereditarySlack cOut delta epsilon n : ENat) ∧
          plainSetComplexity V F hF + (finiteSetLogCard F : ENat) ≤
            ((i + j + hereditarySlack cOut delta epsilon n : Nat) : ENat) ∧
          min (i + hereditarySlack cOut delta epsilon n) (finiteSetLogCard F) ≤
            n + delta + 2 * hereditarySlack cOut delta epsilon n := by
  obtain ⟨cKappaCore, cCore, hCore⟩ := hereditary_family_core V T hV hT
  obtain ⟨cKappaBound, cBound, hBound⟩ :=
    minimalModel_plainSetComplexity_le V hV
  obtain ⟨cSing, hSing⟩ := hereditary_singleton_family V T hV hT
  let cKappa := cKappaCore + cKappaBound
  let cOut := cCore + 4 * cBound + 2 * cSing + 20
  refine ⟨cKappa, cOut, ?_⟩
  intro x n A hA epsilon delta hn hMinimal hSufficient hStrong hNormal i j hPlain
  have hMinCore :
      IsMinimalModel V x A hA delta (logSlack cKappaCore n) :=
    IsMinimalModel.mono le_rfl
      (logSlack_mono_left (by dsimp [cKappa]; omega) n) hMinimal
  have hMinBound :
      IsMinimalModel V x A hA delta (logSlack cKappaBound n) :=
    IsMinimalModel.mono le_rfl
      (logSlack_mono_left (by dsimp [cKappa]; omega) n) hMinimal
  have hABound := hBound x n A hA delta hn hMinBound
  have hCoreSlack : hereditarySlack cCore delta epsilon n ≤
      hereditarySlack cOut delta epsilon n :=
    hereditarySlack_mono_c (by dsimp [cOut]; omega)
  have hCoreSlackPlain :
      hereditarySlack cCore delta epsilon n + cSing ≤
        hereditarySlack cOut delta epsilon n := by
    unfold hereditarySlack
    dsimp [cOut]
    nlinarith [Nat.zero_le delta,
      Nat.zero_le ((epsilon + (Nat.bits n).length) * Nat.sqrt n)]
  have hSingBudget : cSing ≤ hereditarySlack cOut delta epsilon n := by
    unfold hereditarySlack
    dsimp [cOut]
    omega
  by_cases hLchConditions : epsilon ≤ n ∧ epsilon * 2 < Nat.sqrt n
  · by_cases hInteresting :
        ((i + hereditarySlack cCore delta epsilon n : Nat) : ENat) <
          plainSetComplexity V A hA
    · obtain ⟨F, hF, hMem, hStrongF, hComp, hSum⟩ :=
        hCore x n A hA epsilon delta hn hMinCore hSufficient hStrong hNormal
          i j hLchConditions.1 hLchConditions.2 hInteresting hPlain
      have hBoundSlack :
          logSlack cBound n + hereditarySlack cCore delta epsilon n
            ≤ hereditarySlack cOut delta epsilon n := by
        have hbnP : (Nat.bits n).length ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n := by
          by_cases hn0 : n = 0
          · subst hn0; simp
          · have hsq : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (Nat.zero_lt_of_ne_zero hn0)
            calc (Nat.bits n).length ≤ epsilon + (Nat.bits n).length := Nat.le_add_left _ _
              _ = (epsilon + (Nat.bits n).length) * 1 := (Nat.mul_one _).symm
              _ ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n := Nat.mul_le_mul_left _ hsq
        unfold hereditarySlack logSlack
        dsimp [cOut]
        nlinarith [Nat.zero_le delta, hbnP,
          Nat.zero_le ((epsilon + (Nat.bits n).length) * Nat.sqrt n),
          Nat.mul_le_mul_left cBound hbnP]
      have hIntTrans : ((i + hereditarySlack cCore delta epsilon n : Nat) : ENat)
          < (n + delta + logSlack cBound n : Nat) :=
        hInteresting.trans_le hABound
      refine ⟨F, hF, hMem, hStrongF.mono hCoreSlack, ?_, ?_,
        hereditary_min_shift_bound i n delta epsilon cBound cCore
          (hereditarySlack cOut delta epsilon n) F hIntTrans hBoundSlack⟩
      · exact hComp.trans (by exact_mod_cast
          (Nat.add_le_add_left hCoreSlack i))
      · exact hSum.trans (by exact_mod_cast
          (Nat.add_le_add_left hCoreSlack (i + j)))
    · push_neg at hInteresting
      obtain ⟨F, hF, hMem, hStrongF, hComp, hSum, hCard⟩ :=
        hSing A hA (i + hereditarySlack cCore delta epsilon n) i j
          (hereditarySlack cOut delta epsilon n) hInteresting (by omega) hSingBudget
      exact ⟨F, hF, hMem, hStrongF, hComp, hSum, by rw [hCard]; omega⟩
  · push_neg at hLchConditions
    obtain ⟨F, hF, hMem, hStrongF, hComp, hSum, hCard⟩ :=
      hSing A hA (n + delta + logSlack cBound n) i j
        (hereditarySlack cOut delta epsilon n) hABound
        (hereditary_fallback_budget n delta epsilon i cBound cSing cOut hLchConditions
          (by dsimp [cOut]; omega)) hSingBudget
    exact ⟨F, hF, hMem, hStrongF, hComp, hSum, by rw [hCard]; omega⟩

/-- For a normal string with a minimal sufficient strong set model `A`, every plain description
profile point of the code of `A` is within `hereditarySlack cNormal delta epsilon n` of a
strong description profile point of that code. -/
lemma lemma_hereditary_strong_approximation
    (V T : Map) (hV : isOptimalConditional V) (hT : IsOptimalTotalConditional T) :
    ∃ cKappa cNormal : Nat,
      ∀ x n A (hA : A.Nonempty) epsilon delta,
        x.length = n →
        IsStrongSetModel T x A hA epsilon →
        IsSufficientStatistic V x A hA epsilon →
        IsNormalString V T x epsilon epsilon →
        IsMinimalModel V x A hA delta (logSlack cKappa n) →
        ∀ i j, InPlainDescriptionProfile V (codedUniformOn A hA).code i j →
        ∃ i' j', InStrongDescriptionProfile V T (codedUniformOn A hA).code
            (hereditarySlack cNormal delta epsilon n) i' j' ∧
          natPairLInfDistance (i, j) (i', j') ≤ hereditarySlack cNormal delta epsilon n := by
  obtain ⟨cKappa, cOut, hFamily⟩ := hereditary_family_from_plain_point V T hV hT
  obtain ⟨cShift, hShift⟩ := inStrongDescriptionProfile_of_strong_model_params V T hV hT
  obtain ⟨cNormal, hAbsorb⟩ := hereditary_shift_slack_absorb cOut cShift
  refine ⟨cKappa, cNormal, ?_⟩
  intro x n A hA epsilon delta hn hStrong hSuff hNormal hMin i j hPlain
  obtain ⟨F, hF, hMem, hStrongF, hComp, hSum, hCard⟩ :=
    hFamily x n A hA epsilon delta hn hMin hSuff hStrong hNormal i j hPlain
  -- The strong-description shift is charged against `min (i+S) (log #F)`, and the
  -- honest hereditary bound `hCard : min (i+S) (log #F) ≤ n + delta + 2*S` lets us
  -- absorb it into a single slack via `hereditary_shift_slack_absorb`.
  have hAbsorbF := hAbsorb delta epsilon n
    (min (i + hereditarySlack cOut delta epsilon n) (finiteSetLogCard F)) hCard
  obtain ⟨i', j', hProf, hDist⟩ :=
    hShift (codedUniformOn A hA).code F hMem
      (hereditarySlack cOut delta epsilon n) (i + hereditarySlack cOut delta epsilon n) j hStrongF
      hComp (by exact_mod_cast
        (show (i + hereditarySlack cOut delta epsilon n : Nat) + j
          = i + j + hereditarySlack cOut delta epsilon n by omega) ▸ hSum)
  refine ⟨i', j', hProf.mono_epsilon hAbsorbF, ?_⟩
  unfold natPairLInfDistance at hDist ⊢
  omega

end Kolmogorov


