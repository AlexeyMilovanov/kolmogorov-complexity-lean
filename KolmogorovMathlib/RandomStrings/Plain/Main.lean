/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal
import KolmogorovMathlib.RandomStrings.Plain.Native.Referees

/-!
# One constructed machine for both native halting separations

This module assembles the proof of the main theorem of "Limit on the Computational Power of
C-Random Strings": some optimal plain decompressor has a cumulative complexity oracle (and a
plain-random oracle) that does not compute the halting language in polynomial time. It
imports the construction of the fighter decompressor (`Plain.Construction.Diagonal`, which
re-exports the effective family, its accounting and its stability) and the native counting
referees (`Plain.Native.Referees`).

The proof has three layers. First, the ingredients are fixed one after another, each by a
noncomputable choice with a specification lemma: the base optimal machines `nativeBase`
and their literal constant, the family of native referees `nativeFamily`, the extension
price data (`nativePriceData`), the tail data (`nativeTailData`), the rank and capacity
constants (`nativeFixedData`), and finally one good padding `nativePadding`. The resulting
machine is `nativeSeparatingMachine = fighterU nativeFighterParams nativePadding`, which is
conditionally optimal (`native_separating_machine_spec`). Second, for a polynomial-time
reduction of `HBin` to its oracle, the threshold-search index is chosen only now, after the
machine exists, and the referee tuple built from the reduction is a member of the family
(`native_family_contains`) that computes the cumulative count by binary search
(`native_referee_counts_of_clocked_decider`). Third, the diagonal
`constructed_oracle_defeats_polynomial_counting` shows that no such referee is correct, which
gives `native_halting_not_poly_time` for both oracle flags and the joint statement
`native_halting_oracle_separation_joint`.

This is the only module of the formalization that selects witnesses noncomputably. The base,
literal constant, native family, price and tail constants precede the common threshold;
rank and capacity constants precede padding. The module `Plain.Target` restates the results
of this module as the top-level theorems.
-/

namespace Kolmogorov.Milovanov

open RandomStrings

/-- Fixed optimal interpreter data, selected before every native construction parameter.
Blueprint node `native:main` (supporting definition). -/
noncomputable def nativeBase : Base := Classical.choice nonempty_base

/-- The base machine's literal constant, selected before constructing the native family.
Blueprint node `native:main` (supporting definition). -/
noncomputable def nativeLiteral : PlainLiteral nativeBase :=
  Classical.choice (nonempty_plainLiteral nativeBase)

/-- The certified native family; all tuple indices are present before the final machine exists.
Blueprint node `native:family` (supporting definition). -/
noncomputable def nativeFamily : RefereeFamily :=
  Classical.choose (native_referee_family nativeLiteral.cV)

/-- The selected family retains exactly the explicit native tree and bound data.
Blueprint node `native:family` (supporting lemma). -/
theorem native_family_spec :
    nativeFamily.tree = nativeRefereeTree nativeLiteral.cV ∧
      nativeFamily.bound = nativeRefereeBound :=
  Classical.choose_spec (native_referee_family nativeLiteral.cV)

/-- Repackage the joint extension-price certificate without selecting or changing any constants.
Blueprint node `native:main` (supporting lemma). Tuple fields are `C,lam,n₀,cGap`. -/
theorem native_price_data_exists (B : Base) :
    ∃ data : ℕ × ℕ × ℕ × ℕ,
      ExtensionPriceConstants B data.1 data.2.1 data.2.2.1 ∧
      ExtensionPriceSpec B (extensionPriceAlgorithm B data.2.1 data.2.2.1)
        data.2.2.2 data.2.2.1 := by
  obtain ⟨C, lam, n₀, cGap, A, hc, ha, _, hs⟩ := extension_price_sound_complete B
  subst A
  exact ⟨(C, lam, n₀, cGap), hc, hs⟩

/-- Price data `(C,lam,n₀,cGap)` from the explicit extension-price existential certificate.
Blueprint node `native:main` (supporting definition). -/
noncomputable def nativePriceData : ℕ × ℕ × ℕ × ℕ :=
  Classical.choose (native_price_data_exists nativeBase)

/-- The chosen price data certify the exact frozen algorithm at its original threshold.
Blueprint node `native:main` (supporting lemma). -/
theorem native_price_data_spec :
    ExtensionPriceConstants nativeBase nativePriceData.1 nativePriceData.2.1
      nativePriceData.2.2.1 ∧
    ExtensionPriceSpec nativeBase
      (extensionPriceAlgorithm nativeBase nativePriceData.2.1 nativePriceData.2.2.1)
      nativePriceData.2.2.2 nativePriceData.2.2.1 :=
  Classical.choose_spec (native_price_data_exists nativeBase)

/-- Tail data `(c₁,n₀)` selected from the frozen exponential-tail theorem.
Blueprint node `native:main` (supporting definition). -/
noncomputable def nativeTailData : ℕ × ℕ :=
  ⟨Classical.choose (exponential_tail_budget nativeBase),
    Classical.choose (Classical.choose_spec (exponential_tail_budget nativeBase))⟩

/-- The selected tail coefficient is positive and its threshold includes all numerical bounds.
Blueprint node `native:main` (supporting lemma). -/
theorem native_tail_data_spec :
    1 ≤ nativeTailData.1 ∧ 32 ≤ nativeTailData.2 ∧
      ∀ n ≥ nativeTailData.2,
        rest nativeBase n (2 ^ n) ≤ nativeTailData.1 * 2 ^ (2 ^ n - n) :=
  Classical.choose_spec (Classical.choose_spec (exponential_tail_budget nativeBase))

/-- All padding-independent fighter parameters, with the maximum price/tail threshold.
Blueprint node `native:main` (supporting definition). Constants precede the search index. -/
noncomputable def nativeFighterParams : FighterParams where
  B := nativeBase
  literal := nativeLiteral
  family := nativeFamily
  lam := nativePriceData.2.1
  n₀ := max nativePriceData.2.2.1 nativeTailData.2
  c₁ := nativeTailData.1
  threshold := native_tail_data_spec.2.1.trans (le_max_right _ _)
  tail_positive := native_tail_data_spec.1
  tail_bound := fun n hn =>
    native_tail_data_spec.2.2 n ((le_max_right _ _).trans hn)

/-- Enlarging the threshold gives the fighter the exact price hypotheses of the construction.
Blueprint node `native:main` (supporting lemma). -/
theorem native_fighter_price_hypotheses :
    FighterPriceHypotheses nativeFighterParams nativePriceData.1 nativePriceData.2.2.2 := by
  have h := fighter_price_hypotheses_mono nativeBase nativePriceData.1 nativePriceData.2.1
    nativePriceData.2.2.2 nativePriceData.2.2.1 nativeFighterParams.n₀
    (le_max_left _ _) native_price_data_spec.1 native_price_data_spec.2
  exact ⟨h.2, h.1⟩

/-- The rank constant and capacity threshold, chosen before padding.
Blueprint node `native:main` (supporting definition). -/
noncomputable def nativeFixedData : ℕ × ℕ :=
  ⟨Classical.choose (fighter_fixed_constants_exist nativeFighterParams
      nativePriceData.1 nativePriceData.2.2.2 native_fighter_price_hypotheses),
    Classical.choose (Classical.choose_spec (fighter_fixed_constants_exist nativeFighterParams
      nativePriceData.1 nativePriceData.2.2.2 native_fighter_price_hypotheses))⟩

/-- The fixed constants share the same fighter parameters and price-gap constant.
Blueprint node `native:main` (supporting lemma). -/
theorem native_fixed_data_spec :
    FighterFixedConstants nativeFighterParams nativePriceData.1 nativePriceData.2.2.2
      nativeFixedData.1 nativeFixedData.2 :=
  Classical.choose_spec (Classical.choose_spec (fighter_fixed_constants_exist nativeFighterParams
    nativePriceData.1 nativePriceData.2.2.2 native_fighter_price_hypotheses))

/-- One positive even padding satisfying the five good-padding requirements.
Blueprint node `native:main` (supporting definition). -/
noncomputable def nativePadding : ℕ :=
  Classical.choose (fighter_good_padding_exists nativeFighterParams nativePriceData.1
    nativePriceData.2.2.2 nativeFixedData.1 nativeFixedData.2 native_fixed_data_spec)

/-- The selected padding is good and the guarded allocation never fails at any tick.
Blueprint node `native:main` (supporting lemma). -/
theorem native_padding_spec :
    GoodPadding nativeFighterParams nativeFixedData.2 nativeFixedData.1
      nativePriceData.2.2.2 nativePadding ∧
    ∀ tick, (fighterState nativeFighterParams nativePadding tick).failed = false :=
  Classical.choose_spec (fighter_good_padding_exists nativeFighterParams nativePriceData.1
    nativePriceData.2.2.2 nativeFixedData.1 nativeFixedData.2 native_fixed_data_spec)

/-- The single conditional plain decompressor witnessing both native oracle separations.
Blueprint node `native:main` (supporting definition). This is the fighter machine. -/
noncomputable def nativeSeparatingMachine : Map := fighterU nativeFighterParams nativePadding

/-- The named machine is conditionally optimal and has the normalization's exact literal bound.
Blueprint node `native:main` (supporting lemma). Optimality includes partial computability. -/
theorem native_separating_machine_spec :
    isOptimalConditional nativeSeparatingMachine ∧
      ∀ x, plainK nativeSeparatingMachine x ≤ (x.length + (nativePadding + nativeLiteral.cV) : ℕ) :=
  ⟨fighter_machine_optimal_conditional nativeFighterParams nativePadding
      native_padding_spec.1.positive,
    constructed_machine_literal_bound nativeBase nativeLiteral nativePadding
      native_padding_spec.1.positive (fighterG nativeFighterParams nativePadding)⟩

/-- Every tuple belongs to the selected family's positive-index tree-and-bound interface.
Blueprint node `native:family` (supporting lemma). -/
theorem native_family_contains (θ : NativeTuple) (d : ℕ) :
    nativeFighterParams.family.Contains d (native_counting_referee nativeLiteral.cV θ d)
      (nativeTupleBound θ) := by
  obtain ⟨l, _, hl, htuple⟩ := native_tuple_occurs_above θ 0
  refine ⟨l, hl, ?_, ?_⟩
  · change nativeFamily.tree d l = _
    rw [native_family_spec.1]
    funext m
    change native_counting_referee nativeLiteral.cV (nativeTupleAt l) d m = _
    rw [htuple]
  · change nativeFamily.bound l = _
    rw [native_family_spec.2]
    funext m
    change nativeTupleBound (nativeTupleAt l) m = _
    rw [htuple]

/-- For either flag, native clocked correctness contradicts the counting diagonal for this machine.
Blueprint node `native:main` (supporting lemma). The search index is chosen only after `U`. -/
theorem native_halting_not_poly_time (flag : NativeOracleFlag) :
    HBin ∉ PolyTimeOracle (nativeOracle flag nativeSeparatingMachine) := by
  intro hpoly
  obtain ⟨c, e, hdecider⟩ := exists_clocked_of_polyTime _ _ hpoly
  obtain ⟨e₀, hsearch⟩ :=
    exists_threshold_search_index nativeSeparatingMachine native_separating_machine_spec.1.1
  let θ : NativeTuple := (c, e, e₀, flag)
  have hcorrect := native_referee_counts_of_clocked_decider nativeSeparatingMachine
    native_separating_machine_spec.1 nativeLiteral.cV nativePadding
    native_separating_machine_spec.2 θ hsearch hdecider
  obtain ⟨m, hwrong⟩ := constructed_oracle_defeats_polynomial_counting nativeFighterParams
    nativePriceData.1 nativePriceData.2.2.2 nativeFixedData.1 nativeFixedData.2 nativePadding
    native_fixed_data_spec native_padding_spec.1
    (native_counting_referee nativeLiteral.cV θ nativePadding) (nativeTupleBound θ)
    (native_family_contains θ nativePadding)
  exact hwrong (hcorrect m)

/-- The specific native-family fighter separates binary halting from its cumulative oracle class.
Blueprint node `native:main`. -/
theorem native_halting_not_poly_time_cumulative :
    HBin ∉ PolyTimeOracle (CumulativeOracle encF nativeSeparatingMachine) :=
  native_halting_not_poly_time .cumulative

/-- The same native-family fighter separates binary halting from its plain-random oracle class.
Blueprint node `native:random`. -/
theorem native_halting_not_poly_time_random :
    HBin ∉ PolyTimeOracle (PlainRandomOracle nativeSeparatingMachine) :=
  native_halting_not_poly_time .random

/-- One optimal conditional plain machine witnesses both native oracle-class separations.
Blueprint node `native:joint`. This has exactly the frozen `Target` joint theorem's statement. -/
theorem native_halting_oracle_separation_joint :
    ∃ U : Map, isOptimalConditional U ∧
      HBin ∉ RandomStrings.PolyTimeOracle (CumulativeOracle encF U) ∧
      HBin ∉ RandomStrings.PolyTimeOracle (PlainRandomOracle U) := by
  exact ⟨nativeSeparatingMachine, native_separating_machine_spec.1,
    native_halting_not_poly_time_cumulative, native_halting_not_poly_time_random⟩

end Kolmogorov.Milovanov
