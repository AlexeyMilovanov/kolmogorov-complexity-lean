import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BoundaryCurve
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileEndpointBound

/-!
# Logarithmic-precision realization of a profile boundary

The Section 3 curve-realization theorem `exists_string_with_profile` produces,
for every `ProfileCurve`, a string whose *prefix* description profile follows the
curve up to `m + O(log n)`, where `m` bounds the complexity of the curve code.
Combining it with `profileBoundary_profileCurve` and the plain/prefix profile
bridges yields the Section 7 statement used by Theorem `card`: every profile
boundary is realized by a string of length `n_P` whose *plain* description
profile is within `O(KP + log n_P)` of the boundary epigraph.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Every profile boundary is realized, up to radius `O(KP + log n_P)`, by the
plain description profile of some string of length `n_P`. -/
theorem exists_string_realizing_profileBoundary
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ b : ProfileBoundary V,
      ∃ y : BitString, y.length = b.n_P ∧
        ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V y)
          (profileSet V b) (C * b.KP + logSlack C b.n_P) := by
  obtain ⟨C1, hcurve⟩ := profileBoundary_profileCurve V U hV hU
  obtain ⟨cReal, hreal⟩ := exists_string_with_profile U hU
  obtain ⟨c1, hbridge1⟩ := inDescriptionProfile_of_inPlainDescriptionProfile V U hV hU
  obtain ⟨c2, hbridge2⟩ := inPlainDescriptionProfile_of_inDescriptionProfile V U hV hU
  refine ⟨C1 + cReal + c1 + c2 + 1, ?_⟩
  intro b
  set n := b.n_P with hn
  set m := C1 * b.KP + C1 with hm
  set L := logSlack cReal n with hL
  set C := C1 + cReal + c1 + c2 + 1 with hC
  obtain ⟨curve⟩ := hcurve b
  obtain ⟨y, hylen, hupper, hlower⟩ := hreal 0 n b.k_P m b.height curve
  -- The final radius.
  set E := m + L + c2 + logSlack c1 n with hE
  have hslackC : logSlack cReal n + logSlack c1 n + logSlack (C1 + c2 + 1) n =
      logSlack C n := by
    simp only [logSlack, hC]
    ring
  have hbase : C1 + c2 ≤ logSlack (C1 + c2 + 1) n := by
    unfold logSlack
    have : 0 ≤ (C1 + c2 + 1) * (Nat.bits n).length := Nat.zero_le _
    omega
  have hEle : E ≤ C * b.KP + logSlack C n := by
    have hmul : C1 * b.KP ≤ C * b.KP := Nat.mul_le_mul_right _ (by omega)
    rw [hE, hm, hL]
    omega
  refine ⟨y, hylen, ?_, ?_⟩
  · -- Every plain profile point is close to the boundary epigraph.
    rintro ⟨i, j⟩ hq
    by_cases hin : b.height i ≤ j
    · exact ⟨(i, j), hin, by unfold natPairLInfDistance; simp⟩
    · -- `(i,j)` lies strictly below the curve, so `i` is left of `k_P ≤ n`.
      have hpos : 0 < b.height i := by omega
      have hik : i < b.k_P := by
        by_contra hcon
        have := b.height_zero_of_ge i (by omega)
        omega
      have hkn : b.k_P ≤ n := by
        have h := b.k_P_le_add_height 0
        rw [b.height_zero] at h
        simpa [hn] using h
      set i' := i + logSlack c1 i with hi'
      have hprefix : InDescriptionProfile U y i' j := hbridge1 y i j hq
      have hheight : b.height i' ≤ j + (m + L) := by
        rcases hlower i' with hno | hle
        · by_contra hcon
          exact hno (hprefix.mono_j (by omega))
        · omega
      have hlog : logSlack c1 i ≤ logSlack c1 n := logSlack_mono_right c1 (by omega)
      refine ⟨(i', max j (b.height i')),
        show b.height i' ≤ max j (b.height i') from le_max_right _ _, ?_⟩
      unfold natPairLInfDistance
      simp only
      have hmax : max j (b.height i') ≤ j + (m + L) := by
        rcases le_total j (b.height i') with h | h
        · rw [max_eq_right h]; omega
        · rw [max_eq_left h]; omega
      have hmaxge : j ≤ max j (b.height i') := le_max_left _ _
      exact max_le (by omega) (by omega)
  · -- Every boundary point is close to the plain profile.
    rintro ⟨i, j⟩ hq
    have hij : b.height i ≤ j := hq
    have hpref := hupper i
    have hplain : InPlainDescriptionProfile V y (i + m + logSlack cReal n + c2)
        (b.height i + logSlack cReal n) := hbridge2 y _ _ hpref
    have hplain' : InPlainDescriptionProfile V y (i + m + logSlack cReal n + c2)
        (max j (b.height i + logSlack cReal n)) :=
      hplain.mono_j (le_max_right _ _)
    refine ⟨(i + m + logSlack cReal n + c2, max j (b.height i + logSlack cReal n)),
      hplain', ?_⟩
    unfold natPairLInfDistance
    simp only
    have hmax : max j (b.height i + logSlack cReal n) ≤ j + logSlack cReal n := by
      rcases le_total j (b.height i + logSlack cReal n) with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    have hmaxge : j ≤ max j (b.height i + logSlack cReal n) := le_max_left _ _
    exact max_le (by omega) (by omega)

/-- The plain complexity of a string whose plain profile is `E`-close to a
boundary epigraph is within `2 * E` (plus logarithmic slack) of the boundary
endpoint `k_P`. -/
theorem plainK_close_of_profileBoundary_neighborhood
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (b : ProfileBoundary V) (y : BitString) (E ky : ℕ),
      ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V y)
        (profileSet V b) E →
      plainK V y = (ky : ENat) →
      ky ≤ b.k_P + C * (E + 1) + logSlack C b.n_P ∧
        b.k_P ≤ ky + 2 * E + C := by
  obtain ⟨cUp, hUp⟩ := plainK_upper_of_profileNeighborhood_endpoint_sharp V hV
  obtain ⟨cSingle, hSingle⟩ := plainSetComplexity_singleton_le_plainK V hV
  refine ⟨2 * cUp + 2 * cSingle + 2, ?_⟩
  intro b y E ky hnbhd hky
  have hkP : k_P (profileSet V b) = (b.k_P : ENat) := b.k_P_profileSet
  constructor
  · have hmem : y ∈ profileNeighborhood V (profileSet V b) E := hnbhd
    have h := hUp (profileSet V b) b.k_P E y hkP hmem
    rw [hky] at h
    have hcast : ky ≤ b.k_P + 2 * E + logSlack cUp (b.k_P + 2 * E) := by
      exact_mod_cast h
    -- Fold the slack at the endpoint scale into a slack at the length scale.
    have hkn : b.k_P ≤ b.n_P := by
      have hk := b.k_P_le_add_height 0
      rw [b.height_zero] at hk
      omega
    have hsplit : logSlack cUp (b.k_P + 2 * E) ≤
        logSlack cUp b.k_P + logSlack cUp (2 * E) :=
      logSlack_add_le cUp _ _
    have hmono : logSlack cUp b.k_P ≤ logSlack cUp b.n_P :=
      logSlack_mono_right cUp hkn
    have hsmall : logSlack cUp (2 * E) ≤ cUp * (2 * E) + cUp := by
      unfold logSlack
      have := length_natBits_le_self (2 * E)
      nlinarith [Nat.zero_le cUp]
    have hmono' : logSlack cUp b.n_P ≤ logSlack (2 * cUp + 2 * cSingle + 2) b.n_P :=
      logSlack_mono_left (by omega) _
    have hlin : 2 * E + (cUp * (2 * E) + cUp) ≤
        (2 * cUp + 2 * cSingle + 2) * (E + 1) := by
      nlinarith [Nat.zero_le E, Nat.zero_le cUp, Nat.zero_le cSingle]
    omega
  · -- The singleton `{y}` is a `(ky + cSingle, 0)` model of `y`.
    have hsingle : InPlainDescriptionProfile V y (ky + cSingle) 0 := by
      refine ⟨{y}, Finset.singleton_nonempty y, Finset.mem_singleton_self y, ?_, ?_⟩
      · calc plainSetComplexity V {y} (Finset.singleton_nonempty y)
            ≤ plainK V y + (cSingle : ENat) := hSingle y
          _ = ((ky + cSingle : ℕ) : ENat) := by rw [hky]; push_cast; ring
      · simp
    obtain ⟨⟨a, c⟩, hmem, hdist⟩ := hnbhd.1 (ky + cSingle, 0) hsingle
    have hheight : b.height a ≤ c := hmem
    have hsuff : b.k_P ≤ a + b.height a := b.k_P_le_add_height a
    unfold natPairLInfDistance at hdist
    simp only at hdist
    have h1 : a ≤ ky + cSingle + E := by
      have := le_of_max_le_left hdist
      omega
    have h2 : c ≤ E := by
      have := le_of_max_le_right hdist
      omega
    have hCs : cSingle ≤ 2 * cUp + 2 * cSingle + 2 := by omega
    omega

end Kolmogorov
