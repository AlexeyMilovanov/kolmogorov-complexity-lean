import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.CommonInformation.ConditionalIndependence
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.ConditionalComplexity.Continuity
import KolmogorovMathlib.Complexity.KolmogorovLevin.Refinements

/-!
# The logarithmic term of Kolmogorov–Levin is unavoidable

`exists_plainK_pair_ge_add_log` and `exists_plainK_pair_le_sub_log` (SUV Exercise 37): there
are pairs with `C(x, y) ≥ C(x) + C(y | x) + log n - O(1)` and pairs with
`C(x, y) ≤ C(x) + C(y | x) - log n + O(1)`, so the `O(log n)` error term in the
Kolmogorov–Levin theorem cannot be removed in either direction.

The upper direction is a counting argument over `pairsFinset` and `pairCodesFinset`, whose
common cardinality `(n + 1) * 2 ^ n` is computed here; the lower direction uses the coding
`pairCodeWithLengthBits`, which prefixes a string by its own binary length, and the bit
surgery `flipBitAt`.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution

/-- Construct the set of pairs `(x, y)` with `x.length = k` and `y.length = n - k`
as `k` ranges from `0` to `n`. -/
def pairsFinset (n : ℕ) : Finset (BitString × BitString) :=
  (Finset.range (n + 1)).biUnion (fun k =>
    (stringsOfLength k) ×ˢ (stringsOfLength (n - k)))

/-- The image under `pairCode` of all pairs in `pairsFinset n`. -/
def pairCodesFinset (n : ℕ) : Finset BitString :=
  (pairsFinset n).image (fun p => pairCode p.1 p.2)

/-- There are `(n + 1) * 2 ^ n` pairs of strings whose lengths add up to `n`. -/
lemma card_pairsFinset (n : ℕ) : (pairsFinset n).card = (n + 1) * 2 ^ n := by
  dsimp [pairsFinset]
  rw [Finset.card_biUnion]
  · have h_sum : ∀ k ∈ Finset.range (n + 1),
        (stringsOfLength k ×ˢ stringsOfLength (n - k)).card = 2 ^ n := by
      intro k hk
      rw [Finset.card_product, card_stringsOfLength, card_stringsOfLength]
      have h_k_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl h_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
  · intro k1 hk1 k2 hk2 h_ne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_product, mem_stringsOfLength, mem_stringsOfLength] at hp1 hp2
    have h1 := hp1.1
    have h2 := hp2.1
    omega

/-- Coding is injective on pairs, so there are `(n + 1) * 2 ^ n` codes of pairs of total
length `n`. -/
lemma card_pairCodesFinset (n : ℕ) : (pairCodesFinset n).card = (n + 1) * 2 ^ n := by
  dsimp [pairCodesFinset]
  rw [Finset.card_image_of_injective _ (fun p1 p2 h => pairCode_injective h)]
  exact card_pairsFinset n

/-- **Exercise 37, upper direction.** The `O(log n)` term in the Kolmogorov–Levin
theorem is unavoidable: pairs with `C(x, y) ≥ C(x) + C(y | x) + log n - O(1)`. -/
theorem exists_plainK_pair_ge_add_log (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ x y : BitString, x.length ≤ n ∧ y.length ≤ n ∧
      plainK U x + condK U y x + ((Nat.log 2 n : ℕ) : ℕ∞) ≤ cPair U x y + (c : ℕ∞) := by
  obtain ⟨c1, h1⟩ := plainK_le_length U hU
  obtain ⟨c2', h2'⟩ := condK_le_plainK U hU
  set c2 := c2' + c1
  have h2 : ∀ y x, condK U y x ≤ (y.length : ℕ∞) + (c2 : ℕ∞) := fun y x => by
    have hc2 : c1 + c2' = c2 := by omega
    calc condK U y x ≤ plainK U y + (c2' : ℕ∞) := h2' y x
      _ ≤ (y.length : ℕ∞) + (c1 : ℕ∞) + (c2' : ℕ∞) := by gcongr; exact h1 y
      _ = (y.length : ℕ∞) + ((c1 + c2' : ℕ) : ℕ∞) := by push_cast; ring
      _ = (y.length : ℕ∞) + (c2 : ℕ∞) := by rw [hc2]
  have h_nil1 : plainK U [] ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) (h1 [])
  have h_nil2 : condK U [] [] ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) (h2 [] [])
  set c0 := (plainK U [] + condK U [] []).toNat
  refine ⟨c1 + c2 + c0, fun n => ?_⟩
  cases n with
  | zero =>
    refine ⟨[], [], rfl.le, rfl.le, ?_⟩
    have hlog0 : Nat.log 2 0 = 0 := rfl
    have h_c0 : plainK U [] + condK U [] [] = (c0 : ℕ∞) := by
      rw [ENat.natCast_toNat]
      exact WithTop.add_ne_top.mpr ⟨h_nil1, h_nil2⟩
    have h_le0 : plainK U [] + condK U [] [] + ((Nat.log 2 0 : ℕ) : ℕ∞) = (c0 : ℕ∞) := by
      rw [hlog0]; simp [h_c0]
    rw [h_le0]
    calc (c0 : ℕ∞)
        ≤ ((c1 + c2 + c0 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_add_left c0 (c1 + c2)
      _ ≤ cPair U [] [] + ((c1 + c2 + c0 : ℕ) : ℕ∞) := le_add_self
  | succ m =>
    set L := Nat.log 2 (m + 1)
    set S := pairCodesFinset (m + 1)
    set W := generatedWords U [] (m + 1 + L - 1)
    have hW_card : W.card ≤ 2 ^ (m + 1 + L) - 1 := by
      dsimp [W]
      have h1 := card_generatedWordsLe U [] (m + 1 + L - 1)
      have h2 := length_programsLe_add_one (m + 1 + L - 1)
      have h3 : m + 1 + L - 1 + 1 = m + 1 + L := Nat.sub_add_cancel (by omega)
      rw [h3] at h2
      have h_pow_pos : 0 < 2 ^ (m + 1 + L) := Nat.two_pow_pos _
      omega
    have hL_pow : 2 ^ L ≤ m + 1 := Nat.pow_log_le_self 2 (by omega)
    have h_pow_lt : 2 ^ (m + 1 + L) - 1 < (m + 2) * 2 ^ (m + 1) := by
      have h1 : 2 ^ (m + 1 + L) = 2 ^ (m + 1) * 2 ^ L := by rw [← pow_add]
      have h2 : 2 ^ (m + 1) * 2 ^ L ≤ 2 ^ (m + 1) * (m + 1) := Nat.mul_le_mul_left _ hL_pow
      have h3 : 2 ^ (m + 1) * (m + 1) < 2 ^ (m + 1) * (m + 2) :=
        Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self (m + 1)) (Nat.two_pow_pos (m + 1))
      have h4 : 2 ^ (m + 1) * (m + 2) = (m + 2) * 2 ^ (m + 1) := by ring
      omega
    have hS_card : S.card = (m + 2) * 2 ^ (m + 1) := card_pairCodesFinset (m + 1)
    have h_not_sub : ¬ S ⊆ W := fun hsub => by
      have h_le := Finset.card_le_card hsub
      rw [hS_card] at h_le
      omega
    rw [Finset.not_subset] at h_not_sub
    rcases h_not_sub with ⟨z, hzS, hzW⟩
    dsimp [S, pairCodesFinset, pairsFinset] at hzS
    rw [Finset.mem_image] at hzS
    rcases hzS with ⟨p, hp, rfl⟩
    rw [Finset.mem_biUnion] at hp
    rcases hp with ⟨k, hk, hp⟩
    rw [Finset.mem_product, mem_stringsOfLength, mem_stringsOfLength] at hp
    rcases hp with ⟨hx, hy⟩
    have hk_le : k ≤ m + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    refine ⟨p.1, p.2, by omega, by omega, ?_⟩
    have hz_bound : (m + 1 + L : ℕ∞) ≤ plainK U (pairCode p.1 p.2) := by
      by_contra h_lt
      simp only [not_le] at h_lt
      have hz_top : plainK U (pairCode p.1 p.2) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENat.natCast_ne_top _) (h1 (pairCode p.1 p.2))
      obtain ⟨val, hval⟩ : ∃ v : ℕ, plainK U (pairCode p.1 p.2) = (v : ℕ∞) :=
        ⟨(plainK U (pairCode p.1 p.2)).toNat,
         (ENat.natCast_toNat hz_top).symm⟩
      have h_le_m : plainK U (pairCode p.1 p.2) ≤ (m + 1 + L - 1 : ℕ∞) := by
        rw [hval] at h_lt ⊢
        exact_mod_cast Nat.le_pred_of_lt (ENat.natCast_lt_natCast.mp h_lt)
      have h_in_W : pairCode p.1 p.2 ∈ W := by
        dsimp [W, generatedWords]
        obtain ⟨p_code, hp_prod⟩ := (condK_le_iff U (pairCode p.1 p.2) [] (m + 1 + L - 1)).mp h_le_m
        rw [List.mem_toFinset, List.mem_filterMap]
        exact ⟨p_code, mem_programsLe (m + 1 + L - 1) p_code hp_prod.1,
               progToOut_eq_some.mpr hp_prod.2⟩
      exact hzW h_in_W
    have hx_k : plainK U p.1 ≤ (k : ℕ∞) + (c1 : ℕ∞) := by
      have h1p := h1 p.1; change _ ≤ (p.1.length : ℕ∞) + (c1 : ℕ∞) at h1p
      rw [hx] at h1p; exact h1p
    have hy_k : condK U p.2 p.1 ≤ (m + 1 - k : ℕ∞) + (c2 : ℕ∞) := by
      have h2p := h2 p.2 p.1; change _ ≤ (p.2.length : ℕ∞) + (c2 : ℕ∞) at h2p
      rw [hy] at h2p; exact h2p
    dsimp [cPair]
    calc plainK U p.1 + condK U p.2 p.1 + (L : ℕ∞)
        ≤ (k : ℕ∞) + (c1 : ℕ∞) + ((m + 1 - k : ℕ∞) + (c2 : ℕ∞)) + (L : ℕ∞) := by gcongr
      _ = ((k + c1 + (m + 1 - k + c2) + L : ℕ) : ℕ∞) := by push_cast; rfl
      _ = ((m + 1 + L + c1 + c2 : ℕ) : ℕ∞) := by congr 1; omega
      _ = (m + 1 + L : ℕ∞) + ((c1 + c2 : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ plainK U (pairCode p.1 p.2) + ((c1 + c2 : ℕ) : ℕ∞) := by gcongr
      _ ≤ plainK U (pairCode p.1 p.2) + ((c1 + c2 + c0 : ℕ) : ℕ∞) := by
            have hc0_le : ((c1 + c2 : ℕ) : ℕ∞) ≤ ((c1 + c2 + c0 : ℕ) : ℕ∞) := by
              exact_mod_cast Nat.le_add_right (c1 + c2) c0
            rw [add_comm (plainK U (pairCode p.1 p.2)), add_comm (plainK U (pairCode p.1 p.2))]
            exact add_le_add_left hc0_le _

/-- The code of the pair consisting of the binary length of `y` and `y` itself. -/
def pairCodeWithLengthBits (y : BitString) : BitString :=
  pairCode (Nat.bits y.length) y

/-- Prefixing a string by its own binary length is computable. -/
lemma pairCodeWithLengthBits_computable : Computable pairCodeWithLengthBits := by
  have h : pairCodeWithLengthBits = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
    (fun y : BitString => (Nat.bits y.length, y)) := by
    funext y; rfl
  rw [h]
  have hlen : Computable (fun y : BitString => Nat.bits y.length) :=
    natBits_computable.comp Computable.list_length
  exact pairCode_computable.comp (hlen.pair Computable.id)

/-- **Exercise 37, lower direction.** Pairs with
`C(x, y) ≤ C(x) + C(y | x) - log n + O(1)`. -/
theorem exists_plainK_pair_le_sub_log (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ x y : BitString, x.length ≤ n ∧ y.length ≤ n ∧
      cPair U x y + ((Nat.log 2 n : ℕ) : ℕ∞) ≤ plainK U x + condK U y x + (c : ℕ∞) := by
  obtain ⟨cg, hg⟩ := plainK_map_le U hU pairCodeWithLengthBits pairCodeWithLengthBits_computable
  obtain ⟨clen, hlen⟩ := plainK_le_length U hU
  have h_pair_ne_top : cPair U [] [] ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hlen (pairCode (Nat.bits 0) []))
  set c0 := (cPair U [] []).toNat
  refine ⟨cg + clen + c0, fun n => ?_⟩
  cases n with
  | zero =>
    refine ⟨[], [], rfl.le, rfl.le, ?_⟩
    have hlog0 : Nat.log 2 0 = 0 := rfl
    have hc0 : cPair U [] [] = (c0 : ℕ∞) := by
      rw [ENat.natCast_toNat h_pair_ne_top]
    have h_lhs : cPair U [] [] + ((Nat.log 2 0 : ℕ) : ℕ∞) = (c0 : ℕ∞) := by
      rw [hlog0]; simp [hc0]
    rw [h_lhs]
    calc (c0 : ℕ∞)
        ≤ ((cg + clen + c0 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_add_left c0 (cg + clen)
      _ ≤ plainK U [] + condK U [] [] + ((cg + clen + c0 : ℕ) : ℕ∞) := le_add_self
  | succ m =>
    cases m with
    | zero =>
      refine ⟨[], [], by simp, by simp, ?_⟩
      have hlog1 : Nat.log 2 1 = 0 := rfl
      have hc0 : cPair U [] [] = (c0 : ℕ∞) := by
        rw [ENat.natCast_toNat h_pair_ne_top]
      have h_lhs : cPair U [] [] + ((Nat.log 2 1 : ℕ) : ℕ∞) = (c0 : ℕ∞) := by
        rw [hlog1]; simp [hc0]
      rw [h_lhs]
      calc (c0 : ℕ∞)
          ≤ ((cg + clen + c0 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_add_left c0 (cg + clen)
        _ ≤ plainK U [] + condK U [] [] + ((cg + clen + c0 : ℕ) : ℕ∞) := le_add_self
    | succ m' =>
      set L := Nat.log 2 (m' + 2)
      have hL_pos : 1 ≤ L := by
        dsimp [L]
        have h_log2 : Nat.log 2 2 = 1 := rfl
        rw [← h_log2]
        have h2_le : 2 ≤ m' + 2 := by omega
        exact Nat.log_mono_right h2_le
      set A := (Finset.range (m' + 2)).image (fun i => Nat.bits (i + 1))
      have hA_card : A.card = m' + 2 := by
        dsimp [A]
        rw [Finset.card_image_of_injective]
        · exact Finset.card_range (m' + 2)
        · intro i1 i2 h
          have h_eq := natBits_injective h
          omega
      set W1 := generatedWords U [] (L - 1)
      have hW1_card : W1.card ≤ m' + 1 := by
        dsimp [W1]
        have h1 := card_generatedWordsLe U [] (L - 1)
        have h2 := length_programsLe_add_one (L - 1)
        have h_sub : L - 1 + 1 = L := Nat.sub_add_cancel hL_pos
        rw [h_sub] at h2
        have hL_pow : 2 ^ L ≤ m' + 2 := Nat.pow_log_le_self 2 (by omega)
        omega
      have h_not_sub1 : ¬ A ⊆ W1 := fun hsub => by
        have hle := Finset.card_le_card hsub
        rw [hA_card] at hle
        omega
      rw [Finset.not_subset] at h_not_sub1
      rcases h_not_sub1 with ⟨x, hxA, hxW1⟩
      rw [Finset.mem_image] at hxA
      rcases hxA with ⟨i, hi, rfl⟩
      set k := i + 1
      have hk_pos : 1 ≤ k := by omega
      have hk_le : k ≤ m' + 2 := by
        have hi_lt := Finset.mem_range.mp hi
        omega
      have hx_bound : (L : ℕ∞) ≤ plainK U (Nat.bits k) := by
        by_contra h_lt
        simp only [not_le] at h_lt
        have hx_top : plainK U (Nat.bits k) ≠ ⊤ :=
          ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hlen (Nat.bits k))
        obtain ⟨val, hval⟩ : ∃ v : ℕ, plainK U (Nat.bits k) = (v : ℕ∞) :=
          ⟨(plainK U (Nat.bits k)).toNat, (ENat.natCast_toNat hx_top).symm⟩
        have h_le_m : plainK U (Nat.bits k) ≤ (L - 1 : ℕ∞) := by
          rw [hval] at h_lt ⊢
          exact_mod_cast Nat.le_pred_of_lt (ENat.natCast_lt_natCast.mp h_lt)
        have h_in_W : Nat.bits k ∈ W1 := by
          dsimp [W1, generatedWords]
          obtain ⟨p_code, hp_prod⟩ := (condK_le_iff U (Nat.bits k) [] (L - 1)).mp h_le_m
          rw [List.mem_toFinset, List.mem_filterMap]
          exact ⟨p_code, mem_programsLe (L - 1) p_code hp_prod.1, progToOut_eq_some.mpr hp_prod.2⟩
        exact hxW1 h_in_W
      set B := stringsOfLength k
      have hB_card : B.card = 2 ^ k := card_stringsOfLength k
      set W2 := generatedWords U (Nat.bits k) (k - 1)
      have hW2_card : W2.card ≤ 2 ^ k - 1 := by
        dsimp [W2]
        have h1 := card_generatedWordsLe U (Nat.bits k) (k - 1)
        have h2 := length_programsLe_add_one (k - 1)
        rw [Nat.sub_add_cancel hk_pos] at h2
        omega
      have h_not_sub2 : ¬ B ⊆ W2 := fun hsub => by
        have hle := Finset.card_le_card hsub
        rw [hB_card] at hle
        have h_pow_pos : 0 < 2 ^ k := Nat.two_pow_pos _
        omega
      rw [Finset.not_subset] at h_not_sub2
      rcases h_not_sub2 with ⟨y, hyB, hyW2⟩
      rw [mem_stringsOfLength] at hyB
      refine ⟨Nat.bits k, y, (length_natBits_le k).trans hk_le, by omega, ?_⟩
      have hy_bound : (k : ℕ∞) ≤ condK U y (Nat.bits k) := by
        by_contra h_lt
        simp only [not_le] at h_lt
        obtain ⟨c2', h2'⟩ := condK_le_plainK U hU
        have hy_top : condK U y (Nat.bits k) ≠ ⊤ :=
          ne_top_of_le_ne_top (ENat.natCast_ne_top _) (h2' y (Nat.bits k) |>.trans
            (add_le_add_left (hlen y) (c2' : ℕ∞)))
        obtain ⟨val, hval⟩ : ∃ v : ℕ, condK U y (Nat.bits k) = (v : ℕ∞) :=
          ⟨(condK U y (Nat.bits k)).toNat, (ENat.natCast_toNat hy_top).symm⟩
        have h_le_m : condK U y (Nat.bits k) ≤ (k - 1 : ℕ∞) := by
          rw [hval] at h_lt ⊢
          exact_mod_cast Nat.le_pred_of_lt (ENat.natCast_lt_natCast.mp h_lt)
        have h_in_W : y ∈ W2 := by
          dsimp [W2, generatedWords]
          obtain ⟨p_code, hp_prod⟩ := (condK_le_iff U y (Nat.bits k) (k - 1)).mp h_le_m
          rw [List.mem_toFinset, List.mem_filterMap]
          exact ⟨p_code, mem_programsLe (k - 1) p_code hp_prod.1, progToOut_eq_some.mpr hp_prod.2⟩
        exact hyW2 h_in_W
      have h_pair_code : pairCode (Nat.bits k) y = pairCodeWithLengthBits y := by
        dsimp [pairCodeWithLengthBits]
        rw [hyB]
      dsimp [cPair]
      rw [h_pair_code]
      calc plainK U (pairCodeWithLengthBits y) + (L : ℕ∞)
          ≤ plainK U y + (cg : ℕ∞) + (L : ℕ∞) := by gcongr; exact hg y
        _ ≤ (y.length : ℕ∞) + (clen : ℕ∞) + (cg : ℕ∞) + (L : ℕ∞) := by gcongr; exact hlen y
        _ = (k : ℕ∞) + (L : ℕ∞) + ((cg + clen : ℕ) : ℕ∞) := by
              push_cast [hyB]; ring
        _ ≤ condK U y (Nat.bits k) + plainK U (Nat.bits k) + ((cg + clen : ℕ) : ℕ∞) := by
              have h_sum : (k : ℕ∞) + (L : ℕ∞) ≤ condK U y (Nat.bits k) + plainK U (Nat.bits k) :=
                add_le_add hy_bound hx_bound
              exact add_le_add_left h_sum ((cg + clen : ℕ) : ℕ∞)
        _ = plainK U (Nat.bits k) + condK U y (Nat.bits k) + ((cg + clen : ℕ) : ℕ∞) := by
              push_cast; ring
        _ ≤ plainK U (Nat.bits k) + condK U y (Nat.bits k) + ((cg + clen + c0 : ℕ) : ℕ∞) := by
              have hc0_le : ((cg + clen : ℕ) : ℕ∞) ≤ ((cg + clen + c0 : ℕ) : ℕ∞) := by
                exact_mod_cast Nat.le_add_right (cg + clen) c0
              exact add_le_add_right hc0_le (plainK U (Nat.bits k) + condK U y (Nat.bits k))

/-- Flip bit `i` of `x`, leaving the other positions unchanged. -/
def flipBitAt (x : BitString) (i : ℕ) : BitString :=
  x.take i ++ [!x.getD i false] ++ x.drop (i + 1)

/-- Flipping the `i`-th bit of `x`, for `i` below the length of `x`, is the update of `x` at `i`
by the negated bit. -/
theorem flipBitAt_eq_set {x : BitString} {i : ℕ} (hi : i < x.length) :
    flipBitAt x i = x.set i (!x.getD i false) := by
  unfold flipBitAt
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hi]
  simp

/-- Flipping the bit at a given position is primitive recursive in the string and the position. -/
theorem flipBitAt_primrec : Primrec₂ flipBitAt := by
  have h_b : Primrec (fun (p : BitString × ℕ) => !p.1.getD p.2 false) :=
    Primrec.not.comp ((Primrec.list_getD false).comp Primrec.fst Primrec.snd)
  have h_take_b : Primrec (fun (p : BitString × ℕ) => p.1.take p.2 ++ [!p.1.getD p.2 false]) :=
    Primrec.list_append.comp
      (Primrec.list_take.comp Primrec.snd Primrec.fst)
      (Primrec.list_cons.comp h_b (Primrec.const []))
  have h_drop : Primrec (fun (p : BitString × ℕ) => p.1.drop (p.2 + 1)) :=
    Primrec.list_drop.comp (Primrec.succ.comp Primrec.snd) Primrec.fst
  have h : Primrec (fun (p : BitString × ℕ) => flipBitAt p.1 p.2) :=
    Primrec.list_append.comp h_take_b h_drop
  exact h.to₂

/-- The decompressor that reads a program `q` as a pair (index width, payload), runs `U` on the
tail of the payload, and flips the bit of the output at the position coded by the head. -/
noncomputable def oneBitFlipDecompressor (U : Map) : Map := fun (q, y) =>
  (U ((decodeSecond q).drop (bitsToNat (decodeFirst q)), y)).map (fun x =>
    let i := bitsToNat ((decodeSecond q).take (bitsToNat (decodeFirst q)))
    flipBitAt x i)

/-- The decompressor that runs `U` and then flips one bit of the output is a decompressor. -/
theorem oneBitFlipDecompressor_isDecompressor {U : Map} (hU : isDecompressor U) :
    isDecompressor (oneBitFlipDecompressor U) := by
  have hf_input : Computable (fun (p : BitString × BitString) =>
      ((decodeSecond p.1).drop (bitsToNat (decodeFirst p.1)), p.2)) := by
    have h_drop : Computable (fun (p : BitString × BitString) =>
        (decodeSecond p.1).drop (bitsToNat (decodeFirst p.1))) :=
      (Primrec.list_drop.comp
        (bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst))
        (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst)).to_comp
    exact h_drop.pair Computable.snd
  have hU_f : Partrec (fun (p : BitString × BitString) =>
      U (((decodeSecond p.1).drop (bitsToNat (decodeFirst p.1)), p.2))) :=
    Partrec.comp hU hf_input
  have hg : Computable (fun (p : (BitString × BitString) × BitString) =>
      let i := bitsToNat ((decodeSecond p.1.1).take (bitsToNat (decodeFirst p.1.1)))
      flipBitAt p.2 i) := by
    have h_i : Computable (fun (p : (BitString × BitString) × BitString) =>
        bitsToNat ((decodeSecond p.1.1).take (bitsToNat (decodeFirst p.1.1)))) :=
      (bitsToNat_primrec.comp
        (Primrec.list_take.comp
          (bitsToNat_primrec.comp
            (CodedFiniteDistribution.decodeFirst_primrec.comp
              (Primrec.fst.comp Primrec.fst)))
          (CodedFiniteDistribution.decodeSecond_primrec.comp
            (Primrec.fst.comp Primrec.fst)))).to_comp
    exact flipBitAt_primrec.to_comp.comp Computable.snd h_i
  exact Partrec.map hU_f hg

/-- From a program `p` for `x` and a position `i`, the program carrying `i` self-delimitingly
in front of `p` produces the string `x` with its `i`-th bit flipped. -/
theorem oneBitFlipDecompressor_produces {U : Map} {x y p : BitString} {i : ℕ}
    (hp : produces U p y x) (hi : i < x.length) :
    produces (oneBitFlipDecompressor U)
      (pairCode (Nat.bits (Nat.bits i).length) (Nat.bits i ++ p)) y
      (x.set i (!x.getD i false)) := by
  dsimp [oneBitFlipDecompressor, produces]
  rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits,
    List.drop_left, List.take_left, bitsToNat_bits]
  rw [Part.mem_map_iff]
  refine ⟨x, hp, ?_⟩
  exact flipBitAt_eq_set hi

/-- The overhead of naming a bit position below `n` self-delimitingly is at most
`log n + (6 + c) (log log n + 1)`. -/
theorem oneBitFlip_overhead_bound (n i c_D : ℕ) (hi : i < n) :
    (Nat.bits i).length + 2 * (Nat.bits (Nat.bits i).length).length + 1 + c_D ≤
      Nat.log 2 n + (6 + c_D) * (Nat.log 2 (Nat.log 2 n) + 1) := by
  have h_i_le : i ≤ n := by omega
  have h_i_len : (Nat.bits i).length ≤ (Nat.bits n).length := Kolmogorov.length_natBits_mono h_i_le
  have h_bits_n : (Nat.bits n).length ≤ Nat.log 2 n + 1 := length_natBits_le_log n
  have h_ii_len : (Nat.bits (Nat.bits i).length).length ≤ (Nat.bits (Nat.bits n).length).length :=
    Kolmogorov.length_natBits_mono h_i_len
  have h_bits_nn : (Nat.bits (Nat.bits n).length).length ≤ Nat.log 2 ((Nat.bits n).length) + 1 :=
    length_natBits_le_log _
  have h_log_succ : Nat.log 2 ((Nat.bits n).length) ≤ Nat.log 2 (Nat.log 2 n) + 1 :=
    (Nat.log_mono_right h_bits_n).trans (log_succ_le _)
  have H1 : (Nat.bits i).length ≤ Nat.log 2 n + 1 := h_i_len.trans h_bits_n
  have H2 : (Nat.bits (Nat.bits i).length).length ≤ Nat.log 2 (Nat.log 2 n) + 2 :=
    h_ii_len.trans (h_bits_nn.trans (by omega))
  calc (Nat.bits i).length + 2 * (Nat.bits (Nat.bits i).length).length + 1 + c_D
    _ ≤ (Nat.log 2 n + 1) + 2 * (Nat.log 2 (Nat.log 2 n) + 2) + 1 + c_D := by omega
    _ = Nat.log 2 n + 2 * Nat.log 2 (Nat.log 2 n) + (6 + c_D) := by omega
    _ ≤ Nat.log 2 n + (6 + c_D) * Nat.log 2 (Nat.log 2 n) + (6 + c_D) * 1 := by
      have : 2 * Nat.log 2 (Nat.log 2 n) ≤ (6 + c_D) * Nat.log 2 (Nat.log 2 n) := by
        nlinarith [Nat.zero_le (Nat.log 2 (Nat.log 2 n)), Nat.zero_le c_D]
      omega
    _ = Nat.log 2 n + (6 + c_D) * (Nat.log 2 (Nat.log 2 n) + 1) := by ring

/-- **Exercise 38.** Flipping one bit changes `C(x)` and `C(x | n)` by at most
`log n + O(log log n)`. -/
theorem plainK_flipBit_le_add_log (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ (n i : ℕ) (x : BitString), x.length = n → i < n →
      (plainK U (x.set i (!x.getD i false)) ≤ plainK U x +
          ((Nat.log 2 n + k * (Nat.log 2 (Nat.log 2 n) + 1) : ℕ) : ℕ∞)) ∧
        (condK U (x.set i (!x.getD i false)) (Nat.bits n) ≤ condK U x (Nat.bits n) +
          ((Nat.log 2 n + k * (Nat.log 2 (Nat.log 2 n) + 1) : ℕ) : ℕ∞)) := by
  obtain ⟨c_D, hc_D⟩ := hU.2 (oneBitFlipDecompressor U) (oneBitFlipDecompressor_isDecompressor hU.1)
  use 6 + c_D
  intro n i x hx hi
  have h_bound := oneBitFlip_overhead_bound n i c_D hi
  have h_cond_le (y : BitString) :
      condK U (x.set i (!x.getD i false)) y ≤ condK U x y +
        ((Nat.log 2 n + (6 + c_D) * (Nat.log 2 (Nat.log 2 n) + 1) : ℕ) : ℕ∞) := by
    by_cases hK : condK U x y = ⊤
    · rw [hK, top_add]; exact le_top
    · have hne : (candidateLengths U x y).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro he
        have : condK U x y = ⊤ := by change sInf (candidateLengths U x y) = ⊤; rw [he, sInf_empty]
        exact hK this
      obtain ⟨p, hp, hp_l⟩ := csInf_mem hne
      have h_prod := oneBitFlipDecompressor_produces hp (by rw [hx]; exact hi)
      have h_le_D : condK (oneBitFlipDecompressor U) (x.set i (!x.getD i false)) y ≤
          ((pairCode (Nat.bits (Nat.bits i).length) (Nat.bits i ++ p)).length : ℕ∞) :=
        sInf_le ⟨pairCode (Nat.bits (Nat.bits i).length) (Nat.bits i ++ p), h_prod, rfl⟩
      have h_len_eq :
          (pairCode (Nat.bits (Nat.bits i).length) (Nat.bits i ++ p)).length + c_D =
            p.length + ((Nat.bits i).length +
              2 * (Nat.bits (Nat.bits i).length).length + 1 + c_D) := by
        rw [length_pairCode, List.length_append]; omega
      calc condK U (x.set i (!x.getD i false)) y
        _ ≤ condK (oneBitFlipDecompressor U) (x.set i (!x.getD i false)) y + (c_D : ℕ∞) :=
          hc_D _ _
        _ ≤ ((pairCode (Nat.bits (Nat.bits i).length) (Nat.bits i ++ p)).length : ℕ∞) +
            (c_D : ℕ∞) := by
          gcongr
        _ = (p.length : ℕ∞) +
            ((Nat.bits i).length + 2 * (Nat.bits (Nat.bits i).length).length + 1 + c_D : ℕ) := by
          exact_mod_cast h_len_eq
        _ ≤ condK U x y +
            ((Nat.log 2 n + (6 + c_D) * (Nat.log 2 (Nat.log 2 n) + 1) : ℕ) : ℕ∞) := by
          change (p.length : ℕ∞) = condK U x y at hp_l
          rw [hp_l]
          gcongr
  refine ⟨h_cond_le [], h_cond_le (Nat.bits n)⟩

/-- The set of descriptions of `x` of length at most `n` with respect to `D`. -/
def descriptionsLe (D : Map) (x : BitString) (n : ℕ) : Set BitString :=
  {p : BitString | produces D p [] x ∧ p.length ≤ n}

/-- The set of shortest descriptions of `x` with respect to `D`. -/
def shortestDescriptions (D : Map) (x : BitString) : Set BitString :=
  {p : BitString | produces D p [] x ∧ (p.length : ℕ∞) = plainK D x}


end Kolmogorov
