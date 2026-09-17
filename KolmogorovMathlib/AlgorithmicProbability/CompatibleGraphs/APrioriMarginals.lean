import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.Prefix.SelfDelimitingMachines
import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs.Basic

/-!
# Order of the Kraft–Chaitin free list

The free list of the online Kraft–Chaitin allocator is kept sorted by position in the binary
tree.  `leftValue_le_of_state` states that: padded to a common length, the value of an earlier
free node is at most the value of a later one, which is what lets the allocator serve a request
by scanning the list from the left.  `getElem_free'_part3` is the last of the three read-off
lemmas for the rebuilt list, describing the entries after the replaced block.

The construction, the other two read-off lemmas and the incomparability of distinct free nodes
are in `AlgorithmicProbability/CompatibleGraphs/Basic`.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-- Entries of the rebuilt free list after the replaced block are the old ones, shifted. -/
lemma getElem_free'_part3 {F : List BitString} {idx diff : ℕ} {B : List BitString}
    (hA : idx < F.length) (hB : B.length = diff) (k : ℕ) (hk : idx + diff ≤ k)
    (hk' : k < (F.take idx ++ B ++ F.drop (idx + 1)).length) :
    (F.take idx ++ B ++ F.drop (idx + 1))[k] = F[k - diff + 1]'(by
      have htake : (F.take idx).length = idx := by rw [List.length_take, Nat.min_eq_left (by omega)]
      have hlen : (F.take idx ++ B ++ F.drop (idx + 1)).length = F.length + diff - 1 := by
        simp only [List.length_append, htake, hB, List.length_drop]
        omega
      omega) := by
  have htake : (F.take idx).length = idx := by rw [List.length_take, Nat.min_eq_left (by omega)]
  have h1 : (F.take idx ++ B).length ≤ k := by
    rw [List.length_append, htake, hB]; exact hk
  rw [List.getElem_append_right h1]
  have h2 : k - (F.take idx ++ B).length < (F.drop (idx + 1)).length := by
    rw [List.length_drop]
    have h_app_len : (F.take idx ++ B).length = idx + diff := by
      simp [List.length_append, htake, hB]
    have hk_len : (F.take idx ++ B ++ F.drop (idx + 1)).length =
        idx + diff + (F.length - (idx + 1)) := by
      simp only [List.length_append, h_app_len, List.length_drop]
    omega
  have h2' : k - diff + 1 < F.length := by
    have h_app_len : (F.take idx ++ B).length = idx + diff := by
      simp [List.length_append, htake, hB]
    have h2_drop : k - (F.take idx ++ B).length < F.length - (idx + 1) := by
      rwa [List.length_drop] at h2
    rw [h_app_len] at h2_drop
    omega
  have h3 : (F.drop (idx + 1))[k - (F.take idx ++ B).length]'h2 = F[k - diff + 1]'h2' := by
    rw [List.getElem_drop]
    congr 1
    rw [List.length_append, htake, hB]
    omega
  exact h3

/-- The free list of the allocator is sorted by value: padded to a common length `L`, the value of
an earlier free node is at most the value of a later one. -/
lemma leftValue_le_of_state (req : ℕ → Option (BitString × ℕ)) (n : ℕ)
    (free : List BitString) (hfree : KraftChaitin.allocatorState req n = some free)
    (i j : ℕ) (hi : i < free.length) (hj : j < free.length) (hij : i ≤ j) (L : ℕ)
    (h_i : (free[i]'hi).length ≤ L) (h_j : (free[j]'hj).length ≤ L) :
    leftValue ((free[i]'hi) ++ List.replicate (L - (free[i]'hi).length) false) ≤
    leftValue ((free[j]'hj) ++ List.replicate (L - (free[j]'hj).length) false) := by
  induction n generalizing free i j L with
  | zero =>
    unfold KraftChaitin.allocatorState at hfree
    have h1 : free = [[]] := Option.some.inj hfree.symm
    subst h1
    dsimp at hi hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    rfl
  | succ n ih =>
    unfold KraftChaitin.allocatorState at hfree
    rcases hF : KraftChaitin.allocatorState req n with _ | F
    · rw [hF] at hfree; contradiction
    rw [hF] at hfree
    dsimp only at hfree
    rcases hreq : req n with _ | ⟨o, l⟩
    · rw [hreq] at hfree
      injection hfree with h1; subst h1
      exact ih F hF i j hi hj hij L h_i h_j
    rw [hreq] at hfree
    dsimp only at hfree
    rcases halloc : KraftChaitin.allocateOne F l with _ | ⟨w_n, free'⟩
    · rw [halloc] at hfree; contradiction
    rw [halloc] at hfree
    injection hfree with h1; subst h1
    unfold KraftChaitin.allocateOne at halloc
    rcases hfind : F.findIdx? (fun v => v.length ≤ l) with _ | idx
    · rw [hfind] at halloc; contradiction
    rw [hfind] at halloc
    injection halloc with h_pair
    injection h_pair with _ hfree'_eq
    let diff := l - F[idx]!.length
    let B := ((List.range diff).map
        (fun m => F[idx]! ++ List.replicate m false ++ [true])).reverse
    have hB_len : B.length = diff := by simp [B]
    subst free'
    obtain ⟨h_idx_lt, h_idx_len_dec, h_idx_min⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
    have h_idx_len : F[idx].length ≤ l := of_decide_eq_true h_idx_len_dec
    have h_idx_eq : F[idx]! = F[idx] := getElem!_pos F idx h_idx_lt
    have h_idx_len_F : F[idx]!.length ≤ l := by rw [h_idx_eq]; exact h_idx_len
    have h_diff : diff = l - F[idx].length := by rw [← h_idx_eq]
    have hB_get_len : ∀ (m : ℕ) (hm : m < B.length), (B[m]'hm).length = l - m := fun m hm =>
      splitNodeBlock_getElem_length F[idx]! l m h_idx_len_F hm
    have h_len : (F.take idx ++ B ++ F.drop (idx + 1)).length = F.length + diff - 1 := by
      simp only [List.length_append, List.length_take, hB_len, List.length_drop]
      omega
    have hi' : i < F.length + diff - 1 := by rw [← h_len]; exact hi
    have hj' : j < F.length + diff - 1 := by rw [← h_len]; exact hj
    rcases eq_or_lt_of_le hij with rfl | hij_lt
    · rfl
    rcases lt_or_ge j idx with hj_lt | hj_ge
    · have h_i_eq : (F.take idx ++ B ++ F.drop (idx + 1))[i] = F[i] :=
        getElem_free'_part1 (by omega) i (by omega) hi
      have h_j_eq : (F.take idx ++ B ++ F.drop (idx + 1))[j] = F[j] :=
        getElem_free'_part1 (by omega) j hj_lt hj
      have h_i_F : F[i].length ≤ L := by rwa [h_i_eq] at h_i
      have h_j_F : F[j].length ≤ L := by rwa [h_j_eq] at h_j
      rw [h_i_eq, h_j_eq]
      exact ih F hF i j (by omega) (by omega) hij L h_i_F h_j_F
    rcases lt_or_ge i idx with hi_lt | hi_ge
    · rcases lt_or_ge j (idx + diff) with hj_mid | hj_high
      · have hjB : j - idx < B.length := by rw [hB_len]; omega
        have h_i_eq : (F.take idx ++ B ++ F.drop (idx + 1))[i] = F[i] :=
          getElem_free'_part1 (by omega) i hi_lt hi
        have h_j_eq : (F.take idx ++ B ++ F.drop (idx + 1))[j] = B[j - idx] :=
          getElem_free'_part2 (by omega) hB_len j hj_ge hj_mid hj
        have h_i_F : F[i].length ≤ L := by rwa [h_i_eq] at h_i
        have h_j_F : (B[j - idx]'hjB).length ≤ L := by rwa [h_j_eq] at h_j
        have h_l_j_L : l - (j - idx) ≤ L := by rw [← hB_get_len (j - idx) hjB]; exact h_j_F
        have h_idx_L : F[idx].length ≤ L := by
          have hlt : j - idx < diff := by omega
          rw [h_diff] at hlt
          omega
        have h1 := ih F hF i idx (by omega) h_idx_lt (by omega) L h_i_F h_idx_L
        rw [← h_idx_eq] at h1
        rw [h_i_eq, h_j_eq]
        exact h1.trans (leftValue_pad_le_splitNodeBlock_pad F[idx]! l (j - idx) L
          h_idx_len_F h_l_j_L hjB)
      · have hj_F_lt : j - diff + 1 < F.length := by omega
        have h_i_eq : (F.take idx ++ B ++ F.drop (idx + 1))[i] = F[i] :=
          getElem_free'_part1 (by omega) i hi_lt hi
        have h_j_eq : (F.take idx ++ B ++ F.drop (idx + 1))[j] = F[j - diff + 1]'hj_F_lt :=
          getElem_free'_part3 h_idx_lt hB_len j hj_high hj
        have h_i_F : F[i].length ≤ L := by rwa [h_i_eq] at h_i
        have h_j_F : (F[j - diff + 1]'hj_F_lt).length ≤ L := by rwa [h_j_eq] at h_j
        rw [h_i_eq, h_j_eq]
        exact ih F hF i (j - diff + 1) (by omega) hj_F_lt (by omega) L h_i_F h_j_F
    rcases lt_or_ge i (idx + diff) with hi_mid | hi_high
    · have hiB : i - idx < B.length := by rw [hB_len]; omega
      have h_i_eq : (F.take idx ++ B ++ F.drop (idx + 1))[i] = B[i - idx] :=
        getElem_free'_part2 (by omega) hB_len i hi_ge hi_mid hi
      have h_i_F : (B[i - idx]'hiB).length ≤ L := by rwa [h_i_eq] at h_i
      have h_l_i_L : l - (i - idx) ≤ L := by rw [← hB_get_len (i - idx) hiB]; exact h_i_F
      rcases lt_or_ge j (idx + diff) with hj_mid | hj_high
      · have hjB : j - idx < B.length := by rw [hB_len]; omega
        have h_j_eq : (F.take idx ++ B ++ F.drop (idx + 1))[j] = B[j - idx] :=
          getElem_free'_part2 (by omega) hB_len j hj_ge hj_mid hj
        rw [h_i_eq, h_j_eq]
        exact leftValue_splitNodeBlock_pad_mono F[idx]! l (i - idx) (j - idx) L
          h_idx_len_F hiB hjB (by omega) h_l_i_L
      · have hj_F_lt : j - diff + 1 < F.length := by omega
        have h_j_eq : (F.take idx ++ B ++ F.drop (idx + 1))[j] = F[j - diff + 1]'hj_F_lt :=
          getElem_free'_part3 h_idx_lt hB_len j hj_high hj
        have h_j_F : (F[j - diff + 1]'hj_F_lt).length ≤ L := by rwa [h_j_eq] at h_j
        have h_idx_L : F[idx].length ≤ L := by
          have hlt : i - idx < diff := by omega
          rw [h_diff] at hlt
          omega
        have h1 := ih F hF idx (j - diff + 1) h_idx_lt hj_F_lt (by omega) L h_idx_L h_j_F
        obtain ⟨hpf1, hpf2⟩ :=
          allocatorState_getElem_incomparable req n F hF idx (j - diff + 1) (by omega) hj_F_lt
        rw [← h_idx_eq] at h1 hpf1 hpf2
        rw [h_i_eq, h_j_eq]
        exact leftValue_splitNodeBlock_pad_le_of_prefixFree F[idx]! (F[j - diff + 1]'hj_F_lt)
          l (i - idx) L h_idx_len_F h_j_F hpf1 hpf2 hiB h_l_i_L h1
    · have hi_F_lt : i - diff + 1 < F.length := by omega
      have hj_F_lt : j - diff + 1 < F.length := by omega
      have h_i_eq : (F.take idx ++ B ++ F.drop (idx + 1))[i] = F[i - diff + 1]'hi_F_lt :=
        getElem_free'_part3 h_idx_lt hB_len i hi_high hi
      have h_j_eq : (F.take idx ++ B ++ F.drop (idx + 1))[j] = F[j - diff + 1]'hj_F_lt :=
        getElem_free'_part3 h_idx_lt hB_len j (by omega) hj
      have h_i_F : (F[i - diff + 1]'hi_F_lt).length ≤ L := by rwa [h_i_eq] at h_i
      have h_j_F : (F[j - diff + 1]'hj_F_lt).length ≤ L := by rwa [h_j_eq] at h_j
      rw [h_i_eq, h_j_eq]
      exact ih F hF (i - diff + 1) (j - diff + 1) hi_F_lt hj_F_lt (by omega) L h_i_F h_j_F

end Kolmogorov
