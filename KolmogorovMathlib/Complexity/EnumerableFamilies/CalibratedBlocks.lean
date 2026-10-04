import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.EnumerableFamilies.CountingBounds
import KolmogorovMathlib.Complexity.EnumerableFamilies.Enumeration
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Reduce
import Mathlib.Data.Nat.Dist

/-!
# The block decompressor of the calibration theorem

The calibration theorem — a function that is upper semicomputable, does not grow along partial
computable maps and has small sublevel sets equals `C` up to a constant — needs a decompressor
that produces every string of small value from a short program.  That is `decompressor2`,
built here: it searches for a stage at which the level containing the input is full and reads
the string off the block enumerated there.

`decompressor2_partrec` (with `decompressor2Check_rfind_partrec` and
`decompressor2Check_ofOpt_partrec`) makes it partial computable,
`exists_stage_ncard_le_enumVList_length` shows the search terminates because every sublevel
set is exhausted, `k_le_length_add_of_qStage` says what it produces, and
`le_plainK_of_two_pow_le_card_of_nonGrowth` is the resulting lower bound on the function.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- The unbounded search for a stage at which the block decompressor fires is partial
computable. -/
lemma decompressor2Check_rfind_partrec (c_k : Code) (c₁ : ℕ) :
    Partrec (fun (w : BitString) =>
      Nat.rfind (fun s => Part.some (decompressor2Check c_k c₁ w s).isSome)) :=
  Partrec.rfind (decompressor2Check_rfind_p_partrec c_k c₁).to₂

/-- The value of the block decompressor at a stage, read as a partial function, is
partial computable. -/
lemma decompressor2Check_ofOpt_partrec (c_k : Code) (c₁ : ℕ) :
    Partrec (fun (p : BitString × ℕ) => Part.ofOption (decompressor2Check c_k c₁ p.1 p.2)) :=
  Computable.ofOption (decompressor2Check_computable c_k c₁)

/-- The block decompressor is partial computable. -/
lemma decompressor2_partrec (c_k : Code) (c₁ : ℕ) :
    Partrec (decompressor2 c_k c₁) :=
  Partrec.bind (decompressor2Check_rfind_partrec c_k c₁)
    (decompressor2Check_ofOpt_partrec c_k c₁).to₂

/-- Every sublevel set of `k` is exhausted by some stage of the enumeration. -/
private lemma exists_stage_ncard_le_enumVList_length {k : BitString → ℕ} {c_k : Code}
    (hfin : ∀ n : ℕ, {x : BitString | k x < n}.Finite)
    (hdom_ck : ∀ (n : ℕ) (x : BitString), k x < n →
      (c_k.eval (Encodable.encode (n, x))).Dom)
    (n : ℕ) : ∃ s : ℕ, {x : BitString | k x < n}.ncard ≤ (enumVList c_k n s).length := by
  have h_stage : ∀ x ∈ (hfin n).toFinset, ∃ s, x ∈ enumVList c_k n s := by
    intro x hx
    have hx_spec := (Set.Finite.mem_toFinset (hfin n)).mp hx
    have h_c_dom : (c_k.eval (Encodable.encode (n, x))).Dom := hdom_ck n x hx_spec
    obtain ⟨r0, hr0⟩ := Part.dom_iff_mem.mp h_c_dom
    obtain ⟨s0, hs0⟩ := Nat.Partrec.Code.evaln_complete.mp hr0
    let s1 := max s0 x.length
    have hs0_x : s0 ≤ s1 := le_max_left _ _
    have hs0_eval : (Code.evaln s1 c_k (Encodable.encode (n, x))).isSome = true := by
      have hr_s0 := Nat.Partrec.Code.evaln_mono hs0_x hs0
      exact Option.isSome_iff_exists.mpr ⟨r0, hr_s0⟩
    have hs0_len : x.length ≤ s1 := le_max_right _ _
    obtain ⟨s_first, hs_first_le, hs_first_halt, hs_first_spec, hs_first_len⟩ :=
      firstAppearsAt_spec c_k n x s1 hs0_eval hs0_len
    have h_in_step : x ∈ enumVStep c_k n s_first :=
      enumV_step_mem c_k n s_first x hs_first_halt hs_first_spec hs_first_len
    exact ⟨s1, enumV_list_mem c_k n s_first x h_in_step s1 hs_first_le⟩
  choose stage hstage using h_stage
  let stage_fn := fun (x : BitString) => if hx : x ∈ (hfin n).toFinset then stage x hx else 0
  let s0 := (hfin n).toFinset.sup stage_fn
  have hs0_all : ∀ x ∈ {x | k x < n}, x ∈ enumVList c_k n s0 := by
    intro x hx
    have hx_fin : x ∈ (hfin n).toFinset := (hfin n).mem_toFinset.mpr hx
    have h_le : stage x hx_fin ≤ s0 := by
      have h_le' : stage_fn x ≤ s0 := Finset.le_sup hx_fin
      dsimp [stage_fn] at h_le'
      rwa [dite_eq_left hx_fin] at h_le'
    have h_pre := enumV_list_prefix c_k n (stage x hx_fin) s0 h_le
    exact h_pre.subset (hstage x hx_fin)
  have h_sub_fin : (hfin n).toFinset ⊆ (enumVList c_k n s0).toFinset := by
    intro x hx
    rw [List.mem_toFinset]
    exact hs0_all x ((hfin n).mem_toFinset.mp hx)
  have h_card_sub : (hfin n).toFinset.card ≤ (enumVList c_k n s0).toFinset.card :=
    Finset.card_le_card h_sub_fin
  rw [List.toFinset_card_of_nodup (enumV_list_nodup c_k n s0)] at h_card_sub
  rw [← Set.ncard_eq_toFinset_card {x | k x < n} (hfin n)] at h_card_sub
  exact ⟨s0, h_card_sub⟩
-- hence every pool eventually reaches its quota

/-- Every string of length `i` is produced by the block decompressor from a string of small
`k`-value, so `k` is bounded by the length up to the calibration constants. -/
private lemma k_le_length_add_of_qStage {k : BitString → ℕ} {c₁ c_B : ℕ} {c_k : Code}
    (hsub : ∀ (n s : ℕ) (z : BitString), z ∈ enumVList c_k n s → k z < n)
    (h_qstage : ∀ m : ℕ, ∃ s : ℕ, qStage c_k c₁ m s = true)
    (hc_B : ∀ x y : BitString, y ∈ decompressor2 c_k c₁ x → k y ≤ k x + c_B)
    (i : ℕ) (y : BitString) (hy_len : y.length = i) : k y ≤ i + c₁ + c_B := by
  have hy_mem_exact : y ∈ exactLengthPrograms i := hy_len ▸ mem_exactLengthPrograms_length y
  obtain ⟨j, hj_def⟩ :
      ∃ j, (exactLengthPrograms i).findIdx (fun x => x == y) = j := ⟨_, rfl⟩
  have hj_lt : j < (exactLengthPrograms i).length := by
    rw [← hj_def, List.findIdx_lt_length]
    exact ⟨y, hy_mem_exact, beq_self_eq_true y⟩
  have hj_lt_pow : j < 2 ^ i := by
    have h := hj_lt
    rw [length_exactLengthPrograms i] at h
    exact h
  have hj_get : (exactLengthPrograms i).getD j [] = y := by
    have hfind : (exactLengthPrograms i).findIdx (fun x => x == y)
        < (exactLengthPrograms i).length := by
      rw [hj_def]; exact hj_lt
    have h_getElem := List.findIdx_getElem (w := hfind) (p := fun x => x == y)
      (xs := exactLengthPrograms i)
    simp only [beq_iff_eq] at h_getElem
    rw [← hj_def, List.getD_eq_getElem (hn := hfind)]
    exact h_getElem
  obtain ⟨s, hs⟩ := h_qstage i
  have hb_len : (qBlock c_k c₁ i s).length = 2 ^ i := qBlock_length c_k c₁ hs
  have hj_lt_block : j < (qBlock c_k c₁ i s).length := by rw [hb_len]; exact hj_lt_pow
  obtain ⟨z, hz_def⟩ : ∃ z, (qBlock c_k c₁ i s)[j]'hj_lt_block = z := ⟨_, rfl⟩
  have hz_mem : z ∈ qBlock c_k c₁ i s := hz_def ▸ List.getElem_mem hj_lt_block
  have hz_idx : (qBlock c_k c₁ i s).findIdx (fun x => x == z) = j := by
    rw [← hz_def]
    exact findIdx_getElem_eq (qBlock_nodup c_k c₁ i s) j hj_lt_block
  have hz_k : k z < i + c₁ + 1 :=
    hsub (i + c₁ + 1) s z (qBlock_mem_enumV c_k c₁ i s hz_mem)
  -- the check fires on `z` at the pair `⟨i, s⟩`
  have hcheck : decompressor2Check c_k c₁ z (Nat.pair i s) = some y := by
    rw [decompressor2Check_fires c_k c₁ z i s hs hz_mem, hz_idx, hj_get]
  have hrfind_dom :
      (Nat.rfind (fun w => Part.some (decompressor2Check c_k c₁ z w).isSome)).Dom := by
    let p : ℕ →. Bool := fun w => Part.some (decompressor2Check c_k c₁ z w).isSome
    have h_rfind : (Nat.rfind p).Dom := by
      rw [Nat.rfind_dom]
      refine ⟨Nat.pair i s, ?_, fun _ => Part.some_dom _⟩
      rw [Part.mem_some_iff, hcheck]
      rfl
    exact h_rfind
  obtain ⟨w_found, hw_found⟩ := Part.dom_iff_mem.mp hrfind_dom
  have hw_spec := Nat.mem_rfind.mp hw_found
  have hw_isSome : (decompressor2Check c_k c₁ z w_found).isSome = true := by
    have h1 := hw_spec.1
    simp only [Part.mem_some_iff] at h1
    exact h1.symm
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp hw_isSome
  obtain ⟨hst', hmem', hval'⟩ := decompressor2Check_spec c_k c₁ z w_found hy'
  -- whatever pair the search finds, it describes the same block, hence the same output
  have hlevel : w_found.unpair.1 = i := by
    have h1 : z ∈ qBlock c_k c₁ w_found.unpair.1 (max s w_found.unpair.2) := by
      rw [qBlock_stable c_k c₁ hst' (le_max_right s w_found.unpair.2)]
      exact hmem'
    have h2 : z ∈ qBlock c_k c₁ i (max s w_found.unpair.2) := by
      rw [qBlock_stable c_k c₁ hs (le_max_left s w_found.unpair.2)]
      exact hz_mem
    exact qBlock_level_unique c_k c₁ h1 h2
  have hst'' : qStage c_k c₁ i w_found.unpair.2 = true := by rw [← hlevel]; exact hst'
  have hblock_eq : qBlock c_k c₁ i w_found.unpair.2 = qBlock c_k c₁ i s := by
    have e1 : qBlock c_k c₁ i (max s w_found.unpair.2) = qBlock c_k c₁ i s :=
      qBlock_stable c_k c₁ hs (le_max_left _ _)
    have e2 : qBlock c_k c₁ i (max s w_found.unpair.2) = qBlock c_k c₁ i w_found.unpair.2 :=
      qBlock_stable c_k c₁ hst'' (le_max_right _ _)
    rw [← e2, e1]
  have hy_eq : y' = y := by
    rw [hval', hlevel, hblock_eq, hz_idx, hj_get]
  have hy_mem : y ∈ decompressor2 c_k c₁ z := by
    dsimp [decompressor2]
    rw [Part.mem_bind_iff]
    refine ⟨w_found, hw_found, Part.mem_ofOption.mpr ?_⟩
    rw [Option.mem_def, hy', hy_eq]
  have hkb := hc_B z y hy_mem
  omega

/-- A function that does not grow along partial computable maps and whose sublevel sets
are large enough is bounded below by plain complexity up to an additive constant.
SUV Theorem 9, second direction. -/
lemma le_plainK_of_two_pow_le_card_of_nonGrowth (U : Map) (hU : isOptimalConditional U)
    (k : BitString → ℕ)
    (hnongrowth : ∀ A : BitString →. BitString, Partrec A →
      ∃ c : ℕ, ∀ x y : BitString, y ∈ A x → k y ≤ k x + c)
    (c₁ : ℕ)
    (hcard_lower : ∀ n : ℕ, c₁ ≤ n → 2 ^ (n - c₁) ≤ {x : BitString | k x < n}.ncard)
    (henum : IsUpperSemicomputable (fun x => (k x : ℕ∞)))
    (hfin : ∀ n : ℕ, {x : BitString | k x < n}.Finite) :
    ∃ c : ℕ, ∀ x : BitString, (k x : ℕ∞) ≤ plainK U x + (c : ℕ∞) := by
  have h_re : IsRE (fun p : ℕ × BitString => k p.2 < p.1) := by
    obtain ⟨f_k, hf_k_part, hf_k_dom⟩ := henum
    use fun p : ℕ × BitString => f_k (p.2, p.1)
    refine ⟨Partrec.comp hf_k_part (Computable.pair Computable.snd Computable.fst),
             fun ⟨n, x⟩ => ?_⟩
    dsimp
    have h_coe : ((k x : ℕ∞) < (n : ℕ∞)) ↔ k x < n := WithTop.coe_lt_coe
    exact (hf_k_dom (x, n)).trans h_coe
  obtain ⟨f_enum, hf_partrec, hf_dom⟩ := h_re
  obtain ⟨c_k, hc_k⟩ := Nat.Partrec.Code.exists_code.mp hf_partrec
  have hd2_partrec : Partrec (decompressor2 c_k c₁) := decompressor2_partrec c_k c₁
  obtain ⟨c_B, hc_B⟩ := hnongrowth (decompressor2 c_k c₁) hd2_partrec
  -- every level of the enumeration is eventually complete
  have hdom_ck : ∀ (n : ℕ) (x : BitString), k x < n →
      (c_k.eval (Encodable.encode (n, x))).Dom := by
    intro n x hx_spec
    have hdom : (f_enum (n, x)).Dom := (hf_dom (n, x)).mpr hx_spec
    rw [hc_k]
    dsimp
    have h_dec : Encodable.decode (α := ℕ × BitString)
        (Nat.pair n (Encodable.encode x)) = (some (n, x) : Option (ℕ × BitString)) :=
      Encodable.encodek (n, x)
    rw [h_dec]
    dsimp [Part.ofOption]
    rw [Part.bind_some]
    obtain ⟨u0, hu0⟩ := Part.dom_iff_mem.mp hdom
    exact Part.dom_iff_mem.mpr ⟨Encodable.encode u0, Part.mem_map Encodable.encode hu0⟩
  have h_enum_complete : ∀ n : ℕ, ∃ s : ℕ,
      {x : BitString | k x < n}.ncard ≤ (enumVList c_k n s).length :=
    fun n => exists_stage_ncard_le_enumVList_length hfin hdom_ck n
  have h_pool_full : ∀ m : ℕ, ∃ s : ℕ,
      2 ^ (m + 1) ≤ (enumVList c_k (m + c₁ + 1) s).length := by
    intro m
    obtain ⟨s, hs⟩ := h_enum_complete (m + c₁ + 1)
    refine ⟨s, ?_⟩
    have hc := hcard_lower (m + c₁ + 1) (by omega)
    have he : m + c₁ + 1 - c₁ = m + 1 := by omega
    rw [he] at hc
    exact hc.trans hs
  have h_qstage : ∀ m : ℕ, ∃ s : ℕ, qStage c_k c₁ m s = true := by
    intro m
    induction m with
    | zero =>
      obtain ⟨s, hs⟩ := h_pool_full 0
      refine ⟨s, (qStage_iff c_k c₁ 0 s).mpr fun m' hm' => ?_⟩
      obtain rfl := Nat.le_zero.mp hm'
      exact hs
    | succ m ih =>
      obtain ⟨s1, hs1⟩ := ih
      obtain ⟨s2, hs2⟩ := h_pool_full (m + 1)
      have hs1' : qStage c_k c₁ m (max s1 s2) = true :=
        qStage_mono c_k c₁ hs1 (le_max_left _ _)
      have hs2' : 2 ^ (m + 1 + 1) ≤ (enumVList c_k (m + 1 + c₁ + 1) (max s1 s2)).length :=
        hs2.trans (enumV_list_length_mono c_k _ (le_max_right _ _))
      refine ⟨max s1 s2, (qStage_iff c_k c₁ (m + 1) (max s1 s2)).mpr fun m' hm' => ?_⟩
      rcases Nat.eq_or_lt_of_le hm' with h | h
      · exact h ▸ hs2'
      · exact (qStage_iff c_k c₁ m (max s1 s2)).mp hs1' m' (Nat.lt_succ_iff.mp h)
  -- the decompressor maps a string of small `k`-value onto every string of length `i`
  have hsub : ∀ (n s : ℕ) (z : BitString), z ∈ enumVList c_k n s → k z < n :=
    fun n s z hz =>
      enumV_list_sub (fun n => {x : BitString | k x < n}) c_k f_enum hc_k hf_dom n s z hz
  have h_k_len_aux : ∀ (i : ℕ) (y : BitString), y.length = i → k y ≤ i + c₁ + c_B :=
    fun i y hy_len => k_le_length_add_of_qStage hsub h_qstage hc_B i y hy_len
  have h_k_len : ∀ y : BitString, k y ≤ y.length + c₁ + c_B :=
    fun y => h_k_len_aux y.length y rfl
  have hA_partrec : Partrec (fun p : BitString => U (p, [])) :=
    Partrec.comp hU.1 (Computable.pair Computable.id (Computable.const []))
  obtain ⟨c_A, hc_A⟩ := hnongrowth (fun p => U (p, [])) hA_partrec
  refine ⟨c₁ + c_B + c_A, fun x => ?_⟩
  by_cases h_top : plainK U x = ⊤
  · rw [h_top]
    exact le_top
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, plainK U x = (m : ℕ∞) := by
      cases h : plainK U x
      · contradiction
      · exact ⟨_, rfl⟩
    have h_condK : condK U x [] ≤ (m : ℕ∞) := by rw [← hm]; rfl
    have h_ex := (condK_le_iff U x [] m).mp h_condK
    obtain ⟨p, hp_len, hp_prod⟩ := h_ex
    have hp_mem : x ∈ U (p, []) := hp_prod
    have hkx : k x ≤ k p + c_A := hc_A p x hp_mem
    have hkp : k p ≤ p.length + c₁ + c_B := h_k_len p
    have h_p_len : p.length ≤ m := hp_len
    have h_tot_nat : k x ≤ m + c₁ + c_B + c_A := by omega
    rw [hm]
    have h_coe : (k x : ℕ∞) ≤ ((m + c₁ + c_B + c_A : ℕ) : ℕ∞) := WithTop.coe_le_coe.mpr h_tot_nat
    have h_assoc : ((m + c₁ + c_B + c_A : ℕ) : ℕ∞) =
        (m : ℕ∞) + (c₁ : ℕ∞) + (c_B : ℕ∞) + (c_A : ℕ∞) := by
      push_cast
      rfl
    rw [h_assoc] at h_coe
    have h_group : (m : ℕ∞) + (c₁ : ℕ∞) + (c_B : ℕ∞) + (c_A : ℕ∞) =
        (m : ℕ∞) + ((c₁ + c_B + c_A : ℕ) : ℕ∞) := by
      push_cast
      ring
    rw [h_group] at h_coe
    exact h_coe

end Kolmogorov
