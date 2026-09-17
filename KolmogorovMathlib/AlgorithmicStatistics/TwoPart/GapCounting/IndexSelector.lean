import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Part02
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting.GapBounds
import KolmogorovMathlib.Foundation.ListUtil

/-!
# Counting descriptions: the enumeration

Properties of the online enumeration `appearanceListCodes` of the `(i, j)`-descriptions of `x`
that the index selector addresses.  It only grows (`appearanceListCodes_prefix`,
`prefix_of_le_appearanceListCodes`), it is sound — every entry decodes to a genuine
size-restricted description (`mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes`,
`snapshotDescriptionsAndSizeLe_subset_descriptions`) — and its length never exceeds the number
of descriptions (`appearanceListCodes_length_le_descriptionsContaining`,
`appearanceListCodes_length_lt_of_not_manyIJ`).

`indexSelectorFn_eq_code` says the selector returns the code stored at an index, and
`description_count_of_conditional_complexity_gap` is the conclusion: a computable function
that recovers the model from `y` forces `x` to have many descriptions.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- A member of `candidateCodes` decodes to a size-restricted snapshot description of `x`. -/
theorem mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes {c : Code} {i j : ℕ}
    {x : BitString} {t : ℕ} {w : BitString} (hw : w ∈ candidateCodes c i j x t) :
    isCanonicalUniformCodeBool w = true ∧
    x ∈ ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset ∧
    ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset
      ∈ snapshotDescriptionsAndSizeLe c i j t := by
  simp only [candidateCodes, List.mem_filter, decide_eq_true_eq] at hw
  obtain ⟨⟨hsnap, hcanon⟩, hxmem, hsize⟩ := hw
  refine ⟨hcanon, hxmem, ?_⟩
  rw [snapshotDescriptionsAndSizeLe, Finset.mem_filter]
  refine ⟨?_, hsize⟩
  rw [snapshotDescriptions, Finset.mem_image]
  exact ⟨w, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hsnap, hcanon⟩), rfl⟩

/-- The computable size-restricted snapshot universe at any time is contained in the
abstract description universe (it stabilizes to equality at the halting-count maximum). -/
theorem snapshotDescriptionsAndSizeLe_subset_descriptions {U : Map} {c : Code}
    (hc : IsCodeFor c U) (i j t : ℕ) :
    snapshotDescriptionsAndSizeLe c i j t ⊆ descriptionsWithComplexityLeAndSizeLe U i j := by
  obtain ⟨t₀, hmax⟩ := exists_max_countHalts c i
  have hT : ∀ t'', countHalts c i t'' ≤ countHalts c i (max t t₀) :=
    fun t'' => le_trans (hmax t'') (countHalts_mono c i (le_max_right t t₀))
  intro S hS
  rw [← snapshotDescriptionsAndSizeLe_eq_descriptionsWithComplexityLeAndSizeLe hc i j (max t t₀) hT]
  exact snapshotDescriptionsAndSizeLe_subset_of_le c i j (le_max_left t t₀) hS

/-- `eraseDups` on `BitString` lists produces a duplicate-free list.  (The core
`List.nodup_eraseDups` lemma is not available in Lean `v4.28`; this is the stand-in
proved from `eraseDups_cons` and the repo's `mem_eraseDups_bitString`.) -/
theorem nodup_eraseDups_bitString : ∀ (l : List BitString), l.eraseDups.Nodup :=
  nodup_eraseDups_list

/-- **Rank bound.**  The online enumeration of `(i,j)`-descriptions of `x` never grows
longer than the number of abstract `(i,j)`-descriptions containing `x`.  The decoded
support is an injective map from the (deduplicated) code list into that finset. -/
theorem appearanceListCodes_length_le_descriptionsContaining {U : Map} {c : Code}
    (hc : IsCodeFor c U) (i j : ℕ) (x : BitString) (t : ℕ) :
    (appearanceListCodes c i j x t).length
      ≤ ((descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S)).card := by
  set L := appearanceListCodes c i j x t with hL
  set f : BitString → Finset BitString :=
    fun w => ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset with hf
  have hnodup : L.Nodup := by
    rw [hL]; cases t <;> exact nodup_eraseDups_bitString _
  have hmaps : ∀ w ∈ L,
      f w ∈ (descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S) := by
    intro w hw
    obtain ⟨t', hw'⟩ := exists_candidate_of_mem_appearanceListCodes hw
    obtain ⟨_, hxS, hSmem⟩ := mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes hw'
    rw [Finset.mem_filter]
    exact ⟨snapshotDescriptionsAndSizeLe_subset_descriptions hc i j t' hSmem, hxS⟩
  have hinj : ∀ w1 ∈ L, ∀ w2 ∈ L, f w1 = f w2 → w1 = w2 := by
    intro w1 hw1 w2 hw2 heq
    obtain ⟨t1, hc1⟩ := exists_candidate_of_mem_appearanceListCodes hw1
    obtain ⟨t2, hc2⟩ := exists_candidate_of_mem_appearanceListCodes hw2
    have hcanon1 := (mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes hc1).1
    have hcanon2 := (mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes hc2).1
    obtain ⟨hne1, he1⟩ := eq_codedUniformOn_of_isCanonicalUniformCodeBool hcanon1
    obtain ⟨hne2, he2⟩ := eq_codedUniformOn_of_isCanonicalUniformCodeBool hcanon2
    rw [he1, he2]
    exact codedUniformOn_code_congr _ _ heq
  have hlen : L.length = (L.map f).length := by simp
  have hnd : (L.map f).Nodup := List.Nodup.map_on hinj hnodup
  have hsub : (L.map f).toFinset
      ⊆ (descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S) := by
    intro S hS
    rw [List.mem_toFinset, List.mem_map] at hS
    obtain ⟨w, hwL, rfl⟩ := hS
    exact hmaps w hwL
  calc L.length = (L.map f).length := hlen
    _ = (L.map f).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- If `x` has fewer than `2^m` `(i,j)`-descriptions, then the online enumeration of its
descriptions stays strictly shorter than `2^m` at every time.  Hence the model code's rank
in the enumeration fits in `m` bits — the bound consumed by
`description_count_of_conditional_complexity_gap`. -/
theorem appearanceListCodes_length_lt_of_not_manyIJ {U : Map} {c : Code}
    (hc : IsCodeFor c U) {x : BitString} {i j m : ℕ}
    (hnm : ¬ ManyIJDescriptions U x i j m) (t : ℕ) :
    (appearanceListCodes c i j x t).length < 2 ^ m := by
  rw [ManyIJDescriptions, not_le] at hnm
  exact lt_of_le_of_lt (appearanceListCodes_length_le_descriptionsContaining hc i j x t) hnm

/-- Removing duplicates from a repetition-free list changes nothing. -/
theorem eraseDups_eq_self_of_nodup {α} [BEq α] [LawfulBEq α] {l : List α} (h : l.Nodup) :
  l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h1 := List.nodup_cons.mp h
    rw [List.eraseDups_cons]
    have hf : l.filter (fun b => !(b == a)) = l := by
      apply List.filter_eq_self.mpr
      intro x hx
      have hne : x ≠ a := ne_of_mem_of_not_mem hx h1.1
      simp [hne]
    rw [hf, ih h1.2]

/-- A repetition-free list is a prefix of the duplicate-free form of any extension
of it. -/
theorem prefix_eraseDups_append_of_nodup {α} [BEq α] [LawfulBEq α] (l1 l2 : List α) (h : l1.Nodup) :
  l1 <+: (l1 ++ l2).eraseDups := by
  rw [List.eraseDups_append]
  have heq : l1.eraseDups = l1 := eraseDups_eq_self_of_nodup h
  rw [heq]
  exact List.prefix_append _ _

/-- Each stage of the accumulated candidate list is a prefix of the next. -/
theorem appearanceListCodes_prefix (c : Code) (i j : ℕ) (x : BitString) (t : ℕ) :
    appearanceListCodes c i j x t <+: appearanceListCodes c i j x (t + 1) := by
  have hn : (appearanceListCodes c i j x t).Nodup := by
    cases t <;> exact nodup_eraseDups_bitString _
  have h_eq : appearanceListCodes c i j x (t + 1) =
      (appearanceListCodes c i j x t ++ candidateCodes c i j x (t + 1)).eraseDups := rfl
  rw [h_eq]
  exact prefix_eraseDups_append_of_nodup _ _ hn

/-- An earlier stage of the accumulated candidate list is a prefix of a later one. -/
theorem prefix_of_le_appearanceListCodes (c : Code) (i j : ℕ) (x : BitString) {t1 t2 : ℕ}
    (hle : t1 ≤ t2) :
  appearanceListCodes c i j x t1 <+: appearanceListCodes c i j x t2 := by
  induction hle with
  | refl => exact List.prefix_refl _
  | step ht ih => exact List.IsPrefix.trans ih (appearanceListCodes_prefix c i j x _)

/-- An element of a list occurs at some position, that is, after dropping fewer than
`|l|` entries the list starts with it. -/
theorem exists_drop_eq_cons_of_mem (l : List BitString) (a : BitString) (h : a ∈ l) :
  ∃ r l', r < l.length ∧ l.drop r = a :: l' := by
  induction l with
  | nil => cases h
  | cons x l ih =>
    cases h with
    | head _ =>
      exact ⟨0, l, by simp, rfl⟩
    | tail _ h =>
      obtain ⟨r, l', hr, hl'⟩ := ih h
      exact ⟨r + 1, l', Nat.succ_lt_succ hr, hl'⟩

/-- A code in the accumulated candidate list has an index at which the selector
returns exactly that code. -/
theorem indexSelectorFn_eq_code (c : Code) (i j : ℕ) (x : BitString) (code : BitString) (t0 : ℕ)
  (h_mem : code ∈ appearanceListCodes c i j x t0) :
  ∃ r < (appearanceListCodes c i j x t0).length,
    ∀ (y w : BitString), decodeFirst y = x → selNat w = i → selAlpha w = j → selH w = r →
        indexSelectorFn c y w = Part.some code := by
  obtain ⟨r, l', hr_lt, h_drop⟩ := exists_drop_eq_cons_of_mem _ _ h_mem
  refine ⟨r, hr_lt, ?_⟩
  intro y w hy hi hj hr
  apply Part.eq_some_iff.mpr
  unfold indexSelectorFn
  simp only [hy, hi, hj, hr]
  rw [Part.mem_bind_iff]
  refine ⟨Nat.find (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length),
    ?_, ?_⟩
  · let test : PFun Nat Bool := fun t =>
      Part.some (decide (r < (appearanceListCodes c i j x t).length))
    change Nat.find
      (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length) ∈ Nat.rfind test
    rw [Nat.mem_rfind]
    refine ⟨?_, ?_⟩
    · simp only [test, Part.mem_some_iff]
      symm
      rw [decide_eq_true_iff]
      exact Nat.find_spec
        (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length)
    · intro m hm
      simp only [test, Part.mem_some_iff]
      symm
      rw [decide_eq_false_iff_not]
      exact Nat.find_min
        (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length) hm
  · simp only [Part.mem_some_iff]
    have h_drop_eq :
        (appearanceListCodes c i j x
          (Nat.find (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length)))[r]! =
          (appearanceListCodes c i j x t0)[r]! := by
      have h_drop_eq : appearanceListCodes c i j x
          (Nat.find (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length)) <+:
          appearanceListCodes c i j x t0 := by
        exact prefix_of_le_appearanceListCodes c i j x ( Nat.find_le hr_lt );
      obtain ⟨ k, hk ⟩ := h_drop_eq;
      grind;
    convert h_drop_eq.symm using 1
    · replace h_drop := congr_arg List.head? h_drop; aesop
    · clear h_drop_eq
      have h_get :
          (appearanceListCodes c i j x
            (Nat.find (⟨t0, hr_lt⟩ : ∃ t,
              r < (appearanceListCodes c i j x t).length)))[r]? =
            (List.drop r (appearanceListCodes c i j x
              (Nat.find (⟨t0, hr_lt⟩ : ∃ t,
                r < (appearanceListCodes c i j x t).length)))).head? :=
        List.head?_drop.symm
      cases h : List.drop r (appearanceListCodes c i j x
        (Nat.find (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length)))
      · rw [List.getElem!_eq_getElem?_getD, h_get, h]
        rfl
      · rw [List.getElem!_eq_getElem?_getD, h_get, h]
        rfl

/-- A computable function that extracts the index from `y` to return the right model code.
If `x` has `< 2^m` `(i,j)`-descriptions, it is fully determined by
`x, K(x), i, j` and an `m`-bit index. -/
theorem description_count_of_conditional_complexity_gap (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n i j m kx : ℕ),
      x.length = n →
      x ∈ A →
      setComplexity U A hA = (i : ENat) →
      A.card ≤ 2 ^ j →
      HasPrefixComplexityValue U x kx →
      ¬ ManyIJDescriptions U x i j m →
      KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤
          (m + logSlack c (n + i + j) : ENat) := by
  obtain ⟨c_opt, hcRaw⟩ := Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  have hc_opt : IsCodeFor c_opt U := by
    exact hcRaw
  obtain ⟨c_kp, hkp⟩ := KP_partrec_cond_first_map_le U hU (indexSelectorFn c_opt)
    (partrec_indexSelectorFn c_opt)
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨C2, hC2⟩ := logSlack_linear_bound 2 3 7
  let C1 := C2 + c_kp + c_plain + c_len + 6
  use C1
  intro A hA x n i j m kx hn hx hi hj hkx h_not_many
  obtain ⟨t₀, ht₀⟩ := code_mem_appearanceListCodes hc_opt A hA x i j hx hi hj
  set y := prefixComplexityContext x kx
  set code := (codedUniformOn A hA).code
  have hy : decodeFirst y = x := by
    dsimp [y, prefixComplexityContext]
    rw [decodeFirst_pairCode]
  obtain ⟨r, hr_lt, hr_spec⟩ := indexSelectorFn_eq_code c_opt i j x code t₀ ht₀
  set w := richInput i j 0 r
  have hw_i : selNat w = i := selNat_richInput i j 0 r
  have hw_j : selAlpha w = j := selAlpha_richInput i j 0 r
  have hw_h : selH w = r := selH_richInput i j 0 r
  have h_some : indexSelectorFn c_opt y w = Part.some code := hr_spec y w hy hw_i hw_j hw_h
  have h_in : code ∈ indexSelectorFn c_opt y w := Part.eq_some_iff.mp h_some
  have h_bound1 : KP U code y ≤ KP U w y + (c_kp : ENat) := hkp w code y h_in
  have h_bound2 : KP U w y ≤ KPPlain U w + (c_plain : ENat) := hc_plain w y
  have h_bound3 : KPPlain U w ≤
      (w.length : ENat) + 2 * (Nat.bits w.length).length + c_len := hc_len w
  have h_w_len_r : w.length ≤ 2 * (Nat.bits i).length + 2 * (Nat.bits j).length +
      (Nat.bits r).length + 6 := by
    unfold w richInput selectorInput pack4
    simp [length_pairCode]
    omega
  have hr_lt_2m : r < 2 ^ m := lt_trans hr_lt
    (appearanceListCodes_length_lt_of_not_manyIJ hc_opt h_not_many t₀)
  have hr_lt_2i : r < 2 ^ (i + 1) := by
    have h1 := appearanceListCodes_length_le_descriptionsContaining hc_opt i j x t₀
    have h2 := Finset.card_filter_le (descriptionsWithComplexityLeAndSizeLe U i j) (fun S => x ∈ S)
    have h3 := card_descriptionsWithComplexityLeAndSizeLe U i j
    exact lt_of_lt_of_le hr_lt (h1.trans (h2.trans h3))
  let M := n + i + j
  have h_w_len_M : w.length ≤ 3 * M + 7 := by
    have hi_len : (Nat.bits i).length ≤ i := length_natBits_le i
    have hj_len : (Nat.bits j).length ≤ j := length_natBits_le j
    have hr_len : (Nat.bits r).length ≤ i + 1 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr hr_lt_2i
    omega
  have h_slack : c_kp + c_plain + c_len + 2 * (Nat.bits i).length + 2 * (Nat.bits j).length + 6 + 2
      * (Nat.bits w.length).length ≤ logSlack C1 M := by
    have hw1 : (Nat.bits w.length).length ≤ (Nat.bits (3 * M + 7)).length := by
      have h : w.length < 2 ^ (Nat.size (3 * M + 7)) :=
        lt_of_le_of_lt h_w_len_M (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hw3 : 2 * (Nat.bits (3 * M + 7)).length ≤ logSlack 2 (3 * M + 7) := by
      unfold logSlack
      omega
    have hw5 : logSlack C2 M = C2 * (Nat.bits M).length + C2 := rfl
    have hw6 : logSlack C1 M =
        (C2 + c_kp + c_plain + c_len + 6) * (Nat.bits M).length +
          (C2 + c_kp + c_plain + c_len + 6) := rfl
    have hiM : i ≤ M := by omega
    have hjM : j ≤ M := by omega
    have hi_len : (Nat.bits i).length ≤ (Nat.bits M).length := by
      have h : i < 2 ^ (Nat.size M) := lt_of_le_of_lt hiM (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hj_len : (Nat.bits j).length ≤ (Nat.bits M).length := by
      have h : j < 2 ^ (Nat.size M) := lt_of_le_of_lt hjM (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hC2_M := hC2 M
    nlinarith
  calc KP U code y ≤ KP U w y + c_kp := h_bound1
    _ ≤ KPPlain U w + c_plain + c_kp := by gcongr
    _ ≤ (w.length : ENat) + 2 * (Nat.bits w.length).length + c_len + c_plain + c_kp := by gcongr
    _ ≤ ((2 * (Nat.bits i).length + 2 * (Nat.bits j).length + (Nat.bits r).length + 6 : ℕ) : ENat) +
        2 * (Nat.bits w.length).length + c_len + c_plain + c_kp := by
      have h : w.length + 2 * w.length.bits.length + c_len + c_plain + c_kp ≤
          (2 * i.bits.length + 2 * j.bits.length + r.bits.length + 6) +
            2 * w.length.bits.length + c_len + c_plain + c_kp := by omega
      exact_mod_cast h
    _ ≤ ((2 * (Nat.bits i).length + 2 * (Nat.bits j).length + m + 6 : ℕ) : ENat) + 2 *
        (Nat.bits w.length).length + c_len + c_plain + c_kp := by
      have h_r_m : (Nat.bits r).length ≤ m := by
        rw [Nat.size_eq_bits_len]
        exact Nat.size_le.mpr hr_lt_2m
      have h : (2 * i.bits.length + 2 * j.bits.length + r.bits.length + 6) +
          2 * w.length.bits.length + c_len + c_plain + c_kp ≤
            (2 * i.bits.length + 2 * j.bits.length + m + 6) +
              2 * w.length.bits.length + c_len + c_plain + c_kp := by omega
      exact_mod_cast h
    _ = (m : ENat) + (c_kp + c_plain + c_len + 2 * (Nat.bits i).length +
        2 * (Nat.bits j).length + 6 + 2 * (Nat.bits w.length).length : ℕ) := by
      push_cast
      ring
    _ ≤ (m : ENat) + logSlack C1 M := by gcongr

/-- If `x ∈ A`, `setComplexity U A hA = i`, and `A.card ≤ 2^j`, then `x` has at
least `2^0 = 1` `(i, j)`-description. -/
theorem manyIJDescriptions_zero (U : Map) (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
    (i j : ℕ)
    (hxA : x ∈ A) (h_comp : setComplexity U A hA = (i : ENat)) (h_size : A.card ≤ 2 ^ j) :
    ManyIJDescriptions U x i j 0 := by
  unfold ManyIJDescriptions
  rw [pow_zero]
  refine Finset.card_pos.mpr ?_
  refine ⟨A, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hxA⟩
  unfold descriptionsWithComplexityLeAndSizeLe
  rw [Finset.mem_filter]
  refine ⟨?_, h_size⟩
  exact mem_descriptionsWithComplexityLe_of_complexity hA (by rw [h_comp])

/-
Arithmetic lemma for bounding the sum of two log-slack terms into a single log-slack term.
-/

end Kolmogorov
