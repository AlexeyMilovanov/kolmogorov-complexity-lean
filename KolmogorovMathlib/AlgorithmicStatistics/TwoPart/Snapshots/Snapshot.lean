import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions

/-!
# Description Snapshot (Phase D infrastructure)

This module builds the computable enumeration bridge for the description
universe. It mirrors the `snapshotCodes` machinery to the level of
`descriptionsWithComplexityLeAndSizeLe` and `richDescriptionElements`,
showing that these rich elements can be isolated computably given the halting
count.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Computable test if a code represents a canonical uniform distribution. -/
def isCanonicalUniformCodeBool (c : BitString) : Bool :=
  let S := ((decodeDistributionData c).map CodedDistributionEntry.point).toFinset
  decide (S.Nonempty ∧ c = codedDistributionDataCode ((canonicalFinsetList S).map fun x =>
    { point := x, mass := ratMassInvNat (max 1 S.card) (by positivity) }))

/-
The computable test accurately reflects `isCanonicalUniformCode`.
-/
theorem isCanonicalUniformCodeBool_iff (c : BitString) :
    isCanonicalUniformCodeBool c = true ↔ isCanonicalUniformCode c := by
  constructor <;> intro h;
  · -- Let `S` be the finset of points decoded from `c`. Unfolding `h` gives
    -- its nonemptiness and the equality of `c` with the corresponding canonical code.
    set S := ((decodeDistributionData c).map CodedDistributionEntry.point).toFinset with hS_def
    obtain ⟨hSne, hc_eq⟩ : S.Nonempty ∧
        c = codedDistributionDataCode ((canonicalFinsetList S).map fun x =>
          { point := x, mass := ratMassInvNat (max 1 S.card) (by positivity) }) := by
      rw [hS_def]
      simpa only [isCanonicalUniformCodeBool, decide_eq_true_eq] using h
    -- Since `S.Nonempty`, `max 1 S.card = S.card`, so by `codedUniformOn_code_eq` the right side
    --   equals `(codedUniformOn S hSne).code`; hence `c = (codedUniformOn S hSne).code`.
    have hc_eq' : c = (codedUniformOn S hSne).code := by
      convert hc_eq using 1
      convert codedUniformOn_code_eq S hSne using 1
      simp only [max_eq_right (show 1 ≤ _ from Finset.card_pos.mpr hSne)]
    -- Now `codedUniformOn S hSne` is a probability (`codedUniformOn_isProbability`), so
    --   `probModelOfCode c = probModelOfCode (codedUniformOn S hSne).code = codedUniformOn S hSne`
    --   by `probModelOfCode_eq`.
    have h_prob : probModelOfCode c = codedUniformOn S hSne := by
      exact probModelOfCode_eq ( codedUniformOn_isProbability S hSne ) ▸ hc_eq'.symm ▸ rfl;
    refine ⟨?_, ?_⟩
    · convert hSne using 1
      exact h_prob.symm ▸ codedUniformOn_support S hSne
    · convert hc_eq'
      exact h_prob.symm ▸ codedUniformOn_support S hSne
  · obtain ⟨hSne, hc⟩ := h;
    have hS : ((decodeDistributionData c).map CodedDistributionEntry.point).toFinset =
        (probModelOfCode c).support := by
      rw [hc, dataPoints_codedUniformOn, canonicalFinsetList_toFinset,
        probModelOfCode_eq (codedUniformOn_isProbability _ _), codedUniformOn_support]
    unfold isCanonicalUniformCodeBool
    simp only [hS, decide_eq_true_eq]
    constructor
    · exact hSne
    · convert hc using 1
      convert (codedUniformOn_code_eq _ hSne).symm using 1
      simp only [max_eq_right (show 1 ≤ _ from Finset.card_pos.mpr hSne)]

/-
`isCanonicalUniformCodeBool` is a primitive recursive function.
-/
theorem isCanonicalUniformCodeBool_primrec : Primrec isCanonicalUniformCodeBool := by
  have h_conj : Primrec (fun c : BitString => decide
      (((decodeDistributionData c).map CodedDistributionEntry.point).toFinset.Nonempty)) := by
    have h_card : Primrec (fun c : BitString =>
        (List.map CodedDistributionEntry.point (decodeDistributionData c)).toFinset.card) := by
      have h_len : Primrec (fun c : BitString => (canonicalFinsetList
          ((decodeDistributionData c).map CodedDistributionEntry.point).toFinset).length) := by
        have h_map : Primrec (fun c : BitString =>
            (decodeDistributionData c).map CodedDistributionEntry.point) :=
          Primrec.list_map decodeDistributionData_primrec (entry_point_primrec.comp Primrec.snd)
        exact Primrec.list_length.comp (canonicalFinsetList_toFinset_primrec.comp h_map)
      exact h_len.of_eq (fun _ => Finset.length_sort _)
    exact (PrimrecPred.decide (Primrec.nat_lt.comp (Primrec.const 0) h_card)).of_eq
      (fun c => by simp [Finset.card_pos])
  have h_eq : Primrec
      (fun c : BitString => decide (c = codedDistributionDataCode
        ((canonicalFinsetList ((decodeDistributionData c).map
          CodedDistributionEntry.point).toFinset).map fun x =>
            ({ point := x, mass := ratMassInvNat (max 1 (canonicalFinsetList
              ((decodeDistributionData c).map CodedDistributionEntry.point).toFinset).length)
                (by positivity)} : CodedDistributionEntry)))) := by
    have h_pair : Primrec
        (fun c : BitString => (c, codedDistributionDataCode
          ((canonicalFinsetList ((decodeDistributionData c).map
            CodedDistributionEntry.point).toFinset).map fun x =>
              ({ point := x, mass := ratMassInvNat (max 1 (canonicalFinsetList
                ((decodeDistributionData c).map CodedDistributionEntry.point).toFinset).length)
                  (by positivity)} : CodedDistributionEntry)))) := by
      refine Primrec.pair Primrec.id ?_
      convert codedUniformEncoder_primrec.comp _ using 1
      convert canonicalFinsetList_toFinset_primrec.comp _ using 1
      exact Primrec.list_map decodeDistributionData_primrec (entry_point_primrec.comp Primrec.snd)
    convert Primrec.eq.comp (Primrec.fst.comp h_pair) (Primrec.snd.comp h_pair) using 1
    simp +decide [PrimrecPred]
  convert Primrec.cond _ h_conj (Primrec.const false) using 1
  rotate_left
  · exact fun c => decide (c = codedDistributionDataCode (List.map (fun x =>
      ({ point := x, mass := ratMassInvNat (max 1 (List.length (canonicalFinsetList (List.map
        CodedDistributionEntry.point (decodeDistributionData c)).toFinset))) (by positivity) } :
          CodedDistributionEntry)) (canonicalFinsetList (List.map CodedDistributionEntry.point
            (decodeDistributionData c)).toFinset)))
  · convert h_eq using 1
  · ext
    unfold isCanonicalUniformCodeBool
    simpa only [length_canonicalFinsetList, List.toFinset_nonempty_iff, ne_eq,
      List.map_eq_nil_iff, Bool.decide_and, decide_not, Bool.cond_false_right] using
      Bool.and_comm _ _

/-- Supports of the canonical-uniform codes appearing in `snapshotCodes c i t`. -/
def snapshotDescriptions (c : Code) (i t : ℕ) : Finset (Finset BitString) :=
  ((snapshotCodes c i t).filter isCanonicalUniformCodeBool).toFinset.image
    (fun w => ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset)

/-- `snapshotDescriptions` is primitive recursive.

NOTE (faithfulness caveat): previously stated with `(snapshotDescriptions ...).toList`
which used the noncomputable `Finset.toList`. This has been restated faithfully
using the computable canonical enumeration. -/
theorem snapshotDescriptions_primrec (c : Code) :
    Primrec (fun p : ℕ × ℕ =>
      (canonicalFinsetList ((snapshotCodes c p.1 p.2).filter
        isCanonicalUniformCodeBool).toFinset).map
          (fun w => canonicalFinsetList (((decodeDistributionData w).map
            CodedDistributionEntry.point).toFinset))) := by
  have h1 : Primrec (fun p : ℕ × ℕ => snapshotCodes c p.1 p.2) :=
    snapshotCodes_primrec c
  have h2 : Primrec (fun p : ℕ × ℕ => (snapshotCodes c p.1 p.2).filter
      isCanonicalUniformCodeBool) :=
    list_filter_primrec h1 (isCanonicalUniformCodeBool_primrec.comp Primrec.snd)
  have h3 : Primrec (fun p : ℕ × ℕ => canonicalFinsetList
      ((snapshotCodes c p.1 p.2).filter isCanonicalUniformCodeBool).toFinset) :=
    canonicalFinsetList_toFinset_primrec.comp h2
  have h4 : Primrec
      (fun w : BitString => canonicalFinsetList (((decodeDistributionData w).map
        CodedDistributionEntry.point).toFinset)) := by
    have h4_1 : Primrec (fun w : BitString =>
        (decodeDistributionData w).map CodedDistributionEntry.point) :=
      Primrec.list_map decodeDistributionData_primrec (entry_point_primrec.comp Primrec.snd)
    exact canonicalFinsetList_toFinset_primrec.comp h4_1
  exact Primrec.list_map h3 (h4.comp Primrec.snd)

/-- Computable mirror of `descriptionsWithComplexityLeAndSizeLe`. -/
def snapshotDescriptionsAndSizeLe (c : Code) (i j t : ℕ) : Finset (Finset BitString) :=
  (snapshotDescriptions c i t).filter (fun S => S.card ≤ 2 ^ j)

/-- `snapshotDescriptionsAndSizeLe` is primitive recursive.

NOTE (faithfulness caveat): restated faithfully to use the computable canonical list
rather than the noncomputable `Finset.toList`. -/
theorem snapshotDescriptionsAndSizeLe_primrec (c : Code) :
    Primrec (fun p : (ℕ × ℕ) × ℕ =>
      ((canonicalFinsetList ((snapshotCodes c p.1.1 p.1.2).filter
        isCanonicalUniformCodeBool).toFinset).map
          (fun w => canonicalFinsetList (((decodeDistributionData w).map
            CodedDistributionEntry.point).toFinset))).filter
              (fun S => S.length ≤ 2 ^ p.2)) := by
  have h1 : Primrec (fun p : (ℕ × ℕ) × ℕ => snapshotCodes c p.1.1 p.1.2) :=
    (snapshotCodes_primrec c).comp Primrec.fst
  have h2 : Primrec (fun p : (ℕ × ℕ) × ℕ =>
      (snapshotCodes c p.1.1 p.1.2).filter isCanonicalUniformCodeBool) :=
    list_filter_primrec h1 (isCanonicalUniformCodeBool_primrec.comp Primrec.snd)
  have h3 : Primrec (fun p : (ℕ × ℕ) × ℕ => canonicalFinsetList
      ((snapshotCodes c p.1.1 p.1.2).filter isCanonicalUniformCodeBool).toFinset) :=
    canonicalFinsetList_toFinset_primrec.comp h2
  have h4 : Primrec
      (fun w : BitString => canonicalFinsetList (((decodeDistributionData w).map
        CodedDistributionEntry.point).toFinset)) := by
    have h4_1 : Primrec (fun w : BitString =>
        (decodeDistributionData w).map CodedDistributionEntry.point) :=
      Primrec.list_map decodeDistributionData_primrec (entry_point_primrec.comp Primrec.snd)
    exact canonicalFinsetList_toFinset_primrec.comp h4_1
  have h5 : Primrec (fun p : (ℕ × ℕ) × ℕ =>
      (canonicalFinsetList ((snapshotCodes c p.1.1 p.1.2).filter
        isCanonicalUniformCodeBool).toFinset).map
          (fun w => canonicalFinsetList (((decodeDistributionData w).map
            CodedDistributionEntry.point).toFinset))) :=
    Primrec.list_map h3 (h4.comp Primrec.snd)
  have h6 : Primrec₂ (fun (p : (ℕ × ℕ) × ℕ) (S : List BitString) =>
      decide (S.length ≤ 2 ^ p.2)) := by
    have hlen : Primrec (fun (p : ((ℕ × ℕ) × ℕ) × List BitString) => p.2.length) :=
      Primrec.list_length.comp Primrec.snd
    have hpow2 : Primrec (fun (p : ((ℕ × ℕ) × ℕ) × List BitString) => 2 ^ p.1.2) :=
      primrec_two_pow_aux.comp (Primrec.snd.comp Primrec.fst)
    have h7 : PrimrecPred (fun a : ((ℕ × ℕ) × ℕ) × List BitString => a.2.length ≤ 2 ^ a.1.2) :=
      Primrec.nat_le.comp hlen hpow2
    exact PrimrecPred.decide h7
  exact list_filter_primrec h5 h6

/-- Computable mirror of `richDescriptionElements`. -/
def snapshotRichElements (c : Code) (i j k t : ℕ) : Finset BitString :=
  ((snapshotDescriptionsAndSizeLe c i j t).biUnion id).filter
    (fun y => 2 ^ k ≤ ((snapshotDescriptionsAndSizeLe c i j t).filter (fun S => y ∈ S)).card)

/-- Computable list mirror of the size-restricted description universe:
the canonical list of canonical-uniform codes, each mapped to the canonical list
of its support, filtered by the size budget.  Each entry is `canonicalFinsetList`
of a description appearing in `snapshotDescriptionsAndSizeLe`. -/
def snapshotDescList (c : Code) (i j t : ℕ) : List (List BitString) :=
  ((canonicalFinsetList ((snapshotCodes c i t).filter
    isCanonicalUniformCodeBool).toFinset).map
      (fun w => canonicalFinsetList (((decodeDistributionData w).map
        CodedDistributionEntry.point).toFinset))).filter
          (fun S => decide (S.length ≤ 2 ^ j))

/-- Computable list mirror of `snapshotRichElements`: flatten the description
lists and keep the points contained in at least `2 ^ k` distinct descriptions
(counted via `List.countP` on the nodup description list). -/
def snapshotRichElementsList (c : Code) (i j k t : ℕ) : List BitString :=
  (snapshotDescList c i j t).flatten.filter
    (fun y => decide (2 ^ k ≤ (snapshotDescList c i j t).countP (fun S => decide (y ∈ S))))

/-
The list-of-lists mirror `snapshotDescList`, read as a finset of finsets via
`toFinset`, equals the abstract size-restricted description universe; moreover
the underlying list of descriptions has no duplicates.  This packages the only
combinatorial input needed for the rich-element bridge: distinct canonical-uniform
codes give distinct supports, so the description list faithfully enumerates the
finset of descriptions.
-/
theorem snapshotDescList_nodup_map_toFinset (c : Code) (i j t : ℕ) :
    ((snapshotDescList c i j t).map List.toFinset).Nodup ∧
      ((snapshotDescList c i j t).map List.toFinset).toFinset
        = snapshotDescriptionsAndSizeLe c i j t := by
  refine ⟨ List.nodup_map_iff_inj_on ?_ |>.2 ?_, ?_ ⟩;
  · refine List.Nodup.filter _ ?_;
    rw [ List.nodup_map_iff_inj_on ];
    · intro x hx y hy hxy
      have hxmem : x ∈ snapshotCodes c i t ∧ isCanonicalUniformCodeBool x = true := by
        simpa only [mem_canonicalFinsetList, List.mem_toFinset, List.mem_filter] using hx
      have hymem : y ∈ snapshotCodes c i t ∧ isCanonicalUniformCodeBool y = true := by
        simpa only [mem_canonicalFinsetList, List.mem_toFinset, List.mem_filter] using hy
      have hxcanonical := hxmem.2
      have hycanonical := hymem.2
      have hsupport :
          ((decodeDistributionData x).map CodedDistributionEntry.point).toFinset =
            ((decodeDistributionData y).map CodedDistributionEntry.point).toFinset := by
        simpa only [canonicalFinsetList_toFinset] using congrArg List.toFinset hxy
      simp only [isCanonicalUniformCodeBool, decide_eq_true_eq] at hxcanonical hycanonical
      rw [hxcanonical.2, hycanonical.2]
      simp only [hsupport]
    · exact canonicalFinsetList_nodup _;
  · intro x hx y hy hxy
    obtain ⟨hxmap, _⟩ := List.mem_filter.mp hx
    obtain ⟨hymap, _⟩ := List.mem_filter.mp hy
    obtain ⟨wx, _, hwx⟩ := List.mem_map.mp hxmap
    obtain ⟨wy, _, hwy⟩ := List.mem_map.mp hymap
    calc
      x = canonicalFinsetList x.toFinset := by rw [← hwx, canonicalFinsetList_toFinset]
      _ = canonicalFinsetList y.toFinset := congrArg canonicalFinsetList hxy
      _ = y := by rw [← hwy, canonicalFinsetList_toFinset]
  · ext
    unfold snapshotDescList snapshotDescriptionsAndSizeLe
    simp only [List.mem_toFinset, List.mem_map]
    unfold snapshotDescriptions
    simp only [List.mem_filter, List.mem_map, Finset.mem_filter, Finset.mem_image,
      List.mem_toFinset, mem_canonicalFinsetList, decide_eq_true_eq]
    constructor
    · rintro ⟨a, ⟨⟨w, hw, hwa⟩, ha⟩, haa⟩
      refine ⟨⟨w, hw, ?_⟩, ?_⟩
      · rw [← haa, ← hwa, canonicalFinsetList_toFinset]
      · rw [← haa, ← hwa, canonicalFinsetList_toFinset,
          ← length_canonicalFinsetList, hwa]
        exact ha
    · rintro ⟨⟨w, hw, hwa⟩, ha⟩
      refine ⟨canonicalFinsetList
        ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset, ?_⟩
      refine ⟨⟨⟨w, hw, rfl⟩, ?_⟩, (canonicalFinsetList_toFinset _).trans hwa⟩
      rw [length_canonicalFinsetList, hwa]
      exact ha

/-
The list mirror `snapshotRichElementsList`, read as a finset via `toFinset`,
equals `snapshotRichElements`.  This is the structural bridge that lets the
primitive-recursive list construction stand in for the abstract rich set.
-/
theorem snapshotRichElementsList_toFinset (c : Code) (i j k t : ℕ) :
    (snapshotRichElementsList c i j k t).toFinset = snapshotRichElements c i j k t := by
  ext y
  simp only [snapshotRichElementsList, List.filter_flatten, List.mem_toFinset, List.mem_flatten,
    List.mem_map, exists_exists_and_eq_and, List.mem_filter, decide_eq_true_eq,
    snapshotRichElements, Finset.mem_filter, Finset.mem_biUnion, id_eq]
  constructor <;> intro h
  · obtain ⟨l, hl_mem, hy_mem, h_count_le⟩ := h
    constructor
    · use l.toFinset
      have h_nodup := snapshotDescList_nodup_map_toFinset c i j t
      simp_all +decide only [snapshotDescriptionsAndSizeLe, Finset.mem_filter, snapshotDescList,
        List.toFinset_filter, List.mem_filter, List.mem_map, mem_canonicalFinsetList,
        List.mem_toFinset, decide_eq_true_eq, and_true]
      unfold snapshotDescriptions; aesop
    · have h_countP_eq_card : ∀ (l : List (List BitString)),
          List.Nodup (List.map List.toFinset l) → ∀
          (y : BitString), List.countP (fun S => decide (y ∈ S)) l = Finset.card
          (Finset.filter (fun S => y ∈ S) (List.toFinset (List.map List.toFinset l))) := by
        intros l hl y
        induction l <;> simp_all +decide only [List.countP_nil, List.map_nil, List.toFinset_nil,
          Finset.filter_empty, Finset.card_empty, List.map_cons, List.nodup_cons, List.mem_map,
          not_exists, not_and, List.countP_cons, decide_eq_true_eq, List.toFinset_cons,
          forall_const]
        split_ifs <;> simp_all +decide only [Finset.filter_insert, List.mem_toFinset, ↓reduceIte,
          Finset.mem_filter, List.mem_map, and_true, not_exists, not_and, not_false_eq_true,
          implies_true, Finset.card_insert_of_notMem, add_zero]
      rw [h_countP_eq_card _ (snapshotDescList_nodup_map_toFinset c i j t |>.1) y] at h_count_le
      rw [snapshotDescList_nodup_map_toFinset c i j t |>.2] at h_count_le
      exact h_count_le
  · obtain ⟨⟨S, hS₁, hS₂⟩, hS₃⟩ := h
    have hS₄ : ∃ a ∈ snapshotDescList c i j t, S = a.toFinset := by
      have := snapshotDescList_nodup_map_toFinset c i j t
      simp_all +decide only [snapshotDescriptionsAndSizeLe, Finset.mem_filter]
      have hS_mem : S ∈ (List.map List.toFinset (snapshotDescList c i j t)).toFinset := by
        rw [this.2]
        exact Finset.mem_filter.mpr hS₁
      obtain ⟨a, ha, haS⟩ := List.mem_map.mp (List.mem_toFinset.mp hS_mem)
      exact ⟨a, ha, haS.symm⟩
    obtain ⟨a, ha₁, rfl⟩ := hS₄
    have h_card_le_length : ∀ {l : List (List BitString)}, List.Nodup (List.map List.toFinset l) → ∀
        y, (Finset.filter (fun S => y ∈ S) (List.toFinset (List.map List.toFinset l))).card ≤
        (List.filter (fun S => decide (y ∈ S)) l).length := by
      intros l hl y
      induction l <;> simp_all +decide only [List.map_nil, List.toFinset_nil,
        Finset.filter_empty, Finset.card_empty, List.filter_nil, List.length_nil,
        le_refl, List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and,
        List.toFinset_cons, List.filter_cons, decide_eq_true_eq, forall_const]
      split_ifs <;> simp_all +decide only [Finset.filter_insert, List.mem_toFinset, ↓reduceIte,
        Finset.mem_filter, List.mem_map, and_true, not_exists, not_and, not_false_eq_true,
        implies_true, Finset.card_insert_of_notMem, List.length_cons, add_le_add_iff_right]
    have h_le := h_card_le_length (snapshotDescList_nodup_map_toFinset c i j t |>.1) y
    rw [snapshotDescList_nodup_map_toFinset c i j t |>.2] at h_le
    rw [← List.countP_eq_length_filter] at h_le
    exact ⟨a, ha₁, List.mem_toFinset.mp hS₂, le_trans hS₃ h_le⟩

/-
The list mirror `snapshotRichElementsList` is primitive recursive in its
numeric parameters.  Pure `Primrec` plumbing over the already-established
`snapshotDescriptionsAndSizeLe_primrec`, `list_filter_primrec`,
`list_countP_primrec`, and `Primrec.list_flatten`.
-/
theorem snapshotDescList_primrec (c : Code) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => snapshotDescList c p.1.1 p.2 p.1.2) :=
  (snapshotDescriptionsAndSizeLe_primrec c).of_eq (fun _ => rfl)

/-- The stage list of rich description elements is primitive recursive in its
parameters. -/
theorem snapshotRichElementsList_primrec (c : Code) :
    Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      snapshotRichElementsList c p.1.1 p.1.2 p.2.1 p.2.2) := by
  apply Primrec.of_eq;
  rotate_right;
  · exact fun p => (snapshotDescList c p.1.1 p.1.2 p.2.2).flatten.filter
      (fun y => decide (2 ^ p.2.1 ≤
        (snapshotDescList c p.1.1 p.1.2 p.2.2).countP (fun S => decide (y ∈ S))))
  · convert list_filter_primrec _ _ using 1
    · have h1 : Primrec (fun p : (ℕ × ℕ) × ℕ =>
          ((canonicalFinsetList ((snapshotCodes c p.1.1 p.1.2).filter
            isCanonicalUniformCodeBool).toFinset).map
              (fun w => canonicalFinsetList (((decodeDistributionData w).map
                CodedDistributionEntry.point).toFinset))).filter
                  (fun S => S.length ≤ 2 ^ p.2)) :=
        (snapshotDescriptionsAndSizeLe_primrec c).of_eq (fun _ => rfl)
      have hdesc : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
          snapshotDescList c p.1.1 p.1.2 p.2.2) :=
        (h1.comp (Primrec.pair
          (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst))).of_eq (fun _ => by simp [snapshotDescList])
      exact Primrec.list_flatten.comp hdesc
    · have h_countP : Primrec₂ (fun (p : (ℕ × ℕ) × ℕ × ℕ) (y : BitString) =>
          (snapshotDescList c p.1.1 p.1.2 p.2.2).countP
            (fun S => decide (y ∈ S))) := by
        apply list_countP_primrec
        · convert snapshotDescriptionsAndSizeLe_primrec c using 1
          constructor <;> intro h
          · convert snapshotDescriptionsAndSizeLe_primrec c using 1
          · convert h.comp _ using 1
            rotate_left
            · exact fun p => ((p.1.1.1, p.1.2.2), p.1.1.2)
            · exact Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp
                Primrec.fst)) (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
                  (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
            · exact funext fun x => rfl
        · exact bitString_mem_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
      have h_twoPow : Primrec (fun (p : (ℕ × ℕ) × ℕ × ℕ) => 2 ^ p.2.1) := by
        exact primrec_two_pow_aux.comp (Primrec.fst.comp Primrec.snd)
      exact (PrimrecPred.decide (Primrec.nat_le.comp (h_twoPow.comp Primrec.fst)
        (h_countP.comp Primrec.fst Primrec.snd))).to₂
  · unfold snapshotRichElementsList; aesop

/-- `snapshotRichElements` is primitive recursive.

NOTE (faithfulness caveat): previously stated with `(snapshotRichElements ...).toList`
which used the noncomputable `Finset.toList`. This has been restated faithfully
using the computable `canonicalFinsetList` enumeration. -/
theorem snapshotRichElements_primrec (c : Code) :
    Primrec
      (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
        canonicalFinsetList (snapshotRichElements c p.1.1 p.1.2 p.2.1 p.2.2)) := by
  have hrw : (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
        canonicalFinsetList (snapshotRichElements c p.1.1 p.1.2 p.2.1 p.2.2))
      = (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
        canonicalFinsetList ((snapshotRichElementsList c p.1.1 p.1.2 p.2.1 p.2.2).toFinset)) := by
    funext p; rw [snapshotRichElementsList_toFinset]
  rw [hrw]
  exact canonicalFinsetList_toFinset_primrec.comp (snapshotRichElementsList_primrec c)

/-
**Core of the stabilization bridge**: at the stabilization time `t₀` the
computable snapshot description universe coincides with the abstract description
universe `descriptionsWithComplexityLe`.  Both inclusions go through the
canonical-uniform characterization `isCanonicalUniformCodeBool_iff`:
* a canonical-uniform code in `modelsWithComplexityLe U i` is the output
  `modelCodeOfProgram U p` of a bounded program; being a real probability code it
  halts, so `code_mem_snapshot_of_max` places it into `snapshotCodes c i t₀`;
* conversely a canonical-uniform code in `snapshotCodes c i t₀` is
  `runOut c t₀ p = some w` of a bounded program, so by `runOut_sound`
  `modelCodeOfProgram U p = w` lands it in `modelsWithComplexityLe U i`.
On shared canonical-uniform codes the support maps agree.
-/
theorem snapshotDescriptions_eq_descriptionsWithComplexityLe {c : Code} {U : Map}
    (hc : IsCodeFor c U) (i : ℕ) (t₀ : ℕ)
    (hmax : ∀ t', countHalts c i t' ≤ countHalts c i t₀) :
    snapshotDescriptions c i t₀ = descriptionsWithComplexityLe U i := by
  ext T;
  constructor <;> intro hT;
  · unfold snapshotDescriptions at hT
    simp_all +decide only [List.toFinset_filter, Finset.mem_image, Finset.mem_filter,
      List.mem_toFinset]
    obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ := hT
    unfold descriptionsWithComplexityLe
    simp_all +decide only [Finset.mem_biUnion]
    use a
    simp_all +decide only [modelsWithComplexityLe, Finset.mem_image, List.mem_toFinset]
    obtain ⟨ p, hp₁, hp₂ ⟩ := List.mem_filterMap.mp ha₁;
    refine ⟨ ⟨ p, hp₁, ?_ ⟩, ?_ ⟩;
    · have := runOut_sound hc hp₂
      simp_all +decide only [modelCodeOfProgram]
      cases this ; aesop;
    · rw [ ite_eq_left ];
      · rw [isCanonicalUniformCodeBool_iff] at ha₂
        obtain ⟨hSne, hc⟩ := ha₂
        rw [Finset.mem_singleton, hc, dataPoints_codedUniformOn, canonicalFinsetList_toFinset,
          probModelOfCode_eq (codedUniformOn_isProbability _ _), codedUniformOn_support]
      · exact isCanonicalUniformCodeBool_iff a |>.1 ha₂;
  · obtain ⟨c', hc', hc'_T⟩ : ∃ c' ∈ modelsWithComplexityLe U i, isCanonicalUniformCode c' ∧
      (probModelOfCode c').support = T := by
      contrapose! hT
      simp_all +decide only [ne_eq, descriptionsWithComplexityLe, Finset.mem_biUnion, not_exists,
        not_and]
      grind;
    obtain ⟨p, hp, hp'⟩ : ∃ p ∈ boundedPrograms i, produces U p [] c' := by
      obtain ⟨ p, hp, hp' ⟩ := Finset.mem_image.mp hc';
      unfold modelCodeOfProgram at hp'
      simp_all +decide only [List.mem_toFinset, produces]
      split_ifs at hp' <;> simp_all +decide only [List.nil_eq, Part.mem_eq]
      · exact ⟨ p, hp, _, hp' ⟩;
      · have := hc'_T.1
        simp_all +decide only [isCanonicalUniformCode, List.nil_eq]
        obtain ⟨ h, hh ⟩ := this
        have := congr_arg List.length hh
        simp +decide only [codedUniformOn_code_eq, List.length_nil, List.length_eq_zero_iff] at this
        cases h : canonicalFinsetList T <;> simp_all +decide only [exists_const, and_self,
          List.map_nil, codedDistributionDataCode, List.cons_ne_self, List.map_cons, reduceCtorEq]
    have h_code_mem_snapshot : c' ∈ snapshotCodes c i t₀ := by
      exact code_mem_snapshot_of_max hc i t₀ hmax hp hp';
    have h_code_mem_snapshot2 : isCanonicalUniformCodeBool c' := by
      exact isCanonicalUniformCodeBool_iff c' |>.2 hc'_T.1;
    have h_code_mem_snapshot3 :
        ((decodeDistributionData c').map CodedDistributionEntry.point).toFinset =
        (probModelOfCode c').support := by
      obtain ⟨hSne, hc⟩ := hc'_T.left
      rw [hc, dataPoints_codedUniformOn, canonicalFinsetList_toFinset,
        probModelOfCode_eq (codedUniformOn_isProbability _ _), codedUniformOn_support]
    unfold snapshotDescriptions; aesop;

/-- The size-restricted snapshot universe coincides with the abstract one at the
stabilization time, by filtering both sides of
`snapshotDescriptions_eq_descriptionsWithComplexityLe`. -/
theorem snapshotDescriptionsAndSizeLe_eq_descriptionsWithComplexityLeAndSizeLe {c : Code} {U : Map}
    (hc : IsCodeFor c U) (i j : ℕ) (t₀ : ℕ)
    (hmax : ∀ t', countHalts c i t' ≤ countHalts c i t₀) :
    snapshotDescriptionsAndSizeLe c i j t₀ = descriptionsWithComplexityLeAndSizeLe U i j := by
  unfold snapshotDescriptionsAndSizeLe descriptionsWithComplexityLeAndSizeLe
  rw [snapshotDescriptions_eq_descriptionsWithComplexityLe hc i t₀ hmax]

/--
**Stabilization bridge**: at the stabilization time `t₀` from `exists_max_countHalts`,
the computable snapshot rich set exactly equals the true abstract rich set.
This bridges the primitive recursive selector to the abstract combinatorics.
-/
theorem snapshotRichElements_eq_richDescriptionElements {c : Code} {U : Map} (hc : IsCodeFor c U)
    (i j k : ℕ) (t₀ : ℕ) (hmax : ∀ t', countHalts c i t' ≤ countHalts c i t₀) :
    snapshotRichElements c i j k t₀ = richDescriptionElements U i j k := by
  unfold snapshotRichElements richDescriptionElements
  rw [snapshotDescriptionsAndSizeLe_eq_descriptionsWithComplexityLeAndSizeLe hc i j t₀ hmax]

/-- The selector input packing the three profile parameters and the halting-count
advice. -/
def richInput (i j k h : ℕ) : BitString :=
  selectorInput i j k h

end Kolmogorov
