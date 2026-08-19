import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-!
# Description Snapshot (Phase D infrastructure)

This module builds the computable enumeration bridge for the description
universe. It mirrors the `snapshotCodes` machinery to the level of
`descriptionsWithComplexityLeAndSizeLe` and `richDescriptionElements`,
showing that these rich elements can be isolated computably given the halting
count.
-/

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
      twoPow_primrec.comp (Primrec.snd.comp Primrec.fst)
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

theorem snapshotRichElementsList_primrec (c : Code) :
    Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      snapshotRichElementsList c p.1.1 p.1.2 p.2.1 p.2.2) := by
  apply Primrec.of_eq;
  rotate_right;
  · exact fun p => (snapshotDescList c p.1.1 p.1.2 p.2.2).flatten.filter
      (fun y => decide (2 ^ p.2.1 ≤
        (snapshotDescList c p.1.1 p.1.2 p.2.2).countP (fun S => decide (y ∈ S))))
  · refine (list_filter_primrec ?_ ?_).of_eq (fun _ => rfl)
    · have h1 : Primrec (fun p : (ℕ × ℕ) × ℕ =>
          ((canonicalFinsetList ((snapshotCodes c p.1.1 p.1.2).filter
            isCanonicalUniformCodeBool).toFinset).map
              (fun w => canonicalFinsetList (((decodeDistributionData w).map
                CodedDistributionEntry.point).toFinset))).filter
                  (fun S => S.length ≤ 2 ^ p.2)) :=
        (snapshotDescriptionsAndSizeLe_primrec c).of_eq (fun _ => rfl)
      refine (Primrec.list_flatten.comp (h1.comp (Primrec.pair
        (Primrec.fst.comp Primrec.fst |> Primrec.pair <|
          Primrec.snd.comp Primrec.snd) <| Primrec.snd.comp Primrec.fst))).of_eq (fun _ => rfl)
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
        exact twoPow_primrec.comp (Primrec.fst.comp Primrec.snd)
      exact PrimrecPred.decide (Primrec.nat_le.comp (h_twoPow.comp Primrec.fst)
        (h_countP.comp Primrec.fst Primrec.snd))
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
    · rw [ if_pos ];
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

def richInput (i j k h : ℕ) : BitString :=
  selectorInput i j k h

@[simp] theorem selNat_richInput (i j k h : ℕ) :
    selNat (richInput i j k h) = i := by
  simp [richInput]

@[simp] theorem selAlpha_richInput (i j k h : ℕ) :
    selAlpha (richInput i j k h) = j := by
  simp [richInput]

@[simp] theorem selMaxK_richInput (i j k h : ℕ) :
    selMaxK (richInput i j k h) = k := by
  simp [richInput]

@[simp] theorem selH_richInput (i j k h : ℕ) :
    selH (richInput i j k h) = h := by
  simp [richInput]

noncomputable def richSelectorFn (c : Code) : BitString →. BitString := fun s =>
  (Nat.rfind (fun t => Part.some (decide (countHalts c (selNat s) t = selH s)))).bind
    (fun t => Part.some
      (codedDistributionDataCode ((canonicalFinsetList
        (snapshotRichElements c (selNat s) (selAlpha s) (selMaxK s) t)).map fun x =>
          { point := x,
            mass := ratMassInvNat (max 1 (canonicalFinsetList
              (snapshotRichElements c (selNat s)
                (selAlpha s) (selMaxK s) t)).length)
                (by positivity) })))

theorem partrec_richSelectorFn (c : Code) : Partrec (richSelectorFn c) := by
  -- Ordinal selector computability for the snapshot rich-element stream.
  have h_eq : Computable (fun p : ℕ × ℕ => decide (p.1 = p.2)) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.fst Primrec.snd)).to_comp
  have h_check : Computable₂ (fun (s : BitString) (t : ℕ) =>
      decide (countHalts c (selNat s) t = selH s)) :=
    (h_eq.comp (Computable.pair
      ((countHalts_computable c).comp
        (Computable.pair (selNat_computable.comp Computable.fst) Computable.snd))
      (selH_computable.comp Computable.fst))).to₂
  have h_args : Primrec (fun p : BitString × ℕ =>
      ((selNat p.1, selAlpha p.1), selMaxK p.1, p.2)) :=
    Primrec.pair
      (Primrec.pair (selNat_primrec.comp Primrec.fst) (selAlpha_primrec.comp Primrec.fst))
      (Primrec.pair (selMaxK_primrec.comp Primrec.fst) Primrec.snd)
  have h_body := (codedUniformEncoder_primrec.comp
    ((snapshotRichElements_primrec c).comp h_args)).to_comp.to₂
  exact (Partrec.bind (Partrec.rfind h_check.partrec₂) h_body.partrec₂).of_eq
    (fun _ => rfl)

theorem exists_partrec_richSet_code (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ f : BitString →. BitString, Partrec f ∧
      ∀ i j k (hne : (richDescriptionElements U i j k).Nonempty),
        ∃ h < 2 ^ (i + 1), f (richInput i j k h) = Part.some
            ((codedUniformOn (richDescriptionElements U i j k) hne).code) := by
  obtain ⟨c, hc⟩ : ∃ c : Code, IsCodeFor c U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  refine ⟨ richSelectorFn c, partrec_richSelectorFn c, ?_ ⟩;
  intro i j k hne
  obtain ⟨t_star, hmax⟩ := exists_max_countHalts c i
  set h := countHalts c i t_star
  have h_lt : h < 2 ^ (i + 1) := by
    exact lt_of_le_of_lt ( countHalts_le_length c i t_star ) ( length_boundedPrograms_lt i )
  set t₀ := Nat.find (⟨t_star, rfl⟩ : ∃ t, countHalts c i t = h)
  have ht0 : countHalts c i t₀ = h := by
    exact Nat.find_spec ( ⟨ t_star, rfl ⟩ : ∃ t, countHalts c i t = h )
  have ht0_min : ∀ m < t₀, countHalts c i m ≠ h := by
    exact fun m mn => fun hm => mn.not_ge <| Nat.find_min' _ hm
  have hmax0 : ∀ t', countHalts c i t' ≤ countHalts c i t₀ := by
    grind
  use h, h_lt;
  convert Part.eq_some_iff.mpr _ using 1;
  unfold richSelectorFn
  simp +decide only [selNat_richInput, selH_richInput, selAlpha_richInput, selMaxK_richInput,
    length_canonicalFinsetList, Part.mem_bind_iff, Part.mem_some_iff]
  refine ⟨t₀, Nat.mem_rfind.mpr ⟨?_, fun {m} hm => ?_⟩, ?_⟩
  · exact Part.mem_some_iff.mpr (decide_eq_true ht0).symm
  · exact Part.mem_some_iff.mpr (decide_eq_false (ht0_min m hm)).symm
  · simp_all +decide only [ne_eq, implies_true,
      snapshotRichElements_eq_richDescriptionElements hc i j k t₀ hmax0, Finset.one_le_card,
      sup_of_le_right]
    convert codedUniformOn_code_eq _ hne using 1

theorem richInput_KPPlain_le (U : Map) (hU : IsOptimalPrefixConditional U) (c_partrec : ℕ) :
    ∃ c : ℕ, ∀ i j k h, h < 2 ^ (i + 1) →
      KPPlain U (richInput i j k h) + (c_partrec : ENat) ≤
        (i + 1 : ENat) + logSlack c (i + j + k) := by
  -- Let `c₀` be the constant from `KPPlain_le_length_add_log U hU` (gives `KPPlain U s ≤ s.length +
  --   2*(Nat.bits s.length).length + c₀`).
  obtain ⟨c₀, hc₀⟩ := KPPlain_le_length_add_log U hU;
  refine ⟨ 19 + c₀ + c_partrec, fun i j k h hh => le_trans (add_le_add (hc₀ _) le_rfl) ?_⟩
  norm_cast; simp +decide only [richInput]
  -- Let `L := (Nat.bits (i+j+k)).length`.
  set L := (Nat.bits (i + j + k)).length with hL_def
  have hL : (Nat.bits i).length ≤ L ∧ (Nat.bits j).length ≤ L ∧ (Nat.bits k).length ≤ L ∧
      (Nat.bits h).length ≤ i + 1 ∧ i < 2 ^ L := by
    have hL : (Nat.bits i).length ≤ L ∧ (Nat.bits j).length ≤ L ∧ (Nat.bits k).length ≤ L := by
      have hL : ∀ a b : ℕ, a ≤ b → (Nat.bits a).length ≤ (Nat.bits b).length := by
        intros a b hab
        rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
        exact Nat.size_le_size hab
      exact ⟨ hL _ _ ( by linarith ), hL _ _ ( by linarith ), hL _ _ ( by linarith ) ⟩;
    exact ⟨hL.1, hL.2.1, hL.2.2, length_natBits_lt_pow hh,
      lt_two_pow_length_natBits i |> lt_of_lt_of_le <| Nat.pow_le_pow_right (by decide) hL.1⟩
  -- Then `(selectorInput i j k h).length ≤ 6*L + i + 4`.
  have h_selectorInput_length : (selectorInput i j k h).length ≤ 6 * L + i + 4 := by
    unfold selectorInput
    simp +decide only [pairCode, pack4, List.append_assoc, List.length_append, length_natCode]
    linarith
  -- Then `(Nat.bits (selectorInput i j k h).length).length ≤ L + 4`.
  have h_bits_length : (Nat.bits (selectorInput i j k h).length).length ≤ L + 4 := by
    have h_bits_length : (selectorInput i j k h).length < 2 ^ (L + 4) := by
      rw [pow_add]
      nlinarith [Nat.pow_le_pow_right two_pos (show L ≥ 0 by positivity),
        show L ≤ 2 ^ L by
          exact Nat.recOn L (by norm_num) fun n ihn => by
            rw [pow_succ']; linarith [Nat.one_le_pow n 2 zero_lt_two]]
    exact length_natBits_lt_pow h_bits_length;
  -- Abstract the (large) `selectorInput` length as an opaque atom before running
  -- `nlinarith`, so the arithmetic solver does not repeatedly `whnf` the `richInput`
  -- definition.
  unfold logSlack
  set P := (selectorInput i j k h).length with hP
  clear_value P
  clear hP
  rw [← hL_def]
  nlinarith

theorem setComplexity_richDescriptionElements_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ i j k (hne : (richDescriptionElements U i j k).Nonempty),
      setComplexity U (richDescriptionElements U i j k) hne ≤ (i + 1 : ENat) + logSlack c
          (i + j + k) := by
  obtain ⟨f, hf, hf_spec⟩ := exists_partrec_richSet_code U hU
  obtain ⟨c₃, hc₃⟩ := KPPlain_partrec_map_le U hU f hf
  obtain ⟨c₄, hc₄⟩ := richInput_KPPlain_le U hU c₃
  refine ⟨c₄, fun i j k hne => ?_⟩
  obtain ⟨h, hh₁, hh₂⟩ := hf_spec i j k hne
  have hmem : (codedUniformOn (richDescriptionElements U i j k) hne).code ∈
      f (richInput i j k h) := by
    rw [hh₂]; exact Part.mem_some _
  exact le_trans (hc₃ _ _ hmem) (hc₄ i j k h hh₁)

/-- **Rich-set reduction.**  If `x` belongs to at least `2^k` distinct
`(i,j)`-descriptions, then the computable rich set witnesses a description of
`x` of complexity `(i+1) + logSlack c (i+j+k)` and log-size `i + 1 + j - k`.

This is the honest consequence of the selector bridge: it combines
`mem_richDescriptionElements_of_many` (membership), the selector complexity
bound `setComplexity_richDescriptionElements_le`, and the double-counting
cardinality bound `card_richDescriptionElements_le`.  It is *not* yet either half
of the improving-descriptions proposition (the rich set has log-size `i+1+j-k`,
which still carries the extra `i+1` from the description-count bound), but it is
the single combinatorial+coding witness those halves are built from. -/
theorem inDescriptionProfile_of_many (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (i j k : ℕ), ManyIJDescriptions U x i j k →
      InDescriptionProfile U x ((i + 1) + logSlack c (i + j + k)) (i + 1 + j - k) := by
  obtain ⟨c, hc⟩ := setComplexity_richDescriptionElements_le U hU
  refine ⟨c, fun x i j k hmany => ?_⟩
  have hx : x ∈ richDescriptionElements U i j k :=
    mem_richDescriptionElements_of_many U x i j k hmany
  have hne : (richDescriptionElements U i j k).Nonempty := ⟨x, hx⟩
  refine ⟨richDescriptionElements U i j k, hne, hx, ?_, ?_⟩
  · refine le_trans (hc i j k hne) (le_of_eq ?_)
    push_cast
    ring
  · exact card_richDescriptionElements_le U i j k

/-!
### Size-Portion Selector Decomposition

The size-improvement half is carried by a single, honestly-stated selector
obligation `richSizePortion_selector_spec`.  It bundles, for one shared coding
constant `c` and one shared selected-portion family `S`, the three facts that the
article's portion/batch construction must deliver:

* membership and nonemptiness of the selected portion (the witness must contain
  `x`);
* the complexity bound `setComplexity ≤ i + logSlack c (n+i+j)` (to be discharged
  via the snapshot selector machinery: `exists_partrec_richSet_code`,
  `KPPlain_partrec_map_le`, `richInput_KPPlain_le`);
* the cardinality bound `card ≤ 2^(j-k+logSlack c (n+i+j))` (the half-rich
  portion count).

Bundling into one existential is deliberate: the three bounds all constrain the
*same* selected set, so splitting them across separate lemmas about a post-hoc
`Classical.choose` would make each individually unprovable (nothing would pin the
chosen witness).  The assembled interface `exists_richSizePortion_logSlack` is a
thin projection of this obligation.
-/

/-
Logarithmic-slack absorption: an additive `+1` together with a doubling of
the slack argument is absorbed by enlarging the slack constant.  If `A ≤ 2 * B`
then `1 + logSlack c₄ A ≤ logSlack (2 * c₄ + 1) B`.  This is the arithmetic that
lets the coding-wrapper lemmas replace the raw selector slack argument
`i + j + k` (or `i + j + k + m`) by the visible-parameter slack `n + i + j`.
-/
theorem logSlack_one_add_le_two_mul (c₄ A B : ℕ) (h : A ≤ 2 * B) :
    1 + logSlack c₄ A ≤ logSlack (2 * c₄ + 1) B := by
  unfold logSlack; ring_nf;
  have h_bits : (Nat.bits A).length ≤ (Nat.bits (2 * B)).length := by
    rw [ Nat.size_eq_bits_len, Nat.size_eq_bits_len ] ; exact Nat.size_le_size h;
  rcases B with ( _ | B ) <;> simp_all +decide;
  · linarith;
  · nlinarith

/-
Logarithmic-slack absorption with an additive `+4` and a slack argument bounded
by `2 * B + 3`.  This is the complexity-portion analogue of
`logSlack_one_add_le_two_mul`: the raw selector slack argument
`i + j + k + (i - k + 3)` is at most `2 * (n + i + j) + 3` (using `k ≤ i`), and the
additive `+4` (one from the address `(i-k)+1` rounding, three absorbed) is paid for
by enlarging the slack constant to `4 * c₄ + 4`.
-/
theorem logSlack_four_add_le (c₄ A B : ℕ) (h : A ≤ 2 * B + 3) :
    4 + logSlack c₄ A ≤ logSlack (4 * c₄ + 4) B := by
  have h_bits : (Nat.bits A).length ≤ (Nat.bits B).length + 2 := by
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_le]
    calc A ≤ 2 * B + 3 := h
      _ < 4 * 2 ^ Nat.size B := by nlinarith [Nat.lt_size_self B]
      _ = 2 ^ (Nat.size B + 2) := by rw [pow_add]; ring
  unfold logSlack
  have hmul : c₄ * (Nat.bits A).length ≤ c₄ * ((Nat.bits B).length + 2) := by gcongr
  nlinarith [hmul, Nat.zero_le (c₄ * (Nat.bits B).length),
    Nat.zero_le ((Nat.bits B).length), Nat.zero_le c₄]

/-
Address-parameterized refinement of `richInput_KPPlain_le`.  When the batch
address `h` is bounded by `2 ^ (m + 1)` (with `m` possibly much smaller than
`i`, as for the complexity portion where `m = i - k`), the plain complexity of
`richInput i j k h` is controlled by `m + 1` plus a logarithmic slack in all
visible parameters `i + j + k + m`.  The original `richInput_KPPlain_le` is the
special case `m = i`.
-/
theorem richInput_KPPlain_le_addr (U : Map) (hU : IsOptimalPrefixConditional U) (c_partrec : ℕ) :
    ∃ c : ℕ, ∀ (i j k h m : ℕ), h < 2 ^ (m + 1) →
      KPPlain U (richInput i j k h) + (c_partrec : ENat)
        ≤ ((m : ENat) + 1) + logSlack c (i + j + k + m) := by
  -- Set `c₀` from `KPPlain_le_length_add_log U hU`.
  obtain ⟨c₀, hc₀⟩ := KPPlain_le_length_add_log U hU;
  refine ⟨19 + c₀ + c_partrec, fun i j k h m hlt => le_trans (add_le_add (hc₀ _) le_rfl) ?_⟩
  set L := (Nat.bits (i + j + k + m)).length with hL_def
  have hL : (Nat.bits i).length ≤ L ∧ (Nat.bits j).length ≤ L ∧ (Nat.bits k).length ≤ L ∧
      (Nat.bits m).length ≤ L ∧ (Nat.bits h).length ≤ m + 1 ∧ m < 2 ^ L := by
    have hL : (Nat.bits i).length ≤ L ∧ (Nat.bits j).length ≤ L ∧ (Nat.bits k).length ≤ L ∧
        (Nat.bits m).length ≤ L := by
      have hL : ∀ a b : ℕ, a ≤ b → (Nat.bits a).length ≤ (Nat.bits b).length := by
        intros a b hab
        rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
        exact Nat.size_le_size hab
      exact ⟨hL _ _ (by linarith), hL _ _ (by linarith),
        hL _ _ (by linarith), hL _ _ (by linarith)⟩
    exact ⟨hL.1, hL.2.1, hL.2.2.1, hL.2.2.2, length_natBits_lt_pow hlt,
      lt_two_pow_length_natBits m |> lt_of_lt_of_le <| Nat.pow_le_pow_right (by decide) hL.2.2.2⟩
  unfold logSlack; norm_cast; simp +arith +decide only [ge_iff_le]
  -- By definition of `selectorInput`, we have:
  have h_selectorInput_length : (selectorInput i j k h).length ≤ 6 * L + m + 4 := by
    unfold selectorInput
    simp +decide only [pairCode, pack4, List.append_assoc, List.length_append, length_natCode]
    linarith
  have h_bits_length : (Nat.bits (selectorInput i j k h).length).length ≤ L + 4 := by
    have h_bits_length : (selectorInput i j k h).length < 2 ^ (L + 4) := by
      rw [pow_add]
      nlinarith [Nat.pow_le_pow_right two_pos (show L ≥ 0 by positivity),
        show L ≤ 2 ^ L by
          exact Nat.recOn L (by norm_num) fun n ihn => by
            rw [pow_succ']; linarith [Nat.one_le_pow n 2 zero_lt_two]]
    exact length_natBits_lt_pow h_bits_length;
  have h_richInput_length : (richInput i j k h).length ≤ 6 * L + m + 4 := by
    simpa only [richInput] using h_selectorInput_length
  have h_richInput_bits_length : (Nat.bits (richInput i j k h).length).length ≤ L + 4 := by
    simpa only [richInput] using h_bits_length
  -- Abstract the (large) `richInput` length as an opaque atom before running
  -- `nlinarith`, so the arithmetic solver does not repeatedly `whnf` the `richInput`
  -- definition.
  clear h_selectorInput_length h_bits_length
  set P := (richInput i j k h).length with hP
  clear_value P
  clear hP
  rw [← hL_def]
  nlinarith [Nat.zero_le (c₀ * L), Nat.zero_le (c_partrec * L)]

/-
**List chunking membership.**  If a list `L` of length at most `a * b`
contains `x` and the chunk size `b` is positive, then `x` lies in one of the `a`
consecutive length-`b` chunks `(L.drop (h * b)).take b`, indexed by some `h < a`.

This is the pure combinatorial ingredient of the size-portion (half-rich) batch
construction: the rich set has at most `2^(i+1+j-k)` elements, so cutting its
canonical list into chunks of size `2^(j-k)` yields at most `2^(i+1)` batches,
and the batch containing `x` is selected by an address `h < 2^(i+1)`.
-/
theorem mem_listChunk_of_mem {α : Type*} (L : List α) (a b : ℕ)
    (hb : 0 < b) {x : α} (hx : x ∈ L) (hlen : L.length ≤ a * b) :
    ∃ h < a, x ∈ (L.drop (h * b)).take b := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hx
  refine ⟨k / b, ?_, ?_⟩
  · exact Nat.div_lt_of_lt_mul <| by linarith [Fin.is_lt k]
  · rw [← hk, List.mem_iff_get]
    refine ⟨⟨k % b, ?_⟩, ?_⟩
    · simp only [List.length_take, List.length_drop, lt_inf_iff]
      exact ⟨Nat.mod_lt _ hb,
        lt_tsub_iff_left.mpr (by linarith [Nat.mod_add_div k b, k.2])⟩
    · simp only [List.get_eq_getElem, List.getElem_take, List.getElem_drop]
      exact getElem_congr rfl (Nat.div_add_mod' k b) _

/-- `emittedHalfRichChunks_fold_step` processes a single new rich element `x`.
If `x` is already placed, it does nothing. Otherwise, it extracts the currently
unplaced half-rich elements, forms a new chunk of size at most `2^j` with `x` at
the head, and appends it to the emitted chunks list. -/
def emittedHalfRichChunks_fold_step (j : ℕ) (half_rich : List BitString)
    (chunks : List (List BitString)) (x : BitString) : List (List BitString) :=
  bif decide (x ∈ chunks.flatten) then
    chunks
  else
    let unplaced_half := half_rich.filter (fun y =>
      bif decide (y ∈ chunks.flatten) then false else true)
    let new_chunk := (x :: unplaced_half.filter (fun y =>
      bif decide (y = x) then false else true)).take (2 ^ j)
    chunks ++ [new_chunk]

theorem emittedHalfRichChunks_fold_step_primrec :
    Primrec₂ (fun (p : ℕ × List BitString × List (List BitString)) (x : BitString) =>
      emittedHalfRichChunks_fold_step p.1 p.2.1 p.2.2 x) := by
  -- Primitive-recursive plumbing for the online half-rich stream: the step
  -- function is a composition of primitive recursive functions.
  have h_step_primrec : Primrec
      (fun p : ℕ × (List BitString × (List (List BitString) × BitString)) =>
        emittedHalfRichChunks_fold_step p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    have h_append_primrec : Primrec
          (fun p : List (List BitString) × (Nat × BitString × List BitString) => p.1 ++ [List.take (
            2 ^ p.2.1) (p.2.2.1 :: List.filter (fun y => bif decide (
              y = p.2.2.1) then false else true) (List.filter (fun y => bif decide (
                y ∈ p.1.flatten) then false else true) p.2.2.2))]) := by
        refine Primrec.list_append.comp Primrec.fst ?_
        refine Primrec.list_cons.comp ?_ (Primrec.const [])
        refine Primrec.list_take.comp (twoPow_primrec.comp (Primrec.fst.comp Primrec.snd)) ?_
        refine Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) ?_
        refine (list_filter_primrec ?_ ?_).of_eq (fun _ => rfl)
        · refine (list_filter_primrec (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
            ?_).of_eq (fun _ => rfl)
          refine (Primrec.cond (bitString_mem_primrec.comp Primrec.snd
            (Primrec.list_flatten.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.const false) (Primrec.const true)).of_eq (fun _ => rfl)
        · refine (Primrec.cond (PrimrecPred.decide (Primrec.eq.comp Primrec.snd
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
            (Primrec.const false) (Primrec.const true)).of_eq (fun _ => rfl)
    have h_false_branch := h_append_primrec.comp (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair Primrec.fst (Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp Primrec.snd))))
    refine (Primrec.cond (bitString_mem_primrec.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)) (Primrec.list_flatten.comp (Primrec.fst.comp
      (Primrec.snd.comp Primrec.snd))))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      h_false_branch).of_eq ?_
    · intro p; cases p; rfl
  convert h_step_primrec.comp _ using 1;
  rotate_left;
  · exact ( ℕ × List BitString × List ( List BitString ) ) × BitString;
  · exact inferInstance;
  · exact fun p => ( p.1.1, p.1.2.1, p.1.2.2, p.2 );
  · exact Primrec.pair ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.pair ( Primrec.fst.comp (
    Primrec.snd.comp ( Primrec.fst ) ) ) ( Primrec.pair ( Primrec.snd.comp ( Primrec.snd.comp (
      Primrec.fst ) ) ) ( Primrec.snd ) ) );
  · bound

/-
General `foldl` combinator: a left fold with a primitive-recursive step
function, initial accumulator, and list, all primitive recursive in the input,
is primitive recursive.
-/
theorem list_foldl_primrec {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → σ} {h : α → σ → β → σ}
    (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec (fun p : (α × σ) × β => h p.1.1 p.1.2 p.2)) :
    Primrec (fun a => (f a).foldl (h a) (g a)) := by
  refine Primrec.list_foldl hf hg
    (show Primrec₂ (fun (a : α) (p : σ × β) => h a p.1 p.2) from ?_)
  exact hh.comp (Primrec.pair (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd))

def emittedHalfRichChunks_step (c : Code) (i j k : ℕ) (t : ℕ) (chunks : List (List BitString)) :
    List (List BitString) :=
  let rich := (snapshotRichElementsList c i j k t).eraseDups
  let half_rich := (snapshotRichElementsList c i j (k - 1) t).eraseDups
  rich.foldl (emittedHalfRichChunks_fold_step j half_rich) chunks

theorem emittedHalfRichChunks_step_primrec (c : Code) :
    Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ × List (List BitString) =>
      emittedHalfRichChunks_step c p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2) := by
  -- Compose the primitive-recursive rich and half-rich snapshot lists with the
  -- fold step.
  apply list_foldl_primrec;
  · have h_eraseDups_primrec : Primrec (fun (l : List BitString) => l.eraseDups) :=
      eraseDups_bitstring_primrec
    exact h_eraseDups_primrec.comp (
        snapshotRichElementsList_primrec c |> Primrec.comp <| Primrec.pair ( Primrec.pair (
            Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst ) ) ) ( Primrec.snd.comp (
              Primrec.fst.comp ( Primrec.fst ) ) ) ) ( Primrec.pair ( Primrec.snd.comp (
                Primrec.fst ) ) ( Primrec.fst.comp ( Primrec.snd ) ) ) );
  · exact Primrec.snd.comp ( Primrec.snd );
  · convert emittedHalfRichChunks_fold_step_primrec.comp _ _ using 1;
    rotate_left;
    · exact fun p => ( p.1.1.1.1.2, ( snapshotRichElementsList c p.1.1.1.1.1 p.1.1.1.1.2 (
        p.1.1.1.2 - 1 ) p.1.1.2.1 ).eraseDups, p.1.2 );
    · exact fun p => p.2;
    · apply Primrec₂.comp;
      · exact Primrec.pair Primrec.fst Primrec.snd;
      · exact Primrec.snd.comp ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst.comp (
          Primrec.fst ) ) ) );
      · apply Primrec.pair;
        · have h_eraseDups_primrec : Primrec (fun (L : List BitString) => L.eraseDups) := by
            grind +suggestions;
          convert h_eraseDups_primrec.comp _ using 1;
          convert snapshotRichElementsList_primrec c |> Primrec.comp <| _ using 1;
          rotate_left;
          · exact fun p => ( p.1.1.1.1, p.1.1.1.2 - 1, p.1.1.2.1 );
          · exact Primrec.pair ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst.comp (
              Primrec.fst ) ) ) ) ( Primrec.pair ( Primrec.nat_sub.comp ( Primrec.snd.comp (
                Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst ) ) ) ) ( Primrec.const 1 ) ) (
                  Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst.comp ( Primrec.fst ) ) ) ) );
          · grind;
        · exact Primrec.snd.comp ( Primrec.fst );
    · exact Primrec.snd;
    · rfl

def emittedHalfRichChunksList (c : Code) (i j k : ℕ) : ℕ → List (List BitString)
| 0 => emittedHalfRichChunks_step c i j k 0 []
| t + 1 => emittedHalfRichChunks_step c i j k (t + 1) (emittedHalfRichChunksList c i j k t)

theorem emittedHalfRichChunksList_primrec (c : Code) :
    Primrec (fun p : ((
        ℕ × ℕ) × ℕ) × ℕ => emittedHalfRichChunksList c p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  -- Primitive recursion over time for the emitted online chunk stream.
  apply Primrec.of_eq;
  rotate_right;
  · exact fun p => ( List.foldl (
      fun chunks t => emittedHalfRichChunks_step c p.1.1.1 p.1.1.2 p.1.2 ( t + 1 ) chunks ) (
        emittedHalfRichChunks_step c p.1.1.1 p.1.1.2 p.1.2 0 [ ] ) ( List.range p.2 ) );
  · apply list_foldl_primrec;
    · exact Primrec.list_range.comp ( Primrec.snd );
    · convert emittedHalfRichChunks_step_primrec c |> Primrec.comp <| _ using 1;
      rotate_left;
      · exact fun p => ( p.1, 0, [ ] );
      · exact Primrec.pair ( Primrec.fst ) ( Primrec.pair ( Primrec.const 0 ) ( Primrec.const [
        ] ) );
      · grind;
    · convert emittedHalfRichChunks_step_primrec c |> Primrec.comp <| _ using 1;
      rotate_left;
      · exact fun p => ( p.1.1.1, p.2 + 1, p.1.2 );
      · exact Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.succ.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      · grind;
  · intro n; induction n.2 <;> simp_all +decide [ List.range_succ ] ;
    · rfl;
    · rfl

def emittedHalfRichChunks (c : Code) (i j k : ℕ) (t : ℕ) : List (Finset BitString) :=
  (emittedHalfRichChunksList c i j k t).map List.toFinset

/-- A single `emittedHalfRichChunks_fold_step` either leaves the accumulator
unchanged or appends one new chunk, so a left fold over it always extends the
accumulator by some suffix. -/
theorem emittedHalfRichChunks_foldStep_append (j : ℕ) (half_rich L : List BitString)
    (acc : List (List BitString)) :
    ∃ r, L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc = acc ++ r := by
  induction L using List.reverseRecOn generalizing acc
  case' nil => exact ⟨[], by simp⟩
  case' append_singleton xs x ih =>
      obtain ⟨r, hr⟩ := ih acc
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hr]
      rcases Bool.eq_false_or_eq_true
          (decide (x ∈ (acc ++ r).flatten)) with h | h <;>
        simp only [emittedHalfRichChunks_fold_step, h, cond_true, cond_false]
      · exact ⟨r, rfl⟩
      · exact ⟨_, (List.append_assoc _ _ _)⟩

/-- Every chunk produced by a left fold of `emittedHalfRichChunks_fold_step` has
length at most `2 ^ j`, provided the starting accumulator does. -/
theorem emittedHalfRichChunks_foldStep_length (j : ℕ) (half_rich L : List BitString)
    (acc : List (List BitString)) (hacc : ∀ l ∈ acc, l.length ≤ 2 ^ j) :
    ∀ l ∈ L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc, l.length ≤ 2 ^ j := by
  induction L using List.reverseRecOn generalizing acc
  case' nil => simpa using hacc
  case' append_singleton xs x ih =>
      intro l hl
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hl
      set acc' := xs.foldl (emittedHalfRichChunks_fold_step j half_rich) acc with hacc'
      have hacc'_len : ∀ l ∈ acc', l.length ≤ 2 ^ j := ih acc hacc
      rcases Bool.eq_false_or_eq_true (decide (x ∈ acc'.flatten)) with h | h <;>
        simp only [emittedHalfRichChunks_fold_step, h, cond_true, cond_false] at hl
      · exact hacc'_len l hl
      · rw [List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | hl
        · exact hacc'_len l hl
        · subst hl
          rw [List.length_take]
          exact Nat.min_le_left _ _

theorem emittedHalfRichChunks_mono (c : Code) (i j k : ℕ) (t : ℕ) :
    ∃ rest, emittedHalfRichChunks c i j k (t + 1) = emittedHalfRichChunks c i j k t ++ rest := by
  obtain ⟨r, hr⟩ := emittedHalfRichChunks_foldStep_append j
    ((snapshotRichElementsList c i j (k - 1) (t + 1)).eraseDups)
    ((snapshotRichElementsList c i j k (t + 1)).eraseDups)
    (emittedHalfRichChunksList c i j k t)
  refine ⟨r.map List.toFinset, ?_⟩
  simp only [emittedHalfRichChunks, emittedHalfRichChunksList, emittedHalfRichChunks_step, hr,
    List.map_append]

theorem emittedHalfRichChunks_card_le (c : Code) (i j k t : ℕ) (S : Finset BitString)
    (hS : S ∈ emittedHalfRichChunks c i j k t) : S.card ≤ 2 ^ j := by
  have h_length : ∀ tt, ∀ l ∈ emittedHalfRichChunksList c i j k tt, l.length ≤ 2 ^ j := by
    intro tt
    induction tt
    case' zero =>
        simp only [emittedHalfRichChunksList, emittedHalfRichChunks_step]
        exact emittedHalfRichChunks_foldStep_length j _ _ [] (by simp)
    case' succ n ih =>
        simp only [emittedHalfRichChunksList, emittedHalfRichChunks_step]
        exact emittedHalfRichChunks_foldStep_length j _ _ _ ih
  obtain ⟨l, hl_mem, hl_eq⟩ := List.mem_map.mp hS
  rw [← hl_eq]
  exact le_trans (List.toFinset_card_le l) (h_length t l hl_mem)

/-- A left fold of `emittedHalfRichChunks_fold_step` only ever extends the
flattened accumulator: the starting flatten is a subset of the final one. -/
theorem emittedHalfRichChunks_foldStep_flatten_subset (j : ℕ) (half_rich L : List BitString)
    (acc : List (List BitString)) :
    acc.flatten ⊆ (L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc).flatten := by
  obtain ⟨r, hr⟩ := emittedHalfRichChunks_foldStep_append j half_rich L acc
  rw [hr, List.flatten_append]
  exact List.subset_append_left _ _

/-
Every element of the rich list `L` ends up placed (i.e. in the flattened
accumulator) after the left fold of `emittedHalfRichChunks_fold_step`, since each
element either is already placed or becomes the head of a freshly emitted chunk
(and `2 ^ j ≥ 1`).
-/
theorem emittedHalfRichChunks_foldStep_mem_flatten (j : ℕ) (half_rich L : List BitString)
    (acc : List (List BitString)) (y : BitString) (hy : y ∈ L) :
    y ∈ (L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc).flatten := by
  induction L generalizing acc
  case' nil => simp at hy
  case' cons a as ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hy with rfl | hmem
      · refine emittedHalfRichChunks_foldStep_flatten_subset j half_rich as _ ?_
        unfold emittedHalfRichChunks_fold_step
        rcases Bool.eq_false_or_eq_true (decide (y ∈ acc.flatten)) with h | h <;>
          simp only [h, cond_true, cond_false]
        · exact of_decide_eq_true h
        · rw [List.flatten_append, List.mem_append]
          refine Or.inr ?_
          obtain ⟨m, hm⟩ : ∃ m, 2 ^ j = m + 1 :=
            ⟨2 ^ j - 1, by have := Nat.one_le_two_pow (n := j); omega⟩
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil, hm,
            List.take_succ_cons, List.mem_cons, true_or]
      · exact ih _ hmem

private theorem mem_eraseDups_iff {x : BitString} {L : List BitString} :
    x ∈ L.eraseDups ↔ x ∈ L := by
  induction L using List.reverseRecOn
  case' nil => simp
  case' append_singleton xs a ih =>
    rw [List.eraseDups_append]
    by_cases ha : a ∈ xs <;> simp_all [List.removeAll, List.eraseDups_cons]

private theorem nodup_eraseDupsBy_loop (L acc : List BitString) (hacc : acc.Nodup) :
    (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) L acc).Nodup := by
  induction L generalizing acc with
  | nil => simpa only [List.eraseDupsBy.loop] using List.nodup_reverse.mpr hacc
  | cons x L ih =>
    unfold List.eraseDupsBy.loop
    split
    · exact ih acc hacc
    · apply ih
      simp only [List.nodup_cons]
      refine ⟨?_, hacc⟩
      intro hx
      rename_i h
      exact List.any_eq_false.mp h x hx (by simp)

private theorem nodup_eraseDups (L : List BitString) : L.eraseDups.Nodup :=
  nodup_eraseDupsBy_loop L [] (by simp)

private theorem emittedHalfRichChunks_fold_step_mem_ne_nil (j : ℕ) (half_rich : List BitString)
    (M : List BitString) (acc : List (List BitString)) (hacc : ∀ l ∈ acc, l ≠ []) :
    ∀ l ∈ List.foldl (emittedHalfRichChunks_fold_step j half_rich) acc M, l ≠ [] := by
  induction M generalizing acc with
  | nil => simpa using hacc
  | cons x M ih =>
    rw [List.foldl_cons]
    apply ih
    intro l hl
    by_cases hx : x ∈ acc.flatten
    · exact hacc l (by simpa [emittedHalfRichChunks_fold_step, hx] using hl)
    · have hdecide : decide (x ∈ acc.flatten) = false := by simp [hx]
      simp only [emittedHalfRichChunks_fold_step, hdecide, cond_false, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with hl | rfl
      · exact hacc l hl
      · obtain ⟨n, hn⟩ : ∃ n, 2 ^ j = n + 1 :=
          ⟨2 ^ j - 1, by have := Nat.one_le_two_pow (n := j); omega⟩
        simp [hn]

/-
Every rich element appears in some emitted chunk at some time `t`.
-/
theorem emittedHalfRichChunks_cover_rich (U : Map) (c : Code) (hc : IsCodeFor c U) (i j k : ℕ)
    (x : BitString)
    (hx : x ∈ richDescriptionElements U i j k) :
    ∃ t, ∃ S ∈ emittedHalfRichChunks c i j k t, x ∈ S := by
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, ∀ t', countHalts c i t' ≤ countHalts c i t₀ := exists_max_countHalts c i;
  -- By `snapshotRichElements_eq_richDescriptionElements hc i j k t₀ ht₀`, `snapshotRichElements c i
  --   j k t₀ = richDescriptionElements U i j k`, so `x ∈ snapshotRichElements c i j k t₀`.
  have h_snapshot : x ∈ snapshotRichElements c i j k t₀ := by
    rw [ snapshotRichElements_eq_richDescriptionElements hc i j k t₀ ht₀ ] ; assumption;
  -- By `snapshotRichElementsList_toFinset`, this equals `(snapshotRichElementsList c i j k
  --   t₀).toFinset`, so `x ∈ snapshotRichElementsList c i j k t₀`.
  have h_snapshot_list : x ∈ (snapshotRichElementsList c i j k t₀).toFinset := by
    rw [snapshotRichElementsList_toFinset]
    exact h_snapshot
  have h_eraseDups : x ∈ (snapshotRichElementsList c i j k t₀).eraseDups :=
    mem_eraseDups_iff.mpr <| List.mem_toFinset.mp h_snapshot_list
  -- By `emittedHalfRichChunks_foldStep_mem_flatten`, `x ∈ (emittedHalfRichChunksList c i j k
  --   t₀).flatten`.
  have h_flatten : x ∈ (emittedHalfRichChunksList c i j k t₀).flatten := by
    cases t₀ with
    | zero => exact emittedHalfRichChunks_foldStep_mem_flatten j _ _ _ _ h_eraseDups
    | succ t₀ =>
        exact emittedHalfRichChunks_foldStep_mem_flatten j _ _ _ _ h_eraseDups
  rw [List.mem_flatten] at h_flatten
  obtain ⟨l, hl₁, hl₂⟩ := h_flatten
  exact ⟨t₀, l.toFinset, List.mem_map.mpr ⟨l, hl₁, rfl⟩, by simpa using hl₂⟩

/-- The total number of descriptions in the snapshot is bounded by `2^(i+1)`. -/
theorem snapshotDescList_length_le (c : Code) (i j : ℕ) (t : ℕ) :
    (snapshotDescList c i j t).length ≤ 2 ^ (i + 1) := by
  unfold snapshotDescList
  refine le_trans (List.length_filter_le _ _) ?_
  rw [List.length_map, length_canonicalFinsetList]
  refine le_trans (List.toFinset_card_le _) ?_
  refine le_trans (List.length_filter_le _ _) ?_
  unfold snapshotCodes
  refine le_trans (List.length_filterMap_le _ _) ?_
  exact le_of_lt (length_boundedPrograms_lt i)

/-
Every element placed by a left fold of `emittedHalfRichChunks_fold_step`
lies in `half_rich`, provided the seed list `L` and the starting accumulator do.
Indeed each new chunk is `(x :: filtered_half_rich).take (2^j)`, where the head
`x ∈ L ⊆ half_rich` and the tail is filtered from `half_rich`.
-/
theorem emittedHalfRichChunks_foldStep_flatten_mem (j : ℕ) (half_rich : List BitString)
    (L : List BitString) (acc : List (List BitString))
    (hL : ∀ y ∈ L, y ∈ half_rich)
    (hacc : ∀ y ∈ acc.flatten, y ∈ half_rich) :
    ∀ y ∈ (L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc).flatten,
      y ∈ half_rich := by
  have h_ind : ∀ (xs : List BitString) (acc : List (List BitString)), (∀ y ∈ xs, y ∈ half_rich) →
      (∀ y ∈ acc.flatten, y ∈ half_rich) →
      (∀ y ∈ (xs.foldl (emittedHalfRichChunks_fold_step j half_rich) acc).flatten,
        y ∈ half_rich) := by
    intros xs acc hxs hacc y hy; induction xs using List.reverseRecOn generalizing acc
    case' nil => exact hacc y hy
    case' append_singleton xs x ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.mem_flatten] at hy; obtain ⟨ l, hl₁,
          hl₂ ⟩ := hy; unfold emittedHalfRichChunks_fold_step at hl₁; by_cases hx : x ∈ (
              List.foldl (
                  emittedHalfRichChunks_fold_step j half_rich ) acc xs ).flatten
      · simp_all +decide only [List.mem_flatten, forall_exists_index, and_imp,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or,
          implies_true, forall_const, Bool.cond_true_right, Bool.or_false,
          List.filter_filter]
        convert ih acc hacc l _ hl₂ using 1;
        unfold emittedHalfRichChunks_fold_step at *; aesop;
      · simp_all +decide only [List.mem_flatten, forall_exists_index, and_imp,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or,
          implies_true, forall_const, Bool.cond_true_right, Bool.or_false,
          List.filter_filter, not_exists, not_and]
        unfold emittedHalfRichChunks_fold_step at *; by_cases hx : ∃ l ∈ List.foldl (
          fun chunks x => bif decide ( ∃ l ∈ chunks, x ∈ l ) then chunks else chunks ++ [
            List.take ( 2 ^ j ) ( x :: List.filter ( fun a => !decide ( a = x ) && !decide (
              ∃ l ∈ chunks, a ∈ l ) ) half_rich ) ] ) acc xs, x ∈ l
        · simp_all +decide only [List.mem_flatten, Bool.cond_true_right, Bool.or_false,
            List.filter_filter, decide_true, cond_true]
          grind
        · simp_all +decide only [List.mem_flatten, Bool.cond_true_right, Bool.or_false,
            List.filter_filter, decide_false, cond_false, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false, not_exists, not_and, not_false_eq_true, implies_true]
          rcases hl₁ with ( hl₁ | rfl );
          · exact ih acc hacc _ hl₁ hl₂;
          · have := List.mem_of_mem_take hl₂; aesop;
  exact h_ind L acc hL hacc

/-
The flattened accumulator stays `Nodup` through a left fold of
`emittedHalfRichChunks_fold_step`, when `half_rich` is `Nodup` and the starting
accumulator's flatten is `Nodup`.  Each appended chunk consists of fresh elements
(not already in the flattened accumulator) drawn without repetition from
`half_rich`, so it is internally `Nodup` and disjoint from the accumulator.
-/
theorem emittedHalfRichChunks_foldStep_flatten_nodup (j : ℕ) (half_rich : List BitString)
    (hhr : half_rich.Nodup) (L : List BitString) (acc : List (List BitString))
    (hacc : acc.flatten.Nodup) :
    (L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc).flatten.Nodup := by
  induction L using List.reverseRecOn generalizing acc
  case' nil => exact hacc
  case' append_singleton L ih ih_hyp =>
    unfold emittedHalfRichChunks_fold_step at *
    by_cases hx : ih ∈ (List.foldl (emittedHalfRichChunks_fold_step j half_rich) acc L).flatten <;>
      simp_all +decide only [List.mem_flatten, Bool.cond_true_right, Bool.or_false,
        List.filter_filter, List.foldl_append, List.foldl_cons, List.foldl_nil]
    · unfold emittedHalfRichChunks_fold_step at *; aesop;
    · rw [decide_eq_false]
      · simp_all +decide only [not_exists, not_and, cond_false, List.flatten_append,
          List.flatten_cons, List.flatten_nil, List.append_nil]
        rw [ List.nodup_append ];
        refine ⟨ ?_, ?_, ?_ ⟩;
        · grind +splitIndPred;
        · refine List.Nodup.sublist ( List.take_sublist _ _ ) ?_;
          grind;
        · intro a ha b hb hab; have := List.mem_of_mem_take hb
          simp_all +decide only [List.mem_flatten, List.mem_cons, List.mem_filter,
            decide_true, Bool.not_true, Bool.and_false, Bool.false_eq_true, and_false, or_false]
          unfold emittedHalfRichChunks_fold_step at *; aesop;
      · simp_all +decide only [not_exists, not_and]
        convert hx using 1;
        unfold emittedHalfRichChunks_fold_step; aesop;

/-
The flatten of all emitted chunks is `Nodup`: the chunks are pairwise
disjoint and each is internally duplicate-free.
-/
theorem emittedHalfRichChunksList_flatten_nodup (c : Code) (i j k t : ℕ) :
    ((emittedHalfRichChunksList c i j k t).flatten).Nodup := by
  induction t with
  | zero =>
    exact emittedHalfRichChunks_foldStep_flatten_nodup j _ (nodup_eraseDups _) _ _ (
      by simp)
  | succ t ih =>
    exact emittedHalfRichChunks_foldStep_flatten_nodup j _ (nodup_eraseDups _) _ _ ih

/-
A halting output of `runOut` is preserved under a larger step budget.
-/
theorem runOut_mono {c : Code} {t t' : ℕ} (h : t ≤ t') {p w : BitString}
    (hw : runOut c t p = some w) : runOut c t' p = some w := by
  unfold runOut at hw ⊢
  rw [Option.bind_eq_some_iff] at hw ⊢
  obtain ⟨a, ha_eval, ha_decode⟩ := hw
  exact ⟨a, Nat.Partrec.Code.evaln_mono h ha_eval, ha_decode⟩

/-
`snapshotCodes` only grows with the step budget.
-/
theorem snapshotCodes_mem_of_le {c : Code} {alpha t t' : ℕ} (h : t ≤ t') {w : BitString}
    (hw : w ∈ snapshotCodes c alpha t) : w ∈ snapshotCodes c alpha t' := by
  unfold snapshotCodes at hw ⊢;
  grind +suggestions

/-
`snapshotDescriptions` only grows with the step budget.
-/
theorem snapshotDescriptions_subset_of_le (c : Code) (i : ℕ) {t t' : ℕ} (h : t ≤ t') :
    snapshotDescriptions c i t ⊆ snapshotDescriptions c i t' := by
  unfold snapshotDescriptions
  intro S hS
  rw [Finset.mem_image] at hS ⊢
  obtain ⟨w, hw, rfl⟩ := hS
  refine ⟨w, ?_, rfl⟩
  simp only [List.mem_toFinset, List.mem_filter] at hw ⊢
  exact ⟨snapshotCodes_mem_of_le h hw.1, hw.2⟩

/-
`snapshotDescriptionsAndSizeLe` only grows with the step budget.
-/
theorem snapshotDescriptionsAndSizeLe_subset_of_le (c : Code) (i j : ℕ) {t t' : ℕ} (h : t ≤ t') :
    snapshotDescriptionsAndSizeLe c i j t ⊆ snapshotDescriptionsAndSizeLe c i j t' := by
  unfold snapshotDescriptionsAndSizeLe
  intro S hS
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨snapshotDescriptions_subset_of_le c i h hS.1, hS.2⟩

/-
The multiplicity of `y` in the size-restricted description list equals the number
of size-restricted descriptions containing `y`.
-/
theorem snapshotDescList_countP_eq_card (c : Code) (i j t : ℕ) (y : BitString) :
    (snapshotDescList c i j t).countP (fun S => decide (y ∈ S)) =
      ((snapshotDescriptionsAndSizeLe c i j t).filter (fun S => y ∈ S)).card := by
  rw [ ← snapshotDescList_nodup_map_toFinset c i j t |>.2, Finset.card_eq_sum_ones,
    Finset.sum_filter, List.countP_eq_length_filter ];
  rw [ List.sum_toFinset ];
  · induction ( snapshotDescList c i j t ) using List.reverseRecOn <;> aesop (
    simp_config := { singlePass := true } ) ;
  · exact snapshotDescList_nodup_map_toFinset c i j t |>.1

/-
The multiplicity of `y` is monotone in the step budget.
-/
theorem snapshotDescList_countP_mono (c : Code) (i j : ℕ) (y : BitString) {t t' : ℕ} (h : t ≤ t') :
    (snapshotDescList c i j t).countP (fun S => decide (y ∈ S)) ≤
      (snapshotDescList c i j t').countP (fun S => decide (y ∈ S)) := by
  -- Apply `snapshotDescList_countP_eq_card` to both sides.
  rw [snapshotDescList_countP_eq_card, snapshotDescList_countP_eq_card];
  exact Finset.card_mono <| Finset.filter_subset_filter _ <|
    snapshotDescriptionsAndSizeLe_subset_of_le c i j h

/-
Membership in the `m`-rich element list yields multiplicity at least `2^m`.
-/
theorem mem_snapshotRichElementsList_multiplicity (c : Code) (i j m t : ℕ) {y : BitString}
    (hy : y ∈ snapshotRichElementsList c i j m t) :
    2 ^ m ≤ (snapshotDescList c i j t).countP (fun S => decide (y ∈ S)) := by
  contrapose! hy;
  unfold snapshotRichElementsList; aesop;

/-
Variant of `emittedHalfRichChunks_foldStep_flatten_mem`: when the seed list `L`
is contained in `half_rich`, every placed element is either already in the initial
accumulator or in `half_rich`.
-/
theorem emittedHalfRichChunks_foldStep_flatten_mem_or (j : ℕ) (half_rich : List BitString)
    (L : List BitString) (acc : List (List BitString))
    (hL : ∀ y ∈ L, y ∈ half_rich) :
    ∀ y ∈ (L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc).flatten,
      y ∈ acc.flatten ∨ y ∈ half_rich := by
  revert hL;
  induction L using List.reverseRecOn generalizing acc with
  | nil => aesop
  | append_singleton L ih =>
    unfold emittedHalfRichChunks_fold_step
    simp +decide only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatten, Bool.cond_true_right, Bool.or_false, List.filter_filter,
      List.foldl_append, List.foldl_cons, List.foldl_nil, forall_exists_index, and_imp]
    rename_i h; intro h' y x hx hy; by_cases h : ∃ l ∈ List.foldl ( fun chunks x => bif decide (
        ∃ l ∈ chunks, x ∈ l ) then chunks else chunks ++ [ List.take ( 2 ^ j ) ( x :: List.filter (
          fun a => !decide ( a = x ) && !decide ( ∃ l ∈ chunks, a ∈ l ) ) half_rich ) ] ) acc L,
            ih ∈ l
    · simp_all +decide only [true_or, implies_true, List.mem_flatten,
        forall_exists_index, and_imp, forall_const, decide_true, cond_true]
      unfold emittedHalfRichChunks_fold_step at *; aesop;
    · simp_all +decide only [true_or, implies_true, List.mem_flatten,
        forall_exists_index, and_imp, forall_const, decide_false, cond_false,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_exists, not_and]
      rcases hx with ( hx | rfl );
      · rename_i h''; specialize h'' acc y x
        simp_all +decide only [forall_const]
        exact h'' ( by unfold emittedHalfRichChunks_fold_step; aesop );
      · have := List.mem_of_mem_take hy; aesop;

/-
The `m`-rich element list shrinks as the multiplicity threshold `m` grows.
-/
theorem snapshotRichElementsList_subset_threshold (c : Code) (i j t : ℕ) {m m' : ℕ}
    (h : m' ≤ m) {y : BitString} (hy : y ∈ snapshotRichElementsList c i j m t) :
    y ∈ snapshotRichElementsList c i j m' t := by
  unfold snapshotRichElementsList at *
  simp_all +decide only [List.filter_flatten, List.mem_flatten, List.mem_map,
    exists_exists_and_eq_and, List.mem_filter, decide_eq_true_eq]
  exact ⟨ _, hy.choose_spec.1, hy.choose_spec.2.1, le_trans ( pow_le_pow_right₀ (
      by decide ) h ) hy.choose_spec.2.2 ⟩

/-
Every element of every emitted chunk has multiplicity at least `2^(k-1)` in the
size-restricted description list at the same time.  Elements placed at an earlier time
stay above threshold by monotonicity of the multiplicity.
-/
theorem emittedHalfRichChunksList_flatten_half_rich (c : Code) (i j k t : ℕ) :
    ∀ y ∈ (emittedHalfRichChunksList c i j k t).flatten,
      2 ^ (k - 1) ≤ (snapshotDescList c i j t).countP (fun S => decide (y ∈ S)) := by
  -- The two invariants used at every time `s` do not depend on `t`: every rich
  -- element is `(k-1)`-rich (`hRich`), and every `(k-1)`-rich element has
  -- multiplicity at least `2^(k-1)` in the description list (`hMult`).
  have hRich : ∀ s z, z ∈ (snapshotRichElementsList c i j k s).eraseDups → z ∈
      (snapshotRichElementsList c i j (k - 1) s).eraseDups := by
    intro s z hz
    have hz' : z ∈ snapshotRichElementsList c i j k s := mem_eraseDups_iff.mp hz
    exact mem_eraseDups_iff.mpr
      (snapshotRichElementsList_subset_threshold c i j s (Nat.sub_le k 1) hz')
  have hMult : ∀ s z, z ∈ (snapshotRichElementsList c i j (k - 1) s).eraseDups → 2 ^ (k - 1) ≤
      (snapshotDescList c i j s).countP (fun S => decide (z ∈ S)) := fun s z hz =>
    mem_snapshotRichElementsList_multiplicity c i j (k - 1) s (mem_eraseDups_iff.mp hz)
  induction t with
  | zero =>
    intro y hy
    simp only [emittedHalfRichChunksList, emittedHalfRichChunks_step] at hy
    rcases emittedHalfRichChunks_foldStep_flatten_mem_or j _ _ [] (hRich 0) y hy with h | h
    · simp at h
    · exact hMult 0 y h
  | succ t ih =>
    intro y hy
    rw [emittedHalfRichChunksList] at hy
    unfold emittedHalfRichChunks_step at hy
    rw [List.mem_flatten] at hy
    obtain ⟨l, hl₁, hl₂⟩ := hy
    have h_ind : y ∈ (emittedHalfRichChunksList c i j k t).flatten ∨ y ∈
        (snapshotRichElementsList c i j (k - 1) (t + 1)).eraseDups :=
      emittedHalfRichChunks_foldStep_flatten_mem_or j _ _ _ (hRich (t + 1)) y
        (List.mem_flatten.mpr ⟨l, hl₁, hl₂⟩)
    cases h_ind with
    | inl h_old =>
      rw [List.mem_flatten] at h_old
      obtain ⟨l, hl, hyl⟩ := h_old
      exact le_trans (ih y (List.mem_flatten.mpr ⟨l, hl, hyl⟩))
        (snapshotDescList_countP_mono c i j y (Nat.le_succ _))
    | inr h => exact hMult (t + 1) y h

/-
Each emitted chunk list is nonempty (its first element is the triggering element).
-/
theorem emittedHalfRichChunksList_mem_ne_nil (c : Code) (i j k t : ℕ) :
    ∀ l ∈ emittedHalfRichChunksList c i j k t, l ≠ [] := by
  induction t with
  | zero =>
    exact emittedHalfRichChunks_fold_step_mem_ne_nil j _ _ [] (by simp)
  | succ t ih =>
    exact emittedHalfRichChunks_fold_step_mem_ne_nil j _ _ _ ih

/-
The list of emitted chunks (as finsets) has no duplicates: the chunks are
pairwise disjoint and nonempty, hence distinct as finsets.
-/
theorem emittedHalfRichChunks_nodup (c : Code) (i j k t : ℕ) :
    (emittedHalfRichChunks c i j k t).Nodup := by
  unfold emittedHalfRichChunks;
  have h_nodup : List.Nodup (emittedHalfRichChunksList c i j k t).flatten ∧ ∀ l ∈
      emittedHalfRichChunksList c i j k t, l ≠ [] := by
    exact ⟨ emittedHalfRichChunksList_flatten_nodup c i j k t,
      emittedHalfRichChunksList_mem_ne_nil c i j k t ⟩;
  have h_disjoint : List.Pairwise List.Disjoint _ := (List.nodup_flatten.mp h_nodup.1).2
  have H : List.Pairwise (fun a b => a.toFinset ≠ b.toFinset)
      (emittedHalfRichChunksList c i j k t) := by
    apply List.Pairwise.imp_of_mem _ h_disjoint
    intro a b ha hb hab heq
    have h_not_disj : ¬ List.Disjoint a b := by
      intro h_disj
      have h_sub : a ⊆ b := by
        intro x hx
        have hx2 : x ∈ a.toFinset := List.mem_toFinset.mpr hx
        rw [heq] at hx2
        exact List.mem_toFinset.mp hx2
      cases a with
      | nil => exact h_nodup.2 _ ha rfl
      | cons x xs =>
        have hx : x ∈ x :: xs := List.Mem.head _
        exact h_disj hx (h_sub hx)
    exact h_not_disj hab
  exact List.pairwise_map.mpr H
/-
The size-restricted description list has no duplicate descriptions.
-/
theorem snapshotDescList_nodup (c : Code) (i j t : ℕ) :
    (snapshotDescList c i j t).Nodup := by
  -- We already proved `snapshotDescList_nodup_map_toFinset c i j t` of type
  -- `((snapshotDescList c i j t).map List.toFinset).Nodup ∧ ...`.
  -- By `List.Nodup.of_map`, this implies `(snapshotDescList c i j t).Nodup`.
  exact
    List.Nodup.of_map List.toFinset
      (snapshotDescList_nodup_map_toFinset c i j t).1

/-- A double-counting bound for bipartite incidence of half-rich elements in descriptions. -/
theorem bipartite_incidence_bound (c : Code) (i j k : ℕ) (t : ℕ) :
    ((emittedHalfRichChunks c i j k t).filter (fun S => S.card = 2 ^ j)).length * 2 ^ (j + k - 1) ≤
      (snapshotDescList c i j t).length * 2 ^ j := by
  have hcore : ((List.filter (fun S => S.card = 2 ^ j) (emittedHalfRichChunks c i j k t)).length) *
      2 ^ (k - 1) ≤ ( snapshotDescList c i j t ).length := by
    set Full := (List.filter (fun S => S.card = 2 ^ j) (emittedHalfRichChunks c i j k t))
    set desc := snapshotDescList c i j t
    set D := desc.length;
    have hcore : ∑ S ∈ Full.toFinset, ∑ y ∈ S, (desc.countP (fun S' => decide (y ∈ S'))) ≥
        Full.length * 2 ^ j * 2 ^ (k - 1) := by
      have hcore : ∀ S ∈ Full.toFinset, ∑ y ∈ S, (desc.countP (fun S' => decide (y ∈ S'))) ≥ 2 ^ j *
          2 ^ (k - 1) := by
        intros S hS
        have h_mult : ∀ y ∈ S, 2 ^ (k - 1) ≤ desc.countP (fun S' => y ∈ S') := by
          intro y hy; have := emittedHalfRichChunksList_flatten_half_rich c i j k t; simp_all
            +decide ;
          obtain ⟨ l, hl₁, hl₂ ⟩ := List.mem_map.mp ( List.mem_filter.mp hS |>.1 ) ; aesop;
        refine le_trans ?_ ( Finset.sum_le_sum h_mult ) ; aesop;
      refine le_trans ?_ ( Finset.sum_le_sum hcore );
      rw [ ← List.toFinset_card_of_nodup ];
      · norm_num [ mul_assoc ];
      · exact List.Nodup.filter _ ( emittedHalfRichChunks_nodup c i j k t );
    have hcore : ∑ S ∈ Full.toFinset, ∑ y ∈ S, (desc.countP (fun S' => decide (
        y ∈ S'))) ≤ D * 2 ^ j := by
      have hcore_upper : ∀ S' ∈ desc.toFinset, ∑ S ∈ Full.toFinset, (S ∩ S'.toFinset).card ≤
          S'.length := by
        intros S' hS'
        have h_disjoint : ∀ S₁ S₂, S₁ ∈ Full.toFinset → S₂ ∈ Full.toFinset → S₁ ≠ S₂ → Disjoint S₁
            S₂ := by
          intros S₁ S₂ hS₁ hS₂ hne
          have h_disjoint : ∀ l₁ l₂, l₁ ∈ emittedHalfRichChunksList c i j k t → l₂ ∈
              emittedHalfRichChunksList c i j k t → l₁ ≠ l₂ → Disjoint l₁.toFinset l₂.toFinset := by
            intros l₁ l₂ hl₁ hl₂ hne
            have h_disjoint : List.Pairwise (fun l₁ l₂ => List.Disjoint l₁ l₂)
                (emittedHalfRichChunksList c i j k t) := by
              exact List.nodup_flatten.mp (
                  emittedHalfRichChunksList_flatten_nodup c i j k t ) |>.2;
            rw [ List.pairwise_iff_get ] at h_disjoint;
            obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hl₁; obtain ⟨ j,
              hj ⟩ := List.mem_iff_get.mp hl₂; cases lt_trichotomy i j <;> simp_all +decide [
                List.disjoint_iff_ne ] ;
            · grind;
            · grind;
          change S₁ ∈ (List.filter (fun S => S.card = 2 ^ j)
            (emittedHalfRichChunks c i j k t)).toFinset at hS₁
          change S₂ ∈ (List.filter (fun S => S.card = 2 ^ j)
            (emittedHalfRichChunks c i j k t)).toFinset at hS₂
          have hS₁' := (List.mem_filter.mp (List.mem_toFinset.mp hS₁)).1
          have hS₂' := (List.mem_filter.mp (List.mem_toFinset.mp hS₂)).1
          obtain ⟨l₁, hl₁, rfl⟩ := List.mem_map.mp hS₁'
          obtain ⟨l₂, hl₂, rfl⟩ := List.mem_map.mp hS₂'
          exact h_disjoint l₁ l₂ hl₁ hl₂ fun h_eq => hne (congrArg List.toFinset h_eq)
        rw [ ← Finset.card_biUnion ];
        · exact le_trans ( Finset.card_le_card (
            show _ ⊆ S'.toFinset from Finset.biUnion_subset.mpr fun x hx =>
              Finset.inter_subset_right ) ) ( List.toFinset_card_le _ );
        · exact fun x hx y hy hxy => Disjoint.mono inf_le_left inf_le_left (
            h_disjoint x y hx hy hxy );
      have hcore_upper : ∑ S ∈ Full.toFinset, ∑ y ∈ S, (desc.countP (fun S' => decide (y ∈ S'))) = ∑
          S' ∈ desc.toFinset, ∑ S ∈ Full.toFinset, (S ∩ S'.toFinset).card := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl ];
        intros S hS
        have hcore_upper : ∀ y ∈ S, (desc.countP (fun S' => decide (y ∈ S'))) = ∑ S' ∈
            desc.toFinset, (if y ∈ S' then 1 else 0) := by
          intros y hy; rw [ List.countP_eq_length_filter ]
          simp +decide only [Finset.sum_boole, Nat.cast_id]
          rw [ ← Multiset.coe_card ] ; rw [ ← Multiset.toFinset_card_of_nodup ]
          · aesop
          · exact List.Nodup.filter _ ( snapshotDescList_nodup c i j t )
        rw [ Finset.sum_congr rfl hcore_upper, Finset.sum_comm ];
        simp +decide only [Finset.sum_boole, Nat.cast_id]
        exact Finset.sum_congr rfl fun x hx => congr_arg Finset.card <| by ext; aesop;
      refine hcore_upper.symm ▸ le_trans ( Finset.sum_le_sum ‹_› ) ?_;
      refine le_trans ( Finset.sum_le_sum fun x hx => show x.length ≤ 2 ^ j from ?_ ) ?_;
      · change x ∈ (snapshotDescList c i j t).toFinset at hx
        rw [List.mem_toFinset] at hx
        unfold snapshotDescList at hx
        rw [List.mem_filter] at hx
        exact of_decide_eq_true hx.2
      · simp +zetaDelta only [Finset.sum_const, smul_eq_mul, Nat.ofNat_pos, pow_pos,
          mul_le_mul_iff_left₀] at *
        exact List.toFinset_card_le _;
    nlinarith [ pow_pos ( zero_lt_two' ℕ ) j ];
  cases k with
  | zero =>
    simp only [zero_tsub, pow_zero, mul_one, add_zero] at hcore ⊢
    exact Nat.mul_le_mul hcore (Nat.pow_le_pow_right (by decide) (Nat.pred_le _))
  | succ k =>
    rw [show k + 1 - 1 = k by omega] at hcore
    rw [show j + (k + 1) - 1 = j + k by omega, pow_add]
    calc
      _ = _ * 2 ^ j := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hcore

/-- Full chunks are bounded by the half-rich incidence count, `<= 2^(i - k + O(1))`.

This is derived from the two structural obligations
`bipartite_incidence_bound` and `snapshotDescList_length_le` by elementary
`Nat`-power arithmetic:
`F * 2^(j+k-1) ≤ D * 2^j ≤ 2^(i+1) * 2^j`, and since
`(i+1)+j ≤ (i-k+2)+(j+k-1)` in `ℕ` (truncated subtraction, `omega`-checkable),
cancelling the common factor `2^(j+k-1)` gives `F ≤ 2^(i-k+2)`. -/
theorem emittedHalfRichChunks_full_count_le (U : Map) (c : Code) (_hc : IsCodeFor c U) (i j k : ℕ)
    (t : ℕ) :
    ((emittedHalfRichChunks c i j k t).filter (fun S => S.card = 2 ^ j)).length ≤ 2 ^ (
      i - k + 2) := by
  have hbip := bipartite_incidence_bound c i j k t
  have hlen := snapshotDescList_length_le c i j t
  set F := ((emittedHalfRichChunks c i j k t).filter (fun S => S.card = 2 ^ j)).length with hF
  set D := (snapshotDescList c i j t).length with hD
  -- `F * 2^(j+k-1) ≤ D * 2^j ≤ 2^(i+1) * 2^j`.
  have h1 : F * 2 ^ (j + k - 1) ≤ 2 ^ (i + 1) * 2 ^ j :=
    le_trans hbip (by gcongr)
  -- Bound the RHS by `2^(i-k+2) * 2^(j+k-1)` via a single-exponent comparison.
  have h2 : F * 2 ^ (j + k - 1) ≤ 2 ^ (i - k + 2) * 2 ^ (j + k - 1) := by
    refine le_trans h1 ?_
    rw [← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

/-- The length of the description list equals the cardinality of the abstract
size-restricted description universe.  Distinct canonical-uniform codes give
distinct supports, so `snapshotDescList` enumerates `snapshotDescriptionsAndSizeLe`
without duplicates; hence counting list entries and finset elements agree.

This is the bridge for the non-full chunk charging argument: the right-hand side
`(snapshotDescList c i j t).length` equals the *finset* cardinality
`(snapshotDescriptionsAndSizeLe c i j t).card`, which is monotone in `t` via
`snapshotDescriptionsAndSizeLe_subset_of_le`.  The temporal "fresh descriptions"
must therefore be charged at the finset level (new elements of the growing finset
on disjoint time intervals), not as appended list suffixes — `snapshotDescList`
is not itself list-append-monotone in `t`. -/
theorem snapshotDescList_length_eq_card (c : Code) (i j t : ℕ) :
    (snapshotDescList c i j t).length = (snapshotDescriptionsAndSizeLe c i j t).card := by
  obtain ⟨hnodup, hset⟩ := snapshotDescList_nodup_map_toFinset c i j t
  rw [← hset, List.toFinset_card_of_nodup hnodup, List.length_map]

/-
Fold helper.  If some `half_rich` element `y` remains unplaced at the end of a
`emittedHalfRichChunks_fold_step` left fold, then every chunk appended during the
fold (present in the result but not in the starting accumulator `acc`) is full,
i.e. has length `2 ^ j`.  Contrapositively: a single non-full appended chunk
forces *every* `half_rich` element to be placed.
-/
theorem emittedHalfRichChunks_foldStep_unplaced_full (j : ℕ) (half_rich L : List BitString)
    (acc : List (List BitString)) (y : BitString)
    (hy_hr : y ∈ half_rich)
    (hy_unplaced : y ∉ (L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc).flatten) :
    ∀ S ∈ L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc,
      S ∉ acc → S.length = 2 ^ j := by
  induction L using List.reverseRecOn generalizing acc y
  case' nil => simp_all +decide
  case' append_singleton L ih _ => simp_all +decide only [List.mem_flatten, not_exists,
    not_and, List.foldl_append, List.foldl_cons, emittedHalfRichChunks_fold_step,
    Bool.cond_true_right, Bool.or_false, List.filter_filter, List.foldl_nil]
  rename_i h
  specialize h acc y hy_hr
  by_cases h' : ∃ l ∈ List.foldl (emittedHalfRichChunks_fold_step j half_rich) acc L,
      ih ∈ l
  · simp_all +decide only [decide_true, cond_true, not_false_eq_true, implies_true,
      forall_const]
  · simp_all +decide only [decide_false, cond_false, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, true_or, not_false_eq_true, implies_true, forall_const,
      not_exists, not_and]
    by_contra h_contra;
    have h_new_chunk_length : y ∈ List.take (2 ^ j)
        (ih :: List.filter (fun a => !decide (a = ih) && !decide (
          ∃ l ∈ List.foldl (emittedHalfRichChunks_fold_step j half_rich) acc L,
            a ∈ l)) half_rich) := by
      rw [ List.take_of_length_le ]; all_goals grind;
    exact hy_unplaced _ ( Or.inr rfl ) h_new_chunk_length

/-
A chunk is emitted at time `t` if it appears in `emittedHalfRichChunks` at time
`t` but not at `t-1` (or is present at time 0).
At the emission time of a non-full chunk, all half-rich elements are placed.
-/
theorem nonfull_chunk_emit_time (c : Code) (i j k : ℕ) (t : ℕ) (S : Finset BitString)
    (h_emit : S ∈ emittedHalfRichChunks c i j k t)
    (h_new : t > 0 → S ∉ emittedHalfRichChunks c i j k (t - 1))
    (h_nonfull : S.card < 2 ^ j) :
    ∀ x ∈ snapshotRichElementsList c i j (k - 1) t,
      x ∈ (emittedHalfRichChunksList c i j k t).flatten := by
  obtain ⟨l, hl⟩ : ∃ l ∈ emittedHalfRichChunksList c i j k t, l.toFinset = S := by
    unfold emittedHalfRichChunks at h_emit; aesop;
  have h_l_nodup : l.Nodup := by
    have := emittedHalfRichChunksList_flatten_nodup c i j k t;
    exact List.Nodup.sublist ( List.sublist_flatten_of_mem hl.1 ) this;
  have h_l_not_in_acc : l ∉ (if t > 0 then
      emittedHalfRichChunksList c i j k (t - 1) else []) := by
    by_cases ht : t > 0
    · simp only [ht, if_true]
      intro h_prev
      apply h_new ht
      unfold emittedHalfRichChunks
      exact List.mem_map.mpr ⟨l, h_prev, hl.2⟩
    · simp only [ht, if_false, List.not_mem_nil]
      exact not_false
  by_contra h_contra; push Not at h_contra;
  obtain ⟨x, hx_rich, hx_unplaced⟩ := h_contra
  have hx_half_rich : x ∈ (snapshotRichElementsList c i j (k - 1) t).eraseDups := by
    have h_eraseDups : ∀ {L : List BitString}, x ∈ L → x ∈ L.eraseDups := by
      intros L hL; induction L using List.reverseRecOn
      case' nil => simp_all +decide
      case' append_singleton L ih _ => simp_all +decide [ List.eraseDups_append ]
      grind
    exact h_eraseDups hx_rich
  have hx_unplaced_fold : x ∉ (List.foldl
      (emittedHalfRichChunks_fold_step j
        (snapshotRichElementsList c i j (k - 1) t).eraseDups)
      (if t > 0 then emittedHalfRichChunksList c i j k (t - 1) else [])
      (snapshotRichElementsList c i j k t).eraseDups).flatten := by
    cases t with
    | zero =>
      simpa only [emittedHalfRichChunksList, emittedHalfRichChunks_step, gt_iff_lt,
        lt_self_iff_false, ↓reduceIte] using hx_unplaced
    | succ t =>
      simpa only [emittedHalfRichChunksList, emittedHalfRichChunks_step, gt_iff_lt,
        lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, ↓reduceIte,
        add_tsub_cancel_right] using hx_unplaced
  have h_l_length : l.length = 2 ^ j := by
    apply emittedHalfRichChunks_foldStep_unplaced_full j
      (snapshotRichElementsList c i j (k - 1) t).eraseDups
      (snapshotRichElementsList c i j k t).eraseDups
      (if t > 0 then emittedHalfRichChunksList c i j k (t - 1) else []) x
      hx_half_rich hx_unplaced_fold l (by
    cases t <;> simp_all +decide only [emittedHalfRichChunksList, gt_iff_lt,
      lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, ↓reduceIte,
      add_tsub_cancel_right]
    · unfold emittedHalfRichChunks_step at hl; aesop;
    · exact hl.1) (by
    exact h_l_not_in_acc)
  have h_l_card : S.card = 2 ^ j := by
    rw [ ← hl.2, List.toFinset_card_of_nodup h_l_nodup, h_l_length ]
  linarith [h_nonfull]

/-
A trigger element that moves from not-half-rich to rich must gain at least
`2^(k-1)` fresh descriptions in `snapshotDescriptionsAndSizeLe` during that
time interval.
-/
theorem trigger_gains_fresh_finset (c : Code) (i j k : ℕ) (t₁ t₂ : ℕ) (y : BitString)
    (h_not_half_rich : y ∉ snapshotRichElementsList c i j (k - 1) t₁)
    (h_rich : y ∈ snapshotRichElementsList c i j k t₂) :
    2 ^ (k - 1) ≤
        ((snapshotDescriptionsAndSizeLe c i j t₂).filter (fun S => y ∈ S) \
          (snapshotDescriptionsAndSizeLe c i j t₁).filter (fun S => y ∈ S)).card := by
  rw [Finset.card_sdiff]
  apply Nat.le_sub_of_add_le'
  -- Since $y$ is not half-rich at $t₁$, the number of descriptions containing
  --   $y$ at $t₁$ is less than $2^{k-1}$.
  have h_count_lt : ((snapshotDescriptionsAndSizeLe c i j t₁).filter (fun S => y ∈ S)).card < 2 ^
      (k - 1) := by
    contrapose! h_not_half_rich;
    unfold snapshotRichElementsList; simp_all +decide [ List.mem_filter ] ;
    have h_card_le : (snapshotDescList c i j t₁).countP (fun S => decide (y ∈ S)) ≥
        (Finset.filter (fun S => y ∈ S) (snapshotDescriptionsAndSizeLe c i j t₁)).card := by
      rw [ snapshotDescList_countP_eq_card ];
    have h_card_le : ∃ S ∈ snapshotDescList c i j t₁, y ∈ S := by
      exact List.countP_pos_iff.mp (lt_of_lt_of_le (by
        linarith [Nat.one_le_pow (k - 1) 2 zero_lt_two]) h_card_le) |>
          fun ⟨S, hS⟩ => ⟨S, by aesop⟩
    grind;
  -- Since $y$ is rich at $t₂$, the number of descriptions containing $y$ at
  --   $t₂$ is at least $2^k$.
  have h_count_ge :
      ((snapshotDescriptionsAndSizeLe c i j t₂).filter (fun S => y ∈ S)).card ≥ 2 ^ k := by
    have := mem_snapshotRichElementsList_multiplicity c i j k t₂ h_rich
    simp_all +decide [snapshotDescList_countP_eq_card]
  have h_inter : Finset.card (Finset.filter (fun S => y ∈ S)
      (snapshotDescriptionsAndSizeLe c i j t₁) ∩ Finset.filter (fun S => y ∈ S)
        (snapshotDescriptionsAndSizeLe c i j t₂)) ≤ Finset.card (Finset.filter
          (fun S => y ∈ S) (snapshotDescriptionsAndSizeLe c i j t₁)) :=
    Finset.card_le_card Finset.inter_subset_left
  cases k with
  | zero =>
    simp only [zero_tsub, pow_zero] at h_count_lt h_count_ge ⊢
    omega
  | succ k =>
    simp only [Nat.succ_sub_one, pow_succ'] at h_count_lt h_count_ge ⊢
    omega

/-- The emission time of the `m`-th nonfull chunk up to time `t`.
Returns 0 if `m` is out of bounds. -/
def nonfullChunkEmissionTime (c : Code) (i j k t m : ℕ) : ℕ :=
  let chunks := emittedHalfRichChunksList c i j k t
  let nonfull := chunks.filter (fun l => l.length < 2 ^ j)
  match (nonfull.drop m).head? with
  | none => 0
  | some l =>
    (List.range (t + 1)).find? (fun τ => l ∈ emittedHalfRichChunksList c i j k τ) |>.getD 0

/-- The trigger element of the `m`-th nonfull chunk up to time `t`.
Returns an empty list (default bitstring) if `m` is out of bounds. -/
def nonfullChunkTrigger (c : Code) (i j k t m : ℕ) : BitString :=
  let chunks := emittedHalfRichChunksList c i j k t
  let nonfull := chunks.filter (fun l => l.length < 2 ^ j)
  match (nonfull.drop m).head? with
  | none => []
  | some [] => []
  | some (x::_) => x

/-- At time `0` the step budget is exhausted, so no program has produced output yet
and the snapshot description list is empty. -/
theorem snapshotDescList_zero (c : Code) (i j : ℕ) : snapshotDescList c i j 0 = [] := by
  have h : snapshotCodes c i 0 = [] := by
    simp only [snapshotCodes]
    rw [List.filterMap_eq_nil_iff]
    intro p _
    simp only [runOut]
    have he : Code.evaln 0 c (Encodable.encode ((p, []) : BitString × BitString)) = none := by
      rw [Option.eq_none_iff_forall_not_mem]
      intro x hx
      exact absurd (Nat.Partrec.Code.evaln_bound hx) (by omega)
    rw [he]; rfl
  simp only [snapshotDescList, h, List.filter_nil, List.toFinset_nil,
    canonicalFinsetList, Finset.sort_empty, List.map_nil]

/-- Consequently there are no rich elements at time `0`. -/
theorem snapshotRichElementsList_zero (c : Code) (i j k : ℕ) :
    snapshotRichElementsList c i j k 0 = [] := by
  simp only [snapshotRichElementsList, snapshotDescList_zero, List.flatten_nil,
    List.filter_nil]

/-- The emission time of any nonfull chunk (found within `List.range (t + 1)`) is at
most `t`. -/
theorem nonfullChunkEmissionTime_le (c : Code) (i j k t m : ℕ) :
    nonfullChunkEmissionTime c i j k t m ≤ t := by
  have key : ∀ (o : Option ℕ), (∀ τ ∈ o, τ ≤ t) → o.getD 0 ≤ t := by
    intro o ho
    cases o with
    | none => simp
    | some τ => exact ho τ rfl
  simp only [nonfullChunkEmissionTime]
  split
  · exact Nat.zero_le t
  · apply key
    intro τ hτ
    rw [Option.mem_def] at hτ
    have hmem := List.mem_of_find?_eq_some hτ
    rw [List.mem_range] at hmem
    omega

/-- The emitted online stream list grows by one step: `t+1` extends `t` by a
suffix. -/
theorem emittedHalfRichChunksList_succ_append (c : Code) (i j k t : ℕ) :
    ∃ rest, emittedHalfRichChunksList c i j k (t + 1)
      = emittedHalfRichChunksList c i j k t ++ rest := by
  obtain ⟨r, hr⟩ := emittedHalfRichChunks_foldStep_append j
    ((snapshotRichElementsList c i j (k - 1) (t + 1)).eraseDups)
    ((snapshotRichElementsList c i j k (t + 1)).eraseDups)
    (emittedHalfRichChunksList c i j k t)
  exact ⟨r, by simpa [emittedHalfRichChunksList, emittedHalfRichChunks_step] using hr⟩

/-- The emitted online stream list is monotone: any later stage extends an
earlier one by a suffix. -/
theorem emittedHalfRichChunksList_prefix (c : Code) (i j k : ℕ) {t t' : ℕ} (h : t ≤ t') :
    ∃ rest, emittedHalfRichChunksList c i j k t'
      = emittedHalfRichChunksList c i j k t ++ rest := by
  induction t'
  case' zero => exact ⟨[], by simp [Nat.le_zero.mp h]⟩
  case' succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with hlt | heq
      · obtain ⟨r1, hr1⟩ := ih (Nat.lt_succ_iff.mp hlt)
        obtain ⟨r2, hr2⟩ := emittedHalfRichChunksList_succ_append c i j k n
        exact ⟨r1 ++ r2, by rw [hr2, hr1, List.append_assoc]⟩
      · subst heq; exact ⟨[], by simp⟩

/-- The list of emitted chunks (as lists) has no duplicates: it is the preimage,
under the injective-on-this-list map `List.toFinset`, of the nodup finset list. -/
theorem emittedHalfRichChunksList_Nodup (c : Code) (i j k t : ℕ) :
    (emittedHalfRichChunksList c i j k t).Nodup := by
  have hmap := emittedHalfRichChunks_nodup c i j k t
  unfold emittedHalfRichChunks at hmap
  exact hmap.of_map _

/-- Filtering the emitted-chunk list commutes with the time-prefix structure: a
later filtered list extends an earlier one by a suffix. -/
theorem emittedHalfRichChunksList_filter_prefix (c : Code) (i j k : ℕ) {t t' : ℕ}
    (h : t ≤ t') (P : List BitString → Bool) :
    ∃ rest, (emittedHalfRichChunksList c i j k t').filter P
      = (emittedHalfRichChunksList c i j k t).filter P ++ rest := by
  obtain ⟨rest, hrest⟩ := emittedHalfRichChunksList_prefix c i j k h
  exact ⟨rest.filter P, by rw [hrest, List.filter_append]⟩

/-- The number of nonfull chunks (list form) is monotone in time. -/
theorem emittedHalfRichChunksList_numNonfull_mono (c : Code) (i j k : ℕ) {t t' : ℕ}
    (h : t ≤ t') :
    ((emittedHalfRichChunksList c i j k t).filter (fun l => l.length < 2 ^ j)).length
      ≤ ((emittedHalfRichChunksList c i j k t').filter (fun l => l.length < 2 ^ j)).length := by
  obtain ⟨rest, hrest⟩ :=
    emittedHalfRichChunksList_filter_prefix c i j k h (fun l => l.length < 2 ^ j)
  rw [hrest, List.length_append]
  exact Nat.le_add_right _ _

/-
**Fold-level: a single online step appends at most one nonfull chunk.**
Processing the rich stream `L` (all of whose elements are half-rich, `hL`)
by `emittedHalfRichChunks_fold_step` from accumulator `acc` increases the number
of nonfull (length `< 2^j`) chunks by at most one; and if it does increase the
count, then afterwards every half-rich element has been placed into the flatten.
The second conjunct is the invariant that makes the induction go through: once a
nonfull chunk is opened it swallows all currently-unplaced half-rich elements,
so no further chunk can ever be opened in the same step.
-/
theorem emittedHalfRichChunks_foldStep_nonfull_count (j : ℕ) (half_rich : List BitString)
    (L : List BitString) (acc : List (List BitString)) (hL : ∀ x ∈ L, x ∈ half_rich) :
    ((L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc).filter
        (fun l => l.length < 2 ^ j)).length
      ≤ (acc.filter (fun l => l.length < 2 ^ j)).length + 1
    ∧ ((acc.filter (fun l => l.length < 2 ^ j)).length + 1
        ≤ ((L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc).filter
            (fun l => l.length < 2 ^ j)).length
      → ∀ y ∈ half_rich,
          y ∈ (L.foldl (emittedHalfRichChunks_fold_step j half_rich) acc).flatten) := by
  induction L using List.reverseRecOn generalizing acc with
  | nil => simp_all +decide
  | append_singleton L x ih =>
      have hL' : ∀ y ∈ L, y ∈ half_rich := by
        intro y hy
        exact hL y (List.mem_append.mpr (Or.inl hy))
      have hx_half : x ∈ half_rich :=
        hL x (List.mem_append.mpr (Or.inr (List.mem_singleton_self x)))
      let prev := List.foldl (emittedHalfRichChunks_fold_step j half_rich) acc L
      have ih' := ih acc hL'
      change
        ((prev.filter (fun l => l.length < 2 ^ j)).length ≤
          (acc.filter (fun l => l.length < 2 ^ j)).length + 1) ∧
        ((acc.filter (fun l => l.length < 2 ^ j)).length + 1 ≤
            (prev.filter (fun l => l.length < 2 ^ j)).length →
          ∀ y ∈ half_rich, y ∈ prev.flatten) at ih'
      by_cases hx_prev : x ∈ prev.flatten
      · have hdec : decide (x ∈ prev.flatten) = true := decide_eq_true hx_prev
        simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil,
          emittedHalfRichChunks_fold_step, prev, hdec, cond_true] using ih'
      · have hdec : decide (x ∈ prev.flatten) = false := decide_eq_false hx_prev
        let unplaced := half_rich.filter (fun y =>
          bif decide (y ∈ prev.flatten) then false else true)
        let base := x :: unplaced.filter (fun y =>
          bif decide (y = x) then false else true)
        let newChunk := base.take (2 ^ j)
        have hstep : emittedHalfRichChunks_fold_step j half_rich prev x =
            prev ++ [newChunk] := by
          simp only [emittedHalfRichChunks_fold_step, hdec, cond_false, unplaced,
            base, newChunk]
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hstep]
        by_cases hnew : newChunk.length < 2 ^ j
        · have hprev_le : (prev.filter (fun l => l.length < 2 ^ j)).length ≤
              (acc.filter (fun l => l.length < 2 ^ j)).length := by
            apply Nat.le_of_not_gt
            intro hinc
            exact hx_prev (ih'.2 (by omega) x hx_half)
          have hcount :
              ((prev ++ [newChunk]).filter (fun l => l.length < 2 ^ j)).length =
                (prev.filter (fun l => l.length < 2 ^ j)).length + 1 := by
            simp +decide [hnew]
          constructor
          · rw [hcount]
            exact Nat.add_le_add_right hprev_le 1
          · intro _ y hy
            by_cases hy_prev : y ∈ prev.flatten
            · simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
                List.append_nil, List.mem_append] using Or.inl hy_prev
            · have hbase_le : base.length ≤ 2 ^ j := by
                simp only [newChunk, List.length_take] at hnew
                omega
              have hy_base : y ∈ base := by
                by_cases hyx : y = x
                · exact List.mem_cons.mpr (Or.inl hyx)
                · apply List.mem_cons.mpr
                  apply Or.inr
                  apply List.mem_filter.mpr
                  refine ⟨?_, ?_⟩
                  · apply List.mem_filter.mpr
                    refine ⟨hy, ?_⟩
                    rw [decide_eq_false hy_prev]
                    exact rfl
                  · rw [decide_eq_false hyx]
                    exact rfl
              have hy_new : y ∈ newChunk := by
                simpa only [newChunk, List.take_of_length_le hbase_le] using hy_base
              simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
                List.append_nil, List.mem_append] using Or.inr hy_new
        · have hcount :
              ((prev ++ [newChunk]).filter (fun l => l.length < 2 ^ j)).length =
                (prev.filter (fun l => l.length < 2 ^ j)).length := by
            simp +decide [hnew]
          constructor
          · rw [hcount]
            exact ih'.1
          · intro hinc y hy
            rw [hcount] at hinc
            have hy_prev := ih'.2 hinc y hy
            simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
              List.append_nil, List.mem_append] using Or.inl hy_prev

/-
A single online time step appends at most one nonfull chunk.
-/
theorem emittedHalfRichChunksList_numNonfull_succ_le (c : Code) (i j k t : ℕ) :
    ((emittedHalfRichChunksList c i j k (t + 1)).filter (fun l => l.length < 2 ^ j)).length
      ≤ ((emittedHalfRichChunksList c i j k t).filter (fun l => l.length < 2 ^ j)).length + 1 := by
  have h_eraseDups : ∀ {L : List BitString} {x : BitString}, x ∈ L.eraseDups ↔ x ∈ L := by
    intros L x; induction L using List.reverseRecOn generalizing x
    case' nil => simp_all +decide
    case' append_singleton L ih _ => simp_all +decide [ List.eraseDups_append ]
    simp_all +decide [ List.removeAll ];
    grind;
  exact emittedHalfRichChunks_foldStep_nonfull_count j _ _ _ (fun x hx =>
    h_eraseDups.mpr
    (snapshotRichElementsList_subset_threshold _ _ _ _ (Nat.sub_le _ _)
      (h_eraseDups.mp hx))) |>.left

/-
At time `0` at most one nonfull chunk exists (the first online step opens at
most one nonfull chunk from the empty accumulator).
-/
theorem emittedHalfRichChunksList_numNonfull_zero_le (c : Code) (i j k : ℕ) :
    ((emittedHalfRichChunksList c i j k 0).filter (fun l => l.length < 2 ^ j)).length ≤ 1 := by
  simp only [emittedHalfRichChunksList, emittedHalfRichChunks_step,
    snapshotRichElementsList_zero, List.eraseDups_nil, List.foldl_nil,
    List.filter_nil, List.length_nil, Nat.zero_le]

/-
The finset-form and list-form counts of nonfull chunks agree.
-/
theorem emittedHalfRich_nonfull_len_eq (c : Code) (i j k t : ℕ) :
    ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length
      = ((emittedHalfRichChunksList c i j k t).filter (fun l => l.length < 2 ^ j)).length := by
  rw [ emittedHalfRichChunks, List.filter_map ];
  rw [ List.length_map, List.filter_congr ];
  intro x hx;
  have := List.Nodup.sublist (List.sublist_flatten_of_mem hx)
    (emittedHalfRichChunksList_flatten_nodup c i j k t);
  simp_all +decide [ List.toFinset_card_of_nodup ];

/-
Emission times of consecutive nonfull chunks are strictly increasing.
-/
theorem nonfullChunkEmissionTime_strict_mono (c : Code) (i j k t m : ℕ)
    (h_lt : m + 1 < ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length) :
    nonfullChunkEmissionTime c i j k t m < nonfullChunkEmissionTime c i j k t (m + 1) := by
  -- The final nonfull-chunk list preserves the chronological order of first
  -- emission times, and distinct nonempty chunks cannot first appear at the
  -- same time.
  obtain ⟨l_m, hl_m⟩ : ∃ l_m,
      (List.drop m (List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k t))).head? = some l_m := by
    simp +zetaDelta only [List.head?_drop] at *;
    rw [ emittedHalfRich_nonfull_len_eq ] at h_lt;
    exact ⟨ _, List.getElem?_eq_getElem <| by linarith ⟩;
  obtain ⟨l₁, hl₁⟩ : ∃ l₁,
      (List.drop (m + 1) (List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k t))).head? = some l₁ := by
    simp_all +decide [ emittedHalfRich_nonfull_len_eq ];
  have h_mem_iff_count : ∀ τ ≤ t, l_m ∈ emittedHalfRichChunksList c i j k τ ↔ m <
      ((List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k τ)).length) := by
    intros τ hτ
    have h_mem_iff_count : l_m ∈ List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k τ) ↔ m <
        ((List.filter (fun l => l.length < 2 ^ j)
          (emittedHalfRichChunksList c i j k τ)).length) := by
      have h_mem_iff_count : List.Nodup
          (List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k t)) := by
        exact List.Nodup.filter _ ( emittedHalfRichChunksList_Nodup c i j k t );
      obtain ⟨rest, hrest⟩ := emittedHalfRichChunksList_filter_prefix c i j k hτ
        (fun l => l.length < 2 ^ j);
      rw [ List.head?_drop ] at hl_m;
      grind;
    simp +zetaDelta at *;
    grind;
  have h_mem_iff_count₁ : ∀ τ ≤ t, l₁ ∈ emittedHalfRichChunksList c i j k τ ↔ m + 1 <
      ((List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k τ)).length) := by
    intro τ hτ;
    have h_mem_iff_count₁ : l₁ ∈ List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k τ) ↔ m + 1 <
        ((List.filter (fun l => l.length < 2 ^ j)
          (emittedHalfRichChunksList c i j k τ)).length) := by
      have h_mem_iff_count₁ : List.Nodup
          (List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k t)) := by
        exact List.Nodup.filter _ ( emittedHalfRichChunksList_Nodup c i j k t );
      obtain ⟨rest, hrest⟩ := emittedHalfRichChunksList_filter_prefix c i j k hτ
        (fun l => l.length < 2 ^ j);
      rw [ List.head?_drop ] at hl₁;
      grind;
    grind +suggestions;
  obtain ⟨A, hA⟩ : ∃ A, A ≤ t ∧ m <
      ((List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k A)).length) ∧ ∀ τ
      < A,
      ¬(m < ((List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k τ)).length)) := by
    have h_exists_A : ∃ A ≤ t, m <
        ((List.filter (fun l => l.length < 2 ^ j)
          (emittedHalfRichChunksList c i j k A)).length) := by
      exact ⟨ t, le_rfl, by linarith [ emittedHalfRich_nonfull_len_eq c i j k t ] ⟩;
    exact ⟨Nat.find h_exists_A, Nat.find_spec h_exists_A |>.1,
      Nat.find_spec h_exists_A |>.2, fun τ hτ => fun h =>
        Nat.find_min h_exists_A hτ
          ⟨Nat.le_trans (Nat.le_of_lt hτ) (Nat.find_spec h_exists_A |>.1), h⟩⟩;
  obtain ⟨B, hB⟩ : ∃ B, B ≤ t ∧ m + 1 <
      ((List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k B)).length) ∧ ∀ τ
      < B,
      ¬(m + 1 < ((List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k τ)).length)) := by
    have hB_exists : ∃ B ≤ t, m + 1 <
        ((List.filter (fun l => l.length < 2 ^ j)
          (emittedHalfRichChunksList c i j k B)).length) := by
      exact ⟨ t, le_rfl, by simpa only [ emittedHalfRich_nonfull_len_eq ] using h_lt ⟩;
    exact ⟨Nat.find hB_exists, Nat.find_spec hB_exists |>.1,
      Nat.find_spec hB_exists |>.2, fun τ hτ => fun h =>
        Nat.find_min hB_exists hτ
          ⟨Nat.le_trans (Nat.le_of_lt hτ) (Nat.find_spec hB_exists |>.1), h⟩⟩;
  have hA_lt_B : A < B := by
    have h_nf_A :
        ((List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k A)).length) ≤ m
        + 1 := by
      rcases A with _ | A
      · exact le_trans (emittedHalfRichChunksList_numNonfull_zero_le c i j k)
          (Nat.succ_le_succ (Nat.zero_le m))
      · exact le_trans (emittedHalfRichChunksList_numNonfull_succ_le c i j k A)
          (Nat.add_le_add_right
            (Nat.le_of_not_gt (hA.2.2 A (Nat.lt_succ_self A))) 1)
    grind;
  unfold nonfullChunkEmissionTime
  dsimp only
  rw [hl_m, hl₁]
  dsimp only
  rw [show List.find? (fun τ => decide (l_m ∈ emittedHalfRichChunksList c i j k τ))
      (List.range (t + 1)) = some A from ?_,
    show List.find? (fun τ => decide (l₁ ∈ emittedHalfRichChunksList c i j k τ))
      (List.range (t + 1)) = some B from ?_];
  · exact hA_lt_B;
  · apply List.find?_range_eq_some.mpr
    refine ⟨decide_eq_true (h_mem_iff_count₁ B hB.1 |>.mpr hB.2.1),
      List.mem_range.mpr (Nat.lt_succ_of_le hB.1), ?_⟩
    intro τ hτ
    have hnot : l₁ ∉ emittedHalfRichChunksList c i j k τ := by
      intro hmem
      exact hB.2.2 τ hτ ((h_mem_iff_count₁ τ (by omega)).mp hmem)
    rw [decide_eq_false hnot]
    exact rfl
  · apply List.find?_range_eq_some.mpr
    refine ⟨decide_eq_true (h_mem_iff_count A hA.1 |>.mpr hA.2.1),
      List.mem_range.mpr (Nat.lt_succ_of_le hA.1), ?_⟩
    intro τ hτ
    have hnot : l_m ∉ emittedHalfRichChunksList c i j k τ := by
      intro hmem
      exact hA.2.2 τ hτ ((h_mem_iff_count τ (by omega)).mp hmem)
    rw [decide_eq_false hnot]
    exact rfl

/-
The trigger of the `m+1`-th nonfull chunk was not half-rich at the emission
time of the `m`-th nonfull chunk.
-/
theorem nonfullChunkTrigger_not_halfrich_prev (c : Code) (i j k t m : ℕ)
    (h_lt : m + 1 < ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length) :
    nonfullChunkTrigger c i j k t (m + 1) ∉ snapshotRichElementsList c i j (k - 1)
        (nonfullChunkEmissionTime c i j k t m) := by
  -- A nonfull emission exhausts all currently unplaced half-rich elements, so
  -- the later trigger was not half-rich at the previous nonfull emission time.
  have h_nonfullChunkEmissionTime : nonfullChunkEmissionTime c i j k t m < nonfullChunkEmissionTime
      c i j k t (m + 1) := by
    apply nonfullChunkEmissionTime_strict_mono c i j k t m h_lt;
  have h_nonfullChunkTrigger : ∃ l_m,
      (List.drop m (List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k t))).head? = some l_m ∧
      l_m.length < 2 ^ j ∧ l_m ≠ [] ∧
      l_m ∈ emittedHalfRichChunksList c i j k t := by
    let L := List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k t)
    have hm_lt : m < L.length := by
      rw [show L.length = ((emittedHalfRichChunks c i j k t).filter
          (fun S => S.card < 2 ^ j)).length by
        exact (emittedHalfRich_nonfull_len_eq c i j k t).symm]
      omega
    refine ⟨L[m], ?_, ?_, ?_, ?_⟩
    · rw [List.head?_drop]
      exact List.getElem?_eq_getElem hm_lt
    · exact of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hm_lt)).2
    · exact emittedHalfRichChunksList_mem_ne_nil c i j k t L[m]
        (List.mem_filter.mp (List.getElem_mem hm_lt)).1
    · exact (List.mem_filter.mp (List.getElem_mem hm_lt)).1
  obtain ⟨l_m, hl_m⟩ := h_nonfullChunkTrigger
  obtain ⟨l₁, hl₁⟩ : ∃ l₁,
      (List.drop (m + 1) (List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k t))).head? = some l₁ ∧
      l₁.length < 2 ^ j ∧ l₁ ≠ [] ∧
      l₁ ∈ emittedHalfRichChunksList c i j k t := by
    let L := List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k t)
    have hm1_lt : m + 1 < L.length := by
      rw [show L.length = ((emittedHalfRichChunks c i j k t).filter
          (fun S => S.card < 2 ^ j)).length by
        exact (emittedHalfRich_nonfull_len_eq c i j k t).symm]
      exact h_lt
    refine ⟨L[m + 1], ?_, ?_, ?_, ?_⟩
    · rw [List.head?_drop]
      exact List.getElem?_eq_getElem hm1_lt
    · exact of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hm1_lt)).2
    · exact emittedHalfRichChunksList_mem_ne_nil c i j k t L[m + 1]
        (List.mem_filter.mp (List.getElem_mem hm1_lt)).1
    · exact (List.mem_filter.mp (List.getElem_mem hm1_lt)).1
  have h_l₁_unplaced : ∀ y ∈ l₁, y ∉
      (emittedHalfRichChunksList c i j k (nonfullChunkEmissionTime c i j k t m)).flatten := by
    intros y hy₁ hy₂
    have h_l₁_not_in_chunk : l₁ ∉ emittedHalfRichChunksList c i j k
        (nonfullChunkEmissionTime c i j k t m) := by
      unfold nonfullChunkEmissionTime at *; simp_all +decide ;
      cases h : List.find? (fun τ => decide
          (l₁ ∈ emittedHalfRichChunksList c i j k τ)) (List.range (t + 1))
        <;> simp_all +decide;
    have h_l₁_not_in_chunk : ∃ rest, emittedHalfRichChunksList c i j k t = emittedHalfRichChunksList
        c i j k (nonfullChunkEmissionTime c i j k t m) ++ rest := by
      apply emittedHalfRichChunksList_prefix;
      exact nonfullChunkEmissionTime_le c i j k t m;
    obtain ⟨ rest, hrest ⟩ := h_l₁_not_in_chunk; simp_all +decide [ List.mem_append ] ;
    have h_l₁_not_in_chunk : List.Nodup
        (List.flatten (emittedHalfRichChunksList c i j k
          (nonfullChunkEmissionTime c i j k t m) ++ rest)) := by
      exact hrest ▸ emittedHalfRichChunksList_flatten_nodup c i j k t;
    grind;
  have h_nonfullChunkTrigger_not_in_chunk :
      l_m.toFinset ∈ emittedHalfRichChunks c i j k
        (nonfullChunkEmissionTime c i j k t m) ∧
      (nonfullChunkEmissionTime c i j k t m > 0 →
        l_m.toFinset ∉ emittedHalfRichChunks c i j k
          (nonfullChunkEmissionTime c i j k t m - 1)) ∧
      l_m.toFinset.card < 2 ^ j := by
    have h_nonfullChunkTrigger_not_in_chunk : l_m ∈ emittedHalfRichChunksList c i j k
        (nonfullChunkEmissionTime c i j k t m) ∧
        (nonfullChunkEmissionTime c i j k t m > 0 →
          l_m ∉ emittedHalfRichChunksList c i j k
            (nonfullChunkEmissionTime c i j k t m - 1)) := by
      unfold nonfullChunkEmissionTime at *; simp_all +decide ;
      cases h : List.find? (fun τ => decide
          (l_m ∈ emittedHalfRichChunksList c i j k τ)) (List.range (t + 1))
        <;> simp_all +decide [ List.find?_eq_none ];
    unfold emittedHalfRichChunks;
    simp_all +decide only [List.mem_map, gt_iff_lt, not_exists, not_and];
    refine ⟨ ⟨ l_m, h_nonfullChunkTrigger_not_in_chunk.1, rfl ⟩, ?_, ?_ ⟩;
    · intro h_pos x hx h_eq;
      have h_eq_lists : x = l_m := by
        have h_eq_lists : x ∈ emittedHalfRichChunksList c i j k
            (nonfullChunkEmissionTime c i j k t m) := by
          have := emittedHalfRichChunksList_prefix c i j k
            (Nat.sub_le (nonfullChunkEmissionTime c i j k t m) 1);
          aesop;
        have h_eq_lists : List.Nodup
            (List.map List.toFinset (emittedHalfRichChunksList c i j k
              (nonfullChunkEmissionTime c i j k t m))) := by
          exact emittedHalfRichChunks_nodup c i j k ( nonfullChunkEmissionTime c i j k t m );
        rw [ List.nodup_map_iff_inj_on ] at h_eq_lists;
        · exact h_eq_lists x ‹_› l_m h_nonfullChunkTrigger_not_in_chunk.1 h_eq;
        · exact emittedHalfRichChunksList_Nodup c i j k (nonfullChunkEmissionTime c i j k t m);
      grind;
    · exact lt_of_le_of_lt ( List.toFinset_card_le _ ) hl_m.2.1;
  have := nonfull_chunk_emit_time c i j k
    (nonfullChunkEmissionTime c i j k t m) l_m.toFinset
    h_nonfullChunkTrigger_not_in_chunk.1 h_nonfullChunkTrigger_not_in_chunk.2.1
    h_nonfullChunkTrigger_not_in_chunk.2.2;
  unfold nonfullChunkTrigger
  dsimp only
  rw [hl₁.1]
  cases l₁ with
  | nil => exact (hl₁.2.2.1 rfl).elim
  | cons y ys =>
      intro hy
      exact h_l₁_unplaced y (List.mem_cons_self)
        (this y hy)

/-
The trigger of a nonfull chunk is rich at its emission time.
-/
theorem nonfullChunkTrigger_rich_curr (c : Code) (i j k t m : ℕ)
    (h_lt : m < ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length) :
    nonfullChunkTrigger c i j k t m ∈ snapshotRichElementsList c i j k
        (nonfullChunkEmissionTime c i j k t m) := by
  -- The head of an emitted chunk is exactly the rich trigger element that
  -- caused that chunk to be opened.
  let L := (emittedHalfRichChunksList c i j k t).filter (fun l => l.length < 2 ^ j)
  have hm_lt : m < L.length := by
    rw [← emittedHalfRich_nonfull_len_eq c i j k t]
    exact h_lt
  let l := L[m]
  have hl_mem : l ∈ L := List.getElem_mem hm_lt
  have hl_drop : l ∈ L.drop m := by
    rw [List.mem_iff_getElem]
    exact ⟨0, by simpa [l]⟩
  have hl_ne : l ≠ [] := by
    apply emittedHalfRichChunksList_mem_ne_nil c i j k t
    exact (List.mem_filter.mp hl_mem).1
  have hl_head : (L.drop m).head? = some l := by
    rw [List.head?_drop]
    exact List.getElem?_eq_getElem hm_lt
  have hl : l ∈ L.drop m ∧ l ≠ [] ∧ (L.drop m).head? = some l :=
    ⟨hl_drop, hl_ne, hl_head⟩
  obtain ⟨τ, hτ⟩ : ∃ τ ∈ List.range (t + 1),
      l ∈ emittedHalfRichChunksList c i j k τ ∧
        ∀ τ' < τ, l ∉ emittedHalfRichChunksList c i j k τ' := by
    have h_exists_τ : ∃ τ ∈ List.range (t + 1),
        l ∈ emittedHalfRichChunksList c i j k τ := by
      exact ⟨t, List.mem_range.mpr (Nat.lt_succ_self t),
        List.mem_of_mem_filter (List.mem_of_mem_drop hl.1)⟩
    refine ⟨Nat.find h_exists_τ, (Nat.find_spec h_exists_τ).1,
      (Nat.find_spec h_exists_τ).2, ?_⟩
    intro τ' hτ' hmem
    apply Nat.find_min h_exists_τ hτ'
    exact ⟨List.mem_range.mpr (by
      linarith [List.mem_range.mp (Nat.find_spec h_exists_τ).1]), hmem⟩
  have h_l_head : ∃ x ∈ (snapshotRichElementsList c i j k τ).eraseDups,
      l ≠ [] ∧ l.head? = some x := by
    have h_l_head : ∀ {L : List BitString} {acc : List (List BitString)}, l ∈ List.foldl
        (emittedHalfRichChunks_fold_step j ((snapshotRichElementsList c i j (k - 1) τ).eraseDups))
        acc L → l ∉ acc → ∃ x ∈ L, l ≠ [] ∧ l.head? = some x := by
      intros L acc hl hacc
      induction L using List.reverseRecOn generalizing acc with
      | nil => exact (hacc hl).elim
      | append_singleton L x ih =>
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hl
          let acc' := List.foldl (emittedHalfRichChunks_fold_step j
            (snapshotRichElementsList c i j (k - 1) τ).eraseDups) acc L
          change l ∈ emittedHalfRichChunks_fold_step j
            (snapshotRichElementsList c i j (k - 1) τ).eraseDups acc' x at hl
          by_cases hx : x ∈ acc'.flatten
          · have hdec : decide (x ∈ acc'.flatten) = true := decide_eq_true hx
            simp only [emittedHalfRichChunks_fold_step, hdec, cond_true] at hl
            obtain ⟨y, hy, hne, hhead⟩ := ih hl hacc
            exact ⟨y, List.mem_append.mpr (Or.inl hy), hne, hhead⟩
          · have hdec : decide (x ∈ acc'.flatten) = false := decide_eq_false hx
            simp only [emittedHalfRichChunks_fold_step, hdec, cond_false,
              List.mem_append, List.mem_singleton] at hl
            rcases hl with hl | hl
            · obtain ⟨y, hy, hne, hhead⟩ := ih hl hacc
              exact ⟨y, List.mem_append.mpr (Or.inl hy), hne, hhead⟩
            · rw [hl]
              obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero
                (Nat.ne_of_gt (pow_pos (by omega : 0 < 2) j))
              refine ⟨x, List.mem_append.mpr (Or.inr (List.mem_singleton_self x)), ?_, ?_⟩
              · rw [hq, List.take_succ_cons]
                exact List.cons_ne_nil x _
              · simp only [hq, List.take_succ_cons, List.head?_cons]
    rcases τ with _ | τ
    · have : l ∈ ([] : List (List BitString)) := by
        simpa only [emittedHalfRichChunksList, emittedHalfRichChunks_step,
          snapshotRichElementsList_zero, List.eraseDups_nil, List.foldl_nil]
          using hτ.2.1
      exact (List.not_mem_nil this).elim
    · exact h_l_head hτ.2.1 (hτ.2.2 τ (Nat.lt_succ_self τ))
  obtain ⟨x, hx⟩ := h_l_head
  have hx_rich : x ∈ snapshotRichElementsList c i j k τ := by
    have h_eraseDups : ∀ {L : List BitString}, x ∈ L.eraseDups → x ∈ L := by
      intros L hL; induction L using List.reverseRecOn
      case' nil => simp_all +decide
      case' append_singleton L ih _ => simp_all +decide [ List.eraseDups_append ]
      simp_all +decide [ List.removeAll ];
      grind;
    exact h_eraseDups hx.1;
  simp only [nonfullChunkTrigger, nonfullChunkEmissionTime]
  change (match (L.drop m).head? with
    | none => []
    | some [] => []
    | some (x :: _) => x) ∈
      snapshotRichElementsList c i j k
        (match (L.drop m).head? with
        | none => 0
        | some l => (List.find? (fun τ => decide
            (l ∈ emittedHalfRichChunksList c i j k τ)) (List.range (t + 1))).getD 0)
  rw [hl_head]
  simp only
  rw [show List.find? (fun τ => decide (l ∈ emittedHalfRichChunksList c i j k τ))
      (List.range (t + 1)) = some τ from ?_]
  · cases hcase : l with
    | nil => exact (hl_ne hcase).elim
    | cons a tail =>
      have hax : a = x := by simpa [hcase] using hx.2.2
      simpa [hax] using hx_rich
  · apply List.find?_range_eq_some.mpr
    refine ⟨decide_eq_true hτ.2.1, hτ.1, ?_⟩
    intro τ' hτ'
    have hnot := hτ.2.2 τ' hτ'
    rw [decide_eq_false hnot]
    exact rfl

/-- Strictly-monotone emission times give a plain monotonicity: for `a < b` both
below the number of nonfull chunks, `τ a < τ b`. -/
theorem nonfullChunkEmissionTime_lt_of_lt (c : Code) (i j k t : ℕ) {a : ℕ} : ∀ {b : ℕ},
    a < b →
    b < ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length →
    nonfullChunkEmissionTime c i j k t a < nonfullChunkEmissionTime c i j k t b
  | 0, hab, _ => absurd hab (by omega)
  | n + 1, hab, hb => by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hab) with h' | h'
    · exact lt_trans (nonfullChunkEmissionTime_lt_of_lt c i j k t h' (by omega))
        (nonfullChunkEmissionTime_strict_mono c i j k t n (by omega))
    · subst h'
      exact nonfullChunkEmissionTime_strict_mono c i j k t a (by omega)

/-- Weak monotonicity of nonfull-chunk emission times. -/
theorem nonfullChunkEmissionTime_mono (c : Code) (i j k t : ℕ) {a b : ℕ}
    (hab : a ≤ b)
    (hb : b < ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length) :
    nonfullChunkEmissionTime c i j k t a ≤ nonfullChunkEmissionTime c i j k t b := by
  rcases lt_or_eq_of_le hab with h | h
  · exact le_of_lt (nonfullChunkEmissionTime_lt_of_lt c i j k t h hb)
  · exact le_of_eq (by rw [h])

/-- Between any two non-full chunks, there is at least one trigger element that
moves from not-half-rich to rich, requiring 2^(k-1) fresh descriptions on
disjoint time intervals.

Assembled from the indexed helpers: each nonfull chunk `m` (index `< F`) has a
trigger `y m` that is not half-rich at the *previous* nonfull emission time
`prevT m` but is rich at its own emission time `τ m`.  By
`trigger_gains_fresh_finset` this forces at least `2 ^ (k-1)` descriptions
containing `y m` to be *fresh* on the interval `(prevT m, τ m]`.  Strict
monotonicity of the emission times makes these fresh sets pairwise disjoint and
all contained in the final description universe, so the count multiplies out. -/
theorem nonfull_chunk_fresh_descriptions (c : Code) (i j k : ℕ) (t : ℕ) :
    ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length * 2 ^ (k - 1) ≤
      (snapshotDescList c i j t).length := by
  rw [snapshotDescList_length_eq_card]
  set F := ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length with hF
  -- The fresh-description finset charged to the `m`-th nonfull chunk.
  let D : ℕ → Finset (Finset BitString) := fun m =>
    (snapshotDescriptionsAndSizeLe c i j (nonfullChunkEmissionTime c i j k t m)).filter
        (fun s => nonfullChunkTrigger c i j k t m ∈ s) \
      (snapshotDescriptionsAndSizeLe c i j
        (if m = 0 then 0 else nonfullChunkEmissionTime c i j k t (m - 1))).filter
        (fun s => nonfullChunkTrigger c i j k t m ∈ s)
  have hDm : ∀ m, D m =
      (snapshotDescriptionsAndSizeLe c i j (nonfullChunkEmissionTime c i j k t m)).filter
          (fun s => nonfullChunkTrigger c i j k t m ∈ s) \
        (snapshotDescriptionsAndSizeLe c i j
          (if m = 0 then 0 else nonfullChunkEmissionTime c i j k t (m - 1))).filter
          (fun s => nonfullChunkTrigger c i j k t m ∈ s) := fun m => rfl
  -- Lower bound: each charged finset has at least `2 ^ (k-1)` elements.
  have lower : ∀ m ∈ Finset.range F, 2 ^ (k - 1) ≤ (D m).card := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [hDm m]
    by_cases hm0 : m = 0
    · subst hm0
      simp only
      refine trigger_gains_fresh_finset c i j k 0 (nonfullChunkEmissionTime c i j k t 0)
        _ ?_ (nonfullChunkTrigger_rich_curr c i j k t 0 (by omega))
      rw [snapshotRichElementsList_zero]
      simp
    · rw [if_neg hm0]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      exact trigger_gains_fresh_finset c i j k (nonfullChunkEmissionTime c i j k t m')
        (nonfullChunkEmissionTime c i j k t (m' + 1))
        _ (nonfullChunkTrigger_not_halfrich_prev c i j k t m' (by omega))
        (nonfullChunkTrigger_rich_curr c i j k t (m' + 1) (by omega))
  -- Core disjointness for `p < q`: a fresh description of chunk `q` cannot already
  -- be present at `τ p ≤ τ (q-1) = prevT q`.
  have key : ∀ p q, p < F → q < F → p < q → Disjoint (D p) (D q) := by
    intro p q _ hq hpq
    rw [Finset.disjoint_left]
    intro s hsp hsq
    rw [hDm p, Finset.mem_sdiff, Finset.mem_filter] at hsp
    rw [hDm q, Finset.mem_sdiff] at hsq
    obtain ⟨⟨hsp_mem, _⟩, _⟩ := hsp
    obtain ⟨hsq_mem, hsq_not⟩ := hsq
    rw [Finset.mem_filter] at hsq_mem
    apply hsq_not
    rw [Finset.mem_filter]
    refine ⟨?_, hsq_mem.2⟩
    have hq0 : q ≠ 0 := by omega
    rw [if_neg hq0]
    refine snapshotDescriptionsAndSizeLe_subset_of_le c i j ?_ hsp_mem
    exact nonfullChunkEmissionTime_mono c i j k t (by omega) (by omega)
  -- The charged finsets are pairwise disjoint.
  have disjoint : (↑(Finset.range F) : Set ℕ).PairwiseDisjoint D := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    change Disjoint (D a) (D b)
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact key a b ha hb hlt
    · exact (key b a hb ha hlt).symm
  -- Every charged finset lives in the final description universe.
  have subset : ∀ m ∈ Finset.range F,
      D m ⊆ snapshotDescriptionsAndSizeLe c i j t := by
    intro m _ s hs
    rw [hDm m, Finset.mem_sdiff] at hs
    obtain ⟨hs_mem, _⟩ := hs
    rw [Finset.mem_filter] at hs_mem
    exact snapshotDescriptionsAndSizeLe_subset_of_le c i j
      (nonfullChunkEmissionTime_le c i j k t m) hs_mem.1
  calc F * 2 ^ (k - 1)
      = ∑ _m ∈ Finset.range F, 2 ^ (k - 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ ∑ m ∈ Finset.range F, (D m).card := Finset.sum_le_sum lower
    _ = ((Finset.range F).biUnion D).card := (Finset.card_biUnion disjoint).symm
    _ ≤ (snapshotDescriptionsAndSizeLe c i j t).card := by
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_biUnion] at hs
        obtain ⟨m, hm, hsm⟩ := hs
        exact subset m hm hsm

/-- Non-full chunks are bounded by the number of fresh occurrences needed,
`<= 2^(i - k + O(1))`. -/
theorem emittedHalfRichChunks_nonfull_count_le (U : Map) (c : Code) (_hc : IsCodeFor c U)
    (i j k : ℕ) (t : ℕ) :
    ((emittedHalfRichChunks c i j k t).filter
      (fun S => S.card < 2 ^ j)).length ≤ 2 ^ (i - k + 2) := by
  have hfresh := nonfull_chunk_fresh_descriptions c i j k t
  have hlen := snapshotDescList_length_le c i j t
  set F := ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length
  have h1 : F * 2 ^ (k - 1) ≤ 2 ^ (i + 1) := le_trans hfresh hlen
  have h2 : F * 2 ^ (k - 1) ≤ 2 ^ (i - k + 2) * 2 ^ (k - 1) := by
    refine le_trans h1 ?_
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

/-- The total number of chunks is bounded by `2^(i - k + 3)`. -/
theorem emittedHalfRichChunks_length_le (U : Map) (c : Code) (hc : IsCodeFor c U) (i j k : ℕ)
    (t : ℕ) :
    (emittedHalfRichChunks c i j k t).length ≤ 2 ^ (i - k + 3) := by
  have hfull := emittedHalfRichChunks_full_count_le U c hc i j k t
  have hnonfull := emittedHalfRichChunks_nonfull_count_le U c hc i j k t
  have hlen : (emittedHalfRichChunks c i j k t).length =
      ((emittedHalfRichChunks c i j k t).filter (fun S => S.card = 2 ^ j)).length +
      ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length := by
    -- Every chunk has card ≤ 2^j, so `card < 2^j` is exactly the negation of `card = 2^j`;
    -- the two filters therefore partition the list.
    have hcong : (emittedHalfRichChunks c i j k t).filter (fun S => !decide (S.card = 2 ^ j))
        = (emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j) := by
      apply List.filter_congr
      intro S hS
      have hSle := emittedHalfRichChunks_card_le c i j k t S hS
      have hiff : (S.card < 2 ^ j) ↔ ¬ (S.card = 2 ^ j) := by omega
      simp [hiff]
    rw [List.length_eq_length_filter_add (l := emittedHalfRichChunks c i j k t)
      (fun S => decide (S.card = 2 ^ j))]
    congr 1
    exact congrArg List.length hcong
  rw [hlen]
  have hp : (2 : ℕ) ^ (i - k + 3) = 2 ^ (i - k + 2) + 2 ^ (i - k + 2) := by
    rw [pow_succ 2 (i - k + 2), mul_two]
  omega

/-- Given `i, j, k, h`, run the online stream until the `h`-th chunk is emitted
and output its canonical uniform code. -/
noncomputable def onlineHalfRichChunkSelectorFn (c : Code) : BitString →. BitString :=
  fun s =>
    let i := selNat s
    let j := selAlpha s
    let k := selMaxK s
    let h := selH s
    (Nat.rfind (fun t => Part.some
      (decide (h < (emittedHalfRichChunksList c i j k t).length)))).bind
      (fun t =>
        let chunks := emittedHalfRichChunksList c i j k t
        Part.some (match chunks.drop h with
          | [] => []
          | S :: _ =>
            codedDistributionDataCode
              ((canonicalFinsetList S.toFinset).map fun x =>
                { point := x,
                  mass := ratMassInvNat
                    (max 1 (canonicalFinsetList S.toFinset).length) (by positivity) })))

/-
The output body of the online chunk selector, as a function of the input
bitstring `s` and the discovered time `t`, is primitive recursive.  This is the
deterministic post-`rfind` computation: read the parameters off `s`, run the
stream to time `t`, drop the first `h` chunks, and emit the canonical-uniform
code of the head chunk (or the empty string if no chunk is present).
-/
theorem onlineHalfRichChunkBody_primrec (c : Code) :
    Primrec (fun p : BitString × ℕ =>
      (match (emittedHalfRichChunksList c (selNat p.1) (selAlpha p.1)
        (selMaxK p.1) p.2).drop (selH p.1) with
        | [] => ([] : BitString)
        | S :: _ =>
          codedDistributionDataCode ((canonicalFinsetList S.toFinset).map fun x =>
            { point := x,
              mass := ratMassInvNat
                (max 1 (canonicalFinsetList S.toFinset).length) (by positivity) }))) := by
  have h_list_drop_primrec : Primrec
      (fun p : BitString × ℕ => List.drop (selH p.1)
        (emittedHalfRichChunksList c (selNat p.1) (selAlpha p.1)
          (selMaxK p.1) p.2)) := by
    have h_index : Primrec (fun p : BitString × ℕ => selH p.1) :=
      selH_primrec.comp Primrec.fst
    have h_args : Primrec
        (fun p : BitString × ℕ => (selNat p.1, selAlpha p.1, selMaxK p.1, p.2)) :=
      Primrec.pair (selNat_primrec.comp Primrec.fst)
        (Primrec.pair (selAlpha_primrec.comp Primrec.fst)
          (Primrec.pair (selMaxK_primrec.comp Primrec.fst) Primrec.snd))
    have h_nestedArgs : Primrec
        (fun p : ℕ × ℕ × ℕ × ℕ => (((p.1, p.2.1), p.2.2.1), p.2.2.2)) :=
      Primrec.pair
        (Primrec.pair
          (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have h_chunks : Primrec
        (fun p : ℕ × ℕ × ℕ × ℕ =>
          emittedHalfRichChunksList c p.1 p.2.1 p.2.2.1 p.2.2.2) :=
      ((emittedHalfRichChunksList_primrec c).comp h_nestedArgs).of_eq (fun _ => rfl)
    exact KraftChaitin.drop_primrec.comp (h_chunks.comp h_args) h_index
  have h_cons : Primrec₂ (fun (_ : BitString × ℕ)
      (q : List BitString × List (List BitString)) =>
      codedDistributionDataCode
        ((canonicalFinsetList q.1.toFinset).map fun x =>
          { point := x,
            mass := ratMassInvNat
              (max 1 (canonicalFinsetList q.1.toFinset).length) (by positivity) })) :=
    ((codedUniformEncoder_primrec.comp
      (canonicalFinsetList_toFinset_primrec.comp
        (Primrec.fst.comp Primrec.snd))).of_eq (fun _ => rfl)).to₂
  exact (Primrec.list_casesOn h_list_drop_primrec (Primrec.const []) h_cons).of_eq
    (fun p => by
      cases List.drop (selH p.1) (emittedHalfRichChunksList c (selNat p.1)
        (selAlpha p.1) (selMaxK p.1) p.2) <;> rfl)

theorem partrec_onlineHalfRichChunkSelectorFn (c : Code) :
    Partrec (onlineHalfRichChunkSelectorFn c) := by
  -- Ordinal selector computability for the emitted half-rich chunk stream.
  have h_args : Primrec (fun p : BitString × ℕ =>
      (((selNat p.1, selAlpha p.1), selMaxK p.1), p.2)) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.pair (selNat_primrec.comp Primrec.fst)
          (selAlpha_primrec.comp Primrec.fst))
        (selMaxK_primrec.comp Primrec.fst)) Primrec.snd
  have h_check : Computable₂ (fun (s : BitString) (t : ℕ) =>
      decide (selH s <
        (emittedHalfRichChunksList c (selNat s) (selAlpha s) (selMaxK s) t).length)) :=
    (PrimrecPred.decide (Primrec.nat_lt.comp
      (selH_primrec.comp Primrec.fst)
      (Primrec.list_length.comp
        ((emittedHalfRichChunksList_primrec c).comp h_args)))).to_comp.to₂
  have h_body := (onlineHalfRichChunkBody_primrec c).to_comp.to₂
  exact (Partrec.bind (Partrec.rfind h_check.partrec₂) h_body.partrec₂).of_eq
    (fun _ => rfl)

/-- Equal chunk lists yield the same chunk (as a finset) at a common index,
independent of the index-bound proof. -/
theorem toFinset_get_eq_of_listEq {l l' : List (List BitString)} (hll : l = l')
    {n : ℕ} (hn : n < l.length) (hn' : n < l'.length) :
    (l.get ⟨n, hn⟩).toFinset = (l'.get ⟨n, hn'⟩).toFinset := by
  subst hll; rfl

/-- `ratMassInvNat` depends only on its numerator, not the positivity proof. -/
theorem ratMassInvNat_congr {a b : ℕ} (hab : a = b) (ha : 0 < a) (hb : 0 < b) :
    ratMassInvNat a ha = ratMassInvNat b hb := by subst hab; rfl

/-
Evaluating the online ordinal selector at `richInput i j k h` with a valid
ordinal `h` returns the canonical-uniform code of the `h`-th emitted chunk.
-/
theorem onlineHalfRichChunkSelectorFn_eq (c : Code) (i j k h t : ℕ)
    (h_lt : h < (emittedHalfRichChunksList c i j k t).length)
    (h_first : ∀ t' < t, ¬(h < (emittedHalfRichChunksList c i j k t').length))
    (hne : ((emittedHalfRichChunksList c i j k t).get ⟨h, h_lt⟩).toFinset.Nonempty) :
    onlineHalfRichChunkSelectorFn c (richInput i j k h)
      = Part.some
          ((codedUniformOn
            ((emittedHalfRichChunksList c i j k t).get ⟨h, h_lt⟩).toFinset hne).code) := by
  -- Evaluation of the ordinal selector at the first time the requested chunk
  -- exists.
  convert Part.eq_some_iff.mpr _ using 1;
  unfold onlineHalfRichChunkSelectorFn;
  simp +decide only [selH_richInput, selNat_richInput, selAlpha_richInput,
    selMaxK_richInput, length_canonicalFinsetList, List.get_eq_getElem,
    Part.mem_bind_iff, Part.mem_some_iff];
  refine ⟨ t, ?_, ?_ ⟩;
  · refine Nat.mem_rfind.mpr ⟨?_, fun { m } hm => ?_⟩
    · exact Part.mem_some_iff.mpr (decide_eq_true h_lt).symm
    · exact Part.mem_some_iff.mpr
        (decide_eq_false fun hlt => h_first m hm hlt).symm
  · have hcard : max 1
        (emittedHalfRichChunksList c i j k t)[h].toFinset.card =
        (emittedHalfRichChunksList c i j k t)[h].toFinset.card :=
      Nat.max_eq_right (Finset.Nonempty.card_pos hne)
    rw [List.drop_eq_getElem_cons h_lt]
    simp only
    rw [codedUniformOn_code_eq]
    congr 3
    funext x
    congr 1
    exact ratMassInvNat_congr hcard.symm _ _

/-- Stability of a fixed chunk index across time: once chunk `h` exists at time
`t`, it has the same value (as a finset) at any later time `t'`. -/
theorem emittedHalfRichChunksList_get_stable (c : Code) (i j k h : ℕ) {t t' : ℕ}
    (htt : t ≤ t') (h_lt : h < (emittedHalfRichChunksList c i j k t).length)
    (h_lt' : h < (emittedHalfRichChunksList c i j k t').length) :
    (emittedHalfRichChunksList c i j k t').get ⟨h, h_lt'⟩
      = (emittedHalfRichChunksList c i j k t).get ⟨h, h_lt⟩ := by
  obtain ⟨rest, hrest⟩ := emittedHalfRichChunksList_prefix c i j k htt
  simp only [hrest, List.get_eq_getElem, List.getElem_append_left h_lt]

/-
Minimality-free evaluation of the online ordinal selector: if chunk `h`
exists and is nonempty at *some* time `t`, the selector returns its
canonical-uniform code.  Derived from `onlineHalfRichChunkSelectorFn_eq` by
running to the first time the chunk appears and using stability.
-/
theorem onlineHalfRichChunkSelectorFn_eq_of_mem (c : Code) (i j k h t : ℕ)
    (h_lt : h < (emittedHalfRichChunksList c i j k t).length)
    (hne : ((emittedHalfRichChunksList c i j k t).get ⟨h, h_lt⟩).toFinset.Nonempty) :
    onlineHalfRichChunkSelectorFn c (richInput i j k h)
      = Part.some
          ((codedUniformOn
            ((emittedHalfRichChunksList c i j k t).get ⟨h, h_lt⟩).toFinset hne).code) := by
  apply Eq.symm; exact (by
    have := onlineHalfRichChunkSelectorFn_eq c i j k h
      (Nat.find (⟨t, h_lt⟩ : ∃ t,
        h < (emittedHalfRichChunksList c i j k t).length))
      (Nat.find_spec (⟨t, h_lt⟩ : ∃ t,
        h < (emittedHalfRichChunksList c i j k t).length))
      (fun t' ht' => Nat.find_min (⟨t, h_lt⟩ : ∃ t,
        h < (emittedHalfRichChunksList c i j k t).length) ht') (by
    grind +suggestions)
    grind +suggestions
  )

/-
**Complexity-portion selector obligation (primary target).**

This is the selector/coding obligation corresponding to the standard main
statement `A -> C`: many `(i,j)` descriptions imply an `(i-k,j)` description, up
to visible logarithmic slack.  The size-improvement statement should be derived
from this one rather than proved by an independent size selector.

The intended construction is the online half-rich covering stream described in
`docs/section3-online-half-rich-cover.md`: enumerate chunks as they are created
and address a chunk by its ordinal, not by a final snapshot/halt-count.

The complexity-improvement analogue of `richSizePortion_selector_correct`, with
batches of size `≤ 2 ^ j` addressed by `h < 2 ^ (i - k + 4)`.  This is proved
from the effective `emittedHalfRichChunks` stream and is the
foundational step of the complexity chain
(`setComplexity_halfRichComplexityPortion_le` → … →
`ImprovingDescriptionsComplexityLogSlack`).
-/
theorem halfRichComplexityPortion_selector_correct (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ f : BitString →. BitString, Partrec f ∧
      ∀ x n i j k, x.length = n → ManyIJDescriptions U x i j k → k ≤ i →
        ∃ h < 2 ^ (i - k + 4),
          ∃ (S : Finset BitString) (hS : S.Nonempty),
            x ∈ S ∧
            S.card ≤ 2 ^ j ∧
            f (richInput i j k h) = Part.some ((codedUniformOn S hS).code) := by
  -- Proved from the effective `emittedHalfRichChunks` stream above: coverage of
  -- rich elements, the full/non-full online counting bounds, and a
  -- partial-recursive ordinal selector that runs until the requested chunk is
  -- emitted.
  obtain ⟨c, hc⟩ : ∃ c : Code, IsCodeFor c U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  refine ⟨ _, partrec_onlineHalfRichChunkSelectorFn c, ?_ ⟩;
  intro x n i j k hx hmany hk;
  obtain ⟨t, S, hS₁, hS₂⟩ := emittedHalfRichChunks_cover_rich U c hc i j k x
    (mem_richDescriptionElements_of_many U x i j k hmany);
  obtain ⟨ h, hh₁, hh₂ ⟩ := List.mem_map.mp hS₁;
  obtain ⟨ h', hh'₁, hh'₂ ⟩ := List.mem_iff_getElem.mp hh₁;
  refine ⟨ h', ?_, S, ?_, ?_, ?_, ?_ ⟩;
  any_goals assumption;
  any_goals exact Finset.nonempty_of_ne_empty ( by rintro rfl; simp_all +decide );
  · exact lt_of_lt_of_le hh'₁ (by
      simpa [emittedHalfRichChunks] using
        emittedHalfRichChunks_length_le U c hc i j k t |> le_trans <|
          Nat.pow_le_pow_right (by decide) <| by omega);
  · exact emittedHalfRichChunks_card_le c i j k t S hS₁;
  · have hset :
        ((emittedHalfRichChunksList c i j k t).get ⟨h', hh'₁⟩).toFinset = S := by
      change (emittedHalfRichChunksList c i j k t)[h'].toFinset = S
      rw [hh'₂, hh₂]
    have hne :
        ((emittedHalfRichChunksList c i j k t).get ⟨h', hh'₁⟩).toFinset.Nonempty :=
      hset.symm ▸ Finset.nonempty_of_ne_empty (by rintro rfl; simp_all +decide)
    calc
      onlineHalfRichChunkSelectorFn c (richInput i j k h') =
          Part.some ((codedUniformOn _ hne).code) :=
        onlineHalfRichChunkSelectorFn_eq_of_mem c i j k h' t hh'₁ hne
      _ = Part.some ((codedUniformOn S _).code) :=
        congrArg Part.some (codedUniformOn_code_congr hne _ hset)

/-- Half-rich dump bound: the objects with many descriptions are few.  This is
the proved whole-rich cardinality estimate; the genuine complexity-half work is
to refine this into a computable portion family with only about `2^(i-k)` viable
portion addresses. -/
theorem halfRich_dump_card_le (U : Map) :
    ∀ i j k : ℕ,
      (richDescriptionElements U i j k).card ≤ 2 ^ (i + 1 + j - k) := by
  intro i j k
  exact card_richDescriptionElements_le U i j k

/-
7. `setComplexity` bound and complexity portion assembly.

The coding wrapper around `halfRichComplexityPortion_selector_correct`. Here the
batch address is small, `h < 2 ^ (i - k + 4)`, so the address-parameterized
bound `richInput_KPPlain_le_addr` (with `m = i - k + 3`) yields complexity
`(i - k + 1) + logSlack`, and `logSlack_one_add_le_two_mul` absorbs the `+1` and
the slack argument `i + j + k + (i - k) = 2 * i + j` into the visible-parameter
slack `n + i + j`.
-/
theorem setComplexity_halfRichComplexityPortion_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x n i j k, x.length = n → ManyIJDescriptions U x i j k → k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (n + i + j) : ENat) ∧
        S.card ≤ 2 ^ j := by
  obtain ⟨f, hf, hf_spec⟩ := halfRichComplexityPortion_selector_correct U hU
  obtain ⟨c₃, hc₃⟩ := KPPlain_partrec_map_le U hU f hf
  obtain ⟨c₄, hc₄⟩ := richInput_KPPlain_le_addr U hU c₃
  refine ⟨4 * c₄ + 4, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨h, hh, S, hS, hxS, hcard, hfeq⟩ := hf_spec x n i j k hn hmany hk
  refine ⟨S, hS, hxS, ?_, hcard⟩
  have hmem : (codedUniformOn S hS).code ∈ f (richInput i j k h) := by
    rw [hfeq]; exact Part.mem_some _
  have hbound : setComplexity U S hS
      ≤ ((i - k : ℕ) : ENat) + 4 + logSlack c₄ (i + j + k + (i - k + 3)) :=
    le_trans (hc₃ _ _ hmem) (hc₄ i j k h (i - k + 3) hh)
  have habs : 4 + logSlack c₄ (i + j + k + (i - k + 3)) ≤ logSlack (4 * c₄ + 4) (n + i + j) := by
    apply logSlack_four_add_le
    omega
  refine le_trans hbound ?_
  rw [← ENat.natCast_sub, add_assoc]
  gcongr
  exact_mod_cast habs

/-- Selector/coding interface for the complexity-improvement half. -/
theorem exists_halfRichComplexityRefinedSet_logSlack (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x n i j k,
      x.length = n → ManyIJDescriptions U x i j k → k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (n + i + j) : ENat) ∧
        S.card ≤ 2 ^ (j + logSlack c (n + i + j)) := by
  obtain ⟨c, hc⟩ := setComplexity_halfRichComplexityPortion_le U hU
  refine ⟨c, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨S, hS, hx, hcomp, hcard⟩ := hc x n i j k hn hmany hk
  refine ⟨S, hS, hx, hcomp, ?_⟩
  exact hcard.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- Faithful logarithmic-slack target for the complexity-improvement half. -/
theorem exists_description_smaller_complexity_of_many_logSlack
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ImprovingDescriptionsComplexityLogSlack U := by
  obtain ⟨c, hc⟩ := exists_halfRichComplexityRefinedSet_logSlack U hU
  refine ⟨c, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨S, hS, hxS, hcomp, hcard⟩ := hc x n i j k hn hmany hk
  exact ⟨S, hS, hxS, hcomp, hcard⟩

/-- **Size form as a corollary of the complexity form.**

The standard Section 3 derivation: the `(i, j - k)` size-improvement statement is
*not* an independent selector obligation but a corollary of the stronger
`(i - k, j)` complexity-improvement statement, obtained by the
portion/description-shift move (`inDescriptionProfile_portion`).

Sketch.  Set `k₀ = min k i` (so the complexity form, which needs `k₀ ≤ i`,
applies).  The complexity form gives an `(i - k₀ + s, j + s)`-description with
`s = logSlack c₁ (n+i+j)`.  Slicing it into `2^k` contiguous chunks and keeping
the chunk containing `x` (`inDescriptionProfile_portion`, `s := k`, legal since
`k ≤ j ≤ j + s`) yields complexity `(i - k₀ + s) + k + 2·|bits k| + c₀` and size
exponent `(j + s) - k + 1`.  Since `i - k₀ + k ≤ i + 1` (using
`ManyIJDescriptions.le_succ`: `k ≤ i + 1`), the complexity is `≤ i + (1 + s + 2·|bits k| + c₀)`,
and `2·|bits k| ≤ 2·|bits (n+i+j)|`, so the whole address overhead is absorbed
into the single visible slack `logSlack (c₁ + c₀ + 3) (n+i+j)`; the size exponent
`(j - k) + s + 1` is likewise `≤ (j - k) + logSlack (c₁ + c₀ + 3) (n+i+j)`. -/
theorem improvingDescriptionsSize_of_complexity (U : Map)
    (hU : IsOptimalPrefixConditional U) (hC : ImprovingDescriptionsComplexityLogSlack U) :
    ImprovingDescriptionsSizeLogSlack U := by
  obtain ⟨c1, hC⟩ := hC
  obtain ⟨c0, hportion⟩ := inDescriptionProfile_portion U hU
  refine ⟨c1 + c0 + 3, fun x n i j k hn hmany hk => ?_⟩
  have hk_le : k ≤ i + 1 := hmany.le_succ
  set k₀ := min k i with hk0
  have hk0k : k₀ ≤ k := min_le_left k i
  have hk0i : k₀ ≤ i := min_le_right k i
  have hmany0 : ManyIJDescriptions U x i j k₀ := hmany.mono_k hk0k
  set s1 := logSlack c1 (n + i + j) with hs1
  have hprof : InDescriptionProfile U x (i - k₀ + s1) (j + s1) := hC x n i j k₀ hn hmany0 hk0i
  have hk_le_size : k ≤ j + s1 := le_trans hk (Nat.le_add_right j s1)
  have hport := hportion x (i - k₀ + s1) (j + s1) k hprof hk_le_size
  set L := (Nat.bits k).length with hL
  set slack := logSlack (c1 + c0 + 3) (n + i + j) with hslack
  -- The single absorption inequality: address overhead fits inside the slack.
  have hkey : 1 + s1 + 2 * L + c0 ≤ slack := by
    have hLM : L ≤ (Nat.bits (n + i + j)).length := by
      rw [hL]; exact length_natBits_mono (by omega)
    rw [hs1, hslack, hL]
    unfold logSlack
    nlinarith [hLM, Nat.zero_le ((Nat.bits (n + i + j)).length), Nat.zero_le c0,
      Nat.zero_le c1, Nat.zero_le L]
  have hik : i - k₀ + k ≤ i + 1 := by omega
  have hBcomp : i - k₀ + s1 + k + 2 * L + c0 ≤ i + slack := by omega
  have hQsize : j + s1 - k + 1 ≤ j - k + slack := by omega
  exact (hport.mono_i hBcomp).mono_j hQsize

/-- Faithful logarithmic-slack target for the size-improvement half, now obtained
as the standard corollary of the complexity form via
`improvingDescriptionsSize_of_complexity`. -/
theorem exists_description_smaller_size_of_many_logSlack
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ImprovingDescriptionsSizeLogSlack U :=
  improvingDescriptionsSize_of_complexity U hU
    (exists_description_smaller_complexity_of_many_logSlack U hU)

theorem snapshotCodes_toFinset_eq_of_max {c : Code} {U : Map} (hc : IsCodeFor c U) (alpha t t₀ : ℕ)
    (h_ge : t₀ ≤ t)
    (hmax : ∀ t', countHalts c alpha t' ≤ countHalts c alpha t₀) :
    (snapshotCodes c alpha t).toFinset = (snapshotCodes c alpha t₀).toFinset := by
  ext w
  simp only [List.mem_toFinset]
  constructor
  · intro hw
    unfold snapshotCodes at hw
    rw [List.mem_filterMap] at hw
    obtain ⟨p, hp, hw_run⟩ := hw
    have h_prod := runOut_sound hc hw_run
    exact code_mem_snapshot_of_max hc alpha t₀ hmax hp h_prod
  · intro hw
    exact snapshotCodes_mem_of_le h_ge hw

theorem snapshotDescList_eq_of_max {c : Code} {U : Map} (hc : IsCodeFor c U) (i j t t₀ : ℕ)
    (h_ge : t₀ ≤ t)
    (hmax : ∀ t', countHalts c i t' ≤ countHalts c i t₀) :
    snapshotDescList c i j t = snapshotDescList c i j t₀ := by
  unfold snapshotDescList
  have h_eq : ((snapshotCodes c i t).filter isCanonicalUniformCodeBool).toFinset =
              ((snapshotCodes c i t₀).filter isCanonicalUniformCodeBool).toFinset := by
    ext w
    simp only [List.mem_toFinset, List.mem_filter]
    have h_set := snapshotCodes_toFinset_eq_of_max hc i t t₀ h_ge hmax
    rw [Finset.ext_iff] at h_set
    specialize h_set w
    simp only [List.mem_toFinset] at h_set
    rw [h_set]
  rw [h_eq]

end Kolmogorov
