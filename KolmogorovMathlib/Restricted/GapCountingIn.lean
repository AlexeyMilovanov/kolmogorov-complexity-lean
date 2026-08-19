import KolmogorovMathlib.Restricted.Improving
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting

/-!
# Restricted gap counting: the family description-count leaf

This file builds the restricted analogue of the unrestricted appearance-list /
index-selector machinery in `AlgorithmicStatistics/TwoPart/GapCounting.lean`,
filtered by membership in a `DescriptionFamily 𝒜` (via its computable
enumeration).  The end product is
`restricted_description_count_of_conditional_complexity_gap_aux`, the exact
content of the M5 leaf `restricted_description_count_of_conditional_complexity_gap`.

Everything here is a faithful mirror of the unrestricted proofs; the only new
ingredient is that the online enumeration is intersected with the family
enumeration `𝒜.enumeration.enum t`, so that the rank of `A` is bounded by the
number of *family* `(i,j)`-descriptions of `x`
(`descriptionsWithComplexityLeAndSizeLeIn 𝒜 U i j`), controlled by
`¬ ManyIJDescriptionsIn`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Family-filtered candidate codes: the unrestricted `candidateCodes` slice at
stage `t`, kept only if the code has already appeared in the family enumeration
`𝒜.enumeration.enum t`. -/
def familyCandidateCodes (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (j : ℕ)
    (x : BitString) (t : ℕ) : List BitString :=
  (candidateCodes c i j x t).filter (fun w => decide (w ∈ 𝒜.enumeration.enum t))

/-- The online enumeration of *family* `(i,j)`-descriptions of `x`, in appearance
order, deduplicated. Mirrors `appearanceListCodes`. -/
def familyAppearanceListCodes (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (j : ℕ)
    (x : BitString) : ℕ → List BitString
  | 0 => (familyCandidateCodes c i 𝒜 j x 0).eraseDups
  | t + 1 =>
      (familyAppearanceListCodes c i 𝒜 j x t ++ familyCandidateCodes c i 𝒜 j x (t + 1)).eraseDups

/-
Computability of the family-filtered candidate slice, as a function of
`((i,j),x),t`.  Mirrors `candidateCodes_primrec` but the family filter uses the
merely-`Computable` enumeration, so the result is `Computable`.
-/
theorem familyCandidateCodes_computable (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun p : ((ℕ × ℕ) × BitString) × ℕ =>
      familyCandidateCodes c p.1.1.1 𝒜 p.1.1.2 p.1.2 p.2) := by
  -- The function `familyCandidateCodes` is the composition of `candidateCodes` and `filter`.
  have h_filter : Computable (fun p : List BitString × List BitString => p.1.filter (fun w =>
      decide (w ∈ p.2))) := by
    exact (@list_filter_primrec (List BitString × List BitString) BitString _ _
      (fun a => a.1) (fun a w => decide (w ∈ a.2)) Primrec.fst
      (bitString_mem_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to_comp.of_eq
      (fun _ => rfl)
  exact (h_filter.comp ( Computable.pair ( ( candidateCodes_primrec c ).to_comp )
      ( 𝒜.enumeration.computable.comp ( Computable.snd ) ) )).of_eq (fun _ => rfl)

/-
Computability of the online family enumeration, as a function of `((i,j),x),t`.
Mirrors `appearanceListCodes_primrec` via `Computable.nat_rec`.
-/
theorem familyAppearanceListCodes_computable (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun p : ((ℕ × ℕ) × BitString) × ℕ =>
      familyAppearanceListCodes c p.1.1.1 𝒜 p.1.1.2 p.1.2 p.2) := by
  convert Computable.nat_rec _ _ _ using 1;
  rotate_left;
  · exact fun p => p.2;
  · exact fun p =>
      ( familyCandidateCodes c p.1.1.1 𝒜 p.1.1.2 p.1.2 0 ).eraseDups;
  · exact fun p q =>
      ( q.2 ++ familyCandidateCodes c p.1.1.1 𝒜 p.1.1.2 p.1.2 ( q.1 + 1 ) ).eraseDups;
  · exact Computable.snd;
  · have h_eraseDups : Primrec (fun l : List BitString => l.eraseDups) :=
      eraseDups_bitstring_primrec
    exact (Computable.comp ( h_eraseDups.to_comp )
        ( familyCandidateCodes_computable c 𝒜 |> Computable.comp <| Computable.pair (
          Computable.fst ) ( Computable.const 0 ) )).of_eq (fun _ => rfl)
  · have h_eraseDups : Computable (fun l : List BitString => l.eraseDups) :=
      eraseDups_bitstring_primrec.to_comp
    exact (h_eraseDups.comp ( Computable.list_append.comp ( Computable.snd.comp (
        Computable.snd ) ) ( familyCandidateCodes_computable c 𝒜 |> Computable.comp
          <| Computable.pair ( Computable.fst.comp <| Computable.fst )
          <| Computable.succ.comp <| Computable.fst.comp <| Computable.snd ) )).of_eq (fun _ => rfl)
  · funext p
    obtain ⟨p₁, t⟩ := p
    induction t with
    | zero => simp_all +decide [ familyAppearanceListCodes ]
    | succ t ih => simp_all +decide [ familyAppearanceListCodes ]

theorem mem_familyAppearanceListCodes_of_mem_familyCandidateCodes
    {c : Code} {i : ℕ} {𝒜 : PreDescriptionFamily} {j : ℕ} {x : BitString} {t : ℕ}
    {w : BitString} :
    w ∈ familyCandidateCodes c i 𝒜 j x t → w ∈ familyAppearanceListCodes c i 𝒜 j x t := by
  induction t generalizing w with
  | zero => exact fun h => mem_eraseDups_bitString.mpr h
  | succ t ih =>
    exact fun hw => mem_eraseDups_bitString.mpr (List.mem_append_right _ hw)

theorem exists_familyCandidate_of_mem_familyAppearanceListCodes
    {c : Code} {i : ℕ} {𝒜 : PreDescriptionFamily} {j : ℕ} {x : BitString} {t : ℕ}
    {w : BitString} (hw : w ∈ familyAppearanceListCodes c i 𝒜 j x t) :
    ∃ t', w ∈ familyCandidateCodes c i 𝒜 j x t' := by
  -- Split according to whether `w` first appears at the current or an earlier stage.
  induction t generalizing w with
  | zero => exact ⟨ 0, by simpa using mem_eraseDups_bitString.mp hw ⟩
  | succ t ih =>
    contrapose! hw;
    simp +decide only [familyAppearanceListCodes];
    rw [ mem_eraseDups_bitString ] ; simp +decide only [List.mem_append, hw, or_false];
    exact fun h => by obtain ⟨ t', ht' ⟩ := ih h; exact hw t' ht';

theorem familyAppearanceListCodes_nodup (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j : ℕ) (x : BitString) (t : ℕ) :
    (familyAppearanceListCodes c i 𝒜 j x t).Nodup := by
  induction t with
  | zero => exact nodup_eraseDups_bitString _
  | succ t ih => exact nodup_eraseDups_bitString _

theorem prefix_of_le_familyAppearanceListCodes (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j : ℕ) (x : BitString) {t1 t2 : ℕ} (hle : t1 ≤ t2) :
    familyAppearanceListCodes c i 𝒜 j x t1 <+: familyAppearanceListCodes c i 𝒜 j x t2 := by
  induction hle with
  | refl => rfl
  | @step t2 hle ih =>
    refine ih.trans ?_
    exact prefix_eraseDups_append_of_nodup _ _ (familyAppearanceListCodes_nodup c i 𝒜 j x _)

/-
Membership step: the canonical code of a family member `A ∋ x` of complexity
`≤ i` and log-size `≤ j` eventually appears in the online family enumeration.
Mirrors `code_mem_appearanceListCodes` (with `≤ i` instead of `= i`), and additionally
uses `𝒜.enumeration.complete` for the family filter.
-/
theorem code_mem_familyAppearanceListCodes {U : Map} {c : Code} (hc : IsCodeFor c U)
    (𝒜 : PreDescriptionFamily) (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (i j : ℕ)
    (hmem : 𝒜.mem A) (hxA : x ∈ A) (hcomp : setComplexity U A hA ≤ (i : ENat))
    (hsize : A.card ≤ 2 ^ j) :
    ∃ t₀, (codedUniformOn A hA).code ∈ familyAppearanceListCodes c i 𝒜 j x t₀ := by
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, (codedUniformOn A hA).code ∈ candidateCodes c i j x t₁ := by
    have := exists_max_countHalts c i;
    obtain ⟨ t₁, ht₁ ⟩ := this; use t₁
    simp_all +decide only [candidateCodes, List.mem_toFinset, List.mem_map, Bool.decide_and,
      List.filter_filter, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨ ?_, ?_, ?_ ⟩;
    · apply code_mem_snapshot_of_max hc i t₁ ht₁;
      · exact Classical.choose_spec ( exists_halting_program_of_complexity_le U (
          codedUniformOn A hA ) i hcomp ) |>.1;
      · grind;
    · have := dataPoints_codedUniformOn A hA
      simp_all +decide only [canonicalFinsetList_toFinset, and_true];
      replace this :=
          congr_arg List.toFinset this;
      rw [ Finset.ext_iff ] at this;
      specialize this x;
      simp_all +decide [ canonicalFinsetList ] ;
    · exact isCanonicalUniformCodeBool_iff _ |>.2 ( isCanonicalUniformCode_codedUniformOn A hA );
  obtain ⟨ t₂, ht₂ ⟩ := 𝒜.enumeration.complete A hA hmem;
  use t₂ + t₁;
  -- Since `t₂ + t₁ ≥ t₁`, we have `candidateCodes c i j x (t₂ + t₁) ⊇ candidateCodes c i j x t₁`.
  have h_candidateCodes_superset : candidateCodes c i j x (t₂ + t₁) ⊇ candidateCodes c i j x
      t₁ := by
    simp +decide only [candidateCodes, List.mem_toFinset, List.mem_map, Bool.decide_and,
      List.filter_filter];
    intro a ha
    simp_all +decide only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, decide_true,
      Bool.and_self, and_true];
    have h_snapshotCodes_superset : ∀ t₁ t₂,
        t₁ ≤ t₂ → snapshotCodes c i t₁ ⊆ snapshotCodes c i t₂ := by
      grind +suggestions;
    exact h_snapshotCodes_superset _ _ ( Nat.le_add_left _ _ ) ha.1;
  -- Since `t₂ + t₁ ≥ t₂`, we have `𝒜.enumeration.enum (t₂ + t₁) ⊇ 𝒜.enumeration.enum t₂`.
  have h_enum_superset : 𝒜.enumeration.enum (t₂ + t₁) ⊇ 𝒜.enumeration.enum t₂ := by
    have := 𝒜.enumeration.mono;
    exact List.Subset.trans ( List.IsPrefix.subset ( show 𝒜.enumeration.enum t₂ <+:
        𝒜.enumeration.enum ( t₂ + t₁ ) from by
          exact Nat.recOn t₁ ( by simp ) fun n ihn => by
            simpa [ Nat.add_assoc ] using ihn.trans ( this _ ) ) ) ( by simp +decide );
  exact mem_familyAppearanceListCodes_of_mem_familyCandidateCodes ( List.mem_filter.mpr ⟨
      h_candidateCodes_superset ht₁, by simpa using h_enum_superset ht₂ ⟩ )

/-
Rank bound: the online family enumeration never grows longer than the number
of *family* `(i,j)`-descriptions of `x`.  Mirrors
`appearanceListCodes_length_le_descriptionsContaining`, using `𝒜.enumeration.sound`
for family membership.
-/
theorem familyAppearanceListCodes_length_le {U : Map} {c : Code}
    (hc : IsCodeFor c U) (𝒜 : PreDescriptionFamily) (i j : ℕ) (x : BitString) (t : ℕ) :
    (familyAppearanceListCodes c i 𝒜 j x t).length
      ≤ ((descriptionsWithComplexityLeAndSizeLeIn 𝒜 U i j).filter (fun S => x ∈ S)).card := by
  -- Map each enumerated code to its finite support.
  set f : BitString → Finset BitString :=
      fun w => ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset;
  have h_inj : ∀ w ∈ familyAppearanceListCodes c i 𝒜 j x t,
      f w ∈ descriptionsWithComplexityLeAndSizeLeIn 𝒜 U i j ∧ x ∈ f w := by
    intro w hw
    obtain ⟨t', ht'⟩ := exists_familyCandidate_of_mem_familyAppearanceListCodes hw
    have hw_cand : w ∈ candidateCodes c i j x t' := by
      exact List.mem_filter.mp ht' |>.1
    have hw_enum : w ∈ 𝒜.enumeration.enum t' := by
      unfold familyCandidateCodes at ht'; aesop;
    generalize_proofs at *;
    obtain ⟨S', hS', hmem, hw_eq⟩ := 𝒜.enumeration.sound t' w hw_enum
    have hw_support : f w = S' := by
      have :=
          eq_codedUniformOn_of_isCanonicalUniformCodeBool (
            show isCanonicalUniformCodeBool w = true from by
              exact mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes hw_cand |>.1 )
      generalize_proofs at *;
      obtain ⟨ hne, hw_eq ⟩ := this
      generalize_proofs at *;
      exact codedUniformOn_code_injective hne hS' ( by
        simp +decide [ ‹w = ( codedUniformOn S' hS' ).code› ] at hw_eq ⊢;
        tauto ) ▸ rfl
    generalize_proofs at *;
    simp_all +decide [ descriptionsWithComplexityLeAndSizeLeIn ] ;
    have :=
        mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes hw_cand;
    simp_all +decide [ descriptionsWithComplexityLeAndSizeLe ] ;
    have :=
        snapshotDescriptionsAndSizeLe_subset_descriptions hc i j t' this.2.2;
    simp_all +decide [ descriptionsWithComplexityLe ] ;
    simp_all +decide [ descriptionsWithComplexityLeAndSizeLe, descriptionsWithComplexityLe ];
    grind +suggestions;
  have h_inj : ∀ w1 w2,
      w1 ∈ familyAppearanceListCodes c i 𝒜 j x t →
      w2 ∈ familyAppearanceListCodes c i 𝒜 j x t → f w1 = f w2 → w1 = w2 := by
    intros w1 w2 hw1 hw2 h_eq
    have h_eq_code : isCanonicalUniformCodeBool w1 = true ∧ isCanonicalUniformCodeBool w2 =
        true := by
      have h_eq_code : ∀ w ∈ familyAppearanceListCodes c i 𝒜 j x t,
          isCanonicalUniformCodeBool w = true := by
        intros w hw
        obtain ⟨t', ht'⟩ := exists_familyCandidate_of_mem_familyAppearanceListCodes hw
        have h_eq_code : isCanonicalUniformCodeBool w = true := by
          exact mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes ( List.mem_filter.mp
              ht' |>.1 ) |>.1
        exact h_eq_code;
      exact ⟨ h_eq_code w1 hw1, h_eq_code w2 hw2 ⟩;
    obtain ⟨h1, h2⟩ := eq_codedUniformOn_of_isCanonicalUniformCodeBool h_eq_code.left
    obtain ⟨h3, h4⟩ := eq_codedUniformOn_of_isCanonicalUniformCodeBool h_eq_code.right;
    grobner;
  have h_card : (familyAppearanceListCodes c i 𝒜 j x t).toFinset.card ≤
      (descriptionsWithComplexityLeAndSizeLeIn 𝒜 U i j |>.filter (fun S => x ∈ S)).card := by
    have h_card : (familyAppearanceListCodes c i 𝒜 j x t).toFinset.card ≤ (Finset.image f
        (familyAppearanceListCodes c i 𝒜 j x t).toFinset).card := by
      rw [ Finset.card_image_of_injOn fun w hw w' hw' h =>
          h_inj w w' ( by simpa using hw ) ( by simpa using hw' ) h ];
    exact h_card.trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun w hw => by aesop );
  rwa [ List.toFinset_card_of_nodup ( familyAppearanceListCodes_nodup c i 𝒜 j x t ) ] at h_card

theorem familyAppearanceListCodes_length_lt_of_not_manyIJIn {U : Map} {c : Code}
    (hc : IsCodeFor c U) {𝒜 : PreDescriptionFamily} {x : BitString} {i j m : ℕ}
    (hnm : ¬ ManyIJDescriptionsIn 𝒜 U x i j m) (t : ℕ) :
    (familyAppearanceListCodes c i 𝒜 j x t).length < 2 ^ m := by
  rw [ManyIJDescriptionsIn, not_le] at hnm
  exact lt_of_le_of_lt (familyAppearanceListCodes_length_le hc 𝒜 i j x t) hnm

theorem familyAppearanceListCodes_length_le_two_pow_i {U : Map} {c : Code}
    (hc : IsCodeFor c U) (𝒜 : PreDescriptionFamily) (i j : ℕ) (x : BitString) (t : ℕ) :
    (familyAppearanceListCodes c i 𝒜 j x t).length ≤ 2 ^ (i + 1) := by
  classical
  refine (familyAppearanceListCodes_length_le hc 𝒜 i j x t).trans ?_
  refine le_trans (Finset.card_filter_le _ _) ?_
  refine le_trans ?_ (card_descriptionsWithComplexityLeAndSizeLe U i j)
  refine Finset.card_le_card ?_
  intro S hS
  have hS' := (Finset.mem_filter.mp (by
    unfold descriptionsWithComplexityLeAndSizeLeIn at hS; exact hS)).1
  exact hS'

/-- The computable index selector for the family enumeration. Mirrors
`indexSelectorFn`. -/
def familyIndexSelectorFn (c : Code) (𝒜 : PreDescriptionFamily) :
    BitString → BitString →. BitString := fun y w =>
  let x := decodeFirst y
  let i := selNat w
  let j := selAlpha w
  let h := selH w
  (Nat.rfind (fun t =>
      Part.some (decide (h < (familyAppearanceListCodes c i 𝒜 j x t).length)))).bind
    (fun t => Part.some (match (familyAppearanceListCodes c i 𝒜 j x t).drop h with
      | [] => []
      | a :: _ => a))

theorem partrec_familyIndexSelectorFn (c : Code) (𝒜 : PreDescriptionFamily) :
    Partrec (fun p : BitString × BitString => familyIndexSelectorFn c 𝒜 p.2 p.1) := by
  have hpredC : Computable (fun n : (BitString × BitString) × ℕ =>
      decide ( selH n.1.1 < ( familyAppearanceListCodes c ( selNat n.1.1 ) 𝒜
        ( selAlpha n.1.1 ) ( decodeFirst n.1.2 ) n.2 ).length )) := by
    have h_length_computable : Computable (fun (n : ((BitString × BitString) × ℕ)) =>
        (familyAppearanceListCodes c (selNat n.1.1) 𝒜 (selAlpha n.1.1)
          (decodeFirst n.1.2) n.2).length) := by
      have h_length_computable : Computable (fun (n : ((BitString × BitString) × ℕ)) =>
          familyAppearanceListCodes c (selNat n.1.1) 𝒜 (selAlpha n.1.1)
            (decodeFirst n.1.2) n.2) := by
        have := @familyAppearanceListCodes_computable c 𝒜;
        convert this.comp ( Computable.pair ( Computable.pair (
            selNat_primrec.to_comp.comp ( Computable.fst.comp ( Computable.fst ) ) )
            ( selAlpha_primrec.to_comp.comp ( Computable.fst.comp ( Computable.fst ) ) ) )
            ( decodeFirst_primrec.to_comp.comp ( Computable.snd.comp ( Computable.fst ) ) )
          |> Computable.pair <| Computable.snd ) using 1;
      exact Computable.list_length.comp h_length_computable;
    have h_selH_computable : Computable (fun (n : BitString × BitString) => selH n.1) := by
      exact Computable.comp ( selH_primrec.to_comp ) ( Computable.fst );
    have h_decide_computable : Computable (fun (n : ℕ × ℕ) => decide (n.1 < n.2)) :=
      (PrimrecPred.decide (Primrec.nat_lt.comp Primrec.fst Primrec.snd)).to_comp
    convert h_decide_computable.comp ( Computable.pair ( h_selH_computable.comp (
        Computable.fst ) ) h_length_computable ) using 1;
  have houtC : Computable (fun p : (BitString × BitString) × ℕ =>
      List.headI ( List.drop ( selH p.1.1 ) ( familyAppearanceListCodes c
        ( selNat p.1.1 ) 𝒜 ( selAlpha p.1.1 ) ( decodeFirst p.1.2 ) p.2 ) )) := by
    have h_drop_head : Computable (fun p : List BitString × ℕ =>
        List.headI (List.drop p.2 p.1)) := by
      have h_drop : Primrec (fun p : List BitString × ℕ => List.drop p.2 p.1) :=
        Primrec.list_drop.comp Primrec.snd Primrec.fst
      have h_headI : Primrec (fun l : List BitString => l.headI) := by
        convert Primrec.list_headI using 1;
      exact Computable.comp ( h_headI.to_comp ) ( h_drop.to_comp );
    convert h_drop_head.comp ( Computable.pair _ _ ) using 1;
    · convert familyAppearanceListCodes_computable c 𝒜 |> Computable.comp
        <| Computable.pair _ _ using 1;
      rotate_left;
      · exact fun (p : (BitString × BitString) × ℕ) =>
          ( ( selNat p.1.1, selAlpha p.1.1 ), decodeFirst p.1.2 );
      · exact fun (p : (BitString × BitString) × ℕ) => p.2;
      · exact Computable.pair ( Computable.pair ( selNat_primrec.to_comp.comp (
          Computable.fst.comp ( Computable.fst ) ) ) ( selAlpha_primrec.to_comp.comp (
            Computable.fst.comp ( Computable.fst ) ) ) ) ( decodeFirst_primrec.to_comp.comp (
              Computable.snd.comp ( Computable.fst ) ) );
      · exact Computable.snd;
      · grind +revert;
    · exact Computable.comp ( selH_primrec.to_comp )
        ( Computable.fst.comp ( Computable.fst ) );
  have hbind : Partrec (fun p : BitString × BitString =>
      (Nat.rfind (fun t => Part.some ( decide ( selH p.1 <
        ( familyAppearanceListCodes c ( selNat p.1 ) 𝒜 ( selAlpha p.1 )
          ( decodeFirst p.2 ) t ).length ) ))).bind (fun t =>
        Part.some ( ( familyAppearanceListCodes c ( selNat p.1 ) 𝒜 ( selAlpha p.1 )
          ( decodeFirst p.2 ) t ).drop ( selH p.1 ) |> List.headI ))) :=
    Partrec.bind (Partrec.rfind (Computable₂.partrec₂ hpredC))
      (Computable₂.partrec₂ houtC)
  refine hbind.of_eq fun p => ?_
  unfold familyIndexSelectorFn;
  congr! 2;
  cases h : List.drop ( selH p.1 )
      ( familyAppearanceListCodes c ( selNat p.1 ) 𝒜 ( selAlpha p.1 )
        ( decodeFirst p.2 ) ‹_› ) <;> aesop

theorem familyIndexSelectorFn_eq_code (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (j : ℕ)
    (x : BitString) (code : BitString) (t0 : ℕ)
    (h_mem : code ∈ familyAppearanceListCodes c i 𝒜 j x t0) :
    ∃ r < (familyAppearanceListCodes c i 𝒜 j x t0).length,
      ∀ (y w : BitString), decodeFirst y = x → selNat w = i → selAlpha w = j → selH w = r →
        familyIndexSelectorFn c 𝒜 y w = Part.some code := by
  obtain ⟨ r, l', hr_lt, hr_drop ⟩ :=
      exists_drop_eq_cons_of_mem ( familyAppearanceListCodes c i 𝒜 j x t0 ) code h_mem;
  use r;
  unfold familyIndexSelectorFn;
  refine ⟨ hr_lt, fun y w hy hi hj hr => ?_ ⟩;
  convert Part.eq_some_iff.mpr _ using 1;
  simp +decide only [hy, hi, hj, hr, Part.mem_bind_iff, Nat.mem_rfind,
    Part.mem_some_iff, true_eq_decide_iff, false_eq_decide_iff, not_lt];
  refine ⟨ Nat.find ( ⟨ t0, hr_lt ⟩ : ∃ t,
      r < ( familyAppearanceListCodes c i 𝒜 j x t ).length ), ?_, ?_ ⟩;
  · refine Nat.mem_rfind.mpr ⟨?_, fun { m } hm => ?_⟩
    · exact Part.mem_some_iff.mpr (decide_eq_true (Nat.find_spec ( ⟨ t0, hr_lt ⟩ :
        ∃ t, r < ( familyAppearanceListCodes c i 𝒜 j x t ).length ))).symm
    · exact Part.mem_some_iff.mpr (decide_eq_false fun contra =>
        hm.not_ge ( Nat.find_min' _ contra )).symm
  · have h_prefix : familyAppearanceListCodes c i 𝒜 j x (Nat.find (⟨t0, hr_lt⟩ : ∃ t,
      r < (familyAppearanceListCodes c i 𝒜 j x t).length)) <+:
        familyAppearanceListCodes c i 𝒜 j x t0 := by
      exact prefix_of_le_familyAppearanceListCodes c i 𝒜 j x ( Nat.find_min' _ hr_lt );
    obtain ⟨ k, hk ⟩ := h_prefix;
    have h_drop : List.drop r (familyAppearanceListCodes c i 𝒜 j x (Nat.find (⟨t0,
        hr_lt⟩ : ∃ t, r < (familyAppearanceListCodes c i 𝒜 j x t).length)) ++ k) = code :: l' := by
      rw [hk, hr_drop];
    rw [ List.drop_append ] at h_drop;
    cases h : List.drop r ( familyAppearanceListCodes c i 𝒜 j x ( Nat.find ( ⟨ t0,
        hr_lt ⟩ : ∃ t,
          r < ( familyAppearanceListCodes c i 𝒜 j x t ).length ) ) ) <;> simp_all +decide;
    grind

/-- The M5 leaf content: the restricted description-count bound. -/
theorem restricted_description_count_of_conditional_complexity_gap_aux
    (U : Map) (hU : IsOptimalPrefixConditional U) (𝒜 : PreDescriptionFamily) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n i j m kx : ℕ),
      x.length = n →
      𝒜.mem A →
      x ∈ A →
      setComplexity U A hA ≤ (i : ENat) →
      A.card ≤ 2 ^ j →
      HasPrefixComplexityValue U x kx →
      ¬ ManyIJDescriptionsIn 𝒜 U x i j m →
      KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤
        (m + logSlack c (n + i + j) : ENat) := by
  obtain ⟨c_opt, hc_opt⟩ : ∃ c_opt : Code, IsCodeFor c_opt U := by
    exact Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨c_kp, hkp⟩ := KP_partrec_cond_first_map_le U hU (familyIndexSelectorFn c_opt 𝒜)
    (partrec_familyIndexSelectorFn c_opt 𝒜)
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨C2, hC2⟩ := logSlack_linear_bound 2 3 7
  let C1 := C2 + c_kp + c_plain + c_len + 6
  use C1
  intro A hA x n i j m kx hn hmem hx hi hj hkx h_not_many
  obtain ⟨t₀, ht₀⟩ := code_mem_familyAppearanceListCodes hc_opt 𝒜 A hA x i j hmem hx hi hj
  set y := prefixComplexityContext x kx
  set code := (codedUniformOn A hA).code
  have hy : decodeFirst y = x := by
    dsimp [y, prefixComplexityContext]
    rw [decodeFirst_pairCode]
  obtain ⟨r, hr_lt, hr_spec⟩ := familyIndexSelectorFn_eq_code c_opt i 𝒜 j x code t₀ ht₀
  set w := richInput i j 0 r
  have hw_i : selNat w = i := selNat_richInput i j 0 r
  have hw_j : selAlpha w = j := selAlpha_richInput i j 0 r
  have hw_h : selH w = r := selH_richInput i j 0 r
  have h_some : familyIndexSelectorFn c_opt 𝒜 y w = Part.some code := hr_spec y w hy hw_i hw_j hw_h
  have h_in : code ∈ familyIndexSelectorFn c_opt 𝒜 y w := Part.eq_some_iff.mp h_some
  have h_bound1 : KP U code y ≤ KP U w y + (c_kp : ENat) := hkp w code y h_in
  have h_bound2 : KP U w y ≤ KPPlain U w + (c_plain : ENat) := hc_plain w y
  have h_bound3 : KPPlain U w ≤ (w.length : ENat) + 2 * (Nat.bits w.length).length + c_len :=
      hc_len w
  have h_w_len_r : w.length ≤ 2 * (Nat.bits i).length + 2 * (Nat.bits j).length + (Nat.bits
      r).length + 6 := by
    unfold w richInput selectorInput pack4
    simp [length_pairCode]
    omega
  have hr_lt_2m : r < 2 ^ m :=
    lt_trans hr_lt (familyAppearanceListCodes_length_lt_of_not_manyIJIn hc_opt h_not_many t₀)
  have hr_lt_2i : r < 2 ^ (i + 1) :=
    lt_of_lt_of_le hr_lt (familyAppearanceListCodes_length_le_two_pow_i hc_opt 𝒜 i j x t₀)
  let M := n + i + j
  have h_w_len_M : w.length ≤ 3 * M + 7 := by
    have hi_len : (Nat.bits i).length ≤ i := length_natBits_le_self i
    have hj_len : (Nat.bits j).length ≤ j := length_natBits_le_self j
    have hr_len : (Nat.bits r).length ≤ i + 1 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr hr_lt_2i
    omega
  have h_slack : c_kp + c_plain + c_len + 2 * (Nat.bits i).length + 2 * (Nat.bits j).length +
      6 + 2 * (Nat.bits w.length).length ≤ logSlack C1 M := by
    have hw1 : (Nat.bits w.length).length ≤ (Nat.bits (3 * M + 7)).length := by
      have h : w.length < 2 ^ (Nat.size (3 * M + 7)) :=
          lt_of_le_of_lt h_w_len_M (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hw3 : 2 * (Nat.bits (3 * M + 7)).length ≤ logSlack 2 (3 * M + 7) :=
        by unfold logSlack; omega
    have hw5 : logSlack C2 M = C2 * (Nat.bits M).length + C2 := rfl
    have hw6 : logSlack C1 M = (C2 + c_kp + c_plain + c_len + 6) * (Nat.bits M).length + (C2 +
        c_kp + c_plain + c_len + 6) := rfl
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
    _ ≤ ((2 * (Nat.bits i).length + 2 * (Nat.bits j).length + (Nat.bits r).length + 6 : ℕ) :
        ENat) + 2 * (Nat.bits w.length).length + c_len + c_plain + c_kp := by
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
    _ = (m : ENat) + (c_kp + c_plain + c_len + 2 * (Nat.bits i).length + 2 * (Nat.bits
        j).length + 6 + 2 * (Nat.bits w.length).length : ℕ) := by push_cast; ring
    _ ≤ (m : ENat) + logSlack C1 M := by gcongr

end Kolmogorov
