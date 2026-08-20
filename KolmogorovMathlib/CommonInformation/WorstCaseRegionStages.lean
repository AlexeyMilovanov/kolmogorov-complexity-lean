import KolmogorovMathlib.CommonInformation.WorstCaseRegionAdvice

/-!
# Common Information: indexed stage completion for the worst-case region

This file extends the three-stream recovery used for SUV Theorem 223 to the
finite indexed family required by Theorem 224.  The executable merged count
contains two unconditional streams and, for every member of
`muchnikConditionalBounds n`, one compact two-parameter conditional stream.
No three-parameter common-witness enumeration occurs in this advice layer.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- Pointwise upper bounds that saturate their mapped sum are all equalities. -/
theorem map_sum_pointwise_eq_of_le_and_sum_eq
    {ι : Type*} (l : List ι) (f g : ι → Nat)
    (hle : ∀ a ∈ l, f a ≤ g a)
    (hsum : (l.map f).sum = (l.map g).sum) :
  ∀ a ∈ l, f a = g a := by
  have map_sum_le :
      ∀ (r : List ι), (∀ a ∈ r, f a ≤ g a) →
        (r.map f).sum ≤ (r.map g).sum := by
    intro r hr
    induction r with
    | nil => simp
    | cons b r ih =>
        have hb : f b ≤ g b := hr b (List.Mem.head r)
        have htail : ∀ a ∈ r, f a ≤ g a := by
          intro a ha
          exact hr a (List.Mem.tail b ha)
        have hi := ih htail
        simp only [List.map_cons, List.sum_cons]
        omega
  induction l with
  | nil => simp
  | cons b r ih =>
      have hb : f b ≤ g b := hle b (List.Mem.head r)
      have htail : ∀ a ∈ r, f a ≤ g a := by
        intro a ha
        exact hle a (List.Mem.tail b ha)
      have htailSum :
          (r.map f).sum ≤ (r.map g).sum :=
        map_sum_le r htail
      have hhead : f b = g b := by
        simp only [List.map_cons, List.sum_cons] at hsum
        omega
      have hsumTail : (r.map f).sum = (r.map g).sum := by
        simp only [List.map_cons, List.sum_cons] at hsum
        omega
      intro a ha
      rcases (List.mem_cons.mp ha) with rfl | ha
      · exact hhead
      · exact ih htail hsumTail a ha

/-- Executable sum of both unconditional stage lengths and all indexed compact
conditional-stage lengths at time `t`. -/
def muchnikRegionMergedStageCount (c : Code) (n t : Nat) : Nat :=
  (boundedOutputStage c (2 * n - 1) t).length +
  (boundedOutputStage c (3 * n - 1) t).length +
  ((muchnikConditionalBounds n).map fun b =>
    (conditionalDescriptionPairsStage c b.1 b.2 t).length).sum

/-- The indexed merged-stage count is computable uniformly in `n` and `t`, for
each fixed decompressor code. -/
theorem muchnikRegionMergedStageCount_computable (c : Code) :
  Computable fun p : Nat × Nat =>
    muchnikRegionMergedStageCount c p.1 p.2 := by
  have hn : Primrec (fun p : Nat × Nat => p.1) := Primrec.fst
  have ht : Computable (fun p : Nat × Nat => p.2) := Computable.snd
  have hMarginalBound : Computable (fun p : Nat × Nat => 2 * p.1 - 1) :=
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 2) hn)
      (Primrec.const 1)).to_comp
  have hPairBound : Computable (fun p : Nat × Nat => 3 * p.1 - 1) :=
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 3) hn)
      (Primrec.const 1)).to_comp
  have hStage₁ : Computable (fun p : Nat × Nat =>
      boundedOutputStage c (2 * p.1 - 1) p.2) :=
    (boundedOutputStage_computable c).comp (hMarginalBound.pair ht)
  have hStage₂ : Computable (fun p : Nat × Nat =>
      boundedOutputStage c (3 * p.1 - 1) p.2) :=
    (boundedOutputStage_computable c).comp (hPairBound.pair ht)
  have hIndexedStage :
      Primrec (fun q : (Nat × Nat) × (Nat × Nat) =>
        conditionalDescriptionPairsStage c q.2.1 q.2.2 q.1.2) :=
    (conditionalDescriptionPairsStage_primrec c).comp
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))
  have hIndexedLength :
      Primrec₂ (fun (p : Nat × Nat) (b : Nat × Nat) =>
        (conditionalDescriptionPairsStage c b.1 b.2 p.2).length) :=
    (Primrec.list_length.comp hIndexedStage).to₂
  have hIndexedLengths :
      Primrec (fun p : Nat × Nat =>
        (muchnikConditionalBounds p.1).map fun b =>
          (conditionalDescriptionPairsStage c b.1 b.2 p.2).length) :=
    Primrec.list_map
      (muchnikConditionalBounds_primrec.comp hn)
      hIndexedLength
  have hListSum : Primrec (fun l : List Nat => l.sum) := by
    have hstep : Primrec₂
        (fun (_ : List Nat) (q : Nat × Nat) => q.1 + q.2) :=
      (Primrec.nat_add.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
    exact Primrec.list_foldr Primrec.id (Primrec.const 0) hstep
  have hIndexedSum : Computable (fun p : Nat × Nat =>
      ((muchnikConditionalBounds p.1).map fun b =>
        (conditionalDescriptionPairsStage c b.1 b.2 p.2).length).sum) :=
    (hListSum.comp hIndexedLengths).to_comp
  have hAdd : Computable₂ (fun a b : Nat => a + b) :=
    Primrec.nat_add.to_comp
  unfold muchnikRegionMergedStageCount
  exact hAdd.comp
    (hAdd.comp
      (Computable.list_length.comp hStage₁)
      (Computable.list_length.comp hStage₂))
    hIndexedSum

/-- Equality of the indexed stage-length sum with the semantic cardinality sum
forces every compact stream in the bound list to be complete. -/
theorem muchnikRegionConditionalStages_exact_of_sum
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n t : Nat}
    (hsum :
      ((muchnikConditionalBounds n).map fun b =>
        (conditionalDescriptionPairsStage c b.1 b.2 t).length).sum =
      ((muchnikConditionalBounds n).map fun b =>
        (conditionalDescriptionPairsLe V b.1 b.2).card).sum) :
  ∀ b ∈ muchnikConditionalBounds n,
    (conditionalDescriptionPairsStage c b.1 b.2 t).toFinset =
      conditionalDescriptionPairsLe V b.1 b.2 := by
  have hle :
      ∀ b ∈ muchnikConditionalBounds n,
        (conditionalDescriptionPairsStage c b.1 b.2 t).length ≤
          (conditionalDescriptionPairsLe V b.1 b.2).card := by
    intro b _
    let l := conditionalDescriptionPairsStage c b.1 b.2 t
    let F := conditionalDescriptionPairsLe V b.1 b.2
    have hsub : l.toFinset ⊆ F :=
      conditionalDescriptionPairsStage_toFinset_subset hc _ _ _
    calc
      l.length = l.toFinset.card :=
        (List.toFinset_card_of_nodup
          (conditionalDescriptionPairsStage_nodup c b.1 b.2 t)).symm
      _ ≤ F.card := Finset.card_le_card hsub
  have hpoint :=
    map_sum_pointwise_eq_of_le_and_sum_eq
      (muchnikConditionalBounds n)
      (fun b => (conditionalDescriptionPairsStage c b.1 b.2 t).length)
      (fun b => (conditionalDescriptionPairsLe V b.1 b.2).card)
      hle hsum
  intro b hb
  exact toFinset_eq_of_subset_card
    (conditionalDescriptionPairsStage_nodup c b.1 b.2 t)
    (conditionalDescriptionPairsStage_toFinset_subset hc _ _ _)
    (hpoint b hb)

/-- One finite stage simultaneously completes every compact stream indexed by
`muchnikConditionalBounds n`. -/
theorem exists_common_complete_stage_for_muchnikConditionalBounds
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    (n : Nat) :
  ∃ T, ∀ b ∈ muchnikConditionalBounds n,
    (conditionalDescriptionPairsStage c b.1 b.2 T).toFinset =
      conditionalDescriptionPairsLe V b.1 b.2 := by
  -- For each bound b, get a completion time T_b
  have h_exists : ∀ b ∈ muchnikConditionalBounds n,
      ∃ T, (conditionalDescriptionPairsStage c b.1 b.2 T).toFinset =
        conditionalDescriptionPairsLe V b.1 b.2 := fun b hb =>
    exists_conditionalDescriptionPairsStage_complete hc b.1 b.2
  -- Choose such T for each b (or 0 if none exists, but they all do)
  choose! T hT using h_exists
  -- Take the maximum over all completion times
  refine ⟨List.foldr max 0 ((muchnikConditionalBounds n).map T), ?_⟩
  intro b hb
  have hbT : b ∈ muchnikConditionalBounds n := hb
  have hTb := hT b hbT
  have hTle : T b ≤ List.foldr max 0 ((muchnikConditionalBounds n).map T) := by
    have hmem : T b ∈ (muchnikConditionalBounds n).map T := List.mem_map.mpr ⟨b, hbT, rfl⟩
    have hfoldr : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
      intro l x hx
      induction l with
      | nil => simp at hx
      | cons hd tl ih =>
        simp only [List.foldr]
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_max_left _ _
        · exact Nat.le_trans (ih hx) (le_max_right _ _)
    exact hfoldr _ _ hmem
  have hprefix : conditionalDescriptionPairsStage c b.1 b.2 (T b) <+:
      conditionalDescriptionPairsStage c b.1 b.2
        (List.foldr max 0 ((muchnikConditionalBounds n).map T)) :=
    conditionalDescriptionPairsStage_prefix_of_le c b.1 b.2 hTle
  apply complete_stage_persists hTle hprefix hTb
  intro w hw
  obtain ⟨z, v, rfl, hz, hv⟩ :=
    mem_conditionalDescriptionPairsStage_sound hc (List.mem_toFinset.mp hw)
  exact (mem_conditionalDescriptionPairsLe_iff V b.1 b.2
    (pairCode z v)).mpr ⟨z, v, rfl, hz, hv⟩

/-- Equality with the semantic advice total recovers both unconditional
streams and every indexed compact conditional stream. -/
theorem muchnikRegionMergedStage_exact_of_total
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n t : Nat}
    (hcount :
      muchnikRegionMergedStageCount c n t =
        muchnikRegionAdviceCount V n) :
    (boundedOutputStage c (2 * n - 1) t).toFinset =
        compressibleWords V [] (2 * n - 1) ∧
    (boundedOutputStage c (3 * n - 1) t).toFinset =
        compressibleWords V [] (3 * n - 1) ∧
    ∀ b ∈ muchnikConditionalBounds n,
      (conditionalDescriptionPairsStage c b.1 b.2 t).toFinset =
        conditionalDescriptionPairsLe V b.1 b.2 := by
  let l₁ := boundedOutputStage c (2 * n - 1) t
  let l₂ := boundedOutputStage c (3 * n - 1) t
  let l_cond := (muchnikConditionalBounds n).map fun b =>
    (conditionalDescriptionPairsStage c b.1 b.2 t).length
  let F₁ := compressibleWords V [] (2 * n - 1)
  let F₂ := compressibleWords V [] (3 * n - 1)
  let F_cond := (muchnikConditionalBounds n).map fun b =>
    (conditionalDescriptionPairsLe V b.1 b.2).card
  have hsub₁ : l₁.toFinset ⊆ F₁ :=
    boundedOutputStage_toFinset_subset_compressibleWords hc _ _
  have hsub₂ : l₂.toFinset ⊆ F₂ :=
    boundedOutputStage_toFinset_subset_compressibleWords hc _ _
  have hsub₃ : ∀ b ∈ muchnikConditionalBounds n,
      (conditionalDescriptionPairsStage c b.1 b.2 t).toFinset ⊆
      conditionalDescriptionPairsLe V b.1 b.2 := by
    intro b _
    exact conditionalDescriptionPairsStage_toFinset_subset hc _ _ _
  have hle₁ : l₁.length ≤ F₁.card := by
    calc l₁.length = l₁.toFinset.card :=
        (List.toFinset_card_of_nodup
          (boundedOutputStage_nodup c (2 * n - 1) t)).symm
      _ ≤ F₁.card := Finset.card_le_card hsub₁
  have hle₂ : l₂.length ≤ F₂.card := by
    calc l₂.length = l₂.toFinset.card :=
        (List.toFinset_card_of_nodup
          (boundedOutputStage_nodup c (3 * n - 1) t)).symm
      _ ≤ F₂.card := Finset.card_le_card hsub₂
  have hle₃ : l_cond.sum ≤ F_cond.sum := by
    have helper : ∀ (l : List (Nat × Nat)),
        (∀ b ∈ l, (conditionalDescriptionPairsStage c b.1 b.2 t).length ≤
          (conditionalDescriptionPairsLe V b.1 b.2).card) →
        ((l.map fun b => (conditionalDescriptionPairsStage c b.1 b.2 t).length).sum) ≤
        ((l.map fun b => (conditionalDescriptionPairsLe V b.1 b.2).card).sum) := by
      intro l hl
      induction l with
      | nil => simp
      | cons b l ih =>
          have hb : (conditionalDescriptionPairsStage c b.1 b.2 t).length ≤
              (conditionalDescriptionPairsLe V b.1 b.2).card := hl b (List.Mem.head l)
          have htail : ∀ b' ∈ l,
              (conditionalDescriptionPairsStage c b'.1 b'.2 t).length ≤
              (conditionalDescriptionPairsLe V b'.1 b'.2).card := by
            intro b' hb'
            exact hl b' (List.Mem.tail b hb')
          have hi := ih htail
          simp only [List.map_cons, List.sum_cons]
          omega
    exact helper (muchnikConditionalBounds n) (fun b hb => by
      calc (conditionalDescriptionPairsStage c b.1 b.2 t).length
          = (conditionalDescriptionPairsStage c b.1 b.2 t).toFinset.card :=
            (List.toFinset_card_of_nodup
              (conditionalDescriptionPairsStage_nodup c b.1 b.2 t)).symm
        _ ≤ (conditionalDescriptionPairsLe V b.1 b.2).card :=
            Finset.card_le_card (hsub₃ b hb))
  have hsum : l₁.length + l₂.length + l_cond.sum =
      F₁.card + F₂.card + F_cond.sum := by
    simp only [muchnikRegionMergedStageCount, muchnikRegionAdviceCount,
      muchnikRegionConditionalAdvice] at hcount
    exact hcount
  obtain ⟨hcard₁, hcard₂, hcard₃⟩ :=
    three_eq_of_le_and_sum_eq hle₁ hle₂ hle₃ hsum
  exact ⟨
    toFinset_eq_of_subset_card
      (boundedOutputStage_nodup c (2 * n - 1) t) hsub₁ hcard₁,
    toFinset_eq_of_subset_card
      (boundedOutputStage_nodup c (3 * n - 1) t) hsub₂ hcard₂,
    muchnikRegionConditionalStages_exact_of_sum hc hcard₃ ⟩

/-- The executable indexed merged count eventually reaches the exact semantic
advice total. -/
theorem exists_muchnikRegionMergedStageCount_eq
    {V : Map} {c : Code} (hc : IsCodeFor c V) (n : Nat) :
  ∃ t,
    muchnikRegionMergedStageCount c n t =
      muchnikRegionAdviceCount V n := by
  -- Get a common completion time for all conditional streams
  obtain ⟨T₃, hT₃⟩ := exists_common_complete_stage_for_muchnikConditionalBounds hc n
  -- Get completion times for the two unconditional streams
  let T₁ := boundedOutputCompletionTime c (2 * n - 1)
  let T₂ := boundedOutputCompletionTime c (3 * n - 1)
  let T := max T₁ (max T₂ T₃)
  have hT₁ : T₁ ≤ T := le_max_left _ _
  have hT₂ : T₂ ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hT₃le : T₃ ≤ T := le_trans (le_max_right _ _) (le_max_right _ _)
  have hStage₁ :
      boundedOutputStage c (2 * n - 1) T =
        completedBoundedOutput c (2 * n - 1) :=
    boundedOutputStage_eq_completed_of_completion_le c _ _ hT₁
  have hStage₂ :
      boundedOutputStage c (3 * n - 1) T =
        completedBoundedOutput c (3 * n - 1) :=
    boundedOutputStage_eq_completed_of_completion_le c _ _ hT₂
  -- All conditional streams are also complete at time T
  have hConditional : ∀ b ∈ muchnikConditionalBounds n,
      (conditionalDescriptionPairsStage c b.1 b.2 T).toFinset =
        conditionalDescriptionPairsLe V b.1 b.2 := by
    intro b hb
    have hprefix :
        conditionalDescriptionPairsStage c b.1 b.2 T₃ <+:
        conditionalDescriptionPairsStage c b.1 b.2 T :=
      conditionalDescriptionPairsStage_prefix_of_le c b.1 b.2 hT₃le
    exact complete_stage_persists hT₃le hprefix (hT₃ b hb)
      (conditionalDescriptionPairsStage_toFinset_subset hc _ _ _)
  refine ⟨T, ?_⟩
  unfold muchnikRegionMergedStageCount muchnikRegionAdviceCount
  -- Prove the cardinality equalities for each component
  have hCard₁ :
      (boundedOutputStage c (2 * n - 1) T).length =
        (compressibleWords V [] (2 * n - 1)).card := by
    rw [hStage₁]
    calc
      (completedBoundedOutput c (2 * n - 1)).length =
          (completedBoundedOutput c (2 * n - 1)).toFinset.card :=
        (List.toFinset_card_of_nodup
          (boundedOutputStage_nodup c (2 * n - 1)
            (maxHaltingStage c (2 * n - 1)))).symm
      _ = (compressibleWords V [] (2 * n - 1)).card :=
        congrArg Finset.card
          (completedBoundedOutput_toFinset_eq_compressibleWords hc _)
  have hCard₂ :
      (boundedOutputStage c (3 * n - 1) T).length =
        (compressibleWords V [] (3 * n - 1)).card := by
    rw [hStage₂]
    calc
      (completedBoundedOutput c (3 * n - 1)).length =
          (completedBoundedOutput c (3 * n - 1)).toFinset.card :=
        (List.toFinset_card_of_nodup
          (boundedOutputStage_nodup c (3 * n - 1)
            (maxHaltingStage c (3 * n - 1)))).symm
      _ = (compressibleWords V [] (3 * n - 1)).card :=
        congrArg Finset.card
          (completedBoundedOutput_toFinset_eq_compressibleWords hc _)
  have hCard₃ :
      ((muchnikConditionalBounds n).map fun b =>
        (conditionalDescriptionPairsStage c b.1 b.2 T).length).sum =
      ((muchnikConditionalBounds n).map fun b =>
        (conditionalDescriptionPairsLe V b.1 b.2).card).sum := by
    congr 1
    apply List.map_congr_left
    intro b hb
    have heq := hConditional b hb
    calc
      (conditionalDescriptionPairsStage c b.1 b.2 T).length =
          (conditionalDescriptionPairsStage c b.1 b.2 T).toFinset.card :=
        (List.toFinset_card_of_nodup
          (conditionalDescriptionPairsStage_nodup c b.1 b.2 T)).symm
      _ = (conditionalDescriptionPairsLe V b.1 b.2).card := congrArg Finset.card heq
  rw [hCard₁, hCard₂, hCard₃]
  rfl

end Kolmogorov
