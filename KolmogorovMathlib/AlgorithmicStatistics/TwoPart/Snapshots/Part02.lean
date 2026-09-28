import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Snapshot
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.RichChunks
import KolmogorovMathlib.Foundation.ListUtil

/-!
# Emitted chunks of the snapshot: soundness

The snapshot enumeration groups the half-rich descriptions it discovers into chunks of at most
`2 ^ j` elements, emitted as they fill up.  This part proves the emitted list is sound.

`emittedHalfRichChunks_foldStep_append` says one fold step either does nothing or appends a
chunk, `emittedHalfRichChunks_card_le` bounds a chunk by `2 ^ j`,
`emittedHalfRichChunks_mono` says the list only grows, and the `flatten` lemmas —
`…_flatten_subset`, `…_flatten_mem`, `…_flatten_nodup`,
`emittedHalfRichChunksList_flatten_nodup` — show the chunks are pairwise disjoint and
internally duplicate-free, so flattening loses nothing.  `snapshotDescList_length_le` bounds
the whole snapshot by `2 ^ (i + 1)`.  How many chunks there are is counted in `Part03`.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- A single `emittedHalfRichChunksFoldStep` either leaves the accumulator
unchanged or appends one new chunk, so a left fold over it always extends the
accumulator by some suffix. -/
theorem emittedHalfRichChunks_foldStep_append (j : ℕ) (half_rich L : List BitString)
    (acc : List (List BitString)) :
    ∃ r, L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc = acc ++ r := by
  induction L using List.reverseRecOn generalizing acc
  case' nil => exact ⟨[], by simp⟩
  case' append_singleton xs x ih =>
      obtain ⟨r, hr⟩ := ih acc
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hr]
      rcases Bool.eq_false_or_eq_true
          (decide (x ∈ (acc ++ r).flatten)) with h | h <;>
        simp only [emittedHalfRichChunksFoldStep, h, cond_true, cond_false]
      · exact ⟨r, rfl⟩
      · exact ⟨_, (List.append_assoc _ _ _)⟩

/-- Every chunk produced by a left fold of `emittedHalfRichChunksFoldStep` has
length at most `2 ^ j`, provided the starting accumulator does. -/
theorem emittedHalfRichChunks_foldStep_length (j : ℕ) (half_rich L : List BitString)
    (acc : List (List BitString)) (hacc : ∀ l ∈ acc, l.length ≤ 2 ^ j) :
    ∀ l ∈ L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc, l.length ≤ 2 ^ j := by
  induction L using List.reverseRecOn generalizing acc
  case' nil => simpa using hacc
  case' append_singleton xs x ih =>
      intro l hl
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hl
      set acc' := xs.foldl (emittedHalfRichChunksFoldStep j half_rich) acc with hacc'
      have hacc'_len : ∀ l ∈ acc', l.length ≤ 2 ^ j := ih acc hacc
      rcases Bool.eq_false_or_eq_true (decide (x ∈ acc'.flatten)) with h | h <;>
        simp only [emittedHalfRichChunksFoldStep, h, cond_true, cond_false] at hl
      · exact hacc'_len l hl
      · rw [List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | hl
        · exact hacc'_len l hl
        · subst hl
          rw [List.length_take]
          exact Nat.min_le_left _ _

/-- The list of emitted half-rich chunks only grows with time. -/
theorem emittedHalfRichChunks_mono (c : Code) (i j k : ℕ) (t : ℕ) :
    ∃ rest, emittedHalfRichChunks c i j k (t + 1) = emittedHalfRichChunks c i j k t ++ rest := by
  obtain ⟨r, hr⟩ := emittedHalfRichChunks_foldStep_append j
    ((snapshotRichElementsList c i j (k - 1) (t + 1)).eraseDups)
    ((snapshotRichElementsList c i j k (t + 1)).eraseDups)
    (emittedHalfRichChunksList c i j k t)
  refine ⟨r.map List.toFinset, ?_⟩
  simp only [emittedHalfRichChunks, emittedHalfRichChunksList, emittedHalfRichChunksStep, hr,
    List.map_append]

/-- Every emitted half-rich chunk has at most `2 ^ j` elements. -/
theorem emittedHalfRichChunks_card_le (c : Code) (i j k t : ℕ) (S : Finset BitString)
    (hS : S ∈ emittedHalfRichChunks c i j k t) : S.card ≤ 2 ^ j := by
  have h_length : ∀ tt, ∀ l ∈ emittedHalfRichChunksList c i j k tt, l.length ≤ 2 ^ j := by
    intro tt
    induction tt
    case' zero =>
        simp only [emittedHalfRichChunksList, emittedHalfRichChunksStep]
        exact emittedHalfRichChunks_foldStep_length j _ _ [] (by simp)
    case' succ n ih =>
        simp only [emittedHalfRichChunksList, emittedHalfRichChunksStep]
        exact emittedHalfRichChunks_foldStep_length j _ _ _ ih
  obtain ⟨l, hl_mem, hl_eq⟩ := List.mem_map.mp hS
  rw [← hl_eq]
  exact le_trans (List.toFinset_card_le l) (h_length t l hl_mem)

/-- A left fold of `emittedHalfRichChunksFoldStep` only ever extends the
flattened accumulator: the starting flatten is a subset of the final one. -/
theorem emittedHalfRichChunks_foldStep_flatten_subset (j : ℕ) (half_rich L : List BitString)
    (acc : List (List BitString)) :
    acc.flatten ⊆ (L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc).flatten := by
  obtain ⟨r, hr⟩ := emittedHalfRichChunks_foldStep_append j half_rich L acc
  rw [hr, List.flatten_append]
  exact List.subset_append_left _ _

/-
Every element of the rich list `L` ends up placed (i.e. in the flattened
accumulator) after the left fold of `emittedHalfRichChunksFoldStep`, since each
element either is already placed or becomes the head of a freshly emitted chunk
(and `2 ^ j ≥ 1`).
-/
theorem emittedHalfRichChunks_foldStep_mem_flatten (j : ℕ) (half_rich L : List BitString)
    (acc : List (List BitString)) (y : BitString) (hy : y ∈ L) :
    y ∈ (L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc).flatten := by
  induction L generalizing acc
  case' nil => simp at hy
  case' cons a as ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hy with rfl | hmem
      · refine emittedHalfRichChunks_foldStep_flatten_subset j half_rich as _ ?_
        unfold emittedHalfRichChunksFoldStep
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

/-
Every rich element appears in some emitted chunk at some time `t`.
-/
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
Every element placed by a left fold of `emittedHalfRichChunksFoldStep`
lies in `half_rich`, provided the seed list `L` and the starting accumulator do.
Indeed each new chunk is `(x :: filtered_half_rich).take (2^j)`, where the head
`x ∈ L ⊆ half_rich` and the tail is filtered from `half_rich`.
-/
theorem emittedHalfRichChunks_foldStep_flatten_mem (j : ℕ) (half_rich : List BitString)
    (L : List BitString) (acc : List (List BitString))
    (hL : ∀ y ∈ L, y ∈ half_rich)
    (hacc : ∀ y ∈ acc.flatten, y ∈ half_rich) :
    ∀ y ∈ (L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc).flatten,
      y ∈ half_rich := by
  have h_ind : ∀ (xs : List BitString) (acc : List (List BitString)), (∀ y ∈ xs, y ∈ half_rich) →
      (∀ y ∈ acc.flatten, y ∈ half_rich) →
      (∀ y ∈ (xs.foldl (emittedHalfRichChunksFoldStep j half_rich) acc).flatten,
        y ∈ half_rich) := by
    intros xs acc hxs hacc y hy; induction xs using List.reverseRecOn generalizing acc
    case' nil => exact hacc y hy
    case' append_singleton xs x ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.mem_flatten] at hy; obtain ⟨ l, hl₁,
          hl₂ ⟩ := hy; unfold emittedHalfRichChunksFoldStep at hl₁; by_cases hx : x ∈ (
              List.foldl (
                  emittedHalfRichChunksFoldStep j half_rich ) acc xs ).flatten
      · simp_all +decide only [List.mem_flatten, forall_exists_index, and_imp,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or,
          implies_true, forall_const, Bool.cond_true_right, Bool.or_false,
          List.filter_filter]
        convert ih acc hacc l _ hl₂ using 1;
        unfold emittedHalfRichChunksFoldStep at *; aesop;
      · simp_all +decide only [List.mem_flatten, forall_exists_index, and_imp,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or,
          implies_true, forall_const, Bool.cond_true_right, Bool.or_false,
          List.filter_filter, not_exists, not_and]
        unfold emittedHalfRichChunksFoldStep at *; by_cases hx : ∃ l ∈ List.foldl (
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
`emittedHalfRichChunksFoldStep`, when `half_rich` is `Nodup` and the starting
accumulator's flatten is `Nodup`.  Each appended chunk consists of fresh elements
(not already in the flattened accumulator) drawn without repetition from
`half_rich`, so it is internally `Nodup` and disjoint from the accumulator.
-/
theorem emittedHalfRichChunks_foldStep_flatten_nodup (j : ℕ) (half_rich : List BitString)
    (hhr : half_rich.Nodup) (L : List BitString) (acc : List (List BitString))
    (hacc : acc.flatten.Nodup) :
    (L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc).flatten.Nodup := by
  induction L using List.reverseRecOn generalizing acc
  case' nil => exact hacc
  case' append_singleton L ih ih_hyp =>
    unfold emittedHalfRichChunksFoldStep at *
    by_cases hx : ih ∈ (List.foldl (emittedHalfRichChunksFoldStep j half_rich) acc L).flatten <;>
      simp_all +decide only [List.mem_flatten, Bool.cond_true_right, Bool.or_false,
        List.filter_filter, List.foldl_append, List.foldl_cons, List.foldl_nil]
    · unfold emittedHalfRichChunksFoldStep at *; aesop;
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
          unfold emittedHalfRichChunksFoldStep at *; aesop;
      · simp_all +decide only [not_exists, not_and]
        convert hx using 1;
        unfold emittedHalfRichChunksFoldStep; aesop;

/-
The flatten of all emitted chunks is `Nodup`: the chunks are pairwise
disjoint and each is internally duplicate-free.
-/
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
  nodup_eraseDups_list L

/-- The emitted half-rich chunks are pairwise disjoint and internally duplicate-free, so their
concatenation has no repetition. -/
theorem emittedHalfRichChunksList_flatten_nodup (c : Code) (i j k t : ℕ) :
    ((emittedHalfRichChunksList c i j k t).flatten).Nodup := by
  induction t with
  | zero =>
    exact emittedHalfRichChunks_foldStep_flatten_nodup j _ (nodup_eraseDups _) _ _ (
      by simp)
  | succ t ih =>
    convert emittedHalfRichChunks_foldStep_flatten_nodup j _ _ _ _ ih using 1
    exact nodup_eraseDups _

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
    ∀ y ∈ (L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc).flatten,
      y ∈ acc.flatten ∨ y ∈ half_rich := by
  revert hL;
  induction L using List.reverseRecOn generalizing acc with
  | nil => aesop
  | append_singleton L ih =>
    unfold emittedHalfRichChunksFoldStep
    simp +decide only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatten, Bool.cond_true_right, Bool.or_false, List.filter_filter,
      List.foldl_append, List.foldl_cons, List.foldl_nil, forall_exists_index, and_imp]
    rename_i h; intro h' y x hx hy; by_cases h : ∃ l ∈ List.foldl ( fun chunks x => bif decide (
        ∃ l ∈ chunks, x ∈ l ) then chunks else chunks ++ [ List.take ( 2 ^ j ) ( x :: List.filter (
          fun a => !decide ( a = x ) && !decide ( ∃ l ∈ chunks, a ∈ l ) ) half_rich ) ] ) acc L,
            ih ∈ l
    · simp_all +decide only [true_or, implies_true, List.mem_flatten,
        forall_exists_index, and_imp, forall_const, decide_true, cond_true]
      unfold emittedHalfRichChunksFoldStep at *; aesop;
    · simp_all +decide only [true_or, implies_true, List.mem_flatten,
        forall_exists_index, and_imp, forall_const, decide_false, cond_false,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_exists, not_and]
      rcases hx with ( hx | rfl );
      · rename_i h''; specialize h'' acc y x
        simp_all +decide only [forall_const]
        exact h'' ( by unfold emittedHalfRichChunksFoldStep; aesop );
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

/-- Every rich description element is eventually emitted in some half-rich chunk. -/
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
        convert emittedHalfRichChunks_foldStep_mem_flatten j _ _ _ _ h_eraseDups using 1
  rw [List.mem_flatten] at h_flatten
  obtain ⟨l, hl₁, hl₂⟩ := h_flatten
  exact ⟨t₀, l.toFinset, List.mem_map.mpr ⟨l, hl₁, rfl⟩, by simpa using hl₂⟩

/-- Every emitted element occurs in at least `2 ^ (k - 1)` of the snapshot descriptions, which is
what "half-rich" means. -/
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
    simp only [emittedHalfRichChunksList, emittedHalfRichChunksStep] at hy
    rcases emittedHalfRichChunks_foldStep_flatten_mem_or j _ _ [] (hRich 0) y hy with h | h
    · simp at h
    · exact hMult 0 y h
  | succ t ih =>
    intro y hy
    rw [emittedHalfRichChunksList] at hy
    unfold emittedHalfRichChunksStep at hy
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
private theorem emittedHalfRichChunks_fold_step_mem_ne_nil (j : ℕ) (half_rich : List BitString)
    (M : List BitString) (acc : List (List BitString)) (hacc : ∀ l ∈ acc, l ≠ []) :
    ∀ l ∈ List.foldl (emittedHalfRichChunksFoldStep j half_rich) acc M, l ≠ [] := by
  induction M generalizing acc with
  | nil => simpa using hacc
  | cons x M ih =>
    rw [List.foldl_cons]
    apply ih
    intro l hl
    by_cases hx : x ∈ acc.flatten
    · exact hacc l (by simpa [emittedHalfRichChunksFoldStep, hx] using hl)
    · have hdecide : decide (x ∈ acc.flatten) = false := by simp [hx]
      simp only [emittedHalfRichChunksFoldStep, hdecide, cond_false, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with hl | rfl
      · exact hacc l hl
      · obtain ⟨n, hn⟩ : ∃ n, 2 ^ j = n + 1 :=
          ⟨2 ^ j - 1, by have := Nat.one_le_two_pow (n := j); omega⟩
        simp [hn]

/-- No emitted chunk is empty. -/
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
  convert List.Pairwise.imp_of_mem _ _;
  · use fun a b => a ≠ b;
  · aesop;
  · rw [ List.pairwise_map ];
    refine List.Pairwise.imp_of_mem ?_ ( List.nodup_flatten.mp h_nodup.1 |>.2 );
    intro a b ha hb hab h
    apply h_nodup.2 b hb
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hxb
    have hxa : x ∈ a := List.mem_toFinset.mp (h ▸ List.mem_toFinset.mpr hxb)
    exact (List.disjoint_iff_ne.mp hab) x hxa x hxb rfl

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
`emittedHalfRichChunksFoldStep` left fold, then every chunk appended during the
fold (present in the result but not in the starting accumulator `acc`) is full,
i.e. has length `2 ^ j`.  Contrapositively: a single non-full appended chunk
forces *every* `half_rich` element to be placed.
-/
theorem emittedHalfRichChunks_foldStep_unplaced_full (j : ℕ) (half_rich L : List BitString)
    (acc : List (List BitString)) (y : BitString)
    (hy_hr : y ∈ half_rich)
    (hy_unplaced : y ∉ (L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc).flatten) :
    ∀ S ∈ L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc,
      S ∉ acc → S.length = 2 ^ j := by
  induction L using List.reverseRecOn generalizing acc y
  case' nil => simp_all +decide
  case' append_singleton L ih _ => simp_all +decide only [List.mem_flatten, not_exists,
    not_and, List.foldl_append, List.foldl_cons, emittedHalfRichChunksFoldStep,
    Bool.cond_true_right, Bool.or_false, List.filter_filter, List.foldl_nil]
  rename_i h
  specialize h acc y hy_hr
  by_cases h' : ∃ l ∈ List.foldl (emittedHalfRichChunksFoldStep j half_rich) acc L,
      ih ∈ l
  · simp_all +decide only [decide_true, cond_true, not_false_eq_true, implies_true,
      forall_const]
  · simp_all +decide only [decide_false, cond_false, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, true_or, not_false_eq_true, implies_true, forall_const,
      not_exists, not_and]
    by_contra h_contra;
    have h_new_chunk_length : y ∈ List.take (2 ^ j)
        (ih :: List.filter (fun a => !decide (a = ih) && !decide (
          ∃ l ∈ List.foldl (emittedHalfRichChunksFoldStep j half_rich) acc L,
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
  by_contra h_contra; push_neg at h_contra;
  obtain ⟨x, hx_rich, hx_unplaced⟩ := h_contra
  have hx_half_rich : x ∈ (snapshotRichElementsList c i j (k - 1) t).eraseDups := by
    have h_eraseDups : ∀ {L : List BitString}, x ∈ L → x ∈ L.eraseDups := by
      intros L hL; induction L using List.reverseRecOn
      case' nil => simp_all +decide
      case' append_singleton L ih _ => simp_all +decide [ List.eraseDups_append ]
      grind
    exact h_eraseDups hx_rich
  have hx_unplaced_fold : x ∉ (List.foldl
      (emittedHalfRichChunksFoldStep j
        (snapshotRichElementsList c i j (k - 1) t).eraseDups)
      (if t > 0 then emittedHalfRichChunksList c i j k (t - 1) else [])
      (snapshotRichElementsList c i j k t).eraseDups).flatten := by
    cases t with
    | zero =>
      simpa only [emittedHalfRichChunksList, emittedHalfRichChunksStep, gt_iff_lt,
        lt_self_iff_false, ↓reduceIte] using hx_unplaced
    | succ t =>
      simpa only [emittedHalfRichChunksList, emittedHalfRichChunksStep, gt_iff_lt,
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
    · unfold emittedHalfRichChunksStep at hl; aesop;
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
  exact ⟨r, by simpa [emittedHalfRichChunksList, emittedHalfRichChunksStep] using hr⟩

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
by `emittedHalfRichChunksFoldStep` from accumulator `acc` increases the number
of nonfull (length `< 2^j`) chunks by at most one; and if it does increase the
count, then afterwards every half-rich element has been placed into the flatten.
The second conjunct is the invariant that makes the induction go through: once a
nonfull chunk is opened it swallows all currently-unplaced half-rich elements,
so no further chunk can ever be opened in the same step.
-/

end Kolmogorov
