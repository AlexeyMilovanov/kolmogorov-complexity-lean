import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.Part01

/-!
# The temporal enumeration of bad sets

The realization construction deletes the bad sets in the order in which they are discovered.
This module shows the resulting temporal enumeration is well behaved: duplicate-free
(`badSetsUpToTime_nodup`, `newBadSetsAtTime_nodup`), monotone in the time budget
(`badSetsUpToTime_mem_mono`), a sublist of the full bad enumeration
(`temporalBadEnumList_sublist_badEnumList`), and eventually constant — no new bad set appears
past the stage at which the relevant enumerations complete
(`newBadSetsAtTime_eq_nil_of_gt`, `temporalBadEnumList_eq_of_max`).

`badUnion_subset_temporal_of_max` is the completeness bridge: at a stabilization time the
temporal union already covers the whole bad union, so the lex-least survivor
(`lexLeastSurvivor_mem_rem`, `lexLeastSurvivor_encode_le`) is a survivor in the full sense.
The list lemmas around them (`filter_length_le_of_subset_of_nodup`, `filter_sum_toFinset_eq`,
`filter_sum_le_of_subset_of_nodup`) are what carry the refresh counts along a sublist.
-/



namespace Kolmogorov
open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- Past the stage at which all relevant enumerations are complete, no new bad sets
appear. -/
theorem newBadSetsAtTime_eq_nil_of_gt (c : Nat.Partrec.Code) {U : Map} (hc : IsCodeFor c U) (n :
    ℕ)
    (h : ℕ → ℕ) (m c_gen : ℕ) (t t₀ : ℕ)
    (h_gt : t₀ < t)
    (hmax : ∀ j, j < n → ∀ t', countHalts c j t' ≤ countHalts c j t₀) :
    newBadSetsAtTime c n h m c_gen t = [] := by
  obtain ⟨t_minus_1, ht⟩ : ∃ x, t = x + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt
      (lt_of_le_of_lt (Nat.zero_le _) h_gt))
  subst ht
  have h_ge : t₀ ≤ t_minus_1 := Nat.le_of_lt_succ h_gt
  have ht_ge : t₀ ≤ t_minus_1 + 1 := Nat.le_succ_of_le h_ge
  have h1 := badSetsUpToTime_eq_of_max c hc n h m c_gen (t_minus_1 + 1) t₀ ht_ge hmax
  have h2 := badSetsUpToTime_eq_of_max c hc n h m c_gen t_minus_1 t₀ h_ge hmax
  unfold newBadSetsAtTime
  simp only [h1, h2]
  exact List.filter_eq_nil_iff.mpr (fun S hS => by simp_all)

/-- Past that stage the temporal enumeration of bad sets no longer changes, proved
by induction on the extra steps. -/
theorem temporalBadEnumList_eq_of_max_aux (c : Nat.Partrec.Code) {U : Map} (hc : IsCodeFor c U)
    (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (t₀ k : ℕ)
    (h_ge : t₀ ≤ k)
    (hmax : ∀ j, j < n → ∀ t', countHalts c j t' ≤ countHalts c j t₀) :
    temporalBadEnumList c n h m c_gen k = temporalBadEnumList c n h m c_gen t₀ := by
  induction k, h_ge using Nat.le_induction with
  | base => rfl
  | succ k h_ge_k ih =>
    unfold temporalBadEnumList
    have h_range : List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] := by
      exact List.range_succ
    rw [h_range]
    rw [List.flatMap_append, List.flatMap_singleton]
    have h_ih : (List.range (k + 1)).flatMap (fun t => newBadSetsAtTime c n h m c_gen t) =
        temporalBadEnumList c n h m c_gen k := rfl
    rw [h_ih]
    have h_nil : newBadSetsAtTime c n h m c_gen (k + 1) = [] := by
      have h_gt : t₀ < k + 1 := Nat.lt_succ_of_le h_ge_k
      exact newBadSetsAtTime_eq_nil_of_gt c hc n h m c_gen (k + 1) t₀ h_gt hmax
    rw [h_nil, List.append_nil]
    exact ih

/-- Past the completion stage the temporal enumeration of bad sets is constant. -/
theorem temporalBadEnumList_eq_of_max (c : Nat.Partrec.Code) {U : Map} (hc : IsCodeFor c U) (n :
    ℕ)
    (h : ℕ → ℕ) (m c_gen : ℕ) (t t₀ : ℕ)
    (h_ge : t₀ ≤ t)
    (hmax : ∀ j, j < n → ∀ t', countHalts c j t' ≤ countHalts c j t₀) :
    temporalBadEnumList c n h m c_gen t = temporalBadEnumList c n h m c_gen t₀ :=
  temporalBadEnumList_eq_of_max_aux c hc n h m c_gen t₀ t h_ge hmax

/-- Split sublemma bounding the total number of refreshes for the temporal bad enumeration.
This separates the combinatorics (nodup and mapping to descriptions) from the stabilization
loop. -/
theorem temporalBadEnumList_sublist_badEnumList (U : Map) (c_U : Nat.Partrec.Code)
    (hc_code : IsCodeFor c_U U) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx T : ℕ) :
    ∀ x, x ∈ temporalBadEnumList c_U n h m c_gen T → x ∈ badEnumList U n h m c_gen kx :=
        by
  intro d hd
  unfold temporalBadEnumList at hd
  obtain ⟨t, _ht⟩ : ∃ t, d ∈ newBadSetsAtTime c_U n h m c_gen t ∧ t ≤ T := by
    simp only [List.mem_flatMap, List.mem_range] at hd
    rcases hd with ⟨t, _, hd⟩
    exact ⟨t, hd, by omega⟩
  have h_subset : d ∈ badSetsUpToTime c_U n h m c_gen t := by
    cases t <;> simp_all [newBadSetsAtTime]
  obtain ⟨j, hj⟩ : ∃ j, j ∈ (List.range n).filter (fun j => m + logSlack c_gen n < h j)
      ∧ d ∈
      (snapshotDescList c_U j (h j - (m + logSlack c_gen n)) t).map List.toFinset := by
    unfold badSetsUpToTime at h_subset
    rw [mem_List.dedup, List.mem_flatMap] at h_subset
    exact h_subset
  have h_subset_desc : d ∈ descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack
      c_gen n))
      := by
    have h_mem : d ∈ (snapshotDescList c_U j (h j - (m + logSlack c_gen n)) t).map
        List.toFinset → d
        ∈ snapshotDescriptionsAndSizeLe c_U j (h j - (m + logSlack c_gen n)) t := by
      intro hd_map
      have h_nodup := snapshotDescList_nodup_map_toFinset c_U j (h j - (m + logSlack c_gen n)) t
      rcases List.mem_map.mp hd_map with ⟨orig, horig, heq⟩
      subst heq
      rw [← h_nodup.2]
      exact List.mem_toFinset.mpr (List.mem_map_of_mem (f := List.toFinset) horig)
    exact snapshotDescriptionsAndSizeLe_subset_descriptions hc_code j (h j - (m + logSlack c_gen
        n)) t (h_mem hj.2)
  have h_final : d ∈ (badEnumList U n h m c_gen kx).toFinset := by
    rw [badEnumList, List.mem_toFinset, Finset.mem_toList, Finset.mem_biUnion]
    refine ⟨j, ?_, h_subset_desc⟩
    simpa only [Finset.mem_filter, Finset.mem_range, List.mem_filter, List.mem_range,
      decide_eq_true_eq] using hj.1
  exact List.mem_toFinset.mp h_final

/-- A repetition-free list contained in another has no more entries passing a test
than the larger one. -/
theorem filter_length_le_of_subset_of_nodup {α} (L1 L2 : List α) (p : α → Bool)
    (h_nodup1 : L1.Nodup) (h_nodup2 : L2.Nodup)
    (h_sub : ∀ x ∈ L1, x ∈ L2) :
    (L1.filter p).length ≤ (L2.filter p).length := by
  classical
  have h1 : (L1.filter p).length = (L1.toFinset.filter (fun x => p x = true)).card := by
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter p h_nodup1)]
    exact congr_arg Finset.card (List.toFinset_filter L1 p)
  have h2 : (L2.filter p).length = (L2.toFinset.filter (fun x => p x = true)).card := by
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter p h_nodup2)]
    exact congr_arg Finset.card (List.toFinset_filter L2 p)
  rw [h1, h2]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨List.mem_toFinset.mpr (h_sub x (List.mem_toFinset.mp hx.1)), hx.2⟩

/-- Summing a function over the filtered set of a repetition-free list agrees with
summing over the filtered list. -/
theorem filter_sum_toFinset_eq {α} [DecidableEq α] (L : List α) (p : α → Bool) (f : α →
    ℕ)
    (h_nodup : L.Nodup) :
    ((L.toFinset.filter (fun x => p x = true)).toList.map f).sum = ((L.filter p).map f).sum :=
        by
  let S := L.toFinset.filter (fun x => p x = true)
  have hleft : ((L.toFinset.filter (fun x => p x = true)).toList.map f).sum = S.sum f := by
    symm
    simp [S]
  have hright : ((L.filter p).map f).sum = S.sum f := by
    symm
    have hnod : (L.filter p).Nodup := List.Nodup.filter p h_nodup
    simpa [S, List.toFinset_filter] using (List.sum_toFinset f (l := L.filter p) hnod)
  rw [hleft, hright]

/-- For a repetition-free sublist, the sum over the entries passing a test is at
most the corresponding sum for the larger list. -/
theorem filter_sum_le_of_subset_of_nodup {α} (L1 L2 : List α) (p : α → Bool) (f : α →
    ℕ)
    (h_nodup1 : L1.Nodup) (h_nodup2 : L2.Nodup)
    (h_sub : ∀ x ∈ L1, x ∈ L2) :
    ((L1.filter p).map f).sum ≤ ((L2.filter p).map f).sum := by
  classical
  let S1 := L1.toFinset.filter (fun x => p x = true)
  let S2 := L2.toFinset.filter (fun x => p x = true)
  have h1 : ((L1.filter p).map f).sum = S1.sum f := by
    symm
    have hnod : (L1.filter p).Nodup := List.Nodup.filter p h_nodup1
    simpa [S1, List.toFinset_filter] using (List.sum_toFinset f (l := L1.filter p) hnod)
  have h2 : ((L2.filter p).map f).sum = S2.sum f := by
    symm
    have hnod : (L2.filter p).Nodup := List.Nodup.filter p h_nodup2
    simpa [S2, List.toFinset_filter] using (List.sum_toFinset f (l := L2.filter p) hnod)
  rw [h1, h2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨List.mem_toFinset.mpr (h_sub x (List.mem_toFinset.mp hx.1)), hx.2⟩
  · intro x _ _
    exact Nat.zero_le (f x)

/-- `List.dedup` produces a duplicate-free list. -/
theorem List.dedup_nodup {α} [DecidableEq α] (l : List α) : (List.dedup l).Nodup := by
  induction l with
  | nil => simp [List.dedup]
  | cons a l ih =>
    unfold List.dedup
    split_ifs with hmem
    · exact ih
    · exact List.nodup_cons.mpr ⟨hmem, ih⟩

/-- The snapshot bad-set enumeration up to time `t` is duplicate-free. -/
theorem badSetsUpToTime_nodup (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen t :
    ℕ) :
    (badSetsUpToTime c n h m c_gen t).Nodup := by
  unfold badSetsUpToTime
  exact List.dedup_nodup _

/-- Membership in `badSetsUpToTime` is monotone in the time budget: the snapshot
description universe only grows. -/
theorem badSetsUpToTime_mem_mono (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen :
    ℕ)
    {t t' : ℕ} (hle : t ≤ t') {d : Finset BitString}
    (hd : d ∈ badSetsUpToTime c n h m c_gen t) :
    d ∈ badSetsUpToTime c n h m c_gen t' := by
  unfold badSetsUpToTime at hd ⊢
  rw [mem_List.dedup] at hd ⊢
  rw [List.mem_flatMap] at hd ⊢
  obtain ⟨j, hj, hdj⟩ := hd
  refine ⟨j, hj, ?_⟩
  -- Convert list membership to membership in `snapshotDescriptionsAndSizeLe`,
  -- use its monotonicity, and convert back.
  have hkey : ∀ s, (d ∈ (snapshotDescList c j (h j - (m + logSlack c_gen n)) s).map
      List.toFinset)
      ↔ d ∈ snapshotDescriptionsAndSizeLe c j (h j - (m + logSlack c_gen n)) s := by
    intro s
    rw [← List.mem_toFinset, snapshotDescList_nodup_map_toFinset c j (h j - (m + logSlack
        c_gen n)) s |>.2]
  rw [hkey] at hdj ⊢
  exact snapshotDescriptionsAndSizeLe_subset_of_le c j (h j - (m + logSlack c_gen n)) hle hdj

/-- The newly-discovered bad sets at time `t` are among those discovered up to `t`. -/
theorem newBadSetsAtTime_mem_badSetsUpToTime (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ)
    (m c_gen t : ℕ) {d : Finset BitString}
    (hd : d ∈ newBadSetsAtTime c n h m c_gen t) :
    d ∈ badSetsUpToTime c n h m c_gen t := by
  cases t with
  | zero => simpa [newBadSetsAtTime] using hd
  | succ s =>
    rw [newBadSetsAtTime, List.mem_filter] at hd
    exact hd.1

/-- The newly-discovered bad sets at time `t` are duplicate-free. -/
theorem newBadSetsAtTime_nodup (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen t :
    ℕ) :
    (newBadSetsAtTime c n h m c_gen t).Nodup := by
  cases t with
  | zero => simpa [newBadSetsAtTime] using badSetsUpToTime_nodup c n h m c_gen 0
  | succ s =>
    rw [newBadSetsAtTime]
    exact (badSetsUpToTime_nodup c n h m c_gen (s + 1)).filter _

/-- Bad sets discovered at distinct times are disjoint: a set first discovered at
time `t` is already in `badSetsUpToTime` at every later time, so it is filtered out
of `newBadSetsAtTime` there. -/
theorem newBadSetsAtTime_disjoint (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen :
    ℕ)
    {t t' : ℕ} (hlt : t < t') :
    List.Disjoint (newBadSetsAtTime c n h m c_gen t) (newBadSetsAtTime c n h m c_gen t') := by
  intro d hd hd'
  obtain ⟨s, rfl⟩ : ∃ s, t' = s + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  rw [newBadSetsAtTime, List.mem_filter] at hd'
  have hts : t ≤ s := Nat.lt_succ_iff.mp hlt
  have : d ∈ badSetsUpToTime c n h m c_gen s :=
    badSetsUpToTime_mem_mono c n h m c_gen hts
      (newBadSetsAtTime_mem_badSetsUpToTime c n h m c_gen t hd)
  simp only [decide_eq_true_eq] at hd'
  exact hd'.2 this

/-- The temporal enumeration of bad sets has no repetitions. -/
theorem temporalBadEnumList_nodup (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen t
    : ℕ) :
    (temporalBadEnumList c n h m c_gen t).Nodup := by
  unfold temporalBadEnumList
  rw [List.nodup_flatMap]
  refine ⟨fun x _ => newBadSetsAtTime_nodup c n h m c_gen x, ?_⟩
  refine (List.pairwise_lt_range (n := t + 1)).imp ?_
  intro a b hab
  exact newBadSetsAtTime_disjoint c n h m c_gen hab

/-- The greedy window over the temporal bad-set enumeration leaves a remainder of at
most `2 ^ (i + 1) + n * 2 ^ (i + 1)`. -/
theorem temporalBadEnumList_bound (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U)
    (n kx : ℕ) (h : ℕ → ℕ) (m c_gen i t : ℕ) (c : ℕ) (hc : ProfileCurve U c n kx m
        h)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h
        m c_gen kx).length).Nonempty)
    :
    (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
      (temporalBadEnumList c_U n h m c_gen t)).2.2 ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) := by
  have hW : 0 < 2 ^ h i := pow_pos (by decide) _
  have h_surv :
      (stringsOfLength n \ (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^
          h i)) (temporalBadEnumList c_U n h m c_gen t)).1).Nonempty
      := by
    -- The temporal deletions are all elements of `badEnumList`, so the fold's deleted
    -- set is contained in the full `badUnionUpTo`, and `hrem` supplies a survivor.
    obtain ⟨x, hx⟩ := hrem
    rw [Finset.mem_sdiff] at hx
    refine ⟨x, ?_⟩
    rw [Finset.mem_sdiff]
    refine ⟨hx.1, fun hxdel => hx.2 ?_⟩
    have hsub : (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
        (temporalBadEnumList c_U n h m c_gen t)).1
          ⊆ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length
              := by
      refine GreedyWindow.fold_deleted_subset _ _ _ _ (fun d hd => ?_)
      have hdmem : d ∈ badEnumList U n h m c_gen kx :=
        temporalBadEnumList_sublist_badEnumList U c_U hc_code n h m c_gen kx t d hd
      exact Finset.inter_subset_left.trans (subset_badUnionUpTo_full _ hdmem)
    exact hsub hxdel
  have h_bound := GreedyWindow.fold_count_split_div_le_of_survivor_toFinset (stringsOfLength n)
      (2 ^ h i) hW (fun S => firstElements S (2 ^ h i)) (fun S => firstElements_subset S (2 ^ h
      i)) (fun S => firstElements_card S (2 ^ h i)) (temporalBadEnumList c_U n h m c_gen t)
      (bucket1Pred U i) (temporalBadEnumList_nodup c_U n h m c_gen t) h_surv
  have h_nodup1 := temporalBadEnumList_nodup c_U n h m c_gen t
  have h_nodup2 : (badEnumList U n h m c_gen kx).Nodup := by
    unfold badEnumList
    exact Finset.nodup_toList _
  have h_sub := temporalBadEnumList_sublist_badEnumList U c_U hc_code n h m c_gen kx t
  have h_len_le := filter_length_le_of_subset_of_nodup _ _ (bucket1Pred U i) h_nodup1 h_nodup2
      h_sub
  have h_sum_le := filter_sum_le_of_subset_of_nodup _ _ (fun d => !bucket1Pred U i d) (fun d =>
      (d ∩ stringsOfLength n).card) h_nodup1 h_nodup2 h_sub
  have h_len_b1 := bucket1_bound U n h m c_gen kx i
  have h_sum_b2 := bucket2_bound_of_curve U c n kx m c_gen h hc i
  have h_len_eq :
      ((temporalBadEnumList c_U n h m c_gen t).toFinset.filter (fun d => bucket1Pred U i d =
          true)).card
      = ((temporalBadEnumList c_U n h m c_gen t).filter (bucket1Pred U i)).length := by
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ h_nodup1)]
    exact congr_arg Finset.card (List.toFinset_filter _ _).symm
  have h_sum_eq :
      (((temporalBadEnumList c_U n h m c_gen t).toFinset.filter (fun d => !(bucket1Pred U i d)
          = true)).toList.map (fun d => (d ∩ stringsOfLength n).card)).sum
      =
      (((temporalBadEnumList c_U n h m c_gen t).filter (fun d => !bucket1Pred U i d)).map (fun
          d => (d ∩ stringsOfLength n).card)).sum
      := by
    simpa using (filter_sum_toFinset_eq (temporalBadEnumList c_U n h m c_gen t)
      (fun d => !bucket1Pred U i d) (fun d => (d ∩ stringsOfLength n).card) h_nodup1)
  calc (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
      (temporalBadEnumList c_U n h m c_gen t)).2.2
    _ ≤ ((temporalBadEnumList c_U n h m c_gen t).toFinset.filter (fun d => bucket1Pred U i d
        = true)).card +
        (((temporalBadEnumList c_U n h m c_gen t).toFinset.filter (fun d => !(bucket1Pred U i
            d) = true)).toList.map (fun d => (d ∩ stringsOfLength n).card)).sum / 2 ^ h i :=
            h_bound
    _ = ((temporalBadEnumList c_U n h m c_gen t).filter (bucket1Pred U i)).length +
        (((temporalBadEnumList c_U n h m c_gen t).filter (fun d => !bucket1Pred U i d)).map
            (fun d => (d ∩ stringsOfLength n).card)).sum
            / 2 ^ h i := by
      rw [h_len_eq, h_sum_eq]
    _ ≤ ((badEnumList U n h m c_gen kx).filter (bucket1Pred U i)).length +
        (((badEnumList U n h m c_gen kx).filter (fun d => !bucket1Pred U i d)).map (fun d => (d
            ∩ stringsOfLength n).card)).sum
            / 2 ^ h i := by
      apply Nat.add_le_add
      · exact h_len_le
      · exact Nat.div_le_div_right h_sum_le
    _ ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1 + h i) / 2 ^ h i := by
      apply Nat.add_le_add
      · exact h_len_b1
      · exact Nat.div_le_div_right h_sum_b2
    _ = 2 ^ (i + 1) + n * 2 ^ (i + 1) := by
      have h_pow : 2 ^ (i + 1 + h i) = 2 ^ (i + 1) * 2 ^ h i := pow_add 2 (i + 1) (h i)
      rw [h_pow]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_div_cancel _ hW]

/-
Simultaneous stabilization of the halting-count snapshots across all finitely many
levels `j < n`.  Each `countHalts c j ·` is monotone (`countHalts_mono`) and bounded
(`countHalts_le_length`), hence eventually constant at its maximum (`exists_max_countHalts`);
taking the maximum of the finitely many stabilization times yields a single `t₀` that is
simultaneously a stabilization point and a level-wise maximum.
-/
theorem exists_simultaneous_stable_countHalts (c : Nat.Partrec.Code) (n : ℕ) :
    ∃ t₀, (∀ j < n, ∀ t ≥ t₀, countHalts c j t = countHalts c j t₀) ∧
          (∀ j < n, ∀ t', countHalts c j t' ≤ countHalts c j t₀) := by
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, ∀ j < n, ∀ t ≥ t₀, countHalts c j t = countHalts
      c j t₀ := by
    have h_const : ∀ j < n, ∃ t₀, ∀ t ≥ t₀, countHalts c j t = countHalts c j t₀
        := by
      intro j hj
      obtain ⟨t₀, ht₀⟩ : ∃ t₀, ∀ t', countHalts c j t' ≤ countHalts c j t₀ :=
          exists_max_countHalts c j;
      exact ⟨ t₀, fun t ht => le_antisymm ( ht₀ t ) ( countHalts_mono c j ht ) ⟩;
    choose! t₀ ht₀ using h_const;
    use Finset.sup (Finset.range n) t₀;
    intro j hj t ht;
    rw [ ht₀ j hj t ( le_trans ( Finset.le_sup ( f := t₀ ) ( Finset.mem_range.mpr hj ) ) ht
        ), ht₀ j hj ( Finset.sup ( Finset.range n ) t₀ ) ( Finset.le_sup ( f := t₀ ) (
        Finset.mem_range.mpr hj ) ) ];
  use t₀
  refine ⟨ht₀, fun j hj t' => ?_⟩
  by_cases h : t₀ ≤ t'
  · rw [ht₀ j hj t' h]
  · exact countHalts_mono c j (le_of_not_ge h)

/-- T1: The temporal refresh count is bounded and stabilizes to `version*`. -/
theorem temporalRefreshCount_stabilizes (U : Map) (c_U : Nat.Partrec.Code)
    (hc_code : IsCodeFor c_U U) (c n kx m c_gen i : ℕ) (h : ℕ → ℕ) (hc : ProfileCurve U
        c n kx m h)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h
        m c_gen kx).length).Nonempty) :
    ∃ T version, version ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) + 1 ∧
      temporalRefreshCount c_U n h m c_gen i T = version ∧
      ∀ t ≥ T, temporalRefreshCount c_U n h m c_gen i t = version := by
  obtain ⟨t₀, _ht₀, hmax⟩ := exists_simultaneous_stable_countHalts c_U n
  use t₀
  use temporalRefreshCount c_U n h m c_gen i t₀
  refine ⟨?_, rfl, ?_⟩
  · have h_bound := temporalBadEnumList_bound U c_U hc_code n kx h m c_gen i t₀ c hc hrem
    unfold temporalRefreshCount
    exact Nat.le_succ_of_le h_bound
  · intro t ht
    unfold temporalRefreshCount
    rw [temporalBadEnumList_eq_of_max c_U hc_code n h m c_gen t t₀ ht hmax]

/-
The temporal fold does not directly imply that `lexLeastSurvivor` belongs to the held
window.  Unlike `windowRefreshSequence`
(whose `_stabilizes` lemma pins the final refresh index at `L.length`, so the final window
is `firstElements (survivors) (2^{h i})`), the abstract `GreedyWindow.fold` only refreshes
when the window is fully deleted; at the end the window is the block installed at the *last*
refresh, `firstElements (G \ deletedₖ) (2^{h i})` for an earlier `deletedₖ ⊆
    deleted_final`.
Because `firstElements` keeps the `decodeBits`-smallest elements and
`G \ deletedₖ ⊇ G \ deleted_final`, the globally lex-least survivor need not be among the
smallest elements of the larger set `G \ deletedₖ` — smaller strings deleted only *after*
    the
last refresh can crowd it out.  So the final window contains *some* survivor, but not
necessarily *this* one from a static argument alone.

The bridge below adds the missing temporal information: extend the chronological
enumeration to a complete later time and use stability of the refresh count over the suffix.
If a smaller still-live element crowded out the global survivor at time `T`, the suffix would
eventually delete it and force another refresh, contradicting stability.

Conditional bridge from the abstract greedy-window survivor lemma to the concrete
temporal process.

This conditional bridge is used below after the completeness/stability lemmas provide
a later time `T_full` whose temporal list is the old list plus a suffix containing all
still-missing bad sets, and whose suffix adds no refresh.  The final hypothesis packages
the lex-minimality fact for the chosen complete list.
-/
theorem temporalWindow_contains_survivor_of_append_no_refresh
    (c_U : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen i T T_full : ℕ)
    (x : BitString) (hxG : x ∈ stringsOfLength n)
    (L_rest : List (Finset BitString))
    (h_append :
      temporalBadEnumList c_U n h m c_gen T_full =
        temporalBadEnumList c_U n h m c_gen T ++ L_rest)
    (h_no_refresh :
      temporalRefreshCount c_U n h m c_gen i T_full =
        temporalRefreshCount c_U n h m c_gen i T)
    (h_surv :
      ∀ d ∈ temporalBadEnumList c_U n h m c_gen T_full,
        x ∉ d)
    (h_min :
      ∀ y, y ∈ stringsOfLength n →
        (∀ d ∈ temporalBadEnumList c_U n h m c_gen T_full, y ∉ d) →
          Encodable.encode x ≤ Encodable.encode y) :
    x ∈ temporalWindow c_U n h m c_gen i T := by
  unfold temporalWindow GreedyWindow.fold
  exact GreedyWindow.temporalWindow_contains_survivor_aux
    (stringsOfLength n) Encodable.encode (2 ^ h i) (pow_pos (by decide) _)
    (temporalBadEnumList c_U n h m c_gen T) L_rest x
    (by
      intro d hd
      apply h_surv d
      rw [h_append]
      exact hd)
    hxG
    (by
      unfold temporalRefreshCount GreedyWindow.fold at h_no_refresh
      rw [h_append] at h_no_refresh
      exact h_no_refresh)
    (by
      intro y hyG hySurv
      apply h_min y hyG
      intro d hd
      rw [h_append] at hd
      exact hySurv d hd)
    (by
      intro a b _ _ hab
      exact Encodable.encode_injective hab)

/-
Every set appearing in the temporal bad-set enumeration is one of the genuine
`badEnumList` bad sets, hence contained in the full bad union.  Needs `IsCodeFor c_U U`
(without it `snapshotDescList c_U …` may enumerate arbitrary sets).  Chain:
`temporalBadEnumList` flattens `newBadSetsAtTime ⊆ badSetsUpToTime`, whose sets come, per
level `j < n` with `m + logSlack c_gen n < h j`, from `snapshotDescList` which
(`snapshotDescriptionsAndSizeLe_subset_descriptions`) lies inside
`descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n))` — exactly the sets
`badEnumList` unions.
-/
theorem temporalBadEnumList_subset_fullBadUnion (U : Map) (c_U : Nat.Partrec.Code)
    (hc_code : IsCodeFor c_U U) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx T : ℕ)
    {d : Finset BitString} (hd : d ∈ temporalBadEnumList c_U n h m c_gen T) :
    d ⊆ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length :=
        by
  unfold temporalBadEnumList at hd
  rw [List.mem_flatMap] at hd
  obtain ⟨t, _, hd_in⟩ := hd
  have h_subset : d ∈ badSetsUpToTime c_U n h m c_gen t := by
    cases t with
    | zero => exact hd_in
    | succ t' =>
      unfold newBadSetsAtTime at hd_in
      rw [List.mem_filter] at hd_in
      exact hd_in.1
  unfold badSetsUpToTime at h_subset
  rw [mem_List.dedup, List.mem_flatMap] at h_subset
  obtain ⟨j, hj_mem, hd_j⟩ := h_subset
  have h_subset_d :
      d ∈ descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n)) := by
    rw [List.mem_map] at hd_j
    obtain ⟨L, hL, hd_eq⟩ := hd_j
    have h_mem_snap := snapshotDescList_nodup_map_toFinset c_U j (h j - (m + logSlack c_gen n)) t
    have h_in_snap : d ∈ snapshotDescriptionsAndSizeLe c_U j (h j - (m + logSlack c_gen n)) t := by
      rw [← h_mem_snap.2, List.mem_toFinset, ← hd_eq]
      exact List.mem_map.mpr ⟨L, hL, rfl⟩
    exact snapshotDescriptionsAndSizeLe_subset_descriptions hc_code j
      (h j - (m + logSlack c_gen n)) t h_in_snap
  have h_subset_badEnum : d ∈ badEnumList U n h m c_gen kx := by
    unfold badEnumList
    rw [Finset.mem_toList, Finset.mem_biUnion]
    exact ⟨j, (by
      rw [Finset.mem_filter, Finset.mem_range]
      rw [List.mem_filter, List.mem_range] at hj_mem
      exact ⟨hj_mem.1, of_decide_eq_true hj_mem.2⟩), h_subset_d⟩
  exact subset_badUnionUpTo_full _ h_subset_badEnum

/-- The stabilized temporal window is nonempty.  Proved directly (no survivor-containment):
the survivor set `stringsOfLength n \ fullBadUnion` is nonempty (`hrem`) and disjoint from
every temporal deletion (`temporalBadEnumList_subset_fullBadUnion`), so
`GreedyWindow.fold_window_nonempty` applies. -/
theorem temporalWindow_nonempty (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i T : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    (temporalWindow c_U n h m c_gen i T).Nonempty := by
  unfold temporalWindow
  have hfirst_ne : ∀ S : Finset BitString, S.Nonempty → (firstElements S (2 ^ h i)).Nonempty
      := by
    intro S hS
    rw [← Finset.card_pos, firstElements_card]
    exact lt_min (Nat.one_le_pow _ _ (by decide)) (Finset.card_pos.mpr hS)
  have hdisj : ∀ d ∈ temporalBadEnumList c_U n h m c_gen T,
      Disjoint (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
        (badEnumList U n h m c_gen kx).length) (d ∩ stringsOfLength n) := by
    intro d hd
    have hsub := temporalBadEnumList_subset_fullBadUnion U c_U hc_code n h m c_gen kx (T := T)
        hd
    rw [Finset.disjoint_left]
    intro x hxS hxd
    exact (Finset.mem_sdiff.mp hxS).2 (hsub (Finset.mem_inter.mp hxd).1)
  exact GreedyWindow.fold_window_nonempty (stringsOfLength n)
    (fun S => firstElements S (2 ^ h i)) hfirst_ne _ hrem Finset.sdiff_subset _ hdisj

/-! ### Completeness bridge for `temporalWindow_contains_survivor`

The following helpers let us apply `temporalWindow_contains_survivor_of_append_no_refresh`
with the concrete `lexLeastSurvivor`: at a simultaneous stabilization time the temporal
enumeration covers every static bad set, so a temporal survivor is a full survivor, and
`lexLeastSurvivor` is the encoding-minimal full survivor. -/

/-
The chronological list at a later time extends the one at an earlier time.
-/
theorem temporalBadEnumList_append_of_le (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ)
    (m c_gen : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∃ L_rest, temporalBadEnumList c n h m c_gen b =
      temporalBadEnumList c n h m c_gen a ++ L_rest := by
  set L_b := List.range (b + 1)
  set L_a := List.range (a + 1);
  -- Split the range into the prefix through `a` and the suffix from `a + 1` to `b`.
  have h_split : L_b = L_a ++ (L_b.drop (a + 1)) := by
    have hmin : min (a + 1) (b + 1) = a + 1 := Nat.min_eq_left (Nat.succ_le_succ hab)
    conv_lhs => rw [← List.take_append_drop (a + 1) L_b]
    rw [List.take_range, hmin]
  -- `flatMap` preserves this prefix-suffix decomposition.
  have h_flatMap_split : List.flatMap (fun t => newBadSetsAtTime c n h m c_gen t) L_b =
      List.flatMap
      (fun t => newBadSetsAtTime c n h m c_gen t) L_a ++ List.flatMap
      (fun t => newBadSetsAtTime c n h m c_gen t) (L_b.drop (a + 1)) := by
    rw [ ← List.flatMap_append, ← h_split ];
  exact ⟨ _, h_flatMap_split ⟩

/-
Any set present in `badSetsUpToTime` at time `t` occurs in the chronological
enumeration up to `t`.
-/
theorem badSetsUpToTime_mem_temporal (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen
    : ℕ)
    {d : Finset BitString} (t : ℕ) (hd : d ∈ badSetsUpToTime c n h m c_gen t) :
    d ∈ temporalBadEnumList c n h m c_gen t := by
  induction t generalizing d with
  | zero =>
    simp only [temporalBadEnumList, zero_add, List.range_one, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, newBadSetsAtTime]
    exact hd
  | succ t ih =>
    rw [temporalBadEnumList, List.mem_flatMap]
    by_cases hprev : d ∈ badSetsUpToTime c n h m c_gen t
    · have hd_temporal := ih hprev
      rw [temporalBadEnumList, List.mem_flatMap] at hd_temporal
      obtain ⟨s, hs, hd_s⟩ := hd_temporal
      exact ⟨s, List.mem_range.mpr (Nat.lt_succ_of_lt (List.mem_range.mp hs)), hd_s⟩
    · exact ⟨t + 1, by simp, by simpa [newBadSetsAtTime, hprev] using hd⟩

/-
At a simultaneous stabilization time, every static bad set occurs in the temporal
enumeration.
-/
theorem badEnumList_mem_temporal_of_max (U : Map) (c_U : Nat.Partrec.Code)
    (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (m c_gen kx t : ℕ)
    (hmax : ∀ j < n, ∀ t', countHalts c_U j t' ≤ countHalts c_U j t)
    {d : Finset BitString} (hd : d ∈ badEnumList U n h m c_gen kx) :
    d ∈ temporalBadEnumList c_U n h m c_gen t := by
  unfold badEnumList at hd
  rw [Finset.mem_toList, Finset.mem_biUnion] at hd
  obtain ⟨j, hj, hd⟩ := hd
  have hd_map :
      d ∈ (snapshotDescList c_U j (h j - (m + logSlack c_gen n)) t).map List.toFinset := by
    have h_mem_snap := snapshotDescList_nodup_map_toFinset c_U j (h j - (m + logSlack c_gen n)) t
    have h_in_snap : d ∈ snapshotDescriptionsAndSizeLe c_U j (h j - (m + logSlack c_gen n)) t := by
      have h_eq := snapshotDescriptionsAndSizeLe_eq_descriptionsWithComplexityLeAndSizeLe
        hc_code j (h j - (m + logSlack c_gen n)) t
      have hj_range := (Finset.mem_filter.mp hj).1
      rw [Finset.mem_range] at hj_range
      rw [← h_eq (hmax j hj_range)] at hd
      exact hd
    rw [← h_mem_snap.2] at h_in_snap
    exact List.mem_toFinset.mp h_in_snap
  have hd_dedup : d ∈ List.dedup (((List.range n).filter
      (fun j => decide (m + logSlack c_gen n < h j))).flatMap (fun j =>
      (snapshotDescList c_U j (h j - (m + logSlack c_gen n)) t).map List.toFinset)) := by
    rw [mem_List.dedup, List.mem_flatMap]
    have hj_list : j ∈ (List.range n).filter (fun j => decide (m + logSlack c_gen n < h j)) := by
      rw [List.mem_filter, List.mem_range]
      have := Finset.mem_filter.mp hj
      rw [Finset.mem_range] at this
      exact ⟨this.1, decide_eq_true_eq.mpr this.2⟩
    exact ⟨j, hj_list, hd_map⟩
  exact badSetsUpToTime_mem_temporal c_U n h m c_gen t hd_dedup

/-- Completeness: at a stabilization time the temporal union covers the full bad union. -/
theorem badUnion_subset_temporal_of_max (U : Map) (c_U : Nat.Partrec.Code)
    (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (m c_gen kx t : ℕ)
    (hmax : ∀ j < n, ∀ t', countHalts c_U j t' ≤ countHalts c_U j t) :
    badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length ⊆
      badUnionUpTo (temporalBadEnumList c_U n h m c_gen t)
        (temporalBadEnumList c_U n h m c_gen t).length := by
  intro x hx
  rw [mem_badUnionUpTo_full] at hx ⊢
  obtain ⟨d, hd, hxd⟩ := hx
  exact ⟨d, badEnumList_mem_temporal_of_max U c_U hc_code n h m c_gen kx t hmax hd, hxd⟩

/-
Auxiliary: `lexLeastSurvivor` really is a survivor — a length-`n` string outside the
full bad-union — provided that set is nonempty.
-/
theorem lexLeastSurvivor_mem_rem (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    lexLeastSurvivor U n h m c_gen kx ∈
      stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
        (badEnumList U n h m c_gen kx).length := by
  unfold lexLeastSurvivor;
  have h_first1_nonempty :
      (firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
          (badEnumList U n h m c_gen kx).length) 1).Nonempty
      := by
    exact Finset.card_pos.mp ( by rw [ firstElements_card ] ; exact lt_min ( by norm_num ) (
        Finset.card_pos.mpr hrem ) );
  simp +zetaDelta only [ne_eq, Finset.toList_eq_nil, dite_not, dite_eq_ite, Finset.mem_sdiff] at
      *;
  split_ifs <;> simp_all +decide only [Finset.Nonempty, Finset.mem_sdiff, Finset.notMem_empty,
    exists_const];
  exact ⟨ Finset.mem_sdiff.mp ( firstElements_subset _ _ |> Finset.mem_of_subset <|
      Finset.mem_toList.mp <| List.head_mem <| by aesop ) |>.1, Finset.mem_sdiff.mp (
      firstElements_subset _ _ |> Finset.mem_of_subset <| Finset.mem_toList.mp <| List.head_mem
      <| by aesop ) |>.2 ⟩

/-
`lexLeastSurvivor` is the encoding-minimal element of the full survivor set.
-/
theorem lexLeastSurvivor_encode_le (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty)
    {y : BitString}
    (hy : y ∈ stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length) :
    Encodable.encode (lexLeastSurvivor U n h m c_gen kx) ≤ Encodable.encode y := by
  unfold lexLeastSurvivor;
  have h_first_nonempty :
      (firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
        (badEnumList U n h m c_gen kx).length) 1).toList ≠ [] := by
    exact List.ne_nil_of_mem (Finset.mem_toList.mpr
      (Classical.choose_spec (Finset.card_pos.mp (by
        rw [firstElements_card]
        exact Nat.pos_of_ne_zero (by aesop)))))
  obtain ⟨x, hx⟩ : ∃ x,
      x ∈ firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
        (badEnumList U n h m c_gen kx).length) 1 ∧
      x = (firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
        (badEnumList U n h m c_gen kx).length) 1).toList.head h_first_nonempty := by
    exact ⟨_, Finset.mem_toList.mp (List.head_mem h_first_nonempty), rfl⟩
  generalize_proofs at *;
  by_cases hyx : y ∈ firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m
      c_gen kx) (badEnumList U n h m c_gen kx).length) 1;
  · have := firstElements_card ( stringsOfLength n \ badUnionUpTo ( badEnumList U n h m c_gen
      kx ) ( badEnumList U n h m c_gen kx |> List.length ) ) 1; simp_all +decide ;
    rw [ Finset.card_eq_one ] at this ; aesop ( simp_config := { singlePass := true } ) ;
  · have := GreedyWindow.firstBlock_le_of_mem_of_not_mem Encodable.encode 1 (stringsOfLength n
      \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length) x
      hx.1 y hy hyx; aesop;

end Kolmogorov
