import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

def boundedOutputStage (c : Code) (m : ℕ) : ℕ → List BitString
  | 0 => (snapshotCodes c m 0).eraseDups
  | t + 1 => (boundedOutputStage c m t ++ snapshotCodes c m (t + 1)).eraseDups

theorem boundedOutputStage_nodup (c : Code) (m t : ℕ) : (boundedOutputStage c m t).Nodup := by
  induction t with
  | zero => exact nodup_eraseDups_bitString _
  | succ t ih => exact nodup_eraseDups_bitString _

theorem boundedOutputStage_prefix (c : Code) (m t : ℕ) :
    boundedOutputStage c m t <+: boundedOutputStage c m (t + 1) := by
  dsimp [boundedOutputStage]
  exact prefix_eraseDups_append_of_nodup _ _ (boundedOutputStage_nodup c m t)

theorem boundedOutputStage_prefix_of_le (c : Code) (m : ℕ) {t1 t2 : ℕ} (h : t1 ≤ t2) :
    boundedOutputStage c m t1 <+: boundedOutputStage c m t2 := by
  induction h with
  | refl => exact List.prefix_refl _
  | step ht ih => exact List.IsPrefix.trans ih (boundedOutputStage_prefix c m _)

theorem boundedOutputStage_primrec (c : Code) :
    Primrec (fun p : ℕ × ℕ => boundedOutputStage c p.1 p.2) := by
  have hbase : Primrec (fun p : ℕ × ℕ => (snapshotCodes c p.1 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      ((snapshotCodes_primrec c).comp (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep : Primrec₂ (fun (p : ℕ × ℕ) (z : ℕ × List BitString) =>
      (z.2 ++ snapshotCodes c p.1 (z.1 + 1)).eraseDups) :=
    eraseDups_bitstring_primrec.comp (Primrec.list_append.comp
      (Primrec.snd.comp Primrec.snd)
      ((snapshotCodes_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  rintro ⟨m, t⟩
  induction t with
  | zero => rfl
  | succ t ih => simp only [boundedOutputStage]; rw [← ih]

theorem boundedOutputStage_computable (c : Code) :
    Computable (fun p : ℕ × ℕ => boundedOutputStage c p.1 p.2) :=
  (boundedOutputStage_primrec c).to_comp

def suffixCountIncluding {α : Type*} [DecidableEq α] (L : List α) (x : α) : ℕ :=
  match L with
  | [] => 0
  | y :: ys => if y = x then L.length else suffixCountIncluding ys x

def tailAfter {α : Type*} [DecidableEq α] (L : List α) (x : α) : ℕ :=
  match L with
  | [] => 0
  | y :: ys => if y = x then ys.length else tailAfter ys x

@[simp] theorem suffixCountIncluding_nil {α : Type*} [DecidableEq α] (x : α) :
    suffixCountIncluding [] x = 0 := rfl

@[simp] theorem tailAfter_nil {α : Type*} [DecidableEq α] (x : α) :
    tailAfter [] x = 0 := rfl

theorem suffixCountIncluding_eq_zero_of_not_mem {α : Type*} [DecidableEq α]
    {L : List α} {x : α} (hx : x ∉ L) :
    suffixCountIncluding L x = 0 := by
  induction L with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.mem_cons, not_or] at hx
    unfold suffixCountIncluding
    dsimp
    split_ifs with h_eq
    · exact False.elim (hx.1 (Eq.symm h_eq))
    · exact ih hx.2

theorem suffixCountIncluding_eq_tailAfter_add_one {α : Type*} [DecidableEq α]
    {L : List α} {x : α} (hx : x ∈ L) :
    suffixCountIncluding L x = tailAfter L x + 1 := by
  induction L with
  | nil => cases hx
  | cons y ys ih =>
    unfold suffixCountIncluding tailAfter
    dsimp
    split_ifs with hxy
    · rfl
    · simp only [List.mem_cons] at hx
      have hxy' : x ∈ ys := hx.resolve_left (Ne.symm hxy)
      exact ih hxy'

theorem suffixCountIncluding_append_of_mem
    {α : Type*} [DecidableEq α]
    {L R : List α} {x : α} (hx : x ∈ L) :
    suffixCountIncluding (L ++ R) x =
      suffixCountIncluding L x + R.length := by
  induction L with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    unfold suffixCountIncluding
    simp only [List.cons_append]
    split_ifs with hxy
    · simp [hxy]; ring
    · exact ih (List.mem_cons.mp hx |> Or.resolve_left <| Ne.symm hxy)

theorem suffixCountIncluding_pos_iff_mem
    {α : Type*} [DecidableEq α]
    {L : List α} {x : α} :
    0 < suffixCountIncluding L x ↔ x ∈ L := by
  by_cases hx : x ∈ L
  · exact ⟨fun _ => hx,
      fun _ => suffixCountIncluding_eq_tailAfter_add_one hx ▸ Nat.succ_pos _⟩
  · exact ⟨fun h => False.elim
      (h.ne' ((suffixCountIncluding_eq_zero_of_not_mem hx).symm ▸ rfl)),
      fun h => False.elim (hx h)⟩

theorem tailAfter_append_singleton {α : Type*} [DecidableEq α]
    {L : List α} {x : α} (hx : x ∉ L) :
    tailAfter (L ++ [x]) x = 0 := by
  induction L with
  | nil =>
    unfold tailAfter
    dsimp
    split_ifs
    · rfl
    · rfl
  | cons y ys ih =>
    simp only [List.mem_cons, not_or] at hx
    unfold tailAfter
    dsimp
    split_ifs with h_eq
    · exact False.elim (hx.1 (Eq.symm h_eq))
    · exact ih hx.2

theorem snapshotCodes_mem_of_bound_le
    {c : Nat.Partrec.Code} {m m' t : ℕ} (hmm : m ≤ m')
    {x : BitString} (hx : x ∈ snapshotCodes c m t) :
    x ∈ snapshotCodes c m' t := by
  unfold snapshotCodes at hx ⊢
  simp only [List.mem_filterMap] at hx ⊢
  rcases hx with ⟨p, hp_mem, hp_run⟩
  refine ⟨p, ?_, hp_run⟩
  rw [mem_boundedPrograms_iff] at hp_mem ⊢
  exact le_trans hp_mem hmm

theorem boundedOutputStage_toFinset_eq_snapshotCodes
    (c : Nat.Partrec.Code) (m t : ℕ) :
    (boundedOutputStage c m t).toFinset = (snapshotCodes c m t).toFinset := by
  induction t with
  | zero =>
    dsimp [boundedOutputStage]
    ext x
    simp only [List.mem_toFinset, mem_eraseDups_bitString]
  | succ t ih =>
    dsimp [boundedOutputStage]
    ext x
    simp only [List.mem_toFinset, mem_eraseDups_bitString, List.mem_append]
    have ih_x : x ∈ boundedOutputStage c m t ↔ x ∈ snapshotCodes c m t := by
      have h_ext := Finset.ext_iff.mp ih x
      simpa only [List.mem_toFinset] using h_ext
    constructor
    · rintro (hx | hx)
      · exact snapshotCodes_mem_of_le (Nat.le_succ t) (ih_x.mp hx)
      · exact hx
    · intro hx
      exact Or.inr hx

theorem boundedOutputStage_mem_of_bound_le
    {c : Nat.Partrec.Code} {m m' t : ℕ} (hmm : m ≤ m')
    {x : BitString} (hx : x ∈ boundedOutputStage c m t) :
    x ∈ boundedOutputStage c m' t := by
  have h1 : x ∈ (boundedOutputStage c m t).toFinset := by simp [hx]
  rw [boundedOutputStage_toFinset_eq_snapshotCodes] at h1
  have h2 := snapshotCodes_mem_of_bound_le hmm (List.mem_toFinset.mp h1)
  have h3 : x ∈ (snapshotCodes c m' t).toFinset := List.mem_toFinset.mpr h2
  rw [← boundedOutputStage_toFinset_eq_snapshotCodes] at h3
  exact List.mem_toFinset.mp h3

open Classical in
noncomputable def maxHaltingStage (c : Code) (m : ℕ) : ℕ :=
  Nat.find (exists_max_countHalts c m)

open Classical in
theorem maxHaltingStage_spec (c : Code) (m : ℕ) :
    ∀ t, countHalts c m t ≤ countHalts c m (maxHaltingStage c m) :=
  Nat.find_spec (exists_max_countHalts c m)

noncomputable def completedBoundedOutput (c : Code) (m : ℕ) : List BitString :=
  boundedOutputStage c m (maxHaltingStage c m)

noncomputable def completedBoundedOutputFinset (c : Code) (m : ℕ) : Finset BitString :=
  (completedBoundedOutput c m).toFinset

open Classical in
noncomputable def boundedOutputCompletionTime (c : Code) (m : ℕ) : ℕ :=
  if h : ∃ t, (boundedOutputStage c m t).length = (completedBoundedOutput c m).length
  then Nat.find h
  else 0

open Classical in
theorem boundedOutputCompletionTime_spec (c : Code) (m : ℕ) :
    (boundedOutputStage c m (boundedOutputCompletionTime c m)).length =
      (completedBoundedOutput c m).length := by
  let hex : ∃ t, (boundedOutputStage c m t).length =
      (completedBoundedOutput c m).length :=
    ⟨maxHaltingStage c m, rfl⟩
  unfold boundedOutputCompletionTime
  rw [dif_pos hex]
  exact Nat.find_spec hex

open Classical in
theorem boundedOutputCompletionTime_le_complete_stage (c : Code) (m t : ℕ)
    (ht : (boundedOutputStage c m t).length = (completedBoundedOutput c m).length) :
    boundedOutputCompletionTime c m ≤ t := by
  unfold boundedOutputCompletionTime
  split_ifs with h
  · exact Nat.find_min' h ht
  · exact False.elim (h ⟨t, ht⟩)

theorem boundedOutputStage_eq_completed_at_completion (c : Code) (m : ℕ) :
    boundedOutputStage c m (boundedOutputCompletionTime c m) =
      completedBoundedOutput c m := by
  have hlen :
      (boundedOutputStage c m (boundedOutputCompletionTime c m)).length =
        (completedBoundedOutput c m).length :=
    boundedOutputCompletionTime_spec c m
  have hle :
      boundedOutputCompletionTime c m ≤ maxHaltingStage c m :=
    boundedOutputCompletionTime_le_complete_stage c m (maxHaltingStage c m) rfl
  have hprefix := boundedOutputStage_prefix_of_le c m hle
  unfold completedBoundedOutput at hlen ⊢
  exact hprefix.eq_of_length hlen

theorem snapshotCodes_toFinset_eq_of_countHalts_max
    (c : Code) (m T t : ℕ) (hTt : T ≤ t)
    (hmax : ∀ t', countHalts c m t' ≤ countHalts c m T) :
    (snapshotCodes c m t).toFinset = (snapshotCodes c m T).toFinset := by
  ext w
  simp only [List.mem_toFinset]
  constructor
  · intro hw
    unfold snapshotCodes at hw ⊢
    rw [List.mem_filterMap] at hw ⊢
    obtain ⟨p, hp, hwrun⟩ := hw
    refine ⟨p, hp, ?_⟩
    unfold runOut at hwrun ⊢
    rw [Option.bind_eq_some_iff] at hwrun ⊢
    obtain ⟨a, ha_t, ha_decode⟩ := hwrun
    have hp_t : haltsWithin c t p = true := by
      unfold haltsWithin
      exact Option.isSome_iff_exists.mpr ⟨a, ha_t⟩
    have hp_T : haltsWithin c T p = true := by
      by_contra hp_not
      rw [Bool.not_eq_true] at hp_not
      have hlt : countHalts c m T < countHalts c m t := by
        unfold countHalts
        exact countP_lt_of_witness hp hp_not hp_t
          (fun q _ hq => haltsWithin_mono c hTt q hq)
      exact (not_lt_of_ge (hmax t)) hlt
    obtain ⟨aT, ha_T⟩ := Option.isSome_iff_exists.mp hp_T
    have haT_t := Nat.Partrec.Code.evaln_mono hTt ha_T
    have ha_eq : aT = a := Option.some.inj (haT_t.symm.trans ha_t)
    subst aT
    exact ⟨a, ha_T, ha_decode⟩
  · exact snapshotCodes_mem_of_le hTt

theorem boundedOutputStage_eq_completed_of_completion_le (c : Code) (m t : ℕ)
    (hle : boundedOutputCompletionTime c m ≤ t) :
    boundedOutputStage c m t = completedBoundedOutput c m := by
  by_cases ht : t ≤ maxHaltingStage c m
  · have hprefix :
        boundedOutputStage c m (boundedOutputCompletionTime c m) <+:
          boundedOutputStage c m t :=
      boundedOutputStage_prefix_of_le c m hle
    have hcompletion :=
      boundedOutputStage_eq_completed_at_completion c m
    have htmax : boundedOutputStage c m t <+:
        boundedOutputStage c m (maxHaltingStage c m) :=
      boundedOutputStage_prefix_of_le c m ht
    unfold completedBoundedOutput at hcompletion ⊢
    rw [hcompletion] at hprefix
    have hlen :
        (boundedOutputStage c m t).length =
          (boundedOutputStage c m (maxHaltingStage c m)).length :=
      Nat.le_antisymm htmax.length_le hprefix.length_le
    exact htmax.eq_of_length hlen
  · have hmax_t : maxHaltingStage c m ≤ t := Nat.le_of_not_ge ht
    have hprefix :
        boundedOutputStage c m (maxHaltingStage c m) <+:
          boundedOutputStage c m t :=
      boundedOutputStage_prefix_of_le c m hmax_t
    have hset :
        (boundedOutputStage c m t).toFinset =
          (boundedOutputStage c m (maxHaltingStage c m)).toFinset := by
      rw [boundedOutputStage_toFinset_eq_snapshotCodes,
        boundedOutputStage_toFinset_eq_snapshotCodes]
      exact snapshotCodes_toFinset_eq_of_countHalts_max c m
        (maxHaltingStage c m) t hmax_t (maxHaltingStage_spec c m)
    have hlen :
        (boundedOutputStage c m (maxHaltingStage c m)).length =
          (boundedOutputStage c m t).length := by
      calc
        (boundedOutputStage c m (maxHaltingStage c m)).length =
            (boundedOutputStage c m (maxHaltingStage c m)).toFinset.card :=
          (List.toFinset_card_of_nodup
            (boundedOutputStage_nodup c m (maxHaltingStage c m))).symm
        _ = (boundedOutputStage c m t).toFinset.card :=
          congrArg Finset.card hset.symm
        _ = (boundedOutputStage c m t).length :=
          List.toFinset_card_of_nodup (boundedOutputStage_nodup c m t)
    exact (hprefix.eq_of_length hlen).symm

/- Every finite stage is an initial segment of the completed first-appearance
list.  Before the least completion time this is time monotonicity; at and after
that time it follows from stabilization. -/
theorem boundedOutputStage_prefix_completed (c : Code) (m t : ℕ) :
    boundedOutputStage c m t <+: completedBoundedOutput c m := by
  by_cases ht : t ≤ boundedOutputCompletionTime c m
  · have hprefix :=
      boundedOutputStage_prefix_of_le c m ht
    rwa [boundedOutputStage_eq_completed_at_completion] at hprefix
  · have hdone : boundedOutputCompletionTime c m ≤ t :=
      Nat.le_of_not_ge ht
    rw [boundedOutputStage_eq_completed_of_completion_le c m t hdone]

theorem boundedOutputStage_toFinset_subset_completed (c : Code) (m t : ℕ) :
    (boundedOutputStage c m t).toFinset ⊆ completedBoundedOutputFinset c m := by
  intro x hx
  rw [List.mem_toFinset] at hx
  rw [completedBoundedOutputFinset, List.mem_toFinset]
  exact (boundedOutputStage_prefix_completed c m t).sublist.subset hx

theorem mem_completedBoundedOutput_iff_plainK_le
    {V : Map} {c : Nat.Partrec.Code} (hc : IsCodeFor c V)
    (m : ℕ) (x : BitString) :
    x ∈ completedBoundedOutput c m ↔ plainK V x ≤ (m : ENat) := by
  constructor
  · intro hx
    have hx_snapshot : x ∈ snapshotCodes c m (maxHaltingStage c m) := by
      have hx_finset : x ∈ (completedBoundedOutput c m).toFinset :=
        List.mem_toFinset.mpr hx
      unfold completedBoundedOutput at hx_finset
      rw [boundedOutputStage_toFinset_eq_snapshotCodes] at hx_finset
      exact List.mem_toFinset.mp hx_finset
    unfold snapshotCodes at hx_snapshot
    rw [List.mem_filterMap] at hx_snapshot
    obtain ⟨p, hp_bound, hp_run⟩ := hx_snapshot
    exact (condKLeIff V x [] m).mpr
      ⟨p, (mem_boundedPrograms_iff p m).mp hp_bound, runOut_sound hc hp_run⟩
  · intro hx
    obtain ⟨p, hp_length, hp_produces⟩ := (condKLeIff V x [] m).mp hx
    have hp_bound : p ∈ boundedPrograms m :=
      (mem_boundedPrograms_iff p m).mpr hp_length
    have hx_snapshot : x ∈ snapshotCodes c m (maxHaltingStage c m) :=
      code_mem_snapshot_of_max hc m (maxHaltingStage c m)
        (maxHaltingStage_spec c m) hp_bound hp_produces
    have hx_finset : x ∈ (completedBoundedOutput c m).toFinset := by
      unfold completedBoundedOutput
      rw [boundedOutputStage_toFinset_eq_snapshotCodes]
      exact List.mem_toFinset.mpr hx_snapshot
    exact List.mem_toFinset.mp hx_finset

end Kolmogorov
