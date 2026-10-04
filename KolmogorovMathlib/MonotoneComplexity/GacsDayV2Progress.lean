import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Replay
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFibre

/-!
# V2 global progress — the son-base multiplicity bound (Reading C)

The one genuinely-new derivation of the wide-block progress argument: an
accepted block round's son increment `grayTailSonBase` for a fibre `(i, c)` is
the SUM over that fibre's `mult(r)` grandson roots, each requesting at
`dyadicScale ε_r`; the sum is bounded by `mult(r) · dyadicScale ε_r =
dyadicScale (grayCallDepth q e)` (the mass-recovery bridge).  This restores
the flattened controller's per-round son bound verbatim, so every downstream
progress lemma of `GacsDayChargedTailGlobalProgress` transfers.
-/

namespace Kolmogorov

/-- Sum of a list of guarded constants equals the constant times the count. -/
lemma sum_map_ite_eq_countP {α : Type _} (l : List α) (p : α → Prop)
    [DecidablePred p] (cst : ℚ) :
    (l.map fun x => if p x then cst else 0).sum = cst * (l.countP fun x => decide (p x)) := by
  induction l with
  | nil => simp
  | cons x t ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases hx : p x
      · simp [hx]; ring
      · simp [hx]

/-- A matching slot of the wide next-slots has its grandson in the block. -/
lemma grayBlockNextSlots_grandson_mem {n b : ℕ}
    {q L e used round : ℕ} {threshold : ℚ} {A : Allocation}
    {frozen : GrayTailFrozen n b} {sm : FamilyServerMove}
    {sl : GrayTailSlot n b}
    (hsl : sl ∈ grayBlockNextSlots q L e used round threshold A frozen sm) :
    sl.2.2 ∈ grayAdvBlockGrandsons b q L round := by
  rw [grayBlockNextSlots, List.mem_flatMap] at hsl
  obtain ⟨i, -, hsl⟩ := hsl
  rw [List.mem_flatMap] at hsl
  obtain ⟨c, -, hsl⟩ := hsl
  rw [List.mem_map] at hsl
  obtain ⟨g, hg, rfl⟩ := hsl
  exact hg

/-- The matching-fibre positions of the wide next-slots inject (via grandson)
into the nodup grandson block, hence number at most `mult(r)`. -/
lemma grayBlockNextSlots_fibre_count_le {n b : ℕ}
    (q L e used round : ℕ) (threshold : ℚ) (A : Allocation)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) (i : Fin n) (c : Fin b) :
    ((grayBlockNextSlots q L e used round threshold A frozen sm).filter
      fun s => decide (s.1 = i ∧ s.2.1 = c)).length ≤ grayAdvBlockMult q L round := by
  set slots := grayBlockNextSlots q L e used round threshold A frozen sm with hslots
  set matching := slots.filter fun s => decide (s.1 = i ∧ s.2.1 = c) with hmatch
  have hnodup_slots : slots.Nodup := grayBlockNextSlots_nodup _ _ _ _ _ _ _ _ _
  have hnodup_match : matching.Nodup := hnodup_slots.filter _
  -- the grandson map on matching is injective (matching share i,c)
  have hgs_nodup : (matching.map fun s => s.2.2).Nodup := by
    rw [List.nodup_map_iff_inj_on]
    · intro s hs s' hs' heq
      have hsm := List.mem_filter.mp hs
      have hsm' := List.mem_filter.mp hs'
      have hi : s.1 = i ∧ s.2.1 = c := by
        simpa using (of_decide_eq_true hsm.2)
      have hi' : s'.1 = i ∧ s'.2.1 = c := by
        simpa using (of_decide_eq_true hsm'.2)
      obtain ⟨s1, s2, s3⟩ := s
      obtain ⟨s1', s2', s3'⟩ := s'
      simp only at heq hi hi'
      obtain ⟨hi1, hi2⟩ := hi
      obtain ⟨hi1', hi2'⟩ := hi'
      subst hi1; subst hi2; subst hi1'; subst hi2'; subst heq
      rfl
    · exact hnodup_match
  -- the grandsons of matching slots lie in the block
  have hgs_sub : (matching.map fun s => s.2.2) ⊆ grayAdvBlockGrandsons b q L round := by
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨s, hs, rfl⟩ := hg
    have := List.mem_filter.mp hs
    exact grayBlockNextSlots_grandson_mem this.1
  calc matching.length = (matching.map fun s => s.2.2).length := by rw [List.length_map]
    _ ≤ (grayAdvBlockGrandsons b q L round).length :=
        (List.subperm_of_subset hgs_nodup hgs_sub).length_le
    _ ≤ grayAdvBlockMult q L round := by
        rw [grayAdvBlockGrandsons, List.length_take, List.length_drop]
        exact Nat.min_le_left _ _

/-- **The son-base multiplicity keystone** (Reading C): an accepted wide-block
round's son increment for a fibre `(i, c)` is at most `dyadicScale
(grayCallDepth q e)` — the flattened controller's per-round son bound,
recovered as the block sum `≤ mult(r) · dyadicScale ε_r`. -/
lemma grayChargedBlockRoundSonBase_le_callScale {n b q L e r : Nat}
    {A : Allocation} {slots : List (GrayTailSlot n b)}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hgoal : grayChargedBlockGoalAtB q L e r slots.length A move server = true)
    (hcount : ∀ (i : Fin n) (c : Fin b),
      (slots.filter fun s => decide (s.1 = i ∧ s.2.1 = c)).length ≤
        grayAdvBlockMult q L r)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries slots move) i c ≤
      dyadicScale (grayCallDepth q e) := by
  set α := dyadicScale (grayTailRoundEps q L e r) with hα
  have hαnn : (0:ℚ) ≤ α := (dyadicScale_pos _).le
  set es := grayTailSlotEntries slots move with hes
  -- son-base = (es.map (guarded req)).sum
  rw [grayTailSonBase_eq_sum_map]
  -- pointwise bound by the guarded constant α
  have hle : (es.map fun q => if q.1.1 = i ∧ q.1.2.1 = c then getReq q.2 [] else 0).sum ≤
      (es.map fun q => if q.1.1 = i ∧ q.1.2.1 = c then α else 0).sum := by
    apply List.sum_le_sum
    intro q hq
    by_cases hm : q.1.1 = i ∧ q.1.2.1 = c
    · simp only [ite_eq_left hm]
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hq
      rw [← hj]
      exact (grayChargedBlockGoalAtB_root_bounds hgoal j).2
    · simp [ite_eq_right hm]
  refine le_trans hle ?_
  -- the guarded-constant sum = α · countP
  rw [sum_map_ite_eq_countP es (fun q => q.1.1 = i ∧ q.1.2.1 = c) α]
  -- countP over es = countP over slots (= filter length) ≤ mult(r)
  have hmapfst : es.map Prod.fst = slots := by
    rw [hes, grayTailSlotEntries, List.map_ofFn]
    exact List.ofFn_get slots
  have hcountP : (es.countP fun q => decide (q.1.1 = i ∧ q.1.2.1 = c)) =
      (slots.filter fun sl => decide (sl.1 = i ∧ sl.2.1 = c)).length := by
    have : (es.countP fun q => decide (q.1.1 = i ∧ q.1.2.1 = c)) =
        (es.map Prod.fst).countP fun sl => decide (sl.1 = i ∧ sl.2.1 = c) := by
      rw [List.countP_map]; rfl
    rw [this, hmapfst, List.countP_eq_length_filter]
  rw [hcountP]
  -- α · count ≤ α · mult(r) = dyadicScale callDepth
  have hcnt := hcount i c
  calc α * ((slots.filter fun sl => decide (sl.1 = i ∧ sl.2.1 = c)).length : ℚ)
      ≤ α * (grayAdvBlockMult q L r : ℚ) := by
        apply mul_le_mul_of_nonneg_left ?_ hαnn
        exact_mod_cast hcnt
    _ = dyadicScale (grayCallDepth q e) := by
        rw [hα, mul_comm]
        exact grayAdvBlock_fibre_mass q L e r

/-- **Shape-based fibre count**: if the slots are nodup with grandsons in
round `r`'s block range, then each fibre `(i, c)` has at most `mult(r)`
matching slots (distinct grandsons in a range of size `mult(r)`). -/
lemma grayInAdvBlock_fibre_count_le {n b q L r : Nat}
    {slots : List (GrayTailSlot n b)}
    (hnodup : slots.Nodup)
    (hrange : ∀ s ∈ slots, grayInAdvBlock q L r s.2.2.val)
    (i : Fin n) (c : Fin b) :
    (slots.filter fun s => decide (s.1 = i ∧ s.2.1 = c)).length ≤
      grayAdvBlockMult q L r := by
  set matching := slots.filter fun s => decide (s.1 = i ∧ s.2.1 = c) with hm
  have hmnodup : matching.Nodup := hnodup.filter _
  -- grandson vals of matching slots are nodup
  have hvals_nodup : (matching.map fun s => s.2.2.val).Nodup := by
    rw [List.nodup_map_iff_inj_on]
    · intro s hs s' hs' heq
      have h1 := of_decide_eq_true (List.mem_filter.mp hs).2
      have h2 := of_decide_eq_true (List.mem_filter.mp hs').2
      obtain ⟨s1, s2, s3⟩ := s; obtain ⟨s1', s2', s3'⟩ := s'
      simp only at heq h1 h2
      obtain ⟨e1, e2⟩ := h1; obtain ⟨e1', e2'⟩ := h2
      subst e1; subst e2; subst e1'; subst e2'
      have : s3 = s3' := Fin.val_injective heq
      subst this; rfl
    · exact hmnodup
  -- grandson vals lie in Ico offset (offset+mult)
  have hsub : ∀ v ∈ (matching.map fun s => s.2.2.val),
      v ∈ Finset.Ico (grayAdvBlockOffset q L r)
        (grayAdvBlockOffset q L r + grayAdvBlockMult q L r) := by
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨s, hs, rfl⟩ := hv
    have hin := hrange s (List.mem_of_mem_filter hs)
    rw [Finset.mem_Ico]
    exact ⟨hin.1, hin.2⟩
  calc matching.length = (matching.map fun s => s.2.2.val).length := by
        rw [List.length_map]
    _ = (matching.map fun s => s.2.2.val).toFinset.card := by
        rw [List.toFinset_card_of_nodup hvals_nodup]
    _ ≤ (Finset.Ico (grayAdvBlockOffset q L r)
          (grayAdvBlockOffset q L r + grayAdvBlockMult q L r)).card := by
        apply Finset.card_le_card
        intro v hv
        exact hsub v (List.mem_toFinset.mp hv)
    _ = grayAdvBlockMult q L r := by rw [Nat.card_Ico]; omega

/-! ## The base / width invariant chain (mirrors GacsDayChargedTailGlobalProgress) -/

/-- A block tail step keeps every open slot below the service threshold. -/
lemma grayChargedBlockTail_active_base_le_step
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (st : GrayTailState n b) (sm : FamilyServerMove)
    (hprev : forall s, s ∈ st.slots ->
      grayTailFrozenSonBase st.frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q)) :
    forall s, s ∈ (grayChargedBlockTailStep q L a e sigma A st sm).slots ->
      grayTailFrozenSonBase
          (grayChargedBlockTailStep q L a e sigma A st sm).frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
  unfold grayChargedBlockTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, ite_false]
  split
  · exact hprev
  · split
    · exact hprev
    · split
      · intro s hs
        exact grayBlockNextSlots_base_le_global hs
      · exact hprev

/-- At every time of a block tail run, every open slot is below the service threshold. -/
theorem grayChargedBlockTail_active_base_le_stateAt
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    forall s, s ∈ (grayChargedBlockTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).slots ->
      grayTailFrozenSonBase
          (grayChargedBlockTailStateAt (n := n) (b := b)
            q L a e sigma A sm t).frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
  induction t with
  | zero =>
      intro s hs
      simpa [grayChargedBlockTailStateAt, grayChargedBlockTailFold,
        grayChargedBlockTailInitialState, grayTailFrozenSonBase,
        grayTailFrozenEntries, grayTailSonBase] using
        grayTail_threshold_nonneg_global q e
  | succ t ih =>
      rw [grayChargedBlockTailStateAt_succ]
      exact grayChargedBlockTail_active_base_le_step q L a e sigma A _ (sm t) ih

/-- A block tail step keeps every frozen son base below `dyadicScale e`. -/
lemma grayChargedBlockTail_all_frozen_base_le_step
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (st : GrayTailState n b) (sm : FamilyServerMove)
    (hshape : GrayBlockTailShape q L st)
    (hprev : forall (i : Fin n) (c : Fin b),
      grayTailFrozenSonBase st.frozen i c <= dyadicScale e)
    (hactive : forall s, s ∈ st.slots ->
      grayTailFrozenSonBase st.frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q)) :
    forall (i : Fin n) (c : Fin b),
      grayTailFrozenSonBase
        (grayChargedBlockTailStep q L a e sigma A st sm).frozen i c <=
          dyadicScale e := by
  unfold grayChargedBlockTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, ite_false]
  split
  · exact hprev
  · split
    · exact hprev
    · split
      · rename_i hgoal
        intro i c
        rw [grayTailFrozenSonBase_append_global]
        by_cases hson : GrayTailHasKey st.slots i c
        · obtain ⟨s, hs, hi, hc⟩ := hson
          have hold : grayTailFrozenSonBase st.frozen i c <=
              dyadicScale e - dyadicScale e /
                (6 * halfAmplification q) := by
            simpa [hi, hc] using hactive s hs
          have hnew := grayChargedBlockRoundSonBase_le_callScale
            (n := n) (b := b) (q := q) (L := L) (e := e)
            (r := st.frozen.length) (A := st.unavailable)
            (slots := st.slots) (move := grayBlockCurrentMove q L e sigma st)
            (server := grayTailLocalServerMove
              (grayTailRoundDelta q L e st.frozen.length) st.slots sm)
            hgoal
            (fun i c => grayInAdvBlock_fibre_count_le hshape.slots_nodup
              hshape.slots_range i c) i c
          exact le_trans (add_le_add hold hnew)
            (grayTail_callScale_add_threshold_le q e)
        · rw [grayTailSonBase_eq_zero_of_not_hasKey i c hson, add_zero]
          exact hprev i c
      · exact hprev

/-- At every time of a block tail run, every frozen son base is at most `dyadicScale e`. -/
theorem grayChargedBlockTail_all_frozen_base_le_stateAt
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    forall (i : Fin n) (c : Fin b),
      grayTailFrozenSonBase
        (grayChargedBlockTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen i c <= dyadicScale e := by
  induction t with
  | zero =>
      intro i c
      simp [grayChargedBlockTailStateAt, grayChargedBlockTailFold,
        grayChargedBlockTailInitialState, grayTailFrozenSonBase,
        grayTailFrozenEntries, grayTailSonBase, (dyadicScale_pos e).le]
  | succ t ih =>
      rw [grayChargedBlockTailStateAt_succ]
      apply grayChargedBlockTail_all_frozen_base_le_step q L a e sigma A _ (sm t)
        (grayChargedBlockTailCertified_stateAt q L a e sigma A sm t).shape ih
      exact grayChargedBlockTail_active_base_le_stateAt q L a e sigma A sm t

/-! ## The block-length relation (record-agnostic): slots = fibres · mult -/

private lemma list_sum_map_const {α : Type _} (l : List α) (k : Nat) :
    (l.map fun _ => k).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons x t ih => simp; ring

private lemma list_sum_map_mul_const {α : Type _} (l : List α) (g : α → Nat) (k : Nat) :
    (l.map fun x => g x * k).sum = (l.map g).sum * k := by
  induction l with
  | nil => simp
  | cons x t ih => simp [ih]; ring

/-- **The wide block factors as narrow-fibres × grandson block** (when the
round index fits): `|grayBlockNextSlots| = |grayTailNextSlots| · |grandsons|`. -/
lemma grayBlockNextSlots_length {n b : ℕ}
    (q L e used round : ℕ) (threshold : ℚ) (A : Allocation)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) (hr : round < b) :
    (grayBlockNextSlots q L e used round threshold A frozen sm).length =
      (grayTailNextSlots e used round threshold A frozen sm).length *
        (grayAdvBlockGrandsons b q L round).length := by
  unfold grayBlockNextSlots grayTailNextSlots
  rw [dite_eq_left hr]
  simp only [List.length_flatMap, List.length_map, list_sum_map_const]
  rw [list_sum_map_mul_const]

/-- **The fibre-count width bridge**: when the fibre quarter has NOT fired
(`¬ grayTailGlobalQuarterB` on the narrow fibres) and the grandson block is
nonempty, the WIDE slot count satisfies `n·source·mult < 4·|slots|` — the
`mult`-scaled width the frozen-tail contradiction needs (recovering the
call-depth magnitude per round via the mass bridge). -/
lemma grayBlockNextSlots_fibre_width {n b : ℕ}
    (q L e used round : ℕ) (threshold : ℚ) (A : Allocation)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) (hr : round < b)
    (hG : 0 < (grayAdvBlockGrandsons b q L round).length)
    (hnq : grayTailGlobalQuarterB used
      (grayTailNextSlots e used round threshold A frozen sm) = false) :
    n * used * (grayAdvBlockGrandsons b q L round).length <
      4 * (grayBlockNextSlots q L e used round threshold A frozen sm).length := by
  rw [grayBlockNextSlots_length q L e used round threshold A frozen sm hr]
  have hnq' : n * used <
      4 * (grayTailNextSlots e used round threshold A frozen sm).length := by
    unfold grayTailGlobalQuarterB at hnq
    rw [decide_eq_false_iff_not, not_le] at hnq
    exact hnq
  set N := (grayTailNextSlots e used round threshold A frozen sm).length
  set G := (grayAdvBlockGrandsons b q L round).length
  calc n * used * G < 4 * N * G := by
        exact Nat.mul_lt_mul_of_lt_of_le hnq' (le_refl G) hG
    _ = 4 * (N * G) := by ring

end Kolmogorov
