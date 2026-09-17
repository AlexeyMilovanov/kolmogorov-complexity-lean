import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafC

/-!
# Leaf D of the tail frontier: the bookkeeping lemmas

This module collects the arithmetic bookkeeping of one real controller history
of the tail frontier: the displayed root request of the terminal move
(`grayTail_root_request_eq_raised_sum`), the per-son slack and payment bounds
(`grayTail_raisedSon_le_add_slack`, `grayTail_inactive_son_paid`,
`grayTail_raisedSum_le_add_sourceSlack`), the round-sum identities
(`grayTail_listSum_eq_sum_range_getD`, `grayTail_ownerCharge_sum_eq`,
`grayTail_ownerCharge_sum_le_lastCap`) and the terminal source gain
(`grayTail_terminal_source_gain`).

The accumulated request is decomposed into per-round increments by
`grayTail_frozenSonBase_eq_sum_rounds` (in `GacsDayLadderTailFibre`), and the
sum of per-round positive parts must be retained: collapsing the rounds first
is refuted by `not_aggregatedGrayTailFloorBound`.

The active Gacs-Day recursion uses `GacsDayChargedClosureLeaves`.
-/

namespace Kolmogorov

open scoped BigOperators

/-! ### D2: the displayed root request -/

/-- **Child D2 (proved).**  The displayed root request of the terminal move is
the sum of the *raised* accumulated son requests, lifted to the terminal
floor. -/
theorem grayTail_root_request_eq_raised_sum
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hdata : GrayTailTerminalData q L a e n sigma A sm T) (i : Fin n) :
    getFamilyReq (grayTailRunMove q L a e n sigma A sm T) i.val [] =
      max (∑ c : Fin (grayTailBranch q L a e),
            (if grayTailThreshold q e <
                grayTailFrozenSonBase
                  (grayTailRunState q L a e n sigma A sm T).frozen i c
              then dyadicScale e
              else grayTailFrozenSonBase
                (grayTailRunState q L a e n sigma A sm T).frozen i c))
        (grayTailTargetFloor q a) := by
  rw [hdata.root_request_eq i]
  congr 1
  exact Finset.sum_congr rfl fun c _ => hdata.son_request_eq i c

/-! ### D3: the coupled inequality on a feasible history -/

/-- Raising one accumulated son request at the tail threshold costs at most the
threshold slack. -/
lemma grayTail_raisedSon_le_add_slack
    (q e : ℕ) (x : ℚ) :
    (if grayTailThreshold q e < x then dyadicScale e else x) ≤
      x + dyadicScale e / (6 * halfAmplification q) := by
  have hslack : 0 ≤ dyadicScale e / (6 * halfAmplification q) := by
    exact div_nonneg (dyadicScale_pos e).le
      (mul_nonneg (by norm_num) (halfAmplification_pos q).le)
  split_ifs with h
  · change dyadicScale e - dyadicScale e / (6 * halfAmplification q) < x at h
    linarith
  · linarith

/-- One selected inactive source son is paid for by its full epsilon reserve.
The same reserve absorbs both threshold raising and twice the increment of the
son's owner round.  This is the sharp local estimate used before any sums are
regrouped by roots or rounds. -/
lemma grayTail_inactive_son_paid
    (q e : ℕ) (gamma owner : ℚ)
    (hgamma_cap : gamma ≤ dyadicScale e)
    (howner_cap : owner ≤
      dyadicScale e / (12 * halfAmplification q)) :
    (halfAmplification q + 1 / 2) *
        (if grayTailThreshold q e < gamma then dyadicScale e else gamma) +
      halfAmplification q * (2 * owner) ≤
        halfAmplification q * gamma + dyadicScale e := by
  let kappa : ℚ := halfAmplification q
  let eps : ℚ := dyadicScale e
  have hkappa : 0 < kappa := by
    simpa only [kappa] using halfAmplification_pos q
  have heps : 0 < eps := by
    simpa only [eps] using dyadicScale_pos e
  have howner_scaled : 2 * kappa * owner ≤ eps / 6 := by
    calc
      2 * kappa * owner ≤
          (2 * kappa) * (eps / (12 * kappa)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [kappa, eps] using howner_cap)
          (mul_nonneg (by norm_num) hkappa.le)
      _ = eps / 6 := by
        field_simp [ne_of_gt hkappa]
        ring
  split_ifs with hraised
  · have hgap : kappa * (eps - gamma) < eps / 6 := by
      have hdiff : eps - gamma < eps / (6 * kappa) := by
        change eps - eps / (6 * kappa) < gamma at hraised
        linarith
      calc
        kappa * (eps - gamma) < kappa * (eps / (6 * kappa)) :=
          mul_lt_mul_of_pos_left hdiff hkappa
        _ = eps / 6 := by
          field_simp [ne_of_gt hkappa]
    change (kappa + 1 / 2) * eps + kappa * (2 * owner) ≤
      kappa * gamma + eps
    nlinarith
  · change (kappa + 1 / 2) * gamma + kappa * (2 * owner) ≤
      kappa * gamma + eps
    nlinarith

/-- Summing the scalar threshold estimate over the supported source sons costs
at most `used` copies of the threshold slack. -/
lemma grayTail_raisedSum_le_add_sourceSlack
    (q e b used : ℕ) (x : Fin b → ℚ)
    (hzero : ∀ c, ¬ c.val < used → x c = 0) :
    (∑ c, if grayTailThreshold q e < x c then dyadicScale e else x c) ≤
      (∑ c, x c) +
        (used : ℚ) * (dyadicScale e / (6 * halfAmplification q)) := by
  classical
  let S : Finset (Fin b) := Finset.univ.filter fun c => c.val < used
  let slack : ℚ := dyadicScale e / (6 * halfAmplification q)
  have hthreshold : 0 ≤ grayTailThreshold q e :=
    grayTail_threshold_nonneg_global q e
  have hslack : 0 ≤ slack := by
    exact div_nonneg (dyadicScale_pos e).le
      (mul_nonneg (by norm_num) (halfAmplification_pos q).le)
  have hpoint : ∀ c : Fin b,
      (if grayTailThreshold q e < x c then dyadicScale e else x c) ≤
        x c + if c.val < used then slack else 0 := by
    intro c
    by_cases hc : c.val < used
    · simpa [hc, slack] using grayTail_raisedSon_le_add_slack q e (x c)
    · rw [hzero c hc]
      simp [hc, not_lt_of_ge hthreshold]
  have hcard : (S.card : ℚ) ≤ (used : ℚ) := by
    change ((Finset.univ.filter fun c : Fin b => c.val < used).card : ℚ) ≤ used
    exact_mod_cast grayTail_source_fin_card_le b used
  have hcardSlack : (S.card : ℚ) * slack ≤ (used : ℚ) * slack :=
    mul_le_mul_of_nonneg_right hcard hslack
  calc
    (∑ c, if grayTailThreshold q e < x c then dyadicScale e else x c) ≤
        ∑ c, (x c + if c.val < used then slack else 0) := by
      exact Finset.sum_le_sum fun c _ => hpoint c
    _ = (∑ c, x c) + (S.card : ℚ) * slack := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_filter]
      simp [S]
    _ ≤ (∑ c, x c) + (used : ℚ) * slack := by
      linarith
    _ = (∑ c, x c) +
        (used : ℚ) * (dyadicScale e / (6 * halfAmplification q)) := rfl


/-- Reindex a mapped list sum by the natural positions used by `List.getD`. -/
lemma grayTail_listSum_eq_sum_range_getD
    {α : Type*} [Inhabited α] (l : List α) (f : α → ℚ) :
    (l.map f).sum = ∑ k ∈ Finset.range l.length, f (l.getD k default) := by
  calc
    (l.map f).sum = ∑ i : Fin l.length, f l[i.val] := by
      rw [← List.ofFn_getElem_eq_map l f, List.sum_ofFn]
    _ = ∑ i : Fin l.length, f (l.getD i.val default) := by
      exact Finset.sum_congr rfl fun i _ => by
        rw [List.getD_eq_getElem l default i.isLt]
    _ = ∑ k ∈ Finset.range l.length, f (l.getD k default) :=
      Fin.sum_univ_eq_sum_range (fun k => f (l.getD k default)) l.length

/-- Chronological owner charges regroup exactly into twice the owner-round
increment of every selected inactive son.  The coefficient `2` is retained
explicitly; this is the bookkeeping identity needed before applying the
per-call cap. -/
lemma grayTail_ownerCharge_sum_eq
    {n b : ℕ} (frozen : GrayTailFrozen n b) (slots : List (GrayTailSlot n b))
    (used : ℕ) (I : List ℕ)
    (hchron : ∀ k, k < frozen.length → (frozen.getD k default).roundIndex = k)
    (howner : ∀ z ∈ grayTailSelectedInactive slots used I,
      grayTailOwnerIndex frozen z.1 z.2 < frozen.length) :
    (frozen.map fun p =>
        grayTailOwnerCharge frozen slots used I p.roundIndex).sum =
      2 * ∑ z ∈ grayTailSelectedInactive slots used I,
        grayTailSonBase
          (grayTailSlotEntries
            (frozen.getD (grayTailOwnerIndex frozen z.1 z.2) default).slots
            (frozen.getD (grayTailOwnerIndex frozen z.1 z.2) default).move)
          z.1 z.2 := by
  classical
  let S := grayTailSelectedInactive slots used I
  let owner : Fin n × Fin b → ℕ := fun z => grayTailOwnerIndex frozen z.1 z.2
  let x : Fin n × Fin b → ℚ := fun z =>
    grayTailSonBase
      (grayTailSlotEntries (frozen.getD (owner z) default).slots
        (frozen.getD (owner z) default).move) z.1 z.2
  have hfibre (k : ℕ) :
      (∑ z ∈ S.filter (fun z => owner z = k),
          grayTailSonBase
            (grayTailSlotEntries (frozen.getD k default).slots
              (frozen.getD k default).move) z.1 z.2) =
        ∑ z ∈ S.filter (fun z => owner z = k), x z := by
    apply Finset.sum_congr rfl
    intro z hz
    have hzk : owner z = k := (Finset.mem_filter.mp hz).2
    simp only [x]
    rw [hzk]
  rw [grayTail_listSum_eq_sum_range_getD]
  calc
    (∑ k ∈ Finset.range frozen.length,
        grayTailOwnerCharge frozen slots used I
          (frozen.getD k default).roundIndex) =
      ∑ k ∈ Finset.range frozen.length,
        grayTailOwnerCharge frozen slots used I k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hchron k (Finset.mem_range.mp hk)]
    _ = ∑ k ∈ Finset.range frozen.length,
        2 * ∑ z ∈ S.filter (fun z => owner z = k),
          grayTailSonBase
            (grayTailSlotEntries (frozen.getD k default).slots
              (frozen.getD k default).move) z.1 z.2 := by
        simp only [grayTailOwnerCharge, S, owner]
    _ = ∑ k ∈ Finset.range frozen.length,
        2 * ∑ z ∈ S.filter (fun z => owner z = k), x z := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hfibre k]
    _ = 2 * ∑ k ∈ Finset.range frozen.length,
        ∑ z ∈ S.filter (fun z => owner z = k), x z := by
        rw [Finset.mul_sum]
    _ = 2 * ∑ z ∈ S, x z := by
        rw [sum_owner_fibres S owner frozen.length]
        intro z hz
        exact howner z (by simpa only [S] using hz)
    _ = 2 * ∑ z ∈ grayTailSelectedInactive slots used I,
        grayTailSonBase
          (grayTailSlotEntries
            (frozen.getD (grayTailOwnerIndex frozen z.1 z.2) default).slots
            (frozen.getD (grayTailOwnerIndex frozen z.1 z.2) default).move)
          z.1 z.2 := by
        rfl

/-- The total chronological owner charge of an actual controller history is
bounded by twice the number of selected inactive sons times the certified
per-call cap. -/
lemma grayTail_ownerCharge_sum_le_lastCap
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hx_cap : ∀ p ∈ (grayTailRunState q L a e n sigma A sm T).frozen,
      ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)),
        grayTailSonBase (grayTailSlotEntries p.slots p.move) i c ≤
          dyadicScale e / (12 * halfAmplification q))
    (howner : ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      c.val < 2 ^ (e - a) →
        ¬ GrayTailHasSon (grayTailRunState q L a e n sigma A sm T).slots i c →
          GrayTailOwnerSplitAt
            (grayTailRunState q L a e n sigma A sm T).frozen i c
            (grayTailOwnerIndex
              (grayTailRunState q L a e n sigma A sm T).frozen i c))
    (I : List ℕ) :
    ((grayTailRunState q L a e n sigma A sm T).frozen.map fun p =>
        grayTailOwnerCharge
          (grayTailRunState q L a e n sigma A sm T).frozen
          (grayTailRunState q L a e n sigma A sm T).slots
          (2 ^ (e - a)) I p.roundIndex).sum ≤
      2 * ((grayTailSelectedInactive
        (grayTailRunState q L a e n sigma A sm T).slots
        (2 ^ (e - a)) I).card : ℚ) *
          (dyadicScale e / (12 * halfAmplification q)) := by
  classical
  let frozen := (grayTailRunState q L a e n sigma A sm T).frozen
  let slots := (grayTailRunState q L a e n sigma A sm T).slots
  let used := 2 ^ (e - a)
  let S := grayTailSelectedInactive slots used I
  let cap := dyadicScale e / (12 * halfAmplification q)
  have hchron : ∀ k, k < frozen.length →
      (frozen.getD k default).roundIndex = k := by
    intro k hk
    rw [List.getD_eq_getElem frozen default hk]
    exact
      grayTail_frozen_roundIndex_eq_position
        (q := q) (L := L) (a := a) (e := e) (n := n)
        (sigma := sigma) (A := A) (sm := sm) (T := T) k hk
  have howner_lt : ∀ z ∈ S, grayTailOwnerIndex frozen z.1 z.2 < frozen.length := by
    intro z hz
    have hzsel : z ∈ grayTailSelectedInactive slots used I := by
      simpa only [S] using hz
    have hzparts :
        z.1.val ∈ I ∧ z.2.val < used ∧ ¬ GrayTailHasSon slots z.1 z.2 := by
      simpa only [grayTailSelectedInactive, Finset.mem_filter, Finset.mem_univ,
        true_and] using hzsel
    have hsplit : GrayTailOwnerSplitAt frozen z.1 z.2
        (grayTailOwnerIndex frozen z.1 z.2) := by
      simpa only [frozen, slots, used] using
        howner z.1 z.2 hzparts.2.1 hzparts.2.2
    exact grayTailOwnerIndex_lt_length ⟨_, hsplit⟩
  rw [grayTail_ownerCharge_sum_eq frozen slots used I hchron howner_lt]
  have hpoint : ∀ z ∈ S,
      grayTailSonBase
        (grayTailSlotEntries
          (frozen.getD (grayTailOwnerIndex frozen z.1 z.2) default).slots
          (frozen.getD (grayTailOwnerIndex frozen z.1 z.2) default).move)
        z.1 z.2 ≤ cap := by
    intro z hz
    have hlt := howner_lt z hz
    have hp : frozen.getD (grayTailOwnerIndex frozen z.1 z.2) default ∈ frozen := by
      rw [List.getD_eq_getElem frozen default hlt]
      exact List.get_mem frozen ⟨grayTailOwnerIndex frozen z.1 z.2, hlt⟩
    simpa only [frozen, cap] using
      hx_cap (frozen.getD (grayTailOwnerIndex frozen z.1 z.2) default) hp z.1 z.2
  calc
    2 * ∑ z ∈ grayTailSelectedInactive slots used I,
        grayTailSonBase
          (grayTailSlotEntries
            (frozen.getD (grayTailOwnerIndex frozen z.1 z.2) default).slots
            (frozen.getD (grayTailOwnerIndex frozen z.1 z.2) default).move)
          z.1 z.2 ≤
      2 * ∑ _z ∈ S, cap := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum fun z hz => hpoint z hz
        · norm_num
    _ = 2 * (S.card : ℚ) * cap := by
        simp [mul_assoc]
    _ = 2 * ((grayTailSelectedInactive
        (grayTailRunState q L a e n sigma A sm T).slots
        (2 ^ (e - a)) I).card : ℚ) *
          (dyadicScale e / (12 * halfAmplification q)) := by
        rfl

/-- Every source son receives the robust pointwise progress already in the
first frozen round.  Nonnegativity of all later increments transports that
gain to the terminal accumulated son base. -/
lemma grayTail_terminal_source_gain
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hn : 1 ≤ n)
    (hdata : GrayTailTerminalData q L a e n sigma A sm T)
    (i : Fin n) (c : Fin (grayTailBranch q L a e))
    (hc : c.val < 2 ^ (e - a)) :
    (3 / 4 : ℚ) * dyadicScale (grayCallDepth q e) ≤
      halfAmplification q *
        grayTailFrozenSonBase
          (grayTailRunState q L a e n sigma A sm T).frozen i c := by
  let st := grayTailRunState q L a e n sigma A sm T
  have hfrozen_ne : st.frozen ≠ [] := by
    intro hfrozen
    have hslots :
        st.slots = grayTailSlots n (grayTailBranch q L a e)
          (2 ^ (e - a)) 0 := by
      exact (grayTailStateAt_sourceFirst
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm T).1 hfrozen
    have hused : 2 ^ (e - a) ≤ grayTailBranch q L a e := by
      unfold grayTailBranch ladderBranching
      exact le_trans (by omega) (le_max_left _ _)
    have hbranch : 0 < grayTailBranch q L a e :=
      lt_of_lt_of_le (Nat.two_pow_pos _) hused
    have hlength : st.slots.length = n * 2 ^ (e - a) := by
      rw [hslots, grayTailSlots_length _ _ _ _ hbranch hused]
    have hpositive : 0 < n * 2 ^ (e - a) :=
      Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hn) (Nat.two_pow_pos _)
    have hquarter := hdata.terminal_width
    change 4 * st.slots.length ≤ n * 2 ^ (e - a) at hquarter
    rw [hlength] at hquarter
    omega
  have hlen : 0 < st.frozen.length := List.length_pos_iff.mpr hfrozen_ne
  let p := st.frozen.get ⟨0, hlen⟩
  have hp : p ∈ st.frozen := List.get_mem st.frozen ⟨0, hlen⟩
  have hp_index : p.roundIndex = 0 := by
    simpa only [st, p] using hdata.round_index_eq 0 hlen
  have hp_son : GrayTailRoundHasSon p i c := by
    simpa only [st] using hdata.first_round p hp hp_index i c hc
  rcases hp_son with ⟨s, hs, hsi, hsc⟩
  obtain ⟨j, hj, hjs⟩ := List.mem_iff_getElem.mp hs
  have hj_i : (p.slots.get ⟨j, hj⟩).1 = i := by
    rw [List.get_eq_getElem, hjs, hsi]
  have hj_c : (p.slots.get ⟨j, hj⟩).2.1 = c := by
    rw [List.get_eq_getElem, hjs, hsc]
  have hround :
      (3 / 4 : ℚ) * dyadicScale (grayCallDepth q e) ≤
        halfAmplification q *
          grayTailSonBase (grayTailSlotEntries p.slots p.move) i c := by
    exact grayTailSlotEntries_selected_progress_global
      (halfAmplification_pos q)
      (mul_nonneg (by norm_num) (dyadicScale_pos _).le)
      (familyRobustGrayGoalAtB.to_pointwise
        (hdata.certified.round_valid p (by simpa only [st] using hp)).2.2.2.2.1)
      ⟨j, hj⟩ i c hj_i hj_c
  have hterm_nonneg : ∀ x ∈ st.frozen,
      0 ≤ grayTailSonBase (grayTailSlotEntries x.slots x.move) i c := by
    intro x hx
    have hvalid := hdata.certified.round_valid x (by simpa only [st] using hx)
    exact grayTailSonBase_nonneg_global
      (grayTailSlotEntries_root_nonneg (halfAmplification_pos q)
        (mul_nonneg (by norm_num) (dyadicScale_pos _).le)
        (familyRobustGrayGoalAtB.to_pointwise hvalid.2.2.2.2.1))
  have hp_le :
      grayTailSonBase (grayTailSlotEntries p.slots p.move) i c ≤
        (st.frozen.map fun x =>
          grayTailSonBase (grayTailSlotEntries x.slots x.move) i c).sum := by
    apply List.single_le_sum
    · intro y hy
      rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact hterm_nonneg x hx
    · exact List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [grayTail_frozenSonBase_eq_sum_rounds]
  exact le_trans hround
    (mul_le_mul_of_nonneg_left hp_le (halfAmplification_pos q).le)

end Kolmogorov
