import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Corner
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Leaf2Hereditary

/-!
# The source side of the subfamily bound for the composed charge

The mass accounting for the sources of a V2 charged run, assembled root sublist by root sublist.
The per-round statements come first — the local subfamily inequality of a frozen round
(`grayChargedV2_rounds_subfamily_le_mass`) and the mass of a transported source round after
filtering (`grayChargeMass_transportRound_filter_eq`,
`grayChargedV2_source_round_mass_filter_eq`) — supported by the list identities that collapse
membership indicators over duplicate-free lists and commute list and finset sums. Summing over
the rounds identifies the source ledger with the owner-restricted frozen base sum
(`grayChargedV2_leaf2_PI_eq_base`), assembles the reserve deficit
(`grayChargedV2_leaf2_reserve_deficit`) and yields the pointwise subfamily bound
`grayChargedV2_l5subfamily_pointwise`.
-/



namespace Kolmogorov

/-- **Per-round subfamily bound**: the local subfamily inequality of a frozen
round, from `familyGrayChargeAtB.subfamily`. -/
lemma grayChargedV2_rounds_subfamily_le_mass
    {q L a e n U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (k : Fin (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen.length)
    (J : List Nat)
    (hJ : J ∈ (List.range
      (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen[k.val]).slots.length)).sublists) :
    halfAmplification q *
        (2 * totalRootRequestOnList J
            (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm U).core.frozen[k.val]).move) -
          totalRootRequest
            (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm U).core.frozen[k.val]).slots.length)
            (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm U).core.frozen[k.val]).move)) <=
      grayChargeMass
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen[k.val]).blockAnchor + L)
        ((grayChargedRoundLocalChargeV2 hae _ (List.getElem_mem k.isLt)).filter
          fun z => decide (z.1 ∈ J)) := by
  set p := (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm U).core.frozen[k.val] with hpdef
  have hp : p ∈ (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen := List.getElem_mem k.isLt
  unfold grayChargedRoundLocalChargeV2
  split
  next hfine =>
    have hsplit := grayChargedRunStateV2_frozen_phase_split
      q L a e sigma A sm U hp hae hfine
    have hvalid := grayChargedLocalChargeOfBlockGoal_valid
      (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm U hp
        hae hfine)
    have hsub := familyGrayChargeAtB.subfamily hvalid hJ
    have hEq : grayTailRoundDelta q L e p.roundIndex =
        p.blockAnchor + L := by
      rw [hsplit.1, grayTailRoundDelta]
    rw [← hEq]
    exact hsub
  next hfine =>
    have hSp := grayChargedRunStateV2_frozen_spend_goal
      q L a e sigma A sm U hp hfine
    have hvalid := grayChargedLocalChargeOfBlockSpendGoal_valid
      hSp.choose_spec.2.2.2
    have hsub := familyGrayChargeAtB.subfamily hvalid hJ
    have hfineEq3 : p.fineEnd = p.blockAnchor + L :=
      grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm U hp
    have hEq : grayChargedSpendDelta a L e hSp.choose =
        p.blockAnchor + L := by
      have hanchor := hSp.choose_spec.2.1
      have hfineEq2 := hSp.choose_spec.2.2.1
      have hd : grayChargedSpendDelta a L e hSp.choose =
          grayChargedSpendEps a L e hSp.choose + L := rfl
      omega
    rw [← hEq]
    exact hsub

/-- Nodup collapse: a membership indicator sum over a nodup list keeps at
most one nonzero term. -/
lemma grayCharged_sum_map_ite_owner_mem {β : Type _} [DecidableEq β]
    (I : List β) (owner : β) (X : Rat) (hI : I.Nodup) :
    (I.map (fun i => if owner = i then X else 0)).sum =
      (if owner ∈ I then X else 0) := by
  induction I with
  | nil => simp
  | cons a rest ih =>
      have hnr : rest.Nodup := (List.nodup_cons.mp hI).2
      have har : a ∉ rest := (List.nodup_cons.mp hI).1
      rw [List.map_cons, List.sum_cons, ih hnr]
      by_cases hoa : owner = a
      · rw [ite_eq_left hoa]
        have hor : owner ∉ rest := by rw [hoa]; exact har
        rw [ite_eq_right hor, add_zero]
        have hmem : owner ∈ a :: rest := by rw [hoa]; exact List.mem_cons_self
        rw [ite_eq_left hmem]
      · rw [ite_eq_right hoa, zero_add]
        by_cases hor : owner ∈ rest
        · rw [ite_eq_left hor, ite_eq_left (List.mem_cons_of_mem a hor)]
        · rw [ite_eq_right hor]
          have hnm : owner ∉ a :: rest := by
            rw [List.mem_cons]; push Not; exact ⟨hoa, hor⟩
          rw [ite_eq_right hnm]

/-- Swap a list sum of finset sums. -/
lemma grayCharged_list_sum_finset_sum_comm {β γ : Type _}
    (I : List β) (s : Finset γ) (f : β -> γ -> Rat) :
    (I.map (fun i => ∑ j ∈ s, f i j)).sum =
      ∑ j ∈ s, (I.map (fun i => f i j)).sum := by
  induction I with
  | nil => simp
  | cons a rest ih =>
      rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [List.map_cons, List.sum_cons]

/-- **Transport-filter mass equation** (general): filtering a transported
round by a set of outer roots `I` carries the same mass as filtering the
local charge by the slot indices whose owner lies in `I`. -/
lemma grayChargeMass_transportRound_filter_eq
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n b D : Nat}
    {slots : List (GrayTailSlot n b)}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge} (I : List Nat) (hInodup : I.Nodup)
    (hdepth : deltaDepth <= D)
    (hvalid : familyGrayChargeAtB eta kappa alpha beta epsDepth deltaDepth
      slots.length A c s G = true) :
    grayChargeMass D ((grayChargedTransportRound D slots G).filter
        fun z => decide (z.1 ∈ I)) =
      grayChargeMass deltaDepth (G.filter fun z => decide (z.1 ∈
        ((List.finRange slots.length).filter
          (fun j => decide ((slots.get j).1.val ∈ I))).map Fin.val)) := by
  classical
  set Jk := ((List.finRange slots.length).filter
    (fun j => decide ((slots.get j).1.val ∈ I))).map Fin.val with hJkdef
  have hJkNodup : Jk.Nodup := by
    rw [hJkdef]
    apply List.Nodup.map Fin.val_injective
    exact (List.nodup_finRange slots.length).filter _
  have hJklt : ∀ x, x ∈ Jk -> x < slots.length := by
    intro x hx
    rw [hJkdef, List.mem_map] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact j.isLt
  have hJkmem : ∀ j : Fin slots.length,
      (j.val ∈ Jk) ↔ (slots.get j).1.val ∈ I := by
    intro j
    rw [hJkdef]
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    constructor
    · rintro ⟨j', hj', hval⟩
      have hjj : j' = j := Fin.val_injective hval
      rwa [hjj] at hj'
    · intro h
      exact ⟨j, h, rfl⟩
  rw [grayCharged_mass_filter_mem D _ I hInodup]
  have hLHS : (I.map fun i => grayChargeMass D
        (grayChargeAtRoot i (grayChargedTransportRound D slots G))).sum =
      ∑ j : Fin slots.length,
        (if (slots.get j).1.val ∈ I then
          grayChargeMass deltaDepth (grayChargeAtRoot j.val G) else 0) := by
    have hmapEq : (I.map fun i => grayChargeMass D
          (grayChargeAtRoot i (grayChargedTransportRound D slots G))) =
        (I.map fun i => ∑ j : Fin slots.length,
          (if (slots.get j).1.val = i then
            grayChargeMass deltaDepth (grayChargeAtRoot j.val G)
          else 0)) :=
      List.map_congr_left (fun i _ =>
        grayChargeMass_grayChargeAtRoot_transportRound hdepth hvalid)
    rw [hmapEq, grayCharged_list_sum_finset_sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact grayCharged_sum_map_ite_owner_mem I ((slots.get j).1.val)
      (grayChargeMass deltaDepth (grayChargeAtRoot j.val G)) hInodup
  rw [hLHS, grayCharged_mass_filter_mem deltaDepth G Jk hJkNodup,
    ← grayCharged_list_filter_univ_sum Jk hJkNodup hJklt
      (fun j => grayChargeMass deltaDepth (grayChargeAtRoot j G)),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : (slots.get j).1.val ∈ I
  · rw [ite_eq_left h, ite_eq_left ((hJkmem j).mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h ((hJkmem j).mp hc))]

/-- **Per-round source mass equation**: the mass of one transported source
round filtered by outer roots `I` equals the local round charge filtered by
its owner-in-`I` slot indices. Mirrors the phase split of
`grayChargedV2_rounds_request_le_mass`. -/
lemma grayChargedV2_source_round_mass_filter_eq
    {q L a e n U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen)
    (I : List Nat) (hInodup : I.Nodup) :
    grayChargeMass (e + grayTailNewLoss q L)
        ((grayChargedTransportRound (e + grayTailNewLoss q L)
          p.slots
          (grayChargedRoundLocalChargeV2 hae p hp)).filter
          fun z => decide (z.1 ∈ I)) =
      grayChargeMass (p.blockAnchor + L)
        ((grayChargedRoundLocalChargeV2 hae p hp).filter
          fun z => decide (z.1 ∈
            ((List.finRange p.slots.length).filter
              (fun j => decide ((p.slots.get j).1.val ∈ I))).map Fin.val)) := by
  have hub := grayChargedRunStateV2_frozen_depth_ub (t := U) hp hae
  unfold grayChargedRoundLocalChargeV2
  split
  next hfine =>
    have hsplit := grayChargedRunStateV2_frozen_phase_split
      q L a e sigma A sm U hp hae hfine
    have hvalid := grayChargedLocalChargeOfBlockGoal_valid
      (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm U hp
        hae hfine)
    have hdeltaLe : grayTailRoundDelta q L e p.roundIndex <=
        e + grayTailNewLoss q L := by
      have hfineEq : p.fineEnd = p.blockAnchor + L := by
        rw [hsplit.2.1, hsplit.1, grayTailRoundDelta]
      rw [← hsplit.2.1, hfineEq]
      exact hub
    have hEq : grayTailRoundDelta q L e p.roundIndex =
        p.blockAnchor + L := by
      rw [hsplit.1, grayTailRoundDelta]
    rw [grayChargeMass_transportRound_filter_eq I hInodup hdeltaLe hvalid]
    exact congrArg (fun d => grayChargeMass d _) hEq
  next hfine =>
    have hSp := grayChargedRunStateV2_frozen_spend_goal
      q L a e sigma A sm U hp hfine
    have hvalid := grayChargedLocalChargeOfBlockSpendGoal_valid
      hSp.choose_spec.2.2.2
    have hanchor := hSp.choose_spec.2.1
    have hfineEq2 := hSp.choose_spec.2.2.1
    have hd : grayChargedSpendDelta a L e hSp.choose =
        grayChargedSpendEps a L e hSp.choose + L := rfl
    have hfineEq3 : p.fineEnd = p.blockAnchor + L :=
      grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm U hp
    have hdeltaLe : grayChargedSpendDelta a L e hSp.choose <=
        e + grayTailNewLoss q L := by omega
    have hEq : grayChargedSpendDelta a L e hSp.choose =
        p.blockAnchor + L := by omega
    rw [grayChargeMass_transportRound_filter_eq I hInodup hdeltaLe hvalid]
    exact congrArg (fun d => grayChargeMass d _) hEq

/-- The owner-in-`I` slot indices form a sublist of the slot range. -/
lemma grayCharged_ownerFilter_sublist_range {n b : Nat}
    (slots : List (GrayTailSlot n b)) (I : List Nat) :
    ((List.finRange slots.length).filter
        (fun j => decide ((slots.get j).1.val ∈ I))).map Fin.val ∈
      (List.range slots.length).sublists := by
  rw [List.mem_sublists]
  have hrange : (List.finRange slots.length).map Fin.val =
      List.range slots.length := List.map_coe_finRange_eq_range
  rw [← hrange]
  exact List.filter_sublist.map Fin.val

/-- **The source subfamily bound (S)**: at the source ledger's home `T+1`,
`κ·(2·P_I − P) ≤ MS_I`, assembled from the per-round subfamily bounds and
the per-round source mass equation. `P_I` sums the owner-restricted local
requests, `P` the full local requests. -/
theorem grayChargedV2_leaf2_source_subfamily
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (hae : a <= e)
    (I : List Nat) (hInodup : I.Nodup) :
    halfAmplification q *
        (2 * (∑ k : Fin (grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen.length,
            totalRootRequestOnList
              (((List.finRange
                (((grayChargedRunStateV2 (n := n)
                  (b := grayTailBranch q L a e)
                  q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)).filter
                (fun j => decide
                  ((((grayChargedRunStateV2 (n := n)
                    (b := grayTailBranch q L a e)
                    q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.get
                    j).1.val ∈ I))).map Fin.val)
              (((grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[k.val]).move)) -
          (∑ k : Fin (grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen.length,
            totalRootRequest
              (((grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
              (((grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[k.val]).move))) <=
      grayChargeMass (e + grayTailNewLoss q L)
        ((grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae)).filter
          fun z => decide (z.1 ∈ I)) := by
  classical
  rw [grayChargedFrozenSourcesV2_charge_eq hsm replay hU hae,
    List.filter_flatMap, grayChargeMass_flatMap, ← List.ofFn_eq_map,
    List.sum_ofFn]
  have hmass : ∀ k : Fin (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen.length,
      grayChargeMass (e + grayTailNewLoss q L)
        ((grayChargedTransportRound (e + grayTailNewLoss q L)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots)
          (grayChargedRoundLocalChargeV2 hae _
            (List.getElem_mem k.isLt))).filter
          fun z => decide (z.1 ∈ I)) =
      grayChargeMass
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen[k.val]).blockAnchor + L)
        ((grayChargedRoundLocalChargeV2 hae _
          (List.getElem_mem k.isLt)).filter
          fun z => decide (z.1 ∈
            ((List.finRange
              (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)).filter
              (fun j => decide
                ((((grayChargedRunStateV2 (n := n)
                  (b := grayTailBranch q L a e)
                  q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.get
                  j).1.val ∈ I))).map Fin.val)) := fun k =>
    grayChargedV2_source_round_mass_filter_eq hae (List.getElem_mem k.isLt)
      I hInodup
  rw [Finset.sum_congr rfl (fun k _ => hmass k)]
  rw [show (2 * (∑ k : Fin (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.length,
      totalRootRequestOnList
        (((List.finRange
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)).filter
          (fun j => decide
            ((((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.get
              j).1.val ∈ I))).map Fin.val)
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen[k.val]).move)) -
      (∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).move))) =
      ∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        (2 * totalRootRequestOnList
          (((List.finRange
            (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)).filter
            (fun j => decide
              ((((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.get
                j).1.val ∈ I))).map Fin.val)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).move) -
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).move)) from by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact grayChargedV2_rounds_subfamily_le_mass hae k _
    (grayCharged_ownerFilter_sublist_range _ I)

/-- The `Fin n` fibre of a nodup root list has card equal to the list length. -/
lemma grayCharged_fibre_card_eq_length {n : Nat} (I : List Nat)
    (hnodup : I.Nodup) (hlt : ∀ x ∈ I, x < n) :
    (Finset.univ.filter (fun j : Fin n => j.val ∈ I)).card = I.length := by
  classical
  have h := grayCharged_list_filter_univ_sum (n := n) I hnodup hlt
    (fun _ => (1 : Rat))
  rw [Finset.sum_const, List.map_const', List.sum_replicate] at h
  simp only [nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- **H1 upper (D_I)**: the owner-restricted display is at most `|I|` coarse
units. -/
lemma grayChargedV2_totalRootRequestOnList_le (I : List Nat)
    (move : FamilyClientMove) (hi : Rat)
    (hb : ∀ i ∈ I, getFamilyReq move i [] <= hi) :
    totalRootRequestOnList I move <= (I.length : Rat) * hi := by
  induction I with
  | nil => simp [totalRootRequestOnList]
  | cons x xs ih =>
      have hstep : totalRootRequestOnList (x :: xs) move =
          getFamilyReq move x [] + totalRootRequestOnList xs move := rfl
      rw [hstep, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul,
        one_mul]
      have h1 := hb x List.mem_cons_self
      have h2 := ih (fun i hi' => hb i (List.mem_cons_of_mem x hi'))
      linarith

/-- **H1 lower (complement)**: the display outside `I` carries at least
`(n − |I|)` coarse half-units. -/
lemma grayChargedV2_totalRootRequest_sub_onList_ge {n : Nat} (I : List Nat)
    (hnodup : I.Nodup) (hlt : ∀ x ∈ I, x < n)
    (move : FamilyClientMove) (lo : Rat)
    (hb : ∀ i : Fin n, lo <= getFamilyReq move i.val []) :
    ((n : Rat) - (I.length : Rat)) * lo <=
      totalRootRequest n move - totalRootRequestOnList I move := by
  classical
  have hDI : totalRootRequestOnList I move =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
        getFamilyReq move j.val [] := by
    rw [totalRootRequestOnList_eq_map_sum,
      ← grayCharged_list_filter_univ_sum I hnodup hlt
        (fun i => getFamilyReq move i [])]
  have hD : totalRootRequest n move =
      ∑ j : Fin n, getFamilyReq move j.val [] := rfl
  have hsdiff : (∑ j ∈ Finset.univ \
      Finset.univ.filter (fun j : Fin n => j.val ∈ I),
        getFamilyReq move j.val []) =
      totalRootRequest n move - totalRootRequestOnList I move := by
    rw [hDI, hD, eq_sub_iff_add_eq]
    exact Finset.sum_sdiff (Finset.filter_subset _ _)
  rw [← hsdiff]
  have hcard : (Finset.univ \
      Finset.univ.filter (fun j : Fin n => j.val ∈ I)).card =
      n - I.length := by
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      Finset.card_univ, Fintype.card_fin,
      grayCharged_fibre_card_eq_length I hnodup hlt]
  have hle : ((Finset.univ \
      Finset.univ.filter (fun j : Fin n => j.val ∈ I)).card : Rat) * lo <=
      ∑ j ∈ Finset.univ \
        Finset.univ.filter (fun j : Fin n => j.val ∈ I),
        getFamilyReq move j.val [] := by
    have heq : ((Finset.univ \
        Finset.univ.filter (fun j : Fin n => j.val ∈ I)).card : Rat) * lo =
        ∑ _j ∈ Finset.univ \
          Finset.univ.filter (fun j : Fin n => j.val ∈ I), lo := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [heq]
    exact Finset.sum_le_sum (fun j _ => hb j)
  refine le_trans ?_ hle
  rw [hcard]
  have hIn : I.length <= n := by
    rw [← grayCharged_fibre_card_eq_length I hnodup hlt]
    have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun j => j.val ∈ I)
    rwa [Finset.card_univ, Fintype.card_fin] at h1
  rw [Nat.cast_sub hIn]

/-- List map of a sum distributes over the list sum. -/
lemma grayCharged_list_map_add_sum {β : Type _} (I : List β) (x y : β -> Rat) :
    (I.map (fun i => x i + y i)).sum = (I.map x).sum + (I.map y).sum := by
  induction I with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- Right multiplication distributes over a list map sum. -/
lemma grayCharged_list_sum_mul_right {β : Type _} (I : List β) (x : β -> Rat)
    (c : Rat) :
    (I.map x).sum * c = (I.map (fun i => x i * c)).sum := by
  induction I with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, ih]

/-- **The membership count splits over a nodup index list** into the
per-index equality counts. -/
lemma grayCharged_countP_mem_eq_sum_rat {α : Type _} (l : List α)
    (f : α -> Nat) (I : List Nat) (hI : I.Nodup) :
    ((l.countP (fun a => decide (f a ∈ I)) : Nat) : Rat) =
      (I.map (fun i =>
        ((l.countP (fun a => decide (f a = i)) : Nat) : Rat))).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      rw [List.countP_cons]
      have hmap : (I.map fun i =>
            (((a :: rest).countP (fun b => decide (f b = i)) : Nat) : Rat)) =
          (I.map fun i =>
            ((rest.countP (fun b => decide (f b = i)) : Nat) : Rat) +
              (if f a = i then (1 : Rat) else 0)) := by
        refine List.map_congr_left (fun i _ => ?_)
        rw [List.countP_cons]
        push_cast
        by_cases h : f a = i <;> simp [h]
      rw [hmap, grayCharged_list_map_add_sum, ← ih,
        grayCharged_sum_map_ite_owner_mem I (f a) (1 : Rat) hI]
      push_cast
      by_cases h : f a ∈ I <;> simp [h]

/-- **hMR (reserve lower)**: the owner-restricted reserve charge carries at
least `c_I·(5ε/6)`, from the per-root reserve lower bound summed over `I`. -/
lemma grayChargedV2_leaf2_reserve_mass_ge
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hunit : ∀ r, r ∈ reserves ->
      5 * dyadicScale e / 6 <=
        grayChargeMass (e + grayTailNewLoss q L) r.cells)
    (I : List Nat) (hInodup : I.Nodup) :
    ((reserves.countP (fun r => decide (r.coordinate.1.val ∈ I)) : Nat) :
        Rat) * (5 * dyadicScale e / 6) <=
      grayChargeMass (e + grayTailNewLoss q L)
        ((grayChargedReserveChargeV2 reserves).filter
          fun z => decide (z.1 ∈ I)) := by
  classical
  rw [grayCharged_mass_filter_mem (e + grayTailNewLoss q L)
      (grayChargedReserveChargeV2 reserves) I hInodup,
    grayCharged_countP_mem_eq_sum_rat reserves
      (fun r => r.coordinate.1.val) I hInodup,
    grayCharged_list_sum_mul_right]
  refine List.sum_le_sum (fun i _ => ?_)
  exact grayChargedReserveChargeV2_perRoot_mass_ge_of_unit reserves i hunit

/-- **STEP A (reserve↔resolved bijection)**: the reserve count owned by `I`
equals the number of resolved coordinates whose root lies in `I`. -/
lemma grayChargedV2_reserve_countP_eq_resolved_card
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hcoverBack : ∀ r, r ∈ reserves -> r.coordinate ∈
      grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay)
    (hcover : ∀ z, z ∈ grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay ->
      ∃ r, r ∈ reserves ∧ r.coordinate = z)
    (hcoordNodup : (reserves.map (fun r => r.coordinate)).Nodup)
    (I : List Nat) :
    reserves.countP (fun r => decide (r.coordinate.1.val ∈ I)) =
      ((grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay).filter
          (fun z => z.1.val ∈ I)).card := by
  classical
  set resolved := grayChargedReplayV2RaisedSources replay ∪
    grayChargedReplayV2ServerResolvedSources replay with hres
  set L := reserves.map (fun r => r.coordinate) with hL
  have hLtoFinset : L.toFinset = resolved := by
    ext z
    rw [List.mem_toFinset, hL, List.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hcoverBack r hr
    · intro hz
      obtain ⟨r, hr, hrz⟩ := hcover z hz
      exact ⟨r, hr, hrz⟩
  have h1 : reserves.countP (fun r => decide (r.coordinate.1.val ∈ I)) =
      L.countP (fun z => decide (z.1.val ∈ I)) := by
    rw [hL, List.countP_map]
    rfl
  rw [h1, List.countP_eq_length_filter]
  have hfnodup : (L.filter (fun z => decide (z.1.val ∈ I))).Nodup :=
    hcoordNodup.filter _
  rw [← List.toFinset_card_of_nodup hfnodup]
  congr 1
  ext z
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter,
    decide_eq_true_eq]
  rw [← List.mem_toFinset, hLtoFinset]

/-- **The I-restricted source slab card** (`m_I`): the source coordinates
owned by `I` number `|I|·used`. -/
lemma grayCharged_card_source_slab_on {n : Nat} (b used : Nat)
    (hused : used <= b) (I : List Nat) (hnodup : I.Nodup)
    (hlt : ∀ x ∈ I, x < n) :
    (Finset.univ.filter fun z : Fin n × Fin b =>
        z.2.val < used ∧ z.1.val ∈ I).card = I.length * used := by
  classical
  have hprod : (Finset.univ.filter fun z : Fin n × Fin b =>
      z.2.val < used ∧ z.1.val ∈ I) =
      (Finset.univ.filter fun i : Fin n => i.val ∈ I) ×ˢ
        (Finset.univ.filter fun c : Fin b => c.val < used) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product]
    tauto
  have hcard_c : (Finset.univ.filter fun c : Fin b => c.val < used).card =
      used := by
    have himg : ((Finset.univ.filter fun c : Fin b => c.val < used).image
        Fin.val) = Finset.range used := by
      ext m
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_range]
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact hc
      · intro hm
        exact ⟨⟨m, lt_of_lt_of_le hm hused⟩, hm, rfl⟩
    have hh := congrArg Finset.card himg
    rwa [Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_range] at hh
  rw [hprod, Finset.card_product,
    grayCharged_fibre_card_eq_length I hnodup hlt, hcard_c]

/-- **hc_I_lo (the per-`I` quarter)**: the owner-restricted reserve count is
at least `m_I − m/4`.  From STEP A (reserve↔resolved), the source slab card
`m_I = |I|·sc`, the sdiff bound `m_I − c_I ≤ #unresolved`, and the global
three-quarters `4·#unresolved ≤ m`. -/
lemma grayChargedV2_leaf2_quarter
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hcoverBack : ∀ r, r ∈ reserves -> r.coordinate ∈
      grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay)
    (hcover : ∀ z, z ∈ grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay ->
      ∃ r, r ∈ reserves ∧ r.coordinate = z)
    (hcoordNodup : (reserves.map (fun r => r.coordinate)).Nodup)
    (I : List Nat) (hnodup : I.Nodup) (hlt : ∀ x ∈ I, x < n) :
    ((I.length * grayChargedSourceCount a e : Nat) : Rat) -
        ((n * grayChargedSourceCount a e : Nat) : Rat) / 4 <=
      ((reserves.countP (fun r => decide (r.coordinate.1.val ∈ I)) : Nat) :
        Rat) := by
  classical
  have heq := grayChargedReplayV2_resolvedSourceCount_eq replay
  have hquarter := grayChargedReplayV2_terminal_active_quarter replay
  set resolved := grayChargedReplayV2RaisedSources replay ∪
    grayChargedReplayV2ServerResolvedSources replay with hres
  set cI := reserves.countP (fun r => decide (r.coordinate.1.val ∈ I))
    with hcIdef
  set sourceI := Finset.univ.filter
    fun z : Fin n × Fin (grayTailBranch q L a e) =>
      z.2.val < grayChargedSourceCount a e ∧ z.1.val ∈ I with hsourceI
  set nextLen := (grayTailNextSlots e (grayChargedSourceCount a e)
    replay.advantageTerminal.frozen.length (grayChargedThreshold q e) A
    (frozenV1OfV2 replay.advantageTerminal)
    (sm replay.advantageDoneTime)).length with hnextLen
  have hstepA : cI = (resolved.filter (fun z => z.1.val ∈ I)).card :=
    grayChargedV2_reserve_countP_eq_resolved_card replay reserves
      hcoverBack hcover hcoordNodup I
  have hslab : sourceI.card = I.length * grayChargedSourceCount a e :=
    grayCharged_card_source_slab_on (grayTailBranch q L a e)
      (grayChargedSourceCount a e)
      (grayChargedSourceCount_le_grayTailBranch q L a e) I hnodup hlt
  have hsub_I : resolved.filter (fun z => z.1.val ∈ I) ⊆ sourceI := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [hsourceI, Finset.mem_filter]
    exact ⟨Finset.mem_univ z,
      ((mem_grayChargedResolvedSources_union z).mp hz.1).1, hz.2⟩
  have hsub_all : resolved ⊆ Finset.univ.filter
      (fun z : Fin n × Fin (grayTailBranch q L a e) =>
        z.2.val < grayChargedSourceCount a e) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,
      ((mem_grayChargedResolvedSources_union z).mp hz).1⟩
  have hc_le : cI <= sourceI.card := by
    rw [hstepA]
    exact Finset.card_le_card hsub_I
  have hstep1 : (sourceI \ resolved.filter (fun z => z.1.val ∈ I)).card <=
      (Finset.univ.filter
        (fun z : Fin n × Fin (grayTailBranch q L a e) =>
          z.2.val < grayChargedSourceCount a e) \ resolved).card := by
    apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    obtain ⟨hzs, hzr⟩ := hz
    rw [hsourceI, Finset.mem_filter] at hzs
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ z, hzs.2.1⟩, ?_⟩
    intro hzresolved
    exact hzr (Finset.mem_filter.mpr ⟨hzresolved, hzs.2.2⟩)
  have hchain : sourceI.card - cI <= nextLen := by
    rw [hstepA, ← Finset.card_sdiff_of_subset hsub_I]
    refine le_trans hstep1 ?_
    rw [Finset.card_sdiff_of_subset hsub_all,
      grayCharged_card_source_slab n (grayTailBranch q L a e)
        (grayChargedSourceCount a e)
        (grayChargedSourceCount_le_grayTailBranch q L a e)]
    omega
  have hnat : 4 * (I.length * grayChargedSourceCount a e) <=
      n * grayChargedSourceCount a e + 4 * cI := by
    rw [← hslab]
    omega
  have hcast : (4 : Rat) * ((I.length * grayChargedSourceCount a e : Nat) :
      Rat) <= ((n * grayChargedSourceCount a e : Nat) : Rat) +
      4 * ((cI : Nat) : Rat) := by
    exact_mod_cast hnat
  linarith

/-- The owner-restricted round request equals the indicator sum over slots. -/
lemma grayChargedV2_totalReqOnList_ownerFilter {n b : Nat}
    (slots : List (GrayTailSlot n b)) (move : FamilyClientMove)
    (I : List Nat) :
    totalRootRequestOnList
        (((List.finRange slots.length).filter
          (fun j => decide ((slots.get j).1.val ∈ I))).map Fin.val) move =
      ∑ j : Fin slots.length,
        (if (slots.get j).1.val ∈ I then getFamilyReq move j.val [] else 0) := by
  classical
  set Jk := ((List.finRange slots.length).filter
    (fun j => decide ((slots.get j).1.val ∈ I))).map Fin.val with hJkdef
  have hJkNodup : Jk.Nodup := by
    rw [hJkdef]
    apply List.Nodup.map Fin.val_injective
    exact (List.nodup_finRange slots.length).filter _
  have hJklt : ∀ x, x ∈ Jk -> x < slots.length := by
    intro x hx
    rw [hJkdef, List.mem_map] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact j.isLt
  have hJkmem : ∀ j : Fin slots.length,
      (j.val ∈ Jk) ↔ (slots.get j).1.val ∈ I := by
    intro j
    rw [hJkdef]
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    constructor
    · rintro ⟨j', hj', hval⟩
      have hjj : j' = j := Fin.val_injective hval
      rwa [hjj] at hj'
    · intro h
      exact ⟨j, h, rfl⟩
  rw [totalRootRequestOnList_eq_map_sum,
    ← grayCharged_list_filter_univ_sum Jk hJkNodup hJklt
      (fun j => getFamilyReq move j []),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : (slots.get j).1.val ∈ I
  · rw [ite_eq_left h, ite_eq_left ((hJkmem j).mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h ((hJkmem j).mp hc))]

/-- Swap a finset sum of list sums. -/
lemma grayCharged_finset_sum_list_sum_comm {β γ : Type _}
    (s : Finset γ) (l : List β) (f : γ -> β -> Rat) :
    (∑ i ∈ s, (l.map (fun p => f i p)).sum) =
      (l.map (fun p => ∑ i ∈ s, f i p)).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

/-- **PI = the owner-restricted frozen base sum** (`hEbound` connection): the
source ledger request on `I` equals the total son base of the roots in `I`,
via the owner-restricted round request and the frozen owner sum. -/
lemma grayChargedV2_leaf2_PI_eq_base
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (I : List Nat) :
    (∑ k : Fin (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen.length,
      totalRootRequestOnList
        (((List.finRange
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.frozen[k.val]).slots.length)).filter
          (fun j => decide
            ((((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).core.frozen[k.val]).slots.get
              j).1.val ∈ I))).map Fin.val)
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen[k.val]).move)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ∈ I),
        ∑ c : Fin (grayTailBranch q L a e),
          grayTailSonBase (grayTailFrozenEntries
            ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1))
            i c := by
  classical
  set V2frozen := (grayChargedRunStateV2 (n := n)
    (b := grayTailBranch q L a e) q L a e sigma A sm t).core.frozen with hV2
  set entriesV1 := grayTailFrozenEntries (V2frozen.map GrayTailRoundV2.toV1)
    with hentV1
  -- both sides equal the per-round owner-in-I request list sum
  have hLHS :
      (∑ k : Fin V2frozen.length,
        totalRootRequestOnList
          (((List.finRange ((V2frozen[k.val]).slots.length)).filter
            (fun j => decide (((V2frozen[k.val]).slots.get j).1.val ∈ I))).map
            Fin.val) ((V2frozen[k.val]).move)) =
      (V2frozen.map fun r => ∑ j : Fin r.slots.length,
        (if (r.slots.get j).1.val ∈ I then getFamilyReq r.move j.val []
        else 0)).sum := by
    rw [sum_map_eq_sum_finRange_rat]
    exact Finset.sum_congr rfl (fun k _ =>
      grayChargedV2_totalReqOnList_ownerFilter _ _ I)
  have hRHS :
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ∈ I),
        ∑ c : Fin (grayTailBranch q L a e),
          grayTailSonBase entriesV1 i c) =
      (V2frozen.map fun r => ∑ j : Fin r.slots.length,
        (if (r.slots.get j).1.val ∈ I then getFamilyReq r.move j.val []
        else 0)).sum := by
    have h1 : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ∈ I),
          ∑ c : Fin (grayTailBranch q L a e), grayTailSonBase entriesV1 i c) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ∈ I),
          (entriesV1.map fun p => if p.1.1 = i then getReq p.2 [] else 0).sum := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact grayTailSonBase_sum_over_sons entriesV1 i
    rw [h1, grayCharged_finset_sum_list_sum_comm]
    have h2 : (entriesV1.map fun p =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ∈ I),
            (if p.1.1 = i then getReq p.2 [] else 0)) =
        entriesV1.map fun p =>
          if p.1.1.val ∈ I then getReq p.2 [] else 0 := by
      refine List.map_congr_left (fun p _ => ?_)
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h2, hentV1, grayTailFrozenEntries, sum_map_flatMap_rat, List.map_map]
    congr 1
    refine List.map_congr_left (fun r _ => ?_)
    rw [Function.comp_apply, grayTailSlotEntries, sum_map_ofFn_rat]
    rfl
  rw [hLHS, hRHS]

/-- **The reserve deficit `(R_I)` assembled**: from the reserve family facts
and the raised-remainder cap `hEbound`, the owner-restricted reserve deficit
holds.  Discharges every premise of `grayChargedV2_reserve_deficit_closes`
except `hEbound`. -/
lemma grayChargedV2_leaf2_reserve_deficit
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hcoverBack : ∀ r, r ∈ reserves -> r.coordinate ∈
      grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay)
    (hcover : ∀ z, z ∈ grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay ->
      ∃ r, r ∈ reserves ∧ r.coordinate = z)
    (hcoordNodup : (reserves.map (fun r => r.coordinate)).Nodup)
    (hunit : ∀ r, r ∈ reserves ->
      5 * dyadicScale e / 6 <=
        grayChargeMass (e + grayTailNewLoss q L) r.cells)
    (hmove : grayChargedRunMoveV2 q L a e n sigma A sm U =
      grayChargedRunMoveV2 q L a e n sigma A sm T)
    (I : List Nat) (hInodup : I.Nodup) (hIlt : ∀ x ∈ I, x < n)
    (PI P : Rat)
    (hEbound : 2 * (totalRootRequestOnList I
          (grayChargedRunMoveV2 q L a e n sigma A sm U) - PI) -
        (totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) -
          P) <=
      ((reserves.countP (fun r => decide (r.coordinate.1.val ∈ I)) : Nat) :
        Rat) *
        (dyadicScale e / (6 * halfAmplification q))) :
    (1 / 2) * (2 * PI - P) +
        (halfAmplification q + 1 / 2) *
          (2 * (totalRootRequestOnList I
              (grayChargedRunMoveV2 q L a e n sigma A sm U) - PI) -
            (totalRootRequest n
                (grayChargedRunMoveV2 q L a e n sigma A sm U) - P)) <=
      grayChargeMass (e + grayTailNewLoss q L)
        ((grayChargedReserveChargeV2 reserves).filter
          fun z => decide (z.1 ∈ I)) := by
  have hfinal := replay.final
  have hkappa : (1 : Rat) <= halfAmplification q := by
    unfold halfAmplification
    have hq : (0 : Rat) <= (q : Rat) / 2 := by positivity
    linarith
  have heps : (0 : Rat) < dyadicScale e := dyadicScale_pos e
  -- request window bounds (H1) at U via move stability
  have hupper : ∀ i ∈ I,
      getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U) i [] <=
        dyadicScale a := by
    intro i hi
    rw [hmove]
    exact (grayChargedV2_final_request_window hpin hae hfinal
      ⟨i, hIlt i hi⟩).2
  have hlower : ∀ i : Fin n,
      dyadicScale a / 2 <=
        getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U) i.val [] := by
    intro i
    rw [hmove]
    exact (grayChargedV2_final_request_window hpin hae hfinal i).1
  have hconv : ((grayChargedSourceCount a e : Nat) : Rat) * dyadicScale e =
      dyadicScale a := grayCharged_dyadic_pow_convert a e hae
  -- hDI_up
  have hDI_up : totalRootRequestOnList I
      (grayChargedRunMoveV2 q L a e n sigma A sm U) <=
      ((I.length * grayChargedSourceCount a e : Nat) : Rat) *
        dyadicScale e := by
    have h1 := grayChargedV2_totalRootRequestOnList_le I
      (grayChargedRunMoveV2 q L a e n sigma A sm U) (dyadicScale a) hupper
    have h2 : ((I.length * grayChargedSourceCount a e : Nat) : Rat) *
        dyadicScale e = (I.length : Rat) * dyadicScale a := by
      push_cast
      rw [mul_assoc, hconv]
    rw [h2]
    exact h1
  -- hDIc_lo
  have hDIc_lo : (((n * grayChargedSourceCount a e : Nat) : Rat) -
        ((I.length * grayChargedSourceCount a e : Nat) : Rat)) *
        dyadicScale e / 2 <=
      totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) -
        totalRootRequestOnList I
          (grayChargedRunMoveV2 q L a e n sigma A sm U) := by
    have h1 := grayChargedV2_totalRootRequest_sub_onList_ge I hInodup hIlt
      (grayChargedRunMoveV2 q L a e n sigma A sm U) (dyadicScale a / 2)
      hlower
    have h2 : (((n * grayChargedSourceCount a e : Nat) : Rat) -
        ((I.length * grayChargedSourceCount a e : Nat) : Rat)) *
        dyadicScale e / 2 =
        ((n : Rat) - (I.length : Rat)) * (dyadicScale a / 2) := by
      push_cast
      rw [← hconv]
      ring
    rw [h2]
    exact h1
  -- hmI
  have hmI : ((I.length * grayChargedSourceCount a e : Nat) : Rat) <=
      ((n * grayChargedSourceCount a e : Nat) : Rat) := by
    have hIn : I.length <= n := by
      rw [← grayCharged_fibre_card_eq_length (n := n) I hInodup hIlt]
      have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin n))
        (fun j => j.val ∈ I)
      rwa [Finset.card_univ, Fintype.card_fin] at h1
    have : I.length * grayChargedSourceCount a e <=
        n * grayChargedSourceCount a e := Nat.mul_le_mul_right _ hIn
    exact_mod_cast this
  -- hMR
  have hMR := grayChargedV2_leaf2_reserve_mass_ge reserves hunit I hInodup
  -- hc_I_lo
  have hc_I_lo := grayChargedV2_leaf2_quarter replay reserves hcoverBack
    hcover hcoordNodup I hInodup hIlt
  refine grayChargedV2_reserve_deficit_closes hkappa heps ?_ ?_ hMR hDI_up
    hDIc_lo hc_I_lo hmI hEbound
  · ring
  · ring

/-- **Leaf-2 pointwise assembly**: for a fixed root sublist `I`, the source
subfamily bound `(S)` and the owner-restricted reserve deficit `(R_I)`
combine via `grayChargedV2_h4_assemble` into the hereditary H4 inequality
for the composed charge `source ++ reserve`. -/
theorem grayChargedV2_l5subfamily_pointwise
    {q L e n : Nat} (move : FamilyClientMove)
    (source reserve : FamilyGrayCharge) (I : List Nat)
    {PI P EI E : Rat}
    (hPIsum : PI + EI = totalRootRequestOnList I move)
    (hPsum : P + E = totalRootRequest n move)
    (hS : halfAmplification q * (2 * PI - P) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (source.filter fun z => decide (z.1 ∈ I)))
    (hR : (1 / 2) * (2 * PI - P) +
        (halfAmplification q + 1 / 2) * (2 * EI - E) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (reserve.filter fun z => decide (z.1 ∈ I))) :
    halfAmplification (q + 1) *
        (2 * totalRootRequestOnList I move - totalRootRequest n move) <=
      grayChargeMass (e + grayTailNewLoss q L)
        ((source ++ reserve).filter fun z => decide (z.1 ∈ I)) := by
  have hkey := grayChargedV2_h4_assemble (kappa := halfAmplification q)
    (P := P) (E := E) (PI := PI) (EI := EI)
    (MS := grayChargeMass (e + grayTailNewLoss q L)
      (source.filter fun z => decide (z.1 ∈ I)))
    (MR := grayChargeMass (e + grayTailNewLoss q L)
      (reserve.filter fun z => decide (z.1 ∈ I)))
    hS hR
  rw [halfAmplification_succ, List.filter_append, grayChargeMass_append]
  rw [hPIsum, hPsum] at hkey
  exact hkey

end Kolmogorov
