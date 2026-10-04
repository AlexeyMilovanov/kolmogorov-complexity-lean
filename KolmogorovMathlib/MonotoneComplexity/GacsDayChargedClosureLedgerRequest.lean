import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureLedger

/-!
# The frozen-ledger request arithmetic of the charged Gacs-Day closure

This file supplies the arithmetic half of H5 for the recursive part of the
charged final charge.  Three independent facts are combined:

* summing the son bases of one outer root recovers exactly the total displayed
  request of all frozen ledger entries owned by that root;
* a spend pass never plants a recursive call under a *source* son, because
  `grayChargedSparePairs` drops the first `source` sons, so the source-son base
  of the full charged controller is controlled by the pure advantage fold and
  is bounded by one reserve scale;
* hence the charged root request dominates the total son base of its root.

Together with `grayChargedFrozenSources_perRoot_mass_le` this gives the H5
per-root cap for the recursive half of the final charge.
-/

namespace Kolmogorov

open scoped BigOperators

/-! ## Step 6 (H5 arithmetic): the frozen-ledger request summation

The remaining ingredient of H5 is purely arithmetic: the displayed recursive
requests of all frozen slots owned by one outer root must be bounded by that
root's final displayed request.  The three lemmas below carry this out
exactly, leaving only the source-son raise bound (`hraise`) as an explicit
hypothesis. -/

/-- A rational-valued sum over a flattened list is the sum of the sums over its parts. -/
lemma sum_map_flatMap_rat {alpha beta : Type _} (l : List alpha)
    (f : alpha -> List beta) (g : beta -> Rat) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- A rational-valued list sum can be written as a sum over the index type `Fin l.length`. -/
lemma sum_map_eq_sum_finRange_rat {alpha : Type _} (l : List alpha)
    (g : alpha -> Rat) :
    (l.map g).sum = ∑ k : Fin l.length, g l[k.val] :=
  (Fin.sum_univ_fun_getElem l g).symm

/-- A rational-valued sum over `List.ofFn F` is the sum of `g (F j)` over all indices `j`. -/
lemma sum_map_ofFn_rat {beta : Type _} {m : Nat} (F : Fin m -> beta)
    (g : beta -> Rat) :
    ((List.ofFn F).map g).sum = ∑ j : Fin m, g (F j) := by
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- Summing the son bases of one root recovers the total displayed request of
all ledger entries owned by that root. -/
lemma grayTailSonBase_sum_over_sons {n b : Nat}
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n) :
    ∑ c : Fin b, grayTailSonBase entries i c =
      (entries.map fun p => if p.1.1 = i then getReq p.2 [] else 0).sum := by
  induction entries with
  | nil => simp [grayTailSonBase]
  | cons p es ih =>
      have hstep : forall c : Fin b, grayTailSonBase (p :: es) i c =
          (if p.1.1 = i ∧ p.1.2.1 = c then getReq p.2 [] else 0)
            + grayTailSonBase es i c := by
        intro c
        unfold grayTailSonBase
        simp only [List.foldr_cons]
        split_ifs with h
        · rfl
        · rw [zero_add]
      simp only [hstep, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons]
      congr 1
      by_cases hp : p.1.1 = i
      · simp [hp, Finset.sum_ite_eq]
      · simp [hp]

/-- The owner-`i` part of the frozen ledger, re-indexed by accepted round and
slot. -/
lemma grayTailFrozenEntries_owner_sum {n b : Nat}
    (frozen : GrayTailFrozen n b) (i : Fin n) :
    ((grayTailFrozenEntries frozen).map fun p =>
        if p.1.1 = i then getReq p.2 [] else 0).sum =
      ∑ k : Fin frozen.length, ∑ j : Fin (frozen[k.val]).slots.length,
        (if ((frozen[k.val]).slots.get j).1 = i then
          getFamilyReq (frozen[k.val]).move j.val [] else 0) := by
  rw [grayTailFrozenEntries, sum_map_flatMap_rat, sum_map_eq_sum_finRange_rat]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [grayTailSlotEntries, sum_map_ofFn_rat]
  rfl

/-- With the source-son raise bound in place, the charged root request
dominates the total son base of that root. -/
lemma grayTailSonBase_sum_le_grayChargedRootRequest {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n)
    (hraise : forall c : Fin b, c.val < source ->
      threshold < grayTailSonBase entries i c ->
        grayTailSonBase entries i c <= eps) :
    ∑ c : Fin b, grayTailSonBase entries i c <=
      grayChargedRootRequest source threshold eps entries i := by
  refine Finset.sum_le_sum ?_
  intro c _
  unfold grayChargedSonRequest grayTailSonRequest
  by_cases hc : c.val < source
  · rw [ite_eq_left hc]
    by_cases ht : threshold < grayTailSonBase entries i c
    · simpa [ht] using hraise c hc ht
    · simp [ht]
  · rw [ite_eq_right hc]

/-! ## Spend rounds occupy only spare sons

Every spend pass draws its slots from `grayChargedSparePairs`, which begins by
dropping the first `source` sons.  Hence no spend round ever plants a recursive
call under a *source* son.  This is what lets the frozen source-son base of the
full charged controller be controlled by the pure advantage fold. -/

/-- Every slot opened by a spend pass sits in the spare range of children. -/
lemma grayChargedSpendSlots_spare {n b source count pass : Nat}
    {threshold eps alpha : Rat} {frozen : GrayTailFrozen n b}
    {s : GrayTailSlot n b}
    (hs : s ∈ grayChargedSpendSlots (n := n) (b := b) source count pass
      threshold eps alpha frozen) : source <= s.2.1.val := by
  rw [grayChargedSpendSlots, List.mem_flatMap] at hs
  obtain ⟨i, -, hs⟩ := hs
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  exact grayChargedSpendPairs_first_ge hp

/-- Every slot the controller opens in a spend pass sits in the spare range of children, above
`grayChargedSourceCount a e`. -/
lemma grayChargedSlotsForPass_spare {n b q a e pass : Nat}
    {frozen : GrayTailFrozen n b} {s : GrayTailSlot n b}
    (hs : s ∈ grayChargedSlotsForPass (n := n) (b := b) q a e pass frozen) :
    grayChargedSourceCount a e <= s.2.1.val :=
  grayChargedSpendSlots_spare hs

/-- One controller step preserves "every active spend slot sits under a spare
son". -/
lemma grayChargedStep_spend_slots_spare {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedState n b) (m : FamilyServerMove)
    (hprev : forall pass, st.phase = .spend pass ->
      forall s, s ∈ st.core.slots -> grayChargedSourceCount a e <= s.2.1.val) :
    forall pass, (grayChargedStep q L a e sigma A st m).phase = .spend pass ->
      forall s, s ∈ (grayChargedStep q L a e sigma A st m).core.slots ->
        grayChargedSourceCount a e <= s.2.1.val := by
  intro pass
  simp only [grayChargedStep]
  split
  · exact hprev pass
  · split
    · simp only [grayChargedStartSpend]
      split
      · simp
      · intro _ s hs
        exact grayChargedSlotsForPass_spare hs
    · simp
  · rename_i pass' heq
    split
    · simp
    · split
      · split
        · split
          · simp
          · intro _ s hs
            exact grayChargedSlotsForPass_spare hs
        · simp
      · intro _ s hs
        exact hprev pass' heq s hs

/-- Every active spend slot of the charged controller sits under a spare son. -/
lemma grayChargedStateAt_spend_slots_spare {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    forall pass, (grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm t).phase = .spend pass ->
      forall s, s ∈ (grayChargedStateAt (n := n) (b := b)
          q L a e sigma A sm t).core.slots ->
        grayChargedSourceCount a e <= s.2.1.val := by
  induction t with
  | zero =>
      intro pass hphase
      simp [grayChargedStateAt, grayChargedFold, grayChargedInitialState]
        at hphase
  | succ t ih =>
      rw [grayChargedStateAt_succ]
      exact grayChargedStep_spend_slots_spare q L a e sigma A _ (sm t) ih


/-! ## The frozen source-son base of the charged controller

Because spend rounds never touch a source son, the source-son base of the full
charged controller is controlled by the pure advantage fold, for which
`grayChargedTail_all_frozen_base_le_stateAt` already gives the reserve-scale
bound.  This discharges the raise side condition of the H5 arithmetic. -/

/-- Freezing a round that holds no key at `(i, c)` preserves the bound `dyadicScale e` on the
frozen son base at that coordinate. -/
lemma grayCharged_frozen_append_source_sonBase_le {n b e : Nat}
    {frozen : GrayTailFrozen n b} {p : GrayTailRound n b} {i : Fin n} {c : Fin b}
    (hkey : ¬ GrayTailHasKey p.slots i c)
    (hprev : grayTailFrozenSonBase frozen i c <= dyadicScale e) :
    grayTailFrozenSonBase (frozen ++ [p]) i c <= dyadicScale e := by
  rw [grayTailFrozenSonBase_append_global,
    grayTailSonBase_eq_zero_of_not_hasKey i c hkey, add_zero]
  exact hprev

/-- Every source son of the charged controller carries accumulated base at
most one reserve scale. -/
lemma grayCharged_frozen_source_sonBase_le {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    forall (i : Fin n) (c : Fin b), c.val < grayChargedSourceCount a e ->
      grayTailFrozenSonBase (grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm t).core.frozen i c <= dyadicScale e := by
  induction t with
  | zero =>
      intro i c _
      simp [grayChargedStateAt, grayChargedFold, grayChargedInitialState,
        grayChargedTailInitialState, grayTailFrozenSonBase,
        grayTailFrozenEntries, grayTailSonBase, (dyadicScale_pos e).le]
  | succ t ih =>
      intro i c hc
      rw [grayChargedStateAt_succ]
      cases hp : (grayChargedStateAt (n := n) (b := b)
          q L a e sigma A sm t).phase with
      | done =>
          rw [(grayChargedStep_done q L a e sigma A _ (sm t) hp).2]
          exact ih i c hc
      | advantage =>
          have hcore :=
            grayChargedStateAt_core_eq_tailStateAt q L a e sigma A sm t hp
          have hstep : (grayChargedStep q L a e sigma A
                (grayChargedStateAt (n := n) (b := b)
                  q L a e sigma A sm t) (sm t)).core.frozen =
              (grayChargedTailStateAt (n := n) (b := b)
                q L a e sigma A sm (t + 1)).frozen := by
            rw [grayChargedTailStateAt_succ, ← hcore]
            simp only [grayChargedStep, hp]
            split
            · exact grayChargedStartSpend_frozen q L a e A _ (sm t)
            · rfl
          rw [hstep]
          exact grayChargedTail_all_frozen_base_le_stateAt
            q L a e sigma A sm (t + 1) i c
      | spend pass =>
          have hspare :=
            grayChargedStateAt_spend_slots_spare q L a e sigma A sm t pass hp
          have hkey : ¬ GrayTailHasKey
              (grayChargedStateAt (n := n) (b := b)
                q L a e sigma A sm t).core.slots i c := by
            rintro ⟨s, hs, -, hsc⟩
            have hle := hspare s hs
            rw [hsc] at hle
            omega
          simp only [grayChargedStep, hp]
          split
          · exact ih i c hc
          · split
            · split
              · split
                · exact grayCharged_frozen_append_source_sonBase_le hkey (ih i c hc)
                · exact grayCharged_frozen_append_source_sonBase_le hkey (ih i c hc)
              · exact grayCharged_frozen_append_source_sonBase_le hkey (ih i c hc)
            · exact ih i c hc


/-- Generic form of the frozen-ledger owner summation. -/
lemma grayTailFrozenEntries_owner_sum_le_rootRequest {n b : Nat}
    (source : Nat) (threshold eps : Rat) (frozen : GrayTailFrozen n b) (i : Fin n)
    (hraise : forall c : Fin b, c.val < source ->
      grayTailSonBase (grayTailFrozenEntries frozen) i c <= eps) :
    ∑ k : Fin frozen.length, ∑ j : Fin (frozen[k.val]).slots.length,
        (if ((frozen[k.val]).slots.get j).1 = i then
          getFamilyReq (frozen[k.val]).move j.val [] else 0) <=
      grayChargedRootRequest source threshold eps
        (grayTailFrozenEntries frozen) i := by
  rw [← grayTailFrozenEntries_owner_sum, ← grayTailSonBase_sum_over_sons]
  exact grayTailSonBase_sum_le_grayChargedRootRequest _ _ _ _ i
    (fun c hc _ => hraise c hc)

/-- **Step 6 (H5 arithmetic).**  The total displayed recursive request of all
frozen slots owned by one outer root is at most that root's final displayed
request.  No side condition is needed: the source-son raise bound is supplied
by `grayCharged_frozen_source_sonBase_le`. -/
theorem grayCharged_frozen_owner_request_sum_le_final_root
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U) (i : Fin n) :
    ∑ k : Fin (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen.length,
        ∑ j : Fin ((grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen[k.val]).slots.length,
          (if (((grayChargedRunState q L a e n sigma A sm
              (T + 1)).core.frozen[k.val]).slots.get j).1 = i then
            getFamilyReq ((grayChargedRunState q L a e n sigma A sm
              (T + 1)).core.frozen[k.val]).move j.val []
          else 0) <=
      getFamilyReq (grayChargedRunMove q L a e n sigma A sm U) i.val [] := by
  rw [grayChargedRunMove_root_eq_of_done (replay.done_stable U hU).1,
    (replay.done_stable U hU).2]
  exact grayTailFrozenEntries_owner_sum_le_rootRequest _ _ _ _ i
    (fun c hc => grayCharged_frozen_source_sonBase_le
      q L a e sigma A sm (T + 1) i c hc)

/-- **Step 6, H5 for the recursive half of the final charge.**  Combining the
per-root geometric split with the frozen-ledger request arithmetic, the mass of
the recursive ledger at every outer root is bounded by four amplified units of
that root's final displayed request. -/
theorem grayChargedFrozenSources_perRoot_cap
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth)
    (phase : Nat -> GrayChargedSourcePhase) (i : Fin n) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i.val (grayChargedSourceCharge
          (grayChargedFrozenSources hsm replay hU hae hfineAll phase))) <=
      4 * halfAmplification q *
        getFamilyReq (grayChargedRunMove q L a e n sigma A sm U) i.val [] := by
  refine le_trans
    (grayChargedFrozenSources_perRoot_mass_le hsm replay hU hae hfineAll
      phase i.val) ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (by norm_num) (halfAmplification_pos q).le)
  simp only [Fin.val_inj]
  exact grayCharged_frozen_owner_request_sum_le_final_root replay hU i

end Kolmogorov
