import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport.SourceLedger
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport.Reserves
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReserveSupport

/-!
# Reserve complements `K(z)` (blueprint D2, the literal prescription)

The reserve contribution of one resolved son is the depth-`D` cylinder of
its reserve MINUS the owner-window cells (the son's own last-call charges
inside the cylinder).  Removing the window costs at most the window's
dyadic mass, so one coarse unit minus the audited `ε/6` — at least
`(5/6)ε` — survives; and every kept cell is, by construction, incomparable
with every owner cell.
-/

namespace Kolmogorov

/-- The complement cells: cylinder extensions avoiding the owner window. -/
def grayChargedReserveComplementV2 (i D : Nat) (R : BitString)
    (owner : FamilyGrayCharge) : FamilyGrayCharge :=
  (grayChargedReserveCylinder i D R).filter fun z =>
    !(owner.any fun u => decide (u.2 <+: z.2))

/-- The complement of the owner charge inside a reserve cylinder is a sublist of that cylinder. -/
lemma grayChargedReserveComplementV2_sublist (i D : Nat) (R : BitString)
    (owner : FamilyGrayCharge) :
    (grayChargedReserveComplementV2 i D R owner).Sublist
      (grayChargedReserveCylinder i D R) :=
  List.filter_sublist

/-- Every cell of the complement is owned by the client it was built for. -/
lemma grayChargedReserveComplementV2_owner {i D : Nat} {R : BitString}
    {owner : FamilyGrayCharge} {z : Nat × BitString}
    (hz : z ∈ grayChargedReserveComplementV2 i D R owner) : z.1 = i :=
  grayChargedReserveCylinder_owner
    ((grayChargedReserveComplementV2_sublist i D R owner).mem hz)

/-- The cells listed by the complement are pairwise distinct. -/
lemma grayChargedReserveComplementV2_nodup (i D : Nat) (R : BitString)
    (owner : FamilyGrayCharge) :
    ((grayChargedReserveComplementV2 i D R owner).map Prod.snd).Nodup :=
  (grayChargedReserveCylinder_nodup i D R).sublist
    ((grayChargedReserveComplementV2_sublist i D R owner).map _)

/-- **Every kept cell avoids every owner cell** (the checkpoint payoff). -/
lemma grayChargedReserveComplementV2_avoids {i D : Nat} {R : BitString}
    {owner : FamilyGrayCharge} {z : Nat × BitString}
    (hz : z ∈ grayChargedReserveComplementV2 i D R owner)
    {u : Nat × BitString} (hu : u ∈ owner) :
    ¬ u.2 <+: z.2 := by
  have hkeep := List.of_mem_filter hz
  rw [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at hkeep
  have := hkeep u hu
  simpa using this

/-- Filtered/negated lengths partition the list. -/
lemma grayCharged_length_filter_split {alpha : Type _}
    (l : List alpha) (p : alpha -> Bool) :
    l.length = (l.filter p).length +
      (l.filter fun a => !(p a)).length := by
  exact List.length_eq_length_filter_add p

/-- A disjunction filter is dominated by the two separate filters. -/
lemma grayCharged_length_filter_or_le {alpha : Type _}
    (l : List alpha) (p1 p2 : alpha -> Bool) :
    (l.filter fun x => p1 x || p2 x).length <=
      (l.filter p1).length + (l.filter p2).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases h1 : p1 x <;> cases h2 : p2 x <;>
        simp [h1, h2] <;> omega

/-- Cylinder cells extending one string `u` number at most `2^{D−|u|}`. -/
lemma grayChargedReserveCylinder_filter_prefix_le
    (i D : Nat) (R : BitString) (u : BitString)
    (hRD : R.length <= D) :
    ((grayChargedReserveCylinder i D R).filter fun z =>
      decide (u <+: z.2)).length <= 2 ^ (D - u.length) := by
  classical
  set l := (grayChargedReserveCylinder i D R).filter fun z =>
    decide (u <+: z.2) with hl
  have hsub : l.Sublist (grayChargedReserveCylinder i D R) := by
    rw [hl]
    exact List.filter_sublist
  have hnodup : (l.map Prod.snd).Nodup :=
    (grayChargedReserveCylinder_nodup i D R).sublist (hsub.map _)
  have hlen : forall z, z ∈ l -> z.2.length = D := by
    intro z hz
    have hmem := hsub.mem hz
    rw [grayChargedReserveCylinder, List.mem_map] at hmem
    obtain ⟨s, hs, rfl⟩ := hmem
    have hslen : s.length = D - R.length := (mem_allStrings _ _).mp hs
    simp only [List.length_append, hslen]
    omega
  have hinj : (l.map fun z => z.2.drop u.length).Nodup := by
    rw [show (l.map fun z => z.2.drop u.length) =
        (l.map Prod.snd).map (fun s => s.drop u.length) by
      rw [List.map_map]
      rfl]
    refine List.Nodup.map_on ?_ hnodup
    intro s hs s2 hs2 hdrop
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hs
    obtain ⟨z2, hz2, rfl⟩ := List.mem_map.mp hs2
    have hpz : u <+: z.2 := by
      have := List.of_mem_filter hz
      simpa using this
    have hpz2 : u <+: z2.2 := by
      have := List.of_mem_filter hz2
      simpa using this
    obtain ⟨t1, ht1⟩ := hpz
    obtain ⟨t2, ht2⟩ := hpz2
    rw [← ht1, ← ht2]
    rw [← ht1, ← ht2] at hdrop
    rw [List.drop_left' rfl, List.drop_left' rfl] at hdrop
    rw [hdrop]
  have hmem : forall s, s ∈ l.map (fun z => z.2.drop u.length) ->
      s ∈ allStrings (D - u.length) := by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hs
    rw [mem_allStrings]
    rw [List.length_drop, hlen z hz]
  calc l.length = (l.map fun z => z.2.drop u.length).length := by
        rw [List.length_map]
    _ <= (allStrings (D - u.length)).length := by
        have hsub2 : (l.map fun z => z.2.drop u.length).toFinset ⊆
            (allStrings (D - u.length)).toFinset := by
          intro s hs
          rw [List.mem_toFinset] at hs ⊢
          exact hmem s hs
        have hcard := Finset.card_le_card hsub2
        rw [List.toFinset_card_of_nodup hinj] at hcard
        calc (l.map fun z => z.2.drop u.length).length <=
            (allStrings (D - u.length)).toFinset.card := hcard
          _ <= (allStrings (D - u.length)).length :=
            List.toFinset_card_le _
    _ = 2 ^ (D - u.length) := length_allStrings _

/-- The union bound for the owner-window filter. -/
lemma grayChargedReserveCylinder_filter_any_le
    (i D : Nat) (R : BitString) (owner : FamilyGrayCharge)
    (hRD : R.length <= D) :
    ((grayChargedReserveCylinder i D R).filter fun z =>
      owner.any fun u => decide (u.2 <+: z.2)).length <=
      (owner.map fun u => 2 ^ (D - u.2.length)).sum := by
  induction owner with
  | nil => simp
  | cons u rest ih =>
      have hstep := grayCharged_length_filter_or_le
        (grayChargedReserveCylinder i D R)
        (fun z => decide (u.2 <+: z.2))
        (fun z => rest.any fun w => decide (w.2 <+: z.2))
      have hone := grayChargedReserveCylinder_filter_prefix_le
        i D R u.2 hRD
      rw [List.map_cons, List.sum_cons]
      calc ((grayChargedReserveCylinder i D R).filter fun z =>
          (u :: rest).any fun w => decide (w.2 <+: z.2)).length =
          ((grayChargedReserveCylinder i D R).filter fun z =>
            decide (u.2 <+: z.2) ||
              rest.any fun w => decide (w.2 <+: z.2)).length := by
            congr 1
        _ <= _ + _ := hstep
        _ <= 2 ^ (D - u.2.length) +
            (rest.map fun w => 2 ^ (D - w.2.length)).sum :=
          Nat.add_le_add hone ih

/-- **The kept count dominates the cylinder minus the window.** -/
theorem grayChargedReserveComplementV2_length_ge
    (i D : Nat) (R : BitString) (owner : FamilyGrayCharge)
    (hRD : R.length <= D) :
    (grayChargedReserveCylinder i D R).length <=
      (grayChargedReserveComplementV2 i D R owner).length +
      (owner.map fun u => 2 ^ (D - u.2.length)).sum := by
  have hsplit := grayCharged_length_filter_split
    (grayChargedReserveCylinder i D R)
    (fun z => !(owner.any fun u => decide (u.2 <+: z.2)))
  have hnotnot : ((grayChargedReserveCylinder i D R).filter fun z =>
      !(!(owner.any fun u => decide (u.2 <+: z.2)))).length =
      ((grayChargedReserveCylinder i D R).filter fun z =>
        owner.any fun u => decide (u.2 <+: z.2)).length := by
    congr 1
    apply List.filter_congr
    intro z _
    simp
  have hunion := grayChargedReserveCylinder_filter_any_le i D R owner hRD
  rw [hnotnot] at hsplit
  rw [grayChargedReserveComplementV2]
  omega

/-- Counting at depth `D` refines to the dyadic scale at depth `k ≤ D`. -/
lemma grayCharged_dyadic_pow_convert (k D : Nat) (hk : k <= D) :
    ((2 ^ (D - k) : Nat) : Rat) * dyadicScale D = dyadicScale k := by
  rw [dyadicScale, dyadicScale, Nat.cast_pow, Nat.cast_ofNat]
  rw [show ((1 : Rat) / 2) ^ D = ((1 : Rat) / 2) ^ (D - k) *
      ((1 : Rat) / 2) ^ k by
    rw [← pow_add]
    congr 1
    omega]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- Owner-window masses convert to depth-`D` counting units. -/
lemma grayCharged_owner_mass_convert (D : Nat) (owner : FamilyGrayCharge) :
    (forall u, u ∈ owner -> u.2.length <= D) ->
    (((owner.map fun u => 2 ^ (D - u.2.length)).sum : Nat) : Rat) *
        dyadicScale D =
      (owner.map fun u => dyadicScale u.2.length).sum := by
  induction owner with
  | nil =>
      intro _
      simp
  | cons u rest ih =>
      intro hlen
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        Nat.cast_add, add_mul,
        ih (fun w hw => hlen w (List.mem_cons_of_mem _ hw))]
      congr 1
      exact grayCharged_dyadic_pow_convert u.2.length D
        (hlen u List.mem_cons_self)

/-- **The complement mass lower bound**: one coarse unit minus the owner
window's dyadic mass. -/
theorem grayChargedReserveComplementV2_mass_ge
    (i D : Nat) (R : BitString) (owner : FamilyGrayCharge)
    (hRD : R.length <= D)
    (howner_len : forall u, u ∈ owner -> u.2.length <= D) :
    dyadicScale R.length -
        (owner.map fun u => dyadicScale u.2.length).sum <=
      grayChargeMass D (grayChargedReserveComplementV2 i D R owner) := by
  have hcount := grayChargedReserveComplementV2_length_ge i D R owner hRD
  have hposD : (0 : Rat) < dyadicScale D := by
    unfold dyadicScale
    positivity
  have hmassC : grayChargeMass D
      (grayChargedReserveComplementV2 i D R owner) =
      ((grayChargedReserveComplementV2 i D R owner).length : Rat) *
        dyadicScale D := by
    rw [grayChargeMass, grayMassOfCount, dyadicScale]
  have howner := grayCharged_owner_mass_convert D owner howner_len
  have hcylM : ((grayChargedReserveCylinder i D R).length : Rat) *
      dyadicScale D = dyadicScale R.length := by
    rw [grayChargedReserveCylinder_length]
    exact grayCharged_dyadic_pow_convert R.length D hRD
  have hcast : ((grayChargedReserveCylinder i D R).length : Rat) <=
      ((grayChargedReserveComplementV2 i D R owner).length : Rat) +
      (((owner.map fun u => 2 ^ (D - u.2.length)).sum : Nat) : Rat) := by
    rw [← Nat.cast_add]
    exact Nat.cast_le.mpr hcount
  have h1 := mul_le_mul_of_nonneg_right hcast hposD.le
  rw [add_mul, howner, hcylM, ← hmassC] at h1
  linarith

end Kolmogorov
