import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AllReduced
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2L5Leaves
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RequestWindow
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Reserves

/-!
# The subfamily bridge (leaf 2 in its named form)

`GrayChargedL5SubfamilyV2` — the hereditary bound over root sublists —
follows from per-root net facts through the machine-checked LP core: the
list-level mass and display sums are identified with the finset sums the
core speaks about, and the dyadic units are scaled out.  After this
module, leaf 2 IS the per-root class accounting.
-/

namespace Kolmogorov

/-- The fold in `totalRootRequestOnList` is the mapped sum. -/
lemma totalRootRequestOnList_eq_map_sum (I : List Nat)
    (move : FamilyClientMove) :
    totalRootRequestOnList I move =
      (I.map fun i => getFamilyReq move i []).sum := by
  induction I with
  | nil => rfl
  | cons x xs ih =>
      rw [totalRootRequestOnList, List.foldr_cons, List.map_cons,
        List.sum_cons, ← ih]
      rfl

/-- Exclusive disjunction filters split lengths exactly. -/
lemma grayCharged_length_filter_or_eq {alpha : Type _}
    (l : List alpha) (p q : alpha -> Bool)
    (h : forall x, x ∈ l -> ¬ (p x = true ∧ q x = true)) :
    (l.filter fun x => p x || q x).length =
      (l.filter p).length + (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx := h x List.mem_cons_self
      have hrest : forall y, y ∈ xs -> ¬ (p y = true ∧ q y = true) :=
        fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hIH := ih hrest
      cases hp : p x <;> cases hq : q x
      · simpa [hp, hq] using hIH
      · simp [hp, hq, hIH]
        omega
      · simp [hp, hq, hIH]
        omega
      · exact absurd ⟨hp, hq⟩ hx

/-- The per-root length decomposition of a membership filter. -/
lemma grayCharged_filter_mem_length (F : FamilyGrayCharge)
    (I : List Nat) (hnodup : I.Nodup) :
    (F.filter fun z => decide (z.1 ∈ I)).length =
      (I.map fun i => (grayChargeAtRoot i F).length).sum := by
  induction I with
  | nil => simp
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hnodup).2
      have hcongr : (F.filter fun z => decide (z.1 ∈ x :: xs)) =
          (F.filter fun z => (z.1 == x) || decide (z.1 ∈ xs)) := by
        apply List.filter_congr
        intro z _
        have hbd : (z.1 == x) = decide (z.1 = x) := by
          cases h : z.1 == x <;> simp_all
        simp [List.mem_cons, hbd]
      rw [hcongr, List.map_cons, List.sum_cons, ← ih hxs]
      rw [grayCharged_length_filter_or_eq F (fun z => z.1 == x)
        (fun z => decide (z.1 ∈ xs)) ?_]
      · rfl
      · intro z _ hcon
        have h1 : z.1 = x := by
          have := hcon.1
          simpa using this
        have h2 : z.1 ∈ xs := by
          have := hcon.2
          simpa using this
        rw [h1] at h2
        exact hx h2

/-- Charge mass is the cell count at the dyadic scale. -/
lemma grayChargeMass_eq_length (D : Nat) (F : FamilyGrayCharge) :
    grayChargeMass D F = (F.length : Rat) * dyadicScale D := by
  rw [grayChargeMass, grayMassOfCount, dyadicScale]

/-- The per-root mass decomposition of a membership filter. -/
lemma grayCharged_mass_filter_mem (D : Nat) (F : FamilyGrayCharge)
    (I : List Nat) (hnodup : I.Nodup) :
    grayChargeMass D (F.filter fun z => decide (z.1 ∈ I)) =
      (I.map fun i => grayChargeMass D (grayChargeAtRoot i F)).sum := by
  rw [grayChargeMass_eq_length, grayCharged_filter_mem_length F I hnodup]
  induction I with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        Nat.cast_add, add_mul, ih (List.nodup_cons.mp hnodup).2,
        ← grayChargeMass_eq_length]

/-- List sums over a root sublist match the finset sums over the
corresponding fibre of `Fin n`. -/
lemma grayCharged_list_filter_univ_sum {n : Nat} (I : List Nat)
    (hnodup : I.Nodup) (hlt : forall x, x ∈ I -> x < n)
    (g : Nat -> Rat) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I), g j.val) =
      (I.map g).sum := by
  classical
  induction I with
  | nil => simp
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hnodup).2
      have hxn : x < n := hlt x List.mem_cons_self
      have hsplit : Finset.univ.filter
          (fun j : Fin n => j.val ∈ x :: xs) =
          insert (⟨x, hxn⟩ : Fin n)
            (Finset.univ.filter (fun j : Fin n => j.val ∈ xs)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, List.mem_cons]
        constructor
        · rintro (h | h)
          · left
            exact Fin.ext h
          · right
            exact h
        · rintro (h | h)
          · left
            rw [h]
          · right
            exact h
      rw [hsplit, Finset.sum_insert ?_, List.map_cons, List.sum_cons,
        ih hxs (fun y hy => hlt y (List.mem_cons_of_mem _ hy))]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx

/-- **Leaf 2 from per-root nets**: the named hereditary bound
`GrayChargedL5SubfamilyV2` follows from a net rate `S ∈ [1/6, 1/2]`, the
quarter-stop on active slots, and the per-root inequality tying each
root's charge mass, display, and active count. All quantities in absolute
units; `B` is the source population per root. -/
theorem grayChargedV2_l5subfamily_of_perRoot_nets
    {q L a e n : Nat} {S : Rat}
    (hae : a <= e)
    (move : FamilyClientMove) (F : FamilyGrayCharge)
    (acts : Fin n -> Nat)
    (hS16 : 1 / 6 <= S) (hS12 : S <= 1 / 2)
    (hquarter : 4 * (∑ i : Fin n, ((acts i : Nat) : Rat)) <=
      (n : Rat) * ((grayChargedSourceCount a e : Nat) : Rat))
    (hnet : forall i : Fin n,
      ((((grayChargedSourceCount a e : Nat) : Rat) - (acts i : Rat)) * S -
        (acts i : Rat) / 2) * dyadicScale e <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i.val F) -
        halfAmplification (q + 1) * getFamilyReq move i.val [])
    (hd : forall i : Fin n,
      dyadicScale a / 2 <= getFamilyReq move i.val []) :
    GrayChargedL5SubfamilyV2 q L e n move F := by
  classical
  intro I hI
  have hIsub : I.Sublist (List.range n) := List.mem_sublists.mp hI
  have hInodup : I.Nodup := List.nodup_range.sublist hIsub
  have hIlt : forall x, x ∈ I -> x < n :=
    fun x hx => List.mem_range.mp (hIsub.subset hx)
  have heps : (0 : Rat) < dyadicScale e := dyadicScale_pos e
  have hkp : (1 : Rat) <= halfAmplification (q + 1) := by
    unfold halfAmplification
    have h0 : (0 : Rat) <= ((q + 1 : Nat) : Rat) / 2 := by positivity
    linarith
  have hbudget : ((grayChargedSourceCount a e : Nat) : Rat) *
      dyadicScale e = dyadicScale a :=
    grayCharged_dyadic_pow_convert a e hae
  -- the scaled bridge over the fibre finset
  have hbridge := grayChargedV2_subfamily_of_perRoot_nets
    (B := grayChargedSourceCount a e)
    (S := S) (kp := halfAmplification (q + 1)) acts
    (fun i => grayChargeMass (e + grayTailNewLoss q L)
      (grayChargeAtRoot i.val F) / dyadicScale e)
    (fun i => getFamilyReq move i.val [] / dyadicScale e)
    (Finset.univ.filter (fun j : Fin n => j.val ∈ I))
    hS16 hS12 hkp hquarter
    (by
      intro i
      have h1 := hnet i
      have h2 : grayChargeMass (e + grayTailNewLoss q L)
          (grayChargeAtRoot i.val F) / dyadicScale e -
          halfAmplification (q + 1) *
            (getFamilyReq move i.val [] / dyadicScale e) =
          (grayChargeMass (e + grayTailNewLoss q L)
            (grayChargeAtRoot i.val F) -
            halfAmplification (q + 1) * getFamilyReq move i.val []) /
            dyadicScale e := by
        field_simp
      rw [h2, le_div_iff₀ heps]
      exact h1)
    (by
      intro i
      rw [le_div_iff₀ heps]
      have h3 : ((grayChargedSourceCount a e : Nat) : Rat) / 2 *
          dyadicScale e = dyadicScale a / 2 := by
        rw [div_mul_eq_mul_div, hbudget]
      rw [h3]
      exact hd i)
  -- collect the divisions
  rw [show (∑ i ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
        getFamilyReq move i.val [] / dyadicScale e) =
      (∑ i ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
        getFamilyReq move i.val []) / dyadicScale e from
    (Finset.sum_div _ _ _).symm] at hbridge
  rw [show (∑ i : Fin n, getFamilyReq move i.val [] / dyadicScale e) =
      (∑ i : Fin n, getFamilyReq move i.val []) / dyadicScale e from
    (Finset.sum_div _ _ _).symm] at hbridge
  rw [show (∑ i ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
        grayChargeMass (e + grayTailNewLoss q L)
          (grayChargeAtRoot i.val F) / dyadicScale e) =
      (∑ i ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
        grayChargeMass (e + grayTailNewLoss q L)
          (grayChargeAtRoot i.val F)) / dyadicScale e from
    (Finset.sum_div _ _ _).symm] at hbridge
  -- clear the scale
  have hmul := mul_le_mul_of_nonneg_right hbridge heps.le
  have h4 : halfAmplification (q + 1) *
      (2 * ((∑ i ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
          getFamilyReq move i.val []) / dyadicScale e) -
        (∑ i : Fin n, getFamilyReq move i.val []) / dyadicScale e) *
      dyadicScale e =
      halfAmplification (q + 1) *
      (2 * (∑ i ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
          getFamilyReq move i.val []) -
        ∑ i : Fin n, getFamilyReq move i.val []) := by
    field_simp
  have h5 : ((∑ i ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i.val F)) / dyadicScale e) * dyadicScale e =
      ∑ i ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
        grayChargeMass (e + grayTailNewLoss q L)
          (grayChargeAtRoot i.val F) := by
    field_simp
  rw [h4, h5] at hmul
  -- identify the three sums with the list-level quantities
  have hId : (∑ i ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
      getFamilyReq move i.val []) = totalRootRequestOnList I move := by
    rw [totalRootRequestOnList_eq_map_sum]
    exact grayCharged_list_filter_univ_sum I hInodup hIlt
      (fun k => getFamilyReq move k [])
  have hIT : (∑ i : Fin n, getFamilyReq move i.val []) =
      totalRootRequest n move := by
    rw [totalRootRequest]
  have hIM : (∑ i ∈ Finset.univ.filter (fun j : Fin n => j.val ∈ I),
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i.val F)) =
      grayChargeMass (e + grayTailNewLoss q L)
        (F.filter fun z => decide (z.1 ∈ I)) := by
    rw [grayCharged_mass_filter_mem _ F I hInodup]
    exact grayCharged_list_filter_univ_sum I hInodup hIlt
      (fun k => grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot k F))
  rw [hId, hIT, hIM] at hmul
  exact hmul

/-- **The aggregate active-count quarter** (leaf-2 `hquarter` supplier): the
narrow terminal active slots number at most a quarter of the source
population — the global 25% stop, from the resolved-count identity and the
three-quarters estimate. Any per-root `acts` summing to this count
satisfies the LP's quarter hypothesis. -/
theorem grayChargedReplayV2_terminal_active_quarter
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    4 * (grayTailNextSlots e (grayChargedSourceCount a e)
        replay.advantageTerminal.frozen.length
        (grayChargedThreshold q e) A
        (frozenV1OfV2 replay.advantageTerminal)
        (sm replay.advantageDoneTime)).length <=
      n * grayChargedSourceCount a e := by
  have heq := grayChargedReplayV2_resolvedSourceCount_eq replay
  have hthree := grayChargedReplayV2_resolved_three_quarters replay
  omega

/-- The aggregate quarter in rational form, for any per-root split. -/
theorem grayChargedV2_perRoot_quarter_of_sum
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (acts : Fin n -> Nat)
    (hsum : (∑ i : Fin n, acts i) =
      (grayTailNextSlots e (grayChargedSourceCount a e)
        replay.advantageTerminal.frozen.length
        (grayChargedThreshold q e) A
        (frozenV1OfV2 replay.advantageTerminal)
        (sm replay.advantageDoneTime)).length) :
    4 * (∑ i : Fin n, ((acts i : Nat) : Rat)) <=
      (n : Rat) * ((grayChargedSourceCount a e : Nat) : Rat) := by
  have hq := grayChargedReplayV2_terminal_active_quarter replay
  have hcast : (∑ i : Fin n, ((acts i : Nat) : Rat)) =
      ((∑ i : Fin n, acts i : Nat) : Rat) := by
    push_cast
    rfl
  rw [hcast, hsum]
  have : 4 * (grayTailNextSlots e (grayChargedSourceCount a e)
      replay.advantageTerminal.frozen.length
      (grayChargedThreshold q e) A
      (frozenV1OfV2 replay.advantageTerminal)
      (sm replay.advantageDoneTime)).length <=
      n * grayChargedSourceCount a e := hq
  calc 4 * (((grayTailNextSlots e (grayChargedSourceCount a e)
        replay.advantageTerminal.frozen.length
        (grayChargedThreshold q e) A
        (frozenV1OfV2 replay.advantageTerminal)
        (sm replay.advantageDoneTime)).length : Nat) : Rat) =
      (((4 * (grayTailNextSlots e (grayChargedSourceCount a e)
        replay.advantageTerminal.frozen.length
        (grayChargedThreshold q e) A
        (frozenV1OfV2 replay.advantageTerminal)
        (sm replay.advantageDoneTime)).length : Nat)) : Rat) := by
        push_cast; ring
    _ <= ((n * grayChargedSourceCount a e : Nat) : Rat) := by
        exact_mod_cast this
    _ = (n : Rat) * ((grayChargedSourceCount a e : Nat) : Rat) := by
        push_cast; ring

/-- **Leaf 2 from the replay, display discharged**: the named subfamily
bound over the final charge, needing only the per-root net inequality and
the active-count quarter — the display lower bound comes from H1. -/
theorem grayChargedV2_l5subfamily_of_replay_nets
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {S : Rat}
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (F : FamilyGrayCharge)
    (acts : Fin n -> Nat)
    (hS16 : 1 / 6 <= S) (hS12 : S <= 1 / 2)
    (hquarter : 4 * (∑ i : Fin n, ((acts i : Nat) : Rat)) <=
      (n : Rat) * ((grayChargedSourceCount a e : Nat) : Rat))
    (hnet : forall i : Fin n,
      ((((grayChargedSourceCount a e : Nat) : Rat) - (acts i : Rat)) * S -
        (acts i : Rat) / 2) * dyadicScale e <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i.val F) -
        halfAmplification (q + 1) *
          getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm T)
            i.val []) :
    GrayChargedL5SubfamilyV2 q L e n
      (grayChargedRunMoveV2 q L a e n sigma A sm T) F := by
  refine grayChargedV2_l5subfamily_of_perRoot_nets hae _ F acts hS16 hS12
    hquarter hnet ?_
  intro i
  exact (grayChargedV2_final_request_window hpin hae replay.final i).1

end Kolmogorov
