/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.OutputSet
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.AllocationLengths

/-!
# Output bounds and uniform rank descriptions

The constructed machine has exponentially bounded output sets at admissible marker
lengths. This module counts outputs from the simulation branch and from earlier,
current, and later levels, which gives `constructed_machine_exponential_output_bound`
(blueprint node `constr:smallset`). It then builds a uniform partial-recursive
enumeration of each small set, suppressing repeated outputs, and codes its elements by
their ranks, which gives `constructed_machine_uniform_rank_code` (blueprint node
`constr:rank`). These estimates supply the description bounds for the constructed
machine in the modules that import this one.
-/

namespace Kolmogorov.Milovanov

/-- The permanent graph is monotone in time, and all its entries realize their target lengths. -/
private theorem allocated_mono_and_input_length
    (P : FighterParams) (d : ℕ) (hd : 1 ≤ d) :
    (∀ t u, t ≤ u → (fighterState P d t).allocated ⊆ (fighterState P d u).allocated) ∧
      ∀ tick a, a ∈ (fighterState P d tick).allocated →
        a.input.length + 1 = a.target := by
  constructor
  · intro t u htu
    induction u, htu using Nat.le_induction with
    | base => exact fun _ h ↦ h
    | succ u htu ih =>
      intro a ha
      exact (fighter_actions_allocation_lengths
        P d (u + 1) (fighterState P d u) hd).1 (ih ha)
  · intro tick
    induction tick with
    | zero => simp [fighterState, initialFighterState]
    | succ tick ih =>
      intro a ha
      rcases (fighter_actions_allocation_lengths
        P d (tick + 1) (fighterState P d tick) hd).2 a ha with hold | hlen
      · exact ih a hold
      · exact hlen

/-- Unconditional freshness also gives injectivity on the union over all ticks. -/
private theorem injOn_input_allocated
    (P : FighterParams) (d : ℕ) (hd : 1 ≤ d) :
    Set.InjOn AllocatedDirective.input
      {a | ∃ tick, a ∈ (fighterState P d tick).allocated} := by
  intro a ha b hb heq
  obtain ⟨t, ht⟩ := ha
  obtain ⟨u, hu⟩ := hb
  have hmono := (allocated_mono_and_input_length P d hd).1
  exact List.inj_on_of_nodup_map (fighter_allocations_injective P d (max t u))
    (hmono t (max t u) (le_max_left _ _) ht)
    (hmono u (max t u) (le_max_right _ _) hu) heq

/-- Any finite collection of permanent allocations is present at one common tick. -/
private theorem exists_tick_forall_mem_allocated
    (P : FighterParams) (d : ℕ) (hd : 1 ≤ d) (s : Set AllocatedDirective)
    (hs : s.Finite) (hmem : ∀ a ∈ s, ∃ tick, a ∈ (fighterState P d tick).allocated) :
    ∃ tick, ∀ a ∈ s, a ∈ (fighterState P d tick).allocated := by
  have hmono := (allocated_mono_and_input_length P d hd).1
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha hs ih =>
    obtain ⟨t, ht⟩ := ih (fun b hb ↦ hmem b (Set.mem_insert_of_mem a hb))
    obtain ⟨u, hu⟩ := hmem a (Set.mem_insert a s)
    refine ⟨max t u, ?_⟩
    intro b hb
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact hmono u (max t u) (le_max_right _ _) hu
    · exact hmono t (max t u) (le_max_left _ _) (ht b hb)

/-- A uniform finite-tick count for any allocation class bounds its cumulative count. The
conclusion includes finiteness, so natural cardinality never hides an infinite set. -/
private theorem finite_and_ncard_allocated_filter_le
    (P : FighterParams) (d : ℕ) (hd : 1 ≤ d) (q : AllocatedDirective → Bool) (M : ℕ)
    (hbound : ∀ tick, ((fighterState P d tick).allocated.filter q).length ≤ M) :
    {a | ∃ tick, a ∈ (fighterState P d tick).allocated ∧ q a = true}.Finite ∧
      {a | ∃ tick, a ∈ (fighterState P d tick).allocated ∧ q a = true}.ncard ≤ M := by
  classical
  let A := {a | ∃ tick, a ∈ (fighterState P d tick).allocated ∧ q a = true}
  have hfinite (s : Set AllocatedDirective) (hs : s.Finite) (hsub : s ⊆ A) :
      s.ncard ≤ M := by
    obtain ⟨tick, ht⟩ := exists_tick_forall_mem_allocated
      P d hd s hs (fun a ha ↦ by obtain ⟨t, hm, _⟩ := hsub ha; exact ⟨t, hm⟩)
    let L := (fighterState P d tick).allocated.filter q
    have hsub' : s ⊆ (L.toFinset : Set AllocatedDirective) := by
      intro a ha
      obtain ⟨_, _, hq⟩ := hsub ha
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨ht a ha, hq⟩)
    calc
      s.ncard ≤ L.toFinset.card := by
        simpa only [Set.ncard_coe_finset] using
          Set.ncard_le_ncard hsub' (Finset.finite_toSet _)
      _ ≤ L.length := List.toFinset_card_le _
      _ ≤ M := hbound tick
  have hfin : A.Finite := by
    by_contra h
    obtain ⟨s, hs, hsf, hcard⟩ := Set.Infinite.exists_subset_ncard_eq h (M + 1)
    have := hfinite s hsf hs
    omega
  exact ⟨hfin, hfinite A hfin (fun _ h ↦ h)⟩

/-- Injective allocation bounds all descriptions with input length below a cutoff, across all
levels and all ticks, by the number of binary programs below that cutoff. -/
private theorem finite_and_ncard_allocated_input_length_lt_le
    (P : FighterParams) (d K : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) :
    {a | ∃ tick, a ∈ (fighterState P d tick).allocated ∧ a.input.length < K}.Finite ∧
      {a | ∃ tick, a ∈ (fighterState P d tick).allocated ∧
        a.input.length < K}.ncard ≤ 2 ^ K := by
  classical
  let A := {a | ∃ tick, a ∈ (fighterState P d tick).allocated ∧ a.input.length < K}
  let T : Set BitString := ((programsLe (K - 1)).toFinset : Set BitString)
  have hT : T.Finite := Finset.finite_toSet _
  have hmap : Set.MapsTo AllocatedDirective.input A T := by
    rintro a ⟨tick, ha, hlen⟩
    exact List.mem_toFinset.mpr (mem_programsLe _ _ (by omega))
  have hinj : Set.InjOn AllocatedDirective.input A :=
    (injOn_input_allocated P d hd).mono
      (by rintro a ⟨t, ht, _⟩; exact ⟨t, ht⟩)
  refine ⟨Set.Finite.of_injOn hmap hinj hT, ?_⟩
  calc
    A.ncard ≤ T.ncard := Set.ncard_le_ncard_of_injOn _ hmap hinj hT
    _ = (programsLe (K - 1)).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (programsLe (K - 1)).length := List.toFinset_card_le _
    _ ≤ 2 ^ K := by
      have h := length_programsLe_add_one (K - 1)
      rw [Nat.sub_add_cancel hK] at h
      omega

/-- The phase-count fuel estimate bounds all successful fuel allocations at the current level,
cumulatively over every tick, without a capacity assumption. -/
private theorem finite_and_ncard_allocated_fuel_le
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) :
    {a | ∃ tick, a ∈ (fighterState P d tick).allocated ∧
      a.level = l ∧ a.kind = .fuel}.Finite ∧
      {a | ∃ tick, a ∈ (fighterState P d tick).allocated ∧
        a.level = l ∧ a.kind = .fuel}.ncard ≤ 2 * P.c₁ * 2 ^ levelUpper l := by
  simpa only [decide_eq_true_eq] using
    finite_and_ncard_allocated_filter_le P d hd
      (fun a ↦ decide (a.level = l ∧ a.kind = .fuel)) _
      (fun tick ↦ (fighter_phase_count P d l tick).2.2)

/-- Every earlier allocation has target at most the current marker scale. The current level need
only be admissible; it need not have started a phase yet. -/
private theorem target_le_levelScale_of_level_lt
    (P : FighterParams) (d l tick : ℕ) (ha : P.Admissible d l)
    (a : AllocatedDirective) (hm : a ∈ (fighterState P d tick).allocated)
    (hlt : a.level < l) : a.target ≤ levelScale l := by
  obtain ⟨haa, hr⟩ := fighter_directive_target_ranges P d tick a hm
  have hj : 1 ≤ a.level := haa.1
  have hu := target_le_upper_add d a.level a.target a.kind hr
  have hp := fighter_previous_upper_bound a.level l hj hlt
  obtain ⟨hn, hd, _⟩ := fighter_admissible_square P d l ha
  have hpad := fighter_log_padding_bound (levelScale l) d hn hd
  omega

/-- Current dummy and payoff targets lie below the current exponential endpoint. -/
private theorem lt_levelUpper_of_targetRange_of_ne_fuel
    (P : FighterParams) (d l r : ℕ) (ha : P.Admissible d l) (kind : DirectiveKind)
    (hk : kind ≠ .fuel) (hr : FighterTargetRange d l kind r) : r < levelUpper l := by
  obtain ⟨hn, hd, _⟩ := fighter_admissible_square P d l ha
  have hb : levelRangeBound l < levelUpper l :=
    fighter_range_below_upper (levelScale l) hn ⟨2 * l, rfl⟩
  cases kind with
  | dummy =>
    have h := fighter_dummy_below_range (levelScale l) d hn hd
    change r = levelScale l + d at hr
    have hsquare : levelScale l ^ 2 ≤ levelRangeBound l := h.2
    omega
  | fuel => exact (hk rfl).elim
  | payoff => exact hr.2.trans hb

/-- Every later level's target exceeds the current description budget, for every kind. -/
private theorem levelUpper_add_lt_of_targetRange_of_lt
    (d j l r : ℕ) (hlt : l < j) (kind : DirectiveKind)
    (hr : FighterTargetRange d j kind r) : levelUpper l + d < r := by
  have hgap : levelUpper l < levelScale j := by
    change tower (2 * l + 1) < tower (2 * j)
    exact (tower_lt_tower_add_one (2 * l + 1)).trans_le (tower_le_tower (by omega))
  have hscale := levelScale_lt_levelUpper j
  cases kind <;> simp only [FighterTargetRange] at hr <;> omega

/-- A directive within the current budget is either a short input or current-level fuel. This
combines the earlier, current, and later target comparisons, without counting. -/
private theorem input_length_lt_or_level_fuel
    (P : FighterParams) (d l tick : ℕ) (hd : 1 ≤ d) (ha : P.Admissible d l)
    (a : AllocatedDirective) (hm : a ∈ (fighterState P d tick).allocated)
    (hlen : a.input.length + 1 ≤ levelUpper l + d) :
    a.input.length < levelUpper l ∨ a.level = l ∧ a.kind = .fuel := by
  have heq := (allocated_mono_and_input_length P d hd).2
    tick a hm
  have hr := (fighter_directive_target_ranges P d tick a hm).2
  rcases lt_trichotomy a.level l with hlt | heql | hgt
  · have h := target_le_levelScale_of_level_lt
      P d l tick ha a hm hlt
    have hscale := levelScale_lt_levelUpper l
    exact Or.inl (by omega)
  · by_cases hk : a.kind = .fuel
    · exact Or.inr ⟨heql, hk⟩
    · rw [heql] at hr
      have h := lt_levelUpper_of_targetRange_of_ne_fuel
        P d l a.target ha a.kind hk hr
      exact Or.inl (by omega)
  · have h := levelUpper_add_lt_of_targetRange_of_lt
      d a.level l a.target hgt a.kind hr
    omega

/-- Every bounded description uses either the padded simulation or an actual successful allocation
within the same budget. First-allocation search supplies the latter witness. -/
private theorem simple_or_exists_allocated_of_mem_fighterSmallSet
    (P : FighterParams) (d n : ℕ) (hd : 1 ≤ d) (y : BitString)
    (hy : y ∈ fighterSmallSet P d n) :
    Simple P.B.V y (2 ^ n) ∨ ∃ tick a,
      a ∈ (fighterState P d tick).allocated ∧
      a.input.length + 1 ≤ 2 ^ n + d ∧ a.output = y := by
  obtain ⟨p, hp, hprod⟩ := (simple_iff_exists_program (fighterU P d) y (2 ^ n + d)).mp hy
  change y ∈ constructed_conditional_machine P.B d (fighterG P d) (p, []) at hprod
  unfold constructed_conditional_machine at hprod
  dsimp only at hprod
  split_ifs at hprod with hs
  · left
    have hdlen : d ≤ p.length := by
      have h := congrArg List.length hs
      simp only [List.length_take, List.length_replicate] at h
      omega
    apply (simple_iff_exists_program P.B.V y (2 ^ n)).mpr
    exact ⟨p.drop d, by simp only [List.length_drop]; omega, hprod⟩
  · right
    cases p with
    | nil => simp at hprod
    | cons b p =>
      cases b with
      | false => simp at hprod
      | true =>
        change y ∈ fighterG P d p at hprod
        rw [fighterG, ite_eq_right (by omega : d ≠ 0)] at hprod
        obtain ⟨tick, _, hlookup⟩ := Part.mem_bind_iff.mp hprod
        have ho := Part.mem_ofOption.mp hlookup
        change (fighterAllocationAt P d tick p) = some y at ho
        unfold fighterAllocationAt at ho
        obtain ⟨a, hfind, hout⟩ := Option.map_eq_some_iff.mp ho
        have hm := List.mem_of_find?_eq_some hfind
        have hin : a.input = p := beq_iff_eq.mp
          (List.find?_some (p := fun a : AllocatedDirective ↦ a.input == p) hfind)
        refine ⟨tick, a, hm, ?_, hout⟩
        simpa only [hin, List.length_cons] using hp

/-- A fixed sparse-output multiplier works for the entire guarded family at admissible levels.
Blueprint node `constr:smallset`. The constant precedes both padding and level and does not
assume the large-even-padding capacity theorem. -/
theorem constructed_machine_exponential_output_bound (P : FighterParams) :
    ∃ cS : ℕ, ∀ d ≥ 1, ∀ l, P.Admissible d l →
      (fighterSmallSet P d (levelScale l)).ncard ≤ cS * 2 ^ (2 ^ levelScale l) := by
  refine ⟨2 * P.c₁ + 4, ?_⟩
  intro d hd l ha
  let S : Set BitString := {y | Simple P.B.V y (levelUpper l)}
  let A : Set AllocatedDirective := {a | ∃ tick,
    a ∈ (fighterState P d tick).allocated ∧ a.input.length < levelUpper l}
  let F : Set AllocatedDirective := {a | ∃ tick,
    a ∈ (fighterState P d tick).allocated ∧ a.level = l ∧ a.kind = .fuel}
  have hs : S.Finite := (simple_finite_card_lt P.B.V (levelUpper l)).1
  have hA := finite_and_ncard_allocated_input_length_lt_le
    P d (levelUpper l) hd (by rw [level_upper_eq]; exact Nat.one_le_pow _ _ (by decide))
  have hF := finite_and_ncard_allocated_fuel_le P d l hd
  have hsub : fighterSmallSet P d (levelScale l) ⊆
      S ∪ (AllocatedDirective.output '' A ∪ AllocatedDirective.output '' F) := by
    intro y hy
    rcases simple_or_exists_allocated_of_mem_fighterSmallSet
      P d (levelScale l) hd y hy with hsim | ⟨tick, a, hm, hlen, hout⟩
    · exact Or.inl hsim
    · have hc := input_length_lt_or_level_fuel
        P d l tick hd ha a hm hlen
      rcases hc with hshort | hfuel
      · exact Or.inr (Or.inl ⟨a, ⟨tick, hm, hshort⟩, hout⟩)
      · exact Or.inr (Or.inr ⟨a, ⟨tick, hm, hfuel⟩, hout⟩)
  have hsim : S.ncard ≤ 2 * 2 ^ levelUpper l := by
    have h := (simple_finite_card_lt P.B.V (levelUpper l)).2.le
    simpa only [simpleCount, Nat.pow_succ, Nat.mul_comm] using h
  calc
    (fighterSmallSet P d (levelScale l)).ncard ≤
        S.ncard + ((AllocatedDirective.output '' A).ncard +
          (AllocatedDirective.output '' F).ncard) :=
      (Set.ncard_le_ncard hsub
        (hs.union ((hA.1.image _).union (hF.1.image _)))).trans
          ((Set.ncard_union_le _ _).trans
            (Nat.add_le_add_left (Set.ncard_union_le _ _) _))
    _ ≤ 2 * 2 ^ levelUpper l + (2 ^ levelUpper l +
        2 * P.c₁ * 2 ^ levelUpper l) :=
      Nat.add_le_add hsim (Nat.add_le_add
        ((Set.ncard_image_le hA.1).trans hA.2)
        ((Set.ncard_image_le hF.1).trans hF.2))
    _ ≤ (2 * P.c₁ + 4) * 2 ^ (2 ^ levelScale l) := by
      rw [← level_upper_eq]
      nlinarith

/-- The directive stream and computable simulation branch uniformly define a computable evaluator
for `U_d`. -/
private lemma partrec_fighterU
    (P : FighterParams) :
    Partrec (fun input : ℕ × (BitString × BitString) ↦ fighterU P input.1 input.2) := by
  have : Partrec fun (input : ℕ × (BitString × BitString)) ↦
    bif decide (input.2.1.take input.1 = List.replicate input.1 false) then
      P.B.V (input.2.1.drop input.1, input.2.2)
    else
      match input.2.1 with | true :: p => fighterG P input.1 p | _ => Part.none := by
    apply Partrec.cond
    · have Hc : Computable fun (input : ℕ × (BitString × BitString)) ↦
          decide (input.2.1.take input.1 = List.replicate input.1 false) := by
        apply Primrec.to_comp
        apply PrimrecPred.decide (PrimrecRel.comp Primrec.eq
          (Primrec.list_take.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
          (Primrec.list_replicate.comp Primrec.fst (Primrec.const false)))
      exact Hc
    · have h1 : Computable fun (input : ℕ × (BitString × BitString)) ↦ (input.2.1.drop input.1,
      input.2.2) := by
        apply Primrec.to_comp
        apply Primrec.pair (Primrec.list_drop.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)
      exact Partrec.comp P.B.optimalV.1 h1
    · have h_match : Partrec fun (input : ℕ × (BitString × BitString)) ↦
          match input.2.1 with | true :: p => fighterG P input.1 p | _ => Part.none := by
        have : Partrec fun (input : ℕ × (BitString × BitString)) ↦
            bif decide (input.2.1.head? = some true) then
              (fun (x : ℕ × (BitString × BitString)) ↦ fighterG P x.1 x.2.1.tail) input
            else
              Part.none := by
          apply Partrec.cond
          · have Hc : Computable fun (input : ℕ × (BitString × BitString)) ↦
                decide (input.2.1.head? = some true) := by
              apply Primrec.to_comp
              apply PrimrecPred.decide (PrimrecRel.comp Primrec.eq
                (Primrec.list_head?.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const (some
                  true)))
            exact Hc
          · have h1 : Computable fun (input : ℕ × (BitString × BitString)) ↦ (input.1,
            input.2.1.tail) := by
              apply Primrec.to_comp
              apply Primrec.pair Primrec.fst (Primrec.list_tail.comp (Primrec.fst.comp Primrec.snd))
            exact Partrec.comp (fighter_directive_stream_partrec P) h1
          · exact Partrec.none
        refine Partrec.of_eq this ?_
        intro a
        dsimp only
        cases h1 : a.2.1 with
        | nil => rfl
        | cons hd tl =>
          cases hd
          · rfl
          · rfl
      exact h_match
  refine Partrec.of_eq this ?_
  intro a
  dsimp only [fighterU, constructed_conditional_machine]
  rw [Bool.cond_decide]
  rfl

/-- Extract a computable code `c` for the evaluator from the `Partrec` assumption. -/
private lemma exists_fighter_evaluator_code
    (P : FighterParams) :
    ∃ c : Nat.Partrec.Code,
      ∀ d p y, (fighterU P d (p, y)).map Encodable.encode = c.eval (Encodable.encode (d, (p, y)))
        := by
  have heval : Partrec (fun input : ℕ × (BitString × BitString) ↦ fighterU P input.1 input.2) :=
    partrec_fighterU P
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp heval
  refine ⟨c, fun d p y ↦ ?_⟩
  have h := congr_fun hc (Encodable.encode (d, (p, y)))
  simp [Encodable.encodek] at h
  exact h.symm

/-- Define a computable enumerator dovetailing `Code.evaln` runs on inputs bounded by `2^n + d`.
-/
private lemma exists_bounded_run_enumerator
    (c : Nat.Partrec.Code) :
    ∃ E' : ℕ → ℕ → ℕ → Option BitString, Computable (fun input : ℕ × ℕ × ℕ ↦ E' input.1
      input.2.1 input.2.2) ∧
      ∀ d n y, (∃ p : BitString, ∃ s : ℕ, p.length ≤ 2 ^ n + d ∧ y ∈ (Nat.Partrec.Code.evaln s c
        (Encodable.encode (d, (p, ([] : BitString))))).bind (Encodable.decode₂ BitString)) ↔ ∃ t,
        E' d n t = some y := by
  refine ⟨fun d n t ↦ (Encodable.decode (α := BitString) t.unpair.1).bind fun p ↦
    if p.length ≤ 2 ^ n + d then
      (Nat.Partrec.Code.evaln t.unpair.2 c (Encodable.encode (d, (p, ([] : BitString))))).bind
        (Encodable.decode₂ BitString)
    else none, ?_, ?_⟩
  · have hpow : Primrec₂ (fun a b : ℕ ↦ a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow
    have hp : Primrec (fun input : ℕ × ℕ × ℕ ↦
        Encodable.decode (α := BitString) input.2.2.unpair.1) :=
      Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd)))
    have hcond : PrimrecPred (fun q : (ℕ × ℕ × ℕ) × BitString ↦
        q.2.length ≤ 2 ^ q.1.2.1 + q.1.1) :=
      Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.nat_add.comp
          (hpow.comp (Primrec.const 2) (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.fst.comp Primrec.fst))
    have hs : Primrec (fun q : (ℕ × ℕ × ℕ) × BitString ↦ q.1.2.2.unpair.2) :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    have hev : Primrec (fun q : (ℕ × ℕ × ℕ) × BitString ↦
        Nat.Partrec.Code.evaln q.1.2.2.unpair.2 c
          (Encodable.encode (q.1.1, (q.2, ([] : BitString))))) :=
      Nat.Partrec.Code.primrec_evaln.comp
        ((hs.pair (Primrec.const c)).pair
          (Primrec.encode.comp
            ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.pair (Primrec.const [])))))
    have hbody : Primrec₂ (fun (input : ℕ × ℕ × ℕ) (p : BitString) ↦
        if p.length ≤ 2 ^ input.2.1 + input.1 then
          (Nat.Partrec.Code.evaln input.2.2.unpair.2 c
            (Encodable.encode (input.1, (p, ([] : BitString))))).bind (Encodable.decode₂ BitString)
        else none) :=
      Primrec.ite hcond ((Primrec.option_bind₁ Primrec.decode₂).comp hev) (Primrec.const none)
    exact (Primrec.option_bind hp hbody).to_comp
  · intro d n y
    constructor
    · rintro ⟨p, s, hlen, hy⟩
      refine ⟨Nat.pair (Encodable.encode p) s, ?_⟩
      simp only [Nat.unpair_pair, Encodable.encodek, Option.bind_some, hlen, ↓reduceIte]
      exact hy
    · rintro ⟨t, ht⟩
      dsimp only at ht
      cases hdec : Encodable.decode (α := BitString) t.unpair.1 with
      | none => rw [hdec] at ht; exact absurd ht (by simp)
      | some p =>
        rw [hdec, Option.bind_some] at ht
        by_cases hlen : p.length ≤ 2 ^ n + d
        · simp only [hlen, ↓reduceIte] at ht
          exact ⟨p, t.unpair.2, hlen, ht⟩
        · simp only [hlen, ↓reduceIte] at ht
          exact absurd ht (by simp)

/-- Establish the equivalence between bounded-run enumeration and the semantic `fighterSmallSet`.
-/
private lemma mem_small_set_iff_bounded_run
    (P : FighterParams) (c : Nat.Partrec.Code)
    (hc : ∀ d p y, (fighterU P d (p, y)).map Encodable.encode = c.eval (Encodable.encode (d, (p,
      y))))
    (d n : ℕ) (y : BitString) :
    y ∈ fighterSmallSet P d n ↔ ∃ p : BitString, ∃ s : ℕ, p.length ≤ 2 ^ n + d ∧ y ∈
      (Nat.Partrec.Code.evaln s c (Encodable.encode (d, (p, ([] : BitString))))).bind
      (Encodable.decode₂ BitString) := by
  have key : ∀ p : BitString, y ∈ fighterU P d (p, []) ↔
      ∃ s : ℕ, y ∈ (Nat.Partrec.Code.evaln s c
        (Encodable.encode (d, (p, ([] : BitString))))).bind (Encodable.decode₂ BitString) := by
    intro p
    constructor
    · intro hy
      have h1 : Encodable.encode y ∈ c.eval (Encodable.encode (d, (p, ([] : BitString)))) := by
        rw [← hc]
        exact Part.mem_map _ hy
      obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp h1
      refine ⟨s, ?_⟩
      rw [Option.mem_def] at hs ⊢
      rw [hs, Option.bind_some]
      exact Encodable.encodek₂ y
    · rintro ⟨s, hs⟩
      rw [Option.mem_def] at hs
      cases hev : Nat.Partrec.Code.evaln s c (Encodable.encode (d, (p, ([] : BitString)))) with
      | none => rw [hev, Option.bind_none] at hs; exact absurd hs (by simp)
      | some m =>
        rw [hev, Option.bind_some] at hs
        have hm : Encodable.encode y = m := Encodable.mem_decode₂.mp hs
        subst hm
        have h1 := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hev)
        rw [← hc] at h1
        obtain ⟨a, ha, hae⟩ := (Part.mem_map_iff _).mp h1
        rw [Encodable.encode_injective hae] at ha
        exact ha
  have hS : y ∈ fighterSmallSet P d n ↔ Simple (fighterU P d) y (2 ^ n + d) := Iff.rfl
  rw [hS, simple_iff_exists_program]
  constructor
  · rintro ⟨p, hp, hy⟩
    obtain ⟨s, hs⟩ := (key p).mp hy
    exact ⟨p, s, hp, hs⟩
  · rintro ⟨p, s, hp, hs⟩
    exact ⟨p, hp, (key p).mpr ⟨s, hs⟩⟩

/-- Dovetail the evaluator to get an enumerator `E'` such that `y ∈ S_{n,d} ↔ ∃ t, E' d n t = some
y`. -/
private lemma exists_computable_enumerator_fighterSmallSet
    (P : FighterParams) :
    ∃ E' : ℕ → ℕ → ℕ → Option BitString, Computable (fun input : ℕ × ℕ × ℕ ↦ E' input.1
      input.2.1 input.2.2) ∧
      ∀ d n y, y ∈ fighterSmallSet P d n ↔ ∃ t, E' d n t = some y := by
  obtain ⟨c, hc⟩ := exists_fighter_evaluator_code P
  obtain ⟨E', hE'_comp, hE'_enum⟩ := exists_bounded_run_enumerator c
  refine ⟨E', hE'_comp, fun d n y ↦ ?_⟩
  rw [mem_small_set_iff_bounded_run P c hc d n y]
  exact hE'_enum d n y

private def distinctOutputSearch
    (E' : ℕ → ℕ → ℕ → Option BitString) (dni : ℕ × ℕ × ℕ) : Part BitString :=
  let d := dni.1
  let n := dni.2.1
  let i := dni.2.2
  (Nat.rfind (fun t ↦ Part.some (decide (i < ((List.range t).filterMap (E' d
    n)).eraseDups.length)))).map
    (fun t ↦ (((List.range t).filterMap (E' d n)).eraseDups.getD i []))

/-- The distinct outputs seen before a given stage form a computable list. -/
private lemma distinct_outputs_computable (E' : ℕ → ℕ → ℕ → Option BitString)
    (hE' : Computable (fun input : ℕ × ℕ × ℕ ↦ E' input.1 input.2.1 input.2.2)) :
    Computable (fun p : ℕ × ℕ × ℕ ↦
      ((List.range p.2.2).filterMap (E' p.1 p.2.1)).eraseDups) := by
  have hmap : Computable (fun p : ℕ × ℕ × ℕ ↦
      (List.range p.2.2).map (E' p.1 p.2.1)) :=
    Computable.list_map
      (Primrec.list_range.to_comp.comp (Computable.snd.comp Computable.snd))
      (hE'.comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)))
  have hfilter : Primrec (fun l : List (Option BitString) ↦ l.filterMap id) :=
    Primrec.listFilterMap Primrec.id Primrec.snd
  exact (CodedFiniteDistribution.eraseDups_bitstring_primrec.to_comp.comp
    (hfilter.to_comp.comp hmap)).of_eq (fun p ↦ by
      simp only [List.filterMap_map, Function.comp_def, id_eq])

/-- The distinct output search function is partial recursive. -/
private lemma distinct_output_search_partrec (E' : ℕ → ℕ → ℕ → Option BitString)
    (hE' : Computable (fun input : ℕ × ℕ × ℕ ↦ E' input.1 input.2.1 input.2.2)) :
    Partrec (distinctOutputSearch E') := by
  have hd : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ ↦ p.1.1) :=
    Computable.fst.comp Computable.fst
  have hn : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ ↦ p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hargs : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ ↦ (p.1.1, p.1.2.1, p.2)) :=
    hd.pair (hn.pair Computable.snd)
  have hstage : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ ↦
      ((List.range p.2).filterMap (E' p.1.1 p.1.2.1)).eraseDups) :=
    ((distinct_outputs_computable E' hE').comp hargs).of_eq (fun _ ↦ rfl)
  have hindex : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ ↦ p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have htest : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ ↦
      decide (p.1.2.2 <
        ((List.range p.2).filterMap (E' p.1.1 p.1.2.1)).eraseDups.length)) :=
    Primrec.nat_lt.decide.to_comp.comp hindex (Computable.list_length.comp hstage)
  exact Partrec.map (Partrec.rfind htest.partrec.to₂)
    (((Primrec.list_getD ([] : BitString)).to_comp.comp hstage hindex).to₂)

/-- Stage lists have exact membership, no duplicates, and preserve prefixes. -/
private lemma distinct_stages_spec
    (f : ℕ → Option BitString) :
    let L := fun t ↦ ((List.range t).filterMap f).eraseDups
    (∀ t, (L t).Nodup) ∧
    (∀ t y, y ∈ L t ↔ ∃ s, s < t ∧ f s = some y) ∧
    (∀ s t, s ≤ t → L s <+: L t) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact Kolmogorov.nodup_eraseDups_list _
  · intro t y
    simp only [Kolmogorov.mem_eraseDups_list,
      List.mem_filterMap, List.mem_range]
  · intro s t hst
    induction hst with
    | refl => exact List.prefix_refl _
    | step _ ih =>
      apply List.IsPrefix.trans ih
      rw [List.range_succ, List.filterMap_append,
        List.eraseDups_append]
      exact List.prefix_append _ _

/-- Least-stage search returns an available entry of a prefix-preserving sequence. -/
private lemma getD_mem_distinct_search
    (L : ℕ → List BitString)
    (hmono : ∀ s t, s ≤ t → L s <+: L t)
    (t i : ℕ) (hi : i < (L t).length) :
    (L t).getD i [] ∈
      (Nat.rfind (fun u ↦ Part.some (decide (i < (L u).length)))).map
        (fun u ↦ (L u).getD i []) := by
  classical
  have hex : ∃ u, i < (L u).length := ⟨t, hi⟩
  let u := Nat.find hex
  rw [Part.mem_map_iff]
  refine ⟨u, ?_, ?_⟩
  · apply Nat.mem_rfind.mpr
    constructor
    · exact ⟨trivial, decide_eq_true (Nat.find_spec hex)⟩
    · intro m hm
      exact ⟨trivial, decide_eq_false (Nat.find_min hex hm)⟩
  · have hu : u ≤ t := Nat.find_le hi
    obtain ⟨r, hr⟩ := hmono u t hu
    have h_len : i < (L u).length := Nat.find_spec hex
    rw [← hr]
    exact (List.getD_append (L u) r [] i h_len).symm

/-- The distinct output search function maps exactly the elements of the small set to bounded
ranks. -/
private lemma mem_fighterSmallSet_iff_exists_rank_lt_ncard
    (P : FighterParams)
    (E' : ℕ → ℕ → ℕ → Option BitString)
    (hE'_eq : ∀ d n y, y ∈ fighterSmallSet P d n ↔ ∃ t, E' d n t = some y) :
    ∀ d n y, y ∈ fighterSmallSet P d n ↔
      ∃ i : ℕ, i < (fighterSmallSet P d n).ncard ∧
        y ∈ distinctOutputSearch E' (d, n, i) := by
  classical
  intro d n y
  let L := fun t ↦ ((List.range t).filterMap (E' d n)).eraseDups
  obtain ⟨hnd, hm, hmono⟩ :=
    distinct_stages_spec
      (E' d n)
  have hsub : ∀ t, ∀ z ∈ L t, z ∈ fighterSmallSet P d n := by
    intro t z hz
    obtain ⟨s, _, hs⟩ := (hm t z).mp hz
    exact (hE'_eq d n z).mpr ⟨s, hs⟩
  constructor
  · intro hy
    obtain ⟨s, hs⟩ := (hE'_eq d n y).mp hy
    have hyL : y ∈ L (s + 1) :=
      (hm (s + 1) y).mpr ⟨s, Nat.lt_succ_self s, hs⟩
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hyL
    have hcard : (L (s + 1)).length ≤
        (fighterSmallSet P d n).ncard := by
      have h := Set.ncard_le_ncard
        (s := ((L (s + 1)).toFinset : Set BitString))
        (t := fighterSmallSet P d n)
        (by
          intro z hz
          exact hsub (s + 1) z (by simpa using hz))
        (constructed_machine_output_set_finite P d n)
      have h_card := List.toFinset_card_of_nodup (hnd (s + 1))
      have h_ncard : Set.ncard (↑(L (s + 1)).toFinset : Set BitString) = (L (s +
        1)).toFinset.card := by
        exact Set.ncard_coe_finset (L (s + 1)).toFinset
      rw [h_ncard, h_card] at h
      exact h
    refine ⟨i, lt_of_lt_of_le hi hcard, ?_⟩
    have hout :=
      getD_mem_distinct_search
        L hmono (s + 1) i hi
    have hget : (L (s + 1)).getD i [] = y :=
      (List.getD_eq_getElem _ _ hi).trans heq
    rw [hget] at hout
    exact hout
  · rintro ⟨i, _, hy⟩
    change y ∈ (Nat.rfind
      (fun t ↦ Part.some (decide (i < (L t).length)))).map
        (fun t ↦ (L t).getD i []) at hy
    obtain ⟨t, ht, heq⟩ := (Part.mem_map_iff _).mp hy
    have hi : i < (L t).length := by
      simpa using (Nat.mem_rfind.mp ht).1
    apply hsub t y
    rw [← heq, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi

/-- Dovetails bounded-length programs for `U_d` and suppresses duplicate outputs in discovery
order, providing bounded-rank coverage into the small set. -/
private lemma exists_partrec_rank_enumerator
    (P : FighterParams) :
    ∃ E : (ℕ × ℕ × ℕ) →. BitString, Partrec E ∧
      ∀ d n y, y ∈ fighterSmallSet P d n ↔
        ∃ i : ℕ, i < (fighterSmallSet P d n).ncard ∧
          y ∈ E (d, n, i) := by
  obtain ⟨E', hE', hE'_eq⟩ :=
    exists_computable_enumerator_fighterSmallSet P
  exact ⟨distinctOutputSearch E', distinct_output_search_partrec E' hE',
    mem_fighterSmallSet_iff_exists_rank_lt_ncard P E' hE'_eq⟩

/-- Parses the canonical first field using `decodeNat`, computes `N := r.length - a`, recovers `n`
using `Nat.log2 N`, and invokes the enumerator `E`. -/
private lemma exists_partrec_rank_decoder
    (E : (ℕ × ℕ × ℕ) →. BitString) (hE : Partrec E)
    (a : ℕ) :
    ∃ f : (BitString × BitString) →. BitString, Partrec f ∧
      ∀ (d n : ℕ) (r : BitString),
        r.length = 2 ^ n + a →
        f (bits d, r) = E (d, n, decodeBits r) := by
  let f : (BitString × BitString) →. BitString := fun (w, r) ↦
    (Part.ofOption (Milovanov.decodeNat w)).bind fun d ↦
    E (d, Nat.log2 (r.length - a), decodeBits r)
  use f
  constructor
  · apply Partrec.bind
    · exact Computable.ofOption (bits_computable.2.comp Computable.fst)
    exact hE.comp <| Computable.pair Computable.snd <|
      Computable.pair
        ((NatLog.nat_log2_primrec.comp (Primrec.nat_sub.comp
            (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.const a))).to_comp)
        (decodeBits_computable.comp (Computable.snd.comp Computable.fst))
  · intro d n r hr
    have h_dec : Milovanov.decodeNat (bits d) = some d := decodeNat_bits d
    dsimp [f]
    rw [h_dec]
    simp [hr]

/-- Shows that any integer `i < 2^m` can be represented as a bitstring of exactly length `m` under
`decodeBits`. -/
private lemma exists_bits_of_lt_two_pow
    (m i : ℕ) (hi : i < 2 ^ m) :
    ∃ r : BitString, r.length = m ∧ decodeBits r = i := by
  induction m generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact ⟨[], rfl, rfl⟩
  | succ m ih =>
    have hi_div : i / 2 < 2 ^ m := by
      have h1 : 2 ^ (m + 1) = 2 ^ m * 2 := by ring
      omega
    obtain ⟨r', hr'l, hr'v⟩ := ih (i / 2) hi_div
    let b : Bool := decide (i % 2 == 1)
    use b :: r'
    constructor
    · simp [hr'l]
    · cases hb : b
      · have h0 : i % 2 = 0 := by
          have hb' : ¬(i % 2 == 1) := decide_eq_false_iff_not.mp hb
          have hb'' : i % 2 ≠ 1 := mt beq_iff_eq.mpr hb'
          omega
        rw [decodeBits, hr'v]
        omega
      · have h1 : i % 2 = 1 := by
          have hb' : (i % 2 == 1) := decide_eq_true_eq.mp hb
          exact beq_iff_eq.mp hb'
        rw [decodeBits, hr'v]
        omega

/-- Uniform fixed-length rank descriptions charge only the prefix complexity of binary padding.
Blueprint node `constr:rank`. The raw rank block recovers the scale through its length;
the compiler constant is fixed before all positive padding and admissible levels. -/
theorem constructed_machine_uniform_rank_code (P : FighterParams) :
    ∃ cRank : ℕ, ∀ d ≥ 1, ∀ l, P.Admissible d l →
      ∀ y ∈ fighterSmallSet P d (levelScale l),
        plainK P.B.V y ≤ (2 ^ levelScale l : ℕ) + KP P.B.D (bits d) [] + (cRank : ENat) := by
  obtain ⟨cS, hcS⟩ := constructed_machine_exponential_output_bound P
  let a := cS
  have hpad : cS ≤ 2 ^ a := Nat.lt_two_pow_self.le
  obtain ⟨E, hE, henum⟩ :=
    exists_partrec_rank_enumerator P
  obtain ⟨f, hf, hdec⟩ :=
    exists_partrec_rank_decoder E hE a
  obtain ⟨c, hc⟩ := plain_prefix_program_raw_suffix P.B f hf
  refine ⟨a + c, ?_⟩
  intro d hd l hl y hy
  obtain ⟨i, hi, hiy⟩ := (henum d (levelScale l) y).mp hy
  have hcap : cS * 2 ^ (2 ^ levelScale l) ≤
      2 ^ (2 ^ levelScale l + a) := by
    calc cS * 2 ^ (2 ^ levelScale l) ≤ 2 ^ a * 2 ^ (2 ^ levelScale l) := Nat.mul_le_mul_right _ hpad
      _ = 2 ^ (2 ^ levelScale l + a) := by rw [Nat.add_comm, pow_add]
  have hip := hi.trans_le ((hcS d hd l hl).trans hcap)
  obtain ⟨r, hr, hv⟩ :=
    exists_bits_of_lt_two_pow _ i hip
  have hyf : y ∈ f (bits d, r) := by
    rw [hdec d (levelScale l) r hr, hv]
    exact hiy
  simpa [KPPlain, hr, Nat.cast_add, add_assoc, add_comm,
    add_left_comm] using hc (bits d) r y hyf

end Kolmogorov.Milovanov
