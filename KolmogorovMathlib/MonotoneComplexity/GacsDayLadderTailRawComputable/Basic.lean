import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.MonotoneComplexity.GacsDayGraftComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRaw
import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustGrayComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwoComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayTailReserveComputable

/-!
# Gacs-Day ladder tail: raw computability

Computability of the anchored reserve search used by the gray-tail ladder.
-/

namespace Kolmogorov

open Encodable

/-! ### Computability of the anchored reserve search -/

/-- Prefix anchoring against a finite allocation is primitive recursive. -/
theorem primrec₂_anchorsB : Primrec₂ anchorsB := by
  refine list_any_primrec (f := fun q : List BitString × BitString => q.1)
    (p := fun q v => v.isPrefixOf q.2) Primrec.fst ?_
  exact (primrec₂_isPrefixOf_gen.comp Primrec.snd
    (Primrec.snd.comp Primrec.fst)).to₂

/-- The anchored family-reserve test is primitive recursive jointly in all
arguments. -/
theorem primrec_anchoredTailFamilyReserveAtB :
    Primrec fun x : (ℕ × ℕ) × Allocation × (ℕ × ℕ) ×
        FamilyServerMove × GacsDayNode × BitString =>
      anchoredTailFamilyReserveAtB x.1.1 x.1.2 x.2.1 x.2.2.1.1 x.2.2.1.2
        x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 := by
  set T := (ℕ × ℕ) × Allocation × (ℕ × ℕ) ×
    FamilyServerMove × GacsDayNode × BitString with hT
  have htail : Primrec fun x : T =>
      tailFamilyReserveAtB x.1.1 x.1.2 x.2.1 x.2.2.1.1 x.2.2.1.2
        x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 :=
    primrec_tailFamilyReserveAtB
  have hsm : Primrec fun x : T => x.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hi : Primrec fun x : T => x.2.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hx : Primrec fun x : T => x.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hR : Primrec fun x : T => x.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hanchor : Primrec fun x : T =>
      anchorsB (getFamilyAlloc x.2.2.2.1 x.2.2.1.2 x.2.2.2.2.1)
        x.2.2.2.2.2 :=
    primrec₂_anchorsB.comp
      (primrec_getFamilyAlloc.comp (hsm.pair (hi.pair hx))) hR
  exact ((Primrec.dom_bool₂ (fun a b => a && b)).comp htail hanchor).of_eq
    fun _ => rfl

/-- The bounded anchored reserve search is computable jointly in all
arguments. -/
theorem computable_getAnchoredTailFamilyReserve_joint :
    Computable fun x : (ℕ × ℕ) × Allocation × (ℕ × ℕ) ×
        FamilyServerMove × GacsDayNode =>
      getAnchoredTailFamilyReserve x.1.1 x.1.2 x.2.1 x.2.2.1.1 x.2.2.1.2
        x.2.2.2.1 x.2.2.2.2 := by
  have hlist : Primrec fun x : (ℕ × ℕ) × Allocation × (ℕ × ℕ) ×
      FamilyServerMove × GacsDayNode => allStrings x.1.1 :=
    CodedFiniteDistribution.allStrings_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hp : Primrec₂ fun
      (x : (ℕ × ℕ) × Allocation × (ℕ × ℕ) × FamilyServerMove × GacsDayNode)
      (R : BitString) =>
        anchoredTailFamilyReserveAtB x.1.1 x.1.2 x.2.1 x.2.2.1.1 x.2.2.1.2
          x.2.2.2.1 x.2.2.2.2 R := by
    exact (primrec_anchoredTailFamilyReserveAtB.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
            ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst)))).pair
              ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp Primrec.fst)))).pair Primrec.snd)))))).to₂
  exact (primrec_list_find? hlist hp).to_comp.of_eq fun _ => rfl

/-! ### Two small list facts -/

/-- `List.sum` on the rationals as a right fold. -/
theorem list_sum_rat_eq_foldr (l : List ℚ) :
    l.sum = l.foldr (fun x acc => x + acc) 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- Emptiness of a list as a decidable numeric test. -/
theorem list_isEmpty_eq_decide {α : Type*} (l : List α) :
    l.isEmpty = decide (l.length = 0) := by
  cases l <;> rfl

/-- Testing a computable list-valued function for emptiness is computable. -/
theorem computable_list_isEmpty {X α : Type} [Primcodable X] [Primcodable α]
    {f : X → List α} (hf : Computable f) : Computable fun x => (f x).isEmpty :=
  (((PrimrecRel.decide Primrec.eq).to_comp.comp
    (Primrec.list_length.to_comp.comp hf) (Computable.const 0))).of_eq fun _ =>
      (list_isEmpty_eq_decide _).symm

/-! ### Local copies of two small server-move combinators

The corresponding lemmas of `GacsDayEndgameCtrlComputable.lean` and
`GacsDayEndgameScheduledComputable.lean` cannot be imported here: those modules
sit *downstream* of the tail code step, so importing them would create a module
cycle.  The two statements are reproved under distinct names. -/

/-- Truncating an allocation is primitive recursive. -/
theorem primrec₂_truncAllocRaw :
    Primrec₂ fun (eps : ℕ) (alloc : Allocation) => truncAlloc eps alloc := by
  have hrel : PrimrecPred fun v : (ℕ × Allocation) × BitString => v.2.length ≤ v.1.1 :=
    Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have hpred : Primrec fun v : (ℕ × Allocation) × BitString =>
      decide (v.2.length ≤ v.1.1) := by
    obtain ⟨_, h⟩ := hrel
    exact h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl
  exact Primrec.list_filter Primrec.snd hpred.to₂

/-- Truncating a server move is primitive recursive. -/
theorem primrec₂_truncServerMoveRaw :
    Primrec₂ fun (eps : ℕ) (m : ServerMove) => truncServerMove eps m := by
  have hf : Primrec₂ fun (q : ℕ × ServerMove) (p : GacsDayNode × Allocation) =>
      ((p.1, truncAlloc q.1 p.2) : GacsDayNode × Allocation) :=
    (Primrec.fst.comp Primrec.snd).pair
      (primrec₂_truncAllocRaw.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_map Primrec.snd hf

/-- Truncating a family server move is computable. -/
theorem computable₂_truncFamilyServerMoveRaw :
    Computable₂ fun (eps : ℕ) (sm : FamilyServerMove) =>
      truncFamilyServerMove eps sm := by
  have hf : Primrec₂ fun (p : ℕ × FamilyServerMove) (m : ServerMove) =>
      truncServerMove p.1 m :=
    primrec₂_truncServerMoveRaw.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_map Primrec.snd hf).to_comp.to₂

/-- Restricting a server move to the actual branching is primitive recursive. -/
theorem primrec₂_inTreeServerMoveRaw :
    Primrec₂ fun (b : ℕ) (m : ServerMove) => inTreeServerMove b m := by
  have hrel : PrimrecPred fun v : ((ℕ × ServerMove) × (GacsDayNode × Allocation)) × ℕ =>
      v.2 < v.1.1.1 :=
    Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hpred : Primrec fun v : ((ℕ × ServerMove) × (GacsDayNode × Allocation)) × ℕ =>
      decide (v.2 < v.1.1.1) := by
    obtain ⟨_, h⟩ := hrel
    exact h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl
  have hall : Primrec fun w : (ℕ × ServerMove) × (GacsDayNode × Allocation) =>
      (w.2.1).all fun c => decide (c < w.1.1) :=
    list_all_primrec (Primrec.fst.comp Primrec.snd) hpred.to₂
  have hp : Primrec fun w : (ℕ × ServerMove) × (GacsDayNode × Allocation) =>
      decide (∀ c ∈ w.2.1, c < w.1.1) := by
    refine hall.of_eq fun w => ?_
    rw [Bool.eq_iff_iff]
    simp
  exact Primrec.list_filter Primrec.snd hp.to₂

/-- Restricting a family server move to the tree is computable. -/
theorem computable₂_inTreeFamilyServerMoveRaw :
    Computable₂ fun (b : ℕ) (sm : FamilyServerMove) =>
      inTreeFamilyServerMove b sm := by
  have hf : Primrec₂ fun (p : ℕ × FamilyServerMove) (m : ServerMove) =>
      inTreeServerMove p.1 m :=
    primrec₂_inTreeServerMoveRaw.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_map Primrec.snd hf).to_comp.to₂

/-! ### Numeric controller parameters -/

/-- The base branching of the tail is primitive recursive in its parameters. -/
theorem primrec₂_grayTailBaseBranch : Primrec₂ grayTailBaseBranch := by
  have hq1 : Primrec fun p : ℕ × ℕ => p.1 + 1 := Primrec.succ.comp Primrec.fst
  have hc : Primrec fun p : ℕ × ℕ => 256 * (p.1 + 1) :=
    Primrec.nat_mul.comp (Primrec.const 256) hq1
  have hsq : Primrec fun p : ℕ × ℕ => (p.1 + 1) ^ 2 :=
    nat_pow_primrec₂.comp hq1 (Primrec.const 2)
  have hexp : Primrec fun p : ℕ × ℕ => 256 * (p.1 + 1) ^ 2 * p.2 :=
    Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 256) hsq) Primrec.snd
  have hpow : Primrec fun p : ℕ × ℕ =>
      2 ^ (256 * (p.1 + 1) ^ 2 * p.2 + 256 * (p.1 + 1)) :=
    nat_pow_primrec₂.comp (Primrec.const 2) (Primrec.nat_add.comp hexp hc)
  exact (Primrec.nat_max.comp (Primrec.const 2)
    (Primrec.nat_mul.comp hc hpow)).of_eq fun _ => rfl

/-- The tail round count is primitive recursive in the stage. -/
theorem primrec_grayTailRoundCount : Primrec grayTailRoundCount :=
  (Primrec.nat_mul.comp (Primrec.const 256)
    (nat_pow_primrec₂.comp Primrec.succ (Primrec.const 2))).of_eq fun _ => rfl

/-- The epsilon depth of a round is computable in its parameters. -/
theorem computable_grayTailRoundEps :
    Computable fun x : ℕ × ℕ × ℕ × ℕ => grayTailRoundEps x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hq : Computable fun x : ℕ × ℕ × ℕ × ℕ => x.1 := Computable.fst
  have hL : Computable fun x : ℕ × ℕ × ℕ × ℕ => x.2.1 := Computable.fst.comp Computable.snd
  have he : Computable fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hr : Computable fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hcall := computable_grayCallDepth.comp hq he
  have hcount := primrec_grayTailRoundCount.to_comp.comp hq
  have hsub := Primrec.nat_sub.to_comp.comp
    (Primrec.nat_sub.to_comp.comp hcount (Computable.const 1)) hr
  exact (Primrec.nat_add.to_comp.comp hcall
    (Primrec.nat_mul.to_comp.comp hsub hL)).of_eq fun _ => rfl

/-- The delta depth of a round is computable in its parameters. -/
theorem computable_grayTailRoundDelta :
    Computable fun x : ℕ × ℕ × ℕ × ℕ => grayTailRoundDelta x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  (Primrec.nat_add.to_comp.comp computable_grayTailRoundEps
    (Computable.fst.comp Computable.snd)).of_eq fun _ => rfl

/-- The target floor of the tail is computable in the stage and the scale. -/
theorem computable₂_grayTailTargetFloor : Computable₂ grayTailTargetFloor := by
  have hD : Computable fun p : ℕ × ℕ => 2 ^ (p.2 + 1) * (p.1 + 3) :=
    (Primrec.nat_mul.comp
      (nat_pow_primrec₂.comp (Primrec.const 2) (Primrec.succ.comp Primrec.snd))
      (Primrec.nat_add.comp Primrec.fst (Primrec.const 3))).to_comp
  refine computable_of_num_den (N := fun _ : ℕ × ℕ => (3 : ℤ))
    (D := fun p : ℕ × ℕ => 2 ^ (p.2 + 1) * (p.1 + 3))
    (Computable.const 3) hD (fun p => by positivity) fun p => ?_
  obtain ⟨q, a⟩ := p
  have hpow : ((1 : ℚ) / 2) ^ a = 1 / (2 : ℚ) ^ a := one_div_pow 2 a
  have h2 : ((2 : ℚ)) ^ a ≠ 0 := by positivity
  have hden : (1 : ℚ) + ((q : ℚ) + 1) / 2 ≠ 0 := by positivity
  have hq3 : ((q : ℚ) + 3) ≠ 0 := by positivity
  simp only [grayTailTargetFloor, dyadicScale, halfAmplification, hpow]
  push_cast
  field_simp
  ring

/-- The list of locally allocated strings is computable in the server move. -/
theorem computable_grayTailLocalAllocatedList :
    Computable grayTailLocalAllocatedList := by
  have hl : Primrec fun m : FamilyServerMove => List.range m.length :=
    Primrec.list_range.comp Primrec.list_length
  exact ((Primrec.list_flatMap hl primrec₂_familyRootAlloc).of_eq fun _ => rfl).to_comp

/-! ### Entries -/

/-- Pairing raw slots with the rows of a family move is computable. -/
theorem computable_rawSlotEntries :
    Computable fun x : List RawSlot × FamilyClientMove => rawSlotEntries x.1 x.2 := by
  have hl : Primrec fun x : List RawSlot × FamilyClientMove => List.range x.1.length :=
    Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)
  have hg : Primrec₂ fun (x : List RawSlot × FamilyClientMove) (j : ℕ) =>
      ((x.1.getD j (0, 0, 0), familyClientMoveAt x.2 j) : RawSlot × ClientMove) :=
    ((Primrec.list_getD ((0, 0, 0) : RawSlot)).comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
      ((Primrec.list_getD ([] : ClientMove)).comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact ((Primrec.list_map hl hg).of_eq fun _ => rfl).to_comp

/-- Listing the raw slots of a round is computable in its parameters. -/
theorem computable_rawSlots :
    Computable fun x : (ℕ × ℕ) × ℕ × ℕ => rawSlots x.1.1 x.1.2 x.2.1 x.2.2 := by
  have hn : Primrec fun x : (ℕ × ℕ) × ℕ × ℕ => x.1.1 := Primrec.fst.comp Primrec.fst
  have hb : Primrec fun x : (ℕ × ℕ) × ℕ × ℕ => x.1.2 := Primrec.snd.comp Primrec.fst
  have hr : Primrec fun x : (ℕ × ℕ) × ℕ × ℕ => x.2.2 := Primrec.snd.comp Primrec.snd
  have hrel : PrimrecPred fun v : ((ℕ × ℕ) × ℕ × ℕ) × ℕ => v.2 < v.1.2.1 :=
    Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hcolpred : Primrec fun v : ((ℕ × ℕ) × ℕ × ℕ) × ℕ => decide (v.2 < v.1.2.1) := by
    obtain ⟨_, h⟩ := hrel
    exact h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl
  have hcols : Primrec fun x : (ℕ × ℕ) × ℕ × ℕ =>
      (List.range x.1.2).filter fun c => decide (c < x.2.1) :=
    Primrec.list_filter (Primrec.list_range.comp hb) hcolpred.to₂
  have hbody : Primrec₂ fun (x : (ℕ × ℕ) × ℕ × ℕ) (i : ℕ) =>
      ((List.range x.1.2).filter fun c => decide (c < x.2.1)).map
        fun c => ((i, c, x.2.2) : RawSlot) := by
    refine Primrec.list_map (hcols.comp Primrec.fst) ?_
    exact (Primrec.snd.comp Primrec.fst).pair
      (Primrec.snd.pair (hr.comp (Primrec.fst.comp Primrec.fst)))
  have hflat : Primrec fun x : (ℕ × ℕ) × ℕ × ℕ =>
      (List.range x.1.1).flatMap fun i =>
        ((List.range x.1.2).filter fun c => decide (c < x.2.1)).map
          fun c => ((i, c, x.2.2) : RawSlot) :=
    Primrec.list_flatMap (Primrec.list_range.comp hn) hbody
  exact ((Primrec.ite (Primrec.nat_lt.comp hr hb) hflat
    (Primrec.const [])).of_eq fun _ => rfl).to_comp

/-- Collecting the entries of the raw frozen rounds is computable. -/
theorem computable_rawFrozenEntries :
    Computable fun frozen : List RawRound => rawFrozenEntries frozen := by
  have hbody : Computable₂ fun (_ : List RawRound) (p : RawRound) =>
      rawSlotEntries p.2.1 p.2.2.1 :=
    (computable_rawSlotEntries.comp
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        (Computable.fst.comp (Computable.snd.comp
          (Computable.snd.comp Computable.snd))))).to₂
  exact (computable_list_flatMap Computable.id hbody).of_eq fun _ => rfl

/-- Collecting the frozen, slot and current entries of a raw state is computable. -/
theorem computable_rawEntries :
    Computable fun x : List RawRound × List RawSlot × FamilyClientMove =>
      rawEntries x.1 x.2.1 x.2.2 :=
  (Primrec.list_append.to_comp.comp (computable_rawFrozenEntries.comp Computable.fst)
    (computable_rawSlotEntries.comp Computable.snd)).of_eq fun _ => rfl

/-- The move a raw slot receives from the entries is computable. -/
theorem computable_rawEntryMove :
    Computable fun x : List (RawSlot × ClientMove) × RawSlot =>
      rawEntryMove x.1 x.2 := by
  have hrel : PrimrecPred fun z : (List (RawSlot × ClientMove) × RawSlot) ×
      (RawSlot × ClientMove) => z.2.1 = z.1.2 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  have hp0 : Primrec fun z : (List (RawSlot × ClientMove) × RawSlot) ×
      (RawSlot × ClientMove) => decide (z.2.1 = z.1.2) := by
    obtain ⟨_, h⟩ := hrel
    exact h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl
  have hp : Primrec₂ fun (x : List (RawSlot × ClientMove) × RawSlot)
      (p : RawSlot × ClientMove) => decide (p.1 = x.2) := hp0.to₂
  have hfind : Primrec fun x : List (RawSlot × ClientMove) × RawSlot =>
      x.1.find? fun p => decide (p.1 = x.2) :=
    primrec_list_find? Primrec.fst hp
  have hg : Primrec₂ fun (_ : List (RawSlot × ClientMove) × RawSlot)
      (p : RawSlot × ClientMove) => p.2 := Primrec.snd.comp Primrec.snd
  have hmap : Primrec fun x : List (RawSlot × ClientMove) × RawSlot =>
      (x.1.find? fun p => decide (p.1 = x.2)).map Prod.snd :=
    Primrec.option_map hfind hg
  exact ((Primrec.option_getD.comp hmap (Primrec.const [])).of_eq fun _ => rfl).to_comp

/-- The raw son base is computable in the entries and the coordinates. -/
theorem computable_rawSonBase :
    Computable fun x : List (RawSlot × ClientMove) × ℕ × ℕ =>
      rawSonBase x.1 x.2.1 x.2.2 := by
  have hl : Computable fun x : List (RawSlot × ClientMove) × ℕ × ℕ => x.1 := Computable.fst
  have hg : Computable fun _ : List (RawSlot × ClientMove) × ℕ × ℕ => (0 : ℚ) :=
    Computable.const 0
  have hh : Computable₂ fun (x : List (RawSlot × ClientMove) × ℕ × ℕ)
      (u : (RawSlot × ClientMove) × ℚ) =>
      if u.1.1.1 = x.2.1 ∧ u.1.1.2.1 = x.2.2 then getReq u.1.2 [] + u.2 else u.2 := by
    have hrel1 : PrimrecPred fun w : (List (RawSlot × ClientMove) × ℕ × ℕ) ×
        ((RawSlot × ClientMove) × ℚ) => w.2.1.1.1 = w.1.2.1 :=
      Primrec.eq.comp
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have hrel2 : PrimrecPred fun w : (List (RawSlot × ClientMove) × ℕ × ℕ) ×
        ((RawSlot × ClientMove) × ℚ) => w.2.1.1.2.1 = w.1.2.2 :=
      Primrec.eq.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have hd1 : Primrec fun w : (List (RawSlot × ClientMove) × ℕ × ℕ) ×
        ((RawSlot × ClientMove) × ℚ) => decide (w.2.1.1.1 = w.1.2.1) := by
      obtain ⟨_, h⟩ := hrel1
      exact h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl
    have hd2 : Primrec fun w : (List (RawSlot × ClientMove) × ℕ × ℕ) ×
        ((RawSlot × ClientMove) × ℚ) => decide (w.2.1.1.2.1 = w.1.2.2) := by
      obtain ⟨_, h⟩ := hrel2
      exact h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl
    have hbool : Computable fun w : (List (RawSlot × ClientMove) × ℕ × ℕ) ×
        ((RawSlot × ClientMove) × ℚ) =>
        (decide (w.2.1.1.1 = w.1.2.1) && decide (w.2.1.1.2.1 = w.1.2.2)) :=
      ((Primrec.dom_bool₂ (fun a b => a && b)).comp hd1 hd2).to_comp
    have hthen : Computable fun w : (List (RawSlot × ClientMove) × ℕ × ℕ) ×
        ((RawSlot × ClientMove) × ℚ) => getReq w.2.1.2 [] + w.2.2 :=
      computable₂_ratAdd.comp
        ((primrec_getReq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.const [])).to_comp)
        (Computable.snd.comp Computable.snd)
    have helse : Computable fun w : (List (RawSlot × ClientMove) × ℕ × ℕ) ×
        ((RawSlot × ClientMove) × ℚ) => w.2.2 := Computable.snd.comp Computable.snd
    have hres : Computable fun w : (List (RawSlot × ClientMove) × ℕ × ℕ) ×
        ((RawSlot × ClientMove) × ℚ) =>
        if w.2.1.1.1 = w.1.2.1 ∧ w.2.1.1.2.1 = w.1.2.2 then getReq w.2.1.2 [] + w.2.2
          else w.2.2 := by
      refine (Computable.cond hbool hthen helse).of_eq fun w => ?_
      by_cases h1 : w.2.1.1.1 = w.1.2.1 <;> by_cases h2 : w.2.1.1.2.1 = w.1.2.2 <;>
        simp [h1, h2]
    exact hres.to₂
  exact (Computable.list_foldr hl hg hh).of_eq fun _ => rfl

/-- The raw son request is computable in its arguments. -/
theorem computable_rawSonRequest :
    Computable fun x : (ℚ × ℚ) × List (RawSlot × ClientMove) × ℕ × ℕ =>
      rawSonRequest x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2 := by
  have hthr : Computable fun x : (ℚ × ℚ) × List (RawSlot × ClientMove) × ℕ × ℕ => x.1.1 :=
    Computable.fst.comp Computable.fst
  have heps : Computable fun x : (ℚ × ℚ) × List (RawSlot × ClientMove) × ℕ × ℕ => x.1.2 :=
    Computable.snd.comp Computable.fst
  have hbase : Computable fun x : (ℚ × ℚ) × List (RawSlot × ClientMove) × ℕ × ℕ =>
      rawSonBase x.2.1 x.2.2.1 x.2.2.2 := computable_rawSonBase.comp Computable.snd
  have hbool : Computable fun x : (ℚ × ℚ) × List (RawSlot × ClientMove) × ℕ × ℕ =>
      !(decide (rawSonBase x.2.1 x.2.2.1 x.2.2.2 ≤ x.1.1)) :=
    Primrec.not.to_comp.comp (computable_ratLe.comp hbase hthr)
  have hres : Computable fun x : (ℚ × ℚ) × List (RawSlot × ClientMove) × ℕ × ℕ =>
      if x.1.1 < rawSonBase x.2.1 x.2.2.1 x.2.2.2 then x.1.2
        else rawSonBase x.2.1 x.2.2.1 x.2.2.2 := by
    refine (Computable.cond hbool heps hbase).of_eq fun x => ?_
    by_cases h : x.1.1 < rawSonBase x.2.1 x.2.2.1 x.2.2.2
    · simp [h, not_le.mpr h]
    · simp [h, not_lt.mp h]
  exact hres.of_eq fun _ => rfl

/-- The raw root request is computable in its arguments. -/
theorem computable_rawRootRequest :
    Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ × List (RawSlot × ClientMove) × ℕ =>
      rawRootRequest x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.1 x.2.2.1 x.2.2.2 := by
  have hdone : Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ × List (RawSlot × ClientMove) × ℕ =>
      x.1.1 := Computable.fst.comp Computable.fst
  have hfloor : Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ × List (RawSlot × ClientMove) × ℕ =>
      x.1.2.1 := Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hthr : Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ × List (RawSlot × ClientMove) × ℕ =>
      x.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have heps : Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ × List (RawSlot × ClientMove) × ℕ =>
      x.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hb : Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ × List (RawSlot × ClientMove) × ℕ =>
      x.2.1 := Computable.fst.comp Computable.snd
  have hentries : Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ ×
      List (RawSlot × ClientMove) × ℕ => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hi : Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ × List (RawSlot × ClientMove) × ℕ =>
      x.2.2.2 := Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hlist : Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ ×
      List (RawSlot × ClientMove) × ℕ =>
      (List.range x.2.1).map fun c =>
        rawSonRequest x.1.2.2.1 x.1.2.2.2 x.2.2.1 x.2.2.2 c := by
    refine Computable.list_map (Primrec.list_range.to_comp.comp hb) ?_
    exact (computable_rawSonRequest.comp
      (((hthr.comp Computable.fst).pair (heps.comp Computable.fst)).pair
        ((hentries.comp Computable.fst).pair
          ((hi.comp Computable.fst).pair Computable.snd)))).to₂
  have hsum : Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ ×
      List (RawSlot × ClientMove) × ℕ =>
      ((List.range x.2.1).map fun c =>
        rawSonRequest x.1.2.2.1 x.1.2.2.2 x.2.2.1 x.2.2.2 c).sum := by
    have hadd : Computable₂ fun (_ : (Bool × ℚ × ℚ × ℚ) × ℕ ×
        List (RawSlot × ClientMove) × ℕ) (u : ℚ × ℚ) => u.1 + u.2 :=
      (computable₂_ratAdd.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)).to₂
    exact (Computable.list_foldr hlist (Computable.const 0) hadd).of_eq fun x =>
      (list_sum_rat_eq_foldr _).symm
  have hmax : Computable fun x : (Bool × ℚ × ℚ × ℚ) × ℕ ×
      List (RawSlot × ClientMove) × ℕ =>
      max (((List.range x.2.1).map fun c =>
        rawSonRequest x.1.2.2.1 x.1.2.2.2 x.2.2.1 x.2.2.2 c).sum) x.1.2.1 := by
    refine (Computable.cond (computable_ratLe.comp hsum hfloor) hfloor hsum).of_eq fun x => ?_
    by_cases h : (((List.range x.2.1).map fun c =>
        rawSonRequest x.1.2.2.1 x.1.2.2.2 x.2.2.1 x.2.2.2 c).sum) ≤ x.1.2.1
    · simp [h]
    · simp [h, max_eq_left (not_le.mp h).le]
  refine (Computable.cond hdone hmax hsum).of_eq fun x => ?_
  cases hd : x.1.1 <;> simp [rawRootRequest]

/-- One outer root's contribution to the erased family move: the two-level graft of `rawRootRequest`
at the root, `rawSonRequest` at the sons `c < b` and `rawEntryMove` at the grandsons. -/
def rawRowMove (done : Bool) (targetFloor threshold eps : ℚ) (b : ℕ)
    (entries : List (RawSlot × ClientMove)) (i : ℕ) : ClientMove :=
  graftTwoLevel (rawRootRequest done targetFloor threshold eps b entries i) b
    (fun c => if c < b then rawSonRequest threshold eps entries i c else 0)
    (fun c c' => if c < b then (if c' < b then rawEntryMove entries (i, c, c') else []) else [])

/-- The arguments of one row of the erased family move. -/
abbrev RawRowArg := (Bool × ℚ × ℚ × ℚ) × ℕ × List (RawSlot × ClientMove) × ℕ

/-- The row of the displayed move belonging to one client is computable in its arguments. -/
theorem computable_rawRowMove :
    Computable fun y : RawRowArg =>
      rawRowMove y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2 y.2.1 y.2.2.1 y.2.2.2 := by
  have hb : Computable fun y : RawRowArg => y.2.1 := Computable.fst.comp Computable.snd
  have hentries : Computable fun y : RawRowArg => y.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hi : Computable fun y : RawRowArg => y.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hthreps : Computable fun y : RawRowArg => y.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hrootarg : Computable fun y : RawRowArg =>
      ((y.1, y.2.1, y.2.2.1, y.2.2.2) :
        (Bool × ℚ × ℚ × ℚ) × ℕ × List (RawSlot × ClientMove) × ℕ) :=
    Computable.fst.pair (hb.pair (hentries.pair hi))
  have hroot : Computable fun y : RawRowArg =>
      rawRootRequest y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2 y.2.1 y.2.2.1 y.2.2.2 :=
    (computable_rawRootRequest.comp hrootarg).of_eq fun _ => rfl
  have hson : Computable fun z : RawRowArg × ℕ =>
      if z.2 < z.1.2.1 then
        rawSonRequest z.1.1.2.2.1 z.1.1.2.2.2 z.1.2.2.1 z.1.2.2.2 z.2 else 0 := by
    have hrel : PrimrecPred fun z : RawRowArg × ℕ => z.2 < z.1.2.1 :=
      Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have hlt : Computable fun z : RawRowArg × ℕ => decide (z.2 < z.1.2.1) := by
      obtain ⟨_, h⟩ := hrel
      exact (h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl).to_comp
    have harg : Computable fun z : RawRowArg × ℕ =>
        ((z.1.1.2.2, z.1.2.2.1, z.1.2.2.2, z.2) :
          (ℚ × ℚ) × List (RawSlot × ClientMove) × ℕ × ℕ) :=
      (hthreps.comp Computable.fst).pair
        ((hentries.comp Computable.fst).pair ((hi.comp Computable.fst).pair Computable.snd))
    have hval : Computable fun z : RawRowArg × ℕ =>
        rawSonRequest z.1.1.2.2.1 z.1.1.2.2.2 z.1.2.2.1 z.1.2.2.2 z.2 :=
      (computable_rawSonRequest.comp harg).of_eq fun _ => rfl
    refine (Computable.cond hlt hval (Computable.const 0)).of_eq fun z => ?_
    by_cases h : z.2 < z.1.2.1 <;> simp [h]
  have hg : Computable fun w : (RawRowArg × ℕ) × ℕ =>
      if w.1.2 < w.1.1.2.1 then
        (if w.2 < w.1.1.2.1 then
          rawEntryMove w.1.1.2.2.1 (w.1.1.2.2.2, w.1.2, w.2) else [])
      else [] := by
    have hrel1 : PrimrecPred fun w : (RawRowArg × ℕ) × ℕ => w.1.2 < w.1.1.2.1 :=
      Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    have hrel2 : PrimrecPred fun w : (RawRowArg × ℕ) × ℕ => w.2 < w.1.1.2.1 :=
      Primrec.nat_lt.comp Primrec.snd
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    have hlt1 : Computable fun w : (RawRowArg × ℕ) × ℕ => decide (w.1.2 < w.1.1.2.1) := by
      obtain ⟨_, h⟩ := hrel1
      exact (h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl).to_comp
    have hlt2 : Computable fun w : (RawRowArg × ℕ) × ℕ => decide (w.2 < w.1.1.2.1) := by
      obtain ⟨_, h⟩ := hrel2
      exact (h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl).to_comp
    have hmovearg : Computable fun w : (RawRowArg × ℕ) × ℕ =>
        ((w.1.1.2.2.1, w.1.1.2.2.2, w.1.2, w.2) :
          List (RawSlot × ClientMove) × RawSlot) :=
      (hentries.comp (Computable.fst.comp Computable.fst)).pair
        ((hi.comp (Computable.fst.comp Computable.fst)).pair
          ((Computable.snd.comp Computable.fst).pair Computable.snd))
    have hmove : Computable fun w : (RawRowArg × ℕ) × ℕ =>
        rawEntryMove w.1.1.2.2.1 (w.1.1.2.2.2, w.1.2, w.2) :=
      (computable_rawEntryMove.comp hmovearg).of_eq fun _ => rfl
    have hinner : Computable fun w : (RawRowArg × ℕ) × ℕ =>
        if w.2 < w.1.1.2.1 then
          rawEntryMove w.1.1.2.2.1 (w.1.1.2.2.2, w.1.2, w.2) else ([] : ClientMove) := by
      refine (Computable.cond hlt2 hmove (Computable.const [])).of_eq fun w => ?_
      by_cases h : w.2 < w.1.1.2.1 <;> simp [h]
    refine (Computable.cond hlt1 hinner (Computable.const [])).of_eq fun w => ?_
    by_cases h : w.1.2 < w.1.1.2.1 <;> simp [h]
  exact (computable_graftTwoLevel (X := RawRowArg)
    (froot := fun y => rawRootRequest y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2 y.2.1 y.2.2.1 y.2.2.2)
    (fb := fun y => y.2.1)
    (fson := fun y c => if c < y.2.1 then
      rawSonRequest y.1.2.2.1 y.1.2.2.2 y.2.2.1 y.2.2.2 c else 0)
    (fg := fun y c c' => if c < y.2.1 then
      (if c' < y.2.1 then rawEntryMove y.2.2.1 (y.2.2.2, c, c') else []) else [])
    hroot hb hson hg).of_eq fun _ => rfl

/-- The raw displayed family move is computable in its arguments. -/
theorem computable_rawFamilyMove :
    Computable fun x : (Bool × ℚ × ℚ × ℚ) × (ℕ × ℕ) ×
        List RawRound × List RawSlot × FamilyClientMove =>
      rawFamilyMove x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.1.1 x.2.1.2
        x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  have hn : Computable fun x : (Bool × ℚ × ℚ × ℚ) × (ℕ × ℕ) ×
      List RawRound × List RawSlot × FamilyClientMove => x.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hb : Computable fun x : (Bool × ℚ × ℚ × ℚ) × (ℕ × ℕ) ×
      List RawRound × List RawSlot × FamilyClientMove => x.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hentries : Computable fun x : (Bool × ℚ × ℚ × ℚ) × (ℕ × ℕ) ×
      List RawRound × List RawSlot × FamilyClientMove =>
      rawEntries x.2.2.1 x.2.2.2.1 x.2.2.2.2 :=
    computable_rawEntries.comp (Computable.snd.comp Computable.snd)
  have harg : Computable fun z : ((Bool × ℚ × ℚ × ℚ) × (ℕ × ℕ) ×
      List RawRound × List RawSlot × FamilyClientMove) × ℕ =>
      ((z.1.1, z.1.2.1.2, rawEntries z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2, z.2) : RawRowArg) :=
    (Computable.fst.comp Computable.fst).pair
      ((hb.comp Computable.fst).pair
        ((hentries.comp Computable.fst).pair Computable.snd))
  have hbody : Computable₂ fun (x : (Bool × ℚ × ℚ × ℚ) × (ℕ × ℕ) ×
      List RawRound × List RawSlot × FamilyClientMove) (i : ℕ) =>
      rawRowMove x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.1.2
        (rawEntries x.2.2.1 x.2.2.2.1 x.2.2.2.2) i :=
    ((computable_rawRowMove.comp harg).of_eq fun _ => rfl).to₂
  exact (Computable.list_map (Primrec.list_range.to_comp.comp hn) hbody).of_eq fun _ => rfl

/-! ### Computability of the anchoring output -/

/-- Whether some raw slot sits at the child `c` of client `i`. -/
def rawForceSonB (slots : List RawSlot) (i c : ℕ) : Bool :=
  slots.any fun s => decide (s.1 = i ∧ s.2.1 = c)

/-- The forced-son test is primitive recursive. -/
theorem primrec_rawForceSonB :
    Primrec fun x : List RawSlot × ℕ × ℕ => rawForceSonB x.1 x.2.1 x.2.2 := by
  have hslots : Primrec fun x : List RawSlot × ℕ × ℕ => x.1 := Primrec.fst
  have hbody : Primrec₂ fun (x : List RawSlot × ℕ × ℕ) (s : RawSlot) =>
      decide (s.1 = x.2.1 ∧ s.2.1 = x.2.2) := by
    have h1 : Primrec fun w : (List RawSlot × ℕ × ℕ) × RawSlot =>
        decide (w.2.1 = w.1.2.1) :=
      (PrimrecRel.decide Primrec.eq).comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have h2 : Primrec fun w : (List RawSlot × ℕ × ℕ) × RawSlot =>
        decide (w.2.2.1 = w.1.2.2) :=
      (PrimrecRel.decide Primrec.eq).comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact ((Primrec.dom_bool₂ (fun a b => a && b)).comp h1 h2).of_eq
      (fun _ => by simp)
  exact (list_any_primrec hslots hbody).of_eq fun _ => rfl

/-- Arguments for one son request of the anchoring output. -/
abbrev RawWaitingSonArg :=
  (List RawSlot × ℚ × ℚ) × List (RawSlot × ClientMove) × ℕ × ℕ

/-- The waiting son request is the `cond` of the forcing test.  Keeping this
plain-value shape lemma separate from the computability proof below is what
keeps that proof inside the default elaboration budget. -/
private theorem rawWaitingSonRequest_eq_cond (forceSlots : List RawSlot)
    (threshold eps : ℚ) (entries : List (RawSlot × ClientMove)) (i c : ℕ) :
    rawWaitingSonRequest forceSlots threshold eps entries i c =
      cond (rawForceSonB forceSlots i c) eps
        (rawSonRequest threshold eps entries i c) := by
  have h : (forceSlots.any fun s => rawSameSonB s (i, c, s.2.2))
      = rawForceSonB forceSlots i c := by
    simp only [rawForceSonB, rawSameSonB]
  rw [rawWaitingSonRequest, h, Bool.cond_eq_ite]

/-- The waiting son request is computable in its arguments. -/
theorem computable_rawWaitingSonRequest :
    Computable fun x : RawWaitingSonArg =>
      rawWaitingSonRequest x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2 := by
  -- the forcing test is composed at the `Primrec` level and only then
  -- transported: composing it as a `Computable` sends the unifier into a deep
  -- `whnf` on the packed argument type.
  have hforceArg : Primrec fun x : RawWaitingSonArg =>
      ((x.1.1, x.2.2.1, x.2.2.2) : List RawSlot × ℕ × ℕ) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hforce : Computable fun x : RawWaitingSonArg =>
      rawForceSonB x.1.1 x.2.2.1 x.2.2.2 :=
    ((primrec_rawForceSonB.comp hforceArg).of_eq fun _ => rfl).to_comp
  have heps : Computable fun x : RawWaitingSonArg => x.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hbaseArg : Computable fun x : RawWaitingSonArg =>
      (((x.1.2.1, x.1.2.2), x.2.1, x.2.2.1, x.2.2.2) :
        (ℚ × ℚ) × List (RawSlot × ClientMove) × ℕ × ℕ) :=
    ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair heps).pair
      ((Computable.fst.comp Computable.snd).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
          (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have hbase : Computable fun x : RawWaitingSonArg =>
      rawSonRequest x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2 :=
    (computable_rawSonRequest.comp hbaseArg).of_eq fun _ => rfl
  exact (Computable.cond hforce heps hbase).of_eq fun x =>
    (rawWaitingSonRequest_eq_cond x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2).symm

/-- Shared arguments for one row of the anchoring output. -/
abbrev RawWaitingRowArg :=
  (Bool × ℚ × ℚ × ℚ) × ℕ × List RawSlot ×
    List (RawSlot × ClientMove) × ℕ

/-- The waiting root request is computable in its arguments. -/
theorem computable_rawWaitingRootRequest :
    Computable fun x : RawWaitingRowArg =>
      rawWaitingRootRequest x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2
        x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  have hdone : Computable fun x : RawWaitingRowArg => x.1.1 :=
    Computable.fst.comp Computable.fst
  have hfloor : Computable fun x : RawWaitingRowArg => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hthr : Computable fun x : RawWaitingRowArg => x.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have heps : Computable fun x : RawWaitingRowArg => x.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hb : Computable fun x : RawWaitingRowArg => x.2.1 :=
    Computable.fst.comp Computable.snd
  have hforce : Computable fun x : RawWaitingRowArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hentries : Computable fun x : RawWaitingRowArg => x.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd))
  have hi : Computable fun x : RawWaitingRowArg => x.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd))
  have harg : Computable fun z : RawWaitingRowArg × ℕ =>
      (((z.1.2.2.1, z.1.1.2.2.1, z.1.1.2.2.2),
        z.1.2.2.2.1, z.1.2.2.2.2, z.2) : RawWaitingSonArg) :=
    ((hforce.comp Computable.fst).pair
      ((hthr.comp Computable.fst).pair (heps.comp Computable.fst))).pair
        ((hentries.comp Computable.fst).pair
          ((hi.comp Computable.fst).pair Computable.snd))
  have hbody : Computable₂ fun (x : RawWaitingRowArg) (c : ℕ) =>
      rawWaitingSonRequest x.2.2.1 x.1.2.2.1 x.1.2.2.2
        x.2.2.2.1 x.2.2.2.2 c :=
    ((computable_rawWaitingSonRequest.comp harg).of_eq fun _ => rfl).to₂
  have hlist : Computable fun x : RawWaitingRowArg =>
      (List.range x.2.1).map fun c =>
        rawWaitingSonRequest x.2.2.1 x.1.2.2.1 x.1.2.2.2
          x.2.2.2.1 x.2.2.2.2 c :=
    Computable.list_map (Primrec.list_range.to_comp.comp hb) hbody
  have hsum : Computable fun x : RawWaitingRowArg =>
      ((List.range x.2.1).map fun c =>
        rawWaitingSonRequest x.2.2.1 x.1.2.2.1 x.1.2.2.2
          x.2.2.2.1 x.2.2.2.2 c).sum := by
    have hadd : Computable₂ fun (_ : RawWaitingRowArg) (u : ℚ × ℚ) =>
        u.1 + u.2 :=
      (computable₂_ratAdd.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)).to₂
    exact (Computable.list_foldr hlist (Computable.const 0) hadd).of_eq fun x =>
      (list_sum_rat_eq_foldr _).symm
  have hmax : Computable fun x : RawWaitingRowArg =>
      max (((List.range x.2.1).map fun c =>
        rawWaitingSonRequest x.2.2.1 x.1.2.2.1 x.1.2.2.2
          x.2.2.2.1 x.2.2.2.2 c).sum) x.1.2.1 := by
    refine (Computable.cond (computable_ratLe.comp hsum hfloor)
      hfloor hsum).of_eq fun x => ?_
    by_cases h : (((List.range x.2.1).map fun c =>
        rawWaitingSonRequest x.2.2.1 x.1.2.2.1 x.1.2.2.2
          x.2.2.2.1 x.2.2.2.2 c).sum) ≤ x.1.2.1
    · simp [h]
    · simp [h, max_eq_left (not_le.mp h).le]
  refine (Computable.cond hdone hmax hsum).of_eq fun x => ?_
  cases hd : x.1.1 <;> simp [rawWaitingRootRequest]

/-- The waiting row of one client, as a two-level graft, is computable in its arguments. -/
theorem computable_rawWaitingRowMove :
    Computable fun y : RawWaitingRowArg =>
      graftTwoLevel
        (rawWaitingRootRequest y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2
          y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2)
        y.2.1
        (fun c => if c < y.2.1 then
          rawWaitingSonRequest y.2.2.1 y.1.2.2.1 y.1.2.2.2
            y.2.2.2.1 y.2.2.2.2 c else 0)
        (fun c c' => if c < y.2.1 then
          if c' < y.2.1 then rawEntryMove y.2.2.2.1 (y.2.2.2.2, c, c')
          else [] else []) := by
  have hb : Computable fun y : RawWaitingRowArg => y.2.1 :=
    Computable.fst.comp Computable.snd
  have hforce : Computable fun y : RawWaitingRowArg => y.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hentries : Computable fun y : RawWaitingRowArg => y.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd))
  have hi : Computable fun y : RawWaitingRowArg => y.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd))
  have hthr : Computable fun y : RawWaitingRowArg => y.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have heps : Computable fun y : RawWaitingRowArg => y.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hroot : Computable fun y : RawWaitingRowArg =>
      rawWaitingRootRequest y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2
        y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 :=
    computable_rawWaitingRootRequest
  have hson : Computable fun z : RawWaitingRowArg × ℕ =>
      if z.2 < z.1.2.1 then
        rawWaitingSonRequest z.1.2.2.1 z.1.1.2.2.1 z.1.1.2.2.2
          z.1.2.2.2.1 z.1.2.2.2.2 z.2 else 0 := by
    have hrel : PrimrecPred fun z : RawWaitingRowArg × ℕ =>
        z.2 < z.1.2.1 :=
      Primrec.nat_lt.comp Primrec.snd
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have hlt : Computable fun z : RawWaitingRowArg × ℕ =>
        decide (z.2 < z.1.2.1) := by
      obtain ⟨_, h⟩ := hrel
      exact (h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl).to_comp
    have harg : Computable fun z : RawWaitingRowArg × ℕ =>
        (((z.1.2.2.1, z.1.1.2.2.1, z.1.1.2.2.2),
          z.1.2.2.2.1, z.1.2.2.2.2, z.2) : RawWaitingSonArg) :=
      ((hforce.comp Computable.fst).pair
        ((hthr.comp Computable.fst).pair (heps.comp Computable.fst))).pair
          ((hentries.comp Computable.fst).pair
            ((hi.comp Computable.fst).pair Computable.snd))
    have hval : Computable fun z : RawWaitingRowArg × ℕ =>
        rawWaitingSonRequest z.1.2.2.1 z.1.1.2.2.1 z.1.1.2.2.2
          z.1.2.2.2.1 z.1.2.2.2.2 z.2 :=
      (computable_rawWaitingSonRequest.comp harg).of_eq fun _ => rfl
    refine (Computable.cond hlt hval (Computable.const 0)).of_eq fun z => ?_
    by_cases h : z.2 < z.1.2.1 <;> simp [h]
  have hg : Computable fun w : (RawWaitingRowArg × ℕ) × ℕ =>
      if w.1.2 < w.1.1.2.1 then
        (if w.2 < w.1.1.2.1 then
          rawEntryMove w.1.1.2.2.2.1 (w.1.1.2.2.2.2, w.1.2, w.2)
          else [])
      else [] := by
    have hrel1 : PrimrecPred fun w : (RawWaitingRowArg × ℕ) × ℕ =>
        w.1.2 < w.1.1.2.1 :=
      Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    have hrel2 : PrimrecPred fun w : (RawWaitingRowArg × ℕ) × ℕ =>
        w.2 < w.1.1.2.1 :=
      Primrec.nat_lt.comp Primrec.snd
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    have hlt1 : Computable fun w : (RawWaitingRowArg × ℕ) × ℕ =>
        decide (w.1.2 < w.1.1.2.1) := by
      obtain ⟨_, h⟩ := hrel1
      exact (h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl).to_comp
    have hlt2 : Computable fun w : (RawWaitingRowArg × ℕ) × ℕ =>
        decide (w.2 < w.1.1.2.1) := by
      obtain ⟨_, h⟩ := hrel2
      exact (h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl).to_comp
    have hmovearg : Computable fun w : (RawWaitingRowArg × ℕ) × ℕ =>
        ((w.1.1.2.2.2.1, w.1.1.2.2.2.2, w.1.2, w.2) :
          List (RawSlot × ClientMove) × RawSlot) :=
      (hentries.comp (Computable.fst.comp Computable.fst)).pair
        ((hi.comp (Computable.fst.comp Computable.fst)).pair
          ((Computable.snd.comp Computable.fst).pair Computable.snd))
    have hmove : Computable fun w : (RawWaitingRowArg × ℕ) × ℕ =>
        rawEntryMove w.1.1.2.2.2.1 (w.1.1.2.2.2.2, w.1.2, w.2) :=
      (computable_rawEntryMove.comp hmovearg).of_eq fun _ => rfl
    have hinner : Computable fun w : (RawWaitingRowArg × ℕ) × ℕ =>
        if w.2 < w.1.1.2.1 then
          rawEntryMove w.1.1.2.2.2.1 (w.1.1.2.2.2.2, w.1.2, w.2)
        else ([] : ClientMove) := by
      refine (Computable.cond hlt2 hmove (Computable.const [])).of_eq fun w => ?_
      by_cases h : w.2 < w.1.1.2.1 <;> simp [h]
    refine (Computable.cond hlt1 hinner (Computable.const [])).of_eq fun w => ?_
    by_cases h : w.1.2 < w.1.1.2.1 <;> simp [h]
  exact (computable_graftTwoLevel (X := RawWaitingRowArg)
    (froot := fun y =>
      rawWaitingRootRequest y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2
        y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2)
    (fb := fun y => y.2.1)
    (fson := fun y c => if c < y.2.1 then
      rawWaitingSonRequest y.2.2.1 y.1.2.2.1 y.1.2.2.2
        y.2.2.2.1 y.2.2.2.2 c else 0)
    (fg := fun y c c' => if c < y.2.1 then
      (if c' < y.2.1 then
        rawEntryMove y.2.2.2.1 (y.2.2.2.2, c, c') else []) else [])
    hroot hb hson hg).of_eq fun _ => rfl

/-- Arguments for the complete anchoring output. -/
abbrev RawWaitingFamilyArg :=
  (Bool × ℚ × ℚ × ℚ) × (ℕ × ℕ) × List RawRound × List RawSlot

/-- The waiting family move is computable in its arguments. -/
theorem computable_rawWaitingFamilyMove :
    Computable fun x : RawWaitingFamilyArg =>
      rawWaitingFamilyMove x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2
        x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2 := by
  have hn : Computable fun x : RawWaitingFamilyArg => x.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hb : Computable fun x : RawWaitingFamilyArg => x.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hfrozen : Computable fun x : RawWaitingFamilyArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hforce : Computable fun x : RawWaitingFamilyArg => x.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hentries : Computable fun x : RawWaitingFamilyArg =>
      rawFrozenEntries x.2.2.1 :=
    computable_rawFrozenEntries.comp hfrozen
  have harg : Computable fun z : RawWaitingFamilyArg × ℕ =>
      ((z.1.1, z.1.2.1.2, z.1.2.2.2,
        rawFrozenEntries z.1.2.2.1, z.2) : RawWaitingRowArg) :=
    (Computable.fst.comp Computable.fst).pair
      ((hb.comp Computable.fst).pair
        ((hforce.comp Computable.fst).pair
          ((hentries.comp Computable.fst).pair Computable.snd)))
  have hbody : Computable₂ fun (x : RawWaitingFamilyArg) (i : ℕ) =>
      graftTwoLevel
        (rawWaitingRootRequest x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2
          x.2.1.2 x.2.2.2 (rawFrozenEntries x.2.2.1) i)
        x.2.1.2
        (fun c => if c < x.2.1.2 then
          rawWaitingSonRequest x.2.2.2 x.1.2.2.1 x.1.2.2.2
            (rawFrozenEntries x.2.2.1) i c else 0)
        (fun c c' => if c < x.2.1.2 then
          if c' < x.2.1.2 then
            rawEntryMove (rawFrozenEntries x.2.2.1) (i, c, c')
          else [] else []) :=
    ((computable_rawWaitingRowMove.comp harg).of_eq fun _ => rfl).to₂
  exact (Computable.list_map (Primrec.list_range.to_comp.comp hn) hbody).of_eq
    fun _ => rfl
/-! ### Server-move localisation -/

/-- `restrictSubtreeAssoc` written as a `flatMap`, the shape accepted by the
computability library. -/
theorem restrictSubtreeAssoc_eq_flatMap {β : Type} (i : ℕ) (l : List (GacsDayNode × β)) :
    restrictSubtreeAssoc i l =
      l.flatMap fun p =>
        if p.1.length = 0 then [] else
        if p.1.headD 0 = i then [(p.1.tail, p.2)] else [] := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨x, v⟩ := p
    rw [List.flatMap_cons, ← ih]
    cases x with
    | nil => simp [restrictSubtreeAssoc]
    | cons j rest => by_cases h : j = i <;> simp [restrictSubtreeAssoc, h]

/-- Restricting the entries of a server move to a subtree is primitive recursive. -/
theorem primrec₂_restrictSubtreeServerMove :
    Primrec₂ fun (i : ℕ) (l : ServerMove) => restrictSubtreeAssoc i l := by
  have hrel1 : PrimrecPred fun w : (ℕ × ServerMove) × (GacsDayNode × Allocation) =>
      w.2.1.length = 0 :=
    Primrec.eq.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.const 0)
  have hrel2 : PrimrecPred fun w : (ℕ × ServerMove) × (GacsDayNode × Allocation) =>
      w.2.1.headD 0 = w.1.1 :=
    Primrec.eq.comp (headD_primrec (Primrec.fst.comp Primrec.snd) 0)
      (Primrec.fst.comp Primrec.fst)
  have hsingle : Primrec fun w : (ℕ × ServerMove) × (GacsDayNode × Allocation) =>
      [((w.2.1.tail, w.2.2) : GacsDayNode × Allocation)] :=
    Primrec.list_cons.comp
      ((Primrec.list_tail.comp (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd)) (Primrec.const [])
  have hbody : Primrec₂ fun (z : ℕ × ServerMove) (p : GacsDayNode × Allocation) =>
      if p.1.length = 0 then [] else
      if p.1.headD 0 = z.1 then [(p.1.tail, p.2)] else
      ([] : List (GacsDayNode × Allocation)) :=
    (Primrec.ite hrel1 (Primrec.const [])
      (Primrec.ite hrel2 hsingle (Primrec.const []))).to₂
  exact (Primrec.list_flatMap Primrec.snd hbody).of_eq fun z =>
    (restrictSubtreeAssoc_eq_flatMap z.1 z.2).symm

/-- Extracting the subtree of a server move below a child is primitive recursive. -/
theorem primrec₂_extractSubtreeServerMoveRaw : Primrec₂ extractSubtreeServerMove :=
  primrec₂_restrictSubtreeServerMove.of_eq fun _ _ => rfl

end Kolmogorov
