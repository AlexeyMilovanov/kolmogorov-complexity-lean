import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.MonotoneComplexity.GacsDayGraftComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRaw
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRawComputable.Basic
import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustGrayComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwoComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayTailReserveComputable

/-!
# Computability of the erased tail transition

The tail controller is defined on structured states; for the computability argument it is run in
an erased, raw form, and this module proves each ingredient of one raw transition computable.

### Outline

* the data of a round: the grandchild subtrees of the raw slots, the localised raw server move,
  and the neighbourhood cells (`computable_rawExtractGrandchildFamilyMove`,
  `computable_rawLocalServerMove`, `computable_neighborhoodCellsList`);
* slot bookkeeping (`computable_rawFrozenSonBase`, the next-slot selection `RawNextArg`) and the
  round threshold, with the rational comparison lemma `not_decide_lt_rat`;
* one transition, assembled from the above;
* the three statements the oracle assembly consumes: `computable_rawQueryOf` for the subcall
  input, `computable_rawInitialStateOf` for the initial state and `computable_rawOutputEnc` for
  the encoded displayed move.
-/

namespace Kolmogorov
open Encodable

/-- Extracting the grandchild subtrees of the raw slots is computable. -/
theorem computable_rawExtractGrandchildFamilyMove :
    Computable fun x : List RawSlot × FamilyServerMove =>
      rawExtractGrandchildFamilyMove x.1 x.2 := by
  have hfam : Primrec fun w : (List RawSlot × FamilyServerMove) × RawSlot =>
      familyServerMoveAt w.1.2 w.2.1 :=
    primrec₂_familyServerMoveAt.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have h1 : Primrec fun w : (List RawSlot × FamilyServerMove) × RawSlot =>
      extractSubtreeServerMove w.2.2.1 (familyServerMoveAt w.1.2 w.2.1) :=
    primrec₂_extractSubtreeServerMoveRaw.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hfam
  have hbody : Primrec₂ fun (x : List RawSlot × FamilyServerMove) (slot : RawSlot) =>
      extractSubtreeServerMove slot.2.2
        (extractSubtreeServerMove slot.2.1 (familyServerMoveAt x.2 slot.1)) :=
    (primrec₂_extractSubtreeServerMoveRaw.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) h1).to₂
  exact ((Primrec.list_map Primrec.fst hbody).of_eq fun _ => rfl).to_comp

/-- The localised raw server move is computable in its arguments. -/
theorem computable_rawLocalServerMove :
    Computable fun x : (ℕ × ℕ) × List RawSlot × FamilyServerMove =>
      rawLocalServerMove x.1.1 x.1.2 x.2.1 x.2.2 := by
  have hextract : Computable fun x : (ℕ × ℕ) × List RawSlot × FamilyServerMove =>
      rawExtractGrandchildFamilyMove x.2.1 x.2.2 :=
    computable_rawExtractGrandchildFamilyMove.comp Computable.snd
  have hin : Computable fun x : (ℕ × ℕ) × List RawSlot × FamilyServerMove =>
      inTreeFamilyServerMove x.1.2 (rawExtractGrandchildFamilyMove x.2.1 x.2.2) :=
    computable₂_inTreeFamilyServerMoveRaw.comp (Computable.snd.comp Computable.fst) hextract
  exact (computable₂_truncFamilyServerMoveRaw.comp
    (Computable.fst.comp Computable.fst) hin).of_eq fun _ => rfl

/-- Neighbourhood cells with computable data. -/
theorem computable_neighborhoodCellsList {X : Type} [Primcodable X]
    {fd : X → ℕ} {fS : X → List BitString} (hd : Computable fd) (hS : Computable fS) :
    Computable fun x : X => neighborhoodCellsList (fd x) (fS x) := by
  refine computable_list_filter (CodedFiniteDistribution.allStrings_primrec.to_comp.comp hd) ?_
  exact primrec₂_comparableB.to_comp.comp (hS.comp Computable.fst) Computable.snd

/-! ### Slot bookkeeping -/

/-- The raw frozen son base is computable in the frozen rounds and the coordinates. -/
theorem computable_rawFrozenSonBase :
    Computable fun x : List RawRound × ℕ × ℕ =>
      rawFrozenSonBase x.1 x.2.1 x.2.2 := by
  have harg : Computable fun x : List RawRound × ℕ × ℕ =>
      ((rawFrozenEntries x.1, x.2.1, x.2.2) : List (RawSlot × ClientMove) × ℕ × ℕ) :=
    (computable_rawFrozenEntries.comp Computable.fst).pair Computable.snd
  exact (computable_rawSonBase.comp harg).of_eq fun _ => rfl

/-- Negated strict comparison of rationals as a non-strict one. -/
theorem not_decide_lt_rat (a b : ℚ) : (!decide (a < b)) = decide (b ≤ a) := by
  by_cases h : a < b
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

/-- The arguments of the next-slot selection. -/
abbrev RawNextArg :=
  (ℕ × ℕ × ℕ × ℕ × ℕ) × ℚ × Allocation × List RawRound × FamilyServerMove

/-- Selecting the raw slots of the next round is computable in its arguments. -/
theorem computable_rawNextSlots :
    Computable fun x : RawNextArg =>
      rawNextSlots x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2
        x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  have hn : Computable fun x : RawNextArg => x.1.1 := Computable.fst.comp Computable.fst
  have hb : Computable fun x : RawNextArg => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have he : Computable fun x : RawNextArg => x.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hused : Computable fun x : RawNextArg => x.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.fst)))
  have hround : Computable fun x : RawNextArg => x.1.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.fst)))
  have hthr : Computable fun x : RawNextArg => x.2.1 := Computable.fst.comp Computable.snd
  have hA : Computable fun x : RawNextArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hfrozen : Computable fun x : RawNextArg => x.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hsm : Computable fun x : RawNextArg => x.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  -- the column test, as a function of `((x, i), c)`
  have hrelc : PrimrecPred fun w : (RawNextArg × ℕ) × ℕ => w.2 < w.1.1.1.2.2.2.1 :=
    Primrec.nat_lt.comp Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))))
  have ht1 : Computable fun w : (RawNextArg × ℕ) × ℕ => decide (w.2 < w.1.1.1.2.2.2.1) := by
    obtain ⟨_, h⟩ := hrelc
    exact (h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl).to_comp
  have hbasearg : Computable fun w : (RawNextArg × ℕ) × ℕ =>
      ((w.1.1.2.2.2.1, w.1.2, w.2) : List RawRound × ℕ × ℕ) :=
    (hfrozen.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd)
  have hbase : Computable fun w : (RawNextArg × ℕ) × ℕ =>
      rawFrozenSonBase w.1.1.2.2.2.1 w.1.2 w.2 :=
    (computable_rawFrozenSonBase.comp hbasearg).of_eq fun _ => rfl
  have ht2 : Computable fun w : (RawNextArg × ℕ) × ℕ =>
      !(decide (w.1.1.2.1 < rawFrozenSonBase w.1.1.2.2.2.1 w.1.2 w.2)) := by
    refine (computable_ratLe.comp hbase
      (hthr.comp (Computable.fst.comp Computable.fst))).of_eq fun w => ?_
    exact (not_decide_lt_rat w.1.1.2.1
      (rawFrozenSonBase w.1.1.2.2.2.1 w.1.2 w.2)).symm
  have hresarg : Computable fun w : (RawNextArg × ℕ) × ℕ =>
      (((w.1.1.1.2.2.1, w.1.1.1.2.1), w.1.1.2.2.1, (w.1.1.1.1, w.1.2),
        w.1.1.2.2.2.2, [w.2]) :
        (ℕ × ℕ) × Allocation × (ℕ × ℕ) × FamilyServerMove × GacsDayNode) :=
    (((he.comp (Computable.fst.comp Computable.fst)).pair
        (hb.comp (Computable.fst.comp Computable.fst))).pair
      (((hA.comp (Computable.fst.comp Computable.fst))).pair
        ((((hn.comp (Computable.fst.comp Computable.fst))).pair
            (Computable.snd.comp Computable.fst)).pair
          (((hsm.comp (Computable.fst.comp Computable.fst))).pair
            (Computable.list_cons.comp Computable.snd (Computable.const []))))))
  have ht3 : Computable fun w : (RawNextArg × ℕ) × ℕ =>
      !(getTailFamilyReserve w.1.1.1.2.2.1 w.1.1.1.2.1 w.1.1.2.2.1 w.1.1.1.1 w.1.2
        w.1.1.2.2.2.2 [w.2]).isSome :=
    Primrec.not.to_comp.comp
      (Primrec.option_isSome.to_comp.comp
        ((computable_getTailFamilyReserve_joint.comp hresarg).of_eq fun _ => rfl))
  have hand : Computable₂ fun a b : Bool => a && b :=
    (Primrec.dom_bool₂ (fun a b => a && b)).to_comp
  have hpred : Computable fun w : (RawNextArg × ℕ) × ℕ =>
      (decide (w.2 < w.1.1.1.2.2.2.1) &&
        !(decide (w.1.1.2.1 < rawFrozenSonBase w.1.1.2.2.2.1 w.1.2 w.2))) &&
      !(getTailFamilyReserve w.1.1.1.2.2.1 w.1.1.1.2.1 w.1.1.2.2.1 w.1.1.1.1 w.1.2
        w.1.1.2.2.2.2 [w.2]).isSome :=
    hand.comp (hand.comp ht1 ht2) ht3
  have hcols : Computable fun z : RawNextArg × ℕ =>
      (List.range z.1.1.2.1).filter fun c =>
        (decide (c < z.1.1.2.2.2.1) &&
          !(decide (z.1.2.1 < rawFrozenSonBase z.1.2.2.2.1 z.2 c))) &&
        !(getTailFamilyReserve z.1.1.2.2.1 z.1.1.2.1 z.1.2.2.1 z.1.1.1 z.2
          z.1.2.2.2.2 [c]).isSome :=
    computable_list_filter (Primrec.list_range.to_comp.comp (hb.comp Computable.fst))
      hpred.to₂
  have hslotbody : Computable₂ fun (z : RawNextArg × ℕ) (c : ℕ) =>
      ((z.2, c, z.1.1.2.2.2.2) : RawSlot) :=
    ((Computable.snd.comp Computable.fst).pair
      (Computable.snd.pair
        ((hround.comp (Computable.fst.comp Computable.fst))))).to₂
  have hmapped : Computable fun z : RawNextArg × ℕ =>
      ((List.range z.1.1.2.1).filter fun c =>
        (decide (c < z.1.1.2.2.2.1) &&
          !(decide (z.1.2.1 < rawFrozenSonBase z.1.2.2.2.1 z.2 c))) &&
        !(getTailFamilyReserve z.1.1.2.2.1 z.1.1.2.1 z.1.2.2.1 z.1.1.1 z.2
          z.1.2.2.2.2 [c]).isSome).map fun c => ((z.2, c, z.1.1.2.2.2.2) : RawSlot) :=
    Computable.list_map hcols hslotbody
  have hflat : Computable fun x : RawNextArg =>
      (List.range x.1.1).flatMap fun i =>
        ((List.range x.1.2.1).filter fun c =>
          (decide (c < x.1.2.2.2.1) &&
            !(decide (x.2.1 < rawFrozenSonBase x.2.2.2.1 i c))) &&
          !(getTailFamilyReserve x.1.2.2.1 x.1.2.1 x.2.2.1 x.1.1 i
            x.2.2.2.2 [c]).isSome).map fun c => ((i, c, x.1.2.2.2.2) : RawSlot) :=
    computable_list_flatMap (Primrec.list_range.to_comp.comp hn) hmapped.to₂
  have hrelr : PrimrecPred fun x : RawNextArg => x.1.2.2.2.2 < x.1.2.1 :=
    Primrec.nat_lt.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hlt : Computable fun x : RawNextArg => decide (x.1.2.2.2.2 < x.1.2.1) := by
    obtain ⟨_, h⟩ := hrelr
    exact (h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl).to_comp
  refine (Computable.cond hlt hflat (Computable.const [])).of_eq fun x => ?_
  by_cases h : x.1.2.2.2.2 < x.1.2.1 <;> simp [rawNextSlots, h]

/-- The initial raw tail state is computable in its parameters. -/
theorem computable_rawInitialState :
    Computable fun x : (ℕ × ℕ × ℕ × ℕ) × Allocation =>
      rawInitialState x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2 := by
  have hn : Computable fun x : (ℕ × ℕ × ℕ × ℕ) × Allocation => x.1.1 :=
    Computable.fst.comp Computable.fst
  have hb : Computable fun x : (ℕ × ℕ × ℕ × ℕ) × Allocation => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hused : Computable fun x : (ℕ × ℕ × ℕ × ℕ) × Allocation =>
      2 ^ (x.1.2.2.2 - x.1.2.2.1) :=
    (nat_pow_primrec₂.comp (Primrec.const 2)
      (Primrec.nat_sub.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to_comp
  have harg : Computable fun x : (ℕ × ℕ × ℕ × ℕ) × Allocation =>
      (((x.1.1, x.1.2.1), 2 ^ (x.1.2.2.2 - x.1.2.2.1), 0) : (ℕ × ℕ) × ℕ × ℕ) :=
    (hn.pair hb).pair (hused.pair (Computable.const 0))
  have hslots : Computable fun x : (ℕ × ℕ × ℕ × ℕ) × Allocation =>
      rawSlots x.1.1 x.1.2.1 (2 ^ (x.1.2.2.2 - x.1.2.2.1)) 0 :=
    (computable_rawSlots.comp harg).of_eq fun _ => rfl
  exact ((((Computable.const 0).pair
      ((Computable.const 0).pair (Computable.const false))).pair
    ((Computable.const []).pair
      (Computable.snd.pair
        (hslots.pair ((Computable.const []).pair
          (Computable.const (([], []) : FamilyGameHistory))))))).of_eq
    fun _ => rfl)

/-- Testing whether two raw slots share client and child is computable. -/
theorem computable_rawSameSonB :
    Computable fun x : RawSlot × RawSlot => rawSameSonB x.1 x.2 := by
  have h1 : PrimrecPred fun x : RawSlot × RawSlot => x.1.1 = x.2.1 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have h2 : PrimrecPred fun x : RawSlot × RawSlot => x.1.2.1 = x.2.2.1 :=
    Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hd1 : Primrec fun x : RawSlot × RawSlot => decide (x.1.1 = x.2.1) := by
    obtain ⟨_, h⟩ := h1
    exact h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl
  have hd2 : Primrec fun x : RawSlot × RawSlot => decide (x.1.2.1 = x.2.2.1) := by
    obtain ⟨_, h⟩ := h2
    exact h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl
  have hand : Computable₂ fun a b : Bool => a && b :=
    (Primrec.dom_bool₂ (fun a b => a && b)).to_comp
  exact (hand.comp hd1.to_comp hd2.to_comp).of_eq fun x => by
    simp [rawSameSonB]

/-- Selecting the retained raw slots is computable. -/
theorem computable_rawRetainedSlots :
    Computable fun x : List RawSlot × List RawSlot => rawRetainedSlots x.1 x.2 := by
  have hp : Computable₂ fun (x : List RawSlot × List RawSlot) (s : RawSlot) =>
      x.1.any (fun t => rawSameSonB s t) := by
    have hf : Computable fun z : (List RawSlot × List RawSlot) × RawSlot => z.1.1 :=
      Computable.fst.comp Computable.fst
    have harg : Computable fun w : ((List RawSlot × List RawSlot) × RawSlot) × RawSlot =>
        (w.1.2, w.2) :=
      (Computable.snd.comp Computable.fst).pair Computable.snd
    have hpred : Computable₂ fun (z : (List RawSlot × List RawSlot) × RawSlot) (t : RawSlot) =>
        rawSameSonB z.2 t :=
      (computable_rawSameSonB.comp harg).of_eq (fun _ => rfl) |>.to₂
    exact (computable_list_any hf hpred).to₂
  exact (computable_list_filter Computable.snd hp).of_eq fun _ => rfl

/-- Counting the raw slots of one client is computable. -/
theorem computable_rawRootSlotCount :
    Computable fun x : List RawSlot × ℕ => rawRootSlotCount x.1 x.2 := by
  have hrel : PrimrecPred fun z : (List RawSlot × ℕ) × RawSlot => z.2.1 = z.1.2 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  have hd : Primrec fun z : (List RawSlot × ℕ) × RawSlot => decide (z.2.1 = z.1.2) := by
    obtain ⟨_, h⟩ := hrel
    exact h.of_eq fun _ => decide_eq_decide.mpr Iff.rfl
  have hfilt : Computable fun x : List RawSlot × ℕ =>
      x.1.filter fun s => decide (s.1 = x.2) :=
    computable_list_filter Computable.fst hd.to_comp.to₂
  exact (Primrec.list_length.to_comp.comp hfilt).of_eq fun _ => rfl

/-- The per-root quarter test is computable. -/
theorem computable_rawPerRootQuarterB :
    Computable fun x : (ℕ × ℕ) × List RawSlot => rawPerRootQuarterB x.1.1 x.1.2 x.2 := by
  have hn : Computable fun x : (ℕ × ℕ) × List RawSlot => x.1.1 :=
    Computable.fst.comp Computable.fst
  have hused : Computable fun x : (ℕ × ℕ) × List RawSlot => x.1.2 :=
    Computable.snd.comp Computable.fst
  have hslots : Computable fun x : (ℕ × ℕ) × List RawSlot => x.2 := Computable.snd
  have hrange : Computable fun x : (ℕ × ℕ) × List RawSlot => List.range x.1.1 :=
    Primrec.list_range.to_comp.comp hn
  have hbody : Computable₂ fun (x : (ℕ × ℕ) × List RawSlot) (i : ℕ) =>
      decide (4 * rawRootSlotCount x.2 i ≤ x.1.2) := by
    have hcarg : Computable fun z : ((ℕ × ℕ) × List RawSlot) × ℕ =>
        (z.1.2, z.2) :=
      (hslots.comp Computable.fst).pair Computable.snd
    have hc : Computable fun z : ((ℕ × ℕ) × List RawSlot) × ℕ =>
        rawRootSlotCount z.1.2 z.2 :=
      (computable_rawRootSlotCount.comp hcarg).of_eq fun _ => rfl
    have h4c : Computable fun z : ((ℕ × ℕ) × List RawSlot) × ℕ =>
        4 * rawRootSlotCount z.1.2 z.2 :=
      Primrec.nat_mul.to_comp.comp (Computable.const 4) hc
    have hd : Computable fun z : ((ℕ × ℕ) × List RawSlot) × ℕ =>
        decide (4 * rawRootSlotCount z.1.2 z.2 ≤ z.1.1.2) :=
      (PrimrecRel.decide Primrec.nat_le).to_comp.comp h4c (hused.comp Computable.fst)
    exact hd.to₂
  exact (computable_list_all hrange hbody).of_eq fun _ => rfl

/-- The global quarter test is computable. -/
theorem computable_rawGlobalQuarterB :
    Computable fun x : (ℕ × ℕ) × List RawSlot => rawGlobalQuarterB x.1.1 x.1.2 x.2 := by
  have h4 : Computable fun x : (ℕ × ℕ) × List RawSlot => 4 * x.2.length :=
    Primrec.nat_mul.to_comp.comp (Computable.const 4)
      (Primrec.list_length.to_comp.comp Computable.snd)
  have hnm : Computable fun x : (ℕ × ℕ) × List RawSlot => x.1.1 * x.1.2 :=
    Primrec.nat_mul.to_comp.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst)
  exact ((PrimrecRel.decide Primrec.nat_le).to_comp.comp h4 hnm).of_eq fun _ => rfl

/-! ### The round threshold -/

/-- The round threshold in closed form. -/
theorem rawThreshold_eq (q e : ℕ) :
    dyadicScale e - dyadicScale e / (6 * halfAmplification q) =
      (((3 * q + 5 : ℕ) : ℤ) : ℚ) / ((2 ^ e * (3 * q + 6) : ℕ) : ℚ) := by
  have hpow : ((1 : ℚ) / 2) ^ e = 1 / (2 : ℚ) ^ e := one_div_pow 2 e
  have h2 : ((2 : ℚ)) ^ e ≠ 0 := by positivity
  have hq : (6 : ℚ) * (1 + (q : ℚ) / 2) ≠ 0 := by positivity
  simp only [dyadicScale, halfAmplification, hpow]
  push_cast
  field_simp
  ring

/-- The service threshold is computable in the stage and the scale. -/
theorem computable₂_rawThreshold :
    Computable₂ fun (q e : ℕ) =>
      dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
  have hN : Computable fun p : ℕ × ℕ => ((3 * p.1 + 5 : ℕ) : ℤ) :=
    (ComputableReals.primrec_natCastInt.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst)
        (Primrec.const 5))).to_comp
  have hD : Computable fun p : ℕ × ℕ => 2 ^ p.2 * (3 * p.1 + 6) :=
    (Primrec.nat_mul.comp (nat_pow_primrec₂.comp (Primrec.const 2) Primrec.snd)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst)
        (Primrec.const 6))).to_comp
  exact computable_of_num_den hN hD (fun p => by positivity)
    fun p => rawThreshold_eq p.1 p.2

/-- Arguments for checking whether a live slot has an ordinary but not yet
anchored reserve. -/
abbrev RawReserveScanArg :=
  (ℕ × ℕ × ℕ) × Allocation × List RawSlot × FamilyServerMove

/-- The scan for an unanchored reserve is primitive recursive. -/
theorem primrec_rawHasUnanchoredReserveB :
    Primrec fun x : RawReserveScanArg =>
      rawHasUnanchoredReserveB x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2 := by
  have hslots : Primrec fun x : RawReserveScanArg => x.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hbody : Primrec₂ fun (x : RawReserveScanArg) (s : RawSlot) =>
      (getTailFamilyReserve x.1.1 x.1.2.2 x.2.1 x.1.2.1
        s.1 x.2.2.2 [s.2.1]).isSome := by
    have he : Primrec fun z : RawReserveScanArg × RawSlot => z.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hn : Primrec fun z : RawReserveScanArg × RawSlot => z.1.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hb : Primrec fun z : RawReserveScanArg × RawSlot => z.1.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hA : Primrec fun z : RawReserveScanArg × RawSlot => z.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hi : Primrec fun z : RawReserveScanArg × RawSlot => z.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hsm : Primrec fun z : RawReserveScanArg × RawSlot => z.1.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have hnode : Primrec fun z : RawReserveScanArg × RawSlot => [z.2.2.1] :=
      Primrec.list_cons.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const [])
    have harg : Primrec fun z : RawReserveScanArg × RawSlot =>
        (((z.1.1.1, z.1.1.2.2), z.1.2.1, (z.1.1.2.1, z.2.1),
          z.1.2.2.2, [z.2.2.1]) :
          (ℕ × ℕ) × Allocation × (ℕ × ℕ) × FamilyServerMove × GacsDayNode) :=
      (he.pair hb).pair (hA.pair ((hn.pair hi).pair (hsm.pair hnode)))
    exact (Primrec.option_isSome.comp
      (primrec_getTailFamilyReserve_joint.comp harg)).to₂
  exact (list_any_primrec hslots hbody).of_eq fun _ => rfl

/-- The scan for an unanchored reserve is computable. -/
theorem computable_rawHasUnanchoredReserveB :
    Computable fun x : RawReserveScanArg =>
      rawHasUnanchoredReserveB x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2 :=
  primrec_rawHasUnanchoredReserveB.to_comp
/-! ### One transition -/

/-- The arguments of one erased transition. -/
abbrev RawStepArg := RawParam × RawState × FamilyServerMove × FamilyClientMove

/-- Packed arguments of the final case distinction of one raw transition:
`((cond, time, roundStart, done), (frozen, unavailable, slots, anchors, history),
(goal, unanchored, newRound, neighbours, candidates),
(perRootQuarterB, roundCount), current, localSM)`. -/
abbrev RawAsmArg :=
  (Bool × ℕ × ℕ × Bool) ×
    (List RawRound × Allocation × List RawSlot × List RawSlot × FamilyGameHistory) ×
    (Bool × Bool × RawRound × Allocation × List RawSlot) ×
    (Bool × ℕ) × FamilyClientMove × FamilyServerMove

/-- The pure case distinction performed at the end of `rawStepWith`, with every
piece of round data supplied as an ordinary argument. -/
def rawStepAssemble (z : RawAsmArg) : RawState :=
  if z.1.1 then
    ((z.1.2.1 + 1, z.1.2.2.1, z.1.2.2.2), z.2.1)
  else if z.2.2.1.1 then
    ((z.1.2.1 + 1, z.1.2.1 + 1,
        z.2.2.2.1.1 ||
          decide (z.2.2.2.1.2 ≤ (z.2.1.1 ++ [z.2.2.1.2.2.1]).length)),
      (z.2.1.1 ++ [z.2.2.1.2.2.1], z.2.1.2.1 ++ z.2.2.1.2.2.2.1,
        z.2.2.1.2.2.2.2, [], ([], [])))
  else
    ((z.1.2.1 + 1, z.1.2.2.1, z.1.2.2.2),
      (z.2.1.1, z.2.1.2.1, z.2.1.2.2.1, z.2.1.2.2.2.1,
        (z.2.1.2.2.2.2.1 ++ [z.2.2.2.2.1],
          z.2.1.2.2.2.2.2 ++ [z.2.2.2.2.2])))

/-- The final case distinction of a raw transition is computable. -/
theorem computable_rawStepAssemble : Computable rawStepAssemble := by
  have hA : Computable fun z : RawAsmArg => z.1 := Computable.fst
  have hB : Computable fun z : RawAsmArg => z.2.1 := Computable.fst.comp Computable.snd
  have hC : Computable fun z : RawAsmArg => z.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hD : Computable fun z : RawAsmArg => z.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hEF : Computable fun z : RawAsmArg => z.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hcond : Computable fun z : RawAsmArg => z.1.1 := Computable.fst.comp hA
  have htime : Computable fun z : RawAsmArg => z.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hA)
  have hstart : Computable fun z : RawAsmArg => z.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hA))
  have hdone : Computable fun z : RawAsmArg => z.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hA))
  have hfrozen : Computable fun z : RawAsmArg => z.2.1.1 := Computable.fst.comp hB
  have hunav : Computable fun z : RawAsmArg => z.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hB)
  have hslots : Computable fun z : RawAsmArg => z.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hB))
  have hanchors : Computable fun z : RawAsmArg => z.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hB)))
  have hhist : Computable fun z : RawAsmArg => z.2.1.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hB)))
  have hgoal : Computable fun z : RawAsmArg => z.2.2.1.1 := Computable.fst.comp hC
  have hunanchored : Computable fun z : RawAsmArg => z.2.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hC)
  have hround : Computable fun z : RawAsmArg => z.2.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hC))
  have hnbrs : Computable fun z : RawAsmArg => z.2.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hC)))
  have hcand : Computable fun z : RawAsmArg => z.2.2.1.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hC)))
  have hperroot : Computable fun z : RawAsmArg => z.2.2.2.1.1 := Computable.fst.comp hD
  have hrc : Computable fun z : RawAsmArg => z.2.2.2.1.2 := Computable.snd.comp hD
  have hcur : Computable fun z : RawAsmArg => z.2.2.2.2.1 := Computable.fst.comp hEF
  have hsm : Computable fun z : RawAsmArg => z.2.2.2.2.2 := Computable.snd.comp hEF
  have hsucc : Computable fun z : RawAsmArg => z.1.2.1 + 1 :=
    Primrec.succ.to_comp.comp htime
  have hfrozen' : Computable fun z : RawAsmArg => z.2.1.1 ++ [z.2.2.1.2.2.1] :=
    Primrec.list_append.to_comp.comp hfrozen
      (Computable.list_cons.comp hround (Computable.const []))
  have hunav' : Computable fun z : RawAsmArg =>
      z.2.1.2.1 ++ z.2.2.1.2.2.2.1 :=
    Primrec.list_append.to_comp.comp hunav hnbrs
  have hthen : Computable fun z : RawAsmArg =>
      (((z.1.2.1 + 1, z.1.2.2.1, z.1.2.2.2), z.2.1) : RawState) :=
    (hsucc.pair (hstart.pair hdone)).pair hB
  have hle2 : Computable fun z : RawAsmArg =>
      decide (z.2.2.2.1.2 ≤ (z.2.1.1 ++ [z.2.2.1.2.2.1]).length) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp hrc
      (Primrec.list_length.to_comp.comp hfrozen')
  have hdone' : Computable fun z : RawAsmArg =>
      (z.2.2.2.1.1 ||
        decide (z.2.2.2.1.2 ≤ (z.2.1.1 ++ [z.2.2.1.2.2.1]).length)) := by
    refine (Computable.cond hperroot (Computable.const true) hle2).of_eq fun z => ?_
    cases z.2.2.2.1.1 <;> simp
  have hcontinue : Computable fun z : RawAsmArg =>
      (((z.1.2.1 + 1, z.1.2.1 + 1,
          z.2.2.2.1.1 ||
            decide (z.2.2.2.1.2 ≤ (z.2.1.1 ++ [z.2.2.1.2.2.1]).length)),
        (z.2.1.1 ++ [z.2.2.1.2.2.1], z.2.1.2.1 ++ z.2.2.1.2.2.2.1,
          z.2.2.1.2.2.2.2, [], (([], []) : FamilyGameHistory))) : RawState) :=
    (hsucc.pair (hsucc.pair hdone')).pair
      (hfrozen'.pair (hunav'.pair (hcand.pair
        ((Computable.const []).pair
          (Computable.const (([], []) : FamilyGameHistory))))))
  have hlose : Computable fun z : RawAsmArg =>
      (((z.1.2.1 + 1, z.1.2.2.1, z.1.2.2.2),
        (z.2.1.1, z.2.1.2.1, z.2.1.2.2.1, z.2.1.2.2.2.1,
          ((z.2.1.2.2.2.2.1 ++ [z.2.2.2.2.1],
            z.2.1.2.2.2.2.2 ++ [z.2.2.2.2.2]) : FamilyGameHistory))) : RawState) :=
    (hsucc.pair (hstart.pair hdone)).pair
      (hfrozen.pair (hunav.pair (hslots.pair (hanchors.pair
        ((Primrec.list_append.to_comp.comp (Computable.fst.comp hhist)
            (Computable.list_cons.comp hcur (Computable.const []))).pair
          (Primrec.list_append.to_comp.comp (Computable.snd.comp hhist)
            (Computable.list_cons.comp hsm (Computable.const []))))))))
  refine (Computable.cond hcond hthen
    (Computable.cond hgoal hcontinue hlose)).of_eq fun z => ?_
  rw [rawStepAssemble]
  cases z.1.1 <;> cases z.2.2.1.1 <;> simp

/-- The local server move extracted during a raw step is computable. -/
private theorem computable_rawStepWith_localServerMove :
    Computable fun x : RawStepArg =>
      rawLocalServerMove
        (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length)
        x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1 := by
  have hq : Computable fun x : RawStepArg => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hL : Computable fun x : RawStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have he : Computable fun x : RawStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hb : Computable fun x : RawStepArg => x.1.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hst : Computable fun x : RawStepArg => x.2.1 := Computable.fst.comp Computable.snd
  have hsm : Computable fun x : RawStepArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hfrozen : Computable fun x : RawStepArg => x.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hst)
  have hslots : Computable fun x : RawStepArg => x.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hst)))
  have hr : Computable fun x : RawStepArg => x.2.1.2.1.length :=
    Primrec.list_length.to_comp.comp hfrozen
  have hdelta : Computable fun x : RawStepArg =>
      grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length :=
    (computable_grayTailRoundDelta.comp (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have hlocalarg : Computable fun x : RawStepArg =>
      (((grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length, x.1.2.1.2),
        x.2.1.2.2.2.1, x.2.2.1) : (ℕ × ℕ) × List RawSlot × FamilyServerMove) :=
    (hdelta.pair hb).pair (hslots.pair hsm)
  exact (computable_rawLocalServerMove.comp hlocalarg).of_eq fun _ => rfl

/-- The robust Gray goal test in a raw step is computable. -/
private theorem computable_rawStepWith_goal :
    Computable fun x : RawStepArg =>
      familyRobustGrayGoalAtB (halfAmplification x.1.1.1)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth x.1.1.1 x.1.1.2.2.2))
        (grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length)
        (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length)
        x.2.1.2.2.2.1.length x.2.1.2.2.1 x.2.2.2
        (rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
          x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1) := by
  have hq : Computable fun x : RawStepArg => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hL : Computable fun x : RawStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have he : Computable fun x : RawStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hst : Computable fun x : RawStepArg => x.2.1 := Computable.fst.comp Computable.snd
  have hcur : Computable fun x : RawStepArg => x.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hfrozen : Computable fun x : RawStepArg => x.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hst)
  have hunav : Computable fun x : RawStepArg => x.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hst))
  have hslots : Computable fun x : RawStepArg => x.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hst)))
  have hr : Computable fun x : RawStepArg => x.2.1.2.1.length :=
    Primrec.list_length.to_comp.comp hfrozen
  have heps : Computable fun x : RawStepArg =>
      grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length :=
    (computable_grayTailRoundEps.comp (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have hdelta : Computable fun x : RawStepArg =>
      grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length :=
    (computable_grayTailRoundDelta.comp (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have hlocal := computable_rawStepWith_localServerMove
  have hkappa : Computable fun x : RawStepArg => halfAmplification x.1.1.1 :=
    computable_halfAmplification.comp hq
  have hcall : Computable fun x : RawStepArg => grayCallDepth x.1.1.1 x.1.1.2.2.2 :=
    computable_grayCallDepth.comp hq he
  have hbeta : Computable fun x : RawStepArg =>
      (3 / 4 : ℚ) * dyadicScale (grayCallDepth x.1.1.1 x.1.1.2.2.2) :=
    computable₂_ratMul.comp (Computable.const ((3 : ℚ) / 4))
      (computable_dyadicScale.comp hcall)
  have hgoalarg : Computable fun x : RawStepArg =>
      (((halfAmplification x.1.1.1,
          (3 / 4 : ℚ) * dyadicScale (grayCallDepth x.1.1.1 x.1.1.2.2.2)),
        (grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length,
          grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length,
          x.2.1.2.2.2.1.length),
        x.2.1.2.2.1, x.2.2.2,
        rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
          x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1) :
        (ℚ × ℚ) × (ℕ × ℕ × ℕ) × Allocation × FamilyClientMove × FamilyServerMove) :=
    (hkappa.pair hbeta).pair
      ((heps.pair (hdelta.pair (Primrec.list_length.to_comp.comp hslots))).pair
        (hunav.pair (hcur.pair hlocal)))
  exact (computable_familyRobustGrayGoalAtB_joint.comp hgoalarg).of_eq fun _ => rfl

/-- The frozen ledger of a raw step after the round currently being played has been appended. -/
private abbrev rawStepFrozen (x : RawStepArg) : List RawRound :=
  x.2.1.2.1 ++ [((x.2.1.2.1.length, x.2.1.1.1,
      grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length),
    x.2.1.2.2.2.1, x.2.2.2,
    grayTailLocalAllocatedList
      (rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
        x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1),
    x.2.1.2.2.1)]

/-- The candidate next slots of a raw step: the slots produced from the appended ledger
`rawStepFrozen x` at the tail exit threshold. -/
private abbrev rawStepNextSlots (x : RawStepArg) :=
  rawNextSlots x.1.2.1.1 x.1.2.1.2 x.1.1.2.2.2 (2 ^ (x.1.1.2.2.2 - x.1.1.2.2.1))
    (rawStepFrozen x).length
    (dyadicScale x.1.1.2.2.2 - dyadicScale x.1.1.2.2.2 / (6 * halfAmplification x.1.1.1))
    x.1.2.2 (rawStepFrozen x) x.2.2.1

/-- The candidate next slots constructed during a raw step are computable. -/
private theorem computable_rawStepWith_nextSlots :
    Computable fun x : RawStepArg => rawStepNextSlots x := by
  have hq : Computable fun x : RawStepArg => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hL : Computable fun x : RawStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ha : Computable fun x : RawStepArg => x.1.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have he : Computable fun x : RawStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hn : Computable fun x : RawStepArg => x.1.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hb : Computable fun x : RawStepArg => x.1.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hA : Computable fun x : RawStepArg => x.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hst : Computable fun x : RawStepArg => x.2.1 := Computable.fst.comp Computable.snd
  have hsm : Computable fun x : RawStepArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hcur : Computable fun x : RawStepArg => x.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have htime : Computable fun x : RawStepArg => x.2.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp hst)
  have hfrozen : Computable fun x : RawStepArg => x.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hst)
  have hunav : Computable fun x : RawStepArg => x.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hst))
  have hslots : Computable fun x : RawStepArg => x.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hst)))
  have hr : Computable fun x : RawStepArg => x.2.1.2.1.length :=
    Primrec.list_length.to_comp.comp hfrozen
  have heps : Computable fun x : RawStepArg =>
      grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length :=
    (computable_grayTailRoundEps.comp (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have hlocal := computable_rawStepWith_localServerMove
  have halloc : Computable fun x : RawStepArg =>
      grayTailLocalAllocatedList
        (rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
          x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1) :=
    computable_grayTailLocalAllocatedList.comp hlocal
  have hnewround : Computable fun x : RawStepArg =>
      ([((x.2.1.2.1.length, x.2.1.1.1,
            grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length),
          x.2.1.2.2.2.1, x.2.2.2,
          grayTailLocalAllocatedList
            (rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
              x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1),
          x.2.1.2.2.1)] : List RawRound) :=
    Computable.list_cons.comp
      ((hr.pair (htime.pair heps)).pair
        (hslots.pair (hcur.pair (halloc.pair hunav)))) (Computable.const [])
  have hfrozen' : Computable fun x : RawStepArg =>
      x.2.1.2.1 ++ [((x.2.1.2.1.length, x.2.1.1.1,
          grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length),
        x.2.1.2.2.2.1, x.2.2.2,
        grayTailLocalAllocatedList
          (rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
            x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1),
        x.2.1.2.2.1)] :=
    Primrec.list_append.to_comp.comp hfrozen hnewround
  have hthr : Computable fun x : RawStepArg =>
      dyadicScale x.1.1.2.2.2 -
        dyadicScale x.1.1.2.2.2 / (6 * halfAmplification x.1.1.1) :=
    computable₂_rawThreshold.comp hq he
  have hpow : Computable fun x : RawStepArg => 2 ^ (x.1.1.2.2.2 - x.1.1.2.2.1) :=
    (nat_pow_primrec₂.to_comp.comp (Computable.const 2)
      (Primrec.nat_sub.to_comp.comp he ha))
  have hcandarg : Computable fun x : RawStepArg =>
      (((x.1.2.1.1, x.1.2.1.2, x.1.1.2.2.2, 2 ^ (x.1.1.2.2.2 - x.1.1.2.2.1),
          (x.2.1.2.1 ++ [((x.2.1.2.1.length, x.2.1.1.1,
              grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length),
            x.2.1.2.2.2.1, x.2.2.2,
            grayTailLocalAllocatedList
              (rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
                x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1),
            x.2.1.2.2.1)]).length),
        dyadicScale x.1.1.2.2.2 -
          dyadicScale x.1.1.2.2.2 / (6 * halfAmplification x.1.1.1),
        x.1.2.2,
        x.2.1.2.1 ++ [((x.2.1.2.1.length, x.2.1.1.1,
            grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length),
          x.2.1.2.2.2.1, x.2.2.2,
          grayTailLocalAllocatedList
            (rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
              x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1),
          x.2.1.2.2.1)],
        x.2.2.1) : RawNextArg) :=
    (hn.pair (hb.pair (he.pair (hpow.pair
      (Primrec.list_length.to_comp.comp hfrozen'))))).pair
      (hthr.pair (hA.pair (hfrozen'.pair hsm)))
  exact (computable_rawNextSlots.comp hcandarg).of_eq fun _ => rfl

/-- The global quarter test evaluation during a raw step is computable. -/
private theorem computable_rawStepWith_globalQuarterB :
    Computable fun x : RawStepArg =>
      rawGlobalQuarterB x.1.2.1.1 (2 ^ (x.1.1.2.2.2 - x.1.1.2.2.1))
        (rawStepNextSlots x) := by
  have hn : Computable fun x : RawStepArg => x.1.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have ha : Computable fun x : RawStepArg => x.1.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have he : Computable fun x : RawStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hpow : Computable fun x : RawStepArg => 2 ^ (x.1.1.2.2.2 - x.1.1.2.2.1) :=
    (nat_pow_primrec₂.to_comp.comp (Computable.const 2)
      (Primrec.nat_sub.to_comp.comp he ha))
  have hcand := computable_rawStepWith_nextSlots
  exact (computable_rawGlobalQuarterB.comp ((hn.pair hpow).pair hcand)).of_eq fun _ => rfl

/-- The raw tail step, fed the current move, is computable in its arguments. -/
theorem computable_rawStepWith :
    Computable fun x : RawStepArg =>
      rawStepWith x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2 x.1.2.1.1 x.1.2.1.2
        x.1.2.2 x.2.1 x.2.2.1 x.2.2.2 := by
  -- parameters
  have hq : Computable fun x : RawStepArg => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hL : Computable fun x : RawStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have he : Computable fun x : RawStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hn : Computable fun x : RawStepArg => x.1.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hb : Computable fun x : RawStepArg => x.1.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hA : Computable fun x : RawStepArg => x.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  -- state components
  have hst : Computable fun x : RawStepArg => x.2.1 := Computable.fst.comp Computable.snd
  have hsm : Computable fun x : RawStepArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hcur : Computable fun x : RawStepArg => x.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have htime : Computable fun x : RawStepArg => x.2.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp hst)
  have hstart : Computable fun x : RawStepArg => x.2.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hdone : Computable fun x : RawStepArg => x.2.1.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hfrozen : Computable fun x : RawStepArg => x.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hst)
  have hunav : Computable fun x : RawStepArg => x.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hst))
  have hslots : Computable fun x : RawStepArg => x.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hst)))
  have hanchors : Computable fun x : RawStepArg => x.2.1.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hst))))
  have hhist : Computable fun x : RawStepArg => x.2.1.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hst))))
  -- round data & sub-computations
  have hr : Computable fun x : RawStepArg => x.2.1.2.1.length :=
    Primrec.list_length.to_comp.comp hfrozen
  have heps : Computable fun x : RawStepArg =>
      grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length :=
    (computable_grayTailRoundEps.comp (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have hlocal := computable_rawStepWith_localServerMove
  have hgoal := computable_rawStepWith_goal
  have hscanArg : Computable fun x : RawStepArg =>
      (((x.1.1.2.2.2, x.1.2.1.1, x.1.2.1.2), x.1.2.2,
        x.2.1.2.2.2.1, x.2.2.1) : RawReserveScanArg) :=
    (he.pair (hn.pair hb)).pair (hA.pair (hslots.pair hsm))
  have hunanchored : Computable fun x : RawStepArg =>
      rawHasUnanchoredReserveB x.1.1.2.2.2 x.1.2.1.1 x.1.2.1.2
        x.1.2.2 x.2.1.2.2.2.1 x.2.2.1 :=
    (computable_rawHasUnanchoredReserveB.comp hscanArg).of_eq fun _ => rfl
  have halloc : Computable fun x : RawStepArg =>
      grayTailLocalAllocatedList
        (rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
          x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1) :=
    computable_grayTailLocalAllocatedList.comp hlocal
  have hnbrs : Computable fun x : RawStepArg =>
      neighborhoodCellsList
        (grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length)
        (grayTailLocalAllocatedList
          (rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
            x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1)) :=
    computable_neighborhoodCellsList heps halloc
  have hcand := computable_rawStepWith_nextSlots
  have hglobal := computable_rawStepWith_globalQuarterB
  have hround : Computable fun x : RawStepArg =>
      (((x.2.1.2.1.length, x.2.1.1.1,
            grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length),
          x.2.1.2.2.2.1, x.2.2.2,
          grayTailLocalAllocatedList
            (rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2
              x.2.1.2.1.length) x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1),
          x.2.1.2.2.1) : RawRound) :=
    (hr.pair (htime.pair heps)).pair (hslots.pair (hcur.pair (halloc.pair hunav)))
  have hemp : Computable fun x : RawStepArg => x.2.1.2.2.2.1.isEmpty := by
    have hz : Computable fun x : RawStepArg => decide (x.2.1.2.2.2.1.length = 0) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Primrec.list_length.to_comp.comp hslots) (Computable.const 0)
    exact hz.of_eq fun x => (list_isEmpty_eq_decide _).symm
  have hcond : Computable fun x : RawStepArg =>
      (x.2.1.1.2.2 || x.2.1.2.2.2.1.isEmpty) := by
    refine (Computable.cond hdone (Computable.const true) hemp).of_eq fun x => ?_
    cases x.2.1.1.2.2 <;> simp
  have hrc : Computable fun x : RawStepArg => grayTailRoundCount x.1.1.1 :=
    primrec_grayTailRoundCount.to_comp.comp hq
  have harg := (hcond.pair (htime.pair (hstart.pair hdone))).pair
    ((hfrozen.pair (hunav.pair (hslots.pair (hanchors.pair hhist)))).pair
      ((hgoal.pair (hunanchored.pair (hround.pair (hnbrs.pair hcand)))).pair
        ((hglobal.pair hrc).pair (hcur.pair hlocal))))
  refine (computable_rawStepAssemble.comp harg).of_eq fun x => ?_
  cases hd : x.2.1.1.2.2 <;>
    cases hs : x.2.1.2.2.2.1.isEmpty <;>
      simp [rawWaitingB, rawStepAssemble, rawStepWith, rawStepNextSlots, rawStepFrozen,
        hd, hs]
/-- The raw displayed output of a state is computable in its arguments. -/
theorem computable_rawOutput :
    Computable fun x : RawParam × RawState × FamilyClientMove =>
      rawOutput x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2 x.1.2.1.1 x.1.2.1.2
        x.2.1 x.2.2 := by
  have hq : Computable fun x : RawParam × RawState × FamilyClientMove => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have ha : Computable fun x : RawParam × RawState × FamilyClientMove => x.1.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have he : Computable fun x : RawParam × RawState × FamilyClientMove => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hn : Computable fun x : RawParam × RawState × FamilyClientMove => x.1.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hb : Computable fun x : RawParam × RawState × FamilyClientMove => x.1.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hst : Computable fun x : RawParam × RawState × FamilyClientMove => x.2.1 :=
    Computable.fst.comp Computable.snd
  have hcur : Computable fun x : RawParam × RawState × FamilyClientMove => x.2.2 :=
    Computable.snd.comp Computable.snd
  have hdone : Computable fun x : RawParam × RawState × FamilyClientMove =>
      x.2.1.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hfrozen : Computable fun x : RawParam × RawState × FamilyClientMove =>
      x.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hst)
  have hslots : Computable fun x : RawParam × RawState × FamilyClientMove =>
      x.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hst)))
  have hanchors : Computable fun x : RawParam × RawState × FamilyClientMove =>
      x.2.1.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hst))))
  have hfloor : Computable fun x : RawParam × RawState × FamilyClientMove =>
      grayTailTargetFloor x.1.1.1 x.1.1.2.2.1 :=
    computable₂_grayTailTargetFloor.comp hq ha
  have hthr : Computable fun x : RawParam × RawState × FamilyClientMove =>
      dyadicScale x.1.1.2.2.2 -
        dyadicScale x.1.1.2.2.2 / (6 * halfAmplification x.1.1.1) :=
    computable₂_rawThreshold.comp hq he
  have hscale : Computable fun x : RawParam × RawState × FamilyClientMove =>
      dyadicScale x.1.1.2.2.2 :=
    computable_dyadicScale.comp he
  have hempty : Computable fun x : RawParam × RawState × FamilyClientMove =>
      x.2.1.2.2.2.2.1.isEmpty := by
    have hz : Computable fun x : RawParam × RawState × FamilyClientMove =>
        decide (x.2.1.2.2.2.2.1.length = 0) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Primrec.list_length.to_comp.comp hanchors) (Computable.const 0)
    exact hz.of_eq fun x => (list_isEmpty_eq_decide _).symm
  have hcond : Computable fun x : RawParam × RawState × FamilyClientMove =>
      rawAnchoringOutputB x.2.1 := by
    have hnot : Computable fun x : RawParam × RawState × FamilyClientMove =>
        !x.2.1.2.2.2.2.1.isEmpty :=
      Primrec.not.to_comp.comp hempty
    exact ((Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp.comp
      hdone hnot).of_eq fun _ => rfl
  have hmove : Computable fun x : RawParam × RawState × FamilyClientMove =>
      (if x.2.1.1.2.2 then [] else x.2.2 : FamilyClientMove) := by
    refine (Computable.cond hdone (Computable.const []) hcur).of_eq fun x => ?_
    cases x.2.1.1.2.2 <;> simp
  have hregularArg : Computable fun x : RawParam × RawState × FamilyClientMove =>
      (((x.2.1.1.2.2, grayTailTargetFloor x.1.1.1 x.1.1.2.2.1,
          dyadicScale x.1.1.2.2.2 -
            dyadicScale x.1.1.2.2.2 / (6 * halfAmplification x.1.1.1),
          dyadicScale x.1.1.2.2.2),
        (x.1.2.1.1, x.1.2.1.2),
        x.2.1.2.1, x.2.1.2.2.2.1,
        (if x.2.1.1.2.2 then [] else x.2.2 : FamilyClientMove)) :
        (Bool × ℚ × ℚ × ℚ) × (ℕ × ℕ) ×
          List RawRound × List RawSlot × FamilyClientMove) :=
    (hdone.pair (hfloor.pair (hthr.pair hscale))).pair
      ((hn.pair hb).pair (hfrozen.pair (hslots.pair hmove)))
  have hregular : Computable fun x : RawParam × RawState × FamilyClientMove =>
      rawFamilyMove x.2.1.1.2.2
        (grayTailTargetFloor x.1.1.1 x.1.1.2.2.1)
        (dyadicScale x.1.1.2.2.2 -
          dyadicScale x.1.1.2.2.2 / (6 * halfAmplification x.1.1.1))
        (dyadicScale x.1.1.2.2.2) x.1.2.1.1 x.1.2.1.2
        x.2.1.2.1 x.2.1.2.2.2.1
        (if x.2.1.1.2.2 then [] else x.2.2) :=
    (computable_rawFamilyMove.comp hregularArg).of_eq fun _ => rfl
  exact hregular.of_eq fun _ => rfl


/-- The query a raw state sends to the scheme is computable. -/
theorem computable_rawQuery :
    Computable fun x : (ℕ × ℕ × ℕ) × RawState =>
      rawQuery x.1.1 x.1.2.1 x.1.2.2 x.2 := by
  have hq : Computable fun x : (ℕ × ℕ × ℕ) × RawState => x.1.1 :=
    Computable.fst.comp Computable.fst
  have hL : Computable fun x : (ℕ × ℕ × ℕ) × RawState => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have he : Computable fun x : (ℕ × ℕ × ℕ) × RawState => x.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hfrozen : Computable fun x : (ℕ × ℕ × ℕ) × RawState => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hunav : Computable fun x : (ℕ × ℕ × ℕ) × RawState => x.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hslots : Computable fun x : (ℕ × ℕ × ℕ) × RawState => x.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd)))
  have hhist : Computable fun x : (ℕ × ℕ × ℕ) × RawState => x.2.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have hcall : Computable fun x : (ℕ × ℕ × ℕ) × RawState => grayCallDepth x.1.1 x.1.2.2 :=
    computable_grayCallDepth.comp hq he
  have heps : Computable fun x : (ℕ × ℕ × ℕ) × RawState =>
      grayTailRoundEps x.1.1 x.1.2.1 x.1.2.2 x.2.2.1.length :=
    (computable_grayTailRoundEps.comp
      (hq.pair (hL.pair (he.pair (Primrec.list_length.to_comp.comp hfrozen))))).of_eq
      fun _ => rfl
  exact ((hcall.pair heps).pair
    (hunav.pair ((Primrec.list_length.to_comp.comp hslots).pair hhist))).of_eq fun _ => rfl

/-! ### The three statements consumed by the oracle assembly -/

/-- **One erased controller transition is computable.** -/
theorem computable_rawStepOf :
    Computable fun x : RawParam × RawState × FamilyServerMove × FamilyClientMove =>
      rawStepOf x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  computable_rawStepWith.of_eq fun _ => rfl

/-- **The displayed move of an erased state is computable.** -/
theorem computable_rawOutputOf :
    Computable fun x : RawParam × RawState × FamilyClientMove =>
      rawOutputOf x.1 x.2.1 x.2.2 :=
  computable_rawOutput.of_eq fun _ => rfl

/-- **The subcall input of an erased state is computable.** -/
theorem computable_rawQueryOf :
    Computable fun x : RawParam × RawState => rawQueryOf x.1 x.2 := by
  have harg : Computable fun x : RawParam × RawState =>
      (((x.1.1.1, x.1.1.2.1, x.1.1.2.2.2), x.2) : (ℕ × ℕ × ℕ) × RawState) :=
    ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
          (Computable.fst.comp Computable.fst)))))).pair Computable.snd
  exact (computable_rawQuery.comp harg).of_eq fun _ => rfl

/-- **The initial erased state is computable.** -/
theorem computable_rawInitialStateOf : Computable rawInitialStateOf := by
  have harg : Computable fun P : RawParam =>
      (((P.2.1.1, P.2.1.2, P.1.2.2.1, P.1.2.2.2), P.2.2) : (ℕ × ℕ × ℕ × ℕ) × Allocation) :=
    ((Computable.fst.comp (Computable.fst.comp Computable.snd)).pair
      ((Computable.snd.comp (Computable.fst.comp Computable.snd)).pair
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
          (Computable.snd.comp (Computable.snd.comp
            (Computable.snd.comp Computable.fst)))))).pair
      (Computable.snd.comp Computable.snd)
  exact (computable_rawInitialState.comp harg).of_eq fun _ => rfl

/-- The encoded displayed move is computable. -/
theorem computable_rawOutputEnc :
    Computable fun x : RawParam × RawState × FamilyClientMove =>
      rawOutputEnc x.1 x.2.1 x.2.2 :=
  (Computable.encode.comp computable_rawOutputOf).of_eq fun _ => by
    rw [rawOutputEnc]

end Kolmogorov
