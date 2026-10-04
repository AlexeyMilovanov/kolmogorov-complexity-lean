import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedRawComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure

/-!
# Computability of the erased V2 advantage transition

The V2 twin of the first half of `GacsDayChargedStepComputable.lean`.  The
erased wide-block advantage transition `rawChargedBlockTailStepV2` performs a
two-level case distinction:

* the *tick* branch, taken when the core is done or has no live slots;
* the *accept* branch `rawBlockAcceptV2`, taken when the re-anchored block goal
  `grayChargedBlockGoalAtB` fires — it freezes a nine-field V2 round, recomputes
  the wide candidate block, and installs the per-round snapshot harvest;
* the *reject* branch `rawBlockRejectV2`, which only extends the history.

Both non-trivial branches are named, proved computable jointly in all their
arguments, and the transition is then the `cond` of the three
(`rawChargedBlockTailStepV2_eq_cond`).  This is the same decomposition V1 uses
(`chargedRawStepAssemble` / `chargedTailAsm`), specialised to the V2 record.
-/


namespace Kolmogorov

/-! ### The two non-trivial branches -/

/-- The V2 frozen ledger after an accepted wide-block advantage round. -/
def rawBlockFrozenV2 (q L e b : ℕ) (st : RawStateV2) (sm : FamilyServerMove)
    (current : FamilyClientMove) : List RawRoundV2 :=
  st.2.1 ++
    [((st.2.1.length, st.1.1, grayTailRoundEps q L e st.2.1.length,
        grayTailRoundEps q L e st.2.1.length + graySpendSpan q,
        grayTailRoundDelta q L e st.2.1.length),
      (st.2.2.2.1, current,
        grayTailLocalAllocatedList
          (rawLocalServerMove (grayTailRoundDelta q L e st.2.1.length) b
            st.2.2.2.1 sm),
        st.2.2.1))]

/-- The V2 core state produced by an accepted wide-block advantage round. -/
def rawBlockAcceptV2 (q L a e n b : ℕ) (A : Allocation) (st : RawStateV2)
    (sm : FamilyServerMove) (current : FamilyClientMove) : RawStateV2 :=
  let frozen' := rawBlockFrozenV2 q L e b st sm current
  let frozenV1 := rawFrozenV1OfV2 frozen'
  let threshold := dyadicScale e -
    dyadicScale e / (6 * halfAmplification q)
  let source := grayChargedSourceCount a e
  let candidates :=
    rawBlockNextSlots n b q L e source frozen'.length threshold A frozenV1 sm
  ((st.1.1 + 1, st.1.1 + 1,
      rawGlobalQuarterB n source
          (rawNextSlots n b e source frozen'.length threshold A frozenV1 sm) ||
        decide (grayChargedAdvantageRoundCount q ≤ frozen'.length)),
    (frozen',
      A ++ rawGrayHarvest (grayTailRoundDelta q L e frozen'.length) b
        candidates n sm,
      candidates, [], ([], [])))

/-- The V2 core state produced by a rejected advantage round. -/
def rawBlockRejectV2 (q L e b : ℕ) (st : RawStateV2) (sm : FamilyServerMove)
    (current : FamilyClientMove) : RawStateV2 :=
  ((st.1.1 + 1, st.1.2.1, st.1.2.2),
    (st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1,
      (st.2.2.2.2.2.1 ++ [current],
        st.2.2.2.2.2.2 ++
          [rawLocalServerMove (grayTailRoundDelta q L e st.2.1.length) b
            st.2.2.2.1 sm])))

/-- **The V2 advantage transition as a two-level `cond`** — the shape the
computability proof consumes. -/
theorem rawChargedBlockTailStepV2_eq_cond (q L a e n b : ℕ) (A : Allocation)
    (st : RawStateV2) (sm : FamilyServerMove) (current : FamilyClientMove) :
    rawChargedBlockTailStepV2 q L a e n b A st sm current =
      cond (st.1.2.2 || st.2.2.2.1.isEmpty)
        (((st.1.1 + 1, st.1.2.1, st.1.2.2), st.2) : RawStateV2)
        (cond (grayChargedBlockGoalAtB q L e st.2.1.length st.2.2.2.1.length
              st.2.2.1 current
              (rawLocalServerMove (grayTailRoundDelta q L e st.2.1.length) b
                st.2.2.2.1 sm))
          (rawBlockAcceptV2 q L a e n b A st sm current)
          (rawBlockRejectV2 q L e b st sm current)) := by
  by_cases h1 : st.1.2.2 = true
  · simp [rawChargedBlockTailStepV2, h1]
  · simp only [Bool.not_eq_true] at h1
    by_cases h2 : st.2.2.2.1.isEmpty = true
    · simp [rawChargedBlockTailStepV2, h1, h2]
    · simp only [Bool.not_eq_true] at h2
      by_cases h3 : grayChargedBlockGoalAtB q L e st.2.1.length
          st.2.2.2.1.length st.2.2.1 current
          (rawLocalServerMove (grayTailRoundDelta q L e st.2.1.length) b
            st.2.2.2.1 sm) = true
      · simp [rawChargedBlockTailStepV2, rawBlockAcceptV2, rawBlockFrozenV2,
          h1, h2, h3]
      · simp only [Bool.not_eq_true] at h3
        simp [rawChargedBlockTailStepV2, rawBlockRejectV2, h1, h2, h3]

/-! ### Computability of the branches -/

/-- The advantage round budget is computable in the stage. -/
theorem computable_grayChargedAdvantageRoundCount {X : Type} [Primcodable X]
    {fq : X → ℕ} (hq : Computable fq) :
    Computable fun x : X => grayChargedAdvantageRoundCount (fq x) :=
  (Primrec.nat_sub.to_comp.comp (primrec_grayTailRoundCount.to_comp.comp hq)
    (Computable.const 8)).of_eq fun _ => rfl

/-- The rejecting branch of a raw V2 block step is computable in computable parameters. -/
theorem computable_rawBlockRejectV2 {X : Type} [Primcodable X]
    {fq fL fe fb : X → ℕ} {fst : X → RawStateV2}
    {fsm : X → FamilyServerMove} {fcur : X → FamilyClientMove}
    (hq : Computable fq) (hL : Computable fL) (he : Computable fe)
    (hb : Computable fb) (hst : Computable fst) (hsm : Computable fsm)
    (hcur : Computable fcur) :
    Computable fun x : X =>
      rawBlockRejectV2 (fq x) (fL x) (fe x) (fb x) (fst x) (fsm x) (fcur x) := by
  have hbody : Computable fun x : X => (fst x).2 := Computable.snd.comp hst
  have htime : Computable fun x : X => (fst x).1.1 + 1 :=
    Primrec.succ.to_comp.comp (Computable.fst.comp (Computable.fst.comp hst))
  have hstart : Computable fun x : X => (fst x).1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hdone : Computable fun x : X => (fst x).1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hfrozen : Computable fun x : X => (fst x).2.1 := Computable.fst.comp hbody
  have hunav : Computable fun x : X => (fst x).2.2.1 :=
    Computable.fst.comp (Computable.snd.comp hbody)
  have hslots : Computable fun x : X => (fst x).2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hbody))
  have hanch : Computable fun x : X => (fst x).2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hbody)))
  have hh1 : Computable fun x : X => (fst x).2.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hbody))))
  have hh2 : Computable fun x : X => (fst x).2.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hbody))))
  have hr : Computable fun x : X => (fst x).2.1.length :=
    Primrec.list_length.to_comp.comp hfrozen
  have hdelta : Computable fun x : X =>
      grayTailRoundDelta (fq x) (fL x) (fe x) (fst x).2.1.length :=
    (computable_grayTailRoundDelta.comp
      (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have hlocal : Computable fun x : X =>
      rawLocalServerMove (grayTailRoundDelta (fq x) (fL x) (fe x)
        (fst x).2.1.length) (fb x) (fst x).2.2.2.1 (fsm x) :=
    (computable_rawLocalServerMove.comp
      ((hdelta.pair hb).pair (hslots.pair hsm))).of_eq fun _ => rfl
  have hnewH1 : Computable fun x : X => (fst x).2.2.2.2.2.1 ++ [fcur x] :=
    Primrec.list_append.to_comp.comp hh1
      (Computable.list_cons.comp hcur (Computable.const []))
  have hnewH2 : Computable fun x : X =>
      (fst x).2.2.2.2.2.2 ++
        [rawLocalServerMove (grayTailRoundDelta (fq x) (fL x) (fe x)
          (fst x).2.1.length) (fb x) (fst x).2.2.2.1 (fsm x)] :=
    Primrec.list_append.to_comp.comp hh2
      (Computable.list_cons.comp hlocal (Computable.const []))
  exact ((htime.pair (hstart.pair hdone)).pair
    (hfrozen.pair (hunav.pair (hslots.pair
      (hanch.pair (hnewH1.pair hnewH2)))))).of_eq fun _ => rfl

/-- The accepting branch of a raw V2 block step is computable in computable parameters. -/
theorem computable_rawBlockAcceptV2 {X : Type} [Primcodable X]
    {fq fL fa fe fn fb : X → ℕ} {fA : X → Allocation} {fst : X → RawStateV2}
    {fsm : X → FamilyServerMove} {fcur : X → FamilyClientMove}
    (hq : Computable fq) (hL : Computable fL) (ha : Computable fa)
    (he : Computable fe) (hn : Computable fn) (hb : Computable fb)
    (hA : Computable fA) (hst : Computable fst) (hsm : Computable fsm)
    (hcur : Computable fcur) :
    Computable fun x : X =>
      rawBlockAcceptV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x) (fA x)
        (fst x) (fsm x) (fcur x) := by
  have hbody : Computable fun x : X => (fst x).2 := Computable.snd.comp hst
  have htime : Computable fun x : X => (fst x).1.1 :=
    Computable.fst.comp (Computable.fst.comp hst)
  have htime1 : Computable fun x : X => (fst x).1.1 + 1 :=
    Primrec.succ.to_comp.comp htime
  have hfrozen : Computable fun x : X => (fst x).2.1 := Computable.fst.comp hbody
  have hunav : Computable fun x : X => (fst x).2.2.1 :=
    Computable.fst.comp (Computable.snd.comp hbody)
  have hslots : Computable fun x : X => (fst x).2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hbody))
  have hr : Computable fun x : X => (fst x).2.1.length :=
    Primrec.list_length.to_comp.comp hfrozen
  have heps : Computable fun x : X =>
      grayTailRoundEps (fq x) (fL x) (fe x) (fst x).2.1.length :=
    (computable_grayTailRoundEps.comp
      (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have hdelta : Computable fun x : X =>
      grayTailRoundDelta (fq x) (fL x) (fe x) (fst x).2.1.length :=
    (computable_grayTailRoundDelta.comp
      (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have hlocal : Computable fun x : X =>
      rawLocalServerMove (grayTailRoundDelta (fq x) (fL x) (fe x)
        (fst x).2.1.length) (fb x) (fst x).2.2.2.1 (fsm x) :=
    (computable_rawLocalServerMove.comp
      ((hdelta.pair hb).pair (hslots.pair hsm))).of_eq fun _ => rfl
  have halloc : Computable fun x : X =>
      grayTailLocalAllocatedList
        (rawLocalServerMove (grayTailRoundDelta (fq x) (fL x) (fe x)
          (fst x).2.1.length) (fb x) (fst x).2.2.2.1 (fsm x)) :=
    computable_grayTailLocalAllocatedList.comp hlocal
  have hspan : Computable fun x : X => graySpendSpan (fq x) :=
    primrec_graySpendSpan.to_comp.comp hq
  have hchild : Computable fun x : X =>
      grayTailRoundEps (fq x) (fL x) (fe x) (fst x).2.1.length +
        graySpendSpan (fq x) :=
    Primrec.nat_add.to_comp.comp heps hspan
  have hround : Computable fun x : X =>
      ((((fst x).2.1.length, (fst x).1.1,
          grayTailRoundEps (fq x) (fL x) (fe x) (fst x).2.1.length,
          grayTailRoundEps (fq x) (fL x) (fe x) (fst x).2.1.length +
            graySpendSpan (fq x),
          grayTailRoundDelta (fq x) (fL x) (fe x) (fst x).2.1.length),
        ((fst x).2.2.2.1, fcur x,
          grayTailLocalAllocatedList
            (rawLocalServerMove (grayTailRoundDelta (fq x) (fL x) (fe x)
              (fst x).2.1.length) (fb x) (fst x).2.2.2.1 (fsm x)),
          (fst x).2.2.1)) : RawRoundV2) :=
    (hr.pair (htime.pair (heps.pair (hchild.pair hdelta)))).pair
      (hslots.pair (hcur.pair (halloc.pair hunav)))
  have hfrozen' : Computable fun x : X =>
      rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x) (fst x) (fsm x) (fcur x) :=
    (Primrec.list_append.to_comp.comp hfrozen
      (Computable.list_cons.comp hround (Computable.const []))).of_eq
      fun _ => rfl
  have hlen' : Computable fun x : X =>
      (rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x) (fst x) (fsm x)
        (fcur x)).length :=
    Primrec.list_length.to_comp.comp hfrozen'
  have hfrv1 : Computable fun x : X =>
      rawFrozenV1OfV2 (rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x) (fst x)
        (fsm x) (fcur x)) :=
    computable_rawFrozenV1OfV2 hfrozen'
  have hthr : Computable fun x : X =>
      dyadicScale (fe x) - dyadicScale (fe x) / (6 * halfAmplification (fq x)) :=
    computable₂_rawThreshold.comp hq he
  have hsource : Computable fun x : X => grayChargedSourceCount (fa x) (fe x) :=
    computable_grayChargedSourceCount ha he
  have hcand : Computable fun x : X =>
      rawBlockNextSlots (fn x) (fb x) (fq x) (fL x) (fe x)
        (grayChargedSourceCount (fa x) (fe x))
        (rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x) (fst x) (fsm x)
          (fcur x)).length
        (dyadicScale (fe x) -
          dyadicScale (fe x) / (6 * halfAmplification (fq x)))
        (fA x)
        (rawFrozenV1OfV2 (rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x) (fst x)
          (fsm x) (fcur x))) (fsm x) :=
    computable_rawBlockNextSlots hn hb hq hL he hsource hlen' hthr hA hfrv1 hsm
  have hnarrow : Computable fun x : X =>
      rawNextSlots (fn x) (fb x) (fe x)
        (grayChargedSourceCount (fa x) (fe x))
        (rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x) (fst x) (fsm x)
          (fcur x)).length
        (dyadicScale (fe x) -
          dyadicScale (fe x) / (6 * halfAmplification (fq x)))
        (fA x)
        (rawFrozenV1OfV2 (rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x) (fst x)
          (fsm x) (fcur x))) (fsm x) :=
    (computable_rawNextSlots.comp
      ((hn.pair (hb.pair (he.pair (hsource.pair hlen')))).pair
        (hthr.pair (hA.pair (hfrv1.pair hsm))))).of_eq fun _ => rfl
  have hquarter : Computable fun x : X =>
      rawGlobalQuarterB (fn x) (grayChargedSourceCount (fa x) (fe x))
        (rawNextSlots (fn x) (fb x) (fe x)
          (grayChargedSourceCount (fa x) (fe x))
          (rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x) (fst x) (fsm x)
            (fcur x)).length
          (dyadicScale (fe x) -
            dyadicScale (fe x) / (6 * halfAmplification (fq x)))
          (fA x)
          (rawFrozenV1OfV2 (rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x)
            (fst x) (fsm x) (fcur x))) (fsm x)) :=
    (computable_rawGlobalQuarterB.comp
      ((hn.pair hsource).pair hnarrow)).of_eq fun _ => rfl
  have hbudget : Computable fun x : X =>
      decide (grayChargedAdvantageRoundCount (fq x) ≤
        (rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x) (fst x) (fsm x)
          (fcur x)).length) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp
      (computable_grayChargedAdvantageRoundCount hq) hlen'
  have hor : Computable₂ fun a b : Bool => a || b :=
    (Primrec.dom_bool₂ (fun a b => a || b)).to_comp
  have hdone' := hor.comp hquarter hbudget
  have hdeltaNext : Computable fun x : X =>
      grayTailRoundDelta (fq x) (fL x) (fe x)
        (rawBlockFrozenV2 (fq x) (fL x) (fe x) (fb x) (fst x) (fsm x)
          (fcur x)).length :=
    (computable_grayTailRoundDelta.comp
      (hq.pair (hL.pair (he.pair hlen')))).of_eq fun _ => rfl
  have hharv := Primrec.list_append.to_comp.comp hA
    (computable_rawGrayHarvest hdeltaNext hb hcand hn hsm)
  exact ((htime1.pair (htime1.pair hdone')).pair
    (hfrozen'.pair (hharv.pair (hcand.pair
      ((Computable.const ([] : List RawSlot)).pair
        (Computable.const (([], []) : FamilyGameHistory))))))).of_eq
    fun _ => rfl

/-- **The erased V2 advantage transition is computable** jointly in all its
arguments. -/
theorem computable_rawChargedBlockTailStepV2 {X : Type} [Primcodable X]
    {fq fL fa fe fn fb : X → ℕ} {fA : X → Allocation} {fst : X → RawStateV2}
    {fsm : X → FamilyServerMove} {fcur : X → FamilyClientMove}
    (hq : Computable fq) (hL : Computable fL) (ha : Computable fa)
    (he : Computable fe) (hn : Computable fn) (hb : Computable fb)
    (hA : Computable fA) (hst : Computable fst) (hsm : Computable fsm)
    (hcur : Computable fcur) :
    Computable fun x : X =>
      rawChargedBlockTailStepV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
        (fA x) (fst x) (fsm x) (fcur x) := by
  have hbody : Computable fun x : X => (fst x).2 := Computable.snd.comp hst
  have htime1 : Computable fun x : X => (fst x).1.1 + 1 :=
    Primrec.succ.to_comp.comp (Computable.fst.comp (Computable.fst.comp hst))
  have hstart : Computable fun x : X => (fst x).1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hdone : Computable fun x : X => (fst x).1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hfrozen : Computable fun x : X => (fst x).2.1 := Computable.fst.comp hbody
  have hunav : Computable fun x : X => (fst x).2.2.1 :=
    Computable.fst.comp (Computable.snd.comp hbody)
  have hslots : Computable fun x : X => (fst x).2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hbody))
  have hr : Computable fun x : X => (fst x).2.1.length :=
    Primrec.list_length.to_comp.comp hfrozen
  have hdelta : Computable fun x : X =>
      grayTailRoundDelta (fq x) (fL x) (fe x) (fst x).2.1.length :=
    (computable_grayTailRoundDelta.comp
      (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have hlocal : Computable fun x : X =>
      rawLocalServerMove (grayTailRoundDelta (fq x) (fL x) (fe x)
        (fst x).2.1.length) (fb x) (fst x).2.2.2.1 (fsm x) :=
    (computable_rawLocalServerMove.comp
      ((hdelta.pair hb).pair (hslots.pair hsm))).of_eq fun _ => rfl
  have hemp : Computable fun x : X => (fst x).2.2.2.1.isEmpty := by
    have hz : Computable fun x : X => decide ((fst x).2.2.2.1.length = 0) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Primrec.list_length.to_comp.comp hslots) (Computable.const 0)
    exact hz.of_eq fun x => (list_isEmpty_eq_decide _).symm
  have hor : Computable₂ fun a b : Bool => a || b :=
    (Primrec.dom_bool₂ (fun a b => a || b)).to_comp
  have hguard : Computable fun x : X =>
      (fst x).1.2.2 || (fst x).2.2.2.1.isEmpty := hor.comp hdone hemp
  have htick : Computable fun x : X =>
      ((((fst x).1.1 + 1, (fst x).1.2.1, (fst x).1.2.2), (fst x).2) :
        RawStateV2) :=
    (htime1.pair (hstart.pair hdone)).pair hbody
  have hgoal : Computable fun x : X =>
      grayChargedBlockGoalAtB (fq x) (fL x) (fe x) (fst x).2.1.length
        (fst x).2.2.2.1.length (fst x).2.2.1 (fcur x)
        (rawLocalServerMove (grayTailRoundDelta (fq x) (fL x) (fe x)
          (fst x).2.1.length) (fb x) (fst x).2.2.2.1 (fsm x)) :=
    computable_grayChargedBlockGoalAtB hq hL he hr
      (Primrec.list_length.to_comp.comp hslots) hunav hcur hlocal
  have hacc := computable_rawBlockAcceptV2 hq hL ha he hn hb hA hst hsm hcur
  have hrej := computable_rawBlockRejectV2 hq hL he hb hst hsm hcur
  refine (Computable.cond hguard htick
    (Computable.cond hgoal hacc hrej)).of_eq fun x => ?_
  exact (rawChargedBlockTailStepV2_eq_cond (fq x) (fL x) (fa x) (fe x) (fn x)
    (fb x) (fA x) (fst x) (fsm x) (fcur x)).symm

/-! ### The phase-tagged V2 transition -/

/-- The V2 frozen ledger after an accepted spend pass. -/
def rawSpendFrozenV2 (q L a e b tag : ℕ) (st : RawStateV2)
    (sm : FamilyServerMove) (current : FamilyClientMove) : List RawRoundV2 :=
  st.2.1 ++
    [((st.2.1.length, st.1.1, grayChargedSpendEps a L e (tag - 2),
        grayChargedSpendEps a L e (tag - 2) + graySpendSpan q,
        grayChargedSpendDelta a L e (tag - 2)),
      (st.2.2.2.1, current,
        grayTailLocalAllocatedList
          (rawLocalServerMove (grayChargedSpendDelta a L e (tag - 2)) b
            st.2.2.2.1 sm),
        st.2.2.1))]

/-- The V2 charged state produced by an accepted spend pass: the next pass if
one remains and it has slots, otherwise the terminal state. -/
def rawSpendAcceptV2 (q L a e n b tag : ℕ) (A : Allocation) (st : RawStateV2)
    (sm : FamilyServerMove) (current : FamilyClientMove) : RawChargedStateV2 :=
  let frozen' := rawSpendFrozenV2 q L a e b tag st sm current
  let slotsNext := rawChargedSlotsForPassV2 q L a e n b (tag - 2 + 1) frozen'
  let unavailable' := A ++
    rawGrayHarvest (grayChargedSpendDelta a L e (tag - 2 + 1)) b slotsNext n sm
  cond (decide (tag - 2 + 1 < 8) && !slotsNext.isEmpty)
    (tag - 2 + 3, ((st.1.1 + 1, st.1.1 + 1, false),
      (frozen', unavailable', slotsNext, [], ([], []))))
    ((1 : ℕ), ((st.1.1 + 1, st.1.1 + 1, true),
      (frozen', unavailable', [], [], ([], []))))

/-- The V2 charged state produced by a rejected spend round. -/
def rawSpendRejectV2 (a L e b tag : ℕ) (st : RawStateV2)
    (sm : FamilyServerMove) (current : FamilyClientMove) : RawChargedStateV2 :=
  (tag, ((st.1.1 + 1, st.1.2.1, st.1.2.2),
    (st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1,
      (st.2.2.2.2.2.1 ++ [current],
        st.2.2.2.2.2.2 ++
          [rawLocalServerMove (grayChargedSpendDelta a L e (tag - 2)) b
            st.2.2.2.1 sm]))))

/-- **The phase-tagged V2 transition as a nest of `cond`s** — the shape the
computability proof consumes.  The advantage arm carries the v15.1 wait:
a done stepped core exits only when `rawChargedWaitServedB` holds. -/
theorem rawChargedStepV2With_eq_cond (q L a e n b : ℕ) (A : Allocation)
    (tag : ℕ) (st : RawStateV2) (sm : FamilyServerMove)
    (current : FamilyClientMove) :
    rawChargedStepV2With q L a e n b A tag st sm current =
      cond (decide (tag = 1))
        (((1 : ℕ), ((st.1.1 + 1, st.1.2.1, st.1.2.2), st.2)) : RawChargedStateV2)
        (cond (decide (tag = 0))
          (cond (rawChargedBlockTailStepV2 q L a e n b A st sm current).1.2.2
            (cond (rawChargedWaitServedB q a e n b
                (rawChargedBlockTailStepV2 q L a e n b A st sm current) sm)
              (rawChargedStartSpendV2 q L a e n b A
                (rawChargedBlockTailStepV2 q L a e n b A st sm current) sm)
              ((0 : ℕ), rawChargedBlockTailStepV2 q L a e n b A st sm current))
            ((0 : ℕ), rawChargedBlockTailStepV2 q L a e n b A st sm current))
          (cond st.2.2.2.1.isEmpty
            (((1 : ℕ), ((st.1.1 + 1, st.1.2.1, true), st.2)) :
              RawChargedStateV2)
            (cond (grayChargedBlockSpendGoalAtB q L a e (tag - 2)
                st.2.2.2.1.length st.2.2.1 current
                (rawLocalServerMove (grayChargedSpendDelta a L e (tag - 2)) b
                  st.2.2.2.1 sm))
              (rawSpendAcceptV2 q L a e n b tag A st sm current)
              (rawSpendRejectV2 a L e b tag st sm current)))) := by
  unfold rawChargedStepV2With
  by_cases h1 : tag = 1
  · simp [h1]
  · rw [ite_eq_right h1]
    by_cases h0 : tag = 0
    · rw [ite_eq_left h0]
      simp only [h0, decide_true, Bool.cond_true]
      by_cases hd : (rawChargedBlockTailStepV2 q L a e n b A st sm current).1.2.2 = true
      · rw [ite_eq_left hd]
        simp only [hd, Bool.cond_true]
        by_cases hw : rawChargedWaitServedB q a e n b
            (rawChargedBlockTailStepV2 q L a e n b A st sm current) sm = true
        · rw [ite_eq_left hw]
          simp [hw]
        · simp only [Bool.not_eq_true] at hw
          rw [ite_eq_right (by simp [hw])]
          simp [hw]
      · simp only [Bool.not_eq_true] at hd
        rw [ite_eq_right (by simp [hd])]
        simp [hd]
    · rw [ite_eq_right h0]
      simp only [h1, h0, decide_false, Bool.cond_false]
      by_cases hs : st.2.2.2.1.isEmpty = true
      · simp [hs]
      · simp only [Bool.not_eq_true] at hs
        rw [ite_eq_right (by simp [hs])]
        simp only [hs, Bool.cond_false]
        by_cases hg : grayChargedBlockSpendGoalAtB q L a e (tag - 2)
            st.2.2.2.1.length st.2.2.1 current
            (rawLocalServerMove (grayChargedSpendDelta a L e (tag - 2)) b
              st.2.2.2.1 sm) = true
        · rw [ite_eq_left hg]
          simp only [hg, Bool.cond_true, rawSpendAcceptV2, rawSpendFrozenV2]
          by_cases hp : tag - 2 + 1 < 8
          · rw [ite_eq_left hp]
            by_cases hemp : (rawChargedSlotsForPassV2 q L a e n b (tag - 2 + 1)
                (st.2.1 ++
                  [((st.2.1.length, st.1.1, grayChargedSpendEps a L e (tag - 2),
                      grayChargedSpendEps a L e (tag - 2) + graySpendSpan q,
                      grayChargedSpendDelta a L e (tag - 2)),
                    (st.2.2.2.1, current,
                      grayTailLocalAllocatedList
                        (rawLocalServerMove
                          (grayChargedSpendDelta a L e (tag - 2)) b
                          st.2.2.2.1 sm),
                      st.2.2.1))])).isEmpty = true
            · simp [hp, hemp]
            · simp only [Bool.not_eq_true] at hemp
              simp [hp, hemp]
          · simp [hp]
        · simp only [Bool.not_eq_true] at hg
          rw [ite_eq_right (by simp [hg])]
          simp [hg, rawSpendRejectV2]

/-! ### Computability of the phase-tagged transition -/

/-- Freezing a raw V2 spend round is computable in computable parameters. -/
theorem computable_rawSpendFrozenV2 {X : Type} [Primcodable X]
    {fq fL fa fe fb ftag : X → ℕ} {fst : X → RawStateV2}
    {fsm : X → FamilyServerMove} {fcur : X → FamilyClientMove}
    (hq : Computable fq) (hL : Computable fL) (ha : Computable fa)
    (he : Computable fe) (hb : Computable fb) (htag : Computable ftag)
    (hst : Computable fst) (hsm : Computable fsm) (hcur : Computable fcur) :
    Computable fun x : X =>
      rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x) (fst x)
        (fsm x) (fcur x) := by
  have hbody : Computable fun x : X => (fst x).2 := Computable.snd.comp hst
  have htime : Computable fun x : X => (fst x).1.1 :=
    Computable.fst.comp (Computable.fst.comp hst)
  have hfrozen : Computable fun x : X => (fst x).2.1 := Computable.fst.comp hbody
  have hunav : Computable fun x : X => (fst x).2.2.1 :=
    Computable.fst.comp (Computable.snd.comp hbody)
  have hslots : Computable fun x : X => (fst x).2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hbody))
  have hr : Computable fun x : X => (fst x).2.1.length :=
    Primrec.list_length.to_comp.comp hfrozen
  have hpass : Computable fun x : X => ftag x - 2 :=
    Primrec.nat_sub.to_comp.comp htag (Computable.const 2)
  have heps : Computable fun x : X =>
      grayChargedSpendEps (fa x) (fL x) (fe x) (ftag x - 2) :=
    computable_grayChargedSpendEps ha hL he hpass
  have hdelta : Computable fun x : X =>
      grayChargedSpendDelta (fa x) (fL x) (fe x) (ftag x - 2) :=
    computable_grayChargedSpendDelta ha hL he hpass
  have hspan : Computable fun x : X => graySpendSpan (fq x) :=
    primrec_graySpendSpan.to_comp.comp hq
  have hchild : Computable fun x : X =>
      grayChargedSpendEps (fa x) (fL x) (fe x) (ftag x - 2) +
        graySpendSpan (fq x) :=
    Primrec.nat_add.to_comp.comp heps hspan
  have hlocal : Computable fun x : X =>
      rawLocalServerMove (grayChargedSpendDelta (fa x) (fL x) (fe x)
        (ftag x - 2)) (fb x) (fst x).2.2.2.1 (fsm x) :=
    (computable_rawLocalServerMove.comp
      ((hdelta.pair hb).pair (hslots.pair hsm))).of_eq fun _ => rfl
  have halloc : Computable fun x : X =>
      grayTailLocalAllocatedList
        (rawLocalServerMove (grayChargedSpendDelta (fa x) (fL x) (fe x)
          (ftag x - 2)) (fb x) (fst x).2.2.2.1 (fsm x)) :=
    computable_grayTailLocalAllocatedList.comp hlocal
  have hround : Computable fun x : X =>
      ((((fst x).2.1.length, (fst x).1.1,
          grayChargedSpendEps (fa x) (fL x) (fe x) (ftag x - 2),
          grayChargedSpendEps (fa x) (fL x) (fe x) (ftag x - 2) +
            graySpendSpan (fq x),
          grayChargedSpendDelta (fa x) (fL x) (fe x) (ftag x - 2)),
        ((fst x).2.2.2.1, fcur x,
          grayTailLocalAllocatedList
            (rawLocalServerMove (grayChargedSpendDelta (fa x) (fL x) (fe x)
              (ftag x - 2)) (fb x) (fst x).2.2.2.1 (fsm x)),
          (fst x).2.2.1)) : RawRoundV2) :=
    (hr.pair (htime.pair (heps.pair (hchild.pair hdelta)))).pair
      (hslots.pair (hcur.pair (halloc.pair hunav)))
  exact (Primrec.list_append.to_comp.comp hfrozen
    (Computable.list_cons.comp hround (Computable.const []))).of_eq fun _ => rfl

/-- The rejecting branch of a raw V2 spend step is computable in computable parameters. -/
theorem computable_rawSpendRejectV2 {X : Type} [Primcodable X]
    {fa fL fe fb ftag : X → ℕ} {fst : X → RawStateV2}
    {fsm : X → FamilyServerMove} {fcur : X → FamilyClientMove}
    (ha : Computable fa) (hL : Computable fL) (he : Computable fe)
    (hb : Computable fb) (htag : Computable ftag) (hst : Computable fst)
    (hsm : Computable fsm) (hcur : Computable fcur) :
    Computable fun x : X =>
      rawSpendRejectV2 (fa x) (fL x) (fe x) (fb x) (ftag x) (fst x) (fsm x)
        (fcur x) := by
  have hbody : Computable fun x : X => (fst x).2 := Computable.snd.comp hst
  have htime : Computable fun x : X => (fst x).1.1 + 1 :=
    Primrec.succ.to_comp.comp (Computable.fst.comp (Computable.fst.comp hst))
  have hstart : Computable fun x : X => (fst x).1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hdone : Computable fun x : X => (fst x).1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hfrozen : Computable fun x : X => (fst x).2.1 := Computable.fst.comp hbody
  have hunav : Computable fun x : X => (fst x).2.2.1 :=
    Computable.fst.comp (Computable.snd.comp hbody)
  have hslots : Computable fun x : X => (fst x).2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hbody))
  have hanch : Computable fun x : X => (fst x).2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hbody)))
  have hh1 : Computable fun x : X => (fst x).2.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hbody))))
  have hh2 : Computable fun x : X => (fst x).2.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hbody))))
  have hpass : Computable fun x : X => ftag x - 2 :=
    Primrec.nat_sub.to_comp.comp htag (Computable.const 2)
  have hdelta : Computable fun x : X =>
      grayChargedSpendDelta (fa x) (fL x) (fe x) (ftag x - 2) :=
    computable_grayChargedSpendDelta ha hL he hpass
  have hlocal : Computable fun x : X =>
      rawLocalServerMove (grayChargedSpendDelta (fa x) (fL x) (fe x)
        (ftag x - 2)) (fb x) (fst x).2.2.2.1 (fsm x) :=
    (computable_rawLocalServerMove.comp
      ((hdelta.pair hb).pair (hslots.pair hsm))).of_eq fun _ => rfl
  have hnewH1 : Computable fun x : X => (fst x).2.2.2.2.2.1 ++ [fcur x] :=
    Primrec.list_append.to_comp.comp hh1
      (Computable.list_cons.comp hcur (Computable.const []))
  have hnewH2 : Computable fun x : X =>
      (fst x).2.2.2.2.2.2 ++
        [rawLocalServerMove (grayChargedSpendDelta (fa x) (fL x) (fe x)
          (ftag x - 2)) (fb x) (fst x).2.2.2.1 (fsm x)] :=
    Primrec.list_append.to_comp.comp hh2
      (Computable.list_cons.comp hlocal (Computable.const []))
  exact (htag.pair ((htime.pair (hstart.pair hdone)).pair
    (hfrozen.pair (hunav.pair (hslots.pair
      (hanch.pair (hnewH1.pair hnewH2))))))).of_eq fun _ => rfl

/-- The accepting branch of a raw V2 spend step is computable in computable parameters. -/
theorem computable_rawSpendAcceptV2 {X : Type} [Primcodable X]
    {fq fL fa fe fn fb ftag : X → ℕ} {fA : X → Allocation}
    {fst : X → RawStateV2} {fsm : X → FamilyServerMove}
    {fcur : X → FamilyClientMove}
    (hq : Computable fq) (hL : Computable fL) (ha : Computable fa)
    (he : Computable fe) (hn : Computable fn) (hb : Computable fb)
    (htag : Computable ftag) (hA : Computable fA) (hst : Computable fst)
    (hsm : Computable fsm) (hcur : Computable fcur) :
    Computable fun x : X =>
      rawSpendAcceptV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x) (ftag x)
        (fA x) (fst x) (fsm x) (fcur x) := by
  have htime1 : Computable fun x : X => (fst x).1.1 + 1 :=
    Primrec.succ.to_comp.comp (Computable.fst.comp (Computable.fst.comp hst))
  have hpass1 : Computable fun x : X => ftag x - 2 + 1 :=
    Primrec.succ.to_comp.comp
      (Primrec.nat_sub.to_comp.comp htag (Computable.const 2))
  have hfrozen' : Computable fun x : X =>
      rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x) (fst x)
        (fsm x) (fcur x) :=
    computable_rawSpendFrozenV2 hq hL ha he hb htag hst hsm hcur
  have hslotsNext : Computable fun x : X =>
      rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
        (ftag x - 2 + 1)
        (rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x) (fst x)
          (fsm x) (fcur x)) :=
    computable_rawChargedSlotsForPassV2 hq hL ha he hn hb hpass1 hfrozen'
  have hdeltaNext : Computable fun x : X =>
      grayChargedSpendDelta (fa x) (fL x) (fe x) (ftag x - 2 + 1) :=
    computable_grayChargedSpendDelta ha hL he hpass1
  have hunav' : Computable fun x : X =>
      fA x ++ rawGrayHarvest
        (grayChargedSpendDelta (fa x) (fL x) (fe x) (ftag x - 2 + 1)) (fb x)
        (rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
          (ftag x - 2 + 1)
          (rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x) (fst x)
            (fsm x) (fcur x))) (fn x) (fsm x) :=
    Primrec.list_append.to_comp.comp hA
      (computable_rawGrayHarvest hdeltaNext hb hslotsNext hn hsm)
  have hemp : Computable fun x : X =>
      (rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
        (ftag x - 2 + 1)
        (rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x) (fst x)
          (fsm x) (fcur x))).isEmpty := by
    have hz : Computable fun x : X =>
        decide ((rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x)
          (fb x) (ftag x - 2 + 1)
          (rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x) (fst x)
            (fsm x) (fcur x))).length = 0) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Primrec.list_length.to_comp.comp hslotsNext) (Computable.const 0)
    exact hz.of_eq fun x => (list_isEmpty_eq_decide _).symm
  have hand : Computable₂ fun a b : Bool => a && b :=
    (Primrec.dom_bool₂ (fun a b => a && b)).to_comp
  have hguard := hand.comp
    ((PrimrecRel.decide Primrec.nat_lt).to_comp.comp hpass1 (Computable.const 8))
    (Primrec.not.to_comp.comp hemp)
  have hthen : Computable fun x : X =>
      ((ftag x - 2 + 3, (((fst x).1.1 + 1, (fst x).1.1 + 1, false),
        (rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x) (fst x)
            (fsm x) (fcur x),
          fA x ++ rawGrayHarvest
            (grayChargedSpendDelta (fa x) (fL x) (fe x) (ftag x - 2 + 1)) (fb x)
            (rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
              (ftag x - 2 + 1)
              (rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x)
                (fst x) (fsm x) (fcur x))) (fn x) (fsm x),
          rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
            (ftag x - 2 + 1)
            (rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x)
              (fst x) (fsm x) (fcur x)),
          ([] : List RawSlot),
          (([], []) : FamilyGameHistory)))) : RawChargedStateV2) :=
    (Primrec.succ.to_comp.comp (Primrec.succ.to_comp.comp hpass1)).pair
      ((htime1.pair (htime1.pair (Computable.const false))).pair
        (hfrozen'.pair (hunav'.pair (hslotsNext.pair
          ((Computable.const ([] : List RawSlot)).pair
            (Computable.const (([], []) : FamilyGameHistory)))))))
  have helse : Computable fun x : X =>
      (((1 : ℕ), (((fst x).1.1 + 1, (fst x).1.1 + 1, true),
        (rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x) (fst x)
            (fsm x) (fcur x),
          fA x ++ rawGrayHarvest
            (grayChargedSpendDelta (fa x) (fL x) (fe x) (ftag x - 2 + 1)) (fb x)
            (rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
              (ftag x - 2 + 1)
              (rawSpendFrozenV2 (fq x) (fL x) (fa x) (fe x) (fb x) (ftag x)
                (fst x) (fsm x) (fcur x))) (fn x) (fsm x),
          ([] : List RawSlot), ([] : List RawSlot),
          (([], []) : FamilyGameHistory)))) : RawChargedStateV2) :=
    (Computable.const 1).pair
      ((htime1.pair (htime1.pair (Computable.const true))).pair
        (hfrozen'.pair (hunav'.pair
          ((Computable.const ([] : List RawSlot)).pair
            ((Computable.const ([] : List RawSlot)).pair
              (Computable.const (([], []) : FamilyGameHistory)))))))
  exact (Computable.cond hguard hthen helse).of_eq fun _ => rfl

/-- **The erased phase-tagged V2 transition is computable** jointly in all its
arguments (the v15.1 wait included). -/
theorem computable_rawChargedStepV2With {X : Type} [Primcodable X]
    {fq fL fa fe fn fb ftag : X → ℕ} {fA : X → Allocation}
    {fst : X → RawStateV2} {fsm : X → FamilyServerMove}
    {fcur : X → FamilyClientMove}
    (hq : Computable fq) (hL : Computable fL) (ha : Computable fa)
    (he : Computable fe) (hn : Computable fn) (hb : Computable fb)
    (htag : Computable ftag) (hA : Computable fA) (hst : Computable fst)
    (hsm : Computable fsm) (hcur : Computable fcur) :
    Computable fun x : X =>
      rawChargedStepV2With (fq x) (fL x) (fa x) (fe x) (fn x) (fb x) (fA x)
        (ftag x) (fst x) (fsm x) (fcur x) := by
  have hbody : Computable fun x : X => (fst x).2 := Computable.snd.comp hst
  have htime1 : Computable fun x : X => (fst x).1.1 + 1 :=
    Primrec.succ.to_comp.comp (Computable.fst.comp (Computable.fst.comp hst))
  have hstart : Computable fun x : X => (fst x).1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hdone : Computable fun x : X => (fst x).1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hunav : Computable fun x : X => (fst x).2.2.1 :=
    Computable.fst.comp (Computable.snd.comp hbody)
  have hslots : Computable fun x : X => (fst x).2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hbody))
  have hpass : Computable fun x : X => ftag x - 2 :=
    Primrec.nat_sub.to_comp.comp htag (Computable.const 2)
  -- the tick branches
  have htick1 : Computable fun x : X =>
      (((1 : ℕ), (((fst x).1.1 + 1, (fst x).1.2.1, (fst x).1.2.2), (fst x).2)) :
        RawChargedStateV2) :=
    (Computable.const 1).pair ((htime1.pair (hstart.pair hdone)).pair hbody)
  have htick2 : Computable fun x : X =>
      (((1 : ℕ), (((fst x).1.1 + 1, (fst x).1.2.1, true), (fst x).2)) :
        RawChargedStateV2) :=
    (Computable.const 1).pair
      ((htime1.pair (hstart.pair (Computable.const true))).pair hbody)
  -- the advantage arm
  have hnext : Computable fun x : X =>
      rawChargedBlockTailStepV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
        (fA x) (fst x) (fsm x) (fcur x) :=
    computable_rawChargedBlockTailStepV2 hq hL ha he hn hb hA hst hsm hcur
  have hnextDone : Computable fun x : X =>
      (rawChargedBlockTailStepV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
        (fA x) (fst x) (fsm x) (fcur x)).1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp hnext))
  have hwait : Computable fun x : X =>
      rawChargedWaitServedB (fq x) (fa x) (fe x) (fn x) (fb x)
        (rawChargedBlockTailStepV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
          (fA x) (fst x) (fsm x) (fcur x)) (fsm x) :=
    computable_rawChargedWaitServedB hq ha he hn hb hnext hsm
  have hstartSpend : Computable fun x : X =>
      rawChargedStartSpendV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x) (fA x)
        (rawChargedBlockTailStepV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
          (fA x) (fst x) (fsm x) (fcur x)) (fsm x) :=
    computable_rawChargedStartSpendV2 hq hL ha he hn hb hA hnext hsm
  have hstay : Computable fun x : X =>
      (((0 : ℕ), rawChargedBlockTailStepV2 (fq x) (fL x) (fa x) (fe x) (fn x)
        (fb x) (fA x) (fst x) (fsm x) (fcur x)) : RawChargedStateV2) :=
    (Computable.const 0).pair hnext
  have hadv := Computable.cond hnextDone
    (Computable.cond hwait hstartSpend hstay) hstay
  -- the spend arm
  have hemp : Computable fun x : X => (fst x).2.2.2.1.isEmpty := by
    have hz : Computable fun x : X => decide ((fst x).2.2.2.1.length = 0) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Primrec.list_length.to_comp.comp hslots) (Computable.const 0)
    exact hz.of_eq fun x => (list_isEmpty_eq_decide _).symm
  have hdelta : Computable fun x : X =>
      grayChargedSpendDelta (fa x) (fL x) (fe x) (ftag x - 2) :=
    computable_grayChargedSpendDelta ha hL he hpass
  have hlocal : Computable fun x : X =>
      rawLocalServerMove (grayChargedSpendDelta (fa x) (fL x) (fe x)
        (ftag x - 2)) (fb x) (fst x).2.2.2.1 (fsm x) :=
    (computable_rawLocalServerMove.comp
      ((hdelta.pair hb).pair (hslots.pair hsm))).of_eq fun _ => rfl
  have hgoal : Computable fun x : X =>
      grayChargedBlockSpendGoalAtB (fq x) (fL x) (fa x) (fe x) (ftag x - 2)
        (fst x).2.2.2.1.length (fst x).2.2.1 (fcur x)
        (rawLocalServerMove (grayChargedSpendDelta (fa x) (fL x) (fe x)
          (ftag x - 2)) (fb x) (fst x).2.2.2.1 (fsm x)) :=
    computable_grayChargedBlockSpendGoalAtB hq hL ha he hpass
      (Primrec.list_length.to_comp.comp hslots) hunav hcur hlocal
  have hacc := computable_rawSpendAcceptV2 hq hL ha he hn hb htag hA hst hsm hcur
  have hrej := computable_rawSpendRejectV2 ha hL he hb htag hst hsm hcur
  have hspend := Computable.cond hemp htick2 (Computable.cond hgoal hacc hrej)
  have hIsOne : Computable fun x : X => decide (ftag x = 1) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp htag (Computable.const 1)
  have hIsZero : Computable fun x : X => decide (ftag x = 0) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp htag (Computable.const 0)
  refine (Computable.cond hIsOne htick1
    (Computable.cond hIsZero hadv hspend)).of_eq fun x => ?_
  exact (rawChargedStepV2With_eq_cond (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
    (fA x) (ftag x) (fst x) (fsm x) (fcur x)).symm

/-! ### Computability of the displayed V2 move -/

/-- The slots a raw V2 state displays are computable in the state. -/
theorem computable_rawChargedDisplaySlotsV2 {X : Type} [Primcodable X]
    {fst : X → RawStateV2} (hst : Computable fst) :
    Computable fun x : X => rawChargedDisplaySlotsV2 (fst x) := by
  have hdone : Computable fun x : X => (fst x).1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hslots : Computable fun x : X => (fst x).2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hst)))
  exact (Computable.cond hdone (Computable.const ([] : List RawSlot))
    hslots).of_eq fun _ => rfl

/-- The current move a raw V2 state displays is computable in its arguments. -/
theorem computable_rawChargedDisplayCurrentV2 {X : Type} [Primcodable X]
    {ftag : X → ℕ} {fst : X → RawStateV2} {fcur : X → FamilyClientMove}
    (htag : Computable ftag) (hst : Computable fst) (hcur : Computable fcur) :
    Computable fun x : X =>
      rawChargedDisplayCurrentV2 (ftag x) (fst x) (fcur x) := by
  have hdone : Computable fun x : X => (fst x).1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hslots : Computable fun x : X => (fst x).2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hst)))
  have hemp : Computable fun x : X => (fst x).2.2.2.1.isEmpty := by
    have hz : Computable fun x : X => decide ((fst x).2.2.2.1.length = 0) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Primrec.list_length.to_comp.comp hslots) (Computable.const 0)
    exact hz.of_eq fun x => (list_isEmpty_eq_decide _).symm
  have hor : Computable₂ fun a b : Bool => a || b :=
    (Primrec.dom_bool₂ (fun a b => a || b)).to_comp
  have hnil : Computable fun _ : X => ([] : FamilyClientMove) :=
    Computable.const []
  have hIsOne : Computable fun x : X => decide (ftag x = 1) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp htag (Computable.const 1)
  have hIsZero : Computable fun x : X => decide (ftag x = 0) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp htag (Computable.const 0)
  exact (Computable.cond hIsOne hnil
    (Computable.cond hIsZero
      (Computable.cond (hor.comp hdone hemp) hnil hcur)
      (Computable.cond hemp hnil hcur))).of_eq fun _ => rfl

/-- **The erased displayed V2 move is computable** jointly in its
arguments. -/
theorem computable_rawChargedOutputV2 {X : Type} [Primcodable X]
    {fq fa fe fn fb ftag : X → ℕ} {fst : X → RawStateV2}
    {fcur : X → FamilyClientMove}
    (hq : Computable fq) (ha : Computable fa) (he : Computable fe)
    (hn : Computable fn) (hb : Computable fb) (htag : Computable ftag)
    (hst : Computable fst) (hcur : Computable fcur) :
    Computable fun x : X =>
      rawChargedOutputV2 (fq x) (fa x) (fe x) (fn x) (fb x) (ftag x) (fst x)
        (fcur x) := by
  have hfrozen : Computable fun x : X => (fst x).2.1 :=
    Computable.fst.comp (Computable.snd.comp hst)
  have hfrv1 : Computable fun x : X => rawFrozenV1OfV2 (fst x).2.1 :=
    computable_rawFrozenV1OfV2 hfrozen
  have hsource : Computable fun x : X => grayChargedSourceCount (fa x) (fe x) :=
    computable_grayChargedSourceCount ha he
  have hthr : Computable fun x : X => grayChargedThreshold (fq x) (fe x) :=
    computable_grayChargedThreshold hq he
  have heps : Computable fun x : X => dyadicScale (fe x) :=
    computable_dyadicScale.comp he
  have hslots : Computable fun x : X => rawChargedDisplaySlotsV2 (fst x) :=
    computable_rawChargedDisplaySlotsV2 hst
  have hcurrent : Computable fun x : X =>
      rawChargedDisplayCurrentV2 (ftag x) (fst x) (fcur x) :=
    computable_rawChargedDisplayCurrentV2 htag hst hcur
  exact (computable_chargedFamMoveP.comp
    ((hsource.pair (hthr.pair heps)).pair
      ((hn.pair hb).pair (hfrv1.pair (hslots.pair hcurrent))))).of_eq
    fun _ => rfl

/-! ### The statements consumed by the oracle assembly -/

/-- **One erased V2 charged transition is computable.** -/
theorem computable_rawStepOfV2 :
    Computable fun x : RawParamV2 × RawChargedStateV2 × FamilyServerMove ×
        FamilyClientMove => rawStepOfV2 x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hP : Computable fun x : RawParamV2 × RawChargedStateV2 ×
      FamilyServerMove × FamilyClientMove => x.1 := Computable.fst
  have hnum : Computable fun x : RawParamV2 × RawChargedStateV2 ×
      FamilyServerMove × FamilyClientMove => x.1.1 := Computable.fst.comp hP
  have hnb : Computable fun x : RawParamV2 × RawChargedStateV2 ×
      FamilyServerMove × FamilyClientMove => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hP)
  have hstc : Computable fun x : RawParamV2 × RawChargedStateV2 ×
      FamilyServerMove × FamilyClientMove => x.2.1 :=
    Computable.fst.comp Computable.snd
  exact (computable_rawChargedStepV2With
    (Computable.fst.comp hnum)
    (Computable.fst.comp (Computable.snd.comp hnum))
    (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hnum)))
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hnum)))
    (Computable.fst.comp hnb) (Computable.snd.comp hnb)
    (Computable.fst.comp hstc)
    (Computable.snd.comp (Computable.snd.comp hP))
    (Computable.snd.comp hstc)
    (Computable.fst.comp (Computable.snd.comp Computable.snd))
    (Computable.snd.comp (Computable.snd.comp Computable.snd))).of_eq
    fun _ => rfl

/-- **The displayed move of an erased V2 state is computable.** -/
theorem computable_rawOutputOfV2 :
    Computable fun x : RawParamV2 × RawChargedStateV2 × FamilyClientMove =>
      rawOutputOfV2 x.1 x.2.1 x.2.2 := by
  have hP : Computable fun x : RawParamV2 × RawChargedStateV2 ×
      FamilyClientMove => x.1 := Computable.fst
  have hnum : Computable fun x : RawParamV2 × RawChargedStateV2 ×
      FamilyClientMove => x.1.1 := Computable.fst.comp hP
  have hnb : Computable fun x : RawParamV2 × RawChargedStateV2 ×
      FamilyClientMove => x.1.2.1 := Computable.fst.comp (Computable.snd.comp hP)
  have hstc : Computable fun x : RawParamV2 × RawChargedStateV2 ×
      FamilyClientMove => x.2.1 := Computable.fst.comp Computable.snd
  exact (computable_rawChargedOutputV2
    (Computable.fst.comp hnum)
    (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hnum)))
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hnum)))
    (Computable.fst.comp hnb) (Computable.snd.comp hnb)
    (Computable.fst.comp hstc) (Computable.snd.comp hstc)
    (Computable.snd.comp Computable.snd)).of_eq fun _ => rfl

/-- **The subcall input of an erased V2 state is computable.** -/
theorem computable_rawQueryOfV2 :
    Computable fun x : RawParamV2 × RawChargedStateV2 =>
      rawQueryOfV2 x.1 x.2 := by
  have hnum : Computable fun x : RawParamV2 × RawChargedStateV2 => x.1.1 :=
    Computable.fst.comp Computable.fst
  exact (computable_rawChargedQueryV2
    (Computable.fst.comp hnum)
    (Computable.fst.comp (Computable.snd.comp hnum))
    (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hnum)))
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hnum)))
    (Computable.fst.comp Computable.snd)
    (Computable.snd.comp Computable.snd)).of_eq fun _ => rfl

/-- **The initial erased V2 charged state is computable.** -/
theorem computable_rawInitialStateOfV2 : Computable rawInitialStateOfV2 := by
  have hnum : Computable fun P : RawParamV2 => P.1 := Computable.fst
  have hnb : Computable fun P : RawParamV2 => P.2.1 :=
    Computable.fst.comp Computable.snd
  exact ((Computable.const 0).pair
    (computable_rawInitialStateV2
      (Computable.fst.comp hnb) (Computable.snd.comp hnb)
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hnum)))
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hnum)))
      (Computable.fst.comp hnum)
      (Computable.fst.comp (Computable.snd.comp hnum))
      (Computable.snd.comp Computable.snd))).of_eq fun _ => rfl

/-- The encoded displayed V2 move is computable. -/
theorem computable_rawOutputEncV2 :
    Computable fun x : RawParamV2 × RawChargedStateV2 × FamilyClientMove =>
      rawOutputEncV2 x.1 x.2.1 x.2.2 :=
  (Computable.encode.comp computable_rawOutputOfV2).of_eq fun _ => rfl

/-! ### The erased controller computes the outer V2 strategy -/

/-- The answers the scheme `sigma` gives to the queries of the erased V2
controller, as a function of the phase tag and the erased state. -/
def rawSchemeAnswerV2 (q L a e : ℕ) (sigma : FamilyStrategyScheme) :
    ℕ → RawStateV2 → FamilyClientMove :=
  fun tag st => sigma (rawChargedQueryV2 q L a e tag st).1.1
    (rawChargedQueryV2 q L a e tag st).1.2
    (rawChargedQueryV2 q L a e tag st).2.1
    (rawChargedQueryV2 q L a e tag st).2.2.1
    (rawChargedQueryV2 q L a e tag st).2.2.2

/-- **The erased V2 controller computes the outer V2 strategy.**  Running the
raw phase-tagged fold with the child answers read off `rawChargedQueryV2` and
then displaying the result reproduces `grayChargedStrategyV2` exactly.  This is
the statement the oracle assembly consumes; V1's twin is the composition of
`rawChargedFoldWith_eq` and `rawChargedOutput_eq` performed inside
`chargedPhi_eq`. -/
theorem rawOutputOfV2_fold_eq (q L a e n : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (history : FamilyGameHistory) :
    rawOutputOfV2 ((q, L, a, e), (n, grayTailBranch q L a e), A)
        (rawChargedFoldV2With q L a e n (grayTailBranch q L a e) A
          (rawSchemeAnswerV2 q L a e sigma) history.2)
        (rawSchemeAnswerV2 q L a e sigma
          (rawChargedFoldV2With q L a e n (grayTailBranch q L a e) A
            (rawSchemeAnswerV2 q L a e sigma) history.2).1
          (rawChargedFoldV2With q L a e n (grayTailBranch q L a e) A
            (rawSchemeAnswerV2 q L a e sigma) history.2).2) =
      grayChargedStrategyV2 q L a e sigma A n history := by
  unfold rawSchemeAnswerV2
  rw [rawChargedFoldV2With_eq]
  simp only [rawOutputOfV2, toRawChargedStateV2]
  rw [rawChargedQueryV2_eq_phase q L a e
    (grayChargedFoldV2 (n := n) (b := grayTailBranch q L a e) q L a e sigma A
      history.2) sigma]
  exact rawChargedOutputV2_eq q L a e sigma
    (grayChargedFoldV2 (n := n) (b := grayTailBranch q L a e) q L a e sigma A
      history.2)

end Kolmogorov
