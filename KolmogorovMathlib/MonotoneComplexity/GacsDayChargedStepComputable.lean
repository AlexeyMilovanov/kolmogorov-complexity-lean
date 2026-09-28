import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedStepComputable.TailStep

/-!
# Computability of the erased charged transition

The phase-tagged transition `rawChargedStepWith` opens a spending pass out of
the advantage transition of `TailStep.lean` and then performs a pure case
distinction on the phase tag.  This module carries the opening step
`chargedStartSpendP`, the pure assembler `chargedAsm`, and the inputs
`chargedStepAsmArg` it is fed with, whose pieces — the advantage result, the
localised server move, the round frozen by the pass, the acceptance test and
the slots of the next pass — are computed separately.
-/


namespace Kolmogorov

/-! ### Starting the spend phase -/

/-- Packed arguments of `rawChargedStartSpend`:
`((q, L, a, e), (n, b), A, core, sm)`. -/
abbrev CStartArg :=
  (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ) × Allocation × RawState × FamilyServerMove

/-- Packed form of `rawChargedStartSpend`. -/
def chargedStartSpendP (x : CStartArg) : RawChargedState :=
  rawChargedStartSpend x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.1.1 x.2.1.2
    x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- Opening a spend pass either finishes the run, when the pass opens no slot, or moves to the
pass with its slots and harvested unavailable set. -/
theorem chargedStartSpendP_eq (x : CStartArg) :
    chargedStartSpendP x =
      (if (chargedPassSlots ((x.1.1, x.1.2.2.1, x.1.2.2.2),
            (x.2.1.1, x.2.1.2, 0), x.2.2.2.1.2.1)).isEmpty then
        ((1 : ℕ), ((x.2.2.2.1.1.1, x.2.2.2.1.1.2.1, true),
          (x.2.2.2.1.2.1, x.2.2.2.1.2.2.1, [], x.2.2.2.1.2.2.2.2.1, ([], []))))
      else
        ((2 : ℕ), ((x.2.2.2.1.1.1, x.2.2.2.1.1.2.1, false),
          (x.2.2.2.1.2.1,
            x.2.2.1 ++ rawGrayHarvest
              (grayChargedSpendDelta x.1.2.2.1 x.1.2.1 x.1.2.2.2 0) x.2.1.2
              (chargedPassSlots ((x.1.1, x.1.2.2.1, x.1.2.2.2),
                (x.2.1.1, x.2.1.2, 0), x.2.2.2.1.2.1)) x.2.1.1 x.2.2.2.2,
            chargedPassSlots ((x.1.1, x.1.2.2.1, x.1.2.2.2),
              (x.2.1.1, x.2.1.2, 0), x.2.2.2.1.2.1),
            x.2.2.2.1.2.2.2.2.1, ([], []))))) := rfl

/-- Opening a spend pass is computable. -/
theorem computable_chargedStartSpendP : Computable chargedStartSpendP := by
  have hq : Computable fun x : CStartArg => x.1.1 := Computable.fst.comp Computable.fst
  have hL : Computable fun x : CStartArg => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have ha : Computable fun x : CStartArg => x.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have he : Computable fun x : CStartArg => x.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hn : Computable fun x : CStartArg => x.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hb : Computable fun x : CStartArg => x.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hA : Computable fun x : CStartArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hcore : Computable fun x : CStartArg => x.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hsm : Computable fun x : CStartArg => x.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have htime : Computable fun x : CStartArg => x.2.2.2.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp hcore)
  have hstart : Computable fun x : CStartArg => x.2.2.2.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp hcore))
  have hfrozen : Computable fun x : CStartArg => x.2.2.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hcore)
  have hunav : Computable fun x : CStartArg => x.2.2.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hcore))
  have hanchors : Computable fun x : CStartArg => x.2.2.2.1.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hcore))))
  have hslotarg : Computable fun x : CStartArg =>
      (((x.1.1, x.1.2.2.1, x.1.2.2.2),
        (x.2.1.1, x.2.1.2, 0), x.2.2.2.1.2.1) : CPassArg) :=
    (hq.pair (ha.pair he)).pair
      ((hn.pair (hb.pair (Computable.const 0))).pair hfrozen)
  have hslots : Computable fun x : CStartArg =>
      chargedPassSlots ((x.1.1, x.1.2.2.1, x.1.2.2.2),
        (x.2.1.1, x.2.1.2, 0), x.2.2.2.1.2.1) :=
    computable_chargedPassSlots.comp hslotarg
  have hemp : Computable fun x : CStartArg =>
      (chargedPassSlots ((x.1.1, x.1.2.2.1, x.1.2.2.2),
        (x.2.1.1, x.2.1.2, 0), x.2.2.2.1.2.1)).isEmpty :=
    computable_list_isEmpty hslots
  have hdelta0 : Computable fun x : CStartArg =>
      grayChargedSpendDelta x.1.2.2.1 x.1.2.1 x.1.2.2.2 0 :=
    computable_grayChargedSpendDelta ha hL he (Computable.const 0)
  have hharv0 := Primrec.list_append.to_comp.comp hA
    (computable_rawGrayHarvest hdelta0 hb hslots hn hsm)
  have hthen : Computable fun x : CStartArg =>
      (((1 : ℕ), ((x.2.2.2.1.1.1, x.2.2.2.1.1.2.1, true),
        (x.2.2.2.1.2.1, x.2.2.2.1.2.2.1, ([] : List RawSlot),
          x.2.2.2.1.2.2.2.2.1,
          (([], []) : FamilyGameHistory)))) : RawChargedState) :=
    (Computable.const 1).pair
      ((htime.pair (hstart.pair (Computable.const true))).pair
        (hfrozen.pair (hunav.pair ((Computable.const []).pair
          (hanchors.pair (Computable.const (([], []) : FamilyGameHistory)))))))
  have helse : Computable fun x : CStartArg =>
      (((2 : ℕ), ((x.2.2.2.1.1.1, x.2.2.2.1.1.2.1, false),
        (x.2.2.2.1.2.1,
          x.2.2.1 ++ rawGrayHarvest
            (grayChargedSpendDelta x.1.2.2.1 x.1.2.1 x.1.2.2.2 0) x.2.1.2
            (chargedPassSlots ((x.1.1, x.1.2.2.1, x.1.2.2.2),
              (x.2.1.1, x.2.1.2, 0), x.2.2.2.1.2.1)) x.2.1.1 x.2.2.2.2,
          chargedPassSlots ((x.1.1, x.1.2.2.1, x.1.2.2.2),
            (x.2.1.1, x.2.1.2, 0), x.2.2.2.1.2.1),
          x.2.2.2.1.2.2.2.2.1,
          (([], []) : FamilyGameHistory)))) : RawChargedState) :=
    (Computable.const 2).pair
      ((htime.pair (hstart.pair (Computable.const false))).pair
        (hfrozen.pair (hharv0.pair (hslots.pair
          (hanchors.pair (Computable.const (([], []) : FamilyGameHistory)))))))
  refine (Computable.cond hemp hthen helse).of_eq fun x => ?_
  rw [chargedStartSpendP_eq]
  cases hx : (chargedPassSlots ((x.1.1, x.1.2.2.1, x.1.2.2.2),
      (x.2.1.1, x.2.1.2, 0), x.2.2.2.1.2.1)).isEmpty <;> simp

/-! ### The phase-tagged charged transition -/

/-- Packed arguments of one erased charged transition. -/
abbrev CStepArg := RawParam × ℕ × RawState × FamilyServerMove × FamilyClientMove

/-- Packed erased charged transition. -/
def chargedStepP (x : CStepArg) : RawChargedState :=
  rawChargedStepWith x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2 x.1.2.1.1 x.1.2.1.2
    x.1.2.2 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- Packed inputs of the final case distinction of one charged transition:
`((tag, nextTag), state), advantageResult,
(slotsEmpty, goal, nextPass, nextSlotsEmpty),
(newRound, unavailable', nextSlots), current, localServerMove`. -/
abbrev CAsmArg :=
  ((ℕ × ℕ) × RawState) ×
    RawChargedState ×
      (Bool × Bool × ℕ × Bool) ×
        (RawRound × Allocation × List RawSlot) ×
          FamilyClientMove × FamilyServerMove

/-- The pure case distinction performed by `rawChargedStepWith`. -/
def chargedAsm (z : CAsmArg) : RawChargedState :=
  if z.1.1.1 = 1 then
    ((1 : ℕ), ((z.1.2.1.1 + 1, z.1.2.1.2.1, z.1.2.1.2.2), z.1.2.2))
  else if z.1.1.1 = 0 then z.2.1
  else if z.2.2.1.1 then
    ((1 : ℕ), ((z.1.2.1.1 + 1, z.1.2.1.2.1, true), z.1.2.2))
  else if z.2.2.1.2.1 then
    if z.2.2.1.2.2.1 < 8 then
      if z.2.2.1.2.2.2 then
        ((1 : ℕ), ((z.1.2.1.1 + 1, z.1.2.1.1 + 1, true),
          (z.1.2.2.1 ++ [z.2.2.2.1.1], z.2.2.2.1.2.1, [], [], ([], []))))
      else
        (z.1.1.2, ((z.1.2.1.1 + 1, z.1.2.1.1 + 1, false),
          (z.1.2.2.1 ++ [z.2.2.2.1.1], z.2.2.2.1.2.1, z.2.2.2.1.2.2, [], ([], []))))
    else
      ((1 : ℕ), ((z.1.2.1.1 + 1, z.1.2.1.1 + 1, true),
        (z.1.2.2.1 ++ [z.2.2.2.1.1], z.2.2.2.1.2.1, [], [], ([], []))))
  else
    (z.1.1.1, ((z.1.2.1.1 + 1, z.1.2.1.2.1, z.1.2.1.2.2),
      (z.1.2.2.1, z.1.2.2.2.1, z.1.2.2.2.2.1, z.1.2.2.2.2.2.1,
        (z.1.2.2.2.2.2.2.1 ++ [z.2.2.2.2.1], z.1.2.2.2.2.2.2.2 ++ [z.2.2.2.2.2]))))


/-- Assembling the raw charged step from its pieces is computable. -/
theorem computable_chargedAsm : Computable chargedAsm := by
  have htag : Computable fun z : CAsmArg => z.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hnext : Computable fun z : CAsmArg => z.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hst : Computable fun z : CAsmArg => z.1.2 := Computable.snd.comp Computable.fst
  have htime : Computable fun z : CAsmArg => z.1.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp hst)
  have hstart : Computable fun z : CAsmArg => z.1.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hdone : Computable fun z : CAsmArg => z.1.2.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp hst))
  have hrest : Computable fun z : CAsmArg => z.1.2.2 := Computable.snd.comp hst
  have hfrozen : Computable fun z : CAsmArg => z.1.2.2.1 := Computable.fst.comp hrest
  have hunav : Computable fun z : CAsmArg => z.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp hrest)
  have hslots : Computable fun z : CAsmArg => z.1.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hrest))
  have hanchors : Computable fun z : CAsmArg => z.1.2.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hrest)))
  have hhist : Computable fun z : CAsmArg => z.1.2.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hrest)))
  have hadv : Computable fun z : CAsmArg => z.2.1 := Computable.fst.comp Computable.snd
  have hflags : Computable fun z : CAsmArg => z.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hslotsEmpty : Computable fun z : CAsmArg => z.2.2.1.1 := Computable.fst.comp hflags
  have hgoal : Computable fun z : CAsmArg => z.2.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hflags)
  have hpass : Computable fun z : CAsmArg => z.2.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hflags))
  have hnextEmpty : Computable fun z : CAsmArg => z.2.2.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hflags))
  have hdata : Computable fun z : CAsmArg => z.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hround : Computable fun z : CAsmArg => z.2.2.2.1.1 := Computable.fst.comp hdata
  have hunav' : Computable fun z : CAsmArg => z.2.2.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hdata)
  have hnextSlots : Computable fun z : CAsmArg => z.2.2.2.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp hdata)
  have hcur : Computable fun z : CAsmArg => z.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd)))
  have hsm : Computable fun z : CAsmArg => z.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd)))
  have hsucc : Computable fun z : CAsmArg => z.1.2.1.1 + 1 :=
    Primrec.succ.to_comp.comp htime
  have hfrozen' : Computable fun z : CAsmArg => z.1.2.2.1 ++ [z.2.2.2.1.1] :=
    Primrec.list_append.to_comp.comp hfrozen
      (Computable.list_cons.comp hround (Computable.const []))
  have hA : Computable fun z : CAsmArg =>
      (((1 : ℕ), ((z.1.2.1.1 + 1, z.1.2.1.2.1, z.1.2.1.2.2), z.1.2.2)) :
        RawChargedState) :=
    (Computable.const 1).pair ((hsucc.pair (hstart.pair hdone)).pair hrest)
  have hC : Computable fun z : CAsmArg =>
      (((1 : ℕ), ((z.1.2.1.1 + 1, z.1.2.1.2.1, true), z.1.2.2)) : RawChargedState) :=
    (Computable.const 1).pair
      ((hsucc.pair (hstart.pair (Computable.const true))).pair hrest)
  have hDdone : Computable fun z : CAsmArg =>
      (((1 : ℕ), ((z.1.2.1.1 + 1, z.1.2.1.1 + 1, true),
        (z.1.2.2.1 ++ [z.2.2.2.1.1], z.2.2.2.1.2.1, ([] : List RawSlot),
          ([] : List RawSlot), (([], []) : FamilyGameHistory)))) : RawChargedState) :=
    (Computable.const 1).pair
      ((hsucc.pair (hsucc.pair (Computable.const true))).pair
        (hfrozen'.pair (hunav'.pair ((Computable.const []).pair
          ((Computable.const []).pair
            (Computable.const (([], []) : FamilyGameHistory)))))))
  have hDspend : Computable fun z : CAsmArg =>
      ((z.1.1.2, ((z.1.2.1.1 + 1, z.1.2.1.1 + 1, false),
        (z.1.2.2.1 ++ [z.2.2.2.1.1], z.2.2.2.1.2.1, z.2.2.2.1.2.2,
          ([] : List RawSlot), (([], []) : FamilyGameHistory)))) : RawChargedState) :=
    hnext.pair
      ((hsucc.pair (hsucc.pair (Computable.const false))).pair
        (hfrozen'.pair (hunav'.pair (hnextSlots.pair
          ((Computable.const []).pair
            (Computable.const (([], []) : FamilyGameHistory)))))))
  have hE : Computable fun z : CAsmArg =>
      ((z.1.1.1, ((z.1.2.1.1 + 1, z.1.2.1.2.1, z.1.2.1.2.2),
        (z.1.2.2.1, z.1.2.2.2.1, z.1.2.2.2.2.1, z.1.2.2.2.2.2.1,
          ((z.1.2.2.2.2.2.2.1 ++ [z.2.2.2.2.1],
            z.1.2.2.2.2.2.2.2 ++ [z.2.2.2.2.2]) : FamilyGameHistory)))) :
        RawChargedState) :=
    htag.pair
      ((hsucc.pair (hstart.pair hdone)).pair
        (hfrozen.pair (hunav.pair (hslots.pair (hanchors.pair
          ((Primrec.list_append.to_comp.comp (Computable.fst.comp hhist)
              (Computable.list_cons.comp hcur (Computable.const []))).pair
            (Primrec.list_append.to_comp.comp (Computable.snd.comp hhist)
              (Computable.list_cons.comp hsm (Computable.const [])))))))))
  have hisone : Computable fun z : CAsmArg => decide (z.1.1.1 = 1) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp htag (Computable.const 1)
  have hiszero : Computable fun z : CAsmArg => decide (z.1.1.1 = 0) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp htag (Computable.const 0)
  have hlt : Computable fun z : CAsmArg => decide (z.2.2.1.2.2.1 < 8) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp hpass (Computable.const 8)
  refine (Computable.cond hisone hA
    (Computable.cond hiszero hadv
      (Computable.cond hslotsEmpty hC
        (Computable.cond hgoal
          (Computable.cond hlt (Computable.cond hnextEmpty hDdone hDspend) hDdone)
          hE)))).of_eq fun z => ?_
  rw [chargedAsm]
  by_cases k1 : z.1.1.1 = 1
  · simp [k1]
  · by_cases k0 : z.1.1.1 = 0
    · simp [k0]
    · by_cases kp : z.2.2.1.2.2.1 < 8
      · cases hse : z.2.2.1.1 <;> cases hg : z.2.2.1.2.1 <;>
          cases hne : z.2.2.1.2.2.2 <;> simp [k1, k0, kp]
      · cases hse : z.2.2.1.1 <;> cases hg : z.2.2.1.2.1 <;>
          cases hne : z.2.2.1.2.2.2 <;> simp [k1, k0, kp]

/-! ### The pieces of one phase-tagged transition -/

/-- What the advantage branch of a charged transition hands on: the advantage transition itself,
tagged `0` while the advantage phase runs, and the opening of the first spending pass as soon as
that transition reports the phase over. -/
def chargedStepAdvance (x : CStepArg) : RawChargedState :=
  if (chargedTailStepP (x.1, x.2.2)).1.2.2 then
    chargedStartSpendP ((x.1.1.1, x.1.1.2.1, x.1.1.2.2.1, x.1.1.2.2.2),
      (x.1.2.1.1, x.1.2.1.2), x.1.2.2, chargedTailStepP (x.1, x.2.2), x.2.2.2.1)
  else ((0 : ℕ), chargedTailStepP (x.1, x.2.2))

/-- The advantage branch of a charged transition is computable in the packed argument of the
transition. -/
theorem computable_chargedStepAdvance : Computable chargedStepAdvance := by
  have hq : Computable fun x : CStepArg => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hL : Computable fun x : CStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ha : Computable fun x : CStepArg => x.1.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have he : Computable fun x : CStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hn : Computable fun x : CStepArg => x.1.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hb : Computable fun x : CStepArg => x.1.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hAp : Computable fun x : CStepArg => x.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hsm : Computable fun x : CStepArg => x.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have htail : Computable fun x : CStepArg => chargedTailStepP (x.1, x.2.2) :=
    computable_chargedTailStepP.comp
      (Computable.fst.pair (Computable.snd.comp Computable.snd))
  have htaildone : Computable fun x : CStepArg => (chargedTailStepP (x.1, x.2.2)).1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp htail))
  have hstartspend : Computable fun x : CStepArg =>
      chargedStartSpendP ((x.1.1.1, x.1.1.2.1, x.1.1.2.2.1, x.1.1.2.2.2),
        (x.1.2.1.1, x.1.2.1.2), x.1.2.2,
        chargedTailStepP (x.1, x.2.2), x.2.2.2.1) :=
    computable_chargedStartSpendP.comp
      ((hq.pair (hL.pair (ha.pair he))).pair ((hn.pair hb).pair (hAp.pair (htail.pair hsm))))
  refine (Computable.cond htaildone hstartspend
    ((Computable.const 0).pair htail)).of_eq fun x => ?_
  rw [chargedStepAdvance]
  cases hx : (chargedTailStepP (x.1, x.2.2)).1.2.2 <;> simp

/-- The server move a spending pass plays against: the incoming server move restricted to the
son subtree of the base and truncated to the fine depth of the pass. -/
def chargedStepLocalMove (x : CStepArg) : FamilyServerMove :=
  rawLocalServerMove (grayChargedSpendDelta x.1.1.2.2.1 x.1.1.2.1 x.1.1.2.2.2 (x.2.1 - 2))
    x.1.2.1.2 x.2.2.1.2.2.2.1 x.2.2.2.1

/-- The localised server move of a spending pass is computable in the packed argument of the
transition. -/
theorem computable_chargedStepLocalMove : Computable chargedStepLocalMove := by
  have hL : Computable fun x : CStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ha : Computable fun x : CStepArg => x.1.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have he : Computable fun x : CStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hb : Computable fun x : CStepArg => x.1.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hpass : Computable fun x : CStepArg => x.2.1 - 2 :=
    Primrec.nat_sub.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 2)
  have hslots : Computable fun x : CStepArg => x.2.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp (Computable.snd.comp Computable.snd)))))
  have hsm : Computable fun x : CStepArg => x.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact (computable_rawLocalServerMove.comp
    (((computable_grayChargedSpendDelta ha hL he hpass).pair hb).pair
      (hslots.pair hsm))).of_eq fun _ => rfl

/-- The round a spending pass freezes: its index and opening time, the coarse depth of the pass,
the slots it was played on, the client move, the allocation the localised server move granted,
and the unavailable set in force. -/
def chargedStepRound (x : CStepArg) : RawRound :=
  ((x.2.2.1.2.1.length, x.2.2.1.1.1,
      grayChargedSpendEps x.1.1.2.2.1 x.1.1.2.1 x.1.1.2.2.2 (x.2.1 - 2)),
    x.2.2.1.2.2.2.1, x.2.2.2.2, grayTailLocalAllocatedList (chargedStepLocalMove x),
    x.2.2.1.2.2.1)

/-- The round frozen by a spending pass is computable in the packed argument of the
transition. -/
theorem computable_chargedStepRound : Computable chargedStepRound := by
  have hL : Computable fun x : CStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ha : Computable fun x : CStepArg => x.1.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have he : Computable fun x : CStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hpass : Computable fun x : CStepArg => x.2.1 - 2 :=
    Primrec.nat_sub.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 2)
  have hst : Computable fun x : CStepArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have htime : Computable fun x : CStepArg => x.2.2.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp hst)
  have hr : Computable fun x : CStepArg => x.2.2.1.2.1.length :=
    Primrec.list_length.to_comp.comp (Computable.fst.comp (Computable.snd.comp hst))
  have hunav : Computable fun x : CStepArg => x.2.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hst))
  have hslots : Computable fun x : CStepArg => x.2.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hst)))
  have hcur : Computable fun x : CStepArg => x.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have halloc : Computable fun x : CStepArg =>
      grayTailLocalAllocatedList (chargedStepLocalMove x) :=
    computable_grayTailLocalAllocatedList.comp computable_chargedStepLocalMove
  exact ((hr.pair (htime.pair (computable_grayChargedSpendEps ha hL he hpass))).pair
    (hslots.pair (hcur.pair (halloc.pair hunav)))).of_eq fun _ => rfl

/-- The slots the next spending pass opens: the pass slots of pass `tag - 2 + 1`, selected
against the frozen list that this transition produces. -/
def chargedStepNextSlots (x : CStepArg) : List RawSlot :=
  rawChargedSlotsForPass x.1.1.1 x.1.1.2.2.1 x.1.1.2.2.2 x.1.2.1.1 x.1.2.1.2 (x.2.1 - 2 + 1)
    (x.2.2.1.2.1 ++ [chargedStepRound x])

/-- The slots of the next spending pass are computable in the packed argument of the
transition. -/
theorem computable_chargedStepNextSlots : Computable chargedStepNextSlots := by
  have hq : Computable fun x : CStepArg => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have ha : Computable fun x : CStepArg => x.1.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have he : Computable fun x : CStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hn : Computable fun x : CStepArg => x.1.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hb : Computable fun x : CStepArg => x.1.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hnextpass : Computable fun x : CStepArg => x.2.1 - 2 + 1 :=
    Primrec.succ.to_comp.comp (Primrec.nat_sub.to_comp.comp
      (Computable.fst.comp Computable.snd) (Computable.const 2))
  have hfrozen : Computable fun x : CStepArg =>
      x.2.2.1.2.1 ++ [chargedStepRound x] :=
    Primrec.list_append.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp
        (Computable.snd.comp Computable.snd))))
      (Computable.list_cons.comp computable_chargedStepRound (Computable.const []))
  exact (computable_chargedPassSlots.comp
    ((hq.pair (ha.pair he)).pair ((hn.pair (hb.pair hnextpass)).pair hfrozen))).of_eq
      fun _ => rfl

/-- The acceptance test of a spending pass: the charged goal read at the base with the depths of
the pass, the number of slots played, the unavailable set, the client move and the localised
server move. -/
def chargedStepGoal (x : CStepArg) : Bool :=
  grayChargedSpendGoalAtB x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2 (x.2.1 - 2)
    x.2.2.1.2.2.2.1.length x.2.2.1.2.2.1 x.2.2.2.2 (chargedStepLocalMove x)

/-- The acceptance test of a spending pass is computable in the packed argument of the
transition. -/
theorem computable_chargedStepGoal : Computable chargedStepGoal := by
  have hq : Computable fun x : CStepArg => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hL : Computable fun x : CStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ha : Computable fun x : CStepArg => x.1.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have he : Computable fun x : CStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hpass : Computable fun x : CStepArg => x.2.1 - 2 :=
    Primrec.nat_sub.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 2)
  have hst : Computable fun x : CStepArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hunav : Computable fun x : CStepArg => x.2.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hst))
  have hslots : Computable fun x : CStepArg => x.2.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hst)))
  have hcur : Computable fun x : CStepArg => x.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have halpha : Computable fun x : CStepArg =>
      dyadicScale (grayChargedSpendAlphaDepth x.1.1.2.2.1) :=
    computable_dyadicScale.comp
      ((Primrec.nat_add.to_comp.comp ha (Computable.const 3)).of_eq fun _ => rfl)
  have hgoalarg : Computable fun x : CStepArg =>
      ((((4 : ℚ), halfAmplification x.1.1.1,
          dyadicScale (grayChargedSpendAlphaDepth x.1.1.2.2.1),
          (3 / 4 : ℚ) * dyadicScale (grayChargedSpendAlphaDepth x.1.1.2.2.1)),
        (grayChargedSpendEps x.1.1.2.2.1 x.1.1.2.1 x.1.1.2.2.2 (x.2.1 - 2),
          grayChargedSpendDelta x.1.1.2.2.1 x.1.1.2.1 x.1.1.2.2.2 (x.2.1 - 2),
          x.2.2.1.2.2.2.1.length),
        x.2.2.1.2.2.1, x.2.2.2.2, chargedStepLocalMove x) : ChargedGrayGoalParam) :=
    ((Computable.const (4 : ℚ)).pair
        ((computable_halfAmplification.comp hq).pair (halpha.pair
          (computable₂_ratMul.comp (Computable.const ((3 : ℚ) / 4)) halpha)))).pair
      (((computable_grayChargedSpendEps ha hL he hpass).pair
          ((computable_grayChargedSpendDelta ha hL he hpass).pair
            (Primrec.list_length.to_comp.comp hslots))).pair
        (hunav.pair (hcur.pair computable_chargedStepLocalMove)))
  exact (computable_familyChargedGrayGoalAtB_joint.comp hgoalarg).of_eq fun _ => rfl

/-- The inputs of the final case distinction of one charged transition: the phase tag and its
successor, the incoming state, the advantage branch, the acceptance data of the spending pass,
the round it freezes with the slots it hands on, and the client and localised server moves. -/
def chargedStepAsmArg (x : CStepArg) : CAsmArg :=
  let L := x.1.1.2.1
  let a := x.1.1.2.2.1
  let e := x.1.1.2.2.2
  let n := x.1.2.1.1
  let b := x.1.2.1.2
  let A := x.1.2.2
  let tag := x.2.1
  let st := x.2.2.1
  let sm := x.2.2.2.1
  let current := x.2.2.2.2
  let nextSlots := chargedStepNextSlots x
  (((tag, tag - 2 + 3), st),
    chargedStepAdvance x,
    (st.2.2.2.1.isEmpty, chargedStepGoal x, tag - 2 + 1, nextSlots.isEmpty),
    (chargedStepRound x,
      A ++ rawGrayHarvest (grayChargedSpendDelta a L e (tag - 2 + 1)) b
        nextSlots n sm,
      nextSlots),
    current, chargedStepLocalMove x)

/-- The raw charged step is the assembly of its computed pieces. -/
theorem chargedStepP_eq_assemble (x : CStepArg) :
    chargedStepP x = chargedAsm (chargedStepAsmArg x) := rfl

/-- The pieces of the raw charged step are computable in its argument. -/
theorem computable_chargedStepAsmArg : Computable chargedStepAsmArg := by
  have hL : Computable fun x : CStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ha : Computable fun x : CStepArg => x.1.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have he : Computable fun x : CStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hn : Computable fun x : CStepArg => x.1.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hb : Computable fun x : CStepArg => x.1.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hAp : Computable fun x : CStepArg => x.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have htag : Computable fun x : CStepArg => x.2.1 := Computable.fst.comp Computable.snd
  have hst : Computable fun x : CStepArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hsm : Computable fun x : CStepArg => x.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hcur : Computable fun x : CStepArg => x.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hslots : Computable fun x : CStepArg => x.2.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hst)))
  -- the two derived pass indices
  have hnextpass : Computable fun x : CStepArg => x.2.1 - 2 + 1 :=
    Primrec.succ.to_comp.comp (Primrec.nat_sub.to_comp.comp htag (Computable.const 2))
  have hnexttag : Computable fun x : CStepArg => x.2.1 - 2 + 3 :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_sub.to_comp.comp htag (Computable.const 2)) (Computable.const 3)
  -- the unavailable set harvested from the slots of the next pass
  have hunavNext := Primrec.list_append.to_comp.comp hAp
    (computable_rawGrayHarvest (computable_grayChargedSpendDelta ha hL he hnextpass) hb
      computable_chargedStepNextSlots hn hsm)
  have harg := ((htag.pair hnexttag).pair hst).pair
    (computable_chargedStepAdvance.pair
      (((computable_list_isEmpty hslots).pair (computable_chargedStepGoal.pair
          (hnextpass.pair (computable_list_isEmpty computable_chargedStepNextSlots)))).pair
        ((computable_chargedStepRound.pair
          (hunavNext.pair computable_chargedStepNextSlots)).pair
          (hcur.pair computable_chargedStepLocalMove))))
  exact harg.of_eq fun _ => rfl

/-- The raw charged step is computable. -/
theorem computable_chargedStepP : Computable chargedStepP :=
  (computable_chargedAsm.comp computable_chargedStepAsmArg).of_eq fun x =>
    (chargedStepP_eq_assemble x).symm

end Kolmogorov
