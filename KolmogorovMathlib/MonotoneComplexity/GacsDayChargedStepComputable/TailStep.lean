import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRawComputable

/-!
# Computability of the charged advantage transition

The charged advantage transition `rawChargedTailStepWith` performs exactly the
case distinction already packaged as `rawStepAssemble` in
`GacsDayLadderTailRawComputable.lean`; only the acceptance test and the round
budget differ.  We therefore feed `rawStepAssemble` with charged data.

This module carries that transition: the packed form `chargedTailStepP`, the
inputs `chargedTailAsm` of its final case distinction, and the pieces of those
inputs — the localised server move, the frozen round, the acceptance test and
the candidate slots — each with its own computability lemma.  The
phase-tagged transition built on top of it is in the parent module.
-/


namespace Kolmogorov

/-! ### The charged advantage transition -/

/-- Packed charged advantage transition. -/
def chargedTailStepP (x : RawStepArg) : RawState :=
  rawChargedTailStepWith x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2 x.1.2.1.1 x.1.2.1.2
    x.1.2.2 x.2.1 x.2.2.1 x.2.2.2

/-- Charged variant of `rawStepAssemble`: the accept branch installs the
supplied unavailable list verbatim — the per-round snapshot harvest of
v14 §9.2 — instead of appending an increment to the old list. -/
def chargedRawStepAssemble (z : RawAsmArg) : RawState :=
  if z.1.1 then
    ((z.1.2.1 + 1, z.1.2.2.1, z.1.2.2.2), z.2.1)
  else if z.2.2.1.1 then
    ((z.1.2.1 + 1, z.1.2.1 + 1,
        z.2.2.2.1.1 ||
          decide (z.2.2.2.1.2 ≤ (z.2.1.1 ++ [z.2.2.1.2.2.1]).length)),
      (z.2.1.1 ++ [z.2.2.1.2.2.1], z.2.2.1.2.2.2.1,
        z.2.2.1.2.2.2.2, [], ([], [])))
  else
    ((z.1.2.1 + 1, z.1.2.2.1, z.1.2.2.2),
      (z.2.1.1, z.2.1.2.1, z.2.1.2.2.1, z.2.1.2.2.2.1,
        (z.2.1.2.2.2.2.1 ++ [z.2.2.2.2.1],
          z.2.1.2.2.2.2.2 ++ [z.2.2.2.2.2])))

/-- Assembling the raw charged step from its computed pieces is computable. -/
theorem computable_chargedRawStepAssemble :
    Computable chargedRawStepAssemble := by
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
        (z.2.1.1 ++ [z.2.2.1.2.2.1], z.2.2.1.2.2.2.1,
          z.2.2.1.2.2.2.2, [], (([], []) : FamilyGameHistory))) : RawState) :=
    (hsucc.pair (hsucc.pair hdone')).pair
      (hfrozen'.pair (hnbrs.pair (hcand.pair
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
  rw [chargedRawStepAssemble]
  cases z.1.1 <;> cases z.2.2.1.1 <;> simp

/-! ### The pieces of one advantage transition -/

/-- The server move an advantage transition actually plays against: the incoming server move
restricted to the son subtree of the base and truncated to the fine depth of the round that is
being frozen. -/
def chargedTailLocalMove (x : RawStepArg) : FamilyServerMove :=
  rawLocalServerMove (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length)
    x.1.2.1.2 x.2.1.2.2.2.1 x.2.2.1

/-- The localised server move of an advantage transition is computable in the packed argument
of the transition. -/
theorem computable_chargedTailLocalMove : Computable chargedTailLocalMove := by
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
  have hslots : Computable fun x : RawStepArg => x.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hst)))
  have hsm : Computable fun x : RawStepArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hr : Computable fun x : RawStepArg => x.2.1.2.1.length :=
    Primrec.list_length.to_comp.comp (Computable.fst.comp (Computable.snd.comp hst))
  have hdelta : Computable fun x : RawStepArg =>
      grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length :=
    (computable_grayTailRoundDelta.comp (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  exact (computable_rawLocalServerMove.comp
    ((hdelta.pair hb).pair (hslots.pair hsm))).of_eq fun _ => rfl

/-- The round an advantage transition freezes: its index and opening time, its coarse depth,
the slots it was played on, the client move, the allocation the localised server move granted,
and the unavailable set in force. -/
def chargedTailRound (x : RawStepArg) : RawRound :=
  ((x.2.1.2.1.length, x.2.1.1.1,
      grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length),
    x.2.1.2.2.2.1, x.2.2.2, grayTailLocalAllocatedList (chargedTailLocalMove x), x.2.1.2.2.1)

/-- The round frozen by an advantage transition is computable in the packed argument of the
transition. -/
theorem computable_chargedTailRound : Computable chargedTailRound := by
  have hq : Computable fun x : RawStepArg => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hL : Computable fun x : RawStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have he : Computable fun x : RawStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hst : Computable fun x : RawStepArg => x.2.1 := Computable.fst.comp Computable.snd
  have htime : Computable fun x : RawStepArg => x.2.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp hst)
  have hunav : Computable fun x : RawStepArg => x.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hst))
  have hslots : Computable fun x : RawStepArg => x.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hst)))
  have hcur : Computable fun x : RawStepArg => x.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hr : Computable fun x : RawStepArg => x.2.1.2.1.length :=
    Primrec.list_length.to_comp.comp (Computable.fst.comp (Computable.snd.comp hst))
  have heps : Computable fun x : RawStepArg =>
      grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length :=
    (computable_grayTailRoundEps.comp (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have halloc : Computable fun x : RawStepArg =>
      grayTailLocalAllocatedList (chargedTailLocalMove x) :=
    computable_grayTailLocalAllocatedList.comp computable_chargedTailLocalMove
  exact ((hr.pair (htime.pair heps)).pair
    (hslots.pair (hcur.pair (halloc.pair hunav)))).of_eq fun _ => rfl

/-- The frozen list an advantage transition hands on: the old frozen rounds with the round of
this transition appended. -/
def chargedTailFrozen (x : RawStepArg) : List RawRound :=
  x.2.1.2.1 ++ [chargedTailRound x]

/-- The frozen list produced by an advantage transition is computable in the packed argument of
the transition. -/
theorem computable_chargedTailFrozen : Computable chargedTailFrozen :=
  (Primrec.list_append.to_comp.comp
    (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.snd)))
    (Computable.list_cons.comp computable_chargedTailRound
      (Computable.const []))).of_eq fun _ => rfl

/-- The acceptance test of an advantage round: the charged goal of the tail, read at the base
with the round's coarse and fine depths, the number of slots played, the unavailable set, the
client move and the localised server move. -/
def chargedTailGoal (x : RawStepArg) : Bool :=
  grayChargedTailGoalAtB x.1.1.1 x.1.1.2.2.2
    (grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length)
    (grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length)
    x.2.1.2.2.2.1.length x.2.1.2.2.1 x.2.2.2 (chargedTailLocalMove x)

/-- The acceptance test of an advantage round is computable in the packed argument of the
transition. -/
theorem computable_chargedTailGoal : Computable chargedTailGoal := by
  have hq : Computable fun x : RawStepArg => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hL : Computable fun x : RawStepArg => x.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have he : Computable fun x : RawStepArg => x.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hst : Computable fun x : RawStepArg => x.2.1 := Computable.fst.comp Computable.snd
  have hunav : Computable fun x : RawStepArg => x.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hst))
  have hslots : Computable fun x : RawStepArg => x.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hst)))
  have hcur : Computable fun x : RawStepArg => x.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hr : Computable fun x : RawStepArg => x.2.1.2.1.length :=
    Primrec.list_length.to_comp.comp (Computable.fst.comp (Computable.snd.comp hst))
  have heps : Computable fun x : RawStepArg =>
      grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length :=
    (computable_grayTailRoundEps.comp (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have hdelta : Computable fun x : RawStepArg =>
      grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length :=
    (computable_grayTailRoundDelta.comp (hq.pair (hL.pair (he.pair hr)))).of_eq fun _ => rfl
  have halpha : Computable fun x : RawStepArg =>
      dyadicScale (grayCallDepth x.1.1.1 x.1.1.2.2.2) :=
    computable_dyadicScale.comp (computable_grayCallDepth.comp hq he)
  have hgoalarg : Computable fun x : RawStepArg =>
      ((((4 : ℚ), halfAmplification x.1.1.1,
          dyadicScale (grayCallDepth x.1.1.1 x.1.1.2.2.2),
          (3 / 4 : ℚ) * dyadicScale (grayCallDepth x.1.1.1 x.1.1.2.2.2)),
        (grayTailRoundEps x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length,
          grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 x.2.1.2.1.length,
          x.2.1.2.2.2.1.length),
        x.2.1.2.2.1, x.2.2.2, chargedTailLocalMove x) : ChargedGrayGoalParam) :=
    ((Computable.const (4 : ℚ)).pair
        ((computable_halfAmplification.comp hq).pair (halpha.pair
          (computable₂_ratMul.comp (Computable.const ((3 : ℚ) / 4)) halpha)))).pair
      ((heps.pair (hdelta.pair (Primrec.list_length.to_comp.comp hslots))).pair
        (hunav.pair (hcur.pair computable_chargedTailLocalMove)))
  exact (computable_familyChargedGrayGoalAtB_joint.comp hgoalarg).of_eq fun _ => rfl

/-- The slots an advantage transition offers for the next round: the slots still below the
charged threshold, selected from the base against the frozen list this transition produces. -/
def chargedTailCand (x : RawStepArg) : List RawSlot :=
  rawNextSlots x.1.2.1.1 x.1.2.1.2 x.1.1.2.2.2
    (grayChargedSourceCount x.1.1.2.2.1 x.1.1.2.2.2) (chargedTailFrozen x).length
    (grayChargedThreshold x.1.1.1 x.1.1.2.2.2) x.1.2.2 (chargedTailFrozen x) x.2.2.1

/-- The candidate slots of an advantage transition are computable in the packed argument of the
transition. -/
theorem computable_chargedTailCand : Computable chargedTailCand := by
  have hq : Computable fun x : RawStepArg => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
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
  have hsm : Computable fun x : RawStepArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hpow : Computable fun x : RawStepArg =>
      grayChargedSourceCount x.1.1.2.2.1 x.1.1.2.2.2 :=
    (nat_pow_primrec₂.to_comp.comp (Computable.const 2)
      (Primrec.nat_sub.to_comp.comp he ha)).of_eq fun _ => rfl
  have hthr : Computable fun x : RawStepArg => grayChargedThreshold x.1.1.1 x.1.1.2.2.2 :=
    (computable₂_rawThreshold.comp hq he).of_eq fun _ => rfl
  have hcandarg : Computable fun x : RawStepArg =>
      (((x.1.2.1.1, x.1.2.1.2, x.1.1.2.2.2,
          grayChargedSourceCount x.1.1.2.2.1 x.1.1.2.2.2, (chargedTailFrozen x).length),
        grayChargedThreshold x.1.1.1 x.1.1.2.2.2, x.1.2.2,
        chargedTailFrozen x, x.2.2.1) : RawNextArg) :=
    (hn.pair (hb.pair (he.pair (hpow.pair
      (Primrec.list_length.to_comp.comp computable_chargedTailFrozen))))).pair
      (hthr.pair (hA.pair (computable_chargedTailFrozen.pair hsm)))
  exact (computable_rawNextSlots.comp hcandarg).of_eq fun _ => rfl

/-- The packed inputs of the final case distinction of one charged advantage
transition: the phase flag and clock, the incoming state, the acceptance test with the round
and the slots it hands on, the global budget, and the client and localised server moves. -/
def chargedTailAsm (x : RawStepArg) : RawAsmArg :=
  let q := x.1.1.1
  let L := x.1.1.2.1
  let a := x.1.1.2.2.1
  let e := x.1.1.2.2.2
  let n := x.1.2.1.1
  let b := x.1.2.1.2
  let A := x.1.2.2
  let st := x.2.1
  let sm := x.2.2.1
  let current := x.2.2.2
  let cand := chargedTailCand x
  ((st.1.2.2 || st.2.2.2.1.isEmpty, st.1.1, st.1.2.1, st.1.2.2),
    st.2,
    (chargedTailGoal x, false, chargedTailRound x,
      A ++ rawGrayHarvest (grayTailRoundDelta q L e (chargedTailFrozen x).length) b cand n sm,
      cand),
    (rawGlobalQuarterB n (grayChargedSourceCount a e) cand,
      grayChargedAdvantageRoundCount q),
    current, chargedTailLocalMove x)

/-- The raw tail step is the assembly of its computed pieces. -/
theorem chargedTailStepP_eq_assemble (x : RawStepArg) :
    chargedTailStepP x = chargedRawStepAssemble (chargedTailAsm x) := by
  cases hd : x.2.1.1.2.2 <;> cases hs : x.2.1.2.2.2.1.isEmpty <;>
    simp [chargedTailStepP, chargedTailAsm, chargedTailGoal, chargedTailRound,
      chargedTailFrozen, chargedTailCand, chargedTailLocalMove, chargedRawStepAssemble,
      rawChargedTailStepWith, hd, hs]

/-- The pieces of the raw tail step are computable in its argument. -/
theorem computable_chargedTailAsm : Computable chargedTailAsm := by
  -- parameters
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
  have hrest : Computable fun x : RawStepArg => x.2.1.2 := Computable.snd.comp hst
  have hslots : Computable fun x : RawStepArg => x.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hst)))
  -- the harvest of the candidate slots
  have hpow : Computable fun x : RawStepArg =>
      grayChargedSourceCount x.1.1.2.2.1 x.1.1.2.2.2 :=
    (nat_pow_primrec₂.to_comp.comp (Computable.const 2)
      (Primrec.nat_sub.to_comp.comp he ha)).of_eq fun _ => rfl
  have hglobal : Computable fun x : RawStepArg =>
      rawGlobalQuarterB x.1.2.1.1 (grayChargedSourceCount x.1.1.2.2.1 x.1.1.2.2.2)
        (chargedTailCand x) :=
    (computable_rawGlobalQuarterB.comp
      ((hn.pair hpow).pair computable_chargedTailCand)).of_eq fun _ => rfl
  have hdeltaNext : Computable fun x : RawStepArg =>
      grayTailRoundDelta x.1.1.1 x.1.1.2.1 x.1.1.2.2.2 (chargedTailFrozen x).length :=
    (computable_grayTailRoundDelta.comp (hq.pair (hL.pair (he.pair
      (Primrec.list_length.to_comp.comp computable_chargedTailFrozen))))).of_eq fun _ => rfl
  have hharv := Primrec.list_append.to_comp.comp hA
    (computable_rawGrayHarvest hdeltaNext hb computable_chargedTailCand hn hsm)
  -- the phase flag and the round budget
  have hcond : Computable fun x : RawStepArg =>
      (x.2.1.1.2.2 || x.2.1.2.2.2.1.isEmpty) := by
    refine (Computable.cond hdone (Computable.const true)
      (computable_list_isEmpty hslots)).of_eq fun x => ?_
    cases x.2.1.1.2.2 <;> simp
  have hrc : Computable fun x : RawStepArg => grayChargedAdvantageRoundCount x.1.1.1 :=
    (Primrec.nat_sub.to_comp.comp (primrec_grayTailRoundCount.to_comp.comp hq)
      (Computable.const 8)).of_eq fun _ => rfl
  have harg := (hcond.pair (htime.pair (hstart.pair hdone))).pair
    (hrest.pair
      ((computable_chargedTailGoal.pair ((Computable.const false).pair
        (computable_chargedTailRound.pair (hharv.pair computable_chargedTailCand)))).pair
        ((hglobal.pair hrc).pair (hcur.pair computable_chargedTailLocalMove))))
  exact harg.of_eq fun _ => rfl

/-- The raw tail step is computable. -/
theorem computable_chargedTailStepP : Computable chargedTailStepP :=
  (computable_chargedRawStepAssemble.comp computable_chargedTailAsm).of_eq fun x =>
    (chargedTailStepP_eq_assemble x).symm

end Kolmogorov
