import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedStepComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayPartrecFold

/-!
# The charged tail controller driven by a code oracle

This file assembles the oracle-driven form of the *charged* tail controller
`grayChargedStrategy`.  The single recursive call `grayTailCurrentMove` is
answered by running the supplied code through `codeEvalPart` -- the one partial
oracle -- and the finite server history is consumed by the genuine monadic fold
`pfoldl` of `GacsDayPartrecFold.lean`.  Nothing turns a failed oracle
evaluation into a semantic success: `chargedStepPart` is a `Part` and diverges
exactly when the oracle diverges.

`chargedPhi_eq` proves that on a code which really computes the previous scheme
the whole procedure converges to the encoding of the displayed move
`grayChargedStrategy`.

The file is written against the index-erased phase-tagged charged controller of
`GacsDayChargedRaw.lean` (whose commuting theorem with the real
`grayChargedStep` is `rawChargedStepWith_eq`) and its computability layer in
`GacsDayChargedRawComputable.lean` and `GacsDayChargedStepComputable.lean`.
-/


namespace Kolmogorov

open Encodable

/-- The input of the charged oracle controller: the two numeric parameters, the
code for the previous stage, and the scheme input. -/
abbrev ChargedOracleInput := (ℕ × ℕ) × Nat.Partrec.Code × SchemeInput

/-- The branching used by the charged tail controller on a given input.  This is
literally the branching appearing in `grayChargedStrategy`. -/
def chargedOracleBranch (v : ChargedOracleInput) : ℕ :=
  ladderBranching (grayTailBaseBranch v.1.1 v.1.2) v.2.2.1.1 v.2.2.1.2

/-- The packed erased-controller parameters determined by a charged oracle
input. -/
def chargedParamOf (v : ChargedOracleInput) : RawParam :=
  ((v.1.1, v.1.2, v.2.2.1.1, v.2.2.1.2), (v.2.2.2.2.1, chargedOracleBranch v), v.2.2.2.1)

/-- The query `rawChargedQuery` of the charged raw machine, read off a packed parameter `P`,
a round index `tag` and a state `st`: the four numeric fields of `P` are unpacked and passed
to `rawChargedQuery`. -/
def rawChargedQueryOf (P : RawParam) (tag : ℕ) (st : RawState) : SchemeInput :=
  rawChargedQuery P.1.1 P.1.2.1 P.1.2.2.1 P.1.2.2.2 tag st

/-- The query the charged raw machine issues from a parameter, a state and a round index is
computable. -/
theorem computable_rawChargedQueryOf :
    Computable fun x : (RawParam × RawState) × ℕ =>
      rawChargedQueryOf x.1.1 x.2 x.1.2 := by
  have hP : Computable fun x : (RawParam × RawState) × ℕ => x.1.1 :=
    Computable.fst.comp Computable.fst
  have htag : Computable fun x : (RawParam × RawState) × ℕ => x.2 :=
    Computable.snd
  have hst : Computable fun x : (RawParam × RawState) × ℕ => x.1.2 :=
    Computable.snd.comp Computable.fst
  have hq : Computable fun x : (RawParam × RawState) × ℕ => x.1.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp hP)
  have hL : Computable fun x : (RawParam × RawState) × ℕ => x.1.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp hP))
  have ha : Computable fun x : (RawParam × RawState) × ℕ => x.1.1.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp hP)))
  have he : Computable fun x : (RawParam × RawState) × ℕ => x.1.1.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp hP)))
  have hfr : Computable fun x : (RawParam × RawState) × ℕ =>
      x.1.2.2.1.length :=
    Primrec.list_length.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp hst))
  have hcall : Computable fun x : (RawParam × RawState) × ℕ =>
      grayCallDepth x.1.1.1.1 x.1.1.1.2.2.2 :=
    computable_grayCallDepth.comp hq he
  have hround : Computable fun x : (RawParam × RawState) × ℕ =>
      grayTailRoundEps x.1.1.1.1 x.1.1.1.2.1 x.1.1.1.2.2.2
        x.1.2.2.1.length :=
    (computable_grayTailRoundEps.comp
      (hq.pair (hL.pair (he.pair hfr)))).of_eq fun _ => rfl
  have hspBase : Computable fun x : (RawParam × RawState) × ℕ =>
      x.1.1.1.2.2.1 + 3 :=
    Primrec.nat_add.to_comp.comp ha (Computable.const 3)
  have hspA : Computable fun x : (RawParam × RawState) × ℕ =>
      grayChargedSpendAlphaDepth x.1.1.1.2.2.1 :=
    hspBase.of_eq fun _ => rfl
  have hepsRaw : Computable fun x : (RawParam × RawState) × ℕ =>
      x.1.1.1.2.2.2 - (x.2 - 2 + 1) * x.1.1.1.2.1 :=
    Primrec.nat_sub.to_comp.comp he
      (Primrec.nat_mul.to_comp.comp
        (Primrec.succ.to_comp.comp
          (Primrec.nat_sub.to_comp.comp htag (Computable.const 2))) hL)
  have hspE : Computable fun x : (RawParam × RawState) × ℕ =>
      grayChargedSpendEps x.1.1.1.2.2.1 x.1.1.1.2.1 x.1.1.1.2.2.2
        (x.2 - 2) :=
    ((Primrec.nat_add.to_comp.comp hspBase
        (Primrec.nat_sub.to_comp.comp hepsRaw hspBase))).of_eq fun x => by
      unfold grayChargedSpendEps grayChargedSpendAlphaDepth
      omega
  have hcond : Computable fun x : (RawParam × RawState) × ℕ =>
      decide (x.2 < 2) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp htag (Computable.const 2)
  have hite : Computable fun x : (RawParam × RawState) × ℕ =>
      ((if x.2 < 2 then
        ((grayCallDepth x.1.1.1.1 x.1.1.1.2.2.2,
          grayTailRoundEps x.1.1.1.1 x.1.1.1.2.1 x.1.1.1.2.2.2
            x.1.2.2.1.length) : ℕ × ℕ)
      else
        (grayChargedSpendAlphaDepth x.1.1.1.2.2.1,
          grayChargedSpendEps x.1.1.1.2.2.1 x.1.1.1.2.1 x.1.1.1.2.2.2
            (x.2 - 2))) : ℕ × ℕ) := by
    refine (Computable.cond hcond (hcall.pair hround)
      (hspA.pair hspE)).of_eq fun x => ?_
    by_cases hx : x.2 < 2 <;> simp [hx]
  have hpayload : Computable fun x : (RawParam × RawState) × ℕ =>
      (rawQueryOf x.1.1 x.1.2).2 :=
    Computable.snd.comp (computable_rawQueryOf.comp Computable.fst)
  exact (hite.pair hpayload).of_eq fun x => by
    unfold rawChargedQueryOf rawChargedQuery rawQueryOf rawQuery
    by_cases hx : x.2 < 2
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx]

/-- The `Encodable` code of the displayed move of the charged controller at a tagged state. -/
def chargedOutputEnc (P : RawParam) (tag : ℕ) (st : RawState)
    (cur : FamilyClientMove) : ℕ :=
  @Encodable.encode FamilyClientMove Primcodable.toEncodable
    (rawChargedOutput P.1.1 P.1.2.2.1 P.1.2.2.2 P.2.1.1 P.2.1.2 tag st cur)

/-- One oracle-driven transition of the erased phase-tagged charged controller.
The recursive call is the single `codeEvalPart` below; the transition converges
only if it does. -/
def chargedStepPart (w : RawParam × Nat.Partrec.Code) (stc : RawChargedState)
    (sm : FamilyServerMove) : Part RawChargedState :=
  (codeEvalPart (β := FamilyClientMove) w.2
      (rawChargedQueryOf w.1 stc.1 stc.2)).map
    fun cur => chargedStepP (w.1, stc.1, stc.2, sm, cur)

/-- The last oracle call: answer one more recursive call and display the encoded
charged move. -/
def chargedFinalPart (w : RawParam × Nat.Partrec.Code) (stc : RawChargedState) :
    Part ℕ :=
  (codeEvalPart (β := FamilyClientMove) w.2
      (rawChargedQueryOf w.1 stc.1 stc.2)).map
    fun cur => chargedOutputEnc w.1 stc.1 stc.2 cur

/-- The oracle-driven charged controller: fold the finite server history with
the partial charged step, then answer one last recursive call and display the
move. -/
def chargedPhi (v : ChargedOracleInput) : Part ℕ :=
  (pfoldl chargedStepPart (chargedParamOf v, v.2.1)
      (((0 : ℕ), rawInitialStateOf (chargedParamOf v)) : RawChargedState)
      v.2.2.2.2.2.2).bind fun stc => chargedFinalPart (chargedParamOf v, v.2.1) stc

/-! ### Computability of the parameters -/

/-- The branch selector of the charged oracle is primitive recursive. -/
theorem primrec_chargedOracleBranch : Primrec chargedOracleBranch := by
  have hB : Primrec fun v : ChargedOracleInput => grayTailBaseBranch v.1.1 v.1.2 :=
    primrec₂_grayTailBaseBranch.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)
  have ha : Primrec fun v : ChargedOracleInput => v.2.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have he : Primrec fun v : ChargedOracleInput => v.2.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hpow : Primrec fun v : ChargedOracleInput => 2 * 2 ^ (v.2.2.1.2 - v.2.2.1.1) :=
    Primrec.nat_mul.comp (Primrec.const 2)
      (nat_pow_primrec₂.comp (Primrec.const 2) (Primrec.nat_sub.comp he ha))
  exact (Primrec.nat_max.comp hpow hB).of_eq fun _ => rfl

/-- Reading the raw parameters out of a charged oracle input is computable. -/
theorem computable_chargedParamOf : Computable chargedParamOf := by
  have hq : Primrec fun v : ChargedOracleInput => v.1.1 := Primrec.fst.comp Primrec.fst
  have hL : Primrec fun v : ChargedOracleInput => v.1.2 := Primrec.snd.comp Primrec.fst
  have ha : Primrec fun v : ChargedOracleInput => v.2.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have he : Primrec fun v : ChargedOracleInput => v.2.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hA : Primrec fun v : ChargedOracleInput => v.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hn : Primrec fun v : ChargedOracleInput => v.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact ((hq.pair (hL.pair (ha.pair he))).pair
    ((hn.pair primrec_chargedOracleBranch).pair hA)).to_comp

/-- Encoding the output of a charged step is computable. -/
theorem computable_chargedOutputEnc :
    Computable fun x : RawParam × (ℕ × RawState) × FamilyClientMove =>
      chargedOutputEnc x.1 x.2.1.1 x.2.1.2 x.2.2 := by
  have harg : Computable fun x : RawParam × (ℕ × RawState) × FamilyClientMove =>
      (((x.1.1.1, x.1.1.2.2.1, x.1.1.2.2.2), (x.1.2.1.1, x.1.2.1.2),
        x.2.1.1, x.2.1.2, x.2.2) : COutArg) := by
    have hq : Computable fun x : RawParam × (ℕ × RawState) × FamilyClientMove => x.1.1.1 :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have ha : Computable fun x : RawParam × (ℕ × RawState) × FamilyClientMove =>
        x.1.1.2.2.1 :=
      Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst)))
    have he : Computable fun x : RawParam × (ℕ × RawState) × FamilyClientMove =>
        x.1.1.2.2.2 :=
      Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst)))
    have hn : Computable fun x : RawParam × (ℕ × RawState) × FamilyClientMove =>
        x.1.2.1.1 :=
      Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    have hb : Computable fun x : RawParam × (ℕ × RawState) × FamilyClientMove =>
        x.1.2.1.2 :=
      Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    have htag : Computable fun x : RawParam × (ℕ × RawState) × FamilyClientMove =>
        x.2.1.1 := Computable.fst.comp (Computable.fst.comp Computable.snd)
    have hst : Computable fun x : RawParam × (ℕ × RawState) × FamilyClientMove =>
        x.2.1.2 := Computable.snd.comp (Computable.fst.comp Computable.snd)
    have hcur : Computable fun x : RawParam × (ℕ × RawState) × FamilyClientMove =>
        x.2.2 := Computable.snd.comp Computable.snd
    exact (hq.pair (ha.pair he)).pair ((hn.pair hb).pair (htag.pair (hst.pair hcur)))
  exact (Computable.encode.comp (computable_chargedOutP.comp harg)).of_eq fun _ => rfl

/-! ### Partial recursiveness -/

/-- One charged step, as a partial function of parameter, code, state and server move, is partial
recursive. -/
theorem partrec_chargedStepPart :
    Partrec fun x : (RawParam × Nat.Partrec.Code) × RawChargedState × FamilyServerMove =>
      chargedStepPart x.1 x.2.1 x.2.2 := by
  have hP : Computable
      fun x : (RawParam × Nat.Partrec.Code) × RawChargedState × FamilyServerMove =>
        x.1.1 := Computable.fst.comp Computable.fst
  have hcode : Computable
      fun x : (RawParam × Nat.Partrec.Code) × RawChargedState × FamilyServerMove =>
        x.1.2 := Computable.snd.comp Computable.fst
  have htag : Computable
      fun x : (RawParam × Nat.Partrec.Code) × RawChargedState × FamilyServerMove =>
        x.2.1.1 := Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hst : Computable
      fun x : (RawParam × Nat.Partrec.Code) × RawChargedState × FamilyServerMove =>
        x.2.1.2 := Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hsm : Computable
      fun x : (RawParam × Nat.Partrec.Code) × RawChargedState × FamilyServerMove =>
        x.2.2 := Computable.snd.comp Computable.snd
  have hquery := computable_rawChargedQueryOf.comp ((hP.pair hst).pair htag)
  have horacle := (partrec₂_codeEvalPart (β := FamilyClientMove)).comp (hcode.pair hquery)
  have hmap : Computable₂
      fun (x : (RawParam × Nat.Partrec.Code) × RawChargedState × FamilyServerMove)
        (cur : FamilyClientMove) => chargedStepP (x.1.1, x.2.1.1, x.2.1.2, x.2.2, cur) :=
    (computable_chargedStepP.comp
      ((hP.comp Computable.fst).pair
        ((htag.comp Computable.fst).pair
          ((hst.comp Computable.fst).pair
            ((hsm.comp Computable.fst).pair Computable.snd))))).to₂
  exact horacle.map hmap

/-- Folding the charged step over the history of server moves is partial recursive. -/
theorem partrec_chargedFold :
    Partrec fun v : ChargedOracleInput =>
      pfoldl chargedStepPart (chargedParamOf v, v.2.1)
        (((0 : ℕ), rawInitialStateOf (chargedParamOf v)) : RawChargedState)
        v.2.2.2.2.2.2 := by
  have hcode : Computable fun v : ChargedOracleInput => v.2.1 :=
    Computable.fst.comp Computable.snd
  have hhist : Computable fun v : ChargedOracleInput => v.2.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have hw : Computable fun v : ChargedOracleInput =>
      ((chargedParamOf v, v.2.1) : RawParam × Nat.Partrec.Code) :=
    computable_chargedParamOf.pair hcode
  have hinit : Computable fun v : ChargedOracleInput =>
      (((0 : ℕ), rawInitialStateOf (chargedParamOf v)) : RawChargedState) :=
    (Computable.const 0).pair (computable_rawInitialStateOf.comp computable_chargedParamOf)
  have h1 : Partrec
      fun x : (RawParam × Nat.Partrec.Code) × RawChargedState × List FamilyServerMove =>
        pfoldl chargedStepPart x.1 x.2.1 x.2.2 := partrec_pfoldl partrec_chargedStepPart
  have harg : Computable fun v : ChargedOracleInput =>
      (((chargedParamOf v, v.2.1),
          ((0 : ℕ), rawInitialStateOf (chargedParamOf v)), v.2.2.2.2.2.2) :
        (RawParam × Nat.Partrec.Code) × RawChargedState × List FamilyServerMove) :=
    hw.pair (hinit.pair hhist)
  exact (h1.comp harg).of_eq fun _ => rfl

/-- Reading the final client move off a charged state is partial recursive. -/
theorem partrec_chargedFinalPart :
    Partrec fun z : (RawParam × Nat.Partrec.Code) × RawChargedState =>
      chargedFinalPart z.1 z.2 := by
  have hP : Computable fun z : (RawParam × Nat.Partrec.Code) × RawChargedState => z.1.1 :=
    Computable.fst.comp Computable.fst
  have hcode : Computable
      fun z : (RawParam × Nat.Partrec.Code) × RawChargedState => z.1.2 :=
    Computable.snd.comp Computable.fst
  have htag : Computable
      fun z : (RawParam × Nat.Partrec.Code) × RawChargedState => z.2.1 :=
    Computable.fst.comp Computable.snd
  have hst : Computable
      fun z : (RawParam × Nat.Partrec.Code) × RawChargedState => z.2.2 :=
    Computable.snd.comp Computable.snd
  have hquery := computable_rawChargedQueryOf.comp ((hP.pair hst).pair htag)
  have horacle := (partrec₂_codeEvalPart (β := FamilyClientMove)).comp (hcode.pair hquery)
  have hout : Computable₂ fun (z : (RawParam × Nat.Partrec.Code) × RawChargedState)
      (cur : FamilyClientMove) => chargedOutputEnc z.1.1 z.2.1 z.2.2 cur :=
    (computable_chargedOutputEnc.comp
      ((hP.comp Computable.fst).pair
        (((htag.comp Computable.fst).pair (hst.comp Computable.fst)).pair
          Computable.snd))).to₂
  exact horacle.map hout

/-- Reading the final client move off a charged state is partial recursive in the input and the
state jointly. -/
theorem partrec₂_chargedFinal :
    Partrec₂ fun (v : ChargedOracleInput) (stc : RawChargedState) =>
      chargedFinalPart (chargedParamOf v, v.2.1) stc := by
  have hw : Computable fun y : ChargedOracleInput × RawChargedState =>
      ((chargedParamOf y.1, y.1.2.1) : RawParam × Nat.Partrec.Code) :=
    (computable_chargedParamOf.comp Computable.fst).pair
      (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have harg : Computable fun y : ChargedOracleInput × RawChargedState =>
      (((chargedParamOf y.1, y.1.2.1), y.2) :
        (RawParam × Nat.Partrec.Code) × RawChargedState) :=
    hw.pair Computable.snd
  exact (partrec_chargedFinalPart.comp harg).of_eq fun _ => rfl

/-- The charged oracle `chargedPhi` is partial recursive. -/
theorem partrec_chargedPhi : Partrec chargedPhi :=
  (partrec_chargedFold.bind partrec₂_chargedFinal).of_eq fun _ => rfl

/-! ### Semantics -/

/-- On a code computing the scheme `sigma`, the charged oracle returns exactly the move of the
charged strategy `grayChargedStrategy q L a e sigma`. -/
theorem chargedPhi_eq (q L : ℕ) (code : Nat.Partrec.Code) (sigma : FamilyStrategyScheme)
    (h : CodeComputesScheme code sigma) (p : SchemeInput) :
    chargedPhi ((q, L), code, p) =
      Part.some (@encode FamilyClientMove Primcodable.toEncodable
        (grayChargedStrategy q L p.1.1 p.1.2 sigma p.2.1 p.2.2.1 p.2.2.2)) := by
  obtain ⟨⟨a, e⟩, A, n, hist⟩ := p
  set b := ladderBranching (grayTailBaseBranch q L) a e with hbdef
  set P : RawParam := ((q, L, a, e), (n, b), A) with hPdef
  have hoc : ∀ x : SchemeInput,
      codeEvalPart (β := FamilyClientMove) code x
        = Part.some (sigma x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2) :=
    codeEvalPart_of_codeComputes h
  set cur : ℕ → RawState → FamilyClientMove := fun tag st =>
    sigma (rawChargedQuery q L a e tag st).1.1
      (rawChargedQuery q L a e tag st).1.2
      (rawChargedQuery q L a e tag st).2.1
      (rawChargedQuery q L a e tag st).2.2.1
      (rawChargedQuery q L a e tag st).2.2.2 with hcurdef
  have hstep : ∀ (stc : RawChargedState) (sm : FamilyServerMove),
      chargedStepPart (P, code) stc sm =
        Part.some (rawChargedStepWith q L a e n b A stc.1 stc.2 sm (cur stc.1 stc.2)) := by
    intro stc sm
    rw [chargedStepPart, hoc]
    rfl
  have hfold :
      pfoldl chargedStepPart (P, code)
          (((0 : ℕ), rawInitialStateOf P) : RawChargedState) hist.2 =
        Part.some (hist.2.foldl
          (fun stc sm => rawChargedStepWith q L a e n b A stc.1 stc.2 sm (cur stc.1 stc.2))
          ((0 : ℕ), rawInitialStateOf P)) :=
    pfoldl_eq_some_foldl hstep _ _
  have hraw : hist.2.foldl
      (fun stc sm => rawChargedStepWith q L a e n b A stc.1 stc.2 sm (cur stc.1 stc.2))
      ((0 : ℕ), rawInitialStateOf P) =
      toRawChargedState (grayChargedFold (n := n) (b := b) q L a e sigma A hist.2) :=
    rawChargedFoldWith_eq q L a e sigma A hist.2
  change (pfoldl chargedStepPart (P, code)
      (((0 : ℕ), rawInitialStateOf P) : RawChargedState) hist.2).bind
      (fun stc => chargedFinalPart (P, code) stc) = _
  rw [hfold, Part.bind_some, hraw, chargedFinalPart, hoc]
  simp only [Part.map_some, Part.some_inj]
  change @Encodable.encode FamilyClientMove Primcodable.toEncodable
      (rawChargedOutput q a e n b
        (chargedPhaseTag (grayChargedFold (n := n) (b := b) q L a e sigma A hist.2).phase)
        (toRawState (grayChargedFold (n := n) (b := b) q L a e sigma A hist.2).core)
        (cur
          (chargedPhaseTag
            (grayChargedFold (n := n) (b := b) q L a e sigma A hist.2).phase)
          (toRawState
            (grayChargedFold (n := n) (b := b) q L a e sigma A hist.2).core))) = _
  congr 1
  simp only [hcurdef]
  rw [rawChargedQuery_eq_phase q L a e _ sigma,
    rawChargedOutput_eq q L a e sigma]
  rfl

end Kolmogorov
