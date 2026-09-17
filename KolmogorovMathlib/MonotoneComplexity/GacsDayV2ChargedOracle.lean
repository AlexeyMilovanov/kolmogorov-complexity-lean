import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedStepComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedOracle

/-!
# The V2 charged controller driven by a code oracle

The V2 twin of `GacsDayChargedOracle.lean`.  The single recursive child call of
`grayChargedStrategyV2` is answered by running the supplied code through
`codeEvalPart` — the one partial oracle — and the finite server history is
consumed by the genuine monadic fold `pfoldl` of `GacsDayPartrecFold.lean`.
Nothing turns a failed oracle evaluation into a semantic success:
`chargedStepPartV2` is a `Part` and diverges exactly when the oracle diverges.

`chargedPhiV2_eq` proves that on a code which really computes the previous
scheme the whole procedure converges to the encoding of the displayed move
`grayChargedStrategyV2`.

The oracle *input* and the packed *parameters* are shared with V1 verbatim:
`RawParamV2` and `RawParam` are the same product, and the V2 controller runs at
the same outer branching `grayTailBranch q L a e = chargedOracleBranch v`, so
`chargedParamOf` and `computable_chargedParamOf` are reused unchanged.  What is
V2-specific is the erased state (`RawChargedStateV2`), the transition
(`rawStepOfV2`), the child query (`rawQueryOfV2`) and the displayed move
(`rawOutputEncV2`), all supplied by `GacsDayV2ChargedRaw.lean` and its
computability layer.
-/


namespace Kolmogorov

open Encodable

/-- One oracle-driven transition of the erased phase-tagged V2 controller.  The
recursive child call is the single `codeEvalPart` below; the transition
converges only if it does. -/
def chargedStepPartV2 (w : RawParamV2 × Nat.Partrec.Code)
    (stc : RawChargedStateV2) (sm : FamilyServerMove) :
    Part RawChargedStateV2 :=
  (codeEvalPart (β := FamilyClientMove) w.2 (rawQueryOfV2 w.1 stc)).map
    fun cur => rawStepOfV2 w.1 stc sm cur

/-- The last oracle call: answer one more child call and display the encoded
V2 move. -/
def chargedFinalPartV2 (w : RawParamV2 × Nat.Partrec.Code)
    (stc : RawChargedStateV2) : Part ℕ :=
  (codeEvalPart (β := FamilyClientMove) w.2 (rawQueryOfV2 w.1 stc)).map
    fun cur => rawOutputEncV2 w.1 stc cur

/-- The oracle-driven V2 charged controller: fold the finite server history with
the partial V2 step, then answer one last child call and display the move. -/
def chargedPhiV2 (v : ChargedOracleInput) : Part ℕ :=
  (pfoldl chargedStepPartV2 (chargedParamOf v, v.2.1)
      (rawInitialStateOfV2 (chargedParamOf v))
      v.2.2.2.2.2.2).bind fun stc =>
    chargedFinalPartV2 (chargedParamOf v, v.2.1) stc

/-! ### Partial recursiveness -/

/-- One V2 charged step is partial recursive in parameter, code, state and server move. -/
theorem partrec_chargedStepPartV2 :
    Partrec fun x : (RawParamV2 × Nat.Partrec.Code) × RawChargedStateV2 ×
        FamilyServerMove => chargedStepPartV2 x.1 x.2.1 x.2.2 := by
  have hP : Computable fun x : (RawParamV2 × Nat.Partrec.Code) ×
      RawChargedStateV2 × FamilyServerMove => x.1.1 :=
    Computable.fst.comp Computable.fst
  have hcode : Computable fun x : (RawParamV2 × Nat.Partrec.Code) ×
      RawChargedStateV2 × FamilyServerMove => x.1.2 :=
    Computable.snd.comp Computable.fst
  have hstc : Computable fun x : (RawParamV2 × Nat.Partrec.Code) ×
      RawChargedStateV2 × FamilyServerMove => x.2.1 :=
    Computable.fst.comp Computable.snd
  have hsm : Computable fun x : (RawParamV2 × Nat.Partrec.Code) ×
      RawChargedStateV2 × FamilyServerMove => x.2.2 :=
    Computable.snd.comp Computable.snd
  have hquery := computable_rawQueryOfV2.comp (hP.pair hstc)
  have horacle :=
    (partrec₂_codeEvalPart (β := FamilyClientMove)).comp (hcode.pair hquery)
  have hmap : Computable₂ fun (x : (RawParamV2 × Nat.Partrec.Code) ×
      RawChargedStateV2 × FamilyServerMove) (cur : FamilyClientMove) =>
      rawStepOfV2 x.1.1 x.2.1 x.2.2 cur :=
    (computable_rawStepOfV2.comp
      ((hP.comp Computable.fst).pair
        ((hstc.comp Computable.fst).pair
          ((hsm.comp Computable.fst).pair Computable.snd)))).to₂
  exact horacle.map hmap

/-- Folding the V2 charged step over the history of server moves is partial recursive. -/
theorem partrec_chargedFoldV2 :
    Partrec fun v : ChargedOracleInput =>
      pfoldl chargedStepPartV2 (chargedParamOf v, v.2.1)
        (rawInitialStateOfV2 (chargedParamOf v)) v.2.2.2.2.2.2 := by
  have hcode : Computable fun v : ChargedOracleInput => v.2.1 :=
    Computable.fst.comp Computable.snd
  have hhist : Computable fun v : ChargedOracleInput => v.2.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have hw : Computable fun v : ChargedOracleInput =>
      ((chargedParamOf v, v.2.1) : RawParamV2 × Nat.Partrec.Code) :=
    computable_chargedParamOf.pair hcode
  have hinit : Computable fun v : ChargedOracleInput =>
      rawInitialStateOfV2 (chargedParamOf v) :=
    computable_rawInitialStateOfV2.comp computable_chargedParamOf
  have h1 : Partrec fun x : (RawParamV2 × Nat.Partrec.Code) ×
      RawChargedStateV2 × List FamilyServerMove =>
        pfoldl chargedStepPartV2 x.1 x.2.1 x.2.2 :=
    partrec_pfoldl partrec_chargedStepPartV2
  exact (h1.comp (hw.pair (hinit.pair hhist))).of_eq fun _ => rfl

/-- Reading the final client move off a V2 charged state is partial recursive. -/
theorem partrec_chargedFinalPartV2 :
    Partrec fun z : (RawParamV2 × Nat.Partrec.Code) × RawChargedStateV2 =>
      chargedFinalPartV2 z.1 z.2 := by
  have hP : Computable fun z : (RawParamV2 × Nat.Partrec.Code) ×
      RawChargedStateV2 => z.1.1 := Computable.fst.comp Computable.fst
  have hcode : Computable fun z : (RawParamV2 × Nat.Partrec.Code) ×
      RawChargedStateV2 => z.1.2 := Computable.snd.comp Computable.fst
  have hstc : Computable fun z : (RawParamV2 × Nat.Partrec.Code) ×
      RawChargedStateV2 => z.2 := Computable.snd
  have hquery := computable_rawQueryOfV2.comp (hP.pair hstc)
  have horacle :=
    (partrec₂_codeEvalPart (β := FamilyClientMove)).comp (hcode.pair hquery)
  have hout : Computable₂ fun (z : (RawParamV2 × Nat.Partrec.Code) ×
      RawChargedStateV2) (cur : FamilyClientMove) =>
      rawOutputEncV2 z.1.1 z.2 cur :=
    (computable_rawOutputEncV2.comp
      ((hP.comp Computable.fst).pair
        ((hstc.comp Computable.fst).pair Computable.snd))).to₂
  exact horacle.map hout

/-- Reading the final client move off a V2 charged state is partial recursive in the input and
the state jointly. -/
theorem partrec₂_chargedFinalV2 :
    Partrec₂ fun (v : ChargedOracleInput) (stc : RawChargedStateV2) =>
      chargedFinalPartV2 (chargedParamOf v, v.2.1) stc := by
  have hw : Computable fun y : ChargedOracleInput × RawChargedStateV2 =>
      ((chargedParamOf y.1, y.1.2.1) : RawParamV2 × Nat.Partrec.Code) :=
    (computable_chargedParamOf.comp Computable.fst).pair
      (Computable.fst.comp (Computable.snd.comp Computable.fst))
  exact (partrec_chargedFinalPartV2.comp (hw.pair Computable.snd)).of_eq
    fun _ => rfl

/-- **The oracle-driven V2 charged controller is partial recursive.** -/
theorem partrec_chargedPhiV2 : Partrec chargedPhiV2 :=
  (partrec_chargedFoldV2.bind partrec₂_chargedFinalV2).of_eq fun _ => rfl

/-! ### Semantics -/

/-- **On a code that computes the previous scheme, the oracle controller
converges to the displayed V2 move.** -/
theorem chargedPhiV2_eq (q L : ℕ) (code : Nat.Partrec.Code)
    (sigma : FamilyStrategyScheme) (h : CodeComputesScheme code sigma)
    (p : SchemeInput) :
    chargedPhiV2 ((q, L), code, p) =
      Part.some (@encode FamilyClientMove Primcodable.toEncodable
        (grayChargedStrategyV2 q L p.1.1 p.1.2 sigma p.2.1 p.2.2.1 p.2.2.2)) := by
  obtain ⟨⟨a, e⟩, A, n, hist⟩ := p
  set b := grayTailBranch q L a e with hbdef
  set P : RawParamV2 := ((q, L, a, e), (n, b), A) with hPdef
  have hoc : ∀ x : SchemeInput,
      codeEvalPart (β := FamilyClientMove) code x
        = Part.some (sigma x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2) :=
    codeEvalPart_of_codeComputes h
  set cur : ℕ → RawStateV2 → FamilyClientMove := fun tag st =>
    sigma (rawChargedQueryV2 q L a e tag st).1.1
      (rawChargedQueryV2 q L a e tag st).1.2
      (rawChargedQueryV2 q L a e tag st).2.1
      (rawChargedQueryV2 q L a e tag st).2.2.1
      (rawChargedQueryV2 q L a e tag st).2.2.2 with hcurdef
  have hstep : ∀ (stc : RawChargedStateV2) (sm : FamilyServerMove),
      chargedStepPartV2 (P, code) stc sm =
        Part.some (rawChargedStepV2With q L a e n b A stc.1 stc.2 sm
          (cur stc.1 stc.2)) := by
    intro stc sm
    rw [chargedStepPartV2, hoc]
    rfl
  have hfold :
      pfoldl chargedStepPartV2 (P, code) (rawInitialStateOfV2 P) hist.2 =
        Part.some (hist.2.foldl
          (fun stc sm => rawChargedStepV2With q L a e n b A stc.1 stc.2 sm
            (cur stc.1 stc.2))
          (rawInitialStateOfV2 P)) :=
    pfoldl_eq_some_foldl hstep _ _
  change (pfoldl chargedStepPartV2 (P, code) (rawInitialStateOfV2 P) hist.2).bind
      (fun stc => chargedFinalPartV2 (P, code) stc) = _
  rw [hfold, Part.bind_some, chargedFinalPartV2, hoc]
  simp only [Part.map_some, Part.some_inj, rawOutputEncV2]
  refine congrArg _ ?_
  exact rawOutputOfV2_fold_eq q L a e n sigma A hist

end Kolmogorov
