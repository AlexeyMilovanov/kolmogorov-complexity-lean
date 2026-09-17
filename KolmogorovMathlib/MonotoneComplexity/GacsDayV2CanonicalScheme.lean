import KolmogorovMathlib.MonotoneComplexity.GacsDayV2TailStepLegal
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedCodeStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCode
import KolmogorovMathlib.MonotoneComplexity.GacsDayHalfAmplification
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwoComputable

/-!
# The canonical V2 ladder

This module supplies the canonical V2 ladder.  V2's
interface (`PinnedChargedRung`, `GacsDayV2Spec.lean`) is entirely
σ-parametric, so the pinned tail step `pinnedChargedRung_tail_step` can only be
iterated once a concrete sequence of schemes is named.  `canonicalGraySchemeV2`
is that sequence, and this file proves the two facts a ladder has to carry: the
semantic induction and joint computability in the stage.

## The ladder

`canonicalGraySchemeV2 σ₃ : UniformFamilyStrategyScheme` is defined by

* stages `q < 3`: the three proved low stages (`baseFamilyStrategy`, the
  half-step scheme, the stage-two scheme), spelled out here directly.  They are
  reused verbatim as *functions*; the ladder makes no semantic claim about them.
* stage `3`: the parameter `σ₃`.
* stages `q + 1` for `3 ≤ q`: the V2 block controller run over the previous
  stage,
  `fun a e => grayChargedStrategyV2 q (grayFootprint q) a e (canonicalGraySchemeV2 σ₃ q)`,
  i.e. exactly the conclusion shape of `pinnedChargedRung_tail_step`, with the
  frozen V2 footprint schedule `grayFootprint` as the loss budget.

## The base rung is a hypothesis here

The ladder is **parameterised by `σ₃`** on purpose.  The pinned ladder starts at
stage `3` (`PinnedChargedRung` carries `3 ≤ j` in every producer and consumer), so
everything here is stated *modulo* the hypotheses `h₃ : PinnedChargedRung 4 3 σ₃`
(semantics) and `hcode₃ : CodeComputesScheme code₃ σ₃` (computability); neither is
proved here.  Both are discharged for a concrete `σ₃` in `GacsDayV2BaseRung.lean`.

## The pinned-gap calling convention

`PinnedChargedRung eta j sigma` is Day-literal: the stage `j` is the only free
parameter and both depths are derived from the footprint schedule.  Concretely,
the scheme is evaluated **only** at the pinned gap

  `sigma a (a + 8 * grayFootprint (j - 1) + 3)`

(outer scale `a`, bin scale `e = a + 8·fp(j−1) + 3`), the export depth is
`a + grayFootprint j`, the amplification is `halfAmplification j`, the height is
`2 * j`, and the certificate is anchored at the call's outer scale `a`
(`epsDepth := a`, proof document v15.1 A2) rather than at `e`.  The ladder never
touches that convention: it only names the schemes, and the gap arithmetic is
consumed inside `pinnedChargedRung_tail_step`.

## Computability

The computability half mirrors the (now removed) V1 ladder's
`canonicalGrayScheme_computable` step by step, with the V1 tail transformer
`grayCharged_exists_code_step` replaced by its V2 twin
`grayChargedV2_exists_code_step` and the V1 loss schedule replaced by
`grayFootprint`:

* the *codes* are built by the same `Nat.rec` recursion as the schemes
  (`canonicalGrayCodeV2`), so no computable witness is inferred from semantic
  existence;
* that recursion is computable (`computable_canonicalGrayCodeV2`) because the
  V2 code transformer is computable and `grayFootprint` is primitive recursive
  (`primrec_grayFootprint`);
* each code really computes its stage (`canonicalGrayCodeV2_computesScheme`);
* the universal machine turns the computable code family into joint
  computability (`computable_of_codeFamily`), which is
  `UniformFamilyStrategySchemeComputable`.

Like the V1 code ladder, this one keeps the base codes and the
transformer as explicit parameters, so nothing in this file is
`noncomputable` and no choice is made outside the final theorems, where the
witnesses are obtained exactly as V1 obtains them.
-/

namespace Kolmogorov

open Encodable

/-! ## The ladder -/

/-- The canonical V2 strategy sequence: stage `0` is `baseFamilyStrategy a`, stage `1` is
`halfStepFamilyStrategy a (e + 3)`, stage `2` is `stageTwoFamilyStrategy a (e + 3)`, stage `3`
is the parameter `sigma3`, and stage `q + 4` is the V2 block controller `grayChargedStrategyV2
(q + 3) (grayFootprint (q + 3)) a e` run over stage `q + 3`. -/
def canonicalGraySchemeV2 (sigma3 : FamilyStrategyScheme) : UniformFamilyStrategyScheme
  | 0 => fun a _e => baseFamilyStrategy a
  | 1 => fun a e => halfStepFamilyStrategy a (e + 3)
  | 2 => fun a e => stageTwoFamilyStrategy a (e + 3)
  | 3 => sigma3
  | q + 4 => fun a e =>
      grayChargedStrategyV2 (q + 3) (grayFootprint (q + 3)) a e
        (canonicalGraySchemeV2 sigma3 (q + 3))

/-- Stage `0` of the ladder is the base family strategy. -/
@[simp] theorem canonicalGraySchemeV2_zero (sigma3 : FamilyStrategyScheme) :
    canonicalGraySchemeV2 sigma3 0 = fun a (_e : Nat) => baseFamilyStrategy a := rfl

/-- Stage `1` of the ladder is the half-step scheme, read at the gap `e + 3`. -/
@[simp] theorem canonicalGraySchemeV2_one (sigma3 : FamilyStrategyScheme) :
    canonicalGraySchemeV2 sigma3 1 = fun a e => halfStepFamilyStrategy a (e + 3) := rfl

/-- Stage `2` of the ladder is the stage-two scheme, read at the gap `e + 3`. -/
@[simp] theorem canonicalGraySchemeV2_two (sigma3 : FamilyStrategyScheme) :
    canonicalGraySchemeV2 sigma3 2 = fun a e => stageTwoFamilyStrategy a (e + 3) := rfl

/-- Stage `3` of the ladder is the scheme supplied as the parameter. -/
@[simp] theorem canonicalGraySchemeV2_three (sigma3 : FamilyStrategyScheme) :
    canonicalGraySchemeV2 sigma3 3 = sigma3 := rfl

/-- **The defining equation of the ladder on the pinned domain**: exactly the
conclusion shape of `pinnedChargedRung_tail_step`. -/
@[simp] theorem canonicalGraySchemeV2_succ (sigma3 : FamilyStrategyScheme) {q : Nat}
    (hq : 3 <= q) :
    canonicalGraySchemeV2 sigma3 (q + 1) =
      fun a e =>
        grayChargedStrategyV2 q (grayFootprint q) a e (canonicalGraySchemeV2 sigma3 q) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 := ⟨q - 3, by omega⟩
  rfl

/-! ## The semantic induction -/

/-- **The pinned ladder, semantic half.**  Given the (open) base rung at stage
`3`, every stage from `3` on carries the pinned charged rung.  The induction is
`pinnedChargedRung_tail_step` iterated along the defining equation of
`canonicalGraySchemeV2`; no other input is used. -/
theorem pinnedChargedRung_canonicalV2 (sigma3 : FamilyStrategyScheme)
    (h3 : PinnedChargedRung 4 3 sigma3) :
    ∀ q, 3 <= q → PinnedChargedRung 4 q (canonicalGraySchemeV2 sigma3 q) := by
  have key : ∀ r : Nat,
      PinnedChargedRung 4 (r + 3) (canonicalGraySchemeV2 sigma3 (r + 3)) := by
    intro r
    induction r with
    | zero => simpa using h3
    | succ r ih =>
        have hstep := pinnedChargedRung_tail_step (q := r + 3) (by omega) ih
        have hidx : r + 1 + 3 = (r + 3) + 1 := by omega
        rw [hidx, canonicalGraySchemeV2_succ sigma3 (by omega)]
        exact hstep
  intro q hq
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 := ⟨q - 3, by omega⟩
  exact key r

/-! ## Computability of the canonical V2 ladder

The code recursion is the exact code-level image of `canonicalGraySchemeV2`;
this is the V1 code recursion with the extra stage-`3` base slot and with
`grayFootprint` in place of the V1 loss schedule. -/

/-- The canonical V2 sequence of *codes*: the three V1 base codes, the base-rung
code at stage `3`, and from stage `3` on the V2 tail code step run with the
previous code as its oracle. -/
def canonicalGrayCodeV2 (c0 c1 c2 code3 : Nat.Partrec.Code)
    (G : Nat → Nat → Nat.Partrec.Code → Nat.Partrec.Code) : Nat → Nat.Partrec.Code :=
  fun n => Nat.rec (motive := fun _ => Nat.Partrec.Code) c0
    (fun k prev =>
      if k = 0 then c1 else if k = 1 then c2 else if k = 2 then code3
      else G k (grayFootprint k) prev) n

/-- The canonical code ladder starts with `c0` at stage `0`. -/
@[simp] theorem canonicalGrayCodeV2_zero (c0 c1 c2 code3 : Nat.Partrec.Code)
    (G : Nat → Nat → Nat.Partrec.Code → Nat.Partrec.Code) :
    canonicalGrayCodeV2 c0 c1 c2 code3 G 0 = c0 := rfl

/-- The canonical code ladder uses `c1` at stage `1`. -/
@[simp] theorem canonicalGrayCodeV2_one (c0 c1 c2 code3 : Nat.Partrec.Code)
    (G : Nat → Nat → Nat.Partrec.Code → Nat.Partrec.Code) :
    canonicalGrayCodeV2 c0 c1 c2 code3 G 1 = c1 := rfl

/-- The canonical code ladder uses `c2` at stage `2`. -/
@[simp] theorem canonicalGrayCodeV2_two (c0 c1 c2 code3 : Nat.Partrec.Code)
    (G : Nat → Nat → Nat.Partrec.Code → Nat.Partrec.Code) :
    canonicalGrayCodeV2 c0 c1 c2 code3 G 2 = c2 := rfl

/-- The canonical code ladder uses `code3` at stage `3`. -/
@[simp] theorem canonicalGrayCodeV2_three (c0 c1 c2 code3 : Nat.Partrec.Code)
    (G : Nat → Nat → Nat.Partrec.Code → Nat.Partrec.Code) :
    canonicalGrayCodeV2 c0 c1 c2 code3 G 3 = code3 := rfl

/-- **The defining equation of the V2 code recursion.**  From stage four on the
code of a stage is produced by the V2 tail code step from the code of the
previous stage, with exactly the parameters of `canonicalGraySchemeV2`. -/
theorem canonicalGrayCodeV2_add_four (c0 c1 c2 code3 : Nat.Partrec.Code)
    (G : Nat → Nat → Nat.Partrec.Code → Nat.Partrec.Code) (q : Nat) :
    canonicalGrayCodeV2 c0 c1 c2 code3 G (q + 4) =
      G (q + 3) (grayFootprint (q + 3)) (canonicalGrayCodeV2 c0 c1 c2 code3 G (q + 3)) := by
  simp only [canonicalGrayCodeV2]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The V2 code recursion is computable whenever the V2 tail code step is.  V1
twin: `computable_canonicalGrayCode`; the only new ingredients are the extra
constant branch at stage `3` and `primrec_grayFootprint` in place of the V1
loss schedule's primitive recursiveness. -/
theorem computable_canonicalGrayCodeV2 (c0 c1 c2 code3 : Nat.Partrec.Code)
    {G : Nat → Nat → Nat.Partrec.Code → Nat.Partrec.Code}
    (hG : Computable (fun p : (Nat × Nat) × Nat.Partrec.Code => G p.1.1 p.1.2 p.2)) :
    Computable (canonicalGrayCodeV2 c0 c1 c2 code3 G) := by
  have hfp : Computable grayFootprint := primrec_grayFootprint.to_comp
  have hstep : Computable₂ (fun (_ : Nat) (p : Nat × Nat.Partrec.Code) =>
      if p.1 = 0 then c1 else if p.1 = 1 then c2 else if p.1 = 2 then code3
      else G p.1 (grayFootprint p.1) p.2) := by
    have hGcomp : Computable (fun p : Nat × Nat.Partrec.Code =>
        G p.1 (grayFootprint p.1) p.2) :=
      hG.comp ((Computable.fst.pair (hfp.comp Computable.fst)).pair Computable.snd)
    have h0 : Computable (fun p : Nat × Nat.Partrec.Code => decide (p.1 = 0)) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp Computable.fst (Computable.const 0)
    have h1 : Computable (fun p : Nat × Nat.Partrec.Code => decide (p.1 = 1)) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp Computable.fst (Computable.const 1)
    have h2 : Computable (fun p : Nat × Nat.Partrec.Code => decide (p.1 = 2)) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp Computable.fst (Computable.const 2)
    have hite : Computable (fun p : Nat × Nat.Partrec.Code =>
        if p.1 = 0 then c1 else if p.1 = 1 then c2 else if p.1 = 2 then code3
        else G p.1 (grayFootprint p.1) p.2) := by
      refine (Computable.cond h0 (Computable.const c1)
        (Computable.cond h1 (Computable.const c2)
          (Computable.cond h2 (Computable.const code3) hGcomp))).of_eq (fun p => ?_)
      by_cases hp0 : p.1 = 0
      · simp [hp0]
      · by_cases hp1 : p.1 = 1
        · simp [hp1]
        · by_cases hp2 : p.1 = 2 <;> simp [hp0, hp1, hp2]
    exact hite.comp Computable.snd
  have h := Computable.nat_rec (f := fun k : Nat => k) (g := fun _ : Nat => c0)
    (h := fun (_ : Nat) (p : Nat × Nat.Partrec.Code) =>
      if p.1 = 0 then c1 else if p.1 = 1 then c2 else if p.1 = 2 then code3
      else G p.1 (grayFootprint p.1) p.2)
    Computable.id (Computable.const c0) hstep
  exact h

/-- Every canonical V2 code really computes the canonical V2 scheme of its
stage.  The four initial stages are the supplied base codes (three proved in V1,
the fourth the open base rung's code); the inductive step is the V2 tail code
step applied to the code of the previous stage, which is exactly the recursive
call performed by `canonicalGraySchemeV2`. -/
theorem canonicalGrayCodeV2_computesScheme {c0 c1 c2 code3 : Nat.Partrec.Code}
    {G : Nat → Nat → Nat.Partrec.Code → Nat.Partrec.Code}
    {sigma3 : FamilyStrategyScheme}
    (h0 : CodeComputesScheme c0 (fun a (_e : Nat) => baseFamilyStrategy a))
    (h1 : CodeComputesScheme c1 (fun a e => halfStepFamilyStrategy a (e + 3)))
    (h2 : CodeComputesScheme c2 (fun a e => stageTwoFamilyStrategy a (e + 3)))
    (h3 : CodeComputesScheme code3 sigma3)
    (hG : ∀ (q L : Nat) (code : Nat.Partrec.Code) (sigma : FamilyStrategyScheme),
      CodeComputesScheme code sigma →
        CodeComputesScheme (G q L code) (fun a e => grayChargedStrategyV2 q L a e sigma))
    (k : Nat) :
    CodeComputesScheme (canonicalGrayCodeV2 c0 c1 c2 code3 G k)
      (canonicalGraySchemeV2 sigma3 k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2
    | 3 => exact h3
    | (q + 4) =>
        rw [canonicalGrayCodeV2_add_four,
          canonicalGraySchemeV2_succ sigma3 (q := q + 3) (by omega)]
        exact hG (q + 3) (grayFootprint (q + 3)) _ _ (ih (q + 3) (by omega))

/-- **The canonical V2 ladder is uniformly computable.**  The concrete V2
controller recursion, including its recursive calls to the previous canonical V2
code, is computable jointly in the stage, the two dyadic depths, the unavailable
allocation, the family size and the history — given a code for the base rung
`sigma3`.

This mirrors the V1 ladder's computability proof line for line: the three
base codes exist outright, the V2 tail code transformer is
`grayChargedV2_exists_code_step`, the code family is computable by
`computable_canonicalGrayCodeV2`, and the universal machine
(`computable_of_codeFamily`) turns it into joint computability. -/
theorem canonicalGraySchemeV2_computable (sigma3 : FamilyStrategyScheme)
    (code3 : Nat.Partrec.Code) (hcode3 : CodeComputesScheme code3 sigma3) :
    UniformFamilyStrategySchemeComputable (canonicalGraySchemeV2 sigma3) := by
  obtain ⟨c0, h0⟩ := exists_code_baseFamilyScheme
  obtain ⟨c1, h1⟩ :=
    exists_code_of_familyStrategySchemeComputable computable_halfStepFamilyScheme
  obtain ⟨c2, h2⟩ :=
    exists_code_of_familyStrategySchemeComputable computable_stageTwoFamilyScheme
  obtain ⟨G, hGcomp, hG⟩ := grayChargedV2_exists_code_step
  have hcodes := canonicalGrayCodeV2_computesScheme h0 h1 h2 hcode3 hG
  have hcomp := computable_canonicalGrayCodeV2 c0 c1 c2 code3 hGcomp
  have hjoint : Computable (fun p : Nat × SchemeInput =>
      canonicalGraySchemeV2 sigma3 p.1 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
    computable_of_codeFamily (canonicalGrayCodeV2 c0 c1 c2 code3 G) hcomp
      (fun k (p : SchemeInput) =>
        canonicalGraySchemeV2 sigma3 k p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)
      hcodes
  have hreshuffle : Computable
      (fun q : (Nat × Nat × Nat) × (Allocation × (Nat × FamilyGameHistory)) =>
        ((q.1.1, ((q.1.2.1, q.1.2.2), q.2)) : Nat × SchemeInput)) :=
    (Computable.fst.comp Computable.fst).pair
      (((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair Computable.snd)
  have hfinal := hjoint.comp hreshuffle
  exact hfinal

/-- The same statement with the base rung given by computability rather than by
a code; the code is produced by `exists_code_of_familyStrategySchemeComputable`,
exactly as V1 does for its stage-one and stage-two bases. -/
theorem canonicalGraySchemeV2_computable_of_base {sigma3 : FamilyStrategyScheme}
    (hsigma3 : FamilyStrategySchemeComputable sigma3) :
    UniformFamilyStrategySchemeComputable (canonicalGraySchemeV2 sigma3) := by
  obtain ⟨code3, hcode3⟩ := exists_code_of_familyStrategySchemeComputable hsigma3
  exact canonicalGraySchemeV2_computable sigma3 code3 hcode3

end Kolmogorov
