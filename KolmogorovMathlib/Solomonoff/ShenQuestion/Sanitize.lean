/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasureEnumeration
import KolmogorovMathlib.Solomonoff.ShenQuestion.Statement

/-!
# Sanitized conditional stages `Q̂` (blueprint A1.2 / B1 "sanitize in A3.3")

From the raw `IsLSC` numerators `qa s y u` of a conditional continuous semimeasure `Q`
we build, for each condition `u`, the *sanitized* stage numerators

  `qHat qa u t y  :  ℕ`,  representing  `Q̂_t(y | u) = qHat qa u t y / 2 ^ t`.

The sanitizer is the library's `simpleApprox` applied to the section
`fun s y _ => qa s y u` (the library's `simpleApprox` reads its argument only at the
context `[]`, so this is exactly "sanitize `Q(· | u)`").  The resulting stages are
genuine finite dyadic semimeasures in `y`:

* root value exactly `2 ^ t`  (i.e. `Q̂_t([] | u) = 1`),
* support in `|y| ≤ t`,
* children sum `≤` parent,
* dyadically monotone in `t`, with supremum `Q(y | u)`.

These five facts are exactly the interface `A1.2` of the blueprint; the construction of
`ν` uses nothing else about `Q`.
-/

namespace Kolmogorov
namespace Shen

open scoped ENNReal

variable {Q : BitString → BitString → ℝ≥0∞}

/-- Sanitized conditional stage numerator: `Q̂_t(y | u) = qHat qa u t y / 2 ^ t`. -/
def qHat (qa : ℕ → BitString → BitString → ℕ) (u : BitString) (t : ℕ) (y : BitString) : ℕ :=
  simpleApprox (fun s y' _ => qa s y' u) t y

/-- **A1.2 (root).** `Q̂_t([] | u) = 1`.  Difficulty **E**. -/
@[simp] theorem qHat_root (qa : ℕ → BitString → BitString → ℕ) (u : BitString) (t : ℕ) :
    qHat qa u t [] = 2 ^ t :=
  simpleApprox_root _ t

/-- **A1.2 (finite support).** `Q̂_t(y | u) = 0` for `|y| > t`; this is what makes each
stage a *finite* semimeasure and what makes the transition level `D` well defined.
Difficulty **E**. -/
theorem qHat_vanishes (qa : ℕ → BitString → BitString → ℕ) (u : BitString) (t : ℕ)
    (y : BitString) (h : t < y.length) : qHat qa u t y = 0 :=
  simpleApprox_vanishes_below_frontier _ t y h

/-- **A1.2 (coherence).** Each stage is a semimeasure in `y`.  Difficulty **E**
(library `simpleApprox_coherent` at the section `Q(· | u)`). -/
theorem qHat_coherent (hQ : IsConditionalContinuousTreeSemimeasure Q)
    {qa : ℕ → BitString → BitString → ℕ}
    (hsup : ∀ y u, ⨆ s, dyadicValue (qa s y u) s = Q y u)
    (u : BitString) (t : ℕ) (y : BitString) :
    qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y :=
  simpleApprox_coherent (fun y => Q y u) _ (fun out _ => hsup out u) (hQ u) t y

/-- **A1.2 (stage monotonicity).**  Difficulty **E**. -/
theorem qHat_stage_mono {qa : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s y u, dyadicValue (qa s y u) s ≤ dyadicValue (qa (s + 1) y u) (s + 1))
    (u : BitString) (t : ℕ) (y : BitString) :
    dyadicValue (qHat qa u t y) t ≤ dyadicValue (qHat qa u (t + 1) y) (t + 1) :=
  simpleApprox_stage_mono _ (fun s out _ => hmono s out u) t y

/-- **A1.2 (convergence).** `⨆_t Q̂_t(y | u) = Q(y | u)`.  Difficulty **E**. -/
theorem qHat_iSup (hQ : IsConditionalContinuousTreeSemimeasure Q)
    {qa : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s y u, dyadicValue (qa s y u) s ≤ dyadicValue (qa (s + 1) y u) (s + 1))
    (hsup : ∀ y u, ⨆ s, dyadicValue (qa s y u) s = Q y u)
    (u : BitString) (y : BitString) :
    ⨆ t, dyadicValue (qHat qa u t y) t = Q y u :=
  iSup_simpleApprox_eq (fun y => Q y u) _ (fun s out _ => hmono s out u)
    (fun out _ => hsup out u) (hQ u) y

/-! ### Uniform computability of `qHat`

The library's `computable_simpleApprox` is stated for a *fixed* approximation family, so
it cannot be applied uniformly in the condition `u` (the third argument of the family is
read only at `[]`, so `u` cannot be smuggled through it).  We therefore repeat the
library's parameter-code proof, with the condition `u` added to the code. -/

section QHatComputable

open Encodable

attribute [local irreducible] simpleApproxBits levelStep closureLevel simpleApprox

private lemma computable_range_map' {α β : Type*} [Primcodable α] [Primcodable β]
    (n : α → ℕ) (g : α → ℕ → β) (hn : Computable n)
    (hg : Computable (fun q : α × ℕ => g q.1 q.2)) :
    Computable (fun a => (List.range (n a)).map (g a)) := by
  have hstep : Computable₂ (fun (a : α) (q : ℕ × List β) => q.2 ++ [g a q.1]) := by
    have hg' : Computable (fun q : α × (ℕ × List β) => g q.1 q.2.1) :=
      hg.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
    exact (Computable.list_concat.comp (Computable.snd.comp Computable.snd) hg').to₂
  exact (Computable.nat_rec hn (Computable.const []) hstep).of_eq fun a => by
    induction n a with
    | zero => rfl
    | succ n ih => simp [List.range_succ, ih]

/-- Code for the parameter quadruple `(s, k, x, u)`. -/
private def uCode (s k : ℕ) (x u : BitString) : ℕ :=
  Nat.pair (Nat.pair s k) (Nat.pair (encode x) (encode u))

private def uS (c : ℕ) : ℕ := (Nat.unpair (Nat.unpair c).1).1
private def uK (c : ℕ) : ℕ := (Nat.unpair (Nat.unpair c).1).2
private def uX (c : ℕ) : BitString :=
  (decode (α := BitString) (Nat.unpair (Nat.unpair c).2).1).getD []
private def uU (c : ℕ) : BitString :=
  (decode (α := BitString) (Nat.unpair (Nat.unpair c).2).2).getD []
private def uRecode (c k : ℕ) : ℕ := Nat.pair (Nat.pair (uS c) k) (Nat.unpair c).2

@[simp] private lemma uS_code (s k : ℕ) (x u : BitString) : uS (uCode s k x u) = s := by
  simp [uS, uCode]
@[simp] private lemma uK_code (s k : ℕ) (x u : BitString) : uK (uCode s k x u) = k := by
  simp [uK, uCode]
@[simp] private lemma uX_code (s k : ℕ) (x u : BitString) : uX (uCode s k x u) = x := by
  simp [uX, uCode]
@[simp] private lemma uU_code (s k : ℕ) (x u : BitString) : uU (uCode s k x u) = u := by
  simp [uU, uCode]
@[simp] private lemma uS_recode (c k : ℕ) : uS (uRecode c k) = uS c := by
  simp [uS, uRecode]
@[simp] private lemma uK_recode (c k : ℕ) : uK (uRecode c k) = k := by
  simp [uK, uRecode]
@[simp] private lemma uX_recode (c k : ℕ) : uX (uRecode c k) = uX c := by
  simp [uX, uRecode]
@[simp] private lemma uU_recode (c k : ℕ) : uU (uRecode c k) = uU c := by
  simp [uU, uRecode]

private lemma computable_uS : Computable uS :=
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).to_comp
private lemma computable_uK : Computable uK :=
  (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).to_comp
private lemma computable_uX : Computable uX :=
  Computable.option_getD
    (Computable.decode.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp)
    (Computable.const [])
private lemma computable_uU : Computable uU :=
  Computable.option_getD
    (Computable.decode.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp)
    (Computable.const [])
private lemma computable_uRecode : Computable (fun p : ℕ × ℕ => uRecode p.1 p.2) :=
  Primrec₂.natPair.to_comp.comp
    (Primrec₂.natPair.to_comp.comp (computable_uS.comp Computable.fst) Computable.snd)
    ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst)
private lemma computable_uCode :
    Computable (fun q : (ℕ × ℕ) × BitString × BitString => uCode q.1.1 q.1.2 q.2.1 q.2.2) :=
  Primrec₂.natPair.to_comp.comp
    (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst))
    (Primrec₂.natPair.to_comp.comp
      (Primrec.encode.to_comp.comp (Computable.fst.comp Computable.snd))
      (Primrec.encode.to_comp.comp (Computable.snd.comp Computable.snd)))

attribute [local irreducible] uS uK uX uU uRecode uCode

private lemma computable_levelStepU {qa : ℕ → BitString → BitString → ℕ}
    (hcomp : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2)) :
    Computable (fun q : ℕ × List ℕ =>
      levelStep (fun s y' _ => qa s y' (uU q.1)) (uS q.1) (uX q.1) (uK q.1) q.2) := by
  have hc : Computable (fun p : (ℕ × List ℕ) × ℕ => p.1.1) := Computable.fst.comp Computable.fst
  have hprev : Computable (fun p : (ℕ × List ℕ) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hi : Computable (fun p : (ℕ × List ℕ) × ℕ => p.2) := Computable.snd
  have hmain : Computable (fun q : ℕ × List ℕ =>
      (List.range (2 ^ uK q.1)).map (fun i =>
        max (qa (uS q.1) (uX q.1 ++ simpleApproxBits (uK q.1) i) (uU q.1))
          (q.2.getD (2 * i) 0 + q.2.getD (2 * i + 1) 0))) := by
    refine computable_range_map' _ _ ?_ ?_
    · exact primrec_two_pow_aux.to_comp.comp (computable_uK.comp Computable.fst)
    · have hbi : Computable (fun p : (ℕ × List ℕ) × ℕ =>
          simpleApproxBits (uK p.1.1) p.2) :=
        computable_simpleApproxBits.comp (Computable.pair (computable_uK.comp hc) hi)
      have happrox : Computable (fun p : (ℕ × List ℕ) × ℕ =>
          qa (uS p.1.1) (uX p.1.1 ++ simpleApproxBits (uK p.1.1) p.2) (uU p.1.1)) :=
        hcomp.comp (Computable.pair (computable_uS.comp hc)
          (Computable.pair
            (Computable.list_append.comp (computable_uX.comp hc) hbi)
            (computable_uU.comp hc)))
      have h2i : Computable (fun p : (ℕ × List ℕ) × ℕ => 2 * p.2) :=
        Primrec.nat_mul.to_comp.comp (Computable.const 2) hi
      have hgetD : Computable₂ (fun (l : List ℕ) (n : ℕ) => l.getD n 0) :=
        (Primrec.list_getD (0 : ℕ)).to_comp
      have hsum : Computable (fun p : (ℕ × List ℕ) × ℕ =>
          p.1.2.getD (2 * p.2) 0 + p.1.2.getD (2 * p.2 + 1) 0) :=
        Primrec.nat_add.to_comp.comp (hgetD.comp hprev h2i)
          (hgetD.comp hprev (Computable.succ.comp h2i))
      exact Primrec.nat_max.to_comp.comp happrox hsum
  exact hmain.of_eq (fun q => by rw [levelStep])

private lemma computable_closureLevelU {qa : ℕ → BitString → BitString → ℕ}
    (hcomp : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2)) :
    Computable (fun a : ℕ × ℕ =>
      closureLevel (fun s y' _ => qa s y' (uU a.1)) (uS a.1) (uX a.1) (uK a.1) a.2) := by
  have hstepC := computable_levelStepU hcomp
  have hbase : Computable (fun a : ℕ × ℕ =>
      levelStep (fun s y' _ => qa s y' (uU a.1)) (uS a.1) (uX a.1) (uK a.1) []) :=
    hstepC.comp (Computable.pair Computable.fst (Computable.const []))
  have hstep : Computable (fun q : (ℕ × ℕ) × (ℕ × List ℕ) =>
      levelStep (fun s y' _ => qa s y' (uU q.1.1)) (uS q.1.1) (uX q.1.1)
        (uK q.1.1 - (q.2.1 + 1)) q.2.2) := by
    have hcode : Computable (fun q : (ℕ × ℕ) × (ℕ × List ℕ) =>
        uRecode q.1.1 (uK q.1.1 - (q.2.1 + 1))) :=
      computable_uRecode.comp (Computable.pair
        (Computable.fst.comp Computable.fst)
        (Primrec.nat_sub.to_comp.comp
          (computable_uK.comp (Computable.fst.comp Computable.fst))
          (Computable.succ.comp (Computable.fst.comp Computable.snd))))
    exact (hstepC.comp (Computable.pair hcode
      (Computable.snd.comp Computable.snd))).of_eq (fun q => by simp)
  exact (Computable.nat_rec Computable.snd hbase hstep.to₂).of_eq
    (fun a => (closureLevel_rec _ (uS a.1) (uX a.1) (uK a.1) a.2).symm)

/-- **A1.2 (uniform effectivity).**  `Q̂` is computable *uniformly in the condition*.

Proof sketch: encode the condition `u : BitString` by `Encodable.encode u : ℕ` and apply
`computable_simpleApprox_uniform` to the ℕ-indexed family
`b i s y c := qa s y ((Encodable.decode i).getD [])`; that family is computable because
`Encodable.decode` on `BitString` is computable (`Computable.decode`) together with
`hcomp`.  Then compose with `Computable.encode`.  Difficulty **M**, ~40 lines. -/
theorem qHat_computable {qa : ℕ → BitString → BitString → ℕ}
    (hcomp : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString × BitString => qHat qa p.2.2 p.1 p.2.1) := by
  have hlen : Computable (fun p : ℕ × BitString × BitString => p.2.1.length) :=
    Computable.list_length.comp (Computable.fst.comp Computable.snd)
  have hd : Computable (fun p : ℕ × BitString × BitString => p.1 - p.2.1.length) :=
    Primrec.nat_sub.to_comp.comp Computable.fst hlen
  have hcode : Computable (fun p : ℕ × BitString × BitString =>
      uCode p.1 (p.1 - p.2.1.length) p.2.1 p.2.2) :=
    computable_uCode.comp (Computable.pair (Computable.pair Computable.fst hd)
      (Computable.pair (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)))
  have hlevel : Computable (fun p : ℕ × BitString × BitString =>
      closureLevel (fun s y' _ => qa s y' p.2.2) p.1 p.2.1
        (p.1 - p.2.1.length) (p.1 - p.2.1.length)) :=
    ((computable_closureLevelU hcomp).comp (Computable.pair hcode hd)).of_eq (fun p => by simp)
  have hval : Computable (fun p : ℕ × BitString × BitString =>
      (closureLevel (fun s y' _ => qa s y' p.2.2) p.1 p.2.1
        (p.1 - p.2.1.length) (p.1 - p.2.1.length)).getD 0 0) :=
    (Primrec.list_getD (0 : ℕ)).to_comp.comp hlevel (Computable.const 0)
  have hc1 : Computable (fun p : ℕ × BitString × BitString =>
      decide (p.1 < p.2.1.length)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp Computable.fst hlen
  have hc2 : Computable (fun p : ℕ × BitString × BitString =>
      decide (p.2.1.length = 0)) :=
    (PrimrecRel.decide (Primrec.eq (α := ℕ))).to_comp.comp hlen (Computable.const 0)
  have hpow : Computable (fun p : ℕ × BitString × BitString => 2 ^ p.1) :=
    primrec_two_pow_aux.to_comp.comp Computable.fst
  refine (Computable.cond hc1 (Computable.const 0)
    (Computable.cond hc2 hpow hval)).of_eq (fun p => ?_)
  rw [qHat]
  exact (simpleApprox_eq_cond (fun s y' _ => qa s y' p.2.2) p.1 p.2.1).symm

end QHatComputable

end Shen
end Kolmogorov
