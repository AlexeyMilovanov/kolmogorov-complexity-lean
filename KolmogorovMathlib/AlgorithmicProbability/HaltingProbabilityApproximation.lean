/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals

/-!
# Halting probabilities and lower semicomputable reals

Every lower semicomputable real in `[0, 1]` is the halting probability of a prefix
decompressor (`haltingProbability_of_isLowerSemicomputable`,
`semimeasure_realization`), and a real is computable exactly when both
it and its negation are lower semicomputable (`isComputableReal_iff_lowerSemicomputable_and_neg`).
Also included is the characterisation of lower semicomputable *sequences* by enumerability
of the set of rational pairs below them
(`lowerSemicomputableSeq_iff_enumerable_rationalPairs`).

SUV Theorem 46, p. 108.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)

open Kolmogorov.ComputableReals

private def ratLtBool (p : ℚ × ℚ) : Bool := decide (p.1 < p.2)

private theorem ratLtBool_computable : Computable ratLtBool :=
  (PrimrecRel.decide primrec_ratLt).to_comp

attribute [irreducible] ratLtBool

private theorem stageRat_computable : Computable (fun p : (ℚ × ℕ) × ℕ => p.1.1) :=
  Computable.fst.comp Computable.fst

private theorem stagePair_computable :
    Computable (fun p : ℚ × ((ℚ × ℕ) × ℕ) => (p.2.1.1, p.1)) :=
  (stageRat_computable.comp Computable.snd).pair Computable.fst

private theorem stageRatLt_computable :
    Computable (fun p : ℚ × ((ℚ × ℕ) × ℕ) => ratLtBool (p.2.1.1, p.1)) :=
  ratLtBool_computable.comp stagePair_computable

private def condRatLt (p : ℚ × ((ℚ × ℕ) × ℕ)) : Option Unit :=
  cond (ratLtBool (p.2.1.1, p.1)) (some ()) none

attribute [irreducible] condRatLt

private theorem condRatLt_computable : Computable condRatLt := by
  have h := Computable.cond stageRatLt_computable (Computable.const (some ()))
    (Computable.const none)
  exact h.of_eq (fun p => by unfold condRatLt; rfl)

private def chkStep (f : ℕ → ℕ → Option ℚ) (p : (ℚ × ℕ) × ℕ) : Option Unit :=
  (f p.1.2 p.2).bind (fun q => condRatLt (q, p))

attribute [irreducible] chkStep

private theorem chkStep_computable (f : ℕ → ℕ → Option ℚ)
    (hf : Computable (fun z : ℕ × ℕ => f z.1 z.2)) :
    Computable (chkStep f) := by
  have h_f : Computable (fun p : (ℚ × ℕ) × ℕ => f p.1.2 p.2) :=
    hf.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)
  have h_cond2 : Computable₂ (fun (p : (ℚ × ℕ) × ℕ) (q : ℚ) => condRatLt (q, p)) :=
    condRatLt_computable.comp (Computable.snd.pair Computable.fst) |>.to₂
  have h_bind : Computable (fun p : (ℚ × ℕ) × ℕ =>
      (f p.1.2 p.2).bind (fun q => condRatLt (q, p))) :=
    Computable.option_bind h_f h_cond2
  exact h_bind.of_eq (fun p => by
    unfold chkStep condRatLt ratLtBool
    rfl)

private def chkIsSome (f : ℕ → ℕ → Option ℚ) (p : (ℚ × ℕ) × ℕ) : Bool :=
  (chkStep f p).isSome

attribute [irreducible] chkIsSome

private theorem chkIsSome_computable (f : ℕ → ℕ → Option ℚ)
    (hf : Computable (fun z : ℕ × ℕ => f z.1 z.2)) :
    Computable (chkIsSome f) := by
  have h_step : Computable (chkStep f) := chkStep_computable f hf
  have h_isSome : Computable (fun o : Option Unit => o.isSome) :=
    Primrec.to_comp Primrec.option_isSome
  exact (h_isSome.comp h_step).of_eq (fun p => by
    unfold chkIsSome
    rfl)

private def encRatNat (p : ℚ × ℕ) : ℕ :=
  @Encodable.encode (ℚ × ℕ) Primcodable.toEncodable p

private lemma encRatNat_eq (p : ℚ × ℕ) :
    @Encodable.encode (ℚ × ℕ) Primcodable.toEncodable p = encRatNat p := rfl

private theorem encRatNat_primrec : Primrec encRatNat :=
  Primrec.of_eq Primrec.encode encRatNat_eq

private theorem encRatNat_computable : Computable encRatNat := encRatNat_primrec.to_comp

attribute [irreducible] encRatNat

private def f0 (c : Code) (i n : ℕ) : Option ℚ :=
  let r_idx := n.unpair.1
  let fuel := n.unpair.2
  let r := Denumerable.ofNat ℚ r_idx
  cond (Code.evaln fuel c (encRatNat (r, i))).isSome (some r) none

private lemma f0_def (c : Code) (i n : ℕ) :
    f0 c i n = cond (Code.evaln n.unpair.2 c
      (encRatNat (Denumerable.ofNat ℚ n.unpair.1, i))).isSome
      (some (Denumerable.ofNat ℚ n.unpair.1)) none := rfl

attribute [irreducible] f0

private theorem f0_computable (c : Code) :
    Computable (fun z : ℕ × ℕ => f0 c z.1 z.2) := by
  have h_r : Computable (fun p : ℕ × ℕ => Denumerable.ofNat ℚ p.2.unpair.1) :=
    (Computable.ofNat ℚ).comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have h_enc : Computable (fun p : ℕ × ℕ =>
      encRatNat (Denumerable.ofNat ℚ p.2.unpair.1, p.1)) :=
    encRatNat_computable.comp (h_r.pair Computable.fst)
  have h_fuel : Computable (fun p : ℕ × ℕ => p.2.unpair.2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  have h_eval : Computable (fun p : ℕ × ℕ =>
      Code.evaln p.2.unpair.2 c (encRatNat (Denumerable.ofNat ℚ p.2.unpair.1, p.1))) :=
    (evaln_fixed_computable c).comp (h_fuel.pair h_enc)
  have h_isSome : Computable (fun p : ℕ × ℕ =>
      (Code.evaln p.2.unpair.2 c
        (encRatNat (Denumerable.ofNat ℚ p.2.unpair.1, p.1))).isSome) :=
    (Primrec.to_comp Primrec.option_isSome).comp h_eval
  exact (Computable.cond h_isSome (Computable.option_some.comp h_r)
    (Computable.const none)).of_eq (fun p => by
    unfold f0 encRatNat
    rfl)

private def maxRat (p : ℚ × ℚ) : ℚ := max p.1 p.2

private theorem maxRat_computable : Computable maxRat := primrec_ratMax.to_comp

attribute [irreducible] maxRat

private def maxVal (p : ℚ × Option ℚ) : ℚ :=
  (p.2.map (fun q2 => maxRat (p.1, q2))).getD p.1

private theorem maxVal_computable : Computable maxVal := by
  have h_q1 : Computable (fun p : ℚ × Option ℚ => p.1) := Computable.fst
  have h_t : Computable (fun p : ℚ × Option ℚ => p.2) := Computable.snd
  have h_max_arg : Computable (fun p : (ℚ × Option ℚ) × ℚ => (p.1.1, p.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have h_max_call : Computable₂ (fun (p : ℚ × Option ℚ) (q2 : ℚ) => maxRat (p.1, q2)) :=
    (maxRat_computable.comp h_max_arg).to₂
  have h_map : Computable (fun p : ℚ × Option ℚ => p.2.map (fun q2 => maxRat (p.1, q2))) :=
    Computable.option_map h_t h_max_call
  have h_getD : Computable (fun p : Option ℚ × ℚ => p.1.getD p.2) :=
    (Primrec.option_getD.comp Primrec.fst Primrec.snd).to_comp
  exact (h_getD.comp (h_map.pair h_q1)).of_eq (fun p => by unfold maxVal; rfl)

attribute [irreducible] maxVal

private def someMaxVal (p : (Option ℚ × Option ℚ) × ℚ) : Option ℚ :=
  some (maxVal (p.2, p.1.2))

private theorem someMaxVal_computable : Computable someMaxVal := by
  have h_arg : Computable (fun p : (Option ℚ × Option ℚ) × ℚ => (p.2, p.1.2)) :=
    Computable.snd.pair (Computable.snd.comp Computable.fst)
  have h_val := maxVal_computable.comp h_arg
  exact (Computable.option_some.comp h_val).of_eq (fun p => by unfold someMaxVal; rfl)

attribute [irreducible] someMaxVal

private def combineOpt (acc : Option ℚ) (t : Option ℚ) : Option ℚ :=
  Option.casesOn acc t (fun q1 => someMaxVal ((acc, t), q1))

private theorem combineOpt_computable :
    Computable (fun p : Option ℚ × Option ℚ => combineOpt p.1 p.2) := by
  have h_acc : Computable (fun p : Option ℚ × Option ℚ => p.1) := Computable.fst
  have h_t : Computable (fun p : Option ℚ × Option ℚ => p.2) := Computable.snd
  have h_call : Computable₂ (fun (p : Option ℚ × Option ℚ) (q1 : ℚ) =>
      someMaxVal (p, q1)) :=
    someMaxVal_computable.to₂
  have h := Computable.option_casesOn h_acc h_t h_call
  exact h.of_eq (fun p => by unfold combineOpt; rfl)

attribute [irreducible] combineOpt

private def runSeqRec (c : Code) (i n : ℕ) : Option ℚ :=
  Nat.rec (combineOpt none (f0 c i 0)) (fun k acc => combineOpt acc (f0 c i (k + 1))) n

private theorem runSeqRec_computable (c : Code) :
    Computable (fun z : ℕ × ℕ => runSeqRec c z.1 z.2) := by
  have h_f0 := f0_computable c
  have h_f0_zero : Computable (fun p : ℕ × ℕ => f0 c p.1 0) :=
    h_f0.comp (Computable.fst.pair (Computable.const 0))
  have h_init : Computable (fun p : ℕ × ℕ => combineOpt none (f0 c p.1 0)) :=
    combineOpt_computable.comp ((Computable.const none).pair h_f0_zero)
  have h_step_f0_arg :
      Computable (fun p : (ℕ × ℕ) × (ℕ × Option ℚ) => (p.1.1, p.2.1 + 1)) :=
    (Computable.fst.comp Computable.fst).pair
      (Computable.succ.comp (Computable.fst.comp Computable.snd))
  have h_step_f0_call :
      Computable (fun p : (ℕ × ℕ) × (ℕ × Option ℚ) => f0 c p.1.1 (p.2.1 + 1)) :=
    h_f0.comp h_step_f0_arg
  have h_step_acc : Computable (fun p : (ℕ × ℕ) × (ℕ × Option ℚ) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have h_step_call : Computable₂ (fun (z : ℕ × ℕ) (p : ℕ × Option ℚ) =>
      combineOpt p.2 (f0 c z.1 (p.1 + 1))) :=
    (combineOpt_computable.comp (h_step_acc.pair h_step_f0_call)).to₂
  have h_rec := Computable.nat_rec Computable.snd h_init h_step_call
  exact h_rec.of_eq (fun z => by
    unfold runSeqRec
    rfl)

private def runSeq (c : Code) (i n : ℕ) : Option ℚ := runSeqRec c i n

private lemma runSeq_zero (c : Code) (i : ℕ) :
    runSeq c i 0 = combineOpt none (f0 c i 0) := by
  change runSeqRec c i 0 = _
  rfl

private lemma runSeq_succ (c : Code) (i n : ℕ) :
    runSeq c i (n + 1) = combineOpt (runSeq c i n) (f0 c i (n + 1)) := by
  change runSeqRec c i (n + 1) = _
  rfl

private theorem runSeq_computable (c : Code) :
    Computable (fun z : ℕ × ℕ => runSeq c z.1 z.2) :=
  runSeqRec_computable c

attribute [irreducible] runSeq

private theorem combineOpt_mono (acc : Option ℚ) (t : Option ℚ) (q : ℚ) (hq : q ∈ acc) :
    ∃ q' ∈ combineOpt acc t, q ≤ q' := by
  rw [Option.mem_def] at hq
  subst hq
  unfold combineOpt someMaxVal maxVal maxRat
  cases t with
  | none =>
    refine ⟨q, rfl, le_refl q⟩
  | some q2 =>
    refine ⟨max q q2, rfl, le_max_left q q2⟩

private theorem combineOpt_mono_right (acc : Option ℚ) (t : Option ℚ) (q : ℚ) (hq : q ∈ t) :
    ∃ q' ∈ combineOpt acc t, q ≤ q' := by
  rw [Option.mem_def] at hq
  subst hq
  unfold combineOpt someMaxVal maxVal maxRat
  cases acc with
  | none =>
    refine ⟨q, rfl, le_refl q⟩
  | some q1 =>
    refine ⟨max q1 q, rfl, le_max_right q1 q⟩

private theorem runSeq_mono (c : Code) (i n : ℕ) (q : ℚ) (hq : q ∈ runSeq c i n) :
    ∃ q' ∈ runSeq c i (n + 1), q ≤ q' := by
  rw [runSeq_succ]
  exact combineOpt_mono (runSeq c i n) (f0 c i (n + 1)) q hq

private theorem f0_lt (c : Code) (p : ℕ → ℝ) (g : ℚ × ℕ →. Unit)
    (hc : c.eval = fun n =>
      (Part.ofOption (@Encodable.decode (ℚ × ℕ) Primcodable.toEncodable n)).bind
        (fun a => Part.map Encodable.encode (g a)))
    (hg_dom : ∀ ri, (g ri).Dom ↔ (ri.1 : ℝ) < p ri.2)
    (i n : ℕ) (r : ℚ) (hr : r ∈ f0 c i n) : (r : ℝ) < p i := by
  rw [f0_def] at hr
  generalize h_eval : Code.evaln n.unpair.2 c
    (encRatNat (Denumerable.ofNat ℚ n.unpair.1, i)) = res at hr
  cases res with
  | none =>
    dsimp at hr
    contradiction
  | some res_val =>
    dsimp at hr
    have hr_eq : r = Denumerable.ofNat ℚ n.unpair.1 := Option.some.inj hr.symm
    subst hr_eq
    have h_eval_sound := Nat.Partrec.Code.evaln_sound h_eval
    rw [hc] at h_eval_sound
    rw [Part.mem_bind_iff] at h_eval_sound
    obtain ⟨a, ha_dec, ha_map⟩ := h_eval_sound
    have h_pair_eq : encRatNat (Denumerable.ofNat ℚ n.unpair.1, i) =
        @Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (Denumerable.ofNat ℚ n.unpair.1, i) :=
      (encRatNat_eq _).symm
    rw [h_pair_eq] at ha_dec
    rw [Part.mem_ofOption] at ha_dec
    have ha_eq : a = (Denumerable.ofNat ℚ n.unpair.1, i) := by
      generalize h_target : (Denumerable.ofNat ℚ n.unpair.1, i) = target at ha_dec
      have hdec := @Encodable.encodek (ℚ × ℕ) Primcodable.toEncodable target
      rw [ha_dec] at hdec
      exact Option.some.inj hdec
    subst ha_eq
    rw [Part.mem_map_iff] at ha_map
    obtain ⟨u, hu_g, _⟩ := ha_map
    have h_dom : (g (Denumerable.ofNat ℚ n.unpair.1, i)).Dom := Part.dom_iff_mem.mpr ⟨u, hu_g⟩
    exact (hg_dom (Denumerable.ofNat ℚ n.unpair.1, i)).mp h_dom

private theorem combineOpt_lt (acc : Option ℚ) (t : Option ℚ) (p : ℕ → ℝ) (i : ℕ)
    (h_acc : ∀ q ∈ acc, (q : ℝ) < p i) (h_t : ∀ q ∈ t, (q : ℝ) < p i) :
    ∀ q ∈ combineOpt acc t, (q : ℝ) < p i := by
  intro q hq
  unfold combineOpt someMaxVal maxVal maxRat at hq
  cases h1 : acc with
  | none =>
    cases h2 : t with
    | none =>
      rw [h1, h2] at hq; contradiction
    | some q2 =>
      rw [h1, h2] at hq
      dsimp at hq
      injection hq with hq_eq
      subst hq_eq
      exact h_t q2 (Option.mem_def.mpr h2)
  | some q1 =>
    cases h2 : t with
    | none =>
      rw [h1, h2] at hq
      dsimp at hq
      injection hq with hq_eq
      subst hq_eq
      exact h_acc q1 (Option.mem_def.mpr h1)
    | some q2 =>
      rw [h1, h2] at hq
      dsimp at hq
      injection hq with hq_eq
      subst hq_eq
      have h1' := h_acc q1 (Option.mem_def.mpr h1)
      have h2' := h_t q2 (Option.mem_def.mpr h2)
      have hmax : ((max q1 q2 : ℚ) : ℝ) = max (q1 : ℝ) (q2 : ℝ) := by exact_mod_cast rfl
      rw [hmax]
      exact max_lt h1' h2'

private theorem runSeq_lt (c : Code) (p : ℕ → ℝ) (g : ℚ × ℕ →. Unit)
    (hc : c.eval = fun n =>
      (Part.ofOption (@Encodable.decode (ℚ × ℕ) Primcodable.toEncodable n)).bind
        (fun a => Part.map Encodable.encode (g a)))
    (hg_dom : ∀ ri, (g ri).Dom ↔ (ri.1 : ℝ) < p ri.2)
    (i n : ℕ) : ∀ q ∈ runSeq c i n, (q : ℝ) < p i := by
  induction n with
  | zero =>
    intro q hq
    rw [runSeq_zero] at hq
    refine combineOpt_lt none (f0 c i 0) p i ?_ ?_ q hq
    · intro q_none h_none; contradiction
    · intro q_f h_f; exact f0_lt c p g hc hg_dom i 0 q_f h_f
  | succ n ih =>
    intro q hq
    rw [runSeq_succ] at hq
    refine combineOpt_lt (runSeq c i n) (f0 c i (n + 1)) p i ih ?_ q hq
    intro q_f h_f
    exact f0_lt c p g hc hg_dom i (n + 1) q_f h_f

private theorem runSeq_f0_ge (c : Code) (i n : ℕ) (r : ℚ) (hr : r ∈ f0 c i n) :
    ∃ q : ℚ, q ∈ runSeq c i n ∧ r ≤ q := by
  induction n with
  | zero =>
    rw [runSeq_zero]
    refine combineOpt_mono_right none (f0 c i 0) r hr
  | succ n ih =>
    rw [runSeq_succ]
    refine combineOpt_mono_right (runSeq c i n) (f0 c i (n + 1)) r hr

private theorem stageEncoding_k (r : ℚ) (i : ℕ) :
    @Encodable.decode (ℚ × ℕ) Primcodable.toEncodable
      (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (r, i)) = Option.some (r, i) :=
  @Encodable.encodek (ℚ × ℕ) Primcodable.toEncodable (r, i)

private theorem hub_helper (c : Code) (i : ℕ) (r : ℚ) (u : ℝ) (k : ℕ)
    (hk : Code.evaln k c (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (r, i)) ≠ none)
    (hub : u ∈ upperBounds {r' : ℝ | ∃ n' q', runSeq c i n' = some q' ∧ (q' : ℝ) = r'}) :
    (r : ℝ) ≤ u := by
  let e := Kolmogorov.ComputableReals.ratIndex r
  let m := Nat.pair e k
  have h_f0_m : r ∈ f0 c i m := by
    rw [f0_def]
    have h_unpair_e : m.unpair.1 = e := congrArg Prod.fst (Nat.unpair_pair e k)
    have h_unpair_k : m.unpair.2 = k := congrArg Prod.snd (Nat.unpair_pair e k)
    have h_ofNat : Denumerable.ofNat ℚ e = r := Kolmogorov.ComputableReals.ofNat_ratIndex r
    rw [h_unpair_e, h_unpair_k, h_ofNat]
    have h_isSome : (Code.evaln k c (encRatNat (r, i))).isSome = true := by
      have h_enc_eq : encRatNat (r, i) =
          @Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (r, i) :=
        (encRatNat_eq (r, i)).symm
      rw [h_enc_eq]
      cases h_eval_eq : Code.evaln k c
        (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (r, i)) with
      | none => contradiction
      | some res => rfl
    rw [h_isSome]
    rfl
  obtain ⟨q, hq_rec, hrq⟩ := runSeq_f0_ge c i m r h_f0_m
  have hq_in : (q : ℝ) ∈ {r' : ℝ | ∃ n' q', runSeq c i n' = some q' ∧ (q' : ℝ) = r'} :=
    ⟨m, q, hq_rec, rfl⟩
  have hq_ub := hub hq_in
  have hr_q_real : (r : ℝ) ≤ (q : ℝ) := Rat.cast_le.mpr hrq
  exact hr_q_real.trans hq_ub

/-- **Theorem 45.** A sequence of reals is lower semicomputable if and only if
the set of pairs `(r, i)` with `r` rational and `r < p i` is enumerable. -/
theorem lowerSemicomputableSeq_iff_enumerable_rationalPairs (p : ℕ → ℝ) :
    IsLowerSemicomputableSeq p ↔ IsEnumerableSet {z : ℚ × ℕ | (z.1 : ℝ) < p z.2} := by
  constructor
  · intro h
    obtain ⟨f, hf_comp, hf_mono, hf_lub⟩ := h
    unfold IsEnumerableSet IsRE
    have h_lt : ∀ (ri : ℚ × ℕ), (ri.1 : ℝ) < p ri.2 ↔
        ∃ n q, f ri.2 n = some q ∧ ri.1 < q := by
      intro ⟨r, i⟩
      dsimp
      constructor
      · intro hr
        have hlub := hf_lub i
        have h_not_ub : ¬ (r : ℝ) ∈ upperBounds
            {r' : ℝ | ∃ n q, f i n = some q ∧ (q : ℝ) = r'} := by
          intro hub
          have h_le : p i ≤ (r : ℝ) := hlub.2 hub
          exact not_lt_of_ge h_le hr
        rw [mem_upperBounds] at h_not_ub
        push Not at h_not_ub
        obtain ⟨x, ⟨n, q, hfq, rfl⟩, hrx⟩ := h_not_ub
        have hrq : r < q := Rat.cast_lt.mp hrx
        exact ⟨n, q, hfq, hrq⟩
      · rintro ⟨n, q, hfq, hrq⟩
        have hlub := hf_lub i
        have hq_in : (q : ℝ) ∈ {r' : ℝ | ∃ n q', f i n = some q' ∧ (q' : ℝ) = r'} :=
          ⟨n, q, hfq, rfl⟩
        have hle : (q : ℝ) ≤ p i := hlub.1 hq_in
        have hrq_real : (r : ℝ) < (q : ℝ) := Rat.cast_lt.mpr hrq
        exact hrq_real.trans_le hle
    have h_rel : IsRE (fun (ri : ℚ × ℕ) => ∃ n q, f ri.2 n = some q ∧ ri.1 < q) := by
      have h_chk : Computable (chkIsSome f) := chkIsSome_computable f hf_comp
      refine ⟨fun ri => Part.map (fun _ => ())
          (Nat.rfind (fun n => Part.some (chkIsSome f (ri, n)))),
        Partrec.map (Partrec.rfind (Computable.to₂ h_chk).partrec₂)
          (Computable.const ()).to₂, ?_⟩
      intro ri
      change (Nat.rfind (show ℕ →. Bool from fun n => Part.some (chkIsSome f (ri, n)))).Dom ↔ _
      rw [Nat.rfind_dom]
      simp_rw [Part.mem_some_iff]
      have hrfind_simp : (∃ n, true = chkIsSome f (ri, n) ∧
          ∀ {m : ℕ}, m < n → (Part.some (chkIsSome f (ri, m))).Dom) ↔
          (∃ n, chkIsSome f (ri, n) = true) := by
        constructor
        · rintro ⟨n, hn, _⟩; exact ⟨n, hn.symm⟩
        · rintro ⟨n, hn⟩; exact ⟨n, hn.symm, fun _ => Part.some_dom _⟩
      rw [hrfind_simp]
      constructor
      · rintro ⟨n, hn⟩
        unfold chkIsSome chkStep condRatLt ratLtBool at hn
        dsimp at hn
        cases h_f : f ri.2 n with
        | none =>
          rw [h_f] at hn
          dsimp at hn
          contradiction
        | some q =>
          rw [h_f] at hn
          dsimp at hn
          cases h_lt_q : decide (ri.1 < q) with
          | true =>
            rw [h_lt_q] at hn
            exact ⟨n, q, h_f, decide_eq_true_iff.mp h_lt_q⟩
          | false =>
            rw [h_lt_q] at hn
            contradiction
      · rintro ⟨n, q, hfq, hrq⟩
        refine ⟨n, ?_⟩
        unfold chkIsSome chkStep condRatLt ratLtBool
        dsimp
        rw [hfq]
        dsimp
        have h_lt_q : decide (ri.1 < q) = true := decide_eq_true hrq
        rw [h_lt_q]
        rfl
    have h_iff_eq : (fun ri : ℚ × ℕ => (ri.1 : ℝ) < p ri.2) =
        (fun ri => ∃ n q, f ri.2 n = some q ∧ ri.1 < q) := by
      ext ri
      exact h_lt ri
    rw [h_iff_eq]
    exact h_rel
  · intro hA
    unfold IsEnumerableSet IsRE at hA
    obtain ⟨g, hg_partrec, hg_dom⟩ := hA
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg_partrec
    refine ⟨runSeq c, ?_, ?_, ?_⟩
    · exact runSeq_computable c
    · intro i n q hq
      exact runSeq_mono c i n q hq
    · intro i
      refine ⟨?_, ?_⟩
      · rintro x ⟨n, q, hfq, rfl⟩
        exact (runSeq_lt c p g hc hg_dom i n q hfq).le
      · intro u hub
        by_contra h_lt
        push Not at h_lt
        obtain ⟨r, hr_u, hr_p⟩ := exists_rat_btwn h_lt
        have hg_dom_r : (g (r, i)).Dom := (hg_dom (r, i)).mpr hr_p
        obtain ⟨unit_val, h_unit_mem⟩ := Part.dom_iff_mem.mp hg_dom_r
        cases unit_val
        have h_mem : Encodable.encode () ∈
            c.eval (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (r, i)) := by
          rw [hc]
          exact Part.mem_bind (Part.mem_ofOption.mpr (stageEncoding_k r i))
            (Part.mem_map _ h_unit_mem)
        obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h_mem
        have hk_ne : Code.evaln k c
            (@Encodable.encode (ℚ × ℕ) Primcodable.toEncodable (r, i)) ≠ none := by
          intro h_none
          rw [Option.mem_def.mp hk] at h_none
          contradiction
        have hr_le_u : (r : ℝ) ≤ u := hub_helper c i r u k hk_ne hub
        exact not_lt_of_ge hr_le_u hr_u

/-- The machine realizing a stream of requests: on input `p` it searches for a stage at which
the allocator hands out exactly the code `p` for a pending request, and outputs the requested
string.  It is the machine behind SUV Theorem 46 (b) — every lower semicomputable semimeasure
is the exact output distribution of some randomized machine; part (a) is
`aprioriMeasure_empty_isLowerSemicomputableSemimeasure`. -/
def M_def (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString) : Map :=
  fun p =>
    (Nat.rfind fun n => Part.some
      (decide (alloc p.2 n = some p.1 ∧ (req p.2 n).isSome = true))) >>=
      fun n => Part.ofOption ((req p.2 n).map Prod.fst)

/-- A computable request stream whose allocator never issues one code as a prefix of another makes
the request machine a prefix decompressor. -/
lemma isPrefixDecompressor_M_def (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (hreqcomp : Computable (fun p : BitString × ℕ => req p.1 p.2))
    (hcomp : Computable (fun p : BitString × ℕ => alloc p.1 p.2))
    (hprefix : ∀ ctx n m cn cm, alloc ctx n = some cn → alloc ctx m = some cm →
      n ≠ m → ¬ List.IsPrefix cn cm) :
    IsPrefixDecompressor (M_def req alloc) := by
  constructor
  · refine Partrec.bind ?_ ?_
    · exact Partrec.rfind (Partrec.of_eq (Computable.partrec
        (construct_pred_computable req alloc hreqcomp hcomp)) (fun _ => rfl))
    · exact Partrec.of_eq (construct_out_partrec req hreqcomp) (fun _ => rfl)
  · intro ctx p hp q hq hpre
    simp_all only [M_def, Bool.decide_and, Bool.decide_eq_true,
      Option.isSome_map, Part.bind_dom, Part.bind_eq_bind, Part.ofOption_dom,
      Set.mem_ofPred_eq, domainAt, ne_eq]
    obtain ⟨n, hn_dom, _⟩ := hp.1
    obtain ⟨m, hm_dom, _⟩ := hq.1
    have hn_bool : alloc ctx n = some p ∧ (req ctx n).isSome = true := by
      have hn_mem : true ∈ Part.some (decide (alloc ctx n = some p) && (req ctx n).isSome) :=
        hn_dom
      rw [Part.mem_some_iff] at hn_mem
      have h1 : (decide (alloc ctx n = some p) && (req ctx n).isSome) = true := hn_mem.symm
      simpa using h1
    have hm_bool : alloc ctx m = some q ∧ (req ctx m).isSome = true := by
      have hm_mem : true ∈ Part.some (decide (alloc ctx m = some q) && (req ctx m).isSome) :=
        hm_dom
      rw [Part.mem_some_iff] at hm_mem
      have h1 : (decide (alloc ctx m = some q) && (req ctx m).isSome) = true := hm_mem.symm
      simpa using h1
    have hn₁ := hn_bool.1
    have hm₁ := hm_bool.1
    by_cases hnm : n = m
    · cases hnm; rw [hn₁] at hm₁; cases hm₁; rfl
    · exact (hprefix ctx n m p q hn₁ hm₁ hnm hpre).elim

/-- The request machine outputs `x` on the code `p` exactly when some stage requests `x` and the
allocator answers that request with `p`. -/
lemma M_def_eq_some (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (hprefix : ∀ ctx n m cn cm, alloc ctx n = some cn → alloc ctx m = some cm →
      n ≠ m → ¬ List.IsPrefix cn cm) (p ctx x : BitString) :
    M_def req alloc (p, ctx) = Part.some x ↔
      ∃ n l, req ctx n = some (x, l) ∧ alloc ctx n = some p := by
  constructor
  · intro h
    dsimp [M_def] at h
    rw [Part.eq_some_iff, Part.mem_bind_iff] at h
    rcases h with ⟨n, hn, hout⟩
    have hn2 : n ∈ Nat.rfind (show ℕ →. Bool from fun n =>
        Part.some (decide (alloc ctx n = some p ∧ (req ctx n).isSome = true))) := hn
    rw [Nat.mem_rfind] at hn2
    have hn_bool : alloc ctx n = some p ∧ (req ctx n).isSome = true := by
      simpa using hn2.1
    have hreq_some : (req ctx n).isSome = true := hn_bool.2
    obtain ⟨⟨o, l⟩, hreq⟩ := Option.ne_none_iff_exists'.mp (Option.isSome_iff_ne_none.mp hreq_some)
    have ho : o = x := by
      simpa [hreq] using Part.mem_ofOption.mp hout
    subst ho
    exact ⟨n, l, hreq, hn_bool.1⟩
  · rintro ⟨n, l, hreq, halloc⟩
    dsimp [M_def]
    rw [Part.eq_some_iff, Part.mem_bind_iff]
    refine ⟨n, ?_, ?_⟩
    · have hn : n ∈ Nat.rfind (show ℕ →. Bool from fun n =>
          Part.some (decide (alloc ctx n = some p ∧ (req ctx n).isSome = true))) := by
        rw [Nat.mem_rfind]
        refine ⟨by simp [halloc, hreq], fun {m} hm => ?_⟩
        simp only [Part.mem_some_iff]
        rw [eq_comm, decide_eq_false_iff_not, not_and]
        intro hm_alloc _
        have hneq : m ≠ n := Nat.ne_of_lt hm
        exact absurd (List.prefix_refl p)
          (hprefix ctx n m p p halloc hm_alloc hneq.symm)
      exact hn
    · simp [hreq]

/-- The weight `2^{-l}` that stage `n` contributes to `x`, and `0` when that stage requests nothing
or requests another string. -/
noncomputable def gReq (req : BitString → ℕ → Option (BitString × ℕ))
    (ctx x : BitString) (n : ℕ) : ℝ≥0∞ :=
  match req ctx n with
  | some (o, l) => if o = x then (2 : ℝ≥0∞)⁻¹ ^ l else 0
  | none => 0

/-- A stage of nonzero weight for `x` is a stage that requests `x`, at some length. -/
lemma g_ne_zero_imp (req : BitString → ℕ → Option (BitString × ℕ))
    (ctx x : BitString) (n : ℕ) (hn : gReq req ctx x n ≠ 0) :
    ∃ l, req ctx n = some (x, l) := by
  dsimp [gReq] at hn
  cases hreq : req ctx n with
  | none => rw [hreq] at hn; contradiction
  | some p =>
    cases p with
    | mk o l =>
      rw [hreq] at hn
      dsimp at hn
      split_ifs at hn with ho
      · subst ho
        use l
      · contradiction

/-- The code that the allocator hands out at a stage of nonzero weight for `x`. -/
noncomputable def allocString (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (halloc_match : ∀ ctx n o l, req ctx n = some (o, l) →
      ∃ c, alloc ctx n = some c ∧ c.length = l)
    (ctx x : BitString) (n : ℕ) (hn : gReq req ctx x n ≠ 0) : BitString :=
  let l := (g_ne_zero_imp req ctx x n hn).choose
  let hreq := (g_ne_zero_imp req ctx x n hn).choose_spec
  (halloc_match ctx n x l hreq).choose

/-- The defining property of `allocString`: it is the allocator's answer at that stage and its
length is the requested one. -/
lemma allocString_spec (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (halloc_match : ∀ ctx n o l, req ctx n = some (o, l) →
      ∃ c, alloc ctx n = some c ∧ c.length = l)
    (ctx x : BitString) (n : ℕ) (hn : gReq req ctx x n ≠ 0) :
    ∃ l, req ctx n = some (x, l) ∧
      alloc ctx n = some (allocString req alloc halloc_match ctx x n hn) ∧
      (allocString req alloc halloc_match ctx x n hn).length = l := by
  set l := (g_ne_zero_imp req ctx x n hn).choose
  set hreq := (g_ne_zero_imp req ctx x n hn).choose_spec
  set spec := (halloc_match ctx n x l hreq).choose_spec
  exact ⟨l, hreq, spec.1, spec.2⟩

/-- **Exercise 94.** Every computable real is lower semicomputable. -/
theorem isLowerSemicomputable_of_isComputableReal (a : ℝ)
    (ha : ComputableReals.IsComputableReal a) :
    IsLowerSemicomputableReal a :=
  ComputableReals.IsComputableReal.isLowerSemicomputableReal ha

/-- **Exercise 95.** A real is computable if and only if both it and its negation
are lower semicomputable. -/
theorem isComputableReal_iff_lowerSemicomputable_and_neg (a : ℝ) :
    ComputableReals.IsComputableReal a ↔
      IsLowerSemicomputableReal a ∧ IsLowerSemicomputableReal (-a) := by
  constructor
  · intro ha
    have h1 := ComputableReals.IsComputableReal.isLowerSemicomputableReal ha
    have h2 := ComputableReals.IsComputableReal.isLowerSemicomputableReal
      (ComputableReals.IsComputableReal.neg ha)
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ComputableReals.isComputableReal_of_lower_of_lower_neg h1 h2

end Kolmogorov

