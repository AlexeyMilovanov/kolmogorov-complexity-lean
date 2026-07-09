/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Core.UniversalDecompressor
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.Prefix.Encoding
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.TwoStage
import Mathlib.Computability.PartrecCode

namespace Kolmogorov

open Nat.Partrec (Code)

/-- Specification for the conditional two-stage pair map. -/
def condTwoStagePairSpec (U : Map) (ctx : BitString → BitString → Nat → BitString)
    (w r z : BitString) : Prop :=
  ∃ p q x y : BitString,
    w = p ++ q ∧
    produces U p r x ∧
    produces U q (ctx r x p.length) y ∧
    z = pairCode x y

/-- A noncomputable partial map with exactly the graph described by
`condTwoStagePairSpec`, whenever the output is unique. -/
noncomputable def condTwoStagePairBuilder (U : Map)
    (ctx : BitString → BitString → Nat → BitString) : Map := fun pr ↦
  Part.mk (∃ z, condTwoStagePairSpec U ctx pr.1 pr.2 z) (fun h ↦ Classical.choose h)

/-- The domain of `condTwoStagePairBuilder` is exactly the existence of a
two-stage parse. -/
theorem condTwoStagePairBuilder_dom_iff (U : Map) (ctx : BitString → BitString → Nat → BitString)
    (w r : BitString) :
    (condTwoStagePairBuilder U ctx (w, r)).Dom ↔ ∃ z, condTwoStagePairSpec U ctx w r z :=
  Iff.rfl

/-- For a prefix machine `U`, the relational two-stage pair output is unique. -/
theorem condTwoStagePairSpec_unique {U : Map} {ctx : BitString → BitString → Nat → BitString}
    (hU : IsPrefixMachine U) {w r z z' : BitString}
    (hz : condTwoStagePairSpec U ctx w r z) (hz' : condTwoStagePairSpec U ctx w r z') :
    z = z' := by
  obtain ⟨p, q, x, y, hw, hp, hq, hzout⟩ := hz
  obtain ⟨p', q', x', y', hw', hp', hq', hzout'⟩ := hz'
  subst hzout
  subst hzout'
  have hp_pre_w' : p <+: p' ++ q' := by
    rw [← hw']
    exact (List.prefix_append p q).trans (by rw [← hw])
  have hp'_pre_w' : p' <+: p' ++ q' := List.prefix_append p' q'
  have hpp' : p = p' := by
    rcases List.prefix_or_prefix_of_prefix hp_pre_w' hp'_pre_w' with hpre | hpre
    · exact IsPrefixMachine.eq_of_prefix hU hp hp' hpre
    · exact (IsPrefixMachine.eq_of_prefix hU hp' hp hpre).symm
  subst hpp'
  have hx : x = x' := Part.mem_unique hp hp'
  subst hx
  have hqpre : q <+: q' := by
    apply (List.prefix_append_right_inj p).mp
    rw [← hw, ← hw']
  have hqq' : q = q' := IsPrefixMachine.eq_of_prefix hU hq hq' hqpre
  subst hqq'
  have hy : y = y' := Part.mem_unique hq hq'
  subst hy
  rfl

/-- Any relational two-stage parse is produced by the noncomputable
`condTwoStagePairBuilder` when `U` is prefix-free. -/
theorem condTwoStagePairBuilder_produces_of_spec {U : Map}
    {ctx : BitString → BitString → Nat → BitString} (hU : IsPrefixMachine U)
    {w r z : BitString} (hz : condTwoStagePairSpec U ctx w r z) :
    produces (condTwoStagePairBuilder U ctx) w r z := by
  change z ∈ Part.mk (∃ z', condTwoStagePairSpec U ctx w r z')
    (fun h ↦ Classical.choose h)
  rw [Part.mem_mk_iff]
  refine ⟨⟨z, hz⟩, ?_⟩
  exact (condTwoStagePairSpec_unique hU (Classical.choose_spec ⟨z, hz⟩) hz)

/-- Membership in the relational builder is exactly the spec, given prefix-freeness. -/
theorem mem_condTwoStagePairBuilder_iff {U : Map} {ctx : BitString → BitString → Nat → BitString}
    (hU : IsPrefixMachine U) {w r z : BitString} :
    z ∈ condTwoStagePairBuilder U ctx (w, r) ↔ condTwoStagePairSpec U ctx w r z := by
  constructor
  · intro hz
    change z ∈ Part.mk (∃ z', condTwoStagePairSpec U ctx w r z') (fun h ↦ Classical.choose h) at hz
    rw [Part.mem_mk_iff] at hz
    obtain ⟨hdom, hval⟩ := hz
    have := Classical.choose_spec hdom
    rw [hval] at this
    exact this
  · intro hz
    exact condTwoStagePairBuilder_produces_of_spec hU hz

/-- The relational two-stage pair builder is prefix-free whenever `U` is a
prefix machine. -/
theorem condTwoStagePairBuilder_isPrefixMachine {U : Map}
    {ctx : BitString → BitString → Nat → BitString} (hU : IsPrefixMachine U) :
    IsPrefixMachine (condTwoStagePairBuilder U ctx) := by
  intro r w hw w' hw' hpre
  change (condTwoStagePairBuilder U ctx (w, r)).Dom at hw
  change (condTwoStagePairBuilder U ctx (w', r)).Dom at hw'
  rw [condTwoStagePairBuilder_dom_iff] at hw hw'
  obtain ⟨z, hz⟩ := hw
  obtain ⟨z', hz'⟩ := hw'
  obtain ⟨p, q, x, y, hw, hp, hq, hzout⟩ := hz
  obtain ⟨p', q', x', y', hw', hp', hq', hzout'⟩ := hz'
  subst hw
  subst hw'
  have hp_pre_w' : p <+: p' ++ q' := (List.prefix_append p q).trans hpre
  have hp'_pre_w' : p' <+: p' ++ q' := List.prefix_append p' q'
  have hpp' : p = p' := by
    rcases List.prefix_or_prefix_of_prefix hp_pre_w' hp'_pre_w' with hpre' | hpre'
    · exact IsPrefixMachine.eq_of_prefix hU hp hp' hpre'
    · exact (IsPrefixMachine.eq_of_prefix hU hp' hp hpre').symm
  subst hpp'
  have hx : x = x' := Part.mem_unique hp hp'
  subst hx
  have hqpre : q <+: q' := (List.prefix_append_right_inj p).mp hpre
  have hqq' : q = q' := IsPrefixMachine.eq_of_prefix hU hq hq' hqpre
  rw [hqq']

/-- A concrete pair of first-stage and second-stage programs bounds the
complexity in the relational two-stage pair builder by the concatenated length. -/
theorem KP_condTwoStagePairBuilder_le_of_produces {U : Map}
    {ctx : BitString → BitString → Nat → BitString} (hU : IsPrefixMachine U)
    {p q x y r : BitString}
    (hp : produces U p r x) (hq : produces U q (ctx r x p.length) y) :
    KP (condTwoStagePairBuilder U ctx) (pairCode x y) r ≤
      ((p.length + q.length : Nat) : ENat) := by
  have hprod : produces (condTwoStagePairBuilder U ctx) (p ++ q) r (pairCode x y) :=
    condTwoStagePairBuilder_produces_of_spec hU
      ⟨p, q, x, y, rfl, hp, hq, rfl⟩
  have hle := KP_le_programLength_of_produces hprod
  simpa [programLength, List.length_append] using hle

/-! ### The explicit dovetailing two-stage decompressor

We now build a genuinely computable map `condTwoStageMap c ctx` from a
`Nat.Partrec.Code` `c` for `U`, and prove it equals the relational builder. -/

/-- Stage-1 output option: decode `U(take i w, [])` run with fuel `t`, where
`(i, t) = unpair n`. -/
def condTwoStageS1 (c : Code) (w r : BitString) (n : ℕ) : Option BitString :=
  (Code.evaln n.unpair.2 c (Encodable.encode (w.take n.unpair.1, r))).bind
    (fun e ↦ (Encodable.decode e : Option BitString))

/-- Stage-2 output option: decode `U(drop i w, ctx x i)` run with fuel `t`,
where `x` is the stage-1 output. -/
def condTwoStageS2 (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (w r : BitString) (n : ℕ) : Option BitString :=
  (condTwoStageS1 c w r n).bind (fun x ↦
    (Code.evaln n.unpair.2 c (Encodable.encode (w.drop n.unpair.1, ctx r x n.unpair.1))).bind
      (fun e ↦ (Encodable.decode e : Option BitString)))

/-- The candidate pair output for search index `n`. -/
def condTwoStagePairOut (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (w r : BitString) (n : ℕ) : Option BitString :=
  (condTwoStageS1 c w r n).bind (fun x ↦
    (condTwoStageS2 c ctx w r n).map (fun y ↦ pairCode x y))

/-- The dovetailing check predicate: the split index is within range and both
stages have produced an output at fuel `t`. -/
def condTwoStageCheck (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (w r : BitString) (n : ℕ) : Bool :=
  decide (n.unpair.1 ≤ w.length) && (condTwoStagePairOut c ctx w r n).isSome

/-- The explicit computable two-stage decompressor. -/
def condTwoStageMap (c : Code) (ctx : BitString → BitString → Nat → BitString) : Map := fun pr ↦
  (Nat.rfind (fun n ↦ Part.some (condTwoStageCheck c ctx pr.1 pr.2 n))).bind
    (fun n ↦ (↑(condTwoStagePairOut c ctx pr.1 pr.2 n) : Part BitString))

/-
`condTwoStageS1` as a function of the pair `(w, n)` is computable.
-/
theorem condTwoStageS1_computable (c : Code) :
    Computable (fun p : (BitString × BitString) × ℕ ↦ condTwoStageS1 c p.1.1 p.1.2 p.2) := by
  have h_evaln_computable : Computable₂ (fun (n : ℕ) (m : ℕ) ↦ Code.evaln n c m) :=
    evaln_fixed_computable c
  have h_take_computable : Computable₂ (fun (w : BitString) (n : ℕ) ↦ w.take n) := by
    convert primrec_list_take.to_comp using 1
  exact Computable.option_bind
    (h_evaln_computable.comp
      (Computable.snd.comp (Computable.unpair.comp Computable.snd))
      (Computable.encode.comp
        (Computable.pair
          (h_take_computable.comp
            (Computable.fst.comp Computable.fst)
            (Computable.fst.comp (Computable.unpair.comp Computable.snd)))
          (Computable.snd.comp Computable.fst))))
    (Computable.decode.comp Computable.snd)
/-
`condTwoStageS2` as a function of the pair `(w, n)` is computable, provided the
context map is computable.
-/
theorem condTwoStageS2_h_comp_computable (c : Code) :
    Computable (fun p : (BitString × BitString) × ℕ ↦ condTwoStageS1 c p.1.1 p.1.2 p.2) ∧
      Computable (fun p : (BitString × BitString) × ℕ ↦ p.1.1.drop p.2.unpair.1) ∧
      Computable (fun p : (BitString × BitString) × ℕ ↦ p.2.unpair.1 : (BitString × BitString) × ℕ → ℕ) ∧
      Computable (fun p : (BitString × BitString) × ℕ ↦ p.2.unpair.2 : (BitString × BitString) × ℕ → ℕ) := by
  refine ⟨condTwoStageS1_computable c, ?_, ?_, ?_⟩
  · exact Primrec.to_comp
      (primrec_list_drop.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
  · exact Computable.fst.comp (Computable.unpair.comp Computable.snd)
  · exact Computable.snd.comp (Computable.unpair.comp Computable.snd)

theorem condTwoStageS2_h_bind_computable_h4 (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    Computable (fun (px : ((BitString × BitString) × ℕ) × BitString) ↦ ctx px.1.1.2 px.2 px.1.2.unpair.1) := by
  have h1 : Computable (fun (px : ((BitString × BitString) × ℕ) × BitString) ↦ px.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have h2 : Computable (fun (px : ((BitString × BitString) × ℕ) × BitString) ↦ px.2) :=
    Computable.snd
  have h3 : Computable (fun (px : ((BitString × BitString) × ℕ) × BitString) ↦ px.1.2.unpair.1) :=
    Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst))
  exact @Computable.comp (((BitString × BitString) × ℕ) × BitString) ((BitString × BitString) × ℕ) BitString _ _ _
    (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)
    (fun px : ((BitString × BitString) × ℕ) × BitString ↦ ((px.1.1.2, px.2), px.1.2.unpair.1))
    hctx
    (Computable.pair (Computable.pair h1 h2) h3)

theorem condTwoStageS2_h_bind_computable_h6 (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    Computable (fun (px : ((BitString × BitString) × ℕ) × BitString) ↦ Encodable.encode (px.1.1.1.drop px.1.2.unpair.1, ctx px.1.1.2 px.2 px.1.2.unpair.1)) := by
  have h4 := condTwoStageS2_h_bind_computable_h4 ctx hctx
  have h5 : Computable (fun (px : ((BitString × BitString) × ℕ) × BitString) ↦ px.1.1.1.drop px.1.2.unpair.1) :=
    (condTwoStageS2_h_comp_computable c).2.1.comp Computable.fst
  exact Computable.encode.comp (Computable.pair h5 h4)

-- Computability of the two-stage bind step; heavy type inference over the nested context.
theorem condTwoStageS2_h_bind_computable (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    Computable (fun (px : ((BitString × BitString) × ℕ) × BitString) ↦
      Code.evaln px.1.2.unpair.2 c (Encodable.encode (px.1.1.1.drop px.1.2.unpair.1, ctx px.1.1.2 px.2 px.1.2.unpair.1))) := by
  have h6 := condTwoStageS2_h_bind_computable_h6 c ctx hctx
  have h7 : Computable (fun (px : ((BitString × BitString) × ℕ) × BitString) ↦ px.1.2.unpair.2) :=
    (condTwoStageS2_h_comp_computable c).2.2.2.comp Computable.fst
  exact @Computable.comp (((BitString × BitString) × ℕ) × BitString) (ℕ × ℕ) (Option ℕ) _ _ _
    (fun p : ℕ × ℕ ↦ Code.evaln p.1 c p.2)
    (fun px : ((BitString × BitString) × ℕ) × BitString ↦ (px.1.2.unpair.2, Encodable.encode (px.1.1.1.drop px.1.2.unpair.1, ctx px.1.1.2 px.2 px.1.2.unpair.1)))
    (evaln_fixed_computable c) (@Computable.pair (((BitString × BitString) × ℕ) × BitString) ℕ ℕ _ _ _ _ _ h7 h6)

theorem condTwoStageS2_computable (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    Computable (fun p : (BitString × BitString) × ℕ ↦ condTwoStageS2 c ctx p.1.1 p.1.2 p.2) := by
  have h_comp := condTwoStageS2_h_comp_computable c
  change Computable (fun p : (BitString × BitString) × ℕ ↦
    (condTwoStageS1 c p.1.1 p.1.2 p.2).bind (fun x ↦
      (Code.evaln p.2.unpair.2 c
        (Encodable.encode (p.1.1.drop p.2.unpair.1, ctx p.1.2 x p.2.unpair.1))).bind
        (fun e ↦ (Encodable.decode e : Option BitString))))
  apply Computable.option_bind h_comp.1
  apply Computable.option_bind (condTwoStageS2_h_bind_computable c ctx hctx)
  · exact Computable.decode.comp Computable.snd
/-
`condTwoStagePairOut` is computable, provided the context map is computable.
-/
theorem condTwoStagePairOut_computable (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    Computable (fun p : (BitString × BitString) × ℕ ↦ condTwoStagePairOut c ctx p.1.1 p.1.2 p.2) := by
  have h_condTwoStageS2_computable : Computable (fun p : (BitString × BitString) × ℕ ↦ condTwoStageS2 c ctx p.1.1 p.1.2 p.2) :=
    condTwoStageS2_computable c ctx hctx
  have h_condTwoStageS1_computable : Computable (fun p : (BitString × BitString) × ℕ ↦ condTwoStageS1 c p.1.1 p.1.2 p.2) :=
    condTwoStageS1_computable c
  have h_pairCode_computable : Computable₂ (fun (x y : BitString) ↦ pairCode x y) := by
    have h_natCode_computable : Computable (fun (n : ℕ) ↦ natCode n) := by
      have h_natCode_computable : Computable (fun n ↦ List.replicate n true ++ [false]) := by
        have h_replicate : Computable (fun n ↦ List.replicate n true) := by
          apply Computable.of_eq
          apply Computable.nat_rec
          exact Computable.id
          exact Computable.const []
          rotate_left
          exact fun _ p ↦ true :: p.2
          · intro n
            induction n <;> simp +decide [*, List.replicate]
            assumption
          · exact Computable.list_cons.comp (Computable.const true) (Computable.snd.comp Computable.snd)
        exact Computable.comp Computable.list_append (h_replicate.pair (Computable.const [false]))
      exact h_natCode_computable
    exact Computable.comp
      (Computable.list_append.comp
        (Computable.list_append.comp
          (h_natCode_computable.comp (Computable.list_length.comp Computable.fst))
          Computable.fst)
        Computable.snd)
      (Computable.pair Computable.fst Computable.snd)
  change Computable (fun p : (BitString × BitString) × ℕ ↦
    (condTwoStageS1 c p.1.1 p.1.2 p.2).bind (fun x ↦
      (condTwoStageS2 c ctx p.1.1 p.1.2 p.2).map (fun y ↦ pairCode x y)))
  exact Computable.option_bind h_condTwoStageS1_computable (Computable.option_map
    (h_condTwoStageS2_computable.comp Computable.fst)
    (h_pairCode_computable.comp (Computable.snd.comp Computable.fst) Computable.snd))
/-
`condTwoStageCheck` is computable, provided the context map is computable.
-/
theorem condTwoStageCheck_h1_computable :
    Computable (fun p : (BitString × BitString) × ℕ ↦ decide (p.2.unpair.1 ≤ p.1.1.length)) := by
  exact Primrec.to_comp
    (PrimrecPred.decide
      (Primrec.nat_le.comp
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))))

theorem condTwoStageCheck_h2_computable (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    Computable (fun p : (BitString × BitString) × ℕ ↦ (condTwoStagePairOut c ctx p.1.1 p.1.2 p.2).isSome) :=
  Primrec.to_comp Primrec.option_isSome |> Computable.comp <| condTwoStagePairOut_computable c ctx hctx

theorem condTwoStageCheck_computable (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    Computable (fun p : (BitString × BitString) × ℕ ↦ condTwoStageCheck c ctx p.1.1 p.1.2 p.2) := by
  have h3 := Computable.cond condTwoStageCheck_h1_computable (condTwoStageCheck_h2_computable c ctx hctx) (Computable.const false)
  exact Computable.of_eq h3 (fun p ↦ by
    unfold condTwoStageCheck
    cases decide (p.2.unpair.1 ≤ p.1.1.length) <;> rfl)

theorem condTwoStageMap_search_partrec (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    Partrec (fun p : BitString × BitString ↦
      Nat.rfind (fun n ↦ Part.some (condTwoStageCheck c ctx p.1 p.2 n))) := by
  exact Partrec.rfind (condTwoStageCheck_computable c ctx hctx)

theorem condTwoStageMap_output_partrec (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    Partrec (fun p : (BitString × BitString) × ℕ ↦
      (↑(condTwoStagePairOut c ctx p.1.1 p.1.2 p.2) : Part BitString)) := by
  exact (Computable.ofOption (condTwoStagePairOut_computable c ctx hctx)).comp
    (Computable.fst.pair Computable.snd)

-- The explicit two-stage decompressor is partial recursive.
theorem condTwoStageMap_partrec (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    Partrec (condTwoStageMap c ctx) := by
  change Partrec (fun p : BitString × BitString ↦
      (Nat.rfind (fun n ↦ Part.some (condTwoStageCheck c ctx p.1 p.2 n))).bind
        (fun n ↦ (↑(condTwoStagePairOut c ctx p.1 p.2 n) : Part BitString)))
  exact Partrec.bind (condTwoStageMap_search_partrec c ctx hctx)
    (condTwoStageMap_output_partrec c ctx hctx)
/-
Soundness: any value produced by the explicit decompressor satisfies the
relational two-stage spec, provided `c` is a code for `U`.
-/
theorem condTwoStageMap_mem_imp_spec {U : Map} {ctx : BitString → BitString → Nat → BitString}
    {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {w r z : BitString} (hz : z ∈ condTwoStageMap c ctx (w, r)) :
    condTwoStagePairSpec U ctx w r z := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.rfind (fun n ↦ Part.some (condTwoStageCheck c ctx w r n)) = Part.some n ∧ z ∈ (↑(condTwoStagePairOut c ctx w r n) : Part BitString) := by
    unfold condTwoStageMap at hz;
    cases h : Nat.rfind ( fun n ↦ Part.some ( condTwoStageCheck c ctx w r n ) ); simp_all +decide [ Part.mem_bind_iff ];
    aesop;
  obtain ⟨x, y, hx, hy⟩ : ∃ x y, condTwoStageS1 c w r n = some x ∧ condTwoStageS2 c ctx w r n = some y ∧ z = pairCode x y := by
    unfold condTwoStagePairOut at hn; simp_all +decide;
    cases h : condTwoStageS1 c w r n <;> cases h' : condTwoStageS2 c ctx w r n <;> aesop;
  refine ⟨ w.take n.unpair.1, w.drop n.unpair.1, x, y, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ condTwoStageS1, condTwoStageS2 ];
  · rw [ Option.bind_eq_some_iff ] at hx;
    obtain ⟨ a, ha₁, ha₂ ⟩ := hx; have := Nat.Partrec.Code.evaln_sound ha₁; simp_all +decide [ produces ];
    obtain ⟨ b, hb₁, hb₂ ⟩ := this; have := Encodable.encodek ( α := BitString ) b; aesop;
  · rw [ min_eq_left ];
    · rw [ Option.bind_eq_some_iff ] at hy;
      obtain ⟨ ⟨ a, ha₁, ha₂ ⟩, rfl ⟩ := hy; simp_all +decide [ produces ];
      have := Nat.Partrec.Code.evaln_sound ha₁; simp_all +decide;
      obtain ⟨ z, hz₁, hz₂ ⟩ := this; have := Encodable.encodek z; aesop;
    · have := Nat.mem_rfind.mp ( show n ∈ Nat.rfind ( fun n ↦ Part.some ( condTwoStageCheck c ctx w r n ) ) from by aesop ); simp_all +decide [ condTwoStageCheck ];
theorem condTwoStageMap_dom_of_spec {U : Map} {ctx : BitString → BitString → Nat → BitString}
    {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {w r z : BitString} (hz : condTwoStagePairSpec U ctx w r z) :
    (condTwoStageMap c ctx (w, r)).Dom := by
  obtain ⟨p, q, x, y, hw, hx, hy, -⟩ := hz
  subst hw
  have h1mem : Encodable.encode x ∈ c.eval (Encodable.encode (p, r)) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(p, r), by simp,
      Part.mem_map Encodable.encode hx⟩
  obtain ⟨t1, ht1⟩ : ∃ t1, Code.evaln t1 c (Encodable.encode (p, r))
      = some (Encodable.encode x) := by
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h1mem
    exact ⟨k, Option.mem_def.mp hk⟩
  have h2mem : Encodable.encode y ∈ c.eval (Encodable.encode (q, ctx r x p.length)) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(q, ctx r x p.length), by simp,
      Part.mem_map Encodable.encode hy⟩
  obtain ⟨t2, ht2⟩ : ∃ t2, Code.evaln t2 c (Encodable.encode (q, ctx r x p.length))
      = some (Encodable.encode y) := by
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h2mem
    exact ⟨k, Option.mem_def.mp hk⟩
  have ht1' : Code.evaln (max t1 t2) c (Encodable.encode (p, r))
      = some (Encodable.encode x) :=
    Nat.Partrec.Code.evaln_mono (le_max_left t1 t2) ht1
  have ht2' : Code.evaln (max t1 t2) c (Encodable.encode (q, ctx r x p.length))
      = some (Encodable.encode y) :=
    Nat.Partrec.Code.evaln_mono (le_max_right t1 t2) ht2
  have hs1 : condTwoStageS1 c (p ++ q) r (Nat.pair p.length (max t1 t2)) = some x := by
    unfold condTwoStageS1
    simp only [Nat.unpair_pair, List.take_left, ht1', Option.bind_some, Encodable.encodek]
  have hs2 : condTwoStageS2 c ctx (p ++ q) r (Nat.pair p.length (max t1 t2)) = some y := by
    unfold condTwoStageS2
    rw [hs1]
    simp only [Nat.unpair_pair, List.drop_left, Option.bind_some, ht2', Encodable.encodek]
  have hpair : condTwoStagePairOut c ctx (p ++ q) r (Nat.pair p.length (max t1 t2))
      = some (pairCode x y) := by
    unfold condTwoStagePairOut
    rw [hs1, hs2]; rfl
  have hcheck : condTwoStageCheck c ctx (p ++ q) r (Nat.pair p.length (max t1 t2)) = true := by
    unfold condTwoStageCheck
    rw [hpair]
    simp only [Nat.unpair_pair, Option.isSome_some, Bool.and_true, decide_eq_true_eq,
      List.length_append]
    omega
  have hrdom : (Nat.rfind (fun m ↦ Part.some (condTwoStageCheck c ctx (p ++ q) r m))).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨Nat.pair p.length (max t1 t2), by rw [Part.mem_some_iff, hcheck],
      fun {m} _ ↦ Part.some_dom _⟩
  obtain ⟨n', hn'⟩ := Part.dom_iff_mem.mp hrdom
  have hcheck' : condTwoStageCheck c ctx (p ++ q) r n' = true := by
    have h := (Nat.mem_rfind.mp hn').1
    rw [Part.mem_some_iff] at h
    exact h.symm
  have hsome : (condTwoStagePairOut c ctx (p ++ q) r n').isSome = true := by
    unfold condTwoStageCheck at hcheck'
    exact ((Bool.and_eq_true _ _).mp hcheck').2
  obtain ⟨z'', hz''⟩ := Option.isSome_iff_exists.mp hsome
  refine Part.dom_iff_mem.mpr ⟨z'', ?_⟩
  unfold condTwoStageMap
  rw [Part.mem_bind_iff]
  exact ⟨n', hn', by rw [Part.mem_ofOption]; exact Option.mem_def.mpr hz''⟩
theorem condTwoStagePairBuilder_eq_condTwoStageMap {U : Map}
    {ctx : BitString → BitString → Nat → BitString} (hU : IsPrefixMachine U) {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a))) :
    condTwoStagePairBuilder U ctx = condTwoStageMap c ctx := by
  funext pr
  obtain ⟨w, r⟩ := pr
  apply Part.ext
  intro z
  rw [mem_condTwoStagePairBuilder_iff hU]
  constructor
  · intro hz
    -- spec holds; the explicit map halts and, by uniqueness, produces `z`.
    have hdom := condTwoStageMap_dom_of_spec (U := U) (ctx := ctx) hc (r := r) hz
    obtain ⟨z', hz'⟩ := Part.dom_iff_mem.mp hdom
    have hspec' := condTwoStageMap_mem_imp_spec (U := U) (ctx := ctx) hc hz'
    have : z' = z := condTwoStagePairSpec_unique hU hspec' hz
    rwa [this] at hz'
  · intro hz
    exact condTwoStageMap_mem_imp_spec (U := U) (ctx := ctx) hc hz

/-- **Main computability result.** The relational two-stage builder is a genuine
decompressor (partial recursive), provided `U` is a partial recursive prefix
machine and the context map is computable. -/
theorem condTwoStagePairBuilder_isDecompressor {U : Map}
    {ctx : BitString → BitString → Nat → BitString}
    (hUp : isDecompressor U) (hU : IsPrefixMachine U)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    isDecompressor (condTwoStagePairBuilder U ctx) := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hUp
  rw [condTwoStagePairBuilder_eq_condTwoStageMap hU hc]
  exact condTwoStageMap_partrec c ctx hctx

/-- The relational two-stage builder is a prefix decompressor. -/
theorem condTwoStagePairBuilder_isPrefixDecompressor {U : Map}
    {ctx : BitString → BitString → Nat → BitString}
    (hUp : isDecompressor U) (hU : IsPrefixMachine U)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2)) :
    IsPrefixDecompressor (condTwoStagePairBuilder U ctx) :=
  ⟨condTwoStagePairBuilder_isDecompressor hUp hU hctx,
    condTwoStagePairBuilder_isPrefixMachine hU⟩

end Kolmogorov
