import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.Encoding
import KolmogorovMathlib.Core.UniversalDecompressor

/-!
# The Two-Stage Pair Builder and its Computability

This module builds the *coding-direction* infrastructure for prefix symmetry of
information. The central object is the `twoStagePairBuilder`: a prefix machine
that, on a program `p ++ q`, recovers `x` from the self-delimiting `U`-program
`p` and then recovers `y` from the `U`-program `q` run in a context computed from
`x` and `p.length`, finally outputting the encoded pair `pairCode x y`.

The builder is first defined *relationally* (its graph is `twoStagePairSpec`),
which makes the prefix-freeness and coding bound easy. The hard part, supplied
here, is **computability**: we exhibit an explicit dovetailing decompressor
`twoStageMap`, built from a `Nat.Partrec.Code` for `U`, and prove it equals the
relational builder. This yields `twoStagePairBuilder_isDecompressor`, which is
the missing ingredient for the upper direction of prefix SoI.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### The concrete pair code -/

/-- A concrete self-delimiting encoding of a pair of bitstrings.

The first component is preceded by a unary code for its length, so the boundary
between the two components is recoverable from the encoded string. This is an
encoding of outputs/contexts, not a prefix-free program code by itself. -/
def pairCode (x y : BitString) : BitString :=
  natCode x.length ++ x ++ y

/-- The length of the concrete pair code. -/
@[simp] theorem length_pairCode (x y : BitString) :
    (pairCode x y).length = x.length + 1 + x.length + y.length := by
  simp [pairCode, List.length_append, length_natCode]
  omega

/-- The concrete pair code is injective. -/
theorem pairCode_injective :
    Function.Injective (fun p : Prod BitString BitString => pairCode p.1 p.2) := by
  intro p q h
  dsimp [pairCode] at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hl, happ⟩ := natCode_append_inj h
  have hp1 : p.1 = q.1 := List.append_inj_left happ hl
  have hp2 : p.2 = q.2 := by
    rw [hp1] at happ
    exact List.append_cancel_left happ
  exact Prod.ext hp1 hp2

/-! ### The relational two-stage builder -/

/-- The relational graph of the intended two-stage pair builder. A program `w`
splits as `p ++ q`; `p` is a prefix `U`-program for `x`, and `q` is a prefix
`U`-program for `y` in the context computed from `x` and `p.length`. -/
def twoStagePairSpec (U : Map) (ctx : BitString → Nat → BitString)
    (w z : BitString) : Prop :=
  ∃ p q x y : BitString,
    w = p ++ q ∧
    produces U p [] x ∧
    produces U q (ctx x p.length) y ∧
    z = pairCode x y

/-- A noncomputable partial map with exactly the graph described by
`twoStagePairSpec`, whenever the output is unique. -/
noncomputable def twoStagePairBuilder (U : Map)
    (ctx : BitString → Nat → BitString) : Map := fun pr =>
  Part.mk (∃ z, twoStagePairSpec U ctx pr.1 z) (fun h => Classical.choose h)

/-- The domain of `twoStagePairBuilder` is exactly the existence of a
two-stage parse. -/
theorem twoStagePairBuilder_dom_iff (U : Map) (ctx : BitString → Nat → BitString)
    (w r : BitString) :
    (twoStagePairBuilder U ctx (w, r)).Dom ↔ ∃ z, twoStagePairSpec U ctx w z :=
  Iff.rfl

/-- For a prefix machine `U`, the relational two-stage pair output is unique. -/
theorem twoStagePairSpec_unique {U : Map} {ctx : BitString → Nat → BitString}
    (hU : IsPrefixMachine U) {w z z' : BitString}
    (hz : twoStagePairSpec U ctx w z) (hz' : twoStagePairSpec U ctx w z') :
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
`twoStagePairBuilder` when `U` is prefix-free. -/
theorem twoStagePairBuilder_produces_of_spec {U : Map}
    {ctx : BitString → Nat → BitString} (hU : IsPrefixMachine U)
    {w z : BitString} (hz : twoStagePairSpec U ctx w z) :
    produces (twoStagePairBuilder U ctx) w [] z := by
  change z ∈ Part.mk (∃ z', twoStagePairSpec U ctx w z')
    (fun h => Classical.choose h)
  rw [Part.mem_mk_iff]
  refine ⟨⟨z, hz⟩, ?_⟩
  exact (twoStagePairSpec_unique hU (Classical.choose_spec ⟨z, hz⟩) hz)

/-- Membership in the relational builder is exactly the spec, given prefix-freeness. -/
theorem mem_twoStagePairBuilder_iff {U : Map} {ctx : BitString → Nat → BitString}
    (hU : IsPrefixMachine U) {w r z : BitString} :
    z ∈ twoStagePairBuilder U ctx (w, r) ↔ twoStagePairSpec U ctx w z := by
  constructor
  · intro hz
    change z ∈ Part.mk (∃ z', twoStagePairSpec U ctx w z') (fun h => Classical.choose h) at hz
    rw [Part.mem_mk_iff] at hz
    obtain ⟨hdom, hval⟩ := hz
    have := Classical.choose_spec hdom
    rw [hval] at this
    exact this
  · intro hz
    exact twoStagePairBuilder_produces_of_spec hU hz

/-- The relational two-stage pair builder is prefix-free whenever `U` is a
prefix machine. -/
theorem twoStagePairBuilder_isPrefixMachine {U : Map}
    {ctx : BitString → Nat → BitString} (hU : IsPrefixMachine U) :
    IsPrefixMachine (twoStagePairBuilder U ctx) := by
  intro r w hw w' hw' hpre
  change (twoStagePairBuilder U ctx (w, r)).Dom at hw
  change (twoStagePairBuilder U ctx (w', r)).Dom at hw'
  rw [twoStagePairBuilder_dom_iff] at hw hw'
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
theorem KP_twoStagePairBuilder_le_of_produces {U : Map}
    {ctx : BitString → Nat → BitString} (hU : IsPrefixMachine U)
    {p q x y : BitString}
    (hp : produces U p [] x) (hq : produces U q (ctx x p.length) y) :
    KP (twoStagePairBuilder U ctx) (pairCode x y) [] ≤
      ((p.length + q.length : Nat) : ENat) := by
  have hprod : produces (twoStagePairBuilder U ctx) (p ++ q) [] (pairCode x y) :=
    twoStagePairBuilder_produces_of_spec hU
      ⟨p, q, x, y, rfl, hp, hq, rfl⟩
  have hle := KP_le_programLength_of_produces hprod
  simpa [programLength, List.length_append] using hle

/-! ### The explicit dovetailing two-stage decompressor

We now build a genuinely computable map `twoStageMap c ctx` from a
`Nat.Partrec.Code` `c` for `U`, and prove it equals the relational builder. -/

/-
`List.take` is primitive recursive in both arguments; this restates the general
`Primrec.list_take` toolkit lemma at `BitString`, mirroring `primrec_list_drop`.
-/
theorem primrec_list_take :
    Primrec₂ (fun (l : BitString) (n : ℕ) => l.take n) :=
  Primrec.list_take

/-
Evaluating a *fixed* code with given fuel and input is computable.
-/
theorem evaln_fixed_computable (c : Code) :
    Computable (fun p : ℕ × ℕ => Code.evaln p.1 c p.2) :=
  (Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c)) Primrec.snd)).to_comp

/-- Stage-1 output option: decode `U(take i w, [])` run with fuel `t`, where
`(i, t) = unpair n`. -/
def twoStageS1 (c : Code) (w : BitString) (n : ℕ) : Option BitString :=
  (Code.evaln n.unpair.2 c (Encodable.encode (w.take n.unpair.1, ([] : BitString)))).bind
    (fun e => (Encodable.decode e : Option BitString))

/-- Stage-2 output option: decode `U(drop i w, ctx x i)` run with fuel `t`,
where `x` is the stage-1 output. -/
def twoStageS2 (c : Code) (ctx : BitString → Nat → BitString)
    (w : BitString) (n : ℕ) : Option BitString :=
  (twoStageS1 c w n).bind (fun x =>
    (Code.evaln n.unpair.2 c (Encodable.encode (w.drop n.unpair.1, ctx x n.unpair.1))).bind
      (fun e => (Encodable.decode e : Option BitString)))

/-- The candidate pair output for search index `n`. -/
def twoStagePairOut (c : Code) (ctx : BitString → Nat → BitString)
    (w : BitString) (n : ℕ) : Option BitString :=
  (twoStageS1 c w n).bind (fun x =>
    (twoStageS2 c ctx w n).map (fun y => pairCode x y))

/-- The dovetailing check predicate: the split index is within range and both
stages have produced an output at fuel `t`. -/
def twoStageCheck (c : Code) (ctx : BitString → Nat → BitString)
    (w : BitString) (n : ℕ) : Bool :=
  decide (n.unpair.1 ≤ w.length) && (twoStagePairOut c ctx w n).isSome

/-- The explicit computable two-stage decompressor. -/
def twoStageMap (c : Code) (ctx : BitString → Nat → BitString) : Map := fun pr =>
  (Nat.rfind (fun n => Part.some (twoStageCheck c ctx pr.1 n))).bind
    (fun n => (↑(twoStagePairOut c ctx pr.1 n) : Part BitString))

/-
`twoStageS1` as a function of the pair `(w, n)` is computable.
-/
theorem twoStageS1_computable (c : Code) :
    Computable (fun p : BitString × ℕ => twoStageS1 c p.1 p.2) := by
  -- The function `Code.evaln` is computable because it is a primitive recursive function.
  have h_evaln_computable : Computable₂ (fun (n : ℕ) (m : ℕ) => Code.evaln n c m) :=
    evaln_fixed_computable c
  have h_take_computable : Computable₂ (fun (w : BitString) (n : ℕ) => w.take n) :=
    primrec_list_take.to_comp
  convert Computable.option_bind _ _ using 1;
  · exact inferInstance
  · convert h_evaln_computable.comp ( Computable.snd.comp (
      Computable.unpair.comp Computable.snd ) ) ( Computable.encode.comp (
          h_take_computable.comp Computable.fst ( Computable.fst.comp (
              Computable.unpair.comp Computable.snd ) )
                  |> Computable.pair <| Computable.const [] ) ) using 1;
  · exact Computable.decode.comp Computable.snd

/-
`twoStageS2` as a function of the pair `(w, n)` is computable, provided the
context map is computable.
-/
theorem twoStageS2_computable (c : Code) (ctx : BitString → Nat → BitString)
    (hctx : Computable (fun p : BitString × ℕ => ctx p.1 p.2)) :
    Computable (fun p : BitString × ℕ => twoStageS2 c ctx p.1 p.2) := by
  have h_comp : Computable (fun p : BitString × ℕ => twoStageS1 c p.1 p.2) ∧
    Computable (fun p : BitString × ℕ => p.1.drop p.2.unpair.1) ∧
      Computable (fun p : BitString × ℕ => p.2.unpair.1 : BitString × ℕ → ℕ) ∧
        Computable (fun p : BitString × ℕ => p.2.unpair.2 : BitString × ℕ → ℕ) := by
    refine ⟨ twoStageS1_computable c, ?_, ?_, ?_ ⟩;
    · convert Primrec.to_comp ( primrec_list_drop.comp ( Primrec.fst ) ( Primrec.fst.comp (
        Primrec.unpair.comp ( Primrec.snd ) ) ) ) using 1;
    · exact Computable.fst.comp ( Computable.unpair.comp ( Computable.snd ) );
    · exact Computable.snd.comp ( Computable.unpair.comp ( Computable.snd ) );
  have h_comp : Computable (fun p : BitString × ℕ => (twoStageS1 c p.1 p.2).bind (fun x =>
    (Code.evaln p.2.unpair.2 c (Encodable.encode (p.1.drop p.2.unpair.1,
      ctx x p.2.unpair.1))).bind (fun e => (Encodable.decode e : Option BitString)))) := by
    apply Computable.option_bind h_comp.1;
    apply Computable.option_bind;
    · convert evaln_fixed_computable c |> Computable.comp <| Computable.pair (
        h_comp.2.2.2.comp <| Computable.fst ) ( Computable.encode.comp <| Computable.pair (
            h_comp.2.1.comp <| Computable.fst ) <| hctx.comp <| Computable.pair (
                Computable.snd ) <| h_comp.2.2.1.comp <| Computable.fst ) using 1;
    · exact Computable.decode.comp ( Computable.snd );
  exact h_comp

/-! ### Computability of the context encoders -/

/-- The unary code `natCode` is computable. -/
theorem natCode_computable : Computable natCode := by
  apply Primrec.to_comp
  exact Primrec.list_append.comp
    (Primrec.list_replicate.comp Primrec.id (Primrec.const true))
    (Primrec.const [false])

/-- The pair code is computable in both components. -/
theorem pairCode_computable :
    Computable (fun p : BitString × BitString => pairCode p.1 p.2) := by
  have h : (fun p : BitString × BitString => pairCode p.1 p.2)
      = fun p => natCode p.1.length ++ p.1 ++ p.2 := rfl
  rw [h]
  exact Computable.list_append.comp
    (Computable.list_append.comp
      (natCode_computable.comp (Computable.list_length.comp Computable.fst))
      Computable.fst)
    Computable.snd

/-
`twoStagePairOut` is computable, provided the context map is computable.
-/
theorem twoStagePairOut_computable (c : Code) (ctx : BitString → Nat → BitString)
    (hctx : Computable (fun p : BitString × ℕ => ctx p.1 p.2)) :
    Computable (fun p : BitString × ℕ => twoStagePairOut c ctx p.1 p.2) := by
  have h_twoStageS2_computable : Computable (fun p : BitString × ℕ => twoStageS2 c ctx p.1 p.2) :=
    twoStageS2_computable c ctx hctx
  have h_twoStageS1_computable : Computable (fun p : BitString × ℕ => twoStageS1 c p.1 p.2) :=
    twoStageS1_computable c
  convert Computable.option_bind h_twoStageS1_computable _ using 1;
  have h_pairCode_computable : Computable₂ (fun (x y : BitString) => pairCode x y) :=
    pairCode_computable
  convert Computable.option_map _ _ using 1;
  · exact inferInstance
  · exact h_twoStageS2_computable.comp ( Computable.fst );
  · exact h_pairCode_computable.comp ( Computable.snd.comp Computable.fst ) Computable.snd

/-
`twoStageCheck` is computable, provided the context map is computable.
-/
theorem twoStageCheck_computable (c : Code) (ctx : BitString → Nat → BitString)
    (hctx : Computable (fun p : BitString × ℕ => ctx p.1 p.2)) :
    Computable (fun p : BitString × ℕ => twoStageCheck c ctx p.1 p.2) := by
  -- The first part of `twoStageCheck` is computable: `n.unpair.1 ≤ w.length`.
  have h1 : Computable (fun p : BitString × ℕ => decide (p.2.unpair.1 ≤ p.1.length)) := by
    have h1 : Computable (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
      obtain ⟨_, h⟩ := Primrec.nat_le
      exact Computable.of_eq h.to_comp (fun p => by congr)
    convert h1.comp ( Computable.fst.comp ( Computable.unpair.comp (
        Computable.snd ) ) |> Computable.pair <| Computable.list_length.comp (
            Computable.fst ) ) using 1;
  -- The second part of `twoStageCheck` is computable: `(twoStagePairOut c ctx w n).isSome`.
  have h2 : Computable (fun p : BitString × ℕ => (twoStagePairOut c ctx p.1 p.2).isSome) := by
    convert Primrec.to_comp ( Primrec.option_isSome )
        |> Computable.comp <| twoStagePairOut_computable c ctx hctx using 1;
  convert Computable.cond h1 h2 ( Computable.const false ) using 1;
  exact funext fun p => by
    unfold twoStageCheck
    cases decide (p.2.unpair.1 ≤ p.1.length) <;> rfl

/-
The explicit two-stage decompressor is partial recursive.
-/
theorem twoStageMap_partrec (c : Code) (ctx : BitString → Nat → BitString)
    (hctx : Computable (fun p : BitString × ℕ => ctx p.1 p.2)) :
    Partrec (twoStageMap c ctx) := by
  -- The function that takes a pair (w, r) and returns the result of the two-stage map is
  -- partial recursive.
  exact
    (Partrec.bind
      (Partrec.rfind (Computable.to₂ (twoStageCheck_computable c ctx hctx)).partrec₂)
      (Computable.ofOption (twoStagePairOut_computable c ctx hctx)).to₂).comp
        Computable.fst

/-
Soundness: any value produced by the explicit decompressor satisfies the
relational two-stage spec, provided `c` is a code for `U`.
-/
theorem twoStageMap_mem_imp_spec {U : Map} {ctx : BitString → Nat → BitString}
    {c : Code}
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a)))
    {w r z : BitString} (hz : z ∈ twoStageMap c ctx (w, r)) :
    twoStagePairSpec U ctx w z := by
  have evaln_produces {fuel a : ℕ} {input : BitString × BitString}
      {output : BitString}
      (ha_eval : Code.evaln fuel c (Encodable.encode input) = some a)
      (ha_dec : Encodable.decode a = some output) :
      produces U input.1 input.2 output := by
    have h_eval_sound := Nat.Partrec.Code.evaln_sound ha_eval
    rw [hc, Part.mem_bind_iff] at h_eval_sound
    obtain ⟨input', hinput, houtput⟩ := h_eval_sound
    rw [Part.mem_ofOption] at hinput
    have hinput_eq : input' = input := by
      apply Option.some.inj
      rw [← hinput, Encodable.encodek]
    subst input'
    rw [Part.mem_map_iff] at houtput
    obtain ⟨output', hmem, hencode⟩ := houtput
    have houtput_eq : output' = output := by
      apply Option.some.inj
      rw [← ha_dec, ← hencode, Encodable.encodek]
    subst output'
    exact hmem
  obtain ⟨n, hn_rfind, hn_z⟩ : ∃ n,
      n ∈ Nat.rfind (fun n => Part.some (twoStageCheck c ctx w n)) ∧
      z ∈ (↑(twoStagePairOut c ctx w n) : Part BitString) := by
    unfold twoStageMap at hz
    rw [Part.mem_bind_iff] at hz
    exact hz
  have hz1 : twoStagePairOut c ctx w n = some z := Part.mem_ofOption.mp hn_z
  unfold twoStagePairOut at hz1
  rw [Option.bind_eq_some_iff] at hz1
  obtain ⟨x, hx_some, hy_rest⟩ := hz1
  cases h_y : twoStageS2 c ctx w n with
  | none => simp [h_y] at hy_rest
  | some y =>
    simp [h_y] at hy_rest
    have hz_eq : z = pairCode x y := hy_rest.symm
    refine ⟨w.take n.unpair.1, w.drop n.unpair.1, x, y, ?_, ?_, ?_, ?_⟩
    · exact (List.take_append_drop _ _).symm
    · unfold twoStageS1 at hx_some
      rw [Option.bind_eq_some_iff] at hx_some
      obtain ⟨a, ha_eval, ha_dec⟩ := hx_some
      exact evaln_produces ha_eval ha_dec
    · rw [List.length_take, min_eq_left]
      · unfold twoStageS2 at h_y
        rw [hx_some] at h_y
        simp only [Option.bind_some] at h_y
        rw [Option.bind_eq_some_iff] at h_y
        obtain ⟨a, ha_eval, ha_dec⟩ := h_y
        exact evaln_produces ha_eval ha_dec
      · have h_mem := (Nat.mem_rfind.mp hn_rfind).1
        unfold twoStageCheck at h_mem
        rw [Part.mem_some_iff, eq_comm, Bool.and_eq_true] at h_mem
        exact of_decide_eq_true h_mem.1
    · exact hz_eq

/-
Completeness: the explicit decompressor halts whenever the relational spec
is satisfiable, provided `c` is a code for `U`.
-/
theorem twoStageMap_dom_of_spec {U : Map} {ctx : BitString → Nat → BitString}
    {c : Code}
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a)))
    {w r z : BitString} (hz : twoStagePairSpec U ctx w z) :
    (twoStageMap c ctx (w, r)).Dom := by
  obtain ⟨p, q, x, y, hw, hx, hy, -⟩ := hz
  subst hw
  -- Both stages halt, so there is a common fuel for which the search succeeds.
  have h1mem : Encodable.encode x ∈ c.eval (Encodable.encode (p, ([] : BitString))) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(p, ([] : BitString)), by simp [Encodable.encodek],
      Part.mem_map Encodable.encode hx⟩
  obtain ⟨t1, ht1⟩ : ∃ t1, Code.evaln t1 c (Encodable.encode (p, ([] : BitString)))
      = some (Encodable.encode x) := by
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h1mem
    exact ⟨k, Option.mem_def.mp hk⟩
  have h2mem : Encodable.encode y ∈ c.eval (Encodable.encode (q, ctx x p.length)) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(q, ctx x p.length), by simp [Encodable.encodek],
      Part.mem_map Encodable.encode hy⟩
  obtain ⟨t2, ht2⟩ : ∃ t2, Code.evaln t2 c (Encodable.encode (q, ctx x p.length))
      = some (Encodable.encode y) := by
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h2mem
    exact ⟨k, Option.mem_def.mp hk⟩
  have ht1' : Code.evaln (max t1 t2) c (Encodable.encode (p, ([] : BitString)))
      = some (Encodable.encode x) :=
    Nat.Partrec.Code.evaln_mono (le_max_left t1 t2) ht1
  have ht2' : Code.evaln (max t1 t2) c (Encodable.encode (q, ctx x p.length))
      = some (Encodable.encode y) :=
    Nat.Partrec.Code.evaln_mono (le_max_right t1 t2) ht2
  -- The concrete search index `⟨p.length, max t1 t2⟩` passes every check.
  have hs1 : twoStageS1 c (p ++ q) (Nat.pair p.length (max t1 t2)) = some x := by
    unfold twoStageS1
    simp only [Nat.unpair_pair, List.take_left, ht1', Option.bind_some, Encodable.encodek]
  have hs2 : twoStageS2 c ctx (p ++ q) (Nat.pair p.length (max t1 t2)) = some y := by
    unfold twoStageS2
    rw [hs1]
    simp only [Nat.unpair_pair, List.drop_left, Option.bind_some, ht2', Encodable.encodek]
  have hpair : twoStagePairOut c ctx (p ++ q) (Nat.pair p.length (max t1 t2))
      = some (pairCode x y) := by
    unfold twoStagePairOut
    rw [hs1, hs2]; rfl
  have hcheck : twoStageCheck c ctx (p ++ q) (Nat.pair p.length (max t1 t2)) = true := by
    unfold twoStageCheck
    rw [hpair]
    simp only [Nat.unpair_pair, Option.isSome_some, Bool.and_true, decide_eq_true_eq,
      List.length_append]
    omega
  -- The dovetailing search therefore halts, and at its witness the output exists.
  have hrdom : (Nat.rfind (fun m => Part.some (twoStageCheck c ctx (p ++ q) m))).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨Nat.pair p.length (max t1 t2), by rw [Part.mem_some_iff, hcheck],
      fun {m} _ => Part.some_dom _⟩
  obtain ⟨n', hn'⟩ := Part.dom_iff_mem.mp hrdom
  have hcheck' : twoStageCheck c ctx (p ++ q) n' = true := by
    have h := (Nat.mem_rfind.mp hn').1
    rw [Part.mem_some_iff] at h
    exact h.symm
  have hsome : (twoStagePairOut c ctx (p ++ q) n').isSome = true := by
    unfold twoStageCheck at hcheck'
    exact ((Bool.and_eq_true _ _).mp hcheck').2
  obtain ⟨z'', hz''⟩ := Option.isSome_iff_exists.mp hsome
  refine Part.dom_iff_mem.mpr ⟨z'', ?_⟩
  unfold twoStageMap
  rw [Part.mem_bind_iff]
  exact ⟨n', hn', by rw [Part.mem_ofOption]; exact Option.mem_def.mpr hz''⟩

/-- The explicit decompressor equals the relational builder, for a code `c` of a
prefix machine `U`. -/
theorem twoStagePairBuilder_eq_twoStageMap {U : Map}
    {ctx : BitString → Nat → BitString} (hU : IsPrefixMachine U) {c : Code}
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a))) :
    twoStagePairBuilder U ctx = twoStageMap c ctx := by
  funext pr
  obtain ⟨w, r⟩ := pr
  apply Part.ext
  intro z
  rw [mem_twoStagePairBuilder_iff hU]
  constructor
  · intro hz
    -- spec holds; the explicit map halts and, by uniqueness, produces `z`.
    have hdom := twoStageMap_dom_of_spec (U := U) (ctx := ctx) hc (r := r) hz
    obtain ⟨z', hz'⟩ := Part.dom_iff_mem.mp hdom
    have hspec' := twoStageMap_mem_imp_spec (U := U) (ctx := ctx) hc hz'
    have : z' = z := twoStagePairSpec_unique hU hspec' hz
    rwa [this] at hz'
  · intro hz
    exact twoStageMap_mem_imp_spec (U := U) (ctx := ctx) hc hz

/-- **Main computability result.** The relational two-stage builder is a genuine
decompressor (partial recursive), provided `U` is a partial recursive prefix
machine and the context map is computable. -/
theorem twoStagePairBuilder_isDecompressor {U : Map}
    {ctx : BitString → Nat → BitString}
    (hUp : isDecompressor U) (hU : IsPrefixMachine U)
    (hctx : Computable (fun p : BitString × ℕ => ctx p.1 p.2)) :
    isDecompressor (twoStagePairBuilder U ctx) := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hUp
  rw [twoStagePairBuilder_eq_twoStageMap hU hc]
  exact twoStageMap_partrec c ctx hctx

/-- The relational two-stage builder is a prefix decompressor. -/
theorem twoStagePairBuilder_isPrefixDecompressor {U : Map}
    {ctx : BitString → Nat → BitString}
    (hUp : isDecompressor U) (hU : IsPrefixMachine U)
    (hctx : Computable (fun p : BitString × ℕ => ctx p.1 p.2)) :
    IsPrefixDecompressor (twoStagePairBuilder U ctx) :=
  ⟨twoStagePairBuilder_isDecompressor hUp hU hctx,
    twoStagePairBuilder_isPrefixMachine hU⟩

end Kolmogorov
