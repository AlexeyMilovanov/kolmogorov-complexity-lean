import KolmogorovMathlib.Prefix.TwoStage

namespace Kolmogorov

open Nat.Partrec (Code)

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
    (ctx : BitString → BitString → Nat → BitString) : Map := fun pr =>
  Part.mk (∃ z, condTwoStagePairSpec U ctx pr.1 pr.2 z) (fun h => Classical.choose h)

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
    (fun h => Classical.choose h)
  rw [Part.mem_mk_iff]
  refine ⟨⟨z, hz⟩, ?_⟩
  exact (condTwoStagePairSpec_unique hU (Classical.choose_spec ⟨z, hz⟩) hz)

/-- Membership in the relational builder is exactly the spec, given prefix-freeness. -/
theorem mem_condTwoStagePairBuilder_iff {U : Map} {ctx : BitString → BitString → Nat → BitString}
    (hU : IsPrefixMachine U) {w r z : BitString} :
    z ∈ condTwoStagePairBuilder U ctx (w, r) ↔ condTwoStagePairSpec U ctx w r z := by
  constructor
  · intro hz
    change z ∈ Part.mk (∃ z', condTwoStagePairSpec U ctx w r z') (fun h => Classical.choose h) at hz
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
    (fun e => (Encodable.decode e : Option BitString))

/-- Stage-2 output option: decode `U(drop i w, ctx x i)` run with fuel `t`,
where `x` is the stage-1 output. -/
def condTwoStageS2 (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (w r : BitString) (n : ℕ) : Option BitString :=
  (condTwoStageS1 c w r n).bind (fun x =>
    (Code.evaln n.unpair.2 c (Encodable.encode (w.drop n.unpair.1, ctx r x n.unpair.1))).bind
      (fun e => (Encodable.decode e : Option BitString)))

/-- The candidate pair output for search index `n`. -/
def condTwoStagePairOut (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (w r : BitString) (n : ℕ) : Option BitString :=
  (condTwoStageS1 c w r n).bind (fun x =>
    (condTwoStageS2 c ctx w r n).map (fun y => pairCode x y))

/-- The dovetailing check predicate: the split index is within range and both
stages have produced an output at fuel `t`. -/
def condTwoStageCheck (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (w r : BitString) (n : ℕ) : Bool :=
  decide (n.unpair.1 ≤ w.length) && (condTwoStagePairOut c ctx w r n).isSome

/-- The explicit computable two-stage decompressor. -/
def condTwoStageMap (c : Code) (ctx : BitString → BitString → Nat → BitString) : Map := fun pr =>
  (Nat.rfind (fun n => Part.some (condTwoStageCheck c ctx pr.1 pr.2 n))).bind
    (fun n => (↑(condTwoStagePairOut c ctx pr.1 pr.2 n) : Part BitString))

/-
`condTwoStageS1` as a function of the pair `(w, n)` is computable.
-/
theorem condTwoStageS1_computable (c : Code) :
    Computable (fun p : (BitString × BitString) × ℕ => condTwoStageS1 c p.1.1 p.1.2 p.2) := by
  have h_evaln_computable : Computable₂ (fun (n : ℕ) (m : ℕ) => Code.evaln n c m) :=
    evaln_fixed_computable c
  have h_take_computable : Computable₂ (fun (w : BitString) (n : ℕ) => w.take n) :=
    primrec_list_take.to_comp
  convert Computable.option_bind _ _ using 1;
  · exact inferInstance
  · convert h_evaln_computable.comp
      ( Computable.snd.comp ( Computable.unpair.comp Computable.snd ) )
          ( Computable.encode.comp ( h_take_computable.comp (Computable.fst.comp Computable.fst)
                                     ( Computable.fst.comp ( Computable.unpair.comp Computable.snd
                                                             ) ) |> Computable.pair <|
                                                                 Computable.snd.comp Computable.fst
                                                                     ) ) using 1;
  · exact Computable.decode.comp Computable.snd

/-
`condTwoStageS2` as a function of the pair `(w, n)` is computable, provided the
context map is computable.
-/
theorem condTwoStageS2_computable (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ => ctx p.1.1 p.1.2 p.2)) :
    Computable (fun p : (BitString × BitString) × ℕ => condTwoStageS2 c ctx p.1.1 p.1.2 p.2) := by
  have h_comp : Computable
      (fun p : (BitString × BitString) × ℕ => condTwoStageS1 c p.1.1 p.1.2 p.2) ∧ Computable
          (fun p : (BitString × BitString) × ℕ => p.1.1.drop p.2.unpair.1) ∧ Computable
              (fun p : (BitString × BitString) × ℕ => p.2.unpair.1) ∧ Computable
                  (fun p : (BitString × BitString) × ℕ => p.2.unpair.2) := by
    refine ⟨ condTwoStageS1_computable c, ?_, ?_, ?_ ⟩;
    · convert Primrec.to_comp
        ( primrec_list_drop.comp ( Primrec.fst.comp Primrec.fst ) ( Primrec.fst.comp
                                                                    ( Primrec.unpair.comp
                                                                        ( Primrec.snd )
                                                                            ) ) ) using 1;
    · exact Computable.fst.comp ( Computable.unpair.comp ( Computable.snd ) );
    · exact Computable.snd.comp ( Computable.unpair.comp ( Computable.snd ) );
  have h_comp : Computable
      (fun p : (BitString × BitString) × ℕ =>
        (condTwoStageS1 c p.1.1 p.1.2 p.2).bind (fun x =>
          (Code.evaln p.2.unpair.2 c
            (Encodable.encode (p.1.1.drop p.2.unpair.1, ctx p.1.2 x p.2.unpair.1))).bind
              (fun e => (Encodable.decode e : Option BitString)))) := by
    apply Computable.option_bind h_comp.1;
    apply Computable.option_bind;
    · convert evaln_fixed_computable c |> Computable.comp <| Computable.pair
        ( h_comp.2.2.2.comp <| Computable.fst )
            ( Computable.encode.comp <| Computable.pair ( h_comp.2.1.comp <| Computable.fst ) <|
                hctx.comp <| Computable.pair
                    (Computable.pair (Computable.snd.comp (Computable.fst.comp Computable.fst))
                        Computable.snd) (h_comp.2.2.1.comp <| Computable.fst) ) using 1;
    · exact Computable.decode.comp ( Computable.snd );
  exact h_comp

/-
`condTwoStagePairOut` is computable, provided the context map is computable.
-/
theorem condTwoStagePairOut_computable (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ => ctx p.1.1 p.1.2 p.2)) :
    Computable (fun p : (BitString × BitString) × ℕ => condTwoStagePairOut c ctx p.1.1 p.1.2 p.2)
        := by
  have h_condTwoStageS2_computable : Computable
      (fun p : (BitString × BitString) × ℕ => condTwoStageS2 c ctx p.1.1 p.1.2 p.2) :=
    condTwoStageS2_computable c ctx hctx
  have h_condTwoStageS1_computable : Computable
      (fun p : (BitString × BitString) × ℕ => condTwoStageS1 c p.1.1 p.1.2 p.2) :=
    condTwoStageS1_computable c
  convert Computable.option_bind h_condTwoStageS1_computable _ using 1;
  have h_pairCode_computable : Computable₂ (fun (x y : BitString) => pairCode x y) :=
    pairCode_computable
  convert Computable.option_map _ _ using 1;
  · exact inferInstance
  · exact h_condTwoStageS2_computable.comp ( Computable.fst );
  · exact h_pairCode_computable.comp ( Computable.snd.comp Computable.fst ) Computable.snd

/-
`condTwoStageCheck` is computable, provided the context map is computable.
-/
theorem condTwoStageCheck_computable (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ => ctx p.1.1 p.1.2 p.2)) :
    Computable (fun p : (BitString × BitString) × ℕ => condTwoStageCheck c ctx p.1.1 p.1.2 p.2) :=
        by
  have h1 : Computable
      (fun p : (BitString × BitString) × ℕ => decide (p.2.unpair.1 ≤ p.1.1.length)) := by
    have h1 : Computable (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
      obtain ⟨_, h⟩ := Primrec.nat_le
      exact Computable.of_eq h.to_comp (fun p => by congr)
    convert h1.comp
        ( Computable.fst.comp ( Computable.unpair.comp ( Computable.snd ) ) |> Computable.pair <|
            Computable.list_length.comp ( Computable.fst.comp Computable.fst ) ) using 1;
  have h2 : Computable
      (fun p : (BitString × BitString) × ℕ => (condTwoStagePairOut c ctx p.1.1 p.1.2 p.2).isSome)
          := by
    convert Primrec.to_comp ( Primrec.option_isSome ) |> Computable.comp <|
        condTwoStagePairOut_computable c ctx hctx using 1;
  convert Computable.cond h1 h2 ( Computable.const false ) using 1;
  exact funext fun p => by
    unfold condTwoStageCheck
    cases decide (p.2.unpair.1 ≤ p.1.1.length) <;> rfl

/-
The explicit two-stage decompressor is partial recursive.
-/
theorem condTwoStageMap_partrec (c : Code) (ctx : BitString → BitString → Nat → BitString)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ => ctx p.1.1 p.1.2 p.2)) :
    Partrec (condTwoStageMap c ctx) := by
  exact Partrec.bind
    (Partrec.rfind (Computable.to₂ (condTwoStageCheck_computable c ctx hctx)).partrec₂)
    (Computable.ofOption (condTwoStagePairOut_computable c ctx hctx)).to₂

/-
Soundness: any value produced by the explicit decompressor satisfies the
relational two-stage spec, provided `c` is a code for `U`.
-/
theorem condTwoStageMap_mem_imp_spec {U : Map} {ctx : BitString → BitString → Nat → BitString}
    {c : Code}
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a)))
    {w r z : BitString} (hz : z ∈ condTwoStageMap c ctx (w, r)) :
    condTwoStagePairSpec U ctx w r z := by
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
      n ∈ Nat.rfind (fun n => Part.some (condTwoStageCheck c ctx w r n)) ∧
      z ∈ (↑(condTwoStagePairOut c ctx w r n) : Part BitString) := by
    unfold condTwoStageMap at hz
    rw [Part.mem_bind_iff] at hz
    exact hz
  have hz1 : condTwoStagePairOut c ctx w r n = some z := Part.mem_ofOption.mp hn_z
  unfold condTwoStagePairOut at hz1
  rw [Option.bind_eq_some_iff] at hz1
  obtain ⟨x, hx_some, hy_rest⟩ := hz1
  cases h_y : condTwoStageS2 c ctx w r n with
  | none => simp [h_y] at hy_rest
  | some y =>
    simp [h_y] at hy_rest
    have hz_eq : z = pairCode x y := hy_rest.symm
    refine ⟨w.take n.unpair.1, w.drop n.unpair.1, x, y, ?_, ?_, ?_, ?_⟩
    · exact (List.take_append_drop _ _).symm
    · unfold condTwoStageS1 at hx_some
      rw [Option.bind_eq_some_iff] at hx_some
      obtain ⟨a, ha_eval, ha_dec⟩ := hx_some
      exact evaln_produces ha_eval ha_dec
    · rw [List.length_take, min_eq_left]
      · unfold condTwoStageS2 at h_y
        rw [hx_some] at h_y
        simp only [Option.bind_some] at h_y
        rw [Option.bind_eq_some_iff] at h_y
        obtain ⟨a, ha_eval, ha_dec⟩ := h_y
        exact evaln_produces ha_eval ha_dec
      · have h_mem := (Nat.mem_rfind.mp hn_rfind).1
        unfold condTwoStageCheck at h_mem
        rw [Part.mem_some_iff, eq_comm, Bool.and_eq_true] at h_mem
        exact of_decide_eq_true h_mem.1
    · exact hz_eq

theorem condTwoStageMap_dom_of_spec {U : Map} {ctx : BitString → BitString → Nat → BitString}
    {c : Code}
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a)))
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
  have hrdom : (Nat.rfind (fun m => Part.some (condTwoStageCheck c ctx (p ++ q) r m))).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨Nat.pair p.length (max t1 t2), by rw [Part.mem_some_iff, hcheck],
      fun {m} _ => Part.some_dom _⟩
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
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a))) :
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
    (hctx : Computable (fun p : (BitString × BitString) × ℕ => ctx p.1.1 p.1.2 p.2)) :
    isDecompressor (condTwoStagePairBuilder U ctx) := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hUp
  rw [condTwoStagePairBuilder_eq_condTwoStageMap hU hc]
  exact condTwoStageMap_partrec c ctx hctx

/-- The relational two-stage builder is a prefix decompressor. -/
theorem condTwoStagePairBuilder_isPrefixDecompressor {U : Map}
    {ctx : BitString → BitString → Nat → BitString}
    (hUp : isDecompressor U) (hU : IsPrefixMachine U)
    (hctx : Computable (fun p : (BitString × BitString) × ℕ => ctx p.1.1 p.1.2 p.2)) :
    IsPrefixDecompressor (condTwoStagePairBuilder U ctx) :=
  ⟨condTwoStagePairBuilder_isDecompressor hUp hU hctx,
    condTwoStagePairBuilder_isPrefixMachine hU⟩

end Kolmogorov
