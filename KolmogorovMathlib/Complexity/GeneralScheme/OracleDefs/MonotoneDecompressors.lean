import KolmogorovMathlib.Complexity.GeneralScheme.Decision
import KolmogorovMathlib.Oracle.Basic
import KolmogorovMathlib.Oracle.Universal.Optimal
import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasure
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import KolmogorovMathlib.MonotoneComplexity.StreamGapFill
import KolmogorovMathlib.MonotoneComplexity.Omega.PredictCover
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun

/-!
# Monotone Decompressors

Oracle-relative versions of the decision and monotone decompressors used by the general scheme
of Section 6.4 of the book by Shen, Uspensky and Vereshchagin.  The module defines the halting set
`jumpSet` (the book's `0'`), the characteristic sequence `charSeq` of a set, decision
decompressors `DecisionDecompressorIn A` enumerable relative to an oracle `A`, computable stream
maps and optimal monotone decompressors relative to `A`, and (lower semicomputable) continuous
semimeasures relative to `A`.

The main results are the existence of optimal relativized decompressors:
`exists_isOptimalConditionalIn` (plain conditional complexity),
`exists_optimal_decisionDecompressorIn` (decision complexity) and
`exists_isOptimalMonotoneDecompressorIn` (monotone complexity).  Each is obtained by relativizing
the unrelativized construction with the universal oracle machine.
-/

open scoped ENNReal

namespace Kolmogorov

namespace GeneralScheme

open Nat.Partrec (Code)

/-- The halting set `0' = {e | φ_e(e) halts}`. Its characteristic oracle is the library's
`haltingOracle`. -/
def jumpSet : Set ℕ :=
  {e : ℕ | ((Denumerable.ofNat Code e).eval e).Dom}

/-- **SUV Section 6.4.1 (printed p. 203), helper.** The characteristic oracle of `jumpSet` is the
library's `haltingOracle`, the book's `0'` (both are `charOracle` of the same set, by
definition). -/
theorem charOracle_jumpSet : charOracle jumpSet = haltingOracle :=
  rfl

open Classical in
/-- The characteristic sequence of a set of naturals. -/
noncomputable def charSeq (A : Set ℕ) : CantorSeq :=
  fun i => decide (i ∈ A)

/-- Decision decompressors relative to an oracle `A`: the same as `DecisionDecompressor`, with
enumerability relative to `A`. -/
structure DecisionDecompressorIn (A : Set ℕ) where
  /-- `rel p x`: the output on input `p` starts with `x`. -/
  rel : BitString → BitString → Prop
  /-- The set of pairs `(p, x)` is enumerable relative to `A`. -/
  re : PointToSet.IsREIn A (fun q : BitString × BitString => rel q.1 q.2)
  /-- Every output starts with the empty string. -/
  nil_mem : ∀ p, rel p []
  /-- Closure under prefixes of the object. -/
  prefix_closed : ∀ ⦃p x x' : BitString⦄, rel p x → x' <+: x → rel p x'
  /-- `=`-`≍`-regularity. -/
  regular : IsRegular .eq .compat rel

/-- `KR^A_M(x)`: the least length of an input whose output starts with `x`. -/
noncomputable def KRInOf {A : Set ℕ} (M : DecisionDecompressorIn A) (x : BitString) : ℕ∞ :=
  modeComplexity M.rel x

/-- An optimal `A`-decision decompressor. -/
def DecisionDecompressorIn.IsOptimal {A : Set ℕ} (R : DecisionDecompressorIn A) : Prop :=
  ∀ M : DecisionDecompressorIn A, ∃ c : ℕ, ∀ x, KRInOf R x ≤ KRInOf M x + c

/-- A computable continuous stream map relative to `A`: its lower graph is `A`-enumerable. -/
def IsComputableStreamMapIn (A : Set ℕ) (f : BitStream → BitStream) : Prop :=
  IsContinuousStreamMap f ∧
    PointToSet.IsREIn A (fun p : BitString × BitString => streamLowerGraph f p.1 p.2)

/-- An optimal monotone decompressor relative to `A`. -/
def IsOptimalMonotoneDecompressorIn (A : Set ℕ) (D : BitStream → BitStream) : Prop :=
  IsComputableStreamMapIn A D ∧
    ∀ D', IsComputableStreamMapIn A D' → ∃ c : ℕ, ∀ x, KMOf D x ≤ KMOf D' x + c

/-- An `A`-lower-semicomputable continuous semimeasure on the binary tree. Its values are at most
`a [] = 1`, so `toReal` loses nothing. -/
def IsLSCContinuousSemimeasureIn (A : Set ℕ) (a : BitString → ℝ≥0∞) : Prop :=
  IsContinuousTreeSemimeasure a ∧ PointToSet.IsLowerSemicomputableIn A (fun x => (a x).toReal)

/-- A maximal `A`-lower-semicomputable continuous semimeasure (the relativized a priori
probability). -/
def IsMaximalContinuousSemimeasureIn (A : Set ℕ) (a : BitString → ℝ≥0∞) : Prop :=
  IsLSCContinuousSemimeasureIn A a ∧
    ∀ a', IsLSCContinuousSemimeasureIn A a' → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ x, a' x ≤ c * a x

/-- A priori complexity defined by a semimeasure `a`: `-log₂ a(x)`. For the maximal
`A`-semimeasure this is `KA^A`. The formula is that of `KA`. -/
noncomputable def KAOf (a : BitString → ℝ≥0∞) (x : BitString) : ℝ :=
  - Real.logb 2 (a x).toReal

/-- The universal `A`-decompressor: the tagged union of the evaluators `oracleEval A e`. -/
private noncomputable def exists_isOptimalConditionalIn_univ (A : Set ℕ) : Map :=
  taggedUnion fun e pr =>
    (PointToSet.oracleEval A e (Encodable.encode pr)).map
      (fun r => (Encodable.decode r : Option BitString).getD [])

/-- Parsing the unary tag preserves relative partial computability. -/
private lemma exists_isOptimalConditionalIn_partrec_tagged
    {O : Set (ℕ →. ℕ)} {M : ℕ → Map} (hM : PartrecIn₂ O M) :
    PartrecIn O (taggedUnion M) := by
  have hidx : Primrec (fun pr : BitString × BitString =>
      (pr.1.takeWhile id).length) :=
    (Primrec.list_findIdx Primrec.fst (Primrec.not.comp Primrec.snd).to₂).of_eq
      (fun pr => (takeWhile_id_length_eq_findIdx pr.1).symm)
  have hdrop : Primrec (fun pr : BitString × BitString =>
      pr.1.drop ((pr.1.takeWhile id).length + 1)) :=
    list_drop_primrec.comp Primrec.fst (Primrec.succ.comp hidx)
  have hguard : Computable (fun pr : BitString × BitString =>
      decide ((pr.1.takeWhile id).length < pr.1.length)) :=
    primrec_decide_nat_lt.to_comp.comp
      (hidx.to_comp.pair (Primrec.list_length.comp Primrec.fst).to_comp)
  have hargs : Computable (fun pr : BitString × BitString =>
      ((pr.1.takeWhile id).length,
        (pr.1.drop ((pr.1.takeWhile id).length + 1), pr.2))) :=
    hidx.to_comp.pair (hdrop.to_comp.pair Computable.snd)
  refine (PartrecIn.cond hguard.computableIn (PartrecIn.comp hM hargs.computableIn)
    PartrecIn.none).of_eq fun pr => ?_
  simp only [taggedUnion]
  by_cases h : (pr.1.takeWhile id).length < pr.1.length <;> simp [h]

/-- The universal `A`-decompressor is `A`-recursive. -/
private lemma exists_isOptimalConditionalIn_decomp (A : Set ℕ) :
    IsDecompressorIn (charOracle A) (exists_isOptimalConditionalIn_univ A) := by
  have hM : PartrecIn {charOracle A} (exists_isOptimalConditionalIn_univ A) := by
    apply exists_isOptimalConditionalIn_partrec_tagged
    have hargs : Computable (fun t : ℕ × (BitString × BitString) =>
        (t.1, Encodable.encode t.2)) :=
      Computable.fst.pair (Computable.encode.comp Computable.snd)
    have hev := (PointToSet.oracleStage_evaluator A).comp hargs.computableIn
    have hdecode' : ComputableIn₂ {charOracle A}
        (fun (_ : ℕ × (BitString × BitString)) (r : ℕ) =>
          (Encodable.decode r : Option BitString).getD []) :=
      ((Computable.option_getD Computable.decode (Computable.const [])).comp
        Computable.snd).computableIn.to₂
    exact (PartrecIn.map hev hdecode')
  unfold IsDecompressorIn mapToNatFun
  have hd : Computable (fun n => Encodable.decode (α := BitString × BitString) n) :=
    Computable.decode
  have hopt := (Computable.ofOption hd).partrecIn (O := {charOracle A})
  have hmap : PartrecIn₂ {charOracle A} (fun (_ : ℕ) (a : BitString × BitString) =>
      (exists_isOptimalConditionalIn_univ A a).map Encodable.encode) :=
    PartrecIn.map (hM.comp ComputableIn.snd)
      (Computable.encode.comp Computable.snd).computableIn.to₂
  exact RecursiveIn.iff_nat.mpr (PartrecIn.iff_nat.mp (PartrecIn.bind hopt hmap))

/-- Every `A`-recursive decompressor is evaluated by some index `e`. -/
private lemma exists_isOptimalConditionalIn_eval
    (A : Set ℕ) (M : Map) (hM : IsDecompressorIn (charOracle A) M) :
    ∃ e : ℕ, ∀ n : ℕ, PointToSet.oracleEval A e n = mapToNatFun M n := by
  have h_partrec : PartrecIn {charOracle A} (mapToNatFun M) := hM
  obtain ⟨e, he⟩ := PointToSet.oracleStage_universal A (mapToNatFun M) h_partrec
  refine ⟨e, fun n => ?_⟩
  apply Part.ext
  intro v
  change v ∈ Nat.rfindOpt (fun t => PointToSet.oracleStage A t e n) ↔
    v ∈ mapToNatFun M n
  have hmono : ∀ {a t s : ℕ}, t ≤ s →
      a ∈ PointToSet.oracleStage A t e n → a ∈ PointToSet.oracleStage A s e n := by
    intro a t s hts ha
    exact Option.mem_def.mpr
      (PointToSet.oracleStage_persistent A e n a t s hts (Option.mem_def.mp ha))
  have hs : v ∈ Nat.rfindOpt (fun t => PointToSet.oracleStage A t e n) ↔
      ∃ t, PointToSet.oracleStage A t e n = some v := by
    simpa only [Option.mem_def] using (Nat.rfindOpt_mono hmono (a := v))
  exact hs.trans (he n v).symm

/-- **SUV Section 6.4.1 (printed p. 203), unnumbered.** Relativization of the invariance
theorem: for every oracle there is an optimal `A`-decompressor (plain conditional complexity).

Proof idea: the proof of `exists_isOptimalConditional` relativizes, using the universal oracle
machine `PointToSet.oracleEval`. -/
theorem exists_isOptimalConditionalIn (A : Set ℕ) :
    ∃ U : Map, IsOptimalConditionalIn (charOracle A) U := by
  refine ⟨exists_isOptimalConditionalIn_univ A, exists_isOptimalConditionalIn_decomp A, ?_⟩
  intro D hD
  obtain ⟨e, he⟩ := exists_isOptimalConditionalIn_eval A D hD
  refine ⟨e + 1, fun x y => ?_⟩
  apply sInfLeSInfAdd
  rintro len_p ⟨p, hp_out, rfl⟩
  refine ⟨(programLength (natCode e ++ p) : ENat), ?_, ?_⟩
  · refine ⟨natCode e ++ p, ?_, rfl⟩
    apply taggedUnion_produces_natCode (i := e)
    change x ∈ (PointToSet.oracleEval A e (Encodable.encode (p, y))).map
      (fun r => (Encodable.decode r : Option BitString).getD [])
    rw [he (Encodable.encode (p, y))]
    have : x ∈ D (p, y) := hp_out
    simp only [mapToNatFun, Encodable.encodek, Part.ofOption, Part.bind_some]
    simp only [Part.mem_map_iff]
    exact ⟨Encodable.encode x, ⟨x, this, rfl⟩, by simp⟩
  · dsimp [programLength]
    rw [List.length_append, length_natCode]
    push_cast
    rw [add_comm]

/-- The `s`-th element of the `A`-enumeration of index `e` of a set of pairs of bit strings:
the pair with code `n` when stage `t` of the oracle machine `e` succeeds on `n`, where
`(n, t) = Nat.unpair s`. -/
private noncomputable def exists_optimal_decisionDecompressorIn_enum
    (A : Set ℕ) (e s : ℕ) : Option (BitString × BitString) :=
  cond (PointToSet.oracleStage A (Nat.unpair s).2 e (Nat.unpair s).1).isSome
    (Encodable.decode (Nat.unpair s).1) none

private theorem exists_optimal_decisionDecompressorIn_enum_computable (A : Set ℕ) :
    ComputableIn {charOracle A}
      (fun p : ℕ × ℕ => exists_optimal_decisionDecompressorIn_enum A p.1 p.2) := by
  have hunpair : ComputableIn {charOracle A} (fun p : ℕ × ℕ => Nat.unpair p.2) :=
    Computable.unpair.computableIn.comp ComputableIn.snd
  have h1 : ComputableIn {charOracle A} (fun p : ℕ × ℕ => (Nat.unpair p.2).2) :=
    ComputableIn.snd.comp hunpair
  have h2 : ComputableIn {charOracle A} (fun p : ℕ × ℕ => (Nat.unpair p.2).1) :=
    ComputableIn.fst.comp hunpair
  have h3 : ComputableIn {charOracle A} (fun p : ℕ × ℕ => (p.1, (Nat.unpair p.2).1)) :=
    ComputableIn.fst.pair h2
  have h4 : ComputableIn {charOracle A}
      (fun p : ℕ × ℕ => ((Nat.unpair p.2).2, (p.1, (Nat.unpair p.2).1))) :=
    h1.pair h3
  have hstage : ComputableIn {charOracle A}
      (fun p : ℕ × ℕ =>
        PointToSet.oracleStage A (Nat.unpair p.2).2 p.1 (Nat.unpair p.2).1) :=
    (PointToSet.oracleStage_computable A).comp h4
  have hisSome : Computable (Option.isSome (α := ℕ)) := Primrec.option_isSome.to_comp
  have hselect : Computable (fun p : Bool × ℕ =>
      cond p.1 (Encodable.decode (α := BitString × BitString) p.2) none) :=
    Computable.cond Computable.fst (Computable.decode.comp Computable.snd)
      (Computable.const none)
  have h5 : ComputableIn {charOracle A}
      (fun p : ℕ × ℕ =>
        (Option.isSome (PointToSet.oracleStage A (Nat.unpair p.2).2 p.1 (Nat.unpair p.2).1))) :=
    hisSome.computableIn.comp hstage
  have h6 : ComputableIn {charOracle A}
      (fun p : ℕ × ℕ =>
        ((Option.isSome (PointToSet.oracleStage A (Nat.unpair p.2).2 p.1 (Nat.unpair p.2).1)),
          (Nat.unpair p.2).1)) := h5.pair h2
  have h7 := hselect.computableIn (O := {charOracle A}) |>.comp h6
  exact h7.of_eq fun p => rfl

/-- Every `A`-enumerable set of pairs of bit strings is enumerated by some index. -/
private theorem exists_optimal_decisionDecompressorIn_enum_universal (A : Set ℕ)
    (F : BitString × BitString → Prop) (hF : PointToSet.IsREIn A F) :
    ∃ e : ℕ, ∀ w, F w ↔ ∃ s, exists_optimal_decisionDecompressorIn_enum A e s = some w := by
  obtain ⟨f, hf, hFdom⟩ := hF
  let g : ℕ →. ℕ := fun n =>
    (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
      fun w => (f w).map fun _ => 0
  have hg : PartrecIn {charOracle A} g :=
    PartrecIn.bind (Partrec.partrecIn (Computable.ofOption Computable.decode))
      (PartrecIn.map (PartrecIn.comp hf ComputableIn.snd) (ComputableIn.const 0))
  obtain ⟨e, he⟩ := PointToSet.oracleStage_universal A g hg
  refine ⟨e, fun w => ⟨fun hw => ?_, fun ⟨s, hs⟩ => ?_⟩⟩
  · have hdom : (f w).Dom := (hFdom w).mp hw
    have hzero : 0 ∈ (f w).map fun _ => 0 := ⟨hdom, rfl⟩
    have hmem : 0 ∈ g (Encodable.encode w) :=
      Part.mem_bind_iff.mpr ⟨w, Part.mem_ofOption.mpr (Encodable.encodek w), hzero⟩
    obtain ⟨t, ht⟩ := (he _ 0).mp hmem
    exact ⟨Nat.pair (Encodable.encode w) t,
      by simp [exists_optimal_decisionDecompressorIn_enum, ht, Encodable.encodek]⟩
  · cases h : PointToSet.oracleStage A (Nat.unpair s).2 e (Nat.unpair s).1 with
    | none => simp [exists_optimal_decisionDecompressorIn_enum, h] at hs
    | some v =>
      have hdec : Encodable.decode (α := BitString × BitString) (Nat.unpair s).1 = some w := by
        simpa [exists_optimal_decisionDecompressorIn_enum, h] using hs
      obtain ⟨w', hw', hv⟩ := Part.mem_bind_iff.mp ((he _ v).mpr ⟨_, h⟩)
      have hww : w' = w := Option.some.inj ((Part.mem_ofOption.mp hw').symm.trans hdec)
      subst hww
      obtain ⟨hdom, _⟩ := hv
      exact (hFdom w').mpr hdom

/-- Bounded universal quantification over `List.range` of an oracle-computable test is
oracle-computable. -/
private theorem exists_optimal_decisionDecompressorIn_all_range_computable
    {α : Type*} [Primcodable α] (O : Set (ℕ →. ℕ)) (g : α → ℕ → Bool)
    (hg : ComputableIn O (fun p : α × ℕ => g p.1 p.2)) :
    ComputableIn O (fun p : α × ℕ => (List.range p.2).all (g p.1)) := by
  have hstep : ComputableIn₂ O (fun (a : α × ℕ) (r : ℕ × Bool) => r.2 && g a.1 r.1) := by
    refine ComputableIn₂.mk ?_
    have h1 : ComputableIn O (fun u : (α × ℕ) × (ℕ × Bool) => g u.1.1 u.2.1) :=
      hg.comp (ComputableIn.pair (ComputableIn.fst.comp ComputableIn.fst)
        (ComputableIn.fst.comp ComputableIn.snd))
    have h2 : ComputableIn O (fun u : (α × ℕ) × (ℕ × Bool) => u.2.2) :=
      ComputableIn.snd.comp ComputableIn.snd
    exact (Primrec.and.computableIn.comp (h2.pair h1))
  have hrec := ComputableIn.nat_rec (O := O) (f := fun a : α × ℕ => a.2)
    (g := fun _ => true) (h := fun (a : α × ℕ) (r : ℕ × Bool) => r.2 && g a.1 r.1)
    ComputableIn.snd (ComputableIn.const true) hstep
  refine hrec.of_eq fun a => ?_
  obtain ⟨a, n⟩ := a
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, ← ih]

/-- Compatibility of two bit strings (one is a prefix of the other), as a Boolean. -/
private def exists_optimal_decisionDecompressorIn_compat (y y' : BitString) : Bool :=
  decide (y.take y'.length = y') || decide (y'.take y.length = y)

/-- The trimming test of a stage: an enumerated pair `(p', y')` does not clash with `(p, y)`. -/
private def exists_optimal_decisionDecompressorIn_tst (p y : BitString)
    (o : Option (BitString × BitString)) : Bool :=
  match o with
  | none => true
  | some r => !decide (r.1 = p) || exists_optimal_decisionDecompressorIn_compat y r.2

/-- The trimmed, tagged relation as a Boolean check: `x = []`, or `q = natCode i ++ p`, the pair
`(p, y)` is the `s`-th element enumerated by index `i`, `x` is a prefix of `y`, and `y` is
compatible with every earlier enumerated `(p, y')`. -/
private noncomputable def exists_optimal_decisionDecompressorIn_chk (A : Set ℕ)
    (q x : BitString) (i : ℕ) (p : BitString) (s : ℕ) (y : BitString) : Bool :=
  decide (x = []) || (decide (q = natCode i ++ p) &&
    decide (exists_optimal_decisionDecompressorIn_enum A i s = some (p, y)) &&
    decide (x = y.take x.length) &&
    (List.range s).all (fun s' => exists_optimal_decisionDecompressorIn_tst p y
      (exists_optimal_decisionDecompressorIn_enum A i s')))

private abbrev exists_optimal_decisionDecompressorIn_DW :=
  (BitString × BitString) × (ℕ × BitString × ℕ × BitString)

private theorem exists_optimal_decisionDecompressorIn_compat_primrec :
    Primrec (fun u : BitString × BitString =>
      exists_optimal_decisionDecompressorIn_compat u.1 u.2) := by
  have h1 : Primrec (fun u : BitString × BitString => decide (u.1.take u.2.length = u.2)) :=
    primrec_decideEq.comp (Primrec.list_take.comp (Primrec.list_length.comp Primrec.snd)
      Primrec.fst) Primrec.snd
  have h2 : Primrec (fun u : BitString × BitString => decide (u.2.take u.1.length = u.1)) :=
    primrec_decideEq.comp (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst)
      Primrec.snd) Primrec.fst
  exact Primrec.or.comp h1 h2

private theorem exists_optimal_decisionDecompressorIn_tst_primrec :
    Primrec (fun t : (BitString × BitString) × Option (BitString × BitString) =>
      exists_optimal_decisionDecompressorIn_tst t.1.1 t.1.2 t.2) := by
  have hg : Primrec₂ (fun (t : (BitString × BitString) × Option (BitString × BitString))
      (r : BitString × BitString) =>
        !decide (r.1 = t.1.1) || exists_optimal_decisionDecompressorIn_compat t.1.2 r.2) := by
    have h1 : Primrec (fun u : ((BitString × BitString) × Option (BitString × BitString)) ×
        (BitString × BitString) => decide (u.2.1 = u.1.1.1)) :=
      primrec_decideEq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.fst.comp
        Primrec.fst))
    have h2 : Primrec (fun u : ((BitString × BitString) × Option (BitString × BitString)) ×
        (BitString × BitString) => exists_optimal_decisionDecompressorIn_compat u.1.1.2 u.2.2) :=
      exists_optimal_decisionDecompressorIn_compat_primrec.comp
        (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd))
    exact Primrec.or.comp (Primrec.not.comp h1) h2
  have := Primrec.option_casesOn
    (o := fun t : (BitString × BitString) × Option (BitString × BitString) => t.2)
    (f := fun _ => true)
    (g := fun t r => !decide (r.1 = t.1.1) || exists_optimal_decisionDecompressorIn_compat t.1.2
        r.2)
    Primrec.snd (Primrec.const true) hg
  refine this.of_eq fun t => ?_
  rcases t with ⟨⟨p, y⟩, _ | r⟩ <;> rfl

/-- The Boolean check `chk` is computable in the oracle `A`. -/
private theorem exists_optimal_decisionDecompressorIn_chk_computable (A : Set ℕ) :
    ComputableIn {charOracle A} (fun w : exists_optimal_decisionDecompressorIn_DW =>
      exists_optimal_decisionDecompressorIn_chk A w.1.1 w.1.2 w.2.1 w.2.2.1 w.2.2.2.1
        w.2.2.2.2) := by
  have hq : Primrec (fun w : exists_optimal_decisionDecompressorIn_DW => w.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun w : exists_optimal_decisionDecompressorIn_DW => w.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun w : exists_optimal_decisionDecompressorIn_DW => w.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun w : exists_optimal_decisionDecompressorIn_DW => w.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun w : exists_optimal_decisionDecompressorIn_DW => w.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hy : Primrec (fun w : exists_optimal_decisionDecompressorIn_DW => w.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have c1 : Primrec (fun w : exists_optimal_decisionDecompressorIn_DW => decide (w.1.2 = [])) :=
    primrec_decideEq.comp hx (Primrec.const [])
  have c2 : Primrec (fun w : exists_optimal_decisionDecompressorIn_DW =>
      decide (w.1.1 = natCode w.2.1 ++ w.2.2.1)) :=
    primrec_decideEq.comp hq (Primrec.list_append.comp (primrec_natCode.comp hi) hp)
  have c4 : Primrec (fun w : exists_optimal_decisionDecompressorIn_DW =>
      decide (w.1.2 = w.2.2.2.2.take w.1.2.length)) :=
    primrec_decideEq.comp hx (Primrec.list_take.comp (Primrec.list_length.comp hx) hy)
  have hi' : ComputableIn {charOracle A}
      (fun w : exists_optimal_decisionDecompressorIn_DW => w.2.1) := hi.to_comp.computableIn
  have hs' : ComputableIn {charOracle A}
      (fun w : exists_optimal_decisionDecompressorIn_DW => w.2.2.2.1) := hs.to_comp.computableIn
  have hpr := hi'.pair hs'
  have hE := (exists_optimal_decisionDecompressorIn_enum_computable A).comp hpr
  have hsome : Computable (fun w : exists_optimal_decisionDecompressorIn_DW =>
      some (w.2.2.1, w.2.2.2.2)) :=
    (Primrec.option_some.comp (hp.pair hy)).to_comp
  have hdec : Computable (fun u : Option (BitString × BitString) × Option (BitString × BitString) =>
      decide (u.1 = u.2)) := primrec_decideEq.to_comp
  have c3 := hdec.computableIn.comp (hE.pair hsome.computableIn)
  have hs'' : ComputableIn {charOracle A}
      (fun u : exists_optimal_decisionDecompressorIn_DW × ℕ => u.1.2.1) :=
    (hi.comp Primrec.fst).to_comp.computableIn
  have e1 := (exists_optimal_decisionDecompressorIn_enum_computable A).comp
    (hs''.pair ComputableIn.snd)
  have e2 : Primrec (fun u : exists_optimal_decisionDecompressorIn_DW × ℕ =>
      (u.1.2.2.1, u.1.2.2.2.2)) :=
    (hp.comp Primrec.fst).pair (hy.comp Primrec.fst)
  have hg0 := exists_optimal_decisionDecompressorIn_tst_primrec.to_comp.computableIn.comp
    (e2.to_comp.computableIn.pair e1)
  have hg : ComputableIn {charOracle A}
      (fun u : exists_optimal_decisionDecompressorIn_DW × ℕ =>
        exists_optimal_decisionDecompressorIn_tst u.1.2.2.1 u.1.2.2.2.2
          (exists_optimal_decisionDecompressorIn_enum A u.1.2.1 u.2)) := hg0
  have c5a := exists_optimal_decisionDecompressorIn_all_range_computable
    (α := exists_optimal_decisionDecompressorIn_DW) {charOracle A}
    (fun w s' => exists_optimal_decisionDecompressorIn_tst w.2.2.1 w.2.2.2.2
      (exists_optimal_decisionDecompressorIn_enum A w.2.1 s')) hg
  have c5 := c5a.comp (ComputableIn.id.pair hs')
  have h34 := Primrec.and.to_comp.computableIn (O := {charOracle A}) |>.comp
    (c3.pair (c4.to_comp.computableIn))
  have h234 := Primrec.and.to_comp.computableIn (O := {charOracle A}) |>.comp
    ((c2.to_comp.computableIn).pair h34)
  have h2345 := Primrec.and.to_comp.computableIn (O := {charOracle A}) |>.comp
    (h234.pair c5)
  have hall := Primrec.or.to_comp.computableIn (O := {charOracle A}) |>.comp
    ((c1.to_comp.computableIn).pair h2345)
  refine hall.of_eq fun w => ?_
  simp only [exists_optimal_decisionDecompressorIn_chk, Bool.and_assoc, id_eq]

private theorem exists_optimal_decisionDecompressorIn_tst_true_iff (p y : BitString)
    (o : Option (BitString × BitString)) :
    exists_optimal_decisionDecompressorIn_tst p y o = true ↔
      ∀ p' y', o = some (p', y') → p' = p → (y' <+: y ∨ y <+: y') := by
  rcases o with _ | ⟨p', y'⟩
  · simp [exists_optimal_decisionDecompressorIn_tst]
  · simp only [exists_optimal_decisionDecompressorIn_tst,
      exists_optimal_decisionDecompressorIn_compat, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro (h | h | h) a b ⟨rfl, rfl⟩ hp
      · exact absurd hp h
      · exact Or.inl (List.prefix_iff_eq_take.mpr h.symm)
      · exact Or.inr (List.prefix_iff_eq_take.mpr h.symm)
    · intro H
      by_cases hp : p' = p
      · rcases H p' y' ⟨rfl, rfl⟩ hp with h | h
        · exact Or.inr (Or.inl (List.prefix_iff_eq_take.mp h).symm)
        · exact Or.inr (Or.inr (List.prefix_iff_eq_take.mp h).symm)
      · exact Or.inl hp

private theorem exists_optimal_decisionDecompressorIn_chk_true_iff (A : Set ℕ)
    (q x : BitString) (i : ℕ) (p : BitString) (s : ℕ) (y : BitString) :
    exists_optimal_decisionDecompressorIn_chk A q x i p s y = true ↔ x = [] ∨
      (q = natCode i ++ p ∧
      exists_optimal_decisionDecompressorIn_enum A i s = some (p, y) ∧ x <+: y ∧
      ∀ s' < s, ∀ p' y', exists_optimal_decisionDecompressorIn_enum A i s' = some (p', y') →
        p' = p → (y' <+: y ∨ y <+: y')) := by
  simp only [exists_optimal_decisionDecompressorIn_chk, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range,
    exists_optimal_decisionDecompressorIn_tst_true_iff]
  rw [List.prefix_iff_eq_take]
  simp only [and_assoc]

/-- The tagged trimmed relation: `x = []`, or `q = natCode i ++ p` and `x` is a prefix of an
output `y` enumerated by index `i` for `p` that is compatible with everything enumerated earlier
for `p`. -/
private noncomputable def exists_optimal_decisionDecompressorIn_rel (A : Set ℕ)
    (q x : BitString) : Prop :=
  ∃ z : ℕ × BitString × ℕ × BitString,
    exists_optimal_decisionDecompressorIn_chk A q x z.1 z.2.1 z.2.2.1 z.2.2.2 = true

private theorem exists_optimal_decisionDecompressorIn_rel_re (A : Set ℕ) :
    PointToSet.IsREIn A
      (fun q : BitString × BitString => exists_optimal_decisionDecompressorIn_rel A q.1 q.2) := by
  have hF : PointToSet.IsREIn A (fun w : exists_optimal_decisionDecompressorIn_DW =>
      exists_optimal_decisionDecompressorIn_chk A w.1.1 w.1.2 w.2.1 w.2.2.1 w.2.2.2.1
        w.2.2.2.2 = true) :=
    PointToSet.isREIn_of_computableIn_decide A _
      ((exists_optimal_decisionDecompressorIn_chk_computable A).of_eq fun w => by simp)
  exact PointToSet.IsREIn.exists
    (F := fun w : exists_optimal_decisionDecompressorIn_DW =>
      exists_optimal_decisionDecompressorIn_chk A w.1.1 w.1.2 w.2.1 w.2.2.1 w.2.2.2.1
        w.2.2.2.2 = true) hF

private theorem exists_optimal_decisionDecompressorIn_rel_nil (A : Set ℕ) (q : BitString) :
    exists_optimal_decisionDecompressorIn_rel A q [] :=
  ⟨(0, [], 0, []), by simp [exists_optimal_decisionDecompressorIn_chk]⟩

private theorem exists_optimal_decisionDecompressorIn_rel_prefix (A : Set ℕ) {q x x' : BitString}
    (h : exists_optimal_decisionDecompressorIn_rel A q x) (hx : x' <+: x) :
    exists_optimal_decisionDecompressorIn_rel A q x' := by
  obtain ⟨⟨i, p, s, y⟩, hz⟩ := h
  rw [exists_optimal_decisionDecompressorIn_chk_true_iff] at hz
  rcases hz with rfl | ⟨hq, he, hxy, hall⟩
  · rw [List.prefix_nil] at hx
    subst hx
    exact exists_optimal_decisionDecompressorIn_rel_nil A q
  · exact ⟨(i, p, s, y), (exists_optimal_decisionDecompressorIn_chk_true_iff ..).mpr
      (Or.inr ⟨hq, he, hx.trans hxy, hall⟩)⟩

private theorem exists_optimal_decisionDecompressorIn_rel_regular (A : Set ℕ) :
    IsRegular .eq .compat (exists_optimal_decisionDecompressorIn_rel A) := by
  intro q1 x1 q2 x2 h1 h2 hq
  change q1 = q2 at hq
  change x1 <+: x2 ∨ x2 <+: x1
  obtain ⟨⟨i1, p1, s1, y1⟩, hz1⟩ := h1
  obtain ⟨⟨i2, p2, s2, y2⟩, hz2⟩ := h2
  rw [exists_optimal_decisionDecompressorIn_chk_true_iff] at hz1 hz2
  rcases hz1 with rfl | ⟨hq1, he1, hx1, hall1⟩
  · exact Or.inl (List.nil_prefix)
  rcases hz2 with rfl | ⟨hq2, he2, hx2, hall2⟩
  · exact Or.inr (List.nil_prefix)
  obtain ⟨rfl, rfl⟩ := natCode_append_inj (hq1.symm.trans (hq.trans hq2))
  have hy : y1 <+: y2 ∨ y2 <+: y1 := by
    rcases lt_trichotomy s1 s2 with hlt | rfl | hgt
    · rcases hall2 s1 hlt p1 y1 he1 rfl with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rw [he1] at he2
      cases he2
      exact Or.inl (List.prefix_refl _)
    · rcases hall1 s2 hgt p1 y2 he2 rfl with h | h
      · exact Or.inr h
      · exact Or.inl h
  have key : ∀ {a b c d : BitString}, a <+: c → b <+: d → c <+: d → a <+: b ∨ b <+: a := by
    intro a b c d hac hbd hcd
    have had : a <+: d := hac.trans hcd
    rcases le_total a.length b.length with hl | hl
    · exact Or.inl (List.prefix_of_prefix_length_le had hbd hl)
    · exact Or.inr (List.prefix_of_prefix_length_le hbd had hl)
  rcases hy with h | h
  · exact key hx1 hx2 h
  · exact (key hx2 hx1 h).symm

/-- **SUV Section 6.4.1 (printed p. 203), unnumbered.** Relativized Problem 192: an optimal
`A`-decision decompressor exists.

Proof idea: the proof of `exists_optimal_decisionDecompressor` relativizes. Enumerate the
`A`-enumerable relations (universal oracle machine), trim each one to a decision decompressor,
and prefix descriptions with a self-delimiting code of the index. -/
theorem exists_optimal_decisionDecompressorIn (A : Set ℕ) :
    ∃ R : DecisionDecompressorIn A, R.IsOptimal := by
  refine ⟨⟨exists_optimal_decisionDecompressorIn_rel A,
    exists_optimal_decisionDecompressorIn_rel_re A,
    exists_optimal_decisionDecompressorIn_rel_nil A,
    fun _ _ _ h hx => exists_optimal_decisionDecompressorIn_rel_prefix A h hx,
    exists_optimal_decisionDecompressorIn_rel_regular A⟩, ?_⟩
  intro M
  obtain ⟨e, he⟩ := exists_optimal_decisionDecompressorIn_enum_universal A
    (fun q : BitString × BitString => M.rel q.1 q.2) M.re
  refine ⟨e + 1, fun x => ?_⟩
  unfold KRInOf modeComplexity
  apply sInfLeSInfAdd
  rintro len ⟨p, hp, rfl⟩
  refine ⟨((natCode e ++ p).length : ℕ∞), ⟨natCode e ++ p, ?_, rfl⟩, ?_⟩
  · obtain ⟨s, hs⟩ := (he (p, x)).mp hp
    refine ⟨(e, p, s, x), (exists_optimal_decisionDecompressorIn_chk_true_iff ..).mpr
      (Or.inr ⟨rfl, hs, List.prefix_refl x, ?_⟩)⟩
    intro s' _ p' y' hs' hp'
    subst hp'
    have hy' : M.rel p' y' := (he (p', y')).mpr ⟨s', hs'⟩
    rcases M.regular hp hy' rfl with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rw [List.length_append, length_natCode]
    push_cast
    exact le_of_eq (add_comm _ _)

/-- Step 1 of the proof of `exists_isOptimalMonotoneDecompressorIn`: there is a uniformly
`A`-enumerable family `V i` of relations on pairs of bit strings (the universal oracle machine
`PointToSet.oracleEval A`, applied to the code of the pair) containing every `A`-enumerable
relation: the set of triples `(i, x, y)` with `V i x y` is `A`-enumerable, and every
`A`-enumerable relation `R` equals some row `V i`. -/
private theorem exists_isOptimalMonotoneDecompressorIn_universal (A : Set ℕ) :
    ∃ V : ℕ → BitString → BitString → Prop,
      PointToSet.IsREIn A (fun p : ℕ × (BitString × BitString) => V p.1 p.2.1 p.2.2) ∧
      ∀ R : BitString → BitString → Prop,
        PointToSet.IsREIn A (fun p : BitString × BitString => R p.1 p.2) →
          ∃ i, ∀ x y, V i x y ↔ R x y := by
  refine ⟨fun i x y => (PointToSet.oracleEval A i (Encodable.encode (x, y))).Dom, ?_, ?_⟩
  · refine ⟨fun p : ℕ × (BitString × BitString) =>
      PointToSet.oracleEval A p.1 (Encodable.encode p.2), ?_, fun _ => Iff.rfl⟩
    have hargs : Computable (fun p : ℕ × (BitString × BitString) =>
        (p.1, Encodable.encode p.2)) :=
      Computable.fst.pair (Computable.encode.comp Computable.snd)
    have hev := (PointToSet.oracleStage_evaluator A).comp hargs.computableIn
    exact hev.of_eq fun p => rfl
  · intro R ⟨f, hf, hfdom⟩
    have hd : Computable (fun n => Encodable.decode (α := BitString × BitString) n) :=
      Computable.decode
    have hopt := (Computable.ofOption hd).partrecIn (O := {charOracle A})
    have hmap : PartrecIn₂ {charOracle A}
        (fun (_ : ℕ) (a : BitString × BitString) => f a) :=
      hf.comp ComputableIn.snd
    have hg := PartrecIn.bind hopt hmap
    obtain ⟨e, he⟩ := PointToSet.oracleStage_universal A _ hg
    refine ⟨e, fun x y => ?_⟩
    refine Iff.trans ?_ (hfdom (x, y)).symm
    change (PointToSet.oracleEval A e (Encodable.encode (x, y))).Dom ↔ _
    change (Nat.rfindOpt fun t => PointToSet.oracleStage A t e _).Dom ↔ _
    rw [Nat.rfindOpt_dom]
    constructor
    · rintro ⟨t, v, hv⟩
      have := (he (Encodable.encode (x, y)) v).mpr ⟨t, Option.mem_def.mp hv⟩
      simp only [Part.ofOption, Encodable.encodek, Part.bind_some] at this
      exact Part.dom_iff_mem.mpr ⟨v, this⟩
    · intro h
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
      obtain ⟨t, ht⟩ := (he (Encodable.encode (x, y)) v).mp (by
        simp only [Part.ofOption, Encodable.encodek, Part.bind_some]; exact hv)
      exact ⟨t, v, Option.mem_def.mpr ht⟩

private lemma exists_isOptimalMonotoneDecompressorIn_sanitize_prefixCheck_primrec
    {γ : Type*} [Primcodable γ] {fu fv : γ → BitString}
    (hu : Primrec fu) (hv : Primrec fv) : Primrec fun c => prefixCheck (fu c) (fv c) := by
  obtain ⟨_, h⟩ : PrimrecPred fun c => fu c = (fv c).take (fu c).length :=
    Primrec.eq.comp hu (Primrec.list_take.comp (Primrec.list_length.comp hu) hv)
  exact h.of_eq fun c => by simp only [prefixCheck]; congr

private lemma exists_isOptimalMonotoneDecompressorIn_sanitize_compatCheck_primrec
    {γ : Type*} [Primcodable γ] {fx fy fx' fy' : γ → BitString}
    (hx : Primrec fx) (hy : Primrec fy) (hx' : Primrec fx') (hy' : Primrec fy') :
    Primrec fun c => compatCheck (fx c) (fy c) (fx' c) (fy' c) := by
  have P := @exists_isOptimalMonotoneDecompressorIn_sanitize_prefixCheck_primrec γ _
  exact Primrec.or.comp
    (Primrec.not.comp (Primrec.or.comp (P hx hx') (P hx' hx)))
    (Primrec.or.comp (P hy hy') (P hy' hy))

private lemma exists_isOptimalMonotoneDecompressorIn_sanitize_decodePair_primrec :
    Primrec decodePair := by
  have h := Primrec.option_casesOn (Primrec.decode (α := BitString × BitString))
    (Primrec.const (([], []) : BitString × BitString)) (Primrec.snd (α := ℕ)).to₂
  refine h.of_eq fun n => ?_
  cases hd : Encodable.decode (α := BitString × BitString) n <;> simp [decodePair, hd]

private lemma exists_isOptimalMonotoneDecompressorIn_sanitize_all_computableIn
    {O : Set (ℕ →. ℕ)} {γ : Type*} [Primcodable γ] {N : γ → ℕ} {f : γ → ℕ → Bool}
    (hN : ComputableIn O N) (hf : ComputableIn O fun p : γ × ℕ => f p.1 p.2) :
    ComputableIn O fun c => (List.range (N c)).all (f c) := by
  have hstep : ComputableIn₂ O (fun (c : γ) (q : ℕ × Bool) => q.2 && f c q.1) :=
    (Primrec.and.computableIn.comp
      ((ComputableIn.snd.comp ComputableIn.snd).pair
        (hf.comp ((ComputableIn.fst).pair (ComputableIn.fst.comp ComputableIn.snd))))).to₂
  have hrec := ComputableIn.nat_rec hN (ComputableIn.const true) hstep
  refine hrec.of_eq fun c => ?_
  have : ∀ n, @Nat.rec (fun _ => Bool) true (fun y ih => ih && f c y) n =
      (List.range n).all (f c) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.range_succ, ih]
  exact this _

private lemma exists_isOptimalMonotoneDecompressorIn_sanitize_sanStage_computableIn
    {O : Set (ℕ →. ℕ)} {Aa : ℕ → BitString → BitString → ℕ → Bool}
    (hA : ComputableIn O fun p : (ℕ × BitString × BitString) × ℕ =>
      Aa p.1.1 p.1.2.1 p.1.2.2 p.2)
    {γ : Type*} [Primcodable γ] {fa : γ → ℕ} {fx fy : γ → BitString} {fk : γ → ℕ}
    (ha : ComputableIn O fa) (hx : ComputableIn O fx) (hy : ComputableIn O fy)
    (hk : ComputableIn O fk) :
    ComputableIn O fun c => sanStage Aa (fa c) (fx c) (fy c) (fk c) := by
  have hbase : ComputableIn O fun c => Aa (fa c) (fx c) (fy c) (fk c) :=
    hA.comp ((ha.pair (hx.pair hy)).pair hk)
  have hpred : ComputableIn O fun c => Aa (fa c) (fx c) (fy c) (fk c - 1) :=
    hA.comp ((ha.pair (hx.pair hy)).pair (Primrec.pred.computableIn.comp hk))
  have hzero : Primrec fun n : ℕ => decide (n = 0) :=
    primrec_decideEq.comp Primrec.id (Primrec.const 0)
  have hzero' : ComputableIn O fun c => decide (fk c = 0) := hzero.computableIn.comp hk
  have hfinal := Primrec.and.computableIn.comp (hbase.pair
    (Primrec.or.computableIn.comp (hzero'.pair (Primrec.not.computableIn.comp hpred))))
  exact hfinal.of_eq fun c => by simp only [sanStage]

private lemma exists_isOptimalMonotoneDecompressorIn_sanitize_sanStep_computableIn
    {O : Set (ℕ →. ℕ)} {Aa : ℕ → BitString → BitString → ℕ → Bool}
    (hA : ComputableIn O fun p : (ℕ × BitString × BitString) × ℕ =>
      Aa p.1.1 p.1.2.1 p.1.2.2 p.2) :
    ComputableIn O fun p : (ℕ × BitString × BitString) × ℕ =>
      sanStep Aa p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  have hSt := @exists_isOptimalMonotoneDecompressorIn_sanitize_sanStage_computableIn
    O Aa hA
  have hdp := exists_isOptimalMonotoneDecompressorIn_sanitize_decodePair_primrec
  have hcheck : ComputableIn O fun p : (ℕ × BitString × BitString) × ℕ =>
      sanCheck Aa p.1.1 p.1.2.1 p.1.2.2 p.2 := by
    have hN : ComputableIn O fun p : (ℕ × BitString × BitString) × ℕ =>
        sanKey p.1.2.1 p.1.2.2 p.2 :=
      (Primrec₂.natPair.comp Primrec.snd
        (Primrec.encode.comp (Primrec.snd.comp Primrec.fst))).computableIn
    have hq : Primrec fun c : ((ℕ × BitString × BitString) × ℕ) × ℕ =>
        decodePair c.2.unpair.2 :=
      hdp.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
    have hq1 : Primrec fun c : ((ℕ × BitString × BitString) × ℕ) × ℕ =>
        (decodePair c.2.unpair.2).1 := Primrec.fst.comp hq
    have hq2 : Primrec fun c : ((ℕ × BitString × BitString) × ℕ) × ℕ =>
        (decodePair c.2.unpair.2).2 := Primrec.snd.comp hq
    have hk : Primrec fun c : ((ℕ × BitString × BitString) × ℕ) × ℕ => c.2.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
    have ha : Primrec fun c : ((ℕ × BitString × BitString) × ℕ) × ℕ => c.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hx : Primrec fun c : ((ℕ × BitString × BitString) × ℕ) × ℕ => c.1.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hy : Primrec fun c : ((ℕ × BitString × BitString) × ℕ) × ℕ => c.1.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have h1 := hSt ha.computableIn hq1.computableIn hq2.computableIn hk.computableIn
    have h2 := Primrec.not.computableIn.comp h1
    have h3 := (exists_isOptimalMonotoneDecompressorIn_sanitize_compatCheck_primrec
      hx hy hq1 hq2).computableIn (O := O)
    have hbody := Primrec.or.computableIn.comp (h2.pair h3)
    have hall := exists_isOptimalMonotoneDecompressorIn_sanitize_all_computableIn hN
      (f := fun c n => !(sanStage Aa c.1.1 (decodePair n.unpair.2).1 (decodePair n.unpair.2).2
            n.unpair.1) || compatCheck c.1.2.1 c.1.2.2 (decodePair n.unpair.2).1
            (decodePair n.unpair.2).2) (hbody.of_eq fun c => rfl)
    exact hall.of_eq fun c => by simp only [sanCheck]
  have h4 := hSt (Primrec.fst.comp Primrec.fst).computableIn
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).computableIn
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).computableIn
      Primrec.snd.computableIn
  have h5 := Primrec.and.computableIn.comp (h4.pair hcheck)
  exact h5.of_eq fun p => by simp only [sanStep]

private lemma exists_isOptimalMonotoneDecompressorIn_sanitize_or
    {α : Type*} [Primcodable α] {A : Set ℕ} {C G : α → Prop} [DecidablePred C]
    (hC : ComputableIn {charOracle A} fun x => decide (C x))
    (hG : PointToSet.IsREIn A G) : PointToSet.IsREIn A fun x => C x ∨ G x := by
  obtain ⟨g, hg, hdom⟩ := hG
  refine ⟨fun x => cond (decide (C x)) (Part.some 0) (g x),
    PartrecIn.cond hC (ComputableIn.const 0).partrecIn hg, fun x => ?_⟩
  by_cases h : C x <;> simp [h, hdom]

/-- Step 2 of the proof of `exists_isOptimalMonotoneDecompressorIn`: relativized
sanitizer plus gap filling (the `A`-version of `sanitizedUniversalStreamRel` followed by
`streamGapFill`). From a uniformly `A`-enumerable family `V i` of relations one gets a uniformly
`A`-enumerable family `U i` of stream lower graphs such that `U i` is the gap filling of `V i`
whenever `V i` is consistent (accept an enumerated pair only if it is compatible with all pairs
enumerated earlier in a fixed order; this does not change a consistent relation; then gap fill:
`U i x y` iff `y = []` or `∃ z, z.1 <+: x ∧ y <+: z.2 ∧ V' i z.1 z.2`, where `V'` is the
sanitized relation). -/
private theorem exists_isOptimalMonotoneDecompressorIn_sanitize (A : Set ℕ)
    (V : ℕ → BitString → BitString → Prop)
    (hV : PointToSet.IsREIn A (fun p : ℕ × (BitString × BitString) => V p.1 p.2.1 p.2.2)) :
    ∃ U : ℕ → BitString → BitString → Prop,
      PointToSet.IsREIn A (fun p : ℕ × (BitString × BitString) => U p.1 p.2.1 p.2.2) ∧
      (∀ i, IsStreamLowerGraph (U i)) ∧
      ∀ i, IsConsistentStreamRelation (V i) → ∀ x y, U i x y ↔ streamGapFill (V i) x y := by
  obtain ⟨e, he, hEnum⟩ := (PointToSet.relative_enumeration A _).mp hV
  let stage : ℕ → BitString → BitString → ℕ → Bool :=
    fun i x y k => decide (e k = some (i, (x, y)))
  have hstage : ComputableIn {charOracle A} fun p : (ℕ × BitString × BitString) × ℕ =>
      stage p.1.1 p.1.2.1 p.1.2.2 p.2 :=
    primrec_decideEq.computableIn.comp
      ((he.comp Primrec.snd.computableIn).pair
        (Primrec.option_some.comp Primrec.fst).computableIn)
  have hVstage : ∀ i x y, V i x y ↔ ∃ k, stage i x y k = true := fun i x y => by
    simpa [stage] using hEnum (i, (x, y))
  have hstep := PointToSet.isREIn_of_computableIn_decide A
    (fun p : (ℕ × (BitString × BitString)) × ℕ =>
      sanStep stage p.1.1 p.1.2.1 p.1.2.2 p.2 = true)
    ((exists_isOptimalMonotoneDecompressorIn_sanitize_sanStep_computableIn
      hstage).of_eq fun p => by simp)
  have hSre : PointToSet.IsREIn A
      (fun p : ℕ × (BitString × BitString) => sanitizedStreamRel stage p.1 p.2.1 p.2.2) :=
    PointToSet.IsREIn.exists hstep
  have hG : PointToSet.IsREIn A fun w : (ℕ × BitString × BitString) × (BitString × BitString) =>
      gapFillCheck (w.1.2, w.2) = true ∧ sanitizedStreamRel stage w.1.1 w.2.1 w.2.2 := by
    refine PointToSet.IsREIn.and ?_ ?_
    · refine PointToSet.isREIn_of_computableIn_decide A _ ?_
      exact (computable_gapFillCheck.computableIn.comp
        (((Primrec.snd.comp Primrec.fst).computableIn).pair
          Primrec.snd.computableIn)).of_eq fun w => by simp
    · exact hSre.comp
        (f := fun w : (ℕ × BitString × BitString) × (BitString × BitString) => (w.1.1, w.2))
        ((Primrec.fst.comp Primrec.fst).computableIn.pair Primrec.snd.computableIn)
  have hex := PointToSet.IsREIn.exists hG
  obtain ⟨_, hnilc⟩ : PrimrecPred fun p : ℕ × BitString × BitString => p.2.2 = [] :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])
  have hor := exists_isOptimalMonotoneDecompressorIn_sanitize_or
    (C := fun p : ℕ × BitString × BitString => p.2.2 = []) hnilc.computableIn hex
  have hUre : PointToSet.IsREIn A (fun p : ℕ × (BitString × BitString) =>
      streamGapFill (sanitizedStreamRel stage p.1) p.2.1 p.2.2) := by
    obtain ⟨f, hf, hdom⟩ := hor
    refine ⟨f, hf, fun p => ?_⟩
    refine Iff.trans ?_ (hdom p)
    constructor
    · rintro (h | ⟨z, hz, hR⟩)
      · exact Or.inl h
      · exact Or.inr ⟨z, (gapFillCheck_eq_true_iff ((p.2.1, p.2.2), z)).mpr hz, hR⟩
    · rintro (h | ⟨z, hz, hR⟩)
      · exact Or.inl h
      · exact Or.inr ⟨z, (gapFillCheck_eq_true_iff ((p.2.1, p.2.2), z)).mp hz, hR⟩
  refine ⟨fun i => streamGapFill (sanitizedStreamRel stage i), hUre,
    fun i => streamGapFill_isStreamLowerGraph (sanitizedStreamRel_isConsistent stage i),
    fun i hcons x y => streamGapFill_congr (fun x y => ?_) x y⟩
  have hcons' : IsConsistentStreamRelation (fun x y => ∃ k, stage i x y k = true) :=
    fun x₁ x₂ y₁ y₂ h₁ h₂ hx => hcons x₁ x₂ y₁ y₂ ((hVstage _ _ _).mpr h₁)
      ((hVstage _ _ _).mpr h₂) hx
  exact (sanitizedStreamRel_eq_of_consistent stage i hcons' x y).trans (hVstage i x y).symm

/-- Step 3 of the proof of `exists_isOptimalMonotoneDecompressorIn`: tagging a uniformly
`A`-enumerable family of relations with self-delimiting indices (`natCode`) gives an
`A`-enumerable relation (relativization of `taggedStreamLowerGraph_isRE`: the relation is
`y = []` or `∃ i q, x = natCode i ++ q ∧ U i q y`). -/
private theorem exists_isOptimalMonotoneDecompressorIn_tagged_re (A : Set ℕ)
    (U : ℕ → BitString → BitString → Prop)
    (hU : PointToSet.IsREIn A (fun p : ℕ × (BitString × BitString) => U p.1 p.2.1 p.2.2)) :
    PointToSet.IsREIn A (fun p : BitString × BitString => taggedStreamLowerGraph U p.1 p.2) := by
  have h_pred : Computable (fun p : (BitString × BitString) × (ℕ × BitString) =>
      decide (p.1.1 = natCode p.2.1 ++ p.2.2)) := by
    apply Primrec.to_comp
    have h_primrec_pred : PrimrecPred (fun p : (BitString × BitString) × (ℕ × BitString) =>
      p.1.1 = natCode p.2.1 ++ p.2.2) :=
      (Primrec.eq (α := BitString)).comp
        (Primrec.fst.comp (Primrec.fst (α := BitString × BitString) (β := ℕ × BitString)))
        (Primrec.list_append.comp
          (primrec_natCode.comp (Primrec.fst.comp
            (Primrec.snd (α := BitString × BitString) (β := ℕ × BitString))))
          (Primrec.snd.comp (Primrec.snd (α := BitString × BitString) (β := ℕ × BitString))))
    rcases h_primrec_pred with ⟨_, hp⟩
    exact hp.of_eq (by intro p; congr)
  have h_U_comp : Computable (fun p : (BitString × BitString) × (ℕ × BitString) =>
      (p.2.1, (p.2.2, p.1.2))) := by
    apply Computable.pair
    · exact Computable.fst.comp Computable.snd
    · apply Computable.pair
      · exact Computable.snd.comp Computable.snd
      · exact Computable.snd.comp Computable.fst
  have hRE1 := hU.comp h_U_comp.computableIn
  have hRE2 : PointToSet.IsREIn A (fun p : (BitString × BitString) × (ℕ × BitString) =>
      p.1.1 = natCode p.2.1 ++ p.2.2) :=
    PointToSet.isREIn_of_computable_decide h_pred
  have hRE3 := hRE2.and hRE1
  have hRE4 := PointToSet.IsREIn.exists
    (F := fun q : (BitString × BitString) × (ℕ × BitString) =>
      q.1.1 = natCode q.2.1 ++ q.2.2 ∧ U q.2.1 q.2.2 q.1.2) hRE3
  obtain ⟨g, hg, hgdom⟩ := hRE4
  have hnil : Computable (fun p : BitString × BitString => decide (p.2 = [])) := by
    have hp : PrimrecPred (fun p : BitString × BitString => p.2 = []) :=
      (Primrec.eq (α := BitString)).comp Primrec.snd (Primrec.const [])
    exact hp.decide.to_comp
  refine ⟨fun p => cond (decide (p.2 = [])) (Part.some 0) (g p),
    PartrecIn.cond hnil.computableIn (ComputableIn.const 0).partrecIn hg, fun p => ?_⟩
  by_cases h : p.2 = []
  · simp [h, taggedStreamLowerGraph]
  · simp only [decide_eq_false h, Bool.cond_false]
    rw [← hgdom p]
    simp only [taggedStreamLowerGraph, h, false_or]
    constructor
    · rintro ⟨i, q, hx, hu⟩
      exact ⟨(i, q), hx, hu⟩
    · rintro ⟨⟨i, q⟩, hx, hu⟩
      exact ⟨i, q, hx, hu⟩

/-- **SUV Section 6.4.1 (printed p. 203), unnumbered.** Relativized Theorem 84: an optimal
`A`-monotone decompressor exists.

Proof idea: the proof of `exists_optimalMonotoneDecompressor` relativizes. Enumerate the
`A`-enumerable consistent relations, close them to lower graphs of continuous stream maps
(`streamGapFill`), and prefix the input with a self-delimiting code of the index. -/
theorem exists_isOptimalMonotoneDecompressorIn (A : Set ℕ) :
    ∃ D, IsOptimalMonotoneDecompressorIn A D := by
  obtain ⟨V, hVre, hVcomp⟩ := exists_isOptimalMonotoneDecompressorIn_universal A
  obtain ⟨U, hUre, hUlg, hUV⟩ :=
    exists_isOptimalMonotoneDecompressorIn_sanitize A V hVre
  have hTlg := taggedStreamLowerGraph_isStreamLowerGraph U hUlg
  refine ⟨streamMapOfLowerGraph (taggedStreamLowerGraph U) hTlg, ⟨?_, ?_⟩, ?_⟩
  · exact streamMapOfLowerGraph_isContinuousStreamMap _
  · obtain ⟨f, hf, hdom⟩ := exists_isOptimalMonotoneDecompressorIn_tagged_re A U hUre
    exact ⟨f, hf, fun w =>
      (streamMapOfLowerGraph_finite_spec hTlg w.1 w.2).trans (hdom w)⟩
  · intro D' hD'
    obtain ⟨hD'c, hD're⟩ := hD'
    have hLlg := continuousStreamMap_lowerGraph_isStreamLowerGraph hD'c.1
    obtain ⟨i, hi⟩ := hVcomp (streamLowerGraph D') hD're
    have hcons : IsConsistentStreamRelation (V i) := fun x₁ x₂ y₁ y₂ h₁ h₂ hx =>
      hLlg.isConsistentStreamRelation x₁ x₂ y₁ y₂ ((hi _ _).mp h₁) ((hi _ _).mp h₂) hx
    have hUi : ∀ x y, U i x y ↔ streamLowerGraph D' x y := fun x y =>
      ((hUV i hcons x y).trans (streamGapFill_congr hi x y)).trans
        (streamGapFill_eq_self hLlg x y)
    refine ⟨(natCode i).length, fun x => ?_⟩
    apply KMOf_tagged_le_add
    intro p hp
    have hl3 : taggedStreamLowerGraph U (natCode i ++ p) x :=
      Or.inr ⟨i, p, rfl, (hUi p x).mpr hp⟩
    change BitStream.finite x ≤ streamMapOfLowerGraph (taggedStreamLowerGraph U) hTlg
      (.finite (natCode i ++ p))
    rwa [streamMapOfLowerGraph_finite_spec]

end GeneralScheme
end Kolmogorov
