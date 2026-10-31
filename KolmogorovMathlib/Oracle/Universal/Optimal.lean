/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Oracle.Universal.Enumeration

/-!
# Optimal oracle prefix machines

For every set `A ⊆ ℕ`, this file constructs a conditional prefix decompressor that is
recursive in the characteristic oracle of `A` and that dominates, up to an additive constant,
every `A`-recursive conditional prefix decompressor (blueprint node `oracle:universal`).

The construction applies an online prefix filter to each indexed stage evaluator
`oracleEval A e`: a program is a candidate for the context `y` as soon as the stage evaluator
has produced an output for it, and it is kept only if no earlier candidate is a distinct
prefix-comparable program.  The filter is `A`-partial recursive, it is prefix-free by
construction and it agrees with every `A`-recursive prefix machine that is evaluated by `e`.
Their tagged union (`taggedUnion`) is therefore optimal, the tag of the `e`-th filter costing
`e + 1` bits.

The main results are `exists_optimalOraclePrefix`, the chosen family `optimalOraclePrefix` with
its specification `exists_optimalOraclePrefix_spec`, and the finiteness of all conditional
complexities `exists_optimalOraclePrefix_finite`, which follows from the literal-output
machine `simpleLenDecompressor`.  The relative prefix complexity of the point-to-set
principles is defined from `optimalOraclePrefix`.
-/

namespace Kolmogorov.PointToSet

/-- The program that appears at dovetail index `n` for the `e`-th oracle program on the context
`y`: the program decoded from the first component of `n`, provided that the bounded oracle
evaluation at the stage given by the second component of `n` has halted on it. -/
private noncomputable def stageCandidate (A : Set ℕ) (e : ℕ) (y : BitString) (n : ℕ) :
    Option BitString :=
  (Encodable.decode n.unpair.1 : Option BitString).bind fun p =>
    if (oracleStage A (n.unpair.2 + 1) e (Encodable.encode (p, y))).isSome then
      some p
    else
      none

/-- The local acceptance test of the prefix filter: the program `p` passes against an earlier
candidate `c` unless `c` is a distinct program comparable with `p` under the prefix order. -/
private def candidateAllows (c : Option BitString) (p : BitString) : Bool :=
  match c with
  | none => true
  | some q => decide ¬ (q ≠ p ∧ (q <+: p ∨ p <+: q))

/-- A conjunction over a list of Boolean tests is `true` exactly when every test is `true`. -/
private lemma foldr_and_true_iff (l : List ℕ) (f : ℕ → Bool) :
    l.foldr (fun n acc => f n && acc) true = true ↔ ∀ n ∈ l, f n = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The online prefix filter of the `e`-th oracle program: a program `p` is accepted on the
context `y` once it has appeared as a candidate, provided that no earlier candidate is a
distinct prefix-comparable program; its output is then the decoded value of `oracleEval`. -/
private noncomputable def oraclePrefixFilter (A : Set ℕ) (e : ℕ) : Map := fun pr =>
  (Nat.rfind fun n => Part.some (decide (stageCandidate A e pr.2 n = some pr.1))).bind fun N =>
    bif (List.range N).foldr
        (fun n acc => candidateAllows (stageCandidate A e pr.2 n) pr.1 && acc) true then
      (oracleEval A e (Encodable.encode pr)).map
        (fun r => (Encodable.decode r : Option BitString).getD [])
    else
      Part.none

/-- Decoding a candidate and testing its bounded oracle computation is uniformly relatively
computable. -/
private lemma computableIn_stageCandidate (A : Set ℕ) :
    ComputableIn {charOracle A}
      (fun t : ℕ × BitString × ℕ => stageCandidate A t.1 t.2.1 t.2.2) := by
  have hd : Computable (fun t : ℕ × BitString × ℕ =>
      (Encodable.decode t.2.2.unpair.1 : Option BitString)) :=
    Computable.decode.comp (Computable.fst.comp
      (Computable.unpair.comp (Computable.snd.comp Computable.snd)))
  have hp : Computable (fun t : ℕ × BitString × ℕ =>
      (Encodable.decode t.2.2.unpair.1 : Option BitString).getD []) :=
    Computable.option_getD hd (Computable.const [])
  have hargs : Computable (fun t : ℕ × BitString × ℕ =>
      (t.2.2.unpair.2 + 1, t.1,
        Encodable.encode
          ((Encodable.decode t.2.2.unpair.1 : Option BitString).getD [], t.2.1))) :=
    (Computable.succ.comp (Computable.snd.comp
      (Computable.unpair.comp (Computable.snd.comp Computable.snd)))).pair
      (Computable.fst.pair
        (Computable.encode.comp (hp.pair (Computable.fst.comp Computable.snd))))
  have hs := (oracleStage_computable A).comp hargs.computableIn
  have hb := Primrec.option_isSome.to_comp.computableIn.comp hs
  have hselect : Computable (fun t : Option BitString × Bool =>
      bif t.2 then t.1 else none) :=
    Computable.cond Computable.snd Computable.fst (Computable.const none)
  refine (hselect.computableIn.comp (hd.computableIn.pair hb)).of_eq ?_
  intro t
  change (bif (oracleStage A (t.2.2.unpair.2 + 1) t.1
      (Encodable.encode
        ((Encodable.decode t.2.2.unpair.1 : Option BitString).getD [], t.2.1))).isSome
    then (Encodable.decode t.2.2.unpair.1 : Option BitString) else none) =
      stageCandidate A t.1 t.2.1 t.2.2
  unfold stageCandidate
  cases h : (Encodable.decode t.2.2.unpair.1 : Option BitString) with
  | none => simp
  | some p =>
    simp only [Option.getD_some, Option.bind_some]
    exact cond_eq_ite _ _ _

/-- For any uniformly relatively computable candidate family, checking all earlier candidates
against the acceptance test is relatively computable, including the empty check. -/
private lemma computableIn_foldr_candidateAllows
    {O : Set (ℕ →. ℕ)} (C : ℕ × BitString × ℕ → Option BitString)
    (hC : ComputableIn O C) :
    ComputableIn O (fun t : (ℕ × BitString × BitString) × ℕ =>
      (List.range t.2).foldr (fun n acc =>
        candidateAllows (C (t.1.1, t.1.2.2, n)) t.1.2.1 && acc) true) := by
  have hgood : Computable (fun qp : BitString × BitString =>
      decide ¬ (qp.1 ≠ qp.2 ∧ (qp.1 <+: qp.2 ∨ qp.2 <+: qp.1))) := by
    have heq : Primrec (fun qp : BitString × BitString => decide (qp.1 = qp.2)) :=
      Primrec.eq.decide
    have hpre := decide_prefix_primrec
    have hrev := decide_prefix_primrec.comp (Primrec.snd.pair Primrec.fst)
    refine (Primrec.not.comp
      (Primrec.and.comp (Primrec.not.comp heq) (Primrec.or.comp hpre hrev))).to_comp.of_eq ?_
    intro qp
    by_cases h1 : qp.1 = qp.2 <;> by_cases h2 : qp.1 <+: qp.2 <;>
      by_cases h3 : qp.2 <+: qp.1 <;> simp_all
  have hlocal : Computable (fun t : Option BitString × BitString =>
      candidateAllows t.1 t.2) := by
    refine (Computable.option_casesOn Computable.fst (Computable.const true)
      (hgood.comp (Computable.snd.pair (Computable.snd.comp Computable.fst))).to₂).of_eq
        fun t => ?_
    cases t.1 <;> rfl
  let good (s : ℕ × BitString × BitString) (n : ℕ) : Bool :=
    candidateAllows (C (s.1, s.2.2, n)) s.2.1
  have hc : ComputableIn O (fun t : (ℕ × BitString × BitString) × ℕ =>
      C (t.1.1, t.1.2.2, t.2)) :=
    hC.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
        Computable.snd)).computableIn
  have hg : ComputableIn O (fun t : (ℕ × BitString × BitString) × ℕ =>
      good t.1 t.2) :=
    hlocal.computableIn.comp (hc.pair
      (Computable.fst.comp (Computable.snd.comp Computable.fst)).computableIn)
  have hstep : ComputableIn O
      (fun t : ((ℕ × BitString × BitString) × ℕ) × (ℕ × Bool) =>
        good t.1.1 t.2.1 && t.2.2) := by
    have htest : ComputableIn O
        (fun t : ((ℕ × BitString × BitString) × ℕ) × (ℕ × Bool) =>
          good t.1.1 t.2.1) :=
      hg.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd)).computableIn
    have hand : Computable (fun b : Bool × Bool => b.1 && b.2) := Primrec.and.to_comp
    have hbool : ComputableIn O
        (fun t : ((ℕ × BitString × BitString) × ℕ) × (ℕ × Bool) => t.2.2) :=
      (Computable.snd.comp Computable.snd).computableIn
    have hpair := htest.pair hbool
    have hcomp := ComputableIn.comp hand.computableIn hpair
    exact hcomp.of_eq fun _ => rfl
  have hN : ComputableIn O (fun t : (ℕ × BitString × BitString) × ℕ => t.2) :=
    ComputableIn.snd
  have hrec := ComputableIn.nat_rec hN (ComputableIn.const true) hstep.to₂
  refine hrec.of_eq fun t => ?_
  have hfold (l : List ℕ) (b : Bool) :
      l.foldr (fun n acc => good t.1 n && acc) b =
        (l.foldr (fun n acc => good t.1 n && acc) true && b) := by
    induction l with
    | nil => simp
    | cons n l ih => simp [ih, Bool.and_assoc]
  change Nat.rec (motive := fun _ => Bool) true (fun n acc => good t.1 n && acc) t.2 =
    (List.range t.2).foldr (fun n acc => good t.1 n && acc) true
  generalize t.2 = N
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.foldr_append]
    change (good t.1 N && Nat.rec (motive := fun _ => Bool) true
      (fun n acc => good t.1 n && acc) N) =
        (List.range N).foldr (fun n acc => good t.1 n && acc) (good t.1 N && true)
    rw [hfold, ih]
    simp [Bool.and_comm]

/-- Parsing the unary tag of a program and checking its terminator preserves uniform relative
partial computability of an indexed family of machines. -/
private lemma partrecIn_taggedUnion
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

/-- A partial map on pairs of bit strings that is partial recursive in the oracle `O` is an
`O`-recursive decompressor, i.e. its numerical encoding is `O`-recursive. -/
private lemma isDecompressorIn_of_partrecIn
    {O : ℕ →. ℕ} {M : Map} (hM : PartrecIn {O} M) : IsDecompressorIn O M := by
  unfold IsDecompressorIn mapToNatFun
  have hd : Computable (fun n => Encodable.decode (α := BitString × BitString) n) :=
    Computable.decode
  have hopt := (Computable.ofOption hd).partrecIn (O := {O})
  have hmap : PartrecIn₂ {O} (fun (_ : ℕ) (a : BitString × BitString) =>
      (M a).map Encodable.encode) :=
    PartrecIn.map (hM.comp ComputableIn.snd)
      (Computable.encode.comp Computable.snd).computableIn.to₂
  exact RecursiveIn.iff_nat.mpr (PartrecIn.iff_nat.mp (PartrecIn.bind hopt hmap))

/-- The tagged union of the prefix filters is a decompressor recursive in the characteristic
oracle of `A`. -/
private lemma isDecompressorIn_taggedUnion_oraclePrefixFilter (A : Set ℕ) :
    IsDecompressorIn (charOracle A) (taggedUnion (oraclePrefixFilter A)) := by
  let C : ℕ × BitString × ℕ → Option BitString := fun t => stageCandidate A t.1 t.2.1 t.2.2
  have hC : ComputableIn {charOracle A} C := computableIn_stageCandidate A
  have hcheck : ComputableIn {charOracle A}
      (fun t : (ℕ × BitString × BitString) × ℕ =>
        decide (C (t.1.1, t.1.2.2, t.2) = some t.1.2.1)) := by
    have hc : ComputableIn {charOracle A}
        (fun t : (ℕ × BitString × BitString) × ℕ => C (t.1.1, t.1.2.2, t.2)) :=
      hC.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
        Computable.snd)).computableIn
    have hs : Computable (fun t : (ℕ × BitString × BitString) × ℕ =>
        (some t.1.2.1 : Option BitString)) :=
      Computable.option_some.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    have heq : Computable (fun p : Option BitString × Option BitString =>
        decide (p.1 = p.2)) := Primrec.eq.decide.to_comp
    exact heq.computableIn.comp (hc.pair hs.computableIn)
  have hfind : PartrecIn {charOracle A} (fun t : ℕ × BitString × BitString =>
      Nat.rfind fun n => Part.some (decide (C (t.1, t.2.2, n) = some t.2.1))) :=
    PartrecIn.rfind hcheck.partrecIn.to₂
  have hacc := computableIn_foldr_candidateAllows C hC
  have hargs : Computable (fun t : ℕ × BitString × BitString =>
      (t.1, Encodable.encode t.2)) :=
    Computable.fst.pair (Computable.encode.comp Computable.snd)
  have heval := (oracleStage_evaluator A).comp hargs.computableIn
  have hdecode : Computable (fun r : ℕ =>
      (Encodable.decode r : Option BitString).getD []) :=
    Computable.option_getD Computable.decode (Computable.const [])
  have hdecode' : ComputableIn₂ {charOracle A}
      (fun (_ : ℕ × BitString × BitString) (r : ℕ) =>
        (Encodable.decode r : Option BitString).getD []) :=
    (hdecode.comp Computable.snd).computableIn.to₂
  have hout := PartrecIn.map heval hdecode'
  have hout' := hout.comp (ComputableIn.fst (β := ℕ))
  have hbody := PartrecIn.cond hacc hout' PartrecIn.none
  have huniform := PartrecIn.bind hfind hbody.to₂
  have hfiltered : PartrecIn₂ {charOracle A} (oraclePrefixFilter A) := by
    apply huniform.of_eq
    intro t
    rfl
  apply isDecompressorIn_of_partrecIn
  exact partrecIn_taggedUnion hfiltered

/-- The tagged union of the prefix filters is a prefix machine, since in each filter a program
that is accepted is not prefix-comparable with any earlier accepted candidate. -/
private lemma isPrefixMachine_taggedUnion_oraclePrefixFilter (A : Set ℕ) :
    IsPrefixMachine (taggedUnion (oraclePrefixFilter A)) := by
  apply taggedUnion_isPrefixMachine
  intro e y
  -- A halting computation supplies an appearance index and all earlier local checks.
  have hcert (p : BitString) (hp : (oraclePrefixFilter A e (p, y)).Dom) :
      ∃ N, stageCandidate A e y N = some p ∧
        ∀ n < N, candidateAllows (stageCandidate A e y n) p = true := by
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hp
    change x ∈ (Nat.rfind fun n => Part.some (decide (stageCandidate A e y n = some p))).bind
      (fun N => bif (List.range N).foldr
          (fun n acc => candidateAllows (stageCandidate A e y n) p && acc) true then
        (oracleEval A e (Encodable.encode (p, y))).map
          (fun r => (Encodable.decode r : Option BitString).getD [])
        else Part.none) at hx
    obtain ⟨N, hN, hx⟩ := Part.mem_bind_iff.mp hx
    have happ : stageCandidate A e y N = some p :=
      of_decide_eq_true (Part.mem_some_iff.mp (Nat.rfind_spec hN)).symm
    have hacc : (List.range N).foldr
        (fun n acc => candidateAllows (stageCandidate A e y n) p && acc) true = true := by
      cases hb : (List.range N).foldr
          (fun n acc => candidateAllows (stageCandidate A e y n) p && acc) true with
      | false => rw [hb] at hx; simp at hx
      | true => rfl
    exact ⟨N, happ, fun n hn => (foldr_and_true_iff _ _).mp hacc n (List.mem_range.mpr hn)⟩
  intro p hp q hq hpre
  by_contra hne
  obtain ⟨Np, hNp, haccp⟩ := hcert p hp
  obtain ⟨Nq, hNq, haccq⟩ := hcert q hq
  have hNneq : Np ≠ Nq := by
    intro h
    subst Nq
    exact hne (Option.some.inj (hNp.symm.trans hNq))
  -- The later appearance must pass the check against the earlier, distinct program.
  rcases lt_or_gt_of_ne hNneq with hlt | hgt
  · have hgood := haccq Np hlt
    simp [candidateAllows, hNp, hne, hpre] at hgood
  · have hgood := haccp Nq hgt
    simp [candidateAllows, hNq, Ne.symm hne, hpre] at hgood

/-- Every `A`-recursive decompressor `M` is evaluated by some oracle program `e`: exact
relative enumeration and persistence identify the searched evaluator `oracleEval A e` with the
numerical encoding of `M`. -/
private lemma exists_oracleEval_eq_mapToNatFun
    (A : Set ℕ) (M : Map) (hM : IsDecompressorIn (charOracle A) M) :
    ∃ e : ℕ, ∀ n : ℕ, oracleEval A e n = mapToNatFun M n := by
  have h_partrec : PartrecIn {charOracle A} (mapToNatFun M) := hM
  obtain ⟨e, he⟩ := oracleStage_universal A (mapToNatFun M) h_partrec
  refine ⟨e, ?_⟩
  intro n
  apply Part.ext
  intro v
  change v ∈ Nat.rfindOpt (fun t => oracleStage A t e n) ↔
    v ∈ mapToNatFun M n
  have hmono : ∀ {a t s : ℕ}, t ≤ s →
      a ∈ oracleStage A t e n → a ∈ oracleStage A s e n := by
    intro a t s hts ha
    exact Option.mem_def.mpr
      (oracleStage_persistent A e n a t s hts
        (Option.mem_def.mp ha))
  have hs :
      v ∈ Nat.rfindOpt (fun t => oracleStage A t e n) ↔
        ∃ t, oracleStage A t e n = some v := by
    simpa only [Option.mem_def] using
      (Nat.rfindOpt_mono hmono (a := v))
  exact hs.trans (he n v).symm

/-- If `oracleEval A e` evaluates the machine `M`, a program `p` appears as a candidate for the
context `y` at some dovetail index exactly when `M` halts on `(p, y)`. -/
private lemma exists_stageCandidate_eq_some_iff_dom
    (A : Set ℕ) (M : Map) (e : ℕ) (p y : BitString)
    (he : ∀ n : ℕ, oracleEval A e n = mapToNatFun M n) :
    (∃ n : ℕ, stageCandidate A e y n = some p) ↔ (M (p, y)).Dom := by
  classical
  have htest (o : Option ℕ) (q : BitString) :
      (if o.isSome then some q else none) = some p ↔
        q = p ∧ ∃ v, o = some v := by
    cases o <;> simp
  have hencoded : mapToNatFun M (Encodable.encode (p, y)) =
      (M (p, y)).map Encodable.encode := by
    simp only [mapToNatFun, Encodable.encodek, Part.ofOption,
      Part.bind_some]
  have hdom : (oracleEval A e (Encodable.encode (p, y))).Dom ↔
      (M (p, y)).Dom := by
    rw [he (Encodable.encode (p, y)), hencoded]
    rfl
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨q, _hq, hc⟩ := Option.bind_eq_some_iff.mp hn
    obtain ⟨hqp, v, hv⟩ :=
      (htest (oracleStage A (n.unpair.2 + 1) e
        (Encodable.encode (q, y))) q).mp hc
    subst q
    apply hdom.mp
    change (Nat.rfindOpt
      (fun t => oracleStage A t e (Encodable.encode (p, y)))).Dom
    exact Nat.rfindOpt_dom.mpr
      ⟨n.unpair.2 + 1, v, Option.mem_def.mpr hv⟩
  · intro hM
    have hd := hdom.mpr hM
    change (Nat.rfindOpt
      (fun t => oracleStage A t e
        (Encodable.encode (p, y)))).Dom at hd
    obtain ⟨t, v, hv⟩ := Nat.rfindOpt_dom.mp hd
    have hs := oracleStage_persistent A e
      (Encodable.encode (p, y)) v t (t + 1)
      (Nat.le_succ t) (Option.mem_def.mp hv)
    refine ⟨Nat.pair (Encodable.encode p) t, ?_⟩
    simp only [stageCandidate, Nat.unpair_pair, Encodable.encodek, Option.bind_some]
    exact (htest _ p).mpr ⟨rfl, v, hs⟩

/-- If `p` appears as a candidate at index `N` for a prefix machine `M` evaluated by
`oracleEval A e`, every acceptance check against the earlier candidates succeeds: all
candidates lie in the prefix-free domain of `M(·, y)`, so none is a distinct comparable
program. -/
private lemma foldr_candidateAllows_eq_true
    (A : Set ℕ) (M : Map) (e : ℕ) (p y : BitString) (N : ℕ)
    (he : ∀ n : ℕ, oracleEval A e n = mapToNatFun M n)
    (hPre : IsPrefixMachine M) (hN : stageCandidate A e y N = some p) :
    (List.range N).foldr
      (fun n acc => candidateAllows (stageCandidate A e y n) p && acc) true = true := by
  rw [foldr_and_true_iff]
  intro n _
  cases hn : stageCandidate A e y n with
  | none => rfl
  | some q =>
    simp only [candidateAllows, decide_eq_true_eq]
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp
      ((exists_stageCandidate_eq_some_iff_dom A M e p y he).mp ⟨N, hN⟩)
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp
      ((exists_stageCandidate_eq_some_iff_dom A M e q y he).mp ⟨n, hn⟩)
    rintro ⟨hneq, hpre | hpre⟩
    · exact hneq (IsPrefixMachine.eq_of_prefix hPre hz hx hpre)
    · exact hneq (IsPrefixMachine.eq_of_prefix hPre hx hz hpre).symm

/-- The decoded output of the oracle evaluation of an encoded input is the output of the
machine `M` that `oracleEval A e` evaluates. -/
private lemma map_decode_oracleEval_eq
    (A : Set ℕ) (M : Map) (e : ℕ) (pr : BitString × BitString)
    (he : ∀ n : ℕ, oracleEval A e n = mapToNatFun M n) :
    (oracleEval A e (Encodable.encode pr)).map
      (fun r => (Encodable.decode r : Option BitString).getD []) = M pr := by
  ext b
  rw [he (Encodable.encode pr)]
  simp [mapToNatFun, Encodable.encodek]

/-- Filtering the oracle evaluation of an exactly represented prefix machine does not change
it: every genuine candidate passes the prefix filter. -/
private lemma oraclePrefixFilter_eq_of_oracleEval_eq
    (A : Set ℕ) (M : Map) (e : ℕ)
    (he : ∀ n : ℕ, oracleEval A e n = mapToNatFun M n)
    (hPre : IsPrefixMachine M) :
    oraclePrefixFilter A e = M := by
  ext ⟨p, y⟩ r
  simp only [oraclePrefixFilter, Part.mem_bind_iff]
  constructor
  · rintro ⟨N, hN, hr⟩
    have hcand := of_decide_eq_true (Part.mem_some_iff.mp (Nat.rfind_spec hN)).symm
    rw [foldr_candidateAllows_eq_true A M e p y N he hPre hcand, Bool.cond_true,
      map_decode_oracleEval_eq A M e (p, y) he] at hr
    exact hr
  · intro hr
    obtain ⟨N₀, hN₀⟩ := (exists_stageCandidate_eq_some_iff_dom A M e p y he).mpr
      (Part.dom_iff_mem.mpr ⟨r, hr⟩)
    have hdom : (Nat.rfind fun n =>
        Part.some (decide (stageCandidate A e y n = some p))).Dom :=
      Nat.rfind_dom.mpr ⟨N₀, Part.mem_some_iff.mpr (decide_eq_true hN₀).symm,
        fun _ => trivial⟩
    obtain ⟨N, hN⟩ := Part.dom_iff_mem.mp hdom
    have hcand := of_decide_eq_true (Part.mem_some_iff.mp (Nat.rfind_spec hN)).symm
    refine ⟨N, hN, ?_⟩
    rw [foldr_candidateAllows_eq_true A M e p y N he hPre hcand, Bool.cond_true,
      map_decode_oracleEval_eq A M e (p, y) he]
    exact hr

/-- The tagged union of the prefix filters simulates every `A`-recursive prefix decompressor
with an additive constant: the program `p` of `M` becomes the program `1^e 0 p`. -/
private lemma exists_KP_taggedUnion_le_add
    (A : Set ℕ) (M : Map) (hM : IsDecompressorIn (charOracle A) M) (hPre : IsPrefixMachine M) :
    ∃ c : ℕ, ∀ x y,
      KP (taggedUnion (oraclePrefixFilter A)) x y ≤ KP M x y + (c : ENat) := by
  obtain ⟨e, he⟩ := exists_oracleEval_eq_mapToNatFun A M hM
  have h_eq := oraclePrefixFilter_eq_of_oracleEval_eq A M e he hPre
  use e + 1
  intro x y
  cases eq_or_ne (KP M x y) ⊤ with
  | inl h_top =>
    rw [h_top]
    exact le_top
  | inr h_ne_top =>
    obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top h_ne_top
    have hp_prod_F : produces (oraclePrefixFilter A e) p y x := by
      rw [h_eq]
      exact hp_prod
    have h_le := taggedUnion_KP_le_of_produces hp_prod_F
    calc
      KP (taggedUnion (oraclePrefixFilter A)) x y
        ≤ ((e + 1 + programLength p : ℕ) : ENat) := h_le
      _ = (e + 1 : ENat) + (programLength p : ENat) := by
        push_cast
        rfl
      _ = (programLength p : ENat) + (e + 1 : ENat) := by
        exact add_comm (e + 1 : ENat) (programLength p : ENat)
      _ = KP M x y + (e + 1 : ENat) := by
        rw [hp_len]

/-- Every total characteristic oracle admits an optimal conditional prefix decompressor.
Blueprint node `oracle:universal`. -/
theorem exists_optimalOraclePrefix (A : Set ℕ) :
    ∃ U : Map, IsOptimalOraclePrefix A U := by
  use taggedUnion (oraclePrefixFilter A)
  refine ⟨isDecompressorIn_taggedUnion_oraclePrefixFilter A,
    isPrefixMachine_taggedUnion_oraclePrefixFilter A, ?_⟩
  intro D hD hPre
  exact exists_KP_taggedUnion_le_add A D hD hPre

/-- Fix one optimal conditional prefix machine for each oracle, once and for all.
Blueprint node `oracle:universal`. -/
noncomputable def optimalOraclePrefix (A : Set ℕ) : Map :=
  Classical.epsilon (IsOptimalOraclePrefix A)

/-- The chosen family has the asserted relative prefix optimality.
Blueprint node `oracle:universal`. -/
theorem exists_optimalOraclePrefix_spec (A : Set ℕ) :
    IsOptimalOraclePrefix A (optimalOraclePrefix A) := by
  exact Classical.epsilon_spec (exists_optimalOraclePrefix A)

/-- Dropping a unary length prefix `1^n 0` from `1^n 0 x` leaves `x`. -/
private lemma drop_replicate_append (n : Nat) (x : List Bool) :
    List.drop (n + 1) (List.replicate n true ++ false :: x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- If `p` is a prefix of `q` and the unary tag of `p` is terminated within `p`, then `p` and
`q` have the same unary tag length. -/
private lemma takeWhile_length_eq_of_prefix {p q : List Bool} (hpre : p <+: q)
    (h_bounds : (p.takeWhile id).length < p.length) :
    (p.takeWhile id).length = (q.takeWhile id).length := by
  induction p generalizing q
  · exact absurd h_bounds (by simp)
  · rename_i a p ih
    rcases hpre with ⟨t, rfl⟩
    cases h_a : a
    · -- a = false
      rfl
    · -- a = true
      subst h_a
      have h1 : (List.takeWhile id (true :: p)).length = (List.takeWhile id p).length + 1 := rfl
      have h2 : (List.takeWhile id (true :: p ++ t)).length =
          (List.takeWhile id (p ++ t)).length + 1 := rfl
      have h_bounds_p : (List.takeWhile id p).length < p.length := by
        rw [h1] at h_bounds
        have h3 : (true :: p).length = p.length + 1 := rfl
        omega
      have h_ih := ih (List.prefix_append p t) h_bounds_p
      rw [h1, h_ih, h2]

/-- The literal-output machine `simpleLenDecompressor` has a prefix-free domain. -/
private lemma simpleLenDecompressor_isPrefixMachine :
    IsPrefixMachine simpleLenDecompressor := by
  intro y p hp q hq hpre
  unfold simpleLenDecompressor at hp hq
  have hp' : simpleLenDecompressorOpt p ≠ (none : Option (List Bool)) := by
    intro h
    change (Part.ofOption (simpleLenDecompressorOpt p)).Dom at hp
    rw [h] at hp
    exact hp
  have hq' : simpleLenDecompressorOpt q ≠ (none : Option (List Bool)) := by
    intro h
    change (Part.ofOption (simpleLenDecompressorOpt q)).Dom at hq
    rw [h] at hq
    exact hq
  unfold simpleLenDecompressorOpt at hp' hq'
  cases h1 : (p.length == (p.takeWhile id).length + (p.takeWhile id).length + 1) <;>
    rw [h1] at hp'
  · exact absurd rfl hp'
  cases h2 : (q.length == (q.takeWhile id).length + (q.takeWhile id).length + 1) <;>
    rw [h2] at hq'
  · exact absurd rfl hq'
  have h1_eq := beq_iff_eq.mp h1
  have h2_eq := beq_iff_eq.mp h2
  have h_bounds : (p.takeWhile id).length < p.length := by omega
  have h_n_eq : (p.takeWhile id).length = (q.takeWhile id).length :=
    takeWhile_length_eq_of_prefix hpre h_bounds
  have h_len_eq : p.length = q.length := by
    rw [h1_eq, h2_eq, h_n_eq]
  rcases hpre with ⟨t, rfl⟩
  have ht : t = [] := by
    have h_len2 : p.length = (p ++ t).length := h_len_eq
    simp only [List.length_append] at h_len2
    cases t
    · rfl
    · simp at h_len2
  subst ht
  exact (List.append_nil p).symm

/-- A well-formed program `1^n 0 x` of `simpleLenDecompressor` outputs `x`. -/
private lemma simpleLenDecompressor_produces (p y : List Bool)
    (h : p.length = (p.takeWhile id).length + (p.takeWhile id).length + 1) :
    produces simpleLenDecompressor p y (p.drop ((p.takeWhile id).length + 1)) := by
  unfold produces simpleLenDecompressor
  have heq : simpleLenDecompressorOpt p = some (p.drop ((p.takeWhile id).length + 1)) := by
    unfold simpleLenDecompressorOpt
    rw [beq_iff_eq.mpr h]
    rfl
  change _ ∈ Part.ofOption (simpleLenDecompressorOpt p)
  rw [heq]
  exact ⟨trivial, rfl⟩

/-- The numerical encoding of a partial recursive decompressor is partial recursive. -/
private lemma partrec_mapToNatFun
    (D : Map) (hD : isDecompressor D) : Partrec (mapToNatFun D) := by
  unfold mapToNatFun
  have hd : Computable (fun n => Encodable.decode (α := BitString × BitString) n) :=
    Computable.decode
  have hopt : Partrec (fun n =>
      Part.ofOption (Encodable.decode (α := BitString × BitString) n)) :=
    Computable.ofOption hd
  have hmap : Partrec₂ (fun (n : ℕ) (a : BitString × BitString) =>
      (D a).map Encodable.encode) := by
    have h1 : Partrec (fun (pr : ℕ × (BitString × BitString)) => D pr.2) :=
      hD.comp Computable.snd
    have h2 : Computable (fun (pr : (ℕ × (BitString × BitString)) × BitString) =>
        Encodable.encode pr.2) :=
      Computable.encode.comp Computable.snd
    exact Partrec.map h1 h2
  exact Partrec.bind hopt hmap

/-- The literal-output machine `simpleLenDecompressor` is recursive in every oracle. -/
private lemma isDecompressorIn_simpleLenDecompressor (A : Set ℕ) :
    IsDecompressorIn (charOracle A) simpleLenDecompressor := by
  unfold IsDecompressorIn
  have h_partrec : Partrec (mapToNatFun simpleLenDecompressor) :=
    partrec_mapToNatFun simpleLenDecompressor simpleLenDecompressor_computable
  have h1 : PartrecIn {charOracle A} (mapToNatFun simpleLenDecompressor) :=
    Partrec.partrecIn h_partrec
  exact RecursiveIn.iff_nat.mpr (PartrecIn.iff_nat.mp h1)

/-- Literal descriptions make every conditional complexity of the chosen machine finite,
before any natural-valued shadow is introduced. Blueprint node `oracle:universal`. -/
theorem exists_optimalOraclePrefix_finite (A : Set ℕ) (x y : BitString) :
    KP (optimalOraclePrefix A) x y ≠ ⊤ := by
  obtain ⟨_, _, hU_optimality⟩ := exists_optimalOraclePrefix_spec A
  obtain ⟨c, hc⟩ := hU_optimality simpleLenDecompressor
    (isDecompressorIn_simpleLenDecompressor A)
    simpleLenDecompressor_isPrefixMachine
  let p := List.replicate x.length true ++ (false :: x)
  have h_p_take : (p.takeWhile id).length = x.length := by simp [p]
  have h_p_len : p.length = 2 * x.length + 1 := by simp [p]; omega
  have h_p_eq : p.length = (p.takeWhile id).length + (p.takeWhile id).length + 1 := by
    rw [h_p_take, h_p_len]; omega
  have h_prod := simpleLenDecompressor_produces p y h_p_eq
  have h_drop : p.drop ((p.takeWhile id).length + 1) = x := by
    rw [h_p_take]; exact drop_replicate_append x.length x
  rw [h_drop] at h_prod
  have h_KP := KP_le_programLength_of_produces h_prod
  have h_c := hc x y
  have h_le : KP (optimalOraclePrefix A) x y ≤ ((2 * x.length + 1 : ℕ) : ENat) + c := by
    calc KP (optimalOraclePrefix A) x y ≤ KP simpleLenDecompressor x y + c := h_c
    _ ≤ (p.length : ENat) + c := by gcongr
    _ = ((2 * x.length + 1 : ℕ) : ENat) + c := by rw [h_p_len]
  have h_fin : ((2 * x.length + 1 : ℕ) : ENat) + c ≠ ⊤ := ENat.natCast_ne_top _
  exact ne_top_of_le_ne_top h_fin h_le

end Kolmogorov.PointToSet
