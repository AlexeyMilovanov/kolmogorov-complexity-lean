import KolmogorovMathlib.Multisource.ConditionalEncoding.ShortestDescription

/-!
# Counting conditional programs: the strengthened form of Problem 317

SUV Problem 317, p. 369 (strengthened form).

The stronger bound `C(P | A, B) = O(log C(A|B))` for a shortest description `P` of `A` given
`B` (`condK_conditionalShortestDescription_le_log_length`).  The conditional programs producing
`A` from `B` are enumerated in computable stages; when many programs of one length produce `A`,
a decoder that ranks the heavy outputs gives `A` a shorter description, so only few programs
of the shortest length exist, and a shortest one is described by its stable rank in the
enumeration together with its length.
-/

namespace Kolmogorov

/-- The programs of one fixed length that produce `A` from `B` form a finite set. -/
private theorem conditionalProgramsOfLength_finite (D : Map) (A B : BitString) (n : ℕ) :
    ({P : BitString | produces D P B A ∧ P.length = n} : Set BitString).Finite := by
  refine ((allStrings n).toFinset.finite_toSet).subset ?_
  intro P hP
  rw [Finset.mem_coe, List.mem_toFinset, mem_allStrings]
  exact hP.2

private abbrev ConditionalProgramStageArg :=
  ((ℕ × BitString) × BitString) × ℕ

/-- The run of the code `c` on the program `P` with condition `B` for `t` steps. -/
private def condRun (c : Nat.Partrec.Code) (t : ℕ) (B P : BitString) : Option BitString :=
  (Nat.Partrec.Code.evaln t c (Encodable.encode (P, B))).bind
    (fun r => (Encodable.decode r : Option BitString))

/-- The program `P` has produced `A` from `B` within `t` steps. -/
private def condOk (c : Nat.Partrec.Code) (x : (ℕ × BitString) × BitString) (t : ℕ)
    (P : BitString) : Bool :=
  decide (condRun c t x.2 P = some x.1.2)

/-- The program `P` produces `A` from `B` for the first time at step `t`. -/
private def condNewAt (c : Nat.Partrec.Code) (x : (ℕ × BitString) × BitString) (t : ℕ)
    (P : BitString) : Bool :=
  condOk c x t P && (decide (t = 0) || !condOk c x (t - 1) P)

/-- The block of step `t`: the programs of length `n` that first succeed at step `t`. -/
private def condBlock (c : Nat.Partrec.Code) (x : (ℕ × BitString) × BitString) (t : ℕ) :
    List BitString :=
  (exactLengthPrograms x.1.1).filter (condNewAt c x t)

/-- The dovetailed history: the blocks of the steps `0, ..., s`, in order. -/
private def condStage (c : Nat.Partrec.Code) (a : ConditionalProgramStageArg) :
    List BitString :=
  (List.range (a.2 + 1)).flatMap (condBlock c a.1)

/-- The bounded run is primitive recursive. -/
private theorem condRun_primrec (c : Nat.Partrec.Code) :
    Primrec (fun q : ((ℕ × BitString) × BitString × BitString) =>
      condRun c q.1.1 q.2.1 q.2.2) := by
  have h1 : Primrec (fun q : ((ℕ × BitString) × BitString × BitString) =>
      Nat.Partrec.Code.evaln q.1.1 c (Encodable.encode (q.2.2, q.2.1))) :=
    (evaln_primrec c).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.encode.comp ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd)))
  exact Primrec.option_bind h1 (Primrec.decode.comp Primrec.snd)

/-- The success test is primitive recursive. -/
private theorem condOk_primrec (c : Nat.Partrec.Code) :
    Primrec (fun q : ((ℕ × BitString) × BitString) × ℕ × BitString =>
      condOk c q.1 q.2.1 q.2.2) := by
  have hrun : Primrec (fun q : ((ℕ × BitString) × BitString) × ℕ × BitString =>
      condRun c q.2.1 q.1.2 q.2.2) :=
    (condRun_primrec c).comp
      (((Primrec.fst.comp Primrec.snd).pair (Primrec.const ([] : BitString))).pair
        ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd)))
  have hA : Primrec (fun q : ((ℕ × BitString) × BitString) × ℕ × BitString =>
      (some q.1.1.2 : Option BitString)) :=
    Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact PrimrecPred.decide (PrimrecRel.comp (@Primrec.eq (Option BitString) _) hrun hA)

/-- The first-success test is primitive recursive. -/
private theorem condNewAt_primrec (c : Nat.Partrec.Code) :
    Primrec (fun q : ((ℕ × BitString) × BitString) × ℕ × BitString =>
      condNewAt c q.1 q.2.1 q.2.2) := by
  have hok := condOk_primrec c
  have hprev : Primrec (fun q : ((ℕ × BitString) × BitString) × ℕ × BitString =>
      condOk c q.1 (q.2.1 - 1) q.2.2) :=
    hok.comp (Primrec.fst.pair
      ((Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).pair
        (Primrec.snd.comp Primrec.snd)))
  have hzero : Primrec (fun q : ((ℕ × BitString) × BitString) × ℕ × BitString =>
      decide (q.2.1 = 0)) :=
    PrimrecPred.decide (PrimrecRel.comp (@Primrec.eq ℕ _) (Primrec.fst.comp Primrec.snd)
      (Primrec.const 0))
  have hnot : Primrec (fun q : ((ℕ × BitString) × BitString) × ℕ × BitString =>
      !condOk c q.1 (q.2.1 - 1) q.2.2) := Primrec.not.comp hprev
  have hor : Primrec (fun q : ((ℕ × BitString) × BitString) × ℕ × BitString =>
      (decide (q.2.1 = 0) || !condOk c q.1 (q.2.1 - 1) q.2.2)) := Primrec.or.comp hzero hnot
  exact Primrec.and.comp hok hor

/-- The step blocks are primitive recursive. -/
private theorem condBlock_primrec (c : Nat.Partrec.Code) :
    Primrec (fun q : ((ℕ × BitString) × BitString) × ℕ => condBlock c q.1 q.2) := by
  have hlist : Primrec (fun q : ((ℕ × BitString) × BitString) × ℕ =>
      exactLengthPrograms q.1.1.1) :=
    primrec_exactLengthPrograms.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have harg : Primrec (fun p : (((ℕ × BitString) × BitString) × ℕ) × BitString =>
      ((p.1.1, p.1.2, p.2) : ((ℕ × BitString) × BitString) × ℕ × BitString)) :=
    (Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  have hpred : Primrec (fun p : (((ℕ × BitString) × BitString) × ℕ) × BitString =>
      condNewAt c p.1.1 p.1.2 p.2) :=
    (condNewAt_primrec c).comp harg
  exact Primrec.list_filter hlist hpred.to₂

/-- The dovetailed history is computable. -/
private theorem condStage_computable (c : Nat.Partrec.Code) : Computable (condStage c) := by
  have hblock : Primrec (fun p : ConditionalProgramStageArg × ℕ => condBlock c p.1.1 p.2) :=
    (condBlock_primrec c).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hrange : Primrec (fun a : ConditionalProgramStageArg => List.range (a.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
  exact (Primrec.list_flatMap hrange hblock.to₂).to_comp

/-- Success is monotone in the step bound. -/
private theorem condOk_mono (c : Nat.Partrec.Code) (x : (ℕ × BitString) × BitString)
    (P : BitString) {t u : ℕ} (htu : t ≤ u) (h : condOk c x t P = true) :
    condOk c x u P = true := by
  unfold condOk condRun at *
  rw [decide_eq_true_eq] at *
  rcases hv : Nat.Partrec.Code.evaln t c (Encodable.encode (P, x.2)) with _ | v
  · rw [hv] at h
    simp at h
  · have hu := Nat.Partrec.Code.evaln_mono htu (Option.mem_def.mpr hv)
    rw [Option.mem_def] at hu
    rw [hu, ← hv]
    exact h

/-- Success at some step is exactly production by `D`. -/
private theorem exists_condOk_iff (D : Map) (c : Nat.Partrec.Code)
    (hc : c.eval = fun m => (Part.ofOption (Encodable.decode m)).bind
      (fun a => Part.map Encodable.encode (D a)))
    (n : ℕ) (A B P : BitString) :
    (∃ t, condOk c ((n, A), B) t P = true) ↔ produces D P B A := by
  have heval : c.eval (Encodable.encode (P, B)) = Part.map Encodable.encode (D (P, B)) := by
    rw [hc]
    simp [Encodable.encodek]
  constructor
  · rintro ⟨t, ht⟩
    unfold condOk condRun at ht
    rw [decide_eq_true_eq] at ht
    rcases hv : Nat.Partrec.Code.evaln t c (Encodable.encode (P, B)) with _ | v
    · rw [hv] at ht
      simp at ht
    · rw [hv] at ht
      have hs := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)
      rw [heval] at hs
      rcases hs with ⟨hdom, hget⟩
      have hget' : Encodable.encode ((D (P, B)).get hdom) = v := hget
      subst hget'
      simp only [Option.bind_some, Encodable.encodek, Option.some.injEq] at ht
      rw [← ht]
      exact Part.get_mem (show (D (P, B)).Dom from hdom)
  · intro hP
    have hm : Encodable.encode A ∈ c.eval (Encodable.encode (P, B)) := by
      rw [heval]
      exact Part.mem_map _ hP
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hm
    refine ⟨t, ?_⟩
    unfold condOk condRun
    rw [decide_eq_true_eq, Option.mem_def.mp ht]
    simp [Encodable.encodek]

/-- One more step appends one block. -/
private theorem condStage_succ (c : Nat.Partrec.Code) (x : (ℕ × BitString) × BitString)
    (s : ℕ) : condStage c (x, s + 1) = condStage c (x, s) ++ condBlock c x (s + 1) := by
  unfold condStage
  rw [List.range_succ, List.flatMap_append]
  simp

/-- Membership in the history: a program of length `n` that first succeeds by step `s`. -/
private theorem mem_condStage (c : Nat.Partrec.Code) (x : (ℕ × BitString) × BitString)
    (s : ℕ) (P : BitString) :
    P ∈ condStage c (x, s) ↔
      P ∈ exactLengthPrograms x.1.1 ∧ ∃ t, t ≤ s ∧ condNewAt c x t P = true := by
  unfold condStage condBlock
  simp only [List.mem_flatMap, List.mem_range, List.mem_filter]
  constructor
  · rintro ⟨t, ht, hP, hnew⟩
    exact ⟨hP, t, by omega, hnew⟩
  · rintro ⟨hP, t, ht, hnew⟩
    exact ⟨t, by omega, hP, hnew⟩

/-- The history is duplicate-free. -/
private theorem condStage_nodup (c : Nat.Partrec.Code) (x : (ℕ × BitString) × BitString)
    (s : ℕ) : (condStage c (x, s)).Nodup := by
  induction s with
  | zero =>
    unfold condStage
    simpa [condBlock] using (exactLengthPrograms_nodup x.1.1).filter _
  | succ s ih =>
    rw [condStage_succ, List.nodup_append]
    refine ⟨ih, (exactLengthPrograms_nodup x.1.1).filter _, ?_⟩
    intro P hP Q hQ hPQ
    subst hPQ
    obtain ⟨_, t, hts, hnew⟩ := (mem_condStage c x s P).1 hP
    have hnew' : condNewAt c x (s + 1) P = true := (List.mem_filter.1 hQ).2
    unfold condNewAt at hnew hnew'
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      at hnew hnew'
    have hoks : condOk c x s P = true := condOk_mono c x P hts hnew.1
    rcases hnew'.2 with h0 | hnot
    · omega
    · simp only [Nat.add_sub_cancel] at hnot
      rw [hoks] at hnot
      exact Bool.noConfusion hnot

/-- Parameters `((B, n), k)` of the enumeration of outputs with many programs. -/
private abbrev HeavyParam := (BitString × ℕ) × ℕ

/-- The number of programs of length `n` that have produced `A` from `B` within `t` steps. -/
private def heavyCount (c : Nat.Partrec.Code) (B : BitString) (n t : ℕ) (A : BitString) : ℕ :=
  ((exactLengthPrograms n).filter (fun P => decide (condRun c t B P = some A))).length

/-- By step `t`, `A` has at least `2^k` programs of length `n` given `B`. -/
private def heavyAt (c : Nat.Partrec.Code) (q : HeavyParam) (t : ℕ) (A : BitString) : Bool :=
  decide (2 ^ q.2 ≤ heavyCount c q.1.1 q.1.2 t A)

/-- `A` becomes heavy exactly at step `t`. -/
private def heavyNew (c : Nat.Partrec.Code) (q : HeavyParam) (t : ℕ) (A : BitString) : Bool :=
  heavyAt c q t A && (decide (t = 0) || !heavyAt c q (t - 1) A)

/-- The outputs seen at step `t`, without repetitions. -/
private def heavyOutputs (c : Nat.Partrec.Code) (q : HeavyParam) (t : ℕ) : List BitString :=
  ((exactLengthPrograms q.1.2).filterMap (fun P => condRun c t q.1.1 P)).eraseDups

/-- The outputs that become heavy at step `t`. -/
private def heavyBlock (c : Nat.Partrec.Code) (q : HeavyParam) (t : ℕ) : List BitString :=
  (heavyOutputs c q t).filter (heavyNew c q t)

/-- The history of heavy outputs up to step `s`. -/
private def heavyStage (c : Nat.Partrec.Code) (a : HeavyParam × ℕ) : List BitString :=
  (List.range (a.2 + 1)).flatMap (heavyBlock c a.1)

/-- The bounded run is monotone in the step bound. -/
private theorem condRun_mono (c : Nat.Partrec.Code) {t u : ℕ} (htu : t ≤ u)
    {B P A : BitString} (h : condRun c t B P = some A) : condRun c u B P = some A := by
  unfold condRun at *
  rcases hv : Nat.Partrec.Code.evaln t c (Encodable.encode (P, B)) with _ | v
  · rw [hv] at h
    simp at h
  · have hu := Nat.Partrec.Code.evaln_mono htu (Option.mem_def.mpr hv)
    rw [Option.mem_def] at hu
    rw [hu, ← hv]
    exact h

/-- Testing a bounded run against a prescribed output is primitive recursive. -/
private theorem condRunEq_primrec (c : Nat.Partrec.Code) :
    Primrec (fun q : ((ℕ × BitString) × BitString × BitString) × BitString =>
      decide (condRun c q.1.1.1 q.1.2.1 q.1.2.2 = some q.2)) := by
  have hrun : Primrec (fun q : ((ℕ × BitString) × BitString × BitString) × BitString =>
      condRun c q.1.1.1 q.1.2.1 q.1.2.2) :=
    (condRun_primrec c).comp Primrec.fst
  have hA : Primrec (fun q : ((ℕ × BitString) × BitString × BitString) × BitString =>
      (some q.2 : Option BitString)) :=
    Primrec.option_some.comp Primrec.snd
  exact PrimrecPred.decide (PrimrecRel.comp (@Primrec.eq (Option BitString) _) hrun hA)

/-- The single-program test of the program count is primitive recursive. -/
private theorem heavyPred_primrec (c : Nat.Partrec.Code) :
    Primrec (fun p : ((((BitString × ℕ) × ℕ) × ℕ) × BitString) × BitString =>
      decide (condRun c p.1.1.2 p.1.1.1.1.1 p.2 = some p.1.2)) := by
  have hT : Primrec (fun p : ((((BitString × ℕ) × ℕ) × ℕ) × BitString) × BitString => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hB : Primrec (fun p : ((((BitString × ℕ) × ℕ) × ℕ) × BitString) × BitString =>
      p.1.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hA : Primrec (fun p : ((((BitString × ℕ) × ℕ) × ℕ) × BitString) × BitString => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have harg : Primrec (fun p : ((((BitString × ℕ) × ℕ) × ℕ) × BitString) × BitString =>
      ((((p.1.1.2, ([] : BitString)), (p.1.1.1.1.1, p.2)), p.1.2) :
        ((ℕ × BitString) × BitString × BitString) × BitString)) :=
    ((hT.pair (Primrec.const [])).pair (hB.pair Primrec.snd)).pair hA
  have h := (condRunEq_primrec c).comp harg
  exact h

/-- The filtered program list is primitive recursive. -/
private theorem heavyList_primrec (c : Nat.Partrec.Code) :
    Primrec (fun r : (HeavyParam × ℕ) × BitString =>
      (exactLengthPrograms r.1.1.1.2).filter
        (fun P => decide (condRun c r.1.2 r.1.1.1.1 P = some r.2))) := by
  have hlist : Primrec (fun r : (HeavyParam × ℕ) × BitString =>
      exactLengthPrograms r.1.1.1.2) :=
    primrec_exactLengthPrograms.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hpred : Primrec₂ (fun (r : (HeavyParam × ℕ) × BitString) (P : BitString) =>
      decide (condRun c r.1.2 r.1.1.1.1 P = some r.2)) :=
    (heavyPred_primrec c).to₂
  exact Primrec.list_filter hlist hpred

/-- The program count is primitive recursive. -/
private theorem heavyCount_primrec (c : Nat.Partrec.Code) :
    Primrec (fun r : (HeavyParam × ℕ) × BitString =>
      heavyCount c r.1.1.1.1 r.1.1.1.2 r.1.2 r.2) :=
  Primrec.list_length.comp (heavyList_primrec c)

/-- The heaviness test is primitive recursive. -/
private theorem heavyAt_primrec (c : Nat.Partrec.Code) :
    Primrec (fun r : (HeavyParam × ℕ) × BitString => heavyAt c r.1.1 r.1.2 r.2) := by
  have hpow2 : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow
  have hpow : Primrec (fun r : (HeavyParam × ℕ) × BitString => 2 ^ r.1.1.2) :=
    hpow2.comp (Primrec.const 2) (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact PrimrecPred.decide (PrimrecRel.comp Primrec.nat_le hpow (heavyCount_primrec c))

/-- The first-heaviness test is primitive recursive. -/
private theorem heavyNew_primrec (c : Nat.Partrec.Code) :
    Primrec (fun r : (HeavyParam × ℕ) × BitString => heavyNew c r.1.1 r.1.2 r.2) := by
  have hok := heavyAt_primrec c
  have harg : Primrec (fun r : (HeavyParam × ℕ) × BitString =>
      (((r.1.1, r.1.2 - 1), r.2) : (HeavyParam × ℕ) × BitString)) :=
    ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1))).pair Primrec.snd
  have hprev : Primrec (fun r : (HeavyParam × ℕ) × BitString =>
      heavyAt c r.1.1 (r.1.2 - 1) r.2) := hok.comp harg
  have hzero : Primrec (fun r : (HeavyParam × ℕ) × BitString => decide (r.1.2 = 0)) :=
    PrimrecPred.decide (PrimrecRel.comp (@Primrec.eq ℕ _) (Primrec.snd.comp Primrec.fst)
      (Primrec.const 0))
  have hnot : Primrec (fun r : (HeavyParam × ℕ) × BitString =>
      !heavyAt c r.1.1 (r.1.2 - 1) r.2) := Primrec.not.comp hprev
  have hor : Primrec (fun r : (HeavyParam × ℕ) × BitString =>
      (decide (r.1.2 = 0) || !heavyAt c r.1.1 (r.1.2 - 1) r.2)) := Primrec.or.comp hzero hnot
  exact Primrec.and.comp hok hor

/-- The outputs seen at a step are primitive recursive. -/
private theorem heavyOutputs_primrec (c : Nat.Partrec.Code) :
    Primrec (fun r : HeavyParam × ℕ => heavyOutputs c r.1 r.2) := by
  have hlist : Primrec (fun r : HeavyParam × ℕ => exactLengthPrograms r.1.1.2) :=
    primrec_exactLengthPrograms.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have harg : Primrec (fun p : (HeavyParam × ℕ) × BitString =>
      (((p.1.2, ([] : BitString)), (p.1.1.1.1, p.2)) :
        (ℕ × BitString) × BitString × BitString)) :=
    ((Primrec.snd.comp Primrec.fst).pair (Primrec.const [])).pair
      ((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd)
  have hf : Primrec (fun p : (HeavyParam × ℕ) × BitString => condRun c p.1.2 p.1.1.1.1 p.2) :=
    (condRun_primrec c).comp harg
  have hfm : Primrec (fun r : HeavyParam × ℕ =>
      (exactLengthPrograms r.1.1.2).filterMap (fun P => condRun c r.2 r.1.1.1 P)) :=
    Primrec.listFilterMap hlist hf.to₂
  exact CodedFiniteDistribution.eraseDups_bitstring_primrec.comp hfm

/-- The heavy history is computable. -/
private theorem heavyStage_computable (c : Nat.Partrec.Code) : Computable (heavyStage c) := by
  have hblock : Primrec (fun r : HeavyParam × ℕ => heavyBlock c r.1 r.2) :=
    Primrec.list_filter (heavyOutputs_primrec c) (heavyNew_primrec c).to₂
  have hblock' : Primrec (fun p : (HeavyParam × ℕ) × ℕ => heavyBlock c p.1.1 p.2) :=
    hblock.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hrange : Primrec (fun a : HeavyParam × ℕ => List.range (a.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
  exact (Primrec.list_flatMap hrange hblock'.to₂).to_comp

/-- Program counts grow with the step bound. -/
private theorem heavyCount_mono (c : Nat.Partrec.Code) (B : BitString) (n : ℕ) {t u : ℕ}
    (htu : t ≤ u) (A : BitString) : heavyCount c B n t A ≤ heavyCount c B n u A := by
  unfold heavyCount
  refine (List.monotone_filter_right _ (fun P h => ?_)).length_le
  rw [decide_eq_true_eq] at h ⊢
  exact condRun_mono c htu h

/-- Heaviness persists. -/
private theorem heavyAt_mono (c : Nat.Partrec.Code) (q : HeavyParam) {t u : ℕ} (htu : t ≤ u)
    {A : BitString} (h : heavyAt c q t A = true) : heavyAt c q u A = true := by
  unfold heavyAt at *
  rw [decide_eq_true_eq] at *
  exact h.trans (heavyCount_mono c _ _ htu A)

/-- One more step appends one block. -/
private theorem heavyStage_succ (c : Nat.Partrec.Code) (q : HeavyParam) (s : ℕ) :
    heavyStage c (q, s + 1) = heavyStage c (q, s) ++ heavyBlock c q (s + 1) := by
  unfold heavyStage
  rw [List.range_succ, List.flatMap_append]
  simp

/-- Membership in the heavy history. -/
private theorem mem_heavyStage (c : Nat.Partrec.Code) (q : HeavyParam) (s : ℕ)
    (A : BitString) :
    A ∈ heavyStage c (q, s) ↔
      ∃ t, t ≤ s ∧ A ∈ heavyOutputs c q t ∧ heavyNew c q t A = true := by
  unfold heavyStage heavyBlock
  simp only [List.mem_flatMap, List.mem_range, List.mem_filter]
  constructor
  · rintro ⟨t, ht, hA, hnew⟩
    exact ⟨t, by omega, hA, hnew⟩
  · rintro ⟨t, ht, hA, hnew⟩
    exact ⟨t, by omega, hA, hnew⟩

/-- Every member of the history is heavy at its stage. -/
private theorem heavyAt_of_mem_heavyStage (c : Nat.Partrec.Code) (q : HeavyParam) (s : ℕ)
    {A : BitString} (hA : A ∈ heavyStage c (q, s)) : heavyAt c q s A = true := by
  obtain ⟨t, hts, _, hnew⟩ := (mem_heavyStage c q s A).1 hA
  simp only [heavyNew, Bool.and_eq_true] at hnew
  exact heavyAt_mono c q hts hnew.1

/-- The heavy history is duplicate-free. -/
private theorem heavyStage_nodup (c : Nat.Partrec.Code) (q : HeavyParam) (s : ℕ) :
    (heavyStage c (q, s)).Nodup := by
  induction s with
  | zero =>
    unfold heavyStage
    simpa [heavyBlock, heavyOutputs] using (nodup_eraseDups_list _).filter _
  | succ s ih =>
    rw [heavyStage_succ, List.nodup_append]
    refine ⟨ih, (nodup_eraseDups_list _).filter _, ?_⟩
    intro A hA A' hA' hAA'
    subst hAA'
    have hheavy := heavyAt_of_mem_heavyStage c q s hA
    have hnew' : heavyNew c q (s + 1) A = true := (List.mem_filter.1 hA').2
    simp only [heavyNew, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at hnew'
    rcases hnew'.2 with h0 | hnot
    · omega
    · simp only [Nat.add_sub_cancel] at hnot
      rw [hheavy] at hnot
      exact Bool.noConfusion hnot

/-- The heavy history grows by prefixes. -/
private theorem heavyStage_prefix (c : Nat.Partrec.Code) (q : HeavyParam) {s t : ℕ}
    (hst : s ≤ t) : heavyStage c (q, s) <+: heavyStage c (q, t) := by
  induction t, hst using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
    rw [heavyStage_succ]
    exact ih.trans (List.prefix_append _ _)

/-- Few outputs have many programs: at most `2^(n-k)` outputs have `2^k` programs of
length `n`, since their program sets are disjoint. -/
private theorem heavyStage_length_le (c : Nat.Partrec.Code) (B : BitString) (n k s : ℕ)
    (hkn : k ≤ n) : (heavyStage c (((B, n), k), s)).length ≤ 2 ^ (n - k) := by
  classical
  set L := heavyStage c (((B, n), k), s) with hL
  have hnd : L.Nodup := heavyStage_nodup c _ s
  have hheavy : ∀ A ∈ L, 2 ^ k ≤ heavyCount c B n s A := by
    intro A hA
    have h := heavyAt_of_mem_heavyStage c _ s hA
    simpa [heavyAt] using h
  let S : Finset BitString := (exactLengthPrograms n).toFinset
  let T : BitString → Finset BitString := fun A => S.filter (fun P => condRun c s B P = some A)
  have hT : ∀ A, heavyCount c B n s A = (T A).card := by
    intro A
    unfold heavyCount
    rw [← List.toFinset_card_of_nodup ((exactLengthPrograms_nodup n).filter _),
      List.toFinset_filter]
    simp [T, S]
  have hdisj : (↑L.toFinset : Set BitString).PairwiseDisjoint T := by
    intro A _ A' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro P hP hP'
    simp only [T, Finset.mem_filter] at hP hP'
    exact hne (Option.some.inj (hP.2.symm.trans hP'.2))
  have hsub : L.toFinset.biUnion T ⊆ S :=
    Finset.biUnion_subset.2 (fun A _ => Finset.filter_subset _ _)
  have hsum : ∑ A ∈ L.toFinset, (T A).card ≤ 2 ^ n := by
    rw [← Finset.card_biUnion hdisj]
    calc (L.toFinset.biUnion T).card ≤ S.card := Finset.card_le_card hsub
      _ = 2 ^ n := by
        rw [List.toFinset_card_of_nodup (exactLengthPrograms_nodup n),
          length_exactLengthPrograms]
  have hlow : L.toFinset.card • 2 ^ k ≤ ∑ A ∈ L.toFinset, (T A).card :=
    Finset.card_nsmul_le_sum _ _ _ (fun A hA => (hT A) ▸ hheavy A (List.mem_toFinset.1 hA))
  rw [List.toFinset_card_of_nodup hnd, smul_eq_mul] at hlow
  have h2 : L.length * 2 ^ k ≤ 2 ^ (n - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
    omega
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

/-- An output with `2^k` programs of length `n` eventually enters the heavy history. -/
private theorem exists_mem_heavyStage (D : Map) (c : Nat.Partrec.Code)
    (hc : c.eval = fun m => (Part.ofOption (Encodable.decode m)).bind
      (fun a => Part.map Encodable.encode (D a)))
    (A B : BitString) (n k : ℕ)
    (hfin : ({P : BitString | produces D P B A ∧ P.length = n} : Set BitString).Finite)
    (hcard : 2 ^ k ≤
      ({P : BitString | produces D P B A ∧ P.length = n} : Set BitString).ncard) :
    ∃ s, A ∈ heavyStage c (((B, n), k), s) := by
  classical
  have hex : ∃ t, heavyAt c ((B, n), k) t A = true := by
    have hstep : ∀ P ∈ hfin.toFinset, ∃ t, condRun c t B P = some A := by
      intro P hP
      have hP' := (hfin.mem_toFinset.1 hP).1
      obtain ⟨t, ht⟩ := (exists_condOk_iff D c hc 0 A B P).2 hP'
      exact ⟨t, by simpa [condOk] using ht⟩
    choose! f hf using hstep
    refine ⟨hfin.toFinset.sup f, ?_⟩
    simp only [heavyAt, decide_eq_true_eq]
    refine hcard.trans ?_
    have hsub : ({P : BitString | produces D P B A ∧ P.length = n} : Set BitString) ⊆
        (((exactLengthPrograms n).filter (fun P =>
          decide (condRun c (hfin.toFinset.sup f) B P = some A))).toFinset :
            Set BitString) := by
      intro P hP
      have hPS : P ∈ hfin.toFinset := hfin.mem_toFinset.2 hP
      rw [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨hP.2 ▸ mem_exactLengthPrograms_self P,
        condRun_mono c (Finset.le_sup hPS) (hf P hPS)⟩
    calc _ ≤ _ := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = _ := Set.ncard_coe_finset _
      _ ≤ heavyCount c B n (hfin.toFinset.sup f) A := List.toFinset_card_le _
  let t0 := Nat.find hex
  have ht0 : heavyAt c ((B, n), k) t0 A = true := Nat.find_spec hex
  refine ⟨t0, (mem_heavyStage c _ t0 A).2 ⟨t0, le_rfl, ?_, ?_⟩⟩
  · have hcnt : 2 ^ k ≤ heavyCount c B n t0 A := by simpa [heavyAt] using ht0
    have hpos : 0 < heavyCount c B n t0 A := lt_of_lt_of_le (Nat.two_pow_pos k) hcnt
    obtain ⟨P, hP⟩ := List.exists_mem_of_length_pos hpos
    rw [List.mem_filter, decide_eq_true_eq] at hP
    unfold heavyOutputs
    rw [mem_eraseDups_list, List.mem_filterMap]
    exact ⟨P, hP.1, hP.2⟩
  · simp only [heavyNew, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true']
    refine ⟨ht0, ?_⟩
    by_cases h0 : t0 = 0
    · exact Or.inl h0
    · right
      have hlt : t0 - 1 < t0 := by omega
      have hmin := Nat.find_min hex hlt
      simpa using hmin

/-- The stage key `((B, n), k)` read off a code `pairCode (bits k) w` with `l(w) = n - k`. -/
private def heavyKey (py : BitString × BitString) : HeavyParam :=
  ((py.2, (decodeSecond py.1).length + bitsToNat (decodeFirst py.1)),
    bitsToNat (decodeFirst py.1))

/-- The index read off the payload `w`. -/
private def heavyIdx (py : BitString × BitString) : ℕ := bitsToNat (decodeSecond py.1)

/-- The decoder: wait until the index appears in the heavy history, return its entry. -/
private def heavyDecoder (c : Nat.Partrec.Code) : Map :=
  fun py => (Nat.rfind (fun s =>
      Part.some (decide (heavyIdx py < (heavyStage c (heavyKey py, s)).length)))).bind
    (fun s => Part.ofOption ((heavyStage c (heavyKey py, s))[heavyIdx py]?))

/-- The decoder is partial recursive. -/
private theorem heavyDecoder_isDecompressor (c : Nat.Partrec.Code) :
    isDecompressor (heavyDecoder c) := by
  have hkF : Computable (fun py : BitString × BitString => bitsToNat (decodeFirst py.1)) :=
    bitsToNat_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst)
  have hkey : Computable heavyKey :=
    (Computable.snd.pair (Primrec.nat_add.to_comp.comp
      (Computable.list_length.comp (decodeSecond_computable.comp Computable.fst)) hkF)).pair hkF
  have hidx : Computable heavyIdx :=
    bitsToNat_primrec.to_comp.comp (decodeSecond_computable.comp Computable.fst)
  have hS : Computable₂ (fun (py : BitString × BitString) (s : ℕ) =>
      heavyStage c (heavyKey py, s)) :=
    (heavyStage_computable c).comp ((hkey.comp Computable.fst).pair Computable.snd)
  have hL : Computable₂ (fun (py : BitString × BitString) (s : ℕ) =>
      (heavyStage c (heavyKey py, s)).length) :=
    Computable.list_length.comp hS
  have hI : Computable₂ (fun (py : BitString × BitString) (_ : ℕ) => heavyIdx py) :=
    hidx.comp Computable.fst
  have hlt : Computable₂ (fun a b : ℕ => decide (a < b)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp
  have hcheck : Computable₂ (fun (py : BitString × BitString) (s : ℕ) =>
      decide (heavyIdx py < (heavyStage c (heavyKey py, s)).length)) :=
    hlt.comp hI hL
  have hget : Computable₂ (fun (py : BitString × BitString) (s : ℕ) =>
      (heavyStage c (heavyKey py, s))[heavyIdx py]?) :=
    Computable.list_getElem?.comp hS hI
  exact Partrec.bind (Partrec.rfind hcheck.partrec₂) (Computable.ofOption hget).to₂

/-- Trailing zero bits do not change a little-endian numeral. -/
private theorem bitsToNat_replicate_false_aux (m : ℕ) :
    bitsToNat (List.replicate m false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [bitsToNat, List.replicate_succ, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- Trailing zero bits do not change a little-endian numeral. -/
private theorem bitsToNat_append_replicate_false_aux (l : BitString) (m : ℕ) :
    bitsToNat (l ++ List.replicate m false) = bitsToNat l := by
  induction l with
  | nil =>
    simp only [List.nil_append, bitsToNat]
    exact bitsToNat_replicate_false_aux m
  | cons b l ih =>
    simp only [bitsToNat, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih]

/-- If `A` has `2^k` programs of length `n` relative to `B`, dovetailing all such
computations and indexing the outputs saves `k` bits.  The self-delimiting copy of `k`
accounts for the logarithmic overhead; `n` is recovered from the total program length. -/
private theorem condK_le_of_many_conditionalPrograms (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (A B : BitString) (n k : ℕ),
      k ≤ n →
      ({P : BitString | produces D P B A ∧ P.length = n} : Set BitString).Finite →
      2 ^ k ≤
        ({P : BitString | produces D P B A ∧ P.length = n} : Set BitString).ncard →
      condK D A B ≤
        ((n - k + 2 * (Nat.bits k).length + c : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hD.1
  obtain ⟨cE, hcE⟩ := hD.2 (heavyDecoder c) (heavyDecoder_isDecompressor c)
  refine ⟨cE + 1, fun A B n k hkn hfin hcard => ?_⟩
  obtain ⟨s0, hs0⟩ := exists_mem_heavyStage D c hc A B n k hfin hcard
  let q : HeavyParam := ((B, n), k)
  let L0 := heavyStage c (q, s0)
  let i := L0.idxOf A
  have hi0 : i < L0.length := List.idxOf_lt_length_iff.2 hs0
  have hiB : i < 2 ^ (n - k) := lt_of_lt_of_le hi0 (heavyStage_length_le c B n k s0 hkn)
  have hbits : (Nat.bits i).length ≤ n - k := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.2 hiB
  let w : BitString := Nat.bits i ++ List.replicate (n - k - (Nat.bits i).length) false
  have hwlen : w.length = n - k := by
    simp only [w, List.length_append, List.length_replicate]
    omega
  have hwnat : bitsToNat w = i := by
    simp only [w]
    rw [bitsToNat_append_replicate_false_aux, bitsToNat_bits]
  have hprod : produces (heavyDecoder c) (pairCode (Nat.bits k) w) B A := by
    have hk : heavyKey (pairCode (Nat.bits k) w, B) = q := by
      simp only [heavyKey, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits, hwlen,
        Nat.sub_add_cancel hkn, q]
    have hidx : heavyIdx (pairCode (Nat.bits k) w, B) = i := by
      simp only [heavyIdx, decodeSecond_pairCode, hwnat]
    change A ∈ (Nat.rfind _).bind _
    rw [hk, hidx]
    have hdom : (Nat.rfind (fun s =>
        Part.some (decide (i < (heavyStage c (q, s)).length)))).Dom :=
      Nat.rfind_dom.2 ⟨s0, by simpa using hi0, fun _ => trivial⟩
    have hmem := Part.get_mem hdom
    have hspec := Nat.rfind_spec hmem
    simp only [Part.mem_some_iff] at hspec
    have hlt : i < (heavyStage c (q, (Nat.rfind _).get hdom)).length :=
      of_decide_eq_true hspec.symm
    rw [Part.mem_bind_iff]
    refine ⟨_, hmem, ?_⟩
    have hent : (heavyStage c (q, (Nat.rfind _).get hdom))[i]? = some A := by
      obtain ⟨r0, hr0⟩ := heavyStage_prefix c q (le_max_right ((Nat.rfind _).get hdom) s0)
      obtain ⟨r1, hr1⟩ := heavyStage_prefix c q (le_max_left ((Nat.rfind _).get hdom) s0)
      have hAt0 : L0[i]? = some A := List.getElem?_idxOf hs0
      have hAtMax : (heavyStage c (q, max ((Nat.rfind _).get hdom) s0))[i]? = some A := by
        rw [← hr0, List.getElem?_append_left hi0]
        exact hAt0
      rw [← hr1, List.getElem?_append_left hlt] at hAtMax
      exact hAtMax
    rw [hent]
    exact Part.mem_some _
  calc
    condK D A B ≤ condK (heavyDecoder c) A B + (cE : ℕ∞) := hcE A B
    _ ≤ ((pairCode (Nat.bits k) w).length : ℕ∞) + (cE : ℕ∞) := by
      gcongr
      exact sInf_le ⟨pairCode (Nat.bits k) w, hprod, rfl⟩
    _ ≤ ((n - k + 2 * (Nat.bits k).length + (cE + 1) : ℕ) : ℕ∞) := by
      rw [length_pairCode]
      exact_mod_cast (show (Nat.bits k).length + 1 + (Nat.bits k).length + w.length + cE ≤
        n - k + 2 * (Nat.bits k).length + (cE + 1) by omega)

/-- A fibre containing `2^k` distinct programs of length `n` must have `k ≤ n`, since
there are exactly `2^n` bit strings of length `n`. -/
private theorem savedBits_le_length_of_many_conditionalPrograms (D : Map)
    (A B : BitString) (n k : ℕ)
    (hcard : 2 ^ k ≤
      ({P : BitString | produces D P B A ∧ P.length = n} : Set BitString).ncard) :
    k ≤ n := by
  let S : Set BitString :=
    {P : BitString | produces D P B A ∧ P.length = n}
  let T : Set BitString := (allStrings n).toFinset
  have hsub : S ⊆ T := by
    intro P hP
    change P ∈ (allStrings n).toFinset
    rw [List.mem_toFinset, mem_allStrings]
    exact hP.2
  have hfinite : T.Finite := Finset.finite_toSet _
  have hle : S.ncard ≤ T.ncard := Set.ncard_le_ncard hsub hfinite
  have hTcard : T.ncard = 2 ^ n := by
    rw [show T = ((allStrings n).toFinset : Set BitString) by rfl,
      Set.ncard_coe_finset, List.toFinset_card_of_nodup (allStrings_nodup n),
      length_allStrings]
  have hpow : 2 ^ k ≤ 2 ^ n := by
    exact hcard.trans (hle.trans_eq hTcard)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow

/-- An exponential eventually exceeds the linear overhead used to encode the saving. -/
private theorem conditionalPrograms_linear_lt_exp (c : ℕ) :
    3 * c + 12 < 2 ^ (c + 5) := by
  induction c with
  | zero => decide
  | succ c ih =>
    have hpow : 2 ^ (c + 1 + 5) = 2 ^ (c + 5) * 2 := by
      rw [show c + 1 + 5 = (c + 5) + 1 by omega, Nat.pow_succ]
    rw [hpow]
    omega

/-- At the chosen saving `2^(c+5)`, the saving is larger than the binary-index overhead. -/
private theorem conditionalPrograms_overhead_lt (c : ℕ) :
    2 * (Nat.bits (2 ^ (c + 5))).length + c < 2 ^ (c + 5) := by
  rw [Nat.size_eq_bits_len (2 ^ (c + 5)), Nat.size_pow]
  have h := conditionalPrograms_linear_lt_exp c
  omega

/-- Conditional Exercise 40: uniformly only constantly many programs of a shortest fixed
length produce the prescribed output from the prescribed condition. -/
private theorem card_conditionalProgramsOfShortestLength_le (D : Map)
    (hD : isOptimalConditional D) :
    ∃ C : ℕ, ∀ (A B : BitString) (n : ℕ),
      (n : ℕ∞) = condK D A B →
      ({P : BitString | produces D P B A ∧ P.length = n} : Set BitString).ncard ≤ C := by
  obtain ⟨c, hc⟩ := condK_le_of_many_conditionalPrograms D hD
  let k := 2 ^ (c + 5)
  refine ⟨2 ^ k, fun A B n hn => ?_⟩
  have hfinite := conditionalProgramsOfLength_finite D A B n
  by_contra hcard
  push Not at hcard
  have hmany : 2 ^ k ≤
      ({P : BitString | produces D P B A ∧ P.length = n} : Set BitString).ncard :=
    le_of_lt hcard
  have hkn := savedBits_le_length_of_many_conditionalPrograms D A B n k hmany
  have hcompress := hc A B n k hkn hfinite hmany
  have hnat : n ≤ n - k + 2 * (Nat.bits k).length + c := by
    have hcast : (n : ℕ∞) ≤
        ((n - k + 2 * (Nat.bits k).length + c : ℕ) : ℕ∞) := by
      rw [hn]
      exact hcompress
    exact_mod_cast hcast
  have hoverhead : 2 * (Nat.bits k).length + c < k := by
    dsimp only [k]
    exact conditionalPrograms_overhead_lt c
  omega

/-- Dovetailing a conditional decompressor over the programs of one fixed length gives
a computable history without repetitions.  The histories grow by prefixes, and their
union is exactly the corresponding program fibre. -/
private theorem exists_conditionalProgramDovetailing (D : Map)
    (hD : isDecompressor D) :
    ∃ stage : ConditionalProgramStageArg → List BitString,
      Computable stage ∧
      (∀ (n : ℕ) (A B : BitString) (s : ℕ),
        (stage (((n, A), B), s)).Nodup) ∧
      (∀ (n : ℕ) (A B : BitString) {s t : ℕ}, s ≤ t →
        stage (((n, A), B), s) <+: stage (((n, A), B), t)) ∧
      (∀ (n : ℕ) (A B P : BitString),
        (∃ s, P ∈ stage (((n, A), B), s)) ↔
          produces D P B A ∧ P.length = n) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hD
  refine ⟨condStage c, condStage_computable c,
    fun n A B s => condStage_nodup c ((n, A), B) s, ?_, ?_⟩
  · intro n A B s t hst
    induction t, hst using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ t _ ih =>
      rw [condStage_succ]
      exact ih.trans (List.prefix_append _ _)
  · intro n A B P
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨hP, t, _, hnew⟩ := (mem_condStage c ((n, A), B) s P).1 hs
      have hok : condOk c ((n, A), B) t P = true := by
        simp only [condNewAt, Bool.and_eq_true] at hnew
        exact hnew.1
      exact ⟨(exists_condOk_iff D c hc n A B P).1 ⟨t, hok⟩,
        exactLengthPrograms_length_eq n P hP⟩
    · rintro ⟨hP, hlen⟩
      have hex := (exists_condOk_iff D c hc n A B P).2 hP
      classical
      let t := Nat.find hex
      have htok : condOk c ((n, A), B) t P = true := Nat.find_spec hex
      refine ⟨t, (mem_condStage c ((n, A), B) t P).2
        ⟨hlen ▸ mem_exactLengthPrograms_self P, t, le_rfl, ?_⟩⟩
      unfold condNewAt
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      refine ⟨htok, ?_⟩
      by_cases h0 : t = 0
      · exact Or.inl h0
      · right
        have hlt : t - 1 < t := by omega
        have hmin := Nat.find_min hex hlt
        simpa using hmin

/-- In a duplicate-free prefix enumeration of a finite set, every enumerated member has
a stable rank below the cardinality of the set.  Once a stage contains that rank, its
entry there is the prescribed member. -/
private theorem exists_stableRank_of_prefixEnumeration
    (D : Map)
    (stage : ConditionalProgramStageArg → List BitString)
    (hNodup : ∀ (n : ℕ) (A B : BitString) (s : ℕ),
      (stage (((n, A), B), s)).Nodup)
    (hPrefix : ∀ (n : ℕ) (A B : BitString) {s t : ℕ}, s ≤ t →
      stage (((n, A), B), s) <+: stage (((n, A), B), t))
    (hMem : ∀ (n : ℕ) (A B P : BitString),
      (∃ s, P ∈ stage (((n, A), B), s)) ↔
        produces D P B A ∧ P.length = n)
    (A B P : BitString) (n : ℕ)
    (hP : produces D P B A) (hlen : P.length = n)
    (hfinite :
      ({Q : BitString | produces D Q B A ∧ Q.length = n} : Set BitString).Finite) :
    ∃ i : ℕ,
      i < ({Q : BitString | produces D Q B A ∧ Q.length = n} : Set BitString).ncard ∧
      (∃ s, i < (stage (((n, A), B), s)).length) ∧
      ∀ s, i < (stage (((n, A), B), s)).length →
        (stage (((n, A), B), s))[i]? = some P := by
  obtain ⟨s0, hs0⟩ := (hMem n A B P).2 ⟨hP, hlen⟩
  let L0 := stage (((n, A), B), s0)
  let i := L0.idxOf P
  have hi0 : i < L0.length := List.idxOf_lt_length_iff.2 hs0
  have hiCard : i <
      ({Q : BitString | produces D Q B A ∧ Q.length = n} : Set BitString).ncard := by
    have hsub : (L0.toFinset : Set BitString) ⊆
        {Q : BitString | produces D Q B A ∧ Q.length = n} := by
      intro Q hQ
      rw [Finset.mem_coe, List.mem_toFinset] at hQ
      exact (hMem n A B Q).1 ⟨s0, hQ⟩
    have hcard := Set.ncard_le_ncard hsub hfinite
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup (hNodup n A B s0)] at hcard
    exact hi0.trans_le hcard
  refine ⟨i, hiCard, ⟨s0, hi0⟩, fun s his => ?_⟩
  obtain ⟨r0, hr0⟩ := hPrefix n A B (le_max_right s s0)
  obtain ⟨rs, hrs⟩ := hPrefix n A B (le_max_left s s0)
  have hAt0 : L0[i]? = some P := List.getElem?_idxOf hs0
  have hAtMax : (stage (((n, A), B), max s s0))[i]? = some P := by
    rw [← hr0, List.getElem?_append_left hi0]
    exact hAt0
  rw [← hrs, List.getElem?_append_left his] at hAtMax
  exact hAtMax

/-- The stage key `((n, A), B)` read off a rank code `pairCode (bits n) (natCode i)` and
a condition `pairCode A B`. -/
private def rankKey (py : BitString × BitString) : (ℕ × BitString) × BitString :=
  ((bitsToNat (decodeFirst py.1), decodeFirst py.2), decodeSecond py.2)

/-- The rank `i` read off a rank code `pairCode (bits n) (natCode i)`. -/
private def rankIdx (py : BitString × BitString) : ℕ := (decodeSecond py.1).length - 1

/-- The rank decoder of a staged history: wait for the rank to appear, return its entry. -/
private def rankDecoder (stage : ConditionalProgramStageArg → List BitString) : Map :=
  fun py => (Nat.rfind (fun s =>
      Part.some (decide (rankIdx py < (stage (rankKey py, s)).length)))).bind
    (fun s => Part.ofOption ((stage (rankKey py, s))[rankIdx py]?))

/-- The stage key is computable. -/
private theorem rankKey_computable : Computable rankKey :=
  ((bitsToNat_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst)).pair
    (decodeFirst_computable.comp Computable.snd)).pair
    (decodeSecond_computable.comp Computable.snd)

/-- The rank is computable. -/
private theorem rankIdx_computable : Computable rankIdx :=
  Primrec.nat_sub.to_comp.comp
    (Computable.list_length.comp (decodeSecond_computable.comp Computable.fst))
    (Computable.const 1)

/-- The rank decoder of a computable history is partial recursive. -/
private theorem rankDecoder_isDecompressor
    (stage : ConditionalProgramStageArg → List BitString) (hstage : Computable stage) :
    isDecompressor (rankDecoder stage) := by
  have hS : Computable₂ (fun (py : BitString × BitString) (s : ℕ) =>
      stage (rankKey py, s)) :=
    hstage.comp ((rankKey_computable.comp Computable.fst).pair Computable.snd)
  have hL : Computable₂ (fun (py : BitString × BitString) (s : ℕ) =>
      (stage (rankKey py, s)).length) :=
    Computable.list_length.comp hS
  have hI : Computable₂ (fun (py : BitString × BitString) (_ : ℕ) => rankIdx py) :=
    rankIdx_computable.comp Computable.fst
  have hlt : Computable₂ (fun a b : ℕ => decide (a < b)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp
  have hcheck : Computable₂ (fun (py : BitString × BitString) (s : ℕ) =>
      decide (rankIdx py < (stage (rankKey py, s)).length)) :=
    hlt.comp hI hL
  have hget : Computable₂ (fun (py : BitString × BitString) (s : ℕ) =>
      (stage (rankKey py, s))[rankIdx py]?) :=
    Computable.list_getElem?.comp hS hI
  exact Partrec.bind (Partrec.rfind hcheck.partrec₂) (Computable.ofOption hget).to₂

/-- A computable prefix history has a partial-recursive rank decoder: it parses the
length and rank, waits until that entry appears, and returns the stable entry. -/
private theorem exists_rankDecoder_of_computableStages
    (stage : ConditionalProgramStageArg → List BitString)
    (hstage : Computable stage) :
    ∃ E : Map, isDecompressor E ∧
      ∀ (A B P : BitString) (n i : ℕ),
        (∃ s, i < (stage (((n, A), B), s)).length) →
        (∀ s, i < (stage (((n, A), B), s)).length →
          (stage (((n, A), B), s))[i]? = some P) →
        produces E (pairCode (Nat.bits n) (natCode i)) (pairCode A B) P := by
  refine ⟨rankDecoder stage, rankDecoder_isDecompressor stage hstage,
    fun A B P n i hex hstable => ?_⟩
  have hk : rankKey (pairCode (Nat.bits n) (natCode i), pairCode A B) = ((n, A), B) := by
    simp [rankKey, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  have hi : rankIdx (pairCode (Nat.bits n) (natCode i), pairCode A B) = i := by
    simp [rankIdx, decodeSecond_pairCode, natCode]
  change P ∈ (Nat.rfind _).bind _
  rw [hk, hi]
  obtain ⟨s0, hs0⟩ := hex
  have hdom : (Nat.rfind (fun s =>
      Part.some (decide (i < (stage (((n, A), B), s)).length)))).Dom :=
    Nat.rfind_dom.2 ⟨s0, by simpa using hs0, fun _ => trivial⟩
  have hmem := Part.get_mem hdom
  have hspec := Nat.rfind_spec hmem
  simp only [Part.mem_some_iff] at hspec
  have hlt : i < (stage (((n, A), B), (Nat.rfind _).get hdom)).length :=
    of_decide_eq_true hspec.symm
  rw [Part.mem_bind_iff]
  refine ⟨_, hmem, ?_⟩
  rw [hstable _ hlt]
  exact Part.mem_some _

/-- Dovetailing the computations of `D` at one program length gives a partial-recursive
decoder for the rank of every member of the resulting finite fibre. -/
private theorem exists_conditionalProgramRankDecoder (D : Map) (hD : isDecompressor D) :
    ∃ E : Map, isDecompressor E ∧
      ∀ (A B P : BitString) (n : ℕ),
        produces D P B A → P.length = n →
        ({Q : BitString | produces D Q B A ∧ Q.length = n} : Set BitString).Finite →
        ∃ i : ℕ,
          i < ({Q : BitString | produces D Q B A ∧ Q.length = n} : Set BitString).ncard ∧
          produces E (pairCode (Nat.bits n) (natCode i)) (pairCode A B) P := by
  obtain ⟨stage, hstage, hNodup, hPrefix, hMem⟩ :=
    exists_conditionalProgramDovetailing D hD
  obtain ⟨E, hE, hDecode⟩ :=
    exists_rankDecoder_of_computableStages stage hstage
  refine ⟨E, hE, fun A B P n hP hlen hfinite => ?_⟩
  obtain ⟨i, hi, hexists, hstable⟩ :=
    exists_stableRank_of_prefixEnumeration D stage hNodup hPrefix hMem
      A B P n hP hlen hfinite
  exact ⟨i, hi, hDecode A B P n i hexists hstable⟩

/-- The self-delimiting pair of a binary length and a bounded unary rank costs twice the
binary length plus the rank bound and a constant. -/
private theorem length_conditionalProgramRankCode_le (n i C : ℕ) (hi : i < C) :
    (pairCode (Nat.bits n) (natCode i)).length ≤ 2 * (Nat.bits n).length + C + 1 := by
  rw [length_pairCode, length_natCode]
  omega

/-- A member of a uniformly bounded fixed-length program fibre is reconstructed from its
index in the dovetailed enumeration, while its length is supplied in binary. -/
private theorem condK_program_le_bits_length_of_card (D : Map)
    (hD : isOptimalConditional D) (C : ℕ) :
    ∃ c : ℕ, ∀ (A B P : BitString) (n : ℕ),
      produces D P B A → P.length = n →
      ({Q : BitString | produces D Q B A ∧ Q.length = n} : Set BitString).Finite →
      ({Q : BitString | produces D Q B A ∧ Q.length = n} : Set BitString).ncard ≤ C →
      condK D P (pairCode A B) ≤
        ((2 * (Nat.bits n).length + c : ℕ) : ℕ∞) := by
  obtain ⟨E, hE, hRank⟩ := exists_conditionalProgramRankDecoder D hD.1
  obtain ⟨cE, hcE⟩ := hD.2 E hE
  refine ⟨C + 1 + cE, fun A B P n hP hlen hfin hcard => ?_⟩
  obtain ⟨i, hi, hEi⟩ := hRank A B P n hP hlen hfin
  have hiC : i < C := lt_of_lt_of_le hi hcard
  have hcode := length_conditionalProgramRankCode_le n i C hiC
  calc
    condK D P (pairCode A B) ≤ condK E P (pairCode A B) + (cE : ℕ∞) :=
      hcE P (pairCode A B)
    _ ≤ ((pairCode (Nat.bits n) (natCode i)).length : ℕ∞) + (cE : ℕ∞) := by
      gcongr
      exact sInf_le ⟨pairCode (Nat.bits n) (natCode i), hEi, rfl⟩
    _ ≤ ((2 * (Nat.bits n).length + (C + 1 + cE) : ℕ) : ℕ∞) := by
      exact_mod_cast (show
        (pairCode (Nat.bits n) (natCode i)).length + cE ≤
          2 * (Nat.bits n).length + (C + 1 + cE) by omega)

/-- Two copies of the binary length and a constant are absorbed by one logarithmic slack. -/
private theorem two_mul_bits_length_add_le_logSlack (c n : ℕ) :
    2 * (Nat.bits n).length + c ≤ logSlack (c + 2) n := by
  unfold logSlack
  nlinarith [Nat.zero_le (c * (Nat.bits n).length)]

/-- A stronger form of Problem 317, with the logarithm of the length of the description
`l(P) = C(A|B)` in place of the logarithm of `C(A,B)`: `C(P | A, B) = O(log C(A|B))`.  Since
`C(A|B) ≤ C(A,B) + O(1)`, it implies `condK_conditionalShortestDescription_le_log`.

SUV Problem 317, p. 369 (strengthened form). -/
theorem condK_conditionalShortestDescription_le_log_length (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ A B P : BitString, produces D P B A → (P.length : ℕ∞) = condK D A B →
      condK D P (pairCode A B) ≤ (logSlack c P.length : ℕ∞) := by
  obtain ⟨C, hC⟩ := card_conditionalProgramsOfShortestLength_le D hD
  obtain ⟨c, hc⟩ := condK_program_le_bits_length_of_card D hD C
  refine ⟨c + 2, fun A B P hP hshort => ?_⟩
  have hfinite := conditionalProgramsOfLength_finite D A B P.length
  have hcard := hC A B P.length hshort
  refine (hc A B P P.length hP rfl hfinite hcard).trans ?_
  exact_mod_cast two_mul_bits_length_add_le_logSlack c P.length

end Kolmogorov
