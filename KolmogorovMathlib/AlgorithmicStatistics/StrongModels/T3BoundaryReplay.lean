import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T3Boundary
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T3
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T3RunComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import Mathlib.Tactic

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

structure T3BoundaryDRunInput where
  n : Nat
  k : Nat
  epsilon : Nat
  delta : Nat
  t : Nat

def T3BoundaryDRunInput.toProd (input : T3BoundaryDRunInput) :
    Nat × Nat × Nat × Nat × Nat :=
  (input.n, input.k, input.epsilon, input.delta, input.t)

def T3BoundaryDRunInput.ofProd
    (p : Nat × Nat × Nat × Nat × Nat) :
    T3BoundaryDRunInput :=
  { n := p.1
  , k := p.2.1
  , epsilon := p.2.2.1
  , delta := p.2.2.2.1
  , t := p.2.2.2.2 }

def t3BoundaryDRunInputEquiv :
    T3BoundaryDRunInput ≃ Nat × Nat × Nat × Nat × Nat where
  toFun := T3BoundaryDRunInput.toProd
  invFun := T3BoundaryDRunInput.ofProd
  left_inv i := by cases i; rfl
  right_inv p := by rcases p with ⟨p1, p2, p3, p4, p5⟩; rfl

private abbrev T3BoundaryDRunInputData :=
  (Nat × Nat) × (Nat × (Nat × Nat))

private def T3BoundaryDRunInput.toData (input : T3BoundaryDRunInput) :
    T3BoundaryDRunInputData :=
  ((input.n, input.k), (input.epsilon, (input.delta, input.t)))

private def T3BoundaryDRunInput.ofData (p : T3BoundaryDRunInputData) :
    T3BoundaryDRunInput :=
  { n := p.1.1
  , k := p.1.2
  , epsilon := p.2.1
  , delta := p.2.2.1
  , t := p.2.2.2 }

private def t3BoundaryDRunInputDataEquiv :
    T3BoundaryDRunInput ≃ T3BoundaryDRunInputData where
  toFun := T3BoundaryDRunInput.toData
  invFun := T3BoundaryDRunInput.ofData
  left_inv i := by cases i; rfl
  right_inv p := by rcases p with ⟨⟨p1, p2⟩, ⟨p3, ⟨p4, p5⟩⟩⟩; rfl

instance : Primcodable T3BoundaryDRunInput :=
  Primcodable.ofEquiv _ t3BoundaryDRunInputDataEquiv

def t3BoundaryDRunStateEquiv : T3BoundaryDRunState ≃ List BitString × List BitString × Nat where
  toFun s := (s.current, s.dSeen, s.rebuilds)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by rcases p with ⟨p1, p2, p3⟩; rfl

instance : Primcodable T3BoundaryDRunState :=
  Primcodable.ofEquiv _ t3BoundaryDRunStateEquiv

def T3BoundaryDRunInput.run (input : T3BoundaryDRunInput) (q : Nat.Partrec.Code) :
    T3BoundaryDRunState :=
  t3BoundaryDRun q input.n input.k input.epsilon input.delta input.t

theorem t3BoundaryDRun_current_eq_of_rebuilds_eq
    (q : Nat.Partrec.Code) (n k epsilon delta : Nat) {s t : Nat}
    (hst : s ≤ t)
    (hversion :
      (t3BoundaryDRun q n k epsilon delta s).rebuilds =
      (t3BoundaryDRun q n k epsilon delta t).rebuilds) :
    (t3BoundaryDRun q n k epsilon delta s).current =
    (t3BoundaryDRun q n k epsilon delta t).current := by
  revert hversion
  induction t, hst using Nat.le_induction with
  | base => intro _; rfl
  | succ u hu ih =>
    intro hversion
    have hversion' : (t3BoundaryDRun q n k epsilon delta s).rebuilds =
        (t3BoundaryDRun q n k epsilon delta u).rebuilds := by
      apply le_antisymm
      · exact t3BoundaryDRun_rebuilds_mono q n k epsilon delta hu
      · rw [hversion]
        exact t3BoundaryDRun_rebuilds_mono q n k epsilon delta (Nat.le_succ _)
    have ih' := ih hversion'
    generalize hg :
      t3BoundaryDQuotaReached q n k epsilon delta (u + 1)
        (t3BoundaryDRun q n k epsilon delta u) = g
    cases g
    · have heq := t3BoundaryDRun_eq_of_not_reached q n k epsilon delta u hg
      rw [ih']
      rw [heq]
    · have hsucc := t3BoundaryDRun_rebuilds_succ_of_reached q n k epsilon delta u hg
      rw [hversion', hsucc] at hversion
      omega

/-! ### Primitive recursiveness of the boundary run

The run is a primitive recursion on the stage index.  To keep each elaboration
under the default heartbeat budget the pieces are proved as small standalone
lemmas: the state-field projections, the `bif`-normal-form rewrites of the step,
and the uniform `Primrec` facts for the initial model, the quota test, and the
rebuild. -/

private theorem t3BoundaryDRunState_current_primrec :
    Primrec (fun s : T3BoundaryDRunState => s.current) :=
  Primrec.fst.comp (Primrec.of_equiv (e := t3BoundaryDRunStateEquiv))

private theorem t3BoundaryDRunState_dSeen_primrec :
    Primrec (fun s : T3BoundaryDRunState => s.dSeen) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := t3BoundaryDRunStateEquiv)))

private theorem t3BoundaryDRunState_rebuilds_primrec :
    Primrec (fun s : T3BoundaryDRunState => s.rebuilds) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := t3BoundaryDRunStateEquiv)))

/-- The quota test in explicit `decide`-of-membership form. -/
private theorem t3BoundaryDQuotaReached_eq (q : Nat.Partrec.Code)
    (n k epsilon delta t : Nat) (s : T3BoundaryDRunState) :
    t3BoundaryDQuotaReached q n k epsilon delta t s =
      decide (2 ^ (k - epsilon - delta) ≤
        (s.current.filter (fun x => decide (x ∈ t1DStage q n k t))).length) := by
  unfold t3BoundaryDQuotaReached
  simp only [List.contains_eq_mem, ge_iff_le]

/-- The rebuild step in explicit form. -/
private theorem t3BoundaryDRebuild_eq (q : Nat.Partrec.Code)
    (n k epsilon t : Nat) (s : T3BoundaryDRunState) :
    t3BoundaryDRebuild q n k epsilon t s =
      ⟨((canonicalFinsetList (stringsOfLength n)).filter
          (fun x => !decide (x ∈ (s.dSeen ++ s.current.filter
            (fun y => decide (y ∈ t1DStage q n k t))).eraseDups))).take
          (2 ^ (k - epsilon)),
       (s.dSeen ++ s.current.filter
          (fun y => decide (y ∈ t1DStage q n k t))).eraseDups,
       s.rebuilds + 1⟩ := by
  unfold t3BoundaryDRebuild
  simp only [List.contains_eq_mem, decide_not, decide_eq_true_eq]

/-- The step in explicit `bif`-normal form. -/
private theorem t3BoundaryDStep_eq (q : Nat.Partrec.Code)
    (n k epsilon delta t : Nat) (s : T3BoundaryDRunState) :
    t3BoundaryDStep q n k epsilon delta t s =
      bif t3BoundaryDQuotaReached q n k epsilon delta t s
      then t3BoundaryDRebuild q n k epsilon t s else s := by
  unfold t3BoundaryDStep
  cases h : t3BoundaryDQuotaReached q n k epsilon delta t s <;> simp

private theorem t3BoundaryDInitial_primrec :
    Primrec (fun p : (Nat × Nat) × Nat =>
      t3BoundaryDInitial p.1.1 p.1.2 p.2) :=
  Primrec.of_equiv_symm.comp
    ((Primrec.list_take.comp
        (twoPow_primrec.comp
          (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
        (canonicalFinsetList_toFinset_primrec.comp
          (allStrings_primrec.comp (Primrec.fst.comp Primrec.fst)))).pair
      ((Primrec.const ([] : List BitString)).pair (Primrec.const 0)))

private theorem t3BoundaryDQuotaReached_primrec (q : Nat.Partrec.Code) :
    Primrec (fun w : (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState =>
      t3BoundaryDQuotaReached q w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2.1 w.1.2.2.2.2 w.2) := by
  have hp : Primrec (fun w : (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState =>
      w.1) := Primrec.fst
  have hn := Primrec.fst.comp hp
  have hk := Primrec.fst.comp (Primrec.snd.comp hp)
  have heps := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hp))
  have hdelta := Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp)))
  have ht := Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp)))
  have hs : Primrec (fun w : (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState =>
      w.2) := Primrec.snd
  have hdStage := (t1DStage_primrec q).comp ((hn.pair hk).pair ht)
  have hmarkedPred : Primrec₂
      (fun (w : (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState) (x : BitString) =>
        decide (x ∈ t1DStage q w.1.1 w.1.2.1 w.1.2.2.2.2)) :=
    bitString_mem_primrec.comp Primrec.snd (hdStage.comp Primrec.fst)
  have hmarked := list_filter_primrec (t3BoundaryDRunState_current_primrec.comp hs) hmarkedPred
  have hquotaVal := twoPow_primrec.comp
    (Primrec.nat_sub.comp (Primrec.nat_sub.comp hk heps) hdelta)
  exact (PrimrecPred.decide (Primrec.nat_le.comp hquotaVal
    (Primrec.list_length.comp hmarked))).of_eq
    (fun w => (t3BoundaryDQuotaReached_eq q w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2.1
      w.1.2.2.2.2 w.2).symm)

private theorem t3BoundaryDRebuild_primrec (q : Nat.Partrec.Code) :
    Primrec (fun w : (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState =>
      t3BoundaryDRebuild q w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2.2 w.2) := by
  have hp : Primrec (fun w : (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState =>
      w.1) := Primrec.fst
  have hn := Primrec.fst.comp hp
  have hk := Primrec.fst.comp (Primrec.snd.comp hp)
  have heps := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hp))
  have ht := Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp)))
  have hs : Primrec (fun w : (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState =>
      w.2) := Primrec.snd
  have hdStage := (t1DStage_primrec q).comp ((hn.pair hk).pair ht)
  have hmarkedPred : Primrec₂
      (fun (w : (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState) (x : BitString) =>
        decide (x ∈ t1DStage q w.1.1 w.1.2.1 w.1.2.2.2.2)) :=
    bitString_mem_primrec.comp Primrec.snd (hdStage.comp Primrec.fst)
  have hmarked := list_filter_primrec (t3BoundaryDRunState_current_primrec.comp hs) hmarkedPred
  have hnewDSeen := eraseDups_bitstring_primrec.comp
    (Primrec.list_append.comp (t3BoundaryDRunState_dSeen_primrec.comp hs) hmarked)
  have hS := canonicalFinsetList_toFinset_primrec.comp (allStrings_primrec.comp hn)
  have havailPred : Primrec₂
      (fun (w : (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState) (x : BitString) =>
        !decide (x ∈ (w.2.dSeen ++ w.2.current.filter
          (fun y => decide (y ∈ t1DStage q w.1.1 w.1.2.1 w.1.2.2.2.2))).eraseDups)) :=
    Primrec.not.comp (bitString_mem_primrec.comp Primrec.snd (hnewDSeen.comp Primrec.fst))
  have havailable := list_filter_primrec hS havailPred
  have htwoKE := twoPow_primrec.comp (Primrec.nat_sub.comp hk heps)
  exact (Primrec.of_equiv_symm.comp
    ((Primrec.list_take.comp htwoKE havailable).pair
      (hnewDSeen.pair (Primrec.succ.comp (t3BoundaryDRunState_rebuilds_primrec.comp hs))))).of_eq
    (fun w => (t3BoundaryDRebuild_eq q w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2.2 w.2).symm)

private theorem t3BoundaryDStep_primrec (q : Nat.Partrec.Code) :
    Primrec (fun w : (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState =>
      t3BoundaryDStep q w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2.1 w.1.2.2.2.2 w.2) :=
  (Primrec.cond (t3BoundaryDQuotaReached_primrec q) (t3BoundaryDRebuild_primrec q)
    Primrec.snd).of_eq
    (fun w => (t3BoundaryDStep_eq q w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2.1
      w.1.2.2.2.2 w.2).symm)

theorem T3BoundaryDRunInput.run_computable
    (q : Nat.Partrec.Code) :
    Computable (fun input : T3BoundaryDRunInput => input.run q) := by
  -- The run is a primitive recursion on the stage index.
  have hrec : ∀ (n k epsilon delta t : Nat),
      t3BoundaryDRun q n k epsilon delta t =
        Nat.rec (t3BoundaryDInitial n k epsilon)
          (fun t' ih => t3BoundaryDStep q n k epsilon delta (t' + 1) ih) t := by
    intro n k epsilon delta t
    induction t with
    | zero => rfl
    | succ t' ih => exact congrArg (t3BoundaryDStep q n k epsilon delta (t' + 1)) ih
  -- Field projections of the input record (through the data equiv).
  have hToData : Primrec (fun input : T3BoundaryDRunInput =>
      ((input.n, input.k), (input.epsilon, (input.delta, input.t)))) :=
    Primrec.of_equiv (e := t3BoundaryDRunInputDataEquiv)
  have hn : Primrec (fun input : T3BoundaryDRunInput => input.n) :=
    Primrec.fst.comp (Primrec.fst.comp hToData)
  have hk : Primrec (fun input : T3BoundaryDRunInput => input.k) :=
    Primrec.snd.comp (Primrec.fst.comp hToData)
  have hepsilon : Primrec (fun input : T3BoundaryDRunInput => input.epsilon) :=
    Primrec.fst.comp (Primrec.snd.comp hToData)
  have hdelta : Primrec (fun input : T3BoundaryDRunInput => input.delta) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hToData))
  have ht : Primrec (fun input : T3BoundaryDRunInput => input.t) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hToData))
  -- Base case `g`.
  have hg : Primrec (fun input : T3BoundaryDRunInput =>
      t3BoundaryDInitial input.n input.k input.epsilon) :=
    t3BoundaryDInitial_primrec.comp ((hn.pair hk).pair hepsilon)
  -- Step case `h`, built over `r : Input × (ℕ × State)`.
  have hstep : Primrec₂
      (fun (input : T3BoundaryDRunInput) (p : ℕ × T3BoundaryDRunState) =>
        t3BoundaryDStep q input.n input.k input.epsilon input.delta (p.1 + 1) p.2) := by
    let f : T3BoundaryDRunInput × ℕ × T3BoundaryDRunState →
        (Nat × Nat × Nat × Nat × Nat) × T3BoundaryDRunState :=
      fun p => ((p.1.n, p.1.k, p.1.epsilon, p.1.delta, p.2.1 + 1), p.2.2)
    have hf : Primrec f :=
      (((hn.comp Primrec.fst).pair
        ((hk.comp Primrec.fst).pair
          ((hepsilon.comp Primrec.fst).pair
            ((hdelta.comp Primrec.fst).pair
              (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))).pair
        (Primrec.snd.comp Primrec.snd))
    have hcomp := (t3BoundaryDStep_primrec q).comp hf
    exact hcomp.of_eq (fun p => rfl)
  -- primitive recursion
  have hprimrec : Primrec (fun input : T3BoundaryDRunInput => input.run q) :=
    (Primrec.nat_rec' ht hg hstep).of_eq
      (fun input => (hrec input.n input.k input.epsilon input.delta input.t).symm)
  exact hprimrec.to_comp

noncomputable def t3BoundaryVersionDecoder (q : Nat.Partrec.Code) (input : BitString) :
    Part BitString :=
  Nat.rfind (fun m => Part.some (decide (bitsToNat (decodeSecond input) ≤
    (t3BoundaryDRun q
      (bitsToNat ((decodeListCode (decodeFirst input)).getD 0 []))
      (bitsToNat ((decodeListCode (decodeFirst input)).getD 1 []))
      (bitsToNat ((decodeListCode (decodeFirst input)).getD 2 []))
      (bitsToNat ((decodeListCode (decodeFirst input)).getD 3 []))
      m).rebuilds))) >>= fun m =>
    Part.some (canonicalImageCodeOfList
      (t3BoundaryDRun q
        (bitsToNat ((decodeListCode (decodeFirst input)).getD 0 []))
        (bitsToNat ((decodeListCode (decodeFirst input)).getD 1 []))
        (bitsToNat ((decodeListCode (decodeFirst input)).getD 2 []))
        (bitsToNat ((decodeListCode (decodeFirst input)).getD 3 []))
        m).current)

theorem t3BoundaryVersionDecoder_partrec
    (q : Nat.Partrec.Code) :
    Partrec (t3BoundaryVersionDecoder q) := by
  -- The replayed run, as a computable function of the parsed header and stage.
  have hrun : Computable (fun input : T3BoundaryDRunInput => input.run q) :=
    T3BoundaryDRunInput.run_computable q
  have hheader : Computable (fun input : BitString =>
      decodeListCode (decodeFirst input)) :=
    decodeListCode_computable.comp decodeFirst_computable
  have hgetD : Computable₂ (fun (l : List BitString) (i : Nat) => l.getD i []) :=
    (Primrec.list_getD []).to_comp
  have hH0 : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 0 [])) :=
    bitsToNat_primrec.to_comp.comp (hgetD.comp hheader (Computable.const 0))
  have hH1 : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 1 [])) :=
    bitsToNat_primrec.to_comp.comp (hgetD.comp hheader (Computable.const 1))
  have hH2 : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 2 [])) :=
    bitsToNat_primrec.to_comp.comp (hgetD.comp hheader (Computable.const 2))
  have hH3 : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 3 [])) :=
    bitsToNat_primrec.to_comp.comp (hgetD.comp hheader (Computable.const 3))
  have hversionBit : Computable (fun input : BitString =>
      bitsToNat (decodeSecond input)) :=
    bitsToNat_primrec.to_comp.comp decodeSecond_computable
  -- Build the run input record from the parsed header and the stage index.
  have hbuildData : Computable (fun p : BitString × Nat =>
      ((bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []),
        bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 [])),
       (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []),
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 []), p.2)))) :=
    ((hH0.comp Computable.fst).pair (hH1.comp Computable.fst)).pair
      ((hH2.comp Computable.fst).pair
        ((hH3.comp Computable.fst).pair Computable.snd))
  have hinput : Computable (fun p : BitString × Nat =>
      (t3BoundaryDRunInputDataEquiv.symm
        ((bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []),
          bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 [])),
         (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []),
          (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 []), p.2))))) :=
    (Primrec.of_equiv_symm (e := t3BoundaryDRunInputDataEquiv)).to_comp.comp hbuildData
  have hruns : Computable (fun p : BitString × Nat =>
      t3BoundaryDRun q
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 []))
        p.2) :=
    (hrun.comp hinput).of_eq (fun p => rfl)
  have hrebuildsRun : Computable (fun p : BitString × Nat =>
      (t3BoundaryDRun q
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 []))
        p.2).rebuilds) :=
    t3BoundaryDRunState_rebuilds_primrec.to_comp.comp hruns
  have hcurrentRun : Computable (fun p : BitString × Nat =>
      (t3BoundaryDRun q
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 []))
        p.2).current) :=
    t3BoundaryDRunState_current_primrec.to_comp.comp hruns
  have hversionR : Computable (fun p : BitString × Nat =>
      bitsToNat (decodeSecond p.1)) := hversionBit.comp Computable.fst
  have hle : Computable₂ (fun a b : Nat => decide (a ≤ b)) :=
    (PrimrecPred.decide Primrec.nat_le).to_comp
  have hcheck : Computable₂ (fun (input : BitString) (m : Nat) =>
      decide (bitsToNat (decodeSecond input) ≤
        (t3BoundaryDRun q
          (bitsToNat ((decodeListCode (decodeFirst input)).getD 0 []))
          (bitsToNat ((decodeListCode (decodeFirst input)).getD 1 []))
          (bitsToNat ((decodeListCode (decodeFirst input)).getD 2 []))
          (bitsToNat ((decodeListCode (decodeFirst input)).getD 3 []))
          m).rebuilds)) :=
    hle.comp hversionR hrebuildsRun
  have hfind : Partrec (fun input : BitString =>
      Nat.rfind fun m =>
        Part.some (decide (bitsToNat (decodeSecond input) ≤
          (t3BoundaryDRun q
            (bitsToNat ((decodeListCode (decodeFirst input)).getD 0 []))
            (bitsToNat ((decodeListCode (decodeFirst input)).getD 1 []))
            (bitsToNat ((decodeListCode (decodeFirst input)).getD 2 []))
            (bitsToNat ((decodeListCode (decodeFirst input)).getD 3 []))
            m).rebuilds))) :=
    Partrec.rfind hcheck.partrec₂
  have hpost : Computable₂ (fun (input : BitString) (m : Nat) =>
      canonicalImageCodeOfList
        (t3BoundaryDRun q
          (bitsToNat ((decodeListCode (decodeFirst input)).getD 0 []))
          (bitsToNat ((decodeListCode (decodeFirst input)).getD 1 []))
          (bitsToNat ((decodeListCode (decodeFirst input)).getD 2 []))
          (bitsToNat ((decodeListCode (decodeFirst input)).getD 3 []))
          m).current) :=
    (canonicalImageCodeOfList_computable.comp hcurrentRun).to₂
  exact (Partrec.bind hfind hpost.partrec₂).of_eq (fun _ => rfl)

theorem t3BoundaryVersionDecoder_eval
    (q : Nat.Partrec.Code) (n k epsilon delta t : Nat)
    (hwidth :
      (t3BoundaryDRun q n k epsilon delta t).rebuilds <
        2 ^ (epsilon + delta)) :
    canonicalImageCodeOfList
        (t3BoundaryDRun q n k epsilon delta t).current ∈
      t3BoundaryVersionDecoder q
        (t3VersionProgram 0 n k epsilon delta
          (t3BoundaryDRun q n k epsilon delta t).rebuilds) := by
  set version := (t3BoundaryDRun q n k epsilon delta t).rebuilds with hver_def
  -- Roundtrip width: `logSlack 0 n = 0`, so the boundary version fits the header.
  have hv : version < 2 ^ (epsilon + delta + logSlack 0 n) := by
    simpa [logSlack] using hwidth
  obtain ⟨hheader, hversionParse⟩ :=
    t3VersionProgram_roundtrip 0 n k epsilon delta version hv
  have hnparse : bitsToNat ((decodeListCode (decodeFirst
      (t3VersionProgram 0 n k epsilon delta version))).getD 0 []) = n := by
    rw [hheader]; simp [bitsToNat_bits]
  have hkparse : bitsToNat ((decodeListCode (decodeFirst
      (t3VersionProgram 0 n k epsilon delta version))).getD 1 []) = k := by
    rw [hheader]; simp [bitsToNat_bits]
  have heparse : bitsToNat ((decodeListCode (decodeFirst
      (t3VersionProgram 0 n k epsilon delta version))).getD 2 []) = epsilon := by
    rw [hheader]; simp [bitsToNat_bits]
  have hdparse : bitsToNat ((decodeListCode (decodeFirst
      (t3VersionProgram 0 n k epsilon delta version))).getD 3 []) = delta := by
    rw [hheader]; simp [bitsToNat_bits]
  -- A rebuild step increases the version counter by at most one.
  have hstep : ∀ m', (t3BoundaryDRun q n k epsilon delta (m' + 1)).rebuilds ≤
      (t3BoundaryDRun q n k epsilon delta m').rebuilds + 1 := by
    intro m'
    by_cases hreach : t3BoundaryDQuotaReached q n k epsilon delta (m' + 1)
        (t3BoundaryDRun q n k epsilon delta m') = true
    · rw [t3BoundaryDRun_rebuilds_succ_of_reached q n k epsilon delta m' hreach]
    · rw [t3BoundaryDRun_eq_of_not_reached q n k epsilon delta m' (by simpa using hreach)]
      omega
  -- The least stage whose version counter reaches `version`.
  have hex : ∃ m, version ≤ (t3BoundaryDRun q n k epsilon delta m).rebuilds :=
    ⟨t, le_refl version⟩
  set m0 := Nat.find hex with hm0
  have hm0_spec : version ≤ (t3BoundaryDRun q n k epsilon delta m0).rebuilds :=
    Nat.find_spec hex
  have hm0_le : m0 ≤ t := Nat.find_min' hex (le_refl version)
  -- At the least such stage the version counter equals `version` exactly.
  have hrev : (t3BoundaryDRun q n k epsilon delta m0).rebuilds ≤ version := by
    rcases Nat.eq_zero_or_pos m0 with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have hm'lt : m' < m0 := by rw [hm']; exact Nat.lt_succ_self m'
      have hmin : ¬ (version ≤ (t3BoundaryDRun q n k epsilon delta m').rebuilds) :=
        Nat.find_min hex hm'lt
      have hlt : (t3BoundaryDRun q n k epsilon delta m').rebuilds < version :=
        Nat.lt_of_not_le hmin
      have h1 := hstep m'
      rw [hm']
      change (t3BoundaryDRun q n k epsilon delta (m' + 1)).rebuilds ≤ version
      omega
  have hm0_eq : (t3BoundaryDRun q n k epsilon delta m0).rebuilds = version :=
    le_antisymm hrev hm0_spec
  -- Equal version counters give equal current models (`m0 ≤ t`).
  have hcurrent : (t3BoundaryDRun q n k epsilon delta m0).current =
      (t3BoundaryDRun q n k epsilon delta t).current :=
    t3BoundaryDRun_current_eq_of_rebuilds_eq q n k epsilon delta hm0_le hm0_eq
  -- The rfind lands exactly on `m0`.
  have hfind : Nat.rfind (fun m => Part.some (decide
      (version ≤ (t3BoundaryDRun q n k epsilon delta m).rebuilds))) = Part.some m0 := by
    rw [Part.eq_some_iff]
    exact Nat.mem_rfind.mpr ⟨by simpa using hm0_spec,
      fun {m} hm => by simpa using Nat.find_min hex hm⟩
  unfold t3BoundaryVersionDecoder
  simp only [hnparse, hkparse, heparse, hdparse, hversionParse]
  change canonicalImageCodeOfList (t3BoundaryDRun q n k epsilon delta t).current ∈
    (Nat.rfind (fun m => Part.some (decide
      (version ≤ (t3BoundaryDRun q n k epsilon delta m).rebuilds)))).bind
      (fun m => Part.some (canonicalImageCodeOfList
        (t3BoundaryDRun q n k epsilon delta m).current))
  rw [Part.mem_bind_iff]
  refine ⟨m0, ?_, ?_⟩
  · rw [hfind]; exact Part.mem_some m0
  · rw [Part.mem_some_iff]
    exact congrArg canonicalImageCodeOfList hcurrent.symm

/-- Decoder evaluation bounds the ordinary plain complexity of the decoded
canonical finite-set code (boundary replay form). -/
theorem plainSetComplexity_of_t3BoundaryVersionDecoder_eval
    (V : Map) (hV : isOptimalConditional V) (q : Nat.Partrec.Code) :
    ∃ cDecoder : Nat, ∀ p L (hL : L.toFinset.Nonempty),
      canonicalImageCodeOfList L ∈ t3BoundaryVersionDecoder q p →
      plainSetComplexity V L.toFinset hL ≤
        (p.length + cDecoder : ENat) := by
  obtain ⟨cMap, hMap⟩ :=
    plainK_partrec_map_le V hV (t3BoundaryVersionDecoder q)
      (t3BoundaryVersionDecoder_partrec q)
  obtain ⟨cLiteral, hLiteral⟩ := plainKLeLength V hV
  refine ⟨cLiteral + cMap, ?_⟩
  intro p L hL hEval
  unfold plainSetComplexity
  rw [← canonicalImageCodeOfList_eq_codedUniformOn L hL]
  calc
    plainK V (canonicalImageCodeOfList L)
        ≤ plainK V p + (cMap : ENat) :=
      hMap p (canonicalImageCodeOfList L) hEval
    _ ≤ ((p.length : ENat) + (cLiteral : ENat)) + (cMap : ENat) := by
      gcongr
      exact hLiteral p
    _ = (p.length + (cLiteral + cMap) : Nat) := by
      push_cast
      ac_rfl

/-- The current model of the boundary D-only run at any stage has ordinary plain
set complexity at most `epsilon + delta + O(log n)`.  The model is addressed by
its version (= rebuild count), encoded by the four-field header
`t3VersionProgram 0`, and reconstructed by the reachable-version boundary
decoder.  This is the boundary analogue of
`plainSetComplexity_t3RunVersion_le_of_k_le_n` for the interior run. -/
theorem plainSetComplexity_t3BoundaryDRun_current_le
    (V : Map) (hV : isOptimalConditional V)
    (q : Nat.Partrec.Code) (hq : IsCodeFor q V) :
  ∃ cA : Nat, ∀ n k epsilon delta t
      (hA :
        (t3BoundaryDRun q n k epsilon delta t).current.toFinset.Nonempty),
    epsilon ≤ k →
    delta ≤ k - epsilon →
    k ≤ n →
    plainSetComplexity V
        (t3BoundaryDRun q n k epsilon delta t).current.toFinset hA ≤
      (epsilon + delta + logSlack cA n : ENat) := by
  obtain ⟨cDecoder, hDecoder⟩ :=
    plainSetComplexity_of_t3BoundaryVersionDecoder_eval V hV q
  refine ⟨24 + cDecoder, ?_⟩
  intro n k epsilon delta t hA hepsilon hdelta hkn
  have hwidth : (t3BoundaryDRun q n k epsilon delta t).rebuilds <
      2 ^ (epsilon + delta) :=
    t3BoundaryD_rebuilds_lt hq n k epsilon delta t hepsilon hdelta
  have hEval := t3BoundaryVersionDecoder_eval q n k epsilon delta t hwidth
  have hPlain :=
    hDecoder
      (t3VersionProgram 0 n k epsilon delta
        (t3BoundaryDRun q n k epsilon delta t).rebuilds)
      (t3BoundaryDRun q n k epsilon delta t).current hA hEval
  have hProgram :
      (t3VersionProgram 0 n k epsilon delta
        (t3BoundaryDRun q n k epsilon delta t).rebuilds).length ≤
        epsilon + delta + logSlack 24 n := by
    have h := t3VersionProgram_length_le 0 n k epsilon delta
      (t3BoundaryDRun q n k epsilon delta t).rebuilds
      hkn (le_trans hepsilon hkn)
      (le_trans (le_trans hdelta (Nat.sub_le k epsilon)) hkn)
      (by simpa [logSlack] using hwidth)
    simpa using h
  calc
    plainSetComplexity V
        (t3BoundaryDRun q n k epsilon delta t).current.toFinset hA
        ≤ (((t3VersionProgram 0 n k epsilon delta
            (t3BoundaryDRun q n k epsilon delta t).rebuilds).length +
            cDecoder : Nat) : ENat) := by
      simpa only [Nat.cast_add] using hPlain
    _ ≤ ((epsilon + delta + logSlack 24 n + cDecoder : Nat) : ENat) := by
      exact_mod_cast Nat.add_le_add_right hProgram cDecoder
    _ ≤ ((epsilon + delta + logSlack (24 + cDecoder) n : Nat) : ENat) := by
      exact_mod_cast (show
        epsilon + delta + logSlack 24 n + cDecoder ≤
          epsilon + delta + logSlack (24 + cDecoder) n by
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits n).length)])

end Kolmogorov
