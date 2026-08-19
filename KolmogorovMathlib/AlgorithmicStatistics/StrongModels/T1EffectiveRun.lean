import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams


namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

structure T1RunState where
  current : List BitString
  bMarked : List BitString
  cMarked : List BitString
  dMarked : List BitString
  seenCPrime : List BitString
  seenCDouble : List BitString
  versions : List (List BitString)
  external : Nat
  saturation : Nat
  totalC : Nat
  totalD : Nat

abbrev T1RunStateData :=
  List BitString × List BitString × List BitString × List BitString × List BitString ×
    List BitString × List (List BitString) × Nat × Nat × Nat × Nat

def T1RunState.toProd (s : T1RunState) : T1RunStateData :=
  (s.current, s.bMarked, s.cMarked, s.dMarked, s.seenCPrime,
   s.seenCDouble, s.versions, s.external, s.saturation, s.totalC, s.totalD)

def T1RunState.ofProd (p : T1RunStateData) : T1RunState :=
  { current := p.1, bMarked := p.2.1, cMarked := p.2.2.1, dMarked := p.2.2.2.1,
    seenCPrime := p.2.2.2.2.1, seenCDouble := p.2.2.2.2.2.1, versions := p.2.2.2.2.2.2.1,
    external := p.2.2.2.2.2.2.2.1, saturation := p.2.2.2.2.2.2.2.2.1,
    totalC := p.2.2.2.2.2.2.2.2.2.1, totalD := p.2.2.2.2.2.2.2.2.2.2 }

def t1RunStateEquiv : Equiv T1RunState T1RunStateData where
  toFun := T1RunState.toProd
  invFun := T1RunState.ofProd
  left_inv s := by cases s; rfl
  right_inv p := by
    rcases p with ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩
    rfl

instance : Primcodable T1RunState := Primcodable.ofEquiv _ t1RunStateEquiv

private theorem t1RunState_toProd_primrec :
    Primrec T1RunState.toProd := by
  exact Primrec.of_equiv

private theorem t1RunState_ofProd_primrec :
    Primrec T1RunState.ofProd := by
  exact Primrec.of_equiv_symm

private theorem t1RunState_current_primrec :
    Primrec T1RunState.current :=
  Primrec.fst.comp t1RunState_toProd_primrec

private theorem t1RunState_bMarked_primrec :
    Primrec T1RunState.bMarked :=
  (Primrec.fst.comp Primrec.snd).comp t1RunState_toProd_primrec

private theorem t1RunState_cMarked_primrec :
    Primrec T1RunState.cMarked :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    t1RunState_toProd_primrec

private theorem t1RunState_dMarked_primrec :
    Primrec T1RunState.dMarked :=
  (Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd))).comp t1RunState_toProd_primrec

private theorem t1RunState_seenCPrime_primrec :
    Primrec T1RunState.seenCPrime :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd)))).comp t1RunState_toProd_primrec

private theorem t1RunState_seenCDouble_primrec :
    Primrec T1RunState.seenCDouble :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))).comp
      t1RunState_toProd_primrec

private theorem t1RunState_versions_primrec :
    Primrec T1RunState.versions :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)))))).comp t1RunState_toProd_primrec

private theorem t1RunState_external_primrec :
    Primrec T1RunState.external :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))))).comp t1RunState_toProd_primrec

private theorem t1RunState_saturation_primrec :
    Primrec T1RunState.saturation :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))))).comp
        t1RunState_toProd_primrec

private theorem t1RunState_totalC_primrec :
    Primrec T1RunState.totalC :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.snd))))))))).comp
          t1RunState_toProd_primrec

private theorem t1RunState_totalD_primrec :
    Primrec T1RunState.totalD := by
  have h1 : Primrec (fun p : T1RunStateData => p.2) := Primrec.snd
  have h2 : Primrec (fun p : T1RunStateData => p.2.2) :=
    Primrec.snd.comp h1
  have h3 : Primrec (fun p : T1RunStateData => p.2.2.2) :=
    Primrec.snd.comp h2
  have h4 : Primrec (fun p : T1RunStateData => p.2.2.2.2) :=
    Primrec.snd.comp h3
  have h5 : Primrec (fun p : T1RunStateData => p.2.2.2.2.2) :=
    Primrec.snd.comp h4
  have h6 : Primrec (fun p : T1RunStateData => p.2.2.2.2.2.2) :=
    Primrec.snd.comp h5
  have h7 : Primrec (fun p : T1RunStateData => p.2.2.2.2.2.2.2) :=
    Primrec.snd.comp h6
  have h8 : Primrec (fun p : T1RunStateData => p.2.2.2.2.2.2.2.2) :=
    Primrec.snd.comp h7
  have h9 : Primrec (fun p : T1RunStateData => p.2.2.2.2.2.2.2.2.2) :=
    Primrec.snd.comp h8
  have h10 : Primrec (fun p : T1RunStateData =>
      p.2.2.2.2.2.2.2.2.2.2) :=
    Primrec.snd.comp h9
  exact h10.comp t1RunState_toProd_primrec

private theorem t1RunState_mk_primrec
    {α : Type} [Primcodable α]
    {current bMarked cMarked dMarked seenCPrime seenCDouble :
      α → List BitString}
    {versions : α → List (List BitString)}
    {external saturation totalC totalD : α → Nat}
    (hcurrent : Primrec current)
    (hbMarked : Primrec bMarked)
    (hcMarked : Primrec cMarked)
    (hdMarked : Primrec dMarked)
    (hseenCPrime : Primrec seenCPrime)
    (hseenCDouble : Primrec seenCDouble)
    (hversions : Primrec versions)
    (hexternal : Primrec external)
    (hsaturation : Primrec saturation)
    (htotalC : Primrec totalC)
    (htotalD : Primrec totalD) :
    Primrec (fun a =>
      { current := current a
      , bMarked := bMarked a
      , cMarked := cMarked a
      , dMarked := dMarked a
      , seenCPrime := seenCPrime a
      , seenCDouble := seenCDouble a
      , versions := versions a
      , external := external a
      , saturation := saturation a
      , totalC := totalC a
      , totalD := totalD a } : α → T1RunState) := by
  exact t1RunState_ofProd_primrec.comp
    (hcurrent.pair
      (hbMarked.pair
        (hcMarked.pair
          (hdMarked.pair
            (hseenCPrime.pair
              (hseenCDouble.pair
                (hversions.pair
                  (hexternal.pair
                    (hsaturation.pair
                      (htotalC.pair htotalD))))))))))

abbrev T1RunListUpdateData :=
  T1RunState × List BitString × List BitString × List BitString ×
    List BitString × List BitString

private def t1RunUpdateLists (p : T1RunListUpdateData) : T1RunState :=
  { p.1 with
    bMarked := p.2.1
    cMarked := p.2.2.1
    dMarked := p.2.2.2.1
    seenCPrime := p.2.2.2.2.1
    seenCDouble := p.2.2.2.2.2 }

private theorem t1RunUpdateLists_primrec :
    Primrec t1RunUpdateLists := by
  have hs : Primrec (fun p : T1RunListUpdateData => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.snd))))
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

abbrev T1RunCounterUpdateData :=
  T1RunState × Nat × Nat × Nat × Nat

private def t1RunUpdateCounters (p : T1RunCounterUpdateData) :
    T1RunState :=
  { p.1 with
    external := p.2.1
    saturation := p.2.2.1
    totalC := p.2.2.2.1
    totalD := p.2.2.2.2 }

private theorem t1RunUpdateCounters_primrec :
    Primrec t1RunUpdateCounters := by
  have hs : Primrec (fun p : T1RunCounterUpdateData => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (t1RunState_cMarked_primrec.comp hs)
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)))

def t1InitialCurrent (n k epsilon : Nat) : List BitString :=
  (canonicalFinsetList (stringsOfLength n)).take (2 ^ (k - epsilon))

def t1InitialRunState (n k epsilon : Nat) : T1RunState :=
  let initial := t1InitialCurrent n k epsilon
  { current := initial
  , bMarked := []
  , cMarked := []
  , dMarked := []
  , seenCPrime := []
  , seenCDouble := []
  , versions := [initial]
  , external := 0
  , saturation := 0
  , totalC := 0
  , totalD := 0 }

def t1RunMarked (s : T1RunState) : List BitString :=
  (s.bMarked ++ s.cMarked ++ s.dMarked).eraseDups

def t1RunSaturated (s : T1RunState) (quota : Nat) : Bool :=
  let intersection := s.current.filter
    (fun x => decide (x ∈ s.cMarked) || decide (x ∈ s.dMarked))
  decide (quota ≤ intersection.length)

def t1RunUnmarked (n : Nat) (s : T1RunState) : List BitString :=
  (canonicalFinsetList (stringsOfLength n)).filter
    (fun x => !decide (x ∈ t1RunMarked s))

private def t1RunReplaceCurrent
    (p : T1RunState × List BitString) : T1RunState :=
  { p.1 with current := p.2, versions := p.1.versions ++ [p.2] }

private def t1RunBitStringDecidableEq : DecidableEq BitString :=
  inferInstance

private noncomputable def t1RunNextCurrent
    (p : Nat × Nat × Nat × Nat × T1RunState) : List BitString :=
  @t1SparseSubsetSelectorList BitString t1RunBitStringDecidableEq
    (t1RunUnmarked p.2.1 p.2.2.2.2)
    (p.2.2.2.2.seenCDouble.map canonicalPointListOfCode)
    (2 ^ (p.2.2.1 - p.2.2.2.1))
    (p.1 * p.2.1 + p.1)

noncomputable def t1RunRebuild (cSparse n k epsilon : Nat)
    (s : T1RunState) : T1RunState :=
  t1RunReplaceCurrent
    (s, t1RunNextCurrent (cSparse, n, k, epsilon, s))

private theorem t1CubeList_primrec :
    Primrec (fun n : Nat => canonicalFinsetList (stringsOfLength n)) := by
  exact canonicalFinsetList_toFinset_primrec.comp allStrings_primrec

private theorem t1InitialCurrent_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      t1InitialCurrent p.1 p.2.1 p.2.2) := by
  exact Primrec.list_take.comp
    (twoPow_primrec.comp
      (Primrec.nat_sub.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))
    (t1CubeList_primrec.comp Primrec.fst)

private theorem t1InitialRunState_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      t1InitialRunState p.1 p.2.1 p.2.2) := by
  have hinitial : Primrec (fun p : Nat × Nat × Nat =>
      t1InitialCurrent p.1 p.2.1 p.2.2) :=
    t1InitialCurrent_primrec
  exact (t1RunState_mk_primrec
    hinitial
    (Primrec.const [])
    (Primrec.const [])
    (Primrec.const [])
    (Primrec.const [])
    (Primrec.const [])
    (Primrec.list_cons.comp hinitial (Primrec.const []))
    (Primrec.const 0)
    (Primrec.const 0)
    (Primrec.const 0)
    (Primrec.const 0)).of_eq (fun p => by
      simp [t1InitialRunState])

private theorem t1LogSlack_primrec :
    Primrec₂ (fun c n : Nat => logSlack c n) := by
  unfold logSlack
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp Primrec.fst
      (Primrec.list_length.comp
        (primrecNatBits.comp Primrec.snd)))
    Primrec.fst

private theorem t1RunMarked_primrec :
    Primrec t1RunMarked := by
  exact eraseDups_bitstring_primrec.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        t1RunState_bMarked_primrec
        t1RunState_cMarked_primrec)
      t1RunState_dMarked_primrec)

private theorem t1RunSaturated_primrec :
    Primrec (fun p : T1RunState × Nat =>
      t1RunSaturated p.1 p.2) := by
  have hcurrent : Primrec (fun p : T1RunState × Nat => p.1.current) :=
    t1RunState_current_primrec.comp Primrec.fst
  have hcMarked : Primrec (fun p : T1RunState × Nat => p.1.cMarked) :=
    t1RunState_cMarked_primrec.comp Primrec.fst
  have hdMarked : Primrec (fun p : T1RunState × Nat => p.1.dMarked) :=
    t1RunState_dMarked_primrec.comp Primrec.fst
  have hcMem : Primrec (fun q : (T1RunState × Nat) × BitString =>
      decide (q.2 ∈ q.1.1.cMarked)) :=
    by
      convert (@decide_mem_primrec BitString _
        t1RunBitStringDecidableEq).comp
        (hcMarked.comp Primrec.fst) Primrec.snd using 1
      funext q
      apply Bool.eq_iff_iff.mpr
      simp
  have hdMem : Primrec (fun q : (T1RunState × Nat) × BitString =>
      decide (q.2 ∈ q.1.1.dMarked)) :=
    by
      convert (@decide_mem_primrec BitString _
        t1RunBitStringDecidableEq).comp
        (hdMarked.comp Primrec.fst) Primrec.snd using 1
      funext q
      apply Bool.eq_iff_iff.mpr
      simp
  have hintersection : Primrec (fun p : T1RunState × Nat =>
      p.1.current.filter
        (fun x => decide (x ∈ p.1.cMarked) ||
          decide (x ∈ p.1.dMarked))) :=
    list_filter_primrec hcurrent
      ((Primrec.or.comp hcMem hdMem).to₂)
  exact (PrimrecPred.decide
    (Primrec.nat_le.comp Primrec.snd
      (Primrec.list_length.comp hintersection)))

private theorem t1RunUnmarked_primrec :
    Primrec (fun p : Nat × T1RunState =>
      t1RunUnmarked p.1 p.2) := by
  have hcube : Primrec (fun p : Nat × T1RunState =>
      canonicalFinsetList (stringsOfLength p.1)) :=
    t1CubeList_primrec.comp Primrec.fst
  have hmem : Primrec (fun q : (Nat × T1RunState) × BitString =>
      decide (q.2 ∈ t1RunMarked q.1.2)) :=
    by
      convert decide_mem_primrec.comp
        (t1RunMarked_primrec.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd using 1
      funext q
      apply Bool.eq_iff_iff.mpr
      simp
  exact list_filter_primrec hcube
    ((Primrec.not.comp hmem).to₂)

private theorem t1RunUnmarked_computable_comp
    {β : Type} [Primcodable β] {n : β → Nat} {s : β → T1RunState}
    (hn : Computable n) (hs : Computable s) :
    Computable (fun b => t1RunUnmarked (n b) (s b)) :=
  t1RunUnmarked_primrec.to₂.to_comp.comp hn hs

private theorem t1SeenCDoubleModels_primrec :
    Primrec (fun s : T1RunState =>
      s.seenCDouble.map canonicalPointListOfCode) :=
  Primrec.list_map t1RunState_seenCDouble_primrec
    ((canonicalPointListOfCode_primrec.comp Primrec.snd).to₂)

private theorem t1SeenCDoubleModels_computable_comp
    {β : Type} [Primcodable β] {s : β → T1RunState}
    (hs : Computable s) :
    Computable (fun b =>
      (s b).seenCDouble.map canonicalPointListOfCode) :=
  t1SeenCDoubleModels_primrec.to_comp.comp hs

private theorem t1RunReplaceCurrent_primrec :
    Primrec t1RunReplaceCurrent := by
  have hs : Primrec (fun p : T1RunState × List BitString => p.1) :=
    Primrec.fst
  have hnext : Primrec (fun p : T1RunState × List BitString => p.2) :=
    Primrec.snd
  have hb : Primrec (fun p : T1RunState × List BitString => p.1.bMarked) :=
    t1RunState_bMarked_primrec.comp hs
  have hc : Primrec (fun p : T1RunState × List BitString => p.1.cMarked) :=
    t1RunState_cMarked_primrec.comp hs
  have hd : Primrec (fun p : T1RunState × List BitString => p.1.dMarked) :=
    t1RunState_dMarked_primrec.comp hs
  have hcp : Primrec (fun p : T1RunState × List BitString =>
      p.1.seenCPrime) :=
    t1RunState_seenCPrime_primrec.comp hs
  have hcd : Primrec (fun p : T1RunState × List BitString =>
      p.1.seenCDouble) :=
    t1RunState_seenCDouble_primrec.comp hs
  have hversions : Primrec (fun p : T1RunState × List BitString =>
      p.1.versions ++ [p.2]) :=
    Primrec.list_append.comp
      (t1RunState_versions_primrec.comp hs)
      (Primrec.list_cons.comp hnext (Primrec.const []))
  have hext : Primrec (fun p : T1RunState × List BitString =>
      p.1.external) :=
    t1RunState_external_primrec.comp hs
  have hsat : Primrec (fun p : T1RunState × List BitString =>
      p.1.saturation) :=
    t1RunState_saturation_primrec.comp hs
  have htc : Primrec (fun p : T1RunState × List BitString =>
      p.1.totalC) :=
    t1RunState_totalC_primrec.comp hs
  have htd : Primrec (fun p : T1RunState × List BitString =>
      p.1.totalD) :=
    t1RunState_totalD_primrec.comp hs
  have htail10 := htc.pair htd
  have htail9 := hsat.pair htail10
  have htail8 := hext.pair htail9
  have htail7 := hversions.pair htail8
  have htail6 := hcd.pair htail7
  have htail5 := hcp.pair htail6
  have htail4 := hd.pair htail5
  have htail3 := hc.pair htail4
  have htail2 := hb.pair htail3
  exact t1RunState_ofProd_primrec.comp (hnext.pair htail2)

private theorem t1RunNextCurrent_computable :
    Computable t1RunNextCurrent := by
  unfold t1RunNextCurrent
  let P := Nat × Nat × Nat × Nat × T1RunState
  have hcSparse : Primrec (fun p : P => p.1) := Primrec.fst
  have hn : Primrec (fun p : P => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun p : P => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hepsilon : Primrec (fun p : P => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))
  have hs : Primrec (fun p : P => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))
  have hU : Computable (fun p : P =>
      t1RunUnmarked p.2.1 p.2.2.2.2) :=
    t1RunUnmarked_computable_comp hn.to_comp hs.to_comp
  have hCs : Computable (fun p : P =>
      p.2.2.2.2.seenCDouble.map canonicalPointListOfCode) :=
    t1SeenCDoubleModels_computable_comp hs.to_comp
  have hN : Primrec (fun p : P =>
      2 ^ (p.2.2.1 - p.2.2.2.1)) :=
    (twoPow_primrec.comp
      (Primrec.nat_sub.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp
          (Primrec.snd.comp Primrec.snd)))))
  have ht : Primrec (fun p : P => p.1 * p.2.1 + p.1) :=
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp Primrec.fst
        (Primrec.fst.comp Primrec.snd))
      Primrec.fst)
  exact @t1SparseSubsetSelectorList_computable_comp
    BitString P _ t1RunBitStringDecidableEq _
    _ _ _ _ hU hCs hN.to_comp ht.to_comp

private noncomputable def t1RunRebuildTuple
    (p : Nat × Nat × Nat × Nat × T1RunState) : T1RunState :=
  t1RunRebuild p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

private theorem t1RunRebuildTuple_computable :
    Computable t1RunRebuildTuple := by
  let P := Nat × Nat × Nat × Nat × T1RunState
  have hs : Computable (fun p : P => p.2.2.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))).to_comp
  exact (t1RunReplaceCurrent_primrec.to_comp.comp
      (hs.pair t1RunNextCurrent_computable)).of_eq fun a => rfl

theorem t1RunRebuild_computable :
    Computable (fun p : Nat × Nat × Nat × Nat × T1RunState =>
      t1RunRebuild p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2) := by
  exact t1RunRebuildTuple_computable.of_eq fun a => rfl

private abbrev T1RunStepParams :=
  ((Nat × Nat) × (Nat × Nat)) × (Nat × T1RunState)

private def t1RunStepParamsCSparse (p : T1RunStepParams) : Nat :=
  p.1.1.1

private def t1RunStepParamsN (p : T1RunStepParams) : Nat :=
  p.1.1.2

private def t1RunStepParamsK (p : T1RunStepParams) : Nat :=
  p.1.2.1

private def t1RunStepParamsEpsilon (p : T1RunStepParams) : Nat :=
  p.1.2.2

private def t1RunStepParamsQuota (p : T1RunStepParams) : Nat :=
  p.2.1

private def t1RunStepParamsState (p : T1RunStepParams) : T1RunState :=
  p.2.2

private theorem t1RunStepParams_cSparse_primrec :
    Primrec t1RunStepParamsCSparse :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.fst)

private theorem t1RunStepParams_n_primrec :
    Primrec t1RunStepParamsN :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.fst)

private theorem t1RunStepParams_k_primrec :
    Primrec t1RunStepParamsK :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.fst)

private theorem t1RunStepParams_epsilon_primrec :
    Primrec t1RunStepParamsEpsilon :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.fst)

private theorem t1RunStepParams_quota_primrec :
    Primrec t1RunStepParamsQuota :=
  Primrec.fst.comp Primrec.snd

private theorem t1RunStepParams_state_primrec :
    Primrec t1RunStepParamsState :=
  Primrec.snd.comp Primrec.snd

private theorem t1RunListUpdateData_mk_primrec
    {α : Type} [Primcodable α]
    {s : α → T1RunState}
    {b c d cp cd : α → List BitString}
    (hs : Primrec s) (hb : Primrec b) (hc : Primrec c)
    (hd : Primrec d) (hcp : Primrec cp) (hcd : Primrec cd) :
    Primrec (fun a => (s a, b a, c a, d a, cp a, cd a) :
      α → T1RunListUpdateData) :=
  hs.pair (hb.pair (hc.pair (hd.pair (hcp.pair hcd))))

private theorem t1RunCounterUpdateData_mk_primrec
    {α : Type} [Primcodable α]
    {s : α → T1RunState} {external saturation totalC totalD : α → Nat}
    (hs : Primrec s) (hext : Primrec external)
    (hsat : Primrec saturation) (htc : Primrec totalC)
    (htd : Primrec totalD) :
    Primrec (fun a =>
      (s a, external a, saturation a, totalC a, totalD a) :
        α → T1RunCounterUpdateData) :=
  hs.pair (hext.pair (hsat.pair (htc.pair htd)))

private noncomputable def t1RunValidPoints (p : Nat × BitString) :
    List BitString :=
  (canonicalPointListOfCode p.2).filter
    (fun x => x.length = p.1)

private theorem t1RunValidPoints_primrec :
    Primrec t1RunValidPoints := by
  have hpoints : Primrec (fun p : Nat × BitString =>
      canonicalPointListOfCode p.2) :=
    canonicalPointListOfCode_primrec.comp Primrec.snd
  have hlength : Primrec (fun q : (Nat × BitString) × BitString =>
      decide (q.2.length = q.1.1)) :=
    PrimrecPred.decide
      (Primrec.eq.comp
        (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst))
  exact list_filter_primrec hpoints hlength.to₂

private noncomputable def t1RunBatchValidPoints
    (p : Nat × List BitString × List BitString) : List BitString :=
  let toActivate := p.2.2.filter (fun w => w ∈ p.2.1)
  (toActivate.flatMap canonicalPointListOfCode).filter
    (fun x => x.length = p.1)

private theorem t1RunBatchValidPoints_primrec :
    Primrec t1RunBatchValidPoints := by
  have hbatch : Primrec (fun p :
      Nat × List BitString × List BitString => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hmem : Primrec (fun q :
      (Nat × List BitString × List BitString) × BitString =>
        decide (q.2 ∈ q.1.2.1)) :=
    by
      exact PrimrecPred.decide
        (mem_bitstring_primrec.comp
          (Primrec.snd.pair
            (Primrec.fst.comp
              (Primrec.snd.comp Primrec.fst))))
  have htoActivate : Primrec (fun p :
      Nat × List BitString × List BitString =>
        p.2.2.filter (fun w => w ∈ p.2.1)) :=
    list_filter_primrec hbatch hmem.to₂
  have hpoints : Primrec (fun p :
      Nat × List BitString × List BitString =>
        (p.2.2.filter (fun w => w ∈ p.2.1)).flatMap
          canonicalPointListOfCode) :=
    Primrec.list_flatMap htoActivate
      ((canonicalPointListOfCode_primrec.comp Primrec.snd).to₂)
  have hlength : Primrec (fun q :
      (Nat × List BitString × List BitString) × BitString =>
        decide (q.2.length = q.1.1)) :=
    PrimrecPred.decide
      (Primrec.eq.comp
        (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst))
  exact list_filter_primrec hpoints hlength.to₂

private def t1RunHitCount
    (p : List BitString × List BitString) : Nat :=
  (p.1.filter (fun x => x ∈ p.2)).length

private theorem t1RunHitCount_primrec :
    Primrec t1RunHitCount := by
  have hmem : Primrec (fun q :
      (List BitString × List BitString) × BitString =>
        decide (q.2 ∈ q.1.2)) :=
    by
      exact PrimrecPred.decide
        (mem_bitstring_primrec.comp
          (Primrec.snd.pair
            (Primrec.snd.comp Primrec.fst)))
  exact Primrec.list_length.comp
    (list_filter_primrec Primrec.fst hmem.to₂)

private def t1RunAppendB
    (p : T1RunState × List BitString) : T1RunState :=
  { p.1 with bMarked := p.1.bMarked ++ p.2 }

private theorem t1RunAppendB_primrec :
    Primrec t1RunAppendB := by
  have hs : Primrec (fun p : T1RunState × List BitString => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_bMarked_primrec.comp hs) Primrec.snd)
    (t1RunState_cMarked_primrec.comp hs)
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

private noncomputable def t1RunStepBSetPre
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunAppendB
    (t1RunStepParamsState p.1,
      t1RunValidPoints (t1RunStepParamsN p.1, p.2))

private noncomputable def t1RunStepBSetRebuilt
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunRebuildTuple
    (t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
      t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
      t1RunStepBSetPre p)

private def t1RunExternalRebuildFinal
    (p : T1RunState × T1RunState) : T1RunState :=
  { p.2 with external := p.1.external + 1 }

private theorem t1RunExternalRebuildFinal_primrec :
    Primrec t1RunExternalRebuildFinal := by
  have hold : Primrec (fun p : T1RunState × T1RunState => p.1) :=
    Primrec.fst
  have hnew : Primrec (fun p : T1RunState × T1RunState => p.2) :=
    Primrec.snd
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hnew)
    (t1RunState_bMarked_primrec.comp hnew)
    (t1RunState_cMarked_primrec.comp hnew)
    (t1RunState_dMarked_primrec.comp hnew)
    (t1RunState_seenCPrime_primrec.comp hnew)
    (t1RunState_seenCDouble_primrec.comp hnew)
    (t1RunState_versions_primrec.comp hnew)
    (Primrec.nat_add.comp
      (t1RunState_external_primrec.comp hold) (Primrec.const 1))
    (t1RunState_saturation_primrec.comp hnew)
    (t1RunState_totalC_primrec.comp hnew)
    (t1RunState_totalD_primrec.comp hnew)

private noncomputable def t1RunStepBSetFn
    (p : T1RunStepParams × BitString) : T1RunState :=
  let s := t1RunStepParamsState p.1
  let s'' := t1RunStepBSetRebuilt p
  t1RunExternalRebuildFinal (s, s'')

private def t1RunAppendCSeenDouble
    (p : T1RunState × (List BitString × List BitString)) :
    T1RunState :=
  { p.1 with
    cMarked := p.1.cMarked ++ p.2.1
    seenCDouble := p.1.seenCDouble ++ p.2.2 }

private theorem t1RunAppendCSeenDouble_primrec :
    Primrec t1RunAppendCSeenDouble := by
  have hs : Primrec (fun p :
      T1RunState × (List BitString × List BitString) => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_cMarked_primrec.comp hs)
      (Primrec.fst.comp Primrec.snd))
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_seenCDouble_primrec.comp hs)
      (Primrec.snd.comp Primrec.snd))
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

private noncomputable def t1RunStepCDoublePre
    (p : T1RunStepParams × List BitString) : T1RunState :=
  let s := t1RunStepParamsState p.1
  let pts := t1RunBatchValidPoints
    (t1RunStepParamsN p.1, s.seenCPrime, p.2)
  t1RunAppendCSeenDouble (s, pts, p.2)

private noncomputable def t1RunStepCDoubleRebuilt
    (p : T1RunStepParams × List BitString) : T1RunState :=
  t1RunRebuildTuple
    (t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
      t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
      t1RunStepCDoublePre p)

private noncomputable def t1RunStepCDoubleFn
    (p : T1RunStepParams × List BitString) : T1RunState :=
  let s := t1RunStepParamsState p.1
  let s'' := t1RunStepCDoubleRebuilt p
  t1RunExternalRebuildFinal (s, s'')

private def t1RunAppendSeenCPrime
    (p : T1RunState × BitString) : T1RunState :=
  { p.1 with seenCPrime := p.1.seenCPrime ++ [p.2] }

private theorem t1RunAppendSeenCPrime_primrec :
    Primrec t1RunAppendSeenCPrime := by
  have hs : Primrec (fun p : T1RunState × BitString => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (t1RunState_cMarked_primrec.comp hs)
    (t1RunState_dMarked_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_seenCPrime_primrec.comp hs)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

private def t1RunAppendC
    (p : T1RunState × List BitString) : T1RunState :=
  { p.1 with cMarked := p.1.cMarked ++ p.2 }

private theorem t1RunAppendC_primrec :
    Primrec t1RunAppendC := by
  have hs : Primrec (fun p : T1RunState × List BitString => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_cMarked_primrec.comp hs) Primrec.snd)
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

private def t1RunChargeC
    (p : T1RunState × Nat) : T1RunState :=
  { p.1 with totalC := p.1.totalC + p.2 }

private theorem t1RunChargeC_primrec :
    Primrec t1RunChargeC := by
  have hs : Primrec (fun p : T1RunState × Nat => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (t1RunState_cMarked_primrec.comp hs)
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (Primrec.nat_add.comp
      (t1RunState_totalC_primrec.comp hs) Primrec.snd)
    (t1RunState_totalD_primrec.comp hs)

private def t1RunSaturationRebuildFinal
    (p : T1RunState × T1RunState) : T1RunState :=
  { p.2 with saturation := p.1.saturation + 1 }

private theorem t1RunSaturationRebuildFinal_primrec :
    Primrec t1RunSaturationRebuildFinal := by
  have hold : Primrec (fun p : T1RunState × T1RunState => p.1) :=
    Primrec.fst
  have hnew : Primrec (fun p : T1RunState × T1RunState => p.2) :=
    Primrec.snd
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hnew)
    (t1RunState_bMarked_primrec.comp hnew)
    (t1RunState_cMarked_primrec.comp hnew)
    (t1RunState_dMarked_primrec.comp hnew)
    (t1RunState_seenCPrime_primrec.comp hnew)
    (t1RunState_seenCDouble_primrec.comp hnew)
    (t1RunState_versions_primrec.comp hnew)
    (t1RunState_external_primrec.comp hnew)
    (Primrec.nat_add.comp
      (t1RunState_saturation_primrec.comp hold) (Primrec.const 1))
    (t1RunState_totalC_primrec.comp hnew)
    (t1RunState_totalD_primrec.comp hnew)

private noncomputable def t1RunStepCPrimeSeen
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunAppendSeenCPrime (t1RunStepParamsState p.1, p.2)

private noncomputable def t1RunStepCPrimePoints
    (p : T1RunStepParams × BitString) : List BitString :=
  t1RunValidPoints (t1RunStepParamsN p.1, p.2)

private noncomputable def t1RunStepCPrimeCharged
    (p : T1RunStepParams × BitString) : T1RunState :=
  let s := t1RunStepParamsState p.1
  let pts := t1RunStepCPrimePoints p
  let marked := t1RunAppendC (t1RunStepCPrimeSeen p, pts)
  t1RunChargeC (marked, t1RunHitCount (s.current, pts))

private noncomputable def t1RunStepCPrimeRebuilt
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunRebuildTuple
    (t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
      t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
      t1RunStepCPrimeCharged p)

private noncomputable def t1RunStepCPrimeSaturated
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunSaturationRebuildFinal
    (t1RunStepParamsState p.1, t1RunStepCPrimeRebuilt p)

private def t1RunStepCPrimeActive
    (p : T1RunStepParams × BitString) : Bool :=
  decide (p.2 ∈ (t1RunStepParamsState p.1).seenCDouble)

private noncomputable def t1RunStepCPrimeSaturatedGuard
    (p : T1RunStepParams × BitString) : Bool :=
  t1RunSaturated (t1RunStepCPrimeCharged p)
    (t1RunStepParamsQuota p.1)

private noncomputable def t1RunStepCPrimeActiveFn
    (p : T1RunStepParams × BitString) : T1RunState :=
  if t1RunStepCPrimeSaturatedGuard p then
    t1RunStepCPrimeSaturated p
  else t1RunStepCPrimeCharged p

private noncomputable def t1RunStepCPrimeFn
    (p : T1RunStepParams × BitString) : T1RunState :=
  if t1RunStepCPrimeActive p then
    t1RunStepCPrimeActiveFn p
  else
    t1RunStepCPrimeSeen p

private def t1RunAppendD
    (p : T1RunState × List BitString) : T1RunState :=
  { p.1 with dMarked := p.1.dMarked ++ p.2 }

private theorem t1RunAppendD_primrec :
    Primrec t1RunAppendD := by
  have hs : Primrec (fun p : T1RunState × List BitString => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (t1RunState_cMarked_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_dMarked_primrec.comp hs) Primrec.snd)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

private def t1RunChargeD
    (p : T1RunState × Nat) : T1RunState :=
  { p.1 with totalD := p.1.totalD + p.2 }

private theorem t1RunChargeD_primrec :
    Primrec t1RunChargeD := by
  have hs : Primrec (fun p : T1RunState × Nat => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (t1RunState_cMarked_primrec.comp hs)
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (Primrec.nat_add.comp
      (t1RunState_totalD_primrec.comp hs) Primrec.snd)

private noncomputable def t1RunStepDValidPoints
    (p : T1RunStepParams × BitString) : List BitString :=
  if p.2.length = t1RunStepParamsN p.1 then [p.2] else []

private noncomputable def t1RunStepDHitCount
    (p : T1RunStepParams × BitString) : Nat :=
  if p.2 ∈ (t1RunStepParamsState p.1).current then 1 else 0

private noncomputable def t1RunStepDCharged
    (p : T1RunStepParams × BitString) : T1RunState :=
  let marked := t1RunAppendD
    (t1RunStepParamsState p.1, t1RunStepDValidPoints p)
  t1RunChargeD (marked, t1RunStepDHitCount p)

private noncomputable def t1RunStepDRebuilt
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunRebuildTuple
    (t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
      t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
      t1RunStepDCharged p)

private noncomputable def t1RunStepDSaturated
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunSaturationRebuildFinal
    (t1RunStepParamsState p.1, t1RunStepDRebuilt p)

private noncomputable def t1RunStepDSaturatedGuard
    (p : T1RunStepParams × BitString) : Bool :=
  t1RunSaturated (t1RunStepDCharged p)
    (t1RunStepParamsQuota p.1)

private noncomputable def t1RunStepDStringFn
    (p : T1RunStepParams × BitString) : T1RunState :=
  if t1RunStepDSaturatedGuard p then
    t1RunStepDSaturated p
  else t1RunStepDCharged p

private theorem t1RunStepBSetPre_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepBSetPre p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunAppendB_primrec.comp
    ((t1RunStepParams_state_primrec.comp hparams).pair
      (t1RunValidPoints_primrec.comp
        ((t1RunStepParams_n_primrec.comp hparams).pair
          Primrec.snd)))).of_eq (fun p => by rfl)

private theorem t1RunStepBSetRebuilt_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepBSetRebuilt p) := by
  have hparams : Primrec (fun q :
      T1RunStepParams × BitString => q.1) := Primrec.fst
  have hinput : Computable (fun p :
      T1RunStepParams × BitString =>
      ((t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
        t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
        t1RunStepBSetPre p) :
        Nat × Nat × Nat × Nat × T1RunState)) :=
    (t1RunStepParams_cSparse_primrec.comp hparams).to_comp.pair
      ((t1RunStepParams_n_primrec.comp hparams).to_comp.pair
        ((t1RunStepParams_k_primrec.comp hparams).to_comp.pair
          ((t1RunStepParams_epsilon_primrec.comp hparams).to_comp.pair
            t1RunStepBSetPre_primrec.to_comp)))
  exact t1RunRebuildTuple_computable.comp hinput

private theorem t1RunStepBSetFn_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepBSetFn p) := by
  let Q := T1RunStepParams × BitString
  have hparams : Primrec (fun q : Q => q.1) := Primrec.fst
  have hrebuild : Computable (fun q : Q =>
      t1RunStepBSetRebuilt q) :=
    t1RunStepBSetRebuilt_computable
  exact (t1RunExternalRebuildFinal_primrec.to_comp.comp
    ((t1RunStepParams_state_primrec.comp hparams).to_comp.pair
      hrebuild)).of_eq (fun q => by rfl)

private theorem t1RunStepCDoublePre_computable :
    Computable (fun p : T1RunStepParams × List BitString =>
      t1RunStepCDoublePre p) := by
  let Q := T1RunStepParams × List BitString
  have hparams : Primrec (fun q : Q => q.1) := Primrec.fst
  have hs : Primrec (fun q : Q =>
      t1RunStepParamsState q.1) :=
    t1RunStepParams_state_primrec.comp hparams
  have hpoints : Primrec (fun q : Q =>
      t1RunBatchValidPoints
        (t1RunStepParamsN q.1,
          (t1RunStepParamsState q.1).seenCPrime, q.2)) :=
    t1RunBatchValidPoints_primrec.comp
      ((t1RunStepParams_n_primrec.comp hparams).pair
        ((t1RunState_seenCPrime_primrec.comp hs).pair
          Primrec.snd))
  exact (t1RunAppendCSeenDouble_primrec.comp
    (hs.pair (hpoints.pair Primrec.snd))).to_comp.of_eq
      (fun q => by rfl)

private theorem t1RunStepCDoubleRebuilt_computable :
    Computable (fun p : T1RunStepParams × List BitString =>
      t1RunStepCDoubleRebuilt p) := by
  let Q := T1RunStepParams × List BitString
  have hparams : Primrec (fun q : Q => q.1) := Primrec.fst
  have hinput : Computable (fun p : Q =>
      ((t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
        t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
        t1RunStepCDoublePre p) :
        Nat × Nat × Nat × Nat × T1RunState)) :=
    (t1RunStepParams_cSparse_primrec.comp hparams).to_comp.pair
      ((t1RunStepParams_n_primrec.comp hparams).to_comp.pair
        ((t1RunStepParams_k_primrec.comp hparams).to_comp.pair
          ((t1RunStepParams_epsilon_primrec.comp hparams).to_comp.pair
            t1RunStepCDoublePre_computable)))
  exact t1RunRebuildTuple_computable.comp hinput

private theorem t1RunStepCDoubleFn_computable :
    Computable (fun p : T1RunStepParams × List BitString =>
      t1RunStepCDoubleFn p) := by
  let Q := T1RunStepParams × List BitString
  have hparams : Primrec (fun q : Q => q.1) := Primrec.fst
  exact (t1RunExternalRebuildFinal_primrec.to_comp.comp
    ((t1RunStepParams_state_primrec.comp hparams).to_comp.pair
      t1RunStepCDoubleRebuilt_computable)).of_eq
        (fun q => by rfl)

private theorem t1RunStepCPrimeSeen_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeSeen p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunAppendSeenCPrime_primrec.comp
    ((t1RunStepParams_state_primrec.comp hparams).pair
      Primrec.snd)).of_eq (fun p => by rfl)

private theorem t1RunStepCPrimePoints_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimePoints p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunValidPoints_primrec.comp
    ((t1RunStepParams_n_primrec.comp hparams).pair
      Primrec.snd)).of_eq (fun p => by rfl)

private theorem t1RunStepCPrimeCharged_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeCharged p) := by
  let Q := T1RunStepParams × BitString
  have hparams : Primrec (fun p : Q => p.1) := Primrec.fst
  have hs : Primrec (fun p : Q =>
      t1RunStepParamsState p.1) :=
    t1RunStepParams_state_primrec.comp hparams
  have hmarked : Primrec (fun p : Q =>
      t1RunAppendC
        (t1RunStepCPrimeSeen p, t1RunStepCPrimePoints p)) :=
    t1RunAppendC_primrec.comp
      (t1RunStepCPrimeSeen_primrec.pair
        t1RunStepCPrimePoints_primrec)
  have hhits : Primrec (fun p : Q =>
      t1RunHitCount
        ((t1RunStepParamsState p.1).current,
          t1RunStepCPrimePoints p)) :=
    t1RunHitCount_primrec.comp
      ((t1RunState_current_primrec.comp hs).pair
        t1RunStepCPrimePoints_primrec)
  exact (t1RunChargeC_primrec.comp
    (hmarked.pair hhits)).of_eq (fun p => by rfl)

private theorem t1RunStepCPrimeRebuilt_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeRebuilt p) := by
  let Q := T1RunStepParams × BitString
  have hparams : Primrec (fun p : Q => p.1) := Primrec.fst
  have hinput : Computable (fun p : Q =>
      ((t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
        t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
        t1RunStepCPrimeCharged p) :
        Nat × Nat × Nat × Nat × T1RunState)) :=
    (t1RunStepParams_cSparse_primrec.comp hparams).to_comp.pair
      ((t1RunStepParams_n_primrec.comp hparams).to_comp.pair
        ((t1RunStepParams_k_primrec.comp hparams).to_comp.pair
          ((t1RunStepParams_epsilon_primrec.comp hparams).to_comp.pair
            t1RunStepCPrimeCharged_primrec.to_comp)))
  exact t1RunRebuildTuple_computable.comp hinput

private theorem t1RunStepCPrimeSaturated_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeSaturated p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunSaturationRebuildFinal_primrec.to_comp.comp
    ((t1RunStepParams_state_primrec.comp hparams).to_comp.pair
      t1RunStepCPrimeRebuilt_computable)).of_eq
        (fun p => by rfl)

private theorem t1RunStepCPrimeActive_primrec :
    Primrec t1RunStepCPrimeActive := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  have hs : Primrec (fun p :
      T1RunStepParams × BitString =>
      t1RunStepParamsState p.1) :=
    t1RunStepParams_state_primrec.comp hparams
  exact PrimrecPred.decide
    (mem_bitstring_primrec.comp
      (Primrec.snd.pair
        (t1RunState_seenCDouble_primrec.comp hs)))

private theorem t1RunStepCPrimeSaturatedGuard_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeSaturatedGuard p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunSaturated_primrec.comp
    (t1RunStepCPrimeCharged_primrec.pair
      (t1RunStepParams_quota_primrec.comp hparams))).of_eq
        (fun p => by rfl)

private theorem t1RunStepCPrimeActiveFn_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeActiveFn p) := by
  exact (Computable.cond
    t1RunStepCPrimeSaturatedGuard_primrec.to_comp
    t1RunStepCPrimeSaturated_computable
    t1RunStepCPrimeCharged_primrec.to_comp).of_eq
      (fun p => by
        simp only [t1RunStepCPrimeActiveFn]
        cases t1RunStepCPrimeSaturatedGuard p <;> rfl)

private theorem t1RunStepCPrimeFn_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeFn p) := by
  exact (Computable.cond t1RunStepCPrimeActive_primrec.to_comp
    t1RunStepCPrimeActiveFn_computable
    t1RunStepCPrimeSeen_primrec.to_comp).of_eq
      (fun p => by
        simp only [t1RunStepCPrimeFn]
        cases t1RunStepCPrimeActive p <;> rfl)

private theorem t1RunStepDValidPoints_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepDValidPoints p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  have hguard : Primrec (fun p :
      T1RunStepParams × BitString =>
      decide (p.2.length = t1RunStepParamsN p.1)) :=
    PrimrecPred.decide
      (Primrec.eq.comp
        (Primrec.list_length.comp Primrec.snd)
        (t1RunStepParams_n_primrec.comp hparams))
  exact (Primrec.cond hguard
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
    (Primrec.const [])).of_eq (fun p => by
      simp only [t1RunStepDValidPoints]
      split <;> simp_all)

private theorem t1RunStepDHitCount_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepDHitCount p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  have hs : Primrec (fun p :
      T1RunStepParams × BitString =>
      t1RunStepParamsState p.1) :=
    t1RunStepParams_state_primrec.comp hparams
  have hguard : Primrec (fun p :
      T1RunStepParams × BitString =>
      decide (p.2 ∈ (t1RunStepParamsState p.1).current)) :=
    PrimrecPred.decide
      (mem_bitstring_primrec.comp
        (Primrec.snd.pair
          (t1RunState_current_primrec.comp hs)))
  exact (Primrec.cond hguard (Primrec.const 1)
    (Primrec.const 0)).of_eq (fun p => by
      simp only [t1RunStepDHitCount]
      split <;> simp_all)

private theorem t1RunStepDCharged_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepDCharged p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  have hmarked : Primrec (fun p :
      T1RunStepParams × BitString =>
      t1RunAppendD
        (t1RunStepParamsState p.1, t1RunStepDValidPoints p)) :=
    t1RunAppendD_primrec.comp
      ((t1RunStepParams_state_primrec.comp hparams).pair
        t1RunStepDValidPoints_primrec)
  exact (t1RunChargeD_primrec.comp
    (hmarked.pair t1RunStepDHitCount_primrec)).of_eq
      (fun p => by rfl)

private theorem t1RunStepDRebuilt_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepDRebuilt p) := by
  let Q := T1RunStepParams × BitString
  have hparams : Primrec (fun p : Q => p.1) := Primrec.fst
  have hinput : Computable (fun p : Q =>
      ((t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
        t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
        t1RunStepDCharged p) :
        Nat × Nat × Nat × Nat × T1RunState)) :=
    (t1RunStepParams_cSparse_primrec.comp hparams).to_comp.pair
      ((t1RunStepParams_n_primrec.comp hparams).to_comp.pair
        ((t1RunStepParams_k_primrec.comp hparams).to_comp.pair
          ((t1RunStepParams_epsilon_primrec.comp hparams).to_comp.pair
            t1RunStepDCharged_primrec.to_comp)))
  exact t1RunRebuildTuple_computable.comp hinput

private theorem t1RunStepDSaturated_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepDSaturated p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunSaturationRebuildFinal_primrec.to_comp.comp
    ((t1RunStepParams_state_primrec.comp hparams).to_comp.pair
      t1RunStepDRebuilt_computable)).of_eq
        (fun p => by rfl)

private theorem t1RunStepDSaturatedGuard_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepDSaturatedGuard p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunSaturated_primrec.comp
    (t1RunStepDCharged_primrec.pair
      (t1RunStepParams_quota_primrec.comp hparams))).of_eq
        (fun p => by rfl)

private theorem t1RunStepDStringFn_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepDStringFn p) := by
  exact (Computable.cond
    t1RunStepDSaturatedGuard_primrec.to_comp
    t1RunStepDSaturated_computable
    t1RunStepDCharged_primrec.to_comp).of_eq
      (fun p => by
        simp only [t1RunStepDStringFn]
        cases t1RunStepDSaturatedGuard p <;> rfl)

noncomputable def t1RunStep (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent) : T1RunState :=
  let params : T1RunStepParams :=
    (((cSparse, n), (k, epsilon)), (quota, s))
  match event with
  | .bSet w => t1RunStepBSetFn (params, w)
  | .cDoublePrimeBatch batch => t1RunStepCDoubleFn (params, batch)
  | .cPrimeModel w => t1RunStepCPrimeFn (params, w)
  | .dString x => t1RunStepDStringFn (params, x)

noncomputable def t1RunFromEvents (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (events : List T1MarkEvent) : T1RunState :=
  events.foldl (t1RunStep cSparse n k epsilon quota) s

noncomputable def t1RunAt (c : Nat.Partrec.Code)
    (cDesc cSparse n k epsilon quota t : Nat) : T1RunState :=
  t1RunFromEvents cSparse n k epsilon quota
    (t1InitialRunState n k epsilon)
    (t1MarkingEventStage c n k epsilon
      (epsilon + logSlack cDesc n) t)

structure T1RunStepInput where
  cSparse : Nat
  n : Nat
  k : Nat
  epsilon : Nat
  quota : Nat
  s : T1RunState
  event : T1MarkEvent

def T1RunStepInput.toProd (input : T1RunStepInput) :
    Nat × Nat × Nat × Nat × Nat × T1RunState × T1MarkEvent :=
  (input.cSparse, input.n, input.k, input.epsilon, input.quota, input.s, input.event)

def T1RunStepInput.ofProd
    (p : Nat × Nat × Nat × Nat × Nat × T1RunState × T1MarkEvent) :
    T1RunStepInput :=
  { cSparse := p.1
  , n := p.2.1
  , k := p.2.2.1
  , epsilon := p.2.2.2.1
  , quota := p.2.2.2.2.1
  , s := p.2.2.2.2.2.1
  , event := p.2.2.2.2.2.2 }

def t1RunStepInputEquiv :
    T1RunStepInput ≃
      Nat × Nat × Nat × Nat × Nat × T1RunState × T1MarkEvent where
  toFun := T1RunStepInput.toProd
  invFun := T1RunStepInput.ofProd
  left_inv i := by cases i; rfl
  right_inv p := by rcases p with ⟨p1, p2, p3, p4, p5, p6, p7⟩; rfl

private abbrev T1RunStepInputData :=
  T1RunStepParams × T1MarkEvent

private def T1RunStepInput.toData
    (input : T1RunStepInput) : T1RunStepInputData :=
  ((((input.cSparse, input.n), (input.k, input.epsilon)),
    (input.quota, input.s)), input.event)

private def T1RunStepInput.ofData
    (p : T1RunStepInputData) : T1RunStepInput :=
  { cSparse := t1RunStepParamsCSparse p.1
  , n := t1RunStepParamsN p.1
  , k := t1RunStepParamsK p.1
  , epsilon := t1RunStepParamsEpsilon p.1
  , quota := t1RunStepParamsQuota p.1
  , s := t1RunStepParamsState p.1
  , event := p.2 }

private def t1RunStepInputDataEquiv :
    T1RunStepInput ≃ T1RunStepInputData where
  toFun := T1RunStepInput.toData
  invFun := T1RunStepInput.ofData
  left_inv input := by cases input; rfl
  right_inv p := by
    rcases p with
      ⟨⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, s⟩⟩, event⟩
    rfl

instance : Primcodable T1RunStepInput :=
  Primcodable.ofEquiv _ t1RunStepInputDataEquiv

private theorem t1RunStepInput_toData_primrec :
    Primrec T1RunStepInput.toData :=
  Primrec.of_equiv

noncomputable def T1RunStepInput.run (input : T1RunStepInput) : T1RunState :=
  t1RunStep input.cSparse input.n input.k input.epsilon input.quota input.s input.event

private noncomputable def t1RunStepTailRep
    (p : T1RunStepParams × (BitString ⊕ BitString)) :
    T1RunState :=
  match p.2 with
  | .inl w => t1RunStepCPrimeFn (p.1, w)
  | .inr x => t1RunStepDStringFn (p.1, x)

private theorem t1RunStepTailRep_computable :
    Computable t1RunStepTailRep := by
  have hc : Computable₂ (fun
      (p : T1RunStepParams × (BitString ⊕ BitString))
      (w : BitString) => t1RunStepCPrimeFn (p.1, w)) :=
    t1RunStepCPrimeFn_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  have hd : Computable₂ (fun
      (p : T1RunStepParams × (BitString ⊕ BitString))
      (x : BitString) => t1RunStepDStringFn (p.1, x)) :=
    t1RunStepDStringFn_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  exact (Computable.sumCasesOn Computable.snd hc hd).of_eq
    (fun p => by
      rcases p with ⟨params, event⟩
      cases event <;> rfl)

private noncomputable def t1RunStepRestRep
    (p : T1RunStepParams ×
      (List BitString ⊕ (BitString ⊕ BitString))) :
    T1RunState :=
  match p.2 with
  | .inl batch => t1RunStepCDoubleFn (p.1, batch)
  | .inr tail => t1RunStepTailRep (p.1, tail)

private theorem t1RunStepRestRep_computable :
    Computable t1RunStepRestRep := by
  have hcd : Computable₂ (fun
      (p : T1RunStepParams ×
        (List BitString ⊕ (BitString ⊕ BitString)))
      (batch : List BitString) =>
        t1RunStepCDoubleFn (p.1, batch)) :=
    t1RunStepCDoubleFn_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  have htail : Computable₂ (fun
      (p : T1RunStepParams ×
        (List BitString ⊕ (BitString ⊕ BitString)))
      (tail : BitString ⊕ BitString) =>
        t1RunStepTailRep (p.1, tail)) :=
    t1RunStepTailRep_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  exact (Computable.sumCasesOn Computable.snd hcd htail).of_eq
    (fun p => by
      rcases p with ⟨params, event⟩
      cases event <;> rfl)

private noncomputable def t1RunStepRep
    (p : T1RunStepParams ×
      (BitString ⊕ List BitString ⊕ BitString ⊕ BitString)) :
    T1RunState :=
  match p.2 with
  | .inl w => t1RunStepBSetFn (p.1, w)
  | .inr rest => t1RunStepRestRep (p.1, rest)

private theorem t1RunStepRep_computable :
    Computable t1RunStepRep := by
  have hb : Computable₂ (fun
      (p : T1RunStepParams ×
        (BitString ⊕ List BitString ⊕ BitString ⊕ BitString))
      (w : BitString) => t1RunStepBSetFn (p.1, w)) :=
    t1RunStepBSetFn_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  have hrest : Computable₂ (fun
      (p : T1RunStepParams ×
        (BitString ⊕ List BitString ⊕ BitString ⊕ BitString))
      (rest : List BitString ⊕ BitString ⊕ BitString) =>
        t1RunStepRestRep (p.1, rest)) :=
    t1RunStepRestRep_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  exact (Computable.sumCasesOn Computable.snd hb hrest).of_eq
    (fun p => by
      rcases p with ⟨params, event⟩
      cases event <;> rfl)

theorem t1RunStep_computable_uniform :
    Computable T1RunStepInput.run := by
  have hevent : Primrec (fun p : T1RunStepInputData =>
      t1MarkEventEquiv p.2) :=
    Primrec.of_equiv.comp Primrec.snd
  have hrep : Computable (fun input : T1RunStepInput =>
      ((T1RunStepInput.toData input).1,
        t1MarkEventEquiv (T1RunStepInput.toData input).2)) :=
    ((Primrec.fst.comp t1RunStepInput_toData_primrec).to_comp.pair
      (hevent.comp t1RunStepInput_toData_primrec).to_comp)
  exact (t1RunStepRep_computable.comp hrep).of_eq
    (fun input => by
      cases input
      rename_i cSparse n k epsilon quota s event
      cases event <;> rfl)

private noncomputable def t1RunFromEventsNat
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (events : List T1MarkEvent) (i : Nat) : T1RunState :=
  Nat.rec s
    (fun j current =>
      t1RunStep cSparse n k epsilon quota current
        (events.getD j default))
    i

private abbrev T1RunFoldInput :=
  T1RunStepParams × (List T1MarkEvent × Nat)

private noncomputable def t1RunFromEventsNatInput
    (p : T1RunFoldInput) : T1RunState :=
  t1RunFromEventsNat
    (t1RunStepParamsCSparse p.1) (t1RunStepParamsN p.1)
    (t1RunStepParamsK p.1) (t1RunStepParamsEpsilon p.1)
    (t1RunStepParamsQuota p.1) (t1RunStepParamsState p.1)
    p.2.1 p.2.2

private theorem t1RunFromEventsNatInput_computable :
    Computable t1RunFromEventsNatInput := by
  have hparams : Primrec (fun p : T1RunFoldInput => p.1) :=
    Primrec.fst
  have hevents : Primrec (fun p : T1RunFoldInput => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : T1RunFoldInput => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hinitial : Primrec (fun p : T1RunFoldInput =>
      t1RunStepParamsState p.1) :=
    t1RunStepParams_state_primrec.comp hparams
  have hstep : Computable₂ (fun (p : T1RunFoldInput)
      (rec : Nat × T1RunState) =>
      t1RunStep
        (t1RunStepParamsCSparse p.1)
        (t1RunStepParamsN p.1)
        (t1RunStepParamsK p.1)
        (t1RunStepParamsEpsilon p.1)
        (t1RunStepParamsQuota p.1)
        rec.2 (p.2.1[rec.1]?.getD default)) := by
    let Q := T1RunFoldInput × (Nat × T1RunState)
    have hp : Primrec (fun q : Q => q.1) := Primrec.fst
    have hfixed : Primrec (fun q : Q => q.1.1) :=
      Primrec.fst.comp hp
    have hrec : Primrec (fun q : Q => q.2) := Primrec.snd
    have hevent : Primrec (fun q : Q =>
        q.1.2.1[q.2.1]?.getD default) :=
      (Primrec.list_getD default).comp
        ((Primrec.fst.comp (Primrec.snd.comp hp)))
        (Primrec.fst.comp hrec)
    have hnewParams : Primrec (fun q : Q =>
        ((((t1RunStepParamsCSparse q.1.1,
          t1RunStepParamsN q.1.1),
          (t1RunStepParamsK q.1.1,
            t1RunStepParamsEpsilon q.1.1)),
          (t1RunStepParamsQuota q.1.1, q.2.2)) :
          T1RunStepParams)) :=
      ((t1RunStepParams_cSparse_primrec.comp hfixed).pair
        (t1RunStepParams_n_primrec.comp hfixed)).pair
        ((t1RunStepParams_k_primrec.comp hfixed).pair
          (t1RunStepParams_epsilon_primrec.comp hfixed)) |>.pair
        ((t1RunStepParams_quota_primrec.comp hfixed).pair
          (Primrec.snd.comp hrec))
    have heventRep : Primrec (fun q : Q =>
        t1MarkEventEquiv (q.1.2.1[q.2.1]?.getD default)) :=
      Primrec.of_equiv.comp hevent
    exact (t1RunStepRep_computable.comp
      (hnewParams.to_comp.pair heventRep.to_comp)).of_eq
        (fun q => by
          rcases q with ⟨p, ⟨j, current⟩⟩
          rcases p with ⟨params, ⟨events, i⟩⟩
          generalize heventVal :
            events[j]?.getD default = event
          cases event <;>
            simp [t1RunStep, t1RunStepRep,
              t1RunStepRestRep, t1RunStepTailRep,
              t1MarkEventEquiv,
              t1RunStepParamsCSparse, t1RunStepParamsN,
              t1RunStepParamsK, t1RunStepParamsEpsilon,
              t1RunStepParamsQuota, heventVal])
  exact (Computable.nat_rec hi.to_comp hinitial.to_comp hstep).of_eq
    (fun p => by rfl)

private theorem t1RunFromEventsNat_eq_take
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (events : List T1MarkEvent) (i : Nat)
    (hi : i ≤ events.length) :
    t1RunFromEventsNat cSparse n k epsilon quota s events i =
      t1RunFromEvents cSparse n k epsilon quota s
        (events.take i) := by
  induction i with
  | zero =>
      simp [t1RunFromEventsNat, t1RunFromEvents]
  | succ i ih =>
      have hilt : i < events.length := hi
      have htake :
          events.take (i + 1) =
            events.take i ++ [events.getD i default] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hilt,
          List.getD_eq_getElem events default hilt]
        rfl
      change t1RunStep cSparse n k epsilon quota
          (t1RunFromEventsNat cSparse n k epsilon quota s events i)
          (events.getD i default) =
        t1RunFromEvents cSparse n k epsilon quota s
          (events.take (i + 1))
      rw [ih (Nat.le_of_succ_le hi), htake]
      simp [t1RunFromEvents, List.foldl_append]

private theorem t1RunFromEvents_computable :
    Computable (fun p : T1RunStepParams × List T1MarkEvent =>
      t1RunFromEvents
        (t1RunStepParamsCSparse p.1) (t1RunStepParamsN p.1)
        (t1RunStepParamsK p.1) (t1RunStepParamsEpsilon p.1)
        (t1RunStepParamsQuota p.1) (t1RunStepParamsState p.1)
        p.2) := by
  have hinput : Primrec (fun p :
      T1RunStepParams × List T1MarkEvent =>
      ((p.1, p.2, p.2.length) : T1RunFoldInput)) :=
    Primrec.fst.pair
      (Primrec.snd.pair
        (Primrec.list_length.comp Primrec.snd))
  exact (t1RunFromEventsNatInput_computable.comp
    hinput.to_comp).of_eq (fun p => by
      change
        t1RunFromEventsNat
          (t1RunStepParamsCSparse p.1) (t1RunStepParamsN p.1)
          (t1RunStepParamsK p.1) (t1RunStepParamsEpsilon p.1)
          (t1RunStepParamsQuota p.1) (t1RunStepParamsState p.1)
          p.2 p.2.length =
        t1RunFromEvents
          (t1RunStepParamsCSparse p.1) (t1RunStepParamsN p.1)
          (t1RunStepParamsK p.1) (t1RunStepParamsEpsilon p.1)
          (t1RunStepParamsQuota p.1) (t1RunStepParamsState p.1)
          p.2
      rw [t1RunFromEventsNat_eq_take]
      · simp
      · exact le_rfl)

structure T1RunInput where
  c : Nat.Partrec.Code
  cDesc : Nat
  cSparse : Nat
  n : Nat
  k : Nat
  epsilon : Nat
  quota : Nat
  t : Nat

def T1RunInput.toProd (input : T1RunInput) :
    Nat.Partrec.Code × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (input.c, input.cDesc, input.cSparse, input.n, input.k, input.epsilon, input.quota, input.t)

def T1RunInput.ofProd
    (p : Nat.Partrec.Code × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
    T1RunInput :=
  { c := p.1
  , cDesc := p.2.1
  , cSparse := p.2.2.1
  , n := p.2.2.2.1
  , k := p.2.2.2.2.1
  , epsilon := p.2.2.2.2.2.1
  , quota := p.2.2.2.2.2.2.1
  , t := p.2.2.2.2.2.2.2 }

def t1RunInputEquiv :
    T1RunInput ≃
      Nat.Partrec.Code × Nat × Nat × Nat × Nat × Nat × Nat × Nat where
  toFun := T1RunInput.toProd
  invFun := T1RunInput.ofProd
  left_inv i := by cases i; rfl
  right_inv p := by rcases p with ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩; rfl

private abbrev T1RunInputData :=
  ((Nat.Partrec.Code × Nat) × (Nat × Nat)) ×
    ((Nat × Nat) × (Nat × Nat))

private def T1RunInput.toData (input : T1RunInput) :
    T1RunInputData :=
  (((input.c, input.cDesc), (input.cSparse, input.n)),
    ((input.k, input.epsilon), (input.quota, input.t)))

private def T1RunInput.ofData (p : T1RunInputData) :
    T1RunInput :=
  { c := p.1.1.1
  , cDesc := p.1.1.2
  , cSparse := p.1.2.1
  , n := p.1.2.2
  , k := p.2.1.1
  , epsilon := p.2.1.2
  , quota := p.2.2.1
  , t := p.2.2.2 }

private def t1RunInputDataEquiv :
    T1RunInput ≃ T1RunInputData where
  toFun := T1RunInput.toData
  invFun := T1RunInput.ofData
  left_inv input := by cases input; rfl
  right_inv p := by
    rcases p with
      ⟨⟨⟨c, cDesc⟩, ⟨cSparse, n⟩⟩,
        ⟨⟨k, epsilon⟩, ⟨quota, t⟩⟩⟩
    rfl

instance : Primcodable T1RunInput :=
  Primcodable.ofEquiv _ t1RunInputDataEquiv

private theorem t1RunInput_toData_primrec :
    Primrec T1RunInput.toData := by
  have h : Primrec (fun input : T1RunInput =>
      t1RunInputDataEquiv input) :=
    Primrec.of_equiv
  exact h.of_eq (fun input => by rfl)

noncomputable def T1RunInput.run (input : T1RunInput) : T1RunState :=
  t1RunAt input.c input.cDesc input.cSparse input.n input.k
    input.epsilon input.quota input.t

theorem t1RunAt_computable_uniform :
    Computable T1RunInput.run := by
  have hdata : Primrec (fun input : T1RunInput =>
      T1RunInput.toData input) :=
    t1RunInput_toData_primrec
  have hc : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).1.1.1) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).comp hdata
  have hcDesc : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).1.1.2) :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).comp hdata
  have hcSparse : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).1.2.1) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).comp hdata
  have hn : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).1.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).comp hdata
  have hk : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).2.1.1) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).comp hdata
  have hepsilon : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).2.1.2) :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).comp hdata
  have hquota : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).2.2.1) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp hdata
  have ht : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).2.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp hdata
  have hinitial : Primrec (fun input : T1RunInput =>
      t1InitialRunState input.n input.k input.epsilon) :=
    (t1InitialRunState_primrec.comp (hn.pair (hk.pair hepsilon))).of_eq
      (fun input => by rfl)
  have hparams : Primrec (fun input : T1RunInput =>
      ((((input.cSparse, input.n), (input.k, input.epsilon)),
        (input.quota, t1InitialRunState input.n input.k input.epsilon)) :
        T1RunStepParams)) :=
    ((hcSparse.pair hn).pair (hk.pair hepsilon)).pair
      (hquota.pair hinitial)
  have hd : Primrec (fun input : T1RunInput =>
      input.epsilon + logSlack input.cDesc input.n) :=
    (Primrec.nat_add.comp hepsilon
      (Primrec₂.comp t1LogSlack_primrec hcDesc hn)).of_eq
        (fun input => by rfl)
  have heventInput : Primrec (fun input : T1RunInput =>
      ((input.c, input.n, input.k, input.epsilon,
        input.epsilon + logSlack input.cDesc input.n, input.t) :
        Nat.Partrec.Code × Nat × Nat × Nat × Nat × Nat)) :=
    hc.pair (hn.pair (hk.pair
      (hepsilon.pair (hd.pair ht))))
  have hevents : Primrec (fun input : T1RunInput =>
      t1MarkingEventStage input.c input.n input.k input.epsilon
        (input.epsilon + logSlack input.cDesc input.n) input.t) :=
    (t1MarkingEventStage_primrec.comp heventInput).of_eq
      (fun input => by rfl)
  exact (t1RunFromEvents_computable.comp
    (hparams.to_comp.pair hevents.to_comp)).of_eq
      (fun input => by
        cases input
        rfl)

theorem t1RunFromEvents_append
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (events : List T1MarkEvent) (event : T1MarkEvent) :
    t1RunFromEvents cSparse n k epsilon quota s (events ++ [event]) =
      t1RunStep cSparse n k epsilon quota
        (t1RunFromEvents cSparse n k epsilon quota s events) event := by
  simp [t1RunFromEvents, List.foldl_append]

theorem t1RunStep_versions (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent) :
    let s' := t1RunStep cSparse n k epsilon quota s event
    (s'.external + s'.saturation = s.external + s.saturation ∧
      s'.versions = s.versions) ∨
    (s'.external + s'.saturation = s.external + s.saturation + 1 ∧
      s'.versions = s.versions ++ [s'.current]) := by
  cases event with
  | bSet w =>
      simp [t1RunStep, t1RunStepBSetFn,
        t1RunExternalRebuildFinal, t1RunStepBSetRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepBSetPre, t1RunAppendB,
        t1RunStepParamsState]
      omega
  | cDoublePrimeBatch batch =>
      simp [t1RunStep, t1RunStepCDoubleFn,
        t1RunExternalRebuildFinal, t1RunStepCDoubleRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepCDoublePre, t1RunAppendCSeenDouble,
        t1RunStepParamsState]
      omega
  | cPrimeModel w =>
      simp only [t1RunStep, t1RunStepCPrimeFn,
        t1RunStepCPrimeActiveFn]
      split
      · split <;>
          simp_all [t1RunStepCPrimeSaturated,
            t1RunSaturationRebuildFinal, t1RunStepCPrimeRebuilt,
            t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
            t1RunStepCPrimeCharged, t1RunChargeC, t1RunAppendC,
            t1RunStepCPrimeSeen, t1RunAppendSeenCPrime,
            t1RunStepParamsState]
        all_goals omega
      · simp [t1RunStepCPrimeSeen, t1RunAppendSeenCPrime,
          t1RunStepParamsState]
  | dString x =>
      simp only [t1RunStep, t1RunStepDStringFn]
      split <;>
        simp_all [t1RunStepDSaturated,
          t1RunSaturationRebuildFinal, t1RunStepDRebuilt,
          t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
          t1RunStepDCharged, t1RunChargeD, t1RunAppendD,
          t1RunStepParamsState]
      all_goals omega

theorem t1RunStep_versions_prefix
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (event : T1MarkEvent) :
    s.versions <+:
      (t1RunStep cSparse n k epsilon quota s event).versions := by
  rcases t1RunStep_versions cSparse n k epsilon quota s event with h | h
  · rw [h.2]
  · rw [h.2]
    exact List.prefix_append _ _

theorem t1RunFromEvents_versions_prefix
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (events : List T1MarkEvent) :
    s.versions <+:
      (t1RunFromEvents cSparse n k epsilon quota s events).versions := by
  induction events generalizing s with
  | nil =>
      exact List.prefix_refl _
  | cons event events ih =>
      exact (t1RunStep_versions_prefix cSparse n k epsilon quota s event).trans
        (ih (t1RunStep cSparse n k epsilon quota s event))

theorem t1RunAt_versions_prefix (c : Nat.Partrec.Code) (cDesc cSparse n k epsilon quota : Nat)
    {t t' : Nat} (htt' : t ≤ t') :
    (t1RunAt c cDesc cSparse n k epsilon quota t).versions <+:
      (t1RunAt c cDesc cSparse n k epsilon quota t').versions := by
  have hEvents :=
    t1MarkingEventStage_mono c n k epsilon
      (epsilon + logSlack cDesc n) htt'
  obtain ⟨tail, htail⟩ := hEvents
  unfold t1RunAt
  rw [← htail]
  simpa only [t1RunFromEvents, List.foldl_append] using
    (t1RunFromEvents_versions_prefix cSparse n k epsilon quota
      (t1RunFromEvents cSparse n k epsilon quota
        (t1InitialRunState n k epsilon)
        (t1MarkingEventStage c n k epsilon
          (epsilon + logSlack cDesc n) t))
      tail)

/-! ### Exact transition equations for semantic proofs -/

/-- State immediately before the mandatory rebuild caused by a `B` event. -/
noncomputable def t1RunBSetPrepared
    (n : Nat) (s : T1RunState) (w : BitString) : T1RunState :=
  { s with
    bMarked := s.bMarked ++
      (canonicalPointListOfCode w).filter (fun x => x.length = n) }

/-- State immediately before the mandatory rebuild caused by a `C''` batch. -/
noncomputable def t1RunCDoublePrepared
    (n : Nat) (s : T1RunState) (batch : List BitString) : T1RunState :=
  let activated :=
    ((batch.filter fun w => w ∈ s.seenCPrime).flatMap
      canonicalPointListOfCode).filter (fun x => x.length = n)
  { s with
    cMarked := s.cMarked ++ activated
    seenCDouble := s.seenCDouble ++ batch }

/-- State obtained by recording a `C'` code without activating its points. -/
def t1RunCPrimeSeenPrepared
    (s : T1RunState) (w : BitString) : T1RunState :=
  { s with seenCPrime := s.seenCPrime ++ [w] }

/-- State obtained after an active `C'` event has marked and charged its
length-`n` points, but before the optional saturation rebuild. -/
noncomputable def t1RunCPrimePrepared
    (n : Nat) (s : T1RunState) (w : BitString) : T1RunState :=
  let points :=
    (canonicalPointListOfCode w).filter (fun x => x.length = n)
  { t1RunCPrimeSeenPrepared s w with
    cMarked := s.cMarked ++ points
    totalC := s.totalC +
      (s.current.filter fun x => x ∈ points).length }

/-- State after a `D` string has been marked and charged, but before the
optional saturation rebuild. -/
noncomputable def t1RunDPrepared
    (n : Nat) (s : T1RunState) (x : BitString) : T1RunState :=
  { s with
    dMarked := s.dMarked ++ (if x.length = n then [x] else [])
    totalD := s.totalD + (if x ∈ s.current then 1 else 0) }

/-- Equality of the five fields that carry exact marking-event history. -/
def T1RunMarkingDataEq (s s' : T1RunState) : Prop :=
  s.bMarked = s'.bMarked ∧
  s.cMarked = s'.cMarked ∧
  s.dMarked = s'.dMarked ∧
  s.seenCPrime = s'.seenCPrime ∧
  s.seenCDouble = s'.seenCDouble

theorem T1RunMarkingDataEq.refl (s : T1RunState) :
    T1RunMarkingDataEq s s := by
  simp [T1RunMarkingDataEq]

theorem T1RunMarkingDataEq.symm {s s' : T1RunState}
    (h : T1RunMarkingDataEq s s') :
    T1RunMarkingDataEq s' s := by
  rcases h with ⟨hb, hc, hd, hcp, hcd⟩
  exact ⟨hb.symm, hc.symm, hd.symm, hcp.symm, hcd.symm⟩

theorem T1RunMarkingDataEq.trans {s s' s'' : T1RunState}
    (h₁ : T1RunMarkingDataEq s s')
    (h₂ : T1RunMarkingDataEq s' s'') :
    T1RunMarkingDataEq s s'' := by
  rcases h₁ with ⟨hb₁, hc₁, hd₁, hcp₁, hcd₁⟩
  rcases h₂ with ⟨hb₂, hc₂, hd₂, hcp₂, hcd₂⟩
  exact ⟨hb₁.trans hb₂, hc₁.trans hc₂, hd₁.trans hd₂,
    hcp₁.trans hcp₂, hcd₁.trans hcd₂⟩

/-- Rebuilding changes only the current model and version list. -/
theorem t1RunRebuild_markingDataEq
    (cSparse n k epsilon : Nat) (s : T1RunState) :
    T1RunMarkingDataEq s
      (t1RunRebuild cSparse n k epsilon s) := by
  simp [T1RunMarkingDataEq, t1RunRebuild,
    t1RunReplaceCurrent]

/-- A rebuild changes neither rebuild counters nor realized charge counters;
the caller increments exactly one rebuild counter when appropriate. -/
theorem t1RunRebuild_counters
    (cSparse n k epsilon : Nat) (s : T1RunState) :
    (t1RunRebuild cSparse n k epsilon s).external = s.external ∧
      (t1RunRebuild cSparse n k epsilon s).saturation = s.saturation ∧
      (t1RunRebuild cSparse n k epsilon s).totalC = s.totalC ∧
      (t1RunRebuild cSparse n k epsilon s).totalD = s.totalD := by
  simp [t1RunRebuild, t1RunReplaceCurrent]

theorem t1RunStep_bSet_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    t1RunStep cSparse n k epsilon quota s (.bSet w) =
      { t1RunRebuild cSparse n k epsilon
          (t1RunBSetPrepared n s w) with
        external := s.external + 1 } := by
  simp only [t1RunStep, t1RunStepBSetFn,
    t1RunExternalRebuildFinal, t1RunStepBSetRebuilt,
    t1RunRebuildTuple, t1RunBSetPrepared,
    t1RunStepBSetPre, t1RunAppendB, t1RunValidPoints,
    t1RunStepParamsState, t1RunStepParamsN,
    t1RunStepParamsCSparse, t1RunStepParamsK,
    t1RunStepParamsEpsilon]
  repeat constructor

theorem t1RunStep_bSet_markingDataEq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    T1RunMarkingDataEq (t1RunBSetPrepared n s w)
      (t1RunStep cSparse n k epsilon quota s (.bSet w)) := by
  rw [t1RunStep_bSet_eq]
  simpa [T1RunMarkingDataEq] using
    t1RunRebuild_markingDataEq cSparse n k epsilon
      (t1RunBSetPrepared n s w)

theorem t1RunStep_cDouble_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (batch : List BitString) :
    t1RunStep cSparse n k epsilon quota s
        (.cDoublePrimeBatch batch) =
      { t1RunRebuild cSparse n k epsilon
          (t1RunCDoublePrepared n s batch) with
        external := s.external + 1 } := by
  simp only [t1RunStep, t1RunStepCDoubleFn,
    t1RunExternalRebuildFinal, t1RunStepCDoubleRebuilt,
    t1RunRebuildTuple, t1RunCDoublePrepared,
    t1RunStepCDoublePre, t1RunAppendCSeenDouble,
    t1RunBatchValidPoints, t1RunStepParamsState,
    t1RunStepParamsN, t1RunStepParamsCSparse,
    t1RunStepParamsK, t1RunStepParamsEpsilon]
  repeat constructor

theorem t1RunStep_cDouble_markingDataEq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (batch : List BitString) :
    T1RunMarkingDataEq (t1RunCDoublePrepared n s batch)
      (t1RunStep cSparse n k epsilon quota s
        (.cDoublePrimeBatch batch)) := by
  rw [t1RunStep_cDouble_eq]
  simpa [T1RunMarkingDataEq] using
    t1RunRebuild_markingDataEq cSparse n k epsilon
      (t1RunCDoublePrepared n s batch)

theorem t1RunStep_cPrime_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    t1RunStep cSparse n k epsilon quota s (.cPrimeModel w) =
      if w ∈ s.seenCDouble then
        let prepared := t1RunCPrimePrepared n s w
        if t1RunSaturated prepared quota then
          { t1RunRebuild cSparse n k epsilon prepared with
            saturation := s.saturation + 1 }
        else prepared
      else t1RunCPrimeSeenPrepared s w := by
  simp [t1RunStep, t1RunStepCPrimeFn,
    t1RunStepCPrimeActive, t1RunStepCPrimeActiveFn,
    t1RunStepCPrimeSaturatedGuard,
    t1RunStepCPrimeSaturated, t1RunSaturationRebuildFinal,
    t1RunStepCPrimeRebuilt, t1RunRebuildTuple,
    t1RunCPrimePrepared, t1RunStepCPrimeCharged,
    t1RunChargeC, t1RunAppendC, t1RunStepCPrimeSeen,
    t1RunAppendSeenCPrime, t1RunCPrimeSeenPrepared,
    t1RunStepCPrimePoints, t1RunValidPoints,
    t1RunHitCount, t1RunStepParamsState,
    t1RunStepParamsN, t1RunStepParamsCSparse,
    t1RunStepParamsK, t1RunStepParamsEpsilon,
    t1RunStepParamsQuota]
  rfl

theorem t1RunStep_cPrime_seen_markingDataEq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString)
    (hactive : w ∉ s.seenCDouble) :
    T1RunMarkingDataEq (t1RunCPrimeSeenPrepared s w)
      (t1RunStep cSparse n k epsilon quota s
        (.cPrimeModel w)) := by
  rw [t1RunStep_cPrime_eq]
  simp [hactive, T1RunMarkingDataEq]

theorem t1RunStep_cPrime_active_markingDataEq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString)
    (hactive : w ∈ s.seenCDouble) :
    T1RunMarkingDataEq (t1RunCPrimePrepared n s w)
      (t1RunStep cSparse n k epsilon quota s
        (.cPrimeModel w)) := by
  rw [t1RunStep_cPrime_eq]
  simp only [hactive, if_true]
  split
  · simpa [T1RunMarkingDataEq] using
      t1RunRebuild_markingDataEq cSparse n k epsilon
        (t1RunCPrimePrepared n s w)
  · exact T1RunMarkingDataEq.refl _

theorem t1RunStep_dString_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (x : BitString) :
    t1RunStep cSparse n k epsilon quota s (.dString x) =
      let prepared := t1RunDPrepared n s x
      if t1RunSaturated prepared quota then
        { t1RunRebuild cSparse n k epsilon prepared with
          saturation := s.saturation + 1 }
      else prepared := by
  simp [t1RunStep, t1RunStepDStringFn,
    t1RunStepDSaturatedGuard, t1RunStepDSaturated,
    t1RunSaturationRebuildFinal, t1RunStepDRebuilt,
    t1RunRebuildTuple, t1RunDPrepared,
    t1RunStepDCharged, t1RunChargeD, t1RunAppendD,
    t1RunStepDValidPoints, t1RunStepDHitCount,
    t1RunStepParamsState, t1RunStepParamsN,
    t1RunStepParamsCSparse, t1RunStepParamsK,
    t1RunStepParamsEpsilon, t1RunStepParamsQuota]
  rfl

theorem t1RunStep_dString_markingDataEq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (x : BitString) :
    T1RunMarkingDataEq (t1RunDPrepared n s x)
      (t1RunStep cSparse n k epsilon quota s
        (.dString x)) := by
  rw [t1RunStep_dString_eq]
  by_cases hsat :
      t1RunSaturated (t1RunDPrepared n s x) quota = true
  · simp only [hsat, if_true]
    simpa [T1RunMarkingDataEq] using
      t1RunRebuild_markingDataEq cSparse n k epsilon
        (t1RunDPrepared n s x)
  · simp only [Bool.not_eq_true] at hsat
    simp [hsat, T1RunMarkingDataEq]

theorem t1InitialCurrent_nodup (n k epsilon : Nat) :
    (t1InitialCurrent n k epsilon).Nodup := by
  unfold t1InitialCurrent
  exact (List.take_sublist _ _).nodup (canonicalFinsetList_nodup _)

theorem t1InitialCurrent_subset_stringsOfLength (n k epsilon : Nat) :
    (t1InitialCurrent n k epsilon).toFinset ⊆
      stringsOfLength n := by
  intro x hx
  rw [List.mem_toFinset] at hx
  exact mem_canonicalFinsetList.mp
    ((List.mem_of_mem_take hx))

theorem t1InitialCurrent_length {n k epsilon : Nat}
    (hεk : epsilon ≤ k) (hkn : k ≤ n) :
    (t1InitialCurrent n k epsilon).length =
      2 ^ (k - epsilon) := by
  unfold t1InitialCurrent
  rw [List.length_take]
  have h_len : (canonicalFinsetList (stringsOfLength n)).length = 2 ^ n := by
    rw [length_canonicalFinsetList, cardStringsOfLength]
  rw [h_len]
  exact Nat.min_eq_left (Nat.pow_le_pow_right (by decide) (by omega))

theorem t1RunMarked_toFinset (s : T1RunState) :
    (t1RunMarked s).toFinset =
      s.bMarked.toFinset ∪ s.cMarked.toFinset ∪
        s.dMarked.toFinset := by
  ext x
  simp [t1RunMarked]

theorem t1RunUnmarked_nodup (n : Nat) (s : T1RunState) :
    (t1RunUnmarked n s).Nodup := by
  exact (List.filter_sublist).nodup
    (canonicalFinsetList_nodup (stringsOfLength n))

theorem t1RunUnmarked_toFinset (n : Nat) (s : T1RunState) :
    (t1RunUnmarked n s).toFinset =
      stringsOfLength n \ (t1RunMarked s).toFinset := by
  ext x
  simp [t1RunUnmarked]

theorem t1RunUnmarked_eq_canonicalFinsetList
    (n : Nat) (s : T1RunState) :
    t1RunUnmarked n s =
      canonicalFinsetList
        (stringsOfLength n \ (t1RunMarked s).toFinset) := by
  rw [← t1RunUnmarked_toFinset]
  exact (canonicalFinsetList_of_sorted
    (t1RunUnmarked n s) (t1RunUnmarked_nodup n s)
    ((Finset.pairwise_sort (stringsOfLength n) bitStringLE).sublist
      List.filter_sublist)).symm

theorem t1RunRebuild_current_spec
    (cSparse n k epsilon : Nat) (s : T1RunState) :
    (t1RunRebuild cSparse n k epsilon s).current.Nodup ∧
      (t1RunRebuild cSparse n k epsilon s).current.toFinset ⊆
        stringsOfLength n \ (t1RunMarked s).toFinset := by
  have hsub :
      List.Sublist
        (t1RunRebuild cSparse n k epsilon s).current
        (t1RunUnmarked n s) := by
    exact t1SparseSubsetSelectorList_sublist
      (t1RunUnmarked n s)
      (s.seenCDouble.map canonicalPointListOfCode)
      (2 ^ (k - epsilon)) (cSparse * n + cSparse)
  constructor
  · exact hsub.nodup (t1RunUnmarked_nodup n s)
  · have hfinset :
        (t1RunRebuild cSparse n k epsilon s).current.toFinset ⊆
          (t1RunUnmarked n s).toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      exact hsub.subset hx
    rwa [t1RunUnmarked_toFinset] at hfinset

theorem t1RunRebuild_model_spec (V : Map) (c : Nat.Partrec.Code) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon t
      (s : T1RunState),
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      (∀ x ∈ (t1RunMarked s).toFinset,
        T1BMarked V n epsilon x ∨
          (∃ d, T1CMarked V n k d x) ∨
          T1DMarked V n k x) →
      s.seenCDouble.toFinset ⊆
        (t1CDoublePrimeBatches c n k
          (epsilon + logSlack cDesc n) t).flatten.toFinset →
      let s' := t1RunRebuild cSparse n k epsilon s
      s'.current.Nodup ∧
        s'.current.toFinset ⊆ (t1RunUnmarked n s).toFinset ∧
        s'.current.length = 2 ^ (k - epsilon) ∧
        ∀ code ∈ s.seenCDouble,
          (s'.current.toFinset ∩
            (canonicalPointListOfCode code).toFinset).card ≤
              cSparse * n + cSparse := by
  intro cDesc
  obtain ⟨c0, cSparse, hselector⟩ :=
    t1_rebuild_selector_spec V c cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon t s hc0 hεk hkn hmarked hseen
  have hspec :=
    hselector n k epsilon t (t1RunMarked s).toFinset
      s.seenCDouble hc0 hεk hkn hmarked hseen
  rw [← t1RunUnmarked_eq_canonicalFinsetList] at hspec
  simp only [t1RunRebuild, t1RunReplaceCurrent, t1RunNextCurrent]
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1,
    fun code hcode => hspec.2.2.2 _ (List.mem_map_of_mem hcode)⟩

theorem t1RunSaturated_iff
    (s : T1RunState) (quota : Nat) (hcurrent : s.current.Nodup) :
    t1RunSaturated s quota = true ↔
      quota ≤
        (s.current.toFinset ∩
          (s.cMarked.toFinset ∪ s.dMarked.toFinset)).card := by
  let hits := s.current.filter
    (fun x => decide (x ∈ s.cMarked) || decide (x ∈ s.dMarked))
  have hhits : hits.Nodup := hcurrent.filter _
  have hcard :
      hits.length =
        (s.current.toFinset ∩
          (s.cMarked.toFinset ∪ s.dMarked.toFinset)).card := by
    calc
      hits.length = hits.toFinset.card :=
        (List.toFinset_card_of_nodup hhits).symm
      _ = (s.current.toFinset ∩
          (s.cMarked.toFinset ∪ s.dMarked.toFinset)).card := by
        congr! 1
        ext x
        simp [hits]
  simp [t1RunSaturated, hits, hcard]

theorem t1RunStep_bSet_history
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s (.bSet w)
    s'.bMarked =
        s.bMarked ++
          (canonicalPointListOfCode w).filter
            (fun x => x.length = n) ∧
      s'.external = s.external + 1 := by
  simp [t1RunStep, t1RunStepBSetFn, t1RunExternalRebuildFinal,
    t1RunStepBSetRebuilt, t1RunRebuildTuple, t1RunRebuild,
    t1RunReplaceCurrent, t1RunStepBSetPre, t1RunAppendB,
    t1RunValidPoints, t1RunStepParamsState, t1RunStepParamsN]
  rfl

theorem t1RunStep_cDouble_history
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (batch : List BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s
      (.cDoublePrimeBatch batch)
    let activated :=
      ((batch.filter fun w => w ∈ s.seenCPrime).flatMap
        canonicalPointListOfCode).filter (fun x => x.length = n)
    s'.cMarked = s.cMarked ++ activated ∧
      s'.seenCDouble = s.seenCDouble ++ batch ∧
      s'.external = s.external + 1 ∧
      s'.totalC = s.totalC := by
  simp [t1RunStep, t1RunStepCDoubleFn,
    t1RunExternalRebuildFinal, t1RunStepCDoubleRebuilt,
    t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
    t1RunStepCDoublePre, t1RunAppendCSeenDouble,
    t1RunBatchValidPoints, t1RunStepParamsState,
    t1RunStepParamsN]
  rfl

theorem t1RunStep_cPrime_history
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s
      (.cPrimeModel w)
    let points :=
      (canonicalPointListOfCode w).filter (fun x => x.length = n)
    s'.seenCPrime = s.seenCPrime ++ [w] ∧
      (w ∈ s.seenCDouble →
        s'.cMarked = s.cMarked ++ points ∧
        s'.totalC =
          s.totalC + (s.current.filter fun x => x ∈ points).length) ∧
      (w ∉ s.seenCDouble →
        s'.cMarked = s.cMarked ∧ s'.totalC = s.totalC) := by
  by_cases hactive : w ∈ s.seenCDouble
  · simp only [t1RunStep, t1RunStepCPrimeFn,
      t1RunStepCPrimeActive, t1RunStepParamsState, hactive,
      decide_true, if_true, t1RunStepCPrimeActiveFn]
    split
    · simp_all [t1RunStepCPrimeSaturated,
        t1RunSaturationRebuildFinal, t1RunStepCPrimeRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepCPrimeCharged, t1RunChargeC, t1RunHitCount,
        t1RunAppendC, t1RunStepCPrimeSeen,
        t1RunAppendSeenCPrime, t1RunStepCPrimePoints,
        t1RunValidPoints, t1RunStepParamsState,
        t1RunStepParamsN]
      rfl
    · simp_all [t1RunStepCPrimeCharged, t1RunChargeC, t1RunHitCount,
        t1RunAppendC, t1RunStepCPrimeSeen,
        t1RunAppendSeenCPrime, t1RunStepCPrimePoints,
        t1RunValidPoints, t1RunStepParamsState,
        t1RunStepParamsN]
      rfl
  · simp [t1RunStep, t1RunStepCPrimeFn,
      t1RunStepCPrimeActive, hactive, t1RunStepCPrimeSeen,
      t1RunAppendSeenCPrime, t1RunStepParamsState]


theorem t1RunStep_cPrime_seen
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    (t1RunStep cSparse n k epsilon quota s
      (.cPrimeModel w)).seenCPrime = s.seenCPrime ++ [w] := by
  exact (t1RunStep_cPrime_history
    cSparse n k epsilon quota s w).1

theorem t1RunStep_cDouble_seen
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (batch : List BitString) :
    (t1RunStep cSparse n k epsilon quota s
      (.cDoublePrimeBatch batch)).seenCDouble =
        s.seenCDouble ++ batch := by
  exact (t1RunStep_cDouble_history
    cSparse n k epsilon quota s batch).2.1

/-- A `C'` event changes only the `C` marks, `C'` history, charge, and
possibly the current model/version counters. -/
theorem t1RunStep_cPrime_unchanged_histories
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s
      (.cPrimeModel w)
    s'.bMarked = s.bMarked ∧
      s'.dMarked = s.dMarked ∧
      s'.seenCDouble = s.seenCDouble := by
  by_cases hactive : w ∈ s.seenCDouble
  · simp only [t1RunStep, t1RunStepCPrimeFn,
      t1RunStepCPrimeActive, t1RunStepParamsState, hactive,
      decide_true, if_true, t1RunStepCPrimeActiveFn]
    split <;>
      simp_all [t1RunStepCPrimeSaturated,
        t1RunSaturationRebuildFinal, t1RunStepCPrimeRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepCPrimeCharged, t1RunChargeC, t1RunAppendC,
        t1RunStepCPrimeSeen, t1RunAppendSeenCPrime,
        t1RunStepParamsState]
  · simp [t1RunStep, t1RunStepCPrimeFn,
      t1RunStepCPrimeActive, hactive, t1RunStepCPrimeSeen,
      t1RunAppendSeenCPrime, t1RunStepParamsState]

theorem t1RunStep_dString_history
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (x : BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s
      (.dString x)
    s'.dMarked =
        s.dMarked ++ (if x.length = n then [x] else []) ∧
      s'.totalD =
        s.totalD + (if x ∈ s.current then 1 else 0) := by
  simp only [t1RunStep, t1RunStepDStringFn]
  split <;>
    simp_all [t1RunStepDSaturated,
      t1RunSaturationRebuildFinal, t1RunStepDRebuilt,
      t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
      t1RunStepDCharged, t1RunChargeD, t1RunAppendD,
      t1RunStepDValidPoints, t1RunStepDHitCount,
      t1RunStepParamsState, t1RunStepParamsN]

/-- A `D` event changes only the `D` marks, `D` charge, and possibly the
current model/version counters. -/
theorem t1RunStep_dString_unchanged_histories
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s
      (.dString w)
    s'.bMarked = s.bMarked ∧
      s'.cMarked = s.cMarked ∧
      s'.seenCPrime = s.seenCPrime ∧
      s'.seenCDouble = s.seenCDouble := by
  simp only [t1RunStep, t1RunStepDStringFn]
  split <;>
    simp_all [t1RunStepDSaturated,
      t1RunSaturationRebuildFinal, t1RunStepDRebuilt,
      t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
      t1RunStepDCharged, t1RunChargeD, t1RunAppendD,
      t1RunStepParamsState]

theorem t1RunStep_current_eq_of_versions_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent)
    (hversions :
      (t1RunStep cSparse n k epsilon quota s event).versions =
        s.versions) :
    (t1RunStep cSparse n k epsilon quota s event).current =
      s.current := by
  cases event with
  | bSet w =>
      exfalso
      have hlength := congrArg List.length hversions
      simp [t1RunStep, t1RunStepBSetFn,
        t1RunExternalRebuildFinal, t1RunStepBSetRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepBSetPre, t1RunAppendB,
        t1RunStepParamsState] at hlength
  | cDoublePrimeBatch batch =>
      exfalso
      have hlength := congrArg List.length hversions
      simp [t1RunStep, t1RunStepCDoubleFn,
        t1RunExternalRebuildFinal, t1RunStepCDoubleRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepCDoublePre, t1RunAppendCSeenDouble,
        t1RunStepParamsState] at hlength
  | cPrimeModel w =>
      simp only [t1RunStep, t1RunStepCPrimeFn,
        t1RunStepCPrimeActiveFn] at hversions ⊢
      split
      · split
        · exfalso
          have hlength := congrArg List.length hversions
          simp_all [t1RunStepCPrimeSaturated,
            t1RunSaturationRebuildFinal,
            t1RunStepCPrimeRebuilt, t1RunRebuildTuple,
            t1RunRebuild, t1RunReplaceCurrent,
            t1RunStepCPrimeCharged, t1RunChargeC,
            t1RunAppendC, t1RunStepCPrimeSeen,
            t1RunAppendSeenCPrime, t1RunStepParamsState]
        · simp [t1RunStepCPrimeCharged, t1RunChargeC,
            t1RunAppendC, t1RunStepCPrimeSeen,
            t1RunAppendSeenCPrime, t1RunStepParamsState]
      · simp [t1RunStepCPrimeSeen,
          t1RunAppendSeenCPrime, t1RunStepParamsState]
  | dString x =>
      simp only [t1RunStep, t1RunStepDStringFn] at hversions ⊢
      split
      · exfalso
        have hlength := congrArg List.length hversions
        simp_all [t1RunStepDSaturated,
          t1RunSaturationRebuildFinal, t1RunStepDRebuilt,
          t1RunRebuildTuple, t1RunRebuild,
          t1RunReplaceCurrent, t1RunStepDCharged,
          t1RunChargeD, t1RunAppendD,
          t1RunStepParamsState]
      · simp [t1RunStepDCharged, t1RunChargeD,
          t1RunAppendD, t1RunStepParamsState]

theorem t1RunStep_preserves_versions_length
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent)
    (hversions :
      s.versions.length = s.external + s.saturation + 1) :
    let s' := t1RunStep cSparse n k epsilon quota s event
    s'.versions.length = s'.external + s'.saturation + 1 := by
  dsimp only
  rcases t1RunStep_versions cSparse n k epsilon quota s event with
    hsame | hrebuild
  · rw [hsame.2, hsame.1, hversions]
  · rw [hrebuild.2, List.length_append, hrebuild.1, hversions]
    simp

private theorem t1GetD_append_singleton_last
    (versions : List (List BitString)) (current : List BitString) :
    (versions ++ [current]).getD
        ((versions ++ [current]).length - 1) [] =
      current := by
  rw [List.getD_append_right]
  · simp
  · simp

theorem t1RunStep_preserves_versions_last
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent)
    (hlast :
      s.versions.getD (s.versions.length - 1) [] =
        s.current) :
    let s' := t1RunStep cSparse n k epsilon quota s event
    s'.versions.getD (s'.versions.length - 1) [] =
      s'.current := by
  dsimp only
  rcases t1RunStep_versions cSparse n k epsilon quota s event with
    hsame | hrebuild
  · have hcurrent :=
      t1RunStep_current_eq_of_versions_eq
        cSparse n k epsilon quota s event hsame.2
    rw [hsame.2, hcurrent]
    exact hlast
  · rw [hrebuild.2]
    exact t1GetD_append_singleton_last _ _

theorem t1RunFromEvents_preserves_versions_length
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (events : List T1MarkEvent)
    (hversions :
      s.versions.length = s.external + s.saturation + 1) :
    let s' :=
      t1RunFromEvents cSparse n k epsilon quota s events
    s'.versions.length = s'.external + s'.saturation + 1 := by
  induction events generalizing s with
  | nil =>
      simpa [t1RunFromEvents] using hversions
  | cons event events ih =>
      exact ih
        (t1RunStep cSparse n k epsilon quota s event)
        (t1RunStep_preserves_versions_length
          cSparse n k epsilon quota s event hversions)

theorem t1RunFromEvents_preserves_versions_last
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (events : List T1MarkEvent)
    (hlast :
      s.versions.getD (s.versions.length - 1) [] =
        s.current) :
    let s' :=
      t1RunFromEvents cSparse n k epsilon quota s events
    s'.versions.getD (s'.versions.length - 1) [] =
      s'.current := by
  induction events generalizing s with
  | nil =>
      simpa [t1RunFromEvents] using hlast
  | cons event events ih =>
      exact ih
        (t1RunStep cSparse n k epsilon quota s event)
        (t1RunStep_preserves_versions_last
          cSparse n k epsilon quota s event hlast)

theorem t1RunAt_versions_length
    (c : Nat.Partrec.Code)
    (cDesc cSparse n k epsilon quota t : Nat) :
    let s :=
      t1RunAt c cDesc cSparse n k epsilon quota t
    s.versions.length = s.external + s.saturation + 1 := by
  apply t1RunFromEvents_preserves_versions_length
  simp [t1InitialRunState]

theorem t1RunAt_versions_spec
    (c : Nat.Partrec.Code)
    (cDesc cSparse n k epsilon quota t : Nat) :
    let s :=
      t1RunAt c cDesc cSparse n k epsilon quota t
    s.versions.length = s.external + s.saturation + 1 ∧
      s.versions.getD (s.versions.length - 1) [] =
        s.current := by
  constructor
  · exact t1RunAt_versions_length
      c cDesc cSparse n k epsilon quota t
  · apply t1RunFromEvents_preserves_versions_last
    simp [t1InitialRunState]

end Kolmogorov
