import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Part01

/-!
# The run state is primitive recursive

Field-by-field effectiveness of `T1RunState`: reading off the current candidate list, the
three marked lists, the two seen lists, the version list, the two rebuild counters and the two
charges is primitive recursive (`t1RunState_current_primrec`, `…_bMarked_primrec`, …,
`t1RunState_totalD_primrec`), together with the corresponding update operations.

These are the obligations behind the computability of one run step, which is assembled in
`T1Run/Computable`; nothing here is used mathematically.
-/



namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

private theorem t1RunState_toProd_primrec :
    Primrec T1RunState.toProd := by
  exact Primrec.of_equiv

/-- Reading off the current sparse subset of a run state is primitive recursive. -/
theorem t1RunState_current_primrec :
    Primrec T1RunState.current :=
  Primrec.fst.comp t1RunState_toProd_primrec

/-- Reading off the list of B-marked points of a run state is primitive recursive. -/
theorem t1RunState_bMarked_primrec :
    Primrec T1RunState.bMarked :=
  (Primrec.fst.comp Primrec.snd).comp t1RunState_toProd_primrec

/-- Reading off the list of C-marked points of a run state is primitive recursive. -/
theorem t1RunState_cMarked_primrec :
    Primrec T1RunState.cMarked :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    t1RunState_toProd_primrec

/-- Reading off the list of D-marked points of a run state is primitive recursive. -/
theorem t1RunState_dMarked_primrec :
    Primrec T1RunState.dMarked :=
  (Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd))).comp t1RunState_toProd_primrec

/-- Reading off the list of codes seen once on the C′ stream of a run state is primitive
recursive. -/
theorem t1RunState_seenCPrime_primrec :
    Primrec T1RunState.seenCPrime :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd)))).comp t1RunState_toProd_primrec

/-- Reading off the list of codes seen twice of a run state is primitive recursive. -/
theorem t1RunState_seenCDouble_primrec :
    Primrec T1RunState.seenCDouble :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))).comp
      t1RunState_toProd_primrec

/-- Reading off the list of successive versions of the current subset of a run state is
primitive recursive. -/
theorem t1RunState_versions_primrec :
    Primrec T1RunState.versions :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)))))).comp t1RunState_toProd_primrec

/-- Reading off the counter of externally forced rebuilds of a run state is primitive recursive. -/
theorem t1RunState_external_primrec :
    Primrec T1RunState.external :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))))).comp t1RunState_toProd_primrec

/-- Reading off the counter of saturation rebuilds of a run state is primitive recursive. -/
theorem t1RunState_saturation_primrec :
    Primrec T1RunState.saturation :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))))).comp
        t1RunState_toProd_primrec

/-- Reading off the accumulated C-charge of a run state is primitive recursive. -/
theorem t1RunState_totalC_primrec :
    Primrec T1RunState.totalC :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.snd))))))))).comp
          t1RunState_toProd_primrec

/-- Reading off the accumulated D-charge of a run state is primitive recursive. -/
theorem t1RunState_totalD_primrec :
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

/-- Replace the current subset of a run state by a new one, appending it to the list of
versions. -/
def t1RunReplaceCurrent
    (p : T1RunState × List BitString) : T1RunState :=
  { p.1 with current := p.2, versions := p.1.versions ++ [p.2] }

/-- `logSlack` is primitive recursive in the constant and the argument jointly. -/
theorem t1LogSlack_primrec :
    Primrec₂ (fun c n : Nat => logSlack c n) := by
  unfold logSlack
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp Primrec.fst
      (Primrec.list_length.comp
        (primrec_natBits.comp Primrec.snd)))
    Primrec.fst

private theorem t1RunState_ofProd_primrec :
    Primrec T1RunState.ofProd := by
  exact Primrec.of_equiv_symm

/-- A run state built from primitive recursive components is itself a primitive recursive
function of the argument those components are computed from. -/
theorem t1RunState_mk_primrec
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

private def t1RunBitStringDecidableEq : DecidableEq BitString :=
  inferInstance

/-- The subset the run switches to at a rebuild: a sparse subset of the points that are still
unmarked and avoid the models of the codes already seen twice. -/
noncomputable def t1RunNextCurrent
    (p : Nat × Nat × Nat × Nat × T1RunState) : List BitString :=
  @t1SparseSubsetSelectorList BitString t1RunBitStringDecidableEq
    (t1RunUnmarked p.2.1 p.2.2.2.2)
    (p.2.2.2.2.seenCDouble.map canonicalPointListOfCode)
    (2 ^ (p.2.2.1 - p.2.2.2.1))
    (p.1 * p.2.1 + p.1)

/-- Rebuilding step of the T1 run: the current model is replaced by a fresh sparse subset of the
unmarked strings avoiding the models of the codes already seen twice. -/
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
    (t1CubeList_primrec.comp Primrec.fst)
    (primrec_two_pow_aux.comp
      (Primrec.nat_sub.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))

/-- The initial run state is a primitive recursive function of the parameters
`(cSparse, n, k)`. -/
theorem t1InitialRunState_primrec :
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

private theorem t1RunMarked_primrec :
    Primrec t1RunMarked := by
  exact eraseDups_bitstring_primrec.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        t1RunState_bMarked_primrec
        t1RunState_cMarked_primrec)
      t1RunState_dMarked_primrec)

/-- Testing a run state against its quota is primitive recursive. -/
theorem t1RunSaturated_primrec :
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
    (primrec_two_pow_aux.comp
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

/-- The rebuild step in uncurried form, on the tuple `(cSparse, n, k, epsilon, state)`. -/
noncomputable def t1RunRebuildTuple
    (p : Nat × Nat × Nat × Nat × T1RunState) : T1RunState :=
  t1RunRebuild p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-- The uncurried rebuild step is computable. -/
theorem t1RunRebuildTuple_computable :
    Computable t1RunRebuildTuple := by
  let P := Nat × Nat × Nat × Nat × T1RunState
  have hs : Computable (fun p : P => p.2.2.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))).to_comp
  simpa only [t1RunRebuildTuple, t1RunRebuild] using
    t1RunReplaceCurrent_primrec.to_comp.comp
      (hs.pair t1RunNextCurrent_computable)

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

/-- The rebuilding step is computable in its parameters and the run state. -/
theorem t1RunRebuild_computable :
    Computable (fun p : Nat × Nat × Nat × Nat × T1RunState =>
      t1RunRebuild p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2) := by
  simpa only [t1RunRebuildTuple] using
    t1RunRebuildTuple_computable

/-- The parameter bundle of one step of the effective run:
`((cSparse, n), (k, epsilon)), (quota, state)`. -/
abbrev T1RunStepParams :=
  ((Nat × Nat) × (Nat × Nat)) × (Nat × T1RunState)

/-- The sparseness constant of a step parameter bundle. -/
def t1RunStepParamsCSparse (p : T1RunStepParams) : Nat :=
  p.1.1.1

/-- The point length `n` of a step parameter bundle. -/
def t1RunStepParamsN (p : T1RunStepParams) : Nat :=
  p.1.1.2

/-- The level `k` of a step parameter bundle. -/
def t1RunStepParamsK (p : T1RunStepParams) : Nat :=
  p.1.2.1

/-- The precision parameter of a step parameter bundle. -/
def t1RunStepParamsEpsilon (p : T1RunStepParams) : Nat :=
  p.1.2.2

/-- The saturation quota of a step parameter bundle. -/
def t1RunStepParamsQuota (p : T1RunStepParams) : Nat :=
  p.2.1

/-- The run state carried by a step parameter bundle. -/
def t1RunStepParamsState (p : T1RunStepParams) : T1RunState :=
  p.2.2

/-- The sparseness constant is a primitive recursive component of the parameter bundle. -/
theorem t1RunStepParams_cSparse_primrec :
    Primrec t1RunStepParamsCSparse :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.fst)

/-- The point length is a primitive recursive component of the parameter bundle. -/
theorem t1RunStepParams_n_primrec :
    Primrec t1RunStepParamsN :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.fst)

/-- The level is a primitive recursive component of the parameter bundle. -/
theorem t1RunStepParams_k_primrec :
    Primrec t1RunStepParamsK :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.fst)

/-- The precision parameter is a primitive recursive component of the parameter bundle. -/
theorem t1RunStepParams_epsilon_primrec :
    Primrec t1RunStepParamsEpsilon :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.fst)

/-- The quota is a primitive recursive component of the parameter bundle. -/
theorem t1RunStepParams_quota_primrec :
    Primrec t1RunStepParamsQuota :=
  Primrec.fst.comp Primrec.snd

/-- The run state is a primitive recursive component of the parameter bundle. -/
theorem t1RunStepParams_state_primrec :
    Primrec t1RunStepParamsState :=
  Primrec.snd.comp Primrec.snd

/-- The points of the canonical point list of a code that have the length the run works at. -/
noncomputable def t1RunValidPoints (p : Nat × BitString) :
    List BitString :=
  (canonicalPointListOfCode p.2).filter
    (fun x => x.length = p.1)

/-- The valid points contributed by a batch of codes, counting only those codes that have
already been seen once. -/
noncomputable def t1RunBatchValidPoints
    (p : Nat × List BitString × List BitString) : List BitString :=
  let toActivate := p.2.2.filter (fun w => w ∈ p.2.1)
  (toActivate.flatMap canonicalPointListOfCode).filter
    (fun x => x.length = p.1)

/-- How many points of the first list belong to the second one. -/
def t1RunHitCount
    (p : List BitString × List BitString) : Nat :=
  (p.1.filter (fun x => x ∈ p.2)).length

/-- Mark a batch of points as B-marked. -/
def t1RunAppendB
    (p : T1RunState × List BitString) : T1RunState :=
  { p.1 with bMarked := p.1.bMarked ++ p.2 }

/-- The B-step before the rebuild: the valid points of the incoming code are B-marked. -/
noncomputable def t1RunStepBSetPre
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunAppendB
    (t1RunStepParamsState p.1,
      t1RunValidPoints (t1RunStepParamsN p.1, p.2))

/-- The B-step state after the current subset has been rebuilt. -/
noncomputable def t1RunStepBSetRebuilt
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunRebuildTuple
    (t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
      t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
      t1RunStepBSetPre p)

/-- Keep the rebuilt state but count one more externally forced rebuild. -/
def t1RunExternalRebuildFinal
    (p : T1RunState × T1RunState) : T1RunState :=
  { p.2 with external := p.1.external + 1 }

/-- One B-step of the effective run: mark the incoming points, rebuild the current subset and
count the rebuild as externally forced. -/
noncomputable def t1RunStepBSetFn
    (p : T1RunStepParams × BitString) : T1RunState :=
  let s := t1RunStepParamsState p.1
  let s'' := t1RunStepBSetRebuilt p
  t1RunExternalRebuildFinal (s, s'')

/-- Record newly C-marked points together with the codes that have now been seen twice. -/
def t1RunAppendCSeenDouble
    (p : T1RunState × (List BitString × List BitString)) :
    T1RunState :=
  { p.1 with
    cMarked := p.1.cMarked ++ p.2.1
    seenCDouble := p.1.seenCDouble ++ p.2.2 }

/-- The C″-step before the rebuild: the valid points of the codes seen a second time are
C-marked. -/
noncomputable def t1RunStepCDoublePre
    (p : T1RunStepParams × List BitString) : T1RunState :=
  let s := t1RunStepParamsState p.1
  let pts := t1RunBatchValidPoints
    (t1RunStepParamsN p.1, s.seenCPrime, p.2)
  t1RunAppendCSeenDouble (s, pts, p.2)

/-- The C″-step state after the current subset has been rebuilt. -/
noncomputable def t1RunStepCDoubleRebuilt
    (p : T1RunStepParams × List BitString) : T1RunState :=
  t1RunRebuildTuple
    (t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
      t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
      t1RunStepCDoublePre p)

/-- One C″-step of the effective run: mark, rebuild, and count the rebuild as externally
forced. -/
noncomputable def t1RunStepCDoubleFn
    (p : T1RunStepParams × List BitString) : T1RunState :=
  let s := t1RunStepParamsState p.1
  let s'' := t1RunStepCDoubleRebuilt p
  t1RunExternalRebuildFinal (s, s'')

/-- Record a code as seen once on the C′ stream. -/
def t1RunAppendSeenCPrime
    (p : T1RunState × BitString) : T1RunState :=
  { p.1 with seenCPrime := p.1.seenCPrime ++ [p.2] }

/-- Mark a batch of points as C-marked. -/
def t1RunAppendC
    (p : T1RunState × List BitString) : T1RunState :=
  { p.1 with cMarked := p.1.cMarked ++ p.2 }

/-- Add a number of hits to the accumulated C-charge. -/
def t1RunChargeC
    (p : T1RunState × Nat) : T1RunState :=
  { p.1 with totalC := p.1.totalC + p.2 }

/-- Keep the rebuilt state but count one more saturation rebuild. -/
def t1RunSaturationRebuildFinal
    (p : T1RunState × T1RunState) : T1RunState :=
  { p.2 with saturation := p.1.saturation + 1 }

/-- Counting a saturation rebuild is primitive recursive. -/
theorem t1RunSaturationRebuildFinal_primrec :
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

/-- The C′-step on a code that has not been seen before: the code is only recorded. -/
noncomputable def t1RunStepCPrimeSeen
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunAppendSeenCPrime (t1RunStepParamsState p.1, p.2)

/-- The valid points of the code arriving at a C′-step. -/
noncomputable def t1RunStepCPrimePoints
    (p : T1RunStepParams × BitString) : List BitString :=
  t1RunValidPoints (t1RunStepParamsN p.1, p.2)

/-- The C′-step on a code seen before: its valid points are C-marked and the points already
in the current subset are charged. -/
noncomputable def t1RunStepCPrimeCharged
    (p : T1RunStepParams × BitString) : T1RunState :=
  let s := t1RunStepParamsState p.1
  let pts := t1RunStepCPrimePoints p
  let marked := t1RunAppendC (t1RunStepCPrimeSeen p, pts)
  t1RunChargeC (marked, t1RunHitCount (s.current, pts))

/-- The charged C′-state after the current subset has been rebuilt. -/
noncomputable def t1RunStepCPrimeRebuilt
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunRebuildTuple
    (t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
      t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
      t1RunStepCPrimeCharged p)

/-- The rebuilt C′-state, with one saturation rebuild counted. -/
noncomputable def t1RunStepCPrimeSaturated
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunSaturationRebuildFinal
    (t1RunStepParamsState p.1, t1RunStepCPrimeRebuilt p)

end Kolmogorov
