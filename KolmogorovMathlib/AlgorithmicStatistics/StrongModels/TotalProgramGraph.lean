import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProgramList
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.Selector

namespace Kolmogorov

def TotalProgramGraphEntry (T : Map) (p : BitString) (e e' : CodedDistributionEntry) : Prop :=
  ∃ y, produces T p e.point y ∧
    e'.point = pairCode y e.point ∧
    e'.mass = e.mass

def totalProgramGraphData (T : Map)
    (input : BitString × List CodedDistributionEntry) :
    Part (List CodedDistributionEntry) :=
  (totalProgramMapList T (input.1, input.2.map CodedDistributionEntry.point)).map fun ys =>
    (ys.zip input.2).map fun (y, e) => { point := pairCode y e.point, mass := e.mass }

def totalProgramGraphCode (T : Map) : BitString × BitString →. BitString :=
  fun input =>
    (totalProgramGraphData T
      (input.1, CodedFiniteDistribution.decodeDistributionData input.2)).map
        codedDistributionDataCode

private theorem totalProgramGraphZip_rec_aux (n : Nat)
    (data : List CodedDistributionEntry) :
    ∀ ys : List BitString, ys.length ≤ n →
      ys.rec ([] : List (BitString × CodedDistributionEntry))
        (fun y rest ih =>
          ((data[n - (rest.length + 1)]?).map (fun e => (y, e) :: ih)).getD []) =
        ys.zip (data.drop (n - ys.length)) := by
  intro ys
  induction ys with
  | nil => intro _; simp
  | cons y rest ih =>
      intro hlen
      simp only [List.length_cons] at hlen
      have ih' := ih (by omega)
      simp only
      rw [ih']
      have hd : n - rest.length = (n - (rest.length + 1)) + 1 := by omega
      rcases hget : data[n - (rest.length + 1)]? with _ | e
      · have hdrop : data.drop (n - (rest.length + 1)) = [] := by
          rw [List.drop_eq_nil_iff]
          rw [List.getElem?_eq_none_iff] at hget
          omega
        rw [show n - (y :: rest).length = n - (rest.length + 1) by rfl, hdrop]
        rfl
      · obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hget
        have he : data.drop (n - (rest.length + 1)) =
            e :: data.drop (n - rest.length) := by
          rw [List.drop_eq_getElem_cons hlt, hval, ← hd]
        rw [show n - (y :: rest).length = n - (rest.length + 1) by rfl, he]
        rfl

private theorem totalProgramGraphZip_primrec :
    Primrec₂ (fun (ys : List BitString) (data : List CodedDistributionEntry) => ys.zip data) := by
  change Primrec (fun p : List BitString × List CodedDistributionEntry => p.1.zip p.2)
  have hstep : Primrec₂ (fun (input : List BitString × List CodedDistributionEntry)
      (state : BitString × List BitString × List (BitString × CodedDistributionEntry)) =>
        ((input.2[input.1.length - (state.2.1.length + 1)]?).map
          (fun e => (state.1, e) :: state.2.2)).getD []) := by
    change Primrec (fun q :
        (List BitString × List CodedDistributionEntry) ×
          (BitString × List BitString × List (BitString × CodedDistributionEntry)) =>
      ((q.1.2[q.1.1.length - (q.2.2.1.length + 1)]?).map
        (fun e => (q.2.1, e) :: q.2.2.2)).getD [])
    apply Primrec.option_getD.comp _ (Primrec.const [])
    apply Primrec.option_map _ _
    · exact Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.nat_sub.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.succ.comp
            (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))
    · exact Primrec.list_cons.comp
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  refine (Primrec.list_rec Primrec.fst (Primrec.const []) hstep).of_eq ?_
  intro p
  have h := totalProgramGraphZip_rec_aux p.1.length p.2 p.1 le_rfl
  simp only [Nat.sub_self, List.drop_zero] at h
  rw [← h]

private theorem totalProgramMapList_dom_of_forall₂
    {T : Map} {p : BitString} {xs ys : List BitString}
    (hrel : List.Forall₂ (fun x y => produces T p x y) xs ys) :
    (totalProgramMapList T (p, xs)).Dom := by
  have haux : ∀ r, r ≤ xs.length → (totalProgramMapListAux T p xs r).Dom := by
    intro r hr
    induction r with
    | zero => exact trivial
    | succ r ih =>
        rw [Part.dom_iff_mem] at ih ⊢
        obtain ⟨zs, hzs⟩ := ih (Nat.le_of_succ_le hr)
        have hrx : r < xs.length := hr
        have hry : r < ys.length := by rw [← hrel.length_eq]; exact hrx
        have hprod := hrel.get hrx hry
        have hget : xs.getD r [] = xs.get ⟨r, hrx⟩ :=
          List.getD_eq_getElem xs [] hrx
        refine ⟨zs ++ [ys.get ⟨r, hry⟩], ?_⟩
        rw [totalProgramMapListAux_succ, Part.mem_bind_iff]
        refine ⟨zs, hzs, (Part.mem_map_iff _).2 ⟨ys.get ⟨r, hry⟩, ?_, rfl⟩⟩
        rwa [hget]
  exact haux xs.length le_rfl

private theorem totalProgramMapList_mem_of_forall₂
    {T : Map} {p : BitString} {xs ys : List BitString}
    (hrel : List.Forall₂ (fun x y => produces T p x y) xs ys) :
    ys ∈ totalProgramMapList T (p, xs) := by
  obtain ⟨zs, hzs⟩ := Part.dom_iff_mem.mp (totalProgramMapList_dom_of_forall₂ hrel)
  have hzs_rel := totalProgramMapList_correct hzs
  have hunique : ∀ {as bs cs : List BitString},
      List.Forall₂ (fun x y => produces T p x y) as bs →
      List.Forall₂ (fun x y => produces T p x y) as cs → bs = cs := by
    intro as bs cs hbs
    induction hbs generalizing cs with
    | nil =>
        intro hcs
        exact (List.forall₂_nil_left_iff.mp hcs).symm
    | @cons x y as bs hxy htail ih =>
        intro hcs
        rw [List.forall₂_cons_left_iff] at hcs
        obtain ⟨z, cs', hxz, hcs', rfl⟩ := hcs
        exact congrArg₂ List.cons (Part.mem_unique hxy hxz) (ih hcs')
  have heq : ys = zs := hunique hrel hzs_rel
  rwa [heq]

theorem totalProgramGraphData_partrec (T : Map) (hT : isDecompressor T) :
    Partrec (totalProgramGraphData T) := by
  have hinput : Computable (fun input : BitString × List CodedDistributionEntry =>
      (input.1, input.2.map CodedDistributionEntry.point)) := by
    apply Primrec.to_comp
    exact Primrec.pair Primrec.fst
      (Primrec.list_map Primrec.snd
        (CodedFiniteDistribution.entry_point_primrec.comp Primrec.snd).to₂)
  have hentry : Primrec (fun q : BitString × CodedDistributionEntry =>
      ({ point := pairCode q.1 q.2.point, mass := q.2.mass } : CodedDistributionEntry)) := by
    have hpair : Primrec (fun q : BitString × CodedDistributionEntry =>
        (pairCode q.1 q.2.point, q.2.mass)) :=
      (CodedFiniteDistribution.pairCode_primrec.comp Primrec.fst
        (CodedFiniteDistribution.entry_point_primrec.comp Primrec.snd)).pair
        (CodedFiniteDistribution.entry_mass_primrec.comp Primrec.snd)
    exact (Primrec.of_equiv_symm
      (e := CodedFiniteDistribution.CodedDistributionEntry.equivProd)).comp hpair
  have hpost : Computable₂ (fun (input : BitString × List CodedDistributionEntry)
      (ys : List BitString) =>
        (ys.zip input.2).map fun q =>
          ({ point := pairCode q.1 q.2.point, mass := q.2.mass } : CodedDistributionEntry)) := by
    exact (Primrec.list_map
      (totalProgramGraphZip_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (hentry.comp Primrec.snd).to₂).to_comp.to₂
  exact Partrec.map ((totalProgramMapList_partrec T hT).comp hinput) hpost

/-- The canonical graph-code transformer is partial recursive for every
partial-recursive decompressor.  Its only partial step is the finite execution
of the supplied program on the decoded source entries. -/
theorem totalProgramGraphCode_partrec (T : Map) (hT : isDecompressor T) :
    Partrec (totalProgramGraphCode T) := by
  have hinput : Computable (fun input : BitString × BitString =>
      (input.1, CodedFiniteDistribution.decodeDistributionData input.2)) :=
    Computable.fst.pair
      (CodedFiniteDistribution.decodeDistributionData_primrec.to_comp.comp Computable.snd)
  have hcode : Computable₂ (fun (_ : BitString × BitString)
      (out : List CodedDistributionEntry) => codedDistributionDataCode out) :=
    (CodedFiniteDistribution.codedDistributionDataCode_primrec.comp Primrec.snd).to_comp.to₂
  exact Partrec.map ((totalProgramGraphData_partrec T hT).comp hinput) hcode

theorem totalProgramGraphData_spec (T : Map) (p : BitString)
    (data out : List CodedDistributionEntry) :
    out ∈ totalProgramGraphData T (p, data) ↔
      List.Forall₂ (TotalProgramGraphEntry T p) data out := by
  constructor
  · intro hout
    rw [totalProgramGraphData, Part.mem_map_iff] at hout
    obtain ⟨ys, hys, rfl⟩ := hout
    have hrel : List.Forall₂ (fun e y => produces T p e.point y) data ys :=
      List.forall₂_map_left_iff.mp (totalProgramMapList_correct hys)
    clear hys
    induction hrel with
    | nil => simp
    | @cons e y data ys hey htail ih =>
        simp only [List.zip_cons_cons, List.map_cons]
        exact List.Forall₂.cons ⟨y, hey, rfl, rfl⟩ ih
  · intro hrel
    have hex : ∃ ys : List BitString,
        List.Forall₂ (fun e y => produces T p e.point y) data ys ∧
          (ys.zip data).map (fun q =>
            ({ point := pairCode q.1 q.2.point, mass := q.2.mass } :
              CodedDistributionEntry)) = out := by
      induction hrel with
      | nil => exact ⟨[], List.Forall₂.nil, rfl⟩
      | @cons e e' data out hentry htail ih =>
          obtain ⟨y, hy, hpoint, hmass⟩ := hentry
          obtain ⟨ys, hys, hout⟩ := ih
          refine ⟨y :: ys, List.Forall₂.cons hy hys, ?_⟩
          simp only [List.zip_cons_cons, List.map_cons, hout, List.cons.injEq]
          cases e
          cases e'
          simp_all
    obtain ⟨ys, hys, hout⟩ := hex
    rw [totalProgramGraphData, Part.mem_map_iff]
    refine ⟨ys, totalProgramMapList_mem_of_forall₂
      (List.forall₂_map_left_iff.mpr hys), hout⟩

theorem totalProgramGraphData_dom_of_total (T : Map) (p : BitString)
    (hp : IsTotalProgram T p) (data : List CodedDistributionEntry) :
    (totalProgramGraphData T (p, data)).Dom := by
  unfold totalProgramGraphData
  rw [Part.dom_iff_mem]
  obtain ⟨ys, hys⟩ := Part.dom_iff_mem.mp
    (totalProgramMapList_dom_of_total hp (data.map CodedDistributionEntry.point))
  exact ⟨_, (Part.mem_map_iff _).2 ⟨ys, hys, rfl⟩⟩

theorem totalProgramGraphCode_eval (T : Map) (p : BitString)
    (P : CodedFiniteDistribution) (out : List CodedDistributionEntry)
    (h_out : out ∈ totalProgramGraphData T (p, P.data)) :
    codedDistributionDataCode out ∈ totalProgramGraphCode T (p, P.code) := by
  unfold totalProgramGraphCode CodedFiniteDistribution.code
  rw [CodedFiniteDistribution.decodeDistributionData_code]
  exact (Part.mem_map_iff _).2 ⟨out, h_out, rfl⟩

theorem totalProgramGraph_totalMassRat (T : Map) (p : BitString)
    (data out : List CodedDistributionEntry)
    (h_rel : List.Forall₂ (TotalProgramGraphEntry T p) data out) :
    totalMassRat out = totalMassRat data := by
  induction h_rel with
  | nil => rfl
  | @cons e e' data out hentry htail ih =>
      obtain ⟨y, hy, hpoint, hmass⟩ := hentry
      change e'.mass.add (totalMassRat out) = e.mass.add (totalMassRat data)
      rw [hmass, ih]

theorem totalProgramGraph_mass_pair (T : Map) (p : BitString)
    (data out : List CodedDistributionEntry)
    (h_rel : List.Forall₂ (TotalProgramGraphEntry T p) data out)
    (x y : BitString) (h_prod : produces T p x y) :
    CodedFiniteDistribution.mass ⟨out⟩ (pairCode y x) =
      CodedFiniteDistribution.mass ⟨data⟩ x := by
  unfold CodedFiniteDistribution.mass
  induction h_rel with
  | nil => rfl
  | @cons e e' data out hentry htail ih =>
      obtain ⟨z, hz, hpoint, hmass⟩ := hentry
      simp only [List.foldr_cons]
      by_cases hx : e.point = x
      · subst hx
        have hzy : z = y := Part.mem_unique hz h_prod
        simp [hpoint, hmass, hzy, ih]
      · have hne : e'.point ≠ pairCode y x := by
          rw [hpoint]
          intro heq
          have hsecond := congrArg decodeSecond heq
          simp only [decodeSecond_pairCode] at hsecond
          exact hx hsecond
        simp [hne, hx, ih]

theorem totalProgramGraph_isProbability (T : Map) (p : BitString)
    (P : CodedFiniteDistribution) (out : List CodedDistributionEntry)
    (h_rel : List.Forall₂ (TotalProgramGraphEntry T p) P.data out)
    (hP : P.IsProbability) :
    (CodedFiniteDistribution.mk out).IsProbability := by
  unfold CodedFiniteDistribution.IsProbability at hP ⊢
  rw [mass_total, totalProgramGraph_totalMassRat T p P.data out h_rel, ← mass_total]
  exact hP

def IsTotalProgramGraphModel (T : Map) (p : BitString) (P G : CodedFiniteDistribution) : Prop :=
  List.Forall₂ (TotalProgramGraphEntry T p) P.data G.data

/-- The semantic graph relation determines the canonical executable graph code.
This packages the reverse direction of `totalProgramGraphData_spec` together
with the code encoder, so later complexity arguments do not need to assume a
caller-supplied code-production witness. -/
theorem IsTotalProgramGraphModel.code_mem
    {T : Map} {p : BitString} {P G : CodedFiniteDistribution}
    (hG : IsTotalProgramGraphModel T p P G) :
    G.code ∈ totalProgramGraphCode T (p, P.code) := by
  apply totalProgramGraphCode_eval T p P G.data
  exact (totalProgramGraphData_spec T p P.data G.data).mpr hG

/-- A graph model has exactly the source mass at the injectively embedded
point `(output, source)`. -/
theorem IsTotalProgramGraphModel.mass_pair
    {T : Map} {p : BitString} {P G : CodedFiniteDistribution}
    (hG : IsTotalProgramGraphModel T p P G)
    {x y : BitString} (hprod : produces T p x y) :
    G.mass (pairCode y x) = P.mass x :=
  totalProgramGraph_mass_pair T p P.data G.data hG x y hprod

/-- Probability is preserved by a total-program graph model. -/
theorem IsTotalProgramGraphModel.isProbability
    {T : Map} {p : BitString} {P G : CodedFiniteDistribution}
    (hG : IsTotalProgramGraphModel T p P G)
    (hP : P.IsProbability) : G.IsProbability :=
  totalProgramGraph_isProbability T p P G.data hG hP

theorem exists_totalProgramGraphModel (T : Map) (p : BitString)
    (hp : IsTotalProgram T p) (P : CodedFiniteDistribution) :
    ∃ G, IsTotalProgramGraphModel T p P G ∧
      G.code ∈ totalProgramGraphCode T (p, P.code) := by
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.mp
    (totalProgramGraphData_dom_of_total T p hp P.data)
  refine ⟨⟨out⟩, (totalProgramGraphData_spec T p P.data out).mp hout, ?_⟩
  exact totalProgramGraphCode_eval T p P out hout

/-- Executable graph-model existence, packaged with probability preservation. -/
theorem exists_totalProgramGraphProbabilityModel (T : Map) (p : BitString)
    (hp : IsTotalProgram T p) (P : CodedFiniteDistribution)
    (hP : P.IsProbability) :
    ∃ G, IsTotalProgramGraphModel T p P G ∧ G.IsProbability ∧
      G.code ∈ totalProgramGraphCode T (p, P.code) := by
  obtain ⟨G, hG, hcode⟩ := exists_totalProgramGraphModel T p hp P
  exact ⟨G, hG, hG.isProbability hP, hcode⟩

end Kolmogorov
