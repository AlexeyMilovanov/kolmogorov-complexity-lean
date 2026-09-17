import KolmogorovMathlib.Restricted.Selection
import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.Restricted.EffectiveSelection.Part02
import KolmogorovMathlib.Restricted.EffectiveSelection
import KolmogorovMathlib.Restricted.Improving.RestrictedDescriptions

/-!
# Uniform computability of restricted marked selection

This module proves that the staged model-code enumeration, online selector and marked-code stream
are computable uniformly in their numerical parameters. Auxiliary argument and function
definitions expose the nested `Computable` compositions used by the uniform statements.

`familyMarkedCodeSelectorFn` decodes a marked input and returns the model at its duplicate-free
rank. Its partrec proof and rank specification turn the combinatorial marked stream into an
effective description method.

`familyMarkedInput_KPPlain_le_addr` and `selected_family_code_setComplexity_bound` control the
selector input and the selected model code for the final improving theorem.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- `isFamilyModelCodeBool` is primitive recursive jointly in the code `w` and
the parameter `j`. -/
theorem isFamilyModelCodeBool_primrec_uniform :
    Primrec (fun p : BitString × ℕ => isFamilyModelCodeBool p.2 p.1) := by
  unfold isFamilyModelCodeBool
  refine Primrec.and.comp ?_ ?_
  · exact isCanonicalUniformCodeBool_primrec.comp Primrec.fst
  · have h_card : Primrec (fun p : BitString × ℕ =>
        (canonicalFinsetList (((decodeDistributionData p.1).map
          CodedDistributionEntry.point).toFinset)).length) := by
      refine Primrec.list_length.comp
        (Kolmogorov.canonicalFinsetList_toFinset_primrec.comp ?_)
      exact (Primrec.list_map (decodeDistributionData_primrec.comp Primrec.fst)
        (entry_point_primrec.comp Primrec.snd))
    have h2 : Primrec (fun p : BitString × ℕ => 2 ^ p.2) := primrec_two_pow_aux.comp Primrec.snd
    convert Primrec.nat_le.comp h_card h2 using 1
    simp +decide [PrimrecPred]

/-- Uniform version of `blockSelection_primrec`: primitive recursive jointly in
`(n, i, j, k, s)` and the block `B`. -/
theorem blockSelection_primrec_uniform :
    Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString =>
      blockSelection q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 q.2) := by
  have hn : Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString => q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString => q.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString => q.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hB : Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString => q.2) := Primrec.snd
  have hm : Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString =>
      selectionThreshold q.1.2.1 q.1.2.2.2.1) :=
    Primrec₂.comp selectionThreshold_primrec hi hk
  have hpT : Primrec₂ (fun (q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString) (x : BitString) =>
      decide (selectionThreshold q.1.2.1 q.1.2.2.2.1 ≤
        (q.2.filter (fun b => decide (x ∈ canonicalFinsetList
          (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length)) :=
    (PrimrecPred.decide (Primrec.nat_le.comp (hm.comp Primrec.fst)
      (coverFilterCount_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
  have hT := list_filter_primrec (allStrings_primrec.comp hn) hpT
  have hTa := hT.comp (Primrec.fst (β := List BitString)
    (α := (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString))
  have hAllPred : Primrec₂ (fun (a : ((ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString) × List BitString)
      (x : BitString) =>
      decide (0 < (a.2.filter (fun b => decide (x ∈ canonicalFinsetList
        (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length)) :=
    (PrimrecPred.decide (Primrec.nat_lt.comp (Primrec.const 0)
      (coverFilterCount_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
  have hAll := list_all_primrec hTa hAllPred
  have hBound : Primrec (fun a : ((ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString) × List BitString =>
      decide (a.2.length ≤ a.1.2.length * (a.1.1.1 + 1) /
        selectionThreshold a.1.1.2.1 a.1.1.2.2.2.1)) :=
    PrimrecPred.decide (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.nat_div.comp
        (Primrec.nat_mul.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.nat_add.comp (hn.comp Primrec.fst) (Primrec.const 1)))
        (hm.comp Primrec.fst)))
  have hP := (Primrec.and.comp hAll hBound).to₂
  have hg := Primrec.option_getD.comp
    (list_find?_primrec (primrec_sublists_gen hB) hP) (Primrec.const [])
  apply hg.of_eq
  intro q
  unfold blockSelection
  rw [computableGreedyCover_eq]
  congr!

/-- Uniform version of `selectionStrategyOnline_primrec`: primitive recursive
jointly in `(n, i, j, k)` and the list `S`. -/
theorem selectionStrategyOnline_primrec_uniform :
    Primrec (fun q : (ℕ × ℕ × ℕ × ℕ) × List BitString =>
      selectionStrategyOnline q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) := by
  unfold selectionStrategyOnline
  refine Primrec.list_flatMap
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) ?_
  refine Primrec.list_flatMap ?_ ?_
  · refine list_filter_primrec
      (Primrec.list_range.comp (Primrec.nat_add.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const 2))) ?_
    exact (Primrec.beq.comp
      (Primrec.nat_mod.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
        (primrec_two_pow_aux.comp Primrec.snd)) (Primrec.const 0)).to₂
  · have hn : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hi : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have hj : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.1.1.2.2.1) :=
      Primrec.fst.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    have hk : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.1.1.2.2.2) :=
      Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    have hS : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hm : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.2) :=
      Primrec.snd.comp Primrec.fst
    have hs : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.2) := Primrec.snd
    have hwin : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ =>
        (r.1.1.2.take (r.1.2 + 1)).drop ((r.1.2 + 1) - 2 ^ r.2)) :=
      Primrec.list_drop.comp (Primrec.nat_sub.comp (Primrec.succ.comp hm)
        (primrec_two_pow_aux.comp hs)) (Primrec.list_take.comp (Primrec.succ.comp hm) hS)
    have htuple : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ =>
        ((r.1.1.1.1, r.1.1.1.2.1, r.1.1.1.2.2.1, r.1.1.1.2.2.2, r.2),
          (r.1.1.2.take (r.1.2 + 1)).drop ((r.1.2 + 1) - 2 ^ r.2))) :=
      Primrec.pair (Primrec.pair hn (Primrec.pair hi (Primrec.pair hj (Primrec.pair hk hs)))) hwin
    exact (blockSelection_primrec_uniform.comp htuple).to₂

/-- Uniform version of `familyCandidateModelCodesList_computable`: computable
jointly in `(i, j, t)`. -/
theorem familyCandidateModelCodesList_computable_uniform
    (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun q : ℕ × ℕ × ℕ =>
      familyCandidateModelCodesList c q.1 𝒜 q.2.1 q.2.2) := by
  unfold familyCandidateModelCodesList
  have hi : Primrec (fun r : (List BitString × (ℕ × ℕ × ℕ)) × BitString => r.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec (fun r : (List BitString × (ℕ × ℕ × ℕ)) × BitString => r.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hj : Primrec (fun r : (List BitString × (ℕ × ℕ × ℕ)) × BitString => r.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hw : Primrec (fun r : (List BitString × (ℕ × ℕ × ℕ)) × BitString => r.2) := Primrec.snd
  have h1 := (decide_mem_primrec (β := BitString)).comp
      ((snapshotCodes_primrec c).comp (Primrec.pair hi ht)) hw
  have h2 := isFamilyModelCodeBool_primrec_uniform.comp (Primrec.pair hw hj)
  have hb := Primrec.and.comp h1 h2
  have h_filter := list_filter_primrec
    (f := fun a : List BitString × (ℕ × ℕ × ℕ) => a.1) Primrec.fst hb.to₂
  have hcomp := h_filter.to_comp.comp
    (Computable.pair
      ((𝒜.enumeration.computable).comp (Computable.snd.comp Computable.snd))
      Computable.id)
  refine hcomp.of_eq (fun q => ?_)
  simp only [id_eq]
  apply List.filter_congr
  intro w _
  refine congrArg₂ (· && ·) ?_ rfl
  exact congrArg _ (Subsingleton.elim _ _)

section StageUniform
-- `familyCandidateModelCodesList` is a reducible `def`; unfolding it during the
-- `Computable.comp` unifications below is needlessly expensive, so keep it opaque.
attribute [local irreducible] familyCandidateModelCodesList

/-- The base-case argument of the stage recursion: the parameters with stage `0`. -/
def familyStageModelCodesListHgArg (q : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (q.1, q.2.1, 0)

/-- Forming the base-case argument of the stage recursion is computable. -/
theorem familyStageModelCodesList_hg_arg_comp : Computable familyStageModelCodesListHgArg :=
  Computable.pair Computable.fst
    (Computable.pair (Computable.fst.comp Computable.snd) (Computable.const 0))

/-- The base case of the stage recursion: the duplicate-free candidate codes at stage `0`. -/
def familyStageModelCodesListHgFun (c : Code) (𝒜 : PreDescriptionFamily) (q : ℕ × ℕ × ℕ) :
    List BitString :=
  (familyCandidateModelCodesList c q.1 𝒜 q.2.1 0).eraseDups

/-- The base case of the stage recursion is computable in the parameters. -/
theorem familyStageModelCodesList_hg (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (familyStageModelCodesListHgFun c 𝒜) := by
  have H := eraseDups_bitstring_primrec.to_comp.comp
    ((familyCandidateModelCodesList_computable_uniform c 𝒜).comp
      familyStageModelCodesList_hg_arg_comp)
  refine Computable.of_eq H ?_
  intro q
  rw [familyStageModelCodesListHgFun, familyStageModelCodesListHgArg]

/-- The argument passed to the candidate enumeration in the step of the stage recursion. -/
def familyStageModelCodesListHappArg (r : (ℕ × ℕ × ℕ) × (ℕ × List BitString)) : ℕ × ℕ × ℕ :=
  (r.1.1, r.1.2.1, r.2.1 + 1)

/-- Forming the step argument of the stage recursion is computable. -/
theorem familyStageModelCodesList_happ_arg_comp : Computable familyStageModelCodesListHappArg :=
  Computable.pair (Computable.fst.comp Computable.fst)
    (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.succ.comp (Computable.fst.comp Computable.snd)))

/-- The step of the stage recursion before duplicate removal: the list so far extended by the
candidate codes of the next stage. -/
def familyStageModelCodesListHappFun (c : Code) (𝒜 : PreDescriptionFamily)
    (r : (ℕ × ℕ × ℕ) × (ℕ × List BitString)) : List BitString :=
  r.2.2 ++ familyCandidateModelCodesList c r.1.1 𝒜 r.1.2.1 (r.2.1 + 1)

/-- The step of the stage recursion before duplicate removal is computable. -/
theorem familyStageModelCodesList_happ (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (familyStageModelCodesListHappFun c 𝒜) := by
  have H := (Primrec.list_append (α := BitString)).to_comp.comp
    (Computable.snd.comp Computable.snd)
    ((familyCandidateModelCodesList_computable_uniform c 𝒜).comp
      familyStageModelCodesList_happ_arg_comp)
  refine Computable.of_eq H ?_
  intro r
  rw [familyStageModelCodesListHappFun, familyStageModelCodesListHappArg]

/-- The step of the stage recursion: the list so far extended by the next stage's candidate
codes, with duplicates removed. -/
def familyStageModelCodesListHhFun (c : Code) (𝒜 : PreDescriptionFamily) (q : ℕ × ℕ × ℕ)
    (p : ℕ × List BitString) : List BitString :=
  (p.2 ++ familyCandidateModelCodesList c q.1 𝒜 q.2.1 (p.1 + 1)).eraseDups

/-- The step of the stage recursion is computable in the parameters and the state. -/
theorem familyStageModelCodesList_hh (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable₂ (familyStageModelCodesListHhFun c 𝒜) := by
  have H := eraseDups_bitstring_primrec.to_comp.comp (familyStageModelCodesList_happ c 𝒜)
  have H2 : Computable (fun (r : (ℕ × ℕ × ℕ) × (ℕ × List BitString)) =>
      familyStageModelCodesListHhFun c 𝒜 r.1 r.2) := by
    refine Computable.of_eq H ?_
    intro r
    rw [familyStageModelCodesListHhFun, familyStageModelCodesListHappFun]
  exact H2

-- Uniform version of `familyStageModelCodesList_computable`: computable jointly
-- in `(i, j, t)`.
/-- The stage-`t` list of model codes is computable jointly in the parameters and the stage. -/
theorem familyStageModelCodesList_computable_uniform
    (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun q : ℕ × ℕ × ℕ =>
      familyStageModelCodesList c q.1 𝒜 q.2.1 q.2.2) := by
  have hg := familyStageModelCodesList_hg c 𝒜
  have hh := familyStageModelCodesList_hh c 𝒜
  have hn : Computable (fun (q : ℕ × ℕ × ℕ) => q.2.2) := Computable.snd.comp Computable.snd
  have H := Computable.nat_rec hn hg hh
  refine Computable.of_eq H ?_
  intro q
  obtain ⟨i, j, t⟩ := q
  induction t with
  | zero => rfl
  | succ n ih =>
    change familyStageModelCodesListHhFun c 𝒜 (i, j, n)
        (n, Nat.rec (familyStageModelCodesListHgFun c 𝒜 (i, j, n))
          (fun y IH => familyStageModelCodesListHhFun c 𝒜 (i, j, n) (y, IH)) n) =
      familyStageModelCodesList c i 𝒜 j (n + 1)
    rw [ih, familyStageModelCodesListHhFun, familyStageModelCodesList]

end StageUniform

section MarkedStreamUniform
-- `selectionStrategyOnline` is a reducible `def`; keeping it irreducible prevents a
-- `whnf` blow-up when the final `of_eq` reconciles the composed function with
-- the unfolded `familyMarkedCodeStream`.
attribute [local irreducible] selectionStrategyOnline

/-- Uniform version of `familyMarkedCodeStream_computable`: computable jointly in
`(i, n, j, k, t)`. -/
theorem familyMarkedCodeStream_computable_uniform
    (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ =>
      familyMarkedCodeStream c q.1 𝒜 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hi : Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.1) := Computable.fst
  have hn : Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.1) := Computable.fst.comp Computable.snd
  have hjj : Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hkk : Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have htt : Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hstage := (familyStageModelCodesList_computable_uniform c 𝒜).comp
    (Computable.pair hi (Computable.pair hjj htt))
  have htuple := Computable.pair
    (Computable.pair hn (Computable.pair hi (Computable.pair hjj hkk))) hstage
  unfold familyMarkedCodeStream
  exact (selectionStrategyOnline_primrec_uniform.to_comp.comp htuple).of_eq (fun q => rfl)

end MarkedStreamUniform

/-- The selector: from a packed input `(n, i, j, k, r)` it waits for the marked stream to reach
length `r + 1` and returns the code at rank `r`. -/
noncomputable def familyMarkedCodeSelectorFn (c : Code) (𝒜 : PreDescriptionFamily) : BitString →.
    BitString :=
  fun s =>
    let n := selN s
    let i := selI s
    let j := selJ s
    let k := selK s
    let r := selR s
    (Nat.rfind (fun t => Part.some (decide (r < (familyMarkedCodeStream c i 𝒜 n j k
                                                  t).eraseDups.length)))).bind
      (fun t =>
        let stream := (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups
        Part.some (stream.getD r []))

section SelectorPartrec
attribute [local irreducible] familyMarkedCodeStream selN selI selJ selK selR

/-- The selector is partial computable. -/
theorem familyMarkedCodeSelectorFn_partrec (c : Code) (𝒜 : PreDescriptionFamily) : Partrec
    (familyMarkedCodeSelectorFn c 𝒜) := by
  have h_stream : Computable (fun st : BitString × ℕ =>
      (familyMarkedCodeStream c (selI st.1) 𝒜 (selN st.1) (selJ st.1) (selK st.1)
        st.2).eraseDups) :=
    eraseDups_bitstring_primrec.to_comp.comp
      ((familyMarkedCodeStream_computable_uniform c 𝒜).comp
        ((selI_computable.comp Computable.fst).pair
          ((selN_computable.comp Computable.fst).pair
            ((selJ_computable.comp Computable.fst).pair
              ((selK_computable.comp Computable.fst).pair Computable.snd)))))
  have h_lt : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
    obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel (α := ℕ) (· < ·))
    convert h.to_comp
  have h_check : Computable (fun st : BitString × ℕ =>
      decide (selR st.1 <
        (familyMarkedCodeStream c (selI st.1) 𝒜 (selN st.1) (selJ st.1) (selK st.1)
          st.2).eraseDups.length)) :=
    h_lt.comp ((selR_computable.comp Computable.fst).pair
      (Computable.list_length.comp h_stream))
  have h_post : Computable (fun st : BitString × ℕ =>
      (familyMarkedCodeStream c (selI st.1) 𝒜 (selN st.1) (selJ st.1) (selK st.1)
        st.2).eraseDups.getD (selR st.1) []) :=
    ((Primrec.list_getD ([] : BitString)).to_comp).comp h_stream
      (selR_computable.comp Computable.fst)
  exact (Partrec.bind (Partrec.rfind h_check.to₂.partrec₂) h_post.to₂.partrec₂).of_eq
    (fun s => rfl)

end SelectorPartrec

/-- If stage `t` is the first at which the marked stream has rank `r`, the selector returns the
entry of rank `r` in that stage. -/
theorem familyMarkedCodeSelectorFn_eq_of_rank (c : Code) (𝒜 : PreDescriptionFamily)
    (n i j k r t : ℕ)
    (h_lt : r < (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups.length)
    (h_first : ∀ t' < t, ¬(r < (familyMarkedCodeStream c i 𝒜 n j k t').eraseDups.length)) :
    familyMarkedCodeSelectorFn c 𝒜 (familyMarkedInput n i j k r) = Part.some
        ((familyMarkedCodeStream c i 𝒜 n j k t).eraseDups.getD r []) := by
  unfold familyMarkedCodeSelectorFn
  simp only [selN_familyMarkedInput, selI_familyMarkedInput, selJ_familyMarkedInput,
    selK_familyMarkedInput, selR_familyMarkedInput]
  rw [Part.eq_some_iff, Part.mem_bind_iff]
  refine ⟨t, ?_, ?_⟩
  · rw [@Nat.mem_rfind
      ((fun t : ℕ => Part.some
        (decide
          (r < (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups.length))) :
        ℕ →. Bool)
      t]
    constructor
    · simp [h_lt]
    · intro m hm
      simp [h_first m hm]
  · simp

/-- A packed input whose rank is below `2 ^ (m + 1)` has prefix complexity at most `m + 1` plus a
logarithmic slack in the remaining parameters. -/
theorem familyMarkedInput_KPPlain_le_addr (U : Map) (hU : IsOptimalPrefixConditional U)
    (c_partrec : ℕ) :
    ∃ c_slack : ℕ, ∀ (n i j k r m : ℕ), r < 2 ^ (m + 1) →
      KPPlain U (familyMarkedInput n i j k r) + (c_partrec : ENat) ≤ ((m : ENat) + 1) + logSlack
          c_slack (n + i + j + k + m) := by
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c_bits, hc_bits⟩ := logSlack_linear_bound 2 9 5
  refine ⟨(12 + c_len + c_partrec) + c_bits, fun n i j k r m hr => ?_⟩
  let M := n + i + j + k + m
  let W := (Nat.bits M).length
  let w := familyMarkedInput n i j k r
  have hnW : (Nat.bits n).length ≤ W := by exact length_natBits_mono (by omega : n ≤ M)
  have hiW : (Nat.bits i).length ≤ W := by exact length_natBits_mono (by omega : i ≤ M)
  have hjW : (Nat.bits j).length ≤ W := by exact length_natBits_mono (by omega : j ≤ M)
  have hkW : (Nat.bits k).length ≤ W := by exact length_natBits_mono (by omega : k ≤ M)
  have hrm : (Nat.bits r).length ≤ m + 1 := by
    exact length_natBits_lt_pow hr
  have hWle : W ≤ M := by
    simpa [W] using length_natBits_le M
  have hw_len : w.length ≤ (m + 1) + (8 * W + 4) := by
    simp [w, familyMarkedInput]
    omega
  have hw_linear : w.length ≤ 9 * M + 5 := by
    calc w.length ≤ (m + 1) + (8 * W + 4) := hw_len
      _ ≤ (m + 1) + (8 * M + 4) := by omega
      _ ≤ 9 * M + 5 := by omega
  have hbits : 2 * (Nat.bits w.length).length ≤ logSlack c_bits M := by
    have hmono : (Nat.bits w.length).length ≤ (Nat.bits (9 * M + 5)).length :=
      length_natBits_mono hw_linear
    have hraw : 2 * (Nat.bits w.length).length ≤ logSlack 2 (9 * M + 5) := by
      unfold logSlack
      omega
    exact hraw.trans (hc_bits M)
  have hdirect : 8 * W + 4 + c_len + c_partrec ≤ logSlack (12 + c_len + c_partrec) M := by
    unfold logSlack
    simp [W]
    nlinarith [Nat.zero_le (c_len * (Nat.bits M).length),
      Nat.zero_le (c_partrec * (Nat.bits M).length),
      Nat.zero_le (4 * (Nat.bits M).length)]
  have hslack : (8 * W + 4 + c_len + c_partrec) + 2 * (Nat.bits w.length).length ≤
      logSlack ((12 + c_len + c_partrec) + c_bits) M := by
    have hsum : (8 * W + 4 + c_len + c_partrec) + 2 * (Nat.bits w.length).length ≤
        logSlack (12 + c_len + c_partrec) M + logSlack c_bits M := by
      omega
    have hadd : logSlack (12 + c_len + c_partrec) M + logSlack c_bits M =
        logSlack ((12 + c_len + c_partrec) + c_bits) M := by
      rw [logSlack_add_const]
    exact hsum.trans (le_of_eq hadd)
  have hnat : w.length + 2 * (Nat.bits w.length).length + c_len + c_partrec ≤
      (m + 1) + logSlack ((12 + c_len + c_partrec) + c_bits) M := by
    have hlen' : w.length + 2 * (Nat.bits w.length).length + c_len + c_partrec ≤
        (m + 1) + ((8 * W + 4 + c_len + c_partrec) + 2 * (Nat.bits w.length).length) := by
      omega
    omega
  calc KPPlain U w + (c_partrec : ENat)
      ≤ (w.length + 2 * (Nat.bits w.length).length + (c_len : ENat)) + (c_partrec : ENat) := by
        exact add_le_add (hc_len w) le_rfl
    _ = ((w.length + 2 * (Nat.bits w.length).length + c_len + c_partrec : ℕ) : ENat) := by
        push_cast
        ring
    _ ≤ (((m + 1) + logSlack ((12 + c_len + c_partrec) + c_bits) M : ℕ) : ENat) := by
        exact_mod_cast hnat
    _ = ((m : ENat) + 1) + logSlack ((12 + c_len + c_partrec) + c_bits) M := by
        push_cast
        ring

/-- Hard coding leaf for selected marked-code streams.  A code selected by the
effective marked stream has set complexity bounded by its rank in that stream:
`exists_markedStream_rank` and `markedStream_rank_address_slack` supply the
rank-length arithmetic for the packed computable decoder of
`familyMarkedCodeStream`. -/
theorem selected_family_code_setComplexity_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) (_hc : IsCodeFor c U) (𝒜 : PreDescriptionFamily) :
    ∃ c_slack : ℕ, ∀ (n i j k t : ℕ) (w : BitString)
      (S : Finset BitString) (hS : S.Nonempty),
      k ≤ i →
      w ∈ familyMarkedCodeStream c i 𝒜 n j k t →
      w = (codedUniformOn S hS).code →
      setComplexity U S hS ≤ (i - k : ENat) + logSlack c_slack (n + i + j) := by
  obtain ⟨c_map, hc_map⟩ := KPPlain_partrec_map_le U hU (familyMarkedCodeSelectorFn c 𝒜)
    (familyMarkedCodeSelectorFn_partrec c 𝒜)
  obtain ⟨c_input, hc_input⟩ := familyMarkedInput_KPPlain_le_addr U hU c_map
  obtain ⟨c_fold, hc_fold⟩ := logSlack_linear_bound c_input 5 10
  refine ⟨c_fold + 20, fun n i j k t w S hS hk hw_stream hcode => ?_⟩
  obtain ⟨r, hr_stage, hget_t⟩ :=
    exists_rank_getD_eraseDups (familyMarkedCodeStream c i 𝒜 n j k t) hw_stream
  have hr_bound : r < (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) := by
    exact lt_of_lt_of_le hr_stage
      (le_trans (eraseDups_bitString_length_le _)
        (familyMarkedCodeStream_length_bound c i 𝒜 n j k t))
  let M := n + i + j
  let P := 2 * ((i + 2) * (i + 1) * (n + 1))
  let q := (Nat.bits P).length
  let m := i - k + q
  have hpowP : P < 2 ^ q := by
    simpa [P, q] using lt_two_pow_length_natBits P
  have hexp : i + 1 - k = i - k + 1 := by omega
  have hbound_eq :
      (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) =
        P * 2 ^ (i - k) := by
    simp [P, hexp, pow_succ]
    ring
  have hr_pow_m : r < 2 ^ (m + 1) := by
    have hlt : r < P * 2 ^ (i - k) := by
      simpa [hbound_eq] using hr_bound
    have hmul : P * 2 ^ (i - k) ≤ 2 ^ q * 2 ^ (i - k) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hpowP)
    have hpow : 2 ^ q * 2 ^ (i - k) = 2 ^ m := by
      rw [show m = q + (i - k) by omega, pow_add]
    exact lt_of_lt_of_le hlt (by
      calc P * 2 ^ (i - k) ≤ 2 ^ q * 2 ^ (i - k) := hmul
        _ = 2 ^ m := hpow
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ m))
  let h_exists : ∃ u, r < (familyMarkedCodeStream c i 𝒜 n j k u).eraseDups.length := ⟨t, hr_stage⟩
  let t0 := Nat.find h_exists
  have ht0_lt : r < (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups.length :=
    Nat.find_spec h_exists
  have ht0_le_t : t0 ≤ t :=
    Nat.find_le (p := fun u => r < (familyMarkedCodeStream c i 𝒜 n j k u).eraseDups.length) hr_stage
  have hfirst : ∀ t' < t0, ¬(r < (familyMarkedCodeStream c i 𝒜 n j k t').eraseDups.length) := by
    intro t' ht'
    exact Nat.find_min h_exists ht'
  have hpre : (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups <+:
      (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups :=
    familyMarkedCodeStream_eraseDups_prefix_of_le c i 𝒜 n j k ht0_le_t
  have hget_t0 : (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups.getD r [] = w := by
    have hget := StagedEnumeration.getD_eq_of_prefix
      (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups
      (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups hpre r [] ht0_lt
    rw [← hget_t]
    exact hget.symm
  have hsel_eq := familyMarkedCodeSelectorFn_eq_of_rank c 𝒜 n i j k r t0 ht0_lt hfirst
  rw [hget_t0] at hsel_eq
  have hw_sel : w ∈ familyMarkedCodeSelectorFn c 𝒜 (familyMarkedInput n i j k r) :=
    Part.eq_some_iff.mp hsel_eq
  have hcomp1 : KPPlain U w ≤ KPPlain U (familyMarkedInput n i j k r) + (c_map : ENat) :=
    hc_map (familyMarkedInput n i j k r) w hw_sel
  have hcomp2 : KPPlain U (familyMarkedInput n i j k r) + (c_map : ENat) ≤
      ((m : ENat) + 1) + logSlack c_input (n + i + j + k + m) :=
    hc_input n i j k r m hr_pow_m
  have hq : q ≤ 3 * (Nat.bits M).length + 10 := by
    simpa [M, P, q] using markedStream_poly_bits_bound n i j
  have hm_le : m + 1 ≤ (i - k) + (3 * (Nat.bits M).length + 11) := by
    simp [m]
    omega
  have hbudget : n + i + j + k + m ≤ 5 * M + 10 := by
    have hWle : (Nat.bits M).length ≤ M := length_natBits_le M
    simp [M, m]
    omega
  have hfold : logSlack c_input (n + i + j + k + m) ≤ logSlack c_fold M := by
    exact (logSlack_mono (c := c_input) hbudget).trans (hc_fold M)
  have hqslack : 3 * (Nat.bits M).length + 11 + logSlack c_fold M ≤
      logSlack (c_fold + 20) M := by
    unfold logSlack
    nlinarith [Nat.zero_le (17 * (Nat.bits M).length)]
  have htotal : ((m : ENat) + 1) + logSlack c_input (n + i + j + k + m) ≤
      (i - k : ENat) + logSlack (c_fold + 20) M := by
    have hnat : m + 1 + logSlack c_input (n + i + j + k + m) ≤
        (i - k) + logSlack (c_fold + 20) M := by
      have hnat1 : m + 1 + logSlack c_input (n + i + j + k + m) ≤
          (i - k) + (3 * (Nat.bits M).length + 11 + logSlack c_fold M) := by
        omega
      omega
    exact_mod_cast hnat
  unfold setComplexity
  rw [← hcode]
  exact (hcomp1.trans hcomp2).trans htotal

end Kolmogorov


