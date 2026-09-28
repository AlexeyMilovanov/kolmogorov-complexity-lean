import KolmogorovMathlib.StoppingComplexity.Allocator
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.Computability

/-!
# Limiting seed events of the allocator

Blueprint 03 Lemma A4 and the first paragraph of §5: the seed event `A_z^∞` of an input string `z`
is the union, over all stages, of the Cantor cylinders labelled by the atoms allocated to `z`
(`seedEvent`).  Its fair-coin measure is the limit mass `requestLimit ρ z`, seed events of distinct
comparable strings are disjoint, and the event `D_x` of the strict extensions of `x`
(`descendantEvent`) is disjoint from `A_x^∞`.  The stage labels `seedLabels` are computable from the
stream and the label relation is c.e. (`isRE_seedLabel`).

Cantor cylinders are the actual seed events; the ordered dyadic grid of `Allocator` is only the
finite bookkeeping device (Blueprint 03 Lemma A4, last paragraph).
-/

namespace Kolmogorov

open scoped ENNReal

/-- The cylinder labels of the atoms allocated to `z` at stage `s`: the words `bitsOfNatBE prec i`
for `i ∈ A_z` of the stage-`s` state. Blueprint 03 Lemma A4 (enumerated cylinders). -/
def seedLabels (ρ : RequestStream) (s : ℕ) (z : BitString) : List BitString :=
  ((allocRun ρ s).atoms z).map (bitsOfNatBE (allocRun ρ s).prec)

/-- The stage labels are computable from a computable stream (uniformly in the stage and the
string). Blueprint 03 Lemma A4 (uniformity from A3). -/
private lemma primrec_atoms_pub : Primrec₂ AllocState.atoms := by
  have H : Primrec fun p : AllocState × BitString =>
      (@List.lookup _ _ instBEqOfDecidableEq p.2 p.1.table).getD [] :=
    Primrec.option_getD.comp (Primrec.listLookup.comp Primrec.snd (
        (Primrec.snd.comp (Primrec.of_equiv (e := AllocState.equivProd))).of_eq (fun _ => rfl)
      |>.comp Primrec.fst
    )) (Primrec.const [])
  exact H.of_eq fun p => by
    have hk : @List.lookup _ _ instBEqOfDecidableEq p.2 p.1.table = List.lookup p.2 p.1.table := by
      congr
      exact lawful_beq_subsingleton _ _
    rw [hk]
    rfl

private lemma allocRun_computable_atoms_pub {ρ : RequestStream} (hρ : Computable ρ) :
    Computable fun a : ℕ × BitString => (allocRun ρ a.1).atoms a.2 :=
  primrec_atoms_pub.to_comp.comp (allocRun_computable hρ |>.comp Computable.fst) Computable.snd

/-- The stage labels are computable from a computable stream (uniformly in the stage and the
string). Blueprint 03 Lemma A4 (uniformity from A3). -/
theorem seedLabels_computable {ρ : RequestStream} (hρ : Computable ρ) :
    Computable fun a : ℕ × BitString => seedLabels ρ a.1 a.2 := by
  have hatoms : Computable fun a : ℕ × BitString => (allocRun ρ a.1).atoms a.2 :=
    allocRun_computable_atoms_pub hρ
  have hprec : Computable fun a : ℕ × BitString => (allocRun ρ a.1).prec :=
    (Primrec.fst.comp (Primrec.of_equiv (e := AllocState.equivProd))).of_eq (fun _ => rfl)
    |>.to_comp.comp (allocRun_computable hρ |>.comp Computable.fst)
  have hmap : Computable fun a : ℕ × BitString =>
      ((allocRun ρ a.1).atoms a.2).map (bitsOfNatBE (allocRun ρ a.1).prec) :=
    Computable.list_map hatoms
      (primrec_bitsOfNatBE.to_comp.comp (hprec.comp Computable.fst) Computable.snd).to₂
  exact hmap

/-- The seed event `A_z^∞`: the union over all stages of the cylinders of the atoms allocated to
`z`. Blueprint 03 Lemma A4. -/
def seedEvent (ρ : RequestStream) (z : BitString) : Set CantorSeq :=
  ⋃ s, ⋃ i ∈ (allocRun ρ s).atoms z, cantorCylinder (bitsOfNatBE (allocRun ρ s).prec i)

/-- The big-endian value of a concatenation:
`natOfBits (u ++ v) = natOfBits u · 2^|v| + natOfBits v`.
Blueprint 01 F1-CODE (quotient and remainder by `2 ^ |v|`). -/
private theorem natOfBits_append_mul_two_pow (u v : BitString) :
    natOfBits (u ++ v) = natOfBits u * 2 ^ v.length + natOfBits v := by
  induction u with
  | nil => simp [natOfBits]
  | cons b u ih =>
    simp only [List.cons_append, natOfBits, List.length_append, ih, pow_add]
    ring

/-- Refinement keeps the seed event: for `L ≤ L'`, the cylinder of an atom `i < 2^L` of `z` lies
in the union of the cylinders of the refined atoms of `z` at precision `L'` (a point selects the
descendant of `i` numbered by its next `L' - L` bits). Blueprint 03 Lemma A4 ("refinement does not
change the event"). -/
private theorem cantorCylinder_subset_refineState {st : AllocState} {L' : ℕ} (hL : st.prec ≤ L')
    {z : BitString} {i : ℕ} (hi : i ∈ st.atoms z) (hlt : i < 2 ^ st.prec) :
    cantorCylinder (bitsOfNatBE st.prec i) ⊆
      ⋃ k ∈ (refineState st L').atoms z, cantorCylinder (bitsOfNatBE L' k) := by
  intro w hw
  have hw' : cantorPrefix w st.prec = bitsOfNatBE st.prec i := by
    have := (isCantorPrefix_iff_cantorPrefix_eq _ w).1 hw
    rwa [length_bitsOfNatBE] at this
  have hsplit : cantorPrefix w L' =
      bitsOfNatBE st.prec i ++ (cantorPrefix w L').drop st.prec := by
    rw [← hw', ← cantorPrefix_take w st.prec L' hL, List.take_append_drop]
  have hdl : ((cantorPrefix w L').drop st.prec).length = L' - st.prec := by simp
  have hval : natOfBits (cantorPrefix w L') =
      i * 2 ^ (L' - st.prec) + natOfBits ((cantorPrefix w L').drop st.prec) := by
    conv_lhs => rw [hsplit]
    rw [natOfBits_append_mul_two_pow, natOfBits_bitsOfNatBE hlt, hdl]
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨natOfBits (cantorPrefix w L'), ?_, ?_⟩
  · rw [refineState_atoms, List.mem_flatMap]
    refine ⟨i, hi, List.mem_map.2 ⟨_, List.mem_range.2 ?_, hval.symm⟩⟩
    have := natOfBits_lt ((cantorPrefix w L').drop st.prec)
    rwa [hdl] at this
  · have hcode : bitsOfNatBE L' (natOfBits (cantorPrefix w L')) = cantorPrefix w L' := by
      have := bitsOfNatBE_natOfBits (cantorPrefix w L')
      rwa [cantorPrefix_length] at this
    rw [hcode]
    exact (isCantorPrefix_iff_cantorPrefix_eq _ w).2 (by rw [cantorPrefix_length])

/-- An allocation step keeps the refined atoms of every string: it only adds atoms at the
requested string. Blueprint 03 Lemma A4 (the stage events increase). -/
private theorem refineState_atoms_subset_allocStep (st : AllocState) (r : DyadicRequest)
    (w : BitString) :
    (refineState st (requestPrec st.prec r)).atoms w ⊆ (allocStep st r).atoms w := by
  by_cases hw : w = r.1
  · subst hw
    have hstep : (allocStep st r).atoms r.1 =
        (refineState st (requestPrec st.prec r)).atoms r.1 ++
          ((refineState st (requestPrec st.prec r)).freeAtoms r.1).take
            (requestAtomCount st.prec r) := by
      simp [allocStep, AllocState.setAtoms, AllocState.atoms]
    rw [hstep]
    exact List.subset_append_left _ _
  · rw [allocStep_atoms_of_ne st r hw]
    exact List.Subset.refl _

/-- Along a budgeted stream the stage seed events of `z` increase with the stage.
Blueprint 03 Lemma A4 ("the finite-stage events increase"). -/
private theorem monotone_stageSeedEvent {ρ : RequestStream} (hb : IsBudgetedRequestStream ρ)
    (z : BitString) :
    Monotone fun s =>
      ⋃ i ∈ (allocRun ρ s).atoms z, cantorCylinder (bitsOfNatBE (allocRun ρ s).prec i) := by
  refine monotone_nat_of_le_succ fun s => ?_
  obtain ⟨mass, hinv, -⟩ := allocRun_invariant hb s
  rcases hρ : ρ s with _ | r
  · simp only [allocRun, hρ]
    exact le_rfl
  · simp only [allocRun, hρ]
    refine Set.iUnion₂_subset fun i hi => ?_
    refine (cantorCylinder_subset_refineState (L' := requestPrec (allocRun ρ s).prec r)
      (le_max_left _ _) hi (hinv.atoms_lt z i hi)).trans fun w hw => ?_
    simp only [Set.mem_iUnion, exists_prop] at hw ⊢
    obtain ⟨k, hk, hwk⟩ := hw
    exact ⟨k, refineState_atoms_subset_allocStep _ r z hk, hwk⟩

/-- Along a budgeted stream the stage seed event of `z` has the stage mass: its cylinders are
pairwise incomparable (distinct atoms of one grid) and there are `mass z` of them, each of
measure `2^{-prec}`. Blueprint 03 Lemma A4 ("their measures are exactly the finite requested
weights"). -/
private theorem uniformMeasure_stageEvent_eq_stageMass {ρ : RequestStream}
    (hb : IsBudgetedRequestStream ρ) (s : ℕ) (z : BitString) :
    uniformMeasure
        (⋃ i ∈ (allocRun ρ s).atoms z, cantorCylinder (bitsOfNatBE (allocRun ρ s).prec i)) =
      ENNReal.ofReal ((streamStageMass ρ s z : ℚ) : ℝ) := by
  obtain ⟨mass, hinv, hmass⟩ := allocRun_invariant hb s
  have hpw : (((allocRun ρ s).atoms z).map (bitsOfNatBE (allocRun ρ s).prec)).Pairwise
      IsIncomparable := by
    rw [List.pairwise_map]
    refine (hinv.nodup z).imp_of_mem fun {i j} hi hj hij => ?_
    have hne : bitsOfNatBE (allocRun ρ s).prec i ≠ bitsOfNatBE (allocRun ρ s).prec j :=
      fun h => hij (by
        have := congrArg natOfBits h
        rwa [natOfBits_bitsOfNatBE (hinv.atoms_lt z i hi),
          natOfBits_bitsOfNatBE (hinv.atoms_lt z j hj)] at this)
    exact ⟨fun h => hne (h.eq_of_length (by simp)), fun h => hne (h.eq_of_length (by simp)).symm⟩
  have hU : (⋃ i ∈ (allocRun ρ s).atoms z, cantorCylinder (bitsOfNatBE (allocRun ρ s).prec i)) =
      ⋃ p ∈ ((allocRun ρ s).atoms z).map (bitsOfNatBE (allocRun ρ s).prec), cantorCylinder p := by
    ext w
    simp
  rw [hU, uniformMeasure_biUnion_cantorCylinder hpw, List.map_map, ← hmass z]
  simp only [Function.comp_def, length_bitsOfNatBE, List.map_const', List.sum_replicate,
    nsmul_eq_mul, hinv.card z]
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv, ENNReal.inv_pow]

/-- Lemma A4 (measure): along a budgeted stream, the fair-coin measure of the seed event of `z` is
the limit mass `requestLimit ρ z` (continuity from below). Blueprint 03 Lemma A4. -/
theorem uniformMeasure_seedEvent {ρ : RequestStream} (hb : IsBudgetedRequestStream ρ)
    (z : BitString) : uniformMeasure (seedEvent ρ z) = requestLimit ρ z := by
  rw [seedEvent, (monotone_stageSeedEvent hb z).measure_iUnion, requestLimit]
  exact iSup_congr fun s => uniformMeasure_stageEvent_eq_stageMass hb s z

/-- Two cylinders of one grid `[0, 2^L)` that share a point belong to the same atom: both labels
have length `L` and are prefixes of the point, so they coincide, and distinct grid indices have
distinct big-endian labels. Blueprint 03 Lemma A4 (the cylinders of distinct atoms of one grid are
incomparable). -/
private theorem eq_of_mem_cantorCylinder_bitsOfNatBE {L i k : ℕ} (hi : i < 2 ^ L)
    (hk : k < 2 ^ L) {x : CantorSeq} (hxi : x ∈ cantorCylinder (bitsOfNatBE L i))
    (hxk : x ∈ cantorCylinder (bitsOfNatBE L k)) : i = k := by
  have h1 := (isCantorPrefix_iff_cantorPrefix_eq _ x).1 hxi
  have h2 := (isCantorPrefix_iff_cantorPrefix_eq _ x).1 hxk
  rw [length_bitsOfNatBE] at h1 h2
  have := congrArg natOfBits (h1.symm.trans h2)
  rwa [natOfBits_bitsOfNatBE hi, natOfBits_bitsOfNatBE hk] at this

/-- Lemma A4 (disjointness): along a budgeted stream, the seed events of distinct comparable input
strings are disjoint. Blueprint 03 Lemma A4. -/
theorem seedEvent_disjoint {ρ : RequestStream} (hb : IsBudgetedRequestStream ρ) {z w : BitString}
    (h : IsComparable z w) (hne : z ≠ w) : Disjoint (seedEvent ρ z) (seedEvent ρ w) := by
  rw [Set.disjoint_left]
  intro x hxz hxw
  simp only [seedEvent, Set.mem_iUnion, exists_prop] at hxz hxw
  obtain ⟨s, i, hi, hxi⟩ := hxz
  obtain ⟨t, k, hk, hxk⟩ := hxw
  have hz := monotone_stageSeedEvent hb z (le_max_left s t) (Set.mem_iUnion₂.2 ⟨i, hi, hxi⟩)
  have hw := monotone_stageSeedEvent hb w (le_max_right s t) (Set.mem_iUnion₂.2 ⟨k, hk, hxk⟩)
  obtain ⟨i', hi', hxi'⟩ := Set.mem_iUnion₂.1 hz
  obtain ⟨k', hk', hxk'⟩ := Set.mem_iUnion₂.1 hw
  obtain ⟨mass, hinv, -⟩ := allocRun_invariant hb (max s t)
  have hik := eq_of_mem_cantorCylinder_bitsOfNatBE (hinv.atoms_lt z i' hi')
    (hinv.atoms_lt w k' hk') hxi' hxk'
  subst hik
  exact hinv.disjoint z w h hne i' hi' hk'

/-- `D_x`: the union of the seed events of the strict extensions of `x`. Blueprint 03 §5. -/
def descendantEvent (ρ : RequestStream) (x : BitString) : Set CantorSeq :=
  ⋃ y, ⋃ (_ : x <+: y ∧ x ≠ y), seedEvent ρ y

/-- Along a budgeted stream, `A_x^∞` and `D_x` are disjoint (comparable disjointness).
Blueprint 03 §5 (first paragraph). -/
theorem seedEvent_disjoint_descendantEvent {ρ : RequestStream} (hb : IsBudgetedRequestStream ρ)
    (x : BitString) : Disjoint (seedEvent ρ x) (descendantEvent ρ x) := by
  unfold descendantEvent
  refine Set.disjoint_iUnion_right.2 fun y => Set.disjoint_iUnion_right.2 fun hy => ?_
  exact seedEvent_disjoint hb (Or.inl hy.1) hy.2

/-- Lemma A4 (uniformity): for a computable stream, the relation "`p` is a seed label of `z` at
some stage" is computably enumerable, uniformly in `(z, p)`. Blueprint 03 Lemma A4. -/
theorem isRE_seedLabel {ρ : RequestStream} (hρ : Computable ρ) :
    IsRE fun a : BitString × BitString => ∃ s, a.2 ∈ seedLabels ρ s a.1 := by
  have H1 : Computable fun a : (BitString × BitString) × ℕ => seedLabels ρ a.2 a.1.1 :=
    Computable.of_eq ((seedLabels_computable hρ).comp
      (Computable.pair Computable.snd (Computable.fst.comp Computable.fst))) (fun _ => rfl)
  have hany : Computable fun a : (BitString × BitString) × ℕ =>
      decide (a.1.2 ∈ seedLabels ρ a.2 a.1.1) := by
    have h1 : Computable fun a : (BitString × BitString) × ℕ => (a.1.2, seedLabels ρ a.2 a.1.1) :=
      Computable.pair (Computable.snd.comp Computable.fst) H1
    have H2 : Computable (fun p : BitString × List BitString =>
        @decide (p.1 ∈ p.2) (@List.instDecidableMemOfLawfulBEq BitString List.instBEq _ p.1 p.2)) :=
      (Primrec₂.of_eq list_mem_decide_primrec (fun (a : BitString) (l : List BitString) => by
        apply decide_eq_decide.mpr
        rfl
      ) : Primrec₂ (fun (a : BitString) (l : List BitString) =>
        @decide (a ∈ l) (@List.instDecidableMemOfLawfulBEq BitString List.instBEq _ a l))).to_comp
    exact Computable.of_eq (H2.comp h1) (fun _ => rfl)
  exact IsRE.exists_encodable (isRE_of_computable_bool _ _
    (fun p => decide_eq_true_iff) hany)

end Kolmogorov
