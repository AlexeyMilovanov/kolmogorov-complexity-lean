import KolmogorovMathlib.StrongMerging.Upper.DecodersCore
import KolmogorovMathlib.StrongMerging.ExtraDefs

/-!
# The exact partition filter (blueprint T05, `UpperPartitionFilter`)

`sublinear-merging.tex`, subsection "A uniform portfolio and exact partition normalization"
(tex ~944–960) and the blueprint paragraph "Portfolio and exact normalization" (tex ~4026–4038).

For a globally total program `q₀` whose outputs are read as finite sets `Q₀ z = q₀(z)`
(`progModel`, through the total parser `parseModel`), the filter is
`Q z = {y ∈ Q₀ z : Q₀ y = Q₀ z}` (`filterModel`).  It runs `q₀`, never `Q`, on the members of
`Q₀ z`; members may have any length.

* `mem_filterModel_self`, `mem_filterModel_iff_eq`: if `q₀` contains its inputs, then so does
  the filter, and `Q⁻¹(Q z) = Q z` for every binary string `z`.
* `filterPointDecoder` is the literal filtered program.  `upperPartitionFilter` (T05): one prefix
  `pre`, fixed before `q₀`, makes `pre ++ q₀` an exact partition selector
  (`IsExactPartitionSelector`) for `filterModel q₀`, of length `|q₀| + |pre|`.
* `filterSetDecoder` computes `Q z` from the code of `Q₀ z` and the program `q₀`, so
  `CT(Q z | Q₀ z) ≤ |q₀| + c` (`totalC_filterModel_le`), `C(Q z | Q₀ z) ≤ |q₀| + c`
  (`condC_filterModel_le`) and `C(Q z) ≤ C(Q₀ z) + c (|q₀| + 1) + c log₂ (C(Q₀ z) + 2)`
  (`setC_filterModel_le`).  The cardinality only decreases (`filterModel_subset`).

The output tables of `q₀` on a finite list of mixed-length strings are computed by complete runs
(`runList`), as `runTable` does on all strings of one length.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### The filter as a set operation -/

/-- The model `Q₀ z` output by the program `q₀` on the input `z`, read by the total parser
`parseModel` (an invalid output is read as whatever it lists). -/
noncomputable def progModel (q0 z : BitString) : Finset BitString :=
  parseModel (progOut q0 z)

/-- **The partition filter** `Q z = {y ∈ Q₀ z : Q₀ y = Q₀ z}` (T05, tex ~944). -/
noncomputable def filterModel (q0 z : BitString) : Finset BitString :=
  (progModel q0 z).filter fun y => progModel q0 y = progModel q0 z

/-- The filter only removes elements: `Q z ⊆ Q₀ z`. -/
theorem filterModel_subset (q0 z : BitString) : filterModel q0 z ⊆ progModel q0 z :=
  Finset.filter_subset _ _

/-- Membership in the filter. -/
theorem mem_filterModel {q0 z y : BitString} :
    y ∈ filterModel q0 z ↔ y ∈ progModel q0 z ∧ progModel q0 y = progModel q0 z :=
  Finset.mem_filter

/-- The filter at `y` depends only on `Q₀ y`. -/
theorem filterModel_eq_of_progModel_eq {q0 y z : BitString}
    (h : progModel q0 y = progModel q0 z) : filterModel q0 y = filterModel q0 z := by
  simp only [filterModel, h]

/-- If `q₀` contains its inputs, so does the filter. -/
theorem mem_filterModel_self {q0 : BitString} (hc : ∀ z : BitString, z ∈ progModel q0 z)
    (z : BitString) : z ∈ filterModel q0 z :=
  mem_filterModel.mpr ⟨hc z, rfl⟩

/-- **Exact partition** (tex ~948): if `q₀` contains its inputs, then `y ∈ Q z` exactly when
`Q y = Q z`. -/
theorem mem_filterModel_iff_eq {q0 : BitString} (hc : ∀ z : BitString, z ∈ progModel q0 z)
    (z y : BitString) : y ∈ filterModel q0 z ↔ filterModel q0 y = filterModel q0 z := by
  constructor
  · intro hy
    exact filterModel_eq_of_progModel_eq (mem_filterModel.mp hy).2
  · intro h
    rw [← h]
    exact mem_filterModel_self hc y

/-! ### Complete runs on a finite list -/

/-- All runs of `p` on the members of the list `l` have halted within `t` stages. -/
noncomputable def listReady (t : ℕ) (p : BitString) (l : List BitString) : Bool :=
  l.all fun z => (conditionalRunOut uCode t p z).isSome

/-- The output table of `p` on the members of `l` after `t` stages (`[]` if not yet halted). -/
noncomputable def listStage (t : ℕ) (p : BitString) (l : List BitString) :
    List (BitString × BitString) :=
  l.map fun z => (z, (conditionalRunOut uCode t p z).getD [])

/-- **Complete runs on a list**: the output table of `p` on the members of `l`, read at the first
stage at which all runs have halted.  A partial computation that halts when `p` is total. -/
noncomputable def runList (p : BitString) (l : List BitString) :
    Part (List (BitString × BitString)) :=
  (Nat.rfind fun t => Part.some (listReady t p l)).map fun t => listStage t p l

/-- **Complete runs on a list halt for a total program** (as `runTable_dom`): a halting stage for
each member, their sum, `conditionalRunOut_mono`, then `Nat.rfind_dom`. -/
theorem runList_dom {p : BitString} (hp : IsTotalProgram universalDecompressor p)
    (l : List BitString) : (runList p l).Dom := by
  have hstage : ∀ z : BitString, ∃ t, (conditionalRunOut uCode t p z).isSome = true := by
    intro z
    obtain ⟨t, ht⟩ := conditionalRunOut_complete uCode_spec (Part.get_mem (hp z))
    exact ⟨t, by rw [ht]; rfl⟩
  choose f hf using hstage
  have hready : listReady (l.map f).sum p l = true := by
    unfold listReady
    rw [List.all_eq_true]
    intro z hz
    have hle : f z ≤ (l.map f).sum := List.le_sum_of_mem (List.mem_map.2 ⟨z, hz, rfl⟩)
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hf z)
    rw [conditionalRunOut_mono uCode hle hu]
    rfl
  change (Nat.rfind fun t => Part.some (listReady t p l)).Dom
  exact Nat.rfind_dom.2 ⟨_, by rw [hready]; exact Part.mem_some true, fun _ => trivial⟩

/-- Looking up a member `y` of `l` in the table `l.map (z ↦ (z, g z))` returns `g y`. -/
theorem tableOut_map_of_mem (g : BitString → BitString) {l : List BitString} {y : BitString}
    (hy : y ∈ l) : tableOut (l.map fun z => (z, g z)) y = g y := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    by_cases hay : a = y
    · subst hay
      simp [tableOut]
    · have hy' : y ∈ l := by
        rcases List.mem_cons.1 hy with h | h
        · exact absurd h.symm hay
        · exact h
      have := ih hy'
      simpa [tableOut, hay] using this

/-- **Complete runs on a list read back the outputs**: a table returned by `runList p l` gives,
at every member `y` of `l`, the output `progOut p y` (as `tableOut_of_mem_runTable`). -/
theorem tableOut_of_mem_runList {p : BitString} {l : List BitString}
    {T : List (BitString × BitString)} (hT : T ∈ runList p l) {y : BitString} (hy : y ∈ l) :
    tableOut T y = progOut p y := by
  obtain ⟨t, ht, rfl⟩ := (Part.mem_map_iff _).1 hT
  have hready : listReady t p l = true := by
    have h := Nat.rfind_spec ht
    exact (Part.mem_some_iff.1 h).symm
  unfold listReady at hready
  rw [List.all_eq_true] at hready
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hready y hy)
  have hout : progOut p y = u := progOut_eq_of_mem (conditionalRunOut_sound uCode_spec hu)
  rw [hout]
  unfold listStage
  rw [tableOut_map_of_mem (fun z => (conditionalRunOut uCode t p z).getD []) hy, hu]
  rfl

/-- Readiness of the list table is primitive recursive in `((p, l), t)`. -/
theorem listReady_primrec :
    Primrec₂ fun (q : BitString × List BitString) (t : ℕ) => listReady t q.1 q.2 := by
  have hrun : Primrec₂ fun (x : (BitString × List BitString) × ℕ) (z : BitString) =>
      conditionalRunOut uCode x.2 x.1.1 z :=
    Primrec.comp
      (f := fun q : ℕ × BitString × BitString => conditionalRunOut uCode q.1 q.2.1 q.2.2)
      (g := fun y : ((BitString × List BitString) × ℕ) × BitString => (y.1.2, y.1.1.1, y.2))
      uRunOut_primrec
      ((Primrec.snd.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        Primrec.snd))
  have h := list_all_primrec (f := fun x : (BitString × List BitString) × ℕ => x.1.2)
    (p := fun (x : (BitString × List BitString) × ℕ) (z : BitString) =>
      (conditionalRunOut uCode x.2 x.1.1 z).isSome)
    (Primrec.snd.comp Primrec.fst) (Primrec.option_isSome.comp hrun)
  exact h.of_eq fun x => rfl

/-- The list table at a stage is primitive recursive in `((p, l), t)`. -/
theorem listStage_primrec :
    Primrec₂ fun (q : BitString × List BitString) (t : ℕ) => listStage t q.1 q.2 := by
  have hrun : Primrec₂ fun (x : (BitString × List BitString) × ℕ) (z : BitString) =>
      conditionalRunOut uCode x.2 x.1.1 z :=
    Primrec.comp
      (f := fun q : ℕ × BitString × BitString => conditionalRunOut uCode q.1 q.2.1 q.2.2)
      (g := fun y : ((BitString × List BitString) × ℕ) × BitString => (y.1.2, y.1.1.1, y.2))
      uRunOut_primrec
      ((Primrec.snd.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        Primrec.snd))
  have hg : Primrec₂ fun (x : (BitString × List BitString) × ℕ) (z : BitString) =>
      (z, (conditionalRunOut uCode x.2 x.1.1 z).getD []) :=
    Primrec.snd.pair (Primrec.option_getD.comp hrun (Primrec.const []))
  have h := Primrec.list_map (Primrec.snd.comp Primrec.fst) hg
  exact h.of_eq fun x => rfl

/-- **Complete runs on a list are partial recursive** (`Partrec.rfind` and `Partrec.map`). -/
theorem runList_partrec : Partrec₂ runList := by
  have hrf : Partrec fun q : BitString × List BitString =>
      Nat.rfind fun t => Part.some (listReady t q.1 q.2) :=
    Partrec.rfind listReady_primrec.to_comp.partrec₂
  exact (hrf.map listStage_primrec.to_comp).of_eq fun q => rfl

/-! ### The literal filter programs -/

/-- The filter computed from the code `v` of `S = parseModel v` and an output table `T` of `q₀`:
the code of `{y ∈ S : parseModel (T y) = S}`. -/
noncomputable def filterOut (v : BitString) (T : List (BitString × BitString)) : BitString :=
  canonicalFiniteSetCode ((parseModel v).filter fun y => parseModel (tableOut T y) = parseModel v)

/-- **The filter output is primitive recursive** in the code and the table.

Proof sketch: `parseModel v = (canonicalPointListOfCode v).toFinset`, so the filtered set is
`((canonicalPointListOfCode v).filter test).toFinset` (`List.toFinset_filter`); the test compares
the canonical codes `canonicalFiniteSetCode (parseModel w)` (injective,
`canonicalFiniteSetCode_injective`), each primitive recursive by
`canonicalFiniteSetCode_toFinset_primrec.comp canonicalPointListOfCode_primrec`, with
`tableOut_primrec` and `Primrec.eq`; then `primrec_list_filter` and
`canonicalFiniteSetCode_toFinset_primrec`. -/
theorem filterOut_primrec : Primrec₂ filterOut := by
  have hcode : Primrec fun w : BitString => canonicalFiniteSetCode (parseModel w) :=
    (canonicalFiniteSetCode_toFinset_primrec.comp canonicalPointListOfCode_primrec).of_eq
      fun _ => rfl
  have hL : Primrec fun q : BitString × List (BitString × BitString) =>
      canonicalPointListOfCode q.1 :=
    canonicalPointListOfCode_primrec.comp Primrec.fst
  have htest : Primrec₂ fun (q : BitString × List (BitString × BitString)) (y : BitString) =>
      decide (canonicalFiniteSetCode (parseModel (tableOut q.2 y)) =
        canonicalFiniteSetCode (parseModel q.1)) :=
    (Primrec.eq.decide.comp
      (hcode.comp (tableOut_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
      (hcode.comp (Primrec.fst.comp Primrec.fst))).to₂
  have hfilt := primrec_list_filter hL htest
  refine (canonicalFiniteSetCode_toFinset_primrec.comp hfilt).to₂.of_eq fun v T => ?_
  simp only [filterOut]
  congr 1
  ext y
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, decide_eq_true_eq,
    canonicalFiniteSetCode_injective.eq_iff]
  simp only [parseModel, List.mem_toFinset]

/-- **The filter from the model's code**: on the packet `q₀` and the condition `v`, run `q₀` on
the members of `parseModel v` and output `filterOut v`. -/
noncomputable def filterSetDecoder : Map := fun q =>
  (runList q.1 (canonicalPointListOfCode q.2)).map fun T => filterOut q.2 T

/-- **The filtered point program**: on the packet `q₀` and the input `z`, compute `w = q₀(z)`,
then filter `parseModel w`. -/
noncomputable def filterPointDecoder : Map := fun q =>
  (universalDecompressor q).bind fun w =>
    filterSetDecoder (q.1, canonicalFiniteSetCode (parseModel w))

/-- The set-level filter decoder is partial recursive. -/
theorem filterSetDecoder_partrec : isDecompressor filterSetDecoder := by
  have h1 : Partrec fun q : BitString × BitString =>
      runList q.1 (canonicalPointListOfCode q.2) :=
    runList_partrec.comp Computable.fst
      (canonicalPointListOfCode_primrec.to_comp.comp Computable.snd)
  have h2 : Computable₂ fun (q : BitString × BitString) (T : List (BitString × BitString)) =>
      filterOut q.2 T :=
    filterOut_primrec.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd
  exact (Partrec.map h1 h2).of_eq fun q => rfl

/-- The code of a parsed model is primitive recursive in the word. -/
theorem parseModel_code_primrec' :
    Primrec fun w : BitString => canonicalFiniteSetCode (parseModel w) :=
  (canonicalFiniteSetCode_toFinset_primrec.comp canonicalPointListOfCode_primrec).of_eq
    fun _ => rfl

/-- The filtered point program is partial recursive. -/
theorem filterPointDecoder_partrec : isDecompressor filterPointDecoder := by
  have hU : Partrec universalDecompressor := isDecompressor_universalDecompressor
  have hS : Partrec filterSetDecoder := filterSetDecoder_partrec
  have hg : Partrec₂ fun (q : BitString × BitString) (w : BitString) =>
      filterSetDecoder (q.1, canonicalFiniteSetCode (parseModel w)) :=
    hS.comp ((Computable.fst.comp Computable.fst).pair
      (parseModel_code_primrec'.to_comp.comp Computable.snd))
  exact (Partrec.bind hU hg).of_eq fun q => rfl

/-- The set-level filter halts for a total `q₀`. -/
theorem filterSetDecoder_dom {q0 : BitString} (hq0 : IsTotalProgram universalDecompressor q0)
    (v : BitString) : (filterSetDecoder (q0, v)).Dom :=
  runList_dom hq0 _

/-- **The set-level filter on a model code**: for a total `q₀` and a finite set `S`, the decoder
returns the code of `{y ∈ S : Q₀ y = S}`. -/
theorem filterSetDecoder_spec {q0 : BitString} (hq0 : IsTotalProgram universalDecompressor q0)
    (S : Finset BitString) :
    filterSetDecoder (q0, canonicalFiniteSetCode S) =
      Part.some (canonicalFiniteSetCode (S.filter fun y => progModel q0 y = S)) := by
  obtain ⟨T, hT⟩ := Part.dom_iff_mem.mp
    (runList_dom hq0 (canonicalPointListOfCode (canonicalFiniteSetCode S)))
  have hfil : filterOut (canonicalFiniteSetCode S) T =
      canonicalFiniteSetCode (S.filter fun y => progModel q0 y = S) := by
    unfold filterOut
    rw [parseModel_canonicalFiniteSetCode]
    congr 1
    apply Finset.filter_congr
    intro y hy
    have hyl : y ∈ canonicalPointListOfCode (canonicalFiniteSetCode S) := by
      rw [canonicalPointListOfCode_canonicalFiniteSetCode]
      rw [← canonicalFinsetList_toFinset S] at hy
      exact List.mem_toFinset.mp hy
    rw [tableOut_of_mem_runList hT hyl]
    rfl
  rw [Part.eq_some_iff]
  exact (Part.mem_map_iff _).mpr ⟨T, hT, hfil⟩

/-- **The filtered point program on its packet**: for a total `q₀` it halts on every input `z`
with the code of `filterModel q₀ z`. -/
theorem filterPointDecoder_spec {q0 : BitString} (hq0 : IsTotalProgram universalDecompressor q0)
    (z : BitString) :
    filterPointDecoder (q0, z) = Part.some (canonicalFiniteSetCode (filterModel q0 z)) := by
  have hmem : progOut q0 z ∈ universalDecompressor (q0, z) := by
    have h1 := Part.get_mem (hq0 z)
    rwa [progOut_eq_of_mem h1]
  unfold filterPointDecoder
  rw [Part.eq_some_iff, Part.mem_bind_iff]
  refine ⟨progOut q0 z, hmem, ?_⟩
  rw [filterSetDecoder_spec hq0]
  exact Part.mem_some _

/-! ### T05: the exact partition filter -/

/-- **The exact partition filter (blueprint T05, `UpperPartitionFilter`).**  There is one constant
`c_f` (the length of a fixed prefix) such that for every globally total program `q₀` whose
outputs contain their inputs, the program `q = pre ++ q₀` of length `|q₀| + c_f` is an exact
partition selector for the filter `Q z = {y ∈ Q₀ z : Q₀ y = Q₀ z}`: it halts on every input with
the code of `Q z`, `z ∈ Q z`, and `y ∈ Q z ↔ Q y = Q z`.  Mixed-length outputs are allowed.

`sublinear-merging.tex`, tex ~944–950. -/
theorem upperPartitionFilter :
    ∃ cf : ℕ, ∀ q0 : BitString, IsTotalProgram universalDecompressor q0 →
      (∀ z : BitString, z ∈ progModel q0 z) →
        ∃ q : BitString, q.length = q0.length + cf ∧
          IsExactPartitionSelector q (filterModel q0) := by
  obtain ⟨pre, hpre⟩ :=
    Lower.exists_compiled_totalProgram filterPointDecoder filterPointDecoder_partrec
  refine ⟨pre.length, fun q0 hq0 hc => ?_⟩
  have hdom : ∀ y : BitString, (filterPointDecoder (q0, y)).Dom := fun y => by
    rw [filterPointDecoder_spec hq0 y]
    trivial
  obtain ⟨htot, hlen, hprod⟩ := hpre q0 hdom
  refine ⟨pre ++ q0, by rw [hlen, Nat.add_comm], htot, fun z => hprod z _ ?_,
    mem_filterModel_self hc, mem_filterModel_iff_eq hc⟩
  rw [filterPointDecoder_spec hq0 z]
  exact Part.mem_some _

/-! ### T05: complexity overhead of the filter -/

/-- **Total overhead of the filter**: `CT(Q z | Q₀ z) ≤ |q₀| + c` for every total `q₀` and every
`z` (the set-level filter with the packet `q₀`). -/
theorem totalC_filterModel_le :
    ∃ c : ℕ, ∀ q0 : BitString, IsTotalProgram universalDecompressor q0 → ∀ z : BitString,
      totalC (canonicalFiniteSetCode (filterModel q0 z))
        (canonicalFiniteSetCode (progModel q0 z)) ≤ q0.length + c := by
  obtain ⟨c, hc⟩ := totalC_le_of_decoder filterSetDecoder filterSetDecoder_partrec
  refine ⟨c, fun q0 hq0 z => ?_⟩
  have hmem : canonicalFiniteSetCode (filterModel q0 z) ∈
      filterSetDecoder (q0, canonicalFiniteSetCode (progModel q0 z)) := by
    rw [filterSetDecoder_spec hq0]
    exact Part.mem_some _
  exact hc q0 (filterSetDecoder_dom hq0) _ _ hmem

/-- **Plain overhead of the filter**: `C(Q z | Q₀ z) ≤ |q₀| + c`. -/
theorem condC_filterModel_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ q0 : BitString, IsTotalProgram universalDecompressor q0 → ∀ z : BitString,
      condC V (canonicalFiniteSetCode (filterModel q0 z))
        (canonicalFiniteSetCode (progModel q0 z)) ≤ q0.length + c := by
  obtain ⟨c, hc⟩ := condC_le_of_decoder V hV filterSetDecoder filterSetDecoder_partrec
  refine ⟨c, fun q0 hq0 z => ?_⟩
  have hmem : canonicalFiniteSetCode (filterModel q0 z) ∈
      filterSetDecoder (q0, canonicalFiniteSetCode (progModel q0 z)) := by
    rw [filterSetDecoder_spec hq0]
    exact Part.mem_some _
  exact hc q0 _ _ hmem

/-- **A crude logarithm bound** (a local copy of `logb_add_two_le` of `Upper.Tradeoff`):
`log₂ (t + 2) ≤ 2 t + 2` for `t ≥ 0`, from `Real.log_le_sub_one_of_pos` and `log 2 ≥ 1/2`. -/
theorem pfE_logb_add_two_le {t : ℝ} (ht : 0 ≤ t) : Real.logb 2 (t + 2) ≤ 2 * t + 2 := by
  have h1 : Real.log (t + 2) ≤ t + 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < t + 2)
    linarith
  have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have h' : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
    linarith
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t + 2)
    (by linarith : (0 : ℝ) ≤ Real.log 2 - 1 / 2)]

/-- **Model-complexity overhead of the filter** (T05 obligation "complexity overhead"): for an
optimal `V` there is `c` with `C(Q z) ≤ C(Q₀ z) + c (|q₀| + 1) + c log₂ (C(Q₀ z) + 2)` for every
total `q₀` and every `z`.

Proof sketch: `upperComplexityChain_trans V hV` with the empty condition (`plainC_eq_condC_nil`)
gives `C(Q) ≤ C(Q₀) + C(Q | Q₀) + c₃ log₂ (C(Q₀) + C(Q | Q₀) + 2)`; insert
`condC_filterModel_le` (`C(Q | Q₀) ≤ |q₀| + c₁`, monotonicity of `logb`), and split
`log₂ (s + t + 2) ≤ log₂ (s + 2) + log₂ (t + 2)` (as `s + t + 2 ≤ (s + 2) (t + 2)`) and
`log₂ (t + 2) ≤ 2 t + 2` (`logb_add_two_le` of `Upper.Tradeoff`, or `Real.logb_le_sub_one`-style).
Take `c = c₁ + 2 c₃ c₁ + 3 c₃ + 1`. -/
theorem setC_filterModel_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ q0 : BitString, IsTotalProgram universalDecompressor q0 → ∀ z : BitString,
      setC V (filterModel q0 z) ≤ setC V (progModel q0 z) + c * ((q0.length : ℝ) + 1) +
        c * Real.logb 2 (setC V (progModel q0 z) + 2) := by
  obtain ⟨c₃, h₃⟩ := upperComplexityChain_trans V hV
  obtain ⟨c₁, h₁⟩ := condC_filterModel_le V hV
  refine ⟨c₁ + 2 * c₃ * c₁ + 3 * c₃ + 1, fun q0 hq0 z => ?_⟩
  have hchain := h₃ (canonicalFiniteSetCode (filterModel q0 z))
    (canonicalFiniteSetCode (progModel q0 z)) []
  simp only [← plainC_eq_condC_nil] at hchain
  have ht := h₁ q0 hq0 z
  have hs0 := plainC_nonneg V (canonicalFiniteSetCode (progModel q0 z))
  have ht0 := condC_nonneg V (canonicalFiniteSetCode (filterModel q0 z))
    (canonicalFiniteSetCode (progModel q0 z))
  unfold setC
  generalize plainC V (canonicalFiniteSetCode (progModel q0 z)) = s at hchain hs0 ⊢
  generalize condC V (canonicalFiniteSetCode (filterModel q0 z))
    (canonicalFiniteSetCode (progModel q0 z)) = t at hchain ht ht0
  have hL0 : (0 : ℝ) ≤ q0.length := Nat.cast_nonneg _
  have hc₃0 : (0 : ℝ) ≤ c₃ := Nat.cast_nonneg c₃
  have hc₁0 : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg c₁
  have hsplit : Real.logb 2 (s + t + 2) ≤ Real.logb 2 (s + 2) + Real.logb 2 (t + 2) := by
    rw [← Real.logb_mul (by linarith : (0 : ℝ) < s + 2).ne' (by linarith : (0 : ℝ) < t + 2).ne']
    apply Real.logb_le_logb_of_le one_lt_two (by linarith)
    nlinarith [mul_nonneg hs0 ht0]
  have htlog : Real.logb 2 (t + 2) ≤ 2 * ((q0.length : ℝ) + c₁) + 2 :=
    (logb_add_two_mono ht0 ht).trans (pfE_logb_add_two_le (by positivity))
  have hslog : 0 ≤ Real.logb 2 (s + 2) := Real.logb_nonneg one_lt_two (by linarith)
  have m1 : (c₃ : ℝ) * Real.logb 2 (s + t + 2) ≤
      c₃ * (Real.logb 2 (s + 2) + (2 * ((q0.length : ℝ) + c₁) + 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hc₃0
  push_cast
  nlinarith [mul_nonneg hc₁0 hL0, mul_nonneg (mul_nonneg hc₃0 hc₁0) hL0, mul_nonneg hc₃0 hL0,
    mul_nonneg hc₁0 hslog, mul_nonneg (mul_nonneg hc₃0 hc₁0) hslog, mul_nonneg hc₃0 hslog]

end Kolmogorov.StrongMerging.Upper
