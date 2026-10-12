import KolmogorovMathlib.StrongMerging.Coding
import KolmogorovMathlib.StrongMerging.Upper.Hierarchy

/-!
# Decoders of the square-root merger: shared finite procedures (H03–H05 infrastructure)

`sublinear-merging.tex`, appendix "Literal decoders, coding costs, and totality" (tex ~2346–2785):
the finite procedures shared by the total local-list decoder (H03), the plain residual-rank decoder
(H04) and the total point selector (H05).

* `progOut p z`: the output of the program `p` on the condition `z` under the canonical total
  interpreter `universalDecompressor` (default `[]` on divergence).  `instShape pA pB n a b` is the
  shape graph of an instance whose witness outputs are read by `progOut`.
* `runTable p n`: the finite output table of `p` on all strings of length `n`, computed by complete
  runs (a `Nat.rfind` over evaluation stages).  It is a *partial recursive* step that halts when `p`
  is total (`runTable_dom`); it is the point where totality of the witnesses enters (flag 1 of the
  B_GRAPH report).  Its value reads back the outputs (`tableOut_of_mem_runTable`), so the shape read
  from the tables agrees with `instShape` at the data length (`tableShape_agreeOn`) and all
  hierarchy objects can be computed from the tables by B's primitive recursive procedures.
* `incidentBlocks`, `localBlock`: the global depth-`j` list filtered to the blocks incident to one
  typed endpoint, and its `s`-th entry (default `∅`).  One rank in one global list, not a path of
  ranks (tex ~375).  `exists_localBlock_index`: an incident block has a rank `< 2^(jL+1)`.
* `hdrCost`: the header cost `∑ ⌈log₂ (k + 2)⌉` of a list of numeric packet fields.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### Program outputs and the instance shape -/

open Classical in
/-- The output of the program `p` on the condition `z` under the canonical total interpreter
`universalDecompressor`; the default `[]` if the computation diverges. -/
noncomputable def progOut (p z : BitString) : BitString :=
  (universalDecompressor (p, z)).getOrElse []

/-- `progOut` returns the output of a halting run. -/
theorem progOut_eq_of_mem {p z u : BitString} (h : u ∈ universalDecompressor (p, z)) :
    progOut p z = u := by
  classical
  unfold progOut
  rw [Part.getOrElse_of_dom _ h.fst]
  exact Part.get_eq_of_mem h _

/-- The shape parameters of an instance: the witness outputs are read by `progOut` from the two
total witnesses `pA`, `pB`, with data length `n` and size buckets `a`, `b`. -/
noncomputable def instShape (pA pB : BitString) (n a b : ℕ) : ShapeParams :=
  ⟨progOut pA, progOut pB, n, a, b⟩

/-! ### Complete runs: the output table of a total program -/

/-- A fixed `Nat.Partrec.Code` of the canonical total interpreter. -/
noncomputable def uCode : Nat.Partrec.Code :=
  Classical.choose (Lower.exists_isCodeFor_of_isDecompressor isDecompressor_universalDecompressor)

/-- `uCode` computes `universalDecompressor`. -/
theorem uCode_spec : IsCodeFor uCode universalDecompressor :=
  Classical.choose_spec
    (Lower.exists_isCodeFor_of_isDecompressor isDecompressor_universalDecompressor)

/-- The output table of `p` on the strings of length `n` after `t` evaluation stages (an output
not yet available is read as `[]`). -/
noncomputable def stageTable (t : ℕ) (p : BitString) (n : ℕ) : List (BitString × BitString) :=
  (allStrings n).map fun z => (z, (conditionalRunOut uCode t p z).getD [])

/-- All runs of `p` on strings of length `n` have halted within `t` stages. -/
noncomputable def tableReady (t : ℕ) (p : BitString) (n : ℕ) : Bool :=
  (allStrings n).all fun z => (conditionalRunOut uCode t p z).isSome

/-- **Complete runs.**  The output table of `p` on all strings of length `n`, computed at the first
stage at which all `2ⁿ` runs have halted.  A partial computation: it halts when `p` is total. -/
noncomputable def runTable (p : BitString) (n : ℕ) : Part (List (BitString × BitString)) :=
  (Nat.rfind fun t => Part.some (tableReady t p n)).map fun t => stageTable t p n

/-- The bounded evaluator of the canonical interpreter is primitive recursive in the stage, the
program and the condition. -/
theorem uRunOut_primrec :
    Primrec fun q : ℕ × BitString × BitString => conditionalRunOut uCode q.1 q.2.1 q.2.2 := by
  unfold conditionalRunOut
  apply Primrec.option_bind
  · exact (evaln_primrec uCode).comp Primrec.fst
      (Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))
  · exact Primrec.decode.comp Primrec.snd

/-- Readiness of the table is primitive recursive in `((p, n), t)`. -/
theorem tableReady_primrec :
    Primrec₂ fun (q : BitString × ℕ) (t : ℕ) => tableReady t q.1 q.2 := by
  have hrun : Primrec₂ fun (x : (BitString × ℕ) × ℕ) (z : BitString) =>
      conditionalRunOut uCode x.2 x.1.1 z :=
    Primrec.comp (f := fun q : ℕ × BitString × BitString => conditionalRunOut uCode q.1 q.2.1 q.2.2)
      (g := fun y : ((BitString × ℕ) × ℕ) × BitString => (y.1.2, y.1.1.1, y.2)) uRunOut_primrec
      ((Primrec.snd.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        Primrec.snd))
  have h := list_all_primrec (f := fun x : (BitString × ℕ) × ℕ => allStrings x.1.2)
    (p := fun (x : (BitString × ℕ) × ℕ) (z : BitString) =>
      (conditionalRunOut uCode x.2 x.1.1 z).isSome)
    (allStrings_primrec.comp (Primrec.snd.comp Primrec.fst)) (Primrec.option_isSome.comp hrun)
  exact h.of_eq fun x => rfl

/-- The stage table is primitive recursive in `((p, n), t)`. -/
theorem stageTable_primrec :
    Primrec₂ fun (q : BitString × ℕ) (t : ℕ) => stageTable t q.1 q.2 := by
  have hrun : Primrec₂ fun (x : (BitString × ℕ) × ℕ) (z : BitString) =>
      conditionalRunOut uCode x.2 x.1.1 z :=
    Primrec.comp (f := fun q : ℕ × BitString × BitString => conditionalRunOut uCode q.1 q.2.1 q.2.2)
      (g := fun y : ((BitString × ℕ) × ℕ) × BitString => (y.1.2, y.1.1.1, y.2)) uRunOut_primrec
      ((Primrec.snd.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        Primrec.snd))
  have hg : Primrec₂ fun (x : (BitString × ℕ) × ℕ) (z : BitString) =>
      (z, (conditionalRunOut uCode x.2 x.1.1 z).getD []) :=
    Primrec.snd.pair (Primrec.option_getD.comp hrun (Primrec.const []))
  have h := Primrec.list_map (allStrings_primrec.comp (Primrec.snd.comp Primrec.fst)) hg
  exact h.of_eq fun x => rfl

/-- **Complete runs halt for a total program.**  If `p` halts on every condition, `runTable p n`
is defined.

Proof sketch: for each `z ∈ allStrings n` take a stage `t_z` with
`conditionalRunOut uCode t_z p z = some _` (`conditionalRunOut_complete uCode_spec`); the maximum
`t` of these finitely many stages makes `tableReady t p n = true` (`conditionalRunOut_mono`,
`List.all_eq_true`); then `Nat.rfind_dom` and `Part.map`.
Reference: appendix "The finite procedures used by all decoders" (tex ~2462). -/
theorem runTable_dom {p : BitString} (hp : IsTotalProgram universalDecompressor p) (n : ℕ) :
    (runTable p n).Dom := by
  have hstage : ∀ z : BitString, ∃ t, (conditionalRunOut uCode t p z).isSome = true := by
    intro z
    obtain ⟨t, ht⟩ := conditionalRunOut_complete uCode_spec (Part.get_mem (hp z))
    exact ⟨t, by rw [ht]; rfl⟩
  choose f hf using hstage
  have hready : tableReady ((allStrings n).map f).sum p n = true := by
    unfold tableReady
    rw [List.all_eq_true]
    intro z hz
    have hle : f z ≤ ((allStrings n).map f).sum :=
      List.le_sum_of_mem (List.mem_map.2 ⟨z, hz, rfl⟩)
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hf z)
    rw [conditionalRunOut_mono uCode hle hu]
    rfl
  change (Nat.rfind fun t => Part.some (tableReady t p n)).Dom
  exact Nat.rfind_dom.2 ⟨_, by rw [hready]; exact Part.mem_some true, fun _ => trivial⟩

/-- **Complete runs read back the outputs.**  A table returned by `runTable p n` gives, at every
string of length `n`, the output of `p` there.

Proof sketch: `T = stageTable t p n` with `tableReady t p n = true` (`Nat.rfind_spec`,
`Part.mem_map_iff`); for `z` of length `n`, `conditionalRunOut uCode t p z = some u` with
`u ∈ universalDecompressor (p, z)` (`conditionalRunOut_sound uCode_spec`), so
`progOut p z = u` (`progOut_eq_of_mem`); conclude with `tableOut_outputTable`-style lookup in the
mapped list (`stageTable` is `(allStrings n).map`). -/
theorem tableOut_of_mem_runTable {p : BitString} {n : ℕ} {T : List (BitString × BitString)}
    (hT : T ∈ runTable p n) {z : BitString} (hz : z.length = n) : tableOut T z = progOut p z := by
  obtain ⟨t, ht, rfl⟩ := (Part.mem_map_iff _).1 hT
  have hready : tableReady t p n = true := by
    have h := Nat.rfind_spec ht
    exact (Part.mem_some_iff.1 h).symm
  unfold tableReady at hready
  rw [List.all_eq_true] at hready
  have hsome := hready z ((mem_allStrings n z).2 hz)
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hsome
  have hout : progOut p z = u := progOut_eq_of_mem (conditionalRunOut_sound uCode_spec hu)
  have key := tableOut_outputTable (fun y => (conditionalRunOut uCode t p y).getD []) n hz
  unfold stageTable
  rw [key, hu, hout]
  rfl

/-- **Complete runs are partial recursive.**

Proof sketch: `conditionalRunOut uCode` is primitive recursive in `(t, p, z)`
(`Lower.conditionalRunOut_computable`, or its primrec proof), so `tableReady` and `stageTable` are
primitive recursive (`allStrings_primrec`, `Primrec.list_all`-style `List.all`, `Primrec.list_map`,
`Primrec.option_getD`, `Primrec.option_isSome`); `Partrec.rfind` and `Partrec.map`. -/
theorem runTable_partrec : Partrec₂ runTable := by
  have hrf : Partrec fun q : BitString × ℕ =>
      Nat.rfind fun t => Part.some (tableReady t q.1 q.2) :=
    Partrec.rfind tableReady_primrec.to_comp.partrec₂
  exact (hrf.map stageTable_primrec.to_comp).of_eq fun q => rfl

/-- The shape graph read from two output tables, at data length `n` and buckets `a`, `b`. -/
def tableShape (TA TB : List (BitString × BitString)) (n a b : ℕ) : ShapeParams :=
  ⟨tableOut TA, tableOut TB, n, a, b⟩

/-- **Tables computed by complete runs agree with the witnesses at the data length**, so every
hierarchy object read from the tables is the instance's (`shapeEdges_congr`, `level_congr`,
`children_residual_congr`, `firstResidualBlock_congr`). -/
theorem tableShape_agreeOn {pA pB : BitString} {n a b : ℕ} {TA TB : List (BitString × BitString)}
    (hA : TA ∈ runTable pA n) (hB : TB ∈ runTable pB n) :
    (tableShape TA TB n a b).AgreeOn (instShape pA pB n a b) :=
  ⟨rfl, rfl, rfl, fun _ hz => ⟨tableOut_of_mem_runTable hA hz, tableOut_of_mem_runTable hB hz⟩⟩

/-! ### One global local rank -/

/-- The output of the typed endpoint of an edge `z`: the row output (`side = false`) or the column
output (`side = true`). -/
def sideOut (P : ShapeParams) (side : Bool) (z : BitString) : BitString :=
  if side then P.outB z else P.outA z

/-- The depth-`j` blocks incident to the typed endpoint `(side, w)`, in the order of the global
depth-`j` list. -/
noncomputable def incidentBlocks (P : ShapeParams) (R L j : ℕ) (side : Bool) (w : BitString) :
    List (Finset BitString) :=
  (level P R L j).filter fun F => decide (∃ z ∈ F, sideOut P side z = w)

/-- The block of local rank `s` at the typed endpoint `(side, w)` (default `∅` when the rank is out
of range).  At depth zero the global list is `[G]`, so rank `0` names `G`. -/
noncomputable def localBlock (P : ShapeParams) (R L j : ℕ) (side : Bool) (w : BitString)
    (s : ℕ) : Finset BitString :=
  (incidentBlocks P R L j side w).getD s ∅

/-- **One global local rank** (tex ~362–380).  A depth-`j` block `F` containing an edge `z` is the
local block of some rank `s < 2^(jL+1)` at the typed endpoint of `z` on either side, provided
`jL ≤ a` and `jL ≤ b`.

Proof sketch: `F ∈ incidentBlocks P R L j side (sideOut P side z)` (`List.mem_filter`, witness
`z`); take `s` its index (`List.mem_iff_getElem`, `List.getD_eq_getElem`); the length bound is
`card_rowIncidentBlocks_lt` (`side = false`) or `card_colIncidentBlocks_lt` (`side = true`), after
unfolding `sideOut`. -/
theorem exists_localBlock_index (P : ShapeParams) (R L j : ℕ) (side : Bool) (ha : j * L ≤ P.a)
    (hb : j * L ≤ P.b) {F : Finset BitString} (hF : F ∈ level P R L j) {z : BitString}
    (hz : z ∈ F) :
    ∃ s < 2 ^ (j * L + 1), localBlock P R L j side (sideOut P side z) s = F := by
  have hmem : F ∈ incidentBlocks P R L j side (sideOut P side z) := by
    unfold incidentBlocks
    rw [List.mem_filter]
    exact ⟨hF, decide_eq_true ⟨z, hz, rfl⟩⟩
  obtain ⟨s, hs, hget⟩ := List.mem_iff_getElem.1 hmem
  have hlen : (incidentBlocks P R L j side (sideOut P side z)).length < 2 ^ (j * L + 1) := by
    cases side
    · have h := card_rowIncidentBlocks_lt P R L j ha (P.outA z)
      simpa [incidentBlocks, sideOut] using h
    · have h := card_colIncidentBlocks_lt P R L j hb (P.outB z)
      simpa [incidentBlocks, sideOut] using h
  refine ⟨s, lt_trans hs hlen, ?_⟩
  unfold localBlock
  rw [List.getD_eq_getElem _ _ hs, hget]

/-- **The local block is computable from the tables.**  The canonical code of the local block is
primitive recursive in the two tables, `(n, a, b)`, `(R, L, j)`, the side, the endpoint label and
the rank.

Proof sketch: `level_codes_primrec` (with `fA = tableOut ∘ fst`, `fB = tableOut ∘ snd`, both
`Primrec₂` by `tableOut_primrec`) gives the codes of the depth-`j` list; the incidence test of a
coded block is `List.any` over `canonicalPointListOfCode` of an equality of `tableOut` outputs
(primitive recursive); `primrec_list_filter` and `Primrec.list_getD` with default
`canonicalFiniteSetCode ∅`; rewrite `List.map_filter`/`List.getD_map` and
`parseModel_canonicalFiniteSetCode` with `of_eq`. -/
theorem localBlockCode_primrec :
    Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
        (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × Bool × BitString × ℕ =>
      canonicalFiniteSetCode (localBlock (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2)
        q.2.2.1.1 q.2.2.1.2.1 q.2.2.1.2.2 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  have hA : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.1 z :=
    tableOut_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hB : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.2 z :=
    tableOut_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hlev := level_codes_primrec _ _ hA hB
  have hcodes : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × Bool × BitString × ℕ =>
        (level (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2) q.2.2.1.1 q.2.2.1.2.1
          q.2.2.1.2.2).map canonicalFiniteSetCode :=
    (hlev.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))).of_eq fun q => rfl
  have hsideB : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × Bool × BitString × ℕ => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hw : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × Bool × BitString × ℕ => q.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hs : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × Bool × BitString × ℕ => q.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hside : Primrec₂ fun (q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × Bool × BitString × ℕ) (z : BitString) =>
        sideOut (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2) q.2.2.2.1 z := by
    refine (Primrec.cond (hsideB.comp Primrec.fst)
      (tableOut_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      (tableOut_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)).of_eq fun x => ?_
    rcases x with ⟨⟨T, nab, RLj, side, w, s⟩, z⟩
    cases side <;> rfl
  have htest : Primrec₂ fun (q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × Bool × BitString × ℕ) (c : BitString) =>
        decide (q.2.2.2.2.1 ∈ (canonicalPointListOfCode c).map fun z =>
          sideOut (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2) q.2.2.2.1 z) :=
    bitString_mem_primrec.comp (hw.comp Primrec.fst)
      (Primrec.list_map (canonicalPointListOfCode_primrec.comp Primrec.snd)
        (hside.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
  have hfilt := primrec_list_filter hcodes htest
  have hget := (Primrec.list_getD (canonicalFiniteSetCode (∅ : Finset BitString))).comp hfilt hs
  refine hget.of_eq fun q => ?_
  rw [List.filter_map, List.getD_map]
  unfold localBlock incidentBlocks
  congr 2
  apply List.filter_congr
  intro F _
  apply decide_eq_decide.mpr
  simp only [canonicalPointListOfCode_canonicalFiniteSetCode, List.mem_map,
    mem_canonicalFinsetList]

/-- **Local blocks read from tables are the instance's.**  If the tables are complete runs of
`pA`, `pB` and `w` is any label, the local block read from the tables is the local block of the
instance shape. -/
theorem localBlock_tableShape {pA pB : BitString} {n a b : ℕ}
    {TA TB : List (BitString × BitString)} (hA : TA ∈ runTable pA n) (hB : TB ∈ runTable pB n)
    (R L j : ℕ) (side : Bool) (w : BitString) (s : ℕ) :
    localBlock (tableShape TA TB n a b) R L j side w s =
      localBlock (instShape pA pB n a b) R L j side w s := by
  have hag := tableShape_agreeOn (a := a) (b := b) hA hB
  have hside : ∀ z : BitString, z.length = n →
      sideOut (tableShape TA TB n a b) side z = sideOut (instShape pA pB n a b) side z := by
    intro z hz
    obtain ⟨h1, h2⟩ := hag.2.2.2 z hz
    unfold sideOut
    split
    · exact h2
    · exact h1
  unfold localBlock incidentBlocks
  rw [level_congr hag R L j]
  congr 1
  apply List.filter_congr
  intro F hF
  have hlen := length_eq_of_mem_level (instShape pA pB n a b) R L j hF
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨z, hz, hzw⟩
    exact ⟨z, hz, by rw [← hside z (hlen z hz)]; exact hzw⟩
  · rintro ⟨z, hz, hzw⟩
    exact ⟨z, hz, by rw [hside z (hlen z hz)]; exact hzw⟩

/-! ### Header costs -/

/-- The header cost of a list of numeric packet fields: `∑ ⌈log₂ (k + 2)⌉`. -/
def hdrCost (ks : List ℕ) : ℕ :=
  (ks.map headerLog).sum

end Kolmogorov.StrongMerging.Upper
