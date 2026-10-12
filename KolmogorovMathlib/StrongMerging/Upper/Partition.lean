import KolmogorovMathlib.StrongMerging.Upper.Partition.Cells

/-!
# The uniform partition version (blueprint H08, `UpperHierarchyPartition`)

`sublinear-merging.tex`, Corollary `cor:partition` (section "A uniform partition version",
tex ~550–608).  The point selector of H05 is changed in two places, as in the paper:

* in the hierarchy branch the selector returns the first residual `L_F` containing the input
  (`residualCell`), not its parent `F`;
* in the small-degree branch it returns a star of the shape graph (`shapeStar`): the column star
  of `p_B(z)` if `a ≤ b`, the row star of `p_A(z)` if `a > b` (the tie rule reads only the bucket
  exponents).  The singleton defaults are kept.

The cell is `partCell fA fB c₂ R e z`, generic in the two output maps: `partModelAt` reads the
witnesses (`progOut`), `partCellT` reads two output tables, and `partModel` uses a rule
`R = clipR n (ρ n e)`.

Main steps.
1. **Partition identity** (`partModel_partition`): every cell contains its input
   (`mem_partCell_self`) and a member `y` of the cell of `z` has the same length and the same cell
   (`partCell_eq_of_mem`).  A member of a non-default cell is a shape edge of `z`'s shape, so it
   has the same shape parameters (`mem_shapeEdges_pointShape`); residuals of distinct listed
   blocks are disjoint (`disjoint_residual_of_mem_blockPairs`), so the residual containing it is
   unique (`firstResidualBlock_eq_of_mem`).
2. **The program** (`exists_partitionProgram`): the selector program `partDecoder` reads the
   packet `selPacket h e p_A p_B` of H05, computes both output tables by complete runs and returns
   the code of the table cell; it is total on every input for total witnesses.
3. **Cells inside the old selection** (`partModelAt_subset_selectModelAt`): the new cell is a
   subset of H05's selection `F`, and at a calibrated instance `CT(D | F) = O(H)`
   (`cellTotalC_le`) by one total cell-from-parent decoder (`cellDecoder`, packet `cellPacket`).
4. **Raw bounds by transfer** (`rawBounds_of_subset`): H05's selection has the raw bounds of
   `Upper.Tradeoff` (`rawBounds_small`, `rawBounds_big`); a subset `D ∋ x` with `CT(D | F) = O(H)`
   inherits them (`C(D) ≤ C(F) + O(H)`, `log |D| ≤ log |F|`, and composition of total programs).
5. **Assembly** (`partition_core`, `exists_partition_selector_tradeoff'`): the tradeoff constant
   is fixed from the hardwired-`R` point bound `CT(D | x) ≤ (18 + c_P) H`, before the rule; only
   the program-length constant `c_ρ` depends on the rule (auditor's K1).  The mass bound is the
   unchanged common-information argument `tradeoffBounds_of_raw`.

The final theorem `Upper.exists_partition_selector_tradeoff'` has exactly the type of the frozen
`exists_partition_selector_tradeoff` of `StrongMerging.StatementsExtra` (whose definitions it reads
from `StrongMerging.ExtraDefs`).  Everything is proved; the helpers live in the sub-namespace
`Upper.Partition`.

The first part of the development is in `KolmogorovMathlib.StrongMerging.Upper.Partition.Cells`,
imported here.
-/

namespace Kolmogorov.StrongMerging.Upper

namespace Partition

/-! ### The partition selector program -/

/-- The output of the partition selector program from its decoded packet `(h, e, p_A, p_B)` on
the input `z`: complete runs of both witnesses at length `|z|`, then the table cell at the
clipped exponent `R = clipR |z| (ρ |z| e h)`. -/
noncomputable def partOut (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ → ℕ) (h e : ℕ) (pA pB z : BitString) :
    Part BitString :=
  (runTable pA z.length).bind fun TA => (runTable pB z.length).map fun TB =>
    canonicalFiniteSetCode (partCellT c₂ (clipR z.length (ρ z.length e h)) e TA TB z)

/-- **The literal partition selector program** (`cor:partition`, tex ~579), as a machine reading
the packet `selPacket h e p_A p_B` of H05 and the input `z`. -/
noncomputable def partDecoder (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ → ℕ) : Map := fun q =>
  partOut c₂ ρ (numFieldDecode q.1).1 (numFieldDecode (numFieldDecode q.1).2).1
    (decodeTotalProgramPairFirst (numFieldDecode (numFieldDecode q.1).2).2)
    (decodeTotalProgramPairSecond (numFieldDecode (numFieldDecode q.1).2).2) q.2

/-- **The partition selector program is partial recursive** for a computable rule (the proof of
`selectorDecoder_partrec`, with the table cell `partCellT_code_primrec`). -/
theorem partDecoder_partrec (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ → ℕ)
    (hρ : Computable fun q : ℕ × ℕ × ℕ => ρ q.1 q.2.1 q.2.2) :
    isDecompressor (partDecoder c₂ ρ) := by
  have hrest : Computable fun q : BitString × BitString => (numFieldDecode q.1).2 :=
    Computable.snd.comp (numFieldDecode_computable.comp Computable.fst)
  have hh : Computable fun q : BitString × BitString => (numFieldDecode q.1).1 :=
    Computable.fst.comp (numFieldDecode_computable.comp Computable.fst)
  have he : Computable fun q : BitString × BitString =>
      (numFieldDecode (numFieldDecode q.1).2).1 :=
    Computable.fst.comp (numFieldDecode_computable.comp hrest)
  have hbody : Computable fun q : BitString × BitString =>
      (numFieldDecode (numFieldDecode q.1).2).2 :=
    Computable.snd.comp (numFieldDecode_computable.comp hrest)
  have hpA := decodeTotalProgramPairFirst_computable.comp hbody
  have hpB := decodeTotalProgramPairSecond_computable.comp hbody
  have hlen : Computable fun q : BitString × BitString => q.2.length :=
    (Primrec.list_length.comp Primrec.snd).to_comp
  have hfst : Computable fun r : (BitString × BitString) × List (BitString × BitString) => r.1 :=
    Computable.fst
  have hR : Computable fun q : BitString × BitString =>
      clipR q.2.length (ρ q.2.length (numFieldDecode (numFieldDecode q.1).2).1
        (numFieldDecode q.1).1) :=
    clipR_primrec.to_comp.comp hlen (hρ.comp (hlen.pair (he.pair hh)))
  have hfinal : Computable₂ fun (r : (BitString × BitString) × List (BitString × BitString))
      (TB : List (BitString × BitString)) =>
      canonicalFiniteSetCode (partCellT c₂ (clipR r.1.2.length (ρ r.1.2.length
        (numFieldDecode (numFieldDecode r.1.1).2).1 (numFieldDecode r.1.1).1))
        (numFieldDecode (numFieldDecode r.1.1).2).1 r.2 TB r.1.2) :=
    (partCellT_code_primrec.to_comp.comp
      (((Computable.const c₂).pair ((hR.comp (Computable.fst.comp Computable.fst)).pair
        (he.comp (Computable.fst.comp Computable.fst)))).pair
        (((Computable.snd.comp Computable.fst).pair Computable.snd).pair
          (Computable.snd.comp (Computable.fst.comp Computable.fst))))).of_eq fun _ => rfl
  have hinner : Partrec₂ fun (r : BitString × BitString) (TA : List (BitString × BitString)) =>
      (runTable (decodeTotalProgramPairSecond (numFieldDecode (numFieldDecode r.1).2).2)
        r.2.length).map fun TB =>
        canonicalFiniteSetCode (partCellT c₂ (clipR r.2.length (ρ r.2.length
          (numFieldDecode (numFieldDecode r.1).2).1 (numFieldDecode r.1).1))
          (numFieldDecode (numFieldDecode r.1).2).1 TA TB r.2) :=
    Partrec.map (runTable_partrec.comp (hpB.comp hfst) (hlen.comp hfst)) hfinal
  exact (Partrec.bind (runTable_partrec.comp hpA hlen) hinner).of_eq fun q => rfl

/-- **The partition selector program on its packet.**  For total witnesses the program halts on
every input `z` and returns the code of the cell `partModel c₂ (ρ · · h) p_A p_B e z`; totality
uses only witness totality (`runTable_dom`). -/
theorem partDecoder_spec (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ → ℕ) (h e : ℕ) (pA pB z : BitString)
    (hpA : IsTotalProgram universalDecompressor pA)
    (hpB : IsTotalProgram universalDecompressor pB) :
    partDecoder c₂ ρ (selPacket h e pA pB, z) =
      Part.some (canonicalFiniteSetCode (partModel c₂ (fun n e => ρ n e h) pA pB e z)) := by
  obtain ⟨TA, hTA⟩ := Part.dom_iff_mem.mp (runTable_dom hpA z.length)
  obtain ⟨TB, hTB⟩ := Part.dom_iff_mem.mp (runTable_dom hpB z.length)
  have hsel := partCellT_eq hTA hTB c₂ (clipR z.length (ρ z.length e h)) e
  unfold partDecoder partOut
  simp only [selPacket, pointPacket, numFieldDecode_numField, decodeTotalProgramPairFirst_pair,
    decodeTotalProgramPairSecond_pair]
  rw [Part.eq_some_iff, Part.mem_bind_iff]
  refine ⟨TA, hTA, ?_⟩
  rw [Part.mem_map_iff]
  refine ⟨TB, hTB, ?_⟩
  rw [hsel]
  rfl

/-- **The partition selector program** (`cor:partition`, tex ~600: "the new point algorithm is
still total and has length `O(e + 1)`").  For the hierarchy step `c₂` and a computable rule
`ρ n e h` there is `c` such that for total witnesses of length `≤ e` and every packet number `h`
one total program `q` of length `≤ 7 (e + 1) + 4 ⌈log₂ (h + 2)⌉ + c` outputs on every input `z`
the code of the cell `partModel c₂ (ρ · · h) p_A p_B e z`. -/
theorem exists_partitionProgram (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ → ℕ)
    (hρ : Computable fun q : ℕ × ℕ × ℕ => ρ q.1 q.2.1 q.2.2) :
    ∃ c : ℕ, ∀ (pA pB : BitString) (e h : ℕ),
      IsTotalProgram universalDecompressor pA → IsTotalProgram universalDecompressor pB →
      pA.length ≤ e → pB.length ≤ e →
      ∃ q : BitString, q.length ≤ 7 * (e + 1) + 4 * headerLog h + c ∧
        IsTotalProgram universalDecompressor q ∧
        ∀ z : BitString, produces universalDecompressor q z
          (canonicalFiniteSetCode (partModel c₂ (fun n e => ρ n e h) pA pB e z)) := by
  obtain ⟨pre, hpre⟩ := exists_prefix_universalDecompressor_eq (partDecoder c₂ ρ)
    (partDecoder_partrec c₂ ρ hρ)
  refine ⟨pre.length, fun pA pB e h hpA hpB hA hB => ⟨pre ++ selPacket h e pA pB, ?_, ?_, ?_⟩⟩
  · rw [List.length_append]
    have := length_selPacket_le h e pA pB hA hB
    omega
  · intro y
    rw [hpre, partDecoder_spec c₂ ρ h e pA pB y hpA hpB]
    trivial
  · intro z
    change _ ∈ universalDecompressor (pre ++ selPacket h e pA pB, z)
    rw [hpre, partDecoder_spec c₂ ρ h e pA pB z hpA hpB]
    exact Part.mem_some _

/-! ### The cell-from-parent decoder -/

/-- The cell computed from its parent model `parseModel w`: in mode `0` the residual of the
depth-`j` block `parseModel w` (hierarchy branch), in mode `2` the column star of `w`, in any other
mode the row star of `w` (small-degree branch). -/
noncomputable def cellOfParent (P : ShapeParams) (R L j mode : ℕ) (w : BitString) :
    Finset BitString :=
  if mode = 0 then residual P R L j (parseModel w) else shapeStar P (decide (mode = 2)) w

/-- The packet of the cell decoder: numeric fields `n, a, b, R, L, j, mode` and the two witness
bodies. -/
def cellPacket (n a b R L j mode : ℕ) (pA pB : BitString) : BitString :=
  numPacket [n, a, b, R, L, j, mode] (totalProgramPairCode pA pB)

/-- The output of the cell decoder from decoded fields `ks = [n, a, b, R, L, j, mode]`, the two
witness bodies and the condition `w`: complete runs at length `n`, then the cell read from the
tables. -/
noncomputable def cellOut (ks : List ℕ) (pA pB w : BitString) : Part BitString :=
  (runTable pA (ks.getD 0 0)).bind fun TA => (runTable pB (ks.getD 0 0)).map fun TB =>
    canonicalFiniteSetCode (cellOfParent (tableShape TA TB (ks.getD 0 0) (ks.getD 1 0)
      (ks.getD 2 0)) (ks.getD 3 0) (ks.getD 4 0) (ks.getD 5 0) (ks.getD 6 0) w)

/-- **The total cell-from-parent decoder** (tex ~598–606: "given `F` and `O(H)` bits of global
parameters and depth, compute its residual by finite search"; "the selected star … is totally
computable from it using `O(H)` advice"). -/
noncomputable def cellDecoder : Map := fun q =>
  cellOut (decodeFields 7 q.1).1 (decodeTotalProgramPairFirst (decodeFields 7 q.1).2)
    (decodeTotalProgramPairSecond (decodeFields 7 q.1).2) q.2

/-- **The cell code is primitive recursive in the tables and the fields.**

Proof: `Primrec.ite` on `mode = 0`; the residual branch is `residual_code_primrec` with
`fA = tableOut ∘ fst`, `fB = tableOut ∘ snd` (`tableOut_primrec`); the star branch is
`shapeStarCode_primrec` with side `decide (mode = 2)` (`Primrec.eq`). -/
theorem cellOfParentCode_primrec :
    Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
        (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × ℕ × BitString =>
      canonicalFiniteSetCode (cellOfParent (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2)
        q.2.2.1.1 q.2.2.1.2.1 q.2.2.1.2.2 q.2.2.2.1 q.2.2.2.2) := by
  have hA : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.1 z :=
    tableOut_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hB : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.2 z :=
    tableOut_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hin : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × ℕ × BitString => ((q.1, q.2.1, q.2.2.1), q.2.2.2.2) :=
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).pair
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hres := (residual_code_primrec _ _ hA hB).comp hin
  have hmode : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × ℕ × BitString => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hw : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × ℕ × BitString => q.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hside := Primrec.eq.decide.comp hmode (Primrec.const 2)
  have hstar := shapeStarCode_primrec.comp
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (hside.pair hw)))
  have hzero : PrimrecPred fun q : (List (BitString × BitString) ×
      List (BitString × BitString)) × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × ℕ × BitString =>
      q.2.2.2.1 = 0 := Primrec.eq.comp hmode (Primrec.const 0)
  refine (Primrec.ite hzero hres hstar).of_eq fun q => ?_
  unfold cellOfParent
  split_ifs <;> rfl

/-- The parameter tuple of the cell code read from a packet-and-condition `q` and the two tables:
`((TA, TB), (n, a, b), (R, L, j), mode, w)`. -/
def cellTuple (q : BitString × BitString) (TA TB : List (BitString × BitString)) :
    (List (BitString × BitString) × List (BitString × BitString)) × (ℕ × ℕ × ℕ) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString :=
  ((TA, TB), ((decodeFields 7 q.1).1.getD 0 0, (decodeFields 7 q.1).1.getD 1 0,
      (decodeFields 7 q.1).1.getD 2 0),
    ((decodeFields 7 q.1).1.getD 3 0, (decodeFields 7 q.1).1.getD 4 0,
      (decodeFields 7 q.1).1.getD 5 0),
    (decodeFields 7 q.1).1.getD 6 0, q.2)

/-- The cell code as a function of the parameter tuple. -/
noncomputable def cellCode (q : (List (BitString × BitString) × List (BitString × BitString)) ×
    (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × ℕ × BitString) : BitString :=
  canonicalFiniteSetCode (cellOfParent (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2)
    q.2.2.1.1 q.2.2.1.2.1 q.2.2.1.2.2 q.2.2.2.1 q.2.2.2.2)

/-- Packet parsing into the cell tuple is computable. -/
theorem cellTuple_computable :
    Computable fun x : ((BitString × BitString) × List (BitString × BitString)) ×
        List (BitString × BitString) => cellTuple x.1.1 x.1.2 x.2 := by
  have hdf : Computable fun q : BitString × BitString => decodeFields 7 q.1 :=
    decodeFields_computable.comp (Computable.const 7) Computable.fst
  have hks : Computable fun q : BitString × BitString => (decodeFields 7 q.1).1 :=
    Computable.fst.comp hdf
  have hget : ∀ i : ℕ, Computable fun q : BitString × BitString =>
      (decodeFields 7 q.1).1.getD i 0 :=
    fun i => (Primrec.list_getD 0).to_comp.comp hks (Computable.const i)
  have hpar : Computable fun q : BitString × BitString =>
      (((decodeFields 7 q.1).1.getD 0 0, (decodeFields 7 q.1).1.getD 1 0,
        (decodeFields 7 q.1).1.getD 2 0),
        ((decodeFields 7 q.1).1.getD 3 0, (decodeFields 7 q.1).1.getD 4 0,
          (decodeFields 7 q.1).1.getD 5 0),
        (decodeFields 7 q.1).1.getD 6 0, q.2) :=
    ((hget 0).pair ((hget 1).pair (hget 2))).pair (((hget 3).pair ((hget 4).pair (hget 5))).pair
      ((hget 6).pair Computable.snd))
  exact (((Computable.snd.comp Computable.fst).pair Computable.snd).pair
    (hpar.comp (Computable.fst.comp Computable.fst))).of_eq fun x => rfl

/-- **The cell decoder is partial recursive** (as `localBlockDecoder_partrec`): computable packet
parsing (`cellTuple_computable`), two complete runs (`runTable_partrec`, `Partrec.bind`,
`Partrec.map`) and the primitive recursive cell code (`cellOfParentCode_primrec`). -/
theorem cellDecoder_partrec : isDecompressor cellDecoder := by
  have hdf : Computable fun q : BitString × BitString => decodeFields 7 q.1 :=
    decodeFields_computable.comp (Computable.const 7) Computable.fst
  have hn : Computable fun q : BitString × BitString => (decodeFields 7 q.1).1.getD 0 0 :=
    (Primrec.list_getD 0).to_comp.comp (Computable.fst.comp hdf) (Computable.const 0)
  have hpA : Computable fun q : BitString × BitString =>
      decodeTotalProgramPairFirst (decodeFields 7 q.1).2 :=
    decodeTotalProgramPairFirst_computable.comp (Computable.snd.comp hdf)
  have hpB : Computable fun q : BitString × BitString =>
      decodeTotalProgramPairSecond (decodeFields 7 q.1).2 :=
    decodeTotalProgramPairSecond_computable.comp (Computable.snd.comp hdf)
  have hcode : Computable cellCode := cellOfParentCode_primrec.to_comp
  have hcore : Computable₂ fun (p : (BitString × BitString) × List (BitString × BitString))
      (TB : List (BitString × BitString)) => cellCode (cellTuple p.1 p.2 TB) :=
    hcode.comp cellTuple_computable
  have hinner : Partrec₂ fun (q : BitString × BitString) (TA : List (BitString × BitString)) =>
      (runTable (decodeTotalProgramPairSecond (decodeFields 7 q.1).2)
        ((decodeFields 7 q.1).1.getD 0 0)).map fun TB => cellCode (cellTuple q TA TB) :=
    Partrec.map (runTable_partrec.comp (hpB.comp Computable.fst) (hn.comp Computable.fst)) hcore
  refine (Partrec.bind (runTable_partrec.comp hpA hn) hinner).of_eq fun q => ?_
  simp only [cellDecoder, cellOut, cellCode, cellTuple]

/-- The cell decoder on a cell packet: complete runs at length `n`, then the table cell. -/
theorem cellDecoder_packet (n a b R L j mode : ℕ) (pA pB w : BitString) :
    cellDecoder (cellPacket n a b R L j mode pA pB, w) =
      (runTable pA n).bind fun TA => (runTable pB n).map fun TB =>
        canonicalFiniteSetCode (cellOfParent (tableShape TA TB n a b) R L j mode w) := by
  have hfields : decodeFields 7 (cellPacket n a b R L j mode pA pB) =
      ([n, a, b, R, L, j, mode], totalProgramPairCode pA pB) :=
    decodeFields_numPacket [n, a, b, R, L, j, mode] _
  simp only [cellDecoder, cellOut, hfields, decodeTotalProgramPairFirst_pair,
    decodeTotalProgramPairSecond_pair, List.getD_cons_zero, List.getD_cons_succ]

/-- **Cells from a parent only read outputs at the data length** (in mode `0` for a parent of
strings of length `n`): `children_residual_congr` and `shapeStar_congr`. -/
theorem cellOfParent_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (R L j mode : ℕ)
    {w : BitString} (hw : mode = 0 → ∀ y ∈ parseModel w, y.length = P.n) :
    cellOfParent P R L j mode w = cellOfParent Q R L j mode w := by
  unfold cellOfParent
  split_ifs with hm
  · exact (children_residual_congr h R L j (hw hm)).2
  · exact shapeStar_congr h _ w

/-- The cell decoder returns the instance's cell (in mode `0` for a parent of strings of length
`n`). -/
theorem cellDecoder_mem (n a b R L j mode : ℕ) (pA pB w : BitString)
    (hpA : IsTotalProgram universalDecompressor pA)
    (hpB : IsTotalProgram universalDecompressor pB)
    (hw : mode = 0 → ∀ y ∈ parseModel w, y.length = n) :
    canonicalFiniteSetCode (cellOfParent (instShape pA pB n a b) R L j mode w) ∈
      cellDecoder (cellPacket n a b R L j mode pA pB, w) := by
  obtain ⟨TA, hTA⟩ := Part.dom_iff_mem.mp (runTable_dom hpA n)
  obtain ⟨TB, hTB⟩ := Part.dom_iff_mem.mp (runTable_dom hpB n)
  rw [cellDecoder_packet]
  refine Part.mem_bind_iff.mpr ⟨TA, hTA, (Part.mem_map_iff _).mpr ⟨TB, hTB, ?_⟩⟩
  rw [cellOfParent_congr (tableShape_agreeOn (a := a) (b := b) hTA hTB) R L j mode hw]

/-- **Cell packet length.**  The seven numeric fields cost at most four header units each and the
two framed bodies `|p_A| + |p_B| + 3 ⌈log₂ (|p_A| + 2)⌉`.

Proof: as `length_localPacket_le` (whose helper `length_numPacket_le_four` is private in
`Upper.Decoders`): each numeric field costs at most four header units
(`length_totalProgramPairCode`, `Nat.size_eq_bits_len`, `one_le_headerLog`), then `hdrCost` is
unfolded on the explicit list and `omega` concludes. -/
theorem length_cellPacket_le (n a b R L j mode : ℕ) (pA pB : BitString) :
    (cellPacket n a b R L j mode pA pB).length ≤
      pA.length + pB.length + 4 * hdrCost [n, a, b, R, L, j, pA.length, pB.length] +
        4 * headerLog mode := by
  have hbits : ∀ k : ℕ, (Nat.bits k).length ≤ headerLog k := fun k => by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    unfold headerLog
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_pow_clog one_lt_two (k + 2))
  have hss : ∀ k : ℕ, (Nat.bits (Nat.bits k).length).length ≤ (Nat.bits k).length := fun k => by
    rw [Nat.size_eq_bits_len (Nat.bits k).length]
    exact Nat.size_le.2 Nat.lt_two_pow_self
  have hfield : ∀ (k : ℕ) (rest : BitString),
      (numField k rest).length ≤ rest.length + 4 * headerLog k := by
    intro k rest
    unfold numField
    rw [length_totalProgramPairCode]
    have := hbits k
    have := hss k
    have := one_le_headerLog k
    omega
  have hpair : (totalProgramPairCode pA pB).length ≤
      pA.length + pB.length + 3 * headerLog pA.length := by
    rw [length_totalProgramPairCode]
    have := hbits pA.length
    have := hss pA.length
    have := one_le_headerLog pA.length
    omega
  have hc : hdrCost [n, a, b, R, L, j, pA.length, pB.length] = headerLog n + headerLog a +
      headerLog b + headerLog R + headerLog L + headerLog j + headerLog pA.length +
        headerLog pB.length := by
    simp only [hdrCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  unfold cellPacket numPacket
  simp only [List.foldr_cons, List.foldr_nil]
  have h7 := hfield mode (totalProgramPairCode pA pB)
  have h6 := hfield j (numField mode (totalProgramPairCode pA pB))
  have h5 := hfield L (numField j (numField mode (totalProgramPairCode pA pB)))
  have h4 := hfield R (numField L (numField j (numField mode (totalProgramPairCode pA pB))))
  have h3 := hfield b
    (numField R (numField L (numField j (numField mode (totalProgramPairCode pA pB)))))
  have h2 := hfield a (numField b
    (numField R (numField L (numField j (numField mode (totalProgramPairCode pA pB))))))
  have h1 := hfield n (numField a (numField b
    (numField R (numField L (numField j (numField mode (totalProgramPairCode pA pB)))))))
  have := one_le_headerLog pB.length
  rw [hc]
  omega

/-- **The cell-from-parent bound** (tex ~598–606).  There is `c` such that for total witnesses
the cell computed from a parent code `w` has `CT(cell | w) ≤ |p_A| + |p_B| +
4 hdrCost [n, a, b, R, L, j, |p_A|, |p_B|] + 4 ⌈log₂ (mode + 2)⌉ + c` (in mode `0` for a parent of
strings of length `n`). -/
theorem cellOfParent_totalC :
    ∃ c : ℕ, ∀ (pA pB : BitString) (n a b R L j mode : ℕ) (w : BitString),
      IsTotalProgram universalDecompressor pA → IsTotalProgram universalDecompressor pB →
      (mode = 0 → ∀ y ∈ parseModel w, y.length = n) →
      totalC (canonicalFiniteSetCode (cellOfParent (instShape pA pB n a b) R L j mode w)) w ≤
        ((pA.length + pB.length + 4 * hdrCost [n, a, b, R, L, j, pA.length, pB.length] +
          4 * headerLog mode + c : ℕ) : ℝ) := by
  obtain ⟨c, hc⟩ := totalC_le_of_decoder cellDecoder cellDecoder_partrec
  refine ⟨c, fun pA pB n a b R L j mode w hpA hpB hw => ?_⟩
  -- the cell decoder halts on every condition for total witnesses
  have htot : ∀ y, (cellDecoder (cellPacket n a b R L j mode pA pB, y)).Dom := by
    intro y
    obtain ⟨TA, hTA⟩ := Part.dom_iff_mem.mp (runTable_dom hpA n)
    obtain ⟨TB, hTB⟩ := Part.dom_iff_mem.mp (runTable_dom hpB n)
    rw [cellDecoder_packet]
    exact Part.dom_iff_mem.mpr ⟨_, Part.mem_bind_iff.mpr
      ⟨TA, hTA, (Part.mem_map_iff _).mpr ⟨TB, hTB, rfl⟩⟩⟩
  have h1 := hc _ htot w _ (cellDecoder_mem n a b R L j mode pA pB w hpA hpB hw)
  have h2 := length_cellPacket_le n a b R L j mode pA pB
  have h2' : ((cellPacket n a b R L j mode pA pB).length : ℝ) ≤
      ((pA.length + pB.length + 4 * hdrCost [n, a, b, R, L, j, pA.length, pB.length] +
        4 * headerLog mode : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h2' ⊢
  linarith

/-- The cell in mode `2` is the column star. -/
theorem cellOfParent_two (P : ShapeParams) (R L j : ℕ) (w : BitString) :
    cellOfParent P R L j 2 w = shapeStar P true w := by
  simp [cellOfParent]

/-- The cell in mode `1` is the row star. -/
theorem cellOfParent_one (P : ShapeParams) (R L j : ℕ) (w : BitString) :
    cellOfParent P R L j 1 w = shapeStar P false w := by
  simp [cellOfParent]

/-- The cell in mode `0` from the code of a block is its residual. -/
theorem cellOfParent_zero (P : ShapeParams) (R L j : ℕ) (F : Finset BitString) :
    cellOfParent P R L j 0 (canonicalFiniteSetCode F) = residual P R L j F := by
  simp [cellOfParent, parseModel_canonicalFiniteSetCode]

/-- `⌈log₂ (mode + 2)⌉ ≤ 2` for `mode ≤ 2`. -/
theorem headerLog_le_two {mode : ℕ} (hm : mode ≤ 2) : headerLog mode ≤ 2 := by
  have h2 : headerLog 2 = 2 := by
    unfold headerLog
    rw [show (2 + 2 : ℕ) = 2 ^ 2 by norm_num, Nat.clog_pow 2 2 one_lt_two]
  have := Nat.clog_mono_right 2 (show mode + 2 ≤ 2 + 2 by omega)
  unfold headerLog at h2 ⊢
  omega

/-! ### The analytic transfer from the old selection -/

/-- **Score transfer to a subset** (tex ~598: `C(L_F) ≤ C(F) + O(H)`, `|L_F| ≤ |F|`).  There is
`c` such that for `x ∈ D ⊆ F`,
`Score(D, x) ≤ Score(F, x) + CT(D | F) + c log₂ (C(F) + CT(D | F) + 2) + c`.

Proof: `C(D) ≤ C(F) + C(D | F) + c₃ log₂ (C(F) + C(D | F) + 2)`
(`upperComplexityChain_trans` with the empty condition, `plainC_eq_condC_nil`);
`C(D | F) ≤ CT(D | F) + c_t` (`condC_le_totalC_add`), and
`log₂ (s + c_t + 2) ≤ log₂ (s + 2) + log₂ (c_t + 1)` (as in `totalC_fallback_le`); finally
`log₂ |D| ≤ log₂ |F|` from `1 ≤ |D| ≤ |F|` (`Finset.card_le_card`, `Real.logb_le_logb_of_le`).
Take `c = c₃ + c_t + c₃ ⌈log₂ (c_t + 1)⌉₊`; the logarithm is `≥ 1` (`one_le_logb_add_two`). -/
theorem modelScore_le_of_subset (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (D F : Finset BitString), x ∈ D → D ⊆ F →
      modelScore V D x ≤ modelScore V F x + setTotalC D F +
        c * Real.logb 2 (setC V F + setTotalC D F + 2) + c := by
  obtain ⟨c₃, h₃⟩ := upperComplexityChain_trans V hV
  obtain ⟨ct, hct⟩ := condC_le_totalC_add V hV
  refine ⟨c₃ + ct + c₃ * ⌈Real.logb 2 ((ct : ℝ) + 1)⌉₊, fun x D F hxD hDF => ?_⟩
  have hchain := h₃ (canonicalFiniteSetCode D) (canonicalFiniteSetCode F) []
  simp only [← plainC_eq_condC_nil] at hchain
  have hDF' := hct (canonicalFiniteSetCode D) (canonicalFiniteSetCode F)
  have hF0 := plainC_nonneg V (canonicalFiniteSetCode F)
  have hd0 := condC_nonneg V (canonicalFiniteSetCode D) (canonicalFiniteSetCode F)
  have hT0 := totalC_nonneg (canonicalFiniteSetCode D) (canonicalFiniteSetCode F)
  have hct0 : (0 : ℝ) ≤ ct := Nat.cast_nonneg ct
  have hc₃0 : (0 : ℝ) ≤ c₃ := Nat.cast_nonneg c₃
  have hlog : Real.logb 2 (plainC V (canonicalFiniteSetCode F) +
      condC V (canonicalFiniteSetCode D) (canonicalFiniteSetCode F) + 2) ≤
      Real.logb 2 (plainC V (canonicalFiniteSetCode F) +
        totalC (canonicalFiniteSetCode D) (canonicalFiniteSetCode F) + 2) +
        Real.logb 2 ((ct : ℝ) + 1) := by
    rw [← Real.logb_mul (by positivity) (by positivity)]
    apply Real.logb_le_logb_of_le one_lt_two (by positivity)
    nlinarith [mul_nonneg (add_nonneg hF0 hT0) hct0]
  have hceil : Real.logb 2 ((ct : ℝ) + 1) ≤ ⌈Real.logb 2 ((ct : ℝ) + 1)⌉₊ := Nat.le_ceil _
  have hL1 := one_le_logb_add_two (add_nonneg hF0 hT0)
  have hcard : Real.logb 2 D.card ≤ Real.logb 2 F.card := by
    apply Real.logb_le_logb_of_le one_lt_two
    · exact_mod_cast Finset.card_pos.mpr ⟨x, hxD⟩
    · exact_mod_cast Finset.card_le_card hDF
  have m1 := mul_le_mul_of_nonneg_left hlog hc₃0
  have m2 := mul_le_mul_of_nonneg_left hceil hc₃0
  have hrest : (0 : ℝ) ≤ ((ct : ℝ) + c₃ * ⌈Real.logb 2 ((ct : ℝ) + 1)⌉₊) *
      Real.logb 2 (plainC V (canonicalFiniteSetCode F) +
        totalC (canonicalFiniteSetCode D) (canonicalFiniteSetCode F) + 2) :=
    mul_nonneg (by positivity) (by linarith)
  unfold modelScore setC setTotalC
  push_cast
  nlinarith

/-- **Logarithms of quadratic arguments are `O(H)`**: for every `β` there is `k` with
`log₂ (β (n + 1)² + 2) ≤ k H` for all `n, e`.

Proof: `β (n + 1)² + 2 ≤ (β (n + 1) + 2)²`, so the logarithm is at most
`2 log₂ (β (n + 1) + 2)` (`Real.logb_le_logb_of_le`, `Real.logb_pow`/`Real.logb_mul`), and
`logb_le_baseBudget β` gives `k₀`; take `k = 2 k₀`. -/
theorem logb_quad_le_baseBudget (β : ℕ) :
    ∃ k : ℕ, ∀ n e : ℕ, Real.logb 2 ((β : ℝ) * (n + 1) ^ 2 + 2) ≤ k * baseBudget n e := by
  obtain ⟨k₀, hk₀⟩ := logb_le_baseBudget β
  refine ⟨2 * k₀, fun n e => ?_⟩
  have hb : (0 : ℝ) ≤ β := Nat.cast_nonneg β
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < (β : ℝ) * (n + 1) ^ 2 + 2 := by positivity
  have hy : (0 : ℝ) < (β : ℝ) * (n + 1) + 2 := by positivity
  have hle : (β : ℝ) * (n + 1) ^ 2 + 2 ≤ ((β : ℝ) * (n + 1) + 2) ^ 2 := by
    rcases Nat.eq_zero_or_pos β with hβ | hβ
    · subst hβ
      norm_num
    · have hβ1 : (1 : ℝ) ≤ β := by exact_mod_cast hβ
      have hm : (0 : ℝ) ≤ ((β : ℝ) - 1) * β * (n + 1) ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) hb) (by positivity)
      nlinarith [mul_nonneg hb hn]
  have h1 : Real.logb 2 ((β : ℝ) * (n + 1) ^ 2 + 2) ≤
      Real.logb 2 (((β : ℝ) * (n + 1) + 2) ^ 2) :=
    Real.logb_le_logb_of_le one_lt_two hpos hle
  have h2 : Real.logb 2 (((β : ℝ) * (n + 1) + 2) ^ 2) =
      2 * Real.logb 2 ((β : ℝ) * (n + 1) + 2) := by
    rw [sq, Real.logb_mul hy.ne' hy.ne']
    ring
  have h3 := hk₀ n e
  push_cast
  linarith

/-- The depth loss `JL = (⌊n / R⌋ + 1) c₂ H` is at most `2 c₂ (n + 1)²` (for `e ≤ n`, `n ≥ 2`). -/
theorem depthLoss_le_quad {n e R c₂ : ℕ} (hn : 2 ≤ n) (he : e ≤ n) :
    (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) ≤ 2 * (c₂ : ℝ) * ((n : ℝ) + 1) ^ 2 := by
  have hH := (baseBudget_bounds hn he).2
  have h1 : n / R + 1 ≤ n + 1 := by
    have := Nat.div_le_self n R
    omega
  have h2 : c₂ * baseBudget n e ≤ 2 * c₂ * (n + 1) := by
    calc c₂ * baseBudget n e ≤ c₂ * (2 * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * c₂ * (n + 1) := by ring
  have h3 : (n / R + 1) * (c₂ * baseBudget n e) ≤ 2 * c₂ * (n + 1) ^ 2 := by
    calc (n / R + 1) * (c₂ * baseBudget n e) ≤ (n + 1) * (2 * c₂ * (n + 1)) :=
          Nat.mul_le_mul h1 h2
      _ = 2 * c₂ * (n + 1) ^ 2 := by ring
  have h4 : (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) ≤
      ((2 * c₂ * (n + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h3
  calc (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) ≤ ((2 * c₂ * (n + 1) ^ 2 : ℕ) : ℝ) := h4
    _ = 2 * (c₂ : ℝ) * ((n : ℝ) + 1) ^ 2 := by push_cast; ring

/-- **Raw bounds pass to a subset** (tex ~598–608).  Fix `c₂`, the raw constant `k₀` of a model
`F` and a constant `k₁`.  There is `k` such that at every calibrated instance with `1 ≤ R ≤ n`, if
`F` has the raw bounds with `k₀`, `x ∈ D ⊆ F` and `CT(D | F) ≤ k₁ H`, then `D` has the raw bounds
with `k`: the score grows by `O(H)` (`modelScore_le_of_subset`), and the endpoint costs by
`CT(D | F) + 2 log₂ (CT(F | ·) + 2) + O(1) = O(H)` (`Lower.totalC_trans`). -/
theorem rawBounds_of_subset (V : Map) (hV : isOptimalConditional V) :
    ∀ c₂ k₀ k₁ : ℕ, ∃ k : ℕ, ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString)
      (pA pB : BitString) (R : ℕ) (F D : Finset BitString),
      CalInstance V n e x A B pA pB → 1 ≤ R → R ≤ n →
      RawBounds V n e R c₂ k₀ x A B F → D ⊆ F → x ∈ D →
      setTotalC D F ≤ k₁ * baseBudget n e → RawBounds V n e R c₂ k x A B D := by
  intro c₂ k₀ k₁
  obtain ⟨cs, hcs⟩ := modelScore_le_of_subset V hV
  obtain ⟨ctr, htr⟩ := Lower.totalC_trans
  obtain ⟨blit, hblit⟩ := plainC_le_length_add V hV
  obtain ⟨kl, hkl⟩ := logb_le_baseBudget (2 + 2 * k₀ + blit + 2 * k₁)
  obtain ⟨kq, hkq⟩ := logb_quad_le_baseBudget (2 * c₂ + 2 * k₀)
  refine ⟨k₀ + k₁ + cs * kl + cs + 2 * kq + ctr,
    fun n e x A B pA pB R F D I hR1 hRn hraw hDF hxD hT => ?_⟩
  obtain ⟨hxF, hsF, hAF, hBF⟩ := hraw
  have hn := I.two_le
  have hHb := baseBudget_bounds hn I.e_le
  have hH1 : (1 : ℝ) ≤ (baseBudget n e : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ baseBudget n e)
  have hHn : (baseBudget n e : ℝ) ≤ 2 * n := by exact_mod_cast hHb.2
  have hRn' : (R : ℝ) ≤ n := by exact_mod_cast hRn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk₀ : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg k₀
  have hk₁ : (0 : ℝ) ≤ k₁ := Nat.cast_nonneg k₁
  have hb0 : (0 : ℝ) ≤ blit := Nat.cast_nonneg blit
  have hcs0 : (0 : ℝ) ≤ cs := Nat.cast_nonneg cs
  have hkq0 : (0 : ℝ) ≤ kq := Nat.cast_nonneg kq
  have hkl0 : (0 : ℝ) ≤ kl := Nat.cast_nonneg kl
  have hctr0 : (0 : ℝ) ≤ ctr := Nat.cast_nonneg ctr
  have hT0 := totalC_nonneg (canonicalFiniteSetCode D) (canonicalFiniteSetCode F)
  have hCF0 := plainC_nonneg V (canonicalFiniteSetCode F)
  have hH0 : (0 : ℝ) ≤ baseBudget n e := by linarith
  -- `C(F)` is linear in `n`
  have hCx : plainC V x ≤ n + blit := by
    have := hblit x
    rw [I.len] at this
    exact this
  have hlogF := logb_card_nonneg_of_mem hxF
  have hk₀H : (k₀ : ℝ) * baseBudget n e ≤ k₀ * (2 * n) := mul_le_mul_of_nonneg_left hHn hk₀
  have hk₁H : (k₁ : ℝ) * baseBudget n e ≤ k₁ * (2 * n) := mul_le_mul_of_nonneg_left hHn hk₁
  have hCF : setC V F ≤ 2 * n + blit + 2 * k₀ * n := by
    unfold modelScore at hsF
    linarith
  have hsum : setC V F + setTotalC D F ≤ ((2 + 2 * k₀ + blit + 2 * k₁ : ℕ) : ℝ) * (n + 1) := by
    have hbn : (0 : ℝ) ≤ blit * n := mul_nonneg hb0 hn0
    have hk₀n : (0 : ℝ) ≤ k₀ := hk₀
    have hk₁n : (0 : ℝ) ≤ k₁ := hk₁
    push_cast
    linarith
  have hlog1 : Real.logb 2 (setC V F + setTotalC D F + 2) ≤ kl * baseBudget n e :=
    (logb_add_two_mono (add_nonneg hCF0 hT0) hsum).trans (hkl n e)
  -- the score
  have hsc := hcs x D F hxD hDF
  have hm1 := mul_le_mul_of_nonneg_left hlog1 hcs0
  have hcsH : (cs : ℝ) ≤ cs * baseBudget n e := le_mul_of_one_le_right hcs0 hH1
  have hctrH : (ctr : ℝ) ≤ ctr * baseBudget n e := le_mul_of_one_le_right hctr0 hH1
  have hkqH : (0 : ℝ) ≤ kq * baseBudget n e := mul_nonneg hkq0 hH0
  -- the endpoints
  have hJL := depthLoss_le_quad (R := R) (c₂ := c₂) hn I.e_le
  have hk₀q : (k₀ : ℝ) * baseBudget n e ≤ 2 * k₀ * ((n : ℝ) + 1) ^ 2 := by
    have h1 : (0 : ℝ) ≤ k₀ * (((n : ℝ) + 1) ^ 2 - n) := mul_nonneg hk₀ (by nlinarith)
    nlinarith [hk₀H, h1]
  have hend : ∀ Y : Finset BitString,
      setTotalC F Y ≤ (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) + k₀ * baseBudget n e →
      setTotalC D Y ≤ (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) +
        ((k₀ + k₁ + cs * kl + cs + 2 * kq + ctr : ℕ) : ℝ) * baseBudget n e := by
    intro Y hY
    have htrY := htr (canonicalFiniteSetCode Y) (canonicalFiniteSetCode F)
      (canonicalFiniteSetCode D)
    have hY0 := totalC_nonneg (canonicalFiniteSetCode F) (canonicalFiniteSetCode Y)
    have hquad : setTotalC F Y ≤ ((2 * c₂ + 2 * k₀ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ 2 := by
      have := hY.trans (add_le_add hJL hk₀q)
      calc setTotalC F Y ≤ 2 * (c₂ : ℝ) * ((n : ℝ) + 1) ^ 2 + 2 * k₀ * ((n : ℝ) + 1) ^ 2 := this
        _ = ((2 * c₂ + 2 * k₀ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ 2 := by push_cast; ring
    have hlogY : Real.logb 2 (setTotalC F Y + 2) ≤ kq * baseBudget n e :=
      (logb_add_two_mono hY0 hquad).trans (hkq n e)
    have hDF' : totalC (canonicalFiniteSetCode D) (canonicalFiniteSetCode F) ≤
        k₁ * baseBudget n e := hT
    have hFY' : totalC (canonicalFiniteSetCode F) (canonicalFiniteSetCode Y) ≤
        (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) + k₀ * baseBudget n e := hY
    have hlogY' : Real.logb 2 (totalC (canonicalFiniteSetCode F) (canonicalFiniteSetCode Y) + 2) ≤
        kq * baseBudget n e := hlogY
    have hcsklH : (0 : ℝ) ≤ cs * kl * baseBudget n e := mul_nonneg (mul_nonneg hcs0 hkl0) hH0
    have hcsH0 : (0 : ℝ) ≤ cs * baseBudget n e := mul_nonneg hcs0 hH0
    change totalC (canonicalFiniteSetCode D) (canonicalFiniteSetCode Y) ≤ _
    have hK : ((k₀ + k₁ + cs * kl + cs + 2 * kq + ctr : ℕ) : ℝ) * baseBudget n e =
        k₀ * baseBudget n e + k₁ * baseBudget n e + cs * kl * baseBudget n e +
          cs * baseBudget n e + 2 * (kq * baseBudget n e) + ctr * baseBudget n e := by
      push_cast
      ring
    rw [hK]
    linarith
  refine ⟨hxD, ?_, hend A hAF, hend B hBF⟩
  have hK : ((k₀ + k₁ + cs * kl + cs + 2 * kq + ctr : ℕ) : ℝ) * baseBudget n e =
      k₀ * baseBudget n e + k₁ * baseBudget n e + cs * (kl * baseBudget n e) +
        cs * baseBudget n e + 2 * (kq * baseBudget n e) + ctr * baseBudget n e := by
    push_cast
    ring
  rw [hK]
  linarith

/-- **The cell has `CT(D | F) = O(H)` over H05's selection** at a calibrated instance
(tex ~598–606).  In the small-degree branch `D` is the star of the selected original model, in the
hierarchy branch the residual of the selected parent; both are computed from the parent by the
cell decoder with `O(H)` header bits (`cellOfParent_totalC`, `hdrCost_le`). -/
theorem cellTotalC_le (V : Map) (hV : isOptimalConditional V) :
    ∀ c₂ : ℕ, ∃ k₁ : ℕ, ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString) (pA pB : BitString)
      (R : ℕ), CalInstance V n e x A B pA pB → 1 ≤ R → R ≤ n →
        setTotalC (partModelAt c₂ R pA pB e x) (selectModelAt c₂ R pA pB e x) ≤
          k₁ * baseBudget n e := by
  intro c₂
  obtain ⟨cc, hcc⟩ := cellOfParent_totalC
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  obtain ⟨kh, hkh⟩ := hdrCost_le bsize
  refine ⟨2 + 4 * kh + 4 * headerLog c₂ + 8 + cc, fun n e x A B pA pB R I hR1 hRn => ?_⟩
  have hn := I.two_le
  have hoA : progOut pA x = canonicalFiniteSetCode A := progOut_eq_of_mem I.outA
  have hoB : progOut pB x = canonicalFiniteSetCode B := progOut_eq_of_mem I.outB
  have hxA : x ∈ A := I.suffA.1
  have hxB : x ∈ B := I.suffB.1
  have hab := (htyp n e x A I.len I.e_le I.suffA).2
  have hbb := (htyp n e x B I.len I.e_le I.suffB).2
  have hHb := baseBudget_bounds hn I.e_le
  have hgen : ∀ (j mode : ℕ) (w : BitString), j ≤ n → mode ≤ 2 →
      (mode = 0 → ∀ y ∈ parseModel w, y.length = n) →
      totalC (canonicalFiniteSetCode (cellOfParent (instShape pA pB n (Nat.log 2 A.card)
        (Nat.log 2 B.card)) R (c₂ * baseBudget n e) j mode w)) w ≤
        ((2 + 4 * kh + 4 * headerLog c₂ + 8 + cc : ℕ) : ℝ) * baseBudget n e := by
    intro j mode w hj hm hw
    have h1 := hcc pA pB n (Nat.log 2 A.card) (Nat.log 2 B.card) R (c₂ * baseBudget n e) j mode
      w I.totA I.totB hw
    have h2 := hkh c₂ n e _ _ R j pA pB hn I.e_le hab hbb hRn hj I.lenA I.lenB
    have h3 := headerLog_le_two hm
    have hH1 : 1 ≤ baseBudget n e := by omega
    have heH : e ≤ baseBudget n e := by unfold baseBudget; omega
    have hN : pA.length + pB.length +
        4 * hdrCost [n, Nat.log 2 A.card, Nat.log 2 B.card, R, c₂ * baseBudget n e, j,
          pA.length, pB.length] + 4 * headerLog mode + cc ≤
        (2 + 4 * kh + 4 * headerLog c₂ + 8 + cc) * baseBudget n e := by
      have e1 : headerLog c₂ ≤ headerLog c₂ * baseBudget n e := Nat.le_mul_of_pos_right _ hH1
      have e2 : cc ≤ cc * baseBudget n e := Nat.le_mul_of_pos_right _ hH1
      have e3 := I.lenA
      have e4 := I.lenB
      nlinarith
    have hN' : ((pA.length + pB.length +
        4 * hdrCost [n, Nat.log 2 A.card, Nat.log 2 B.card, R, c₂ * baseBudget n e, j,
          pA.length, pB.length] + 4 * headerLog mode + cc : ℕ) : ℝ) ≤
        (((2 + 4 * kh + 4 * headerLog c₂ + 8 + cc) * baseBudget n e : ℕ) : ℝ) := by
      exact_mod_cast hN
    calc _ ≤ _ := h1
      _ ≤ _ := hN'
      _ = _ := by push_cast; ring
  have hxlen := I.len
  subst hxlen
  rcases le_or_gt (min (Nat.log 2 A.card) (Nat.log 2 B.card))
      ((x.length / R + 1) * (c₂ * baseBudget x.length e)) with hs | hbig
  · rw [selectModelAt_of_le (by omega) hoA hoB hxA hxB hs,
      partModelAt_eq_shapeCell (by omega) hoA hoB hxA hxB]
    set P := instShape pA pB x.length (Nat.log 2 A.card) (Nat.log 2 B.card) with hP
    unfold shapeCell
    have hs' : min P.a P.b ≤ (P.n / R + 1) * (c₂ * baseBudget P.n e) := hs
    rw [ite_eq_left hs']
    by_cases hab' : Nat.log 2 A.card ≤ Nat.log 2 B.card
    · have hd : decide (P.a ≤ P.b) = true := decide_eq_true hab'
      have hlab : sideOut P true x = canonicalFiniteSetCode B := hoB
      rw [ite_eq_left hab', hd, hlab, ← cellOfParent_two P R (c₂ * baseBudget x.length e) 0]
      exact hgen 0 2 _ (Nat.zero_le _) le_rfl (by omega)
    · have hd : decide (P.a ≤ P.b) = false := decide_eq_false hab'
      have hlab : sideOut P false x = canonicalFiniteSetCode A := hoA
      rw [ite_eq_right hab', hd, hlab, ← cellOfParent_one P R (c₂ * baseBudget x.length e) 0]
      exact hgen 0 1 _ (Nat.zero_le _) (by omega) (by omega)
  · have hxG : x ∈ shapeEdges (instShape pA pB x.length (Nat.log 2 A.card) (Nat.log 2 B.card)) :=
      mem_shapeEdges_of _ rfl hoA hoB hxA hxB rfl rfl
    obtain ⟨j, F, hsel, hjJ, hF, -, -⟩ :=
      firstResidualBlock_spec (instShape pA pB x.length (Nat.log 2 A.card) (Nat.log 2 B.card)) R
        (c₂ * baseBudget x.length e) (x.length / R + 1) (lt_div_add_one_mul hR1) hxG
    rw [selectModelAt_of_lt (by omega) hoA hoB hxA hxB hbig hsel,
      partModelAt_eq_shapeCell (by omega) hoA hoB hxA hxB]
    have hjn : j ≤ x.length := by
      have : x.length / R ≤ x.length := Nat.div_le_self _ R
      omega
    have h := hgen j 0 (canonicalFiniteSetCode F) hjn (Nat.zero_le _) (fun _ => by
      rw [parseModel_canonicalFiniteSetCode]
      exact length_eq_of_mem_level _ R _ j hF)
    rw [cellOfParent_zero] at h
    set P := instShape pA pB x.length (Nat.log 2 A.card) (Nat.log 2 B.card) with hP
    unfold shapeCell
    have hs' : ¬ (min P.a P.b ≤ (P.n / R + 1) * (c₂ * baseBudget P.n e)) := not_le.mpr hbig
    rw [ite_eq_right hs']
    unfold residualCell
    have hsel' : firstResidualBlock P R (c₂ * baseBudget P.n e) (P.n / R + 1) x = some (j, F) :=
      hsel
    rw [hsel']
    exact h

/-! ### Assembly -/

/-- **The tradeoff core of the partition version.**  There are constants `c₂` (the hierarchy step)
and `c` such that at every calibrated instance and every `1 ≤ R ≤ n` the partition cell at the
hardwired exponent `R` satisfies the tradeoff bounds with the constant `c`.  The constants are
fixed in the order of `tradeoff_core`: the residual constant (H04), `c₂`, the hardwired-`R` point
constants of H05's selector and of the partition program, the transfer constant, then `c`. -/
theorem partition_core (V : Map) (hV : isOptimalConditional V) :
    ∃ c₂ c : ℕ, ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString) (pA pB : BitString)
      (R : ℕ), CalInstance V n e x A B pA pB → 1 ≤ R → R ≤ n →
        TradeoffBounds V n e R c x A B (partModelAt c₂ R pA pB e x) := by
  obtain ⟨u, hbig⟩ := rawBounds_big V hV
  obtain ⟨c₂, hc₂⟩ := exists_const_gt_header u u
  obtain ⟨cH, hsel⟩ := upperHierarchySelector c₂ (fun _ _ h => h)
    (Computable.snd.comp Computable.snd)
  obtain ⟨k₁, hk₁⟩ := rawBounds_small V hV c₂
  obtain ⟨k₂, hk₂⟩ := hbig c₂ hc₂ (18 + cH)
  obtain ⟨kc, hkc⟩ := cellTotalC_le V hV c₂
  obtain ⟨k, hk⟩ := rawBounds_of_subset V hV c₂ (k₁ + k₂) kc
  obtain ⟨cP, hP⟩ := exists_partitionProgram c₂ (fun _ _ h => h)
    (Computable.snd.comp Computable.snd)
  obtain ⟨c, hc⟩ := tradeoffBounds_of_raw V hV c₂ k (18 + cP)
  refine ⟨c₂, c, fun n e x A B pA pB R I hR1 hRn => ?_⟩
  have hRx : R ≤ x.length := I.len ▸ hRn
  -- H05's selection `F` and its raw bounds
  have hptF : pointTotalC (selectModelAt c₂ R pA pB e x) x ≤
      ((18 + cH : ℕ) : ℝ) * baseBudget n e := by
    have h := hsel pA pB e R x I.totA I.totB I.lenA I.lenB
    rw [selectModel_const hR1 hRx] at h
    exact h.trans (point_le_cpt I.two_le hRn)
  have hrawF : RawBounds V n e R c₂ (k₁ + k₂) x A B (selectModelAt c₂ R pA pB e x) := by
    by_cases hs : min (Nat.log 2 A.card) (Nat.log 2 B.card) ≤ (n / R + 1) * (c₂ * baseBudget n e)
    · exact (hk₁ n e x A B pA pB R I hR1 hRn hs).mono (by omega)
    · exact (hk₂ n e x A B pA pB R I hR1 hRn (not_le.mp hs) hptF).mono (by omega)
  -- the partition cell `D` and its point bound from the hardwired-`R` program
  obtain ⟨q, hql, hqt, hqp⟩ := hP pA pB e R I.totA I.totB I.lenA I.lenB
  have hD : partModel c₂ (fun _ _ => R) pA pB e x = partModelAt c₂ R pA pB e x := by
    unfold partModel
    rw [clipR_of_le hR1 hRx]
  have hptD : pointTotalC (partModelAt c₂ R pA pB e x) x ≤
      ((18 + cP : ℕ) : ℝ) * baseBudget n e := by
    have h1 := Lower.totalC_le_length_of_totalProgram hqt (hqp x)
    rw [hD] at h1
    have h2 : (q.length : ℝ) ≤ 7 * ((e : ℝ) + 1) + 4 * (headerLog R : ℝ) + cP := by
      exact_mod_cast hql
    exact h1.trans (h2.trans (point_le_cpt I.two_le hRn))
  have hxD : x ∈ partModelAt c₂ R pA pB e x := mem_partCell_self _ _ _ _ _ x
  have hrawD := hk n e x A B pA pB R _ _ I hR1 hRn hrawF
    (partModelAt_subset_selectModelAt c₂ R pA pB e x) hxD (hkc n e x A B pA pB R I hR1 hRn)
  exact hc n e x A B pA pB R _ I hR1 hRn hrawD hptD

end Partition

open Partition in
/-- **The uniform partition version with a fixed rule (blueprint H08, `UpperHierarchyPartition`;
`cor:partition`).**  The frozen statement `exists_partition_selector_tradeoff` of
`StrongMerging.StatementsExtra`, verbatim.  The partition cell is `partModel c₂ ρ p_A p_B e`, the
program is the partition selector program with `h = 0`; the tradeoff constant `c` is that of
`partition_core`, fixed before the rule, and only `c_ρ` depends on `ρ`. -/
theorem exists_partition_selector_tradeoff' (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ ρ : ℕ → ℕ → ℕ, Computable₂ ρ → ∃ cρ : ℕ,
      ∀ (e : ℕ) (pA pB : BitString), IsBoundedTotalWitness e pA → IsBoundedTotalWitness e pB →
        ∃ (q : BitString) (Q : BitString → Finset BitString), IsExactPartitionSelector q Q ∧
          q.length ≤ cρ * (e + 1) ∧
          ∀ (n : ℕ) (x : BitString) (A B : Finset BitString),
            IsWitnessedInstance V n e pA pB x A B →
              TradeoffBounds V n e (min n (max 1 (ρ n e))) c x A B (Q x) := by
  obtain ⟨c₂, c, hcore⟩ := partition_core V hV
  refine ⟨c, fun ρ hρ => ?_⟩
  obtain ⟨cP, hP⟩ := exists_partitionProgram c₂ (fun n e _ => ρ n e)
    (hρ.comp Computable.fst (Computable.fst.comp Computable.snd))
  refine ⟨cP + 11, fun e pA pB hwA hwB => ?_⟩
  obtain ⟨hpA, hlA⟩ := hwA
  obtain ⟨hpB, hlB⟩ := hwB
  obtain ⟨q, hql, hqt, hqp⟩ := hP pA pB e 0 hpA hpB hlA hlB
  have hpart := partModel_partition c₂ ρ pA pB e
  refine ⟨q, partModel c₂ ρ pA pB e, ⟨hqt, hqp, hpart.1, hpart.2⟩, ?_, ?_⟩
  · have h0 : headerLog 0 = 1 := by
      unfold headerLog
      rw [show (0 + 2 : ℕ) = 2 ^ 1 by norm_num, Nat.clog_pow 2 1 one_lt_two]
    rw [h0] at hql
    nlinarith
  · intro n x A B hI
    obtain ⟨hn, he, hx, hoA, hoB, hsA, hsB⟩ := hI
    have I : CalInstance V n e x A B pA pB :=
      ⟨hn, he, hx, hsA, hsB, hpA, hpB, hlA, hlB, hoA, hoB⟩
    have hR := one_le_clipR (r := ρ n e) (by omega : 1 ≤ n)
    have hQ : partModel c₂ ρ pA pB e x = partModelAt c₂ (clipR n (ρ n e)) pA pB e x := by
      unfold partModel
      rw [hx]
    rw [hQ]
    exact hcore n e x A B pA pB _ I hR.1 hR.2

end Kolmogorov.StrongMerging.Upper
