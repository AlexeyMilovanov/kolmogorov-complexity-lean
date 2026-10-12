import KolmogorovMathlib.StrongMerging.Upper.CoreDecoders.TableMachine

/-!
# Decoders of the minimum-core layer (blueprint M01, M03)

`sublinear-merging.tex`, subsection "Finite minimum-core profiles" (tex ~676–728) and appendix
`bp-upper-mincores` (tex ~3816–3851).

* **Qualifying instances.**  `IsCoreInstance V n e pA pB x A B`: total witnesses `pA, pB` of
  length `≤ e ≤ n`, `|x| = n`, `pA(x) = A`, `pB(x) = B` (canonical codes), and `A, B` are
  `e`-sufficient for `x`.  (This is `IsBoundedTotalWitness`/`IsWitnessedInstance` of
  `StatementsExtra` without `n ≥ 2`.)  `coreShape` is its shape graph, read by `progOut`.
* **One generic table machine.**  `corePacket ks pA pB tail` carries numeric fields `ks`
  (`n, a, b, side, s, …`), the two witness bodies and a tail.  `coreMachine m ker` decodes `m`
  fields, computes both output tables by complete runs (`runTable`, which halts for total
  witnesses), and applies a kernel `ker` to the tables, fields, tail and condition.  Every kernel
  below only reads the tables at the data length, so its value is the instance's
  (`tableShape_agreeOn`, `vertexCores_congr`, `coreOf_congr`).
* **M01 (`UpperComponentDecoder`).**  `componentKer` returns the component of the typed endpoint
  (`∅` at a nonvertex); `upperComponentDecoder`: `x ∈ C_0` and `CT(C_0 | A), CT(C_0 | B) ≤ c H`.
* **M03 (`UpperMinCoreLocalDecoder`).**  `localCoreKer` returns the core of a given local rank
  among the cores incident to the typed endpoint (default `∅`); `pointCoreKer` returns the
  selected core of the condition (default `∅`).  `upperMinCoreLocalDecoder`: at budgets
  `s ≤ a, b` with a selected core `F_s ∋ x`, `CT(F_s | A), CT(F_s | B) ≤ s + c H` and
  `C(F_s | x) ≤ c H`.  No nesting between budgets is used or claimed.

Here `H = e + ⌈log₂ (n + 2)⌉` (`baseBudget n e`).

The first part of the development is in
`KolmogorovMathlib.StrongMerging.Upper.CoreDecoders.TableMachine`, imported here.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### M01: the component decoder -/

/-- **The component kernel** (M01): the canonical code of the component of the typed endpoint
in the table shape; `∅` at a nonvertex.  Total. -/
noncomputable def componentKer (q : CoreIn) : Part BitString :=
  Part.some (canonicalFiniteSetCode (shapeComponent (inShape q) (shapeEdges (inShape q)) (inEnd q)))

/-- The parameters of a family computation: the two output tables, `(n, a, b)`, the budget and
the cap `(s, M)`, and a vertex. -/
abbrev FamParams : Type :=
  (List (BitString × BitString) × List (BitString × BitString)) × (ℕ × ℕ × ℕ) × (ℕ × ℕ) ×
    (BitString ⊕ BitString)

/-- The table shape of family parameters. -/
def famShape (p : FamParams) : ShapeParams :=
  tableShape p.1.1 p.1.2 p.2.1.1 p.2.1.2.1 p.2.1.2.2

/-- One traversal step on lists: append the edges of `G` adjacent to an edge of `S`. -/
def compGrowL (P : ShapeParams) (G S : List BitString) : List BitString :=
  S ++ G.filter fun y => S.any fun z => decide (EdgeAdj P z y)

/-- The list step computes the finset step. -/
theorem toFinset_compGrowL (P : ShapeParams) (G S : List BitString) :
    (compGrowL P G S).toFinset = compGrow P G.toFinset S.toFinset := by
  ext y
  simp [compGrowL, compGrow, List.any_eq_true]

/-- Iterated list steps compute the iterated finset steps. -/
theorem toFinset_iterate_compGrowL (P : ShapeParams) (G : List BitString) :
    ∀ (k : ℕ) (S : List BitString),
      ((compGrowL P G)^[k] S).toFinset = (compGrow P G.toFinset)^[k] S.toFinset
  | 0, _ => rfl
  | k + 1, S => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      toFinset_iterate_compGrowL P G k, toFinset_compGrowL]

/-- **The component code is primitive recursive** in the tables, `(n, a, b)` and the vertex: the
traversal is iterated on the canonical list of the shape edges (`compGrowL`), whose code is
primitive recursive (`shapeEdges_code_primrec`). -/
theorem shapeComponentCode_primrec :
    Primrec fun p : FamParams =>
      canonicalFiniteSetCode (shapeComponent (famShape p) (shapeEdges (famShape p)) p.2.2.2) := by
  have hA : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.1 z :=
    tableOut_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hB : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.2 z :=
    tableOut_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hGc := shapeEdges_code_primrec
    (fun (T : List (BitString × BitString) × List (BitString × BitString)) z => tableOut T.1 z)
    (fun (T : List (BitString × BitString) × List (BitString × BitString)) z => tableOut T.2 z)
    hA hB
  have hGcode : Primrec fun p : FamParams => canonicalFiniteSetCode (shapeEdges (famShape p)) :=
    (hGc.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))).of_eq fun p => rfl
  have hGl : Primrec fun p : FamParams =>
      canonicalPointListOfCode (canonicalFiniteSetCode (shapeEdges (famShape p))) :=
    canonicalPointListOfCode_primrec.comp hGcode
  have hstartTest : Primrec₂ fun (p : FamParams) (z : BitString) =>
      decide ((Sum.inl (tableOut p.1.1 z) : BitString ⊕ BitString) = p.2.2.2) ||
        decide ((Sum.inr (tableOut p.1.2 z) : BitString ⊕ BitString) = p.2.2.2) :=
    Primrec.or.comp
      (Primrec.eq.decide.comp (Primrec.sumInl.comp (tableOut_primrec.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.eq.decide.comp (Primrec.sumInr.comp (tableOut_primrec.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hstart := primrec_list_filter hGl hstartTest
  have hadj : Primrec₂ fun (x : (FamParams × List BitString) × BitString) (z : BitString) =>
      decide (tableOut x.1.1.1.1 z = tableOut x.1.1.1.1 x.2) ||
        decide (tableOut x.1.1.1.2 z = tableOut x.1.1.1.2 x.2) :=
    Primrec.or.comp
      (Primrec.eq.decide.comp
        (tableOut_primrec.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst)))) Primrec.snd)
        (tableOut_primrec.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst)))) (Primrec.snd.comp Primrec.fst)))
      (Primrec.eq.decide.comp
        (tableOut_primrec.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst)))) Primrec.snd)
        (tableOut_primrec.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst)))) (Primrec.snd.comp Primrec.fst)))
  have hany : Primrec₂ fun (x : FamParams × List BitString) (y : BitString) =>
      x.2.any fun z => decide (tableOut x.1.1.1 z = tableOut x.1.1.1 y) ||
        decide (tableOut x.1.1.2 z = tableOut x.1.1.2 y) :=
    list_any_primrec (Primrec.snd.comp Primrec.fst) hadj
  have hfil := primrec_list_filter (hGl.comp Primrec.fst) hany
  have hstep : Primrec₂ fun (p : FamParams) (S : List BitString) =>
      compGrowL (famShape p) (canonicalPointListOfCode
        (canonicalFiniteSetCode (shapeEdges (famShape p)))) S :=
    (Primrec.list_append.comp Primrec.snd hfil).of_eq fun x => by
      unfold compGrowL
      congr 1
      apply List.filter_congr
      intro y _
      congr 1
      funext z
      apply Bool.eq_iff_iff.mpr
      rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
      rfl
  have hiter := Primrec.nat_iterate (Primrec.list_length.comp hGl) hstart hstep
  refine (canonicalFiniteSetCode_toFinset_primrec.comp hiter).of_eq fun p => ?_
  congr 1
  rw [toFinset_iterate_compGrowL]
  have hGl' : (canonicalPointListOfCode (canonicalFiniteSetCode (shapeEdges (famShape p)))).toFinset
      = shapeEdges (famShape p) := by
    rw [canonicalPointListOfCode_canonicalFiniteSetCode, canonicalFinsetList_toFinset]
  have hlen : (canonicalPointListOfCode (canonicalFiniteSetCode (shapeEdges (famShape p)))).length
      = (shapeEdges (famShape p)).card := by
    rw [canonicalPointListOfCode_canonicalFiniteSetCode, length_canonicalFinsetList]
  have hst : ((canonicalPointListOfCode (canonicalFiniteSetCode (shapeEdges (famShape p)))).filter
      fun z => decide ((Sum.inl (tableOut p.1.1 z) : BitString ⊕ BitString) = p.2.2.2) ||
        decide ((Sum.inr (tableOut p.1.2 z) : BitString ⊕ BitString) = p.2.2.2)).toFinset =
      vertexEdges (famShape p) (shapeEdges (famShape p)) p.2.2.2 := by
    rw [List.toFinset_filter, hGl']
    unfold vertexEdges
    apply Finset.filter_congr
    intro z _
    simp [shapeSrc, shapeTgt, famShape, tableShape]
  rw [hGl', hlen, hst]
  rfl

/-- **The field triple `(n, a, b)` of a kernel input is primitive recursive.** -/
theorem inNAB_primrec :
    Primrec fun q : CoreIn => (q.2.1.getD 0 0, q.2.1.getD 1 0, q.2.1.getD 2 0) := by
  have hl : Primrec fun q : CoreIn => q.2.1 := Primrec.fst.comp Primrec.snd
  exact Primrec.pair ((Primrec.list_getD 0).comp hl (Primrec.const 0))
    (Primrec.pair ((Primrec.list_getD 0).comp hl (Primrec.const 1))
      ((Primrec.list_getD 0).comp hl (Primrec.const 2)))

/-- **The typed endpoint of a kernel input is computable.**

Proof sketch: `inEnd q = if q.2.1.getD 3 0 ≠ 0 then Sum.inr y else Sum.inl y`; `Primrec.ite` (or
`Primrec.cond` after `decide`) with `Primrec.list_getD`, `Primrec.eq`, `Primrec.sumInl`,
`Primrec.sumInr`; unfold `inEnd`, `coreEnd`, `inSide` (`of_eq`). -/
theorem inEnd_computable : Computable inEnd := by
  have hb : Primrec fun q : CoreIn => decide (q.2.1.getD 3 0 = 0) :=
    Primrec.eq.decide.comp ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.const 3)) (Primrec.const 0)
  have hy : Primrec fun q : CoreIn => q.2.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have h : Primrec fun q : CoreIn =>
      bif decide (q.2.1.getD 3 0 = 0) then Sum.inl q.2.2.2 else Sum.inr q.2.2.2 :=
    Primrec.cond hb (Primrec.sumInl.comp hy) (Primrec.sumInr.comp hy)
  refine h.to_comp.of_eq fun q => ?_
  unfold inEnd coreEnd inSide
  simp

/-- **The component kernel is partial recursive**: it is total and its value is the component
code, primitive recursive by `shapeComponentCode_primrec`. -/
theorem componentKer_partrec : Partrec componentKer := by
  have hg : Computable fun q : CoreIn =>
      ((q.1, (q.2.1.getD 0 0, q.2.1.getD 1 0, q.2.1.getD 2 0), (0, 0), inEnd q) : FamParams) :=
    Computable.pair Computable.fst (Computable.pair inNAB_primrec.to_comp
      (Computable.pair (Computable.const (0, 0)) inEnd_computable))
  have h := (shapeComponentCode_primrec.to_comp.comp hg).partrec
  exact h.of_eq fun q => rfl

/-- **The component decoder (blueprint M01, `UpperComponentDecoder`).**  For an optimal plain
machine `V` there is a constant `c` such that at every qualifying instance the actual string lies
in its component `C_0`, and `C_0` has total descriptions from either actual endpoint of length at
most `c H`: one fixed total program (the table machine with the component kernel and the packet
`n, a, b, side` and the two witnesses) computes `C_0` from `A` and from `B`; it outputs `∅` at a
nonvertex (`shapeComponent_eq_empty`). -/
theorem upperComponentDecoder (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString),
      IsCoreInstance V n e pA pB x A B →
        x ∈ instComponent pA pB n A B x ∧
          totalC (canonicalFiniteSetCode (instComponent pA pB n A B x))
            (canonicalFiniteSetCode A) ≤ c * baseBudget n e ∧
          totalC (canonicalFiniteSetCode (instComponent pA pB n A B x))
            (canonicalFiniteSetCode B) ≤ c * baseBudget n e := by
  obtain ⟨cD, hcD⟩ := totalC_le_of_decoder (coreMachine 5 componentKer)
    (coreMachine_partrec 5 componentKer_partrec)
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  obtain ⟨cpk, hpk⟩ := length_corePacket_le 5 (bsize + 3)
  refine ⟨cpk + cD, fun n e pA pB x A B h => ?_⟩
  have hxG := h.mem_shapeEdges
  have ha := (htyp n e x A h.length_x h.le_n h.sufA).2
  have hb := (htyp n e x B h.length_x h.le_n h.sufB).2
  have hH : (1 : ℝ) ≤ baseBudget n e := by
    have := one_le_headerLog n
    unfold baseBudget
    exact_mod_cast (by omega : 1 ≤ e + headerLog n)
  have key : ∀ (side : Bool) (y : BitString),
      shapeComponent (coreShape pA pB n A B) (shapeEdges (coreShape pA pB n A B))
          (coreEnd side y) = instComponent pA pB n A B x →
        totalC (canonicalFiniteSetCode (instComponent pA pB n A B x)) y ≤
          ((cpk + cD : ℕ) : ℝ) * baseBudget n e := by
    intro side y hy
    obtain ⟨TA, TB, hTA, hTB, heval⟩ := coreMachine_eval 5 componentKer
      (ks := [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, 0]) rfl h.totalA h.totalB []
    have hag : (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)).AgreeOn
        (coreShape pA pB n A B) := tableShape_agreeOn (n := n) hTA hTB
    have hout : ∀ y', coreMachine 5 componentKer
        (corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, 0] pA pB [], y') =
          Part.some (canonicalFiniteSetCode (shapeComponent (coreShape pA pB n A B)
            (shapeEdges (coreShape pA pB n A B)) (coreEnd side y'))) := by
      intro y'
      rw [heval y']
      unfold componentKer inEnd
      dsimp only
      rw [inShape_mk, inSide_mk, (vertexCores_congr hag 0 0 _).1]
    have hdom : ∀ y', (coreMachine 5 componentKer
        (corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, 0] pA pB [], y')).Dom := by
      intro y'
      rw [hout y']
      trivial
    have hmem : canonicalFiniteSetCode (instComponent pA pB n A B x) ∈ coreMachine 5 componentKer
        (corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, 0] pA pB [], y) := by
      rw [hout y, hy]
      exact Part.mem_some _
    have h1 := hcD _ hdom y _ hmem
    have hfields : ∀ k ∈ [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, 0],
        k ≤ (bsize + 3) * (n + 1) := by
      intro k hk
      have hs := Bool.toNat_le side
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> nlinarith
    have h2 := hpk n e _ pA pB [] (by simp) hfields h.lenA h.lenB h.le_n
    simp only [List.length_nil, zero_add] at h2
    have h3 : ((corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, 0] pA pB []).length
        : ℝ) ≤ cpk * baseBudget n e := by exact_mod_cast h2
    have hcD0 : (cD : ℝ) ≤ cD * baseBudget n e := le_mul_of_one_le_right (Nat.cast_nonneg _) hH
    push_cast
    linarith
  refine ⟨mem_shapeComponent_src hxG, key false _ ?_, key true _ ?_⟩
  · unfold instComponent
    congr 1
    simp only [coreEnd, shapeSrc, h.outA_eq]
    rfl
  · unfold instComponent
    rw [shapeComponent_src_eq_tgt hxG]
    congr 1
    simp only [coreEnd, shapeTgt, h.outB_eq]
    rfl

/-! ### M03: the local and point decoders of selected cores -/

/-- **The local core kernel** (M03): among the cores of the full family at budget `s` (field `4`)
incident to the typed endpoint, in list order, the one of local rank `decodeBits tail`; default
`∅`.  Total. -/
noncomputable def localCoreKer (q : CoreIn) : Part BitString :=
  Part.some (canonicalFiniteSetCode ((incidentCores (inShape q)
    (vertexCores (inShape q) (inBudget q) (inEnd q)) (inEnd q)).getD (decodeBits q.2.2.1) ∅))

/-- **The point core kernel** (M03): the selected core of the condition at budget `s` (field `4`),
default `∅`.  Total. -/
noncomputable def pointCoreKer (q : CoreIn) : Part BitString :=
  Part.some (canonicalFiniteSetCode ((coreOf (inShape q) (inBudget q) q.2.2.2).getD ∅))

/-- `List.sublists'` as a right fold: `[[]]`, and at each head `a` the old sublists followed by
the old sublists with `a` prepended (`List.sublists'_cons`). -/
theorem coreSel_sublists'_eq_foldr {β : Type*} (l : List β) :
    l.sublists' = l.foldr (fun a acc => acc ++ acc.map (List.cons a)) [[]] := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.sublists'_cons, ih, List.foldr_cons]

/-- `List.sublists'` of a primitive recursive list is primitive recursive (a `List.foldr`). -/
theorem coreSel_sublists'_primrec {α β : Type} [Primcodable α] [Primcodable β] {f : α → List β}
    (hf : Primrec f) : Primrec fun a => (f a).sublists' := by
  have h1 : Primrec fun r : α × (β × List (List β)) => r.2.2 := Primrec.snd.comp Primrec.snd
  have h2 : Primrec₂ fun (r : α × (β × List (List β))) (t : List β) => r.2.1 :: t :=
    (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂
  have hstep : Primrec₂ fun (_ : α) (q : β × List (List β)) => q.2 ++ q.2.map (List.cons q.1) :=
    (Primrec.list_append.comp h1 (Primrec.list_map h1 h2)).to₂
  exact (Primrec.list_foldr hf (Primrec.const [[]]) hstep).of_eq fun a =>
    (coreSel_sublists'_eq_foldr (f a)).symm

/-- On a duplicate-free list, the sublists of length `k` are the sublists of `sublists'` of
length `k`, in the same order. -/
theorem coreSel_sublistsLen_eq_filter {β : Type*} {l : List β} (hl : l.Nodup) (k : ℕ) :
    l.sublistsLen k = l.sublists'.filter fun t => decide (t.length = k) := by
  have h1 : List.Sublist (l.sublistsLen k) (l.sublists'.filter fun t => decide (t.length = k)) := by
    have h := (List.sublistsLen_sublist_sublists' k l).filter (fun t => decide (t.length = k))
    rwa [List.filter_eq_self.mpr] at h
    intro t ht
    simp [List.length_of_sublistsLen ht]
  refine h1.eq_of_length_le ?_
  apply List.Nodup.length_le_of_subset
  · exact (List.nodup_sublists'.mpr hl).filter _
  · intro t ht
    rw [List.mem_filter, List.mem_sublists', decide_eq_true_eq] at ht
    exact List.mem_sublistsLen.mpr ht

/-- Mapping the result of `List.findSome?` is `List.findSome?` of the mapped function. -/
theorem coreSel_map_findSome? {α β γ : Type*} (f : α → Option β) (g : β → γ) :
    ∀ l : List α, (l.findSome? f).map g = l.findSome? fun x => (f x).map g
  | [] => rfl
  | x :: l => by
    cases hfx : f x <;> simp [hfx, coreSel_map_findSome? f g l]

/-- The budget-`s` core eligibility test in Boolean form on a list `lT` of the candidate's
points: nonempty, and every entry has row and column counts at least `2^(a - s)`, `2^(b - s)`. -/
def coreEligBool (gA gB : BitString → BitString) (a b s : ℕ) (lT : List BitString) : Bool :=
  decide (0 < lT.length) &&
    lT.all fun z => decide (2 ^ (a - s) ≤ lT.countP fun y => decide (gA y = gA z)) &&
      decide (2 ^ (b - s) ≤ lT.countP fun y => decide (gB y = gB z))

/-- The eligibility test of a parsed candidate agrees with its Boolean form. -/
theorem decide_coreElig_eq (P : ShapeParams) (s : ℕ) (w : BitString) :
    decide (CoreElig P s (parseModel w)) =
      coreEligBool P.outA P.outB P.a P.b s (canonicalPointListOfCode w) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [CoreElig, coreEligBool, ← Finset.card_pos, shapePR_card_parseModel,
    shapePR_mem_parseModel, childPR_rowDeg_parseModel, childPR_colDeg_parseModel,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]

/-- The eligibility test of the set of a list agrees with the Boolean form on its canonical
listing. -/
theorem decide_coreElig_toFinset (P : ShapeParams) (s : ℕ) (t : List BitString) :
    decide (CoreElig P s t.toFinset) =
      coreEligBool P.outA P.outB P.a P.b s (canonicalFinsetList t.toFinset) := by
  have h := decide_coreElig_eq P s (canonicalFiniteSetCode t.toFinset)
  rwa [parseModel_canonicalFiniteSetCode, canonicalPointListOfCode_canonicalFiniteSetCode] at h

/-- The Boolean eligibility form is primitive recursive in primitive recursive data. -/
theorem coreEligBool_primrec {β : Type} [Primcodable β] {gA gB : β → BitString → BitString}
    (hA : Primrec₂ gA) (hB : Primrec₂ gB) {a b s : β → ℕ} (ha : Primrec a) (hb : Primrec b)
    (hs : Primrec s) {l : β → List BitString} (hl : Primrec l) :
    Primrec fun x => coreEligBool (gA x) (gB x) (a x) (b x) (s x) (l x) := by
  have hne : Primrec fun x => decide (0 < (l x).length) :=
    Primrec.nat_lt.decide.comp (Primrec.const 0) (Primrec.list_length.comp hl)
  have hcntA : Primrec fun r : β × BitString =>
      (l r.1).countP fun y => decide (gA r.1 y = gA r.1 r.2) :=
    list_countP_primrec (hl.comp Primrec.fst)
      (Primrec.eq.decide.comp (hA.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (hA.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))).to₂
  have hcntB : Primrec fun r : β × BitString =>
      (l r.1).countP fun y => decide (gB r.1 y = gB r.1 r.2) :=
    list_countP_primrec (hl.comp Primrec.fst)
      (Primrec.eq.decide.comp (hB.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (hB.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))).to₂
  have hthrA : Primrec fun r : β × BitString => 2 ^ (a r.1 - s r.1) :=
    shapePR_pow_primrec.comp (Primrec.const 2)
      (Primrec.nat_sub.comp (ha.comp Primrec.fst) (hs.comp Primrec.fst))
  have hthrB : Primrec fun r : β × BitString => 2 ^ (b r.1 - s r.1) :=
    shapePR_pow_primrec.comp (Primrec.const 2)
      (Primrec.nat_sub.comp (hb.comp Primrec.fst) (hs.comp Primrec.fst))
  have hp : Primrec₂ fun (x : β) (z : BitString) =>
      decide (2 ^ (a x - s x) ≤ (l x).countP fun y => decide (gA x y = gA x z)) &&
        decide (2 ^ (b x - s x) ≤ (l x).countP fun y => decide (gB x y = gB x z)) :=
    (Primrec.and.comp (Primrec.nat_le.decide.comp hthrA hcntA)
      (Primrec.nat_le.decide.comp hthrB hcntB)).to₂
  exact (Primrec.and.comp hne (list_all_primrec hl hp)).of_eq fun x => rfl

/-- **The minimum-cardinality selection is primitive recursive on codes**: the code of
`minCoreSel` of the table shape, at the budget and cap of the parameters, on the remainder
`parseModel w`.

Proof: on `l = canonicalFinsetList (parseModel w)` (duplicate-free), `l.sublistsLen k` is
`(l.sublists').filter (·.length = k)` (`coreSel_sublistsLen_eq_filter`) and `sublists'` is a
`List.foldr` (`coreSel_sublists'_primrec`); eligibility is the Boolean `coreEligBool` on the
canonical listing (`decide_coreElig_toFinset`, `coreEligBool_primrec`); the search over
`k ≤ min M |l|` is `List.findSome?`, the head of a `List.filterMap` (`List.head?_filterMap`,
`coreSel_map_findSome?`). -/
theorem minCoreSelCode_primrec :
    Primrec fun p : FamParams × BitString =>
      (minCoreSel (famShape p.1) p.1.2.2.1.1 p.1.2.2.1.2 (parseModel p.2)).map
        canonicalFiniteSetCode := by
  -- the canonical listing of the remainder
  have hl : Primrec fun x : FamParams × BitString =>
      canonicalFinsetList (canonicalPointListOfCode x.2).toFinset :=
    canonicalFinsetList_toFinset_primrec.comp (canonicalPointListOfCode_primrec.comp Primrec.snd)
  -- the candidates of cardinality `k`
  have hsubs : Primrec fun y : (FamParams × BitString) × ℕ =>
      (canonicalFinsetList (canonicalPointListOfCode y.1.2).toFinset).sublists' :=
    coreSel_sublists'_primrec (hl.comp Primrec.fst)
  have hlen : Primrec₂ fun (y : (FamParams × BitString) × ℕ) (t : List BitString) =>
      decide (t.length = y.2) :=
    (Primrec.eq.decide.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  have hfil := primrec_list_filter hsubs hlen
  -- the eligibility test of a candidate
  have htest : Primrec₂ fun (y : (FamParams × BitString) × ℕ) (t : List BitString) =>
      coreEligBool (tableOut y.1.1.1.1) (tableOut y.1.1.1.2) y.1.1.2.1.2.1 y.1.1.2.1.2.2
        y.1.1.2.2.1.1 (canonicalFinsetList t.toFinset) := by
    have hgA : Primrec₂ fun (r : ((FamParams × BitString) × ℕ) × List BitString)
        (z : BitString) => tableOut r.1.1.1.1.1 z :=
      tableOut_primrec.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))) Primrec.snd
    have hgB : Primrec₂ fun (r : ((FamParams × BitString) × ℕ) × List BitString)
        (z : BitString) => tableOut r.1.1.1.1.2 z :=
      tableOut_primrec.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))) Primrec.snd
    have h := coreEligBool_primrec (β := ((FamParams × BitString) × ℕ) × List BitString)
      hgA hgB
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))))
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))))
      (canonicalFinsetList_toFinset_primrec.comp Primrec.snd)
    exact h.to₂
  have hfind := list_find?_primrec hfil htest
  have hmap := Primrec.option_map hfind
    (canonicalFiniteSetCode_toFinset_primrec.comp Primrec.snd).to₂
  have hrange : Primrec fun x : FamParams × BitString =>
      List.range (min x.1.2.2.1.2 (canonicalPointListOfCode x.2).length + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.nat_min.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.list_length.comp (canonicalPointListOfCode_primrec.comp Primrec.snd))))
  have hfm := Primrec.listFilterMap hrange hmap.to₂
  have hhead := Primrec.list_head?.comp hfm
  refine hhead.of_eq fun x => ?_
  have hnd : (canonicalFinsetList (parseModel x.2)).Nodup := canonicalFinsetList_nodup _
  have hpred : (fun t : List BitString => decide (CoreElig (famShape x.1) x.1.2.2.1.1 t.toFinset))
      = fun t => coreEligBool (tableOut x.1.1.1) (tableOut x.1.1.2) x.1.2.1.2.1 x.1.2.1.2.2
        x.1.2.2.1.1 (canonicalFinsetList t.toFinset) :=
    funext fun t => decide_coreElig_toFinset (famShape x.1) x.1.2.2.1.1 t
  dsimp only
  rw [List.head?_filterMap, minCoreSel, coreSel_map_findSome?, shapePR_card_parseModel]
  congr 1
  funext k
  rw [firstCoreOfCard, Option.map_map, coreSel_sublistsLen_eq_filter hnd, hpred]
  rfl

/-- One forward step of the minimum-core run on sets: select a capped minimum-cardinality
eligible subset of the remainder, append it and remove it; unchanged if nothing is selected. -/
def coreRunStep (P : ShapeParams) (s M : ℕ) (st : List (Finset BitString) × Finset BitString) :
    List (Finset BitString) × Finset BitString :=
  match minCoreSel P s M st.2 with
  | none => st
  | some T => (st.1 ++ [T], st.2 \ T)

/-- If nothing is selected in `rem`, the run stops immediately, whatever the fuel. -/
theorem coreRunAux_of_minCoreSel_none {P : ShapeParams} {s M : ℕ} {rem : Finset BitString}
    (h : minCoreSel P s M rem = none) (n : ℕ) : coreRunAux P s M n rem = ([], rem) := by
  cases n with
  | zero => simp only [coreRunAux]
  | succ n => simp only [coreRunAux, h]

/-- Iterating the forward step `n` times from `(cs, rem)` appends the family of
`coreRunAux P s M n rem` to `cs` and returns its residual. -/
theorem coreRunStep_iterate (P : ShapeParams) (s M n : ℕ) :
    ∀ (cs : List (Finset BitString)) (rem : Finset BitString),
      (coreRunStep P s M)^[n] (cs, rem) =
        (cs ++ (coreRunAux P s M n rem).1, (coreRunAux P s M n rem).2) := by
  induction n with
  | zero =>
    intro cs rem
    simp only [Function.iterate_zero, id_eq, coreRunAux, List.append_nil]
  | succ n ih =>
    intro cs rem
    rw [Function.iterate_succ_apply]
    cases hT : minCoreSel P s M rem with
    | none =>
      have hfix : coreRunStep P s M (cs, rem) = (cs, rem) := by
        simp only [coreRunStep, hT]
      rw [hfix, Function.iterate_fixed hfix, coreRunAux_of_minCoreSel_none hT, List.append_nil]
    | some T =>
      have hstep : coreRunStep P s M (cs, rem) = (cs ++ [T], rem \ T) := by
        simp only [coreRunStep, hT]
      rw [hstep, ih]
      simp only [coreRunAux, hT, List.append_assoc, List.singleton_append]

/-- One forward step of the minimum-core run on codes, for the family parameters `p`: the state
is (codes of the cores so far, code of the remainder); the selection is read on codes
(`minCoreSelCode_primrec`), its code is appended and its points are filtered out of the
remainder. -/
noncomputable def coreCodeStep (p : FamParams) (st : List BitString × BitString) :
    List BitString × BitString :=
  match (minCoreSel (famShape p) p.2.2.1.1 p.2.2.1.2 (parseModel st.2)).map
      canonicalFiniteSetCode with
  | none => st
  | some c => (st.1 ++ [c], canonicalFiniteSetCode ((canonicalPointListOfCode st.2).filter
      fun z => !decide (z ∈ canonicalPointListOfCode c)).toFinset)

/-- The code-level step is primitive recursive. -/
theorem coreCodeStep_primrec : Primrec₂ coreCodeStep := by
  have htup : Primrec fun q : FamParams × (List BitString × BitString) => (q.1, q.2.2) :=
    Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hsel : Primrec fun q : FamParams × (List BitString × BitString) =>
      (minCoreSel (famShape q.1) q.1.2.2.1.1 q.1.2.2.1.2 (parseModel q.2.2)).map
        canonicalFiniteSetCode :=
    (minCoreSelCode_primrec.comp htup).of_eq fun _ => rfl
  have hcodes : Primrec fun r : (FamParams × (List BitString × BitString)) × BitString =>
      r.1.2.1 ++ [r.2] :=
    Primrec.list_append.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  have hnotmem : Primrec₂ fun (r : (FamParams × (List BitString × BitString)) × BitString)
      (z : BitString) => !decide (z ∈ canonicalPointListOfCode r.2) :=
    (Primrec.not.comp (bitString_mem_primrec.comp Primrec.snd
      (canonicalPointListOfCode_primrec.comp (Primrec.snd.comp Primrec.fst)))).to₂
  have hrest : Primrec fun r : (FamParams × (List BitString × BitString)) × BitString =>
      canonicalFiniteSetCode ((canonicalPointListOfCode r.1.2.2).filter
        fun z => !decide (z ∈ canonicalPointListOfCode r.2)).toFinset :=
    canonicalFiniteSetCode_toFinset_primrec.comp (primrec_list_filter
      (canonicalPointListOfCode_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      hnotmem)
  have hsome : Primrec₂ fun (q : FamParams × (List BitString × BitString)) (c : BitString) =>
      (q.2.1 ++ [c], canonicalFiniteSetCode ((canonicalPointListOfCode q.2.2).filter
        fun z => !decide (z ∈ canonicalPointListOfCode c)).toFinset) :=
    (Primrec.pair hcodes hrest).to₂
  have h : Primrec fun q : FamParams × (List BitString × BitString) => coreCodeStep q.1 q.2 := by
    refine (Primrec.option_casesOn hsel Primrec.snd hsome).of_eq fun q => ?_
    rcases hq : (minCoreSel (famShape q.1) q.1.2.2.1.1 q.1.2.2.1.2 (parseModel q.2.2)).map
        canonicalFiniteSetCode with _ | c
    · simp only [coreCodeStep, hq]
    · simp only [coreCodeStep, hq]
  exact h.to₂

/-- The code-level state `st'` represents the set-level state `st`: its codes are the canonical
codes of the cores and its remainder code parses to the remainder. -/
def CoreCodeRel (st : List (Finset BitString) × Finset BitString)
    (st' : List BitString × BitString) : Prop :=
  st'.1 = st.1.map canonicalFiniteSetCode ∧ parseModel st'.2 = st.2

/-- One code-level step simulates one set-level step. -/
theorem coreCodeStep_rel (p : FamParams) {st : List (Finset BitString) × Finset BitString}
    {st' : List BitString × BitString} (h : CoreCodeRel st st') :
    CoreCodeRel (coreRunStep (famShape p) p.2.2.1.1 p.2.2.1.2 st) (coreCodeStep p st') := by
  obtain ⟨cs, rem⟩ := st
  obtain ⟨cs', w⟩ := st'
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  subst h1 h2
  rcases hT : minCoreSel (famShape p) p.2.2.1.1 p.2.2.1.2 (parseModel w) with _ | T
  · simp only [coreRunStep, coreCodeStep, hT, Option.map_none]
    exact ⟨rfl, rfl⟩
  · simp only [coreRunStep, coreCodeStep, CoreCodeRel, hT, Option.map_some, List.map_append,
      List.map_cons, List.map_nil, parseModel_canonicalFiniteSetCode, true_and]
    ext z
    simp [parseModel, canonicalPointListOfCode_canonicalFiniteSetCode]

/-- `n` code-level steps simulate `n` set-level steps. -/
theorem coreCode_rel_iterate (p : FamParams) (n : ℕ)
    {st : List (Finset BitString) × Finset BitString} {st' : List BitString × BitString}
    (h : CoreCodeRel st st') :
    CoreCodeRel ((coreRunStep (famShape p) p.2.2.1.1 p.2.2.1.2)^[n] st)
      ((coreCodeStep p)^[n] st') := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact coreCodeStep_rel p ih

/-- **The capped family and its residual are primitive recursive** in the family parameters.

Proof: the start set is the component (`shapeComponentCode_primrec`); the run
`coreRunAux P s M (|C| + 1) C` is the forward iteration of `coreRunStep`
(`coreRunStep_iterate`), simulated on codes by the primitive recursive step `coreCodeStep`
(`coreCodeStep_primrec`, `coreCode_rel_iterate`) run `|C| + 1` times with
`Primrec.nat_iterate` (as B2's `extract_code_primrec`). -/
theorem vertexCappedCodes_primrec :
    Primrec fun p : FamParams =>
      ((vertexCappedCores (famShape p) p.2.2.1.1 p.2.2.1.2 p.2.2.2).map canonicalFiniteSetCode,
        canonicalFiniteSetCode (vertexResidual (famShape p) p.2.2.1.1 p.2.2.1.2 p.2.2.2)) := by
  have hC := shapeComponentCode_primrec
  have hfuel := Primrec.succ.comp
    (Primrec.list_length.comp (canonicalPointListOfCode_primrec.comp hC))
  have hinit := Primrec.pair (Primrec.const ([] : List BitString)) hC
  have hiter := Primrec.nat_iterate hfuel hinit coreCodeStep_primrec
  have hout := Primrec.pair (Primrec.fst.comp hiter)
    (canonicalFiniteSetCode_toFinset_primrec.comp
      (canonicalPointListOfCode_primrec.comp (Primrec.snd.comp hiter)))
  refine hout.of_eq fun p => ?_
  unfold vertexCappedCores vertexResidual coreFamily coreResidual
  generalize shapeComponent (famShape p) (shapeEdges (famShape p)) p.2.2.2 = C
  have h0 : CoreCodeRel ([], C) ([], canonicalFiniteSetCode C) :=
    ⟨rfl, parseModel_canonicalFiniteSetCode C⟩
  have hR := coreCode_rel_iterate p (C.card + 1) h0
  rw [coreRunStep_iterate, List.nil_append] at hR
  obtain ⟨h1, h2⟩ := hR
  dsimp only at h1 h2
  rw [canonicalPointListOfCode_canonicalFiniteSetCode, length_canonicalFinsetList]
  have h2' : (canonicalPointListOfCode ((coreCodeStep p)^[C.card + 1]
      ([], canonicalFiniteSetCode C)).2).toFinset =
      (coreRunAux (famShape p) p.2.2.1.1 p.2.2.1.2 (C.card + 1) C).2 := h2
  rw [h1, h2']

/-- **The full family is computable from the tables.**  The list of canonical codes of
`vertexCores` of the table shape is primitive recursive in the tables, `(n, a, b)`, the budget and
the vertex: it is the capped family at the cap `|C_0|`, read off the component code. -/
theorem vertexCores_codes_primrec :
    Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
        (ℕ × ℕ × ℕ) × ℕ × (BitString ⊕ BitString) =>
      (vertexCores (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2) q.2.2.1 q.2.2.2).map
        canonicalFiniteSetCode := by
  have hg := Primrec.pair (Primrec.fst (α := List (BitString × BitString) ×
      List (BitString × BitString)) (β := (ℕ × ℕ × ℕ) × ℕ × (BitString ⊕ BitString)))
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const 0)) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hC := shapeComponentCode_primrec.comp hg
  have hlen := Primrec.list_length.comp (canonicalPointListOfCode_primrec.comp hC)
  have hg' := Primrec.pair (Primrec.fst (α := List (BitString × BitString) ×
      List (BitString × BitString)) (β := (ℕ × ℕ × ℕ) × ℕ × (BitString ⊕ BitString)))
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hlen)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have h := Primrec.fst.comp (vertexCappedCodes_primrec.comp hg')
  refine h.of_eq fun q => ?_
  dsimp only
  rw [canonicalPointListOfCode_canonicalFiniteSetCode, length_canonicalFinsetList]
  rfl

/-- **The local core kernel is partial recursive**: on codes, the incident cores are a
`List.filter` (incidence by `list_any_primrec` over the canonical point list) of the family codes
(`vertexCores_codes_primrec`), followed by `List.getD`; relate by `List.filter_map`,
`List.getD_map` and a pointwise equality of the incidence tests. -/
theorem localCoreKer_partrec : Partrec localCoreKer := by
  have hq : Primrec fun r : CoreIn × (BitString ⊕ BitString) × ℕ => r.1 := Primrec.fst
  have hv : Primrec fun r : CoreIn × (BitString ⊕ BitString) × ℕ => r.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hi : Primrec fun r : CoreIn × (BitString ⊕ BitString) × ℕ => r.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hs : Primrec fun r : CoreIn × (BitString ⊕ BitString) × ℕ => r.1.2.1.getD 4 0 :=
    (Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 4)
  have hpar := Primrec.pair (Primrec.fst.comp hq)
    (Primrec.pair (inNAB_primrec.comp hq) (Primrec.pair hs hv))
  have hcodes := vertexCores_codes_primrec.comp hpar
  have hA : Primrec fun x : ((CoreIn × (BitString ⊕ BitString) × ℕ) × BitString) × BitString =>
      decide ((Sum.inl (tableOut x.1.1.1.1.1 x.2) : BitString ⊕ BitString) = x.1.1.2.1) :=
    Primrec.eq.decide.comp (Primrec.sumInl.comp (tableOut_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hB : Primrec fun x : ((CoreIn × (BitString ⊕ BitString) × ℕ) × BitString) × BitString =>
      decide ((Sum.inr (tableOut x.1.1.1.1.2 x.2) : BitString ⊕ BitString) = x.1.1.2.1) :=
    Primrec.eq.decide.comp (Primrec.sumInr.comp (tableOut_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hor := Primrec.or.comp hA hB
  have htest : Primrec₂ fun (r : CoreIn × (BitString ⊕ BitString) × ℕ) (w : BitString) =>
      (canonicalPointListOfCode w).any fun z =>
        decide ((Sum.inl (tableOut r.1.1.1 z) : BitString ⊕ BitString) = r.2.1) ||
          decide ((Sum.inr (tableOut r.1.1.2 z) : BitString ⊕ BitString) = r.2.1) :=
    list_any_primrec (canonicalPointListOfCode_primrec.comp Primrec.snd) hor
  have hfil := primrec_list_filter hcodes htest
  have hget := (Primrec.list_getD (canonicalFiniteSetCode (∅ : Finset BitString))).comp hfil hi
  have harg : Computable fun q : CoreIn => (q, inEnd q, decodeBits q.2.2.1) :=
    Computable.pair Computable.id (Computable.pair inEnd_computable
      (decodeBits_computable.comp (Computable.fst.comp (Computable.snd.comp Computable.snd))))
  refine (hget.to_comp.comp harg).partrec.of_eq fun q => ?_
  have hpred : ∀ T : Finset BitString, ((canonicalFinsetList T).any fun z =>
      decide ((Sum.inl (tableOut q.1.1 z) : BitString ⊕ BitString) = inEnd q) ||
        decide ((Sum.inr (tableOut q.1.2 z) : BitString ⊕ BitString) = inEnd q)) =
      decide (∃ z ∈ T, shapeSrc (inShape q) z = inEnd q ∨ shapeTgt (inShape q) z = inEnd q) := by
    intro T
    rw [Bool.eq_iff_iff]
    simp [List.any_eq_true, mem_canonicalFinsetList, shapeSrc, shapeTgt, inShape, tableShape]
  simp only [PFun.coe_val, localCoreKer, incidentCores, List.filter_map, List.getD_map,
    Function.comp_def, canonicalPointListOfCode_canonicalFiniteSetCode, hpred]
  rfl

/-- **The point core kernel is partial recursive**: `List.find?` of the membership test on the
family codes (`vertexCores_codes_primrec`, `list_find?_primrec`), then `Option.getD`; relate by
`List.find?_map` and `Option.getD_map`.  (Closing such goals by `rfl` before the predicates are
syntactically equal makes `whnf` unfold the run inside `vertexCores` and time out.) -/
theorem pointCoreKer_partrec : Partrec pointCoreKer := by
  have hy : Primrec fun q : CoreIn => q.2.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hv : Primrec fun q : CoreIn => (Sum.inl (tableOut q.1.1 q.2.2.2) : BitString ⊕ BitString) :=
    Primrec.sumInl.comp (tableOut_primrec.comp (Primrec.fst.comp Primrec.fst) hy)
  have hs : Primrec fun q : CoreIn => q.2.1.getD 4 0 :=
    (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.snd) (Primrec.const 4)
  have hpar := Primrec.pair (Primrec.fst (α := List (BitString × BitString) ×
    List (BitString × BitString)) (β := List ℕ × BitString × BitString))
    (Primrec.pair inNAB_primrec (Primrec.pair hs hv))
  have hcodes := vertexCores_codes_primrec.comp hpar
  have htest : Primrec₂ fun (q : CoreIn) (w : BitString) =>
      decide (q.2.2.2 ∈ canonicalPointListOfCode w) :=
    bitString_mem_primrec.comp (hy.comp Primrec.fst)
      (canonicalPointListOfCode_primrec.comp Primrec.snd)
  have hfind := list_find?_primrec hcodes htest
  have hget := Primrec.option_getD.comp hfind
    (Primrec.const (canonicalFiniteSetCode (∅ : Finset BitString)))
  refine hget.to_comp.partrec.of_eq fun q => ?_
  simp only [pointCoreKer, coreOf, List.find?_map, Option.getD_map, Function.comp_def,
    canonicalPointListOfCode_canonicalFiniteSetCode, mem_canonicalFinsetList]
  rfl

/-- Cores computed at either endpoint of the actual string are the same family. -/
theorem vertexCores_tgt_eq_src {P : ShapeParams} (s : ℕ) {x : BitString}
    (hx : x ∈ shapeEdges P) : vertexCores P s (shapeTgt P x) = vertexCores P s (shapeSrc P x) := by
  unfold vertexCores
  rw [shapeComponent_src_eq_tgt hx]

/-- **A selected core has a short local rank at each endpoint** of `x`: it is the entry of rank
`i < 2^(s+1)` among the cores incident to the endpoint (`s ≤ a, b`).

Proof sketch: `coreOf_spec` gives `F ∈ vertexCores P s (shapeSrc P x)` and `x ∈ F`; at the column
endpoint the family is the same (`vertexCores_tgt_eq_src`).  `F` is incident to the endpoint
(witness `x`), so it lies in the filtered list; take its index (`List.mem_iff_getElem`,
`List.getD_eq_getElem`) and bound it by `length_incidentCores_lt`. -/
theorem exists_local_index {P : ShapeParams} {s : ℕ} (hsa : s ≤ P.a) (hsb : s ≤ P.b)
    {x : BitString} (hx : x ∈ shapeEdges P) {F : Finset BitString} (hF : coreOf P s x = some F)
    (side : Bool) :
    ∃ i < 2 ^ (s + 1), (incidentCores P (vertexCores P s (if side then shapeTgt P x
      else shapeSrc P x)) (if side then shapeTgt P x else shapeSrc P x)).getD i ∅ = F := by
  obtain ⟨hFmem, hxF⟩ := coreOf_spec hF
  have key : ∀ v, vertexCores P s v = vertexCores P s (shapeSrc P x) →
      (shapeSrc P x = v ∨ shapeTgt P x = v) →
        ∃ i < 2 ^ (s + 1), (incidentCores P (vertexCores P s v) v).getD i ∅ = F := by
    intro v hfam hinc
    have hmem : F ∈ incidentCores P (vertexCores P s v) v := by
      unfold incidentCores
      rw [List.mem_filter, hfam]
      exact ⟨hFmem, decide_eq_true ⟨x, hxF, hinc⟩⟩
    obtain ⟨i, hi, hiF⟩ := List.mem_iff_getElem.mp hmem
    refine ⟨i, hi.trans (length_incidentCores_lt P s hsa hsb v v), ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hiF]
  cases side
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact key _ rfl (Or.inl rfl)
  · simp only [↓reduceIte]
    exact key _ (vertexCores_tgt_eq_src s hx) (Or.inr rfl)

/-- **The local decoder (blueprint M03, `UpperMinCoreLocalDecoder`).**  For an optimal plain
machine `V` there is a constant `c` such that at every qualifying instance and every budget
`s ≤ a, b`, if `x` lies in a selected core `F_s` (`coreOf … s x = some F`), then
`CT(F_s | A), CT(F_s | B) ≤ s + c H` (one total program: the table machine with the local kernel,
whose packet carries `n, a, b, side, s`, the witnesses and the local rank in at most `s + 1` bits)
and `C(F_s | x) ≤ c H` (the point kernel, which carries no local rank).  The decoders return `∅`
when the requested core is absent.  Nothing relates the cores at different budgets. -/
theorem upperMinCoreLocalDecoder (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) (s : ℕ)
      (F : Finset BitString), IsCoreInstance V n e pA pB x A B →
        s ≤ Nat.log 2 A.card → s ≤ Nat.log 2 B.card →
        coreOf (coreShape pA pB n A B) s x = some F →
          totalC (canonicalFiniteSetCode F) (canonicalFiniteSetCode A) ≤ s + c * baseBudget n e ∧
          totalC (canonicalFiniteSetCode F) (canonicalFiniteSetCode B) ≤ s + c * baseBudget n e ∧
          condC V (canonicalFiniteSetCode F) x ≤ c * baseBudget n e := by
  obtain ⟨cD, hcD⟩ := totalC_le_of_decoder (coreMachine 5 localCoreKer)
    (coreMachine_partrec 5 localCoreKer_partrec)
  obtain ⟨cP, hcP⟩ := condC_le_of_decoder V hV (coreMachine 5 pointCoreKer)
    (coreMachine_partrec 5 pointCoreKer_partrec)
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  obtain ⟨cpk, hpk⟩ := length_corePacket_le 5 (bsize + 3)
  refine ⟨cpk + cD + cP + 1, fun n e pA pB x A B s F h hsa hsb hF => ?_⟩
  have hxG := h.mem_shapeEdges
  have ha := (htyp n e x A h.length_x h.le_n h.sufA).2
  have hb := (htyp n e x B h.length_x h.le_n h.sufB).2
  have hH : (1 : ℝ) ≤ baseBudget n e := by
    have := one_le_headerLog n
    unfold baseBudget
    exact_mod_cast (by omega : 1 ≤ e + headerLog n)
  have hfields : ∀ (t : ℕ), t ≤ 1 → ∀ k ∈ [n, Nat.log 2 A.card, Nat.log 2 B.card, t, s],
      k ≤ (bsize + 3) * (n + 1) := by
    intro t ht k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> nlinarith
  have hcD0 : (cD : ℝ) ≤ cD * baseBudget n e := le_mul_of_one_le_right (Nat.cast_nonneg _) hH
  have hcP0 : (cP : ℝ) ≤ cP * baseBudget n e := le_mul_of_one_le_right (Nat.cast_nonneg _) hH
  have hpos : (0 : ℝ) ≤ (cpk : ℝ) * baseBudget n e := by positivity
  have hpos' : (0 : ℝ) ≤ (cD : ℝ) * baseBudget n e := by positivity
  have hpos'' : (0 : ℝ) ≤ (cP : ℝ) * baseBudget n e := by positivity
  -- the local decoder at either endpoint
  have key : ∀ (side : Bool) (y : BitString),
      coreEnd side y = (if side then shapeTgt (coreShape pA pB n A B) x
        else shapeSrc (coreShape pA pB n A B) x) →
        totalC (canonicalFiniteSetCode F) y ≤
          s + ((cpk + cD + cP + 1 : ℕ) : ℝ) * baseBudget n e := by
    intro side y hy
    obtain ⟨i, hi, hiF⟩ := exists_local_index (P := coreShape pA pB n A B) hsa hsb hxG hF side
    obtain ⟨TA, TB, hTA, hTB, heval⟩ := coreMachine_eval 5 localCoreKer
      (ks := [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, s]) rfl h.totalA h.totalB
      (Nat.bits i)
    have hag : (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)).AgreeOn
        (coreShape pA pB n A B) := tableShape_agreeOn (n := n) hTA hTB
    have hout : ∀ y', coreMachine 5 localCoreKer
        (corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, s] pA pB (Nat.bits i), y')
          = Part.some (canonicalFiniteSetCode ((incidentCores (coreShape pA pB n A B)
            (vertexCores (coreShape pA pB n A B) s (coreEnd side y')) (coreEnd side y')).getD
              i ∅)) := by
      intro y'
      rw [heval y']
      unfold localCoreKer inEnd
      dsimp only
      rw [inShape_mk, inSide_mk, inBudget_mk, (vertexCores_congr hag s 0 _).2.1,
        decodeBits_natBits]
      have hinc : incidentCores (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card))
          (vertexCores (coreShape pA pB n A B) s (coreEnd side y')) (coreEnd side y') =
          incidentCores (coreShape pA pB n A B)
            (vertexCores (coreShape pA pB n A B) s (coreEnd side y')) (coreEnd side y') := by
        unfold incidentCores
        apply List.filter_congr
        intro T hT
        have hlen : ∀ z ∈ T, z.length = n := by
          intro z hz
          have hsub := (coreRunAux_mem _ s _ _ _ T hT).2.1
          exact (mem_stringsOfLength _ _).mp
            (Finset.mem_filter.mp (shapeComponent_subset _ _ _ (hsub hz))).1
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨z, hz, hzv⟩
          refine ⟨z, hz, ?_⟩
          obtain ⟨h1, h2⟩ := hag.2.2.2 z (hlen z hz)
          simpa only [shapeSrc, shapeTgt, h1, h2] using hzv
        · rintro ⟨z, hz, hzv⟩
          refine ⟨z, hz, ?_⟩
          obtain ⟨h1, h2⟩ := hag.2.2.2 z (hlen z hz)
          simpa only [shapeSrc, shapeTgt, h1, h2] using hzv
      rw [hinc]
    have hdom : ∀ y', (coreMachine 5 localCoreKer
        (corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, s] pA pB (Nat.bits i),
          y')).Dom := by
      intro y'
      rw [hout y']
      trivial
    have hmem : canonicalFiniteSetCode F ∈ coreMachine 5 localCoreKer
        (corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, s] pA pB (Nat.bits i),
          y) := by
      rw [hout y, hy, hiF]
      exact Part.mem_some _
    have h1 := hcD _ hdom y _ hmem
    have h2 := hpk n e _ pA pB (Nat.bits i) (by simp) (hfields _ (Bool.toNat_le side))
      h.lenA h.lenB h.le_n
    have hbits : (Nat.bits i).length ≤ s + 1 := by
      rw [Nat.size_eq_bits_len, Nat.size_le]
      exact hi
    have h3 : ((corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, s] pA pB
        (Nat.bits i)).length : ℝ) ≤ (s + 1 : ℕ) + cpk * baseBudget n e := by
      exact_mod_cast h2.trans (by omega)
    push_cast at h3 ⊢
    nlinarith
  refine ⟨key false _ ?_, key true _ ?_, ?_⟩
  · simp only [coreEnd, shapeSrc, h.outA_eq, Bool.false_eq_true, ↓reduceIte]
  · simp only [coreEnd, shapeTgt, h.outB_eq, ↓reduceIte]
  · -- the point decoder
    obtain ⟨TA, TB, hTA, hTB, heval⟩ := coreMachine_eval 5 pointCoreKer
      (ks := [n, Nat.log 2 A.card, Nat.log 2 B.card, 0, s]) rfl h.totalA h.totalB []
    have hag : (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)).AgreeOn
        (coreShape pA pB n A B) := tableShape_agreeOn (n := n) hTA hTB
    have hmem : canonicalFiniteSetCode F ∈ coreMachine 5 pointCoreKer
        (corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, 0, s] pA pB [], x) := by
      rw [heval x]
      unfold pointCoreKer
      dsimp only
      rw [inShape_mk, inBudget_mk, coreOf_congr hag s h.length_x]
      rw [hF]
      exact Part.mem_some _
    have h1 := hcP _ x _ hmem
    have h2 := hpk n e _ pA pB [] (by simp) (hfields 0 (Nat.zero_le _)) h.lenA h.lenB h.le_n
    simp only [List.length_nil, zero_add] at h2
    have h3 : ((corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, 0, s] pA pB []).length
        : ℝ) ≤ cpk * baseBudget n e := by exact_mod_cast h2
    push_cast
    nlinarith

end Kolmogorov.StrongMerging.Upper
