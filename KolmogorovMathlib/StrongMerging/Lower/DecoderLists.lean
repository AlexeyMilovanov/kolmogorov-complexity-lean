import KolmogorovMathlib.StrongMerging.Lower.Models
import KolmogorovMathlib.StrongMerging.Upper.Graph
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# The sharp lower bound: list implementations of the packet decoders

Shared computability layer of the three packet decoders of nodes L31 (`exists_peelDecoder`),
L34 (`exists_projDecoder`) and L35 (`exists_coreDecoder`) of the formalization of
`sublinear-merging.tex` (tex lines 1698-1806; blueprint L31, L34, L35, lines 4921-5026).

Mathlib has no `Primcodable (Finset BitString)`, so every `Finset` object of `Models` used by a
decoder is computed on explicit lists, which are primitive recursive, and then compared with the
`Finset` definition.

* `labelGraphList fA fB M j z` lists the edges of `labelGraph fA fB M j z` without repetition,
  reading the halves of the points of the decoded model (`labelGraphList_toFinset`,
  `labelGraphList_nodup`); it is primitive recursive when the output maps are
  (`primrec_labelGraphList`), and it only depends on the output maps on the codes of the stars of
  the halves of the decoded points (`labelGraphList_congr`).
* `peelRoundList`, `peelStageList`, `peelCoreList`, `ownedLList`, `ownedRList` implement the
  peeling of `Models` on duplicate-free lists (`peelStageList_spec`,
  `peelCoreList_toFinset`, `ownedLList_toFinset`, `ownedRList_toFinset`) and are primitive
  recursive.
* **Graph search** (`exists_graphSearch`): one partial recursive map returns, from the two
  witness bodies, `M`, `j` and a label `z`, the list of edges of the graph of `z` built from the
  actual outputs of the two witnesses, whenever these are total.  It runs the step-bounded
  evaluator of `universalDecompressor` until all the finitely many needed evaluations have halted.
* `peelValueList`, `projCodeList`, `coreCodeList` are the three post-processing steps, with their
  agreement with the `Finset` values and their computability.
* `popField`, `fieldAt` read the numeric fields of a packet (`numPacket`).
* `searchDecoder V S a g post` is the common shape of the three decoders: run `V` on the query
  `a (w, y)` to get a label, run the graph search on `g (w, y) z`, post-process by `post (w, y)`;
  it is partial recursive for computable pieces (`partrec_searchDecoder`).  The pieces are
  `labelQuery`, `graphQuery`, `peelPost`, `projPost` (L31, L34) and `coreLabelQuery`,
  `coreGraphQuery`, `corePost` (L35).
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### Star codes and the labelled graph on lists -/

/-- The canonical model encoder on lists is primitive recursive. -/
theorem primrec_listModelCode : Primrec listModelCode :=
  Upper.canonicalFiniteSetCode_toFinset_primrec.of_eq fun _ => rfl

/-- The code of a row star is primitive recursive in the radius and the center. -/
theorem primrec_rowStar_code :
    Primrec₂ fun (j : ℕ) (y : BitString) => canonicalFiniteSetCode (rowStar j y) :=
  (Upper.canonicalFiniteSetCode_toFinset_primrec.comp primrec_rowStarList).of_eq fun p => by
    simp only [rowStarList_toFinset]

/-- The code of a column star is primitive recursive in the radius and the center. -/
theorem primrec_colStar_code :
    Primrec₂ fun (j : ℕ) (w : BitString) => canonicalFiniteSetCode (colStar j w) :=
  (Upper.canonicalFiniteSetCode_toFinset_primrec.comp primrec_colStarList).of_eq fun p => by
    simp only [colStarList_toFinset]

/-- The edge read off a point `x` of a decoded model: the pair of halves of `x` if `x` has
length `2M`, its halves are at distance `j`, and both witnesses map the stars of the halves to
the label `z`; otherwise nothing. -/
noncomputable def edgeOf (fA fB : BitString → BitString) (M j : ℕ) (z x : BitString) :
    Option (BitString × BitString) :=
  if x.length = 2 * M ∧ hammingDist (leftHalf x) (rightHalf x) = j ∧
      fA (canonicalFiniteSetCode (rowStar j (leftHalf x))) = z ∧
      fB (canonicalFiniteSetCode (colStar j (rightHalf x))) = z then
    some (leftHalf x, rightHalf x)
  else none

/-- **The labelled graph on lists**: the edges read off the points of the decoded model, in the
order of `canonicalPointListOfCode z`. -/
noncomputable def labelGraphList (fA fB : BitString → BitString) (M j : ℕ) (z : BitString) :
    List (BitString × BitString) :=
  (canonicalPointListOfCode z).filterMap (edgeOf fA fB M j z)

/-- The halves of a word of length `2M` have length `M` and recompose the word. -/
theorem halves_of_length {x : BitString} {M : ℕ} (hx : x.length = 2 * M) :
    (leftHalf x).length = M ∧ (rightHalf x).length = M ∧ leftHalf x ++ rightHalf x = x := by
  refine ⟨?_, ?_, List.take_append_drop _ _⟩
  · simp only [leftHalf, List.length_take]
    omega
  · simp only [rightHalf, List.length_drop]
    omega

/-- A successful edge reading returns the halves of a word of length `2M`. -/
theorem edgeOf_eq_some {fA fB : BitString → BitString} {M j : ℕ} {z x : BitString}
    {e : BitString × BitString} (h : edgeOf fA fB M j z x = some e) :
    x.length = 2 * M ∧ e = (leftHalf x, rightHalf x) := by
  unfold edgeOf at h
  split_ifs at h with hc
  · exact ⟨hc.1, (Option.some.inj h).symm⟩

/-- The list graph has exactly the edges of the `Finset` graph `labelGraph`. -/
theorem mem_labelGraphList {fA fB : BitString → BitString} {M j : ℕ} {z : BitString}
    {e : BitString × BitString} :
    e ∈ labelGraphList fA fB M j z ↔ e ∈ labelGraph fA fB M j z := by
  rw [mem_labelGraph]
  simp only [labelGraphList, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hex⟩
    have hc : x.length = 2 * M ∧ hammingDist (leftHalf x) (rightHalf x) = j ∧
        fA (canonicalFiniteSetCode (rowStar j (leftHalf x))) = z ∧
        fB (canonicalFiniteSetCode (colStar j (rightHalf x))) = z := by
      by_contra hc
      unfold edgeOf at hex
      rw [ite_eq_right hc] at hex
      cases hex
    obtain ⟨-, rfl⟩ := edgeOf_eq_some hex
    obtain ⟨hl, hr, hlr⟩ := halves_of_length hc.1
    refine ⟨hl, hr, ?_, hc.2.1, hc.2.2.1, hc.2.2.2⟩
    rw [hlr, decodeModel, List.mem_toFinset]
    exact hx
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨e.1 ++ e.2, ?_, ?_⟩
    · rw [decodeModel, List.mem_toFinset] at h3
      exact h3
    · obtain ⟨hl, hr⟩ := halves_append (h1.trans h2.symm)
      have hlen : (e.1 ++ e.2).length = 2 * M := by
        rw [List.length_append, h1, h2]
        ring
      unfold edgeOf
      rw [ite_eq_left ⟨hlen, by rw [hl, hr]; exact h4, by rw [hl]; exact h5,
        by rw [hr]; exact h6⟩, hl, hr]

/-- The list graph enumerates the `Finset` graph `labelGraph`. -/
theorem labelGraphList_toFinset (fA fB : BitString → BitString) (M j : ℕ) (z : BitString) :
    (labelGraphList fA fB M j z).toFinset = labelGraph fA fB M j z := by
  ext e
  rw [List.mem_toFinset, mem_labelGraphList]

/-- The list graph has no repetitions: the decoded point list has none, and a point is the
concatenation of the halves read off it. -/
theorem labelGraphList_nodup (fA fB : BitString → BitString) (M j : ℕ) (z : BitString) :
    (labelGraphList fA fB M j z).Nodup := by
  refine List.Nodup.filterMap ?_ (canonicalFinsetList_nodup _)
  intro x x' e hx hx'
  obtain ⟨h1, rfl⟩ := edgeOf_eq_some (Option.mem_def.1 hx)
  obtain ⟨h1', he⟩ := edgeOf_eq_some (Option.mem_def.1 hx')
  rw [← (halves_of_length h1).2.2, ← (halves_of_length h1').2.2]
  simp only [Prod.mk.injEq] at he
  rw [he.1, he.2]

/-- The codes of the row stars of the left halves of the decoded points: the inputs on which
the first witness is evaluated by the list graph. -/
noncomputable def neededRow (j : ℕ) (z : BitString) : List BitString :=
  (canonicalPointListOfCode z).map fun x => canonicalFiniteSetCode (rowStar j (leftHalf x))

/-- The codes of the column stars of the right halves of the decoded points: the inputs on which
the second witness is evaluated by the list graph. -/
noncomputable def neededCol (j : ℕ) (z : BitString) : List BitString :=
  (canonicalPointListOfCode z).map fun x => canonicalFiniteSetCode (colStar j (rightHalf x))

/-- The list graph depends on the output maps only through their values on `neededRow` and
`neededCol`. -/
theorem labelGraphList_congr {fA fB gA gB : BitString → BitString} {M j : ℕ} {z : BitString}
    (hA : ∀ c ∈ neededRow j z, fA c = gA c) (hB : ∀ c ∈ neededCol j z, fB c = gB c) :
    labelGraphList fA fB M j z = labelGraphList gA gB M j z := by
  unfold labelGraphList
  refine List.filterMap_congr fun x hx => ?_
  unfold edgeOf
  rw [hA _ (List.mem_map_of_mem hx), hB _ (List.mem_map_of_mem hx)]

/-- **The list graph is primitive recursive** in its parameters when the output maps are. -/
theorem primrec_labelGraphList {α : Type} [Primcodable α] {F G : α → BitString → BitString}
    {M j : α → ℕ} {z : α → BitString} (hF : Primrec₂ F) (hG : Primrec₂ G) (hM : Primrec M)
    (hj : Primrec j) (hz : Primrec z) :
    Primrec fun a => labelGraphList (F a) (G a) (M a) (j a) (z a) := by
  obtain ⟨hl, hr⟩ := primrec_halves
  have hg : Primrec₂ fun (a : α) (x : BitString) => edgeOf (F a) (G a) (M a) (j a) (z a) x := by
    change Primrec fun p : α × BitString => edgeOf (F p.1) (G p.1) (M p.1) (j p.1) (z p.1) p.2
    unfold edgeOf
    refine Primrec.ite ?_ ?_ (Primrec.const none)
    · refine PrimrecPred.and ?_ (PrimrecPred.and ?_ (PrimrecPred.and ?_ ?_))
      · exact Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
          (Primrec.nat_mul.comp (Primrec.const 2) (hM.comp Primrec.fst))
      · exact Primrec.eq.comp (hammingDist_primrec.comp (hl.comp Primrec.snd)
          (hr.comp Primrec.snd)) (hj.comp Primrec.fst)
      · exact Primrec.eq.comp (hF.comp Primrec.fst (primrec_rowStar_code.comp
          (hj.comp Primrec.fst) (hl.comp Primrec.snd))) (hz.comp Primrec.fst)
      · exact Primrec.eq.comp (hG.comp Primrec.fst (primrec_colStar_code.comp
          (hj.comp Primrec.fst) (hr.comp Primrec.snd))) (hz.comp Primrec.fst)
    · exact Primrec.option_some.comp (Primrec.pair (hl.comp Primrec.snd) (hr.comp Primrec.snd))
  exact Primrec.listFilterMap (canonicalPointListOfCode_primrec.comp hz) hg

/-- The needed row inputs are primitive recursive. -/
theorem primrec_neededRow : Primrec₂ neededRow := by
  obtain ⟨hl, -⟩ := primrec_halves
  exact Primrec.list_map (canonicalPointListOfCode_primrec.comp Primrec.snd)
    (primrec_rowStar_code.comp (Primrec.fst.comp Primrec.fst) (hl.comp Primrec.snd))

/-- The needed column inputs are primitive recursive. -/
theorem primrec_neededCol : Primrec₂ neededCol := by
  obtain ⟨-, hr⟩ := primrec_halves
  exact Primrec.list_map (canonicalPointListOfCode_primrec.comp Primrec.snd)
    (primrec_colStar_code.comp (Primrec.fst.comp Primrec.fst) (hr.comp Primrec.snd))

/-! ### Peeling on lists -/

section PeelList

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The degree of a left vertex in an edge list. -/
def degLList (L : List (α × β)) (a : α) : ℕ :=
  (L.filter fun e => e.1 = a).length

/-- The degree of a right vertex in an edge list. -/
def degRList (L : List (α × β)) (b : β) : ℕ :=
  (L.filter fun e => e.2 = b).length

/-- One peeling round on an edge list (list form of `peelRound`). -/
def peelRoundList (θ : ℕ) (L : List (α × β)) : List (α × β) :=
  L.filter fun e => θ ≤ degLList L e.1 ∧ θ ≤ degRList L e.2

/-- The edge list after `k` peeling rounds (list form of `peelStage`). -/
def peelStageList (θ : ℕ) (L : List (α × β)) (k : ℕ) : List (α × β) :=
  (peelRoundList θ)^[k] L

/-- The core of an edge list: `|L|` peeling rounds (list form of `peelCore`). -/
def peelCoreList (θ : ℕ) (L : List (α × β)) : List (α × β) :=
  peelStageList θ L L.length

/-- The edges owned by a left vertex (list form of `ownedL`). -/
def ownedLList (θ : ℕ) (L : List (α × β)) (a : α) : List (α × β) :=
  (List.range L.length).flatMap fun k =>
    if degLList (peelStageList θ L k) a < θ then (peelStageList θ L k).filter (fun e => e.1 = a)
    else []

/-- The edges owned by a right vertex (list form of `ownedR`). -/
def ownedRList (θ : ℕ) (L : List (α × β)) (b : β) : List (α × β) :=
  (List.range L.length).flatMap fun k =>
    if degRList (peelStageList θ L k) b < θ then (peelStageList θ L k).filter (fun e => e.2 = b)
    else []

/-- On a duplicate-free list, the list degree is the `Finset` degree. -/
theorem degLList_eq {L : List (α × β)} (hL : L.Nodup) (a : α) :
    degLList L a = degL L.toFinset a := by
  unfold degLList degL
  rw [← List.toFinset_card_of_nodup (hL.filter _), List.toFinset_filter]
  simp

/-- On a duplicate-free list, the list degree is the `Finset` degree. -/
theorem degRList_eq {L : List (α × β)} (hL : L.Nodup) (b : β) :
    degRList L b = degR L.toFinset b := by
  unfold degRList degR
  rw [← List.toFinset_card_of_nodup (hL.filter _), List.toFinset_filter]
  simp

/-- A list peeling round of a duplicate-free list enumerates the `Finset` round. -/
theorem peelRoundList_toFinset {L : List (α × β)} (hL : L.Nodup) (θ : ℕ) :
    (peelRoundList θ L).toFinset = peelRound θ L.toFinset := by
  ext e
  simp only [peelRoundList, peelRound, List.mem_toFinset, List.mem_filter, mem_filter,
    degLList_eq hL, degRList_eq hL, decide_eq_true_eq]

/-- The list stages of a duplicate-free list have no repetitions and enumerate the `Finset`
stages. -/
theorem peelStageList_spec {L : List (α × β)} (hL : L.Nodup) (θ k : ℕ) :
    (peelStageList θ L k).Nodup ∧ (peelStageList θ L k).toFinset = peelStage θ L.toFinset k := by
  induction k with
  | zero => exact ⟨hL, rfl⟩
  | succ k ih =>
    have h : peelStageList θ L (k + 1) = peelRoundList θ (peelStageList θ L k) := by
      unfold peelStageList
      rw [Function.iterate_succ_apply']
    rw [h, peelStage_succ, ← ih.2]
    exact ⟨ih.1.filter _, peelRoundList_toFinset ih.1 θ⟩

/-- The list core of a duplicate-free list enumerates the `Finset` core. -/
theorem peelCoreList_toFinset {L : List (α × β)} (hL : L.Nodup) (θ : ℕ) :
    (peelCoreList θ L).toFinset = peelCore θ L.toFinset := by
  rw [peelCoreList, (peelStageList_spec hL θ _).2, peelCore, List.toFinset_card_of_nodup hL]

/-- The owned edges of a left vertex, on a duplicate-free list, enumerate `ownedL`. -/
theorem ownedLList_toFinset {L : List (α × β)} (hL : L.Nodup) (θ : ℕ) (a : α) :
    (ownedLList θ L a).toFinset = ownedL θ L.toFinset a := by
  ext e
  simp only [ownedLList, ownedL, List.mem_toFinset, List.mem_flatMap, List.mem_range,
    mem_biUnion, mem_range, List.toFinset_card_of_nodup hL]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  obtain ⟨hnd, hfs⟩ := peelStageList_spec hL θ k
  rw [degLList_eq hnd, hfs]
  split_ifs
  · rw [← hfs]
    simp
  · simp

/-- The owned edges of a right vertex, on a duplicate-free list, enumerate `ownedR`. -/
theorem ownedRList_toFinset {L : List (α × β)} (hL : L.Nodup) (θ : ℕ) (b : β) :
    (ownedRList θ L b).toFinset = ownedR θ L.toFinset b := by
  ext e
  simp only [ownedRList, ownedR, List.mem_toFinset, List.mem_flatMap, List.mem_range,
    mem_biUnion, mem_range, List.toFinset_card_of_nodup hL]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  obtain ⟨hnd, hfs⟩ := peelStageList_spec hL θ k
  rw [degRList_eq hnd, hfs]
  split_ifs
  · rw [← hfs]
    simp
  · simp

end PeelList

/-! ### Computability of the list peeling -/

/-- Edge lists of pairs of words. -/
abbrev EdgeList := List (BitString × BitString)

/-- The list degree of a left vertex is primitive recursive. -/
theorem primrec_degLList : Primrec₂ (degLList : EdgeList → BitString → ℕ) :=
  Primrec.list_length.comp (Upper.primrec_list_filter Primrec.fst
    (PrimrecPred.decide (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst))))

/-- The list degree of a right vertex is primitive recursive. -/
theorem primrec_degRList : Primrec₂ (degRList : EdgeList → BitString → ℕ) :=
  Primrec.list_length.comp (Upper.primrec_list_filter Primrec.fst
    (PrimrecPred.decide (Primrec.eq.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst))))

/-- A list peeling round is primitive recursive. -/
theorem primrec_peelRoundList : Primrec₂ (peelRoundList : ℕ → EdgeList → EdgeList) :=
  Upper.primrec_list_filter Primrec.snd (PrimrecPred.decide (PrimrecPred.and
    (Primrec.nat_le.comp (Primrec.fst.comp Primrec.fst)
      (primrec_degLList.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
    (Primrec.nat_le.comp (Primrec.fst.comp Primrec.fst)
      (primrec_degRList.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))))

/-- The list stages are primitive recursive in the threshold, the list and the stage. -/
theorem primrec_peelStageList :
    Primrec fun p : (ℕ × EdgeList) × ℕ => peelStageList p.1.1 p.1.2 p.2 :=
  Primrec.nat_iterate Primrec.snd (Primrec.snd.comp Primrec.fst)
    (primrec_peelRoundList.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      Primrec.snd)

/-- The list core is primitive recursive. -/
theorem primrec_peelCoreList : Primrec₂ (peelCoreList : ℕ → EdgeList → EdgeList) :=
  primrec_peelStageList.comp (Primrec.pair Primrec.id (Primrec.list_length.comp Primrec.snd))

/-- The owned edges of a left vertex are primitive recursive. -/
theorem primrec_ownedLList :
    Primrec fun p : (ℕ × EdgeList) × BitString => ownedLList p.1.1 p.1.2 p.2 := by
  have hst : Primrec fun q : ((ℕ × EdgeList) × BitString) × ℕ =>
      peelStageList q.1.1.1 q.1.1.2 q.2 :=
    primrec_peelStageList.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  refine Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp
    (Primrec.snd.comp Primrec.fst))) ?_
  refine Primrec.ite ?_ ?_ (Primrec.const [])
  · exact Primrec.nat_lt.comp (primrec_degLList.comp hst (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  · exact Upper.primrec_list_filter hst (PrimrecPred.decide (Primrec.eq.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))

/-- The owned edges of a right vertex are primitive recursive. -/
theorem primrec_ownedRList :
    Primrec fun p : (ℕ × EdgeList) × BitString => ownedRList p.1.1 p.1.2 p.2 := by
  have hst : Primrec fun q : ((ℕ × EdgeList) × BitString) × ℕ =>
      peelStageList q.1.1.1 q.1.1.2 q.2 :=
    primrec_peelStageList.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  refine Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp
    (Primrec.snd.comp Primrec.fst))) ?_
  refine Primrec.ite ?_ ?_ (Primrec.const [])
  · exact Primrec.nat_lt.comp (primrec_degRList.comp hst (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  · exact Upper.primrec_list_filter hst (PrimrecPred.decide (Primrec.eq.comp
      (Primrec.snd.comp Primrec.snd) (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))

/-! ### The graph search -/

/-- The step-indexed evaluator of `conditionalRunOut` is primitive recursive. -/
theorem primrec_conditionalRunOut (c : Nat.Partrec.Code) :
    Primrec (fun q : ℕ × BitString × BitString => conditionalRunOut c q.1 q.2.1 q.2.2) := by
  unfold conditionalRunOut
  apply Primrec.option_bind
  · exact (evaln_primrec c).comp Primrec.fst
      (Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))
  · exact Primrec.decode.comp Primrec.snd

/-- The output of the program `p` on the condition `c` after `s` steps, `[]` if not yet halted. -/
def stageOut (c₀ : Nat.Partrec.Code) (s : ℕ) (p c : BitString) : BitString :=
  (conditionalRunOut c₀ s p c).getD []

/-- Whether all runs of `p` on the conditions of `L` have halted within `s` steps. -/
def allHalted (c₀ : Nat.Partrec.Code) (s : ℕ) (p : BitString) (L : List BitString) : Bool :=
  L.all fun c => (conditionalRunOut c₀ s p c).isSome

/-- The query of the graph search: the two witness bodies, `M`, `j` and the label. -/
abbrev GraphQuery := BitString × BitString × ℕ × ℕ × BitString

/-- One stage of the graph search: if all needed runs of the two witnesses have halted within
`s` steps, the list graph built from their outputs. -/
noncomputable def graphAttempt (c₀ : Nat.Partrec.Code) (pA pB : BitString) (M j : ℕ)
    (z : BitString) (s : ℕ) : Option EdgeList :=
  bif allHalted c₀ s pA (neededRow j z) && allHalted c₀ s pB (neededCol j z) then
    some (labelGraphList (stageOut c₀ s pA) (stageOut c₀ s pB) M j z)
  else none

/-- The stage attempt of the graph search is primitive recursive. -/
theorem primrec_graphAttempt (c₀ : Nat.Partrec.Code) :
    Primrec₂ fun (Q : GraphQuery) (s : ℕ) =>
      graphAttempt c₀ Q.1 Q.2.1 Q.2.2.1 Q.2.2.2.1 Q.2.2.2.2 s := by
  have hrun := primrec_conditionalRunOut c₀
  have hA : Primrec fun p : (GraphQuery × ℕ) × BitString =>
      conditionalRunOut c₀ p.1.2 p.1.1.1 p.2 :=
    hrun.comp (Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
  have hB : Primrec fun p : (GraphQuery × ℕ) × BitString =>
      conditionalRunOut c₀ p.1.2 p.1.1.2.1 p.2 :=
    hrun.comp (Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd))
  have hM : Primrec fun a : GraphQuery × ℕ => a.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hj : Primrec fun a : GraphQuery × ℕ => a.1.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hz : Primrec fun a : GraphQuery × ℕ => a.1.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hallA : Primrec fun a : GraphQuery × ℕ => allHalted c₀ a.2 a.1.1 (neededRow a.1.2.2.2.1
      a.1.2.2.2.2) :=
    list_all_primrec (primrec_neededRow.comp hj hz) (Primrec.option_isSome.comp hA)
  have hallB : Primrec fun a : GraphQuery × ℕ => allHalted c₀ a.2 a.1.2.1 (neededCol a.1.2.2.2.1
      a.1.2.2.2.2) :=
    list_all_primrec (primrec_neededCol.comp hj hz) (Primrec.option_isSome.comp hB)
  have hlist : Primrec fun a : GraphQuery × ℕ => labelGraphList (stageOut c₀ a.2 a.1.1)
      (stageOut c₀ a.2 a.1.2.1) a.1.2.2.1 a.1.2.2.2.1 a.1.2.2.2.2 :=
    primrec_labelGraphList (F := fun a c => stageOut c₀ a.2 a.1.1 c)
      (G := fun a c => stageOut c₀ a.2 a.1.2.1 c)
      ((Primrec.option_getD.comp hA (Primrec.const [])).of_eq fun _ => rfl)
      ((Primrec.option_getD.comp hB (Primrec.const [])).of_eq fun _ => rfl) hM hj hz
  exact Primrec.cond (Primrec.and.comp hallA hallB) (Primrec.option_some.comp hlist)
    (Primrec.const none)

/-- A finite list of conditions on which a total program halts is covered by one stage, from
which on all these runs return the program's outputs. -/
theorem exists_stage_all {c₀ : Nat.Partrec.Code}
    (hcomplete : ∀ p y u : BitString, u ∈ universalDecompressor (p, y) →
      ∃ t, conditionalRunOut c₀ t p y = some u)
    (hmono : ∀ (t t' : ℕ) (p y u : BitString), t ≤ t' → conditionalRunOut c₀ t p y = some u →
      conditionalRunOut c₀ t' p y = some u)
    {p : BitString} {f : BitString → BitString} (hf : ∀ c, f c ∈ universalDecompressor (p, c))
    (L : List BitString) :
    ∃ s, ∀ t, s ≤ t → ∀ c ∈ L, conditionalRunOut c₀ t p c = some (f c) := by
  induction L with
  | nil => exact ⟨0, fun _ _ c hc => absurd hc List.not_mem_nil⟩
  | cons c L ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨t₀, ht₀⟩ := hcomplete p c (f c) (hf c)
    refine ⟨max s t₀, fun t ht c' hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hmono _ _ _ _ _ (le_of_max_le_right ht) ht₀
    · exact hs t (le_of_max_le_left ht) c' hc'

/-- **The graph search** (shared by L31, L34, L35).  One partial recursive map returns, on the
query `(p_A, p_B, M, j, z)`, the list graph of the label `z` built from the actual outputs of the
two witness bodies, whenever every output of the two witnesses is defined (total witnesses).

Proof: `Nat.rfindOpt` of `graphAttempt` (`Partrec.rfindOpt`, `primrec_graphAttempt`).  Every
successful stage has seen halted runs on all needed conditions, and these runs are sound, so its
list is the list graph of the actual outputs (`labelGraphList_congr`); completeness and
monotonicity of the runs (`exists_stage_all`) give a successful stage. -/
theorem exists_graphSearch :
    ∃ S : GraphQuery →. EdgeList, Partrec S ∧ ∀ (pA pB : BitString) (M j : ℕ) (z : BitString)
      (fA fB : BitString → BitString), (∀ c, fA c ∈ universalDecompressor (pA, c)) →
        (∀ c, fB c ∈ universalDecompressor (pB, c)) →
        labelGraphList fA fB M j z ∈ S (pA, pB, M, j, z) := by
  obtain ⟨c₀, hsound, hcomplete, hmono, -⟩ :=
    boundedEvaluationInterface universalDecompressor isDecompressor_universalDecompressor
  refine ⟨fun Q => Nat.rfindOpt (graphAttempt c₀ Q.1 Q.2.1 Q.2.2.1 Q.2.2.2.1 Q.2.2.2.2),
    Partrec.rfindOpt (primrec_graphAttempt c₀).to_comp, ?_⟩
  intro pA pB M j z fA fB hfA hfB
  change labelGraphList fA fB M j z ∈ Nat.rfindOpt (graphAttempt c₀ pA pB M j z)
  have hstage : ∀ (p : BitString) (f : BitString → BitString), (∀ c, f c ∈ universalDecompressor
      (p, c)) → ∀ (s : ℕ) (L : List BitString), allHalted c₀ s p L = true →
      ∀ c ∈ L, stageOut c₀ s p c = f c := by
    intro p f hf s L hall c hc
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 hall c hc)
    have hprod := hsound s p c o ho
    unfold stageOut
    rw [ho, Option.getD_some]
    exact Part.mem_unique hprod (hf c)
  have huniq : ∀ s w, graphAttempt c₀ pA pB M j z s = some w →
      w = labelGraphList fA fB M j z := by
    intro s w hw
    unfold graphAttempt at hw
    cases hb : (allHalted c₀ s pA (neededRow j z) && allHalted c₀ s pB (neededCol j z))
    · rw [hb] at hw
      cases hw
    · rw [hb, Bool.cond_true, Option.some.injEq] at hw
      subst hw
      rw [Bool.and_eq_true] at hb
      exact labelGraphList_congr (hstage pA fA hfA s _ hb.1) (hstage pB fB hfB s _ hb.2)
  obtain ⟨sA, hsA⟩ := exists_stage_all hcomplete hmono hfA (neededRow j z)
  obtain ⟨sB, hsB⟩ := exists_stage_all hcomplete hmono hfB (neededCol j z)
  have hallA : allHalted c₀ (max sA sB) pA (neededRow j z) = true :=
    List.all_eq_true.2 fun c hc => by rw [hsA _ (le_max_left _ _) c hc]; rfl
  have hallB : allHalted c₀ (max sA sB) pB (neededCol j z) = true :=
    List.all_eq_true.2 fun c hc => by rw [hsB _ (le_max_right _ _) c hc]; rfl
  have hs : graphAttempt c₀ pA pB M j z (max sA sB) = some (labelGraphList fA fB M j z) := by
    unfold graphAttempt
    rw [hallA, hallB, Bool.and_true, Bool.cond_true,
      labelGraphList_congr (hstage pA fA hfA _ _ hallA) (hstage pB fB hfB _ _ hallB)]
  have hdom : (Nat.rfindOpt (graphAttempt c₀ pA pB M j z)).Dom :=
    Nat.rfindOpt_dom.2 ⟨_, _, hs⟩
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec (Part.get_mem hdom)
  rw [← huniq n _ hn]
  exact Part.get_mem hdom

/-! ### Post-processing of the edge list -/

/-- The set of a mapped list is the image of the set of the list. -/
theorem toFinset_map_eq_image {γ δ : Type*} [DecidableEq γ] [DecidableEq δ] (f : γ → δ)
    (l : List γ) : (l.map f).toFinset = l.toFinset.image f := by
  ext x
  simp

/-- The value of the peeling decoder on the edge list `L` (node L31): the entry of rank `rank`
in the canonical list of the opposite endpoints of the edges owned by `y`. -/
noncomputable def peelValueList (side : Bool) (θ rank : ℕ) (y : BitString) (L : EdgeList) :
    BitString :=
  if side then (canonicalFinsetList ((ownedRList θ L y).map Prod.fst).toFinset).getD rank []
  else (canonicalFinsetList ((ownedLList θ L y).map Prod.snd).toFinset).getD rank []

/-- On a duplicate-free list, `peelValueList` reads the `Finset` owned sets. -/
theorem peelValueList_eq {L : EdgeList} (hL : L.Nodup) (side : Bool) (θ rank : ℕ)
    (y : BitString) : peelValueList side θ rank y L = if side then
      (canonicalFinsetList ((ownedR θ L.toFinset y).image Prod.fst)).getD rank []
    else (canonicalFinsetList ((ownedL θ L.toFinset y).image Prod.snd)).getD rank [] := by
  unfold peelValueList
  rw [toFinset_map_eq_image, toFinset_map_eq_image, ownedRList_toFinset hL,
    ownedLList_toFinset hL]

/-- The projection of the list core on one side: right vertices for `side = true`, left
vertices for `side = false`. -/
def coreSideList (side : Bool) (θ : ℕ) (L : EdgeList) : List BitString :=
  if side then (peelCoreList θ L).map Prod.snd else (peelCoreList θ L).map Prod.fst

/-- On a duplicate-free list, `coreSideList` enumerates the projection of the `Finset` core. -/
theorem coreSideList_toFinset {L : EdgeList} (hL : L.Nodup) (side : Bool) (θ : ℕ) :
    (coreSideList side θ L).toFinset = if side then (peelCore θ L.toFinset).image Prod.snd
      else (peelCore θ L.toFinset).image Prod.fst := by
  unfold coreSideList
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, toFinset_map_eq_image,
    peelCoreList_toFinset hL]

/-- The value of the partition decoder on the edge list `L` (node L34): the code of the projected
core if it contains the `M`-word `y`, and the code of `{y}` otherwise. -/
noncomputable def projCodeList (side : Bool) (θ M : ℕ) (y : BitString) (L : EdgeList) :
    BitString :=
  if y.length = M ∧ y ∈ coreSideList side θ L then listModelCode (coreSideList side θ L)
  else listModelCode [y]

/-- On a duplicate-free list, `projCodeList` is the code of the `Finset` cell. -/
theorem projCodeList_eq {L : EdgeList} (hL : L.Nodup) (side : Bool) (θ M : ℕ)
    (y : BitString) : projCodeList side θ M y L = canonicalFiniteSetCode
      (if y.length = M ∧ y ∈ (if side then (peelCore θ L.toFinset).image Prod.snd
        else (peelCore θ L.toFinset).image Prod.fst) then
        (if side then (peelCore θ L.toFinset).image Prod.snd
          else (peelCore θ L.toFinset).image Prod.fst)
      else {y}) := by
  unfold projCodeList
  rw [← coreSideList_toFinset hL]
  by_cases h : y.length = M ∧ y ∈ coreSideList side θ L
  · rw [ite_eq_left h, ite_eq_left ⟨h.1, List.mem_toFinset.2 h.2⟩]
    exact listModelCode_eq _ _ rfl
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.1, List.mem_toFinset.1 h'.2⟩]
    exact listModelCode_eq _ _ (by simp)

/-- The value of the projection-description decoder on the edge list `L` (node L35): the code of
the projected core. -/
noncomputable def coreCodeList (side : Bool) (θ : ℕ) (L : EdgeList) : BitString :=
  listModelCode (coreSideList side θ L)

/-- On a duplicate-free list, `coreCodeList` is the code of the projected `Finset` core. -/
theorem coreCodeList_eq {L : EdgeList} (hL : L.Nodup) (side : Bool) (θ : ℕ) :
    coreCodeList side θ L = canonicalFiniteSetCode (if side then
      (peelCore θ L.toFinset).image Prod.snd else (peelCore θ L.toFinset).image Prod.fst) :=
  listModelCode_eq _ _ (coreSideList_toFinset hL side θ)

/-- `q ↦ 2 ^ q` is primitive recursive. -/
theorem primrec_two_pow : Primrec fun q : ℕ => 2 ^ q :=
  (Primrec.nat_iterate Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂).of_eq fun q => by
    change (fun b : ℕ => 2 * b)^[q] 1 = 2 ^ q
    induction q with
    | zero => rfl
    | succ q ih => rw [Function.iterate_succ_apply', ih, pow_succ, mul_comm]

/-- The projection of the list core is primitive recursive. -/
theorem primrec_coreSideList :
    Primrec fun p : (Bool × ℕ) × EdgeList => coreSideList p.1.1 p.1.2 p.2 := by
  have hc : Primrec fun p : (Bool × ℕ) × EdgeList => peelCoreList p.1.2 p.2 :=
    primrec_peelCoreList.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  refine (Primrec.cond (Primrec.fst.comp Primrec.fst)
    (Primrec.list_map hc (Primrec.snd.comp₂ Primrec₂.right))
    (Primrec.list_map hc (Primrec.fst.comp₂ Primrec₂.right))).of_eq fun p => ?_
  rcases p with ⟨⟨s, θ⟩, L⟩
  cases s <;> rfl

/-- The value of the peeling decoder on lists is primitive recursive. -/
theorem primrec_peelValueList :
    Primrec fun p : (Bool × ℕ × ℕ × BitString) × EdgeList =>
      peelValueList p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 := by
  have hθ : Primrec fun p : (Bool × ℕ × ℕ × BitString) × EdgeList => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hr : Primrec fun p : (Bool × ℕ × ℕ × BitString) × EdgeList => p.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hy : Primrec fun p : (Bool × ℕ × ℕ × BitString) × EdgeList => p.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hR : Primrec fun p : (Bool × ℕ × ℕ × BitString) × EdgeList =>
      ownedRList p.1.2.1 p.2 p.1.2.2.2 :=
    primrec_ownedRList.comp (Primrec.pair (Primrec.pair hθ Primrec.snd) hy)
  have hL : Primrec fun p : (Bool × ℕ × ℕ × BitString) × EdgeList =>
      ownedLList p.1.2.1 p.2 p.1.2.2.2 :=
    primrec_ownedLList.comp (Primrec.pair (Primrec.pair hθ Primrec.snd) hy)
  have hT := (Primrec.list_getD []).comp (canonicalFinsetList_toFinset_primrec.comp
    (Primrec.list_map hR (Primrec.fst.comp₂ Primrec₂.right))) hr
  have hF := (Primrec.list_getD []).comp (canonicalFinsetList_toFinset_primrec.comp
    (Primrec.list_map hL (Primrec.snd.comp₂ Primrec₂.right))) hr
  refine (Primrec.cond (Primrec.fst.comp Primrec.fst) hT hF).of_eq fun p => ?_
  rcases p with ⟨⟨s, θ, r, y⟩, L⟩
  cases s <;> rfl

/-- The value of the partition decoder on lists is primitive recursive. -/
theorem primrec_projCodeList :
    Primrec fun p : (Bool × ℕ × ℕ × BitString) × EdgeList =>
      projCodeList p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 := by
  have hy : Primrec fun p : (Bool × ℕ × ℕ × BitString) × EdgeList => p.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hP : Primrec fun p : (Bool × ℕ × ℕ × BitString) × EdgeList =>
      coreSideList p.1.1 p.1.2.1 p.2 :=
    primrec_coreSideList.comp (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  unfold projCodeList
  refine Primrec.ite (PrimrecPred.and ?_ ?_) (primrec_listModelCode.comp hP)
    (primrec_listModelCode.comp (Primrec.list_cons.comp hy (Primrec.const [])))
  · exact Primrec.eq.comp (Primrec.list_length.comp hy)
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  · exact Primrec.primrecPred (bitString_mem_primrec.comp hy hP)

/-- The value of the projection-description decoder on lists is primitive recursive. -/
theorem primrec_coreCodeList :
    Primrec fun p : (Bool × ℕ) × EdgeList => coreCodeList p.1.1 p.1.2 p.2 :=
  primrec_listModelCode.comp primrec_coreSideList

/-! ### Reading the packets -/

/-- Drop the first numeric field of a packet. -/
def popField (w : BitString) : BitString :=
  (numFieldDecode w).2

/-- The `i`-th numeric field of a packet. -/
def fieldAt (i : ℕ) (w : BitString) : ℕ :=
  (numFieldDecode (popField^[i] w)).1

/-- The side flag read from a numeric field. -/
def sideOf (k : ℕ) : Bool :=
  decide (k = 1)

/-- The side flag is read back from its numeric field. -/
@[simp] theorem sideOf_toNat (b : Bool) : sideOf b.toNat = b := by
  cases b <;> rfl

/-- Dropping all the numeric fields of a packet leaves its body. -/
theorem popField_iterate_numPacket (ks : List ℕ) (body : BitString) :
    popField^[ks.length] (numPacket ks body) = body := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have h : popField (numPacket (k :: ks) body) = numPacket ks body := by
      simp [popField, numPacket, numFieldDecode_numField]
    rw [h, ih]

/-- The `i`-th numeric field of a packet is read back. -/
theorem fieldAt_numPacket (ks : List ℕ) (body : BitString) (i : ℕ) (hi : i < ks.length) :
    fieldAt i (numPacket ks body) = ks[i] := by
  induction ks generalizing i with
  | nil => simp at hi
  | cons k ks ih =>
    cases i with
    | zero => simp [fieldAt, numPacket, numFieldDecode_numField]
    | succ i =>
      have h : popField (numPacket (k :: ks) body) = numPacket ks body := by
        simp [popField, numPacket, numFieldDecode_numField]
      rw [fieldAt, Function.iterate_succ_apply, h]
      exact ih i (by simpa using hi)

/-- Dropping a numeric field is computable. -/
theorem computable_popField : Computable popField :=
  Computable.snd.comp numFieldDecode_computable

/-- Dropping `i` numeric fields is computable. -/
theorem computable_popField_iterate (i : ℕ) : Computable (popField^[i]) := by
  induction i with
  | zero => exact Computable.id
  | succ i ih =>
    exact (computable_popField.comp ih).of_eq fun w => (Function.iterate_succ_apply' _ _ _).symm

/-- Reading the `i`-th numeric field is computable. -/
theorem computable_fieldAt (i : ℕ) : Computable (fieldAt i) :=
  Computable.fst.comp (numFieldDecode_computable.comp (computable_popField_iterate i))

/-- The side flag is primitive recursive. -/
theorem primrec_sideOf : Primrec sideOf :=
  PrimrecPred.decide (Primrec.eq.comp Primrec.id (Primrec.const 1))

/-! ### The three decoders as one search pattern -/

/-- A search decoder: on `(w, y)` run `V` on the query `a (w, y)` to obtain a label `z`, run the
graph search `S` on the query `g (w, y) z` and post-process the edge list by `post (w, y)`. -/
def searchDecoder (V : Map) (S : GraphQuery →. EdgeList) (a : BitString × BitString →
    BitString × BitString) (g : BitString × BitString → BitString → GraphQuery)
    (post : BitString × BitString → EdgeList → BitString) : Map := fun p =>
  (V (a p)).bind fun z => (S (g p z)).map (post p)

/-- A search decoder built from partial recursive and computable pieces is partial recursive. -/
theorem partrec_searchDecoder {V : Map} (hV : isDecompressor V) {S : GraphQuery →. EdgeList}
    (hS : Partrec S) {a : BitString × BitString → BitString × BitString} (ha : Computable a)
    {g : BitString × BitString → BitString → GraphQuery} (hg : Computable₂ g)
    {post : BitString × BitString → EdgeList → BitString} (hpost : Computable₂ post) :
    isDecompressor (searchDecoder V S a g post) := by
  have h1 : Partrec fun p => V (a p) := hV.comp ha
  have h2 : Partrec₂ fun p z => (S (g p z)).map (post p) :=
    Partrec.map (hS.comp hg) (hpost.comp (Computable.fst.comp Computable.fst) Computable.snd)
  exact Partrec.bind h1 h2

/-- The value of a search decoder. -/
theorem mem_searchDecoder {V : Map} {S : GraphQuery →. EdgeList}
    {a : BitString × BitString → BitString × BitString}
    {g : BitString × BitString → BitString → GraphQuery}
    {post : BitString × BitString → EdgeList → BitString} {p : BitString × BitString}
    {z : BitString} {L : EdgeList} (hz : z ∈ V (a p)) (hL : L ∈ S (g p z)) :
    post p L ∈ searchDecoder V S a g post p :=
  Part.mem_bind_iff.2 ⟨z, hz, Part.mem_map _ hL⟩

/-- The star code of the queried word on the given side: the column star for `side = true`, the
row star for `side = false`. -/
noncomputable def sideStarCode (j : ℕ) (side : Bool) (y : BitString) : BitString :=
  if side then canonicalFiniteSetCode (colStar j y) else canonicalFiniteSetCode (rowStar j y)

/-- The side star code is computable. -/
theorem computable_sideStarCode :
    Computable fun p : (ℕ × Bool) × BitString => sideStarCode p.1.1 p.1.2 p.2 := by
  refine (Computable.cond (Computable.snd.comp Computable.fst)
    (computable_colStar_code.comp (Computable.fst.comp Computable.fst) Computable.snd)
    (computable_rowStar_code.comp (Computable.fst.comp Computable.fst) Computable.snd)).of_eq
    fun p => ?_
  rcases p with ⟨⟨j, s⟩, y⟩
  cases s <;> rfl

/-- The label query of the decoders of L31 and L34 (`nf` numeric fields, field 1 = `j`, field 3
= side): the witness of the side of the queried word, run on its star. -/
noncomputable def labelQuery (nf : ℕ) (p : BitString × BitString) : BitString × BitString :=
  (if sideOf (fieldAt 3 p.1) then decodeTotalProgramPairSecond (popField^[nf] p.1)
    else decodeTotalProgramPairFirst (popField^[nf] p.1),
    sideStarCode (fieldAt 1 p.1) (sideOf (fieldAt 3 p.1)) p.2)

/-- The graph query of the decoders of L31 and L34: both bodies, `M` (field 0), `j` (field 1)
and the label. -/
noncomputable def graphQuery (nf : ℕ) (p : BitString × BitString) (z : BitString) :
    GraphQuery :=
  (decodeTotalProgramPairFirst (popField^[nf] p.1),
    decodeTotalProgramPairSecond (popField^[nf] p.1), fieldAt 0 p.1, fieldAt 1 p.1, z)

/-- The post-processing of the peeling decoder (L31): fields `q` (2), side (3) and rank (4). -/
noncomputable def peelPost (p : BitString × BitString) (L : EdgeList) : BitString :=
  peelValueList (sideOf (fieldAt 3 p.1)) (2 ^ fieldAt 2 p.1) (fieldAt 4 p.1) p.2 L

/-- The post-processing of the partition decoder (L34): fields `M` (0), `q` (2), side (3). -/
noncomputable def projPost (p : BitString × BitString) (L : EdgeList) : BitString :=
  projCodeList (sideOf (fieldAt 3 p.1)) (2 ^ fieldAt 2 p.1) (fieldAt 0 p.1) p.2 L

/-- The label query of the projection-description decoder (L35): the ordinary program `p_D`,
the unframed tail of the packet, with the empty condition. -/
noncomputable def coreLabelQuery (p : BitString × BitString) : BitString × BitString :=
  (decodeTotalProgramPairSecond (decodeTotalProgramPairSecond (popField^[4] p.1)), [])

/-- The graph query of the projection-description decoder (L35). -/
noncomputable def coreGraphQuery (p : BitString × BitString) (z : BitString) : GraphQuery :=
  (decodeTotalProgramPairFirst (popField^[4] p.1),
    decodeTotalProgramPairFirst (decodeTotalProgramPairSecond (popField^[4] p.1)),
    fieldAt 0 p.1, fieldAt 1 p.1, z)

/-- The post-processing of the projection-description decoder (L35). -/
noncomputable def corePost (p : BitString × BitString) (L : EdgeList) : BitString :=
  coreCodeList (sideOf (fieldAt 3 p.1)) (2 ^ fieldAt 2 p.1) L

/-- The label query is computable. -/
theorem computable_labelQuery (nf : ℕ) : Computable (labelQuery nf) := by
  have hb : Computable fun p : BitString × BitString => popField^[nf] p.1 :=
    (computable_popField_iterate nf).comp Computable.fst
  have hs : Computable fun p : BitString × BitString => sideOf (fieldAt 3 p.1) :=
    primrec_sideOf.to_comp.comp ((computable_fieldAt 3).comp Computable.fst)
  have h1 : Computable fun p : BitString × BitString =>
      (if sideOf (fieldAt 3 p.1) then decodeTotalProgramPairSecond (popField^[nf] p.1)
        else decodeTotalProgramPairFirst (popField^[nf] p.1)) := by
    refine (Computable.cond hs (decodeTotalProgramPairSecond_computable.comp hb)
      (decodeTotalProgramPairFirst_computable.comp hb)).of_eq fun p => ?_
    cases sideOf (fieldAt 3 p.1) <;> rfl
  have hj : Computable fun p : BitString × BitString =>
      (fieldAt 1 p.1, sideOf (fieldAt 3 p.1)) :=
    ((computable_fieldAt 1).comp Computable.fst).pair hs
  have h2 : Computable fun p : BitString × BitString =>
      sideStarCode (fieldAt 1 p.1) (sideOf (fieldAt 3 p.1)) p.2 :=
    (computable_sideStarCode.comp (hj.pair Computable.snd)).of_eq fun _ => by dsimp only
  have h3 : Computable fun p : BitString × BitString =>
      ((if sideOf (fieldAt 3 p.1) then decodeTotalProgramPairSecond (popField^[nf] p.1)
        else decodeTotalProgramPairFirst (popField^[nf] p.1)),
        sideStarCode (fieldAt 1 p.1) (sideOf (fieldAt 3 p.1)) p.2) := h1.pair h2
  exact h3.of_eq fun _ => by dsimp only [labelQuery]

/-- The graph query is computable. -/
theorem computable_graphQuery (nf : ℕ) : Computable₂ (graphQuery nf) := by
  have hw : Computable fun q : (BitString × BitString) × BitString => q.1.1 :=
    Computable.fst.comp Computable.fst
  have hb : Computable fun q : (BitString × BitString) × BitString => popField^[nf] q.1.1 :=
    (computable_popField_iterate nf).comp hw
  have h0 : Computable fun q : (BitString × BitString) × BitString => fieldAt 0 q.1.1 :=
    (computable_fieldAt 0).comp hw
  have h1 : Computable fun q : (BitString × BitString) × BitString => fieldAt 1 q.1.1 :=
    (computable_fieldAt 1).comp hw
  have hA : Computable fun q : (BitString × BitString) × BitString =>
      decodeTotalProgramPairFirst (popField^[nf] q.1.1) :=
    decodeTotalProgramPairFirst_computable.comp hb
  have hB : Computable fun q : (BitString × BitString) × BitString =>
      decodeTotalProgramPairSecond (popField^[nf] q.1.1) :=
    decodeTotalProgramPairSecond_computable.comp hb
  have hjz : Computable fun q : (BitString × BitString) × BitString => (fieldAt 1 q.1.1, q.2) :=
    h1.pair Computable.snd
  have hMjz : Computable fun q : (BitString × BitString) × BitString =>
      (fieldAt 0 q.1.1, fieldAt 1 q.1.1, q.2) := h0.pair hjz
  have hBMjz : Computable fun q : (BitString × BitString) × BitString =>
      (decodeTotalProgramPairSecond (popField^[nf] q.1.1), fieldAt 0 q.1.1, fieldAt 1 q.1.1,
        q.2) := hB.pair hMjz
  have hall : Computable fun q : (BitString × BitString) × BitString =>
      (decodeTotalProgramPairFirst (popField^[nf] q.1.1),
        decodeTotalProgramPairSecond (popField^[nf] q.1.1), fieldAt 0 q.1.1, fieldAt 1 q.1.1,
        q.2) := hA.pair hBMjz
  exact hall.of_eq fun _ => rfl

/-- The peeling post-processing is computable. -/
theorem computable_peelPost : Computable₂ peelPost := by
  have hw : Computable fun q : (BitString × BitString) × EdgeList => q.1.1 :=
    Computable.fst.comp Computable.fst
  have hargs : Computable fun q : (BitString × BitString) × EdgeList =>
      ((sideOf (fieldAt 3 q.1.1), 2 ^ fieldAt 2 q.1.1, fieldAt 4 q.1.1, q.1.2), q.2) :=
    ((primrec_sideOf.to_comp.comp ((computable_fieldAt 3).comp hw)).pair
      ((primrec_two_pow.to_comp.comp ((computable_fieldAt 2).comp hw)).pair
        (((computable_fieldAt 4).comp hw).pair (Computable.snd.comp Computable.fst)))).pair
      Computable.snd
  exact (primrec_peelValueList.to_comp.comp hargs).of_eq fun _ => by dsimp only [peelPost]

/-- The partition post-processing is computable. -/
theorem computable_projPost : Computable₂ projPost := by
  have hw : Computable fun q : (BitString × BitString) × EdgeList => q.1.1 :=
    Computable.fst.comp Computable.fst
  have hargs : Computable fun q : (BitString × BitString) × EdgeList =>
      ((sideOf (fieldAt 3 q.1.1), 2 ^ fieldAt 2 q.1.1, fieldAt 0 q.1.1, q.1.2), q.2) :=
    ((primrec_sideOf.to_comp.comp ((computable_fieldAt 3).comp hw)).pair
      ((primrec_two_pow.to_comp.comp ((computable_fieldAt 2).comp hw)).pair
        (((computable_fieldAt 0).comp hw).pair (Computable.snd.comp Computable.fst)))).pair
      Computable.snd
  exact (primrec_projCodeList.to_comp.comp hargs).of_eq fun _ => by dsimp only [projPost]

/-- The core label query is computable. -/
theorem computable_coreLabelQuery : Computable coreLabelQuery := by
  have hb : Computable fun p : BitString × BitString => popField^[4] p.1 :=
    (computable_popField_iterate 4).comp Computable.fst
  have hD : Computable fun p : BitString × BitString =>
      decodeTotalProgramPairSecond (decodeTotalProgramPairSecond (popField^[4] p.1)) :=
    decodeTotalProgramPairSecond_computable.comp (decodeTotalProgramPairSecond_computable.comp hb)
  have h : Computable fun p : BitString × BitString =>
      (decodeTotalProgramPairSecond (decodeTotalProgramPairSecond (popField^[4] p.1)),
        ([] : BitString)) := hD.pair (Computable.const [])
  exact h.of_eq fun _ => rfl

/-- The core graph query is computable. -/
theorem computable_coreGraphQuery : Computable₂ coreGraphQuery := by
  have hw : Computable fun q : (BitString × BitString) × BitString => q.1.1 :=
    Computable.fst.comp Computable.fst
  have hb : Computable fun q : (BitString × BitString) × BitString => popField^[4] q.1.1 :=
    (computable_popField_iterate 4).comp hw
  have h0 : Computable fun q : (BitString × BitString) × BitString => fieldAt 0 q.1.1 :=
    (computable_fieldAt 0).comp hw
  have h1 : Computable fun q : (BitString × BitString) × BitString => fieldAt 1 q.1.1 :=
    (computable_fieldAt 1).comp hw
  have hA : Computable fun q : (BitString × BitString) × BitString =>
      decodeTotalProgramPairFirst (popField^[4] q.1.1) :=
    decodeTotalProgramPairFirst_computable.comp hb
  have hB : Computable fun q : (BitString × BitString) × BitString =>
      decodeTotalProgramPairFirst (decodeTotalProgramPairSecond (popField^[4] q.1.1)) :=
    decodeTotalProgramPairFirst_computable.comp (decodeTotalProgramPairSecond_computable.comp hb)
  have hjz : Computable fun q : (BitString × BitString) × BitString => (fieldAt 1 q.1.1, q.2) :=
    h1.pair Computable.snd
  have hMjz : Computable fun q : (BitString × BitString) × BitString =>
      (fieldAt 0 q.1.1, fieldAt 1 q.1.1, q.2) := h0.pair hjz
  have hBMjz : Computable fun q : (BitString × BitString) × BitString =>
      (decodeTotalProgramPairFirst (decodeTotalProgramPairSecond (popField^[4] q.1.1)),
        fieldAt 0 q.1.1, fieldAt 1 q.1.1, q.2) := hB.pair hMjz
  have hall : Computable fun q : (BitString × BitString) × BitString =>
      (decodeTotalProgramPairFirst (popField^[4] q.1.1),
        decodeTotalProgramPairFirst (decodeTotalProgramPairSecond (popField^[4] q.1.1)),
        fieldAt 0 q.1.1, fieldAt 1 q.1.1, q.2) := hA.pair hBMjz
  exact hall.of_eq fun _ => rfl

/-- The core post-processing is computable. -/
theorem computable_corePost : Computable₂ corePost := by
  have hw : Computable fun q : (BitString × BitString) × EdgeList => q.1.1 :=
    Computable.fst.comp Computable.fst
  have hargs : Computable fun q : (BitString × BitString) × EdgeList =>
      ((sideOf (fieldAt 3 q.1.1), 2 ^ fieldAt 2 q.1.1), q.2) :=
    ((primrec_sideOf.to_comp.comp ((computable_fieldAt 3).comp hw)).pair
      (primrec_two_pow.to_comp.comp ((computable_fieldAt 2).comp hw))).pair Computable.snd
  exact (primrec_coreCodeList.to_comp.comp hargs).of_eq fun _ => by dsimp only [corePost]

end Kolmogorov.StrongMerging.Lower
