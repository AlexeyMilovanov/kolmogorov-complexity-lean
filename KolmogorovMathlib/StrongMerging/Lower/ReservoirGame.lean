import KolmogorovMathlib.StrongMerging.Basic

/-!
# The moving-sphere reservoir game: events, board and transitions

Blueprint nodes L14–L17 of `sublinear-merging.tex` (paper: "A finite game producing a dense
reservoir"; blueprint: "An exact finite combinatorial game with an effective event stream").

The game is **generic**: it is parametrized by an abstract type `α` of cube points, the canonical
list `G.centers` of the cube (the center search order), the sphere map `G.sphere`, the common
sphere size `G.N` and the two exponents `G.ell`, `G.delta` of the heaviness test.  It does not
depend on the coding of strings, of finite sets or of programs, nor on the Hamming geometry.  Those
enter only through

* the abstract event sources `EventSources` (bounded evaluators of the three candidate families,
  node L14), instantiated later with the bounded evaluators of L04, and
* the explicit hypotheses `GameHyp` of the availability theorem (in `Reservoir.lean`): sphere
  incidence, the heavy-cell bound of L09 as a hypothesis, and the four game inequalities.

Contents:

* `ResEvent`: point, set and table events, with the history counters `pointCount`,
  `tableCount`, `costCount`, `setMass`, and `ValidHistory`, the L14 count/certificate invariants;
* `EventSources`, `stageEvents`, `eventHistory`: the deterministic effective event stream (L14);
* `ReservoirState`: the finite board (L15);
* `badSet`, `chooseCenter`, `chooseReservoir`: the canonical center search (L16);
* `reservoirTransition`, `initState`, `run`, `emittedCenters`: the transitions (L17).

No real number occurs in any executable definition: all tests are integer tests.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

variable {α : Type*}

/-! ### Events and histories -/

/-- An event of the reservoir game (blueprint node L14). -/
inductive ResEvent (α : Type*) where
  /-- A point output `u` of an ordinary program shorter than `K`. -/
  | point (u : α) : ResEvent α
  /-- An eligible finite set `Q`, stored with the length `i` of its certificate program. -/
  | set (Q : Finset α) (i : ℕ) : ResEvent α
  /-- A completed, validated partition table, given by the list of its cells. -/
  | table (P : List (Finset α)) : ResEvent α

namespace ResEvent

/-- Whether an event is a point event. -/
def isPoint : ResEvent α → Bool
  | point _ => true
  | _ => false

/-- Whether an event is a table event. -/
def isTable : ResEvent α → Bool
  | table _ => true
  | _ => false

/-- Whether an event is a set event whose certificate has length `i`. -/
def hasCost (i : ℕ) : ResEvent α → Bool
  | set _ j => j == i
  | _ => false

/-- The cardinality of the set carried by a set event; `0` for the other events. -/
def setCard : ResEvent α → ℕ
  | set Q _ => Q.card
  | _ => 0

end ResEvent

/-- The number of point events of a history (counted with multiplicity). -/
def pointCount (evs : List (ResEvent α)) : ℕ :=
  evs.countP ResEvent.isPoint

/-- The number of table events of a history. -/
def tableCount (evs : List (ResEvent α)) : ℕ :=
  evs.countP ResEvent.isTable

/-- The number of set events of a history whose certificate has length `i`. -/
def costCount (evs : List (ResEvent α)) (i : ℕ) : ℕ :=
  evs.countP (ResEvent.hasCost i)

/-- The total mass `∑ |Q|` of the set events of a history (with multiplicity). -/
def setMass (evs : List (ResEvent α)) : ℕ :=
  (evs.map ResEvent.setCard).sum

/-! ### The game data -/

/-- The fixed data of the generic reservoir game: the cube in canonical center-search order, the
spheres, their common size `N`, and the exponents `ℓ` (`ell`) and `δ` (`delta`) of the heaviness
test `2^ℓ ≤ |Q|`, `|Q| < 2^δ |Q ∩ S_z|`. -/
structure ResGame (α : Type*) where
  /-- The candidate centers, i.e. the cube, in canonical search order. -/
  centers : List α
  /-- The sphere `S_z` around a center `z`. -/
  sphere : α → Finset α
  /-- The common sphere size `N`. -/
  N : ℕ
  /-- The size exponent `ℓ` of a heavy cell. -/
  ell : ℕ
  /-- The density exponent `δ` of a heavy cell. -/
  delta : ℕ
  /-- The center returned by the fallback of the choice (unreachable under `GameHyp`). -/
  fallback : α

variable [DecidableEq α]

/-- The cube, as a finite set. -/
def ResGame.cube (G : ResGame α) : Finset α :=
  G.centers.toFinset

/-- `P`, a list of cells, is an exact partition of `cube`: its cells are nonempty subsets of
`cube`, cover `cube`, and two cells sharing a point are equal (repetitions are allowed). -/
def IsCellPartition (cube : Finset α) (P : List (Finset α)) : Prop :=
  (∀ Q ∈ P, Q.Nonempty ∧ Q ⊆ cube) ∧ (∀ u ∈ cube, ∃ Q ∈ P, u ∈ Q) ∧
    ∀ Q ∈ P, ∀ Q' ∈ P, ∀ u ∈ Q, u ∈ Q' → Q = Q'

/-- **The L14 count and certificate invariants of a history** (the generic form of the event
bounds of the blueprint).  Fewer than `2^K` point events; every set event `(Q, i)` is eligible:
`i ≤ K + τ`, `2^ℓ ≤ |Q|` and `|Q| 2^i ≤ 2^(K+τ)`; at most `2^i` set events of certificate length
`i`; fewer than `2^(S+1)` table events, each an exact partition of the cube. -/
structure ValidHistory (G : ResGame α) (K τ S : ℕ) (evs : List (ResEvent α)) : Prop where
  /-- Fewer than `2^K` point events. -/
  point_count : pointCount evs < 2 ^ K
  /-- Every set event is eligible. -/
  set_elig : ∀ Q i, ResEvent.set Q i ∈ evs →
    i ≤ K + τ ∧ 2 ^ G.ell ≤ Q.card ∧ Q.card * 2 ^ i ≤ 2 ^ (K + τ)
  /-- At most `2^i` set events of certificate length `i`. -/
  cost_count : ∀ i, costCount evs i ≤ 2 ^ i
  /-- Fewer than `2^(S+1)` table events. -/
  table_count : tableCount evs < 2 ^ (S + 1)
  /-- Every table event is an exact partition of the cube. -/
  table_valid : ∀ P, ResEvent.table P ∈ evs → IsCellPartition G.cube P

/-! ### L14: the effective event stream -/

/-- Abstract bounded evaluators of the three candidate families of node L14.  Candidates are
indexed by naturals `c < numPt`, `c < numSet`, `c < numTab`; the evaluators take a candidate and a
stage `s` (a step bound) and return the output once available.  In the instance the point
candidates are the ordinary programs shorter than `K`, the set candidates the ordinary programs of
length at most `K + τ` (with `setCost c` the program length), and the table candidates the
total-interpreter programs of length at most `S`, evaluated on every cube point. -/
structure EventSources (α : Type*) where
  /-- Number of point candidates. -/
  numPt : ℕ
  /-- Bounded evaluator of the point candidates. -/
  ptEval : ℕ → ℕ → Option α
  /-- Number of set candidates. -/
  numSet : ℕ
  /-- Bounded evaluator of the set candidates. -/
  setEval : ℕ → ℕ → Option (Finset α)
  /-- Certificate length of a set candidate. -/
  setCost : ℕ → ℕ
  /-- Number of table candidates. -/
  numTab : ℕ
  /-- Bounded evaluator of a table candidate on one cube point. -/
  tabEval : ℕ → α → ℕ → Option (Finset α)

/-- `s` is the first stage at which the stage-indexed result `f` is available. -/
def firstAt {β : Type*} (f : ℕ → Option β) (s : ℕ) : Bool :=
  (f s).isSome && (List.range s).all fun t => (f t).isNone

/-- Eligibility of a set output with certificate length `i`: `Q ⊆ cube`, `i ≤ K + τ`,
`2^ℓ ≤ |Q|` and `|Q| 2^i ≤ 2^(K+τ)` (that is, `i + log |Q| ≤ K + τ`). -/
def SetEligible (G : ResGame α) (K τ : ℕ) (Q : Finset α) (i : ℕ) : Prop :=
  Q ⊆ G.cube ∧ i ≤ K + τ ∧ 2 ^ G.ell ≤ Q.card ∧ Q.card * 2 ^ i ≤ 2 ^ (K + τ)

instance (G : ResGame α) (K τ : ℕ) (Q : Finset α) (i : ℕ) : Decidable (SetEligible G K τ Q i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- All evaluations of table candidate `c` on the cube are available at stage `s`. -/
def tableDone (G : ResGame α) (src : EventSources α) (c s : ℕ) : Bool :=
  G.centers.all fun u => (src.tabEval c u s).isSome

/-- The validity test of one table entry at stage `s`: the output `Q` at `u` is a subset of the
cube containing `u`, and the table is constant (equal to `Q`) on `Q`. -/
def tableEntryOk (G : ResGame α) (src : EventSources α) (c s : ℕ) (u : α) : Bool :=
  match src.tabEval c u s with
  | some Q => decide (Q ⊆ G.cube ∧ u ∈ Q ∧ ∀ v ∈ Q, src.tabEval c v s = some Q)
  | none => false

/-- The cells (with repetitions) of table candidate `c` at stage `s`. -/
def tableCells (G : ResGame α) (src : EventSources α) (c s : ℕ) : List (Finset α) :=
  G.centers.map fun u => (src.tabEval c u s).getD ∅

/-- The point event of candidate `c` at stage `s`: emitted at its first success, for a cube
point. -/
def ptEventAt (G : ResGame α) (src : EventSources α) (s c : ℕ) : List (ResEvent α) :=
  match src.ptEval c s with
  | some u => if firstAt (src.ptEval c) s ∧ u ∈ G.cube then [ResEvent.point u] else []
  | none => []

/-- The set event of candidate `c` at stage `s`: emitted at its first success, if eligible. -/
def setEventAt (G : ResGame α) (K τ : ℕ) (src : EventSources α) (s c : ℕ) :
    List (ResEvent α) :=
  match src.setEval c s with
  | some Q =>
      if firstAt (src.setEval c) s ∧ SetEligible G K τ Q (src.setCost c) then
        [ResEvent.set Q (src.setCost c)] else []
  | none => []

/-- The table event of candidate `c` at stage `s`: emitted at the first stage at which the whole
table on the cube is available, if it passes the finite partition-map test. -/
def tabEventAt (G : ResGame α) (src : EventSources α) (s c : ℕ) : List (ResEvent α) :=
  if firstAt (fun t => if tableDone G src c t then some () else none) s ∧
      G.centers.all (tableEntryOk G src c s) then
    [ResEvent.table (tableCells G src c s)] else []

/-- The events discovered at stage `s`, in the fixed order: point events, then set events, then
table events, each in candidate order. -/
def stageEvents (G : ResGame α) (K τ : ℕ) (src : EventSources α) (s : ℕ) : List (ResEvent α) :=
  (List.range src.numPt).flatMap (ptEventAt G src s) ++
    (List.range src.numSet).flatMap (setEventAt G K τ src s) ++
    (List.range src.numTab).flatMap (tabEventAt G src s)

/-- **The effective event history** (node L14): all events of the stages `< s`, in processing
order. -/
def eventHistory (G : ResGame α) (K τ : ℕ) (src : EventSources α) (s : ℕ) :
    List (ResEvent α) :=
  (List.range s).flatMap (stageEvents G K τ src)

/-! ### L15: the board -/

/-- **The finite board of the reservoir game** (blueprint node L15): the known validated tables
(newest first), the stored eligible sets with their certificate lengths, the global marked
vertices, the globally marked whole cells, the current center, the current live reservoir, the
epoch record `epochLive` (the reservoir at the last choice), the output tape `emitted` of chosen
centers (newest first), and the ghost charge ledger `ordinaryResets`, `pointCharge`, `cellCharge`
used by the counting proofs.  No oracle state occurs; the unbounded simulation lives in the event
stream, not on the board. -/
structure ReservoirState (α : Type*) where
  /-- The known validated tables, newest first. -/
  tables : List (List (Finset α))
  /-- The stored eligible sets with their certificate lengths. -/
  stored : List (Finset α × ℕ)
  /-- The globally marked vertices. -/
  marks : Finset α
  /-- The globally marked whole cells. -/
  markedCells : List (Finset α)
  /-- The current center. -/
  center : α
  /-- The current live reservoir. -/
  live : Finset α
  /-- The reservoir at the last choice (epoch record). -/
  epochLive : Finset α
  /-- The output tape of chosen centers, newest first. -/
  emitted : List α
  /-- The number of ordinary resets so far. -/
  ordinaryResets : ℕ
  /-- The number of live points deleted by point events so far. -/
  pointCharge : ℕ
  /-- The number of live points deleted by set events (whole-cell marks) so far. -/
  cellCharge : ℕ

/-! ### L16: the canonical center search -/

/-- A cell `Q` is heavy for the center `z`: `2^ℓ ≤ |Q|` and `|Q| < 2^δ |Q ∩ S_z|`. -/
def IsHeavyCell (G : ResGame α) (z : α) (Q : Finset α) : Prop :=
  2 ^ G.ell ≤ Q.card ∧ Q.card < 2 ^ G.delta * (Q ∩ G.sphere z).card

instance (G : ResGame α) (z : α) (Q : Finset α) : Decidable (IsHeavyCell G z Q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The points of `S_z` lying in a heavy cell of the table `P`. -/
def tableHeavyPoints (G : ResGame α) (P : List (Finset α)) (z : α) : Finset α :=
  (G.sphere z).filter fun u => ∃ Q ∈ P, u ∈ Q ∧ IsHeavyCell G z Q

/-- The bad set `B_z`: the points of `S_z` that are marked or lie in a heavy cell of a known
table. -/
def badSet (G : ResGame α) (marks : Finset α) (tables : List (List (Finset α))) (z : α) :
    Finset α :=
  (G.sphere z).filter fun u => u ∈ marks ∨ ∃ P ∈ tables, ∃ Q ∈ P, u ∈ Q ∧ IsHeavyCell G z Q

/-- The first center (in canonical order) passing the choice test `32 |B_z| ≤ N`. -/
def chooseCenter (G : ResGame α) (marks : Finset α) (tables : List (List (Finset α))) :
    Option α :=
  G.centers.find? fun z => decide (32 * (badSet G marks tables z).card ≤ G.N)

/-- **The reservoir choice** (node L16): the first passing center `z` and the reservoir
`S_z \ B_z`; the total fallback `(G.fallback, ∅)` is unreachable under `GameHyp`. -/
def chooseReservoir (G : ResGame α) (marks : Finset α) (tables : List (List (Finset α))) :
    α × Finset α :=
  match chooseCenter G marks tables with
  | some z => (z, G.sphere z \ badSet G marks tables z)
  | none => (G.fallback, ∅)

/-! ### L17: the transitions -/

/-- The union of a list of finite sets. -/
def listUnion (l : List (Finset α)) : Finset α :=
  l.foldr (· ∪ ·) ∅

/-- Membership in `listUnion`. -/
theorem mem_listUnion {l : List (Finset α)} {u : α} : u ∈ listUnion l ↔ ∃ Q ∈ l, u ∈ Q := by
  induction l with
  | nil => simp [listUnion]
  | cons Q l ih =>
    change u ∈ Q ∪ listUnion l ↔ _
    rw [Finset.mem_union, ih]
    simp

namespace ReservoirState

variable (G : ResGame α)

/-- A reservoir choice: the new center and reservoir from `chooseReservoir`, a new epoch, and the
center emitted to the output tape. -/
def reselect (st : ReservoirState α) : ReservoirState α :=
  { st with
    center := (chooseReservoir G st.marks st.tables).1
    live := (chooseReservoir G st.marks st.tables).2
    epochLive := (chooseReservoir G st.marks st.tables).2
    emitted := (chooseReservoir G st.marks st.tables).1 :: st.emitted }

/-- The ordinary reset test: choose again (an ordinary reset) iff `8 |W| < 7 N`. -/
def ordinaryCheck (st : ReservoirState α) : ReservoirState α :=
  if 8 * st.live.card < 7 * G.N then
    { st.reselect G with ordinaryResets := st.ordinaryResets + 1 }
  else st

/-- A point event: mark `u` globally, delete it from the reservoir, then the reset test. -/
def pointStep (st : ReservoirState α) (u : α) : ReservoirState α :=
  ordinaryCheck G
    { st with
      marks := insert u st.marks
      live := st.live.erase u
      pointCharge := st.pointCharge + if u ∈ st.live then 1 else 0 }

/-- A set event: store `(Q, i)`; if `Q` is a cell of a known table and not yet marked as a whole,
mark it permanently and delete its points from the reservoir; then the reset test. -/
def setStep (st : ReservoirState α) (Q : Finset α) (i : ℕ) : ReservoirState α :=
  if (∃ P ∈ st.tables, Q ∈ P) ∧ Q ∉ st.markedCells then
    ordinaryCheck G
      { st with
        stored := (Q, i) :: st.stored
        markedCells := Q :: st.markedCells
        marks := st.marks ∪ Q
        live := st.live \ Q
        cellCharge := st.cellCharge + (st.live ∩ Q).card }
  else
    ordinaryCheck G { st with stored := (Q, i) :: st.stored }

/-- The stored sets that are cells of the table `P`. -/
def activated (st : ReservoirState α) (P : List (Finset α)) : List (Finset α) :=
  (st.stored.map Prod.fst).filter fun Q => decide (Q ∈ P)

/-- A table event (atomic): add the table, mark all stored sets that are its cells, without
intervening ordinary resets, then force exactly one reservoir choice. -/
def tableStep (st : ReservoirState α) (P : List (Finset α)) : ReservoirState α :=
  reselect G
    { st with
      tables := P :: st.tables
      markedCells := activated st P ++ st.markedCells
      marks := st.marks ∪ listUnion (activated st P)
      live := st.live \ listUnion (activated st P) }

end ReservoirState

/-- **The deterministic transition function of the game** (node L17). -/
def reservoirTransition (G : ResGame α) (st : ReservoirState α) : ResEvent α → ReservoirState α
  | .point u => st.pointStep G u
  | .set Q i => st.setStep G Q i
  | .table P => st.tableStep G P

/-- The empty board (before the initial choice). -/
def emptyState (G : ResGame α) : ReservoirState α where
  tables := []
  stored := []
  marks := ∅
  markedCells := []
  center := G.fallback
  live := ∅
  epochLive := ∅
  emitted := []
  ordinaryResets := 0
  pointCharge := 0
  cellCharge := 0

/-- The initial state: the empty board followed by the initial reservoir choice. -/
def initState (G : ResGame α) : ReservoirState α :=
  (emptyState G).reselect G

/-- The state after processing a history of events. -/
def run (G : ResGame α) (evs : List (ResEvent α)) : ReservoirState α :=
  evs.foldl (reservoirTransition G) (initState G)

/-- The emitted centers, in order of emission (the initial choice first). -/
def emittedCenters (G : ResGame α) (evs : List (ResEvent α)) : List α :=
  (run G evs).emitted.reverse

/-- The run on the empty history is the initial state. -/
theorem run_nil (G : ResGame α) : run G [] = initState G :=
  rfl

/-- Processing one more event is one transition. -/
theorem run_append_singleton (G : ResGame α) (evs : List (ResEvent α)) (e : ResEvent α) :
    run G (evs ++ [e]) = reservoirTransition G (run G evs) e := by
  rw [run, List.foldl_append]
  rfl

end Kolmogorov.StrongMerging.Lower
