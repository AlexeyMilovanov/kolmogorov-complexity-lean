/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators

/-!
# Information transmission requests

An information transmission request (SUV pp. 367–368) is a finite acyclic directed graph whose
edges are channels of a given capacity and whose nodes are processors; some nodes receive an
input string and some must produce an output string.  To fulfil the request one writes a
string on every edge, of length at most the capacity of that edge, so that at every node each
outgoing string (and the output string of the node, if any) has conditional complexity `≈ 0`
given the incoming strings and the input string of the node.

Formalisation choices, all of them recorded in the deviation table:

* acyclicity is a `rank` function with `rank u < rank v` on every edge — a topological
  ordering, which is what the cut argument of Section 12.8 uses;
* a node has at most one input and at most one output string (`Option BitString`); a node with
  several input strings is modelled by giving it their `listCode`;
* incoming and outgoing strings are listed in the order of the vertices they come from or go
  to, which is why the vertex type is linearly ordered;
* `≈ 0` is explicit: `IsFulfilledUpTo D r t capSlack ε` bounds every such conditional
  complexity by `ε` and every edge string by its capacity plus `capSlack`.  The book's `≈ 0`
  is `O(log N)` with `N` the total length of the input and output strings, which only makes
  sense for a *sequence* of requests: that is `IsFulfillableUpToLog` on a `RequestFamily`.

SUV Sections 12.1 and 12.8, pp. 367–368, 383–384.
-/

namespace Kolmogorov

/-- An information transmission request: a finite acyclic graph with capacities, input strings
and desired output strings.

SUV Section 12.1, p. 367. -/
structure InformationRequest (V : Type*) [Fintype V] [LinearOrder V] where
  /-- The channels of the network. -/
  edges : Finset (V × V)
  /-- A topological ranking of the vertices, witnessing acyclicity. -/
  rank : V → ℕ
  /-- Every edge increases the rank, so the graph is acyclic. -/
  rank_lt : ∀ e ∈ edges, rank e.1 < rank e.2
  /-- The capacity of a channel; `⊤` is the book's unlimited capacity. -/
  capacity : V × V → ℕ∞
  /-- The input string of an input node. -/
  input : V → Option BitString
  /-- The desired output string of an output node. -/
  output : V → Option BitString

namespace InformationRequest

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The vertices a vertex receives from.

SUV Section 12.1, p. 367. -/
def inNeighbors (r : InformationRequest V) (v : V) : Finset V :=
  (r.edges.filter fun e => e.2 = v).image Prod.fst

/-- The vertices a vertex sends to.

SUV Section 12.1, p. 367. -/
def outNeighbors (r : InformationRequest V) (v : V) : Finset V :=
  (r.edges.filter fun e => e.1 = v).image Prod.snd

/-- The information entering a node under the transmission `t`: the strings on the incoming
edges, in the order of their sources, followed by the input string of the node.

SUV Section 12.1, p. 367. -/
def incoming (r : InformationRequest V) (t : V × V → BitString) (v : V) : List BitString :=
  ((r.inNeighbors v).sort (· ≤ ·)).map (fun u => t (u, v)) ++ (r.input v).toList

/-- The information leaving a node under the transmission `t`: the strings on the outgoing
edges, in the order of their targets, followed by the output string of the node.

SUV Section 12.1, p. 367. -/
def outgoing (r : InformationRequest V) (t : V × V → BitString) (v : V) : List BitString :=
  ((r.outNeighbors v).sort (· ≤ ·)).map (fun w => t (v, w)) ++ (r.output v).toList

/-- `N`: the total length of all input and output strings of the request.

SUV Section 12.1, p. 367. -/
def totalLength (r : InformationRequest V) : ℕ :=
  ∑ v : V, ((r.input v).elim 0 List.length + (r.output v).elim 0 List.length)

/-- The edges entering the cut `I` from outside.

SUV Section 12.8, p. 383. -/
def cutEdges (r : InformationRequest V) (I : Finset V) : Finset (V × V) :=
  r.edges.filter fun e => e.1 ∉ I ∧ e.2 ∈ I

/-- The total capacity of the edges entering the cut `I`.

SUV Section 12.8, p. 383. -/
def cutCapacity (r : InformationRequest V) (I : Finset V) : ℕ∞ :=
  ∑ e ∈ r.cutEdges I, r.capacity e

/-- The input strings of the input nodes inside the cut `I`.

SUV Section 12.8, p. 383. -/
def cutInputs (r : InformationRequest V) (I : Finset V) : List BitString :=
  (I.sort (· ≤ ·)).flatMap fun v => (r.input v).toList

/-- The output strings of the output nodes inside the cut `I`.

SUV Section 12.8, p. 383. -/
def cutOutputs (r : InformationRequest V) (I : Finset V) : List BitString :=
  (I.sort (· ≤ ·)).flatMap fun v => (r.output v).toList

end InformationRequest

/-- The transmission `t` fulfils the request `r` with capacity slack `capSlack` and precision
`ε`: every edge carries at most its capacity plus `capSlack` bits, and at every node every
outgoing string — including the output string of the node — has conditional complexity at most
`ε` given the incoming information of that node.

SUV Section 12.1, p. 367 (with the two slacks made explicit). -/
def IsFulfilledUpTo (D : Map) {V : Type*} [Fintype V] [LinearOrder V]
    (r : InformationRequest V) (t : V × V → BitString) (capSlack ε : ℕ) : Prop :=
  (∀ e ∈ r.edges, ((t e).length : ℕ∞) ≤ r.capacity e + (capSlack : ℕ∞)) ∧
    ∀ v : V, ∀ x ∈ r.outgoing t v, condK D x (listCode (r.incoming t v)) ≤ (ε : ℕ∞)

/-- The transmission `t` fulfils the request `r` with precision `ε` and no slack in the
capacities.

SUV Section 12.1, p. 367. -/
def IsFulfilled (D : Map) {V : Type*} [Fintype V] [LinearOrder V]
    (r : InformationRequest V) (t : V × V → BitString) (ε : ℕ) : Prop :=
  IsFulfilledUpTo D r t 0 ε

/-- A sequence of requests on a fixed graph: the book's `≈ 0` is a statement about such a
sequence, indexed by the bound `N` on the total length of the input and output strings.

SUV Section 12.1, p. 367. -/
def RequestFamily (V : Type*) [Fintype V] [LinearOrder V] := ℕ → InformationRequest V

/-- The family is indexed correctly: the `N`-th request has total input/output length at most
`N`.

SUV Section 12.1, p. 367. -/
def IsBoundedFamily {V : Type*} [Fintype V] [LinearOrder V] (f : RequestFamily V) : Prop :=
  ∀ N : ℕ, (f N).totalLength ≤ N

/-- The family of requests is fulfillable with logarithmic precision: one constant `c` serves
all of them, every request being fulfilled with precision `logSlack c N`.

SUV Section 12.1, p. 367. -/
def IsFulfillableUpToLog (D : Map) {V : Type*} [Fintype V] [LinearOrder V]
    (f : RequestFamily V) : Prop :=
  ∃ c : ℕ, ∀ N : ℕ, ∃ t : V × V → BitString, IsFulfilled D (f N) t (logSlack c N)

/-! ### The cut reconstruction argument -/

private theorem cutMessages_length_le_cutCapacity {V : Type*} [Fintype V] [LinearOrder V]
    (r : InformationRequest V) (t : V × V → BitString) (I : Finset V)
    (hcap : ∀ e ∈ r.edges, ((t e).length : ℕ∞) ≤ r.capacity e)
    (hfin : r.cutCapacity I ≠ ⊤) :
    ((∑ e ∈ r.cutEdges I, (t e).length : ℕ) : ℕ∞) ≤
      (r.cutCapacity I).toNat := by
  rw [ENat.natCast_toNat hfin]
  unfold InformationRequest.cutCapacity
  push_cast
  exact Finset.sum_le_sum fun e he => hcap e (Finset.mem_filter.mp he).1

section CutDecoder

open CodedFiniteDistribution

private def cutStepProgram (c : BitString) : BitString := (decodeListCode c).getD 0 []

private def cutStepContext (c : BitString) (L : List BitString) : BitString :=
  listCode (((decodeListCode c).tail).map fun u => L.getD u.length [])

private def cutStep (D : Map) (st : List BitString × List BitString) :
    Part (List BitString ⊕ (List BitString × List BitString)) :=
  bif st.1.length == 0 then Part.some (Sum.inl st.2) else
    (D (cutStepProgram (st.1.getD 0 []), cutStepContext (st.1.getD 0 []) st.2)).map
      fun x => Sum.inr (st.1.tail, st.2 ++ [x])

private def splitByLengths (ls : List ℕ) (raw : BitString) : List BitString :=
  (ls.foldl (fun st n => (st.1.drop n, st.2 ++ [st.1.take n])) (raw, ([] : List BitString))).2

private def cutDecoder (D : Map) : Map := fun pc =>
  (PFun.fix (cutStep D) (decodeListCode ((decodeListCode (decodeFirst pc.1)).getD 0 []),
      decodeListCode pc.2 ++ splitByLengths
        ((decodeListCode ((decodeListCode (decodeFirst pc.1)).getD 2 [])).map decodeBits)
        (decodeSecond pc.1))).map
    fun L => listCode ((decodeListCode ((decodeListCode (decodeFirst pc.1)).getD 1 [])).map
      fun u => L.getD u.length [])

private theorem cutStepContext_primrec : Primrec₂ cutStepContext := by
  unfold cutStepContext
  refine listCode_primrec.comp (Primrec.list_map
    (Primrec.list_tail.comp (decodeListCode_primrec.comp Primrec.fst)) ?_)
  exact ((Primrec.list_getD []).comp (Primrec.snd.comp Primrec.fst)
    (Primrec.list_length.comp Primrec.snd)).to₂

private theorem cutStep_partrec (D : Map) (hD : Partrec D) : Partrec (cutStep D) := by
  have hc : Primrec fun st : List BitString × List BitString => st.1.getD 0 [] :=
    (Primrec.list_getD []).comp Primrec.fst (Primrec.const 0)
  have hq : Primrec fun st : List BitString × List BitString => cutStepProgram (st.1.getD 0 []) :=
    ((Primrec.list_getD []).comp decodeListCode_primrec (Primrec.const 0)).comp hc
  have hx : Primrec fun st : List BitString × List BitString =>
      cutStepContext (st.1.getD 0 []) st.2 := cutStepContext_primrec.comp hc Primrec.snd
  refine Partrec.cond ?_ (Computable.partrec ?_) (Partrec.map (hD.comp (hq.pair hx).to_comp) ?_)
  · exact (Primrec.beq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 0)).to_comp
  · exact (Primrec.sumInl.comp Primrec.snd).to_comp
  · exact (Primrec.sumInr.comp ((Primrec.list_tail.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.list_cons.comp Primrec.snd (Primrec.const []))))).to_comp.to₂

private theorem splitByLengths_primrec : Primrec₂ splitByLengths := by
  unfold splitByLengths
  refine Primrec.snd.comp (Primrec.list_foldl Primrec.fst
    (Primrec.snd.pair (Primrec.const [])) (h := fun (_ : List ℕ × BitString)
      (sb : (BitString × List BitString) × ℕ) => (sb.1.1.drop sb.2, sb.1.2 ++ [sb.1.1.take sb.2]))
    ?_)
  exact ((Primrec.list_drop.comp (Primrec.snd.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).pair (Primrec.list_append.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.list_take.comp
        (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.const [])))).to₂

private theorem cutDecoder_partrec (D : Map) (hD : Partrec D) : Partrec (cutDecoder D) := by
  have hH : Primrec fun pc : BitString × BitString => decodeListCode (decodeFirst pc.1) :=
    decodeListCode_primrec.comp (decodeFirst_primrec.comp Primrec.fst)
  have hG : ∀ i, Primrec fun pc : BitString × BitString =>
      decodeListCode ((decodeListCode (decodeFirst pc.1)).getD i []) := fun i =>
    decodeListCode_primrec.comp ((Primrec.list_getD []).comp hH (Primrec.const i))
  have hL0 : Primrec fun pc : BitString × BitString => decodeListCode pc.2 ++ splitByLengths
        ((decodeListCode ((decodeListCode (decodeFirst pc.1)).getD 2 [])).map decodeBits)
        (decodeSecond pc.1) :=
    Primrec.list_append.comp (decodeListCode_primrec.comp Primrec.snd)
      (splitByLengths_primrec.comp (Primrec.list_map (hG 2)
        (primrec_decodeBits.comp Primrec.snd).to₂) (decodeSecond_primrec.comp Primrec.fst))
  refine Partrec.map ((Partrec.fix (cutStep_partrec D hD)).comp ((hG 0).pair hL0).to_comp) ?_
  exact (listCode_primrec.comp (Primrec.list_map ((hG 1).comp Primrec.fst)
    ((Primrec.list_getD []).comp (Primrec.snd.comp Primrec.fst)
      (Primrec.list_length.comp Primrec.snd)).to₂)).to_comp.to₂


private theorem splitByLengths_flatten (ms : List BitString) :
    splitByLengths (ms.map List.length) ms.flatten = ms := by
  have key : ∀ (ms : List BitString) (rest : BitString) (acc : List BitString),
      (ms.map List.length).foldl (fun st n => (st.1.drop n, st.2 ++ [st.1.take n]))
        (ms.flatten ++ rest, acc) = (rest, acc ++ ms) := by
    intro ms
    induction ms with
    | nil => intro rest acc; simp
    | cons m ms ih =>
      intro rest acc
      simp only [List.map_cons, List.foldl_cons, List.flatten_cons, List.append_assoc]
      rw [List.drop_left, List.take_left, ih]
      simp
  have h := key ms [] []
  simp only [List.append_nil, List.nil_append] at h
  simp [splitByLengths, h]

/-- The run of steps `codes` from the list `L` produces the strings `xs`. -/
private def CutRun (D : Map) : List BitString → List BitString → List BitString → Prop
  | [], [], _ => True
  | c :: cs, x :: xs, L => x ∈ D (cutStepProgram c, cutStepContext c L) ∧ CutRun D cs xs (L ++ [x])
  | _, _, _ => False

private theorem mem_fix_cutStep_of_cutRun (D : Map) :
    ∀ (codes xs L : List BitString), CutRun D codes xs L →
      L ++ xs ∈ PFun.fix (cutStep D) (codes, L) := by
  intro codes
  induction codes with
  | nil =>
    intro xs L h
    cases xs with
    | nil => exact PFun.mem_fix_iff.mpr (Or.inl (by simp [cutStep]))
    | cons x xs => exact h.elim
  | cons c cs ih =>
    intro xs L h
    cases xs with
    | nil => exact h.elim
    | cons x xs =>
      refine PFun.mem_fix_iff.mpr (Or.inr ⟨(cs, L ++ [x]), ?_, ?_⟩)
      · simp only [cutStep, List.length_cons, List.getD_cons_zero, List.tail_cons]
        exact Part.mem_map _ h.1
      · simpa using ih xs (L ++ [x]) h.2

private theorem cutRun_append (D : Map) :
    ∀ (A xa B xb L : List BitString), CutRun D A xa L → CutRun D B xb (L ++ xa) →
      CutRun D (A ++ B) (xa ++ xb) L := by
  intro A
  induction A with
  | nil =>
    intro xa B xb L h1 h2
    cases xa with
    | nil => simpa using h2
    | cons x xa => exact h1.elim
  | cons c cs ih =>
    intro xa B xb L h1 h2
    cases xa with
    | nil => exact h1.elim
    | cons x xa =>
      refine ⟨h1.1, ih xa B xb (L ++ [x]) h1.2 ?_⟩
      simpa using h2

private theorem cutRun_flatMap {ι : Type*} (D : Map) (S O : ι → List BitString) :
    ∀ (ord : List ι) (L : List BitString),
      (∀ pre v post, ord = pre ++ v :: post → CutRun D (S v) (O v) (L ++ pre.flatMap O)) →
      CutRun D (ord.flatMap S) (ord.flatMap O) L := by
  intro ord
  induction ord with
  | nil => intro L _; simp [CutRun]
  | cons v rest ih =>
    intro L h
    simp only [List.flatMap_cons]
    refine cutRun_append D _ _ _ _ L (by simpa using h [] v rest rfl) (ih _ ?_)
    intro pre w post hrest
    have := h (v :: pre) w post (by simp [hrest])
    simpa [List.append_assoc] using this

private def stepCode (q : BitString) (idx : List ℕ) : BitString :=
  listCode (q :: idx.map fun i => List.replicate i true)

private theorem cutStepProgram_stepCode (q : BitString) (idx : List ℕ) :
    cutStepProgram (stepCode q idx) = q := by
  simp [cutStepProgram, stepCode, -listCode_cons]

private theorem cutStepContext_stepCode (q : BitString) (idx : List ℕ) (L : List BitString) :
    cutStepContext (stepCode q idx) L = listCode (idx.map fun i => L.getD i []) := by
  simp [cutStepContext, stepCode, -listCode_cons, Function.comp_def]

private theorem cutRun_block (D : Map) (q : BitString → BitString) (idx : List ℕ)
    (c : BitString) (F : List BitString) :
    ∀ (xs L : List BitString), L ++ xs <+: F →
      (∀ M, L <+: M → M <+: F → listCode (idx.map fun i => M.getD i []) = c) →
      (∀ x ∈ xs, x ∈ D (q x, c)) →
      CutRun D (xs.map fun x => stepCode (q x) idx) xs L := by
  intro xs
  induction xs with
  | nil => intro L _ _ _; trivial
  | cons x xs ih =>
    intro L hpre hctx hx
    refine ⟨?_, ih (L ++ [x]) (by simpa using hpre) ?_ fun y hy => hx y (by simp [hy])⟩
    · rw [cutStepProgram_stepCode, cutStepContext_stepCode,
        hctx L (List.prefix_refl L) ((List.prefix_append L _).trans hpre)]
      exact hx x (by simp)
    · intro M hM hMF
      exact hctx M ((List.prefix_append L [x]).trans hM) hMF

private theorem getD_idxOf_of_prefix {L M F : List BitString} {y : BitString} (hy : y ∈ L)
    (hLM : L <+: M) (hMF : M <+: F) : M.getD (F.idxOf y) [] = y := by
  obtain ⟨R, rfl⟩ := hLM
  obtain ⟨R', rfl⟩ := hMF
  rw [List.append_assoc, List.idxOf_append_of_mem hy,
    List.getD_append _ _ _ _ (List.idxOf_lt_length_of_mem hy),
    List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hy), List.getElem_idxOf]

private theorem length_listCode_le (l : List BitString) (B : ℕ) (h : ∀ x ∈ l, x.length ≤ B) :
    (listCode l).length ≤ l.length * (2 * B + 1) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [length_listCode_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    nlinarith


private theorem length_flatMap_le {ι : Type*} (f : ι → List BitString) (B : ℕ) :
    ∀ l : List ι, (∀ v ∈ l, (f v).length ≤ B) → (l.flatMap f).length ≤ l.length * B := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons v l ih =>
    intro h
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h v (by simp)
    have h2 := ih fun w hw => h w (by simp [hw])
    nlinarith

section Request

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The vertices of the cut, listed in an order compatible with the topological rank. -/
private noncomputable def cutOrder (r : InformationRequest V) (I : Finset V) : List V :=
  I.toList.mergeSort fun a b => decide (r.rank a ≤ r.rank b)

/-- The strings on the edges entering the cut. -/
private noncomputable def cutMessages (r : InformationRequest V) (t : V × V → BitString)
    (I : Finset V) : List BitString :=
  (r.cutEdges I).toList.map t

/-- Everything the decoder knows at the end: the cut inputs, the entering messages and the
outgoing strings of the cut vertices in topological order. -/
private noncomputable def cutTrace (r : InformationRequest V) (t : V × V → BitString)
    (I : Finset V) : List BitString :=
  r.cutInputs I ++ cutMessages r t I ++ (cutOrder r I).flatMap (r.outgoing t)

open Classical in
/-- A local program of length at most `ε` reconstructing `x` from the incoming information
of `v` (when one exists). -/
private noncomputable def localProgram (D : Map) (r : InformationRequest V)
    (t : V × V → BitString) (ε : ℕ) (v : V) (x : BitString) : BitString :=
  if h : ∃ p : BitString, p.length ≤ ε ∧ x ∈ D (p, listCode (r.incoming t v)) then h.choose
  else []

/-- The step codes of the decoder: one per outgoing string of a cut vertex. -/
private noncomputable def cutCodes (D : Map) (r : InformationRequest V) (t : V × V → BitString)
    (I : Finset V) (ε : ℕ) : List BitString :=
  (cutOrder r I).flatMap fun v => (r.outgoing t v).map fun x =>
    stepCode (localProgram D r t ε v x) ((r.incoming t v).map fun y => (cutTrace r t I).idxOf y)

/-- The program given to `cutDecoder`: a header (step codes, positions of the outputs,
lengths of the messages) followed by the raw concatenation of the entering messages. -/
private noncomputable def cutProgram (D : Map) (r : InformationRequest V)
    (t : V × V → BitString) (I : Finset V) (ε : ℕ) : BitString :=
  pairCode (listCode [listCode (cutCodes D r t I ε),
      listCode ((r.cutOutputs I).map fun y => List.replicate ((cutTrace r t I).idxOf y) true),
      listCode ((cutMessages r t I).map fun m => Nat.bits m.length)])
    (cutMessages r t I).flatten

private theorem mem_cutOrder {r : InformationRequest V} {I : Finset V} {v : V} :
    v ∈ cutOrder r I ↔ v ∈ I := by
  simp [cutOrder, List.mem_mergeSort]

private theorem length_cutOrder (r : InformationRequest V) (I : Finset V) :
    (cutOrder r I).length ≤ Fintype.card V := by
  simpa [cutOrder, List.length_mergeSort] using Finset.card_le_univ I

private theorem mem_pre_of_rank_lt {r : InformationRequest V} {I : Finset V}
    {pre post : List V} {u v : V} (hord : cutOrder r I = pre ++ v :: post) (hu : u ∈ I)
    (hlt : r.rank u < r.rank v) : u ∈ pre := by
  have hp := List.pairwise_mergeSort (le := fun a b => decide (r.rank a ≤ r.rank b))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) I.toList
  have hmem : u ∈ cutOrder r I := mem_cutOrder.mpr hu
  unfold cutOrder at hord hmem
  rw [hord] at hp hmem
  rw [List.pairwise_append, List.pairwise_cons] at hp
  rcases List.mem_append.mp hmem with h | h
  · exact h
  · rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := hp.2.1.1 u h
      simp at this
      omega

private theorem mem_incoming {r : InformationRequest V} {t : V × V → BitString} {v : V}
    {y : BitString} (hy : y ∈ r.incoming t v) :
    (∃ u, (u, v) ∈ r.edges ∧ t (u, v) = y) ∨ r.input v = some y := by
  simp only [InformationRequest.incoming, InformationRequest.inNeighbors, List.mem_append,
    List.mem_map, Finset.mem_sort, Finset.mem_image, Finset.mem_filter, Option.mem_toList] at hy
  rcases hy with ⟨u, ⟨e, ⟨he, he2⟩, rfl⟩, rfl⟩ | h
  · left; exact ⟨e.1, by rw [← he2]; exact he, by rw [← he2]⟩
  · right; exact h

private theorem mem_outgoing_of_edge (r : InformationRequest V) (t : V × V → BitString)
    {v w : V} (h : (v, w) ∈ r.edges) : t (v, w) ∈ r.outgoing t v := by
  simp only [InformationRequest.outgoing, InformationRequest.outNeighbors, List.mem_append,
    List.mem_map, Finset.mem_sort, Finset.mem_image, Finset.mem_filter]
  exact Or.inl ⟨w, ⟨(v, w), ⟨h, rfl⟩, rfl⟩, rfl⟩

private theorem mem_outgoing_of_output (r : InformationRequest V) (t : V × V → BitString)
    {v : V} {y : BitString} (h : r.output v = some y) : y ∈ r.outgoing t v := by
  simp [InformationRequest.outgoing, h]

private theorem mem_cutInputs {r : InformationRequest V} {I : Finset V} {v : V}
    {y : BitString} (hv : v ∈ I) (h : r.input v = some y) : y ∈ r.cutInputs I := by
  simp only [InformationRequest.cutInputs, List.mem_flatMap, Finset.mem_sort]
  exact ⟨v, hv, by simp [h]⟩

private theorem mem_cutOutputs {r : InformationRequest V} {I : Finset V} {y : BitString}
    (h : y ∈ r.cutOutputs I) : ∃ v ∈ I, r.output v = some y := by
  simp only [InformationRequest.cutOutputs, List.mem_flatMap, Finset.mem_sort,
    Option.mem_toList] at h
  exact h

private theorem length_toList_le (o : Option BitString) : o.toList.length ≤ 1 := by
  cases o <;> simp

private theorem length_incoming_le (r : InformationRequest V) (t : V × V → BitString) (v : V) :
    (r.incoming t v).length ≤ Fintype.card V + 1 := by
  simp only [InformationRequest.incoming, List.length_append, List.length_map,
    Finset.length_sort]
  have := Finset.card_le_univ (r.inNeighbors v)
  have := length_toList_le (r.input v)
  omega

private theorem length_outgoing_le (r : InformationRequest V) (t : V × V → BitString) (v : V) :
    (r.outgoing t v).length ≤ Fintype.card V + 1 := by
  simp only [InformationRequest.outgoing, List.length_append, List.length_map,
    Finset.length_sort]
  have := Finset.card_le_univ (r.outNeighbors v)
  have := length_toList_le (r.output v)
  omega

private theorem length_cutInputs_le (r : InformationRequest V) (I : Finset V) :
    (r.cutInputs I).length ≤ Fintype.card V := by
  have h := length_flatMap_le (fun v => (r.input v).toList) 1 (I.sort (· ≤ ·))
    (fun v _ => length_toList_le _)
  rw [Finset.length_sort] at h
  have := Finset.card_le_univ I
  unfold InformationRequest.cutInputs
  omega

private theorem length_cutOutputs_le (r : InformationRequest V) (I : Finset V) :
    (r.cutOutputs I).length ≤ Fintype.card V := by
  have h := length_flatMap_le (fun v => (r.output v).toList) 1 (I.sort (· ≤ ·))
    (fun v _ => length_toList_le _)
  rw [Finset.length_sort] at h
  have := Finset.card_le_univ I
  unfold InformationRequest.cutOutputs
  omega

private theorem length_cutMessages_le (r : InformationRequest V) (t : V × V → BitString)
    (I : Finset V) : (cutMessages r t I).length ≤ Fintype.card V * Fintype.card V := by
  simp only [cutMessages, List.length_map, Finset.length_toList]
  simpa [Fintype.card_prod] using Finset.card_le_univ (r.cutEdges I)

private theorem length_cutTrace_le (r : InformationRequest V) (t : V × V → BitString)
    (I : Finset V) :
    (cutTrace r t I).length ≤ 2 * Fintype.card V * (Fintype.card V + 1) := by
  have h1 := length_cutInputs_le r I
  have h2 := length_cutMessages_le r t I
  have h3 := length_flatMap_le (r.outgoing t) (Fintype.card V + 1) (cutOrder r I)
    (fun v _ => length_outgoing_le r t v)
  have h4 := length_cutOrder r I
  simp only [cutTrace, List.length_append]
  nlinarith

/-- The decoder, run on `cutProgram` with the cut inputs as context, outputs the cut outputs:
every outgoing string of a cut vertex is reconstructed, in topological order, from strings
already known. -/
private theorem cutDecoder_cutProgram (D : Map) (r : InformationRequest V)
    (t : V × V → BitString) (I : Finset V) (ε : ℕ) (hful : IsFulfilled D r t ε) :
    listCode (r.cutOutputs I) ∈
      cutDecoder D (cutProgram D r t I ε, listCode (r.cutInputs I)) := by
  have hrun : CutRun D (cutCodes D r t I ε) ((cutOrder r I).flatMap (r.outgoing t))
      (r.cutInputs I ++ cutMessages r t I) := by
    refine cutRun_flatMap D _ (r.outgoing t) (cutOrder r I) _ ?_
    intro pre v post hord
    have hvI : v ∈ I := mem_cutOrder.mp (by rw [hord]; simp)
    have hpreF : r.cutInputs I ++ cutMessages r t I ++ pre.flatMap (r.outgoing t) ++
        r.outgoing t v <+: cutTrace r t I :=
      ⟨post.flatMap (r.outgoing t), by simp [cutTrace, hord, List.append_assoc]⟩
    have hknown : ∀ y ∈ r.incoming t v,
        y ∈ r.cutInputs I ++ cutMessages r t I ++ pre.flatMap (r.outgoing t) := by
      intro y hy
      rcases mem_incoming hy with ⟨u, hu, rfl⟩ | hin
      · by_cases huI : u ∈ I
        · have hpre := mem_pre_of_rank_lt hord huI (r.rank_lt _ hu)
          simp only [List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨u, hpre, mem_outgoing_of_edge r t hu⟩
        · have hcut : (u, v) ∈ r.cutEdges I := Finset.mem_filter.mpr ⟨hu, huI, hvI⟩
          simp only [cutMessages, List.mem_append, List.mem_map, Finset.mem_toList]
          exact Or.inl (Or.inr ⟨_, hcut, rfl⟩)
      · simp only [List.mem_append]
        exact Or.inl (Or.inl (mem_cutInputs hvI hin))
    refine cutRun_block D (localProgram D r t ε v) _ (listCode (r.incoming t v))
      (cutTrace r t I) (r.outgoing t v) _ hpreF ?_ ?_
    · intro M hLM hMF
      congr 1
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (r.incoming t v)]
      exact List.map_congr_left fun y hy => getD_idxOf_of_prefix (hknown y hy) hLM hMF
    · intro x hx
      obtain ⟨p, hp, hpx⟩ := (condK_le_iff D _ _ ε).mp (hful.2 v x hx)
      have hex : ∃ p : BitString, p.length ≤ ε ∧ x ∈ D (p, listCode (r.incoming t v)) :=
        ⟨p, hp, hpx⟩
      rw [localProgram, dite_eq_left hex]
      exact hex.choose_spec.2
  have hfix := mem_fix_cutStep_of_cutRun D _ _ _ hrun
  have htrace : r.cutInputs I ++ cutMessages r t I ++
      (cutOrder r I).flatMap (r.outgoing t) = cutTrace r t I := rfl
  rw [htrace] at hfix
  simp only [cutDecoder, cutProgram, decodeFirst_pairCode, decodeSecond_pairCode,
    decodeListCode_listCode, List.getD_cons_zero, List.getD_cons_succ, List.map_map,
    Function.comp_def, decodeBits_natBits]
  rw [splitByLengths_flatten]
  refine Part.mem_map_iff _ |>.mpr ⟨_, hfix, ?_⟩
  congr 1
  conv_rhs => rw [← List.map_id (r.cutOutputs I)]
  refine List.map_congr_left fun y hy => ?_
  obtain ⟨v, hvI, hout⟩ := mem_cutOutputs hy
  have hyF : y ∈ cutTrace r t I := by
    simp only [cutTrace, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨v, mem_cutOrder.mpr hvI, mem_outgoing_of_output r t hout⟩
  rw [List.length_replicate]
  exact getD_idxOf_of_prefix hyF (List.prefix_refl _) (List.prefix_refl _)

private theorem length_localProgram_le (D : Map) (r : InformationRequest V)
    (t : V × V → BitString) (ε : ℕ) (v : V) (x : BitString) :
    (localProgram D r t ε v x).length ≤ ε := by
  unfold localProgram
  split_ifs with h
  · exact h.choose_spec.1
  · simp

private theorem length_unaryCode_le (F : List BitString) (l : List BitString) :
    ∀ u ∈ l.map (fun y => List.replicate (F.idxOf y) true), u.length ≤ F.length := by
  intro u hu
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hu
  simpa using List.idxOf_le_length

/-- The length of `cutProgram`: the entering messages verbatim, plus `O(ε)` for the local
programs, plus the logarithmic cost of the message lengths, plus a graph constant. -/
private theorem length_cutProgram_le (D : Map) (r : InformationRequest V)
    (t : V × V → BitString) (I : Finset V) (ε β : ℕ)
    (hβ : ∀ e ∈ r.cutEdges I, (Nat.bits (t e).length).length ≤ β) :
    (cutProgram D r t I ε).length ≤ (∑ e ∈ r.cutEdges I, (t e).length) +
      16 * Fintype.card V * (Fintype.card V + 1) * ε +
      4 * Fintype.card V * Fintype.card V * (2 * β + 1) +
      (4 * Fintype.card V * (Fintype.card V + 1) *
          (3 + 2 * (Fintype.card V + 1) * (4 * Fintype.card V * (Fintype.card V + 1) + 1)) +
        4 * Fintype.card V * (4 * Fintype.card V * (Fintype.card V + 1) + 1) + 7) := by
  have hF := length_cutTrace_le r t I
  have hstep : ∀ c ∈ cutCodes D r t I ε, c.length ≤
      2 * ε + 1 + (Fintype.card V + 1) * (2 * (2 * Fintype.card V * (Fintype.card V + 1)) + 1) := by
    intro c hc
    simp only [cutCodes, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨v, _, x, _, rfl⟩ := hc
    rw [stepCode, length_listCode_cons]
    have h1 := length_localProgram_le D r t ε v x
    have h2 := length_listCode_le
      (((r.incoming t v).map fun y => (cutTrace r t I).idxOf y).map
        fun i => List.replicate i true) _ fun u hu =>
      (length_unaryCode_le (cutTrace r t I) (r.incoming t v) u
        (by rw [List.map_map] at hu; exact hu)).trans hF
    rw [List.length_map, List.length_map] at h2
    have h3 := length_incoming_le r t v
    have h4 := Nat.mul_le_mul_right (2 * (2 * Fintype.card V * (Fintype.card V + 1)) + 1) h3
    simp only [List.map_map, Function.comp_def] at h2 ⊢
    omega
  have hcodes : (cutCodes D r t I ε).length ≤ Fintype.card V * (Fintype.card V + 1) := by
    have h := length_flatMap_le (fun v => (r.outgoing t v).map fun x =>
        stepCode (localProgram D r t ε v x)
          ((r.incoming t v).map fun y => (cutTrace r t I).idxOf y))
      (Fintype.card V + 1) (cutOrder r I) (fun v _ => by
        rw [List.length_map]; exact length_outgoing_le r t v)
    exact h.trans (Nat.mul_le_mul_right _ (length_cutOrder r I))
  have hS := length_listCode_le _ _ hstep
  have hS' := Nat.mul_le_mul_right (2 * (2 * ε + 1 + (Fintype.card V + 1) *
    (2 * (2 * Fintype.card V * (Fintype.card V + 1)) + 1)) + 1) hcodes
  have hO := length_listCode_le _ _ fun u hu =>
    (length_unaryCode_le (cutTrace r t I) (r.cutOutputs I) u hu).trans hF
  rw [List.length_map] at hO
  have hO' := Nat.mul_le_mul_right (2 * (2 * Fintype.card V * (Fintype.card V + 1)) + 1)
    (length_cutOutputs_le r I)
  have hL := length_listCode_le ((cutMessages r t I).map fun m => Nat.bits m.length) β
    (fun u hu => by
      simp only [cutMessages, List.map_map, List.mem_map, Finset.mem_toList,
        Function.comp_apply] at hu
      obtain ⟨e, he, rfl⟩ := hu
      exact hβ e he)
  rw [List.length_map] at hL
  have hL' := Nat.mul_le_mul_right (2 * β + 1) (length_cutMessages_le r t I)
  have hraw : (cutMessages r t I).flatten.length = ∑ e ∈ r.cutEdges I, (t e).length := by
    rw [List.length_flatten, cutMessages, List.map_map]
    exact Finset.sum_map_toList _ _
  rw [cutProgram, length_pairCode, length_listCode_cons, length_listCode_cons,
    length_listCode_cons, listCode_nil, List.length_nil, hraw]
  nlinarith

end Request

private theorem length_le_totalLength_of_output {V : Type*} [Fintype V] [LinearOrder V]
    (r : InformationRequest V) {v : V} {y : BitString} (h : r.output v = some y) :
    y.length ≤ r.totalLength := by
  have hle : ((r.input v).elim 0 List.length + (r.output v).elim 0 List.length) ≤
      r.totalLength :=
    Finset.single_le_sum (f := fun v => (r.input v).elim 0 List.length +
      (r.output v).elim 0 List.length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  rw [h] at hle
  simp only [Option.elim_some] at hle
  omega

/-- The trivial bound: the cut outputs can always be given verbatim, at a cost linear in the
total length `N`. -/
private theorem condK_cutOutputs_le_trivial (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ {V : Type*} [Fintype V] [LinearOrder V] (r : InformationRequest V)
      (I : Finset V) (N : ℕ), r.totalLength ≤ N →
      condK D (listCode (r.cutOutputs I)) (listCode (r.cutInputs I)) ≤
        ((Fintype.card V * (2 * N + 1) + c : ℕ) : ℕ∞) := by
  obtain ⟨cA, hcA⟩ := condK_le_plainK D hD
  obtain ⟨cB, hcB⟩ := plainK_le_length D hD
  refine ⟨cB + cA, ?_⟩
  intro V _ _ r I N hN
  have hlen := length_listCode_le (r.cutOutputs I) N fun y hy => by
    obtain ⟨v, _, hv⟩ := mem_cutOutputs hy
    exact (length_le_totalLength_of_output r hv).trans hN
  have hlen' := hlen.trans (Nat.mul_le_mul_right (2 * N + 1) (length_cutOutputs_le r I))
  calc condK D (listCode (r.cutOutputs I)) (listCode (r.cutInputs I))
      ≤ plainK D (listCode (r.cutOutputs I)) + cA := hcA _ _
    _ ≤ ((listCode (r.cutOutputs I)).length + cB : ℕ∞) + cA := by gcongr; exact hcB _
    _ ≤ ((Fintype.card V * (2 * N + 1) + (cB + cA) : ℕ) : ℕ∞) := by
      push_cast
      rw [← add_assoc]
      gcongr
      exact_mod_cast hlen'

/-- A length bounded linearly in `N` has binary length `log N + O(1)`. -/
private theorem length_bits_le_of_le_linear (n c N m : ℕ) (hm : m ≤ n * (2 * N + 1) + c) :
    (Nat.bits m).length ≤ (Nat.bits N).length + ((Nat.bits (2 * n + c)).length + 2) := by
  have h1 : m ≤ (2 * n + c) * (N + 1) := by nlinarith
  have h2 := length_natBits_mono h1
  have h3 := size_mul_le (2 * n + c) (N + 1)
  have h4 := length_natBits_add_le N 1
  have h5 : (Nat.bits 1).length = 1 := by decide
  simp only [Nat.size_eq_bits_len] at h2 h4 h5 ⊢
  omega

end CutDecoder

private theorem cut_topological_reconstruction (D : Map) (hD : isOptimalConditional D)
    {V : Type*} [Fintype V] [LinearOrder V] :
    ∃ a b : ℕ, ∀ (r : InformationRequest V) (t : V × V → BitString) (I : Finset V)
      (N ε : ℕ), r.totalLength ≤ N → IsFulfilled D r t ε →
      condK D (listCode (r.cutOutputs I)) (listCode (r.cutInputs I)) ≤
        ((∑ e ∈ r.cutEdges I, (t e).length : ℕ) : ℕ∞) +
          (a * ε + logSlack b N : ℕ∞) := by
  obtain ⟨cM, hcM⟩ := hD.2 (cutDecoder D) (cutDecoder_partrec D hD.1)
  obtain ⟨c1, hc1⟩ := condK_cutOutputs_le_trivial D hD
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card V := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K2, K2 = (Nat.bits (2 * n + c1)).length + 2 := ⟨_, rfl⟩
  obtain ⟨C0, hC0⟩ : ∃ C0, C0 = 4 * n * (n + 1) * (3 + 2 * (n + 1) * (4 * n * (n + 1) + 1)) +
      4 * n * (4 * n * (n + 1) + 1) + 7 := ⟨_, rfl⟩
  refine ⟨16 * n * (n + 1), 8 * n * n + 4 * n * n * (2 * K2 + 1) + C0 + cM, ?_⟩
  intro r t I N ε hN hful
  have htriv := hc1 r I N hN
  rw [← hn] at htriv
  by_cases hbig : n * (2 * N + 1) + c1 ≤ ∑ e ∈ r.cutEdges I, (t e).length
  · refine htriv.trans (le_trans ?_ le_self_add)
    exact_mod_cast hbig
  · push Not at hbig
    have hβ : ∀ e ∈ r.cutEdges I, (Nat.bits (t e).length).length ≤ (Nat.bits N).length + K2 :=
      fun e he => hK2 ▸ length_bits_le_of_le_linear n c1 N _
        ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) he).trans hbig.le)
    have hlen := length_cutProgram_le D r t I ε _ hβ
    have hmem := cutDecoder_cutProgram D r t I ε hful
    have hnat : (cutProgram D r t I ε).length + cM ≤ (∑ e ∈ r.cutEdges I, (t e).length) +
        (16 * n * (n + 1) * ε + logSlack (8 * n * n + 4 * n * n * (2 * K2 + 1) + C0 + cM) N) := by
      rw [← hn, ← hC0] at hlen
      have e1 : 4 * n * n * (2 * ((Nat.bits N).length + K2) + 1) =
          8 * n * n * (Nat.bits N).length + 4 * n * n * (2 * K2 + 1) := by ring
      have e2 : 8 * n * n * (Nat.bits N).length ≤
          (8 * n * n + 4 * n * n * (2 * K2 + 1) + C0 + cM) * (Nat.bits N).length :=
        Nat.mul_le_mul_right _ (by omega)
      unfold logSlack
      omega
    calc condK D (listCode (r.cutOutputs I)) (listCode (r.cutInputs I))
        ≤ condK (cutDecoder D) (listCode (r.cutOutputs I)) (listCode (r.cutInputs I)) + cM :=
          hcM _ _
      _ ≤ ((cutProgram D r t I ε).length : ℕ∞) + cM := by
          gcongr
          exact sInf_le ⟨_, hmem, rfl⟩
      _ ≤ _ := by exact_mod_cast hnat

private theorem mul_logSlack_add_logSlack (a b c N : ℕ) :
    a * logSlack c N + logSlack b N = logSlack (a * c + b) N := by
  simp only [logSlack]
  ring

/-- The cut-flow necessary condition: if a bounded family of requests on a fixed graph is
fulfillable with logarithmic precision, then for every cut `I` whose entering edges all have
finite capacity, the output strings inside `I` have conditional complexity at most the
capacity of the cut, given the input strings inside `I`, up to `O(log N)`.

SUV Section 12.8, pp. 383–384. -/
theorem condK_cutOutputs_le_cutCapacity (D : Map) (hD : isOptimalConditional D)
    {V : Type*} [Fintype V] [LinearOrder V] (f : RequestFamily V)
    (hbounded : IsBoundedFamily f) (hful : IsFulfillableUpToLog D f) (I : Finset V)
    (hfin : ∀ N, (f N).cutCapacity I ≠ ⊤) :
    ∃ c : ℕ, ∀ N : ℕ,
      condK D (listCode ((f N).cutOutputs I)) (listCode ((f N).cutInputs I)) ≤
        (((f N).cutCapacity I).toNat : ℕ∞) + (logSlack c N : ℕ∞) := by
  obtain ⟨cFul, hcFul⟩ := hful
  obtain ⟨a, b, hreconstruct⟩ := cut_topological_reconstruction D hD (V := V)
  refine ⟨a * cFul + b, fun N => ?_⟩
  obtain ⟨t, ht⟩ := hcFul N
  have hedgeCapacity : ∀ e ∈ (f N).edges, ((t e).length : ℕ∞) ≤ (f N).capacity e := by
    simpa using ht.1
  have hmessages :=
    cutMessages_length_le_cutCapacity (f N) t I hedgeCapacity (hfin N)
  calc
    condK D (listCode ((f N).cutOutputs I)) (listCode ((f N).cutInputs I))
        ≤ ((∑ e ∈ (f N).cutEdges I, (t e).length : ℕ) : ℕ∞) +
            (a * logSlack cFul N + logSlack b N : ℕ∞) :=
          hreconstruct (f N) t I N (logSlack cFul N) (hbounded N) ht
    _ ≤ (((f N).cutCapacity I).toNat : ℕ∞) +
          (a * logSlack cFul N + logSlack b N : ℕ∞) := add_le_add hmessages le_rfl
    _ = (((f N).cutCapacity I).toNat : ℕ∞) +
          (logSlack (a * cFul + b) N : ℕ∞) := by
            norm_cast
            exact congrArg (((f N).cutCapacity I).toNat + ·)
              (mul_logSlack_add_logSlack a b cFul N)

end Kolmogorov
